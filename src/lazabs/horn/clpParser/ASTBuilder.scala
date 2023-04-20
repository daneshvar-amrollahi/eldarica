package prolog
import lazabs.horn.global._
import lazabs.ast.ASTree._
import ap.theories.ADT
import lazabs.types._

// Return a class object instead of List[HornLiteral], String, Expression). Use case class

// List[HornLiteral]: freshVar = atomName
// String: freshVar
// Expression: Recursively built expression
// Set[HornLiteral]: ForceInt constraints


class ASTBuilder(adt: ADT) extends FoldVisitor[(List[HornLiteral], String, Expression, Set[HornLiteral]), Unit] {

    def combine(a: (List[HornLiteral], String, Expression, Set[HornLiteral]), b: (List[HornLiteral], String, Expression, Set[HornLiteral]), u: Unit) = {
        (List[HornLiteral](), "", new Expression(), Set[HornLiteral]())
    }
    def leaf(u: Unit) = (List[HornLiteral](), "", new Expression(), Set[HornLiteral]())

    var varCount = 0
    val usort = adt.sorts.head
    val anInt = adt.constructors.last
    val anIntIdx = adt.constructors.size - 1
    def getFreshVarName() = {
        varCount += 1
        "V_" + varCount
    }

    def getName(atom: prolog.Absyn.Atom) = {
        atom match {
            case a: prolog.Absyn.Atm => a.lident_
            case a: prolog.Absyn.EAtm => a.ident_
        }
    }

    override def visit(atom: prolog.Absyn.Atm, u: Unit) = {
        val atomName = atom.lident_
        val freshVar = getFreshVarName()
        val hl : HornLiteral = new Interp(
            BinaryExpression(new Variable(freshVar).stype(new AdtType(usort)), EqualityOp(), new ADTctor(adt, atomName, List()).stype(new AdtType(usort)))
        )
        
        (List[HornLiteral](hl), freshVar, new Expression(), Set[HornLiteral]())
    }

    override def visit(atom: prolog.Absyn.EAtm, u: Unit) = {
        val atomName = atom.ident_
        val freshVar = getFreshVarName()
        val hl : HornLiteral = new Interp(
            BinaryExpression(new Variable(freshVar).stype(new AdtType(usort)), EqualityOp(), new ADTctor(adt, atomName, List()).stype(new AdtType(usort)))
        ) 
        (List[HornLiteral](hl), freshVar, new Expression(), Set[HornLiteral]())
    }

    override def visit(complex: prolog.Absyn.Complex, u: Unit) = { 
        var variables = List[Variable]()
        var hls = List[HornLiteral]()

        for (i <- 0 until complex.listterm_.size()) {
            val term = complex.listterm_.get(i)
            if (term.isInstanceOf[prolog.Absyn.TAtom]) {
                val atom = term.asInstanceOf[prolog.Absyn.TAtom].atom_
                if (atom.isInstanceOf[prolog.Absyn.Atm]) {
                    val atm = atom.asInstanceOf[prolog.Absyn.Atm]
                    val arg = atm.accept(this, u)
                    val argVar: String = arg._2
                    val argHLs: List[HornLiteral] = arg._1
                    variables = variables :+ new Variable(argVar).stype(new AdtType(usort))
                    hls = hls ++ argHLs
                } else if (atom.isInstanceOf[prolog.Absyn.EAtm]) {
                    val eatm = atom.asInstanceOf[prolog.Absyn.EAtm]
                    val arg = eatm.accept(this, u)
                    val argVar: String = arg._2
                    val argHLs: List[HornLiteral] = arg._1
                    variables = variables :+ new Variable(argVar).stype(new AdtType(usort))
                    hls = hls ++ argHLs
                } 
            } else if (term.isInstanceOf[prolog.Absyn.Complex]) {
                val complex = term.asInstanceOf[prolog.Absyn.Complex]
                val arg = complex.accept(this, u)
                val argVar: String = arg._2
                val argHLs: List[HornLiteral] = arg._1
                variables = variables :+ new Variable(argVar).stype(new AdtType(usort))
                hls = hls ++ argHLs
            } else if (term.isInstanceOf[prolog.Absyn.VarT]) {
                val varName = term.asInstanceOf[prolog.Absyn.VarT].var_.asInstanceOf[prolog.Absyn.V].uident_ // Fix for Wild
                variables = variables :+ new Variable(varName).stype(new AdtType(usort))
            }             
        }

        val functionName: String = getName(complex.atom_)
        val freshVar: String = getFreshVarName()
        val hl: HornLiteral = new Interp(
            BinaryExpression(new Variable(freshVar).stype(new AdtType(usort)), EqualityOp(), new ADTctor(adt, functionName, variables).stype(new AdtType(usort)))
        )
        (hls :+ hl, freshVar, new Expression(), Set[HornLiteral]())
    }

    
    override def visit(pred: prolog.Absyn.APred, u: Unit) = {
        val atom = pred.atom_
        val relationName = getName(atom)
        val hl: HornLiteral = new RelVar(relationName, List[Parameter]()) 
        (List[HornLiteral](hl), relationName, new Expression(), Set[HornLiteral]())
    }

    override def visit(pred: prolog.Absyn.CPred, u: Unit) = { 
        val atom = pred.atom_
        val relationName = getName(atom)
        var parameters = List[Parameter]()
        var hls = List[HornLiteral]()
        for (i <- 0 until pred.listterm_.size()) {
            val term = pred.listterm_.get(i)
            if (term.isInstanceOf[prolog.Absyn.TAtom]) {
                val atom = term.asInstanceOf[prolog.Absyn.TAtom].atom_
                if (atom.isInstanceOf[prolog.Absyn.Atm]) {
                    val atm = atom.asInstanceOf[prolog.Absyn.Atm]
                    val arg = atm.accept(this, u)
                    val argVar: String = arg._2
                    val argHLs: List[HornLiteral] = arg._1
                    parameters = parameters :+ new Parameter(argVar, new AdtType(usort))
                    hls = hls ++ argHLs
                } else if (atom.isInstanceOf[prolog.Absyn.EAtm]) {
                    val eatm = atom.asInstanceOf[prolog.Absyn.EAtm]
                    val arg = eatm.accept(this, u)
                    val argVar: String = arg._2
                    val argHLs: List[HornLiteral] = arg._1
                    parameters = parameters :+ new Parameter(argVar, new AdtType(usort))
                    hls = hls ++ argHLs
                } 
            } else if (term.isInstanceOf[prolog.Absyn.Complex]) {
                val complex = term.asInstanceOf[prolog.Absyn.Complex]
                val arg = complex.accept(this, u)
                val argVar: String = arg._2
                val argHLs: List[HornLiteral] = arg._1
                parameters = parameters :+ new Parameter(argVar, new AdtType(usort))
                hls = hls ++ argHLs
            } else if (term.isInstanceOf[prolog.Absyn.VarT]) {
                val varName = term.asInstanceOf[prolog.Absyn.VarT].var_.asInstanceOf[prolog.Absyn.V].uident_ // Fix for Wild
                parameters = parameters :+ new Parameter(varName, new AdtType(usort))
            } else if (term.isInstanceOf[prolog.Absyn.TNum]) {
                val number = term.asInstanceOf[prolog.Absyn.TNum]
                val arg = number.accept(this, u)
                val argVar: String = arg._2
                val argHLs: List[HornLiteral] = arg._1
                parameters = parameters :+ new Parameter(argVar, new AdtType(usort))
                hls = hls ++ argHLs
            }
        }        
        val hl: HornLiteral = new RelVar(relationName, parameters)
        (hls :+ hl, "", new Expression(), Set[HornLiteral]())
    }


    

    override def visit(tnum: prolog.Absyn.TNum, u: Unit) = {
        val freshVar = getFreshVarName()
        val hl : HornLiteral = new Interp(
            BinaryExpression(new Variable(freshVar).stype(new AdtType(usort)), EqualityOp(), new ADTctor(adt, "anInt", List(new NumericalConst(BigInt(tnum.num_)))).stype(new AdtType(usort)))
        )
        (List[HornLiteral](hl), freshVar, new Expression(), Set[HornLiteral]())
    }

    override def visit(pred: prolog.Absyn.EPred, u: Unit) = {
        pred.expr_.accept(this, u)
    }

    override def visit(fact: prolog.Absyn.Fact, u: Unit) = {
        var result = leaf(u)
        val predicate = fact.predicate_.asInstanceOf[prolog.Absyn.Predicate]
        if (predicate.isInstanceOf[prolog.Absyn.APred]) {
            result = predicate.asInstanceOf[prolog.Absyn.APred].accept(this, u)
        } else if (predicate.isInstanceOf[prolog.Absyn.CPred]) {
            result = predicate.asInstanceOf[prolog.Absyn.CPred].accept(this, u)
        }
        result
    }

    override def visit(rule: prolog.Absyn.Rule, u: Unit) = { 
        var hornLiterals = List[HornLiteral]()
        var forceInts = Set[HornLiteral]()

        for (i <- 0 until rule.listpredicate_.size()) {
            val predicate = rule.listpredicate_.get(i)
            var result = leaf(u)
            if (predicate.isInstanceOf[prolog.Absyn.APred]) {
                result = predicate.asInstanceOf[prolog.Absyn.APred].accept(this, u)
            } else if (predicate.isInstanceOf[prolog.Absyn.CPred]) {
                result = predicate.asInstanceOf[prolog.Absyn.CPred].accept(this, u)
            } else if (predicate.isInstanceOf[prolog.Absyn.EPred]) {
                result = predicate.asInstanceOf[prolog.Absyn.EPred].accept(this, u)
                forceInts = forceInts ++ result._4
            }
            val hls: List[HornLiteral] = result._1
            hornLiterals = hornLiterals ++ hls
        }

        for (forceInt <- forceInts) {
            hornLiterals = hornLiterals :+ forceInt
        }

        val headPredicate = rule.predicate_.asInstanceOf[prolog.Absyn.Predicate]
        if (headPredicate.isInstanceOf[prolog.Absyn.APred]) {
            hornLiterals = hornLiterals ++ headPredicate.asInstanceOf[prolog.Absyn.APred].accept(this, u)._1
        } else if (headPredicate.isInstanceOf[prolog.Absyn.CPred]) {
            hornLiterals = hornLiterals ++ headPredicate.asInstanceOf[prolog.Absyn.CPred].accept(this, u)._1
        }

        (hornLiterals, "", new Expression(), Set[HornLiteral]())
    }

    override def visit(query: prolog.Absyn.Query, u: Unit) = { 
        var hornLiterals = List[HornLiteral]()
        var forceInts = Set[HornLiteral]()

        for (i <- 0 until query.listpredicate_.size()) {
            val predicate = query.listpredicate_.get(i)
            var result = leaf(u)
            if (predicate.isInstanceOf[prolog.Absyn.APred]) {
                result = predicate.asInstanceOf[prolog.Absyn.APred].accept(this, u)
            } else if (predicate.isInstanceOf[prolog.Absyn.CPred]) {
                result = predicate.asInstanceOf[prolog.Absyn.CPred].accept(this, u)
            } else if (predicate.isInstanceOf[prolog.Absyn.EPred]) {
                result = predicate.asInstanceOf[prolog.Absyn.EPred].accept(this, u)
                forceInts = forceInts ++ result._4
            }
            val hls: List[HornLiteral] = result._1
            hornLiterals = hornLiterals ++ hls
        }

        for (forceInt <- forceInts) {
            hornLiterals = hornLiterals :+ forceInt
        }

        (hornLiterals, "", new Expression(), Set[HornLiteral]())
    }

    override def visit(eq: prolog.Absyn.EqExpr, u: Unit) = { // #= : integer arithmetic
        val l = eq.expr_1.accept(this, u)
        val r = eq.expr_2.accept(this, u)
        val leftExpr = l._3
        val rightExpr = r._3
        val leftIntForces = l._4
        val rightIntForces = r._4 
        val forceInt = Set[HornLiteral](getForceInt(leftExpr), getForceInt(rightExpr))
        
        val left = ADTsel(adt, "theInt", List(leftExpr))
        val right = ADTsel(adt, "theInt", List(rightExpr))    
        val result: Expression = ADTctor(adt, "anInt", List(new BinaryExpression(left, EqualityOp(), right)))
        val forceInts: Set[HornLiteral] = leftIntForces | rightIntForces | forceInt
        
        (List[HornLiteral](new Interp(result)), "", result, forceInts)
    }

    override def visit(eqq: prolog.Absyn.EqqExpr, u: Unit) = { // = : not integer arithmetic
        val l = eqq.expr_1.accept(this, u)
        val r = eqq.expr_2.accept(this, u)
        val leftExpr = l._3
        val rightExpr = r._3
        val leftIntForces = l._4
        val rightIntForces = r._4 

        val result = new BinaryExpression(leftExpr, EqualityOp(), rightExpr)
        val forceInts : Set[HornLiteral] = leftIntForces | rightIntForces

        (List[HornLiteral](new Interp(result)), "", result, forceInts)
    }

    override def visit(neq: prolog.Absyn.NeqExpr, u: Unit) = { // #\= : integer arithmetic
        val l = neq.expr_1.accept(this, u)
        val r = neq.expr_2.accept(this, u)
        val leftExpr = l._3
        val rightExpr = r._3
        val leftIntForces = l._4
        val rightIntForces = r._4 
        val forceInt = Set[HornLiteral](getForceInt(leftExpr), getForceInt(rightExpr))
        
        val left = ADTsel(adt, "theInt", List(leftExpr))
        val right = ADTsel(adt, "theInt", List(rightExpr))    
        val result: Expression = ADTctor(adt, "anInt", List(new BinaryExpression(left, InequalityOp(), right)))
        val forceInts: Set[HornLiteral] = leftIntForces | rightIntForces | forceInt
        
        (List[HornLiteral](new Interp(result)), "", result, forceInts)
    }

    override def visit(neqq: prolog.Absyn.NeqqExpr, u: Unit) = { // =\= : not integer arithmetic
        val l = neqq.expr_1.accept(this, u)
        val r = neqq.expr_2.accept(this, u)
        val leftExpr = l._3
        val rightExpr = r._3
        val leftIntForces = l._4
        val rightIntForces = r._4 

        val result = new BinaryExpression(leftExpr, InequalityOp(), rightExpr)
        val forceInts : Set[HornLiteral] = leftIntForces | rightIntForces

        (List[HornLiteral](new Interp(result)), "", result, forceInts)
    }


    override def visit(disj: prolog.Absyn.DisjExpr, u: Unit) = {
        val l = disj.expr_1.accept(this, u)
        val r = disj.expr_2.accept(this, u)
        val leftExpr = l._3
        val rightExpr = r._3
        val leftIntForces = l._4
        val rightIntForces = r._4 
        val forceInt = Set[HornLiteral](getForceInt(leftExpr), getForceInt(rightExpr))

        var result = new Expression()

        if (disj.expr_1.isInstanceOf[prolog.Absyn.VarExpr] && disj.expr_2.isInstanceOf[prolog.Absyn.VarExpr])
            result = new BinaryExpression(leftExpr, DisjunctionOp(), rightExpr)
        else {
            val left = ADTsel(adt, "theInt", List(leftExpr))
            val right = ADTsel(adt, "theInt", List(rightExpr))
    
            result = ADTctor(adt, "anInt", List(new BinaryExpression(left, DisjunctionOp(), right)))
        }

        var forceInts = Set[HornLiteral]()

        if (disj.expr_1.isInstanceOf[prolog.Absyn.VarExpr] && disj.expr_2.isInstanceOf[prolog.Absyn.VarExpr])
            forceInts = leftIntForces | rightIntForces
        else
            forceInts = leftIntForces | rightIntForces | forceInt

        (List[HornLiteral](new Interp(result)), "", result, forceInts)
    }


    def getForceInt(e: Expression): HornLiteral = {
        new Interp(BinaryExpression(ADTtest(adt, 0, e), EqualityOp(), NumericalConst(BigInt(anIntIdx))))
    }

    override def visit(gt: prolog.Absyn.GtExpr, u: Unit) = {
        val l = gt.expr_1.accept(this, u)
        val r = gt.expr_2.accept(this, u)
        val leftExpr = l._3
        val rightExpr = r._3
        val leftIntForces = l._4
        val rightIntForces = r._4 

        val forceInt = Set[HornLiteral](getForceInt(leftExpr), getForceInt(rightExpr))
        val left = ADTsel(adt, "theInt", List(leftExpr))
        val right = ADTsel(adt, "theInt", List(rightExpr))
        val result = new BinaryExpression(left, GreaterThanOp(), right)

        val forceInts = (leftIntForces | rightIntForces) | forceInt
        (List[HornLiteral](new Interp(result)), "", result, forceInts)
    }

    override def visit(lt: prolog.Absyn.LtExpr, u: Unit) = {
        val l = lt.expr_1.accept(this, u)
        val r = lt.expr_2.accept(this, u)
        val leftExpr = l._3
        val rightExpr = r._3
        val leftIntForces = l._4
        val rightIntForces = r._4 

        val forceInt = Set[HornLiteral](getForceInt(leftExpr), getForceInt(rightExpr))
        val left = ADTsel(adt, "theInt", List(leftExpr))
        val right = ADTsel(adt, "theInt", List(rightExpr))
        val result = new BinaryExpression(left, LessThanOp(), right)

        val forceInts = (leftIntForces | rightIntForces) | forceInt
        (List[HornLiteral](new Interp(result)), "", result, forceInts)
    }

    override def visit(geq: prolog.Absyn.GeqExpr, u: Unit) = {
        val l = geq.expr_1.accept(this, u)
        val r = geq.expr_2.accept(this, u)
        val leftExpr = l._3
        val rightExpr = r._3
        val leftIntForces = l._4
        val rightIntForces = r._4 
        val forceInt = Set[HornLiteral](getForceInt(leftExpr), getForceInt(rightExpr))
        val left = ADTsel(adt, "theInt", List(leftExpr))
        val right = ADTsel(adt, "theInt", List(rightExpr))

        val result = new BinaryExpression(left, GreaterThanEqualOp(), right)
        val forceInts: Set[HornLiteral] = (leftIntForces | rightIntForces) | forceInt
        (List[HornLiteral](new Interp(result)), "", result, forceInts)
    }

    override def visit(leq: prolog.Absyn.LeqExpr, u: Unit) = {
        val l = leq.expr_1.accept(this, u)
        val r = leq.expr_2.accept(this, u)
        val leftExpr = l._3
        val rightExpr = r._3
        val leftIntForces = l._4
        val rightIntForces = r._4 

        val forceInt = Set[HornLiteral](getForceInt(leftExpr), getForceInt(rightExpr))
        val left = ADTsel(adt, "theInt", List(leftExpr))
        val right = ADTsel(adt, "theInt", List(rightExpr))
        val result = new BinaryExpression(left, LessThanEqualOp(), right)

        val forceInts = (leftIntForces | rightIntForces) | forceInt
        (List[HornLiteral](new Interp(result)), "", result, forceInts)
    }

    override def visit(add: prolog.Absyn.AddExpr, u: Unit) = {
        val l = add.expr_1.accept(this, u)
        val r = add.expr_2.accept(this, u)
        val leftExpr = l._3
        val rightExpr = r._3
        val leftIntForces = l._4
        val rightIntForces = r._4 

        val forceInt = Set[HornLiteral](getForceInt(leftExpr), getForceInt(rightExpr))
        val left = ADTsel(adt, "theInt", List(leftExpr))
        val right = ADTsel(adt, "theInt", List(rightExpr))
        val result = ADTctor(adt, "anInt", List(new BinaryExpression(left, AdditionOp(), right)))

        val forceInts = (leftIntForces | rightIntForces) | forceInt
        (List[HornLiteral](new Interp(result)), "", result, forceInts)
    }

    override def visit(sub: prolog.Absyn.SubExpr, u: Unit) = {
        val l = sub.expr_1.accept(this, u)
        val r = sub.expr_2.accept(this, u)
        val leftExpr = l._3
        val rightExpr = r._3
        val leftIntForces = l._4
        val rightIntForces = r._4 

        val forceInt = Set[HornLiteral](getForceInt(leftExpr), getForceInt(rightExpr))
        val left = ADTsel(adt, "theInt", List(leftExpr))
        val right = ADTsel(adt, "theInt", List(rightExpr))
        val result = ADTctor(adt, "anInt", List(new BinaryExpression(left, SubtractionOp(), right)))

        val forceInts = (leftIntForces | rightIntForces) | forceInt
        (List[HornLiteral](new Interp(result)), "", result, forceInts)
    }

    override def visit(mult: prolog.Absyn.MultExpr, u: Unit) = {
        val l = mult.expr_1.accept(this, u)
        val r = mult.expr_2.accept(this, u)
        val leftExpr = l._3
        val rightExpr = r._3
        val leftIntForces = l._4
        val rightIntForces = r._4 

        val forceInt = Set[HornLiteral](getForceInt(leftExpr), getForceInt(rightExpr))
        val left = ADTsel(adt, "theInt", List(leftExpr))
        val right = ADTsel(adt, "theInt", List(rightExpr))
        val result = ADTctor(adt, "anInt", List(new BinaryExpression(left, MultiplicationOp(), right)))

        val forceInts = (leftIntForces | rightIntForces) | forceInt
        (List[HornLiteral](new Interp(result)), "", result, forceInts)
    }

    override def visit(div: prolog.Absyn.DivExpr, u: Unit) = {
        val l = div.expr_1.accept(this, u)
        val r = div.expr_2.accept(this, u)
        val leftExpr = l._3
        val rightExpr = r._3
        val leftIntForces = l._4
        val rightIntForces = r._4 

        val forceInt = Set[HornLiteral](getForceInt(leftExpr), getForceInt(rightExpr))
        val left = ADTsel(adt, "theInt", List(leftExpr))
        val right = ADTsel(adt, "theInt", List(rightExpr))
        val result = ADTctor(adt, "anInt", List(new BinaryExpression(left, DivisionOp(), right)))

        val forceInts = (leftIntForces | rightIntForces) | forceInt
        (List[HornLiteral](new Interp(result)), "", result, forceInts)
    }

    override def visit(mod: prolog.Absyn.ModExpr, u: Unit) = {
        val l = mod.expr_1.accept(this, u)
        val r = mod.expr_2.accept(this, u)
        val leftExpr = l._3
        val rightExpr = r._3
        val leftIntForces = l._4
        val rightIntForces = r._4 

        val forceInt = Set[HornLiteral](getForceInt(leftExpr), getForceInt(rightExpr))
        val left = ADTsel(adt, "theInt", List(leftExpr))
        val right = ADTsel(adt, "theInt", List(rightExpr))
        val result = ADTctor(adt, "anInt", List(new BinaryExpression(left, ModuloOp(), right)))

        val forceInts = (leftIntForces | rightIntForces) | forceInt
        (List[HornLiteral](new Interp(result)), "", result, forceInts)
    }
    
    override def visit(num: prolog.Absyn.NumExpr, u: Unit) = {
        val result = ADTctor(adt, "anInt", List(new NumericalConst(BigInt(num.num_))))
        (List[HornLiteral](), "", result, Set[HornLiteral]())
    }

    override def visit(ve: prolog.Absyn.VarExpr, u: Unit) = {
        val expr = new Variable(ve.uident_).stype(new AdtType(usort))
        (List[HornLiteral](new Interp(expr)), "", expr, Set[HornLiteral]())
    }

    override def visit(e: prolog.Absyn.Empty, u: Unit) = {
        val result = ADTctor(adt, "nil", List[Variable]()).stype(new AdtType(usort))
        (List[HornLiteral](), "", result, Set[HornLiteral]())
    }


    // override def visit(e: prolog.Absyn.Enum, u: Unit) = {

    // }

    // override def visit(e: prolog.Absyn.Const, u: Unit) = {

    // }
    
}
