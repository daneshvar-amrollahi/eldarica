package prolog
import lazabs.horn.global._
import lazabs.ast.ASTree._
import ap.theories.ADT
import lazabs.types._

// Return a class object instead of List[HornLiteral], String, Expression)
// case class

class ASTBuilder(adt: ADT) extends FoldVisitor[(List[HornLiteral], String, Expression), Unit] {

    def combine(a: (List[HornLiteral], String, Expression), b: (List[HornLiteral], String, Expression), u: Unit) = {
        (List[HornLiteral](), "", new Expression())
    }
    def leaf(u: Unit) = (List[HornLiteral](), "", new Expression())

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
        
        (List[HornLiteral](hl), freshVar, new Expression())
    }

    override def visit(atom: prolog.Absyn.EAtm, u: Unit) = {
        val atomName = atom.ident_
        val freshVar = getFreshVarName()
        val hl : HornLiteral = new Interp(
            BinaryExpression(new Variable(freshVar).stype(new AdtType(usort)), EqualityOp(), new ADTctor(adt, atomName, List()).stype(new AdtType(usort)))
        ) 
        (List[HornLiteral](hl), freshVar, new Expression())
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
        (hls :+ hl, freshVar, new Expression())
    }

    
    override def visit(pred: prolog.Absyn.APred, u: Unit) = {
        val atom = pred.atom_
        val relationName = getName(atom)
        val hl: HornLiteral = new RelVar(relationName, List[Parameter]()) 
        (List[HornLiteral](hl), relationName, new Expression())
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
            } 
        }        
        val hl: HornLiteral = new RelVar(relationName, parameters)
        (hls :+ hl, "", new Expression())
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

        for (i <- 0 until rule.listpredicate_.size()) {
            val predicate = rule.listpredicate_.get(i)
            var result = leaf(u)
            if (predicate.isInstanceOf[prolog.Absyn.APred]) {
                result = predicate.asInstanceOf[prolog.Absyn.APred].accept(this, u)
            } else if (predicate.isInstanceOf[prolog.Absyn.CPred]) {
                result = predicate.asInstanceOf[prolog.Absyn.CPred].accept(this, u)
            } else if (predicate.isInstanceOf[prolog.Absyn.EPred]) {
                result = predicate.asInstanceOf[prolog.Absyn.EPred].accept(this, u)
            }
            val hls: List[HornLiteral] = result._1
            hornLiterals = hornLiterals ++ hls
        }

        /*
        println("List of literals returned for rule " + rule)
        for (hl <- hornLiterals) {
            println(hl)
        }
        println()
        */


        val headPredicate = rule.predicate_.asInstanceOf[prolog.Absyn.Predicate]
        if (headPredicate.isInstanceOf[prolog.Absyn.APred]) {
            hornLiterals = hornLiterals ++ headPredicate.asInstanceOf[prolog.Absyn.APred].accept(this, u)._1
        } else if (headPredicate.isInstanceOf[prolog.Absyn.CPred]) {
            hornLiterals = hornLiterals ++ headPredicate.asInstanceOf[prolog.Absyn.CPred].accept(this, u)._1
        }

        (hornLiterals, "", new Expression())
    }

    override def visit(query: prolog.Absyn.Query, u: Unit) = {
        var hornLiterals = List[HornLiteral]()

        for (i <- 0 until query.listpredicate_.size()) {
            val predicate = query.listpredicate_.get(i)
            var result = leaf(u)
            if (predicate.isInstanceOf[prolog.Absyn.APred]) {
                result = predicate.asInstanceOf[prolog.Absyn.APred].accept(this, u)
            } else if (predicate.isInstanceOf[prolog.Absyn.CPred]) {
                result = predicate.asInstanceOf[prolog.Absyn.CPred].accept(this, u)
            } else if (predicate.isInstanceOf[prolog.Absyn.EPred]) {
                result = predicate.asInstanceOf[prolog.Absyn.EPred].accept(this, u)
            }
            val hls: List[HornLiteral] = result._1
            hornLiterals = hornLiterals ++ hls
        }

        /*
        println("List of literals returned for query")
        for (hl <- hornLiterals) {
            println(hl)
        }
        */

        (hornLiterals, "", new Expression())
    }

    override def visit(eq: prolog.Absyn.EqExpr, u: Unit) = {
        val left: Expression = eq.expr_1.accept(this, u)._3
        val right: Expression = eq.expr_2.accept(this, u)._3
        val expr = new BinaryExpression(left, EqualityOp(), right)
        (List[HornLiteral](new Interp(expr)), "", expr)
    }

    override def visit(neq: prolog.Absyn.NeqExpr, u: Unit) = {
        val left: Expression = neq.expr_1.accept(this, u)._3
        val right: Expression = neq.expr_2.accept(this, u)._3
        val expr = new BinaryExpression(left, InequalityOp(), right)
        (List[HornLiteral](new Interp(expr)), "", expr)
    }

    override def visit(gt: prolog.Absyn.GtExpr, u: Unit) = {
        val left: Expression = gt.expr_1.accept(this, u)._3
        val right: Expression = gt.expr_2.accept(this, u)._3
        val expr = new BinaryExpression(left, GreaterThanOp(), right)
        (List[HornLiteral](new Interp(expr)), "", expr)
    }

    override def visit(lt: prolog.Absyn.LtExpr, u: Unit) = {
        val left: Expression = lt.expr_1.accept(this, u)._3
        val right: Expression = lt.expr_2.accept(this, u)._3
        val expr = new BinaryExpression(left, LessThanOp(), right)
        (List[HornLiteral](new Interp(expr)), "", expr)
    }

    override def visit(geq: prolog.Absyn.GeqExpr, u: Unit) = {
        val left_result = geq.expr_1.accept(this, u)._3
        val right_result = geq.expr_2.accept(this, u)._3

        val left: Expression = ADTsel(adt, "value", List(left_result))
        val right: Expression = ADTsel(adt, "value", List(right_result))
        
        val force_int_left = ADTtest(adt, 0, left_result)
        val force_int_right = ADTtest(adt, 0, right_result)
        val eq1 = BinaryExpression(force_int_left, EqualityOp(), NumericalConst(BigInt(anIntIdx)))
        val eq2 = BinaryExpression(force_int_right, EqualityOp(), NumericalConst(BigInt(anIntIdx)))


        val conj = new BinaryExpression(eq1, ConjunctionOp(), eq2)

        val result = new BinaryExpression(conj, ConjunctionOp(), new BinaryExpression(left, GreaterThanEqualOp(), right))

        // val expr = ADTctor(adt, "anInt", List(result))
        (List[HornLiteral](new Interp(result)), "", result)
    }

    override def visit(leq: prolog.Absyn.LeqExpr, u: Unit) = {
        val left: Expression = leq.expr_1.accept(this, u)._3
        val right: Expression = leq.expr_2.accept(this, u)._3
        val expr = new BinaryExpression(left, LessThanEqualOp(), right)
        (List[HornLiteral](new Interp(expr)), "", expr)
    }

    override def visit(add: prolog.Absyn.AddExpr, u: Unit) = {
        val left: Expression = add.expr_1.accept(this, u)._3
        val right: Expression = add.expr_2.accept(this, u)._3
        val expr = new BinaryExpression(left, AdditionOp(), right)
        (List[HornLiteral](new Interp(expr)), "", expr)
    }

    override def visit(sub: prolog.Absyn.SubExpr, u: Unit) = {
        val left: Expression = sub.expr_1.accept(this, u)._3
        val right: Expression = sub.expr_2.accept(this, u)._3
        val expr = new BinaryExpression(left, SubtractionOp(), right)
        (List[HornLiteral](new Interp(expr)), "", expr)
    }

    override def visit(mult: prolog.Absyn.MultExpr, u: Unit) = {
        val left: Expression = mult.expr_1.accept(this, u)._3
        val right: Expression = mult.expr_2.accept(this, u)._3
        val expr = new BinaryExpression(left, MultiplicationOp(), right)
        (List[HornLiteral](new Interp(expr)), "", expr)
    }

    override def visit(div: prolog.Absyn.DivExpr, u: Unit) = {
        val left: Expression = div.expr_1.accept(this, u)._3
        val right: Expression = div.expr_2.accept(this, u)._3
        val expr = new BinaryExpression(left, DivisionOp(), right)
        (List[HornLiteral](new Interp(expr)), "", expr)
    }

    override def visit(mod: prolog.Absyn.ModExpr, u: Unit) = {
        val left: Expression = mod.expr_1.accept(this, u)._3
        val right: Expression = mod.expr_2.accept(this, u)._3
        val expr = new BinaryExpression(left, ModuloOp(), right)
        (List[HornLiteral](new Interp(expr)), "", expr)
    }
    
    override def visit(num: prolog.Absyn.NumExpr, u: Unit) = {
        println("anInt is " + anInt)
        
        val expr = new NumericalConst(BigInt(num.num_))
        val tmp = ADTctor(adt, "anInt", List(expr))
        // (List[HornLiteral](new Interp(expr)), "", expr)
        (List[HornLiteral](), "", tmp)
        // We would like to return anInt(expr)
    }

    override def visit(ve: prolog.Absyn.VarExpr, u: Unit) = {
        val expr = new Variable(ve.uident_).stype(new AdtType(usort))
        (List[HornLiteral](new Interp(expr)), "", expr)
    }

    
}
