package prolog
import lazabs.horn.global._
import lazabs.ast.ASTree._
import ap.theories.ADT
import lazabs.types._

class ASTBuilder(adt: ADT) extends FoldVisitor[(List[HornLiteral], String), Unit] {
    def combine(a: (List[HornLiteral], String), b: (List[HornLiteral], String), u: Unit) = {
        (List[HornLiteral](), "")
    }
    def leaf(u: Unit) = {
        (List[HornLiteral](), "")
    }

    var varCount = 0
    val usort = adt.sorts.head
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
        
        (List[HornLiteral](hl), freshVar)
    }

    override def visit(atom: prolog.Absyn.EAtm, u: Unit) = {
        val atomName = atom.ident_
        val freshVar = getFreshVarName()
        val hl : HornLiteral = new Interp(
            BinaryExpression(new Variable(freshVar).stype(new AdtType(usort)), EqualityOp(), new ADTctor(adt, atomName, List()).stype(new AdtType(usort)))
        ) 
        (List[HornLiteral](hl), freshVar)
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
        (hls :+ hl, freshVar)
    }

    
    override def visit(pred: prolog.Absyn.APred, u: Unit) = {
        val atom = pred.atom_
        val relationName = getName(atom)
        val hl: HornLiteral = new RelVar(relationName, List[Parameter]()) 
        (List[HornLiteral](hl),relationName)
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
        (hls :+ hl, "")
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
            }
            val hls: List[HornLiteral] = result._1
            hornLiterals = hornLiterals ++ hls
        }

        val headPredicate = rule.predicate_.asInstanceOf[prolog.Absyn.Predicate]
        if (headPredicate.isInstanceOf[prolog.Absyn.APred]) {
            hornLiterals = hornLiterals ++ headPredicate.asInstanceOf[prolog.Absyn.APred].accept(this, u)._1
        } else if (headPredicate.isInstanceOf[prolog.Absyn.CPred]) {
            hornLiterals = hornLiterals ++ headPredicate.asInstanceOf[prolog.Absyn.CPred].accept(this, u)._1
        }

        (hornLiterals, "")
    }

}
