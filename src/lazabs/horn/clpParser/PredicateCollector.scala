package prolog

class PredicateCollector extends FoldVisitor[List[(String, Int)], Unit] {

    def combine(a: List[(String, Int)], b: List[(String, Int)], u: Unit) = (a ++ b).distinct
    def leaf(u: Unit) = List[(String, Int)]()

    override def visit(p: prolog.Absyn.Atm, u: Unit) = {
        List[(String, Int)](p.lident_ -> 0)
    }

    override def visit(p: prolog.Absyn.EAtm, u: Unit) = {
        List[(String, Int)](p.ident_ -> 0)
    }

    override def visit(p: prolog.Absyn.CPred, u: Unit) = {
        var result = leaf(u)
        val atm = p.atom_
        if (atm.isInstanceOf[prolog.Absyn.Atm]) {
            val name = atm.asInstanceOf[prolog.Absyn.Atm].lident_
            result = List[(String, Int)](name -> p.listterm_.size())
        } else if (atm.isInstanceOf[prolog.Absyn.EAtm]) {
            val name = atm.asInstanceOf[prolog.Absyn.EAtm].ident_
            result = List[(String, Int)](name -> p.listterm_.size())
        } else {
            throw new RuntimeException("Unknown atom type: " + atm)
        }
        result
    }

}
