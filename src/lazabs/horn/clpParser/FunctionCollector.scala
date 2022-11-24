package prolog

class FunctionCollector extends FoldVisitor[List[(String, Int)], Unit] {

    def combine(a: List[(String, Int)], b: List[(String, Int)], u: Unit) = a ++ b
    def leaf(u: Unit) = List[(String, Int)]()

    override def visit(p: prolog.Absyn.Complex, u: Unit) = {
        var result = leaf(u)
        for (i <- 0 until p.listterm_.size()) {
            result = combine(result, p.listterm_.get(i).accept(this, u), u)
        }
        val atm = p.atom_
        if (atm.isInstanceOf[prolog.Absyn.Atm]) {
            val name = atm.asInstanceOf[prolog.Absyn.Atm].lident_
            result =  combine(result, List[(String, Int)](name -> p.listterm_.size()), u)
        } else if (atm.isInstanceOf[prolog.Absyn.EAtm]) {
            val name = atm.asInstanceOf[prolog.Absyn.EAtm].ident_
            result =  combine(result, List[(String, Int)](name -> p.listterm_.size()), u)
        } else {
            throw new RuntimeException("Unknown atom type: " + atm)
        }
        result
    }

}
