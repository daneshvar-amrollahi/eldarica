package prolog

import lazabs.horn.global._
import java.io.{FileInputStream,InputStream,FileNotFoundException}

object CLPReader {
    def apply(fileName: String): Seq[HornClause] = {
        val in = new java.io.BufferedReader (
                 new java.io.FileReader(fileName))
        val lexer = new Yylex(in)
        val p = new parser(lexer, lexer.getSymbolFactory())
        val ast = p.pDatabase().asInstanceOf[prolog.Absyn.Db] 

        println("[Linearized Tree]")
        println(PrettyPrinter.print(ast))
        println()
        
        val v = new ComposVisitor[Unit]()
        val db = v.visit(ast, ())

        val predicateCollector = new PredicateCollector();
        val predicates = predicateCollector.visit(ast, ());
        println("Predicates Collected: " + predicates)

        val FunctionCollector = new FunctionCollector();
        val functions = FunctionCollector.visit(ast, ());
        println("Functions Collected: " + functions)

        Seq()
    }

}
