package prolog

import lazabs.horn.global._
import java.io.{FileInputStream,InputStream,FileNotFoundException}
import ap.theories.ADT
import ADT._
import lazabs.ast.ASTree._

import ap.SimpleAPI
import lazabs.horn.bottomup._
import HornClauses._
import ap.parser.IExpression._


import lazabs.types._

object CLPReader {
    def apply(fileName: String): Seq[HornClause] = {
        
        val in = new java.io.BufferedReader (
                 new java.io.FileReader(fileName))
        val lexer = new Yylex(in)
        val p = new parser(lexer, lexer.getSymbolFactory())
        val ast = p.pDatabase().asInstanceOf[prolog.Absyn.Db] 

        // println("[Linearized Tree]")
        // println(PrettyPrinter.print(ast))
        // println()
        
        val predicateCollector = new PredicateCollector();
        val predicates = predicateCollector.visit(ast, ());

        val FunctionCollector = new FunctionCollector();
        val functions = FunctionCollector.visit(ast, ());

        createClauses(predicates, functions, ast)
    }

    //hi:0, f:2
    def func(): Seq[HornClause] = {
        // // r(hi, f(X, hi)) :- q(hi, X) 
        val adt = new ADT(
            Seq("U"),
            Seq(
                ("hi", CtorSignature(Seq(), ADTSort(0))),
                ("f", CtorSignature(Seq(("f1", ADTSort(0)), ("f2", ADTSort(0))), ADTSort(0))) 
            )
        )
        
        val Seq(u) = adt.sorts
        val Seq(hi, f) = adt.constructors
        // // val Seq(_, Seq(f1, f2)) = adt.selectors
        SimpleAPI.withProver { p =>
            import p._
            val x = createConstant("x", u)
            val r = createRelation("r", Seq(u, u))
            val q = createRelation("q", Seq(u, u))
            val boz = f(x)
            val prop = (r(hi(), f(x, hi())) :- q(hi(), x))
            SimpleWrapper.solve(prop::Nil) match {
                case Left(sol) =>
                    println("sat") ; println(sol mapValues (pp(_) ) )
                case Right(cex) =>
                    println("unsat") ; println(cex)
            }
        }


        // Goal: r(hi, f(X, hi)) :- q(hi, X) 

        // q(hi, X)

        // q(Y, X), Y = hi.
        
        // r(Y, f(X, Y)) :- q(Y, X), Y = hi.

        // r(Y, Z) :- q(X, Y), Y = hi, Z = f(X, Y).
        
        // val adt = new ADT(
        //     Seq("U"),
        //     Seq(
        //         ("hi", CtorSignature(Seq(), ADTSort(0))),
        //         ("f", CtorSignature(Seq(("f1", ADTSort(0)), ("f2", ADTSort(0))), ADTSort(0))) 
        //     )
        // )

        /*
        val Seq(u) = adt.sorts
        
        println("ADT is " + adt)
        val boz = adt.constructors
        println("cons's are " + boz)


        val q: HornLiteral = new RelVar("q", List[Parameter](
                new Parameter("Y", new AdtType(u)),
                new Parameter("X", new AdtType(u)) 
            )
        ) // q(Y, X)

        // Y = hi
        val yeqhi: HornLiteral = new Interp(BinaryExpression(new Variable("Y"), EqualityOp(), new ADTctor(adt, "hi", List())))
        
        val r: HornLiteral = new RelVar("r", List[Parameter](
            new Parameter("Y", new AdtType(u)),
            new Parameter("Z", new AdtType(u))
        ))
        
        
        // Z = f(X, Y)
        val zeqf: HornLiteral = new Interp(BinaryExpression(new Variable("Z"), EqualityOp(), new ADTctor(adt, "f", List(new Variable("X"), new Variable("Y")))))
        

        val clause: HornClause = new HornClause(r, List(q, yeqhi, zeqf))
        // no head ==> new Interp(new BoolConst(false))

        Seq(clause)
        */
        Seq()
    }

    def createClauses(predicates: List[(String, Int)], functions: List[(String, Int)], database: prolog.Absyn.Db): Seq[HornClause] = {
        
        var result = Seq[HornClause]()
        
        var c = Seq[(String, CtorSignature)]()
        for (function <- functions) {
            val (name, arity) = function
            var argList = Seq[(String, ADTSort)]()
            for (i <- 1 to arity) {
                val arg = (name + "_" + i, ADTSort(0))
                argList = argList :+ arg
            }
            c = c :+ (name, CtorSignature(argList, ADTSort(0)))
        }
        c = c :+ ("anInt", CtorSignature(Seq(("value", OtherSort(Sort.Integer))) , ADTSort(0)))
        val adt = new ADT(Seq("U"), c) 

        val astBuilder = new ASTBuilder(adt)

        for (i <- 0 to database.listclause_.size() - 1) {
            val clause = database.listclause_.get(i)
            if (clause.isInstanceOf[prolog.Absyn.Fact]) {
                val fact = clause.asInstanceOf[prolog.Absyn.Fact]
                val hls = astBuilder.visit(fact, ())._1
                val head: HornLiteral = hls.last
                val body: List[HornLiteral] = hls.dropRight(1)
                result = result :+ new HornClause(head, body)

            } else if (clause.isInstanceOf[prolog.Absyn.Rule]) {
                val rule = clause.asInstanceOf[prolog.Absyn.Rule]
                val hls = astBuilder.visit(rule, ())._1
                val head: HornLiteral = hls.last
                val body: List[HornLiteral] = hls.dropRight(1)
                result = result :+ new HornClause(head, body)
            } else if (clause.isInstanceOf[prolog.Absyn.Query]) {
                val query = clause.asInstanceOf[prolog.Absyn.Query]
                val hls = astBuilder.visit(query, ())._1
                val body: List[HornLiteral] = hls
                val head: HornLiteral = new Interp(new BoolConst(false))
                result = result :+ new HornClause(head, body)
            }
        }
        result
    }
}
