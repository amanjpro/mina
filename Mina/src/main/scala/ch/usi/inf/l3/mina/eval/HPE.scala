package ch.usi.inf.l3.mina.eval

import scala.tools.nsc.Global
import scala.tools.nsc.ast.TreeDSL
import scala.tools.nsc.plugins.Plugin
import scala.tools.nsc.plugins.PluginComponent
import scala.tools.nsc.transform.Transform
import scala.tools.nsc.transform.TypingTransformers
import ch.usi.inf.l3.mina._
import store._

class HPE(val global: Global) extends Plugin {
  import global._

  val name = "mina"
  val description = """|This is a partial evaluator plugin based on Hybrid 
    |Partial Evaluation by W. Cook and A. Shali 
    |http://www.cs.utexas.edu/~wcook/Civet/"""

  val components = List[PluginComponent](HPEComponent)

  private object HPEComponent extends PluginComponent
    with Transform
    with TypingTransformers
    with TreeDSL {

    val global: HPE.this.global.type = HPE.this.global
    val runsAfter = List[String]("parser")
    override val runsBefore = List[String]("namer")
    val phaseName = HPE.this.name

    def newTransformer(unit: CompilationUnit) = new HPETransformer(unit)

    class HPETransformer(unit: CompilationUnit)
      extends TypingTransformer(unit) {
      import CODE._
      private val fevalError: String = """|Blocks marked as CT shall be 
        						|completely known at compilation time."""

      override def transform(tree: Tree): Tree = {
        var newTree: Tree = tree match {
          case cd @ ClassDef(mods, className, tparams, impl) => //if(cd.symbol.isClass)=>
            val newBody = impl.body.flatMap(_ match {
              case vd @ ValDef(mod, name, tpt, rhs) =>
                val scalaTypeName = newTermName("scala")
                val scalaIdent = Ident(scalaTypeName)
                val predefTermName = newTermName("Predef")
                val predefSelect = Select(scalaIdent, predefTermName)
                val printlnSelect = Select(predefSelect, newTermName("println"))
                val applyPrint = Apply(printlnSelect, List(Literal(Constant("Hello"))))
                List(applyPrint, vd) // :: Nil
              case x => List(x) // :: Nil
            })
            treeCopy.ClassDef(tree, mods, className, tparams, treeCopy.Template(
              impl, impl.parents, impl.self, newBody))
          case _ => tree
        }
        super.transform(newTree)
      }

      /*
       * In order to know about a tree, write it in Scala and run the scalac
       * using this command:
       * scalac -Yshow-trees -Xprint:typer YOURPROGRAM
       * 
       */
      private def feval(tree: Tree, env: Environment): (Value, Environment) = {
        tree match {
          case v: Literal => (AbsValue(HPELiteral(v)), env)
          case v: ValDef => (env.getValue(v).get, env)
          case Assign(lhs, rhs) =>
            val (rhs1, env1) = feval(rhs, env)
            val env2 = env.addValue(lhs, rhs1)
            (rhs1, env2)
          //TODO what about binary operations?
          case Block(stats, expr) =>
            var env2 = env
            var tail = stats.tail
            var head = stats.head
            while(stats != Nil) {
              val (_, envTemp) = feval(head, env2)
              env2 = envTemp
              head = tail.head
              tail = tail.tail
            }
            feval(expr, env2)
          case If(cond, thenp, elsep) =>
            val (cond1, env1) = feval(cond, env)
            val x = cond1.value.get
            if (x == Literal(Constant(true)))
              feval(thenp, env1)
            else if (x == Literal(Constant(false)))
              feval(elsep, env1)
            else
              fail(fevalError)
//        While loops in Scala are basically nothing but an if-else conditional
//        Do we need to think about them then? The following is a while-loop tree
//          LabelDef( // def while$1(): Unit, tree.tpe=Unit
//          ()
//          If( // tree.tpe=Unit
//            Apply( // def !=(x: Int): Boolean in class Int, tree.tpe=Boolean
//              "x"."$bang$eq" // def !=(x: Int): Boolean in class Int, tree.tpe=(x: Int)Boolean
//              "y" // y: Int, tree.tpe=Int
//            )
//            Block( // tree.tpe=Unit
//              Assign( // tree.tpe=<error>
//                "y" // y: Int, tree.tpe=Int
//                Apply(
//                  "x"."$plus"
//                  "y"
//                )
//              )
//              Apply( // def while$1(): Unit, tree.tpe=Unit
//                "while$1" // def while$1(): Unit, tree.tpe=()Unit
//                Nil
//              )
//            )
//            ()
//          )
//        )
          case Apply(fun, args) =>
            
          //TODO for while loop you should be able to generate If tree
          /*
           * TODO:
           * Trees that I should care about them
           * Alternative
           * Annotated
           * AppliedTypeTree
           * Apply
           * AssignOrNamedArg
           * Bind
           * CaseDef
           * ClassDef
           * CompoundTypeTree
           * DefDef
           * ExistentialTypeTree
           * Function
           * Ident
           * Import
           * ImportSelector
           * LabelDef
           * Match
           * ModuleDef
           * New
           * PackageDef
           * ReferenceToBoxed
           * Return
           * Select
           * SelectFromTypeTree
           * SingletonTypeTree
           * Star
           * Super
           * Template
           * This
           * Throw
           * Try
           * TypeApply
           * TypeBoundsTree
           * TypeDef
           * TypeTree
           * Typed
           * UnApply
           */
        }
      }

      private def fevalArgs(args: List[Tree], store: Environment) : 
    	  (List[Value], Environment) = {
        var fevaled: List[Value] = Nil
        var env = store
        var tail = args.tail
        var head = args.head
        while(tail != Nil) {
          val (arg1, temp) = feval(head, env)
          fevaled = arg1 :: fevaled
          env = temp
          head = tail.head
          tail = tail.tail
        }
        (fevaled.reverse, env)
      }
      private def fail(msg: String): (Value, Environment) = {
        throw new HPEException(msg)
      }

    }

  }
}
