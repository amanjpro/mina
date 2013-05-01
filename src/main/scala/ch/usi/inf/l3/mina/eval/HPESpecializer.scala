/*
 * Copyright (c) <2013>, Amanj Sherwany <http://www.amanj.me>
 * All rights reserved.
 * */
package ch.usi.inf.l3.mina.eval

import scala.tools.nsc.Global
import scala.tools.nsc.ast.TreeDSL
import scala.tools.nsc.plugins.Plugin
import scala.tools.nsc.plugins.PluginComponent
import scala.tools.nsc.transform.Transform
import scala.tools.nsc.transform.TypingTransformers
import scala.tools.nsc.ast.parser.TreeBuilder
import scala.reflect.runtime.universe._
import scala.language.implicitConversions
import ch.usi.inf.l3.mina._

class HPESpecializer(val hpe: HPE) extends PluginComponent
  with Transform
  with TypingTransformers
  with TreeDSL {

  val global: hpe.global.type = hpe.global
  val runsAfter = List[String](hpe.finder)
  override val runsBefore = List[String](hpe.finalizer)
  val phaseName = hpe.specializer

  import global._
  import hpe._

  def newTransformer(unit: CompilationUnit) = new HPETransformer(unit)

  class HPETransformer(unit: CompilationUnit)
    extends TypingTransformer(unit) {

//    import CODE._
    override def transform(tree: Tree): Tree = {
      //        var newTree: Tree = tree match {
      //          case cd @ ClassDef(mods, className, tparams, impl) => //if(cd.symbol.isClass)=>
      //            val newBody = impl.body.flatMap(_ match {
      //              case vd @ ValDef(mod, name, tpt, rhs) =>
      //                val scalaTypeName = newTermName("scala")
      //                val scalaIdent = Ident(scalaTypeName)
      //                val predefTermName = newTermName("Predef")
      //                val predefSelect = Select(scalaIdent, predefTermName)
      //                val printlnSelect = Select(predefSelect, newTermName("println"))
      //                val applyPrint = Apply(printlnSelect, List(Literal(Constant("Hello"))))
      //                List(applyPrint, vd) // :: Nil
      //              case x => List(x) // :: Nil
      //            })
      //            treeCopy.ClassDef(tree, mods, className, tparams, treeCopy.Template(
      //              impl, impl.parents, impl.self, newBody))
      //          case _ => tree
      //        }
      //Partially evaluate the program!
      val (newTree, _, env2) = peval(tree, env)
      env = env2
      super.transform(newTree)
    }

    def typeTree(tree: Tree): Tree = {
      localTyper.typed { tree }
    }
    private val fevalError: String = "Blocks marked as CT shall be completely "+ 
        							"known and available at compilation time."

    /*
     * In order to know about a tree, write it in Scala and run the scalac
     * using this command:
     * scalac -Yshow-trees -Xprint:parser YOURPROGRAM
     * 
     */
    private def feval(tree: Tree, env: Environment): (CTValue, Environment) = {
      tree match {
        case v: Literal => (CTValue(HPELiteral(v, v.tpe)), env)
        case v: Ident =>
          val value: CTValue = env.getValue(v.name) match {
            case x: CTValue => x
            case _ => fail(fevalError + "  " +  v)
          }
          (value, env)
        case v @ ValDef(mods, name, tpt, rhs) =>
          val (r, env2) = feval(rhs, env)
          (r, env2.addValue(v.name, r))
        case Assign(lhs, rhs) =>
          val (rhs1, env1) = feval(rhs, env)
          val env2 = env.addValue(lhs.symbol.name, rhs1)
          (rhs1, env2)
        //TODO what about binary operations?
        case Block(stats, expr) =>
          var env2 = env
          var tail = stats

          while (tail != Nil) {
            val head = tail.head
            val (_, envTemp) = feval(head, env2)
            env2 = envTemp
            tail = tail.tail
          }
          feval(expr, env2)
        case If(cond, thenp, elsep) =>
          val (cond1, env1) = feval(cond, env)
          hpeAny2Tree(cond1.value) match {
            case Literal(Constant(true)) => feval(thenp, env1)
            case Literal(Constant(false)) => feval(elsep, env1)
            case _ => fail(fevalError)
          }

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
        case apply @ Apply(fun, args) =>
          val reciever = fun.symbol.owner
          digraph.getClassRepr(reciever) match {
            case Some(clazz) =>
              val method = fun.symbol
              val methodTree = tree2Method(clazz.getMemberTree(method))
              val (fevaledArgs, env1) = fevalArgs(args, env)
              val params = methodTree.vparamss.flatten.map(_.name)
              val funStore = env.newStore((params, fevaledArgs))
              val (v, _) = feval(methodTree.rhs, funStore)
              (v, env1)
            case None => 
              fail(fevalError + fun + "   " + reciever)
          }
          //            val result: CTValue = methodSymbol(fun) match {
          //              case None => fail(s"""Couldn't find the applied method call 
          //                                   |${apply}""")
          //              case Some(symbol) =>
          //                val (fevaledArgs, env1) = fevalArgs(args, env)
          //                val params = DEF(symbol).vparamss.flatten
          //                val paramNames = for(param <- params) yield param.name
          //                val funStore = env.newStore((paramNames, fevaledArgs))
          //                // TODO find a way to find the applied functions!
          //                feval(fun, funStore)._1
          //            }
          
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

    def peval(tree: Tree, env: Environment): (Tree, Value, Environment) = {
      tree match {
        case clazz @ ClassDef(mods, name, tparams, impl) =>
//          val c = processClass(clazz, env)
          (clazz, Top, env)
        case method @ DefDef(mods, name, tparams, vparamss, tpt, rhs) =>
          val (rhs1, _, temp) = peval(rhs, env)
          val newMethod = typeTree(treeCopy.DefDef(method, mods, name, tparams,
            vparamss, tpt, rhs1))
          (newMethod, Top, temp)
        case v: Literal =>
          (v, AbsValue(HPELiteral(v, v.tpe)), env)
        case v: Ident =>
          val value = env.getValue(v.name)
          val t: Tree = value match {
            case AbsValue(_) | CTValue(_) => value.value
            case _ => v
          }
          (t, value, env)
        case v @ ValDef(mods, name, tpt, rhs) if (!rhs.isEmpty) =>
          // We won't partially evaluate method parameters and 
          // uninitialized (val/var)s
          val (rtree, r, env2) = peval(rhs, env)
          val treeToCopy = typeTree(treeCopy.ValDef(v, mods, name, tpt, rtree))
          (treeToCopy, r, env2.addValue(v.name, r))
        case a @ Assign(lhs, rhs) =>
          val (rtree, rhs1, env1) = peval(rhs, env)
          val env2 = env.addValue(lhs.symbol.name, rhs1)
          (typeTree(treeCopy.Assign(a, lhs, rtree)), rhs1, env2)
        //TODO change this newTermName to TermName when Scala will have it
        case Apply(fun, t) if (fun.symbol.name == newTermName("CT")) =>
          val (v, env2) = feval(t.head, env)
          (v.value, v, env2)
        //(tree, Top, env)
        case Apply(i, _) =>
          (tree, Top, env)
        case _ => (tree, Top, env)
      }
    }

    private def methodSymbol(fun: Tree): Option[MethodSymbol] = {
      val symb = fun.symbol
      symb.isMethod match {
        case true => Some(symb.asMethod)
        case false => None
      }

      //        fun match {
      //          case This(name) =>
      //          case Select(qual, name) => 
      //          case TypeApply(fun, targs) =>
      //          case _ =>
      //        }
    }
    private def fevalArgs(args: List[Tree], store: Environment): (List[CTValue], Environment) = {
      var fevaled: List[CTValue] = Nil
      var env = store
      var tail = args
      var head = args.head
      while (tail != Nil) {
        val (arg1, temp) = feval(head, env)
        fevaled = arg1 :: fevaled
        env = temp
        head = tail.head
        tail = tail.tail
      }
      (fevaled.reverse, env)
    }

    private def fail(msg: String): Nothing = {
      throw new HPEError(msg)
    }

    private implicit def zip2Lists(list: (List[TermName], List[Value])): List[(TermName, Value)] = {
      list._1 zip list._2
    }

//    private def processClass(cdef: ClassDef, env: Environment): ClassRepr = {
//      var clazz = new ClassRepr(cdef.symbol)
//      var env2 = env
//      def processClassAux(t: Tree): Unit = {
//        t match {
//          case v @ ValDef(mods, name, tpt, rhs) =>
//            val (vprime, _, temp) = peval(v, env)
//            env2 = temp
//            clazz.addField(name, tree2Field(vprime))
//          case m @ DefDef(mods, name, tparams, vparamss, tpt, rhs) =>
//            val (mprime, _, temp) = peval(m, env)
//            env2 = temp
//            clazz.addMethod(name, tree2Method(mprime))
//          case _ =>
//        }
//      }
//
//      cdef.foreach(processClassAux(_))
//
//      var cbody = cdef.impl.body
//      var newBody: List[Tree] = Nil
//      while (cbody != Nil) {
//        val head = cbody.head
//        if (clazz.hasMember(head.symbol.name))
//          newBody = clazz.getMemberTree(head.symbol.name) :: newBody
//        else
//          newBody = head :: newBody
//        cbody = cbody.tail
//      }
//      newBody = newBody.reverse
//      val newClazz = typeTree(treeCopy.ClassDef(cdef, cdef.mods, cdef.name,
//        cdef.tparams,
//        treeCopy.Template(cdef.impl, cdef.impl.parents,
//          cdef.impl.self, newBody)))
//
//      clazz.tree = tree2Class(newClazz)
//      clazz
//    }
    private implicit def hpeAny2Tree(t: Option[HPEAny]): Tree = {
      t match {
        case Some(HPELiteral(x: Tree, _)) => x
        case Some(HPEObject(x: Tree, _, _)) => x
        case _ => typeTree(treeBuilder.makeBlock(Nil))
      }
    }

    private implicit def hpeAny2Type(t: Option[HPEAny]): Type = {
      t match {
        case Some(HPELiteral(_, x: Type)) => x
        case Some(HPEObject(_, x: Type, _)) => x
        case _ => null
      }
    }

    private implicit def tree2Field(t: Tree): ValDef = {
      t match {
        case x: ValDef => x
        case x => fail(s"Unexpected val definition ${x}")
      }
    }

    private implicit def tree2Class(t: Tree): ClassDef = {
      t match {
        case x: ClassDef => x
        case x => fail(s"Unexpected class definition ${x}")
      }
    }

    private implicit def tree2Method(t: Tree): DefDef = {
      t match {
        case x: DefDef => x
        case x => fail(s"Unexpected method definition ${x}")
      }
    }

  }
}
  
