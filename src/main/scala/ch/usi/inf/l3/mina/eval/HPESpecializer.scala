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
    private val fevalError: String = "Blocks marked as CT shall be completely " +
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
            case _ => fail(fevalError + "  " + v)
          }
          (value, env)
        case v @ ValDef(mods, name, tpt, rhs) =>
          val (r, env2) = feval(rhs, env)
          (r, env2.addValue(v.name, r))
        case Assign(lhs, rhs) =>
          val (rhs1, env1) = feval(rhs, env)
          val env2 = env.addValue(lhs.symbol.name, rhs1)
          (rhs1, env2)
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
        // Unary operations
        case select @ Select(qual, name) if (isUnary(select)) =>
          val (r1, env1) =  feval(qual, env)

          
          val methodName = name
          doUop(methodName, r1, env1)
        // Binary operations
        case apply @ Apply(fun @ Select(r, l), args) if (isBinary(apply)) =>
          val arg1 = apply.args.head
          val (r1, env1) =  feval(r, env)
          val (arg11, env2) = feval(arg1, env1)

          val method = fun.symbol
          val methodName = method.name
          doBop(methodName, r1, arg11, env2)

        //        case apply @ Apply(fun, args) 
        //        	if(fun.symbol.owner.fullName == "class Int"
        //        	  && fun.symbol.fullName == "+") =>
        //          val method = fun.symbol
        //          val (fevaledArgs, env1) = fevalArgs(args, env)
        //          val v = fevaledArgs match {
        //            case x :: Nil => 
        //            case _ => fail(fevalError)
        //          }
        //          (v, env1)
        case apply @ Apply(fun, args) =>
          val reciever = fun.symbol.owner.tpe
          digraph.getClassRepr(reciever) match {
            case Some(clazz) =>
              val method = fun.symbol
              val methodTree = tree2Method(clazz.getMemberTree(method.name, method.tpe))
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

    private implicit def tree2Literal(t: Tree): Literal = {
      t match {
        case x: Literal => x
        case _ => fail(s"${t} is not a Literal")
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

    private def isUnary(select: Select): Boolean = {
      val rcvr = select.symbol.owner.tpe
      val c = isAnyVal(rcvr)
      val methodName = select.name
      if (c && isUop(methodName)) {
        true
      } else false
    }
    
    private def isBinary(apply: Apply): Boolean = {
      isBinary(apply, apply.args.size == 1, isBop)
    }
    private def isBinary(apply: Apply, check: Boolean,
        f: TermName => Boolean ): Boolean = {
      val args = apply.args
      val fun = apply.fun
      val rcvr = fun.symbol.owner.tpe
      val c = isAnyVal(rcvr)
      val method = fun.symbol
      val methodName = method.name
      if (c && check && f(methodName)) {
        true
      } else false
    }

    private def isAnyVal(tpe: Type) = {
      if (tpe <:< definitions.BooleanClass.tpe ||
        tpe <:< definitions.ByteClass.tpe ||
        tpe <:< definitions.ShortClass.tpe ||
        tpe <:< definitions.IntClass.tpe ||
        tpe <:< definitions.LongClass.tpe ||
        tpe <:< definitions.DoubleClass.tpe ||
        tpe <:< definitions.FloatClass.tpe ||
        tpe <:< definitions.CharClass.tpe ||
        tpe <:< definitions.StringClass.tpe) true
      else false
    }
    
    private def isUop(name: TermName): Boolean = {
      name match {
        case nme.UNARY_~ | nme.UNARY_+ | nme.UNARY_- | nme.UNARY_! => true
        case _ => false
      }
    }
    
    private def isBop(name: TermName): Boolean = {
      name match {
        case nme.OR | nme.XOR | nme.AND | nme.EQ | nme.NE | nme.ADD |
          nme.SUB | nme.MUL | nme.DIV | nme.MOD | nme.LSL | nme.LSR |
          nme.ASR | nme.LT | nme.LE | nme.GE | nme.GT | nme.ZOR |
          nme.ZAND | nme.MINUS | nme.PLUS => true
        case _ => false
      }
    }
    
    private def toVal(lit: Literal): Any = {
      val v = lit.value
      if(lit.tpe <:< definitions.BooleanClass.tpe) v.booleanValue
      else if(lit.tpe <:< definitions.ByteClass.tpe) v.byteValue
      else if(lit.tpe <:< definitions.ShortClass.tpe) v.shortValue
      else if(lit.tpe <:< definitions.IntClass.tpe) v.intValue
      else if(lit.tpe <:< definitions.LongClass.tpe) v.longValue
      else if(lit.tpe <:< definitions.FloatClass.tpe) v.floatValue
      else if(lit.tpe <:< definitions.DoubleClass.tpe) v.doubleValue
      else if(lit.tpe <:< definitions.CharClass.tpe) v.charValue
      else if(lit.tpe <:< definitions.StringClass.tpe) v.stringValue
      else fail(s"${lit.tpe} is not a builtin value class")
    }

    private def doUop(methodName: TermName, v: CTValue, env: Environment):
    	(CTValue, Environment) = {
      v.value match {
        case Some(HPELiteral(x, _)) =>
          val x1 = toVal(x)
          val lit = doUop(x1, methodName)
          val tlit = typeTree(lit)
          val r = CTValue(HPELiteral(tlit, tlit.tpe))
          (r, env)
        case _ => fail(fevalError)
      }
    }
    private def doBop(methodName: TermName, v1: CTValue,
      v2: CTValue, env: Environment): (CTValue, Environment) = {
      (v1.value, v2.value) match {
        case (Some(HPELiteral(x, _)), Some(HPELiteral(y, _))) =>
          //println(x.intValu + "   " + y.value.)
          val x1 = toVal(x)
          val y1 = toVal(y)
          val lit = doBop(x1, y1, methodName)
          val tlit = typeTree(lit)
          val r = CTValue(HPELiteral(tlit, tlit.tpe))
          (r, env)
        case _ => fail(fevalError)
      }
    }
    
    private def doUop(x: Boolean, name: TermName): Literal = {
      name match {
        case nme.UNARY_! => Literal(Constant(x.unary_!))
        case _ => fail(s"${name} is not a binary operation")
      }
    }
    
    private def doUop(x: Byte, name: TermName): Literal = {
      name match {
        case nme.UNARY_~ => Literal(Constant(x.unary_~))
        case nme.UNARY_+ => Literal(Constant(x.unary_+))
        case nme.UNARY_- => Literal(Constant(x.unary_-))
        case _ => fail(s"${name} is not a binary operation")
      }
    }
    
    private def doUop(x: Short, name: TermName): Literal = {
      name match {
        case nme.UNARY_~ => Literal(Constant(x.unary_~))
        case nme.UNARY_+ => Literal(Constant(x.unary_+))
        case nme.UNARY_- => Literal(Constant(x.unary_-))
        case _ => fail(s"${name} is not a binary operation")
      }
    }
    
    private def doUop(x: Int, name: TermName): Literal = {
      name match {
        case nme.UNARY_~ => Literal(Constant(x.unary_~))
        case nme.UNARY_+ => Literal(Constant(x.unary_+))
        case nme.UNARY_- => Literal(Constant(x.unary_-))
        case _ => fail(s"${name} is not a binary operation")
      }
    }
    
    private def doUop(x: Long, name: TermName): Literal = {
      name match {
        case nme.UNARY_~ => Literal(Constant(x.unary_~))
        case nme.UNARY_+ => Literal(Constant(x.unary_+))
        case nme.UNARY_- => Literal(Constant(x.unary_-))
        case _ => fail(s"${name} is not a binary operation")
      }
    }
    
    private def doUop(x: Float, name: TermName): Literal = {
      name match {
        case nme.UNARY_+ => Literal(Constant(x.unary_+))
        case nme.UNARY_- => Literal(Constant(x.unary_-))
        case _ => fail(s"${name} is not a binary operation")
      }
    }
    
    private def doUop(x: Double, name: TermName): Literal = {
      name match {
        case nme.UNARY_+ => Literal(Constant(x.unary_+))
        case nme.UNARY_- => Literal(Constant(x.unary_-))
        case _ => fail(s"${name} is not a binary operation")
      }
    }
    
    private def doUop(x: Char, name: TermName): Literal = {
      name match {
        case nme.UNARY_~ => Literal(Constant(x.unary_~))
        case nme.UNARY_+ => Literal(Constant(x.unary_+))
        case nme.UNARY_- => Literal(Constant(x.unary_-))
        case _ => fail(s"${name} is not a binary operation")
      }
    }
    
     private def doUop(v: Any, name: TermName): Literal = {
      v match {
        case x: Boolean => doUop(x, name)
        case x: Byte => doUop(x, name)
        case x: Short => doUop(x, name)
        case x: Int => doUop(x, name)
        case x: Long => doUop(x, name)
        case x: Float => doUop(x, name)
        case x: Double => doUop(x, name)
        case x: Char => doUop(x, name)
        case _ =>
          fail(s"${name} is not a binary operation of " +
          		"${fst.getClass} and ${snd.getClass}")
      }
    }
    
    private def doBop(fst: Boolean, snd: Boolean, name: TermName): Literal = {
      name match {
        case nme.OR => Literal(Constant(fst | snd))
        case nme.XOR => Literal(Constant(fst ^ snd))
        case nme.AND => Literal(Constant(fst & snd))
        case nme.EQ => Literal(Constant(fst == snd))
        case nme.NE => Literal(Constant(fst != snd))
        case nme.LT => Literal(Constant(fst < snd))
        case nme.LE => Literal(Constant(fst <= snd))
        case nme.GE => Literal(Constant(fst > snd))
        case nme.GT => Literal(Constant(fst >= snd))
        case nme.ZOR => Literal(Constant(fst || snd))
        case nme.ZAND => Literal(Constant(fst && snd))
        case _ => fail(s"${name} is not a binary operation")
      }
    }
    private def doBop(fst: String, snd: String, name: TermName): Literal = {
      name match {
        case nme.EQ => Literal(Constant(fst == snd))
        case nme.NE => Literal(Constant(fst != snd))
        case nme.ADD | nme.PLUS => Literal(Constant(fst + snd))
        case nme.LT => Literal(Constant(fst < snd))
        case nme.LE => Literal(Constant(fst <= snd))
        case nme.GE => Literal(Constant(fst > snd))
        case nme.GT => Literal(Constant(fst >= snd))
        case _ => fail(s"${name} is not a binary operation")
      }
    }
    private def doBop(fst: Float, snd: Float, name: TermName): Literal = {
      name match {
        case nme.EQ => Literal(Constant(fst == snd))
        case nme.NE => Literal(Constant(fst != snd))
        case nme.ADD | nme.PLUS => Literal(Constant(fst + snd))
        case nme.SUB | nme.MINUS => Literal(Constant(fst - snd))
        case nme.MUL => Literal(Constant(fst * snd))
        case nme.DIV => Literal(Constant(fst / snd))
        case nme.MOD => Literal(Constant(fst % snd))
        case nme.LT => Literal(Constant(fst < snd))
        case nme.LE => Literal(Constant(fst <= snd))
        case nme.GE => Literal(Constant(fst > snd))
        case nme.GT => Literal(Constant(fst >= snd))
        case _ => fail(s"${name} is not a binary operation")
      }
    }
    private def doBop(fst: Double, snd: Double, name: TermName): Literal = {
      name match {
        case nme.EQ => Literal(Constant(fst == snd))
        case nme.NE => Literal(Constant(fst != snd))
        case nme.ADD | nme.PLUS => Literal(Constant(fst + snd))
        case nme.SUB | nme.MINUS => Literal(Constant(fst - snd))
        case nme.MUL => Literal(Constant(fst * snd))
        case nme.DIV => Literal(Constant(fst / snd))
        case nme.MOD => Literal(Constant(fst % snd))
        case nme.LT => Literal(Constant(fst < snd))
        case nme.LE => Literal(Constant(fst <= snd))
        case nme.GE => Literal(Constant(fst > snd))
        case nme.GT => Literal(Constant(fst >= snd))
        case _ => fail(s"${name} is not a binary operation")
      }
    }
    private def doBop(fst: Byte, snd: Byte, name: TermName): Literal = {
      name match {
        case nme.OR => Literal(Constant(fst | snd))
        case nme.XOR => Literal(Constant(fst ^ snd))
        case nme.AND => Literal(Constant(fst & snd))
        case nme.EQ => Literal(Constant(fst == snd))
        case nme.NE => Literal(Constant(fst != snd))
        case nme.ADD | nme.PLUS => Literal(Constant(fst + snd))
        case nme.SUB | nme.MINUS => Literal(Constant(fst - snd))
        case nme.MUL => Literal(Constant(fst * snd))
        case nme.DIV => Literal(Constant(fst / snd))
        case nme.MOD => Literal(Constant(fst % snd))
        case nme.LSL => Literal(Constant(fst << snd))
        case nme.LSR => Literal(Constant(fst >>> snd))
        case nme.ASR => Literal(Constant(fst >> snd))
        case nme.LT => Literal(Constant(fst < snd))
        case nme.LE => Literal(Constant(fst <= snd))
        case nme.GE => Literal(Constant(fst > snd))
        case nme.GT => Literal(Constant(fst >= snd))
        case _ => fail(s"${name} is not a binary operation")
      }
    }
    private def doBop(fst: Short, snd: Short, name: TermName): Literal = {
      name match {
        case nme.OR => Literal(Constant(fst | snd))
        case nme.XOR => Literal(Constant(fst ^ snd))
        case nme.AND => Literal(Constant(fst & snd))
        case nme.EQ => Literal(Constant(fst == snd))
        case nme.NE => Literal(Constant(fst != snd))
        case nme.ADD | nme.PLUS => Literal(Constant(fst + snd))
        case nme.SUB | nme.MINUS => Literal(Constant(fst - snd))
        case nme.MUL => Literal(Constant(fst * snd))
        case nme.DIV => Literal(Constant(fst / snd))
        case nme.MOD => Literal(Constant(fst % snd))
        case nme.LSL => Literal(Constant(fst << snd))
        case nme.LSR => Literal(Constant(fst >>> snd))
        case nme.ASR => Literal(Constant(fst >> snd))
        case nme.LT => Literal(Constant(fst < snd))
        case nme.LE => Literal(Constant(fst <= snd))
        case nme.GE => Literal(Constant(fst > snd))
        case nme.GT => Literal(Constant(fst >= snd))
        case _ => fail(s"${name} is not a binary operation")
      }
    }
    private def doBop(fst: Long, snd: Long, name: TermName): Literal = {
      name match {
        case nme.OR => Literal(Constant(fst | snd))
        case nme.XOR => Literal(Constant(fst ^ snd))
        case nme.AND => Literal(Constant(fst & snd))
        case nme.EQ => Literal(Constant(fst == snd))
        case nme.NE => Literal(Constant(fst != snd))
        case nme.ADD | nme.PLUS => Literal(Constant(fst + snd))
        case nme.SUB | nme.MINUS => Literal(Constant(fst - snd))
        case nme.MUL => Literal(Constant(fst * snd))
        case nme.DIV => Literal(Constant(fst / snd))
        case nme.MOD => Literal(Constant(fst % snd))
        case nme.LSL => Literal(Constant(fst << snd))
        case nme.LSR => Literal(Constant(fst >>> snd))
        case nme.ASR => Literal(Constant(fst >> snd))
        case nme.LT => Literal(Constant(fst < snd))
        case nme.LE => Literal(Constant(fst <= snd))
        case nme.GE => Literal(Constant(fst > snd))
        case nme.GT => Literal(Constant(fst >= snd))
        case _ => fail(s"${name} is not a binary operation")
      }
    }
    private def doBop(fst: Int, snd: Int, name: TermName): Literal = {
      name match {
        case nme.OR => Literal(Constant(fst | snd))
        case nme.XOR => Literal(Constant(fst ^ snd))
        case nme.AND => Literal(Constant(fst & snd))
        case nme.EQ => Literal(Constant(fst == snd))
        case nme.NE => Literal(Constant(fst != snd))
        case nme.ADD | nme.PLUS => Literal(Constant(fst + snd))
        case nme.SUB | nme.MINUS => Literal(Constant(fst - snd))
        case nme.MUL => Literal(Constant(fst * snd))
        case nme.DIV => Literal(Constant(fst / snd))
        case nme.MOD => Literal(Constant(fst % snd))
        case nme.LSL => Literal(Constant(fst << snd))
        case nme.LSR => Literal(Constant(fst >>> snd))
        case nme.ASR => Literal(Constant(fst >> snd))
        case nme.LT => Literal(Constant(fst < snd))
        case nme.LE => Literal(Constant(fst <= snd))
        case nme.GE => Literal(Constant(fst > snd))
        case nme.GT => Literal(Constant(fst >= snd))
        case _ => fail(s"${name} is not a binary operation")
      }
    }
    private def doBop(fst: Any, snd: Any, name: TermName): Literal = {
      (fst, snd) match {
        case (x: String, y) => doBop(x, y.toString, name)
        case (y, x: String) => doBop(x, y.toString, name)
        case (y, x: Double) => doBop(x, y.asInstanceOf[Double], name)
        case (x: Double, y) => doBop(x, y.asInstanceOf[Double], name)
        case (y, x: Float) => doBop(x, y.asInstanceOf[Float], name)
        case (x: Float, y) => doBop(x, y.asInstanceOf[Float], name)
        case (y, x: Long) => doBop(x, y.asInstanceOf[Long], name)
        case (x: Long, y) => doBop(x, y.asInstanceOf[Long], name)
        case (y, x: Int) => doBop(x, y.asInstanceOf[Int], name)
        case (x: Int, y) => doBop(x, y.asInstanceOf[Int], name)
        case (y, x: Short) => doBop(x, y.asInstanceOf[Short], name)
        case (x: Short, y) => doBop(x, y.asInstanceOf[Short], name)
        case (y, x: Byte) => doBop(x, y.asInstanceOf[Byte], name)
        case (x: Byte, y) => doBop(x, y.asInstanceOf[Byte], name)
        case (y, x: Boolean) => doBop(x, y.asInstanceOf[Boolean], name)
        case (x: Boolean, y) => doBop(x, y.asInstanceOf[Boolean], name)
        case (y, x: Char) => doBop(x, y.asInstanceOf[Char], name)
        case (x: Char, y) => doBop(x, y.asInstanceOf[Char], name)
        case (_, _) =>
          fail(s"${name} is not a binary operation of " +
          		"${fst.getClass} and ${snd.getClass}")
      }
    }
    private def doBop(fst: Char, snd: Char, name: TermName): Literal = {
      name match {
        case nme.OR => Literal(Constant(fst | snd))
        case nme.XOR => Literal(Constant(fst ^ snd))
        case nme.AND => Literal(Constant(fst & snd))
        case nme.EQ => Literal(Constant(fst == snd))
        case nme.NE => Literal(Constant(fst != snd))
        case nme.ADD | nme.PLUS => Literal(Constant(fst + snd))
        case nme.SUB | nme.MINUS => Literal(Constant(fst - snd))
        case nme.MUL => Literal(Constant(fst * snd))
        case nme.DIV => Literal(Constant(fst / snd))
        case nme.MOD => Literal(Constant(fst % snd))
        case nme.LSL => Literal(Constant(fst << snd))
        case nme.LSR => Literal(Constant(fst >>> snd))
        case nme.ASR => Literal(Constant(fst >> snd))
        case nme.LT => Literal(Constant(fst < snd))
        case nme.LE => Literal(Constant(fst <= snd))
        case nme.GE => Literal(Constant(fst > snd))
        case nme.GT => Literal(Constant(fst >= snd))
        case _ => fail(s"${name} is not a binary operation")
      }
    }
    
    //    private def doBop(fst: Int, snd: Int, name: TermName): Literal = {
    //      name match {
    //        case nme.OR => Literal(Constant(fst | snd))
    //        case nme.XOR => Literal(Constant(fst ^ snd))
    //        case nme.AND => Literal(Constant(fst & snd))
    //        case nme.EQ => Literal(Constant(fst == snd))
    //        case nme.NE => Literal(Constant(fst != snd))
    //        case nme.ADD | nme.PLUS => Literal(Constant(fst + snd))
    //        case nme.SUB | nme.MINUS => Literal(Constant(fst - snd))
    //        case nme.MUL => Literal(Constant(fst * snd))
    //        case nme.DIV => Literal(Constant(fst / snd))
    //        case nme.MOD => Literal(Constant(fst % snd))
    //        case nme.LSL => Literal(Constant(fst << snd))
    //        case nme.LSR => Literal(Constant(fst >>> snd))
    //        case nme.ASR => Literal(Constant(fst >> snd))
    //        case nme.LT => Literal(Constant(fst < snd))
    //        case nme.LE => Literal(Constant(fst <= snd))
    //        case nme.GE => Literal(Constant(fst > snd))
    //        case nme.GT => Literal(Constant(fst >= snd))
    //        case nme.ZOR => Literal(Constant(fst || snd))
    //        case nme.ZAND => Literal(Constant(fst && snd))
    //        case _ => fail(s"${name} is not a binary operation")
    //      }
    //    }
  }
}
  
