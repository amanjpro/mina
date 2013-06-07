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
import scala.reflect.runtime.universe._
import scala.tools.nsc.symtab.Flags._
import scala.language.implicitConversions
import ch.usi.inf.l3.mina._

class HPESpecializer(val hpe: HPE) extends PluginComponent
  with Transform
  with TypingTransformers
  with TreeDSL {

  import CODE._
  val global: hpe.global.type = hpe.global
  override val runsRightAfter = Some(hpe.finder)
  val runsAfter = List[String](hpe.finder)
  override val runsBefore = List[String](hpe.finalizer)
  val phaseName = hpe.specializer

  import global._
  import hpe._

  def newTransformer(unit: CompilationUnit) = new HPETransformer(unit)

  class HPETransformer(unit: CompilationUnit)
    extends TypingTransformer(unit) {

    // FIXME
    // Still no support for generic methods, but supporting them will be straight forward?!
    // FIXME CT values (and variables) should not survive until runtime!
    // FIXME Apply, and Select should update the env of the variable
    override def transform(tree: Tree): Tree = {
      //Partially evaluate the program!
      val (newTree, _, env2) = peval(tree, env)
      env = env2
      super.transform(newTree)
    }

    def typeTree(tree: Tree): Tree = {
//      if(tree.symbol != null && tree.symbol != NoSymbol){
//        
//      } else 
    	  localTyper.typed { tree }
    }
    private val fevalError = "Blocks marked as CT shall be completely " +
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
          env.getValue(v.symbol.name) match {
            case x: CTValue => (x, env)
            case _ => fail(fevalError + " ident " + v)
          }
        case v @ ValDef(mods, name, tpt, rhs) =>
          val (r, env2) = feval(rhs, env)
          (r, env2.addValue(v.symbol.name, r))
        case Assign(lhs, rhs) =>
          val (rhs1, env1) = feval(rhs, env)
          (rhs1, env.addValue(lhs.symbol.name, rhs1))
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
            case _ => fail(fevalError + " if " + cond)
          }
        case m @ Match(selector, cases) =>
          def matched(cse: CaseDef, env: Environment, mat: CTValue): Boolean = {
            cse.pat match {
              case a @ Alternative(alts) =>
                val fevaledAlts = for (alt <- alts) yield {
                  val (r, _) = feval(alt, env)
                  r
                }
                fevaledAlts.contains(mat)
              case Ident(nme.WILDCARD) => false
              case _ =>
                val (pat, env3) = feval(cse.pat, env)
                pat == mat
            }
          }
          val (r1, env2) = feval(selector, env)
          var continue = true
          val rs = for (cse <- cases; if continue && matched(cse, env2, r1)) yield {
            continue = false
            feval(cse.body, env2)
          }
          rs match {
            case Nil =>
              val last = cases.last
              last.pat match {
                case Ident(nme.WILDCARD) => feval(last.body, env2)
                case _ => fail(fevalError + " match-wildcard " + m)
              }
            case _ => rs.head
          }

        case Typed(exp, t2) => feval(exp, env)
        case Function(vparams, body) =>
          feval(body, env)

        /**
         * An extractor class to create and pattern match with syntax New(tpt).
         * This AST node corresponds to the following Scala code:
         *
         * new T
         *
         * This node always occurs in the following context:
         *
         * (new tpt).<init>[targs](args)
         *
         * For example, an AST representation of:
         *
         * new Example[Int](2)(3)
         *
         * is the following code:
         *
         * Apply( Apply( TypeApply( Select(New(TypeTree(typeOf[Example])),
         * 					nme.CONSTRUCTOR) TypeTree(typeOf[Int])),
         *      			List(Literal(Constant(2)))),
         *         			List(Literal(Constant(3))))
         */

        case cnstrct @ Apply(Select(New(tpt), nme.CONSTRUCTOR), args) =>
          digraph.getClassRepr(tpt.tpe) match {
            case Some(clazz) =>
              val mtree = clazz.getMemberTree(nme.CONSTRUCTOR,
                cnstrct.symbol.tpe)
              mtree match {
                case methodTree: DefDef =>
                  val (fevaledArgs, env1) = fevalArgs(args, env)
                  val params = methodTree.vparamss.flatten.map(_.symbol.name.toTermName)
                  val funStore = Environment((params, fevaledArgs))
                  val (v, env2) = feval(methodTree.rhs, funStore)
                  val obj = HPEObject(cnstrct, clazz.tpe, env2)
                  (CTValue(obj), env)
                case _ => fail(fevalError + " constructor " + mtree)
              }

            case None => fail(s"${fevalError} constructor ${tpt}")
          }

        case Return(expr) => feval(expr, env)

        /**
         * An extractor class to create and pattern match with syntax
         * LabelDef(name, params, rhs).
         * This AST node does not have direct correspondence to Scala code.
         * It is used for tailcalls and like. For example, while/do are
         * desugared to label defs as follows:
         *
         * while (cond) body ==> LabelDef($L, List(),
         *                              if (cond) { body; L$() } else ())
         *
         * do body while (cond) ==> LabelDef($L, List(),
         * 						body; if (cond) L$() else ())
         */
        case LabelDef(name, params, rhs) =>
          feval(rhs, env)
        case ths @ This(n) =>
          (CTValue(HPETree(ths)), env)
        case select @ Select(ths @ This(n), name) =>
          val tree = getMemberTree(ths.symbol.tpe, name, select.symbol.tpe)
          feval(tree, env)
        // Unary operations
        case select @ Select(qual, name) if (isUnary(select)) =>
          val (r1, env1) = feval(qual, env)
          doUop(name, r1, env1)
        // TODO I should find a way to support This tree
        //        case ths @ This(name) => 
        //          env.getValue(name) match {
        //            case x: CTValue => (x, env)
        //            case _ =>
        //              val thisVal = CTValue(HPEObject(ths, ths.tpe, env))
        //              (thisVal, env)
        //          }
        case select @ Select(qual, name) =>
          val (r1, env1) = feval(qual, env)
          if (!qual.symbol.isPackage) {
            digraph.getClassRepr(qual.symbol.owner.tpe) match {
              case Some(repr) =>
                val member = repr.getMemberTree(name, select.symbol.tpe)
                r1.v match {
                  case tree: HPEObject =>
                    feval(member, tree.store)
                  case _ => fail(fevalError + " select " + r1)
                }
              case None => fail(s"${fevalError} select ${select}")
            }
          } else {
            (CTValue(HPETree(select)), env)
          }
        case Apply(fun, t) if (fun.symbol.name == newTermName("RT")) =>
          fail(fevalError)
        case Apply(fun, t) if (fun.symbol.name == newTermName("CT")) =>
          feval(t.head, env)
        // Binary operations
        case apply @ Apply(fun @ Select(r, l), args) if (isBinary(apply)) =>
          val arg1 = apply.args.head
          val (r1, env1) = feval(r, env)
          val (arg11, env2) = feval(arg1, env1)

          val method = fun.symbol
          val methodName = method.name
          doBop(methodName, r1, arg11, env2)
        // If {{{super}}} was {{{Object}}} then we just don't bother
        // executing its constructor
        // TODO once we build a framework to read binary classes to an AST tree
        // we can get rid of this
        case apply @ Apply(fun, args) if (isAnyConstructor(apply)) =>
          val tr = typeTree(reify(new Object()).tree)
          (CTValue(HPEObject(tr, tr.tpe, new Environment)), env)
        case apply @ Apply(fun @ Select(obj, m), args) =>
          val (obj2, env2) = feval(obj, env)
          val reciever = obj.symbol.tpe
          val method = fun.symbol
          fevalApply(reciever, method, args, env2)
        case apply @ Apply(fun, args) if (apply.symbol.isStatic) =>
          val reciever = fun.symbol.owner.tpe
          digraph.getClassRepr(reciever) match {
            case Some(clazz) =>
              val (_, _, env2) = peval(clazz.tree, new Environment)
              val method = fun.symbol
              fevalApply(reciever, method, args, env2)
            case None =>
              fail(s"${fevalError} apply ${reciever}")
          }
        case apply @ Apply(fun, args) =>
          val reciever = fun.symbol.owner.tpe
          val method = fun.symbol
          fevalApply(reciever, method, args, env)
        case x => fail(s"${fevalError} ${x.tpe} otherwise ${x}")
      }
    }

    def peval(tree: Tree, env: Environment): (Tree, Value, Environment) = {
      tree match {
        case clazz: ImplDef =>
          var newEnv = new Environment
          var tail = clazz.impl.body
          var nbody: List[Tree] = Nil
          while (tail != Nil) {
            val head = tail.head
            val (pevaled, _, env2) = peval(head, newEnv)
            newEnv = env2
            nbody = pevaled :: nbody
            tail = tail.tail
          }
          nbody = nbody.reverse
          
//          val newClazz = clazz match {
//            case ClassDef(mods, name, tparams, impl) =>
//              val tmplt = typeTree(treeCopy.Template(impl, impl.parents, impl.self, nbody))
//              treeCopy.ClassDef(clazz, mods, name, tparams, tmplt.asInstanceOf[Template])
//            case ModuleDef(mods, name, impl) =>
//              val tmplt = typeTree(treeCopy.Template(impl, impl.parents, impl.self, nbody))
//              treeCopy.ModuleDef(clazz, mods, name, tmplt.asInstanceOf[Template])
//          }
//          newClazz.tpe = clazz.symbol.tpe
//          val tclazz = typeTree(newClazz)
//          digraph.getClassRepr(tclazz.symbol.tpe) match {
//            case Some(x) => 
//              x.tree = tclazz
//            case None =>
//              val repr = new ClassRepr(clazz.impl.symbol.tpe, tclazz)
//              digraph.addClass(repr)
//              for (p <- tclazz.impl.parents) {
//                val parent = new ClassRepr(p.symbol.tpe)
//                digraph.addClass(parent)
//                digraph.addSubclass(parent, repr)
//              }
//          }
          (clazz, Top, env)
        case method @ DefDef(mods, name, tparams, vparamss, tpt, rhs) =>
          val (rhs1, _, temp) = peval(rhs, env)
          val newMethod = typeTree(treeCopy.DefDef(method, mods, name, tparams,
            vparamss, tpt, rhs1))
          (newMethod, Top, temp)
        case v: Literal =>
          (v, AbsValue(HPELiteral(v, v.tpe)), env)
        case v: Ident =>
          val value = env.getValue(v.symbol.name)
          val t: Tree = value match {
            case CTValue(_) => value.value
            case _ => v
          }
          (t, value, env)
        case v @ ValDef(mods, name, tpt, rhs) if (!rhs.isEmpty) =>
          // We won't partially evaluate method parameters and 
          // uninitialized (val/var)s
          val (rtree, r, env2) = peval(rhs, env)
          r match {
            case CTValue(_) =>
              (EmptyTree, r, env2.addValue(v.symbol.name, r))
            case _ =>
              val treeToCopy = typeTree(treeCopy.ValDef(v, mods, name, tpt, rtree))
              (treeToCopy, r, env2.addValue(v.symbol.name, r))
          }
        case a @ Assign(lhs, rhs) =>
          env.getValue(lhs.symbol.name) match {
            case CTValue(_) =>
              val (r, env1) = feval(rhs, env)
              val env2 = env1.addValue(lhs.symbol.name, r)
              val assgn = typeTree(treeCopy.Assign(a, lhs, r.v.tree))
              (r.v.tree, r, env2)
            case AbsValue(_) =>
              val (rtree, rhs1, env1) = peval(rhs, env)
              val env2 = env1.addValue(lhs.symbol.name, rhs1)
              val assgn = typeTree(treeCopy.Assign(a, lhs, rtree))
              (assgn, rhs1, env2)
            case Top =>
              val (rtree, rhs1, env1) = peval(rhs, env)
              val assgn = typeTree(treeCopy.Assign(a, lhs, rtree))
              (assgn, Top, env1)
            case Bottom =>
              val (rtree, rhs1, env1) = peval(rhs, env)
              val env2 = env1.addValue(lhs.symbol.name, rhs1)
              rhs1 match {
                case CTValue(x) =>
                  (x.tree, rhs1, env2)
                case _ =>
                  val assgn = typeTree(treeCopy.Assign(a, lhs, rtree))
                  (assgn, rhs1, env2)
              }
          }
        case m @ Match(selector, cases) =>
          def matched(cse: CaseDef, env: Environment, mat: Value): Boolean = {
            cse.pat match {
              case Alternative(alts) =>
                val pevaledAlts = for (alt <- alts) yield {
                  val (_, r, _) = peval(alt, env)
                  r
                }
                pevaledAlts.contains(mat)
              case Ident(nme.WILDCARD) => false
              case _ =>
                val (pat, v, env3) = peval(cse.pat, env)
                if (v.value == mat.value) true
                else false
            }
          }
          val (r1, v, env2) = peval(selector, env)
          v match {
            case CTValue(_) | AbsValue(_) =>
              var continue = true
              val rs = for (
                cse <- cases;
                if continue && matched(cse, env2, v)
              ) yield {
                continue = false
                peval(cse.body, env2)
              }
              rs match {
                case Nil =>
                  val last = cases.last
                  last.pat match {
                    case Ident(nme.WILDCARD) => peval(last.body, env2)
                    case _ => fail("No match found exception " + m)
                  }
                case _ => rs.head
              }
            case _ =>
              val rs = for (cse <- cases) yield {
                val (ncse, vncse, envt) = peval(cse.body, env2)
                vncse match {
                  case CTValue(_) | AbsValue(_) =>
                    vncse.value match {
                      case Some(x) =>
                        (typeTree(treeCopy.CaseDef(cse, cse.pat,
                          cse.guard, x.tree)).asInstanceOf[CaseDef], envt)
                      case _ =>
                        (typeTree(treeCopy.CaseDef(cse, cse.pat,
                          cse.guard, ncse)).asInstanceOf[CaseDef], envt)
                    }
                  case Top | Bottom =>
                    (typeTree(treeCopy.CaseDef(cse, cse.pat,
                      cse.guard, ncse)).asInstanceOf[CaseDef], envt)
                }
              }
              val (newCases, newEnvs) = rs.unzip
              val newMatch = treeCopy.Match(typeTree(r1), selector, newCases)
              (typeTree(newMatch), Top, env2.makeConsistent(newEnvs))
          }
        case block @ Block(stats, expr) =>
          var env2 = env
          var tail = stats
          var stats2: List[Tree] = Nil
          while (tail != Nil) {
            val head = tail.head
            val (t, _, envTemp) = peval(head, env2)
            stats2 = t :: stats2
            env2 = envTemp
            tail = tail.tail
          }
          val (expr2, v2, env3) = peval(expr, env2)
          val block2 = treeCopy.Block(block, stats2.reverse, expr2)
          (typeTree(block2), v2, env3)
        case ifelse @ If(cond, thenp, elsep) =>
          val (r, v, env1) = peval(cond, env)
          v match {
            case CTValue(HPELiteral(Literal(Constant(true)), _))
              | AbsValue(HPELiteral(Literal(Constant(true)), _)) =>
              peval(thenp, env1)
            case CTValue(HPELiteral(Literal(Constant(false)), _))
              | AbsValue(HPELiteral(Literal(Constant(false)), _)) =>
              peval(elsep, env1)
            case _ =>
              val (tr, tv, tenv) = peval(thenp, env1)
              val (fr, fv, fenv) = peval(elsep, env1)
              val env2 = env1.makeConsistent(List(tenv, fenv))
              val newIf = typeTree(treeCopy.If(ifelse, r, tr, fr))
              (newIf, Top, env2)
          }
        case fnctn @ Function(vparams, body) =>
          val (r, _, env2) = peval(body, env)
          val fnctn2 = typeTree(treeCopy.Function(fnctn, vparams, r))
          (fnctn2, Top, env2)
        case cnstrct @ Apply(n @ Select(nw @ New(tpt), nme.CONSTRUCTOR), args) =>
          val (trees, vs, env2) = pevalArgs(args, env)
          digraph.getClassRepr(tpt.tpe) match {
            case Some(clazz) =>
              if (hasCT(vs)) {
                val memc = getSpecializedClass(Ident(clazz.tree.symbol.name), tpt.tpe,
                  args, vs)
                val rargs = getRuntimeArgs(trees, vs)
                val newnw = typeTree(treeCopy.Apply(cnstrct,
                  treeCopy.Select(n, treeCopy.New(nw, memc), nme.CONSTRUCTOR),
                  rargs))
                val nobj = HPEObject(newnw, clazz.tpe, new Environment)
                (newnw, AbsValue(nobj), env)
              } else {
                val store = new Environment
                val cnstrct2 = typeTree(treeCopy.Apply(cnstrct, n, trees))
                val obj = HPEObject(cnstrct2, tpt.tpe, store)
                (cnstrct2, AbsValue(obj), env2)
              }
            case None =>
              val cnstrct2 = typeTree(treeCopy.Apply(cnstrct, n, trees))
              (cnstrct2, Top, env2)
          }
        case lbl @ LabelDef(name, params, rhs) =>
          val (r, _, env2) = peval(rhs, env)
          val lbl2 = typeTree(treeCopy.LabelDef(lbl, name, params, r))
          (lbl2, Top, env2)
        case select @ Select(New(tpt), name) =>
          val obj = HPEObject(select, tpt.tpe, new Environment)
		  (select, AbsValue(obj), env)
        case select @ Select(qual, name) if(qual.symbol != null &&
            								qual.symbol != NoSymbol &&
            								qual.symbol.isPackage) =>
          (select, Top, env)
        // TODO Do we need this? think about it MORE
        case select @ Select(ths @ This(n), name) =>  
          val tree = getMemberTree(ths.symbol.tpe, name, select.symbol.tpe)
          if(tree.symbol.isVariable) {
            val (r, v, env2) = peval(tree, env)
            v match {
              case x: CTValue => (r, x, env2)
              case x: AbsValue => (r, x, env2)
              case _ => (select, Top, env)
            }
          } else {
        	(select, Top, env)
          }
        // Unary operations
        case select @ Select(qual, name) if (isUnary(select)) =>
          val (r1, v1, env1) = peval(qual, env)
          v1 match {
            case x: CTValue =>
              val (r, env2) = doUop(name, x, env)
              (r.toTree, r, env2)
            case x: AbsValue =>
              val (r, env2) = doUop(name, x.toCTValue, env)
              (r.toTree, r, env2)
            case _ =>
              val r = treeCopy.Select(select, r1, name)
              (typeTree(r), Top, env1)
          }
        case select @ Select(qual, name) =>
          val (r1, v, env1) = peval(qual, env)
          if(qual.symbol != null && qual.symbol != NoSymbol) {
            digraph.getClassRepr(qual.symbol.owner.tpe) match {
              case Some(repr) =>
                val member = repr.getMemberTree(name, select.symbol.tpe)
                v.value match {
                  case Some(HPEObject(tree, _, store)) =>
                    peval(member, store)
                  case _ =>
                    peval(member, env1)
                }
              case None =>
                (select, Top, env1)
            }
          } else (select, Top, env1)
        case a @ Apply(fun, t) if (fun.symbol.name == newTermName("CT")) =>
          val (v, env2) = feval(t.head, env)
          (v.value, v, env2)
        case a @ Apply(fun, t) if (fun.symbol.name == newTermName("RT")) =>
          t match {
            case x :: Nil =>
              x.foreach({
                _ match {
                  case v: Ident =>
                  	val value = env.getValue(v.symbol.name)
                  	value match {
                  		case CTValue(_) => fail("CT cannot live inside RT")
                  		case _ =>
                  	}
                  case _ =>
                }})
              peval(x, env)
//              (r, Top, env2)
            case _ => fail("Should not happen")
          }
        case apply @ Apply(fun @ Select(r, l), args) if (isBinary(apply)) =>
          val arg1 = apply.args.head
          val (r1, v1, env1) = peval(r, env)
          val (arg2, v2, env2) = peval(arg1, env1)

          val method = fun.symbol
          val methodName = method.name
          (v1, v2) match {
            case (x: CTValue, y: CTValue) =>
              val (r, env3) = doBop(methodName, x, y, env)
              (r.toTree, r, env3)
            case (x: CTValue, y: AbsValue) =>
              val (r, env3) = doBop(methodName, x, y.toCTValue, env)
              (r.toTree, r, env3)
            case (x: AbsValue, y: CTValue) =>
              val (r, env3) = doBop(methodName, x.toCTValue, y, env)
              (r.toTree, r, env3)
            case (x: AbsValue, y: AbsValue) =>
              val (r, env3) = doBop(methodName, x.toCTValue, y.toCTValue, env)
              (r.toTree, r, env3)
            case _ =>
              val r = typeTree(treeCopy.Apply(apply, treeCopy.Select(fun, r1, l),
                List(arg2)))
              (r, Top, env2)
          }
        case apply @ Apply(fun, args) if (fun.symbol != NoSymbol && 
        										fun.symbol.owner.isModule) =>
          val reciever = fun.symbol.owner.tpe
          val (pargs, pvals, env3) = pevalArgs(args, env)
          val ctvals = pvals.filter(isCT(_))
          digraph.getClassRepr(reciever) match {
            case Some(clazz) =>
//              val (_, _, env2) = peval(clazz.tree, new Environment)
              val method = fun.symbol
              val mtree = clazz.getMemberTree(method.name, method.tpe).asInstanceOf[DefDef]
              val tmargs = mtree.vparamss.flatten
              val cargs = getCTArgs(tmargs, pvals)
              val margs = cargs.map(_.symbol.name.toTermName)
              val menv = env.addValues(margs zip pvals)
              if (isAllCT(pvals)) {
                val (r, menv2) = feval(mtree.rhs, menv)
                (r.v.tree, r, env)
              } else if(hasCT(pvals)){val rargs = getRuntimeArgs(args, pvals)
                val rparams = getRuntimeParams(tmargs, pvals)
                val mname = clazz.getNextMethod(method.name, ctvals)
                val (mbody, _, _) = peval(mtree.rhs, menv)
                val tpe = MethodType(rparams.map(_.symbol), apply.tpe) 
                
                val untypedTree = clazz.hasMember(mname, tpe) match {
                  case false =>
                    val temp = DefDef(mtree.mods, mname, mtree.tparams, 
                        List(rparams.asInstanceOf[List[ValDef]]), mtree.tpt, mbody)
                    val symb = mtree.symbol.cloneSymbol(mtree.symbol.owner, 
                					mtree.symbol.flags, mname)
                	symb.setTypeSignature(tpe)
//                	temp.tpe = tpe
//                symb.name = sname
                //untypedTree.tpe = MethodType(rparams.map(_.symbol),
                	//	apply.symbol.tpe)
                    temp.symbol = symb
                    temp
                  case true => clazz.getMemberTree(mname, tpe)
                }
                
                val smtree = typeTree(untypedTree)
                val modulep = clazz.hasMember(mname, tpe) match {
                  case false => 
                    val temp = typeTree(treeCopy.ModuleDef(clazz.tree, clazz.tree.mods,
                    		clazz.tree.symbol.name,
                    		treeCopy.Template(clazz.tree.impl,
                    				clazz.tree.impl.parents,
                    				clazz.tree.impl.self,
                    				smtree :: clazz.tree.impl.body
                    				))).asInstanceOf[ModuleDef]
                    
                    clazz.tree = temp
                    temp
                  case true => clazz.tree
                }
                val sapply = fun match {
                  case Select(qual, name) =>
                    typeTree(treeCopy.Apply(apply,
                    		treeCopy.Select(fun, qual, mname), rargs))
                  case _ => 
                    typeTree(treeCopy.Apply(apply, Ident(mname), rargs))
                }
                (sapply, Top, env)
              } else {
                (apply, Top, env)
              }
            case None => noTreeApply(apply, env)
          }
        case apply @ Apply(fun @ Select(qual @ Super(k, j), m), args) =>
//          val tpe = qual.symbol.tpe
//          digraph.getClassRepr(tpe) match {
//            case Some(clazz) =>
//              val rcvr = clazz.tree
//              pevalApply(rcvr, Top, tpe, fun.symbol.name, apply, fun,
//                (tmpt: Tree, newt: Tree, x: Name) => 
//                  treeCopy.Select(tmpt, qual, x),
//                  	args, env)
//            case None => noTreeApply(apply, env) 
//          }
          //TODO Think about this case more
          // Do we know who is our parent, during compilation time?
          // super.find() which find is called?
          (apply, Top, env)
        case apply @ Apply(fun @ Select(qual @ This(ths), m), args) =>
          def tcopy(tmpt: Tree, newt: Tree, x: Name): Tree = {
            val t = Select(qual, x)
//            val symbol = tmpt.symbol.cloneSymbol(tmpt.symbol.owner,
//        				t.symbol.flags, x)
//        	t.symbol = symbol
//            t.tpe = tmpt.tpe
            t
          }
          val tpe = qual.symbol.tpe
          digraph.getClassRepr(tpe) match {
            case Some(clazz) =>
              val rcvr = clazz.tree
              pevalApply(rcvr, Top, tpe, fun.symbol.name, apply, fun,
                tcopy, args, env)
            case None => 
              noTreeApply(apply, env) 
          }
        case apply @ Apply(fun @ Select(obj @ Ident(_), m), args) =>
          def tcopy(tmpt: Tree, newt: Tree, x: Name): Tree =  { 
            val t = Select(newt, x)
//            t.tpe = tmpt.tpe
//            val symbol = tmpt.symbol.cloneSymbol(tmpt.symbol.owner,
//        				t.symbol.flags, x)
//        	t.symbol = symbol
            t
          }
          val (nobj, nv, env2) = peval(obj, env)
          pevalApply(nobj, nv, obj.symbol.tpe, m, apply, fun,
            tcopy, args, env2)
        case apply @ Apply(fun, args) =>
          def tcopy(tmpt: Tree, newt: Tree, x: Name): Tree = {
        	val t = Ident(x)
//        	t.tpe = tmpt.tpe
//        	val symbol = tmpt.symbol.cloneSymbol(tmpt.symbol.owner,
//        				t.symbol.flags, x)
//        	t.symbol = symbol
        	t
          }
          val tpe = fun.symbol.owner.tpe
          digraph.getClassRepr(tpe) match {
            case Some(clazz) =>
              val rcvr = clazz.tree
              val (rcvr2, nv, env2) = peval(rcvr, new Environment)
              pevalApply(rcvr2, nv, tpe, fun.symbol.name, apply, fun,
                tcopy,
                args, env2)
            case None => noTreeApply(apply, env)
          }
        case rtrn @ Return(t) =>
          val (r, v, env2) = peval(t, env)
          val rtrn2 = treeCopy.Return(tree, r)
          (typeTree(rtrn2), v, env2)
        case Typed(exp, t2) => peval(exp, env)
        case _ => (tree, Top, env)
      }
    }

    private def noTreeApply(apply: Apply, env: Environment):
    		(Tree, Value, Environment) = {
      val tpe = apply.fun.symbol.owner.tpe
      val (pargs, vs, env2) = pevalArgs(apply.args, env)
	  vs.filter(isCT(_)) match {
	    case Nil =>
	      val app = typeTree(treeCopy.Apply(apply, apply.fun, pargs))
	      (app, Top, env2)
	    case _ => 
	      fail(s"${vs}\nTree not found for ${tpe} the " +
	    		s"owner of ${apply.fun.symbol.name} " +
	    		s"and the call is: ${apply}")
	  }
    }
    def isCT(v: Value) = !isNotCT(v)
    def isNotCT(v: Value) = {
      v match {
        case x: CTValue => false
        case _ => true
      }
    }

    private def getRuntimeArgs(exprs: List[Tree], values: List[Value]): List[Tree] = {

      val pvTuple = values zip exprs
      val temp = for ((v, e) <- pvTuple if (isNotCT(v))) yield {
        e
      }
      temp.reverse
    }
    
    private def getCTArgs(exprs: List[ValDef], values: List[Value]): List[ValDef] = {

      val pvTuple = values zip exprs
      val temp = for ((v, e) <- pvTuple if (isCT(v))) yield {
        e
      }
      temp.reverse
    }

    private def getRuntimeParams(params: List[Tree], vals: List[Value]): List[ValDef] = {

      val rparams = for ((param, v) <- (params zip vals) if (isNotCT(v))) yield {
        param.asInstanceOf[ValDef]
      }
      rparams.reverse
    }

    private def getSpecizlizedMethod(clazz: ClassRepr,
      method: DefDef, args: List[Value], env: Environment,
      name: TermName): (DefDef, Option[Environment]) = {
      clazz.getSpecializedOption(method.symbol.name, args) match {
        case Some(mtree) => (mtree, None)
        case None =>
          val rparams = getRuntimeParams(method.vparamss.flatten, args)
          val (sptree, _, env2) = peval(method, env)
          val mtree = sptree.asInstanceOf[DefDef]
          val mname = name
          val spmthd = typeTree(treeCopy.DefDef(mtree, mtree.mods,
            mname, mtree.tparams,
            List(rparams.map(_.asInstanceOf[ValDef])),
            mtree.tpt, mtree.rhs)).asInstanceOf[DefDef]
          clazz.addSpecialized(mname, args, spmthd)
          (spmthd, Some(env2))
      }
    }
    private def getSpecializedClass(name: Ident, tpe: Type,
      args: List[Tree], vals: List[Value]): ImplDef = {
      classBank.getOption(tpe, vals) match {
        case Some(x) => x.tree
        case None =>
          val clazz = digraph.getClassRepr(tpe).get
          val tpes = args.map(_.symbol)
          clazz.getMemberTree(nme.CONSTRUCTOR, MethodType(tpes, tpe)) match {
            case mtree: DefDef =>
              val clazzArgs = getRuntimeParams(args, vals)
              val argNames = mtree.vparamss.flatten.map(_.symbol.name.toTermName)
              val env = Environment(argNames zip vals)
              val (nconst, _, cenv) = peval(mtree, env)
              val nbody = nconst :: {
                for (
                  m <- clazz.tree.impl.body if (m.symbol.name != nme.CONSTRUCTOR)
                ) yield {
                  m
                }
              }
              val nimpl = clazz.tree match {
                case clazztree: ClassDef =>
                  val template = treeCopy.Template(clazz.tree.impl,
	                name :: clazz.tree.impl.parents,
	                clazz.tree.impl.self, nbody)
                  val clazzToPeval = treeCopy.ClassDef(clazztree, clazztree.mods,
                    classBank.getNextClassName(clazztree.symbol.name),
                    clazztree.tparams, template)
                  val (nclazz, _, _) = peval(typeTree(clazzToPeval), cenv)
                  nclazz
                case _ => fail("You should not be able to instansiate an object")
              }
              val clazzrepr = new ClassRepr(tpe, nimpl)
              classBank.add(tpe, vals, clazzrepr)
              digraph.addClass(clazzrepr)
              digraph.addSubclass(clazz, clazzrepr)
              val csymbol = nimpl.symbol.asInstanceOf[ClassSymbol]
              val ownerSymb = csymbol.owner
              ownerSymb.newClass(csymbol.name.toTypeName,
                  csymbol.pos, csymbol.flags)
              nimpl
            case _ => fail("Could not find the AST node of the constructor")
          }
      }
    }
    
    
    private def hasCT(vs: List[Value]): Boolean = {
      vs match {
        case Nil => false
        case CTValue(_) :: xs => true
        case x :: xs => hasCT(xs)
      }
    }
    private def isAllCT(vs: List[Value]): Boolean = {
      def check(args: List[Value]): Boolean = {
        args match {
          case Nil => true
          case CTValue(_) :: xs => check(xs)
          case _ => false
        }
      }
      if (vs == Nil) false
      else check(vs)
    }
    private def pevalArgs(args: List[Tree], store: Environment): (List[Tree], List[Value], Environment) = {
      var pevaled: List[Value] = Nil
      var trees: List[Tree] = Nil
      var env = store
      var tail = args
      while (tail != Nil) {
        val head = tail.head
        val (t, v, temp) = peval(head, env)
        pevaled = v :: pevaled
        trees = t :: trees
        env = temp
        tail = tail.tail
      }
      (trees.reverse, pevaled.reverse, env)
    }
    private def fevalArgs(args: List[Tree], store: Environment): (List[CTValue], Environment) = {
      var fevaled: List[CTValue] = Nil
      var env = store
      var tail = args
      while (tail != Nil) {
        val head = tail.head
        val (arg, temp) = feval(head, env)
        fevaled = arg :: fevaled
        env = temp
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

    private def pevalApply(rcvr: Tree, 
      nv: Value, rcvrtpe: Type,
      m: Name, apply: Apply, fun: Tree,
      tcopy: (Tree, Tree, Name) => Tree,
      args: List[Tree], env: Environment): (Tree, Value, Environment) = {
//      val (nobj, nv, env2) = peval(rcvr, env)
      val (pargs, pvals, env3) = pevalArgs(args, env)
      val ctvals = pvals.filter(isCT(_))
      digraph.getClassRepr(rcvrtpe) match {
        case Some(rcvclass) =>
          val mtree = rcvclass.getMemberTree(m, apply.symbol.tpe).asInstanceOf[DefDef]
          val tmargs = mtree.vparamss.flatten
          val cargs = getCTArgs(tmargs, pvals)
          val margs = cargs.map(_.symbol.name.toTermName)
          val menv = env.addValues(margs zip pvals)
          nv match {
            case x: CTValue =>
              if (isAllCT(pvals)) {
                val (r, menv2) = feval(mtree.rhs, menv)
                (r.v.tree, r, env)
              } else {
                val rargs = getRuntimeArgs(args, pvals)
                val rparams = getRuntimeParams(tmargs, pvals)
                
                val module = getCompanionObject(rcvclass)
                val moduleSymb = module.tree.symbol.moduleClass
                val sname = module.getNextMethod(mtree.symbol.name, ctvals)
//                val falgs = Flag..SYNTHETIC | 
                val symb = moduleSymb.newMethod(sname, 
                    moduleSymb.pos.focus, NoFlags)
//               localTyper.context1.enclClass.owner = module.tree.symbol.moduleClass
//                symb.setInfo(tpe)
//                symb.owner = module.tree.symbol
                
                var tpe = MethodType(rparams.map(_.symbol), apply.tpe) 
                
                val hasMember = module.hasMember(name, tpe)
                val staticm = hasMember match {
                  case false =>
//                    symb.setFlag(Flag.)
                	
                    val obody = mtree.rhs.duplicate
                    val (mbody, _, _) = peval(obody, menv)
//                    obody.symbol.owner = symb
//                	val (mbody, _, _) = peval(obody, menv)
                	val paramSyms = map2(rparams.map(_.symbol.tpe), rparams.map(_.symbol)) {
		              (tp, param) => symb.newSyntheticValueParam(tp, param.name)
		            }
                    tpe = MethodType(paramSyms, apply.tpe)
                    val nrparams = for((p, s) <- (rparams zip paramSyms)) yield {
                	  s.setInfo(p.symbol.tpe)
                      ValDef(s, p.tpt)
                	}
                    
                    if(moduleSymb.info.decls.lookup(symb.name) == NoSymbol) {
                      symb setInfoAndEnter tpe
                    } else {
                      symb setInfo tpe
                    }
                    def findSymbol(name: Name, tpe: Type): Symbol = {
                      val r = for(p <- paramSyms if(p.name == name && p.tpe =:= tpe)) yield {
                        p
                      }
                      r.head
                    }
                    
                    mbody.foreach {
                      (x: Tree) => {
                        if(x.symbol!= null && x.symbol != NoSymbol
                          && x.symbol.owner == mtree.symbol)  {
                          val ns = findSymbol(x.symbol.name, x.symbol.tpe)
                          ns.owner = symb
                          x.symbol = ns
                        }
                      }
                    }

                    
                    
                	
                    val tbody = localTyper.typedPos(symb.pos)(mbody)
                    
                    val methDef = DefDef(symb, List(nrparams), tbody)
                	
                    methDef.tpt setType localTyper.packedType(tbody, symb)
                    typeTree(methDef)
                	
                  case true => module.getMemberTree(sname, tpe)
                }
                
                
//                val (stree, _, env4) = peval(staticTree, menv)
//                val staticm = staticTree
                val modulep = hasMember match {
                  case false => 
                    val temp = localTyper.typedPos(fun.pos) {
                      treeCopy.ModuleDef(module.tree, module.tree.mods,
                    		module.tree.symbol.name,
                    		treeCopy.Template(module.tree.impl,
                    				module.tree.impl.parents,
                    				module.tree.impl.self,
                    				staticm :: module.tree.impl.body))
                     }.asInstanceOf[ModuleDef]
                    module.tree = temp
                    temp
                  case true => module.tree
                }

                val sapplySym = staticm.symbol //apply.symbol.cloneSymbol(staticm.symbol.owner, apply.symbol.flags, sname)
                
//                sapplySym.setInfo(symb.info)
                
//                val thssymb = fun.symbol.cloneSymbol(apply.symbol.owner, 
//                    fun.symbol.flags, modulep.symbol.name)
//                thssymb.setInfo(modulep.symbol.info)
                val ths = REF(modulep.symbol)
                val sapply = Apply(ths DOT sname, rargs).setSymbol(sapplySym)
                
                
//                  
//                
//                sapply.setSymbol = sapplySym
////                sapply.symbol.owner = apply.symbol.owner
//                sapply.symbol.name = sname
//                sapply.tpe = tpe.resultType
                
//                sapply.symbol.setTypeSignature(tpe)
//                val nsapply = typeTree(sapply)
//                sapply.symbol = sapplySym
                
                
                (typeTree(sapply), Top, env3)
              }
            case x: AbsValue =>
              if (hasCT(pvals)) {
                val rargs = getRuntimeArgs(args, pvals)
                val mname = rcvclass.getNextMethod(mtree.symbol.name, ctvals)
                val (specialized, envr) = getSpecizlizedMethod(rcvclass, mtree, pvals, menv, mname)
                val tapply = typeTree(treeCopy.Apply(apply,
                  tcopy(fun, rcvr, mname), rargs))
                (tapply, Top, env3)
              } else {
                val tapply = typeTree(treeCopy.Apply(apply,
                  tcopy(fun, rcvr, fun.symbol.name), pargs))
                (tapply, Top, env3)
              }
            case _ => // receiver is unknown
              if (hasCT(pvals) && closed) {
                val rargs = getRuntimeArgs(args, pvals)
                val clazzes = rcvclass :: digraph.getSubclasses(rcvclass)
                val mname = rcvclass.getNextMethod(mtree.symbol.name, ctvals)
                for (c <- clazzes) {
                  val (specialized, envr) = getSpecizlizedMethod(c, mtree, pvals, menv, mname)
                }
                val tapply = typeTree(treeCopy.Apply(apply,
                  tcopy(fun, rcvr, mname), rargs))
                (tapply, Top, env3)
              } else {
                val tapply = typeTree(treeCopy.Apply(apply, fun, pargs))
                (tapply, Top, env3)
              }
          }
        case _ => 
          val tapply = typeTree(treeCopy.Apply(apply, fun, pargs))
          (tapply, Top, env3)
      }
    }

    private def fevalApply(reciever: Type, method: Symbol,
      args: List[Tree], env: Environment): (CTValue, Environment) = {
      digraph.getClassRepr(reciever) match {
        case Some(clazz) =>
          val mtree = tree2Method(clazz.getMemberTree(method.name, method.tpe))
          val (fevaledArgs, env1) = fevalArgs(args, env)
          val params = mtree.vparamss.flatten.map(_.symbol.name.toTermName)
          val funStore = Environment((params, fevaledArgs))
          val (v, _) = feval(mtree.rhs, funStore)
          (v, env1)
        case None =>
          fail(fevalError)
      }
    }
    private def getCompanionObject(rcvclass: ClassRepr): ClassRepr = {
      digraph.findCompanionModule(rcvclass.tree.symbol) match {
        case None =>
          val modname = rcvclass.tree.symbol.name
          //    	            val temp = typeTree(reify{object Temp {}}.tree).asInstanceOf[ModuleDef]
          //    	            val module = typeTree(treeCopy.ModuleDef(temp, 
          //    	            		temp.mods, modname, temp.impl)).asInstanceOf[ModuleDef]
          val module = typeTree(ModuleDef(rcvclass.tree.mods,
            modname, Template(rcvclass.tree.impl.parents,
              rcvclass.tree.impl.self,
              Nil)))
          val modrepr = new ClassRepr(module.tpe, module.asInstanceOf[ModuleDef])
          val symb = rcvclass.tree.symbol.asClass
          symb.owner.newModule(module.symbol.name.toTypeName, module.symbol.pos, 
              module.symbol.flags)
          digraph.addClass(modrepr)
          modrepr
        case Some(x) => x
      }
    }

    private implicit def hpeAny2Tree(t: Option[HPEAny]): Tree = {
      t match {
        case Some(HPELiteral(x: Tree, _)) => x
        case Some(HPEObject(x: Tree, _, _)) => x
        case Some(HPETree(t)) => t
        case _ =>
          typeTree(treeBuilder.makeBlock(Nil))
      }
    }

    private implicit def hpeAny2Type(t: Option[HPEAny]): Type = {
      t match {
        case Some(HPELiteral(_, x: Type)) => x
        case Some(HPEObject(_, x: Type, _)) => x
        case _ => fail(s"Unexpected type definition ${t}")
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

    private implicit def tree2Class(t: Tree): ImplDef = {
      t match {
        case x: ImplDef => x
        case x => fail(s"Unexpected class definition ${x} ${x.symbol}")
      }
    }

    private implicit def tree2Method(t: Tree): DefDef = {
      t match {
        case x: DefDef => x
        case x => fail(s"Unexpected method definition ${x}")
      }
    }

    private def isAnyConstructor(a: Apply): Boolean = {
      a.symbol.fullName == "java.lang.Object.<init>" ||
    		  a.symbol.fullName == "scala.lang.Any.<init>"
    }

    private def isUnary(select: Select): Boolean = {
      val rcvr = select.symbol.owner.tpe
      val c = isAnyVal(rcvr)
      val methodName = select.symbol.name
      if (c && isUop(methodName)) {
        true
      } else false
    }

    private def isBinary(apply: Apply): Boolean = {
      isBinary(apply, apply.args.size == 1, isBop)
    }
    private def isBinary(apply: Apply, check: Boolean,
      f: TermName => Boolean): Boolean = {
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
      if (lit.tpe <:< definitions.BooleanClass.tpe) v.booleanValue
      else if (lit.tpe <:< definitions.ByteClass.tpe) v.byteValue
      else if (lit.tpe <:< definitions.ShortClass.tpe) v.shortValue
      else if (lit.tpe <:< definitions.IntClass.tpe) v.intValue
      else if (lit.tpe <:< definitions.LongClass.tpe) v.longValue
      else if (lit.tpe <:< definitions.FloatClass.tpe) v.floatValue
      else if (lit.tpe <:< definitions.DoubleClass.tpe) v.doubleValue
      else if (lit.tpe <:< definitions.CharClass.tpe) v.charValue
      else if (lit.tpe <:< definitions.StringClass.tpe) v.stringValue
      else fail(s"${lit.tpe} is not a builtin value class")
    }

    private def doUop(methodName: TermName, v: CTValue, env: Environment): (CTValue, Environment) = {
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
          val x1 = toVal(x)
          val y1 = toVal(y)
          val lit = doBop(x1, y1, methodName)
          val tlit = typeTree(lit)
          val r = CTValue(HPELiteral(tlit, tlit.tpe))
          (r, env)
        case _ => fail(s"${fevalError} BOP ${v1.value} and ${v2.value}")
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

    private def getMemberTree(tpe1: Type, m: Name, mType: Type): Tree = {
      digraph.getClassRepr(tpe1) match {
        case Some(repr) => repr.getMemberTree(m, mType)
        case None => fail(s"Could not find class ${tpe1}")
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
  
