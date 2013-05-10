/*
 * Copyright (c) <2013>, Amanj Sherwany <http://www.amanj.me>
 * All rights reserved.
 * */
package ch.usi.inf.l3.mina.eval

import scala.tools.nsc.Phase
import scala.tools.nsc.plugins.PluginComponent
import scala.language.implicitConversions
import ch.usi.inf.l3.mina._

class HPEFinalizer(val hpe: HPE) extends PluginComponent {
  
  import hpe._
  val global: hpe.global.type = hpe.global
  val runsAfter = List[String](hpe.specializer)
  override val runsBefore = List[String]("superaccessors")
  val phaseName = hpe.finalizer

  import hpe.global._
  def newPhase(_prev: Phase) = new HPECPFinalizer(_prev)
  
  class HPECPFinalizer(prev: Phase) extends StdPhase(prev) {
    override def name = hpe.finalizer

    def apply(unit: CompilationUnit) {
      println(unit.body)
//      for (clazz @ ClassDef(mods, name, tparams, impl) <- unit.body) {
//        val repr = new ClassRepr(name, clazz)
//        digraph.addClass(repr)
//        for (p <- impl.parents) {
//          val pname = p.symbol.name
//          val parent = new ClassRepr(pname)
//          digraph.addClass(parent)
//          digraph.addSubclass(parent, repr)
//        }
//      }
    }
  }
}