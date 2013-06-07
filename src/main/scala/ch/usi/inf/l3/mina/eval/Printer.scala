/*
 * Copyright (c) <2013>, Amanj Sherwany <http://www.amanj.me>
 * All rights reserved.
 * */
package ch.usi.inf.l3.mina.eval

import scala.tools.nsc.Phase
import scala.tools.nsc.plugins.PluginComponent
import scala.language.implicitConversions
import ch.usi.inf.l3.mina._

class HPEPrinter(val hpe: HPE) extends PluginComponent {

  import hpe._

  val global: hpe.global.type = hpe.global
  val runsAfter = List[String](hpe.finalizer)
  override val runsRightAfter = Some(hpe.finalizer)
  override val runsBefore = List[String](hpe.aftr)
  val phaseName = "printerrrr"

  import hpe.global._
  def newPhase(_prev: Phase) = new HPEPrinterK(_prev)

  class HPEPrinterK(prev: Phase) extends StdPhase(prev) {
    override def name = "printerrrr"

    def apply(unit: CompilationUnit) {
      println("   LKJLKJLKJDLKFJSDL:FDSJKF " + unit.body)
    }
  }
}