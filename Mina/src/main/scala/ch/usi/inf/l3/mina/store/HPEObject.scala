/*
 * Copyright (c) <2013>, Amanj Sherwany <http://www.amanj.me>
 * All rights reserved.
 * */

package ch.usi.inf.l3.mina.store

import scala.reflect.api.Trees
import ch.usi.inf.l3._
import mina._

sealed trait HPEAny

case class HPEObject(val tpe: Class, val store: Environment) extends HPEAny

case class HPELiteral(val value: Trees#Literal) extends HPEAny{
  val tpe = value.tpe
}