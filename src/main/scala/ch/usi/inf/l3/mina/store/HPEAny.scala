/*
 * Copyright (c) <2013>, Amanj Sherwany <http://www.amanj.me>
 * All rights reserved.
 * */

package ch.usi.inf.l3.mina.store

import ch.usi.inf.l3.mina._
import ch.usi.inf.l3.mina.eval._

private[mina] trait HPEWrapper {
  self: HPE with EnvWrapper =>
  import self.global._

  private[mina] trait HPEAny {
    val tree: Tree;
    val tpe: Type;
  }
  private[mina] case class HPEObject(val tree: Tree, val tpe: Type,
    val store: Environment) extends HPEAny
    
    
  private[mina] case class HPELiteral(override val tree: Tree, 
      override val tpe: Type) extends HPEAny
}

