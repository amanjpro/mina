/*
 * Copyright (c) <2013>, Amanj Sherwany <http://www.amanj.me>
 * All rights reserved.
 * */

package ch.usi.inf.l3.mina.store

import ch.usi.inf.l3.mina.eval._

private[mina] trait ValueWrapper {
  self: HPE with HPEWrapper =>

  private[mina] sealed trait Value {
    def value: Option[HPEAny];
  }

  case object Bottom extends Value {
    //TODO or should I throw an exception?
    override def value: Option[HPEAny] = None
  }

  case object Top extends Value {
    //TODO or should I throw an exception?
    override def value: Option[HPEAny] = None
  }

  case class CTValue(v: HPEAny) extends Value {
    override def value: Option[HPEAny] = Some(v)
  }

  case class AbsValue(v: HPEAny) extends Value {
    override def value: Option[HPEAny] = Some(v)
  }
}


