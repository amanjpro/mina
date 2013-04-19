/*
 * Copyright (c) <2013>, Amanj Sherwany <http://www.amanj.me>
 * All rights reserved.
 * */
package ch.usi.inf.l3

import scala.reflect.api.Trees
import scala.reflect.api.Types

package object mina {
  type Class = Types#Type
  type Method = Trees#DefDef
  type Var = Trees#TreeApi
}