/*
 * Copyright (c) <2013>, Amanj Sherwany <http://www.amanj.me>
 * All rights reserved.
 * */
package ch.usi.inf.l3

import scala.reflect.api.Trees
import scala.reflect.api.Types
import scala.tools.nsc.Global


package object mina {
//  type Class = Types#Type
//  type Method = Global#DefDef
//  type Field = Global#ValDef
//  type Var = Global#TermName
//  type Tree = Global#Tree
//  type Name = Var
//  type TreeType = Trees#Tree
//  type LiteralType = Trees#Literal
  
  /**
   * Two identity functions, to tell the plugin to deal with the passed
   * expressions as a CT or RT value.
   */
  def CT[T](expr: T) = expr
  def RT[T](expr: T) = expr
}