/*
 * Copyright (c) <2013>, Amanj Sherwany <http://www.amanj.me>
 * All rights reserved.
 * */

package ch.usi.inf.l3.mina.store

import ch.usi.inf.l3._
import mina._

class ClassBank {
  private var nextClassID = 0

  private var classes: List[Class] = Nil
  private var speciazlized: Map[(String, List[Value]), Class] = Map.empty
  def getAllSpecializedClasses = classes

  private def nullify(args: List[Value]): List[Value] = {
    var temp: List[Value] = Nil
    for (arg <- args) {
      arg match {
        case x: CTValue => temp = x :: temp
        case _ => temp = Bottom :: temp
      }
    }
    temp.reverse
  }

  def getClassName(base: String) = {
    val newName = base + "_" + nextClassID
    nextClassID = nextClassID + 1
    newName
  }

  def add(cname: String, args: List[Value], clazz: Class) = {
    classes = clazz :: classes
    speciazlized = speciazlized + ((cname, nullify(args)) -> clazz)
  }

  def get(cname: String, args: List[Value]): Class = {
    speciazlized((cname, nullify(args)))
  }

  def getOption(cname: String, args: List[Value]): Option[Class] = {
    speciazlized.get((cname, nullify(args)))
  }

  def has(cname: String, args: List[Value]): Boolean = {
    getOption(cname, args) match {
      case Some(x) => true
      case None => false
    }
  }
}