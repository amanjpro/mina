/*
 * Copyright (c) <2013>, Amanj Sherwany <http://www.amanj.me>
 * All rights reserved.
 * */

package ch.usi.inf.l3.mina.store

import ch.usi.inf.l3._
import mina._

class MethodBank {
  private var methods: List[Method] = Nil
  private var specialized: Map[(String, List[Value]), Method] = Map.empty
  private var nextMethodID = 0
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

  def getSpecializedMethodsList = methods
  
  def getMethodName(base: String) = {
    val newName = base + "_" + nextMethodID
    nextMethodID += 1
    newName
  }

  def add(name: String, args: List[Value], method: Method) = {
    methods = method :: methods
    specialized = specialized + ((name, nullify(args)) -> method)
  }

  def get(name: String, args: List[Value]): Method = {
    println(args)
    specialized((name, nullify(args)))
  }

  def getOption(name: String, args: List[Value]): Option[Method] = {
    specialized.get((name, nullify(args)))
  }

  def has(name: String, args: List[Value]): Boolean = {
    getOption(name, args) match {
      case Some(x) => true
      case None => false
    }
  }
  
}
