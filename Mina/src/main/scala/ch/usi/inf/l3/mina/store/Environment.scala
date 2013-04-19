/*
 * Copyright (c) <2013>, Amanj Sherwany <http://www.amanj.me>
 * All rights reserved.
 * */

package ch.usi.inf.l3.mina.store

import ch.usi.inf.l3._
import mina._


class Environment private(private val location: Map[Var, Int], 
    private val store: Map[Int, Value], 
    private val loc: Int) {
  
  def this() {
    this(Map.empty, Map.empty, -1)
  }

  def getValue(v: Var): Option[Value] = {
    location.get(v) match {
      case None => None
      case Some(x) => store.get(x)
    }
  }

  def addValue(v: Var, value: Value): Environment = {
    location.get(v) match {
      case None => 
        val l = loc + 1
        val m = location + (v -> l)
        val s = store + (l -> value)
        new Environment(m, s, l)
      case Some(l) =>
        val s = store + (l -> value)
        new Environment(location, s, l)
    }
  }
  
  /**
   * A very important method for handling function calls on objects accurately.
   * 
   * This method makes sure to correctly pass all the parameter to the called 
   * method while still preserving the store of the object.
   * 
   * @param params a list of tuple of method parameters
   * @param sourse the source environment, to look for variables values from
   * @return a new environment which has all the information of its parameters
   */
  def addBatch(vars: List[Var], 
                      source: Environment): Environment = {
    var tail = vars
    var tempStore = this
    while(tail != Nil){
      val  head = tail.head
      tail = tail.tail
      val l = source.location(head)
      val value = source.store(l)
      val loc = tempStore.loc + 1
      tempStore = new Environment(tempStore.location + (head -> l),
                                      tempStore.store + (l -> value),
                                      loc)
    }
    
    tempStore
  }
  
  /**
   * Removes a variable from the environment
   * 
   * @param v the variable to be removed
   * @return a new environment, which has the bindings of variable v removed
   */
  def remove(v: Var): Environment = {
    val location2 = location - (v)
    new Environment(location2, store, loc)
  }
  
  private def getPEValue(v: Var): Option[Value] = {
    location.get(v) match{
      case Some(loc) => store.get(loc)
      case _ => None
    }
  }
  
  def isCT(v: Var): Boolean = {
    getPEValue(v) match{
      case Some(CTValue(_)) => true
      case _ => false
    }
  }

  def isRT(v: Var): Boolean = {
    getPEValue(v) match{
      case Some(Top) => true
      case _ => false
    }
  }
}

