/*
 * Copyright (c) <2013>, Amanj Sherwany <http://www.amanj.me>
 * All rights reserved.
 * */

package ch.usi.inf.l3.mina.store

import ch.usi.inf.l3.mina.eval._
import ch.usi.inf.l3.mina._

trait HPEEnvironmentWrapper {
  self: HPE =>
  import self.global._

  class Environment private (private val location: Map[TermName, Int],
    private val store: Map[Int, Value],
    private val loc: Int) {

    def this() {
      this(Map.empty, Map.empty, -1)
    }

    def getValue(v: TermName): Value = {
      location.get(v) match {
        case None => Bottom
        case Some(x) => store(x)
      }
    }

    def addValue(v: TermName, value: Value): Environment = {
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
    def addBatch(vars: List[TermName],
      source: Environment): Environment = {
      var tail = vars
      var tempStore = this
      while (tail != Nil) {
        val head = tail.head
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

    def newStore(varval: List[(TermName, Value)]): Environment = {
      var env = new Environment
      var tail = varval
      while (tail != Nil) {
        val (x, v) = tail.head
        env = env.addValue(x, v)
        tail = tail.tail
      }
      env
    }
    /**
     * Removes a variable from the environment
     *
     * @param v the variable to be removed
     * @return a new environment, which has the bindings of variable v removed
     */
    def remove(v: TermName): Environment = {
      val location2 = location - (v)
      new Environment(location2, store, loc)
    }

    private def getPEValue(v: TermName): Option[Value] = {
      location.get(v) match {
        case Some(loc) => store.get(loc)
        case _ => None
      }
    }

    def isCT(v: TermName): Boolean = {
      getPEValue(v) match {
        case Some(CTValue(_)) => true
        case _ => false
      }
    }

    def isRT(v: TermName): Boolean = {
      getPEValue(v) match {
        case Some(Top) => true
        case _ => false
      }
    }
  }

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

  private[mina] trait HPEAny {
    val tree: Tree;
    val tpe: Type;
  }
  private[mina] case class HPEObject(val tree: Tree, val tpe: Type,
    val store: Environment) extends HPEAny

  private[mina] case class HPELiteral(override val tree: Tree,
    override val tpe: Type) extends HPEAny
}