/*
 * Copyright (c) <2013>, Amanj Sherwany <http://www.amanj.me>
 * All rights reserved.
 * */

package ch.usi.inf.l3.mina.store

import ch.usi.inf.l3._
import mina._
import mina.eval._

private[mina] trait HPEClassWrapper {
  self: HPE with HPEEnvironmentWrapper =>
  import HPEClassWrapper.this.global._

  class ClassRepr(val tpe: Type, private var classTree: ImplDef = null) {
    
    def hasMember(name: TermName, t: Type): Boolean = {
      var flag = false
      if (hasClassTree) {
        for (m <- classTree.impl.body 
            if(name == m.symbol.name && t == m.symbol.tpe)) {
          flag = true
        }
      }
      flag
    }

    def getMemberTree(name: TermName, t: Type): Tree = {
      var flag = true
      var result: Tree = null
      if (hasClassTree) {
        for (m <- classTree.impl.body 
            if(name == m.symbol.name && t == m.symbol.tpe)) {
          flag = false
          result = m
        }
      }
      if(flag)
        throw new HPEError(s"No member in class ${tpe} " +
        		s"has the name ${name} with the type ${t}")
      else
        result
    }

    override def equals(that: Any): Boolean = {
      that match {
        case x: ClassRepr => tpe == x.tpe
        case _ => false
      }
    }

    override def hashCode = 71 * 5 + tpe.##

    def tree_=(clazz: ClassDef): Unit = classTree = clazz

    def hasClassTree() = {
      classTree match {
        case null => false
        case _ => true
      }
    }

    def tree: ImplDef = classTree match {
      case null => throw new HPEError(s"""${classTree} is null + ${tpe}""")
      case _ => classTree
    }

    override def toString(): String = tpe.toString
  }

  class MethodBank {
    private var methods: List[DefDef] = Nil
    private var specialized: Map[(String, List[Value]), DefDef] = Map.empty
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

    def add(name: String, args: List[Value], method: DefDef) = {
      methods = method :: methods
      specialized = specialized + ((name, nullify(args)) -> method)
    }

    def get(name: String, args: List[Value]): DefDef = {
      specialized((name, nullify(args)))
    }

    def getOption(name: String, args: List[Value]): Option[DefDef] = {
      specialized.get((name, nullify(args)))
    }

    def has(name: String, args: List[Value]): Boolean = {
      getOption(name, args) match {
        case Some(x) => true
        case None => false
      }
    }

    class ClassBank {
      private var nextClassID = 0

      private var classes: List[ClassRepr] = Nil
      private var speciazlized: Map[(String, List[Value]), ClassRepr] = Map.empty
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

      def add(cname: String, args: List[Value], clazz: ClassRepr) = {
        classes = clazz :: classes
        speciazlized = speciazlized + ((cname, nullify(args)) -> clazz)
      }

      def get(cname: String, args: List[Value]): ClassRepr = {
        speciazlized((cname, nullify(args)))
      }

      def getOption(cname: String, args: List[Value]): Option[ClassRepr] = {
        speciazlized.get((cname, nullify(args)))
      }

      def has(cname: String, args: List[Value]): Boolean = {
        getOption(cname, args) match {
          case Some(x) => true
          case None => false
        }
      }
    }

  }

  class ClassDigraph {
    type C = ClassRepr
    private var index = 0
    private var nodes = Map.empty[C, Int]
    private var reversed = Map.empty[Int, C]
    private var edges = Map.empty[Int, Int]

    def addClass(clazz: C) = {
      nodes.contains(clazz) match {
        case false =>
          nodes = nodes + (clazz -> index)
          reversed = reversed + (index -> clazz)
          index += 1
        case true if (!clazz.hasClassTree) =>
          val index1 = nodes(clazz)
          val current = reversed(index1)
          if (! current.hasClassTree) {
            nodes = nodes + (clazz -> index1)
            reversed = reversed + (index1 -> clazz)
          }
        case _ =>
      }
    }

    def addSubclass(clazz: C, subclass: C) = {
      val f = getIndex(clazz)
      val t = getIndex(subclass)
      edges = edges + (f -> t)
    }

    def getSubclass(clazz: C): Option[C] = {
      nodes.get(clazz) match {
        case Some(index) =>
          edges.get(index) match {
            case Some(parent) => reversed.get(parent)
            case None => None
          }
        case None => None
      }
    }

    def getClassRepr(tpe: Type): Option[ClassRepr] = {
      val temp = new ClassRepr(tpe)
      nodes.get(temp) match {
        case None => None
        case Some(index) =>
          val clazz = reversed(index)
          clazz.hasClassTree match {
            case true => Some(clazz)
            case _ => None
          }

      }
    }

    private def getIndex(node: C): Int = {
      nodes.contains(node) match {
        case false =>
          addClass(node)
          nodes(node)
        case true =>
          nodes(node)
      }
    }
  }

}