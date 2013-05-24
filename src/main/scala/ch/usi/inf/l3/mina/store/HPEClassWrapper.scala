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

  /*
   * ImplDef if a super class of both ClassDef (for classes) and ModuleDef 
   * for (objects)
   */
  class ClassRepr(val tpe: Type, private var classTree: ImplDef = null) {
    private var specialized: Map[(Name, List[Value]), DefDef] = Map.empty 
    def getNextMethod(base: TermName, values: List[Value]) = {
      val tail = values.toString.replaceAll("[\\[\\]]", "")
      val name = base.toString + "_m$_i$_"  + tail + "_n$_a$"
      newTermName(name)
    }

    def hasMember(name: TermName, t: Type): Boolean = {
      var flag = false
      if (hasClassTree) {
        for (
          m <- classTree.impl.body if (name == m.symbol.name && t =:= m.symbol.tpe)
        ) {
          flag = true
        }
      }
      flag
    }

    def getMemberTree(name: TermName, t: Type): Tree = {
      var flag = true
      var result: Tree = null
      if (hasClassTree) {
        for (
          m <- classTree.impl.body if (name == m.symbol.name && t =:= m.symbol.tpe)
        ) {
          flag = false
          result = m
        }
      }
      if (flag) {
        throw new HPEError(s"No member in class ${tpe} " +
          s"has the name ${name} with the type ${t}")
      } else
        result
    }

    override def equals(that: Any): Boolean = {
      that match {
        case x: ClassRepr => tpe == x.tpe
        case _ => false
      }
    }

    override def hashCode = 71 * 5 + tpe.##

    def tree_=(clazz: ImplDef): Unit = classTree = clazz

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

    def addSpecialized(name: Name, args: List[Value], method: DefDef) = {
      specialized = specialized + ((name, nullify(args)) -> method)
    }

    def getSpecialized(name: Name, args: List[Value]): DefDef = {
      specialized((name, nullify(args)))
    }

    def getSpecializedOption(name: Name, args: List[Value]): Option[DefDef] = {
      specialized.get((name, nullify(args)))
    }

    def hasSpecialized(name: Name, args: List[Value]): Boolean = {
      getSpecializedOption(name, args) match {
        case Some(x) => true
        case None => false
      }
    }

    override def toString(): String = tpe.toString
  }

  
  class ClassBank {
    private var nextClassID = 0

    
    private var speciazlized: Map[(Type, List[Value]), ClassRepr] = Map.empty
    

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

    def getNextClassName(base: TermName): TermName = {
      val newName = base + "_m$_i$_" + nextClassID + "_n$_a$"
      nextClassID = nextClassID + 1
      newTermName(newName)
    }

    def add(tpe: Type, args: List[Value], clazz: ClassRepr) = {
      
      speciazlized = speciazlized + ((tpe, nullify(args)) -> clazz)
    }

    def get(tpe: Type, args: List[Value]): ClassRepr = {
      speciazlized((tpe, nullify(args)))
    }

    def getOption(tpe: Type, args: List[Value]): Option[ClassRepr] = {
      speciazlized.get((tpe, nullify(args)))
    }

    def has(tpe: Type, args: List[Value]): Boolean = {
      getOption(tpe, args) match {
        case Some(x) => true
        case None => false
      }
    }
  }

  class ClassDigraph {
    type C = ClassRepr
    private var index = 0
    private var nodes = Map.empty[C, Int]
    private var reversed = Map.empty[Int, C]
    private var edges = Map.empty[Int, List[Int]]

    def findCompanionModule(name: String): Option[C] = {
      var r: Option[C] = None
      var tail = nodes.keys.toList
      while (tail != Nil) {
        val clazz = tail.head
        if (clazz.hasClassTree &&
          clazz.tree.name.toString == name &&
          clazz.tree.symbol.isModule) {
          r = Some(clazz)
        }
        tail = tail.tail
      }
      r
    }

    def addClass(clazz: C) = {
      nodes.contains(clazz) match {
        case false =>
          nodes = nodes + (clazz -> index)
          reversed = reversed + (index -> clazz)
          edges = edges + (index -> Nil)
          index += 1
        case true if (!clazz.hasClassTree) =>
          val index1 = nodes(clazz)
          val current = reversed(index1)
          if (!current.hasClassTree) {
            nodes = nodes + (clazz -> index1)
            reversed = reversed + (index1 -> clazz)
          }
        case _ =>
      }
    }

    def addSubclass(clazz: C, subclass: C) = {
      val f = getIndex(clazz)
      val t = getIndex(subclass)
      edges = edges + (f -> (t :: edges(getIndex(clazz))))
    }

    def getSubclasses(clazz: C): List[C] = {
      nodes.get(clazz) match {
        case Some(index) =>
          edges(index) match {
            case Nil => Nil
          	case cs => cs.map(reversed(_))
          }
        case None => Nil
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