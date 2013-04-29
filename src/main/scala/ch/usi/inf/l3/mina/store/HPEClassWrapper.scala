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
  
  class ClassRepr(val name: TermName) {
    private var classTree: Tree = null
    private var methods: Map[TermName, DefDef] = Map.empty
    private var fields: Map[TermName, ValDef] = Map.empty

    def addMethod(n: TermName, method: DefDef): Unit = {
      methods = methods + (n -> method)
    }

    def addField(n: TermName, field: ValDef): Unit = {
      fields = fields + (n -> field)
    }

    def hasMember(n: TermName): Boolean = {
      fields.contains(n) || methods.contains(n)
    }

    def getMemberTree(n: TermName): Tree = {
      if (fields.contains(n)) fields(n)
      else if (methods.contains(n)) methods(n)
      else
        throw new HPEError(s"""|No member in class ${name} 
      					     |has the member ${name}""")
    }
    def getFieldTree(n: TermName): Option[ValDef] = fields.get(n)

    def getMethodTree(n: TermName): Option[DefDef] = methods.get(n)

    def tree_=(clazz: Tree): Unit = classTree = clazz

    def tree: Tree = classTree match {
      case null => throw new HPEError(s"""${classTree} is null""")
      case _ => classTree
    }
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
      println(args)
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

}