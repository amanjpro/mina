/*
 * Copyright (c) <2013>, Amanj Sherwany <http://www.amanj.me>
 * All rights reserved.
 * */
package ch.usi.inf.l3.mina.eval

import scala.tools.nsc.Global
import scala.tools.nsc.ast.TreeDSL
import scala.tools.nsc.plugins.Plugin
import scala.tools.nsc.plugins.PluginComponent
import scala.tools.nsc.transform.Transform
import scala.tools.nsc.transform.TypingTransformers
import scala.tools.nsc.ast.parser.TreeBuilder
import scala.reflect.runtime.universe._
import scala.language.implicitConversions
import ch.usi.inf.l3.mina._
import store._

class HPE(val global: Global) extends Plugin
  with HPEEnvironmentWrapper
  with HPEClassWrapper {
  
  import global._

  var env = new Environment
  val digraph = new ClassDigraph
  
  val name = "mina"
  val finder = s"${name}-finder"
  val specializer = s"${name}-specializer"
  val finalizer = s"${name}-finalizer"
  
  val description = """|This is a partial evaluator plugin based on Hybrid 
    |Partial Evaluation by W. Cook and A. Shali 
    |http://www.cs.utexas.edu/~wcook/Civet/"""

  /**
   * This plugin has three compiler phases:
   * 1- In the first phase, we draw a class diagram and find the members of
   *    each class
   * 2- In the second phase we try to collect as much information as possible
   *    about which method needs to be specialized.
   * 3- In the third phase, we specialize the methods that need to be
   *    specialized, and we change the method calls from unspecialized methods
   *    to their specialized versions.
   */
  val components = List[PluginComponent](
		  	new HPEFinder(this), new HPEFinalizer(this),
		      new HPESpecializer(this))


}