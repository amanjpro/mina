::#!
@echo off
call scala -save -feature %0 %*
goto :eof
::!#

/*
 *  Copyright (c) <2013>, Amanj Sherwany <http://www.amanj.me>
 * All rights reserved.
 * A simple scala script, to automatically build the project and test it
 */

import sys.process._
import scala.io._
import java.io._
import scala.language.postfixOps

var compile = false
var run = false
var testAll = false
var helpf = false
var doc = false

val scalaVersion = "2.10"
val minaVersion = s"${scalaVersion}-1.0-beta"
val sp = File.separator
// The plugin jar file
val mina = s"target${sp}scala-${scalaVersion}${sp}mina_${minaVersion}.jar"
// Test files are in src/test/scala directory
val testBase = s"src${sp}test${sp}scala"
// All the test cases go to bin/test
val base = s"bin${sp}test${sp}"
// Tests compiled with the plugin are in bin/test/plugin
val testDest = s"${base}plugin"
// Tests compiled without the plugin are in bin/test/plain
val plainDest=s"${base}plain"

// Create a destination directory if there is not one
new File(testDest).mkdirs
// Create a destination direcotry if there is not one
new File(plainDest).mkdirs

def help = {
  val h = "This is a small shell script, to automatically build the project " +
    "(plugin) and test the plugin (against the provided test file(case))" +
    "\nCopyright (c) <2013>, Amanj Sherwany <http://www.amanj.me>\n" +
    "ALl rights reserved." 
  println(h)
}

def usage = {
  val usg = "Usage: ./test [options] TEST_FILE" +
     "\n[options] are optional, and they can be one of the following:" +
     "\n-h | --help to print this help message." +
     "\n-c | --compile to recompile and repackage the plugin." +
     "\n-r | --run to run the test case, after compiling it." +
     "\n-a | --all to compile all test cases, without running them." +
     "\n-d | --doc to generate the documentation.\n" + 
     "\nDo not write the .scala extension for the test program."
  println(usg)
}

def processArgs(opt: String): Unit = {
  opt match {
    case "-h" | "--help" =>
      usage
      help
      System.exit(0)
    case "-c" | "--compile" =>
      compile = true
    case "-r" | "--run" =>
      run = true
    case "-a" | "--all" =>
      testAll = true
    case "-d" | "--doc" =>
      doc = true
    case _ => 
      println(s"Invalid option: ${opt}")
      usage
      System.exit(1)
  }
}

if(args.length < 1) {
  usage
  System.exit(1)
}


if(!args.contains("-d") && ! args.contains("--doc") &&
  !args.contains("-a") && ! args.contains("--all"))
  args.init.foreach(processArgs(_))
else args.foreach(processArgs(_))


if (helpf){
  help
  System.exit(0)
}

val file = args.last

if(!doc && !testAll && file.startsWith("-")) {
  usage
  System.exit(1)
}

def dumb(o: OutputStream) = {}
def read(in: InputStream) = {
  var lines = Source.fromInputStream(in).getLines().mkString("\n")
  println(lines)
}
val pio = new ProcessIO(dumb, read, read)

// Build the project first
if(compile) {
  println("===========================")
  println("   Compiling the plugin    ")
  println("===========================")
  "sbt package" run(pio) exitValue
}

// Build the documentation api
if(doc) {
  println("===========================")
  println("    Generating Scaladoc    ")
  println("===========================")
  "sbt doc" run(pio) exitValue
  
  System.exit(0)
}

if(!testAll) {
  println("===========================")
  println("  Compiling the test case  ")
  println("===========================")
  
  // First compile it with the plugin
  val testFile = s"${testBase}${sp}${file}.scala"
  val dst1 = s"${testDest}${sp}${file.toLowerCase}"
  new File(dst1).mkdirs
  s"scalac -d ${dst1} -cp ${mina} -Xplugin:${mina} ${testFile}" run(pio) exitValue

  // Then compile it without the plugin
  val dst2 = s"${plainDest}${sp}${file.toLowerCase}"
  new File(dst2).mkdirs
  s"scalac -d ${dst2} -cp ${mina} ${testFile}" run(pio) exitValue
} else if(testAll) {
  println("===========================")
  println("  Compiling all test cases ")
  println("===========================")
  
  val testCases = 
    new File(testBase).listFiles.map(_.getName).filter(_.endsWith("scala"))
    
  for(tst <- testCases) {
    println(s"Compiling ${tst}")
    println("==========================================")

    // First compile it with the plugin
    val testFile = s"${testBase}${sp}${tst}"
    val dst1 = s"${testDest}${sp}${file.toLowerCase}"
    new File(dst1).mkdirs
    s"scalac -d ${dst1} -cp ${mina} -Xplugin:${mina} ${testFile}" run(pio) exitValue


    val dst2 = s"${plainDest}${sp}${file.toLowerCase}"
    new File(dst2).mkdirs
    // Then compile it without the plugin
    s"scalac -d ${dst2} -cp ${mina} ${testFile}" run(pio) exitValue
  }
}

if(!testAll && run) {
  println("===========================")
  println("   Running the test case   ")
  println("===========================")
  // Run the file once wihtout applying HPE
  
  s"scala -cp ${plainDest}${sp}${file.toLowerCase}:${mina} ${file}" run(pio) exitValue
  
  // Run the same file this time with applying HPE
  s"scala -cp ${testDest}${sp}${file.toLowerCase}:${mina} ${file}" run(pio) exitValue
} else if(testAll && run) {
  println("===========================")
  println("  Running all test cases   ")
  println("===========================")
  
  val testCases = 
    new File(testBase).listFiles.map(_.getName).filter(_.endsWith("scala"))
  
  for(tst <- testCases) {
    println(s"Running ${tst}")
    println("==========================================")
    val test = tst.replaceAll("[\\.]scala", "")
    // Run the file once wihtout applying HPE
    s"scala -cp ${plainDest}${sp}${file.toLowerCase}:${mina} ${test}" run(pio) exitValue
  
    // Run the same file this time with applying HPE
    s"scala -cp ${testDest}${sp}${file.toLowerCase}:${mina} ${test}" run(pio) exitValue
  }
}

System.exit(0)


