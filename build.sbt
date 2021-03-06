organization := "ch.usi.inf.l3"

licenses := ("BSD 3-Clause", new java.net.URL("http://opensource.org/licenses/BSD-3-Clause")) :: Nil

name := "mina"

version := "1.0-beta"

scalaVersion := "2.10.2"

libraryDependencies <+= scalaVersion("org.scala-lang" % "scala-compiler" % _ )

scalacOptions ++= Seq("-unchecked", "-deprecation", "-feature")

mappings in (Compile, packageBin) <+= baseDirectory map { base =>
   (base / "resources/" / "scalac-plugin.xml") -> "scalac-plugin.xml"
}