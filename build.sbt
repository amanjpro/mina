name := "mina"

version := "1.0"

scalaVersion := "2.10.1"

libraryDependencies <+= scalaVersion("org.scala-lang" % "scala-compiler" % _ )

scalacOptions ++= Seq("-unchecked", "-deprecation", "-feature")

mappings in (Compile, packageBin) <+= baseDirectory map { base =>
   (base / "resources/" / "scalac-plugin.xml") -> "scalac-plugin.xml"
}