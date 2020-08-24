import Dependencies._

ThisBuild / scalaVersion     := "2.13.3"
ThisBuild / version          := "0.1.0-SNAPSHOT"
ThisBuild / organization     := "com.example"
ThisBuild / organizationName := "example"

lazy val smallcheck = RootProject(file("../smallcheck4scala/"))

lazy val root = (project in file("."))
  .settings(
    name := "scala-logic-eval",
    resolvers += "jitpack" at "https://jitpack.io",
    libraryDependencies += scalaTest % Test,
    libraryDependencies += "org.scalacheck" %% "scalacheck" % "1.14.1" % Test,
    libraryDependencies += "com.chuusai" %% "shapeless" % "2.3.3",
    libraryDependencies += "org.scala-lang" % "scala-reflect" % scalaVersion.value,
//      libraryDependencies += "com.github.peterzeller" % "smallcheck4scala" % "54fc87c616" % Test
  ).dependsOn(smallcheck)



// See https://www.scala-sbt.org/1.x/docs/Using-Sonatype.html for instructions on how to publish to Sonatype.
