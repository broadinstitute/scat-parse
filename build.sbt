import Dependencies._
val scala212 = "2.12.21"
val scala213 = "2.13.16"
val scala3 = "3.3.6"

GlobalScope / tlCommandAliases ++= Map(
  "fmt" -> List("scalafmtAll", "scalafmtSbt"),
  "fmtCheck" -> List("scalafmtCheckAll", "scalafmtSbtCheck"),
  "prePR" -> List("githubWorkflowGenerate", "+fmt", "bench/compile", "+test")
)

ThisBuild / tlBaseVersion := "2.0"
/*
 * MiMa resets at the 2.0 major. Generalizing over the token type makes cats.parse.Parser0/Parser
 * aliases for cats.parse.generic.Parser0/Parser at the char alphabet, which erases the old classes
 * from the bytecode -- no filter covers a vanished class. 2.0 is source-compatible for char users
 * (the unchanged test suite is the proof) and binary-breaking, declared up front; see spec S7.
 */

ThisBuild / startYear := Some(2021)
ThisBuild / developers += tlGitHubDev("johnynek", "P. Oscar Boykin")

ThisBuild / crossScalaVersions := List(scala212, scala213, scala3)
ThisBuild / scalaVersion := scala213

ThisBuild / githubWorkflowAddedJobs ++= Seq(
  WorkflowJob(
    id = "coverage",
    name = "Generate coverage report",
    scalas = Nil,
    sbtStepPreamble = Nil,
    steps = List(WorkflowStep.Checkout) ++ WorkflowStep.SetupJava(
      githubWorkflowJavaVersions.value.toList
    ) ++ githubWorkflowGeneratedCacheSteps.value ++ List(
      WorkflowStep.Sbt(List("coverage", "rootJVM/test", "coverageAggregate")),
      WorkflowStep.Use(
        UseRef.Public(
          "codecov",
          "codecov-action",
          "v3"
        )
      )
    )
  )
)

ThisBuild / licenses := List(License.MIT)

lazy val root = tlCrossRootProject.aggregate(core, bench)

lazy val docs =
  project.in(file("site")).enablePlugins(TypelevelSitePlugin).dependsOn(core.jvm, bench)

lazy val core = crossProject(JSPlatform, JVMPlatform, NativePlatform)
  .crossType(CrossType.Full)
  .settings(
    name := "cats-parse",
    libraryDependencies ++=
      Seq(
        cats.value,
        munit.value % Test,
        munitScalacheck.value % Test
      ),
    libraryDependencies ++= {
      if (tlIsScala3.value) Nil else Seq("org.scala-lang" % "scala-reflect" % scalaVersion.value)
    },
    // for the generic.Parser[S, *] cats instances (kind-projector's -P vs Scala 3's native syntax,
    // which sbt-typelevel enables automatically once it sees the compiler plugin dependency below)
    libraryDependencies ++= {
      if (tlIsScala3.value) Nil
      else
        Seq(
          compilerPlugin(
            "org.typelevel" % "kind-projector" % "0.13.3" cross CrossVersion.full
          )
        )
    }
    // no mimaBinaryIssueFilters: with the 2.0 reset above there is no previous version to check
    // against, and every filter here named a class the cutover deleted
  )
  .jvmSettings(
    // We test against jawn on JVM for some json parsers
    libraryDependencies += jawnAst.value % Test
  )
  .jsSettings(
    coverageEnabled := false
  )
  .nativeSettings(
    coverageEnabled := false
  )

lazy val bench = project
  .enablePlugins(JmhPlugin, NoPublishPlugin)
  .settings(
    name := "bench",
    coverageEnabled := false,
    scalacOptions += "-Wconf:cat=unused-nowarn:s",
    Compile / unmanagedSources := {
      if (Set("2.12", "2.13").contains(scalaBinaryVersion.value)) {
        (Compile / unmanagedSources).value
      } else Nil
    },
    libraryDependencies ++= {
      if (Set("2.12", "2.13").contains(scalaBinaryVersion.value))
        Seq(
          fastParse,
          parsley,
          jawnAst.value,
          parboiled,
          attoCore
        )
      else Nil
    }
  )
  .dependsOn(core.jvm)
