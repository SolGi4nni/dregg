// fhegg-rtl / hardware / spinalhdl / build.sbt  —  STUB
//
// A commented scaffold, NOT a resolving build. A contributor picking up milestone M0
// (see ../../CONTRIBUTING.md) uncomments the SpinalHDL dependency, sets a real Scala version,
// and runs `sbt "runMain ButterflyGen"` to elaborate Butterfly.scala to Verilog.
//
// TODO(contributor): pin the current SpinalHDL release (check spinalhdl.github.io for the
// latest `spinalHdlVersion`) and the matching Scala version.
//
// ThisBuild / scalaVersion := "2.12.18"
//
// val spinalHdlVersion = "1.10.1"   // TODO: bump to current
// libraryDependencies ++= Seq(
//   "com.github.spinalhdl" %% "spinalhdl-core" % spinalHdlVersion,
//   "com.github.spinalhdl" %% "spinalhdl-lib"  % spinalHdlVersion,
//   compilerPlugin("com.github.spinalhdl" %% "spinalhdl-idsl-plugin" % spinalHdlVersion)
// )
//
// lazy val fheggRtl = (project in file("."))
//   .settings(name := "fhegg-rtl-hardware")
