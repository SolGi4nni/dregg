/- Emit every accepting assignment for the three distinct Boolean descriptor
   shapes in the production workload study.  This creates independent Fiat-
   Shamir / query-PoW transcripts without changing the canonical emitter. -/

import Dregg2.Metatheory.DirectLogicDreggWorkloads

namespace DirectLogicStabilityTranscriptSweep

open Dregg2.Metatheory.DirectLogicOptimizerCertificate
open Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2
open Dregg2.Metatheory.DirectLogicDreggWorkloads
open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)

abbrev Formula := Dregg2.Metatheory.DirectLogicOptimizerCertificate.Formula

def outputDir : String :=
  "../docs/deos/artifacts/direct-logic-dregg-workloads-2026-07-22-stability-v2/transcript-sweep-inputs"

def bitsTruth {n : Nat} (bits : List Bool) (a : Fin n) : Bool := bits.getD a.val false

def renderInts (xs : List Int) : String :=
  String.intercalate "," (xs.map toString) ++ "\n"

def renderBools (xs : List Bool) : String :=
  String.intercalate "," (xs.map fun b => if b then "1" else "0") ++ "\n"

def emitCase {n : Nat} (shape assignment variant : String) (bits : List Bool)
    (p : Formula n) : IO String := do
  if bits.length != n then throw <| IO.userError s!"{shape}/{assignment}: bad bit count"
  let truth := bitsTruth bits
  unless eval truth p do throw <| IO.userError s!"{shape}/{assignment}: nonaccepting"
  let descriptor := publicDescriptor p
  let row := (List.range descriptor.traceWidth).map (canonicalRow truth p)
  let publicInputs := (List.range n).map (canonicalPublic truth)
  let stem := s!"{outputDir}/{shape}-{assignment}-{variant}"
  IO.FS.writeFile (stem ++ ".descriptor.json") (emitVmJson2 descriptor)
  IO.FS.writeFile (stem ++ ".trace.csv") (renderInts row)
  IO.FS.writeFile (stem ++ ".public.csv") (renderInts publicInputs)
  IO.FS.writeFile (stem ++ ".truth.csv") (renderBools bits)
  pure <| String.intercalate "," [shape, assignment, variant, toString n,
    toString descriptor.traceWidth, toString descriptor.constraints.length,
    toString (emitVmJson2 descriptor).length] ++ "\n"

def emitShape {n : Nat} (shape : String) (assignments : List (String × List Bool))
    (source optimized : Formula n) : IO String := do
  let mut rows := ""
  for (assignment, bits) in assignments do
    rows := rows ++ (← emitCase shape assignment "source" bits source)
    rows := rows ++ (← emitCase shape assignment "optimized" bits optimized)
  pure rows

def main : IO Unit := do
  IO.FS.createDirAll outputDir
  let admissionAssignments := [
    ("expiry-none", [true, true, true, true, false, true, true, true, true, true, true, true]),
    ("expiry-timed", [true, true, true, false, true, true, true, true, true, true, true, true]),
    ("expiry-both-abstract", [true, true, true, true, true, true, true, true, true, true, true, true])]
  let branchAssignments := [
    ("left", [true, true, true, false]),
    ("right", [true, true, false, true]),
    ("both", [true, true, true, true])]
  let strandAssignments := [
    ("seed", [true, false, false]), ("vouch", [false, true, false]),
    ("bond", [false, false, true]), ("seed-vouch", [true, true, false]),
    ("seed-bond", [true, false, true]), ("vouch-bond", [false, true, true]),
    ("all", [true, true, true])]
  let admission ← emitShape "admission" admissionAssignments AdmissionWorkload.source
    AdmissionWorkload.certificate.optimized
  let branch ← emitShape "branch" branchAssignments UpgradeWorkload.source
    UpgradeWorkload.certificate.optimized
  let strand ← emitShape "strand" strandAssignments StrandWorkload.source
    StrandWorkload.certificate.optimized
  IO.FS.writeFile (outputDir ++ "/manifest.csv")
    ("shape,assignment,variant,atoms,trace_width,constraints,descriptor_bytes\n" ++
      admission ++ branch ++ strand)
  IO.println "wrote all accepting assignments for three descriptor shapes"

end DirectLogicStabilityTranscriptSweep

def main : IO Unit := DirectLogicStabilityTranscriptSweep.main
