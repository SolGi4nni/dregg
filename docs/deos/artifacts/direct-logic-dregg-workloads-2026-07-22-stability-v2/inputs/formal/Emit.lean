/-
# Lean-authored fixtures for the production-derived direct-logic benchmark

This executable imports the formal source of truth and emits both the naive
source and certified optimized public DescriptorIR2 objects, plus the exact
canonical one-row traces consumed by the Rust benchmark.  It does not rebuild
either formula or trace in another language.

Run from `metatheory/`:

    lake env lean --run ../tools/direct-logic-dregg-benchmark/Emit.lean

The checked-in output directory must already exist.  The emitter overwrites
only its own `generated/` fixtures.
-/

import Dregg2.Metatheory.DirectLogicDreggWorkloads

namespace DirectLogicDreggBenchmarkEmitter

open Dregg2.Metatheory.DirectLogicOptimizerCertificate
open Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2
open Dregg2.Metatheory.DirectLogicDreggWorkloads
open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)

abbrev Formula := Dregg2.Metatheory.DirectLogicOptimizerCertificate.Formula

def outputDir : String := "../tools/direct-logic-dregg-benchmark/generated"

def bitsTruth {n : Nat} (bits : List Bool) (a : Fin n) : Bool :=
  bits.getD a.val false

def admissionBits : List Bool :=
  [true, true, true, true, false, true, true, true, true, true, true, true]

def upgradeBits : List Bool := [true, true, false, true]

def clearanceBits : List Bool := [true, true, true, false]

def strandBits : List Bool := [true, false, false]

#guard admissionBits.length == 12
#guard upgradeBits.length == 4
#guard clearanceBits.length == 4
#guard strandBits.length == 3

#guard eval (bitsTruth admissionBits) AdmissionWorkload.source
#guard eval (bitsTruth admissionBits) AdmissionWorkload.certificate.optimized
#guard eval (bitsTruth upgradeBits) UpgradeWorkload.source
#guard eval (bitsTruth upgradeBits) UpgradeWorkload.certificate.optimized
#guard eval (bitsTruth clearanceBits) ClearanceWorkload.source
#guard eval (bitsTruth clearanceBits) ClearanceWorkload.certificate.optimized
#guard eval (bitsTruth strandBits) StrandWorkload.source
#guard eval (bitsTruth strandBits) StrandWorkload.certificate.optimized

def renderInts (xs : List Int) : String :=
  String.intercalate "," (xs.map toString) ++ "\n"

def renderBools (xs : List Bool) : String :=
  String.intercalate "," (xs.map fun b => if b then "1" else "0") ++ "\n"

def manifestHeader : String :=
  "workload,variant,atoms,trace_width,public_inputs,constraints," ++
  "graph_constraints,multiplications,auxiliaries,descriptor_bytes,formula_true\n"

def emitCase {n : Nat} (workload variant : String) (truthBits : List Bool)
    (p : Formula n) : IO String := do
  if truthBits.length != n then
    throw <| IO.userError s!"{workload}-{variant}: truth vector has wrong length"
  let truth := bitsTruth truthBits
  unless eval truth p do
    throw <| IO.userError s!"{workload}-{variant}: selected assignment is not accepting"
  let descriptor := publicDescriptor p
  let row := (List.range descriptor.traceWidth).map (canonicalRow truth p)
  let publicInputs := (List.range n).map (canonicalPublic truth)
  let stem := s!"{outputDir}/{workload}-{variant}"
  let descriptorBytes := emitVmJson2 descriptor
  IO.FS.writeFile (stem ++ ".descriptor.json") descriptorBytes
  IO.FS.writeFile (stem ++ ".trace.csv") (renderInts row)
  IO.FS.writeFile (stem ++ ".public.csv") (renderInts publicInputs)
  IO.FS.writeFile (stem ++ ".truth.csv") (renderBools truthBits)
  pure <| String.intercalate ","
    [workload, variant, toString n, toString descriptor.traceWidth,
      toString descriptor.piCount, toString descriptor.constraints.length,
      toString (graphConstraints p).length, toString (emittedMultiplications p),
      toString (witnessCount p), toString descriptorBytes.length, "true"] ++ "\n"

def emitPair {n : Nat} (workload : String) (truthBits : List Bool)
    (source optimized : Formula n) : IO String := do
  let sourceRow ← emitCase workload "source" truthBits source
  let optimizedRow ← emitCase workload "optimized" truthBits optimized
  pure (sourceRow ++ optimizedRow)

def main : IO Unit := do
  let admission ← emitPair "admission" admissionBits AdmissionWorkload.source
    AdmissionWorkload.certificate.optimized
  let upgrade ← emitPair "upgrade" upgradeBits UpgradeWorkload.source
    UpgradeWorkload.certificate.optimized
  let clearance ← emitPair "clearance" clearanceBits ClearanceWorkload.source
    ClearanceWorkload.certificate.optimized
  let strand ← emitPair "strand" strandBits StrandWorkload.source
    StrandWorkload.certificate.optimized
  let manifest := manifestHeader ++ admission ++ upgrade ++ clearance ++ strand
  IO.FS.writeFile (outputDir ++ "/manifest.csv") manifest
  IO.println s!"wrote 8 Lean-authored descriptor/trace fixture sets to {outputDir}"

end DirectLogicDreggBenchmarkEmitter

def main : IO Unit := DirectLogicDreggBenchmarkEmitter.main
