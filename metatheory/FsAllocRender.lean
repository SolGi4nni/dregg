/-
# `FsAllocRender` — the machine-splice source for `MinaFinalizeScalars` §4's three tables.

Runs `AirColumnAlloc.allocate` on `finalizeSsa`'s live ranges and prints the value-indexed
`slotTable`/`loTable`/`hiTable` literals plus `NSLOTS` and the op count. The output is SPLICED
into `MinaFinalizeScalars.lean` by tooling — never hand-typed: the v1 `hiTable` hand-paste with
a fabricated tail (caught by `decide`) is the standing reason this file exists.

This file imports the PROGRAM half only (`MinaFinalizeScalarsProg`), not the table file — the
table file's `by decide` theorems are exactly the thing that is stale mid-render.

    cd metatheory && lake env lean --run FsAllocRender.lean
-/
import Dregg2.Circuit.Emit.MinaFinalizeScalarsProg

open Dregg2.Circuit.Emit.MinaFinalizeScalars
open Dregg2.Circuit.Emit.AirColumnAlloc

def main : IO Unit := do
  let ops := finalizeSsa
  let rs := liveRanges ops
  let placed := allocate rs
  let find := fun (v : Nat) => match placed.find? (fun p => p.1.val == v) with
    | some p => (p.2, p.1.lo, p.1.hi)
    | none => (0, 0, 0)
  let n := NVALS
  let slots := (List.range n).map (fun v => (find v).1)
  let los := (List.range n).map (fun v => (find v).2.1)
  let his := (List.range n).map (fun v => (find v).2.2)
  IO.println s!"-- NOPS = {finalizeProg.length}, NVALS = {n}"
  IO.println s!"def slotTable : List Nat := {slots}"
  IO.println s!"def loTable : List Nat := {los}"
  IO.println s!"def hiTable : List Nat := {his}"
  IO.println s!"def NSLOTS : Nat := {allocWidth rs}"
