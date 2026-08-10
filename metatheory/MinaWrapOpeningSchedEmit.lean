/-
# `mina_wrap_opening_sched_emit` — the `dregg-mina-wrap-opening-sched::v1` artifacts.

Renders, from the Lean objects and nothing else:

  * the DESCRIPTOR — `MinaWrapOpeningSched.openingSchedDesc`, serialized by `emitVmJson2`;
  * the HONEST trace + PI vector — the 35-addend opening chain of Mina devnet block 539508
    (`openingAddends`, the literal manifest whose derivation from the Gate's own term list is
    `the_manifest_is_the_derivation`), folded block by block on the scheduled row;
  * two FORGED traces, each an honest trace of a perturbed object:
      - `forged-sg` — ⚑ THE VACUITY'S OWN MOVE: the aggregate slot re-scaled onto `ft_comm` and
        the `sg` slot SOLVED as `−Σ(everything else)`. The chain VANISHES — as a group equation
        the forgery is perfect — and the manifest pins are what refuse it.
      - `forged-fold` — one mid-chain op's destination bumped, everything downstream recomputed
        honestly from the corruption: the op gate refuses, and the falsifier stays inside every
        declared width.

The renderer REFUSES before writing unless: the honest terminal is the identity; the forged-sg
chain closes AND its slot-0 addend differs from the pinned one; the forged-fold terminal is NOT
the identity. A renderer/manifest drift kills the emit rather than the fixtures.

This file only RENDERS; it authors nothing. House Law #1.

    lake build mina_wrap_opening_sched_emit
    ./.lake/build/bin/mina_wrap_opening_sched_emit ../circuit/tests/fixtures

The descriptor JSON and PI vectors are small and TRACKED; the three traces are 2048×581 (~5 MB
each) and are NOT tracked — the Rust test names this command when they are absent.
-/
import Dregg2.Circuit.Emit.MinaWrapOpeningSched
import Dregg2.Circuit.Emit.MinaWrapConjunctionAir

open Dregg2.Circuit.Emit.MinaWrapOpeningSched
open Dregg2.Circuit.Emit.PastaCurveScheduled
  (rcbSchedule OpKind slotOf SEL_IDLE)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaFieldSound (SK SB NG pLimb limbAt COFF)
open Dregg2.Circuit.Emit.PastaCurveSound (smCarryOf)
open Dregg2.Circuit.Emit.MinaWrapConjunctionAir (limbBlock mulWitBlock addSubWitBlock)
open Dregg2.Circuit.Emit.PastaCurveComplete (curveB3 isInfM)
open Dregg2.Circuit.Emit.MinaWrapOpeningGate (SG)
open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)

namespace OpenSchedEmit

abbrev Pt := Dregg2.Circuit.Emit.MinaWrapGroupGate.Pt

def HEIGHT : Nat := 2048
def LIVE : Nat := 35 * 33

/-! ## The block evaluator — the scheduled RCB SSA, one value per op, mod the Pallas base prime. -/

/-- The 39 values of one block: inputs 0..5 (acc ‖ addend), then the schedule's own SSA. An
optional `corrupt` op index bumps that op's destination by 1 and lets everything downstream
consume the corruption honestly. -/
def blockVals (acc addend : Pt) (corrupt : Option Nat) : Array Nat := Id.run do
  let mut vals : Array Nat := Array.replicate 39 0
  vals := ((vals.set! 0 acc.1).set! 1 acc.2.1).set! 2 acc.2.2
  vals := ((vals.set! 3 addend.1).set! 4 addend.2.1).set! 5 addend.2.2
  for i in List.range rcbSchedule.length do
    match rcbSchedule[i]? with
    | some t =>
      let vx := vals.getD t.2.2.1 0
      let vy := vals.getD t.2.2.2 0
      let v := match t.1 with
        | .mul  => vx * vy % pN
        | .add  => (vx + vy) % pN
        | .sub  => (vx + pN - vy) % pN
        | .smul => (curveB3 * vx) % pN
      let v := if corrupt == some i then (v + 1) % pN else v
      vals := vals.set! t.2.1 v
    | none => pure ()
  return vals

/-- Slot tenancy per LOCAL row — fixed across blocks, computed from the allocator's own `slotOf`. -/
def tenantAt : Array (Array (Option Nat)) := Id.run do
  let mut cur : Array (Option Nat) := Array.replicate 11 none
  for v in List.range 6 do
    cur := cur.set! (slotOf v) (some v)
  let mut out : Array (Array (Option Nat)) := #[]
  for r in List.range 33 do
    match rcbSchedule[r]? with
    | some t => cur := cur.set! (slotOf t.2.1) (some t.2.1)
    | none => pure ()
    out := out.push cur
  return out

/-- The 95-cell witness pool of one row: `w1 (1) ‖ w8 (32) ‖ w16 (62)`, in pool order. -/
def witPool (vals : Array Nat) (r : Nat) : List Int :=
  match rcbSchedule[r]? with
  | some t =>
    let xv := vals.getD t.2.2.1 0
    let yv := vals.getD t.2.2.2 0
    let zv := vals.getD t.2.1 0
    match t.1 with
    | .mul  => 0 :: mulWitBlock pN pLimb xv yv zv
    | .add  => addSubWitBlock pN pLimb false xv yv zv ++ List.replicate 63 0
    | .sub  => addSubWitBlock pN pLimb true xv yv zv ++ List.replicate 63 0
    | .smul =>
      let qv := (curveB3 * xv - zv) / pN
      (0 : Int) :: List.replicate 31 0
        ++ [(qv : Int)]
        ++ (List.range 31).map (fun i => smCarryOf xv zv qv pLimb (curveB3 : ℤ) (i + 1) + COFF)
        ++ List.replicate 31 0
  | none => List.replicate 95 0

/-- One LIVE row's `OPEN_W` cells. -/
def rowCells (vals : Array Nat) (b r goBit : Nat) (sgRow : Bool) : List Int :=
  let sel : List Int := (List.range 34).map (fun i => if i == r then 1 else 0)
  let tens := tenantAt.getD r #[]
  let slots : List Int := (List.range 11).flatMap (fun s =>
    match tens.getD s none with
    | some v => limbBlock (vals.getD v 0)
    | none => List.replicate SK 0)
  let blk : List Int := (List.range NBLOCKS).map (fun x => if x == b then 1 else 0)
  let sgxy : List Int :=
    if sgRow then
      (List.range SK).map (fun j => limbAt SG.1 j) ++ (List.range SK).map (fun j => limbAt SG.2.1 j)
    else List.replicate (2 * SK) 0
  sel ++ slots ++ witPool vals r ++ [(goBit : Int)] ++ blk ++ sgxy

/-- One IDLE row: the register parked, the accumulator held, block indicator at 34. -/
def idleRow (acc : Pt) : List Int := Id.run do
  let sel : List Int := List.replicate 33 0 ++ [1]
  -- value slots: the three accumulator slots hold; everything else is quiet.
  let mut slotVals : Array (Option Nat) := Array.replicate 11 none
  slotVals := slotVals.set! (slotOf 0) (some acc.1)
  slotVals := slotVals.set! (slotOf 1) (some acc.2.1)
  slotVals := slotVals.set! (slotOf 2) (some acc.2.2)
  let slots : List Int := (List.range 11).flatMap (fun s =>
    match slotVals.getD s none with
    | some v => limbBlock v
    | none => List.replicate SK 0)
  let blk : List Int := (List.range NBLOCKS).map (fun x => if x == NBLOCKS - 1 then 1 else 0)
  return sel ++ slots ++ List.replicate 95 0 ++ [0] ++ blk ++ List.replicate (2 * SK) 0

/-- The whole chain: 35 blocks × 33 rows, then the idle tail; returns the rows and the terminal
accumulator (the last block's `(X3, Y3, Z3)`). -/
def renderChain (addends : List Pt) (corrupt : Option (Nat × Nat)) :
    Array (List Int) × Pt := Id.run do
  let mut rows : Array (List Int) := #[]
  let mut acc : Pt := (0, 1, 0)
  for b in List.range NBLOCKS do
    let addend := addends.getD b (0, 1, 0)
    let corr : Option Nat := match corrupt with
      | some p => if p.1 == b then some p.2 else none
      | none => none
    let vals := blockVals acc addend corr
    for r in List.range 33 do
      let goBit := if r == 32 && b + 1 < NBLOCKS then 1 else 0
      rows := rows.push (rowCells vals b r goBit (b == 0 && r == 0))
    acc := (vals.getD 32 0, vals.getD 35 0, vals.getD 38 0)
  for _ in List.range (HEIGHT - LIVE) do
    rows := rows.push (idleRow acc)
  return (rows, acc)

/-- The PI vector: `acc_in = O` ‖ `acc_out = terminal` ‖ `sg.x` ‖ `sg.y`. -/
def piCells (terminal : Pt) : List Int :=
  limbBlock 0 ++ limbBlock 1 ++ limbBlock 0
    ++ limbBlock terminal.1 ++ limbBlock terminal.2.1 ++ limbBlock terminal.2.2
    ++ (List.range SK).map (fun j => limbAt SG.1 j)
    ++ (List.range SK).map (fun j => limbAt SG.2.1 j)

def renderRow (cells : List Int) : String :=
  String.intercalate " " (cells.map toString)

def writeTrace (path : System.FilePath) (rows : Array (List Int)) : IO Unit := do
  let h ← IO.FS.Handle.mk path IO.FS.Mode.write
  for r in rows do
    h.putStrLn (renderRow r)

def writePis (path : System.FilePath) (terminal : Pt) : IO Unit :=
  IO.FS.writeFile path (renderRow (piCells terminal) ++ "\n")

/-- The forged-sg addend list — the module's own §4 objects, not a re-derivation. -/
def forgedSgAddends : List Pt := solvedAddend :: forgedTail

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "../circuit/tests/fixtures"
  IO.FS.createDirAll dir
  let p := fun (s : String) => System.FilePath.mk dir / s
  -- REFUSAL 1: the honest chain closes.
  let (honestRows, honestT) := renderChain openingAddends none
  unless isInfM pN honestT do
    IO.eprintln "REFUSED: the honest opening chain does not terminate at the identity"
    return 1
  -- REFUSAL 2: the renderer's fold agrees with the module's own chainFold.
  let spec := chainFold openingAddends
  unless honestT == spec do
    IO.eprintln "REFUSED: the renderer's fold drifts from `chainFold` — renderer bug"
    return 1
  -- REFUSAL 3: the forged-sg chain closes and its slot 0 is NOT the pinned addend.
  let (forgedSgRows, forgedSgT) := renderChain forgedSgAddends none
  unless isInfM pN forgedSgT do
    IO.eprintln "REFUSED: the solved-sg forgery does not close — the exhibit is broken"
    return 1
  unless solvedAddend != openingAddends.getD 0 (0, 1, 0) do
    IO.eprintln "REFUSED: the solved addend IS the pinned one — the falsifier falsifies nothing"
    return 1
  -- REFUSAL 4: the corrupted-fold chain does NOT close.
  let (forgedFoldRows, forgedFoldT) := renderChain openingAddends (some (2, 0))
  unless !(isInfM pN forgedFoldT) do
    IO.eprintln "REFUSED: the corrupted fold still closes — the falsifier falsifies nothing"
    return 1
  -- REFUSAL 5: shape.
  unless honestRows.size == HEIGHT && (honestRows.getD 0 []).length == OPEN_W do
    IO.eprintln s!"REFUSED: trace shape {honestRows.size}×{(honestRows.getD 0 []).length}, wanted {HEIGHT}×{OPEN_W}"
    return 1
  IO.println s!"terminal (honest)      = ({honestT.1}, {honestT.2.1}, {honestT.2.2})"
  IO.println s!"terminal (forged-sg)   = ({forgedSgT.1}, {forgedSgT.2.1}, {forgedSgT.2.2})"
  IO.println s!"terminal (forged-fold X%p==0) = {forgedFoldT.1 % pN == 0}"
  IO.FS.writeFile (p "mina-wrap-opening-sched.json") (emitVmJson2 openingSchedDesc)
  IO.println "descriptor written"
  writePis (p "mina-wrap-opening-sched-pis.txt") honestT
  writePis (p "mina-wrap-opening-sched-forged-sg-pis.txt") forgedSgT
  writePis (p "mina-wrap-opening-sched-forged-fold-pis.txt") forgedFoldT
  IO.println "PI vectors written"
  writeTrace (p "mina-wrap-opening-sched-trace.txt") honestRows
  writeTrace (p "mina-wrap-opening-sched-forged-sg-trace.txt") forgedSgRows
  writeTrace (p "mina-wrap-opening-sched-forged-fold-trace.txt") forgedFoldRows
  IO.println "traces written"
  return 0

end OpenSchedEmit

def main (args : List String) : IO UInt32 := OpenSchedEmit.main args
