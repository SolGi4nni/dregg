/-
# `mina_finalize_scalars_emit` — the `dregg-mina-finalize-scalars::v1` artifacts.

Renders, from the Lean objects and nothing else:

  * the DESCRIPTOR — `MinaFinalizeScalars.finalizeDesc`, serialized by `emitVmJson2`;
  * the HONEST trace + PI vector — Mina devnet block 539508's own Wrap-side wire
    (`MinaRealBlockGate.EVZ/EVZW`'s 47-entry es columns, its raw β/γ and mapped α/ζ/ξ/r, the
    block's `combined_inner_product` and o1-labs' own `perm_scalars` value
    `MinaWrapGroupGate.PERM_SCALAR` as the two claims, and the witnessed inverse computed by
    Fermat's ladder, checked in-trace by the `den·DINV = 1` gate);
  * three FORGED traces, each an honest trace of a perturbed environment:
      - `forged-eval`  — one eval input bumped by 1 (inside the 8-bit limb width), claims kept:
        the cip equality gate must refuse, and nothing else moves;
      - `forged-perm`  — the perm claim bumped by 1: the perm equality gate must refuse;
      - `lct-shift`    — ⚑ the PORT EXHIBIT: `LCT` bumped and the cip claim RECOMPUTED to match.
        This trace PROVES AND VERIFIES — the measured demonstration that the `LCT` port admits a
        one-parameter family of accepting claims until the gate-linearization leaf closes it.
        Emitted so the Rust suite can assert the acceptance rather than prose it.

⚑ The cell values come from a MEMOIZED array evaluator (`valsOf`, one pass over the 301 ops);
before writing anything the driver REFUSES unless that evaluator agrees with the AIR file's own
`progEval` at the two output indices AND both meet the block's `combined_inner_product` and
o1-labs' `perm_scalars` — so a drift between the renderer and the specified denotation, or
between the program and the block, kills the emit rather than the fixtures.

This file only RENDERS; it authors nothing. House Law #1.

    lake build mina_finalize_scalars_emit
    ./.lake/build/bin/mina_finalize_scalars_emit ../circuit/tests/fixtures

The descriptor JSON and the PI vectors are small and TRACKED; the four traces are 512×4461
(~9 MB each) and are NOT tracked — the Rust test names this command when they are absent.
-/
import Dregg2.Circuit.Emit.MinaFinalizeScalarsWeld
import Dregg2.Circuit.Emit.MinaWrapConjunctionAir

open Dregg2.Circuit.Emit.MinaFinalizeScalars
open Dregg2.Circuit.Emit.PastaField (qN)
open Dregg2.Circuit.Emit.PastaFieldSound (SK SB NG qLimb limbAt)
open Dregg2.Circuit.Emit.PastaAddSubSound (NA)
open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.MinaWrapConjunctionAir (limbBlock mulWitBlock addSubWitBlock)
open Dregg2.Bridge.MinaWrapFtEval0 (invCand invOk)

namespace FsEmit

abbrev Fq := ZMod qN

open Dregg2.Circuit.Emit.MinaFinalizeScalarsWeld
  (env0Real cipResultV permResultV bump)

/-! ## The memoized evaluator and the trace generator. -/

/-- All 301 computed values, one pass, array-memoized. -/
def valsOf (env0 : Nat → Fq) : Array Fq :=
  finalizeProg.foldl (fun (arr : Array Fq) o =>
    let get := fun v => if v < NIN_VALS then env0 v else arr.getD (v - NIN_VALS) 0
    arr.push (match o.k with
      | .mul => get o.x * get o.y
      | .add => get o.x + get o.y
      | .sub => get o.x - get o.y
      | .eq => get o.x)) #[]

/-- The environment backed by the memo array (built once per call — bind the result). -/
def mkEnv (env0 : Nat → Fq) : Nat → Fq :=
  let arr := valsOf env0
  fun v => if v < NIN_VALS then env0 v else arr.getD (v - NIN_VALS) 0

/-- Slot tenancy per row: `tenantTable[t][s]` is the value resident in slot `s` at row `t`. -/
def tenantTable : Array (Array (Option Nat)) := Id.run do
  let mut cur : Array (Option Nat) := Array.replicate NSLOTS none
  for v in List.range NIN_VALS do
    cur := cur.set! (slotOfF v) (some v)
  let mut out : Array (Array (Option Nat)) := #[]
  for t in List.range NROWS do
    if t < finalizeProg.length then
      cur := cur.set! (slotOfF (NIN_VALS + t)) (some (NIN_VALS + t))
    out := out.push cur
  return out

/-- The full witness-pool width: w1 (1) + w8 (32) + w16 (62). -/
def WIT_W : Nat := 1 + SK + (NG - 1)

/-- One row's `FS_WIDTH` cells. -/
def rowCells (env : Nat → Fq) (t : Nat) : List Int :=
  let sel : List Int :=
    (List.range (NPHASE + 1)).map (fun i =>
      if i == t && t < NPHASE then 1
      else if i == NPHASE && t ≥ NPHASE then 1 else 0)
  let tens := tenantTable.getD t #[]
  let slots : List Int :=
    (List.range NSLOTS).flatMap (fun s =>
      match tens.getD s none with
      | some v => limbBlock (env v).val
      | none => List.replicate SK 0)
  let wit : List Int :=
    if t < finalizeProg.length then
      let o := finalizeProg.getD t ⟨.eq, 0, 0⟩
      let xv := (env o.x).val
      let yv := (env o.y).val
      let zv := (env (NIN_VALS + t)).val
      match o.k with
      | .mul => 0 :: mulWitBlock qN qLimb xv yv zv
      | .add => addSubWitBlock qN qLimb false xv yv zv
          ++ List.replicate (WIT_W - (1 + (NA - 1))) 0
      | .sub => addSubWitBlock qN qLimb true xv yv zv
          ++ List.replicate (WIT_W - (1 + (NA - 1))) 0
      | .eq => List.replicate WIT_W 0
    else List.replicate WIT_W 0
  sel ++ slots ++ wit

/-- The PI vector: the 103 input blocks, in value order. -/
def piCells (env0 : Nat → Fq) : List Int :=
  (List.range NPI_BLOCKS).flatMap (fun v => limbBlock (env0 v).val)

def renderRow (cells : List Int) : String :=
  String.intercalate " " (cells.map toString)

def writeTrace (path : System.FilePath) (env0 : Nat → Fq) : IO Unit := do
  let env := mkEnv env0
  let h ← IO.FS.Handle.mk path IO.FS.Mode.write
  for t in List.range NROWS do
    h.putStrLn (renderRow (rowCells env t))

def writePis (path : System.FilePath) (env0 : Nat → Fq) : IO Unit :=
  IO.FS.writeFile path (renderRow (piCells env0) ++ "\n")

/-! ## The three perturbed environments. -/

/-- forged-eval: `EZ_5` (a gate-selector eval at ζ) bumped; claims untouched. -/
def envForgedEval : Nat → Fq := bump env0Real (vEZ 5) 1

/-- forged-perm: the perm claim bumped; wire untouched. -/
def envForgedPerm : Nat → Fq := bump env0Real vPERMCL 1

/-- lct-shift: the port moved AND the cip claim recomputed — the accepting forgery family. -/
def envLctShift : Nat → Fq :=
  let e1 := bump env0Real vLCT 1
  let cipNew := mkEnv e1 cipResultV
  fun u => if u = vCIPCL then cipNew else e1 u

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "../circuit/tests/fixtures"
  IO.FS.createDirAll dir
  let p := fun (s : String) => System.FilePath.mk dir / s
  -- REFUSAL 1: the witnessed inverse really inverts.
  let den := (Dregg2.Circuit.Emit.MinaRealBlockGate.ZETA - ((OM3_C : Nat) : Fq))
      * (Dregg2.Circuit.Emit.MinaRealBlockGate.ZETA - 1)
  unless invOk den (env0Real vDINV) do
    IO.eprintln "REFUSED: the witnessed inverse does not invert the real block's denominator"
    return 1
  -- REFUSAL 2: the memoized renderer agrees with the AIR file's own denotation.
  let env := mkEnv env0Real
  let spec := progEval env0Real
  unless env cipResultV == spec cipResultV && env permResultV == spec permResultV do
    IO.eprintln "REFUSED: the memoized evaluator drifts from `progEval` — renderer bug"
    return 1
  -- REFUSAL 3: the honest environment satisfies the block's own two claims.
  unless env cipResultV == env0Real vCIPCL do
    IO.eprintln "REFUSED: the program's cip does not meet the block's combined_inner_product"
    return 1
  unless env permResultV == env0Real vPERMCL do
    IO.eprintln "REFUSED: the program's perm does not meet o1-labs' perm_scalars value"
    return 1
  IO.println s!"cip  = {(env cipResultV).val}"
  IO.println s!"perm = {(env permResultV).val}"
  IO.FS.writeFile (p "mina-finalize-scalars.json") (emitVmJson2 finalizeDesc)
  IO.println "descriptor written"
  writePis (p "mina-finalize-scalars-pis.txt") env0Real
  writePis (p "mina-finalize-scalars-forged-eval-pis.txt") envForgedEval
  writePis (p "mina-finalize-scalars-forged-perm-pis.txt") envForgedPerm
  writePis (p "mina-finalize-scalars-lct-shift-pis.txt") envLctShift
  IO.println "PI vectors written"
  writeTrace (p "mina-finalize-scalars-trace.txt") env0Real
  IO.println "honest trace written"
  writeTrace (p "mina-finalize-scalars-forged-eval-trace.txt") envForgedEval
  writeTrace (p "mina-finalize-scalars-forged-perm-trace.txt") envForgedPerm
  writeTrace (p "mina-finalize-scalars-lct-shift-trace.txt") envLctShift
  IO.println "forged traces written"
  return 0

end FsEmit

def main (args : List String) : IO UInt32 := FsEmit.main args
