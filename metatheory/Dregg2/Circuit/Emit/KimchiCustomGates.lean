/-
# Dregg2.Circuit.Emit.KimchiCustomGates — the FIRST Lean-emitted CUSTOM kimchi gate rows

## ⚑ THE RUNG THIS IS (R1), AND WHAT IT IS NOT

`KimchiTarget` emits only the three GENERIC-family gates (`zero`, `generic`, `rangeCheck0`); every
CUSTOM gate (`poseidon`, `completeAdd`, `varBaseMul`, `endoMul`, `endoMulScalar`) is `holds = False`
there — fail-closed, no row emitter. The Pickles step/wrap circuits are built ON those custom gates.
**This file is the first Lean emission of a custom-gate ROW** (`typ` + `wires` + `coeffs`), and its
fidelity is established DIFFERENTIALLY — byte-diffed against o1js's own `Provable.constraintSystem`
gate list (`bridge/mina-zkapp/scripts/custom-gate-oracle.mjs`, o1js 2.15.0). This is **Phase A**:
a Lean-emitted row whose `typ`/`coeffs` match o1js byte-for-byte. It is **NOT** a soundness proof and
**NOT** "machine-checked Pickles" — that is Phase B (the emitted row's satisfaction refined against
`KimchiVerify`'s checker over the real proof system).

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored synthesis.** The gate rows below are emitted from Lean `def`s. o1js and the
OCaml/proof-systems constants are READ-ONLY ORACLES: o1js supplies the byte target (`gates`), and
`KimchiVerify` (imported, not re-authored) supplies the constraint-body checker the emission answers
to. No Rust or TypeScript authors an AIR constraint here.

## What byte-diffed against o1js, and what did NOT match (the divergence map)

Measured against o1js 2.15.0 `Provable.constraintSystem(f).gates`:

  * **`typ`** — MATCHES. `KGateType.completeAdd`/`poseidon` carry ordinals 3/2
    (`gate.rs` `#[repr(C)]`), exactly o1js's `GateType` `'CompleteAdd'`/`'Poseidon'`.
  * **`coeffs`** —
      - `complete_add`: `[]` (Lean) vs `[]` (o1js). MATCHES (the gate carries no coefficients).
      - `poseidon`: the 15 coefficients of row `j` are `rcsN[5j..5j+4]` flattened (round-major,
        lane-minor) — BYTE-EXACT against o1js's 15 emitted `coeffs` per Poseidon row, all 11 rows
        (`custom-gate-diff.mjs` checks all 165). NO column permutation on the EMISSION side (the
        `STATE_ORDER` permutation is a VERIFIER-side read in `poseidonConstraints`, not an emission
        reordering).
  * **`wires`** — DIVERGES, structurally and by design. o1js emits `PERMUTS = 7` placement cells
    `{row, col}` (the copy-constraint targets of columns 0..6, produced by the wiring pass); a `KRow`
    holds VARIABLE INDICES for the columns the gate constrains (11 for `completeAdd`), PRE-placement.
    The map var-index → placed `{row,col}` is `KimchiPartition`'s named remainder (`KimchiTarget`
    §"Two deliberate departures"). Placement adds no rows, so `typ`/`coeffs`/row-count are the
    byte-comparable fields at this rung; `wires` is not comparable until that pass exists.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`/`native_decide`.
NEW file. Imports `KimchiTarget` (for `KRow`) and `KimchiVerify` (for the constraint-body checker
`completeAddConstraints` and the `rcsN` round-constant table via `PastaPoseidon`).
-/
import Dregg2.Circuit.Emit.KimchiTarget
import Dregg2.Circuit.Emit.KimchiVerify

namespace Dregg2.Circuit.Emit.KimchiCustomGates

open Dregg2.Circuit.Emit.KimchiTarget
open Dregg2.Circuit.Emit.KimchiVerify (completeAddConstraints)
open Dregg2.Circuit.Emit.PastaPoseidon (rcsN)

set_option autoImplicit false

/-! ## §1 — `complete_add`: the SMALLEST custom gate — 7 constraints, ZERO coefficients, one row.

Columns (`complete_add.rs:103-223`, transcribed in `KimchiVerify.completeAddConstraints`):
`x1 y1 x2 y2 x3 y3 inf same_x s inf_z x21_inv` = `w₀..w₁₀`. No coefficients. -/

/-- **The `complete_add` row emitter.** The eleven arguments are the VARIABLE INDICES placed in the
gate's eleven columns; the emitted row is `{ typ = CompleteAdd, wires = those 11, coeffs = [] }`.
o1js's authored `CompleteAdd` row carries `coeffs = []` identically (the byte target). -/
def mkCompleteAdd (x1 y1 x2 y2 x3 y3 inf sameX s infZ x21Inv : Nat) : KRow :=
  { gate := .completeAdd
  , wires := [x1, y1, x2, y2, x3, y3, inf, sameX, s, infZ, x21Inv]
  , coeffs := [] }

/-- `typ` = `CompleteAdd`. -/
theorem mkCompleteAdd_gate (x1 y1 x2 y2 x3 y3 inf sameX s infZ x21Inv : Nat) :
    (mkCompleteAdd x1 y1 x2 y2 x3 y3 inf sameX s infZ x21Inv).gate = .completeAdd := rfl

/-- The `typ` ordinal is `3` — o1js `GateType` `'CompleteAdd'`'s `#[repr(C)]` discriminant. -/
theorem mkCompleteAdd_ordinal (x1 y1 x2 y2 x3 y3 inf sameX s infZ x21Inv : Nat) :
    (mkCompleteAdd x1 y1 x2 y2 x3 y3 inf sameX s infZ x21Inv).gate.ordinal = 3 := rfl

/-- **`coeffs = []`** — byte-exact against o1js's emitted `CompleteAdd` row (`coeffs: []`). -/
theorem mkCompleteAdd_coeffs (x1 y1 x2 y2 x3 y3 inf sameX s infZ x21Inv : Nat) :
    (mkCompleteAdd x1 y1 x2 y2 x3 y3 inf sameX s infZ x21Inv).coeffs = [] := rfl

/-- The eleven wire columns, in order. -/
theorem mkCompleteAdd_wires (x1 y1 x2 y2 x3 y3 inf sameX s infZ x21Inv : Nat) :
    (mkCompleteAdd x1 y1 x2 y2 x3 y3 inf sameX s infZ x21Inv).wires
      = [x1, y1, x2, y2, x3, y3, inf, sameX, s, infZ, x21Inv] := rfl

/-! ### §1a — the row answers to `KimchiVerify`'s checker (satisfaction == the checker body).

`completeAddConstraints` is imported from `KimchiVerify`, NOT re-authored here — the same body
`KimchiRealProofGate` drives on real proofs. `caRowHolds` says a `complete_add` row holds exactly
when every one of those 7 constraint bodies vanishes on the row's own witness columns. -/

/-- The `CommRing`-generic satisfaction of a `complete_add` row against the imported checker. -/
def caRowHolds {R : Type} [CommRing R] (a : Nat → R) (r : KRow) : Prop :=
  ∀ b ∈ completeAddConstraints (r.wv a), b = 0

/-- **The emitted `complete_add` row's satisfaction IS the checker on the eleven named columns.**
This ties the emitter to the imported `KimchiVerify` body — the row is CHECKED, not free. -/
theorem mkCompleteAdd_checked {R : Type} [CommRing R] (a : Nat → R)
    (x1 y1 x2 y2 x3 y3 inf sameX s infZ x21Inv : Nat) :
    caRowHolds a (mkCompleteAdd x1 y1 x2 y2 x3 y3 inf sameX s infZ x21Inv)
      ↔ (∀ b ∈ completeAddConstraints
            ([a x1, a y1, a x2, a y2, a x3, a y3, a inf, a sameX, a s, a infZ, a x21Inv] : List R),
          b = 0) := by
  unfold caRowHolds mkCompleteAdd KRow.wv
  simp

/-! ## §2 — `poseidon`: the ONLY custom gate that carries coefficients (the round constants).

o1js emits one `Poseidon` gate row per FIVE rounds (`ROUNDS_FULL = 55` ⇒ 11 rows), each carrying
15 coefficients: the round constants of those five rounds, laid out ROUND-major then LANE-minor —
`rcsN[5j] ++ rcsN[5j+1] ++ … ++ rcsN[5j+4]` for row `j`. `rcsN` is `PastaPoseidon`'s 55×3 Kimchi
round-constant table, dumped from the pinned `proof-systems` crate — an INDEPENDENT source from
o1js's OCaml/wasm bindings, so the `#guard` below is a genuine cross-implementation gate, not a pin
against its own definition. -/

/-- **The 15 coefficients of Poseidon gate row `j`** — `rcsN[5j..5j+4]` flattened, cast to `ℤ`. -/
def poseidonRowCoeffs (j : Nat) : List ℤ :=
  (List.range 5).flatMap (fun i => (rcsN.getD (5 * j + i) []).map (fun n => (n : ℤ)))

/-- **The `poseidon` row emitter.** `wireVars` are the (up to 7) permutable column variable indices;
`coeffs` are row `j`'s fifteen round constants. `typ = Poseidon` (ordinal 2). -/
def mkPoseidonRow (j : Nat) (wireVars : List Nat) : KRow :=
  { gate := .poseidon
  , wires := wireVars
  , coeffs := poseidonRowCoeffs j }

theorem mkPoseidonRow_gate (j : Nat) (w : List Nat) : (mkPoseidonRow j w).gate = .poseidon := rfl

/-- The `typ` ordinal is `2` — o1js `GateType` `'Poseidon'`'s `#[repr(C)]` discriminant. -/
theorem mkPoseidonRow_ordinal (j : Nat) (w : List Nat) : (mkPoseidonRow j w).gate.ordinal = 2 := rfl

/-- Every Poseidon row carries exactly 15 coefficients (five rounds × three lanes). Checked at the
first, a middle, and the last row (`5·10+4 = 54 < 55`). -/
example : (poseidonRowCoeffs 0).length = 15 := by decide +kernel
example : (poseidonRowCoeffs 5).length = 15 := by decide +kernel
example : (poseidonRowCoeffs 10).length = 15 := by decide +kernel

/-! ### §2a — the BYTE PIN against o1js (this is the gate; it can go red).

`poseidonRowCoeffs 0` is asserted equal to the exact 15 decimal coefficients o1js emitted for
Poseidon gate row 0 of `Poseidon.hash([1,2])` (`custom-gate-oracle.mjs`). If `rcsN` drifts, or
o1js's params change, this `#guard` goes RED. The full 11-row (165-coefficient) cross-check is
`bridge/mina-zkapp/scripts/custom-gate-diff.mjs`. -/

/-- o1js's emitted `coeffs` for Poseidon gate row 0 (`Poseidon.hash([1,2])`, o1js 2.15.0). -/
def o1jsPoseidonRow0Coeffs : List ℤ :=
  [21155079691556475130150866428468322463125560312786319980770950159250751855431,
   16883442198399350202652499677723930673110172289234921799701652810789093522349,
   17030687036425314703519085065002231920937594822150793091243263847382891822670,
   25216718237129482752721276445368692059997901880654047883630276346421457427360,
   9054264347380455706540423067244764093107767235485930776517975315876127782582,
   26439087121446593160953570192891907825526260324480347638727375735543609856888,
   15251000790817261169639394496851831733819930596125214313084182526610855787494,
   10861916012597714684433535077722887124099023163589869801449218212493070551767,
   18597653523270601187312528478986388028263730767495975370566527202946430104139,
   15831416454198644276563319006805490049460322229057756462580029181847589006611,
   15171856919255965617705854914448645702014039524159471542852132430360867202292,
   15488495958879593647482715143904752785889816789652405888927117106448507625751,
   19039802679983063488134304670998725949842655199289961967801223969839823940152,
   4720101937153217036737330058775388037616286510783561045464678919473230044408,
   10226318327254973427513859412126640040910264416718766418164893837597674300190]

/-- **THE BYTE PIN.** The Lean emitter's row-0 coefficients equal o1js's, byte-for-byte. -/
theorem poseidonRow0_matches_o1js : poseidonRowCoeffs 0 = o1jsPoseidonRow0Coeffs := by
  decide +kernel

#assert_axioms mkCompleteAdd_checked
#assert_axioms mkCompleteAdd_ordinal
#assert_axioms mkPoseidonRow_ordinal
#assert_axioms poseidonRow0_matches_o1js

end Dregg2.Circuit.Emit.KimchiCustomGates
