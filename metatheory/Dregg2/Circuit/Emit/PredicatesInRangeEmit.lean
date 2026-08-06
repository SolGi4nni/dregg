/-
# Dregg2.Circuit.Emit.PredicatesInRangeEmit — the emitted `InRange(lo ≤ value ≤ hi)`
arithmetic-predicate descriptor (`dregg-predicate-arith-inrange::bounds-v1`).

## What this file IS

The two-sided membership case: `lo ≤ value ≤ hi`, carried by TWO range checks — one for each side.
Public inputs are `[lo, hi, fact_commitment]` (three PIs, vs the one-sided ops' two):

  * `DIFF_LO = value − lo ∈ [0, 2^29)`  (`value ≥ lo`);
  * `DIFF_HI = hi − value ∈ [0, 2^29)`  (`value ≤ hi`).

| tooth  | constraint                                                       |
|--------|------------------------------------------------------------------|
| C1lo   | `.piBinding first LO PI_LO`                                       |
| C1hi   | `.piBinding first HI PI_HI`                                       |
| C2     | `.piBinding first FACT_COMMITMENT PI_FACT_COMMITMENT`             |
| C3     | `.gate (SLOT_A − INPUT)`  (bare-Input slot identity)             |
| C5lo   | `.gate (DIFF_LO − SLOT_A + LO)`  (`DIFF_LO = value − lo`)        |
| C5hi   | `.gate (DIFF_HI − HI + SLOT_A)`  (`DIFF_HI = hi − value`)        |
| C6lo   | `.lookup ⟨range, [DIFF_LO]⟩`                                      |
| C6hi   | `.lookup ⟨range, [DIFF_HI]⟩`                                      |

Both range lookups are load-bearing: a `value < lo` wraps `DIFF_LO` below zero, a `value > hi` wraps
`DIFF_HI` below zero — either UNSAT.

**THE VALUE↔FACT WELD (M14).** Two Poseidon2 chip lookups force `FACT_COMMITMENT =
hash_2_to_1(hash_fact(pred, [INPUT, t1, t2]), STATE_ROOT)` over the SAME `INPUT` both bounds speak
about — col 6 (`FACT_COMMITMENT`) and col 0 (`INPUT`) are no longer in DISJOINT constraint sets.
Without it a prover proves `lo ≤ value ≤ hi` on a value of its choosing against an unrelated honest
commitment. The InRange layout carries `LO`/`HI`/`DIFF_LO`/`DIFF_HI`, so the weld cols begin at 7.

## ⚑ COMPILER-SOURCED (2026-08-01, Phase 3 of `docs/LOGIC-COMPILER-ASSESSMENT.md`)

The descriptor is `EffectLower.lowerAir` of the `EffectAir` in §2 — the hand-written
`VmConstraint2` list literal is DELETED. Each of the three gates is authored as an EQUATION and the
compiler renders its canonical vanishing polynomial (`AirNormalForm`'s corpus invariant).
RE-EMITS `circuit/descriptors/by-name/predicate-arith-inrange.json` + its PROVENANCE sha.

`#assert_axioms` ⊆ {} on the gate lemmas. Imports read-only.
-/
import Dregg2.Circuit.Emit.AirNormalForm
import Dregg2.Circuit.Emit.EffectLowerCertified

namespace Dregg2.Circuit.Emit.PredicatesInRangeEmit

open Dregg2.Circuit (Assignment Constraint Expr)
open Dregg2.Exec.CircuitEmit (EmittedExpr emitExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId rangeTableDef emitVmJson2 rangeRows
   range_row_mem_iff chipLookupTuple CHIP_RATE CHIP_OUT_LANES)
open Dregg2.Circuit.EffectAirIR (EffectAir LookupLeg)
open Dregg2.Circuit.Emit.EffectLower (lowerAir lowerConstraint)
open Dregg2.Circuit.Emit.AirNormalForm (liftTuple gateBody gateBody_zero_iff normalFormOk)

set_option autoImplicit false

def INPUT : Nat := 0
def SLOT_A : Nat := 1
def LO : Nat := 2
def HI : Nat := 3
def DIFF_LO : Nat := 4
def DIFF_HI : Nat := 5
def FACT_COMMITMENT : Nat := 6
/-! The value↔fact WELD columns (the InRange layout carries `LO`/`HI`/`DIFF_LO`/`DIFF_HI`, so the
weld cols start at 7): tie `INPUT` to the committed fact. -/
def PREDICATE_SYM : Nat := 7
def TERM1 : Nat := 8
def TERM2 : Nat := 9
def STATE_ROOT : Nat := 10
def FACT_HASH : Nat := 11
def FACT_MARK : Int := 64207
def FACTHASH_LANES : List Nat := [12, 13, 14, 15, 16, 17, 18]
def FACTCOMMIT_LANES : List Nat := [19, 20, 21, 22, 23, 24, 25]
/-- **The commitment BLINDING factor** — a PRIVATE witness column, leg 2's input 2.

Makes two presentations of the SAME fact carry DIFFERENT `fact_commitment` public inputs, so
colluding verifiers cannot correlate them. A witness column, NOT PI-bound: the prover chooses it and
the verifier never learns it.

That freedom costs the weld NOTHING. Leg 2 forces `FACT_COMMITMENT` to be the chip image of
`[FACT_HASH, STATE_ROOT, BLINDING, 0]`; leg 1 forces `FACT_HASH = hash_fact(pred, [INPUT, …])` over
the SAME `INPUT` column the comparison bounds. A prover free to pick `BLINDING` can move the
commitment anywhere in the image of the hash — but never to the image of a DIFFERENT value: every
reachable commitment still opens to the `INPUT` compared. Blinding rerandomizes WHICH commitment
names this fact; it cannot change WHICH fact is named. Privacy and the weld are independent.
See `PredicatesArithmeticEmit.BLINDING` for the canonical statement of this argument. -/
def BLINDING : Nat := 26

def PRED_WIDTH : Nat := 27
def PI_LO : Nat := 0
def PI_HI : Nat := 1
def PI_FACT_COMMITMENT : Nat := 2
def DIFF_BITS : Nat := 29

def c1LoPin : VmConstraint2 := .base (.piBinding VmRow.first LO PI_LO)
def c1HiPin : VmConstraint2 := .base (.piBinding VmRow.first HI PI_HI)
def c2FactPin : VmConstraint2 := .base (.piBinding VmRow.first FACT_COMMITMENT PI_FACT_COMMITMENT)

/-- **The C3 slot equation, as the SOURCE states it.** -/
def c3Src : Constraint := ⟨.var SLOT_A, .var INPUT⟩
/-- …and the body the COMPILER renders for it. -/
def c3Body : EmittedExpr := gateBody c3Src
def c3SlotGate : VmConstraint2 := lowerConstraint c3Src

/-- `DIFF_LO = SLOT_A − LO` (`value − lo`). Body `DIFF_LO − SLOT_A + LO`. -/
def c5LoSrc : Constraint :=
  ⟨.var DIFF_LO, .add (.var SLOT_A) (.mul (.const (-1)) (.var LO))⟩
/-- …and the body the COMPILER renders for it. -/
def c5LoBody : EmittedExpr := gateBody c5LoSrc
def c5LoGate : VmConstraint2 := lowerConstraint c5LoSrc

/-- `DIFF_HI = HI − SLOT_A` (`hi − value`). Body `DIFF_HI − HI + SLOT_A`. -/
def c5HiSrc : Constraint :=
  ⟨.var DIFF_HI, .add (.var HI) (.mul (.const (-1)) (.var SLOT_A))⟩
/-- …and the body the COMPILER renders for it. -/
def c5HiBody : EmittedExpr := gateBody c5HiSrc
def c5HiGate : VmConstraint2 := lowerConstraint c5HiSrc

def c6LoLeg : LookupLeg := { table := TableId.range, tuple := [.var DIFF_LO] }
def c6HiLeg : LookupLeg := { table := TableId.range, tuple := [.var DIFF_HI] }
def c6LoRange : VmConstraint2 := .lookup ⟨TableId.range, c6LoLeg.tuple.map emitExpr⟩
def c6HiRange : VmConstraint2 := .lookup ⟨TableId.range, c6HiLeg.tuple.map emitExpr⟩

/-- **THE VALUE↔FACT WELD, leg 1** — `FACT_HASH = hash_fact(pred, [INPUT, term1, term2])`. -/
def factHashLeg : LookupLeg :=
  { table := TableId.poseidon2
  , tuple := liftTuple
      (chipLookupTuple [.var PREDICATE_SYM, .var INPUT, .var TERM1, .var TERM2,
                        .const 0, .const FACT_MARK, .const 1] FACT_HASH FACTHASH_LANES) }
def factHashLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, factHashLeg.tuple.map emitExpr⟩

/-- **THE VALUE↔FACT WELD, leg 2 (BLINDED)** — arity-4 fact-commitment chip lookup binding
`FACT_COMMITMENT = Poseidon2_4to1([fact_hash, state_root, blinding, 0])`, tying the PI-pinned
commitment to the opened fact hash while leaving it rerandomizable by the private `BLINDING`.

The arity-4 chip absorb IS `hash_4_to_1`: `chip_absorb_lanes 4` takes the `seed456 = false` branch,
seeding `st[0..4] = inputs` and `st[4] = arity = 4` — exactly `poseidon2.rs::hash_4_to_1`. The leg
binds the production blinded commitment with ZERO change to the hash function. -/
def factCommitLeg : LookupLeg :=
  { table := TableId.poseidon2
  , tuple := liftTuple
      (chipLookupTuple [.var FACT_HASH, .var STATE_ROOT, .var BLINDING, .const 0]
        FACT_COMMITMENT FACTCOMMIT_LANES) }
def factCommitLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, factCommitLeg.tuple.map emitExpr⟩

/-- **`predicateInRangeDesc`** — the arithmetic `InRange(lo ≤ value ≤ hi)` descriptor, welded. 3 PIs. -/
def predicateInRangeAir : EffectAir :=
  { tables := [rangeTableDef DIFF_BITS]
  , legs   := [ .pin ⟨VmRow.first, LO, PI_LO⟩
              , .pin ⟨VmRow.first, HI, PI_HI⟩
              , .pin ⟨VmRow.first, FACT_COMMITMENT, PI_FACT_COMMITMENT⟩
              , .gate c3Src
              , .gate c5LoSrc
              , .gate c5HiSrc
              , .lookup c6LoLeg
              , .lookup c6HiLeg
              , .lookup factHashLeg
              , .lookup factCommitLeg ] }

#guard predicateInRangeAir.mainRailOk == true

/-- ⚑ **THE TIED SOURCE** — `predicateInRangeAir` carrying its two decidable verdicts in its TYPE:
`mainRailOk` (main-rail expressible) and `pinsTied` (every published column is DERIVED by another
leg). A `TiedAir` cannot be built for a block that publishes a column nothing else constrains, so a
decorative pin is unrepresentable here rather than detectable by a census afterwards. -/
def predicateInRangeTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air := predicateInRangeAir

def predicateInRangeDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-predicate-arith-inrange::bounds-v1" PRED_WIDTH 3 [] predicateInRangeTiedAir).val

/-- ⚑ **THE CERTIFICATE, produced by the emit.** Every leg of the source is FORCED by the emitted
descriptor's constraints on any row window that satisfies them — `AirLeg.forces`, stated in the
SOURCE's vocabulary and never mentioning the lowering, so it is not `P → P`. Not re-derived here.

**Zero bytes move**: `lowerTiedAir … |>.val` is `lowerAir …` by `rfl`. -/
theorem predicateInRangeDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines predicateInRangeDesc [] predicateInRangeAir :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-predicate-arith-inrange::bounds-v1" PRED_WIDTH 3 [] predicateInRangeTiedAir).property

/-- ⚑ **THE ZERO.** The certified lowering emits the term the bare lowering emitted, by `rfl` — so
the migration changed what this definition PROVES, not what it PRODUCES. No re-emit, no VK rotation.
Also the unfolding lemma for the cost/shape proofs below, which reason through `lowerAir`. -/
theorem predicateInRangeDesc_eq_lowerAir :
    predicateInRangeDesc = Dregg2.Circuit.Emit.EffectLower.lowerAir "dregg-predicate-arith-inrange::bounds-v1" PRED_WIDTH 3 [] predicateInRangeAir := rfl

/-- ⚑ The compiler's output IS that constraint list, by `rfl`. -/
theorem predicateInRangeDesc_constraints :
    predicateInRangeDesc.constraints
      = [c1LoPin, c1HiPin, c2FactPin, c3SlotGate, c5LoGate, c5HiGate, c6LoRange, c6HiRange,
         factHashLookup, factCommitLookup] := rfl

-- ⚑ THE CORPUS INVARIANT, DECIDED on this descriptor: every arithmetic body is canonical.
#guard normalFormOk predicateInRangeDesc == true

#guard emitVmJson2 predicateInRangeDesc ==
  "{\"name\":\"dregg-predicate-arith-inrange::bounds-v1\",\"ir\":2,\"trace_width\":27,\"public_input_count\":3,\"challenges\":0,\"tables\":[{\"id\":2,\"name\":\"range\",\"arity\":1,\"sem\":\"range\",\"bits\":29}],\"constraints\":[{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":3,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":6,\"pi_index\":2},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":1}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":0}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":4}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":2}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":3}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":1}}}},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":4}]},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":5}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":7},{\"t\":\"var\",\"v\":7},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":8},{\"t\":\"var\",\"v\":9},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":64207},{\"t\":\"const\",\"v\":1},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":11},{\"t\":\"var\",\"v\":12},{\"t\":\"var\",\"v\":13},{\"t\":\"var\",\"v\":14},{\"t\":\"var\",\"v\":15},{\"t\":\"var\",\"v\":16},{\"t\":\"var\",\"v\":17},{\"t\":\"var\",\"v\":18}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":4},{\"t\":\"var\",\"v\":11},{\"t\":\"var\",\"v\":10},{\"t\":\"var\",\"v\":26},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":6},{\"t\":\"var\",\"v\":19},{\"t\":\"var\",\"v\":20},{\"t\":\"var\",\"v\":21},{\"t\":\"var\",\"v\":22},{\"t\":\"var\",\"v\":23},{\"t\":\"var\",\"v\":24},{\"t\":\"var\",\"v\":25}]}],\"hash_sites\":[],\"ranges\":[]}"

theorem c3_body_zero_iff (a : Assignment) :
    c3Body.eval a = 0 ↔ a SLOT_A = a INPUT := by
  simp only [c3Body]; rw [gateBody_zero_iff]; simp [c3Src, Expr.eval]

theorem c5Lo_body_zero_iff (a : Assignment) :
    c5LoBody.eval a = 0 ↔ a DIFF_LO = a SLOT_A - a LO := by
  simp only [c5LoBody]; rw [gateBody_zero_iff]
  simp only [c5LoSrc, Expr.eval]
  omega

theorem c5Hi_body_zero_iff (a : Assignment) :
    c5HiBody.eval a = 0 ↔ a DIFF_HI = a HI - a SLOT_A := by
  simp only [c5HiBody]; rw [gateBody_zero_iff]
  simp only [c5HiSrc, Expr.eval]
  omega

#guard decide (c3Body.eval (fun i => if i = SLOT_A ∨ i = INPUT then 7 else 0) = 0)
#guard decide (c5LoBody.eval (fun i => if i = DIFF_LO then 30 else if i = SLOT_A then 40 else if i = LO then 10 else 0) = 0)
#guard decide (¬ (c5LoBody.eval (fun i => if i = DIFF_LO then 29 else if i = SLOT_A then 40 else if i = LO then 10 else 0) = 0))
#guard decide (c5HiBody.eval (fun i => if i = DIFF_HI then 60 else if i = HI then 100 else if i = SLOT_A then 40 else 0) = 0)
#guard decide (¬ (c5HiBody.eval (fun i => if i = DIFF_HI then 59 else if i = HI then 100 else if i = SLOT_A then 40 else 0) = 0))

example : ([30] : List ℤ) ∈ rangeRows DIFF_BITS := by
  rw [range_row_mem_iff]; norm_num [DIFF_BITS]
example : ¬ (([2 ^ 29] : List ℤ) ∈ rangeRows DIFF_BITS) := by
  rw [range_row_mem_iff]; norm_num [DIFF_BITS]

#guard predicateInRangeDesc.traceWidth == PRED_WIDTH
#guard predicateInRangeDesc.piCount == 3
#guard predicateInRangeDesc.constraints.length == 10
#guard predicateInRangeDesc.tables.length == 1
#guard (chipLookupTuple [.var PREDICATE_SYM, .var INPUT, .var TERM1, .var TERM2,
                         .const 0, .const FACT_MARK, .const 1] FACT_HASH FACTHASH_LANES).length
         == CHIP_RATE + 1 + CHIP_OUT_LANES
#guard (chipLookupTuple [.var FACT_HASH, .var STATE_ROOT, .var BLINDING, .const 0]
                        FACT_COMMITMENT FACTCOMMIT_LANES).length
         == CHIP_RATE + 1 + CHIP_OUT_LANES

#assert_axioms c3_body_zero_iff
#assert_axioms c5Lo_body_zero_iff
#assert_axioms c5Hi_body_zero_iff


-- The blinded leg is arity-4 (tag 4 = `hash_4_to_1`'s `st[4]`), not the arity-2 absorb.
#guard (chipLookupTuple [.var FACT_HASH, .var STATE_ROOT, .var BLINDING, .const 0]
                        FACT_COMMITMENT FACTCOMMIT_LANES).head? == some (.const 4)
-- `BLINDING` is a real trace column, and it is NOT PI-bound (a witness, never revealed).
#guard BLINDING < PRED_WIDTH

end Dregg2.Circuit.Emit.PredicatesInRangeEmit
