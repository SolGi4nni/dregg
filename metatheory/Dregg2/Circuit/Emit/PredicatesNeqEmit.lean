/-
# Dregg2.Circuit.Emit.PredicatesNeqEmit — the emitted `NotEqual(value, threshold)`
arithmetic-predicate descriptor (`dregg-predicate-arith-neq::threshold-v1`).

## What this file IS

The `≠` case does NOT use a range proof: it uses the standard **nonzero-inverse gadget**. Let
`DIFF = value − threshold`. A witness column `DIFF_INV` and the degree-2 gate `DIFF · DIFF_INV = 1`
prove `DIFF` is INVERTIBLE — hence nonzero — hence `value ≠ threshold`. (Over the ℤ denotation the
gate forces `DIFF ∈ {1, −1}`, a fortiori `DIFF ≠ 0`; over the deployed BabyBear field the SAME gate
is satisfiable for ANY nonzero `DIFF`, which is exactly the field `≠` gadget. Either way the
soundness direction `DIFF·DIFF_INV = 1 ⟹ DIFF ≠ 0 ⟹ value ≠ threshold` holds.)

| tooth | constraint                                                    |
|-------|---------------------------------------------------------------|
| C1    | `.piBinding first THRESHOLD PI_THRESHOLD`                      |
| C2    | `.piBinding first FACT_COMMITMENT PI_FACT_COMMITMENT`          |
| C3    | `.gate (SLOT_A − INPUT)`  (bare-Input slot identity)          |
| C5    | `.gate (DIFF − SLOT_A + THRESHOLD)`  (`DIFF = value − threshold`) |
| CNZ   | `.gate (DIFF · DIFF_INV − 1)`  (`DIFF` invertible ⟹ `DIFF ≠ 0`) |

The nonzero tooth is the comparison judge — a `value = threshold` forces `DIFF = 0`, and
`0 · DIFF_INV = 0 ≠ 1` has NO witness (UNSAT): it BITES.

**THE VALUE↔FACT WELD (M14).** The descriptor's ONLY lookups are the two Poseidon2 chip legs that
force `FACT_COMMITMENT = hash_2_to_1(hash_fact(pred, [INPUT, t1, t2]), STATE_ROOT)` over the SAME
`INPUT` the `≠` gadget speaks about — col 5 (`FACT_COMMITMENT`) and col 0 (`INPUT`) are no longer in
DISJOINT constraint sets. Without it a prover proves `value ≠ threshold` on a value of its choosing
against an unrelated honest commitment. The `≠` layout carries `DIFF_INV` (col 4), so the weld cols
begin at 6 (one past the `≤`/`>`/`<` siblings).

## ⚑ COMPILER-SOURCED (2026-08-01, Phase 3 of `docs/LOGIC-COMPILER-ASSESSMENT.md`)

The descriptor is `EffectLower.lowerAir` of the `EffectAir` in §2 — the hand-written
`VmConstraint2` list literal is DELETED. Every gate is authored as an EQUATION and the compiler
renders its canonical vanishing polynomial (`AirNormalForm`'s corpus invariant). ⚑ This is the
descriptor with a DEGREE-2 gate, and it is why `EffectLowerCore.mulHead` now guards its constant
cross-products on a nonzero constant: unguarded, `DIFF · DIFF_INV` distributed to the genuine
`1·DIFF·DIFF_INV` PLUS a spurious `0·DIFF` and `0·DIFF_INV` — terms the source never wrote and
which would have landed in the wire bytes of every product gate the compiler emits.
RE-EMITS `circuit/descriptors/by-name/predicate-arith-neq.json` + its PROVENANCE sha.

`#assert_axioms` ⊆ {} on the gate lemmas. Imports read-only.
-/
import Dregg2.Circuit.Emit.AirNormalForm

namespace Dregg2.Circuit.Emit.PredicatesNeqEmit

open Dregg2.Circuit (Assignment Constraint Expr)
open Dregg2.Exec.CircuitEmit (EmittedExpr emitExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 TableId emitVmJson2 chipLookupTuple CHIP_RATE CHIP_OUT_LANES)
open Dregg2.Circuit.EffectAirIR (EffectAir LookupLeg)
open Dregg2.Circuit.Emit.EffectLower (lowerAir lowerConstraint)
open Dregg2.Circuit.Emit.AirNormalForm
  (liftTuple gateBody gateBody_eval gateBody_zero_iff normalFormOk)

set_option autoImplicit false

def INPUT : Nat := 0
def SLOT_A : Nat := 1
def THRESHOLD : Nat := 2
def DIFF : Nat := 3
/-- The claimed inverse of `DIFF`; the degree-2 gate `DIFF · DIFF_INV = 1` forces `DIFF ≠ 0`. -/
def DIFF_INV : Nat := 4
def FACT_COMMITMENT : Nat := 5
/-! The value↔fact WELD columns (the `≠` layout carries `DIFF_INV`, so the weld cols shift by one
past the `≤`/`>`/`<` siblings): tie `INPUT` to the committed fact. -/
def PREDICATE_SYM : Nat := 6
def TERM1 : Nat := 7
def TERM2 : Nat := 8
def STATE_ROOT : Nat := 9
def FACT_HASH : Nat := 10
def FACT_MARK : Int := 64207
def FACTHASH_LANES : List Nat := [11, 12, 13, 14, 15, 16, 17]
def FACTCOMMIT_LANES : List Nat := [18, 19, 20, 21, 22, 23, 24]
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
def BLINDING : Nat := 25

def PRED_WIDTH : Nat := 26
def PI_THRESHOLD : Nat := 0
def PI_FACT_COMMITMENT : Nat := 1

def c1ThresholdPin : VmConstraint2 := .base (.piBinding VmRow.first THRESHOLD PI_THRESHOLD)
def c2FactPin : VmConstraint2 := .base (.piBinding VmRow.first FACT_COMMITMENT PI_FACT_COMMITMENT)

/-- **The C3 slot equation, as the SOURCE states it.** -/
def c3Src : Constraint := ⟨.var SLOT_A, .var INPUT⟩
/-- …and the body the COMPILER renders for it. -/
def c3Body : EmittedExpr := gateBody c3Src
def c3SlotGate : VmConstraint2 := lowerConstraint c3Src

/-- The C5 diff-computation body `DIFF − SLOT_A + THRESHOLD` (`DIFF = SLOT_A − THRESHOLD`, i.e.
`DIFF = value − threshold`). -/
def c5Src : Constraint :=
  ⟨.var DIFF, .add (.var SLOT_A) (.mul (.const (-1)) (.var THRESHOLD))⟩
/-- …and the body the COMPILER renders for it. -/
def c5Body : EmittedExpr := gateBody c5Src
def c5DiffGate : VmConstraint2 := lowerConstraint c5Src

/-- The CNZ nonzero-inverse body `DIFF · DIFF_INV − 1` (degree 2). Zero iff `DIFF · DIFF_INV = 1`,
which forces `DIFF ≠ 0`. -/
def cNzSrc : Constraint := ⟨.mul (.var DIFF) (.var DIFF_INV), .const 1⟩
/-- …and the body the COMPILER renders for it — the ONE degree-2 gate in the batch. -/
def cNzBody : EmittedExpr := gateBody cNzSrc
def cNzGate : VmConstraint2 := lowerConstraint cNzSrc

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

/-- **`predicateNeqDesc`** — the arithmetic `NotEqual(value, threshold)` descriptor, welded (the two
Poseidon2 chip lookups are the only lookups; the nonzero tooth is the comparison judge). -/
def predicateNeqAir : EffectAir :=
  { legs := [ .pin ⟨VmRow.first, THRESHOLD, PI_THRESHOLD⟩
            , .pin ⟨VmRow.first, FACT_COMMITMENT, PI_FACT_COMMITMENT⟩
            , .gate c3Src
            , .gate c5Src
            , .gate cNzSrc
            , .lookup factHashLeg
            , .lookup factCommitLeg ] }

#guard predicateNeqAir.mainRailOk == true

def predicateNeqDesc : EffectVmDescriptor2 :=
  lowerAir "dregg-predicate-arith-neq::threshold-v1" PRED_WIDTH 2 [] predicateNeqAir

/-- ⚑ The compiler's output IS that constraint list, by `rfl`. -/
theorem predicateNeqDesc_constraints :
    predicateNeqDesc.constraints
      = [c1ThresholdPin, c2FactPin, c3SlotGate, c5DiffGate, cNzGate,
         factHashLookup, factCommitLookup] := rfl

-- ⚑ THE CORPUS INVARIANT, DECIDED on this descriptor: every arithmetic body is canonical.
#guard normalFormOk predicateNeqDesc == true

#guard emitVmJson2 predicateNeqDesc ==
  "{\"name\":\"dregg-predicate-arith-neq::threshold-v1\",\"ir\":2,\"trace_width\":26,\"public_input_count\":2,\"tables\":[],\"constraints\":[{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":5,\"pi_index\":1},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":1}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":0}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":3}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":2}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":7},{\"t\":\"var\",\"v\":6},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":7},{\"t\":\"var\",\"v\":8},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":64207},{\"t\":\"const\",\"v\":1},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":10},{\"t\":\"var\",\"v\":11},{\"t\":\"var\",\"v\":12},{\"t\":\"var\",\"v\":13},{\"t\":\"var\",\"v\":14},{\"t\":\"var\",\"v\":15},{\"t\":\"var\",\"v\":16},{\"t\":\"var\",\"v\":17}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":4},{\"t\":\"var\",\"v\":10},{\"t\":\"var\",\"v\":9},{\"t\":\"var\",\"v\":25},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":5},{\"t\":\"var\",\"v\":18},{\"t\":\"var\",\"v\":19},{\"t\":\"var\",\"v\":20},{\"t\":\"var\",\"v\":21},{\"t\":\"var\",\"v\":22},{\"t\":\"var\",\"v\":23},{\"t\":\"var\",\"v\":24}]}],\"hash_sites\":[],\"ranges\":[]}"

theorem c3_body_zero_iff (a : Assignment) :
    c3Body.eval a = 0 ↔ a SLOT_A = a INPUT := by
  simp only [c3Body]; rw [gateBody_zero_iff]; simp [c3Src, Expr.eval]

theorem c5_body_zero_iff (a : Assignment) :
    c5Body.eval a = 0 ↔ a DIFF = a SLOT_A - a THRESHOLD := by
  simp only [c5Body]; rw [gateBody_zero_iff]
  simp only [c5Src, Expr.eval]
  omega

/-- The CNZ gate body is zero iff `DIFF · DIFF_INV = 1`; this IMPLIES `DIFF ≠ 0`. -/
theorem cNz_body_zero_imp_ne (a : Assignment) :
    cNzBody.eval a = 0 → a DIFF ≠ 0 := by
  simp only [cNzBody]
  rw [gateBody_eval]
  simp only [cNzSrc, Expr.eval]
  intro h hz
  rw [hz] at h
  simp at h

#guard decide (c3Body.eval (fun i => if i = SLOT_A ∨ i = INPUT then 7 else 0) = 0)
#guard decide (¬ (c3Body.eval (fun i => if i = SLOT_A then 7 else 0) = 0))
#guard decide (c5Body.eval (fun i => if i = DIFF then 1 else if i = SLOT_A then 41 else if i = THRESHOLD then 40 else 0) = 0)
-- CNZ accepts a genuine inverse (DIFF = 1, DIFF_INV = 1) and rejects DIFF = 0.
#guard decide (cNzBody.eval (fun i => if i = DIFF then 1 else if i = DIFF_INV then 1 else 0) = 0)
#guard decide (¬ (cNzBody.eval (fun i => if i = DIFF then 0 else if i = DIFF_INV then 5 else 0) = 0))

#guard predicateNeqDesc.traceWidth == PRED_WIDTH
#guard predicateNeqDesc.piCount == 2
#guard predicateNeqDesc.constraints.length == 7
#guard predicateNeqDesc.tables.length == 0
#guard (chipLookupTuple [.var PREDICATE_SYM, .var INPUT, .var TERM1, .var TERM2,
                         .const 0, .const FACT_MARK, .const 1] FACT_HASH FACTHASH_LANES).length
         == CHIP_RATE + 1 + CHIP_OUT_LANES
#guard (chipLookupTuple [.var FACT_HASH, .var STATE_ROOT, .var BLINDING, .const 0]
                        FACT_COMMITMENT FACTCOMMIT_LANES).length
         == CHIP_RATE + 1 + CHIP_OUT_LANES

#assert_axioms c3_body_zero_iff
#assert_axioms c5_body_zero_iff
#assert_axioms cNz_body_zero_imp_ne


-- The blinded leg is arity-4 (tag 4 = `hash_4_to_1`'s `st[4]`), not the arity-2 absorb.
#guard (chipLookupTuple [.var FACT_HASH, .var STATE_ROOT, .var BLINDING, .const 0]
                        FACT_COMMITMENT FACTCOMMIT_LANES).head? == some (.const 4)
-- `BLINDING` is a real trace column, and it is NOT PI-bound (a witness, never revealed).
#guard BLINDING < PRED_WIDTH

end Dregg2.Circuit.Emit.PredicatesNeqEmit
