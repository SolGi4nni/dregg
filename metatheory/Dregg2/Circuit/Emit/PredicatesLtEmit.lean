/-
# Dregg2.Circuit.Emit.PredicatesLtEmit — the emitted `LessThan(value, threshold)`
arithmetic-predicate descriptor (`dregg-predicate-arith-lt::threshold-v1`).

The strict `<` sibling. `value < threshold ↔ threshold − value − 1 ≥ 0`:

  * `≤`:  `DIFF = threshold − value ∈ [0, 2^29)`;
  * `<`:  `DIFF = threshold − value − 1 ∈ [0, 2^29)`.

The C6 range lookup is the load-bearing tooth (a `value ≥ threshold` wraps
`DIFF = threshold − value − 1` below zero — UNSAT).

**THE VALUE↔FACT WELD (M14).** Two Poseidon2 chip lookups force `FACT_COMMITMENT =
hash_2_to_1(hash_fact(pred, [INPUT, t1, t2]), STATE_ROOT)` over the SAME `INPUT` the comparison
bounds — col 4 and col 0 are no longer in DISJOINT constraint sets. Without it a prover proves
`value < threshold` on a value of its choosing against an unrelated honest commitment. Geometry
identical to `≥`.

## ⚑ COMPILER-SOURCED (2026-08-01, Phase 3 of `docs/LOGIC-COMPILER-ASSESSMENT.md`)

The descriptor is `EffectLower.lowerAir` of the `EffectAir` in §2; the hand-written `VmConstraint2`
list literal is DELETED. The two gates are authored as EQUATIONS (`SLOT_A = INPUT`,
`DIFF = THRESHOLD − SLOT_A − 1`) and the compiler turns each into its canonical vanishing
polynomial. RE-EMITS `circuit/descriptors/by-name/predicate-arith-lt.json` (+ PROVENANCE sha):
the bare unit coefficients become `mul(const 1, ·)` per `AirNormalForm`'s corpus invariant. Same
polynomial, same p3 symbolic degree, same VK geometry.

`#assert_axioms` ⊆ {} on the gate lemmas. Imports read-only.
-/
import Dregg2.Circuit.Emit.AirNormalForm
import Dregg2.Circuit.Emit.EffectLowerCertified

namespace Dregg2.Circuit.Emit.PredicatesLtEmit

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
def THRESHOLD : Nat := 2
def DIFF : Nat := 3
def FACT_COMMITMENT : Nat := 4
/-! The value↔fact WELD columns (identical geometry to `≥`): tie `INPUT` to the committed fact. -/
def PREDICATE_SYM : Nat := 5
def TERM1 : Nat := 6
def TERM2 : Nat := 7
def STATE_ROOT : Nat := 8
def FACT_HASH : Nat := 9
def FACT_MARK : Int := 64207
def FACTHASH_LANES : List Nat := [10, 11, 12, 13, 14, 15, 16]
def FACTCOMMIT_LANES : List Nat := [17, 18, 19, 20, 21, 22, 23]
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
def BLINDING : Nat := 24

def PRED_WIDTH : Nat := 25
def PI_THRESHOLD : Nat := 0
def PI_FACT_COMMITMENT : Nat := 1
def DIFF_BITS : Nat := 29

def c1ThresholdPin : VmConstraint2 := .base (.piBinding VmRow.first THRESHOLD PI_THRESHOLD)
def c2FactPin : VmConstraint2 := .base (.piBinding VmRow.first FACT_COMMITMENT PI_FACT_COMMITMENT)

/-- **The C3 slot equation, as the SOURCE states it**: the compared slot IS the welded input. -/
def c3Src : Constraint := ⟨.var SLOT_A, .var INPUT⟩
/-- …and the body the compiler renders for it. -/
def c3Body : EmittedExpr := gateBody c3Src
def c3SlotGate : VmConstraint2 := lowerConstraint c3Src

/-- **The C5 diff equation**: `DIFF = THRESHOLD − SLOT_A − 1` (i.e. `DIFF = threshold − value − 1`
— the strict `<` shift). The compiler turns it into the vanishing residual
`DIFF − THRESHOLD + SLOT_A + 1`. -/
def c5Src : Constraint :=
  ⟨.var DIFF, .add (.add (.var THRESHOLD) (.mul (.const (-1)) (.var SLOT_A))) (.const (-1))⟩
def c5Body : EmittedExpr := gateBody c5Src
def c5DiffGate : VmConstraint2 := lowerConstraint c5Src

def c6RangeLeg : LookupLeg := { table := TableId.range, tuple := [.var DIFF] }
def c6RangeLookup : VmConstraint2 := .lookup ⟨TableId.range, c6RangeLeg.tuple.map emitExpr⟩

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

/-- ⚑ **THE AIR SOURCE** — seven legs in emission order: the two PI pins, the slot gate, the diff
gate, the C6 range lookup and the two weld legs. -/
def predicateLtAir : EffectAir :=
  { tables := [rangeTableDef DIFF_BITS]
  , legs   := [ .pin ⟨VmRow.first, THRESHOLD, PI_THRESHOLD⟩
              , .pin ⟨VmRow.first, FACT_COMMITMENT, PI_FACT_COMMITMENT⟩
              , .gate c3Src
              , .gate c5Src
              , .lookup c6RangeLeg
              , .lookup factHashLeg
              , .lookup factCommitLeg ] }

#guard predicateLtAir.mainRailOk == true

/-- ⚑ **THE TIED SOURCE** — `predicateLtAir` carrying its two decidable verdicts in its TYPE:
`mainRailOk` (main-rail expressible) and `pinsTied` (every published column is DERIVED by another
leg). A `TiedAir` cannot be built for a block that publishes a column nothing else constrains, so a
decorative pin is unrepresentable here rather than detectable by a census afterwards. -/
def predicateLtTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air := predicateLtAir

/-- **`predicateLtDesc`** — the arithmetic `LessThan(value, threshold)` descriptor, welded,
**COMPILED from `predicateLtAir`**. -/
def predicateLtDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-predicate-arith-lt::threshold-v1" PRED_WIDTH 2 [] predicateLtTiedAir).val

/-- ⚑ **THE CERTIFICATE, produced by the emit.** Every leg of the source is FORCED by the emitted
descriptor's constraints on any row window that satisfies them — `AirLeg.forces`, stated in the
SOURCE's vocabulary and never mentioning the lowering, so it is not `P → P`. Not re-derived here.

**Zero bytes move**: `lowerTiedAir … |>.val` is `lowerAir …` by `rfl`. -/
theorem predicateLtDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines predicateLtDesc [] predicateLtAir :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-predicate-arith-lt::threshold-v1" PRED_WIDTH 2 [] predicateLtTiedAir).property

/-- ⚑ **THE ZERO.** The certified lowering emits the term the bare lowering emitted, by `rfl` — so
the migration changed what this definition PROVES, not what it PRODUCES. No re-emit, no VK rotation.
Also the unfolding lemma for the cost/shape proofs below, which reason through `lowerAir`. -/
theorem predicateLtDesc_eq_lowerAir :
    predicateLtDesc = Dregg2.Circuit.Emit.EffectLower.lowerAir "dregg-predicate-arith-lt::threshold-v1" PRED_WIDTH 2 [] predicateLtAir := rfl

/-- ⚑ The compiler's output IS that constraint list, by `rfl`. -/
theorem predicateLtDesc_constraints :
    predicateLtDesc.constraints
      = [c1ThresholdPin, c2FactPin, c3SlotGate, c5DiffGate, c6RangeLookup,
         factHashLookup, factCommitLookup] := rfl

-- ⚑ THE CORPUS INVARIANT, DECIDED on this descriptor: every arithmetic body is canonical.
#guard normalFormOk predicateLtDesc == true

#guard emitVmJson2 predicateLtDesc ==
  "{\"name\":\"dregg-predicate-arith-lt::threshold-v1\",\"ir\":2,\"trace_width\":25,\"public_input_count\":2,\"challenges\":0,\"tables\":[{\"id\":2,\"name\":\"range\",\"arity\":1,\"sem\":\"range\",\"bits\":29}],\"constraints\":[{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":4,\"pi_index\":1},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":1}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":0}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":3}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":3}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":7},{\"t\":\"var\",\"v\":5},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":6},{\"t\":\"var\",\"v\":7},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":64207},{\"t\":\"const\",\"v\":1},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":9},{\"t\":\"var\",\"v\":10},{\"t\":\"var\",\"v\":11},{\"t\":\"var\",\"v\":12},{\"t\":\"var\",\"v\":13},{\"t\":\"var\",\"v\":14},{\"t\":\"var\",\"v\":15},{\"t\":\"var\",\"v\":16}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":4},{\"t\":\"var\",\"v\":9},{\"t\":\"var\",\"v\":8},{\"t\":\"var\",\"v\":24},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":4},{\"t\":\"var\",\"v\":17},{\"t\":\"var\",\"v\":18},{\"t\":\"var\",\"v\":19},{\"t\":\"var\",\"v\":20},{\"t\":\"var\",\"v\":21},{\"t\":\"var\",\"v\":22},{\"t\":\"var\",\"v\":23}]}],\"hash_sites\":[],\"ranges\":[]}"

/-- ⚑ RE-ESTABLISHED OVER THE COMPILED BODY (statement verbatim; only `c3Body`'s definition moved
from a hand-written `EmittedExpr` to the compiler's rendering). -/
theorem c3_body_zero_iff (a : Assignment) :
    c3Body.eval a = 0 ↔ a SLOT_A = a INPUT := by
  simp only [c3Body]; rw [gateBody_zero_iff]; simp [c3Src, Expr.eval]

/-- The C5 gate body is zero iff `DIFF = THRESHOLD − SLOT_A − 1` (the strict `<` diff identity).
⚑ Re-established over the compiled body. -/
theorem c5_body_zero_iff (a : Assignment) :
    c5Body.eval a = 0 ↔ a DIFF = a THRESHOLD - a SLOT_A - 1 := by
  simp only [c5Body]; rw [gateBody_zero_iff]
  simp only [c5Src, Expr.eval]
  omega

#guard decide (c3Body.eval (fun i => if i = SLOT_A ∨ i = INPUT then 7 else 0) = 0)
#guard decide (¬ (c3Body.eval (fun i => if i = SLOT_A then 7 else 0) = 0))
#guard decide (c5Body.eval (fun i => if i = DIFF then 59 else if i = THRESHOLD then 100 else if i = SLOT_A then 40 else 0) = 0)
#guard decide (¬ (c5Body.eval (fun i => if i = DIFF then 60 else if i = THRESHOLD then 100 else if i = SLOT_A then 40 else 0) = 0))

example : ([59] : List ℤ) ∈ rangeRows DIFF_BITS := by
  rw [range_row_mem_iff]; norm_num [DIFF_BITS]
example : ¬ (([2 ^ 29] : List ℤ) ∈ rangeRows DIFF_BITS) := by
  rw [range_row_mem_iff]; norm_num [DIFF_BITS]

#guard predicateLtDesc.traceWidth == PRED_WIDTH
#guard predicateLtDesc.piCount == 2
#guard predicateLtDesc.constraints.length == 7
#guard predicateLtDesc.tables.length == 1
#guard (chipLookupTuple [.var PREDICATE_SYM, .var INPUT, .var TERM1, .var TERM2,
                         .const 0, .const FACT_MARK, .const 1] FACT_HASH FACTHASH_LANES).length
         == CHIP_RATE + 1 + CHIP_OUT_LANES
#guard (chipLookupTuple [.var FACT_HASH, .var STATE_ROOT, .var BLINDING, .const 0]
                        FACT_COMMITMENT FACTCOMMIT_LANES).length
         == CHIP_RATE + 1 + CHIP_OUT_LANES

#assert_axioms c3_body_zero_iff
#assert_axioms c5_body_zero_iff


-- The blinded leg is arity-4 (tag 4 = `hash_4_to_1`'s `st[4]`), not the arity-2 absorb.
#guard (chipLookupTuple [.var FACT_HASH, .var STATE_ROOT, .var BLINDING, .const 0]
                        FACT_COMMITMENT FACTCOMMIT_LANES).head? == some (.const 4)
-- `BLINDING` is a real trace column, and it is NOT PI-bound (a witness, never revealed).
#guard BLINDING < PRED_WIDTH

end Dregg2.Circuit.Emit.PredicatesLtEmit
