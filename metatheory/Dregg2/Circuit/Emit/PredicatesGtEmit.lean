/-
# Dregg2.Circuit.Emit.PredicatesGtEmit — the emitted `GreaterThan(value, threshold)`
arithmetic-predicate descriptor (`dregg-predicate-arith-gt::threshold-v1`).

The strict `>` sibling of `PredicatesArithmeticEmit.predicateGeDesc`. Strict comparison is `≥` with a
`+1`: `value > threshold ↔ value ≥ threshold + 1 ↔ value − threshold − 1 ≥ 0`. So the DIFF is the
`≥` DIFF minus one:

  * `≥`:  `DIFF = value − threshold ∈ [0, 2^29)`;
  * `>`:  `DIFF = value − threshold − 1 ∈ [0, 2^29)`.

The five teeth are the arithmetic-comparison core (C1/C2 PI pins, C3 slot identity, C5 diff gate,
C6 range lookup); the C6 range lookup is the load-bearing tooth (a `value ≤ threshold` wraps
`DIFF = value − threshold − 1` below zero — UNSAT).

**THE VALUE↔FACT WELD (M14).** Two Poseidon2 chip lookups force `FACT_COMMITMENT =
hash_2_to_1(hash_fact(pred, [INPUT, t1, t2]), STATE_ROOT)` over the SAME `INPUT` the comparison
bounds, so col 4 and col 0 stop being in DISJOINT constraint sets. Without the weld a prover proves
`value > threshold` on a value of its choosing while presenting the honest, verifier-expected
commitment for an UNRELATED value. (This file previously called the weld "an orthogonal family-wide
follow-up" — it is the half that binds the predicate to token state.) Geometry identical to `≥`.

`#assert_axioms` ⊆ {} on the gate lemmas. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.AirNormalForm

namespace Dregg2.Circuit.Emit.PredicatesGtEmit

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

def c3Src : Constraint := ⟨.var SLOT_A, .var INPUT⟩
/-- …and the body the COMPILER renders for it. -/
def c3Body : EmittedExpr := gateBody c3Src
def c3SlotGate : VmConstraint2 := lowerConstraint c3Src

/-- The C5 diff-computation body `DIFF − SLOT_A + THRESHOLD + 1` (`DIFF = SLOT_A − THRESHOLD − 1`,
i.e. `DIFF = value − threshold − 1` — the strict `>` shift of the `≥` template). -/
def c5Src : Constraint :=
  ⟨.var DIFF, .add (.add (.var SLOT_A) (.mul (.const (-1)) (.var THRESHOLD))) (.const (-1))⟩
/-- …and the body the COMPILER renders for it. -/
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

/-! **`predicateGtDesc`** — the arithmetic `GreaterThan(value, threshold)` descriptor, welded. -/
/-- ⚑ **THE AIR SOURCE** — the legs in emission order. -/
def predicateGtAir : EffectAir :=
  { tables := [rangeTableDef DIFF_BITS]
  , legs   := [ .pin ⟨VmRow.first, THRESHOLD, PI_THRESHOLD⟩
              , .pin ⟨VmRow.first, FACT_COMMITMENT, PI_FACT_COMMITMENT⟩
              , .gate c3Src
              , .gate c5Src
              , .lookup c6RangeLeg
              , .lookup factHashLeg
              , .lookup factCommitLeg ] }

#guard predicateGtAir.mainRailOk == true

/-- **`predicateGtDesc`** — COMPILED from `predicateGtAir`. -/
def predicateGtDesc : EffectVmDescriptor2 :=
  lowerAir "dregg-predicate-arith-gt::threshold-v1" PRED_WIDTH 2 [] predicateGtAir

/-- ⚑ The compiler's output IS that constraint list, by `rfl` — so every downstream
statement over these names is a statement about the COMPILED object. -/
theorem predicateGtDesc_constraints :
    predicateGtDesc.constraints = [c1ThresholdPin, c2FactPin, c3SlotGate, c5DiffGate, c6RangeLookup, factHashLookup, factCommitLookup] := rfl

-- ⚑ THE CORPUS INVARIANT, DECIDED on this descriptor: every arithmetic body is canonical.
#guard normalFormOk predicateGtDesc == true

#guard emitVmJson2 predicateGtDesc ==
  "{\"name\":\"dregg-predicate-arith-gt::threshold-v1\",\"ir\":2,\"trace_width\":25,\"public_input_count\":2,\"tables\":[{\"id\":2,\"name\":\"range\",\"arity\":1,\"sem\":\"range\",\"bits\":29}],\"constraints\":[{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":4,\"pi_index\":1},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":1}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":0}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":3}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":3}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":7},{\"t\":\"var\",\"v\":5},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":6},{\"t\":\"var\",\"v\":7},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":64207},{\"t\":\"const\",\"v\":1},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":9},{\"t\":\"var\",\"v\":10},{\"t\":\"var\",\"v\":11},{\"t\":\"var\",\"v\":12},{\"t\":\"var\",\"v\":13},{\"t\":\"var\",\"v\":14},{\"t\":\"var\",\"v\":15},{\"t\":\"var\",\"v\":16}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":4},{\"t\":\"var\",\"v\":9},{\"t\":\"var\",\"v\":8},{\"t\":\"var\",\"v\":24},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":4},{\"t\":\"var\",\"v\":17},{\"t\":\"var\",\"v\":18},{\"t\":\"var\",\"v\":19},{\"t\":\"var\",\"v\":20},{\"t\":\"var\",\"v\":21},{\"t\":\"var\",\"v\":22},{\"t\":\"var\",\"v\":23}]}],\"hash_sites\":[],\"ranges\":[]}"

theorem c3_body_zero_iff (a : Assignment) :
    c3Body.eval a = 0 ↔ a SLOT_A = a INPUT := by
  simp only [c3Body]; rw [gateBody_zero_iff]; simp [c3Src, Expr.eval]

/-- The C5 gate body is zero iff `DIFF = SLOT_A − THRESHOLD − 1` (the strict `>` diff identity). -/
theorem c5_body_zero_iff (a : Assignment) :
    c5Body.eval a = 0 ↔ a DIFF = a SLOT_A - a THRESHOLD - 1 := by
  simp only [c5Body]; rw [gateBody_zero_iff]
  simp only [c5Src, Expr.eval]
  omega

#guard decide (c3Body.eval (fun i => if i = SLOT_A ∨ i = INPUT then 7 else 0) = 0)
#guard decide (¬ (c3Body.eval (fun i => if i = SLOT_A then 7 else 0) = 0))
#guard decide (c5Body.eval (fun i => if i = DIFF then 59 else if i = SLOT_A then 100 else if i = THRESHOLD then 40 else 0) = 0)
#guard decide (¬ (c5Body.eval (fun i => if i = DIFF then 60 else if i = SLOT_A then 100 else if i = THRESHOLD then 40 else 0) = 0))

example : ([59] : List ℤ) ∈ rangeRows DIFF_BITS := by
  rw [range_row_mem_iff]; norm_num [DIFF_BITS]
example : ¬ (([2 ^ 29] : List ℤ) ∈ rangeRows DIFF_BITS) := by
  rw [range_row_mem_iff]; norm_num [DIFF_BITS]

#guard predicateGtDesc.traceWidth == PRED_WIDTH
#guard predicateGtDesc.piCount == 2
#guard predicateGtDesc.constraints.length == 7
#guard predicateGtDesc.tables.length == 1
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

end Dregg2.Circuit.Emit.PredicatesGtEmit
