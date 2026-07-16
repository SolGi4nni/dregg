/-
# Dregg2.Circuit.Emit.PredicatesLeEmit — the emitted `LessThanOrEqual(value, threshold)`
arithmetic-predicate descriptor (`dregg-predicate-arith-le::threshold-v1`).

## What this file IS

The `≤` sibling of `PredicatesArithmeticEmit.predicateGeDesc`. The hand-STARK deletion left the
comparison ops `Lte`/`Gt`/`Lt`/`Neq`/`InRange` with NO emitted descriptor (fail-closed); only `Gte`
was emitted. This file emits the `≤` case by the SAME one-tooth mechanism as `≥`, with the DIFF
subtraction swapped:

  * `≥` (`predicateGeDesc`):  `DIFF = value − threshold ∈ [0, 2^29)`  (`value ≥ threshold`);
  * `≤` (here):              `DIFF = threshold − value ∈ [0, 2^29)`  (`value ≤ threshold`).

The five teeth are the arithmetic-comparison core, carried one-for-one from the `≥` template:

| tooth | constraint                                                    |
|-------|---------------------------------------------------------------|
| C1    | `.piBinding first THRESHOLD PI_THRESHOLD`  (public threshold)  |
| C2    | `.piBinding first FACT_COMMITMENT PI_FACT_COMMITMENT`          |
| C3    | `.gate (SLOT_A − INPUT)`  (bare-Input slot identity)          |
| C5    | `.gate (DIFF − THRESHOLD + SLOT_A)`  (`DIFF = threshold−value`) |
| C6    | `.lookup ⟨range, [DIFF]⟩`  (`DIFF ∈ [0, 2^29)`)               |

The range lookup is the LOAD-BEARING tooth: `DIFF = threshold − value ∈ [0, 2^29)` iff
`value ≤ threshold` with a bounded gap (a `value > threshold` wraps `DIFF` to
`p − (value − threshold)`, far outside the interval — UNSAT).

| weld  | `.lookup ⟨poseidon2, …⟩` ×2  (`FACT_COMMITMENT` opens over `INPUT`)   |

**THE VALUE↔FACT WELD (M14).** `value ≤ threshold` alone is a claim about a number the prover chose.
What makes it a claim about TOKEN STATE is the second conjunct — `fact_commitment =
hash_2_to_1(hash_fact(pred, [value, t1, t2]), state_root)` — carried by the two Poseidon2 chip
lookups below, feeding the SAME `INPUT` column the range gadget bounds. Without them col 4
(`FACT_COMMITMENT`) and col 0 (`INPUT`) sit in DISJOINT constraint sets and a prover satisfies the
comparison on a value of its choosing while presenting the honest, verifier-expected commitment for
an UNRELATED value. This descriptor previously deferred the weld as "orthogonal hardening" — it is
not orthogonal, it is the half that binds the predicate to state. Now welded, geometry identical to
`≥` (`PredicatesArithmeticEmit`).

## Axiom hygiene
Definitional descriptor + byte-pinned `#guard` + non-vacuous per-gate lemmas (`omega`).
`#assert_axioms` ⊆ {} on the gate lemmas. NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.PredicatesLeEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId rangeTableDef emitVmJson2 rangeRows
   range_row_mem_iff chipLookupTuple CHIP_RATE CHIP_OUT_LANES)

set_option autoImplicit false

/-! ## §1 — trace column layout (one logical row). -/

/-- The private input value being compared. ALSO `terms[0]` of the hashed fact (the weld's leg-1
input the range gadget bounds). -/
def INPUT : Nat := 0
/-- The compiled expression-A result slot; C3 forces `SLOT_A = INPUT`. -/
def SLOT_A : Nat := 1
/-- The public comparison target, PI-bound to `PI_THRESHOLD`. -/
def THRESHOLD : Nat := 2
/-- The comparison difference `threshold − value`; range-proved into `[0, 2^29)`. -/
def DIFF : Nat := 3
/-- The public fact commitment, PI-bound to `PI_FACT_COMMITMENT` AND forced by the weld's leg 2 to
be `hash_2_to_1(FACT_HASH, STATE_ROOT)`. -/
def FACT_COMMITMENT : Nat := 4

/-! ### The value↔fact WELD columns (held forgery #2): tie `INPUT` to the committed fact.

`fact_commitment` (col 4) was ONLY PI-pinned, with `INPUT` (the compared value) a FREE witness — a
prover could prove `value ≤ threshold` about a value they do NOT hold, against a `fact_commitment`
naming a DIFFERENT real fact. The weld opens both hashes IN-CIRCUIT via two Poseidon2 chip lookups
feeding the SAME `INPUT` column, so a satisfying assignment forces `INPUT` to be the committed
fact's value (Poseidon2 CR). Identical geometry to `PredicatesArithmeticEmit` (`≥`). -/

/-- The fact's predicate symbol (`hash_fact` `state[0]`). Witness. -/
def PREDICATE_SYM : Nat := 5
/-- The fact's `term[1]` (`hash_fact` `state[2]`). Witness. -/
def TERM1 : Nat := 6
/-- The fact's `term[2]` (`hash_fact` `state[3]`). Witness. -/
def TERM2 : Nat := 7
/-- The token state root the fact commitment covers. Witness. -/
def STATE_ROOT : Nat := 8
/-- The recomputed `fact_hash = hash_fact(pred, [INPUT, term1, term2])` = the arity-7 lookup's out0. -/
def FACT_HASH : Nat := 9

/-- `hash_fact`'s `state[5]` domain marker (`0xFACF = 64207`). -/
def FACT_MARK : Int := 64207
/-- The seven out-lanes 1..7 of the arity-7 fact-hash chip lookup (out0 = `FACT_HASH`). -/
def FACTHASH_LANES : List Nat := [10, 11, 12, 13, 14, 15, 16]
/-- The seven out-lanes 1..7 of the arity-2 fact-commitment chip lookup (out0 = `FACT_COMMITMENT`). -/
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

/-- Base-trace width (the diff limbs are appended by the assembler, not counted here): the 5
predicate columns + 5 fact witness columns + 2×7 fact chip lanes + the blinding factor. -/
def PRED_WIDTH : Nat := 25

/-- Public-input slot for the threshold. -/
def PI_THRESHOLD : Nat := 0
/-- Public-input slot for the fact commitment. -/
def PI_FACT_COMMITMENT : Nat := 1

/-- The effective diff range width (`[0, 2^29)`). -/
def DIFF_BITS : Nat := 29

/-! ## §2 — the constraint list. -/

/-- **C1** — `threshold` matches the public input. -/
def c1ThresholdPin : VmConstraint2 := .base (.piBinding VmRow.first THRESHOLD PI_THRESHOLD)

/-- **C2** — `fact_commitment` matches the public input. -/
def c2FactPin : VmConstraint2 := .base (.piBinding VmRow.first FACT_COMMITMENT PI_FACT_COMMITMENT)

/-- The C3 slot-identity body `SLOT_A − INPUT`. -/
def c3Body : EmittedExpr := .add (.var SLOT_A) (.mul (.const (-1)) (.var INPUT))

/-- **C3** — the slot-identity gate. -/
def c3SlotGate : VmConstraint2 := .base (.gate c3Body)

/-- The C5 diff-computation body `DIFF − THRESHOLD + SLOT_A` (`DIFF = THRESHOLD − SLOT_A`, i.e.
`DIFF = threshold − value` — the `≤` swap of the `≥` template's `DIFF = value − threshold`). -/
def c5Body : EmittedExpr :=
  .add (.add (.var DIFF) (.mul (.const (-1)) (.var THRESHOLD))) (.var SLOT_A)

/-- **C5** — the diff-computation gate. -/
def c5DiffGate : VmConstraint2 := .base (.gate c5Body)

/-- **C6** — the diff range proof: `DIFF ∈ [0, 2^29)`. -/
def c6RangeLookup : VmConstraint2 := .lookup ⟨TableId.range, [.var DIFF]⟩

/-- **THE VALUE↔FACT WELD, leg 1** — arity-7 fact-hash chip lookup binding `FACT_HASH =
hash_fact(pred, [INPUT, term1, term2])`, feeding the SAME `INPUT` column the range gadget bounds. -/
def factHashLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2,
    chipLookupTuple [.var PREDICATE_SYM, .var INPUT, .var TERM1, .var TERM2,
                     .const 0, .const FACT_MARK, .const 1] FACT_HASH FACTHASH_LANES⟩

/-- **THE VALUE↔FACT WELD, leg 2 (BLINDED)** — arity-4 fact-commitment chip lookup binding
`FACT_COMMITMENT = Poseidon2_4to1([fact_hash, state_root, blinding, 0])`, tying the PI-pinned
commitment to the opened fact hash while leaving it rerandomizable by the private `BLINDING`.

The arity-4 chip absorb IS `hash_4_to_1`: `chip_absorb_lanes 4` takes the `seed456 = false` branch,
seeding `st[0..4] = inputs` and `st[4] = arity = 4` — exactly `poseidon2.rs::hash_4_to_1`. The leg
binds the production blinded commitment with ZERO change to the hash function. -/
def factCommitLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2,
    chipLookupTuple [.var FACT_HASH, .var STATE_ROOT, .var BLINDING, .const 0]
      FACT_COMMITMENT FACTCOMMIT_LANES⟩

/-- **`predicateLeDesc`** — the arithmetic `LessThanOrEqual(value, threshold)` descriptor, carrying
the Poseidon2 value↔fact weld (the two chip lookups) exactly as `≥`. -/
def predicateLeDesc : EffectVmDescriptor2 :=
  { name        := "dregg-predicate-arith-le::threshold-v1"
  , traceWidth  := PRED_WIDTH
  , piCount     := 2
  , tables      := [rangeTableDef DIFF_BITS]
  , constraints := [c1ThresholdPin, c2FactPin, c3SlotGate, c5DiffGate, c6RangeLookup,
                    factHashLookup, factCommitLookup]
  , hashSites   := []
  , ranges      := [] }

/-! ## §3 — the byte-pinned wire golden. -/

#guard emitVmJson2 predicateLeDesc ==
  "{\"name\":\"dregg-predicate-arith-le::threshold-v1\",\"ir\":2,\"trace_width\":25,\"public_input_count\":2,\"tables\":[{\"id\":2,\"name\":\"range\",\"arity\":1,\"sem\":\"range\",\"bits\":29}],\"constraints\":[{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":4,\"pi_index\":1},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":0}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"var\",\"v\":1}}},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":3}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":7},{\"t\":\"var\",\"v\":5},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":6},{\"t\":\"var\",\"v\":7},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":64207},{\"t\":\"const\",\"v\":1},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":9},{\"t\":\"var\",\"v\":10},{\"t\":\"var\",\"v\":11},{\"t\":\"var\",\"v\":12},{\"t\":\"var\",\"v\":13},{\"t\":\"var\",\"v\":14},{\"t\":\"var\",\"v\":15},{\"t\":\"var\",\"v\":16}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":4},{\"t\":\"var\",\"v\":9},{\"t\":\"var\",\"v\":8},{\"t\":\"var\",\"v\":24},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":4},{\"t\":\"var\",\"v\":17},{\"t\":\"var\",\"v\":18},{\"t\":\"var\",\"v\":19},{\"t\":\"var\",\"v\":20},{\"t\":\"var\",\"v\":21},{\"t\":\"var\",\"v\":22},{\"t\":\"var\",\"v\":23}]}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §4 — non-vacuous per-gate lemmas. -/

/-- The C3 gate body is zero iff `SLOT_A = INPUT`. -/
theorem c3_body_zero_iff (a : Assignment) :
    c3Body.eval a = 0 ↔ a SLOT_A = a INPUT := by
  simp only [c3Body, EmittedExpr.eval]
  constructor <;> intro h <;> omega

/-- The C5 gate body is zero iff `DIFF = THRESHOLD − SLOT_A` (the `≤` diff identity). -/
theorem c5_body_zero_iff (a : Assignment) :
    c5Body.eval a = 0 ↔ a DIFF = a THRESHOLD - a SLOT_A := by
  simp only [c5Body, EmittedExpr.eval]
  constructor <;> intro h <;> omega

-- Non-vacuity witnesses.
#guard decide (c3Body.eval (fun i => if i = SLOT_A ∨ i = INPUT then 7 else 0) = 0)
#guard decide (¬ (c3Body.eval (fun i => if i = SLOT_A then 7 else 0) = 0))
#guard decide (c5Body.eval (fun i => if i = DIFF then 60 else if i = THRESHOLD then 100 else if i = SLOT_A then 40 else 0) = 0)
#guard decide (¬ (c5Body.eval (fun i => if i = DIFF then 59 else if i = THRESHOLD then 100 else if i = SLOT_A then 40 else 0) = 0))

-- The range tooth, in Lean (via `range_row_mem_iff`, NEVER `decide` over the table).
example : ([60] : List ℤ) ∈ rangeRows DIFF_BITS := by
  rw [range_row_mem_iff]; norm_num [DIFF_BITS]
example : ¬ (([2 ^ 29] : List ℤ) ∈ rangeRows DIFF_BITS) := by
  rw [range_row_mem_iff]; norm_num [DIFF_BITS]

-- Shape pins.
#guard predicateLeDesc.traceWidth == PRED_WIDTH
#guard predicateLeDesc.piCount == 2
#guard predicateLeDesc.constraints.length == 7
#guard predicateLeDesc.tables.length == 1
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

end Dregg2.Circuit.Emit.PredicatesLeEmit
