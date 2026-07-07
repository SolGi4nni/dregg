/-
# Dregg2.Circuit.Emit.PredicatesArithmeticEmit — the emit-from-Lean face of the
arithmetic-predicate family (`circuit/src/dsl/predicates/arithmetic.rs`), the canonical
`GreaterThanOrEqual(value, threshold)` threshold predicate.

## What this file IS

A REAL `EffectVmDescriptor2` that DECLARES, in the IR-v2 grammar, the statement "a private
`value` satisfies `value ≥ threshold` for a public `threshold`, carrying a public
`fact_commitment`". It re-expresses the hand-AIR arithmetic-predicate semantics
(`circuit/src/dsl/predicates/arithmetic.rs::build_arithmetic_constraints`, the
`DiffKind::ResultMinusThreshold` / GTE lane with a bare-`Input` expression) as an IR-v2
descriptor whose diff range-proof is a `TableSem::Range` lookup rather than the ~30 explicit
bit columns the hand DSL lays down (`arithmetic.rs` C6 @708–738 — the idiomatic IR-v2 target
the dossier prescribes).

The five hand-AIR teeth this descriptor carries, one-for-one:

| hand AIR (arithmetic.rs)                                   | IR-v2 constraint here            |
|-----------------------------------------------------------|----------------------------------|
| C1 PiBinding threshold_col ↔ PI_THRESHOLD (@547)          | `.base (.piBinding .first …)`    |
| C2 PiBinding fact_commitment_col ↔ PI_FACT_COMMITMENT (@553)| `.base (.piBinding .first …)`   |
| C3 slot identity `slot_a == input[0]` (`add_slot_constraints`, Input)| `.base (.gate …)`     |
| C5 diff `diff − result_a + threshold == 0` (@578)         | `.base (.gate …)`                |
| C6 range proof `diff ∈ [0, 2^29)` (bit decomp + hi-bit=0) | `.lookup ⟨.range, [diff]⟩`       |

The hand AIR decomposes `diff` into `NUM_BITS = 30` bits and forces the top bit to zero
(`arithmetic.rs` @736, "proves diff < 2^29"): the NET admissible interval is `[0, 2^29)`. The
range lookup `⟨.range, [diff]⟩` against a `rangeTableDef 29` table enforces EXACTLY that
interval (`DescriptorIR2.rangeRows_mem_iff`), and it is the load-bearing tooth of a `≥`
predicate: `diff = value − threshold` lies in `[0, 2^29)` iff `value ≥ threshold` (a
`value < threshold` wraps `diff` to `p − (threshold − value)`, far outside the interval — UNSAT).

## The byte-pin and the Rust gate

`emitVmJson2 predicateGeDesc` is BYTE-PINNED below (`#guard`). The Rust gate
(`circuit-prove/tests/predicates_arithmetic_emit_gate.rs`) decodes this exact string via
`parse_vm_descriptor2`, asserts it EQUALS an independently hand-built descriptor, proves an
HONEST `value ≥ threshold` witness through the REAL `prove_vm_descriptor2` / `verify_vm_descriptor2`
(ACCEPT), and runs mutation canaries that each bite a distinct constraint: a `value < threshold`
witness (diff out of range → the C6 range tooth), an inconsistent-but-in-range `diff` (the C5 gate),
a `slot_a ≠ input` (the C3 slot identity), and a forged public `threshold` / `fact_commitment`
(the C1 / C2 PI bindings).

## Axiom hygiene

Definitional descriptor + a byte-pinned `#guard` on its wire string + genuinely-proven,
non-vacuous semantic lemmas on the two gate bodies (`c3_body_zero_iff`, `c5_body_zero_iff` —
each TRUE iff its slot/diff identity holds, FALSE otherwise). `#assert_axioms` ⊆ {} (pure
`omega`). NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.PredicatesArithmeticEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId rangeTableDef emitVmJson2 rangeRows)

set_option autoImplicit false

/-! ## §1 — The trace column layout (a single logical row, repeated to a power-of-two height).

The whole predicate fits ONE row. The five base columns below carry the hand AIR's
`threshold_col` / `diff_col` / `fact_commitment_col` plus the compiled-expression input and its
identity slot; the `diff`-decomposition limb columns the hand AIR lays as `diff_bits` are NOT
base columns here — the range lookup's `decomp_cols(29)` limbs are appended past `trace_width`
by the Rust assembler (`descriptor_ir2.rs::build_traces`), the whole point of the lookup idiom. -/

/-- The private input value being compared (`arithmetic.rs` input slot 0). -/
def INPUT : Nat := 0
/-- The compiled expression-A result slot (`slots_a_start + result_slot`); for a bare-`Input`
expression the C3 slot constraint forces `SLOT_A = INPUT`. -/
def SLOT_A : Nat := 1
/-- The public comparison target (`arithmetic.rs` `threshold_col`), PI-bound to `PI_THRESHOLD`. -/
def THRESHOLD : Nat := 2
/-- The comparison difference (`arithmetic.rs` `diff_col`); range-proved into `[0, 2^29)`. -/
def DIFF : Nat := 3
/-- The public fact commitment (`arithmetic.rs` `fact_commitment_col`), PI-bound to
`PI_FACT_COMMITMENT`. -/
def FACT_COMMITMENT : Nat := 4

/-- Total base-trace width (the diff limbs are appended by the assembler, not counted here). -/
def PRED_WIDTH : Nat := 5

/-- Public-input slot for the threshold (`arithmetic.rs::PI_THRESHOLD = 0`). -/
def PI_THRESHOLD : Nat := 0
/-- Public-input slot for the fact commitment (`arithmetic.rs::PI_FACT_COMMITMENT = 1`). -/
def PI_FACT_COMMITMENT : Nat := 1

/-- The effective diff range width: the hand AIR's `NUM_BITS = 30` bits with the top bit forced
to zero leaves `diff ∈ [0, 2^29)` (`arithmetic.rs` @736). -/
def DIFF_BITS : Nat := 29

/-! ## §2 — The constraint list (PI bindings · slot identity · diff gate · range proof). -/

/-- **C1** — `threshold` matches the public input (`arithmetic.rs` @546–550). -/
def c1ThresholdPin : VmConstraint2 := .base (.piBinding VmRow.first THRESHOLD PI_THRESHOLD)

/-- **C2** — `fact_commitment` matches the public input (`arithmetic.rs` @552–556). -/
def c2FactPin : VmConstraint2 := .base (.piBinding VmRow.first FACT_COMMITMENT PI_FACT_COMMITMENT)

/-- The C3 slot-identity body `SLOT_A − INPUT` (a bare-`Input` compiled slot equals its input —
`arithmetic.rs::add_slot_constraints`, the `CompiledOp::Input` arm `slot == input[i]`). -/
def c3Body : EmittedExpr := .add (.var SLOT_A) (.mul (.const (-1)) (.var INPUT))

/-- **C3** — the slot-identity gate. -/
def c3SlotGate : VmConstraint2 := .base (.gate c3Body)

/-- The C5 diff-computation body `DIFF − SLOT_A + THRESHOLD` (`arithmetic.rs` @578–595, the
`ResultMinusThreshold` arm `diff − result_a + threshold == 0`). -/
def c5Body : EmittedExpr :=
  .add (.add (.var DIFF) (.mul (.const (-1)) (.var SLOT_A))) (.var THRESHOLD)

/-- **C5** — the diff-computation gate. -/
def c5DiffGate : VmConstraint2 := .base (.gate c5Body)

/-- **C6** — the diff range proof as a `Range` lookup: `diff ∈ [0, 2^29)` (`arithmetic.rs`
@707–738, the bit-decomposition + high-bit-zero block, mapped to the idiomatic IR-v2 range
table). The Rust assembler decomposes `DIFF` into `decomp_cols(29)` limbs on the byte bus. -/
def c6RangeLookup : VmConstraint2 := .lookup ⟨TableId.range, [.var DIFF]⟩

/-- **`predicateGeDesc`** — the arithmetic `GreaterThanOrEqual(value, threshold)` descriptor.
`tables` declares the range table (its `bits` feeds the assembler's `decomp_cols`); the byte
table is Presence-detected from the range lookup, so no other table is declared. -/
def predicateGeDesc : EffectVmDescriptor2 :=
  { name        := "dregg-predicate-arith-ge::threshold-v1"
  , traceWidth  := PRED_WIDTH
  , piCount     := 2
  , tables      := [rangeTableDef DIFF_BITS]
  , constraints := [c1ThresholdPin, c2FactPin, c3SlotGate, c5DiffGate, c6RangeLookup]
  , hashSites   := []
  , ranges      := [] }

/-! ## §3 — The byte-pinned wire golden (the Rust decoder ingests THIS string). -/

#guard emitVmJson2 predicateGeDesc ==
  "{\"name\":\"dregg-predicate-arith-ge::threshold-v1\",\"ir\":2,\"trace_width\":5,\"public_input_count\":2,\"tables\":[{\"id\":2,\"name\":\"range\",\"arity\":1,\"sem\":\"range\",\"bits\":29}],\"constraints\":[{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":4,\"pi_index\":1},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":0}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"var\",\"v\":2}}},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":3}]}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §4 — Genuinely-proven, non-vacuous semantic lemmas (the gate teeth).

Each gate body is zero EXACTLY when its hand-AIR identity holds. These are the Lean faces of the
C3 / C5 gates the emitted `.gate`s enforce row-for-row in the Rust Ir2 main AIR. -/

/-- The C3 gate body is zero iff the slot equals its input (`SLOT_A = INPUT`). -/
theorem c3_body_zero_iff (a : Assignment) :
    c3Body.eval a = 0 ↔ a SLOT_A = a INPUT := by
  simp only [c3Body, EmittedExpr.eval]
  constructor <;> intro h <;> omega

/-- The C5 gate body is zero iff `diff = result_a − threshold` (`DIFF = SLOT_A − THRESHOLD`) —
the diff-computation identity that, once `diff` is range-proved into `[0, 2^29)`, forces
`SLOT_A ≥ THRESHOLD` (the predicate). -/
theorem c5_body_zero_iff (a : Assignment) :
    c5Body.eval a = 0 ↔ a DIFF = a SLOT_A - a THRESHOLD := by
  simp only [c5Body, EmittedExpr.eval]
  constructor <;> intro h <;> omega

-- Non-vacuity witnesses: each gate ACCEPTS a satisfying assignment and REJECTS a violating one.
#guard decide (c3Body.eval (fun i => if i = SLOT_A ∨ i = INPUT then 7 else 0) = 0)
#guard decide (¬ (c3Body.eval (fun i => if i = SLOT_A then 7 else 0) = 0))
#guard decide (c5Body.eval (fun i => if i = DIFF then 60 else if i = SLOT_A then 100 else if i = THRESHOLD then 40 else 0) = 0)
#guard decide (¬ (c5Body.eval (fun i => if i = DIFF then 59 else if i = SLOT_A then 100 else if i = THRESHOLD then 40 else 0) = 0))

-- The range tooth, in Lean: `diff = 60 ∈ [0, 2^29)` is a range row; a wrapped `value < threshold`
-- diff (here modeled by `2^29`, the first out-of-range value) is NOT.
#guard decide (([60] : List ℤ) ∈ rangeRows DIFF_BITS)
#guard decide (¬ (([2^29] : List ℤ) ∈ rangeRows DIFF_BITS))

-- Shape pins.
#guard predicateGeDesc.traceWidth == PRED_WIDTH
#guard predicateGeDesc.piCount == 2
#guard predicateGeDesc.constraints.length == 5
#guard predicateGeDesc.tables.length == 1

#assert_axioms c3_body_zero_iff
#assert_axioms c5_body_zero_iff

end Dregg2.Circuit.Emit.PredicatesArithmeticEmit
