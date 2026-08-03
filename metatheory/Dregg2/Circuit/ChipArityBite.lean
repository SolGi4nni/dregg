/-
# Dregg2.Circuit.ChipArityBite — the ARMED canary: every chip rail REFUSES an inadmissible arity.

`CHIP_ADMITTED_ARITIES` is the deployed chip AIR's degree-7 admission product
(`circuit/src/descriptor_ir2.rs`; the set is DERIVED by execution in
`circuit/tests/chip_absorb_arity_admission_gate.rs`, never re-typed there). Four Lean constructors
build a tuple whose ARITY TAG is the absorb block's length, and all four now take the admission as
an `autoParam`:

| rail | wire bus | constructor |
|---|---|---|
| wide | `TID_P2` | `chipLookupTupleN` |
| deployed | `TID_P2` | `chipLookupTuple` · `siteLookup` |
| narrow | `TID_P2_NARROW` | `chipLookupTupleNarrow` · `siteLookupNarrow` |
| table AIR | `ir2_p2` | `TableAirIR.chipAbsorbTuple` |

⚑ **THIS FILE IS THE PART THAT CAN GO RED.** The condition itself cannot: a side condition every
honest site discharges silently is INVISIBLE, and "the emitters all still build" is exactly what a
DELETED condition also looks like. `eaf64969a` demonstrated the wide rail's bite in a scratch file
(`PreFixBite.lean`) that was never committed, and the three unchecked rails below sat unchecked for
another day. So each refusal is asserted at build time, on **every rail and both site-level
constructors**, at the three arities this whole condition
exists to refuse — **8 and 14** (`dregg-guarded-hiding-span-m0::wide-blinded-commit-blind5-v1`, both
teeth) and **9** (the pre-`57105f387` blinded tooth) — plus positive controls at every admitted
arity, so a condition that refused EVERYTHING would not read as a pass.

⚠ `#guard_msgs` compares message TEXT. If a Lean upgrade rewords "could not synthesize default
value", update the expected text — do NOT delete the canary, and do not weaken it to
`drop error`: dropping the errors is the same as deleting the file.
-/
import Dregg2.Circuit.Emit.GraduateNarrow
import Dregg2.Circuit.TableAirIR

namespace Dregg2.Circuit.ChipArityBite

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (EffectVmDescriptor VmHashSite HashInput)

/-- An absorb block of `n` distinct column reads — the arity tag is `n`. -/
def ins (n : Nat) : List EmittedExpr := (List.range n).map .var

/-- A v1 hash site absorbing `n` columns. -/
def site (n : Nat) : VmHashSite := ⟨50, (List.range n).map .col, n⟩

/-- A v1 descriptor carrying one hash site at arity `n`. -/
def descAt (n : Nat) : EffectVmDescriptor :=
  { name := "chip-arity-bite", traceWidth := 64, piCount := 0, constraints := []
  , hashSites := [site n], ranges := [] }

/-! ## Positive controls — every ADMITTED arity still builds, silently, on every rail.

Without these the canary would pass just as well against a condition that refuses everything. -/

example : List EmittedExpr := chipLookupTuple (ins 0) 50 (siteLaneCols 100)
example : List EmittedExpr := chipLookupTuple (ins 2) 50 (siteLaneCols 100)
example : List EmittedExpr := chipLookupTuple (ins 3) 50 (siteLaneCols 100)
example : List EmittedExpr := chipLookupTuple (ins 4) 50 (siteLaneCols 100)
example : List EmittedExpr := chipLookupTuple (ins 7) 50 (siteLaneCols 100)
example : List EmittedExpr := chipLookupTuple (ins 11) 50 (siteLaneCols 100)
example : List EmittedExpr := chipLookupTuple (ins 16) 50 (siteLaneCols 100)
example : List EmittedExpr := chipLookupTupleN (ins 4) [40, 41]
example : List EmittedExpr := chipLookupTupleNarrow (ins 4) 50
example : Lookup := siteLookup [] (site 7) 100
example : Lookup := siteLookupNarrow [] (site 7)
example : List Dregg2.Circuit.TableAirIR.TExpr :=
  Dregg2.Circuit.TableAirIR.chipAbsorbTuple [1, 2, 3] 100
example : EffectVmDescriptor2 := Dregg2.Circuit.Emit.EffectVmEmitV2.graduateV1 (descAt 7)
example : EffectVmDescriptor2 := Dregg2.Circuit.Emit.EffectVmEmitV2.graduateV1Narrow (descAt 7)

/-- …and the emitter's own fail-closed gate ADMITS the arity-7 descriptor. -/
theorem graduable_at_admitted_arity :
    Dregg2.Circuit.Emit.EffectVmEmitV2.graduable (descAt 7) = true := by decide

/-! ## The bite: each inadmissible arity FAILS TO ELABORATE, on each rail. -/

section
set_option linter.unusedVariables false

-- ── the DEPLOYED 25-wide constructor, at 8 / 9 / 14 ──────────────────────────────────────────
/--
error: could not synthesize default value for parameter 'hAdm' using tactics
---
error: CHIP ABSORB ARITY NOT ADMITTED — the deployed chip AIR admits only CHIP_ADMITTED_ARITIES = [0, 2, 3, 4, 7, 11, 16] (the roots of the degree-7 admission product, circuit/src/descriptor_ir2.rs:3073). At any other arity the constraint has NO satisfying assignment and the descriptor is UNPROVABLE. PAD the absorb block up to the next admitted arity. Do NOT widen CHIP_ADMITTED_ARITIES: it is the chip's degree budget, and widening it here does not widen the AIR.
⊢ ChipArityAdmitted (ins 8).length
-/
#guard_msgs (error, drop info, drop warning) in
example : List EmittedExpr := chipLookupTuple (ins 8) 50 (siteLaneCols 100)

/--
error: could not synthesize default value for parameter 'hAdm' using tactics
---
error: CHIP ABSORB ARITY NOT ADMITTED — the deployed chip AIR admits only CHIP_ADMITTED_ARITIES = [0, 2, 3, 4, 7, 11, 16] (the roots of the degree-7 admission product, circuit/src/descriptor_ir2.rs:3073). At any other arity the constraint has NO satisfying assignment and the descriptor is UNPROVABLE. PAD the absorb block up to the next admitted arity. Do NOT widen CHIP_ADMITTED_ARITIES: it is the chip's degree budget, and widening it here does not widen the AIR.
⊢ ChipArityAdmitted (ins 9).length
-/
#guard_msgs (error, drop info, drop warning) in
example : List EmittedExpr := chipLookupTuple (ins 9) 50 (siteLaneCols 100)

/--
error: could not synthesize default value for parameter 'hAdm' using tactics
---
error: CHIP ABSORB ARITY NOT ADMITTED — the deployed chip AIR admits only CHIP_ADMITTED_ARITIES = [0, 2, 3, 4, 7, 11, 16] (the roots of the degree-7 admission product, circuit/src/descriptor_ir2.rs:3073). At any other arity the constraint has NO satisfying assignment and the descriptor is UNPROVABLE. PAD the absorb block up to the next admitted arity. Do NOT widen CHIP_ADMITTED_ARITIES: it is the chip's degree budget, and widening it here does not widen the AIR.
⊢ ChipArityAdmitted (ins 14).length
-/
#guard_msgs (error, drop info, drop warning) in
example : List EmittedExpr := chipLookupTuple (ins 14) 50 (siteLaneCols 100)

-- ── the NARROW (`TID_P2_NARROW`) constructor — served by the SAME chip rows ──────────────────
/--
error: could not synthesize default value for parameter 'hAdm' using tactics
---
error: CHIP ABSORB ARITY NOT ADMITTED — the deployed chip AIR admits only CHIP_ADMITTED_ARITIES = [0, 2, 3, 4, 7, 11, 16] (the roots of the degree-7 admission product, circuit/src/descriptor_ir2.rs:3073). At any other arity the constraint has NO satisfying assignment and the descriptor is UNPROVABLE. PAD the absorb block up to the next admitted arity. Do NOT widen CHIP_ADMITTED_ARITIES: it is the chip's degree budget, and widening it here does not widen the AIR.
⊢ ChipArityAdmitted (ins 8).length
-/
#guard_msgs (error, drop info, drop warning) in
example : List EmittedExpr := chipLookupTupleNarrow (ins 8) 50

-- ── the TABLE-AIR chip absorb (`ir2_p2`) ────────────────────────────────────────────────────
/--
error: could not synthesize default value for parameter 'hAdm' using tactics
---
error: CHIP ABSORB ARITY NOT ADMITTED — the deployed chip AIR admits only CHIP_ADMITTED_ARITIES = [0, 2, 3, 4, 7, 11, 16] (the roots of the degree-7 admission product, circuit/src/descriptor_ir2.rs:3073). At any other arity the constraint has NO satisfying assignment and the descriptor is UNPROVABLE. PAD the absorb block up to the next admitted arity. Do NOT widen CHIP_ADMITTED_ARITIES: it is the chip's degree budget, and widening it here does not widen the AIR.
⊢ ChipArityAdmitted [1, 2, 3, 4, 5, 6, 7, 8, 9].length
-/
#guard_msgs (error, drop info, drop warning) in
example : List Dregg2.Circuit.TableAirIR.TExpr :=
  Dregg2.Circuit.TableAirIR.chipAbsorbTuple [1, 2, 3, 4, 5, 6, 7, 8, 9] 100

-- ── the WIDE constructor (`chipLookupTupleN`, `TID_P2`), at 8 / 9 / 14 ───────────────────
-- `eaf64969a` checked this rail and demonstrated its bite in a scratch file that was never
-- committed. This is that demonstration, in the build.
/--
error: could not synthesize default value for parameter 'hAdm' using tactics
---
error: CHIP ABSORB ARITY NOT ADMITTED — the deployed chip AIR admits only CHIP_ADMITTED_ARITIES = [0, 2, 3, 4, 7, 11, 16] (the roots of the degree-7 admission product, circuit/src/descriptor_ir2.rs:3073). At any other arity the constraint has NO satisfying assignment and the descriptor is UNPROVABLE. PAD the absorb block up to the next admitted arity. Do NOT widen CHIP_ADMITTED_ARITIES: it is the chip's degree budget, and widening it here does not widen the AIR.
⊢ ChipArityAdmitted (ins 8).length
-/
#guard_msgs (error, drop info, drop warning) in
example : List EmittedExpr := chipLookupTupleN (ins 8) [40, 41]

/--
error: could not synthesize default value for parameter 'hAdm' using tactics
---
error: CHIP ABSORB ARITY NOT ADMITTED — the deployed chip AIR admits only CHIP_ADMITTED_ARITIES = [0, 2, 3, 4, 7, 11, 16] (the roots of the degree-7 admission product, circuit/src/descriptor_ir2.rs:3073). At any other arity the constraint has NO satisfying assignment and the descriptor is UNPROVABLE. PAD the absorb block up to the next admitted arity. Do NOT widen CHIP_ADMITTED_ARITIES: it is the chip's degree budget, and widening it here does not widen the AIR.
⊢ ChipArityAdmitted (ins 9).length
-/
#guard_msgs (error, drop info, drop warning) in
example : List EmittedExpr := chipLookupTupleN (ins 9) [40, 41]

/--
error: could not synthesize default value for parameter 'hAdm' using tactics
---
error: CHIP ABSORB ARITY NOT ADMITTED — the deployed chip AIR admits only CHIP_ADMITTED_ARITIES = [0, 2, 3, 4, 7, 11, 16] (the roots of the degree-7 admission product, circuit/src/descriptor_ir2.rs:3073). At any other arity the constraint has NO satisfying assignment and the descriptor is UNPROVABLE. PAD the absorb block up to the next admitted arity. Do NOT widen CHIP_ADMITTED_ARITIES: it is the chip's degree budget, and widening it here does not widen the AIR.
⊢ ChipArityAdmitted (ins 14).length
-/
#guard_msgs (error, drop info, drop warning) in
example : List EmittedExpr := chipLookupTupleN (ins 14) [40, 41]

-- ── the NARROW constructor, at the other two arities ─────────────────────────────
/--
error: could not synthesize default value for parameter 'hAdm' using tactics
---
error: CHIP ABSORB ARITY NOT ADMITTED — the deployed chip AIR admits only CHIP_ADMITTED_ARITIES = [0, 2, 3, 4, 7, 11, 16] (the roots of the degree-7 admission product, circuit/src/descriptor_ir2.rs:3073). At any other arity the constraint has NO satisfying assignment and the descriptor is UNPROVABLE. PAD the absorb block up to the next admitted arity. Do NOT widen CHIP_ADMITTED_ARITIES: it is the chip's degree budget, and widening it here does not widen the AIR.
⊢ ChipArityAdmitted (ins 9).length
-/
#guard_msgs (error, drop info, drop warning) in
example : List EmittedExpr := chipLookupTupleNarrow (ins 9) 50

/--
error: could not synthesize default value for parameter 'hAdm' using tactics
---
error: CHIP ABSORB ARITY NOT ADMITTED — the deployed chip AIR admits only CHIP_ADMITTED_ARITIES = [0, 2, 3, 4, 7, 11, 16] (the roots of the degree-7 admission product, circuit/src/descriptor_ir2.rs:3073). At any other arity the constraint has NO satisfying assignment and the descriptor is UNPROVABLE. PAD the absorb block up to the next admitted arity. Do NOT widen CHIP_ADMITTED_ARITIES: it is the chip's degree budget, and widening it here does not widen the AIR.
⊢ ChipArityAdmitted (ins 14).length
-/
#guard_msgs (error, drop info, drop warning) in
example : List EmittedExpr := chipLookupTupleNarrow (ins 14) 50

-- ── the TABLE-AIR chip absorb, at the other two arities ───────────────────────
/--
error: could not synthesize default value for parameter 'hAdm' using tactics
---
error: CHIP ABSORB ARITY NOT ADMITTED — the deployed chip AIR admits only CHIP_ADMITTED_ARITIES = [0, 2, 3, 4, 7, 11, 16] (the roots of the degree-7 admission product, circuit/src/descriptor_ir2.rs:3073). At any other arity the constraint has NO satisfying assignment and the descriptor is UNPROVABLE. PAD the absorb block up to the next admitted arity. Do NOT widen CHIP_ADMITTED_ARITIES: it is the chip's degree budget, and widening it here does not widen the AIR.
⊢ ChipArityAdmitted [1, 2, 3, 4, 5, 6, 7, 8].length
-/
#guard_msgs (error, drop info, drop warning) in
example : List Dregg2.Circuit.TableAirIR.TExpr :=
  Dregg2.Circuit.TableAirIR.chipAbsorbTuple [1, 2, 3, 4, 5, 6, 7, 8] 100

/--
error: could not synthesize default value for parameter 'hAdm' using tactics
---
error: CHIP ABSORB ARITY NOT ADMITTED — the deployed chip AIR admits only CHIP_ADMITTED_ARITIES = [0, 2, 3, 4, 7, 11, 16] (the roots of the degree-7 admission product, circuit/src/descriptor_ir2.rs:3073). At any other arity the constraint has NO satisfying assignment and the descriptor is UNPROVABLE. PAD the absorb block up to the next admitted arity. Do NOT widen CHIP_ADMITTED_ARITIES: it is the chip's degree budget, and widening it here does not widen the AIR.
⊢ ChipArityAdmitted [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14].length
-/
#guard_msgs (error, drop info, drop warning) in
example : List Dregg2.Circuit.TableAirIR.TExpr :=
  Dregg2.Circuit.TableAirIR.chipAbsorbTuple
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] 100

-- ── the SITE-level constructors ── the two the EMITTER actually calls ───────────────
-- `graduateV1` builds its chip lookups through `siteLookup` / `siteLookupNarrow`, so a rail
-- bitten only at `chipLookupTuple*` would still let a bad site through at the level above.
/--
error: could not synthesize default value for parameter 'hAdm' using tactics
---
error: CHIP ABSORB ARITY NOT ADMITTED — the deployed chip AIR admits only CHIP_ADMITTED_ARITIES = [0, 2, 3, 4, 7, 11, 16] (the roots of the degree-7 admission product, circuit/src/descriptor_ir2.rs:3073). At any other arity the constraint has NO satisfying assignment and the descriptor is UNPROVABLE. PAD the absorb block up to the next admitted arity. Do NOT widen CHIP_ADMITTED_ARITIES: it is the chip's degree budget, and widening it here does not widen the AIR.
⊢ ChipArityAdmitted (site 8).inputs.length
-/
#guard_msgs (error, drop info, drop warning) in
example : Lookup := siteLookup [] (site 8) 100

/--
error: could not synthesize default value for parameter 'hAdm' using tactics
---
error: CHIP ABSORB ARITY NOT ADMITTED — the deployed chip AIR admits only CHIP_ADMITTED_ARITIES = [0, 2, 3, 4, 7, 11, 16] (the roots of the degree-7 admission product, circuit/src/descriptor_ir2.rs:3073). At any other arity the constraint has NO satisfying assignment and the descriptor is UNPROVABLE. PAD the absorb block up to the next admitted arity. Do NOT widen CHIP_ADMITTED_ARITIES: it is the chip's degree budget, and widening it here does not widen the AIR.
⊢ ChipArityAdmitted (site 9).inputs.length
-/
#guard_msgs (error, drop info, drop warning) in
example : Lookup := siteLookupNarrow [] (site 9)

end

/-- The emitter's own fail-closed gate REFUSES the arity-9 descriptor — so graduation is refused
before any lookup is built, and `graduable` is not merely a `≤ CHIP_RATE` fit any more. -/
theorem graduable_refuses_inadmissible_arity :
    Dregg2.Circuit.Emit.EffectVmEmitV2.graduable (descAt 9) = false := by decide

/-- And the three refused arities are each `≤ CHIP_RATE` — which is exactly why the OLD condition
let them through. This is the statement that makes the strengthening non-cosmetic. -/
theorem refused_arities_are_all_within_the_rate :
    (¬ ChipArityAdmitted 8 ∧ 8 ≤ CHIP_RATE) ∧
    (¬ ChipArityAdmitted 9 ∧ 9 ≤ CHIP_RATE) ∧
    (¬ ChipArityAdmitted 14 ∧ 14 ≤ CHIP_RATE) := by decide

#assert_axioms graduable_at_admitted_arity
#assert_axioms graduable_refuses_inadmissible_arity
#assert_axioms refused_arities_are_all_within_the_rate

end Dregg2.Circuit.ChipArityBite
