/-
# Dregg2.Circuit.PeepholeZeroTestElision — the asserted-frontier zero-test elision, MEASURED on the pilot.

STATE THE SUBSTRATE OUT LOUD: this is Lean-authored AIR. Every number below is read off the
compiler's PROVEN closed form `TypedLinearPredicateDescriptorIR2.descriptor_exact_resources`; no Rust
hand-writes a constraint, and no cost is asserted — the resource forms are theorems over the actual
emitted `EffectVmDescriptor2`.

## What the peephole rule is (design DESIGN-peephole-layout-optimizer.md §2, rule R1)

An atom on the ASSERTED-TRUE conjunction frontier of `source` (reachable from the root through
`and`-edges only) has its truth forced by the accept equation `output = 1`: the and-tree output is
the product of its child bits, so acceptance forces every asserted atom's bit to 1, hence its residual
to 0. For such an atom the `zeroTest` node (3 degree-≤2 gates + 2 witness columns + 3 multiplications)
is NOT load-bearing: a single degree-1 gate `affineTermₐ = 0` says exactly the same thing at the only
accepting assignment. R1 replaces the atom's `atomLink` + `zeroTest` + its `and`-spine node with that
one linear gate, then the ALREADY-CERTIFIED E1 dead-column deletion removes the freed columns.

## THE FINDING on FieldDeltaRangePilot — R1 does NOT reach hand-parity here, and WHY

The pilot's source is

    source = atom0 ∧ atom1 ∧ ⋀_{j<30} ( b_j=0  ∨  b_j=1 )

(`andAll [transition-atom, recompose-atom, boolAtom_0, …, boolAtom_29]`). The asserted FRONTIER
atoms — reachable from the root through `and`-edges only — are EXACTLY `atom0` (the modular
transition `new-old-delta=0`) and `atom1` (the recomposition `new-Σ2ʲbⱼ=0`). The 30 booleanity
components are DISJUNCTIONS: their two leaf atoms `b_j=0` / `b_j=1` sit under an `∨`, where the
zero-test IS load-bearing — the bit value is genuinely consumed by the `∨`, and neither disjunct's
residual is forced to 0. R1 therefore fires on 2 atoms only. This is not a defect of R1; it is design
§6 verbatim ("the ∨/¬ remainder keeps its zero-tests, correctly"). The design's "→ hand-parity"
recovery (§4) is stated for a PURE CONJUNCTION of equalities; FieldDeltaRangePilot is 2 conjoined
equalities + 30 conjoined disjunctions, so only the 2 equalities recover.

Measured recovery (proven closed form, concrete integers `#guard`ed compiled — no kernel `decide`):

    metric              generated   peephole (R1+E1)   hand (FieldDeltaRangeEmit)
    constraints              374            364                     35
    trace width              280            272                     33
    nonlinear mult           308            298                     30

(CORRECTION: the hand tooth pays 30 nonlinear multiplications, NOT 0 — one `b·(b−1)` per booleanity
gate; see `PeepholeParityMeasurement.hand_multiplications_30`. The earlier `0` here was wrong.)

R1+E1 recovers the 2 transition/recompose zero-tests: −10 constraints, −8 columns, −10 mults. The
residual 94%+ is the 30 booleanity disjunctions (60 load-bearing zero-tests + 30 `∨` + 29 `∧`).
Reaching hand-parity needs a SEPARATE booleanity-pattern rule R2 — recognize an asserted
`(x=c0) ∨ (x=c1)` and lower it to the single quadratic gate `(x-c0)·(x-c1)=0` — which is beyond R1's
zero-test elision and out of this module's scope.

## Resolution / named wall — what is and is NOT proven here

PROVEN (below): the peephole target's exact resources in closed form (`residual_resources`,
`peephole_totals`), reusing `descriptor_exact_resources`; the concrete pilot / residual / peephole
integers (`#guard`, compiled Bool `==`, no kernel reduction — resource-safe like the pilot).

NAMED WALL (NOT attempted here; no `sorry`, no fake contract): the machine-checked
`PassiveDescriptorOptimization.SatisfiabilityPreservation` of the in-place `P_rw` (whose
`SecurityRefinement` must rebuild the ENTIRE elided postorder witness region — the asserted atoms'
`out`/`inv` AND the collapsed `and`-spine outputs — as canonical values, design §5) composed with the
proven E1 pass via `preservation_comp`. The design sizes this at ~days (`P_rw` legs) + ~1.5–2 weeks
(E1 composition, kill-set + `compactE1Ok` certificate). This module delivers the cost/measurement leg
only; it does not instantiate the equisatisfiability contract.

Standalone and additive: imports the pilot + the typed front end, changes nothing in either.
-/
import Dregg2.Crypto.Arith.FieldDeltaRangePilot

namespace Dregg2.Circuit.PeepholeZeroTestElision

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2
open Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2 (witnessCount gate)
open Dregg2.Crypto.Arith.FieldDeltaRangePilot (transitionTerm recomposeTerm prog)

set_option autoImplicit false

/-- Local alias for the optimizer `Formula` type. A bare `Formula` is ambiguous here (a `_root_`
`Formula` is also in scope through the imports), which would silently elaborate to `sorry`. -/
abbrev PFormula (n : Nat) := Dregg2.Metatheory.DirectLogicOptimizerCertificate.Formula n

/-! ## 1. The residual booleanity remainder — the part R1 CANNOT touch.

`residualSource` is the non-asserted remainder of the pilot's `source`: the 30 booleanity
disjunctions conjoined. Its atoms sit under `∨`, so every zero-test here is load-bearing. -/

/-- Right-nested conjunction with no trailing `.top` node: exactly `#components − 1` `.and` nodes. -/
def andAllF {n : Nat} : List (PFormula n) → PFormula n
  | [] => .top
  | [p] => p
  | p :: q :: rest => .and p (andAllF (q :: rest))
termination_by l => l.length

/-- The `j`-th booleanity disjunction `(b_j=0) ∨ (b_j=1)` over a fresh 60-atom registry
(atoms `2j`, `2j+1`), matching the pilot's `boolAtom` shape exactly. -/
def boolAtom60 (j : Fin 30) : PFormula 60 :=
  .or (.atom ⟨2 * j.val, by have := j.isLt; omega⟩)
      (.atom ⟨2 * j.val + 1, by have := j.isLt; omega⟩)

/-- `⋀_{j<30} (b_j=0 ∨ b_j=1)` — the residual the peephole leaves compiled unchanged. -/
def residualSource : PFormula 60 := andAllF ((List.finRange 30).map boolAtom60)

/-- The residual as a live `Program`: 3 public + 30 secret inputs, 60 disjunction-leaf atoms.
Atom terms are cost-irrelevant here (`graphCost`/`witnessCount` read only the formula shape); the
two ASSERTED atom terms live in the direct gates of §2, not in this registry. -/
def residualProgram : Program 3 30 60 :=
  { atomTerms := fun _ => .const 0
  , source := residualSource }

/-- The residual descriptor's resources, in the compiler's PROVEN closed form. -/
theorem residual_resources :
    (descriptor residualProgram).piCount = 3 ∧
    (descriptor residualProgram).traceWidth = 60 + (3 + 30) + witnessCount residualSource ∧
    (descriptor residualProgram).constraints.length
      = 3 + 60 + residualSource.graphCost.equations + 1 :=
  ⟨(descriptor_exact_resources residualProgram).1,
   (descriptor_exact_resources residualProgram).2.1,
   (descriptor_exact_resources residualProgram).2.2.1⟩

/-! ## 2. The peephole target descriptor: residual + the two direct assertion gates.

R1 replaces `atom0`'s (`transition`) and `atom1`'s (`recompose`) atomLink+zeroTest with a single
degree-1 gate `affineTermₐ = 0` each. Post-E1 the freed residual/`out`/`inv`/`and`-output columns are
gone, so the target's trace geometry is exactly the residual's (`residualProgram`), plus these two
linear gates over the raw-input columns. -/

/-- `transition = 0`, asserted directly — the collapsed `atom0` zero-test. -/
def transitionGate : VmConstraint2 := gate (transitionTerm.toWindowAt (rawBase 60))

/-- `recompose = 0`, asserted directly — the collapsed `atom1` zero-test. -/
def recomposeGate : VmConstraint2 := gate (recomposeTerm.toWindowAt (rawBase 60))

/-- The peephole-optimized (R1 then E1) descriptor for the pilot's field-delta conjunction. -/
def peepholeDescriptor : EffectVmDescriptor2 :=
  { descriptor residualProgram with
    constraints := transitionGate :: recomposeGate :: (descriptor residualProgram).constraints }

/-- The peephole totals in closed form: same trace geometry as the residual, plus the two direct
degree-1 assertion gates (no new column, no multiplication). -/
theorem peephole_totals :
    peepholeDescriptor.traceWidth = (descriptor residualProgram).traceWidth ∧
    peepholeDescriptor.constraints.length
      = (descriptor residualProgram).constraints.length + 2 := by
  refine ⟨rfl, ?_⟩
  simp [peepholeDescriptor]

/-! ## 3. THE MEASUREMENT — generated vs peephole vs hand, concrete integers.

Compiled `#guard` (Bool `==`), never a kernel `decide` — resource-safe, matching the pilot's own
measurement style. -/

-- Baseline: the generated pilot descriptor (the ~10.7× re-derivation regression).
#guard prog.source.graphCost.equations == 308
#guard prog.source.graphCost.multiplications == 308
#guard witnessCount prog.source == 185

-- Residual remainder (the 30 booleanity disjunctions R1 leaves alone).
#guard residualSource.graphCost.equations == 298
#guard residualSource.graphCost.multiplications == 298
#guard witnessCount residualSource == 179

-- The peephole target.
#guard peepholeDescriptor.constraints.length == 364     -- generated 374, hand 35
#guard peepholeDescriptor.traceWidth == 272             -- generated 280, hand 33
#guard (descriptor residualProgram).constraints.length == 362

-- Recovered by R1+E1: exactly the two transition/recompose zero-tests.
--   constraints 374 → 364   (−10)
--   trace width 280 → 272   (−8: 2 residual cols + 2 out + 2 inv + 2 and-spine outputs)
--   nonlinear mult 308 → 298 (−10)
#eval peepholeDescriptor.constraints.length   -- 364
#eval peepholeDescriptor.traceWidth           -- 272
#eval residualSource.graphCost.multiplications -- 298 (peephole mult; direct gates are linear)

/-! ## 4. Cost non-increase, and the exact residual named.

The peephole constraint count and trace width, in PROVEN closed form, are strictly below the
generated descriptor's — the recovered terms are precisely the two asserted-frontier zero-tests. The
`≤` here is the design's cost-non-increase leg; the concrete gap (−10 / −8 / −10) is the honest,
partial recovery, with the residual (the 30 load-bearing booleanity disjunctions) named. -/
theorem peephole_constraints_form :
    peepholeDescriptor.constraints.length
      = 3 + 60 + residualSource.graphCost.equations + 1 + 2 := by
  rw [peephole_totals.2, residual_resources.2.2]

theorem peephole_traceWidth_form :
    peepholeDescriptor.traceWidth = 60 + (3 + 30) + witnessCount residualSource := by
  rw [peephole_totals.1, residual_resources.2.1]

#assert_all_clean [
  residual_resources,
  peephole_totals,
  peephole_constraints_form,
  peephole_traceWidth_form
]

end Dregg2.Circuit.PeepholeZeroTestElision
