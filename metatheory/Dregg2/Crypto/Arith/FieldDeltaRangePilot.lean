/-
# Dregg2.Crypto.Arith.FieldDeltaRangePilot — the scalar-mul re-derivation PILOT.

STATE THE SUBSTRATE OUT LOUD: this is Lean-authored AIR. The descriptor here is emitted by the
Lean function `TypedLinearPredicateDescriptorIR2.descriptor` (via `#arithmetizeTypedPredicate`);
no Rust hand-writes any constraint, and the resource numbers below are read off the compiler's
PROVEN closed form `descriptor_exact_resources`.

## Why this file exists

The arithmetizer's typed-predicate fragment could not express ANY of the 52 hand-maintained
descriptors, most often blocked by ONE missing thing: `AffineTerm` had no scalar multiplication, so
a coefficient like `2^29` was unrepresentable except as 2^29 `.add` nodes. This week `AffineTerm`
gained `| scale (k : Int) (t)` with `evalField (.scale k t) = k * evalField t`.

This module is the FIRST descriptor re-derived through the fragment using that constructor: the
`field-delta-result-range` tooth (hand-written in `Circuit/Emit/FieldDeltaRangeEmit.lean` as 33
columns / 35 constraints). Its spec:

    new = old + delta (mod p);   30 booleanity bits b_j;   new = Σ_j 2^j b_j

is expressed as a typed-predicate `Program 3 30 62`:

* public inputs `old,delta,new` (columns 0,1,2); secret bits `b_0..b_29` (columns 3..32);
* affine atom 0  = `new - old - delta`            (the modular transition, zero-tested);
* affine atom 1  = `new - Σ_j 2^j b_j`            (the recomposition — USES `.scale (2^j)`);
* affine atoms `2+2j` = `b_j`, `3+2j` = `b_j - 1` (the two booleanity residuals);
* source formula = `atom0 ∧ atom1 ∧ ⋀_j (b_j=0 ∨ b_j=1)`.

## What this MEASURES — the deliverable

The point is the RE-DERIVATION COST, read from the compiler's proven closed form:

    traceWidth        = atoms + (pub+sec) + witnessCount source
    constraints.length = pub + atoms + source.graphCost.equations + 1

Every affine equality in the hand emit is a single degree-≤2 gate; in the fragment it is forced
through a zeroTest atom (3 constraints + 2 witness columns) plus the Boolean-graph plumbing. That
gap is EXACTLY the ~8.5×/~10.7× blow-up the survey predicted, and it is the baseline the peephole
optimizer will later improve. See `pilot_resources` (proven) and the `#guard`ed integers below.

Standalone and additive: imports the fragment, changes nothing in it.
-/
import Dregg2.Crypto.Arith.ArithmetizeTypedPredicate

namespace Dregg2.Crypto.Arith.FieldDeltaRangePilot

open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2)
open Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2
open Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2 (witnessCount)
open Dregg2.Crypto.Arith.TypedPredicate

set_option autoImplicit false

/-! ## 1. Column addressing for the 33 typed inputs (3 public + 30 secret bits). -/

def oldC : Fin 33 := ⟨0, by omega⟩
def deltaC : Fin 33 := ⟨1, by omega⟩
def newC : Fin 33 := ⟨2, by omega⟩
def bitC (j : Fin 30) : Fin 33 := ⟨3 + j.val, by have := j.isLt; omega⟩

/-! ## 2. The affine atom registry (62 atoms over 33 inputs). -/

/-- `new - (old + delta)` — the modular transition residual. -/
def transitionTerm : AffineTerm 33 :=
  .add (.input newC) (.neg (.add (.input oldC) (.input deltaC)))

/-- `Σ_{j<30} 2^j · b_j` — the weighted bit recomposition. THIS is what `.scale` unblocks:
each `2^j` coefficient is a single `scale` node, not `2^j` copies of `.add`. -/
def recomposeSum : AffineTerm 33 :=
  (List.finRange 30).foldr
    (fun j acc => .add (.scale ((2 : Int) ^ j.val) (.input (bitC j))) acc) (.const 0)

/-- `new - Σ_j 2^j b_j` — the recomposition residual. -/
def recomposeTerm : AffineTerm 33 := .add (.input newC) (.neg recomposeSum)

/-- The full 62-atom registry: transition, recompose, then per-bit `b_j`/`b_j-1`. -/
def atomList : List (AffineTerm 33) :=
  [transitionTerm, recomposeTerm] ++
    (List.finRange 30).flatMap
      (fun j => [.input (bitC j), AffineTerm.eqConst (bitC j) 1])

def atomTerms : Fin 62 → AffineTerm 33 := fun a => atomList.getD a.val (.const 0)

/-! ## 3. The source formula: transition ∧ recompose ∧ ⋀_j (b_j=0 ∨ b_j=1). -/

/-- Booleanity of bit `j` as a disjunction of the two zero-test atoms. -/
def boolAtom (j : Fin 30) : Formula 62 :=
  .or (.atom ⟨2 + 2 * j.val, by have := j.isLt; omega⟩)
      (.atom ⟨3 + 2 * j.val, by have := j.isLt; omega⟩)

/-- Right-nested conjunction with no trailing `.top` node (so the witness/equation
count is exactly `#components - 1` `.and` nodes). -/
def andAll : List (Formula 62) → Formula 62
  | [] => .top
  | [p] => p
  | p :: q :: rest => .and p (andAll (q :: rest))
termination_by l => l.length

def source : Formula 62 :=
  andAll (([.atom ⟨0, by omega⟩, .atom ⟨1, by omega⟩] : List (Formula 62)) ++
    (List.finRange 30).map boolAtom)

def prog : Program 3 30 62 := { atomTerms := atomTerms, source := source }

/-! ## 4. Compile it through the arithmetizer — the LIVE descriptor + kernel-checked bundle. -/

#arithmetizeTypedPredicate fieldDeltaRange := prog

#check (fieldDeltaRange_descriptor : EffectVmDescriptor2)
#check (fieldDeltaRange_sound : LiveRefines fieldDeltaRange_program)
#check (fieldDeltaRange_resources : LiveResources fieldDeltaRange_program)
#check (fieldDeltaRange_low_degree : LiveLowDegree fieldDeltaRange_program)

/-! ## 5. THE MEASUREMENT — generated vs hand-written (`FieldDeltaRangeEmit`: 33 cols / 35 eqns).

The closed form is PROVEN by `descriptor_exact_resources`; the concrete integers are read off the
compiled descriptor. -/

/-- The generated descriptor's resources, in the compiler's PROVEN closed form. -/
theorem pilot_resources :
    (descriptor prog).piCount = 3 ∧
    (descriptor prog).traceWidth = 62 + (3 + 30) + witnessCount prog.source ∧
    (descriptor prog).constraints.length = 3 + 62 + prog.source.graphCost.equations + 1 :=
  ⟨(descriptor_exact_resources prog).1,
   (descriptor_exact_resources prog).2.1,
   (descriptor_exact_resources prog).2.2.1⟩

-- Concrete generated numbers (compiled `==`, no kernel `decide`).
-- traceWidth = 62 atoms + 33 inputs + 185 boolean/inverse witnesses = 280.
#guard fieldDeltaRange_descriptor.piCount == 3
#guard fieldDeltaRange_descriptor.traceWidth == 280
#guard fieldDeltaRange_descriptor.constraints.length == 374
#guard witnessCount prog.source == 185
#guard prog.source.graphCost.equations == 308

-- The closed-form components, displayed.
#eval fieldDeltaRange_descriptor.traceWidth          -- 280   (hand: 33)
#eval fieldDeltaRange_descriptor.constraints.length  -- 374   (hand: 35)
#eval witnessCount prog.source                       -- 185
#eval prog.source.graphCost.equations                -- 308

/-! Every generated refinement theorem, and the resource theorem, is kernel-clean. -/
#assert_all_clean [
  pilot_resources,
  fieldDeltaRange_sound,
  fieldDeltaRange_canonical_iff,
  fieldDeltaRange_resources,
  fieldDeltaRange_low_degree,
  fieldDeltaRange_json_exact
]

end Dregg2.Crypto.Arith.FieldDeltaRangePilot
