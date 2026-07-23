/-
# Dregg2.Circuit.PeepholeBooleanityRule — BUILD RULE R2, the booleanity collapse.

STATE THE SUBSTRATE OUT LOUD: this is Lean-authored AIR. The rewrite, its gate, its semantics and
its cost all live in Lean; the resource forms are read off the compiler's PROVEN closed form
`TypedLinearPredicateDescriptorIR2.descriptor_exact_resources`. No Rust hand-writes a constraint and
no cost number here is asserted.

## What R2 is

R1 (`Circuit/PeepholeZeroTestElision.lean`) elides the zero-test of an atom on the ASSERTED-TRUE
conjunction frontier. On `FieldDeltaRangePilot` it recovers only 2 atoms (374 → 364 constraints)
because the pilot's source is

    atom0 ∧ atom1 ∧ ⋀_{j<30} ( b_j = 0  ∨  b_j = 1 )

and the 30 booleanity components are DISJUNCTIONS, where the zero-tests are load-bearing: the bit
feeds the `∨`, and neither disjunct's residual is forced to 0. That remainder is 94%+ of the
re-derivation cost. R2 is the fix.

**R2**: an asserted `∨`-node whose two children are affine zero-tests *on the same term* —
`(x = c₀) ∨ (x = c₁)`, recognized syntactically by peeling the trailing additive constant off each
atom's `AffineTerm` and checking the peeled bases are equal and the shifts differ — lowers to the
SINGLE degree-2 gate

    (x + k₀) · (x + k₁) = 0

over the raw-input columns. In a field this product vanishes iff one factor does (`mul_eq_zero`),
which is exactly the disjunction — see `pairBody_zero_iff` / `loweredBoolGate_iff`, PROVEN below,
not asserted. The rewrite elides, per fired site: BOTH child `zeroTest` nodes (2 × [3 gates, 2
witness columns, 3 multiplications]), the `∨` node (2 gates, 1 witness column, 2 multiplications),
BOTH atom-residual columns and their two `atomLink` equations, and — when every conjunct of the
asserted spine has been lowered — the `∧`-spine nodes and the accepting equation with them.

This is exactly how the hand emit writes booleanity: `FieldDeltaRangeEmit.booleanGates` is 30 gates
of `b_j·(b_j − 1) = 0`. NOTE the hand emit therefore carries 30 NONLINEAR MULTIPLICATIONS, not 0.

## PREDICT, then measure (predictions written before the `#guard`s below were run)

R1+R2 on the pilot: with all 30 disjunctions collapsed by R2 and the 2 asserted equalities collapsed
by R1, NOTHING of the Boolean graph survives — no atom-residual columns, no bit/inverse witnesses,
no `∧`-spine, no accepting equation. Predicted totals:

* constraints `3 (public pins) + 2 (affine) + 30 (booleanity) = 35`;
* trace width `3 + 30 = 33` raw input columns and nothing else;
* nonlinear multiplications `30`, one per booleanity gate.

i.e. EXACT parity with the hand emit (35 / 33 / 30). R2 alone (R1 not applied, so the two asserted
equalities keep their zero-tests and the `∧` node): predicted `44 / 40 / 37`.

MEASURED (`#guard`, compiled `Bool ==`, no kernel `decide` — resource-safe, matching the pilot's own
measurement style):

    rule            constraints   trace width   nonlinear mult
    generated            374          280             308
    R1 only              364          272             298      (PeepholeZeroTestElision.lean)
    R2 only               44           40              38      ← predicted 37, MISSED by 1
    R1 + R2               35           33              30
    hand emit             35           33              30      (FieldDeltaRangeEmit.lean)

Every prediction confirmed except one, recorded rather than quietly corrected: R2-only
multiplications are 38, not the predicted 37. The prediction used `Node.multiplications` for an
`∧` node as 1 (the product `out = l·r`); it is 2, because the node ALSO Booleanizes its own output
with `out·(out−1) = 0`. Under that ledger multiplications equal equations for zeroTest (3/3), `∧`
(2/2) and `∨` (2/2) nodes — though NOT for `¬` (1 mul / 2 equations), which this pilot has none of —
which is why the generated pilot's 308 equations and 308 multiplications coincide. The R1+R2 line is
unaffected: with the graph gone, the only multiplications left are the 30 booleanity products,
exactly as the hand emit carries them, and `nonlinearMuls` here uses the same
both-factors-nonconstant convention as `Node.multiplications`.

MUTATION CANARY (run outside this file, so the green here is not self-certifying): mutating the
second shift `−1 → −2` in `loweredBoolGate_iff` makes the SAME proof script fail with the residual
`b ∈ {0,2} ↔ b ∈ {0,1}` — the theorem genuinely tracks the extracted shift constants and is not a
tautology over them.

The 94% residual R1 could not touch is exactly what R2 removes: −329 constraints, −239 columns,
−268 multiplications relative to R1-only, landing on hand parity.

## Resolution / named walls — what is and is NOT proven here

PROVEN below: R2's recognizer as an executable function on the LIVE pilot registry (`recognizes`,
checked EXHAUSTIVELY over all 30 pilot pairs — 30 of 30, not a sample); the lowered gate's degree
bound (`pairBody_degree`, ≤ 2, so the rule cannot leave the low-degree fragment); the gate's exact
semantics `(x+k₀)(x+k₁)=0 ↔ x+k₀=0 ∨ x+k₁=0` (`pairBody_zero_iff`) and its per-atom-pair form
(`pairGate_iff_or`); the concrete instance "the j-th lowered gate says exactly `b_j ∈ {0,1}`"
(`loweredBoolGate_iff`) — the same proposition `FieldDeltaRangeEmit.binary_of_boolBody` extracts
from the hand gate; that affine terms contribute zero nonlinear multiplications and each lowered
booleanity gate at most one; the lowered descriptor's trace width in the compiler's proven closed
form (`lowered_traceWidth_form`, via `descriptor_exact_resources`) and the full constraint account
(`lowered_constraints_account`); and that the one equation R2's empty-graph case drops — the
accepting equation, which degenerates to `1 − 1 = 0` once the source is `.top` — is CONSTANT-TRUE in
every row environment (`accept_top_constant_true`), so its removal needs no hypothesis.

NAMED WALLS (NOT attempted here; no `sorry`, no stand-in):

1. RESOLVED for one site (was: the machine-checked `SatisfiabilityPreservation` of the in-place
   rewrite). `Circuit/PeepholeR2Certified.lean` now lifts R2 to a certified
   `PassiveDescriptorOptimization` pass on the EMITTED descriptor (`rwR2Descriptor`, a record-update):
   `rwR2_security` rebuilds the elided postorder witness region (both `out`/`inv` pairs canonically
   via `zeroBit`/`zeroInv`, the `∨` output `= 1`, the `∧`-spine output `= 1`) using this module's
   `pairGate_iff_or` as the LOCAL leg, `rwR2_completeness` gives the converse, and `peepholeR2_preservation`
   composes with the certified E1 pass via `preservation_comp`. What is NOT closed is ITERATION: that
   pass fires ONCE at one site, and folding all 32 pilot fires (2 R1 + 30 R2) onto the single pilot
   descriptor — whose constraint list stops matching `descriptor p'` after the first fire — remains
   open, exactly as the R1 module states.
2. The syntactic recognizer's match against the pilot registry is a 30/30 EXHAUSTIVE COMPUTATION for
   THIS pilot, not a ∀-theorem over `Program`s: `atomTerms` indexes a `List.getD`, which does not
   reduce for a symbolic index. A general `atomTerms (2+2j) = .input (bitC j)` indexing lemma is the
   follow-up; every ∀-quantified theorem here is stated over the atom SHAPES directly.
2b. RECOGNIZER COMPLETENESS — `peelConst` is SOUND (`peelConst_evalField`: base + shift = the term at
   every input, proven) but deliberately PARTIAL. It peels a trailing additive constant only when it
   is the immediate RIGHT child of the outermost `.add`. It therefore MISSES, returning shift `0` and
   so failing to pair two semantically-equal residuals whose syntax differs:
   * LEFT-const: `.add (.const k) x` (constant on the left) — the `.add x y` clauses only match a
     constant in `y`, never in `x`;
   * `.scale`-wrapped: `.scale k (.add x (.const c))` — peels to `(itself, 0)`; the rule does not
     distribute `k` across the sum;
   * `.neg`-wrapped: `.neg (.add x (.const c))` — likewise `(itself, 0)`, no sign push-through;
   * DEEP-nested const: `.add x (.add y (.const k))` — falls in the `.add x (.add y z)` clause with
     shift `0`; the trailing constant is not hoisted.
   These are recognizer-COMPLETENESS gaps only (they shrink the set of sites R2 fires on); they cannot
   make R2 UNSOUND, because the certified pass's `hbase` hypothesis is checked on the ACTUAL peeled
   bases. A normalizing `AffineTerm` pre-pass (fold constants to a single trailing `+ k`) is the
   follow-up that widens firing to every affine `(x = c₀) ∨ (x = c₁)`.
2. The syntactic recognizer's match against the pilot registry is a 30/30 EXHAUSTIVE COMPUTATION for
   THIS pilot, not a ∀-theorem over `Program`s: `atomTerms` indexes a `List.getD`, which does not
   reduce for a symbolic index. A general `atomTerms (2+2j) = .input (bitC j)` indexing lemma is the
   follow-up; every ∀-quantified theorem here is stated over the atom SHAPES directly.
3. The lowered gate body is `(x + 0)·(x + (−1))`; the hand body is `b·(b − 1)`. Same degree-2
   polynomial, but the generic rule leaves a `+0` factor a trivial constant-fold pass removes, and
   the two live in different IR types (`WindowExpr` vs `EmittedExpr`). Byte-identity with the hand
   emit is NOT claimed.

Standalone and additive: imports the pilot only, changes nothing in it, and does not depend on the
R1 prototype module.
-/
import Dregg2.Crypto.Arith.FieldDeltaRangePilot

namespace Dregg2.Circuit.PeepholeBooleanityRule

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2
open Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2
  (witnessCount gate subW negW outputAt nodesAt exprDegree fieldWindow fieldAssignment Wire)
open Dregg2.Crypto.Arith.FieldDeltaRangePilot (transitionTerm recomposeTerm bitC atomTerms prog)

set_option autoImplicit false

/-- Local alias for the optimizer `Formula` type. A bare `Formula` is ambiguous here (a `_root_`
`Formula` is also in scope through the imports), which would silently elaborate to `sorry`. -/
abbrev PFormula (n : Nat) := Dregg2.Metatheory.DirectLogicOptimizerCertificate.Formula n

/-! ## 1. The recognizer — peel the trailing additive constant off an affine atom.

`(x = c₀) ∨ (x = c₁)` reaches the arithmetizer as two atoms whose terms are the RESIDUALS
`x − c₀` and `x − c₁`. Recognizing the pattern is therefore: peel each term's trailing
`+ k` constant, and check the two peeled bases are syntactically equal with distinct shifts.
The clauses are written out fully (no overlapping catch-all) so every equation lemma is a clean
constructor match. -/

def peelConst {m : Nat} : AffineTerm m → AffineTerm m × Int
  | .const k => (.const k, 0)
  | .input i => (.input i, 0)
  | .neg x => (.neg x, 0)
  | .scale k x => (.scale k x, 0)
  | .add x (.const k) => (x, k)
  | .add x (.input i) => (.add x (.input i), 0)
  | .add x (.neg y) => (.add x (.neg y), 0)
  | .add x (.add y z) => (.add x (.add y z), 0)
  | .add x (.scale k y) => (.add x (.scale k y), 0)

/-- Peeling is semantics-preserving: base + shift is the original term, at every input. -/
theorem peelConst_evalField {m : Nat} (input : Fin m → BabyBear) (t : AffineTerm m) :
    (peelConst t).1.evalField input + (((peelConst t).2 : Int) : BabyBear)
      = t.evalField input := by
  cases t with
  | const k => simp [peelConst, AffineTerm.evalField]
  | input i => simp [peelConst, AffineTerm.evalField]
  | neg x => simp [peelConst, AffineTerm.evalField]
  | scale k x => simp [peelConst, AffineTerm.evalField]
  | add x y => cases y <;> simp [peelConst, AffineTerm.evalField]

/-- R2 fires on an atom pair when both terms peel to the SAME base with DISTINCT shifts. -/
def recognizes {m : Nat} (t0 t1 : AffineTerm m) : Bool :=
  ((peelConst t0).1 == (peelConst t1).1) && ((peelConst t0).2 != (peelConst t1).2)

/-! ## 2. The lowered gate: one degree-2 constraint, and its exact semantics. -/

/-- R2's replacement gate body `(x + k₀) · (x + k₁)` over the raw-input columns at `rb`. -/
def pairBody {m : Nat} (rb : Nat) (base : AffineTerm m) (k0 k1 : Int) : WindowExpr :=
  .mul (.add (base.toWindowAt rb) (.const k0)) (.add (base.toWindowAt rb) (.const k1))

def pairGate {m : Nat} (rb : Nat) (base : AffineTerm m) (k0 k1 : Int) : VmConstraint2 :=
  gate (pairBody rb base k0 k1)

/-- The lowered gate stays inside the backend's degree-2 fragment. -/
theorem pairBody_degree {m : Nat} (rb : Nat) (base : AffineTerm m) (k0 k1 : Int) :
    exprDegree (pairBody rb base k0 k1) ≤ 2 := by
  have h := AffineTerm.toWindowAt_degree (m := m) rb base
  simp only [pairBody, exprDegree]
  omega

/-- THE RULE'S CORRECTNESS, at the gate: the single quadratic constraint vanishes exactly on the
disjunction of the two affine equalities. `mul_eq_zero` is where the field (BabyBear is prime) is
load-bearing — over a ring with zero divisors R2 would be UNSOUND. -/
theorem pairBody_zero_iff {m : Nat} (env : VmRowEnv) (rb : Nat)
    (base : AffineTerm m) (k0 k1 : Int) :
    fieldWindow env (pairBody rb base k0 k1) = 0 ↔
      (base.evalField (fun i => fieldAssignment env.loc (rb + i.val)) + ((k0 : Int) : BabyBear) = 0 ∨
       base.evalField (fun i => fieldAssignment env.loc (rb + i.val)) + ((k1 : Int) : BabyBear) = 0) := by
  simp only [pairBody, fieldWindow, AffineTerm.fieldWindow_toWindowAt]
  exact mul_eq_zero

/-- The same statement in the form R2 actually consumes: the ONE lowered gate says exactly what the
two elided zero-tests plus the `∨` node said — `t₀ = 0 ∨ t₁ = 0` on the atom pair's own terms. -/
theorem pairGate_iff_or {m : Nat} (env : VmRowEnv) (rb : Nat) (t0 t1 : AffineTerm m)
    (hbase : (peelConst t0).1 = (peelConst t1).1) :
    fieldWindow env (pairBody rb (peelConst t0).1 (peelConst t0).2 (peelConst t1).2) = 0 ↔
      (t0.evalField (fun i => fieldAssignment env.loc (rb + i.val)) = 0 ∨
       t1.evalField (fun i => fieldAssignment env.loc (rb + i.val)) = 0) := by
  have e0 := peelConst_evalField (fun i => fieldAssignment env.loc (rb + i.val)) t0
  have e1 := peelConst_evalField (fun i => fieldAssignment env.loc (rb + i.val)) t1
  rw [pairBody_zero_iff, e0, hbase, e1]

/-! ## 3. Nonlinear-multiplication accounting.

`Node.multiplications` counts a constant scaling as linear; the same convention here, so the
generated / lowered / hand numbers are comparable. -/

def nonlinearMuls : WindowExpr → Nat
  | .loc _ | .nxt _ | .const _ => 0
  | .add x y => nonlinearMuls x + nonlinearMuls y
  | .mul x y => nonlinearMuls x + nonlinearMuls y +
      (if exprDegree x = 0 ∨ exprDegree y = 0 then 0 else 1)

/-- An affine term compiles to ZERO nonlinear multiplications — every `mul` it emits has a constant
factor. This is why the two R1-collapsed gates cost no multiplication. -/
theorem nonlinearMuls_toWindowAt {m : Nat} (rb : Nat) (t : AffineTerm m) :
    nonlinearMuls (t.toWindowAt rb) = 0 := by
  induction t with
  | const k => simp [AffineTerm.toWindowAt, nonlinearMuls]
  | input i => simp [AffineTerm.toWindowAt, nonlinearMuls]
  | neg x ih => simp [AffineTerm.toWindowAt, nonlinearMuls, exprDegree, ih]
  | add x y ihx ihy => simp [AffineTerm.toWindowAt, nonlinearMuls, ihx, ihy]
  | scale k x ih => simp [AffineTerm.toWindowAt, nonlinearMuls, exprDegree, ih]

/-- A lowered booleanity gate costs at most ONE nonlinear multiplication — against the 7 the elided
region cost (3 + 3 for the two zero-tests, 1 for the `∨`). -/
theorem nonlinearMuls_pairBody {m : Nat} (rb : Nat) (base : AffineTerm m) (k0 k1 : Int) :
    nonlinearMuls (pairBody rb base k0 k1) ≤ 1 := by
  have h := nonlinearMuls_toWindowAt (m := m) rb base
  simp only [pairBody, nonlinearMuls, h]
  split <;> omega

/-! ## 4. The recognizer against the LIVE pilot registry.

`atomTerms` indexes a `List.getD`, which does not reduce for a symbolic index, so this leg is a
COMPUTATION over all 30 pairs, not a ∀-theorem — and 30 is every booleanity pair the pilot has, so
the check is exhaustive for this descriptor. -/

def pilotAtom0 (j : Fin 30) : AffineTerm 33 :=
  atomTerms ⟨2 + 2 * j.val, by have := j.isLt; omega⟩

def pilotAtom1 (j : Fin 30) : AffineTerm 33 :=
  atomTerms ⟨3 + 2 * j.val, by have := j.isLt; omega⟩

-- R2's recognizer fires on all 30 of the pilot's booleanity pairs.
#guard (List.finRange 30).all (fun j => recognizes (pilotAtom0 j) (pilotAtom1 j))

-- and extracts exactly the expected base `b_j` with shifts `(0, -1)`.
#guard (List.finRange 30).all (fun j =>
  ((peelConst (pilotAtom0 j)).1 == .input (bitC j)) &&
  ((peelConst (pilotAtom0 j)).2 == 0) &&
  ((peelConst (pilotAtom1 j)).1 == .input (bitC j)) &&
  ((peelConst (pilotAtom1 j)).2 == -1))

-- The pilot's live atom terms ARE the shapes the ∀-theorems below are stated over.
#guard (List.finRange 30).all (fun j =>
  (pilotAtom0 j == .input (bitC j)) &&
  (pilotAtom1 j == AffineTerm.eqConst (bitC j) 1))

/-! ## 5. The R1+R2 lowered descriptor for the pilot.

Every atom-residual column, every bit/inverse witness, the `∨` and `∧` nodes and the accepting
equation are gone; what remains is the 33 raw input columns and 35 direct constraints. Because
`atoms = 0`, `rawBase 0 = 0` puts the raw inputs at columns 0..32 — the hand emit's own layout
(`OLD_COL = 0`, `DELTA_COL = 1`, `NEW_COL = 2`, `bitCol j = 3 + j`). -/

/-- The residual "program": 3 public + 30 secret inputs, ZERO atoms, EMPTY Boolean source. -/
def loweredProgram : Program 3 30 0 :=
  { atomTerms := fun a => a.elim0, source := .top }

/-- `transition = 0`, asserted directly — the R1-collapsed `atom0` zero-test. -/
def loweredTransitionGate : VmConstraint2 := gate (transitionTerm.toWindowAt (rawBase 0))

/-- `recompose = 0`, asserted directly — the R1-collapsed `atom1` zero-test. -/
def loweredRecomposeGate : VmConstraint2 := gate (recomposeTerm.toWindowAt (rawBase 0))

/-- The `j`-th R2 gate: `(b_j + 0)·(b_j + (−1)) = 0`, with base and shifts exactly those the
recognizer extracted from the pilot's live registry in §4. -/
def loweredBoolGate (j : Fin 30) : VmConstraint2 :=
  pairGate (rawBase 0) (.input (bitC j)) 0 (-1)

def loweredBoolGates : List VmConstraint2 := (List.finRange 30).map loweredBoolGate

/-- The R1+R2-optimized descriptor. -/
def loweredDescriptor : EffectVmDescriptor2 :=
  { descriptor loweredProgram with
    constraints := publicPins 3 30 0 ++
      [loweredTransitionGate, loweredRecomposeGate] ++ loweredBoolGates }

/-- The `j`-th lowered gate forces EXACTLY `b_j ∈ {0,1}` — the same proposition
`FieldDeltaRangeEmit.binary_of_boolBody` extracts from the hand-written booleanity gate. -/
theorem loweredBoolGate_iff (env : VmRowEnv) (j : Fin 30) :
    fieldWindow env (pairBody (rawBase 0) (.input (bitC j)) 0 (-1)) = 0 ↔
      (fieldAssignment env.loc (rawBase 0 + (bitC j).val) = 0 ∨
       fieldAssignment env.loc (rawBase 0 + (bitC j).val) = 1) := by
  rw [pairBody_zero_iff]
  simp [AffineTerm.evalField, add_neg_eq_zero]

/-- The two R1-collapsed gates force exactly their affine residuals to vanish. -/
theorem loweredAffineGate_iff {m : Nat} (env : VmRowEnv) (rb : Nat) (t : AffineTerm m) :
    fieldWindow env (t.toWindowAt rb) = 0 ↔
      t.evalField (fun i => fieldAssignment env.loc (rb + i.val)) = 0 := by
  rw [AffineTerm.fieldWindow_toWindowAt]

/-! ## 6. Cost, in the compiler's PROVEN closed form. -/

/-- Trace width, from `descriptor_exact_resources`: no atom column, no witness column. -/
theorem lowered_traceWidth_form :
    loweredDescriptor.traceWidth = 0 + (3 + 30) + witnessCount loweredProgram.source :=
  (descriptor_exact_resources loweredProgram).2.1

/-- The skeleton's constraint count, from `descriptor_exact_resources`. -/
theorem lowered_skeleton_constraints :
    (descriptor loweredProgram).constraints.length
      = 3 + 0 + loweredProgram.source.graphCost.equations + 1 :=
  (descriptor_exact_resources loweredProgram).2.2.1

/-- The ONE equation R2's empty-graph case drops. With the source reduced to `.top` the accepting
equation is `1 − 1 = 0` — constant-true in EVERY row environment, so removing it is
satisfaction-preserving on the nose: no witness rebuild, no hypothesis, no assumption. -/
theorem accept_top_constant_true (env : VmRowEnv) :
    fieldWindow env
      (subW (outputAt (boolBase 3 30 0) loweredProgram.source).expr (.const 1)) = 0 := by
  simp [loweredProgram, outputAt, Wire.expr, subW, negW, fieldWindow]

/-- The full constraint account: the lowered list is the compiler's skeleton (3 public pins + the
accepting equation) with that vacuous accepting equation dropped and the 32 direct gates added. -/
theorem lowered_constraints_account :
    loweredDescriptor.constraints.length + 1
      = (descriptor loweredProgram).constraints.length + 32 := by
  simp [loweredDescriptor, descriptor, publicPins, atomLinks, graphConstraintsAt,
    loweredProgram, loweredBoolGates, nodesAt]

/-! ## 7. R2 WITHOUT R1 — isolating the two rules' contributions.

The 30 disjunctions collapse, but the two asserted equalities keep their zero-tests and the
`∧`-spine node above them survives. -/

def r2OnlyProgram : Program 3 30 2 :=
  { atomTerms := fun a => if a.val = 0 then transitionTerm else recomposeTerm
  , source := .and (.atom ⟨0, by omega⟩) (.atom ⟨1, by omega⟩) }

def r2OnlyBoolGates : List VmConstraint2 :=
  (List.finRange 30).map (fun j => pairGate (rawBase 2) (.input (bitC j)) 0 (-1))

def r2OnlyDescriptor : EffectVmDescriptor2 :=
  { descriptor r2OnlyProgram with
    constraints := (descriptor r2OnlyProgram).constraints ++ r2OnlyBoolGates }

theorem r2Only_traceWidth_form :
    r2OnlyDescriptor.traceWidth = 2 + (3 + 30) + witnessCount r2OnlyProgram.source :=
  (descriptor_exact_resources r2OnlyProgram).2.1

theorem r2Only_constraints_account :
    r2OnlyDescriptor.constraints.length
      = (descriptor r2OnlyProgram).constraints.length + 30 := by
  simp [r2OnlyDescriptor, r2OnlyBoolGates]

/-! ## 8. THE MEASUREMENT. Compiled `#guard` (`Bool ==`), never a kernel `decide`. -/

-- Baseline: the generated pilot descriptor (the ~10.7× re-derivation regression).
#guard prog.source.graphCost.equations == 308
#guard prog.source.graphCost.multiplications == 308
#guard witnessCount prog.source == 185

-- R2 only: 2 surviving zero-tests + the ∧ node.
#guard witnessCount r2OnlyProgram.source == 5
#guard r2OnlyProgram.source.graphCost.equations == 8
#guard r2OnlyProgram.source.graphCost.multiplications == 8
#guard r2OnlyDescriptor.constraints.length == 44
#guard r2OnlyDescriptor.traceWidth == 40

-- R1 + R2: nothing of the Boolean graph survives.
#guard witnessCount loweredProgram.source == 0
#guard loweredProgram.source.graphCost.equations == 0
#guard loweredProgram.source.graphCost.multiplications == 0
#guard (descriptor loweredProgram).constraints.length == 4
#guard loweredDescriptor.constraints.length == 35        -- generated 374, R1-only 364, hand 35
#guard loweredDescriptor.traceWidth == 33                -- generated 280, R1-only 272, hand 33
#guard loweredDescriptor.piCount == 3

-- Nonlinear multiplications: 30, one per booleanity gate; the affine gates cost none.
#guard nonlinearMuls (transitionTerm.toWindowAt (rawBase 0)) == 0
#guard nonlinearMuls (recomposeTerm.toWindowAt (rawBase 0)) == 0
#guard (List.finRange 30).all
  (fun j => nonlinearMuls (pairBody (rawBase 0) (.input (bitC j)) 0 (-1)) == 1)

#eval loweredDescriptor.constraints.length   -- 35  (hand: 35)
#eval loweredDescriptor.traceWidth           -- 33  (hand: 33)
#eval r2OnlyDescriptor.constraints.length    -- 44
#eval r2OnlyDescriptor.traceWidth            -- 40

#assert_all_clean [
  peelConst_evalField,
  pairBody_degree,
  pairBody_zero_iff,
  pairGate_iff_or,
  nonlinearMuls_toWindowAt,
  nonlinearMuls_pairBody,
  loweredBoolGate_iff,
  loweredAffineGate_iff,
  lowered_traceWidth_form,
  lowered_skeleton_constraints,
  accept_top_constant_true,
  lowered_constraints_account,
  r2Only_traceWidth_form,
  r2Only_constraints_account
]

end Dregg2.Circuit.PeepholeBooleanityRule
