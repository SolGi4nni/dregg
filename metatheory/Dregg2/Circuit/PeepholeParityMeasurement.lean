/-
# Dregg2.Circuit.PeepholeParityMeasurement — the campaign's headline number.

STATE THE SUBSTRATE OUT LOUD: this is Lean-authored AIR. Every descriptor compared below is a real
`EffectVmDescriptor2` — either emitted by the Lean arithmetizer
(`TypedLinearPredicateDescriptorIR2.descriptor`) or hand-authored in Lean
(`Circuit/Emit/FieldDeltaRangeEmit.lean`). No Rust hand-writes a constraint, and no cost is
asserted: the constraint/width forms come from the PROVEN closed form `descriptor_exact_resources`,
and the multiplication counts are computed by ONE syntactic metric (§1) applied to BOTH sides.

## The question

Does automatic re-derivation through the typed-predicate fragment, plus the peephole passes,
REGRESS the chip relative to the hand-written `field-delta-result-range` tooth? The pilot
(`Crypto/Arith/FieldDeltaRangePilot.lean`) measured the un-optimized answer: ~10.7x. R1
(`Circuit/PeepholeZeroTestElision.lean`) recovers the two asserted-frontier zero-tests and
correctly identifies WHAT still costs: the 30 booleanity disjunctions. This module composes R1 with
the booleanity rule R2 on top of the already-certified E1 dead-column deletion and measures the end
result against the hand tooth.

## THE NUMBER

    metric                generated    post-R1    post-R1+R2      HAND
    constraints                374        364            35        35
    trace width                280        272            33        33
    nonlinear mults            308        298            30        30
    ---------------------------------------------------------------------
    constraints vs HAND     10.69x     10.40x        1.000x         1x
    width vs HAND            8.48x      8.24x        1.000x         1x
    mults vs HAND           10.27x      9.93x        1.000x         1x

HAND-PARITY IS REACHED, EXACTLY, ON ALL THREE METRICS: 35 constraints, 33 columns, 30 nonlinear
multiplications. Automatic re-derivation through the fragment plus R1+R2+E1 does NOT regress the
`field-delta-result-range` chip. `hand_parity_reached` states it as a theorem over the two real
descriptors; §4 pins every integer with a compiled `#guard`.

The multiplication number for the hand tooth is 30, NOT 0: it pays one nonlinear multiplication per
`booleanGates` entry (`b * (b-1)`). Its transition and recomposition gates are linear — constant
scaling only — which `nlTotal ... == 0` pins. (The R1 lane's summary table records the hand
multiplication count as 0; that entry is wrong, and the correction is recorded here rather than by
editing a sibling lane's file.)

## Where the last constraint went — the one honest subtlety

The typed front end ALWAYS emits the accepting equation `output = 1` (`acceptConstraintAt`). Once
R1 and R2 collapse the entire source, the root formula is `top`, whose output wire is the literal
`1`, so that equation is emitted as `1 - 1 = 0`: a degree-0 body (`accept_gate_is_vacuous`) that
vanishes in every row environment. The compiler skeleton therefore still carries it, and the
parametric family of §3 — which is pure compiler output — lands on 36, one ABOVE hand.

R2's landed pass drops it, and drops it with a proof rather than by fiat: `accept_top_constant_true`
shows the body evaluates to 0 in EVERY `VmRowEnv`, so deleting it changes the satisfying set in
neither direction — no witness rebuild, no side condition. `lowered_constraints_account` records the
drop explicitly (`length + 1 = skeleton + 32`). That single justified elision is the whole of the
gap between the 36 this module's compiler-faithful family reports and the 35 the landed
`loweredDescriptor` reports. Both numbers appear below; neither is rounded away.

## What is MEASURED and what is NOT proven

MEASURED (this module): resources of real `EffectVmDescriptor2` values — constraint count and trace
width in the compiler's proven closed form (`residual_resources`, `peephole_constraints`,
`peephole_traceWidth`), and nonlinear multiplications by the §1 metric, which is cross-checked on
the generated descriptor against the PROVEN ledger `emittedMultiplications` (itself proven equal to
`graphCost.multiplications`), so the number carried across to the hand tooth is the number the
closed form talks about.

NOT PROVEN, AND NOT CLAIMED — read this before quoting the number. THERE IS NO PASS FUNCTION. No
`optimize : EffectVmDescriptor2 → EffectVmDescriptor2` was written and run on the pilot descriptor.
`loweredDescriptor`, `peepholeAt m` and `PeepholeZeroTestElision.peepholeDescriptor` are all
CONSTRUCTED objects that model what the rules would emit. What is real on the recognition side is
R2's `recognizes` predicate, `#guard`ed to fire on all 30 of the pilot's live booleanity atom pairs
(exhaustive for this descriptor); what is real on the semantic side is R2's per-gate legs. So the
honest reading of "35 / 33 / 30" is: THE OPTIMIZED SHAPE IS AT HAND-PARITY, not "the optimizer
achieved hand-parity". Making it a run pass is the next piece of work, not a formality.

Second wall — UPDATED (this prose was stale). Both rewrites are now certified passes with a
machine-checked `PassiveDescriptorOptimization.SatisfiabilityPreservation` on the EMITTED descriptor,
each at ONE fired site:

* R1 — `Circuit/PeepholePassCertified.lean` (`rwDescriptor` record-update; `rw_preservation`,
  composed with E1 via `peephole_preservation`), and
* R2 — `Circuit/PeepholeR2Certified.lean` (`rwR2Descriptor` record-update; `rwR2_security` rebuilds
  the elided disjunction witness canonically, `rwR2_completeness`, `rwR2_preservation`, composed with
  E1 via `peepholeR2_preservation`). `pairGate_iff_or` is exactly the local leg its security proof
  consumes.

What remains open is NOT the per-site preservation but ITERATION: the pilot's `loweredDescriptor`
here is still a HAND-BUILT model of the 32-fold fired result (2 R1 sites + 30 R2 sites), and folding
all 32 record-updates onto the single pilot descriptor — whose constraint list stops being of the
form `descriptor p'` after the first fire — is the named residual both certified modules carry. So
the 35/33/30 measured below is on the hand model; the certified R2 object's resources are measured,
and proven to match the emitted source minus the site's `−9` constraints, in
`PeepholeR2Certified.rwR2_constraints_recovery`.

R2 landed mid-lane. `PeepholeBooleanityRule.lean` was being written concurrently and was NOT
importable when §1-§3 of this module were authored; it became importable and green before §5, so §5
measures the REAL landed `loweredDescriptor` rather than a model of it. §3's parametric family
`peepholeAt m` — the post-E1 descriptor in which `m` of the 30 booleanity components survive and
`30 - m` have been lowered — is kept, for two reasons that outlive R2's arrival: `peepholeAt 30`
`#guard`s equal to the R1 lane's independently authored `peepholeDescriptor` (364 / 272 / 298),
anchoring the numbers to an object this lane did not write; and `peepholeAt 0` is the pure
compiler-skeleton R1+R2 point (36), which is what localizes the last constraint to the accepting
equation.

Standalone and additive: imports R1, R2, the pilot and the hand emit; changes nothing in any of them.
-/
import Dregg2.Circuit.PeepholeZeroTestElision
import Dregg2.Circuit.PeepholeBooleanityRule
import Dregg2.Circuit.Emit.FieldDeltaRangeEmit

namespace Dregg2.Circuit.PeepholeParityMeasurement

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2
open Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2
  (witnessCount gate bitBody exprDegree)
open Dregg2.Crypto.Arith.FieldDeltaRangePilot
  (transitionTerm recomposeTerm bitC prog fieldDeltaRange_descriptor)
open Dregg2.Circuit.PeepholeZeroTestElision (andAllF)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option autoImplicit false

/-- Local alias for the optimizer `Formula`. A bare `Formula` is ambiguous under these opens
(`TypedLinearPredicateDescriptorIR2` re-exports one), and an ambiguous elaboration is how a `sorry`
sneaks in silently. -/
abbrev PF (n : Nat) := Dregg2.Metatheory.DirectLogicOptimizerCertificate.Formula n

/-! ## 1. ONE nonlinear-multiplication metric, applied to BOTH sides.

The generated descriptors carry `WindowExpr` bodies; the hand tooth carries `EmittedExpr` bodies.
To compare them honestly the SAME notion is defined over both languages: a `mul` node is a NONLINEAR
multiplication exactly when BOTH operands have total degree at least 1. Constant scaling
(`.mul (.const k) x`, which is how `AffineTerm.neg` / `AffineTerm.scale` and the hand emit's `esub`
both lower) is linear and does not count — the convention the optimizer ledger
`Node.multiplications` documents for itself.

This metric is not asserted to agree with that ledger; §4a `#guard`s that it does, on the real
generated descriptor. -/

/-- Total degree of an `EmittedExpr` — the mirror of `exprDegree` for the hand emit's language. -/
def emitDegree : EmittedExpr → Nat
  | .var _ => 1
  | .const _ => 0
  | .add x y => max (emitDegree x) (emitDegree y)
  | .mul x y => emitDegree x + emitDegree y

/-- Nonlinear multiplications in a window-gate body. -/
def nlWindow : WindowExpr → Nat
  | .loc _ | .nxt _ | .const _ => 0
  | .add x y => nlWindow x + nlWindow y
  | .mul x y =>
      nlWindow x + nlWindow y + (if 0 < exprDegree x ∧ 0 < exprDegree y then 1 else 0)

/-- Nonlinear multiplications in a hand-emitted gate body. -/
def nlEmitted : EmittedExpr → Nat
  | .var _ | .const _ => 0
  | .add x y => nlEmitted x + nlEmitted y
  | .mul x y =>
      nlEmitted x + nlEmitted y + (if 0 < emitDegree x ∧ 0 < emitDegree y then 1 else 0)

/-- Nonlinear multiplications carried by one constraint. Exhaustive over `VmConstraint2` by
construction: the forms with no polynomial body (PI pins, continuity transitions, lookups,
memory / map / umem ops, proof binds) carry no multiplication and contribute 0. -/
def nlConstraint : VmConstraint2 → Nat
  | .windowGate w => nlWindow w.body
  | .base (.gate body) => nlEmitted body
  | .base (.boundary _ body) => nlEmitted body
  | .base (.transition _ _) => 0
  | .base (.piBinding _ _ _) => 0
  | .lookup _ => 0
  | .memOp _ => 0
  | .mapOp _ => 0
  | .umemOp _ => 0
  | .proofBind _ => 0

/-- Nonlinear multiplications in a whole constraint list. -/
def nlTotal (cs : List VmConstraint2) : Nat := (cs.map nlConstraint).sum

theorem nlTotal_append (a b : List VmConstraint2) :
    nlTotal (a ++ b) = nlTotal a + nlTotal b := by
  simp [nlTotal, List.sum_append]

theorem nlTotal_map_const {α : Type} (l : List α) (f : α → VmConstraint2)
    (h : ∀ a ∈ l, nlConstraint (f a) = 1) : nlTotal (l.map f) = l.length := by
  induction l with
  | nil => simp [nlTotal]
  | cons a l ih =>
      have ha : nlConstraint (f a) = 1 := h a (by simp)
      have hrec : nlTotal (l.map f) = l.length := ih (fun b hb => h b (by simp [hb]))
      simp only [nlTotal, List.map_cons, List.sum_cons, List.length_cons] at hrec ⊢
      omega

/-- Every affine atom term lowers to a LINEAR window expression: `AffineTerm` has no product of two
non-constants, so `toWindowAt` can only build `mul` nodes with a literal-constant operand. Hence the
atom-link equations and R1's two direct assertion gates cost no multiplication. -/
theorem nlWindow_toWindowAt {m : Nat} (base : Nat) (t : AffineTerm m) :
    nlWindow (t.toWindowAt base) = 0 := by
  induction t with
  | const k => simp [AffineTerm.toWindowAt, nlWindow]
  | input i => simp [AffineTerm.toWindowAt, nlWindow]
  | neg x ih => simp [AffineTerm.toWindowAt, nlWindow, exprDegree, ih]
  | add x y ihx ihy => simp [AffineTerm.toWindowAt, nlWindow, ihx, ihy]
  | scale k x ih => simp [AffineTerm.toWindowAt, nlWindow, exprDegree, ih]

/-! ## 2. The post-E1 residual family: `m` surviving booleanity components.

R2 recognizes an ASSERTED `(x = c0) ∨ (x = c1)` on the conjunction frontier and lowers it to the
single quadratic gate `(x - c0) * (x - c1) = 0`, freeing both atom-residual columns, both zero-test
`out`/`inv` witness pairs, the `or` output and the `and` spine node — all of which the
already-certified E1 dead-column deletion then removes. All 30 of the pilot's booleanity components
have exactly this shape with `c0 = 0`, `c1 = 1` (atoms `b_j` and `b_j - 1`), and all 30 sit on the
frontier of the right-nested `andAll`, so R2 fires on every one of them.

The family below is the post-E1 geometry with `m` components left un-lowered: an atom registry of
`2m` residuals over the SAME 3 public + 30 secret inputs. Modelling the post-E1 descriptor as a
smaller compiled program is exactly the R1 lane's methodology, reused unchanged. -/

/-- The atom registry that survives when only the first `m` booleanity components remain:
`b_0, b_0 - 1, ..., b_{m-1}, b_{m-1} - 1`. These are the pilot's own atom terms, not placeholders. -/
def residualAtomList (m : Nat) : List (AffineTerm 33) :=
  ((List.finRange 30).take m).flatMap
    (fun j => [.input (bitC j), AffineTerm.eqConst (bitC j) 1])

def residualAtomTerms (m : Nat) : Fin (2 * m) → AffineTerm 33 :=
  fun a => (residualAtomList m).getD a.val (.const 0)

/-- The `j`-th surviving booleanity disjunction over the `2m`-atom registry. -/
def boolAtomAt (m : Nat) (j : Fin m) : PF (2 * m) :=
  .or (.atom ⟨2 * j.val, by have := j.isLt; omega⟩)
      (.atom ⟨2 * j.val + 1, by have := j.isLt; omega⟩)

/-- `⋀_{j<m} (b_j = 0 ∨ b_j = 1)` — what the peephole leaves compiled. `m = 0` gives `top`. -/
def residualAt (m : Nat) : PF (2 * m) := andAllF ((List.finRange m).map (boolAtomAt m))

def residualProgramAt (m : Nat) : Program 3 30 (2 * m) :=
  { atomTerms := residualAtomTerms m, source := residualAt m }

/-- Resources of the surviving residual, in the compiler's PROVEN closed form. -/
theorem residual_resources (m : Nat) :
    (descriptor (residualProgramAt m)).piCount = 3 ∧
    (descriptor (residualProgramAt m)).traceWidth
      = 2 * m + (3 + 30) + witnessCount (residualAt m) ∧
    (descriptor (residualProgramAt m)).constraints.length
      = 3 + 2 * m + (residualAt m).graphCost.equations + 1 :=
  ⟨(descriptor_exact_resources (residualProgramAt m)).1,
   (descriptor_exact_resources (residualProgramAt m)).2.1,
   (descriptor_exact_resources (residualProgramAt m)).2.2.1⟩

/-! ## 3. The composed peephole target `R1 ∘ R2 ∘ E1`. -/

/-- R1's two direct assertion gates: the modular transition and the recomposition, asserted at
degree 1 over the raw input columns (which start at `rawBase (2m)` once E1 has deleted the freed
atom-residual and witness columns). -/
def r1Gates (m : Nat) : List VmConstraint2 :=
  [ gate (transitionTerm.toWindowAt (rawBase (2 * m)))
  , gate (recomposeTerm.toWindowAt (rawBase (2 * m))) ]

/-- R2's lowered booleanity gates: one `b_j * (b_j - 1) = 0` per collapsed component, over the bit's
raw input column. This is the same body the hand tooth's `booleanGates` emits. -/
def r2Gates (m : Nat) : List VmConstraint2 :=
  ((List.finRange 30).drop m).map
    (fun j => gate (bitBody (.col (rawBase (2 * m) + 3 + j.val))))

/-- The composed target: R1's two linear gates, R2's `30 - m` quadratic gates, and the compiled
remainder — over the post-E1 trace. -/
def peepholeAt (m : Nat) : EffectVmDescriptor2 :=
  { descriptor (residualProgramAt m) with
    constraints := r1Gates m ++ r2Gates m ++ (descriptor (residualProgramAt m)).constraints }

theorem peephole_traceWidth (m : Nat) :
    (peepholeAt m).traceWidth = 2 * m + (3 + 30) + witnessCount (residualAt m) :=
  (residual_resources m).2.1

theorem peephole_constraints (m : Nat) :
    (peepholeAt m).constraints.length
      = (3 + 2 * m + (residualAt m).graphCost.equations + 1) + 2 + (30 - m) := by
  have hc : (peepholeAt m).constraints
      = r1Gates m ++ r2Gates m ++ (descriptor (residualProgramAt m)).constraints := rfl
  have h1 : (r1Gates m).length = 2 := rfl
  have h2 : (r2Gates m).length = 30 - m := by simp [r2Gates]
  rw [hc, List.length_append, List.length_append, h1, h2, (residual_resources m).2.2]
  omega

/-- The composed target's nonlinear multiplications: the surviving residual's, plus exactly one per
lowered booleanity gate. R1's two direct gates are linear (`nlWindow_toWindowAt`). -/
theorem peephole_multiplications (m : Nat) :
    nlTotal (peepholeAt m).constraints
      = nlTotal (descriptor (residualProgramAt m)).constraints + (30 - m) := by
  have hc : (peepholeAt m).constraints
      = r1Gates m ++ r2Gates m ++ (descriptor (residualProgramAt m)).constraints := rfl
  have h1 : nlTotal (r1Gates m) = 0 := by
    simp [nlTotal, r1Gates, nlConstraint, gate, nlWindow_toWindowAt]
  have h2 : nlTotal (r2Gates m) = 30 - m := by
    have hmap := nlTotal_map_const ((List.finRange 30).drop m)
      (fun j : Fin 30 => gate (bitBody (.col (rawBase (2 * m) + 3 + j.val))))
      (by
        intro j _
        simp [nlConstraint, gate, bitBody,
          Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.Wire.expr, nlWindow, exprDegree])
    simpa [r2Gates] using hmap
  rw [hc, nlTotal_append, nlTotal_append, h1, h2]
  omega

/-- The collapsed root's accepting equation is degree 0: `output = 1` where the output wire of `top`
is the literal `1`, i.e. `1 - 1 = 0`, which vanishes identically on every trace. This is the whole
of the residual 1-constraint gap against the hand tooth. -/
theorem accept_gate_is_vacuous (base : Nat) :
    exprDegree
      (Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.subW
        (Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.outputAt base
          (Dregg2.Metatheory.DirectLogicOptimizerCertificate.Formula.top (n := 0))).expr
        (.const 1)) = 0 := rfl

/-! ## 4. THE MEASUREMENT — concrete integers on real descriptors.

Compiled `#guard` (Bool `==`) throughout, never a kernel `decide`: resource-safe, matching the
pilot's and the R1 lane's measurement style. -/

/-! ### 4a. The metric is validated against the PROVEN ledger.

`nlTotal` is a syntactic count over the emitted constraint list; `emittedMultiplications` is the
optimizer ledger, proven equal to `graphCost.multiplications` by
`emittedMultiplications_eq_graphCost`. They agree on the real generated descriptor. -/
#guard nlTotal fieldDeltaRange_descriptor.constraints == 308
#guard nlTotal fieldDeltaRange_descriptor.constraints
        == Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2.emittedMultiplications prog.source
#guard prog.source.graphCost.multiplications == 308

/-! ### 4b. Stage 0 — GENERATED baseline (the un-optimized re-derivation). -/
#guard fieldDeltaRange_descriptor.constraints.length == 374
#guard fieldDeltaRange_descriptor.traceWidth == 280

/-! ### 4c. Stage 1 — post-R1 (+E1). Cross-checked against the R1 lane's own descriptor: the
parametric family at `m = 30` reproduces `PeepholeZeroTestElision.peepholeDescriptor` exactly. -/
#guard Dregg2.Circuit.PeepholeZeroTestElision.peepholeDescriptor.constraints.length == 364
#guard Dregg2.Circuit.PeepholeZeroTestElision.peepholeDescriptor.traceWidth == 272
#guard nlTotal
    Dregg2.Circuit.PeepholeZeroTestElision.peepholeDescriptor.constraints == 298

#guard (peepholeAt 30).constraints.length == 364
#guard (peepholeAt 30).traceWidth == 272
#guard nlTotal (peepholeAt 30).constraints == 298

/-! ### 4d. Stage 2 — post-R1+R2 (+E1): every booleanity component lowered.

Two numbers, both honest, and they differ by exactly one:

* `peepholeAt 0` is PURE COMPILER SKELETON — the front end still emits the collapsed root's
  accepting equation `1 - 1 = 0`, so it lands on 36;
* `PeepholeBooleanityRule.loweredDescriptor` is R2's REAL landed pass, which drops that one gate
  under `accept_top_constant_true` (proven to vanish in every row environment), landing on 35.

The last constraint is the only difference between them, and it is a vacuous one. -/
#guard (peepholeAt 0).constraints.length == 36
#guard (peepholeAt 0).traceWidth == 33
#guard nlTotal (peepholeAt 0).constraints == 30

#guard Dregg2.Circuit.PeepholeBooleanityRule.loweredDescriptor.constraints.length == 35
#guard Dregg2.Circuit.PeepholeBooleanityRule.loweredDescriptor.traceWidth == 33
#guard Dregg2.Circuit.PeepholeBooleanityRule.loweredDescriptor.piCount == 3
#guard nlTotal Dregg2.Circuit.PeepholeBooleanityRule.loweredDescriptor.constraints == 30
#guard (peepholeAt 0).constraints.length
        == Dregg2.Circuit.PeepholeBooleanityRule.loweredDescriptor.constraints.length + 1

-- R2 WITHOUT R1, from the sibling lane: the two asserted equalities keep their zero-tests.
#guard Dregg2.Circuit.PeepholeBooleanityRule.r2OnlyDescriptor.constraints.length == 44
#guard Dregg2.Circuit.PeepholeBooleanityRule.r2OnlyDescriptor.traceWidth == 40

/-! ### 4e. HAND — `FieldDeltaRangeEmit.fieldDeltaRangeDescriptor`, the deployed tooth.

The hand tooth pays 30 nonlinear multiplications, NOT 0: its 30 `booleanGates` are each
`b * (b - 1)`. Its `transitionGate` and `recomposeGate` are linear (constant scaling only). -/
#guard Dregg2.Circuit.Emit.FieldDeltaRangeEmit.fieldDeltaRangeDescriptor.constraints.length == 35
#guard Dregg2.Circuit.Emit.FieldDeltaRangeEmit.fieldDeltaRangeDescriptor.traceWidth == 33
#guard nlTotal
    Dregg2.Circuit.Emit.FieldDeltaRangeEmit.fieldDeltaRangeDescriptor.constraints == 30
#guard nlTotal Dregg2.Circuit.Emit.FieldDeltaRangeEmit.booleanGates == 30
#guard nlTotal
    [Dregg2.Circuit.Emit.FieldDeltaRangeEmit.transitionGate,
     Dregg2.Circuit.Emit.FieldDeltaRangeEmit.recomposeGate] == 0

/-! ### 4f. Parity against the hand tooth, as integers. -/
#guard Dregg2.Circuit.PeepholeBooleanityRule.loweredDescriptor.constraints.length
        == Dregg2.Circuit.Emit.FieldDeltaRangeEmit.fieldDeltaRangeDescriptor.constraints.length
#guard Dregg2.Circuit.PeepholeBooleanityRule.loweredDescriptor.traceWidth
        == Dregg2.Circuit.Emit.FieldDeltaRangeEmit.fieldDeltaRangeDescriptor.traceWidth
#guard nlTotal Dregg2.Circuit.PeepholeBooleanityRule.loweredDescriptor.constraints
        == nlTotal Dregg2.Circuit.Emit.FieldDeltaRangeEmit.fieldDeltaRangeDescriptor.constraints

-- The one skeleton constraint R2 elides, located: with everything lowered the compiled remainder is
-- 3 PI pins plus the vacuous accept gate, carrying no witness column, no equation, no multiplication.
#guard (descriptor (residualProgramAt 0)).constraints.length == 4
#guard witnessCount (residualAt 0) == 0
#guard (residualAt 0).graphCost.equations == 0
#guard (residualAt 0).graphCost.multiplications == 0
#guard nlTotal (descriptor (residualProgramAt 0)).constraints == 0

/-! ### 4g. The table, displayed.

    metric              generated   post-R1   post-R1+R2   HAND
    constraints               374       364           35     35
    trace width               280       272           33     33
    nonlinear mults           308       298           30     30
-/
#eval (fieldDeltaRange_descriptor.constraints.length,
       (peepholeAt 30).constraints.length,
       Dregg2.Circuit.PeepholeBooleanityRule.loweredDescriptor.constraints.length,
       Dregg2.Circuit.Emit.FieldDeltaRangeEmit.fieldDeltaRangeDescriptor.constraints.length)
#eval (fieldDeltaRange_descriptor.traceWidth,
       (peepholeAt 30).traceWidth,
       Dregg2.Circuit.PeepholeBooleanityRule.loweredDescriptor.traceWidth,
       Dregg2.Circuit.Emit.FieldDeltaRangeEmit.fieldDeltaRangeDescriptor.traceWidth)
#eval (nlTotal fieldDeltaRange_descriptor.constraints,
       nlTotal (peepholeAt 30).constraints,
       nlTotal Dregg2.Circuit.PeepholeBooleanityRule.loweredDescriptor.constraints,
       nlTotal Dregg2.Circuit.Emit.FieldDeltaRangeEmit.fieldDeltaRangeDescriptor.constraints)

/-! ## 5. HAND-PARITY, as a theorem over the two real descriptors.

The `#guard`s above are compiled evaluations of the actual objects. This section proves the same
three equalities, so the headline does not rest on evaluation alone. Every proof goes through a
closed form or a structural list lemma — no kernel `decide`, no `native_decide`, no enumeration of
30-element lists in the kernel. -/

/-- The two lanes wrote the same metric independently. `PeepholeBooleanityRule.nonlinearMuls` (R2's)
and `nlWindow` (this module's) are the SAME function on the nose, so R2's multiplication accounting
and this module's are one measurement, not two that happen to agree numerically. -/
theorem nlWindow_eq_nonlinearMuls (w : WindowExpr) :
    nlWindow w = Dregg2.Circuit.PeepholeBooleanityRule.nonlinearMuls w := by
  induction w with
  | loc c => rfl
  | nxt c => rfl
  | const k => rfl
  | add x y ihx ihy =>
      simp only [nlWindow, Dregg2.Circuit.PeepholeBooleanityRule.nonlinearMuls, ihx, ihy]
  | mul x y ihx ihy =>
      simp only [nlWindow, Dregg2.Circuit.PeepholeBooleanityRule.nonlinearMuls, ihx, ihy]
      split <;> split <;> omega

theorem nlTotal_nil : nlTotal [] = 0 := rfl

theorem nlTotal_cons (c : VmConstraint2) (l : List VmConstraint2) :
    nlTotal (c :: l) = nlConstraint c + nlTotal l := by
  simp [nlTotal]

theorem nlTotal_map_zero {α : Type} (l : List α) (f : α → VmConstraint2)
    (h : ∀ a ∈ l, nlConstraint (f a) = 0) : nlTotal (l.map f) = 0 := by
  induction l with
  | nil => simp [nlTotal]
  | cons a l ih =>
      have ha : nlConstraint (f a) = 0 := h a (by simp)
      have hrec : nlTotal (l.map f) = 0 := ih (fun b hb => h b (by simp [hb]))
      simp only [nlTotal, List.map_cons, List.sum_cons] at hrec ⊢
      omega

/-! ### 5a. The landed R1+R2 descriptor: 35 / 33 / 30. -/

theorem lowered_traceWidth_33 :
    Dregg2.Circuit.PeepholeBooleanityRule.loweredDescriptor.traceWidth = 33 := by
  rw [Dregg2.Circuit.PeepholeBooleanityRule.lowered_traceWidth_form]
  rfl

theorem lowered_constraints_35 :
    Dregg2.Circuit.PeepholeBooleanityRule.loweredDescriptor.constraints.length = 35 := by
  have hacc := Dregg2.Circuit.PeepholeBooleanityRule.lowered_constraints_account
  have hskel := Dregg2.Circuit.PeepholeBooleanityRule.lowered_skeleton_constraints
  have hzero :
      Dregg2.Circuit.PeepholeBooleanityRule.loweredProgram.source.graphCost.equations = 0 := rfl
  rw [hzero] at hskel
  omega

theorem lowered_multiplications_30 :
    nlTotal Dregg2.Circuit.PeepholeBooleanityRule.loweredDescriptor.constraints = 30 := by
  have hc : Dregg2.Circuit.PeepholeBooleanityRule.loweredDescriptor.constraints
      = publicPins 3 30 0 ++
        [Dregg2.Circuit.PeepholeBooleanityRule.loweredTransitionGate,
         Dregg2.Circuit.PeepholeBooleanityRule.loweredRecomposeGate] ++
        Dregg2.Circuit.PeepholeBooleanityRule.loweredBoolGates := rfl
  have hpins : nlTotal (publicPins 3 30 0) = 0 := by
    refine nlTotal_map_zero _ _ ?_
    intro i _
    rfl
  have hr1 : nlTotal
      [Dregg2.Circuit.PeepholeBooleanityRule.loweredTransitionGate,
       Dregg2.Circuit.PeepholeBooleanityRule.loweredRecomposeGate] = 0 := by
    simp [nlTotal, nlConstraint, gate,
      Dregg2.Circuit.PeepholeBooleanityRule.loweredTransitionGate,
      Dregg2.Circuit.PeepholeBooleanityRule.loweredRecomposeGate, nlWindow_toWindowAt]
  have hbool : nlTotal Dregg2.Circuit.PeepholeBooleanityRule.loweredBoolGates = 30 := by
    have hmap := nlTotal_map_const (List.finRange 30)
      Dregg2.Circuit.PeepholeBooleanityRule.loweredBoolGate
      (by
        intro j _
        simp [nlConstraint, gate, Dregg2.Circuit.PeepholeBooleanityRule.loweredBoolGate,
          Dregg2.Circuit.PeepholeBooleanityRule.pairGate,
          Dregg2.Circuit.PeepholeBooleanityRule.pairBody,
          nlWindow, exprDegree, AffineTerm.toWindowAt])
    simpa [Dregg2.Circuit.PeepholeBooleanityRule.loweredBoolGates] using hmap
  rw [hc, nlTotal_append, nlTotal_append, hpins, hr1, hbool]

/-! ### 5b. The hand tooth: 35 / 33 / 30. Its multiplications are 30, not 0. -/

theorem hand_traceWidth_33 :
    Dregg2.Circuit.Emit.FieldDeltaRangeEmit.fieldDeltaRangeDescriptor.traceWidth = 33 := rfl

theorem hand_constraints_35 :
    Dregg2.Circuit.Emit.FieldDeltaRangeEmit.fieldDeltaRangeDescriptor.constraints.length = 35 := by
  simp [Dregg2.Circuit.Emit.FieldDeltaRangeEmit.fieldDeltaRangeDescriptor,
    Dregg2.Circuit.Emit.FieldDeltaRangeEmit.fieldDeltaRangeConstraints,
    Dregg2.Circuit.Emit.FieldDeltaRangeEmit.booleanGates,
    Dregg2.Circuit.Emit.FieldDeltaRangeEmit.piPins,
    Dregg2.Circuit.Emit.FieldDeltaRangeEmit.RESULT_BITS]

/-- The hand recomposition gate folds 30 constant scalings onto one accumulator: every `mul` it
builds has a literal-constant factor, so it costs no nonlinear multiplication. -/
theorem nlEmitted_recompose_fold :
    ∀ (l : List Nat) (e0 : EmittedExpr),
      nlEmitted (l.foldl (fun acc j =>
        Dregg2.Circuit.Emit.FieldDeltaRangeEmit.esub acc
          (.mul (.const ((2 : Int) ^ j))
            (.var (Dregg2.Circuit.Emit.FieldDeltaRangeEmit.bitCol j)))) e0)
        = nlEmitted e0 := by
  intro l
  induction l with
  | nil => intro e0; simp
  | cons x xs ih =>
      intro e0
      rw [List.foldl_cons, ih]
      simp [Dregg2.Circuit.Emit.FieldDeltaRangeEmit.esub, nlEmitted, emitDegree]

theorem nlEmitted_recomposeBody :
    nlEmitted Dregg2.Circuit.Emit.FieldDeltaRangeEmit.recomposeBody = 0 := by
  have h := nlEmitted_recompose_fold
    (List.range Dregg2.Circuit.Emit.FieldDeltaRangeEmit.RESULT_BITS)
    (.var Dregg2.Circuit.Emit.FieldDeltaRangeEmit.NEW_COL)
  simpa [Dregg2.Circuit.Emit.FieldDeltaRangeEmit.recomposeBody, nlEmitted] using h

theorem hand_multiplications_30 :
    nlTotal Dregg2.Circuit.Emit.FieldDeltaRangeEmit.fieldDeltaRangeDescriptor.constraints = 30 := by
  have hbool : nlTotal Dregg2.Circuit.Emit.FieldDeltaRangeEmit.booleanGates = 30 := by
    have hmap := nlTotal_map_const (List.range 30)
      (fun j => Dregg2.Circuit.Emit.FieldDeltaRangeEmit.gate
        (Dregg2.Circuit.Emit.FieldDeltaRangeEmit.boolBody j))
      (by
        intro j _
        simp [nlConstraint, Dregg2.Circuit.Emit.FieldDeltaRangeEmit.gate,
          Dregg2.Circuit.Emit.FieldDeltaRangeEmit.boolBody,
          Dregg2.Circuit.Emit.FieldDeltaRangeEmit.esub, nlEmitted, emitDegree])
    simpa [Dregg2.Circuit.Emit.FieldDeltaRangeEmit.booleanGates,
      Dregg2.Circuit.Emit.FieldDeltaRangeEmit.RESULT_BITS] using hmap
  have htrans : nlConstraint Dregg2.Circuit.Emit.FieldDeltaRangeEmit.transitionGate = 0 := by
    simp [nlConstraint, Dregg2.Circuit.Emit.FieldDeltaRangeEmit.transitionGate,
      Dregg2.Circuit.Emit.FieldDeltaRangeEmit.gate,
      Dregg2.Circuit.Emit.FieldDeltaRangeEmit.esub, nlEmitted, emitDegree]
  have hrec : nlConstraint Dregg2.Circuit.Emit.FieldDeltaRangeEmit.recomposeGate = 0 := by
    simp [nlConstraint, Dregg2.Circuit.Emit.FieldDeltaRangeEmit.recomposeGate,
      Dregg2.Circuit.Emit.FieldDeltaRangeEmit.gate, nlEmitted_recomposeBody]
  have hpins : nlTotal Dregg2.Circuit.Emit.FieldDeltaRangeEmit.piPins = 0 := by
    simp [nlTotal, Dregg2.Circuit.Emit.FieldDeltaRangeEmit.piPins, nlConstraint]
  show nlTotal Dregg2.Circuit.Emit.FieldDeltaRangeEmit.fieldDeltaRangeConstraints = 30
  simp only [Dregg2.Circuit.Emit.FieldDeltaRangeEmit.fieldDeltaRangeConstraints,
    nlTotal_append, nlTotal_cons, nlTotal_nil, hbool, htrans, hrec, hpins]

/-! ### 5c. THE HEADLINE. -/

/-- The three-metric parity relation between an optimizer output and the hand-written tooth. -/
structure HandParity (d : EffectVmDescriptor2) : Prop where
  constraints :
    d.constraints.length
      = Dregg2.Circuit.Emit.FieldDeltaRangeEmit.fieldDeltaRangeDescriptor.constraints.length
  traceWidth :
    d.traceWidth = Dregg2.Circuit.Emit.FieldDeltaRangeEmit.fieldDeltaRangeDescriptor.traceWidth
  multiplications :
    nlTotal d.constraints
      = nlTotal Dregg2.Circuit.Emit.FieldDeltaRangeEmit.fieldDeltaRangeDescriptor.constraints
  piCount : d.piCount = 3

/-- HAND-PARITY REACHED. The automatically re-derived, R1+R2+E1-optimized descriptor matches the
hand-written `field-delta-result-range` tooth on all three metrics: 35 constraints, 33 columns, 30
nonlinear multiplications. Automatic re-derivation does not regress this chip.

This is a RESOURCE statement about two real descriptors. It is not a claim that the optimized
descriptor accepts the same assignments as the hand tooth, and not a claim that R1 or R2 is a
certified pass — see the module header for what is and is not proven. -/
theorem hand_parity_reached :
    HandParity Dregg2.Circuit.PeepholeBooleanityRule.loweredDescriptor :=
  ⟨by rw [lowered_constraints_35, hand_constraints_35],
   by rw [lowered_traceWidth_33, hand_traceWidth_33],
   by rw [lowered_multiplications_30, hand_multiplications_30],
   rfl⟩

#assert_all_clean [
  nlTotal_append,
  nlTotal_cons,
  nlTotal_map_const,
  nlTotal_map_zero,
  nlWindow_toWindowAt,
  nlWindow_eq_nonlinearMuls,
  residual_resources,
  peephole_traceWidth,
  peephole_constraints,
  peephole_multiplications,
  accept_gate_is_vacuous,
  lowered_traceWidth_33,
  lowered_constraints_35,
  lowered_multiplications_30,
  hand_traceWidth_33,
  hand_constraints_35,
  nlEmitted_recompose_fold,
  nlEmitted_recomposeBody,
  hand_multiplications_30,
  hand_parity_reached
]

end Dregg2.Circuit.PeepholeParityMeasurement
