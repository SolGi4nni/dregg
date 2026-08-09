/-
# `Dregg2.Circuit.ChalSchwartzZippel` — the CHALLENGE-GATE Schwartz–Zippel frame, and a citation
made TRUE.

## Why this file exists

`DescriptorIR2.lean` §2.6 has cited `ChalSchwartzZippel.chalGate_forces_polynomial` since the
challenge leaf landed (2026-08-05), and `git grep` found exactly one occurrence — the citation.
The theorem was PHANTOM: the docblock promised that a challenge gate's acceptance at a random draw
forces a polynomial identity with a named exceptional set, and nothing in the tree said it about a
`ChalConstraint`. `OodQuotientConsistency` had the keystone
(`nonexceptional_eval_zero_forces_zero`) but no bridge from the IR's own gate form to a polynomial.

This file is that bridge, and it is stated on the FAITHFUL carrier:

* `residual env z i body` — **the residual polynomial of a challenge body in its `i`-th
  challenge**, over an arbitrary commutative ring `K`, with every OTHER challenge index held at its
  drawn value. Evaluating it at `z i` IS the faithful denotation `ChalExpr.evalIn`
  (`residual_eval`), which is what the deployed `assert_zero_ext` checks.
* `chalDeg i body` — the body's degree in challenge `i`, syntactically. This is **the concrete
  Schwartz–Zippel numerator** the §2.6 docblock names: `residual` has `natDegree ≤ chalDeg`
  (`residual_natDegree_le`), so the exceptional set has at most `chalDeg` elements
  (`chalGate_exceptional_card_le`).
* `chalGate_forces_polynomial` — **the citation, real**: a `ChalConstraint` that HOLDS in `K`
  (`ChalConstraint.holdsIn`, the faithful denotation) at a NON-exceptional challenge forces its
  residual to be the ZERO polynomial. The probability that a uniform draw lands in the exceptional
  set — `≤ chalDeg / |K|` — is the one thing a Schwartz–Zippel argument never discharges, and it is
  carried here exactly as `OodQuotientConsistency` carries it: the set is NAMED and bounded, the
  draw is not modeled.

## ⚠ Carrier discipline (the identity-carrier lesson)

Everything here consumes `ChalExpr.evalIn` / `ChalConstraint.holdsIn` — the K-valued denotations —
NOT the base-lane `eval`/`holdsAt`. A theorem on the base lane would quietly inherit a `2^31`
challenge space where the deployed draw is from the `2^124` quartic extension. The deployed check
is `ExtensionBuilder::assert_zero_ext` on `BinomialExtensionField<BabyBear, 4>`; `holdsIn` is its
Lean-side denotation, and `Dregg2.Circuit.Emit.PastaSzMul` welds the two at its emitted gates.

## Axiom hygiene

`#assert_axioms`-clean; no `sorry`/`admit`/`native_decide`. Facts are NAMED THEOREMS.
-/
import Dregg2.Circuit.OodQuotientConsistency

namespace Dregg2.Circuit.ChalSchwartzZippel

open Polynomial
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.OodQuotientConsistency (exceptionalSet exceptionalSet_card_le
  nonexceptional_eval_zero_forces_zero)

set_option autoImplicit false

/-! ## §1 — the challenge degree: the CONCRETE NUMERATOR. -/

/-- **The degree of a challenge body in challenge `i`**, read off the syntax. `.chal i` is degree
one, every other leaf (including OTHER challenges, which the residual holds at their drawn values)
is degree zero. This is the numerator of the Schwartz–Zippel bound `chalDeg / |K|`. -/
def chalDeg (i : Nat) : ChalExpr → Nat
  | .chal j  => if j = i then 1 else 0
  | .loc _ | .nxt _ | .const _ => 0
  | .add a b => max (chalDeg i a) (chalDeg i b)
  | .mul a b => chalDeg i a + chalDeg i b

/-! ## §2 — the residual polynomial of a challenge body. -/

/-- **The residual of a challenge body in its `i`-th challenge**, over a commutative ring `K`: the
row's cells are cast into `K`, challenge `i` becomes the INDETERMINATE, and every other challenge
is held at its drawn value `z j`. Evaluating at `z i` recovers the faithful denotation
(`residual_eval`), so "the gate accepts" is "this polynomial vanishes at the draw". -/
noncomputable def residual {K : Type*} [CommRing K] (env : VmRowEnv) (z : Nat → K) (i : Nat) :
    ChalExpr → Polynomial K
  | .loc c   => C ((env.loc c : ℤ) : K)
  | .nxt c   => C ((env.nxt c : ℤ) : K)
  | .const k => C ((k : ℤ) : K)
  | .chal j  => if j = i then X else C (z j)
  | .add a b => residual env z i a + residual env z i b
  | .mul a b => residual env z i a * residual env z i b

/-- **The residual evaluated AT the draw is the faithful denotation.** This is the weld between the
polynomial the Schwartz–Zippel argument runs on and the value `assert_zero_ext` checks; without it
the theorem below would be about a different object than the gate. -/
theorem residual_eval {K : Type*} [CommRing K] (env : VmRowEnv) (z : Nat → K) (i : Nat) :
    ∀ e : ChalExpr, (residual env z i e).eval (z i) = e.evalIn env z
  | .loc c   => by simp [residual, ChalExpr.evalIn]
  | .nxt c   => by simp [residual, ChalExpr.evalIn]
  | .const k => by simp [residual, ChalExpr.evalIn]
  | .chal j  => by
      by_cases h : j = i
      · subst h; simp [residual, ChalExpr.evalIn]
      · simp [residual, ChalExpr.evalIn, h]
  | .add a b => by
      simp [residual, ChalExpr.evalIn, residual_eval env z i a, residual_eval env z i b]
  | .mul a b => by
      simp [residual, ChalExpr.evalIn, residual_eval env z i a, residual_eval env z i b]

/-- **The residual's degree is bounded by the syntactic challenge degree** — so `chalDeg` really is
the numerator, not a narrative about it. -/
theorem residual_natDegree_le {K : Type*} [CommRing K] (env : VmRowEnv) (z : Nat → K) (i : Nat) :
    ∀ e : ChalExpr, (residual env z i e).natDegree ≤ chalDeg i e
  | .loc c   => by simp [residual, chalDeg]
  | .nxt c   => by simp [residual, chalDeg]
  | .const k => by simp [residual, chalDeg]
  | .chal j  => by
      by_cases h : j = i
      · subst h; simpa [residual, chalDeg] using natDegree_X_le (R := K)
      · simp [residual, chalDeg, h]
  | .add a b =>
      le_trans (natDegree_add_le _ _)
        (by
          simpa [chalDeg] using
            max_le_max (residual_natDegree_le env z i a) (residual_natDegree_le env z i b))
  | .mul a b =>
      le_trans (natDegree_mul_le)
        (by
          simpa [chalDeg] using
            add_le_add (residual_natDegree_le env z i a) (residual_natDegree_le env z i b))

/-! ## §3 — the theorem the docblock cited. -/

/-- ⚑ **`chalGate_forces_polynomial` — a challenge gate that HOLDS at a non-exceptional draw forces
its residual to be the ZERO polynomial.**

Hypotheses, and where each comes from in deployment:

* `hIn` — the gate's FAITHFUL denotation (`ChalConstraint.holdsIn`): the body vanishes in `K` at
  the drawn challenges. This is what `ExtensionBuilder::assert_zero_ext` checks.
* `hfire` — the gate actually fires on this row: either it is an every-row gate
  (`onTransition = false`) or the row is not the last. A transition gate on the wrap row claims
  nothing, and pretending otherwise would be stating something the descriptor does not force.
* `hnonexc` — the draw is outside the residual's root set. Fiat–Shamir supplies this except with
  probability `≤ chalDeg / |K|` (`chalGate_exceptional_card_le`); the draw itself is a property of
  the deployed transcript (`observe_main` precedes `sample_perm_challenges`) and is NOT modeled
  here, by design. -/
theorem chalGate_forces_polynomial {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K]
    (env : VmRowEnv) (z : Nat → K) (i : Nat) (isLast : Bool) (w : ChalConstraint)
    (hIn : w.holdsIn env z isLast)
    (hfire : w.onTransition = false ∨ isLast = false)
    (hnonexc : z i ∉ exceptionalSet (residual env z i w.body)) :
    residual env z i w.body = 0 := by
  have hval : w.body.evalIn env z = 0 := by
    unfold ChalConstraint.holdsIn at hIn
    rcases hfire with hoff | hlast
    · rwa [hoff, if_neg (by simp)] at hIn
    · by_cases ht : w.onTransition
      · rw [if_pos ht] at hIn; exact hIn hlast
      · rwa [if_neg ht] at hIn
  exact nonexceptional_eval_zero_forces_zero _ (z i)
    (by rw [residual_eval]; exact hval) hnonexc

/-- **…and the exceptional set is SMALL: at most `chalDeg` points.** The cardinality over `|K|` is
the Schwartz–Zippel error; at the deployed `BinomialExtensionField<BabyBear, 4>` the denominator is
`2013265921⁴ ≈ 2^123.63` (named at `PastaSzMul.SZ_DENOMINATOR`, with the ε ledger beside it). -/
theorem chalGate_exceptional_card_le {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K]
    (env : VmRowEnv) (z : Nat → K) (i : Nat) (w : ChalConstraint) :
    (exceptionalSet (residual env z i w.body)).card ≤ chalDeg i w.body :=
  le_trans (exceptionalSet_card_le _) (residual_natDegree_le env z i w.body)

/-! ## §4 — TEETH: both truth-values load-bearing, on the demo gate's shape.

The two-limb comparison `(a₀ + z·a₁) − (b₀ + z·b₁)` from `DescriptorIR2.demoChal`, over ℤ (an
integral domain, so the same theorem instance runs; the deployed `K` is the quartic extension). -/

/-- The demo body: `(loc 0 + chal 0 · loc 1) − (loc 2 + chal 0 · loc 3)`. -/
private def demoBody : ChalExpr :=
  .add (.add (.loc 0) (.mul (.chal 0) (.loc 1)))
       (.mul (.const (-1)) (.add (.loc 2) (.mul (.chal 0) (.loc 3))))

/-- An honest row (`a = b = (3, 5)`) and a FORGED row (`a = (3, 5)`, `b = (4, 5)`). -/
private def envHonest : VmRowEnv :=
  { loc := fun c => if c = 0 then 3 else if c = 1 then 5 else if c = 2 then 3 else
      if c = 3 then 5 else 0
  , nxt := fun _ => 0, pub := fun _ => 0 }

private def envForged : VmRowEnv :=
  { envHonest with loc := fun c => if c = 0 then 3 else if c = 1 then 5 else if c = 2 then 4 else
      if c = 3 then 5 else 0 }

/-- **FIRE**: on the honest row the gate holds at the draw `7`, the draw is non-exceptional (the
residual is the zero polynomial, whose root set is EMPTY), and the theorem returns the polynomial
identity. -/
theorem chalGate_forces_polynomial_fires :
    residual (K := ℤ) envHonest (fun _ => 7) 0 demoBody = 0 := by
  apply chalGate_forces_polynomial envHonest (fun _ => 7) 0 false ⟨demoBody, false⟩
  · show demoBody.evalIn envHonest (fun _ => 7) = 0
    simp [demoBody, ChalExpr.evalIn, envHonest]
  · left; rfl
  · simp [exceptionalSet, residual, demoBody, envHonest]

/-- ⚑ **BITE, both shapes.** A low-limb forgery (`b = (4, 5)`) has residual `(3−4) + z·(5−5) = −1`,
which never vanishes — the gate REFUSES at EVERY draw (`chalGate_refuses_forged_low_limb`). A
high-limb forgery (`b = (3, 6)`) has residual `z·(5−6) = −z`, whose one root `z = 0` is the
exceptional point: at the draw `0` the gate ACCEPTS a false claim while the residual is NOT the
zero polynomial (`chalGate_exceptional_escape`) — so `hnonexc` is genuinely load-bearing, exactly
as in `OodQuotientConsistency.ood_exceptional_escape`. -/
private def envForgedHigh : VmRowEnv :=
  { envHonest with loc := fun c => if c = 0 then 3 else if c = 1 then 5 else if c = 2 then 3 else
      if c = 3 then 6 else 0 }

theorem chalGate_refuses_forged_low_limb :
    demoBody.evalIn (K := ℤ) envForged (fun _ => 7) ≠ 0 := by
  simp [demoBody, ChalExpr.evalIn, envForged, envHonest]

theorem chalGate_exceptional_escape :
    demoBody.evalIn (K := ℤ) envForgedHigh (fun _ => 0) = 0
      ∧ residual (K := ℤ) envForgedHigh (fun _ => 0) 0 demoBody ≠ 0 := by
  constructor
  · simp [demoBody, ChalExpr.evalIn, envForgedHigh, envHonest]
  · intro h
    have := congrArg (Polynomial.eval (1 : ℤ)) h
    simp [demoBody, residual, envForgedHigh, envHonest] at this

/-! ## §5 — axiom hygiene. -/

#assert_axioms residual_eval
#assert_axioms residual_natDegree_le
#assert_axioms chalGate_forces_polynomial
#assert_axioms chalGate_exceptional_card_le
#assert_axioms chalGate_forces_polynomial_fires
#assert_axioms chalGate_refuses_forged_low_limb
#assert_axioms chalGate_exceptional_escape

end Dregg2.Circuit.ChalSchwartzZippel
