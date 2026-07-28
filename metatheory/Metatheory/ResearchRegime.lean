/-
# Metatheory.ResearchRegime — A PUBLISHED VERDICT MAY NOT OUTRANK THE EVIDENCE THAT SETTLED IT.

`Metatheory.Disputation` gives the **witness** regime (a verdict read off a discharging witness,
Byzantine-majority-proof on the certifiable domain) and names the **political/ballot** regime as the
one where a well-behaved adjudicator provably does *not* exist — that non-existence *is* Arrow /
List–Pettit. `Metatheory.OptimisticAdjudication` gives the third regime and prices it.

This module is the **product-facing consequence**: a research platform publishes claims settled in
all three regimes, and the defect worth eliminating is not "wrong facts" — it is **one badge over
three incomparable kinds of confidence.** So a publication carries the regime it was *settled* in and
the regime it is *rendered* as, and the honesty condition `renderedAs ≤ settledIn` is a field, with
theorems saying what each rendering then licenses.

Motivating instance (`docs/DREGGSOLVE.md`): a live platform whose stated invariant is *"a claim is
PENDING until validated by 2 independent Auditors"* renders every such verdict with the same green
VERIFIED badge. Two auditors asserting is an aggregation of assertions — the ballot regime — and §3
exhibits a **unanimous** ballot upholding a claim that a **sound, observed** refutation defeats.

## What is proved here

* **§3 the separations.** The three regimes are pairwise distinct as verdicts, by concrete
  fully-inhabited models, not by appeal:
  - `unanimous_ballot_upholds_a_refuted_claim` — a unanimous ballot, a sound refutation actually
    observed, and the claim genuinely false, all at once. Ballot ⇏ optimistic and ballot ⇏ witness.
  - `witness_does_not_imply_ballot` — a claim that genuinely `Holds` while the ballot rejects it.
    **Truth does not win votes**, so the ballot verdict is not even a lossy proxy for the other two.
  - `settled_witness_imp_optimistic` — the one implication that *does* hold (the free half). So the
    top two are ordered and the bottom one is off the ladder entirely.
* **§4 the publication invariant.** `rendered_witness_is_true` and
  `rendered_optimistic_is_not_refuted`: for an honest publication, the badge means exactly what it
  says. `laundered_publication_can_be_false` shows the honesty field is **not decorative** — drop it
  and a witness-badged publication can carry a refuted claim. (Same discipline as
  `optimistic_unsound_without_actuation`: a floor must be refutable, or it is not doing work.)
* **§5 the challenger obligation, in product vocabulary.** `FundedChallenger` is strictly stronger
  than `CommunityCould`. ⚠ The mathematical content is `OptimisticAdjudication.ChallengerGap`'s —
  this section RENAMES it into the deployment's vocabulary and adds no new mathematics.

## What is NOT claimed

Nothing here says any regime is sound. `optimistic_sound` still carries `RefutationComplete` and
`Actuated` explicitly, and `Actuated` is a synchrony assumption about a deployment that the epistemic
layer cannot even state. This module governs *how a settled verdict may be displayed*; it does not
manufacture settlement. ⚠ And per `OptimisticAdjudication`'s own header: this conceptual
neighbourhood already produced one elegant falsehood (the `Predicate ⊣ Witness` adjudication thesis,
refuted 4/4). Nothing here should be cited as "DreggSolve's verdicts are sound".
-/
import Metatheory.OptimisticAdjudication

namespace Metatheory.ResearchRegime

open Dregg2.Laws Metatheory Metatheory.EpistemicConsensus Metatheory.Disputation
open Metatheory.OptimisticAdjudication

universe u v

/-! # §1. The three regimes, and their strength order -/

/-- **The regime a verdict was settled in.** Not a taxonomy for its own sake: each constructor
corresponds to a theorem about what that verdict licenses (`Disputation.byzantine_majority_cannot_uphold`,
`OptimisticAdjudication.optimistic_sound`, and — for `ballot` — the *absence* of any such theorem). -/
inductive Regime where
  /-- An aggregation of assertions. Arrow / List–Pettit applies; there is no good reflector. -/
  | ballot : Regime
  /-- Upheld unless a refutation is *observed* in the window. Costs `RefutationComplete` + `Actuated`. -/
  | optimistic : Regime
  /-- `∃ w. Discharged` — a realizability fact. Byzantine-majority-proof on the certifiable domain. -/
  | witness : Regime
  deriving DecidableEq, Repr

/-- Strength, as a number, so `renderedAs ≤ settledIn` is a decidable side condition a deployment can
actually check. The order is `ballot < optimistic < witness`; §3 shows it is not merely conventional
in the top two (`settled_witness_imp_optimistic`) and *is* a licensing order rather than an
implication order at the bottom (`witness_does_not_imply_ballot`). -/
def Regime.strength : Regime → Nat
  | .ballot => 0
  | .optimistic => 1
  | .witness => 2

/-! # §2. The ballot regime as an object -/

/-- **A ballot.** Deliberately maximally general: `aggregates` is an *arbitrary* rule over the
assertion profile, so nothing in §3 turns on picking a bad voting scheme. The separations below hold
for a unanimity rule, which is the most favourable case an aggregation can have. -/
structure Ballot (ι : Type v) where
  /-- Which agents assert the claim. -/
  asserts : ι → Prop
  /-- The aggregation rule: does this profile carry the motion? -/
  aggregates : (ι → Prop) → Prop

/-- The ballot's verdict. -/
def Ballot.upholds {ι : Type v} (B : Ballot ι) : Prop := B.aggregates B.asserts

variable {P W R : Type u} [Verifiable P W] [Refutable P W R] {ι : Type v}

/-- **What it means to be settled at a given regime.** One definition, three clauses, each pointing
at the verdict object the corresponding module already built. -/
def SettledAt (X : Claim P) (observed : R → Prop) (B : Ballot ι) : Regime → Prop
  | .ballot => B.upholds
  | .optimistic => optimisticallyUpheld (P := P) (W := W) X observed
  | .witness => upheld (P := P) (W := W) X

/-! # §3. The separations — the regimes are three different things -/

/-- **`settled_witness_imp_optimistic` — the ONE implication that holds.** A witness-settled claim is
optimistically upheld: no sound refutation of a true claim can exist, hence none can be observed.
This is `upheld_optimisticallyUpheld` (the free half — no completeness, no liveness, no synchrony)
lifted to `SettledAt`, and it is what makes `witness` genuinely *above* `optimistic` rather than
merely adjacent to it. -/
theorem settled_witness_imp_optimistic (X : Claim P) (observed : R → Prop) (B : Ballot ι)
    (h : SettledAt (W := W) X observed B Regime.witness) :
    SettledAt (W := W) X observed B Regime.optimistic :=
  upheld_optimisticallyUpheld (W := W) X observed h

/-! ## §3a. Ballot ⇏ anything — a unanimous vote over a refuted claim.

The model: one statement, **no** witnesses (so the claim is genuinely false), one refutation
certificate which is sound, and a window that **does** observe it. The ballot is unanimous and its
rule is unanimity — the most favourable aggregation available. -/
namespace Laundering

/-- Statements: one. -/
abbrev Stmt := Unit

/-- Witnesses: **none** — `Holds` is uninhabited, so the claim is FALSE. -/
abbrev Wit := Empty

/-- Refutation certificates: one, sound (vacuously, `Wit` being empty). -/
abbrev Cert := Unit

instance : Verifiable Stmt Wit where
  Verify := fun _ w => Empty.elim w

instance : Refutable Stmt Wit Cert where
  Refutes := fun _ _ => true
  refutes_sound := by rintro _ _ _ ⟨w, -⟩; exact Empty.elim w

/-- The claim under dispute. -/
def X : Claim Stmt := ⟨()⟩

/-- The window **does** deliver the certificate — unlike `OptimisticAdjudication.Silence`, nothing
here is hiding behind a missed observation. -/
def observedAll : Cert → Prop := fun _ => True

/-- A **unanimous** ballot over a single agent, whose rule is unanimity. -/
def B : Ballot Unit where
  asserts := fun _ => True
  aggregates := fun a => ∀ i, a i

/-- The ballot upholds the claim. -/
theorem B_upholds : B.upholds := fun _ => trivial

/-- The claim genuinely does not hold — there is no witness at all. -/
theorem X_not_upheld : ¬ upheld (P := Stmt) (W := Wit) X := by
  rintro ⟨w, -⟩; exact Empty.elim w

/-- And it is not even optimistically upheld: a sound refutation was **observed**. -/
theorem X_not_optimistically_upheld :
    ¬ optimisticallyUpheld (P := Stmt) (W := Wit) X observedAll := by
  intro h; exact h ⟨(), trivial, rfl⟩

/-- **`unanimous_ballot_upholds_a_refuted_claim` — the anti-laundering counterexample.**

A **unanimous** ballot upholds, a **sound refutation was actually observed**, and the claim is
**false** — simultaneously, in one inhabited model. So `ballot` implies neither of the other two
regimes, and no quorum size, auditor count, or reputation weighting changes this: the ballot verdict
is a function of the assertion profile, which is not constrained by `Discharged` at all.

This is the shape of a platform that renders a two-auditor agreement with the same badge as a checked
certificate. -/
theorem unanimous_ballot_upholds_a_refuted_claim :
    B.upholds
      ∧ ¬ optimisticallyUpheld (P := Stmt) (W := Wit) X observedAll
      ∧ ¬ upheld (P := Stmt) (W := Wit) X :=
  ⟨B_upholds, X_not_optimistically_upheld, X_not_upheld⟩

end Laundering

/-! ## §3b. Witness ⇏ ballot — truth does not win votes.

The converse direction, and it matters for a different reason: it rules out treating the ballot
verdict as a *lossy proxy* for the real one. It is not measuring a noisy version of truth; it is
measuring something else. -/
namespace TrueButUnpopular

/-- Statements: one. -/
abbrev Stmt := Unit

/-- Witnesses: one, and it verifies — the claim genuinely `Holds`. -/
abbrev Wit := Unit

/-- Refutation certificates: **none**, so `refutes_sound` is vacuous and cannot be doing the work. -/
abbrev Cert := Empty

instance : Verifiable Stmt Wit where
  Verify := fun _ _ => true

instance : Refutable Stmt Wit Cert where
  Refutes := fun _ r => Empty.elim r
  refutes_sound := by rintro _ r; exact Empty.elim r

/-- The claim. -/
def X : Claim Stmt := ⟨()⟩

/-- A ballot in which **nobody** asserts, under a unanimity rule. -/
def B : Ballot Unit where
  asserts := fun _ => False
  aggregates := fun a => ∀ i, a i

/-- The claim genuinely holds: a discharging witness exists. -/
theorem X_upheld : upheld (P := Stmt) (W := Wit) X := ⟨(), rfl⟩

/-- Yet the ballot rejects it. -/
theorem B_rejects : ¬ B.upholds := fun h => h ()

/-- **`witness_does_not_imply_ballot` — a true claim can lose the vote.**

Together with §3a this places `ballot` *off* the implication ladder in both directions: it neither
follows from nor implies a witness verdict. A deployment may still need it (novelty, significance,
"is this the right question"), but it may never be rendered as, or substituted for, the other two. -/
theorem witness_does_not_imply_ballot :
    upheld (P := Stmt) (W := Wit) X ∧ ¬ B.upholds :=
  ⟨X_upheld, B_rejects⟩

end TrueButUnpopular

/-! # §4. The publication invariant — the badge means what it says -/

/-- **A publication.** The claim, the evidence context, the regime it was actually settled in, the
regime it is rendered as, and — as a *field* — the honesty condition.

Carrying `honest` in the structure is the design decision: a publication that outranks its evidence
is not a runtime error to be caught, it is **not constructible**. -/
structure Publication (P W R : Type u) (ι : Type v) [Verifiable P W] [Refutable P W R] where
  /-- The claim being published. -/
  claim : Claim P
  /-- Which refutation certificates the challenge window observed. -/
  observed : R → Prop
  /-- The ballot, where one was taken. -/
  ballot : Ballot ι
  /-- The regime in which the claim was actually settled. -/
  settledIn : Regime
  /-- The regime the publication is rendered as — the badge. -/
  renderedAs : Regime
  /-- The settlement actually obtained. -/
  settlement : SettledAt (W := W) claim observed ballot settledIn
  /-- **The honesty condition: a badge may not outrank its evidence.** -/
  honest : renderedAs.strength ≤ settledIn.strength

/-- **`rendered_witness_is_true` — a witness badge means the claim holds.**

For an honest publication rendered at witness strength, the claim genuinely `Holds`: a discharging
witness exists. This is the invariant the whole structure exists to deliver, and it is exactly what a
uniform green badge cannot provide. -/
theorem rendered_witness_is_true (p : Publication P W R ι)
    (h : p.renderedAs = Regime.witness) :
    upheld (P := P) (W := W) p.claim := by
  have hh := p.honest
  rw [h] at hh
  have hset := p.settlement
  cases hc : p.settledIn with
  | ballot => rw [hc] at hh; exact absurd hh (by decide)
  | optimistic => rw [hc] at hh; exact absurd hh (by decide)
  | witness => rw [hc] at hset; exact hset

/-- **`rendered_optimistic_is_not_refuted` — an optimistic badge means nothing refuted it.**

For an honest publication rendered at optimistic strength, no observed certificate refutes the claim.
Note the proof genuinely uses the ladder: a witness-settled claim discharges this via
`settled_witness_imp_optimistic`, which is why `witness` is allowed to render as `optimistic` at all.

⚠ This is the *safety-for-the-honest-prover* content only. It does **not** say the claim holds — that
step is `optimistic_sound`, which still owes `RefutationComplete` and `Actuated`. -/
theorem rendered_optimistic_is_not_refuted (p : Publication P W R ι)
    (h : p.renderedAs = Regime.optimistic) :
    optimisticallyUpheld (P := P) (W := W) p.claim p.observed := by
  have hh := p.honest
  rw [h] at hh
  have hset := p.settlement
  cases hc : p.settledIn with
  | ballot => rw [hc] at hh; exact absurd hh (by decide)
  | optimistic => rw [hc] at hset; exact hset
  | witness =>
      rw [hc] at hset
      exact settled_witness_imp_optimistic (W := W) p.claim p.observed p.ballot hset

/-! ## §4a. The honesty field is load-bearing.

Per `feedback-prove-the-floor-false`: a condition must be refutable, or it is decoration. Drop
`honest` from `Publication` and the witness badge stops meaning anything — here is the instance. -/
namespace Laundered

open Laundering

/-- The laundered publication, **without** the honesty condition: settled by a unanimous ballot,
rendered as a checked witness. Every field but `honest` is inhabited exactly as `Publication`
demands. -/
theorem laundered_publication_can_be_false :
    SettledAt (W := Wit) X observedAll B Regime.ballot
      ∧ ¬ Regime.strength Regime.witness ≤ Regime.strength Regime.ballot
      ∧ ¬ upheld (P := Stmt) (W := Wit) X :=
  ⟨B_upholds, by decide, X_not_upheld⟩

end Laundered

/-! ## §4b. NON-VACUITY — `Publication` is inhabited, and the §4 theorems bite.

`rendered_witness_is_true` quantifies over `Publication`s. If that structure were uninhabited the
theorem would be green and empty — the failure mode recorded as *a proved carrier is an idle
carrier*. So both regimes are constructed, and the witness theorem is applied to a real one. -/
namespace Nonvacuity

/-- An honest publication settled by a **witness** and rendered as one. -/
def honestWitness :
    Publication TrueButUnpopular.Stmt TrueButUnpopular.Wit TrueButUnpopular.Cert Unit where
  claim := TrueButUnpopular.X
  observed := fun r => Empty.elim r
  ballot := TrueButUnpopular.B
  settledIn := Regime.witness
  renderedAs := Regime.witness
  settlement := TrueButUnpopular.X_upheld
  honest := by decide

/-- **The witness theorem bites on a real publication** — it is applied here, not merely stated. -/
theorem rendered_witness_is_true_bites :
    upheld (P := TrueButUnpopular.Stmt) (W := TrueButUnpopular.Wit) honestWitness.claim :=
  rendered_witness_is_true honestWitness rfl

/-- An honest publication settled by a **ballot** and rendered as one — the strongest badge its
evidence allows. The witness rendering of this same settlement is exactly what `honest` refuses, and
§4a is the proof that the refusal is load-bearing. -/
def honestBallot :
    Publication Laundering.Stmt Laundering.Wit Laundering.Cert Unit where
  claim := Laundering.X
  observed := Laundering.observedAll
  ballot := Laundering.B
  settledIn := Regime.ballot
  renderedAs := Regime.ballot
  settlement := Laundering.B_upholds
  honest := by decide

/-- **`honest_ballot_badge_carries_no_truth`** — and here is why the regime must be *displayed*
rather than merely respected. This publication is entirely honest: its badge does not outrank its
evidence. The claim underneath it is still false. A reader who cannot see the regime cannot tell this
publication from `honestWitness`, and no amount of internal discipline fixes that — only rendering
the regime does. -/
theorem honest_ballot_badge_carries_no_truth :
    ¬ upheld (P := Laundering.Stmt) (W := Laundering.Wit) honestBallot.claim :=
  Laundering.X_not_upheld

end Nonvacuity

/-! # §5. The challenger obligation, in the deployment's vocabulary

⚠ **This section adds no mathematics.** Its content is
`OptimisticAdjudication.ChallengerGap.distKnows_honest_does_not_give_a_challenger`; what is new is
naming the two obligations as the *product's*, so a design document cannot state the weak one and
believe it has the strong one. -/

variable {Ω : Type u} {κ : Type v}

/-- **`CommunityCould`** — the obligation a design document reaches for by default: *if the claim is
false, the honest community distributedly knows a refutation.* -/
def CommunityCould (F : Frame Ω κ) (φ : Frame.Prop' Ω) (w : Ω) : Prop :=
  F.DistKnows F.Honest φ w

/-- **`FundedChallenger`** — the obligation an optimistic settlement actually needs: *some single
honest agent knows the refutation*, because a challenger has to be one party that can act. -/
def FundedChallenger (F : Frame Ω κ) (φ : Frame.Prop' Ω) (w : Ω) : Prop :=
  ∃ i, F.Honest i ∧ F.Knows i φ w

/-- `FundedChallenger` implies `CommunityCould` — the ladder runs this way and only this way. -/
theorem fundedChallenger_imp_communityCould (F : Frame Ω κ) (φ : Frame.Prop' Ω) (w : Ω)
    (h : FundedChallenger F φ w) : CommunityCould F φ w := by
  obtain ⟨i, _, hk⟩ := h
  exact F.knows_imp_distKnows F.Honest i (by assumption) φ w hk

/-- **`communityCould_does_not_give_fundedChallenger`** — the converse fails, in a concrete frame.

Product consequence: challengers must be **individually funded and individually addressed**. "The
community will catch it" is precisely the obligation this rules out; a bounty pool split across a
crowd does not discharge it, and a named bonded challenger per claim does. -/
theorem communityCould_does_not_give_fundedChallenger :
    CommunityCould ChallengerGap.CF ChallengerGap.φ ChallengerGap.CF.actual
      ∧ ¬ FundedChallenger ChallengerGap.CF ChallengerGap.φ ChallengerGap.CF.actual :=
  ChallengerGap.distKnows_honest_does_not_give_a_challenger

end Metatheory.ResearchRegime

#assert_axioms Metatheory.ResearchRegime.settled_witness_imp_optimistic
#assert_axioms Metatheory.ResearchRegime.Laundering.unanimous_ballot_upholds_a_refuted_claim
#assert_axioms Metatheory.ResearchRegime.TrueButUnpopular.witness_does_not_imply_ballot
#assert_axioms Metatheory.ResearchRegime.rendered_witness_is_true
#assert_axioms Metatheory.ResearchRegime.rendered_optimistic_is_not_refuted
#assert_axioms Metatheory.ResearchRegime.Laundered.laundered_publication_can_be_false
#assert_axioms Metatheory.ResearchRegime.fundedChallenger_imp_communityCould
#assert_axioms Metatheory.ResearchRegime.Nonvacuity.rendered_witness_is_true_bites
#assert_axioms Metatheory.ResearchRegime.Nonvacuity.honest_ballot_badge_carries_no_truth
