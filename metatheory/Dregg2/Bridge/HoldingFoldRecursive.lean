/-
# Metatheory.Bridge.HoldingFoldRecursive — the RECURSIVE / IVC verification layer on top
of the additive proof-of-holdings fold: "a light client folds N holding proofs into ONE
aggregate that soundly attests to the total weight."

`Dregg2.Bridge.ProofOfHoldingsGeneric` proves the ADDITIVE segment-fold: `foldWeights` sums
the per-holding non-custodial contributions and `foldWeights_append` is the homomorphism a
recursive light client exploits (verify two segments independently, add). But that fold
carries the finality/holds verdicts as GIVEN booleans — it does not yet MODEL the per-step
VERIFIER. This file adds the recursive-verification layer: an abstract `StepVerifier` that
ACCEPTS a single holding proof (what a real circuit / SNARK step-verifier does), a
`foldAccept` that conjoins the per-step accept over the whole list (the recursion an IVC
light client runs), and the keystone `fold_sound` — if the folded verification accepts, then
EVERY step's holding is consensus-proven, finalized, and genuinely held, so the aggregate
weight is exactly the sum of genuinely-backed balances. "The folded proof is sound iff each
step is."

## `StepVerifier` — the assumed step-soundness (a circuit provides it)
`StepVerifier C` bundles the data a per-step verifier supplies over a chain `C`:
  * `st : C.State` — the finalized head the light client checks each holding against.
  * `accept : GHolding C → Bool` — the executable per-step verifier (verifies ONE holding
    proof; this is the SNARK/circuit `Verify` a light client runs per fold step).
  * `sound : ∀ h, accept h = true → (h is consensusVerified ∧ Finalized ∧ Holds …)` — the
    step-soundness GUARANTEE. It is a STRUCTURE FIELD — the assumed soundness a real circuit
    verifier PROVIDES — never a global `axiom` and never a laundered `def FooHard`. (Per
    no-named-carrier-laundering: `#assert_axioms` cannot see a hypothesis/field, so we keep
    the assumption WHERE it is honest — as data supplied to the model, discharged for real on
    every concrete instance below.)

## The recursive fold
  * `foldAccept C sv hs` — the left-fold conjoining `sv.accept` over the holdings list (the
    recursive verification: a light client folds and ANDs). `foldAccept_append` — the fold
    conjunction is HOMOMORPHIC over `++` (verify segments independently and AND).
  * `foldAggregate C hs` — the folded total weight (`foldWeights` over the accepted list).
    `foldAggregate_append` inherits `foldWeights_append`.

## The keystones
  * `fold_sound` — if `foldAccept sv hs = true`, then every holding is a genuine
    non-custodial `grantsWeightG` of its own proven balance (via `sv.sound`), and the
    aggregate weight is EXACTLY the sum of the proven balances — no inflation. The folded
    proof soundly attests to the total weight.
  * `fold_step_backed_noncustodial` — composes `weight_backed_and_noncustodial_generic`: each
    accepted step is backed AND the deployed grant leaves ledger state unchanged (a pure read).
  * `fold_complete` — if every holding satisfies `accept`, the fold accepts.
  * `recursive_fold_backed` — the clean top theorem: a recursive light client verifies two
    ballot segments independently (`foldAccept_append`), folds their weights
    (`foldAggregate_append`), and the aggregate is backed (sum of proven balances, every step
    a non-custodial grant) and NON-CUSTODIAL (state unchanged).

## Non-vacuity (the recursion BITES — not `True`-shaped)
Instantiated at the SECOND, genuinely-different `toyChain` (state-dependent finality `h ≤ st`,
non-trivial `Holds` `proof = amount`) of the generic file:
  * HONEST FOLD: `toyStepVerifier` accepts iff consensus-tier ∧ finalized ∧ proof matches —
    its `sound` field is DISCHARGED for real (not assumed) via `decide`. Three good holdings
    fold-accept and `fold_sound` fires end-to-end: aggregate `150` = sum of proven balances.
  * REJECT TEETH: the SAME verifier REJECTS a holding whose proof does not certify the amount
    (`999 ≠ 50`), so `foldAccept` is `false` on any list containing it (`reject_teeth`) — the
    recursion correctly refuses. This bites only because `accept`/`Holds` are non-trivial; it
    proves the fold is a real conjunctive verification, not a `True`-shaped constant.

Kernel-clean: `#assert_axioms` hard-gates every theorem ⊆ {propext, Classical.choice,
Quot.sound}. The step-soundness stays an ASSUMED `StepVerifier.sound` field (a real circuit
provides it) — never an `axiom`, never a laundered `def FooHard`.
-/
import Dregg2.Bridge.ProofOfHoldingsGeneric

namespace Dregg2.Bridge.HoldingFoldRecursive

open Dregg2.Bridge.ProofOfHoldingsGeneric

/-! ## §1 — `StepVerifier`: the abstract per-step verifier + its assumed soundness. -/

/-- **`StepVerifier C`** — the data a recursive light client's per-step verifier supplies over
chain `C`. `accept` is the executable single-proof verifier (a SNARK/circuit `Verify` run per
fold step); `sound` is the step-soundness GUARANTEE it carries — a STRUCTURE FIELD (the
assumed soundness a real circuit provides), never an `axiom` and never a laundered `def
FooHard`. `st` is the finalized head each holding is checked against. -/
structure StepVerifier (C : ChainParams) where
  /-- The finalized head the light client verifies each holding against. -/
  st : C.State
  /-- The executable per-step verifier: verifies ONE holding proof. -/
  accept : GHolding C → Bool
  /-- **STEP-SOUNDNESS (assumed data, not an axiom).** Whenever the step verifier accepts a
  holding, that holding is genuinely consensus-verified, its height is `Finalized` in `st`,
  and its proof genuinely `Holds` the claimed balance. This is the guarantee a real circuit
  verifier provides per step; it is a field of the structure, discharged for real on every
  concrete instance. -/
  sound : ∀ h : GHolding C, accept h = true →
    h.tier = GTier.consensusVerified
      ∧ C.Finalized h.height st
      ∧ C.Holds h.proof h.owner h.asset h.amount h.height

/-! ## §2 — The recursive fold `foldAccept` and its append-homomorphism. -/

/-- **`foldAccept C sv hs`** — the recursive verification: a left-fold conjoining the per-step
`sv.accept` over the whole holdings list. A light client folds the list and ANDs the step
verdicts; `foldAccept = true` iff EVERY step accepted. -/
def foldAccept (C : ChainParams) (sv : StepVerifier C) (hs : List (GHolding C)) : Bool :=
  hs.foldl (fun acc h => acc && sv.accept h) true

/-- Peeling the fold accumulator: a left-fold with `&&` factors its start bit out front. The
lemma that turns the tail-recursive `foldl` into the head-conjunction the append proof needs. -/
private theorem foldl_accept_start (C : ChainParams) (sv : StepVerifier C) :
    ∀ (b : Bool) (hs : List (GHolding C)),
      hs.foldl (fun acc h => acc && sv.accept h) b
        = (b && hs.foldl (fun acc h => acc && sv.accept h) true) := by
  intro b hs
  induction hs generalizing b with
  | nil => simp
  | cons h t ih =>
    simp only [List.foldl_cons]
    rw [ih (b && sv.accept h), ih (true && sv.accept h)]
    simp [Bool.and_assoc]

/-- The empty fold accepts (vacuously). -/
theorem foldAccept_nil (C : ChainParams) (sv : StepVerifier C) :
    foldAccept C sv [] = true := rfl

/-- **`foldAccept` peels one step.** The recursive verification of `h :: hs` is `accept h`
ANDed with the recursive verification of `hs` — the per-step conjunction. -/
theorem foldAccept_cons (C : ChainParams) (sv : StepVerifier C)
    (h : GHolding C) (hs : List (GHolding C)) :
    foldAccept C sv (h :: hs) = (sv.accept h && foldAccept C sv hs) := by
  unfold foldAccept
  rw [List.foldl_cons, foldl_accept_start C sv (true && sv.accept h) hs, Bool.true_and]

/-- **FOLD-ACCEPT HOMOMORPHISM (the recursion the fold exploits).** Verifying a concatenation
of segments equals verifying each segment independently and ANDing — so a recursive light
client folds two segments' accept-verdicts separately and combines them by `&&`. This is the
verification-layer analog of `foldWeights_append`. -/
theorem foldAccept_append (C : ChainParams) (sv : StepVerifier C)
    (l1 l2 : List (GHolding C)) :
    foldAccept C sv (l1 ++ l2) = (foldAccept C sv l1 && foldAccept C sv l2) := by
  induction l1 with
  | nil => rw [List.nil_append, foldAccept_nil, Bool.true_and]
  | cons h t ih =>
    rw [List.cons_append, foldAccept_cons, foldAccept_cons, ih, Bool.and_assoc]

/-- If the folded verification accepts, then EVERY step accepted (the fold is a genuine
conjunction — one rejected step drops the whole aggregate). -/
theorem foldAccept_all (C : ChainParams) (sv : StepVerifier C) :
    ∀ (hs : List (GHolding C)), foldAccept C sv hs = true → ∀ x ∈ hs, sv.accept x = true
  | [], _, x, hx => by simp at hx
  | h :: t, hacc, x, hx => by
    rw [foldAccept_cons, Bool.and_eq_true] at hacc
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact hacc.1
    · exact foldAccept_all C sv t hacc.2 x hmem

/-! ## §3 — The folded aggregate weight and its append-homomorphism. -/

/-- **`foldAggregate C hs`** — the folded total weight the recursive light client attests to:
the additive `foldWeights` over the verified holdings (each carried with an affirmative
finality verdict, since the step verifier certified finalization). No chain state. -/
def foldAggregate (C : ChainParams) (hs : List (GHolding C)) : Nat :=
  foldWeights C (hs.map (fun h => (h, true)))

/-- The aggregate peels one contribution — the recursion the no-inflation proof folds over. -/
theorem foldAggregate_cons (C : ChainParams) (h : GHolding C) (hs : List (GHolding C)) :
    foldAggregate C (h :: hs) = foldContribution C h true + foldAggregate C hs := by
  simp [foldAggregate, foldWeights]

/-- **AGGREGATE HOMOMORPHISM.** The folded weight over a concatenation is the sum of the
segment aggregates — inherited from `foldWeights_append`. A recursive verifier folds two
segments' weights independently and adds. -/
theorem foldAggregate_append (C : ChainParams) (l1 l2 : List (GHolding C)) :
    foldAggregate C (l1 ++ l2) = foldAggregate C l1 + foldAggregate C l2 := by
  unfold foldAggregate
  rw [List.map_append, foldWeights_append]

/-! ## §4 — THE KEYSTONES: fold-soundness, backed-noncustodial, completeness. -/

/-- Under all-accepted, the aggregate is EXACTLY the sum of the proven balances — each
accepted step contributes its own amount (via `sv.sound` ⇒ consensus tier ⇒ full contribution),
so the fold credits neither more (no inflation) nor less than the proven snapshots. -/
theorem foldAggregate_backed (C : ChainParams) (sv : StepVerifier C) :
    ∀ (hs : List (GHolding C)), (∀ h ∈ hs, sv.accept h = true) →
      foldAggregate C hs = (hs.map (fun h => h.amount)).sum
  | [], _ => rfl
  | h :: t, hall => by
    have ha : sv.accept h = true := hall h (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨ht, _, _⟩ := sv.sound h ha
    have hrest : ∀ x ∈ t, sv.accept x = true := fun x hx => hall x (List.mem_cons.mpr (Or.inr hx))
    rw [foldAggregate_cons, foldAggregate_backed C sv t hrest, List.map_cons, List.sum_cons]
    have hc : foldContribution C h true = h.amount := by
      simp [foldContribution, grantWeightCoreG, GTier.isConsensusVerified, ht]
    rw [hc]

/-- **THE KEYSTONE — `fold_sound`.** If the recursive verification accepts (`foldAccept sv hs
= true`), then (1) EVERY holding is a genuine non-custodial `grantsWeightG` of its own proven
balance — consensus-verified, finalized against `sv.st`, genuinely holding — via the assumed
step-soundness `sv.sound`, and (2) the folded aggregate weight is EXACTLY the sum of those
proven balances (no inflation). The folded proof soundly attests to the total weight: "the
aggregate is sound iff each step is." -/
theorem fold_sound (C : ChainParams) (sv : StepVerifier C) (hs : List (GHolding C))
    (hacc : foldAccept C sv hs = true) :
    (∀ h ∈ hs, grantsWeightG C sv.st h h.owner h.amount)
    ∧ foldAggregate C hs = (hs.map (fun h => h.amount)).sum := by
  have hall : ∀ h ∈ hs, sv.accept h = true := foldAccept_all C sv hs hacc
  refine ⟨?_, foldAggregate_backed C sv hs hall⟩
  intro h hmem
  obtain ⟨ht, hf, hh⟩ := sv.sound h (hall h hmem)
  exact ⟨ht, hf, hh, rfl, Nat.le_refl _⟩

/-- **`fold_step_backed_noncustodial`.** Composing `weight_backed_and_noncustodial_generic`
over the fold: whenever the recursive verification accepts, each accepted step is BACKED (a
consensus-proven, finalized, genuinely-holding snapshot of at least its weight) AND
NON-CUSTODIAL — the deployed grant leaves the ledger state definitionally unchanged, for any
prior state and finality verdict. Evaluating the folded proof is a pure read. -/
theorem fold_step_backed_noncustodial (C : ChainParams) (sv : StepVerifier C)
    (hs : List (GHolding C)) (hacc : foldAccept C sv hs = true) (fv : Bool) (pre : C.State) :
    ∀ h ∈ hs,
      (h.tier = GTier.consensusVerified
        ∧ C.Finalized h.height sv.st
        ∧ C.Holds h.proof h.owner h.asset h.amount h.height
        ∧ h.amount ≤ h.amount
        ∧ h.owner = h.owner)
      ∧ (grantWeightG C h fv pre).2 = pre := by
  intro h hmem
  have hg : grantsWeightG C sv.st h h.owner h.amount := (fold_sound C sv hs hacc).1 h hmem
  exact weight_backed_and_noncustodial_generic C sv.st h h.owner h.amount hg fv pre

/-- **`fold_complete`.** If every holding satisfies the step verifier (`accept h = true`), the
recursive verification accepts — the fold is complete w.r.t. its per-step verifier. -/
theorem fold_complete (C : ChainParams) (sv : StepVerifier C) :
    ∀ (hs : List (GHolding C)), (∀ h ∈ hs, sv.accept h = true) → foldAccept C sv hs = true
  | [], _ => rfl
  | h :: t, hall => by
    rw [foldAccept_cons, hall h (List.mem_cons.mpr (Or.inl rfl)), Bool.true_and,
        fold_complete C sv t (fun x hx => hall x (List.mem_cons.mpr (Or.inr hx)))]

/-- **`recursive_fold_backed` — the clean top theorem.** A recursive light client verifies two
ballot segments INDEPENDENTLY and ANDs (`foldAccept_append`); when both accept, (1) the fused
verification accepts, (2) the aggregate weight is the sum of the segment aggregates
(`foldAggregate_append`), (3) it equals the sum of the proven balances — no inflation, (4)
every counted holding is a genuine non-custodial `grantsWeightG` of its own proven balance, and
(5) the deployed grant leaves ledger state unchanged (a pure read). The recursive fold soundly
attests to the total weight, non-custodially. -/
theorem recursive_fold_backed (C : ChainParams) (sv : StepVerifier C)
    (l1 l2 : List (GHolding C))
    (h1 : foldAccept C sv l1 = true) (h2 : foldAccept C sv l2 = true) (pre : C.State) :
    foldAccept C sv (l1 ++ l2) = true
    ∧ foldAggregate C (l1 ++ l2) = foldAggregate C l1 + foldAggregate C l2
    ∧ foldAggregate C (l1 ++ l2) = ((l1 ++ l2).map (fun h => h.amount)).sum
    ∧ (∀ h ∈ l1 ++ l2, grantsWeightG C sv.st h h.owner h.amount)
    ∧ (∀ h : GHolding C, (grantWeightG C h true pre).2 = pre) := by
  have hacc : foldAccept C sv (l1 ++ l2) = true := by rw [foldAccept_append, h1, Bool.true_and, h2]
  obtain ⟨hgrants, hsum⟩ := fold_sound C sv (l1 ++ l2) hacc
  exact ⟨hacc, foldAggregate_append C l1 l2, hsum, hgrants,
         fun h => grant_preserves_custody_generic C h true pre⟩

/-! ## §5 — NON-VACUITY (a): an HONEST all-accept fold whose `sound` is DISCHARGED for real.

At the SECOND, genuinely-different `toyChain` of the generic file (state-dependent finality
`h ≤ st`, non-trivial `Holds` `proof = amount`). The verifier's `sound` field is not assumed
here — it is PROVEN via `decide`, so the honest fold fires `fold_sound` end-to-end with no
open obligation. -/

/-- The honest toy step verifier: accept iff consensus-tier ∧ height finalized at head `10`
∧ the proof certifies the amount. Each conjunct is decidable, so `accept` is executable. -/
def toyAccept (h : GHolding toyChain) : Bool :=
  decide (h.tier = GTier.consensusVerified) && decide (h.height ≤ 10) && decide (h.proof = h.amount)

/-- **The honest `StepVerifier` on `toyChain`** — its step-soundness field is DISCHARGED for
real (via `decide`), not assumed: `accept h = true` genuinely entails consensus tier, finality
at head `10`, and a matching proof, which ARE `toyChain`'s `Finalized`/`Holds`. -/
def toyStepVerifier : StepVerifier toyChain where
  st := 10
  accept := toyAccept
  sound := by
    intro h hacc
    simp only [toyAccept, Bool.and_eq_true, decide_eq_true_eq] at hacc
    exact ⟨hacc.1.1, hacc.1.2, hacc.2⟩

/-- The valid toy holding is accepted (consensus, `4 ≤ 10`, `50 = 50`). -/
theorem toyAccept_proven : toyAccept toyProven = true := by decide

/-- Three good toy holdings — the honest fold's ballot list. -/
def honestBallots : List (GHolding toyChain) := [toyProven, toyProven, toyProven]

/-- **THE HONEST FOLD ACCEPTS** — every step passes, so the recursive verification accepts.
Proven via `fold_complete` (the completeness keystone), not by brute reduction. -/
theorem honest_foldAccept : foldAccept toyChain toyStepVerifier honestBallots = true := by
  apply fold_complete
  intro h hmem
  simp only [honestBallots, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl <;> exact toyAccept_proven

/-- **`fold_sound` FIRES END-TO-END on the honest fold.** Every holding is a genuine
non-custodial grant, and the aggregate `= 150` is exactly the sum of the proven balances — the
folded proof soundly attests to the total weight. -/
theorem honest_fold_sound :
    (∀ h ∈ honestBallots, grantsWeightG toyChain toyStepVerifier.st h h.owner h.amount)
    ∧ foldAggregate toyChain honestBallots = (honestBallots.map (fun h => h.amount)).sum :=
  fold_sound toyChain toyStepVerifier honestBallots honest_foldAccept

/-- The honest aggregate is the concrete total `150`. -/
theorem honest_aggregate : foldAggregate toyChain honestBallots = 150 := by decide

/-- A concrete counted step IS a genuine non-custodial grant — `grantsWeightG` fires for
`toyProven`'s owner `3` at its proven balance `50`, pulled straight out of `fold_sound`. -/
theorem honest_first_grants :
    grantsWeightG toyChain toyStepVerifier.st toyProven toyProven.owner toyProven.amount :=
  honest_fold_sound.1 toyProven (List.mem_cons.mpr (Or.inl rfl))

/-! ## §6 — NON-VACUITY (b): REJECT TEETH — the recursion correctly refuses a bad step. -/

/-- The SAME honest verifier REJECTS a holding whose proof does not certify the amount
(`999 ≠ 50`) — `accept` has teeth because `toyChain.Holds` is a non-trivial relation. -/
theorem toyAccept_badProof : toyAccept toyBadProof = false := by decide

/-- A ballot list with one bad holding in the middle. -/
def badBallots : List (GHolding toyChain) := [toyProven, toyBadProof, toyProven]

/-- **REJECT TEETH.** One rejected step drops the whole aggregate: `foldAccept` is `false` on
`badBallots` — the recursive verification correctly REFUSES. This bites only because `accept`
/ `Holds` are non-trivial (a `True`-shaped fold could never reject), so it witnesses that the
recursion is a genuine conjunctive verification, not a constant. -/
theorem reject_teeth : foldAccept toyChain toyStepVerifier badBallots = false := by decide

/-- **REJECT TEETH via the homomorphism.** Because the middle segment `[toyBadProof]` fails,
`foldAccept_append` forces the whole concatenation to `false` — the fold's conjunction
propagates a single rejected step through any segmentation the light client chooses. -/
theorem reject_teeth_segmented :
    foldAccept toyChain toyStepVerifier ([toyProven] ++ ([toyBadProof] ++ [toyProven])) = false := by
  rw [foldAccept_append, foldAccept_append]
  decide

/-- **THE RECURSION BITES, not `True`.** Same verifier, same shape: the honest list ACCEPTS
(`true`) and the one-bad-step list REJECTS (`false`). The fold discriminates — `fold_sound`'s
hypothesis is genuinely unavailable on `badBallots`. -/
theorem fold_discriminates :
    foldAccept toyChain toyStepVerifier honestBallots = true
    ∧ foldAccept toyChain toyStepVerifier badBallots = false :=
  ⟨honest_foldAccept, reject_teeth⟩

/-! It runs (`#guard`). -/

#guard foldAccept toyChain toyStepVerifier honestBallots == true
#guard foldAccept toyChain toyStepVerifier badBallots == false
#guard foldAggregate toyChain honestBallots == 150
#guard foldAggregate toyChain ([toyProven] ++ [toyProven]) == 100
#guard toyAccept toyProven == true
#guard toyAccept toyBadProof == false

/-! ## §7 — Axiom hygiene — every theorem kernel-clean (CI hard-gate). -/

#assert_axioms foldAccept_nil
#assert_axioms foldAccept_cons
#assert_axioms foldAccept_append
#assert_axioms foldAccept_all
#assert_axioms foldAggregate_cons
#assert_axioms foldAggregate_append
#assert_axioms foldAggregate_backed
#assert_axioms fold_sound
#assert_axioms fold_step_backed_noncustodial
#assert_axioms fold_complete
#assert_axioms recursive_fold_backed

#assert_axioms toyAccept_proven
#assert_axioms honest_foldAccept
#assert_axioms honest_fold_sound
#assert_axioms honest_aggregate
#assert_axioms honest_first_grants
#assert_axioms toyAccept_badProof
#assert_axioms reject_teeth
#assert_axioms reject_teeth_segmented
#assert_axioms fold_discriminates

#print axioms fold_sound
#print axioms fold_complete
#print axioms foldAccept_append
#print axioms recursive_fold_backed
#print axioms reject_teeth

end Dregg2.Bridge.HoldingFoldRecursive
