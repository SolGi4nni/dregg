/-
# `Dregg2.Circuit.FriFoldConsistencyDichotomy` — the OTHER HALF of the strategy-quantified FRI
soundness argument: a fold-INCONSISTENT prover is caught by the QUERY phase, and the two branches
composed into ONE statement about an arbitrary strategy.

`FriAdversaryObject`/`FriChainStepIdx` quantified the prover (`chain_far_survival_strategy`,
`ud_tower_far_survival_strategy`) but gated the bound on the path-local `FoldConsistentAlong`.
The gate is load-bearing — `FriChainStepIdx.consistencyFreeSurvival_false` refutes the ungated
statement with a prover that COMMITS A CODEWORD at round 1 — so `∀ S` was, until this file, a
quantifier over a set of provers with no companion theorem about its complement. Both module
headers and `CorrelatedAgreement/Interface.lean:123,831` say the same thing in words: "the OTHER
branch, that a fold-inconsistent prover is caught by the query phase, is NOT proved here or
anywhere in-tree". This file proves it, at the resolution the existing objects support.

## What the shelf already had, and what it did NOT

  * `FriQuerySoundness.accept_prob_le` (`:132`) — the COUNTING core: a pair of words disagreeing
    on more than `δ·|ι|` points passes `k` uniform spot checks with mass `≤ (1−δ)^k`. PROVEN,
    generic, and it is exactly the payment this file spends. `fold_check_pass_prob_le` (`:189`)
    is its `(f', Fold α f)` instance at ONE round of a `FriSetup`.
  * `DeployedTraceExtract.accept_close_or_paid` (`:545`) — a per-run dichotomy, but a DIFFERENT
    one: it splits on whether the ORACLE is close to the domain code, and pays on a `d`-far FOLD.
    It says nothing about a prover's commitment DEVIATING from the fold, has no `Strategy`, no
    `fsChain`, no `FoldConsistentAlong`, and no round index. It cannot be wired to the gate.
  * NOTHING in the tree relates `FoldConsistentAlong` (a `Strategy`-level, path-local EQUALITY of
    commitments) to any query-phase mass. `grep FoldClose|consistency_dichotomy|caught_or` is
    empty outside this file. So: the counting lemma was on the shelf; the DICHOTOMY was not.

## The finding that shapes the whole file: EXACT consistency is not spot-checkable

`FoldConsistentAlong` is an EQUALITY (`S (c :: cs) = fold (S cs) c`). Its negation gives ONE
disagreeing point. `accept_prob_le` pays `(1−δ)^k` only for MORE than `δ·|ι|` disagreeing points,
so at the exact gate the admissible `δ` is `0` and the payment is `(1−0)^k = 1` — nothing. This
is not a proof-engineering shortfall, it is true of the protocol: a prover that deviates from the
fold at ONE point is invisible to `k` spot checks with probability `(1 − 1/|ι|)^k`. It is stated
here as a THEOREM, not prose (`exact_gate_pays_nothing`), because it is the reason the gate must
be slackened rather than the reason the branch cannot be proved.

So the honest dichotomy is graded by a slack radius `d`, and BOTH branches carry content:

  **`foldConsistent_or_query_paid`** — for ANY strategy `S`, any oracle `H`, any `n`, and any
  `δ` with `δ·|ι| ≤ d`: EITHER `S` is `d`-fold-close along the whole walked path
  (`FoldCloseAlong`, which at `d = 0` IS `FoldConsistentAlong`), OR there is a round `j < n` at
  which the prover's committed word and the fold it was supposed to be disagree on more than `d`
  points, and the verifier's `k`-point fold check at that round passes with mass `≤ (1−δ)^k`.

Not excluded middle: the right disjunct is strictly stronger than `¬ FoldCloseAlong` — it names
the round and carries the paid probability.

## What is PROVED here versus what is NAMED

PROVED (no hypothesis): the dichotomy; the survival chain under the slackened gate
(`chain_far_slack_of_farCover`) and its priced form (`chain_far_survival_slack_gated`); the
composition of the two branches over the product space (`strategy_soundness_compose`); the
product-space probability plumbing; and both firings.

NAMED, never axiomatized — exactly ONE thing:

  * **`ChainStepGap C rad d goodSet fold`** — "a word `rad`-far from the code, folded at a
    challenge outside its good set, is `(rad + d)`-far": the per-round distance obligation WITH A
    MARGIN `d`. This is the same species as the existing `FriAdversaryObject.ChainStep` (a `def`
    whose instances are ladder stage L2), it IS `ChainStep` at `d = 0`
    (`chainStepGap_zero_iff_chainStep`), and it is not a restatement of anything classical.
    From it `ChainStepSlack` — the hypothesis the slackened chain actually consumes — is a
    THEOREM (`chainStepSlack_of_gap`, via `FriLdtJohnson.hamming_triangle`), so the named object
    is one honest step from the machine-checked chain, not a chain of hand-waves.
    ⚑ WHERE THE INSTANCE MUST COME FROM, precisely. `FriChainStepIdx.goodδ_card_lt` (`:670`) is
    already margin-shaped: a word not `n²·d`-close to `C` has fewer than `n` challenges folding it
    `d`-close to `C'` — source radius `n²·d`, target radius `d`, a margin of `n²·d − d`. So the
    obligation is not exotic. What blocks the instance is that every landed radius schedule runs
    at `d = 0`: `FriSetupTower` welds five real arity-8 layers at `2^19` but instantiates
    `far = ∉ code` (`FriSetupTower:49-52`, which also records why — `FriPositiveRadiusPayment`
    proved positive-radius farness UNINHABITED at `|ι| = 16`, and the positive-radius schedule at
    the `2^19` domain is named there as the NEXT rung, not claimed). At `d = 0` the margin is `0`
    and `ChainStepGap` collapses to `ChainStep`, whose §3 payment is nothing. So the residual is
    exactly: **the positive-radius schedule that `FriSetupTower` names as its next rung is what
    turns this file's named obligation into a discharged one.** (⚠ `FriChainStepIdx`'s header
    still says "No welded setup TOWER" — that is STALE; `FriSetupTower` landed it.)

## Non-vacuity (§7): ONE strategy, BOTH branches, and the gap visibly closed

`halfDeviator` deviates from the fold on HALF the domain: enough to escape farness with
probability EXACTLY 1 (`halfDeviator_escape_prob_one` — so the survival theorem says NOTHING
about it, precisely the hole this file fills), and few enough that the query phase can MISS it
(`halfDeviator_query_event_nonempty` — the caught branch is a genuine probability, not `0`).
`foldConsistent_or_query_paid` takes the RIGHT branch on it (`halfDeviator_dichotomy_right`) and
the LEFT branch on `honestStrategy` (`honest_dichotomy_left`). The composed bound fires at
`1·0/2 + (3/4)^3 = 27/64 < 1` (`halfDeviator_composed`, `halfDeviator_composed_lt_one`).

⚑ Stated so it cannot be read up: at the §7 instance the FS branch pays `0` (empty bad sets), so
the firing exercises the QUERY branch — which is the branch this file adds. The FS branch's own
non-vacuity is `FriChainStepIdx.k8_chain_far_survival` (`7/|BabyBear|`) and
`FriSetupTower.tower_chain_far_survival`, not re-demonstrated here.

## ⚑ What this module does NOT do

  * **It does not bind the commitment.** `Strategy R (ι → F)` hands the verifier a WORD, so
    `queryPassesAlong` reads the same word at every query. A deployed prover commits a Merkle root
    and answers openings, and pinning "the opened leaves come from one word" is the extraction
    substrate's job (`RomQueryLog` + `FriVerifierMerkle`, ladder stage L4). Without that, this is
    a statement about a prover that has already been forced to be word-consistent across queries.
  * **The query model is the uniform i.i.d. one.** Same idealization `FriQuerySoundness` and
    `DeployedTraceExtract` run on; `FriQuerySamplingBias` proves the deployed sampler is NOT that.
  * **Fixed-`C`.** The commitment type does not shrink per round, so this composes with
    `chain_far_survival_strategy` (fixed-`C`) and NOT yet with `chain_far_survival_idx_strategy`
    or the five-layer `FriSetupTower`. The indexed lift is the same induction over `Σ i, W i`
    that `chainStepIdx_iff_sigma` already performs for `ChainStep`; it is not done here.
  * **It does not reach the verifier's accept.** `bad` is any event implying the terminal
    commitment is not far; connecting that to "the deployed verifier accepted" is
    `FriLdtExtractV3`/`DeployedTraceExtract`, untouched.
  * **It moves no deployed statement and discharges no FRI/STARK floor.** ADDITIVE only.

## Rooting
NOT imported by `Dregg2.lean` — it needs one `import Dregg2.Circuit.FriFoldConsistencyDichotomy`
line added there (deliberately not edited: concurrent lanes).

## Axiom hygiene
`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`, no
`native_decide`. ADDITIVE: no existing module is edited.
-/
import Dregg2.Circuit.FriChainStepIdx
import Dregg2.Circuit.FriQuerySoundness
import Dregg2.Circuit.FriLdtJohnson
import Dregg2.Tactics
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Dregg2.Circuit.FriFoldConsistencyDichotomy

open Dregg2.Crypto.RomOracle
open Dregg2.Circuit.FriAdversaryObject
open Dregg2.Circuit.FriChainStepIdx (hitWin hitWin_fsRun_true_iff hit_bound)
open Dregg2.Circuit.FriSoundness (disagree mem_disagree disagree_eq_empty_iff closeN farN)
open Dregg2.Circuit.FriQuerySoundness (Accepts accept_prob_le soundness_error_compose)
open Dregg2.Circuit.FriLdtJohnson (disagree_symm hamming_triangle)
open Dregg2.Crypto.ProbCrypto (winProb winProb_le_of_imp winProb_top)

/-! ## §0 — probability plumbing over a PRODUCT sample space.

The two branches live on different randomness: farness survival is over the random oracle
`H : D → R`, the spot-check payment is over the query sample `Q : Fin k → ι`. Composing them into
one statement means one space `(D → R) × (Fin k → ι)`, so we need (a) a marginal lift and (b) a
fiberwise bound. Both are pure counting; neither exists in-tree. -/

section Product

variable {Ω Ω₁ Ω₂ : Type} [Fintype Ω] [Fintype Ω₁] [Fintype Ω₂]

/-- **Union bound on `winProb`** — the `Finset`-level `FriQuerySoundness.soundness_error_compose`
read as a probability statement. If every winning outcome of `f` wins `g` or wins `h`, then
`winProb f ≤ winProb g + winProb h`. -/
theorem winProb_le_add [DecidableEq Ω] {f g h : Ω → Bool}
    (himp : ∀ o, f o = true → g o = true ∨ h o = true) :
    winProb f ≤ winProb g + winProb h := by
  have hsub : (Finset.univ.filter (fun o : Ω => f o = true))
      ⊆ (Finset.univ.filter (fun o : Ω => g o = true))
        ∪ (Finset.univ.filter (fun o : Ω => h o = true)) := by
    intro o ho
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ho
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact himp o ho
  simpa [winProb] using soundness_error_compose _ _ _ hsub

/-- **Marginal lift.** An event that depends only on the FIRST coordinate has the same
probability on the product space as on its own — the second coordinate's randomness is
irrelevant to it. This is what lets the oracle-only survival bound be spent inside a statement
whose sample space also carries the query sample. -/
theorem winProb_fst [Nonempty Ω₂] (p : Ω₁ → Bool) :
    winProb (fun ω : Ω₁ × Ω₂ => p ω.1) = winProb p := by
  classical
  have hf : (Finset.univ.filter (fun ω : Ω₁ × Ω₂ => p ω.1 = true))
      = (Finset.univ.filter (fun o : Ω₁ => p o = true)) ×ˢ (Finset.univ : Finset Ω₂) := by
    ext ⟨a, b⟩
    simp
  have h2 : (Fintype.card Ω₂ : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := Ω₂)
  rw [winProb, winProb, hf, Finset.card_product, Finset.card_univ, Fintype.card_prod]
  push_cast
  rw [mul_div_mul_right _ _ h2]

/-- **Fiberwise bound.** If for EVERY first coordinate the winning slice of the second coordinate
has density at most `β`, the whole product event has probability at most `β`. This is how the
`(1−δ)^k` spot-check mass — proved per-oracle, since which round is inconsistent depends on the
oracle — becomes a bound on the joint event. -/
theorem winProb_le_of_fiber {β : ℝ} (hβ : 0 ≤ β) (w : Ω₁ × Ω₂ → Bool)
    (h : ∀ o : Ω₁, ((Finset.univ.filter (fun o₂ : Ω₂ => w (o, o₂) = true)).card : ℝ)
           ≤ β * (Fintype.card Ω₂ : ℝ)) :
    winProb w ≤ β := by
  classical
  have hsum : ((Finset.univ.filter (fun ω : Ω₁ × Ω₂ => w ω = true)).card : ℝ)
      = ∑ o : Ω₁, ((Finset.univ.filter (fun o₂ : Ω₂ => w (o, o₂) = true)).card : ℝ) := by
    have h1 : (Finset.univ.filter (fun ω : Ω₁ × Ω₂ => w ω = true)).card
        = ∑ ω : Ω₁ × Ω₂, if w ω = true then 1 else 0 := Finset.card_filter _ _
    have h2 : ∀ o : Ω₁, (Finset.univ.filter (fun o₂ : Ω₂ => w (o, o₂) = true)).card
        = ∑ o₂ : Ω₂, if w (o, o₂) = true then 1 else 0 := fun o => Finset.card_filter _ _
    rw [h1, Fintype.sum_prod_type]
    push_cast
    exact Finset.sum_congr rfl (fun o _ => by rw [h2 o]; push_cast; rfl)
  rcases Nat.eq_zero_or_pos (Fintype.card Ω₁) with h1 | h1
  · have : Fintype.card (Ω₁ × Ω₂) = 0 := by rw [Fintype.card_prod, h1, zero_mul]
    simp [winProb, this, hβ]
  rcases Nat.eq_zero_or_pos (Fintype.card Ω₂) with h2 | h2
  · have : Fintype.card (Ω₁ × Ω₂) = 0 := by rw [Fintype.card_prod, h2, mul_zero]
    simp [winProb, this, hβ]
  have hc1 : (0 : ℝ) < (Fintype.card Ω₁ : ℝ) := by exact_mod_cast h1
  have hc2 : (0 : ℝ) < (Fintype.card Ω₂ : ℝ) := by exact_mod_cast h2
  rw [winProb, Fintype.card_prod]
  rw [div_le_iff₀ (by push_cast; positivity)]
  rw [hsum]
  calc ∑ o : Ω₁, ((Finset.univ.filter (fun o₂ : Ω₂ => w (o, o₂) = true)).card : ℝ)
      ≤ ∑ _o : Ω₁, β * (Fintype.card Ω₂ : ℝ) := Finset.sum_le_sum (fun o _ => h o)
    _ = (Fintype.card Ω₁ : ℝ) * (β * (Fintype.card Ω₂ : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = β * ((Fintype.card Ω₁ : ℝ) * (Fintype.card Ω₂ : ℝ)) := by ring
    _ = β * ((Fintype.card Ω₁ * Fintype.card Ω₂ : ℕ) : ℝ) := by push_cast; ring

end Product

/-! ## §1 — the walked path, named.

`FoldConsistentAlong` is written with the raw expression `H (enc (S cs) cs)` inlined three times.
Every statement below needs to point at the three objects that expression hides — the challenge
drawn, the word the prover COMMITS next, and the word the fold PRESCRIBES — so they get names. -/

variable {F : Type} [Field F] [DecidableEq F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {R D : Type}

/-- The challenge the oracle `H` draws at transcript prefix `ds` (the FS query point carries the
prover's current commitment, which is what makes the bad set per-point). -/
def chalAt (enc : (ι → F) → List R → D) (S : Strategy R (ι → F)) (H : D → R)
    (ds : List R) : R := H (enc (S ds) ds)

/-- The transcript prefix one FS round later. `fsChain _ _ _ (n+1) cs = fsChain _ _ _ n
(stepPrefix cs)` holds by `rfl`. -/
def stepPrefix (enc : (ι → F) → List R → D) (S : Strategy R (ι → F)) (H : D → R)
    (ds : List R) : List R := chalAt enc S H ds :: ds

/-- **The word the prover COMMITS for the next round** at prefix `ds`. -/
def committedNext (enc : (ι → F) → List R → D) (S : Strategy R (ι → F)) (H : D → R)
    (ds : List R) : ι → F := S (stepPrefix enc S H ds)

/-- **The word the fold PRESCRIBES** at prefix `ds` — what an honest prover would have to commit.
The verifier's fold-consistency spot check tests `committedNext` against exactly this. -/
def prescribedFold (enc : (ι → F) → List R → D) (S : Strategy R (ι → F))
    (fold : (ι → F) → R → (ι → F)) (H : D → R) (ds : List R) : ι → F :=
  fold (S ds) (chalAt enc S H ds)

@[simp] theorem fsChain_succ_stepPrefix (enc : (ι → F) → List R → D) (S : Strategy R (ι → F))
    (H : D → R) (n : ℕ) (cs : List R) :
    fsChain enc S H (n + 1) cs = fsChain enc S H n (stepPrefix enc S H cs) := rfl

/-! ## §2 — `FoldCloseAlong`: the gate, GRADED by a slack radius. -/

/-- **⚑ `FoldCloseAlong d` — the path-local gate with slack `d`.** Along the FS path the oracle
actually walks, each round's committed word disagrees with the fold it was supposed to be on at
most `d` points. At `d = 0` this is EXACTLY `FriAdversaryObject.FoldConsistentAlong`
(`foldCloseAlong_zero_iff_consistent`); at `d > 0` it is strictly weaker, and it is the strongest
predicate a `k`-point spot check can enforce (`exact_gate_pays_nothing`). -/
def FoldCloseAlong (enc : (ι → F) → List R → D) (S : Strategy R (ι → F))
    (fold : (ι → F) → R → (ι → F)) (H : D → R) (d : ℕ) : ℕ → List R → Prop
  | 0, _ => True
  | n + 1, cs =>
      (disagree (committedNext enc S H cs) (prescribedFold enc S fold H cs)).card ≤ d
        ∧ FoldCloseAlong enc S fold H d n (stepPrefix enc S H cs)

@[simp] theorem foldCloseAlong_zero_rounds (enc : (ι → F) → List R → D) (S : Strategy R (ι → F))
    (fold : (ι → F) → R → (ι → F)) (H : D → R) (d : ℕ) (cs : List R) :
    FoldCloseAlong enc S fold H d 0 cs := trivial

theorem foldCloseAlong_succ (enc : (ι → F) → List R → D) (S : Strategy R (ι → F))
    (fold : (ι → F) → R → (ι → F)) (H : D → R) (d n : ℕ) (cs : List R) :
    FoldCloseAlong enc S fold H d (n + 1) cs ↔
      ((disagree (committedNext enc S H cs) (prescribedFold enc S fold H cs)).card ≤ d
        ∧ FoldCloseAlong enc S fold H d n (stepPrefix enc S H cs)) := Iff.rfl

/-- **At `d = 0` the graded gate IS the landed one.** So nothing below changes the meaning of the
`FriAdversaryObject`/`FriChainStepIdx` gate; it grades it. -/
theorem foldCloseAlong_zero_iff_consistent (enc : (ι → F) → List R → D) (S : Strategy R (ι → F))
    (fold : (ι → F) → R → (ι → F)) (H : D → R) :
    ∀ (n : ℕ) (cs : List R),
      FoldCloseAlong enc S fold H 0 n cs ↔ FoldConsistentAlong enc S fold H n cs := by
  intro n
  induction n with
  | zero => intro cs; simp [FoldConsistentAlong]
  | succ n ih =>
      intro cs
      rw [foldCloseAlong_succ, foldConsistentAlong_succ, ih (stepPrefix enc S H cs)]
      constructor
      · rintro ⟨hcard, htail⟩
        refine ⟨?_, htail⟩
        have : disagree (committedNext enc S H cs) (prescribedFold enc S fold H cs) = ∅ := by
          rw [← Finset.card_eq_zero]; omega
        exact disagree_eq_empty_iff.mp this
      · rintro ⟨heq, htail⟩
        refine ⟨?_, htail⟩
        have : disagree (committedNext enc S H cs) (prescribedFold enc S fold H cs) = ∅ :=
          disagree_eq_empty_iff.mpr heq
        rw [this]; simp

/-- Monotone in the slack: more slack is a weaker gate. -/
theorem foldCloseAlong_mono (enc : (ι → F) → List R → D) (S : Strategy R (ι → F))
    (fold : (ι → F) → R → (ι → F)) (H : D → R) {d d' : ℕ} (hd : d ≤ d') :
    ∀ (n : ℕ) (cs : List R),
      FoldCloseAlong enc S fold H d n cs → FoldCloseAlong enc S fold H d' n cs := by
  intro n
  induction n with
  | zero => intro cs _; trivial
  | succ n ih =>
      intro cs h
      rw [foldCloseAlong_succ] at h ⊢
      exact ⟨h.1.trans hd, ih _ h.2⟩

/-- **The honest prover satisfies the graded gate at EVERY slack**, for free — via
`FriAdversaryObject.honest_foldConsistentAlong` at `d = 0` and monotonicity. So the grading, like
the original gate, costs the honest prover nothing. -/
theorem honest_foldCloseAlong (enc : (ι → F) → List R → D) (fold : (ι → F) → R → (ι → F))
    (w0 : ι → F) (H : D → R) (d : ℕ) :
    ∀ (n : ℕ) (cs : List R), FoldCloseAlong enc (honestStrategy fold w0) fold H d n cs := by
  intro n cs
  exact foldCloseAlong_mono enc _ fold H (Nat.zero_le d) n cs
    ((foldCloseAlong_zero_iff_consistent enc _ fold H n cs).mpr
      (honest_foldConsistentAlong enc fold w0 H n cs))

/-! ## §3 — ⚑ THE DICHOTOMY. -/

/-- **Where the gate first fails, quantitatively.** If `S` is not `d`-fold-close along the walked
path for `n` rounds, then some round `j < n` on that path has the prover's committed word
disagreeing with the prescribed fold on MORE than `d` points. Induction on `n`: the head case is
the failing conjunct, the tail case is the IH at `stepPrefix`, whose chain prefix is
`fsChain _ _ _ (j+1)` by `rfl`. -/
theorem exists_deviating_round (enc : (ι → F) → List R → D) (S : Strategy R (ι → F))
    (fold : (ι → F) → R → (ι → F)) (H : D → R) (d : ℕ) :
    ∀ (n : ℕ) (cs : List R), ¬ FoldCloseAlong enc S fold H d n cs →
      ∃ j, j < n ∧
        d < (disagree (committedNext enc S H (fsChain enc S H j cs))
              (prescribedFold enc S fold H (fsChain enc S H j cs))).card := by
  intro n
  induction n with
  | zero => intro cs h; exact absurd trivial h
  | succ n ih =>
      intro cs h
      rw [foldCloseAlong_succ] at h
      by_cases hhead :
          (disagree (committedNext enc S H cs) (prescribedFold enc S fold H cs)).card ≤ d
      · have htail : ¬ FoldCloseAlong enc S fold H d n (stepPrefix enc S H cs) := by
          intro hc; exact h ⟨hhead, hc⟩
        obtain ⟨j, hj, hcard⟩ := ih (stepPrefix enc S H cs) htail
        exact ⟨j + 1, by omega, by simpa using hcard⟩
      · exact ⟨0, by omega, by simpa [fsChain] using Nat.lt_of_not_le hhead⟩

/-- **⚑⚑ THE FOLD-CONSISTENCY DICHOTOMY.** For an ARBITRARY prover strategy `S`, an arbitrary
oracle `H`, any round count `n`, any slack `d`, any query count `k`, and any `δ` with
`δ·|ι| ≤ d`: EITHER

  * `S` is `d`-fold-close along the whole walked path — the branch on which the farness-survival
    machinery runs (`chain_far_survival_slack_gated` below; at `d = 0` this branch is literally
    `FoldConsistentAlong`, so it is the branch `chain_far_survival_strategy` consumes) — OR
  * there is a round `j < n` at which the prover's committed word deviates from the prescribed
    fold on more than `d` points, AND the fraction of `k`-query samples on which the verifier's
    fold-consistency check at that round PASSES is at most `(1−δ)^k`.

This is the statement `FriAdversaryObject:206-208`, `FriChainStepIdx:42-44` and
`CorrelatedAgreement/Interface.lean:123,831` all name and none prove. It is not excluded middle:
the right disjunct names the round and carries the paid mass, and its proof is
`FriQuerySoundness.accept_prob_le` at the deviating round's `(committedNext, prescribedFold)`
pair — the same counting core the whole query column is built on. -/
theorem foldConsistent_or_query_paid (enc : (ι → F) → List R → D) (S : Strategy R (ι → F))
    (fold : (ι → F) → R → (ι → F)) (H : D → R) (d k : ℕ) {δ : ℝ}
    (hι : 0 < Fintype.card ι) (hδ0 : 0 ≤ δ) (hδd : δ * (Fintype.card ι : ℝ) ≤ (d : ℝ))
    (n : ℕ) (cs : List R) :
    FoldCloseAlong enc S fold H d n cs
      ∨ ∃ j, j < n ∧
          d < (disagree (committedNext enc S H (fsChain enc S H j cs))
                (prescribedFold enc S fold H (fsChain enc S H j cs))).card ∧
          ((Finset.univ.filter (fun Q : Fin k → ι =>
                Accepts (committedNext enc S H (fsChain enc S H j cs))
                  (prescribedFold enc S fold H (fsChain enc S H j cs)) Q)).card : ℝ)
              / ((Fintype.card ι : ℝ) ^ k)
            ≤ (1 - δ) ^ k := by
  by_cases hclose : FoldCloseAlong enc S fold H d n cs
  · exact Or.inl hclose
  · obtain ⟨j, hj, hcard⟩ := exists_deviating_round enc S fold H d n cs hclose
    refine Or.inr ⟨j, hj, hcard, accept_prob_le k hι hδ0 ?_⟩
    calc δ * (Fintype.card ι : ℝ) ≤ (d : ℝ) := hδd
      _ < _ := by exact_mod_cast hcard

/-- **⚑ WHY THE GATE HAD TO BE GRADED** — the EXACT gate is not spot-checkable. At `d = 0` the
dichotomy's side condition `δ·|ι| ≤ 0` forces `δ ≤ 0` (for a nonempty domain), so the payment
`(1−δ)^k` is at least `1`: the caught branch pays NOTHING. A prover that deviates from the fold
at a single point is invisible to `k` spot checks with probability `(1 − 1/|ι|)^k`, and that is a
fact about the protocol, not about this formalization. Hence `FoldCloseAlong d` for `d > 0` is
the strongest gate the query phase can enforce, and the farness chain must be made to tolerate
it — which is §4. -/
theorem exact_gate_pays_nothing {δ : ℝ} (k : ℕ) (hι : 0 < Fintype.card ι)
    (hδ0 : 0 ≤ δ) (hδd : δ * (Fintype.card ι : ℝ) ≤ ((0 : ℕ) : ℝ)) :
    (1 : ℝ) ≤ (1 - δ) ^ k := by
  have hc : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hι
  have hδ : δ ≤ 0 := by
    by_contra hnot
    have hpos : (0 : ℝ) < δ := not_le.mp hnot
    have hmul : (0 : ℝ) < δ * (Fintype.card ι : ℝ) := mul_pos hpos hc
    push_cast at hδd
    linarith
  have hδ0' : δ = 0 := le_antisymm hδ hδ0
  simp [hδ0']

/-! ## §4 — the farness chain, made to TOLERATE the slack the query phase enforces. -/

/-- **`ChainStepSlack` — the per-round distance obligation the SLACKENED chain consumes.** "A far
word folded at a challenge outside its good set stays far, and so does anything within `d` of
that fold." At `d = 0` it is exactly `FriAdversaryObject.ChainStep`
(`chainStepSlack_zero_iff_chainStep`). It is not assumed anywhere below: every use is discharged
either by `chainStepSlack_of_gap` (from the named `ChainStepGap`) or, at the §7 instance,
directly. -/
def ChainStepSlack (far : (ι → F) → Prop) (goodSet : (ι → F) → Finset R)
    (fold : (ι → F) → R → (ι → F)) (d : ℕ) : Prop :=
  ∀ (w w' : ι → F) (ρ : R), far w → ρ ∉ goodSet w →
    (disagree w' (fold w ρ)).card ≤ d → far w'

/-- `ChainStepSlack` at zero slack is `ChainStep` — the grading is conservative. -/
theorem chainStepSlack_zero_iff_chainStep (far : (ι → F) → Prop)
    (goodSet : (ι → F) → Finset R) (fold : (ι → F) → R → (ι → F)) :
    ChainStepSlack far goodSet fold 0 ↔ ChainStep far goodSet fold := by
  constructor
  · intro h w ρ hfar hgood
    exact h w (fold w ρ) ρ hfar hgood (by simp [disagree_eq_empty_iff])
  · intro h w w' ρ hfar hgood hd
    have : w' = fold w ρ := by
      apply disagree_eq_empty_iff.mp
      rw [← Finset.card_eq_zero]; omega
    rw [this]
    exact h w ρ hfar hgood

/-- **⚑ THE ONE NAMED OBLIGATION — `ChainStepGap`.** The per-round distance-preservation
obligation WITH A MARGIN: a word `rad`-far from the code, folded at a challenge outside its good
set, is `(rad + d)`-far. Same species as `FriAdversaryObject.ChainStep` (a `def`, instances are
ladder stage L2), and literally `ChainStep` at `d = 0`. It is the honest price of the §3 finding:
because spot checks can only enforce `d`-closeness, the fold analysis must leave `d` of room.

⚑ The deployed cap machinery already yields margins of this shape — `FriChainStepIdx.goodδ_card_lt`
says a word not `n²·d`-close to `C` has fewer than `n` challenges folding it `d`-close to `C'`, so
instantiating its good set at radius `d + d'` gives the `d'`-margin outright. Welding that in
needs the shrinking-domain tower this file's fixed-`C` shape (shared with
`chain_far_survival_strategy`) cannot see, which is the gap `FriChainStepIdx`'s header already
reports as "No welded setup TOWER". -/
def ChainStepGap (C : Submodule F (ι → F)) (rad d : ℕ) (goodSet : (ι → F) → Finset R)
    (fold : (ι → F) → R → (ι → F)) : Prop :=
  ∀ (w : ι → F) (ρ : R), farN C rad w → ρ ∉ goodSet w → farN C (rad + d) (fold w ρ)

/-- At zero margin the named obligation is the landed one. -/
theorem chainStepGap_zero_iff_chainStep (C : Submodule F (ι → F)) (rad : ℕ)
    (goodSet : (ι → F) → Finset R) (fold : (ι → F) → R → (ι → F)) :
    ChainStepGap C rad 0 goodSet fold ↔ ChainStep (farN C rad) goodSet fold := by
  simp [ChainStepGap, ChainStep]

/-- **The named obligation DISCHARGES the chain's hypothesis** — a theorem, not an assumption.
If the fold preserves farness with a `d`-margin, then everything within `d` of the fold is still
`rad`-far: by the Hamming triangle inequality (`FriLdtJohnson.hamming_triangle`), a codeword
`rad`-close to the perturbed word would be `(rad + d)`-close to the fold itself, contradicting
the margin. -/
theorem chainStepSlack_of_gap {C : Submodule F (ι → F)} {rad d : ℕ}
    {goodSet : (ι → F) → Finset R} {fold : (ι → F) → R → (ι → F)}
    (hgap : ChainStepGap C rad d goodSet fold) :
    ChainStepSlack (farN C rad) goodSet fold d := by
  intro w w' ρ hfar hgood hd hclose
  obtain ⟨g, hgC, hgcard⟩ := hclose
  refine hgap w ρ hfar hgood ⟨g, hgC, ?_⟩
  calc (disagree (fold w ρ) g).card
      ≤ (disagree (fold w ρ) w').card + (disagree w' g).card := hamming_triangle _ _ _
    _ ≤ d + rad := by
        refine Nat.add_le_add ?_ hgcard
        rw [disagree_symm]
        exact hd
    _ = rad + d := Nat.add_comm _ _

/-- **⚑ FARNESS SURVIVES THE CHAIN UNDER THE SLACKENED GATE.** The exact shape of
`FriAdversaryObject.chain_far_strategy_of_farCover`, with `FoldConsistentAlong` replaced by
`FoldCloseAlong d` and `ChainStep` by `ChainStepSlack _ _ _ d`. Same induction; the one new step
is that the prover's committed word is only `d`-close to the fold, which is exactly what
`ChainStepSlack` absorbs. This is the branch the dichotomy's LEFT disjunct feeds. -/
theorem chain_far_slack_of_farCover {far : (ι → F) → Prop} {goodSet : (ι → F) → Finset R}
    {fold : (ι → F) → R → (ι → F)} {d : ℕ} (hslack : ChainStepSlack far goodSet fold d)
    (enc : (ι → F) → List R → D) (E : D → Finset R) (S : Strategy R (ι → F))
    (hcover : ∀ (w : ι → F) (cs : List R), far w → goodSet w ⊆ E (enc w cs))
    (H : D → R) :
    ∀ (n : ℕ) (cs : List R),
      far (S cs) →
      AvoidsBad enc S E H n cs →
      FoldCloseAlong enc S fold H d n cs →
      far (S (fsChain enc S H n cs)) := by
  intro n
  induction n with
  | zero => intro cs hfar _ _; simpa [fsChain] using hfar
  | succ n ih =>
      intro cs hfar havoid hclose
      simp only [AvoidsBad] at havoid
      rw [foldCloseAlong_succ] at hclose
      obtain ⟨hnotE, htail⟩ := havoid
      obtain ⟨hcard, hclostail⟩ := hclose
      have hnotGood : chalAt enc S H cs ∉ goodSet (S cs) :=
        fun hmem => hnotE (hcover _ _ hfar hmem)
      have hfar' : far (S (stepPrefix enc S H cs)) :=
        hslack (S cs) (committedNext enc S H cs) (chalAt enc S H cs) hfar hnotGood hcard
      exact ih (stepPrefix enc S H cs) hfar' htail hclostail

/-- **⚑ THE SLACKENED SURVIVAL BOUND, PRICED.** `FriChainStepIdx.chain_far_survival_strategy`
with the graded gate: for an arbitrary strategy, any boolean event implying "`S` was `d`-fold-
close along the path AND the terminal commitment is NOT far" has probability `≤ n·b/|R|`. Recipe
unchanged — `fsRun_queryBounded` + `hit_bound` + `chain_far_slack_of_farCover`, glued by
`hitWin_fsRun_true_iff`. At `d = 0` this IS `chain_far_survival_strategy`
(`foldCloseAlong_zero_iff_consistent`). -/
theorem chain_far_survival_slack [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]
    [Nonempty R] {far : (ι → F) → Prop} {goodSet : (ι → F) → Finset R}
    {fold : (ι → F) → R → (ι → F)} {d : ℕ} (hslack : ChainStepSlack far goodSet fold d)
    (enc : (ι → F) → List R → D) (E : D → Finset R) {b : ℕ} (hE : ∀ dd, (E dd).card ≤ b)
    (S : Strategy R (ι → F))
    (hcover : ∀ (w : ι → F) (cs : List R), far w → goodSet w ⊆ E (enc w cs))
    (hfar0 : far (S [])) (n : ℕ) {bad : (D → R) → Bool}
    (hbad : ∀ H : D → R, bad H = true →
      FoldCloseAlong enc S fold H d n [] ∧ ¬ far (S (fsChain enc S H n []))) :
    winProb bad ≤ ((n : ℝ) * (b : ℝ)) / (Fintype.card R : ℝ) := by
  have himp : ∀ H : D → R, bad H = true → hitWin E (fsRun enc S n []) H = true := by
    intro H hH
    obtain ⟨hclose, hnotfar⟩ := hbad H hH
    by_contra hnot
    have havoid : AvoidsBad enc S E H n [] := by
      by_contra hav
      exact hnot ((hitWin_fsRun_true_iff enc S E H n []).mpr hav)
    exact hnotfar (chain_far_slack_of_farCover hslack enc E S hcover H n [] hfar0 havoid hclose)
  exact (winProb_le_of_imp himp).trans (hit_bound _ (fsRun_queryBounded enc S n []) E hE)

open Classical in
/-- The GATED reading of the slackened bound — the form the composition consumes. -/
theorem chain_far_survival_slack_gated [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]
    [Nonempty R] {far : (ι → F) → Prop} {goodSet : (ι → F) → Finset R}
    {fold : (ι → F) → R → (ι → F)} {d : ℕ} (hslack : ChainStepSlack far goodSet fold d)
    (enc : (ι → F) → List R → D) (E : D → Finset R) {b : ℕ} (hE : ∀ dd, (E dd).card ≤ b)
    (S : Strategy R (ι → F))
    (hcover : ∀ (w : ι → F) (cs : List R), far w → goodSet w ⊆ E (enc w cs))
    (hfar0 : far (S [])) (n : ℕ) {bad : (D → R) → Bool}
    (hbad : ∀ H : D → R, bad H = true → ¬ far (S (fsChain enc S H n []))) :
    winProb (fun H : D → R => bad H && decide (FoldCloseAlong enc S fold H d n []))
      ≤ ((n : ℝ) * (b : ℝ)) / (Fintype.card R : ℝ) := by
  refine chain_far_survival_slack hslack enc E hE S hcover hfar0 n ?_
  intro H hH
  rw [Bool.and_eq_true] at hH
  exact ⟨of_decide_eq_true hH.2, hbad H hH.1⟩

/-! ## §5 — the QUERY PHASE as an event on the walked path. -/

/-- **The verifier's fold-consistency spot check, along the whole path.** At every round the
`k`-point sample `Q` is opened on the committed word and on the fold it was supposed to be, and
must agree. `Bool`-valued so it is an event without decidability side conditions. -/
def queryPassesAlong (enc : (ι → F) → List R → D) (S : Strategy R (ι → F))
    (fold : (ι → F) → R → (ι → F)) (H : D → R) {k : ℕ} (Q : Fin k → ι) :
    ℕ → List R → Bool
  | 0, _ => true
  | n + 1, cs =>
      decide (Accepts (committedNext enc S H cs) (prescribedFold enc S fold H cs) Q)
        && queryPassesAlong enc S fold H Q n (stepPrefix enc S H cs)

/-- Passing the whole path means passing at every round on it. -/
theorem accepts_of_queryPassesAlong (enc : (ι → F) → List R → D) (S : Strategy R (ι → F))
    (fold : (ι → F) → R → (ι → F)) (H : D → R) {k : ℕ} (Q : Fin k → ι) :
    ∀ (n : ℕ) (cs : List R), queryPassesAlong enc S fold H Q n cs = true →
      ∀ j, j < n →
        Accepts (committedNext enc S H (fsChain enc S H j cs))
          (prescribedFold enc S fold H (fsChain enc S H j cs)) Q := by
  intro n
  induction n with
  | zero => intro cs _ j hj; omega
  | succ n ih =>
      intro cs hpass j hj
      rw [queryPassesAlong, Bool.and_eq_true] at hpass
      match j, hj with
      | 0, _ => simpa [fsChain] using of_decide_eq_true hpass.1
      | (j + 1), hj =>
          have := ih (stepPrefix enc S H cs) hpass.2 j (by omega)
          simpa using this

open Classical in
/-- **⚑⚑ THE MISSING HALF, ON ITS OWN: A FOLD-INCONSISTENT PROVER IS CAUGHT BY THE QUERY PHASE.**
Over the joint randomness (random oracle × query sample), the probability that an ARBITRARY
strategy is NOT `d`-fold-close along the walked path AND still passes the verifier's
fold-consistency spot checks at every round is at most `(1−δ)^k`, for any `δ` with `δ·|ι| ≤ d`.

This is the branch `FriAdversaryObject:206-208`, `FriChainStepIdx:42-44` and
`CorrelatedAgreement/Interface.lean:123,831` name as unproved. Per oracle, the dichotomy
(`foldConsistent_or_query_paid`) names the deviating round; `accepts_of_queryPassesAlong` says
passing the path means passing THERE; `accept_prob_le` prices that round's fibre; the fibre bound
lifts to the joint event by `winProb_le_of_fiber`. Nothing is assumed. -/
theorem inconsistent_caught_by_query [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]
    (enc : (ι → F) → List R → D) (S : Strategy R (ι → F))
    (fold : (ι → F) → R → (ι → F)) (d n k : ℕ) {δ : ℝ}
    (hι : 0 < Fintype.card ι) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδd : δ * (Fintype.card ι : ℝ) ≤ (d : ℝ)) :
    winProb (fun ω : (D → R) × (Fin k → ι) =>
        (!decide (FoldCloseAlong enc S fold ω.1 d n []))
          && queryPassesAlong enc S fold ω.1 ω.2 n [])
      ≤ (1 - δ) ^ k := by
  have hβ : (0 : ℝ) ≤ (1 - δ) ^ k := pow_nonneg (by linarith) k
  refine winProb_le_of_fiber hβ _ ?_
  intro H
  show ((Finset.univ.filter (fun Q : Fin k → ι =>
      ((!decide (FoldCloseAlong enc S fold H d n []))
        && queryPassesAlong enc S fold H Q n []) = true)).card : ℝ)
    ≤ (1 - δ) ^ k * (Fintype.card (Fin k → ι) : ℝ)
  have hcardQ : (Fintype.card (Fin k → ι) : ℝ) = (Fintype.card ι : ℝ) ^ k := by
    rw [Fintype.card_fun]
    push_cast
    simp
  have hpos : (0 : ℝ) < (Fintype.card ι : ℝ) ^ k := by
    have hc : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hι
    positivity
  rw [hcardQ]
  by_cases hc : FoldCloseAlong enc S fold H d n []
  · have hz : (Finset.univ.filter (fun Q : Fin k → ι =>
        ((!decide (FoldCloseAlong enc S fold H d n []))
          && queryPassesAlong enc S fold H Q n []) = true)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro Q _
      simp [hc]
    rw [hz, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hβ (le_of_lt hpos)
  · obtain ⟨j, hj, _, hmass⟩ :=
      (foldConsistent_or_query_paid enc S fold H d k hι hδ0 hδd n []).resolve_left hc
    have hsub : (Finset.univ.filter (fun Q : Fin k → ι =>
        ((!decide (FoldCloseAlong enc S fold H d n []))
          && queryPassesAlong enc S fold H Q n []) = true))
        ⊆ (Finset.univ.filter (fun Q : Fin k → ι =>
            Accepts (committedNext enc S H (fsChain enc S H j []))
              (prescribedFold enc S fold H (fsChain enc S H j [])) Q)) := by
      intro Q hQ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true] at hQ ⊢
      exact accepts_of_queryPassesAlong enc S fold H Q n [] hQ.2 j hj
    have hcard : ((Finset.univ.filter (fun Q : Fin k → ι =>
        ((!decide (FoldCloseAlong enc S fold H d n []))
          && queryPassesAlong enc S fold H Q n []) = true)).card : ℝ)
        ≤ ((Finset.univ.filter (fun Q : Fin k → ι =>
            Accepts (committedNext enc S H (fsChain enc S H j []))
              (prescribedFold enc S fold H (fsChain enc S H j [])) Q)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact hcard.trans ((div_le_iff₀ hpos).mp hmass)

/-! ## §6 — ⚑⚑ THE COMPOSITION: one statement about an ARBITRARY strategy. -/

open Classical in
/-- **⚑⚑ STRATEGY-QUANTIFIED SOUNDNESS, BOTH BRANCHES, ONE BOUND.** For an ARBITRARY prover
strategy `S` — with NO fold-consistency gate anywhere in the statement — the probability, over
the random oracle AND the query sample jointly, that `S` both defeats farness and passes the
verifier's fold-consistency spot checks at every round is at most

    n·b/|R|   (the FS challenge branch)   +   (1−δ)^k   (the query branch).

The dichotomy `foldConsistent_or_query_paid` splits the joint event: on oracles where `S` is
`d`-fold-close the first addend pays (`chain_far_survival_slack_gated`, lifted to the product
space by `winProb_fst`); on oracles where it is not, the deviating round's spot check bounds the
query fibre by `(1−δ)^k` (`winProb_le_of_fiber`). `winProb_le_add` unions them.

⚑ THIS is what makes the `∀ S` of `chain_far_survival_strategy` / `ud_tower_far_survival_strategy`
mean something: those price a gated event and are silent on the complement — and
`consistencyFreeSurvival_false` proves the complement is where a prover wins with probability 1.
Here the complement is priced, so the bound is over ALL strategies. What it is NOT: a statement
about the deployed verifier's actual query pattern (`queryPassesAlong` is the fold-consistency
check as an event over a uniform `k`-sample, the same idealization `FriQuerySoundness` and
`DeployedTraceExtract` already run on — `FriQuerySamplingBias` records that the deployed sampler
is biased), and it inherits the single named `ChainStepGap` through `hslack`. -/
theorem strategy_soundness_compose [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]
    [Nonempty R] {far : (ι → F) → Prop} {goodSet : (ι → F) → Finset R}
    {fold : (ι → F) → R → (ι → F)} {d : ℕ} (hslack : ChainStepSlack far goodSet fold d)
    (enc : (ι → F) → List R → D) (E : D → Finset R) {b : ℕ} (hE : ∀ dd, (E dd).card ≤ b)
    (S : Strategy R (ι → F))
    (hcover : ∀ (w : ι → F) (cs : List R), far w → goodSet w ⊆ E (enc w cs))
    (hfar0 : far (S [])) (n k : ℕ) {δ : ℝ}
    (hι : 0 < Fintype.card ι) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδd : δ * (Fintype.card ι : ℝ) ≤ (d : ℝ))
    {bad : (D → R) → Bool}
    (hbad : ∀ H : D → R, bad H = true → ¬ far (S (fsChain enc S H n []))) :
    winProb (fun ω : (D → R) × (Fin k → ι) =>
        bad ω.1 && queryPassesAlong enc S fold ω.1 ω.2 n [])
      ≤ ((n : ℝ) * (b : ℝ)) / (Fintype.card R : ℝ) + (1 - δ) ^ k := by
  have hιne : Nonempty ι := Fintype.card_pos_iff.mp hι
  have hQne : Nonempty (Fin k → ι) := ⟨fun _ => Classical.arbitrary ι⟩
  refine le_trans (winProb_le_add
      (f := fun ω : (D → R) × (Fin k → ι) =>
        bad ω.1 && queryPassesAlong enc S fold ω.1 ω.2 n [])
      (g := fun ω : (D → R) × (Fin k → ι) =>
        bad ω.1 && decide (FoldCloseAlong enc S fold ω.1 d n []))
      (h := fun ω : (D → R) × (Fin k → ι) =>
        (!decide (FoldCloseAlong enc S fold ω.1 d n []))
          && queryPassesAlong enc S fold ω.1 ω.2 n []) ?_) ?_
  · -- The joint event is covered by the two branches.
    intro ω hω
    rw [Bool.and_eq_true] at hω
    by_cases hc : FoldCloseAlong enc S fold ω.1 d n []
    · exact Or.inl (by simp [hω.1, hc])
    · exact Or.inr (by simp [hc, hω.2])
  refine add_le_add ?_ ?_
  · -- BRANCH 1: the gated survival bound, lifted off the query coordinate.
    rw [winProb_fst (Ω₂ := Fin k → ι)
      (fun H : D → R => bad H && decide (FoldCloseAlong enc S fold H d n []))]
    exact chain_far_survival_slack_gated hslack enc E hE S hcover hfar0 n hbad
  · -- BRANCH 2: the missing half, proved on its own above.
    exact inconsistent_caught_by_query enc S fold d n k hι hδ0 hδ1 hδd

/-! ## §7 — ⚑ NON-VACUITY: one strategy, both branches, and the hole visibly plugged.

`halfDeviator` deviates from the fold on HALF a four-point domain. That is enough to leave
farness with certainty — so `chain_far_survival_strategy` is SILENT about it, which is exactly
the hole this file exists to fill — and few enough that a query sample can miss the deviation, so
the caught branch is a genuine probability rather than a certainty. -/

section Teeth

open Dregg2.Crypto.ProbCrypto (winProb winProb_top)

/-- The all-zero word — the "codeword" the deviating prover slides toward. -/
def wZero : Fin 4 → ZMod 5 := ![0, 0, 0, 0]

/-- The all-ones word: full support, the fold's constant image. -/
def wOne : Fin 4 → ZMod 5 := ![1, 1, 1, 1]

/-- The deviator's round-1 commitment: agrees with the prescribed fold on HALF the domain. -/
def wHalf : Fin 4 → ZMod 5 := ![0, 0, 1, 1]

/-- Farness = support at least `3`. `wOne` is far; `wHalf` is not. -/
def farW (w : Fin 4 → ZMod 5) : Prop := 3 ≤ (disagree w wZero).card

/-- The fold is the constant map to the full-support word — the most farness-preserving fold
there is (its image has support `4`, a margin of `1` over the farness threshold `3`). -/
def foldOne : (Fin 4 → ZMod 5) → Bool → (Fin 4 → ZMod 5) := fun _ _ => wOne

/-- Empty good sets. -/
def goodW : (Fin 4 → ZMod 5) → Finset Bool := fun _ => ∅

/-- One query point; the canary needs no transcript structure. -/
def encW : (Fin 4 → ZMod 5) → List Bool → Unit := fun _ _ => ()

/-- Empty bad sets: the cap is `b = 0`, so the FS branch of the composed bound is `0`. -/
def EW : Unit → Finset Bool := fun _ => ∅

/-- **THE DEVIATING PROVER.** At round `0` it shows the far `wOne`; from round `1` on it shows
`wHalf` — which is NOT the fold (`foldOne _ _ = wOne`) and is NOT far. The word-typed sibling of
`FriChainStepIdx.codewordCommit`, refined so that the deviation is PARTIAL: the query phase can
miss it. -/
def halfDeviator : Strategy Bool (Fin 4 → ZMod 5) :=
  fun cs => if cs.length = 0 then wOne else wHalf

theorem halfDeviator_nil : halfDeviator [] = wOne := rfl

theorem halfDeviator_cons (c : Bool) (cs : List Bool) : halfDeviator (c :: cs) = wHalf := rfl

theorem disagree_wOne_wZero : (disagree wOne wZero).card = 4 := by decide

theorem disagree_wHalf_wZero : (disagree wHalf wZero).card = 2 := by decide

theorem disagree_wHalf_wOne : (disagree wHalf wOne).card = 2 := by decide

/-- `wOne` is far. -/
theorem farW_wOne : farW wOne := by rw [farW, disagree_wOne_wZero]; omega

/-- `wHalf` is NOT far — the escape. -/
theorem not_farW_wHalf : ¬ farW wHalf := by rw [farW, disagree_wHalf_wZero]; omega

/-- **The slack obligation holds at slack `1`, by the Hamming triangle.** Anything within `1` of
`wOne` (support `4`) still has support `≥ 3`, hence is far. Discharged directly, so the §7
instance carries no hypothesis at all. -/
theorem chainStepSlack_W : ChainStepSlack farW goodW foldOne 1 := by
  intro w w' ρ _ _ hd
  rw [farW]
  have htri : (disagree wOne wZero).card
      ≤ (disagree wOne w').card + (disagree w' wZero).card := hamming_triangle _ _ _
  have h1 : (disagree wOne w').card ≤ 1 := by
    rw [disagree_symm]
    simpa [foldOne] using hd
  rw [disagree_wOne_wZero] at htri
  omega

/-- The cap `b = 0`. -/
theorem EW_card : ∀ dd, (EW dd).card ≤ 0 := by intro dd; simp [EW]

/-- The cover, trivially (empty good sets). -/
theorem cover_W : ∀ (w : Fin 4 → ZMod 5) (cs : List Bool),
    farW w → goodW w ⊆ EW (encW w cs) := by
  intro w cs _; simp [goodW, EW]

/-- The deviator starts far. -/
theorem halfDeviator_far0 : farW (halfDeviator []) := farW_wOne

/-- **⚑ THE ESCAPE IS DETERMINISTIC** — after one FS round the deviator's commitment is not far,
under EVERY oracle. So the farness-survival theorems, which price only the gated event, say
NOTHING about this prover. -/
theorem halfDeviator_escapes (H : Unit → Bool) :
    ¬ farW (halfDeviator (fsChain encW halfDeviator H 1 [])) := by
  simpa [fsChain, encW, halfDeviator_cons] using not_farW_wHalf

open Classical in
/-- **Probability EXACTLY 1.** The un-priced complement of the gate is where a prover wins with
certainty — the same fact `FriChainStepIdx.codewordCommit_escape_prob_one` records, restated on
the word-typed deviator this file then CATCHES. -/
theorem halfDeviator_escape_prob_one :
    winProb (fun H : Unit → Bool =>
        decide (¬ farW (halfDeviator (fsChain encW halfDeviator H 1 [])))) = 1 := by
  have hfun : (fun H : Unit → Bool =>
      decide (¬ farW (halfDeviator (fsChain encW halfDeviator H 1 []))))
      = (fun _ : Unit → Bool => true) :=
    funext fun H => decide_eq_true (halfDeviator_escapes H)
  rw [hfun, winProb_top]

/-- The deviator is NOT `1`-fold-close at round `1`: its committed `wHalf` disagrees with the
prescribed `wOne` on `2 > 1` points. -/
theorem halfDeviator_not_foldClose (H : Unit → Bool) :
    ¬ FoldCloseAlong encW halfDeviator foldOne H 1 1 [] := by
  intro hc
  rw [foldCloseAlong_succ] at hc
  have h1 := hc.1
  rw [show committedNext encW halfDeviator H [] = wHalf from rfl,
    show prescribedFold encW halfDeviator foldOne H [] = wOne from rfl,
    disagree_wHalf_wOne] at h1
  omega

/-- **⚑ BRANCH 2 FIRES.** On the deviating prover the dichotomy takes its RIGHT disjunct: at
`δ = 1/4`, `d = 1`, `|ι| = 4` (so `δ·|ι| = 1 ≤ d`) there is a round `j < 1` whose deviation
exceeds `1` and whose `k`-query fold check passes with mass at most `(3/4)^k`. -/
theorem halfDeviator_dichotomy_right (H : Unit → Bool) (k : ℕ) :
    ∃ j, j < 1 ∧
      1 < (disagree (committedNext encW halfDeviator H (fsChain encW halfDeviator H j []))
            (prescribedFold encW halfDeviator foldOne H (fsChain encW halfDeviator H j []))).card ∧
      ((Finset.univ.filter (fun Q : Fin k → Fin 4 =>
            Accepts (committedNext encW halfDeviator H (fsChain encW halfDeviator H j []))
              (prescribedFold encW halfDeviator foldOne H
                (fsChain encW halfDeviator H j [])) Q)).card : ℝ)
          / ((Fintype.card (Fin 4) : ℝ) ^ k)
        ≤ (1 - (1 / 4 : ℝ)) ^ k := by
  refine (foldConsistent_or_query_paid encW halfDeviator foldOne H 1 k
      (δ := (1 / 4 : ℝ)) (by decide) (by norm_num) ?_ 1 []).resolve_left
    (halfDeviator_not_foldClose H)
  rw [show (Fintype.card (Fin 4) : ℝ) = 4 by simp]
  norm_num

/-- **⚑ BRANCH 1 FIRES, at the very same instance.** The honest prover over the SAME fold and
domain takes the dichotomy's LEFT disjunct — so the dichotomy is not one-sided, and the caught
branch is not an artifact of the setup. -/
theorem honestW_dichotomy_left (H : Unit → Bool) :
    FoldCloseAlong encW (honestStrategy foldOne wOne) foldOne H 1 1 [] :=
  honest_foldCloseAlong encW foldOne wOne H 1 1 []

/-- **COMPLETENESS at the same instance**: the honest prover passes the fold-consistency spot
check on EVERY sample, so the caught branch never fires for it. Its committed word and the
prescribed fold are literally the same word. -/
theorem honestW_query_passes (H : Unit → Bool) (Q : Fin 3 → Fin 4) :
    queryPassesAlong encW (honestStrategy foldOne wOne) foldOne H Q 1 [] = true := by
  have h1 : committedNext encW (honestStrategy foldOne wOne) H [] = wOne := rfl
  have h2 : prescribedFold encW (honestStrategy foldOne wOne) foldOne H [] = wOne := rfl
  rw [queryPassesAlong, h1, h2]
  simp [queryPassesAlong, Accepts]

/-- **The caught branch is a REAL probability, not a certainty.** A three-query sample that only
ever lands on `2` — where `wHalf` and `wOne` agree — passes the deviator's fold check. So the
`(3/4)^k` bound is bounding a NON-EMPTY event, and soundness here is genuinely probabilistic
(the same polarity `FriQuerySoundness.far_accepted_by_missing_query` records for the far-oracle
check). -/
theorem halfDeviator_query_event_nonempty (H : Unit → Bool) :
    queryPassesAlong encW halfDeviator foldOne H (![2, 2, 2] : Fin 3 → Fin 4) 1 [] = true := by
  have h1 : committedNext encW halfDeviator H [] = wHalf := rfl
  have h2 : prescribedFold encW halfDeviator foldOne H [] = wOne := rfl
  rw [queryPassesAlong, h1, h2]
  simp only [queryPassesAlong, Bool.and_true, decide_eq_true_eq]
  decide

open Classical in
/-- **⚑ THE MISSING HALF, FIRED ON ITS OWN.** `inconsistent_caught_by_query` at the deviator:
the joint probability that it is fold-INCONSISTENT and still passes every fold-consistency spot
check is at most `(3/4)^3 = 27/64`. This is the branch that did not exist in the tree. -/
theorem halfDeviator_caught_bound :
    winProb (fun ω : (Unit → Bool) × (Fin 3 → Fin 4) =>
        (!decide (FoldCloseAlong encW halfDeviator foldOne ω.1 1 1 []))
          && queryPassesAlong encW halfDeviator foldOne ω.1 ω.2 1 [])
      ≤ (1 - (1 / 4 : ℝ)) ^ 3 := by
  have hι : 0 < Fintype.card (Fin 4) := by simp
  have hδd : (1 / 4 : ℝ) * (Fintype.card (Fin 4) : ℝ) ≤ ((1 : ℕ) : ℝ) := by
    rw [show (Fintype.card (Fin 4) : ℝ) = 4 by simp]
    norm_num
  exact inconsistent_caught_by_query encW halfDeviator foldOne 1 1 3 hι (by norm_num)
    (by norm_num) hδd

open Classical in
/-- **The caught event is NON-EMPTY** — the deviator IS fold-inconsistent (`!decide … = true`)
and there is a sample that still passes. So `halfDeviator_caught_bound` bounds a probability
strictly between `0` and `1`; it is not a vacuous `≤ 1` over an empty event. -/
theorem halfDeviator_caught_event_nonempty :
    ∃ ω : (Unit → Bool) × (Fin 3 → Fin 4),
      ((!decide (FoldCloseAlong encW halfDeviator foldOne ω.1 1 1 []))
        && queryPassesAlong encW halfDeviator foldOne ω.1 ω.2 1 []) = true := by
  refine ⟨(fun _ => true, ![2, 2, 2]), ?_⟩
  have hnc := halfDeviator_not_foldClose (fun _ : Unit => true)
  simp [hnc, halfDeviator_query_event_nonempty]

set_option maxHeartbeats 1000000 in
/-- **⚑⚑ THE COMPOSITION FIRES.** The deviator defeats farness with probability `1`
(`halfDeviator_escape_prob_one`), and the composed theorem still bounds it: the joint probability
that it defeats farness AND passes the fold-consistency spot checks is at most
`1·0/2 + (3/4)^3 = 27/64`. The gate-free `∀ S` statement therefore has teeth on exactly the
prover the gate excludes. -/
theorem halfDeviator_composed :
    winProb (fun ω : (Unit → Bool) × (Fin 3 → Fin 4) =>
        (fun _ : Unit → Bool => true) ω.1
          && queryPassesAlong encW halfDeviator foldOne ω.1 ω.2 1 [])
      ≤ ((1 : ℕ) : ℝ) * ((0 : ℕ) : ℝ) / (Fintype.card Bool : ℝ) + (1 - (1 / 4 : ℝ)) ^ 3 := by
  have hι : 0 < Fintype.card (Fin 4) := by simp
  have hδd : (1 / 4 : ℝ) * (Fintype.card (Fin 4) : ℝ) ≤ ((1 : ℕ) : ℝ) := by
    rw [show (Fintype.card (Fin 4) : ℝ) = 4 by simp]
    norm_num
  exact strategy_soundness_compose (d := 1) (bad := fun _ => true) chainStepSlack_W encW EW
    EW_card halfDeviator cover_W halfDeviator_far0 1 3 (δ := (1 / 4 : ℝ)) hι (by norm_num)
    (by norm_num) hδd (fun H _ => halfDeviator_escapes H)

/-- **The composed event is NON-EMPTY too** — so `halfDeviator_composed`'s `27/64` is a real
probability, not a bound over nothing. -/
theorem halfDeviator_composed_event_nonempty :
    ∃ ω : (Unit → Bool) × (Fin 3 → Fin 4),
      ((fun _ : Unit → Bool => true) ω.1
        && queryPassesAlong encW halfDeviator foldOne ω.1 ω.2 1 []) = true :=
  ⟨(fun _ => true, ![2, 2, 2]), by simpa using halfDeviator_query_event_nonempty (fun _ => true)⟩

/-- The composed bound is genuinely sub-`1` — unlike anything the exact gate can produce
(`exact_gate_pays_nothing`). -/
theorem halfDeviator_composed_lt_one :
    ((1 : ℕ) : ℝ) * ((0 : ℕ) : ℝ) / (Fintype.card Bool : ℝ) + (1 - (1 / 4 : ℝ)) ^ 3 < 1 := by
  rw [show (Fintype.card Bool : ℝ) = 2 by simp]
  norm_num

end Teeth

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  winProb_le_add,
  winProb_fst,
  winProb_le_of_fiber,
  foldCloseAlong_zero_iff_consistent,
  foldCloseAlong_mono,
  honest_foldCloseAlong,
  exists_deviating_round,
  foldConsistent_or_query_paid,
  exact_gate_pays_nothing,
  chainStepSlack_zero_iff_chainStep,
  chainStepGap_zero_iff_chainStep,
  chainStepSlack_of_gap,
  chain_far_slack_of_farCover,
  chain_far_survival_slack,
  chain_far_survival_slack_gated,
  accepts_of_queryPassesAlong,
  inconsistent_caught_by_query,
  strategy_soundness_compose,
  chainStepSlack_W,
  halfDeviator_escapes,
  halfDeviator_escape_prob_one,
  halfDeviator_not_foldClose,
  halfDeviator_dichotomy_right,
  honestW_dichotomy_left,
  honestW_query_passes,
  halfDeviator_query_event_nonempty,
  halfDeviator_caught_bound,
  halfDeviator_caught_event_nonempty,
  halfDeviator_composed,
  halfDeviator_composed_event_nonempty,
  halfDeviator_composed_lt_one
]

end Dregg2.Circuit.FriFoldConsistencyDichotomy
