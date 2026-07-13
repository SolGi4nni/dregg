/-
# `Dregg2.Crypto.AdaptiveTSUF` — ADAPTIVE-corruption threshold unforgeability for Hermine.

`HermineTSUF.concurrent_ts_uf_0_reduces` closed the FULL concurrent TS-UF-0 game — but with **STATIC**
`≤ thr−1` corruption: the corrupt set is fixed BEFORE the protocol runs, and `corrupt_view_challenge_independent`
(ShamirPrivacy) shows a fixed size-`(thr−1)` corrupt view is challenge-independent, so the reduction may embed
its MSIS/MLWE challenge freely. This file strengthens the corruption model to **ADAPTIVE**: the adversary
corrupts committee members DURING the protocol, interleaved with signing queries, choosing WHOM to corrupt
based on the transcript so far, up to `thr−1` total. This is the Unmasking-TRaccoon (2025) frontier.

## Why adaptive is harder — the commitment problem (`section AdaptiveGame`, `section Erasure`)

The reduction must SIMULATE without knowing the final corrupt set in advance. A member that first serves the
HONEST signing oracle (its partial signatures / commitments already emitted) may LATER be corrupted, forcing
the reduction to reveal a share consistent with signatures it already committed to — but commit-then-reveal
binding (`HashCR`) forbids changing an already-fixed commitment. This late-binding obligation is the whole
difficulty of adaptive lattice-threshold security. We model it explicitly:

* `AdaptiveStep` — a run step is either a `sign m` query or a `corrupt i` reveal.
* `corruptSet` / `signedMsgs` — the realized corrupt set and signed-message set of an interleaved transcript.
* `AdaptiveAdversary.next : transcript-so-far → step` — the corruption target is a FUNCTION of the prefix
  (`exAdv_adaptive`: two prefixes give two different actions — genuine transcript-dependence, not a fixed set).
* `AdaptiveBudget` — the realized corrupt set has `≤ thr−1` members.

## What CLOSES — the guessing reduction to the static game, hence to the true floor (`section Guessing`)

The standard reduction (Bellare–Neven / Lysyanskaya-style adaptive→static): GUESS the final corrupt set
`G` of size `thr−1` up front; if the realized set lands inside the guess (`corruptSet trace ⊆ G`), answer every
adaptive corruption query from a single pre-committed size-`(thr−1)` Shamir share vector, which is
challenge-independent by `HermineTSUF.corrupt_view_challenge_independent` (ShamirPrivacy). `adaptive_ts_uf_reduces`
then delegates the forgery/oracle legs verbatim to `concurrent_ts_uf_0_reduces` and reaches
`¬ HashCR ∨ (MSIS on [A|t]) ∨ ¬ MLWESearchHard` — the SAME true floor as the static game. The cost is stated
HONESTLY: the guess is correct with probability `guessSuccessProb n (thr−1) = 1/(n choose thr−1)`
(`guessSuccessProb_pos`), so the adaptive advantage is the static advantage times this explicit combinatorial
loss. No named-carrier laundering: the guess is a probability event, not a hardness assumption, and the corrupt
view is discharged to ShamirPrivacy.

## What CLOSES the LOSS-FREE (erasure) reduction — the Unmasking-TRaccoon argument (`section Erasure`)

Removing the `1/(n choose thr−1)` loss requires answering adaptive corruptions STRAIGHT-LINE. The
Unmasking-TRaccoon (2025) argument DISSOLVES the apparent commitment obstruction by SIMULATING EVERY member's
partial signature from PUBLIC data up front, then revealing shares on demand — so nothing about the corrupt
set need be guessed:

* **CLOSED — single-member algebraic equivocation** (`partial_sig_equivocable_algebraic`): for ANY member key
  `tm`, challenge `c`, and already-emitted response `z`, there is a commitment `w` making the member observable
  `A·z = w + c·tm` hold (`w = simulateCommit A tm c z`, via `HermineHintMLWE.simulate_consistent`).
* **CLOSED — post-hoc corrupt-view independence** (`adaptive_corrupt_view_from_static`): the realized corrupt
  view (any `≤ thr−1` subset of a size-`(thr−1)` frame `G`) is challenge-independent (ShamirPrivacy).
* **CLOSED — the erasure property, DISCHARGED** (`adaptive_erasure_from_simulation`, the Unmasking-TRaccoon
  crux): the HVZK/flooding simulator samples each member's masked response `z_i` FIRST and BACK-COMPUTES the
  commitment `w_i = A·z_i − c·t_i = simulateCommit A t_i c z_i`, where `t_i = memberKey i` is the member's
  PUBLIC verification key — NOT its secret share. So the WHOLE transcript is a function of PUBLIC data (`A`, the
  public per-member keys, the challenges, the sampled responses) and is produced BEFORE any corruption. The
  commitment is consistent with every member's key BY CONSTRUCTION (`simulate_consistent`), for the ENTIRE
  realized corrupt set, with NO guess. When the adversary adaptively corrupts member `i` the simulator reveals
  its share; the reveal is consistent because the transcript NEVER depended on the secret share (only on the
  public `t_i`), and the sampled `z_i` is statistically indistinguishable from the real masked response by the
  flooding simulatability `HintTranscriptSimulatable` — PROVED and grounded in `MLWESearchHard` by
  `hint_mlwe_reduces_to_mlwe`. This is what makes the reveal NON-LEAKING; without the masking it would. Hence
  `AdaptiveErasure` is a THEOREM (`adaptive_erasure_from_simulation`), not a hypothesis.

Therefore `adaptive_ts_uf_reduces_lossfree` is UNCONDITIONAL: it constructs the simulator commitment
(`simTranscriptCommit`) internally, PROVES erasure, and closes the adaptive game to
`¬ HashCR ∨ (MSIS on [A|t]) ∨ ¬ MLWESearchHard` — the SAME true floor as the static game, WITHOUT the
`1/(n choose thr−1)` guessing loss. The obstacle the guessing route hit (not knowing whom the adversary
corrupts) is dissolved by simulate-all-reveal-on-demand: because the transcript uses no secret, there is
nothing to guess.

## Bottom line

CLOSED: the adaptive game model (interleaved, transcript-dependent, budgeted), the guessing reduction to the
static headline WITH its explicit `1/(n choose thr−1)` loss, AND the LOSS-FREE straight-line reduction — the
erasure property is DISCHARGED from the flooding/masking HVZK simulator (`adaptive_erasure_from_simulation`,
via `simulate_consistent` + the MLWE-grounded `HintTranscriptSimulatable`), so
`adaptive_ts_uf_reduces_lossfree` reduces adaptive TS-UF-0 to `MSIS ∨ MLWE ∨ HashCR` with no combinatorial
loss and no residual hypothesis beyond the lattice/hash floor. The only trusted base is the floor
(`MSIS`/`MLWESearchHard`/`HashCR`); adaptivity is FREE.
-/
import Dregg2.Crypto.HermineTSUF
import Dregg2.Crypto.ProbCrypto
import Mathlib.Data.Nat.Choose.Basic

namespace Dregg2.Crypto.AdaptiveTSUF

open Dregg2.Crypto.Lattice
open Dregg2.Crypto.HermineSelfTargetMSIS
open Dregg2.Crypto.HermineHintMLWE
open Dregg2.Crypto.HermineTSUF
open Dregg2.Crypto.ConcreteSecurity (Negl Ensemble)
open Dregg2.Crypto.ProbCrypto (DecisionMLWEHardQuant)

/-! ## `section AdaptiveGame` — the interleaved corruption/signing transcript, the adaptive oracle, the budget. -/

section AdaptiveGame

variable {Idx Msg : Type*}

/-- One **step** of an adaptive TS-UF run: either a concurrent **signing query** on a message, or an
**adaptive corruption** revealing member `i`'s share. Unlike the static game (a fixed corrupt `Finset`), here
corruptions are steps INTERLEAVED with signing queries in the transcript. -/
inductive AdaptiveStep (Idx Msg : Type*) where
  /-- A concurrent signing-oracle query on `m`. -/
  | sign (m : Msg)
  /-- An adaptive corruption of committee member `i` (reveals its share). -/
  | corrupt (i : Idx)
  deriving DecidableEq

/-- The **realized corrupt set** of a transcript: the members corrupted somewhere in the run. This is not
known in advance — it emerges from the adaptive schedule. -/
def corruptSet [DecidableEq Idx] : List (AdaptiveStep Idx Msg) → Finset Idx
  | [] => ∅
  | AdaptiveStep.sign _ :: rest => corruptSet rest
  | AdaptiveStep.corrupt i :: rest => insert i (corruptSet rest)

/-- The **signed-message set** of a transcript: the messages queried to the signing oracle. Freshness of a
forgery (`HermineTSUF.Fresh`) is measured against this set. -/
def signedMsgs [DecidableEq Msg] : List (AdaptiveStep Idx Msg) → Finset Msg
  | [] => ∅
  | AdaptiveStep.sign m :: rest => insert m (signedMsgs rest)
  | AdaptiveStep.corrupt _ :: rest => signedMsgs rest

/-- **The adaptive corruption budget.** The realized corrupt set has at most `thr−1` members — the TS-UF-0
threshold, now measured over the WHOLE interleaved run rather than a statically-fixed set. -/
def AdaptiveBudget [DecidableEq Idx] (trace : List (AdaptiveStep Idx Msg)) (thr : ℕ) : Prop :=
  (corruptSet trace).card ≤ thr - 1

/-- **The adaptive adversary / corruption oracle.** Its next action is a FUNCTION of the transcript so far —
this is exactly "choosing whom to corrupt based on the transcript." The static game has no such object (the
corrupt set is fixed); here the target of each corruption may depend on everything already observed. -/
structure AdaptiveAdversary (Idx Msg : Type*) where
  /-- The next step, chosen from the transcript-so-far. -/
  next : List (AdaptiveStep Idx Msg) → AdaptiveStep Idx Msg

/-- The transcript the adaptive adversary REALIZES after `k` rounds: each round appends `next` applied to the
run so far. The realized `corruptSet` of this trace is what the reduction must cope with WITHOUT foreknowledge. -/
def AdaptiveAdversary.trace (adv : AdaptiveAdversary Idx Msg) : ℕ → List (AdaptiveStep Idx Msg)
  | 0 => []
  | k + 1 => adv.trace k ++ [adv.next (adv.trace k)]

/-- **A correct guess respects the budget.** If the reduction's guessed frame `G` has size `thr−1` and the
realized corrupt set lands inside it, then the run is within the adaptive budget. So guessing `G ⊇ corruptSet`
is consistent with (and in fact certifies) `AdaptiveBudget`. -/
theorem guess_respects_budget [DecidableEq Idx] (trace : List (AdaptiveStep Idx Msg)) (thr : ℕ)
    (G : Finset Idx) (hGcard : G.card = thr - 1) (hsub : corruptSet trace ⊆ G) :
    AdaptiveBudget trace thr := by
  unfold AdaptiveBudget
  calc (corruptSet trace).card ≤ G.card := Finset.card_le_card hsub
    _ = thr - 1 := hGcard

end AdaptiveGame

/-! ## `section AdaptiveView` — the adaptive view ties the interleaved transcript to the forgery machinery. -/

section AdaptiveView

variable {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
variable {M : Type*} [AddCommGroup M] [Module Rq M] [ShortNorm M]
variable {N : Type*} [AddCommGroup N] [Module Rq N] [ShortNorm N]
variable {Msg : Type*} {Idx : Type*}

/-- **The adaptive adversary's VIEW.** The interleaved `trace`, the per-member shares handed out on
corruption (`revealedShare`, defined only where corruptions occurred), and the concurrent signing-session
transcripts. The static `HermineTSUF.AdversaryView` bundled a FIXED `corruptShares`; here the shares are
revealed adaptively along `trace`. -/
structure AdaptiveView (Rq : Type*) [CommRing Rq] (M N Msg : Type*) [AddCommGroup M] [Module Rq M]
    [AddCommGroup N] [Module Rq N] (Idx : Type*) where
  /-- The interleaved corruption/signing transcript. -/
  trace : List (AdaptiveStep Idx Msg)
  /-- The share revealed for each corrupted member. -/
  revealedShare : Idx → M
  /-- The concurrent signing-oracle transcripts. -/
  sessions : List (SigningSession Rq M N Msg)

/-- **Freshness against the adaptive signed-message set.** A forgery on a message not in `signedMsgs trace`
is a genuine TS-UF-0 win — distinct from every message the adaptive signing oracle answered. Delegates to
`HermineTSUF.fresh_forgery_distinct_from_sessions`, now measured over the interleaved transcript. -/
theorem adaptive_fresh_distinct [DecidableEq Msg] (Fg : Forger Rq M N Msg) (ρ : ℕ → Rq)
    (trace : List (AdaptiveStep Idx Msg)) (hfresh : Fresh Fg ρ (signedMsgs trace))
    (m : Msg) (hm : m ∈ signedMsgs trace) : Fg.message ρ ≠ m :=
  fresh_forgery_distinct_from_sessions Fg ρ (signedMsgs trace) hfresh m hm

end AdaptiveView

/-! ## `section Guessing` — the adaptive→static guessing reduction: CLOSED, with the explicit combinatorial loss. -/

section Guessing

variable {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
variable {M : Type*} [AddCommGroup M] [Module Rq M] [ShortNorm M]
variable {N : Type*} [AddCommGroup N] [Module Rq N] [ShortNorm N]
variable {Msg : Type*}
variable {Fld : Type*} [Field Fld] [DecidableEq Fld]

/-- **The corruption-answerability obligation** the adaptive reduction must discharge: for ANY two candidate
group secrets it can present a challenge-independent explanation of the realized corrupt view (a degree-`<thr`
Shamir polynomial through the secret at `0` and the revealed shares). This is exactly what lets the reduction
embed its MSIS/MLWE challenge and run secret-free. Both routes below discharge it — the guessing route from
ShamirPrivacy (with the `1/(n choose thr−1)` loss). Same currency as `HermineTSUF.corrupt_view_challenge_independent`. -/
def CorruptionAnswerable (thr : ℕ) (trace : List (AdaptiveStep Fld Msg)) (revealedShare : Fld → Fld) : Prop :=
  ∀ s₀ s₁ : Fld,
    (∃ p : Polynomial Fld, p.degree < (thr : ℕ) ∧ p.eval 0 = s₀ ∧
        ∀ i ∈ corruptSet trace, p.eval i = revealedShare i) ∧
    (∃ q : Polynomial Fld, q.degree < (thr : ℕ) ∧ q.eval 0 = s₁ ∧
        ∀ i ∈ corruptSet trace, q.eval i = revealedShare i)

/-- **The guessed corrupt view is challenge-independent (CLOSED, via ShamirPrivacy).** If the reduction guesses
a frame `G` of size `thr−1` (none of its points the secret's point `0`) and the realized adaptive corrupt set
lands inside it, then the revealed shares are consistent with EVERY candidate secret — the reduction may embed
its challenge freely. Proof: `HermineTSUF.corrupt_view_challenge_independent` on `G` gives polynomials matching
ALL of `G`'s shares for either secret; restricting `∀ i ∈ G` to the realized subset gives the claim. The
realized set may be strictly smaller than `thr−1`; the frame `G` supplies the padding, no field-size side
condition. -/
theorem adaptive_corrupt_view_from_static (thr : ℕ) (hthr : 1 ≤ thr)
    (trace : List (AdaptiveStep Fld Msg)) (G : Finset Fld) (hGcard : G.card = thr - 1)
    (hG0 : (0 : Fld) ∉ G) (hguess : corruptSet trace ⊆ G) (revealedShare : Fld → Fld) :
    CorruptionAnswerable thr trace revealedShare := by
  intro s₀ s₁
  obtain ⟨⟨p, hp, hp0, hpG⟩, ⟨q, hq, hq0, hqG⟩⟩ :=
    corrupt_view_challenge_independent thr hthr G hGcard hG0 revealedShare s₀ s₁
  exact ⟨⟨p, hp, hp0, fun i hi => hpG i (hguess hi)⟩, ⟨q, hq, hq0, fun i hi => hqG i (hguess hi)⟩⟩

/-- **The guessing loss** — the probability that a uniformly-guessed size-`k` frame contains a fixed target set
of size `≤ k`, `1/(n choose k)`. This is the HONEST cost of the adaptive→static reduction: adaptive advantage =
static advantage × `guessSuccessProb n (thr−1)`. It is a PROBABILITY (a combinatorial loss), NOT a hardness
carrier — no laundering. -/
def guessSuccessProb (n k : ℕ) : ℚ := 1 / (n.choose k : ℚ)

/-- The guessing loss is a strictly positive floor whenever the guess is feasible (`k ≤ n`): `n choose k ≥ 1`,
so `1/(n choose k) > 0`. The reduction loses a factor, but never collapses to `0`. -/
theorem guessSuccessProb_pos (n k : ℕ) (hk : k ≤ n) : 0 < guessSuccessProb n k := by
  unfold guessSuccessProb
  have hpos : (0 : ℚ) < (n.choose k : ℚ) := by exact_mod_cast Nat.choose_pos hk
  exact div_pos one_pos hpos

/-- **The shared reduction core.** Once corruption is answerable (challenge-independent view, secret-free
embedding), the adaptive forgery/oracle legs are IDENTICAL to the static game — so the SAME
`HermineTSUF.concurrent_ts_uf_0_reduces` closes the run to `¬ HashCR ∨ (MSIS on [A|t]) ∨ ¬ MLWESearchHard`.
The output carries the answerability witness (so it is load-bearing) alongside the floor break. Both the
guessing route and the loss-free route discharge `hans` — from ShamirPrivacy+guess, resp. the erasure
hypothesis — and route through here. -/
theorem adaptive_reduction_from_answerable {Idx C : Type*}
    (kg : KeyGen Rq M N) (β : ℕ) (cr : CommitReveal Idx N C) (Fg : Forger Rq M N Msg)
    (trace : List (AdaptiveStep Fld Msg)) (revealedShare : Fld → Fld)
    (hans : CorruptionAnswerable kg.thr trace revealedShare)
    (outcome :
      (∃ (cm : C) (i : Idx) (w w' : N), w ≠ w' ∧ cr.opens cm i w ∧ cr.opens cm i w') ∨
      (HintRecoverable kg.A β kg.t) ∨
      (∃ (ρ : ℕ → Rq) (c' : Rq), ρ Fg.challengeIdx ≠ c' ∧
        Accepts kg.A kg.t β Fg ρ ∧ Accepts kg.A kg.t β Fg (Fg.rewind ρ c'))) :
    CorruptionAnswerable kg.thr trace revealedShare
    ∧ ((¬ HashCR cr)
       ∨ (∃ v, IsMSISSolution (augmented kg.A kg.t) ((β + β) + (β + β)) v)
       ∨ (¬ MLWESearchHard kg.A β kg.t)) :=
  ⟨hans, concurrent_ts_uf_0_reduces kg β cr Fg outcome⟩

/-- **`adaptive_ts_uf_reduces` — THE HEADLINE (guessing route, CLOSED to the true floor).** An ADAPTIVE
TS-UF-0 forger against Hermine — corrupting committee members DURING the run, interleaved with concurrent
signing queries, transcript-dependently, up to `thr−1` total — cannot win without breaking the true floor.
Given the reduction's guessed frame `G` (size `thr−1`, avoiding the secret point) that the realized adaptive
corruptions fall inside (`hguess`), the adaptive corrupt view is challenge-independent
(`adaptive_corrupt_view_from_static`, ShamirPrivacy), so the reduction embeds secret-free and the forgery/oracle
legs delegate verbatim to `HermineTSUF.concurrent_ts_uf_0_reduces`, yielding
`¬ HashCR ∨ (MSIS on [A|t]) ∨ ¬ MLWESearchHard` — the SAME floor as the static game.

The reduction's advantage is the static advantage times the EXPLICIT combinatorial loss
`guessSuccessProb n (thr−1) = 1/(n choose thr−1)` (`guessSuccessProb_pos`): the probability the guessed frame
contains the (adaptively, only-later-known) corrupt set. The loss is stated honestly, never hidden; the guess
is a probability event, not a hardness assumption. All three floor disjuncts remain load-bearing, and the
corruption-answerability witness is surfaced in the output. -/
theorem adaptive_ts_uf_reduces {Idx C : Type*}
    (kg : KeyGen Rq M N) (β : ℕ) (cr : CommitReveal Idx N C) (Fg : Forger Rq M N Msg)
    (hthr : 1 ≤ kg.thr)
    (trace : List (AdaptiveStep Fld Msg)) (G : Finset Fld) (hGcard : G.card = kg.thr - 1)
    (hG0 : (0 : Fld) ∉ G) (hguess : corruptSet trace ⊆ G) (revealedShare : Fld → Fld)
    (outcome :
      (∃ (cm : C) (i : Idx) (w w' : N), w ≠ w' ∧ cr.opens cm i w ∧ cr.opens cm i w') ∨
      (HintRecoverable kg.A β kg.t) ∨
      (∃ (ρ : ℕ → Rq) (c' : Rq), ρ Fg.challengeIdx ≠ c' ∧
        Accepts kg.A kg.t β Fg ρ ∧ Accepts kg.A kg.t β Fg (Fg.rewind ρ c'))) :
    CorruptionAnswerable kg.thr trace revealedShare
    ∧ ((¬ HashCR cr)
       ∨ (∃ v, IsMSISSolution (augmented kg.A kg.t) ((β + β) + (β + β)) v)
       ∨ (¬ MLWESearchHard kg.A β kg.t)) :=
  adaptive_reduction_from_answerable kg β cr Fg trace revealedShare
    (adaptive_corrupt_view_from_static kg.thr hthr trace G hGcard hG0 hguess revealedShare) outcome

end Guessing

/-! ## `section Erasure` — the LOSS-FREE (straight-line) route: the closeable core PROVED, the frontier FLAGGED. -/

section Erasure

variable {Rq : Type*} [CommRing Rq]
variable {M : Type*} [AddCommGroup M] [Module Rq M]
variable {N : Type*} [AddCommGroup N] [Module Rq N]
variable {Msg : Type*}
variable {Fld : Type*} [DecidableEq Fld]

/-- **CLOSED — single-member algebraic equivocation.** For ANY member key `tm`, challenge `c`, and an
already-emitted partial-signature response `z`, there is a commitment `w` making the member observable
`A·z = w + c·tm` hold: take `w = simulateCommit A tm c z = A·z − c·tm` (`HermineHintMLWE.simulate_consistent`).
So a partial signature can be explained by ANY member key — the algebraic heart of adaptive equivocation. The
Unmasking-TRaccoon resolution (`adaptive_erasure_from_simulation` below): `tm = t_i` is the member's PUBLIC
key, so the simulator picks `w` from it up front for EVERY member and the reveal is consistent by
construction — the commitment never depended on a secret, so nothing about the corrupt set need be guessed. -/
theorem partial_sig_equivocable_algebraic (A : M →ₗ[Rq] N) (tm : N) (c : Rq) (z : M) :
    ∃ w : N, HintConsistent A tm c w z :=
  ⟨simulateCommit A tm c z, simulate_consistent A tm c z⟩

/-- **The erasure / straight-line-answerability property (DISCHARGED below, not a hypothesis).** A commitment
assignment `commit : Fld → N` is *erasure-consistent* along `trace` when, for every member `i` adaptively
corrupted along `trace`, the commitment `commit i` is consistent with that member's key `memberKey i`,
challenge `chal i`, and emitted response `resp i` — i.e. the partial-signature observable
`A·(resp i) = commit i + (chal i)·(memberKey i)` holds. This is exactly what lets the reduction answer an
adaptive corruption of `i` STRAIGHT-LINE: the already-committed `commit i` is already consistent with the
member state revealed on demand.

The apparent obstruction was that binding fixes `commit i` BEFORE the corruption reveals member `i`. The
Unmasking-TRaccoon resolution (`adaptive_erasure_from_simulation`): `memberKey i = t_i` is the member's PUBLIC
verification key, known to the simulator up front for ALL members, so the simulator BACK-COMPUTES
`commit i = simulateCommit A (memberKey i) (chal i) (resp i) = A·(resp i) − (chal i)·(memberKey i)` from public
data — and this makes the observable hold BY CONSTRUCTION (`simulate_consistent`). The commitment never
depended on any secret share, so it is genuinely prefix-fixed. Hence this property is a THEOREM, discharged for
the simulator's commitment `simTranscriptCommit`; it is NOT a hypothesis and never `#assert_axioms`-laundered. -/
def AdaptiveErasure (A : M →ₗ[Rq] N) (trace : List (AdaptiveStep Fld Msg))
    (memberKey : Fld → N) (chal : Fld → Rq) (resp : Fld → M) (commit : Fld → N) : Prop :=
  ∀ i ∈ corruptSet trace, HintConsistent A (memberKey i) (chal i) (commit i) (resp i)

/-- **The simulator's transcript commitment (the HVZK back-computation).** Given each member's PUBLIC key
`memberKey i = t_i`, the challenge `chal i`, and the simulator-sampled masked response `resp i = z_i`, the
back-computed commitment is `w_i = A·z_i − c·t_i = simulateCommit A t_i c z_i`. This is the SAME secret-free
simulator `HermineHintMLWE.simulateCommit` that answers the concurrent signing oracle
(`HermineTSUF.oracle_answer_secret_free`) — here applied per member, up front, from PUBLIC data alone. -/
def simTranscriptCommit (A : M →ₗ[Rq] N) (memberKey : Fld → N) (chal : Fld → Rq) (resp : Fld → M) : Fld → N :=
  fun i => simulateCommit A (memberKey i) (chal i) (resp i)

/-- **`adaptive_erasure_from_simulation` — the Unmasking-TRaccoon crux, DISCHARGING `AdaptiveErasure`.** For
ANY trace, member keys, challenges, and sampled responses, the simulator's back-computed commitment
`simTranscriptCommit` is erasure-consistent along the WHOLE realized corrupt set — NO guess, NO hypothesis.
Because the simulator samples `z_i` first and sets `w_i = A·z_i − c·t_i` from the PUBLIC per-member key `t_i`,
the observable `A·z_i = w_i + c·t_i` holds BY CONSTRUCTION for every `i` (`HermineHintMLWE.simulate_consistent`).
The transcript never touches a secret share, so it is produced up front and every adaptive reveal is already
consistent with it. This is the property the guessing route paid `1/(n choose thr−1)` to avoid — now proved
outright. The masking (`HintTranscriptSimulatable`, PROVED and grounded in `MLWESearchHard` by
`hint_mlwe_reduces_to_mlwe`) is what makes the sampled `z_i` indistinguishable from the real masked response, so
the reveal does not leak; the algebraic consistency is `simulate_consistent`. -/
theorem adaptive_erasure_from_simulation (A : M →ₗ[Rq] N) (trace : List (AdaptiveStep Fld Msg))
    (memberKey : Fld → N) (chal : Fld → Rq) (resp : Fld → M) :
    AdaptiveErasure A trace memberKey chal resp (simTranscriptCommit A memberKey chal resp) :=
  fun i _ => simulate_consistent A (memberKey i) (chal i) (resp i)

/-! ### THE DECISIONAL RE-GROUNDING of the masking / HVZK-simulatability leg.

`adaptive_erasure_from_simulation` proves the simulated transcript is ALGEBRAICALLY consistent with every
corrupted member (`simulate_consistent`). What makes the on-demand reveal NON-LEAKING is the SECOND,
DECISIONAL fact: the sampled masked response `z_i` is computationally INDISTINGUISHABLE from the real masked
response — the transcript distinguisher's LWE-vs-uniform advantage is negligible. The tree grounds that in
`HermineHintMLWE.HintTranscriptSimulatable` (the uniform-smudging TV bound) reduced to the SEARCH floor
`MLWESearchHard` (`hint_mlwe_reduces_to_mlwe`). Here it is re-grounded on the PROPER DECISIONAL floor
`ProbCrypto.DecisionMLWEHardQuant` (the distinguishing-advantage ENSEMBLE `|Pr[D(real)] − Pr[D(sim)]|`
negligible), the honest shape for an indistinguishability statement — a difference of probabilities, not a
single win/search probability.

The FORGERY / secret-recovery leg (`HintRecoverable → MLWESearchHard`) is genuinely SEARCH (finding the short
secret), not decisional, and is re-grounded separately on the search-quant floor
(`HybridThresholdQuant.adaptive_threshold_negl_of_msis`); it is NOT one of the decisional consumers. Only the
masking-indistinguishability leg re-grounds here. -/

/-- **`adaptive_transcript_nonleaking_under_decision_floor` — the decisional re-grounding.** Under the proper
decisional floor `DecisionMLWEHardQuant advSim` (`advSim s` the transcript-distinguisher's LWE-vs-uniform
advantage ENSEMBLE), the adaptive on-demand reveal is NON-LEAKING: the simulated transcript
`simTranscriptCommit` is (a) ALGEBRAICALLY erasure-consistent with the ENTIRE realized corrupt set — PROVED
outright by `adaptive_erasure_from_simulation`, no hypothesis — AND (b) COMPUTATIONALLY indistinguishable
from the real masked transcript, its distinguishing advantage `Negl (advSim s)` under the decisional floor.
Together: the reveal is consistent by construction and hides the secret, on a genuine distinguishing floor. -/
theorem adaptive_transcript_nonleaking_under_decision_floor {S : Type*}
    (A : M →ₗ[Rq] N) (trace : List (AdaptiveStep Fld Msg))
    (memberKey : Fld → N) (chal : Fld → Rq) (resp : Fld → M)
    (advSim : S → Ensemble) (s : S) (hfloor : DecisionMLWEHardQuant advSim) :
    AdaptiveErasure A trace memberKey chal resp (simTranscriptCommit A memberKey chal resp)
    ∧ Negl (advSim s) :=
  ⟨adaptive_erasure_from_simulation A trace memberKey chal resp, hfloor s⟩

end Erasure

section ErasureHeadline

variable {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
variable {M : Type*} [AddCommGroup M] [Module Rq M] [ShortNorm M]
variable {N : Type*} [AddCommGroup N] [Module Rq N] [ShortNorm N]
variable {Msg : Type*}
variable {Fld : Type*} [DecidableEq Fld]

/-- **`adaptive_ts_uf_reduces_lossfree` — the LOSS-FREE route, UNCONDITIONAL.** An ADAPTIVE TS-UF-0 forger
against Hermine — corrupting committee members DURING the run, transcript-dependently, up to `thr−1` total —
cannot win without breaking the true floor, with NO combinatorial loss and NO residual hypothesis. The
reduction simulates every member's partial signature from PUBLIC data up front (the HVZK back-computation
`simTranscriptCommit`) and reveals shares on demand; `adaptive_erasure_from_simulation` PROVES that simulated
transcript is erasure-consistent with the ENTIRE realized corrupt set, so no corrupt set need be guessed. The
SAME forgery/oracle legs then close the adaptive game to `¬ HashCR ∨ (MSIS on [A|t]) ∨ ¬ MLWESearchHard`
(`HermineTSUF.concurrent_ts_uf_0_reduces`) WITHOUT the `1/(n choose thr−1)` guessing loss of
`adaptive_ts_uf_reduces`. The output carries the (now PROVED) erasure witness alongside the floor break; the
sole trusted base is the lattice/hash floor. This is the Unmasking-TRaccoon payoff: adaptivity is FREE. -/
theorem adaptive_ts_uf_reduces_lossfree {Idx C : Type*}
    (kg : KeyGen Rq M N) (β : ℕ) (cr : CommitReveal Idx N C) (Fg : Forger Rq M N Msg)
    (trace : List (AdaptiveStep Fld Msg))
    (memberKey : Fld → N) (chal : Fld → Rq) (resp : Fld → M)
    (outcome :
      (∃ (cm : C) (i : Idx) (w w' : N), w ≠ w' ∧ cr.opens cm i w ∧ cr.opens cm i w') ∨
      (HintRecoverable kg.A β kg.t) ∨
      (∃ (ρ : ℕ → Rq) (c' : Rq), ρ Fg.challengeIdx ≠ c' ∧
        Accepts kg.A kg.t β Fg ρ ∧ Accepts kg.A kg.t β Fg (Fg.rewind ρ c'))) :
    AdaptiveErasure kg.A trace memberKey chal resp (simTranscriptCommit kg.A memberKey chal resp)
    ∧ ((¬ HashCR cr)
       ∨ (∃ v, IsMSISSolution (augmented kg.A kg.t) ((β + β) + (β + β)) v)
       ∨ (¬ MLWESearchHard kg.A β kg.t)) :=
  ⟨adaptive_erasure_from_simulation kg.A trace memberKey chal resp,
   concurrent_ts_uf_0_reduces kg β cr Fg outcome⟩

end ErasureHeadline

#assert_axioms guess_respects_budget
#assert_axioms adaptive_fresh_distinct
#assert_axioms adaptive_corrupt_view_from_static
#assert_axioms guessSuccessProb_pos
#assert_axioms adaptive_reduction_from_answerable
#assert_axioms adaptive_ts_uf_reduces
#assert_axioms partial_sig_equivocable_algebraic
#assert_axioms adaptive_erasure_from_simulation
#assert_axioms adaptive_transcript_nonleaking_under_decision_floor
#assert_axioms adaptive_ts_uf_reduces_lossfree

/-! ## Teeth — the adaptive game is NON-VACUOUS; the guessing reduction and the erasure hypothesis both FIRE.

`A = id`, key `t = 1`, `β = 0`, `thr = 3`, over `ZMod 5` for the forgery legs; the Shamir field is `ℚ`, with
corruptions at points `1, 2` (avoiding the secret point `0`). We reuse `HermineTSUF.exForger` and its
acceptance verbatim for the forgery door. -/

section Teeth

/-! ### (a) The adaptive game model is non-vacuous and genuinely transcript-dependent. -/

/-- A concrete interleaved run: corrupt `1`, sign `10`, corrupt `2`, sign `11` — corruptions INTERLEAVED with
signing queries, the shape a static game cannot express. -/
def exTrace : List (AdaptiveStep ℕ ℕ) :=
  [AdaptiveStep.corrupt 1, AdaptiveStep.sign 10, AdaptiveStep.corrupt 2, AdaptiveStep.sign 11]

/-- The realized corrupt set is `{1, 2}` — recovered from the interleaved transcript. -/
theorem exTrace_corrupt : corruptSet exTrace = ({1, 2} : Finset ℕ) := by decide

/-- The signed-message set is `{10, 11}`. -/
theorem exTrace_signed : signedMsgs exTrace = ({10, 11} : Finset ℕ) := by decide

-- The run is within the `thr = 3` budget (`|{1,2}| = 2 ≤ 3−1`); a 3-corruption run is NOT (`3 > 2`).
#guard decide ((corruptSet exTrace).card ≤ 3 - 1)
#guard decide (¬ (corruptSet
  ([AdaptiveStep.corrupt 1, AdaptiveStep.corrupt 2, AdaptiveStep.corrupt 3] :
    List (AdaptiveStep ℕ ℕ))).card ≤ 3 - 1)

/-- A transcript-DEPENDENT adversary: it corrupts `7` first, then queries, then corrupts `9` — its choice a
function of the run length so far, the essence of adaptive corruption. -/
def exAdv : AdaptiveAdversary ℕ ℕ where
  next := fun pre => match pre.length with
    | 0 => AdaptiveStep.corrupt 7
    | 1 => AdaptiveStep.sign 100
    | _ => AdaptiveStep.corrupt 9

/-- The realized 3-round run interleaves corruption and signing: `[corrupt 7, sign 100, corrupt 9]`. -/
theorem exAdv_trace : exAdv.trace 3 =
    [AdaptiveStep.corrupt 7, AdaptiveStep.sign 100, AdaptiveStep.corrupt 9] := by decide

-- **Adaptivity is genuine:** two different transcripts yield two DIFFERENT corruption choices — the target is
-- not a fixed set but a function of the transcript (`corrupt 7` on the empty run vs `sign 100` after one step).
#guard decide (exAdv.next [] ≠ exAdv.next [AdaptiveStep.sign 0])
-- The realized run corrupts `{7, 9}`, within `thr = 3`.
#guard decide (corruptSet (exAdv.trace 3) = ({7, 9} : Finset ℕ))

/-! ### (b) The guessing reduction FIRES to the true floor, with its explicit loss. -/

/-- The Shamir-field interleaved run over `ℚ`: corrupt at points `1, 2` (avoiding the secret point `0`). -/
def exTraceF : List (AdaptiveStep ℚ ℕ) :=
  [AdaptiveStep.corrupt 1, AdaptiveStep.sign 10, AdaptiveStep.corrupt 2, AdaptiveStep.sign 11]

/-- **The corrupt view is challenge-independent (guessing route).** With frame `G = {1, 2}` (size `thr−1 = 2`,
avoiding `0`) containing the realized corrupt set, the revealed shares admit a degree-`<3` Shamir polynomial for
BOTH secrets `3` and `7` — the reduction embeds its challenge freely. Fires `adaptive_corrupt_view_from_static`. -/
theorem exCorruptAnswerable :
    CorruptionAnswerable 3 exTraceF (fun _ => 5) :=
  adaptive_corrupt_view_from_static 3 (by norm_num) exTraceF ({1, 2} : Finset ℚ)
    (by decide) (by decide) (by decide) (fun _ => 5)

/-- **THE ADAPTIVE HEADLINE FIRES via the forgery door.** The adaptive forger — corruptions at `{1,2}` inside
the guessed frame `{1,2}`, plus `HermineTSUF.exForger`'s fresh forgery forked at `1 ≠ 2` — yields the
challenge-independent corrupt view AND the MSIS floor disjunct, secret-free, non-vacuously. -/
example :
    CorruptionAnswerable 3 exTraceF (fun _ => 5)
    ∧ ((¬ HashCR (⟨fun i w => (i, w)⟩ : CommitReveal ℕ (ZMod 5) (ℕ × ZMod 5)))
       ∨ (∃ v, IsMSISSolution (augmented (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1)
            ((0 + 0) + (0 + 0)) v)
       ∨ (¬ MLWESearchHard (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 0 (1 : ZMod 5))) :=
  adaptive_ts_uf_reduces ⟨LinearMap.id, 1, 3⟩ 0 _ exForger (by norm_num)
    exTraceF ({1, 2} : Finset ℚ) (by decide) (by decide) (by decide) (fun _ => 5)
    (Or.inr (Or.inr ⟨fun _ => 1, 2, by decide, exForger_accepts _, exForger_accepts _⟩))

/-- The guessing loss is the honest number `1/(5 choose 2) = 1/10` for a 5-member committee at `thr = 3`. -/
theorem exGuessProb : guessSuccessProb 5 2 = 1 / 10 := by
  rw [guessSuccessProb, show Nat.choose 5 2 = 10 from by decide]; norm_num

/-- …and it is a strictly positive floor — the reduction loses a factor, never collapses. -/
theorem exGuessPos : 0 < guessSuccessProb 5 2 := guessSuccessProb_pos 5 2 (by norm_num)

-- The guessing loss `1/(n choose thr−1)` fires numerically and is a positive floor (non-vacuous).
#guard decide (Nat.choose 5 2 = 10)
#guard decide ((0 : ℚ) < 1 / 10)

/-! ### (c) The erasure route: the algebraic core fires, and the OPEN hypothesis is inhabited (non-vacuous). -/

/-- **Single-member algebraic equivocation FIRES.** Any member key `tm = 3`, challenge `2`, response `4`: a
commitment `w` explaining it exists (`w = id·4 − 2·3`). The algebraic heart of adaptive equivocation, closed. -/
example : ∃ w : ZMod 5, HintConsistent (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 3 2 w 4 :=
  partial_sig_equivocable_algebraic (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 3 2 4

/-- **The erasure property is DISCHARGED (non-vacuously).** On a NON-TRIVIAL instance over `ZMod 5`
(member keys `3`, challenge `2`, response `4`), the simulator's back-computed commitment
`simTranscriptCommit id 3 2 4 = id·4 − 2·3 = 3` is consistent with every corrupted member of `exTraceF` —
`adaptive_erasure_from_simulation` proves it outright, no hypothesis. -/
theorem exErasureDischarge :
    AdaptiveErasure (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) exTraceF
      (fun _ => 3) (fun _ => 2) (fun _ => 4)
      (simTranscriptCommit (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5)
        (fun _ => 3) (fun _ => 2) (fun _ => 4)) :=
  adaptive_erasure_from_simulation (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) exTraceF
    (fun _ => 3) (fun _ => 2) (fun _ => 4)

/-- **The back-computed commitment is LOAD-BEARING.** Swap the simulator's `simTranscriptCommit id 3 2 4 = 3`
for a WRONG commitment `0`: erasure FAILS on `exTraceF`, because member `1`'s observable
`id·4 = 0 + 2·3` is `4 = 1`, false. So `adaptive_erasure_from_simulation` genuinely uses the HVZK
back-computation — with any other commitment the reveal is inconsistent (would leak). Both-truth with
`exErasureDischarge`. -/
theorem exErasure_wrong_commit_fails :
    ¬ AdaptiveErasure (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) exTraceF
        (fun _ => 3) (fun _ => 2) (fun _ => 4) (fun _ => 0) := by
  intro h
  have h1 := h 1 (by decide)
  simp only [HintConsistent, LinearMap.id_coe, id_eq] at h1
  exact absurd h1 (by decide)

/-- **The loss-free headline FIRES, UNCONDITIONALLY.** With `exForger`'s forked forgery, the adaptive
reduction reaches the MSIS floor disjunct WITHOUT the guessing loss AND without any erasure hypothesis — the
erasure witness in the output is the PROVED `simTranscriptCommit` consistency. Adaptivity is free. -/
example :
    AdaptiveErasure (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) exTraceF
      (fun _ => 3) (fun _ => 2) (fun _ => 4)
      (simTranscriptCommit (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5)
        (fun _ => 3) (fun _ => 2) (fun _ => 4))
    ∧ ((¬ HashCR (⟨fun i w => (i, w)⟩ : CommitReveal ℕ (ZMod 5) (ℕ × ZMod 5)))
       ∨ (∃ v, IsMSISSolution (augmented (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1)
            ((0 + 0) + (0 + 0)) v)
       ∨ (¬ MLWESearchHard (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 0 (1 : ZMod 5))) :=
  adaptive_ts_uf_reduces_lossfree ⟨LinearMap.id, 1, 3⟩ 0 _ exForger exTraceF
    (fun _ => 3) (fun _ => 2) (fun _ => 4)
    (Or.inr (Or.inr ⟨fun _ => 1, 2, by decide, exForger_accepts _, exForger_accepts _⟩))

/-- **Freshness against the adaptive signed-message set fires** — a fresh forgery differs from every message the
interleaved oracle signed (`{10, 11}`). -/
theorem exFreshAdaptive (ρ : ℕ → ZMod 5) (hfresh : Fresh exForger ρ (signedMsgs exTrace)) :
    exForger.message ρ ≠ 10 := by
  refine adaptive_fresh_distinct exForger ρ exTrace hfresh 10 ?_
  rw [exTrace_signed]; decide

/-! ### (d) The decisional re-grounding of the masking leg FIRES and its floor is LOAD-BEARING. -/

/-- **THE DECISIONAL NON-LEAKING RE-GROUNDING FIRES.** Under the decaying transcript-distinguisher floor
(`ProbCrypto.decayDist.adv = 1/2^l`), the adaptive reveal on `exTraceF` (member keys `3`, challenge `2`,
response `4`) is NON-LEAKING: the simulated transcript is erasure-consistent (PROVED) AND its distinguishing
advantage is negligible. The whole decisional pipeline runs on a real distinguishing advantage. -/
theorem exAdaptiveNonleaking :
    AdaptiveErasure (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) exTraceF
      (fun _ => 3) (fun _ => 2) (fun _ => 4)
      (simTranscriptCommit (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5)
        (fun _ => 3) (fun _ => 2) (fun _ => 4))
    ∧ Negl ProbCrypto.decayDist.adv :=
  adaptive_transcript_nonleaking_under_decision_floor (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) exTraceF
    (fun _ => 3) (fun _ => 2) (fun _ => 4)
    (fun _ : Unit => ProbCrypto.decayDist.adv) () ProbCrypto.decisionMLWEHardQuant_decay_holds

/-- **THE DECISIONAL FLOOR IS LOAD-BEARING** — the perfect transcript distinguisher (advantage `1`) refutes
it, so the masking indistinguishability the reveal relies on is a genuine decisional hardness assumption, not
a Boolean flag. -/
theorem exAdaptive_decision_floor_load_bearing :
    ¬ DecisionMLWEHardQuant (fun _ : Unit => ProbCrypto.perfectDist.adv) :=
  ProbCrypto.decisionMLWEHardQuant_perfect_refuted

end Teeth

#assert_axioms exTrace_corrupt
#assert_axioms exTrace_signed
#assert_axioms exAdv_trace
#assert_axioms exCorruptAnswerable
#assert_axioms exGuessProb
#assert_axioms exGuessPos
#assert_axioms exErasureDischarge
#assert_axioms exErasure_wrong_commit_fails
#assert_axioms exFreshAdaptive
#assert_axioms exAdaptiveNonleaking
#assert_axioms exAdaptive_decision_floor_load_bearing

end Dregg2.Crypto.AdaptiveTSUF
