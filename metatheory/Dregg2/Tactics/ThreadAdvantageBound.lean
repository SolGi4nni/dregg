/-
# `Dregg2.Tactics.ThreadAdvantageBound` — the `thread_advantage_bound` tactic:
the MECHANICAL SWEEP that re-threads an old-floor-conditioned lemma onto the PROPER computational floor.

## What this closes

The 07-13 floor-fix (`Dregg2/Circuit/HashFloorHonesty.lean` + `Dregg2/Crypto/CryptoFloorTeeth.lean`)
proved the OLD floors — `HashCR` / `Poseidon2SpongeCR` / `compressNInjective` / `MSISHard` — stated as
INJECTIVITY / existence-refutation, VACUOUS at real parameters, and defined the PROPER computational
replacements: a keyed-hash-family collision floor (every collision-finder's advantage `Negl`) and
the adversary-indexed `MSISHardQuantShape`/`HashCRHardQuantShape` (`∀ s, Negl (adv s)`).
⚑ That collision floor — `HashFloorHonesty.CollisionResistant` — was itself refuted and is DELETED
(2026-07-28); its honest successor is `FloorGames.HashCRHardQuant F Eff`, and the leaf that read it
out of context went with it. That left ~180 downstream
consumers to re-thread. The threading is UNIFORM: each old-floor use — a Boolean "two openings ⟹ equal"
— becomes an ADDITIVE negligible advantage term, and the resulting `Negl` obligation is discharged by the
negligibility-closure algebra of `Dregg2/Crypto/ConcreteSecurity.lean`
(`negl_zero`, `negl_add`, `negl_const_mul`, `negl_finset_sum`, `negl_two_pow`).

## ⚑ THE FLOOR THE DEMOS TEACH IS THE PROVED KEYED-ROM FLOOR (2026-07-24 re-point)

The original §1-§3 prototypes took `hCR : CollisionResistant F` — a floor
`Crypto.FloorGames.hashCRHardQuant_top_false_of_compressing` PROVES FALSE for every compressing
family, i.e. for every deployed hash. A demo that teaches a refuted assumption is worse than no demo,
so those three are DELETED and their successors below thread the SAME closure algebra with the floor
a THEOREM: `Crypto.KeyedRomFloor.keyedRom_hard` (the birthday bound — nothing refutable carried),
derived IN-PROOF at the extracted finder family and entering the leaves as an already-discharged
`Negl` / `NeglFam` fact.

⚑ 2026-07-28: the `CollisionResistant` leaf that survived here "for legacy call sites" is GONE with
its floor. It cost nothing — a floor hypothesis of that shape is a `∀`-statement, so the generic
`apply_assumption; done` leaf already closed the same goals, and the `HashCRHardQuant` successor
enters the way the PROVED floor does: derived in-proof at the extracted finder and handed to the
leaves as an already-discharged `Negl`/`NeglFam`. A context-`Hard` leaf is deliberately NOT added —
see the transparency note below, it deterministically times out.

## The tactic

`thread_advantage_bound` closes a goal `Negl e` by STRUCTURAL RECURSION over the closure algebra,
pulling the proper floor from the local context at the leaves:

  * `Negl (fun _ => 0)`                      ↦ `negl_zero`                         (a bound-with-no-hash leg)
  * `Negl (fun n => 1/2ⁿ)`                   ↦ `negl_two_pow`                      (an explicit decaying term)
  * `Negl (adv s)` with `NeglFam adv` there  ↦ a DISCHARGED per-index family from the context, applied
                                                at the index (`apply_assumption`) — ⚑ the PROVED
                                                instantiation the demos put there is `keyedRom_hard`
                                                at the extracted finder family
  * `Negl (collisionAdv F A)`                ↦ NO leaf of its own any more: the refuted
                                                `CollisionResistant` floor it read is deleted, and the
                                                honest `HashCRHardQuant F Eff` enters as a derived
                                                `Negl`/`NeglFam` through the two leaves above
  * `Negl (adv s)`                           ↦ the floor `hfloor : MSISHardQuantShape adv` (etc.) applied to `s`
  * `Negl (fun n => f n + g n)`              ↦ `negl_add`, recurse on both      (two independent hash legs)
  * `Negl (fun n => a * f n)`                ↦ `negl_const_mul`, recurse         (a query-count / RLC factor)
  * `Negl (fun n => nᵏ * f n)`               ↦ `negl_mul_monomial`, recurse      (a polynomial factor)
  * `Negl (fun n => ∑ i ∈ s, f i n)`         ↦ `negl_finset_sum`, recurse per i  (the FRI/STARK multi-round
                                                 fold — a soundness error summed over `rounds` Merkle checks)

So the two commonest consumer SHAPES thread mechanically:

  1. **SINGLE-USE binding / equivocation**: "opens ⟹ equal" restates as "the equivocation advantage
     is negligible", a single floor leaf — now discharged from `keyedRom_hard` at a query-class
     membership (`commitment_binding_binds_rom`).
  2. **SUMMED multi-round** (the `friFold` / `StarkSound` chain): a total binding-failure advantage =
     `∑ r ∈ rounds, gameAdv (keyedRomGame F) (finder r)`, negligible by `negl_finset_sum` at every
     round (`friFold_binding_binds_rom`).

and the MIXED tower shape — a de-batching term SCALED by a query count, PLUS the multi-round sum, PLUS a
zero leg — threads by composing all of the above additively (`stark_sound_tower_binds_rom` below).

## Scope — what it does NOT do (honest boundary)

The tactic discharges the UNIFORM part: the `Negl` obligation the restatement introduces. It does NOT
synthesize the restatement's STATEMENT — that is per-theorem-shaped (you name the `CollisionFinder` built
from the specific equivocating opener, and the ensemble the specific protocol's soundness error tracks).
Nor does it discharge a `negl_of_eventually_le` DOMINATION step (which needs a concrete bounding witness),
or a `PolyBounded` side-goal (`negl_mul_poly`) — those carry real content and are left for the caller.
It covers the closure-algebra spine (sum / scale / monomial / finite-sum / decay / zero) and the two floor
leaves (the discharged `NeglFam`, the `*HardQuant` family); that is the mechanical majority of the ~180.

## Axiom hygiene

The emitted proofs compose only the `#assert_all_clean` closure lemmas and the floor hypothesis — no
`sorry`, no fresh `axiom`. Every prototype below is pinned `#assert_axioms`-clean
(⊆ {propext, Classical.choice, Quot.sound}); the floor enters as a HYPOTHESIS, so the restatements are
genuine implications, and a `fail_if_success` tooth shows the tactic REFUSES a non-negligible goal (it is
a real discharger, not a `sorry` in tactic costume).
-/
import Dregg2.Circuit.HashFloorHonesty
import Dregg2.Crypto.ConcreteSecurity
import Dregg2.Crypto.ProbCrypto
import Dregg2.Crypto.KeyedRomFloor

namespace Dregg2.Tactics.ThreadAdvantageBound

open Dregg2.Crypto.ConcreteSecurity
  (Negl negl_zero negl_two_pow negl_add negl_const_mul negl_mul_monomial negl_finset_sum Ensemble
   PolyBounded)
open Dregg2.Crypto.ProbCrypto
  (MSISHardQuantShape MLWEHardQuantShape DLHardQuantShape HashCRHardQuantShape DecisionMLWEHardQuantShape)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder collisionAdv)
open Dregg2.Crypto.FloorGames (Game Adversary Hard gameAdv)
open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily keyedRomGame KeyedRomEff keyedRom_hard)

set_option autoImplicit false

/-! ## The floor LEAF — close `Negl (collisionAdv F A)` / `Negl (adv s)` from the proper floor in
context.

The floors are `∀`-statements (`MSISHardQuantShape adv := ∀ s, Negl (adv s)`,
`NeglFam adv := ∀ s, Negl (adv s)`), so a floor leaf is
the floor hypothesis APPLIED to the adversary/index the goal names. `assumption` catches a bare
`Negl _` hypothesis.

⚑ The `apply_assumption; done` leaf is the one with a PROVED instantiation: the demos derive
`NeglFam (fun r => gameAdv (keyedRomGame F) (finder r))` — i.e. `∀ r, Negl (…)` — from
`keyedRom_hard` (the birthday bound — a THEOREM) and the leaf applies it per index; `done` guards
against a partial application leaving subgoals. ⚑ Why NOT a context-`Hard` leaf
(`exact ‹Hard _ _› _ ‹_›`): its rigid `Negl (gameAdv ?G ?A)` result forces the unifier to
whnf-unfold `gameAdv`↔`collisionAdv` winProb bodies against cross-shaped goals and deterministically
times out (measured 2026-07-24). The PROVED floor therefore enters through a derived `NeglFam` fact,
never through a context `Hard`. -/
/-- **A ∀-INDEXED FAMILY OF DISCHARGED BOUNDS** — the content-free plumbing shape
(`∀ s, Negl (adv s)`), NAMED so the leaf that applies it says what it is: an already-discharged
family being indexed, never a hardness assumption (`HardQuantVacuity`'s lesson, kept visible). The
keyed-ROM demos put `keyedRom_hard`-derived families in context at this shape. -/
abbrev NeglFam {S : Type*} (adv : S → Ensemble) : Prop := ∀ s, Negl (adv s)

syntax "advantage_floor_leaf" : tactic
macro_rules
  | `(tactic| advantage_floor_leaf) =>
    `(tactic| first
        | assumption
        | (apply_assumption; done)
        | exact ‹HashCRHardQuantShape _› _
        | exact ‹MSISHardQuantShape _› _
        | exact ‹MLWEHardQuantShape _› _
        | exact ‹DecisionMLWEHardQuantShape _› _
        | exact ‹DLHardQuantShape _› _)

/-! ⚑ TRANSPARENCY NOTE (2026-07-24): the two decay leaves of `thread_advantage_bound` run
`with_reducible` — a `Negl (gameAdv …)` goal must FAIL them fast (at default transparency the defeq
attempt whnf-unfolds `gameAdv`'s `winProb` over a function-space `Fintype` and can time out), and
every in-tree use of these leaves is a syntactic `fun _ => 0` / `fun n => 1 / 2 ^ n` leg, which
reducible matching still closes. -/

/-! ## `thread_advantage_bound` — the recursive closure-algebra discharger.

Leaves are tried BEFORE the recursive combinators (so a `collisionAdv`/`0`/`1/2ⁿ` leaf never regresses),
and each combinator recurses via `<;> thread_advantage_bound` on strictly smaller goals — the recursion
terminates when the advantage expression bottoms out at a floor leaf. -/
syntax "thread_advantage_bound" : tactic
macro_rules
  | `(tactic| thread_advantage_bound) =>
    `(tactic| first
        | with_reducible exact negl_zero
        | with_reducible exact negl_two_pow
        | advantage_floor_leaf
        | (refine negl_add ?_ ?_ <;> thread_advantage_bound)
        | (refine negl_const_mul _ ?_ <;> thread_advantage_bound)
        | (refine negl_mul_monomial _ ?_ <;> thread_advantage_bound)
        | (refine negl_finset_sum _ (fun _ _ => ?_) <;> thread_advantage_bound))

/-! ## §1 — PROTOTYPE on real consumer SHAPE 1: single-use equivocation binding, on the PROVED floor.

⚑ The predecessor (`commitment_binding_advantage_bound`, DELETED 07-24) took
`hCR : CollisionResistant F` — refuted for every compressing family
(`FloorGames.hashCRHardQuant_top_false_of_compressing`), so it taught every future user a FALSE
assumption. The successor threads the SAME single-leaf shape with the floor a THEOREM: the adversary
is a query-bounded oracle program against the SAMPLED keyed oracle, and `keyedRom_hard` (the birthday
bound) closes the leaf. What the caller supplies is a polynomial query budget and the class
membership — nothing refutable. -/

/-- **SHAPE-1 prototype (commitment / opening binding), DISCHARGED.** A query-bounded equivocator of
the sampled keyed oracle has negligible advantage — "opens ⟹ equal except with negligible
probability", with the floor `keyedRom_hard` derived in-proof (not assumed). Proof:
`thread_advantage_bound` (the `assumption` leaf at the derived bound). -/
theorem commitment_binding_binds_rom (F : KeyedRomFamily) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (hw : ∀ l, letI := F.rFin l; Fintype.card (F.R l) = 2 ^ l)
    (A : Adversary (keyedRomGame F)) (hA : KeyedRomEff F Q A) :
    Negl (gameAdv (keyedRomGame F) A) := by
  have hleaf : Negl (gameAdv (keyedRomGame F) A) := keyedRom_hard F Q hQ hw A hA
  thread_advantage_bound

/-! ## §2 — PROTOTYPE on real consumer SHAPE 2: the multi-round FRI/STARK fold, on the PROVED floor.

The `StarkSound` / FRI-proximity chain runs `rounds` Merkle-binding checks. The total binding-failure
advantage is the finite SUM of the per-round advantages, negligible by `negl_finset_sum` — the
union-bound step — with each round's leaf closed from the ONE proved floor at that round's extracted
finder (the derived `NeglFam`, applied per index by the leaf). Predecessor
(`friFold_binding_advantage_bound`, `CollisionResistant`-conditioned) DELETED 07-24. -/

/-- **SHAPE-2 prototype (multi-round FRI/STARK binding), DISCHARGED.** The total opening-binding
failure advantage across `rounds` checks — each round an extracted query-bounded finder against the
sampled oracle — is negligible, floor derived in-proof. Proof: `thread_advantage_bound`
(`negl_finset_sum`, then the `NeglFam` leaf per round). -/
theorem friFold_binding_binds_rom (F : KeyedRomFamily) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (hw : ∀ l, letI := F.rFin l; Fintype.card (F.R l) = 2 ^ l)
    (rounds : Finset ℕ) (finder : ℕ → Adversary (keyedRomGame F))
    (hmem : ∀ r, KeyedRomEff F Q (finder r)) :
    Negl (fun n => ∑ r ∈ rounds, gameAdv (keyedRomGame F) (finder r) n) := by
  have hfam : NeglFam (fun r => gameAdv (keyedRomGame F) (finder r)) :=
    fun r => keyedRom_hard F Q hQ hw (finder r) (hmem r)
  thread_advantage_bound

/-! ## §3 — PROTOTYPE on the MIXED tower shape: de-batch scale + multi-round sum + zero leg.

A full `AlgoStarkSoundTransferV3`-style soundness error threads THREE contributions additively: an RLC
de-batching term SCALED by a query-count factor, the multi-round Merkle fold SUM, and an algebra leg that
carries no hash (advantage `0`). `thread_advantage_bound` composes `negl_add` / `negl_const_mul` /
`negl_finset_sum` / `negl_zero` and closes every leaf from the ONE proved floor. Predecessor
(`stark_sound_tower_advantage_bound`, `CollisionResistant`-conditioned) DELETED 07-24. -/

/-- **MIXED tower prototype, DISCHARGED.** A composite STARK soundness-error advantage
`c · (debatch term) + ∑_{r ∈ rounds} (per-round term) + 0` is negligible, floor derived in-proof —
the additive threading of every hash leg through the tower, all bottoming at leaves fed by
`keyedRom_hard`. -/
theorem stark_sound_tower_binds_rom (F : KeyedRomFamily) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (hw : ∀ l, letI := F.rFin l; Fintype.card (F.R l) = 2 ^ l)
    (c : ℝ) (debatch : Adversary (keyedRomGame F)) (hdb : KeyedRomEff F Q debatch)
    (rounds : Finset ℕ) (finder : ℕ → Adversary (keyedRomGame F))
    (hmem : ∀ r, KeyedRomEff F Q (finder r)) :
    Negl (fun n => c * gameAdv (keyedRomGame F) debatch n
        + (∑ r ∈ rounds, gameAdv (keyedRomGame F) (finder r) n) + 0) := by
  have hdb' : Negl (gameAdv (keyedRomGame F) debatch) := keyedRom_hard F Q hQ hw debatch hdb
  have hfam : NeglFam (fun r => gameAdv (keyedRomGame F) (finder r)) :=
    fun r => keyedRom_hard F Q hQ hw (finder r) (hmem r)
  thread_advantage_bound

/-! ## §4 — the `*HardQuantShape` leg. ⚠ **NO PROBLEM CONTENT — UNDISCHARGED OBLIGATIONS, NOT KEYSTONES.**

⚑ **Read this before the four theorems below.** The 07-16 vacuity sweep proved that
`MSISHardQuantShape adv := ∀ s, Negl (adv s)` mentions no lattice and is `Iff.rfl`-equal to the hash-CR and
discrete-log floors, so `(adv) (s) (hfloor : MSISHardQuantShape adv) : Negl (adv s)` is `hfloor s` — a
`P → P` instantiation that transports no hardness (`HardQuantVacuity` §2). The floors were renamed to
`*Shape` in the 07-16 repair precisely so these signatures would stop claiming otherwise: the hypothesis
now says, in its own name, that it is a shape and not a problem.

**These four are RETAINED and are NOT re-grounded.** `VrfRegrounded.lattice_vrf_uniqueness_advantage_bound`
was re-grounded because its reduction (`VRF.lattice_vrf_uniqueness_reduces_to_msis`) exists in the tree and
could be put into the statement. These four have no such reduction available:

  * the two forking legs (`forger_advantage_bound_under_msis`, `forger_advantage_with_challenge_bound`) have
    a REAL partial leg — `ProbCrypto.ForkingFamily.bound` is a proved inequality and
    `HermineTSUF.prob_forger_forkProb_yields_msis` genuinely extracts an `IsMSISSolution` — but nothing in
    the tree connects `forkProb` to the advantage of an adversary against an `FloorGames.MSISFamily`. That
    connection is the honest remaining work, and inventing it in a docstring is what this whole sweep is
    about. **Named obligation: `forkProb ≤ msisAdv (extracted solver)`, undischarged.**
  * the two decisional legs (`decision_distinguisher_advantage_bound`, `lossy_id_advantage_bound`) have NO
    reduction in the tree at all — nothing relates the lossy-keygen switch or the HVZK simulation term to
    `FloorGames.DecisionMLWEHardQuant`'s LWE-vs-uniform game. **Named obligation: the game hop itself,
    undischarged.**

They are kept because they are TRUE and because the tactic prototypes are real; they are labelled because
they are `P → P`. Do not cite them as MSIS/decision-MLWE grounding. -/

/-- ⚠ **NO MSIS CONTENT — `hfloor s`.** Under `MSISHardQuantShape adv` — a predicate that mentions no
lattice — the advantage at index `s` is negligible. The name says `under_msis`; the statement does not.
Retained as the tactic prototype and as an undischarged obligation (§4 header). The honest floor is
`FloorGames.MSISHardQuant`; the missing leg is `forkProb ≤ msisAdv (extracted solver)`. -/
theorem forger_advantage_bound_under_msis {S : Type*} (adv : S → Ensemble) (s : S)
    (hfloor : MSISHardQuantShape adv) :
    Negl (adv s) := by
  thread_advantage_bound

/-- ⚠ **NO MSIS CONTENT** (§4 header). A mixed bound: a decaying challenge-space term `1/2ⁿ` PLUS the
advantage at `s`. The `1/2ⁿ` leg is negligible on its own (`negl_two_pow`, no floor needed) and the other
leg is `hfloor s`, so the decoration adds nothing the floor did not already hand back. -/
theorem forger_advantage_with_challenge_bound {S : Type*} (adv : S → Ensemble) (s : S)
    (hfloor : MSISHardQuantShape adv) :
    Negl (fun n => (1 / (2 : ℝ) ^ n) + adv s n) := by
  thread_advantage_bound

/-! ## §4b — PROTOTYPE on the DECISIONAL floor (the LWE-vs-uniform distinguishing leg).

The decisional consumers (`LossyIdentification`'s lossy-keygen switch, the HVZK transcript-indistinguishability
leg of `AdaptiveTSUF`/`ThresholdSignerRefinement`) rest on `DecisionMLWEHardQuantShape adv := ∀ s, Negl (adv s)`,
where `adv s` is a distinguisher's LWE-vs-uniform advantage ENSEMBLE (`ProbCrypto.distinguishAdv`, a
DIFFERENCE of two acceptance probabilities — not a single `winProb`). The new floor leaf threads it exactly
like the search floors. -/

/-- ⚠ **NO DECISION-MLWE CONTENT — `hfloor s`** (§4 header). `DecisionMLWEHardQuantShape adv` is the same
content-free `Prop` as the MSIS shape; nothing in it is a distinguishing game. The honest floor is
`FloorGames.DecisionMLWEHardQuant`, whose real world is a PROVED `Lattice.IsMLWESample`; the missing leg is
the game hop that would connect this consumer to it. -/
theorem decision_distinguisher_advantage_bound {S : Type*} (adv : S → Ensemble) (s : S)
    (hfloor : DecisionMLWEHardQuantShape adv) :
    Negl (adv s) := by
  thread_advantage_bound

/-- ⚠ **NO DECISION-MLWE CONTENT** (§4 header). The lossy-ID game-hop SHAPE: the tight-EUF-CMA advantage decomposes as the
decision-MLWE key-switch term (`adv s`, a distinguishing floor leaf) PLUS the statistical lossy-soundness
term PLUS the HVZK simulation term (both given negligible) — negligible by additive threading. Proof:
`thread_advantage_bound` (`negl_add` down to the `DecisionMLWEHardQuantShape` leaf and the two `assumption`
legs). -/
theorem lossy_id_advantage_bound {S : Type*} (adv : S → Ensemble) (s : S) (lossyBound simTerm : Ensemble)
    (hfloor : DecisionMLWEHardQuantShape adv) (hlossy : Negl lossyBound) (hsim : Negl simTerm) :
    Negl (fun n => adv s n + lossyBound n + simTerm n) := by
  thread_advantage_bound

/-! ## §5 — TEETH: the tactic is a REAL discharger, not a `sorry` in tactic costume.

It closes a `Negl` goal ONLY when the negligibility is genuinely available (a floor leaf or a decaying
term through the closure algebra). On a NON-negligible goal — the constant `1`, with no floor to appeal
to — it FAILS. `fail_if_success` witnesses the refusal; a `sorry`-in-disguise tactic would pass here. -/

/-- **(TOOTH — the tactic REFUSES a non-negligible goal.)** The constant-`1` ensemble is NOT negligible
(`ConcreteSecurity.not_negl_one`); `thread_advantage_bound` cannot close it (no leaf matches, no floor in
context), so the inner `have` fails and `fail_if_success` succeeds. This is the non-vacuity teeth: the
tactic discharges REAL negligibility, it does not fabricate it. -/
example : True := by
  fail_if_success
    (have : Negl (fun _ : ℕ => (1 : ℝ)) := by thread_advantage_bound)
  trivial

-- **(TOOTH — the tactic REFUSES a floor leaf with NO floor in context.)** Even a genuine `collisionAdv`
-- advantage is not closable without a collision floor in context — the tactic does not invent the
-- assumption. ⚑ Since 2026-07-28 there is no floor that would close it either: the leaf that read
-- `CollisionResistant` out of context died with that def, so this now refuses unconditionally.
set_option linter.unusedVariables false in
example (F : KeyedHashFamily) (A : CollisionFinder F) : True := by
  fail_if_success
    (have : Negl (collisionAdv F A) := by thread_advantage_bound)
  trivial

/-! ## §6 — axiom-hygiene pins. -/

#assert_all_clean [
  commitment_binding_binds_rom,
  friFold_binding_binds_rom,
  stark_sound_tower_binds_rom,
  forger_advantage_bound_under_msis,
  forger_advantage_with_challenge_bound,
  decision_distinguisher_advantage_bound,
  lossy_id_advantage_bound
]

end Dregg2.Tactics.ThreadAdvantageBound
