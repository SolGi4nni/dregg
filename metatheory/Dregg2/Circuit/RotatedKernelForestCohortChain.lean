/-
# Dregg2.Circuit.RotatedKernelForestCohortChain — the DEPLOYED per-cohort PROOF-CHAIN forcing.

This module closes foolable gap #2 (the verifier forces only the LEAD effect) at the level the DEPLOYED
shape actually carries it: the per-COHORT proof chain.

## What the deployed shape already is (read-only ground truth)

`sdk/full_turn_proof.rs::prove_cohort_run_chain` splits a turn into maximal homogeneous cohort runs
(`split_into_cohort_runs`) and emits ONE rotated `Ir2BatchProof` per run — a LIST of legs (`AttachedSubProof`),
each leg carrying its OWN rotated PI vector, whose `OLD_COMMIT`/`NEW_COMMIT` felts are the leg's published
pre/post 8-felt state commitments. The producer threads `s_k → s_{k+1}` so each leg's `OLD_COMMIT` IS the
prior leg's `NEW_COMMIT` (the chained-root column). So the deployed evidence for a turn `[Transfer,
SetPermissions]` is ALREADY a 2-leg chain `[transferLeg, setPermsLeg]`.

The gap is purely in the VERIFIER: the deployed NODE verify `turn/executor/proof_verify.rs` resolves ONE
descriptor by `vm_effects.first()` (the lead cohort) and runs `verify_vm_descriptor2` ONCE — it does NOT
iterate the legs nor check the chain. (The SDK `verify_full_turn_bound` DOES already iterate + chain-check;
this module is the soundness statement that BACKS wiring that same shape into the node leg.)

## What this module builds (ADDITIVE — nothing existing is mutated; NOT live-wired)

A `CohortProofChain` is the published-commitment view of the deployed leg list: a LIST of `DecodedStep`s
(each = a cohort leg's descriptor + published commitment + faithful decode), CHAINED at the published
commitment (`leg[i].pc.pubPost = leg[i+1].pc.pubPre`, same turn), with the endpoints pinned to the turn's
published pre/post.

  1. **`chainForcesEveryCohort`** — THE FOREST-FORCING STATEMENT. From the per-effect refinement family
     `hrefines : ∀ e, descriptorRefines S hash (R e) (dispatchArm e)` + each leg's circuit accept
     (`Satisfied2` of its descriptor) + the per-leg faithful decode, EVERY leg's kernel transition
     `dispatchArm e legᵢ.pre legᵢ.post` is forced — not just the lead. This is `StepsRefine` lifted to the
     cohort chain; combined with the published-commit chain it folds (via `turnDecodeChain_refines_turnSpec`)
     into a genuine whole-turn `turnSpec` whose endpoints commit to the published `(pre, post)`.

  2. **`cohort_chain_forces_tail`** — the SHARP per-effect tooth: in a 2-cohort chain, the TAIL leg's
     transition is forced exactly as strongly as the lead's. A turn `[Transfer, SetPermissions]` has its
     SetPermissions transition `dispatchArm eTail` FORCED, not merely applied-and-committed.

  3. **`chainBroken_rejects`** / **`missing_tail_unchained`** — THE CHAIN-REJECTION TOOTH. A leg list whose
     published commitments do NOT chain (`legᵢ.pc.pubPost ≠ legᵢ₊₁.pc.pubPre`) CANNOT be a `CohortProofChain`
     (the `pubSeam` field is uninhabitable) — the chain check REJECTS it. The honest chained forest accepts
     (`cohort_chain_accepts_honest`); the same forest with a leg's published commit unchained (the deployed
     anti-splice: a dropped/forged tail leaves `pubPost[i] ≠ pubPre[i+1]`) is rejected. This is the Lean
     backing for the deployable adjacency check `this_old == prev_new` (`full_turn_proof.rs:2448`).

## The lift onto `ClosureForest`

The per-leg `descriptorRefines` is exactly the rung the WHOLE-TURN `ClosureForest` apex carries per step;
a `CohortProofChain` IS a `TurnDecodeChain` (every leg's `Satisfied2` + the published seam + the endpoints),
so `chainForcesEveryCohort` + the chain fold lands the SAME `execFullTurnA`/`turnSpec` conclusion the
`ClosureForest` headline lands — now witnessing that EVERY cohort leg (not the lead) was forced.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} + the named carriers inherited through the
imported keystone (`Poseidon2SpongeCR`, the `CommitSurface` CR fields entering through `descriptorRefines`).
No `sorry`, no `native_decide`, no `:= True`, no fresh axiom. NEW file; imports read-only.
-/
import Dregg2.Circuit.CircuitSoundness

namespace Dregg2.Circuit.RotatedKernelForestCohortChain

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (FullActionA execFullTurnA)
open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 VmTrace Satisfied2)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

set_option autoImplicit false

/-! ## §1 — the per-cohort PROOF-CHAIN view (the deployed leg list, published-commitment level).

A `CohortProofChain` is the published-commitment view of the deployed `prove_cohort_run_chain` leg list.
Each leg is a `DecodedStep` carrying its cohort descriptor, its published `(OLD_COMMIT, NEW_COMMIT)`
commitment, and the faithful decode to its `(pre, post)` kernels. The chain carries:

  * `legSat` — every leg publishes a circuit `Satisfied2` of its cohort descriptor (the per-leg accept the
    deployed verifier WOULD run with `verify_vm_descriptor2` on each leg);
  * `pubChain` — the published commitments CHAIN: each leg's NEW (`pubPost`) IS the next leg's OLD
    (`pubPre`), at the same boundary turn (the deployed adjacency check `this_old == prev_new`);
  * `headPre`/`lastPost` — the turn-level endpoints pin the first OLD / last NEW (the deployed endpoint
    pins `proof_old_commit == expected_old_commit` / `proof_new_commit == expected_new_commit`).

This is EXACTLY a `TurnDecodeChain` (same fields, re-presented as the per-cohort leg list); we expose the
bridge `toTurnDecodeChain` so the proven whole-turn fold applies verbatim. -/

/-- **`CohortProofChain hash S start fin`** — the deployed per-cohort proof-chain as the published-commitment
view: a LIST of cohort legs (`DecodedStep`s) whose published commitments chain, with the turn endpoints
pinned. This is the verifier's accepting evidence for a HETEROGENEOUS turn under the deployed
`prove_cohort_run_chain` shape — NOT the lead leg alone. -/
structure CohortProofChain (hash : List ℤ → ℤ) (S : CommitSurface)
    (start fin : RecChainedState) where
  /-- the per-cohort legs, in chain order (one per maximal homogeneous run). -/
  legs     : List (DecodedStep S)
  /-- every leg publishes a circuit `Satisfied2` of its cohort descriptor — the per-leg accept the
      deployed verifier WOULD run on each leg (not just the lead). -/
  legSat   : ∀ d ∈ legs, ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
                Satisfied2 hash d.descr minit mfin maddrs t ∧ tracePublishedCommit t = d.pc
  /-- the turn pre-state IS the first leg's pre (empty turn: `start = fin`). -/
  headPre  : legs.head?.elim (start = fin) (fun d => start = d.pre)
  /-- the turn post-state IS the last leg's post. -/
  lastPost : legs.getLast?.elim (start = fin) (fun d => d.post = fin)
  /-- the threaded FULL-state seam (each leg's post IS the next leg's pre — the deployed producer's
      `s_k → s_{k+1}` threading). The KERNEL half is DERIVED from `pubChain` (the frame tooth
      `stateDecodeChain_frame_continuous`); this carries the residual full-state thread, exactly as
      `TurnDecodeChain.seam`. -/
  seam     : List.IsChain (fun a b => a.post = b.pre) legs
  /-- THE PUBLISHED-COMMIT CHAIN: each leg's published NEW (`pubPost`) IS the next leg's published OLD
      (`pubPre`), at the same boundary turn. THIS is the deployed adjacency check `this_old == prev_new`;
      a leg list that does NOT chain cannot inhabit this field (the rejection tooth, §4). -/
  pubChain : List.IsChain (fun a b => a.pc.turn = b.pc.turn ∧ a.pc.pubPost = b.pc.pubPre) legs

/-- **`toTurnDecodeChain`** — a `CohortProofChain` IS a `TurnDecodeChain`. The published-commit chain
(`pubChain`) supplies BOTH the kernel seam (DERIVED via `stateDecodeChain_frame_continuous`) and the
published seam (`pubSeam`) the whole-turn fold consumes. So every proven `TurnDecodeChain` keystone applies
to the per-cohort leg list verbatim. -/
def CohortProofChain.toTurnDecodeChain
    {hash : List ℤ → ℤ} {S : CommitSurface} {start fin : RecChainedState}
    (c : CohortProofChain hash S start fin) :
    TurnDecodeChain hash S start fin where
  steps   := c.legs
  sat     := c.legSat
  headPre := c.headPre
  lastPost := c.lastPost
  seam    := c.seam
  pubSeam := c.pubChain

/-! ## §2 — `chainForcesEveryCohort`: the FOREST-FORCING statement (every cohort, not the lead).

The per-effect refinement family `hrefines` discharges `dispatchArm e legᵢ.pre legᵢ.post` for EVERY leg
whose descriptor is `R e` — from that leg's OWN circuit accept (`legSat`) + its OWN faithful decode. This
is `StepsRefine` over the cohort chain: strictly stronger than the deployed lead-only check, which forces
the transition of `legs.head` alone. -/

/-- **`chainForcesEveryCohort` — EVERY cohort leg's transition is forced.** Given the carried per-effect
family `hrefines` + the named CR carrier + the per-leg effect identification (`hidx : each leg's descriptor
is `R e` for some `e`), EVERY leg's kernel transition `dispatchArm e legᵢ.pre legᵢ.post` is forced from that
leg's own accept + decode. The fold-ready `StepsRefine` over the cohort chain — the lead-only deployed check
forces only `legs.head`; this forces ALL. -/
theorem chainForcesEveryCohort
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    (hCR : Poseidon2SpongeCR hash)
    (hrefines : ∀ e, descriptorRefines S hash (R e) (dispatchArm e))
    {start fin : RecChainedState} (c : CohortProofChain hash S start fin)
    (hidx : ∀ d ∈ c.legs, ∃ e : EffectIdx, d.descr = R e) :
    ∀ d ∈ c.legs, ∃ e : EffectIdx, d.descr = R e ∧ dispatchArm e d.pre d.post :=
  -- exactly `stepsRefine_of_descriptorRefines` on the `TurnDecodeChain` view: each leg's accept + decode
  -- forces its transition, quantified over ALL legs.
  stepsRefine_of_descriptorRefines hash S R hCR hrefines c.toTurnDecodeChain hidx

/-- **`cohort_chain_forces_tail` (the SHARP per-effect tooth).** In any cohort chain, a leg that is NOT the
lead (any `d ∈ c.legs`) has its transition forced exactly as strongly as the lead. Instantiated at the LAST
leg of a 2-cohort turn `[Transfer, SetPermissions]`, this says the SetPermissions transition `dispatchArm
eTail` is FORCED — closing the gap where the deployed verifier proved only the Transfer lead. -/
theorem cohort_chain_forces_tail
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    (hCR : Poseidon2SpongeCR hash)
    (hrefines : ∀ e, descriptorRefines S hash (R e) (dispatchArm e))
    {start fin : RecChainedState} (c : CohortProofChain hash S start fin)
    (hidx : ∀ d ∈ c.legs, ∃ e : EffectIdx, d.descr = R e)
    (tail : DecodedStep S) (htail : tail ∈ c.legs) :
    ∃ e : EffectIdx, tail.descr = R e ∧ dispatchArm e tail.pre tail.post :=
  chainForcesEveryCohort hash S R hCR hrefines c hidx tail htail

/-! ## §3 — the whole-turn run: the cohort chain folds to a GENUINE executor run forcing every leg.

`chainForcesEveryCohort` is the per-leg rung; the published-commit chain threads the seam. Together they
fold (`turnDecodeChain_refines_turnSpec` + `execFullTurnA_iff_turnSpec`) into a genuine `execFullTurnA`
run whose endpoints commit to the published turn-level `(pre, post)` — the `ClosureForest` headline, now
landed through the per-cohort proof chain so the witness is "every cohort leg forced", not "lead forced". -/

/-- **`lightclient_cohort_chain_forces_full_turn` — the per-cohort chain yields the whole-turn run.** A
verified `CohortProofChain` (every leg accepts + the published commits chain + endpoints pinned) + the
carried per-effect family ⟹ a genuine `execFullTurnA start acts = some fin` whose endpoints commit to the
turn-level published `(pre, post)`. Identical conclusion to `ClosureForest`'s headline, reached through the
deployed per-cohort leg list — so the run that exists is one where EVERY cohort's transition was forced. -/
theorem lightclient_cohort_chain_forces_full_turn
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    (hCR : Poseidon2SpongeCR hash)
    (hrefines : ∀ e, descriptorRefines S hash (R e) (dispatchArm e))
    {start fin : RecChainedState} (c : CohortProofChain hash S start fin)
    (hidx : ∀ d ∈ c.legs, ∃ e : EffectIdx, d.descr = R e)
    (te : TurnEndpoints hash S c.toTurnDecodeChain) :
    ∃ (acts : List FullActionA) (s s' : RecChainedState),
      execFullTurnA s acts = some s' ∧
      te.tp.pubPre = S.commit s.kernel te.tp.turn ∧
      te.tp.pubPost = S.commit s'.kernel te.tp.turn :=
  -- the whole-turn fold over the `TurnDecodeChain` view; the carried family forces every leg.
  lightclient_turn_unfoolable_forest hash S R hCR hrefines c.toTurnDecodeChain hidx te

/-! ## §4 — THE CHAIN-REJECTION TOOTH: a missing / unchained tail leg is REJECTED.

The deployable artifact is the adjacency check `legᵢ.pc.pubPost = legᵢ₊₁.pc.pubPre` (the deployed
`this_old == prev_new`, `full_turn_proof.rs:2448`). We prove it BITES: a leg list whose published
commitments do NOT chain cannot inhabit `pubChain`, so it is NOT a `CohortProofChain` — the verifier
rejects it. An honest chained forest accepts (§4.1). -/

/-- **`chainBroken_rejects` (the CHAIN-REJECTION TOOTH).** If two adjacent legs `a, b` do NOT chain at the
published commitment (`a.pc.pubPost ≠ b.pc.pubPre`), they cannot appear adjacent in ANY `CohortProofChain`:
the `pubChain` field would force `a.pc.pubPost = b.pc.pubPre`, contradiction. A dropped/forged tail leg
(whose `OLD_COMMIT` no longer matches the prior `NEW_COMMIT`) is REJECTED by the chain check — the deployed
anti-splice `this_old == prev_new`. -/
theorem chainBroken_rejects
    {hash : List ℤ → ℤ} {S : CommitSurface} {start fin : RecChainedState}
    (a b : DecodedStep S) (rest pre : List (DecodedStep S))
    (hbad : a.pc.pubPost ≠ b.pc.pubPre)
    (c : CohortProofChain hash S start fin)
    (hlegs : c.legs = pre ++ a :: b :: rest) :
    False := by
  -- `pubChain` is a chain over `c.legs`; the adjacent pair `a, b` (somewhere after `pre`) must satisfy
  -- the chain relation, which includes `a.pc.pubPost = b.pc.pubPre` — contradicting `hbad`.
  have hchain := c.pubChain
  rw [hlegs] at hchain
  -- peel `pre`: a sublist chain stays a chain; reach the `a :: b :: rest` suffix.
  have hsuffix : List.IsChain
      (fun a b => a.pc.turn = b.pc.turn ∧ a.pc.pubPost = b.pc.pubPre) (a :: b :: rest) := by
    clear hbad hlegs
    induction pre with
    | nil => simpa using hchain
    | cons p ps ih =>
        apply ih
        exact (List.isChain_cons.mp (by simpa using hchain)).2
  -- the head relation of the suffix gives `a.pc.pubPost = b.pc.pubPre`.
  have hrel : a.pc.turn = b.pc.turn ∧ a.pc.pubPost = b.pc.pubPre :=
    (List.isChain_cons.mp hsuffix).1 b (by simp)
  exact hbad hrel.2

/-! ### §4.1 — the both-polarities corollary: honest chains accept, unchained tails reject. -/

/-- **`cohort_chain_accepts_honest`** — an HONEST 2-cohort chain (its two legs chain at the published
commitment) is a genuine `CohortProofChain`: the constructor succeeds. The accepting side of the tooth.
Built from two legs whose published commits chain (`hchain`) + the per-leg accepts + the endpoint threads —
this is the honest `[lead, tail]` forest the verifier ACCEPTS. -/
def cohort_chain_accepts_honest
    {hash : List ℤ → ℤ} {S : CommitSurface} {start fin : RecChainedState}
    (lead tail : DecodedStep S)
    (hsat : ∀ d ∈ [lead, tail], ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
              Satisfied2 hash d.descr minit mfin maddrs t ∧ tracePublishedCommit t = d.pc)
    (hheadPre : start = lead.pre)
    (hlastPost : tail.post = fin)
    (hseam : lead.post = tail.pre)
    (hchain : lead.pc.turn = tail.pc.turn ∧ lead.pc.pubPost = tail.pc.pubPre) :
    CohortProofChain hash S start fin where
  legs := [lead, tail]
  legSat := hsat
  headPre := by simpa using hheadPre
  lastPost := by simpa using hlastPost
  seam := by
    rw [List.isChain_cons]
    refine ⟨?_, by simp⟩
    intro b hb
    simp only [List.head?_cons, Option.mem_some_iff] at hb
    subst hb; exact hseam
  pubChain := by
    -- a two-element chain: the single relation `lead → tail` is `hchain`.
    rw [List.isChain_cons]
    refine ⟨?_, by simp⟩
    intro b hb
    simp only [List.head?_cons, Option.mem_some_iff] at hb
    subst hb; exact hchain

/-- **`unchained_tail_rejects`** — the SAME honest 2-cohort shape, but with the tail leg UNCHAINED
(`lead.pc.pubPost ≠ tail.pc.pubPre` — the deployed splice/drop signature: the tail's `OLD_COMMIT` no longer
matches the lead's `NEW_COMMIT`), is REJECTED: it cannot be a `CohortProofChain`. This is `chainBroken_rejects`
at the 2-leg list `[lead, tail]` (empty prefix, empty rest). The deployed adjacency check `this_old ==
prev_new` BITES exactly here. -/
theorem unchained_tail_rejects
    {hash : List ℤ → ℤ} {S : CommitSurface} {start fin : RecChainedState}
    (lead tail : DecodedStep S)
    (hbad : lead.pc.pubPost ≠ tail.pc.pubPre)
    (c : CohortProofChain hash S start fin)
    (hlegs : c.legs = [lead, tail]) :
    False :=
  chainBroken_rejects lead tail [] [] hbad c (by simpa using hlegs)

/-! ## §5 — axiom hygiene. -/

#assert_axioms CohortProofChain.toTurnDecodeChain
#assert_axioms chainForcesEveryCohort
#assert_axioms cohort_chain_forces_tail
#assert_axioms lightclient_cohort_chain_forces_full_turn
#assert_axioms chainBroken_rejects
#assert_axioms cohort_chain_accepts_honest
#assert_axioms unchained_tail_rejects

end Dregg2.Circuit.RotatedKernelForestCohortChain
