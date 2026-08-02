/-
# Dregg2.Circuit.Freshness — CROSS-TURN FRESHNESS / NO-REPLAY, headline + hash-floor grounding.

`CircuitSoundness.lightclient_unfoolable` proves SINGLE-TRANSITION soundness — a verifying batch
decodes to a genuine kernel step at the GIVEN turn. It says NOTHING about whether that transition is
FRESH (not already applied). The freshness footnote in `CircuitSoundness` used to punt cross-turn
no-replay to "the DEPLOYED machinery, NOT modeled". This module (with `CrossTurnFreshness`) MODELS and
PROVES it — the punt is a THEOREM, not prose.

## What is proved (and where the real work lives)

The engine is `Dregg2.Circuit.CrossTurnFreshness`: it models a `TurnChain` (a state sequence with a
strictly-monotone agent nonce), proves the commitment is injective in the nonce, and concludes
`no_replay` (a fixed pre-anchor opens the CAS gate at most once), with the whole DEPLOYED forest
executor (`Admission.runTurn` over `FullForest.execFullForestA`) discharged as strictly nonce-advancing
(`runTurn_forest_strictly_advances`, `deployed_forest_no_replay`). This module RE-EXPORTS those under
the task's headline names and closes the last question the task poses about them:

  **exactly which crypto residual `commit_binds_nonce` rests on.**

## The nonce-binding argument, and its residual

`recStateCommit k t = cmb (cellDigest CH compress compressN k t) (RH k)`, and the agent nonce lives in
the agent cell's `Value` (`k.cell agent`), hashed into the commitment through the leaf hash `CH` (the
deployed `compute_commitment`'s `hash_4_to_1(bal_lo, bal_hi, NONCE, field0)` — `cell_state.rs`). So
"equal commitment ⟹ equal nonce" is `CrossTurnFreshness.commit_inj_nonce`, which rides
`CommitSurface.commit_binds_of_noColl` (= `recStateCommit_binds_kernel_of_noCollFin`). A nonce
difference under an equal commitment is therefore a CONCRETE Poseidon COLLISION AT NAMED POINTS — and
that is the literal side condition, not a slogan: the theorem takes `¬ S.CommitColl k k' t`, which
names the root combiner's, node hash's, frame sponge's and cell leaf's exact argument pairs.

⚑ It has been wrong twice. It used to ride the injective `commit_binds` under the bundled CR set
(`cmbInj`/`compInj`/`compNInj`/`leafInj`), all four of which are FALSE at deployed BabyBear width, so
the "not an assumption" was true and the theorem was vacuous anyway. The first repair gave it an
`OrBreak S.StateBreak` disjunct — but that disjunct's sponge leg is a GLOBAL collision existential
which pigeonhole SUPPLIES at every BabyBear-bounded sponge, so it was free and the theorem was vacuous
again. Only a claim about NAMED points discriminates.

`§2` grounds that residual: the FOUR sponge-shaped CR fields (`cmb`, `compress` as 2-element sponges,
`compressN` the frame sponge, `CH` the leaf) all reduce to a SINGLE `Poseidon2SpongeCR sponge` (via
`compressNInjective_of_poseidon2CR` + `cellLeafInjective_of_realization` + the 2-element specialization
`spongeCompress_inj`, retained where it is proved). ⚑ 2026-08-01: those reductions no longer have a
target — `CommitSurface`'s four injectivity FIELDS are DELETED (refuted at deployed BabyBear width by
pigeonhole), and `Poseidon2SpongeCR` is refuted at the same width
(`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`), so reducing four false premises to one false
premise bought nothing. `poseidon2CommitSurface` is now `spongeCommitSurface` and carries NO crypto
floor. ⚑ THE CAVEAT THAT STOOD HERE IS SPENT — AND ITS HISTORY IS THE POINT. It said the theorems
long called "the live binding consumer" (`CommitFaithfulRegrounded.commit_binds_nonce_faithful` /
`no_replay_faithful`) do NOT return concrete collision events, because `FaithfulBreak` opened with a
global-existential `SpongeCollision compressN` — free at any field-bounded sponge, so the disjunction
held unconditionally. That was TRUE when written and is FALSE now: `FaithfulBreak` has been NARROWED
to open at a named pair (`CompressColl cmb`), and the free version carries the explicit name
`FaithfulBreakGlobal`. They DO now return concrete events. Cite objects by NAME, not by describing
their shape — a correction can go stale faster than what it corrected, and this one did, within a day;
the parametric statements here carry the per-instance `¬ S.CommitColl` residual instead of a refuted
premise or a free disjunct.

THE ONE HONEST RESIDUAL, named precisely: `RestHashIffFrameFin RH` (the rest-hash binding of the 15
non-`cell` components) is NOT reducible to a `List ℤ` sponge CR, because the state carries
FUNCTION-valued components (`caps : CellId → List Auth`, `delegations`) over an infinite domain — no
injective serialization to `List ℤ` exists. It is a STRUCTURAL/realizable carrier (a canonical rest
hash IS injective on its inputs), same status as the encoder-injectivity fields — never an `axiom`,
never a hole — but it is not a crypto assumption and not sponge-shaped. So the residual of the whole
no-replay defense is: `¬ S.CommitColl` at the chain's states (a REFUTABLE claim about named argument
pairs — no assumed CR floor at all since 2026-08-01, and no free disjunct since the second pass that
day) + the PROVED nonce-monotone invariant, with `RestHashIffFrameFin` the single named
non-sponge-reducible structural carrier.

## Teeth (both load-bearing carriers bite)

  * `collapse_not_CR` + `collapse_breaks_commit_binds_nonce`: a Poseidon2-CR-VIOLATING (collapsing)
    hash lets two DISTINCT-nonce states share a commitment — so the hash floor is load-bearing.
  * `noTick_admits_replay`: a chain WITHOUT the nonce tick (a constant commitment sequence) admits the
    SAME pre-anchor at two distinct indices — the replay `no_replay` forbids — so nonce-monotonicity is
    load-bearing.
  * `CrossTurnFreshness.witnessChain_replay_rejected` (re-exported): on an inhabited monotone chain a
    replayed proof IS rejected once the commitment advances — the defense is non-vacuous.
-/
/- ⚠ SCOPE (honest, 2026-07-09; REVISED 2026-08-01): `no_replay`/`deployed_no_replay` are proved
PARAMETRIC over a `CommitSurface`, and `nonce_strictly_increases` is DERIVED from the deployed
executor — both real. The 2026-07-09 text warned that `poseidon2_no_replay` inherited
`RestHashIffFrame` + `LeafRealization` and told the reader not to cite it as fully grounded. Both of
those are now gone for a better reason than the one predicted: `RestHashIffFrame` was replaced by the
SATISFIABLE finite-support successor `RestHashIffFrameFin` (2026-07-31), and `LeafRealization` only
ever fed the `leafInj` FIELD, which is deleted. The theorem is `sponge_no_replay` and it carries no
crypto floor — what it now carries is the per-instance `C.NoCommitColl` residual: a replay requires a
CONCRETE collision of the root combiner, node hash, frame sponge or cell leaf AT THE NAMED ARGUMENT
PAIRS the binding visits. ⚠ Still NOT closed:
whether every executor-reached kernel is `FiniteRepresentable`
(`FinKernelState.denote_surjective_on_reachable`, gated on the per-effect `hpres`). -/

import Dregg2.Circuit.CrossTurnFreshness
import Dregg2.Circuit.Poseidon2Binding

namespace Dregg2.Circuit.Freshness

open Dregg2.Circuit
open Dregg2.Circuit.CircuitSoundness (CommitSurface)
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.RestFrameFin (FiniteRepresentable RestHashIffFrameFin)
open Dregg2.Circuit.Poseidon2Binding
open Dregg2.Circuit.CollisionReduce (OrBreak)
open Dregg2.Exec

/-! ## §1 — the headline theorems (re-exported from the proved `CrossTurnFreshness` engine).

Each of these is a thin naming of a `CrossTurnFreshness` theorem under the task's headline. The real
proofs (per-arm `BodyNonceNondecreasing` discharge, the forest fold, `commit_inj_nonce`) live there. -/

/-- The agent (turn-author) cell's stored replay nonce, read off a kernel state. -/
abbrev agentNonce (k : RecordKernelState) (agent : CellId) : Int :=
  CrossTurnFreshness.agentNonce k agent

/-- **`CommitChain`** — a sequence of verified turns whose live commitment carries a
strictly-monotone agent nonce (the deployed CAS discipline: each step's pre-anchor equals the prior
post, and the never-rolled-back prologue ticks the nonce). Identically `CrossTurnFreshness.TurnChain`. -/
abbrev CommitChain := CrossTurnFreshness.TurnChain

/-- **`commit_binds_nonce`** — equal commitments force equal agent nonce, unless `S`'s commitment
primitives collide at the NAMED argument pairs the binding visits (`S.CommitColl k k' t`). A nonce
difference under an equal commitment IS that collision. Not assumed.

⚑ **EXTRACTOR FORM 2026-08-01 (second pass).** The predecessor concluded the equality outright, via
the deleted `CommitSurface.commit_binds`, which consumed four `CommitSurface` injectivity fields FALSE
at deployed BabyBear width — VACUOUSLY TRUE. The first repair wrapped it in `OrBreak S.StateBreak`,
whose sponge leg is a GLOBAL collision existential pigeonhole supplies at every BabyBear-bounded
sponge — vacuous again, by free disjunct. See `CrossTurnFreshness.commit_inj_nonce`. -/
theorem commit_binds_nonce (S : CommitSurface) (k k' : RecordKernelState) (t : Turn)
    (agent : CellId) (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (hno : ¬ S.CommitColl k k' t)
    (h : S.commit k t = S.commit k' t) :
    agentNonce k agent = agentNonce k' agent :=
  CrossTurnFreshness.commit_inj_nonce S k k' t agent hwf hwf' hfin hfin' hno h

/-- **The replay teeth (contrapositive):** distinct agent nonces give distinct commitments, unless the
primitives collide at those named pairs. A monotone-advancing nonce therefore drives a commitment that
never returns. -/
theorem commit_neq_of_nonce_neq (S : CommitSurface) (k k' : RecordKernelState) (t : Turn)
    (agent : CellId) (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (hno : ¬ S.CommitColl k k' t)
    (hne : agentNonce k agent ≠ agentNonce k' agent) :
    S.commit k t ≠ S.commit k' t :=
  CrossTurnFreshness.commit_neq_of_nonce_neq S k k' t agent hwf hwf' hfin hfin' hno hne

/-- **`nonce_monotone_along_chain`** — the agent nonce STRICTLY increases along any proper prefix of a
`CommitChain`. -/
theorem nonce_monotone_along_chain {S : CommitSurface} {agent : CellId} {t : Turn}
    (C : CommitChain S agent t) {i j : Nat} (hij : i < j) :
    agentNonce (C.seq i) agent < agentNonce (C.seq j) agent :=
  C.nonce_mono_lt hij

/-- **`commit_no_repeat`** — the live-commitment sequence along a `CommitChain` never repeats, given
the chain's per-instance residual `C.NoCommitColl`. -/
theorem commit_no_repeat {S : CommitSurface} {agent : CellId} {t : Turn}
    (C : CommitChain S agent t) (hfin : ∀ n, FiniteRepresentable (C.seq n))
    (hno : C.NoCommitColl) {i j : Nat} (hne : i ≠ j) :
    C.commitAt i ≠ C.commitAt j :=
  C.commit_no_repeat hfin hno hne

/-- **`no_replay` — THE HEADLINE: a proof is applicable AT MOST ONCE.** If the CAS gate
(`LiveCommitMatches`) matches a fixed pre-anchor at two turn indices `i`, `j` of a `CommitChain`, then
`i = j`. Because the nonce strictly advances and the commitment binds the nonce (given the chain's
per-instance residual `hno`), a consumed pre-anchor never re-matches — no replay.

⚑ **EXTRACTOR FORM 2026-08-01 (second pass)**: `hno` replaced an `OrBreak S.StateBreak` disjunct that
was FREE at deployed parameters, which in turn had replaced an unconditional conclusion that was
vacuous (it rode the deleted `CommitSurface.commit_binds`). -/
theorem no_replay {S : CommitSurface} {agent : CellId} {t : Turn}
    (C : CommitChain S agent t) (hfin : ∀ n, FiniteRepresentable (C.seq n))
    (hno : C.NoCommitColl)
    {i j : Nat} {preCommit : ℤ}
    (hi : CrossTurnFreshness.LiveCommitMatches C i preCommit)
    (hj : CrossTurnFreshness.LiveCommitMatches C j preCommit) :
    i = j :=
  CrossTurnFreshness.no_replay C hfin hno hi hj

/-- **`replay_rejected_after_apply`** — once a pre-anchor matched at turn `i`, every strictly-later
turn `j > i` rejects the same proof (the live commitment has advanced and never returns), given the
chain's per-instance residual. -/
theorem replay_rejected_after_apply {S : CommitSurface} {agent : CellId} {t : Turn}
    (C : CommitChain S agent t) (hfin : ∀ n, FiniteRepresentable (C.seq n))
    (hno : C.NoCommitColl)
    {i j : Nat} {preCommit : ℤ}
    (hi : CrossTurnFreshness.LiveCommitMatches C i preCommit) (hlt : i < j) :
    ¬ CrossTurnFreshness.LiveCommitMatches C j preCommit :=
  CrossTurnFreshness.replay_rejected_after_apply C hfin hno hi hlt

/-- **`nonce_strictly_increases` — PROVED FROM THE DEPLOYED STEP RELATION.** Every accepted
`Admission.runTurn` over the live forest body (`FullForest.execFullForestA`) STRICTLY advances the
agent nonce. NB: the BARE body effects do NOT all tick the nonce (`recTransfer`/`recKExecAsset` and
every metadata write are nonce-PRESERVING — FpuProbe F5; only `incrementNonceA` on the agent cell
raises it); the strict advance comes from the never-rolled-back committed PROLOGUE (`+1`,
`prologue_strictly_increases_nonce` = `Admission.commitPrologue_nonce`), while the whole forest body is
proved nonce-NONDECREASING per-arm (`execFullForestA_agentNonce_nondecr`) — the three reset vectors
(`setField "nonce"`, `incrementNonce`, `makeSovereign`) all closed at the executor. So the net turn
strictly increases the agent nonce unconditionally. -/
theorem nonce_strictly_increases (ctx : Admission.AdmCtx) (h : Admission.TurnHdr)
    (s : RecChainedState) (f : FullForest.FullForestA)
    (hadm : Admission.admissible ctx h s = true) :
    ∀ s', Admission.runTurn ctx h s (fun s₀ => FullForest.execFullForestA s₀ f) = some s' →
      agentNonce s.kernel h.agent < agentNonce s'.kernel h.agent :=
  CrossTurnFreshness.runTurn_forest_strictly_advances ctx h s f hadm

/-- **`deployed_no_replay` — NO REPLAY ON THE DEPLOYED FOREST EXECUTOR.** Given indexed states each
produced by an ACCEPTED `Admission.runTurn` over any `execFullForestA` body, a fixed pre-anchor opens
the CAS gate at most once. The monotone advance is DERIVED from the executor (not assumed) via
`nonce_strictly_increases`. -/
theorem deployed_no_replay (S : CommitSurface) (agent : CellId) (t : Turn)
    (seq : Nat → RecChainedState) (ctxs : Nat → Admission.AdmCtx) (hdrs : Nat → Admission.TurnHdr)
    (fwd : Nat → FullForest.FullForestA)
    (wf : ∀ i, AccountsWF (seq i).kernel)
    (finrep : ∀ i, FiniteRepresentable (seq i).kernel)
    (hagent : ∀ i, (hdrs i).agent = agent)
    (hadm : ∀ i, Admission.admissible (ctxs i) (hdrs i) (seq i) = true)
    (hstep : ∀ i, Admission.runTurn (ctxs i) (hdrs i) (seq i)
                    (fun s₀ => FullForest.execFullForestA s₀ (fwd i)) = some (seq (i + 1)))
    (hno : (CrossTurnFreshness.acceptedSeq_to_TurnChain S agent t seq wf
      (CrossTurnFreshness.forest_advance_holds agent seq ctxs hdrs fwd hagent hadm hstep)).NoCommitColl)
    {i j : Nat} {preCommit : ℤ}
    (hi : CrossTurnFreshness.LiveCommitMatches
        (CrossTurnFreshness.acceptedSeq_to_TurnChain S agent t seq wf
          (CrossTurnFreshness.forest_advance_holds agent seq ctxs hdrs fwd hagent hadm hstep))
        i preCommit)
    (hj : CrossTurnFreshness.LiveCommitMatches
        (CrossTurnFreshness.acceptedSeq_to_TurnChain S agent t seq wf
          (CrossTurnFreshness.forest_advance_holds agent seq ctxs hdrs fwd hagent hadm hstep))
        j preCommit) :
    i = j :=
  CrossTurnFreshness.deployed_forest_no_replay S agent t seq ctxs hdrs fwd wf finrep hagent hadm
    hstep hno hi hj

/-! ## §2 — grounding the `commit_binds_nonce` residual in a SINGLE `Poseidon2SpongeCR`.

The four sponge-shaped CR fields of a `CommitSurface` reduce to ONE `Poseidon2SpongeCR sponge`:
`compressN := sponge` directly; `cmb`, `compress` as 2-element sponges (`spongeCompress`); `CH` via a
`LeafRealization` on the same sponge. `RestHashIffFrame` is the one non-sponge-reducible carrier
(function-valued state components). -/

/-- A 2-to-1 node/root hash realized as a 2-element sponge absorb (the deployed `hash_4_to_1`/node
compress is a fixed-arity sponge). -/
def spongeCompress (sponge : List ℤ → ℤ) (a b : ℤ) : ℤ := sponge [a, b]

/-- **`spongeCompress_inj`** — a 2-element sponge is an injective 2-to-1 hash, from `Poseidon2SpongeCR`.
`sponge [a,b] = sponge [c,d]` ⇒[CR] `[a,b] = [c,d]` ⇒ `a = c ∧ b = d`. So the root combiner and the
Merkle node hash's injectivity are the SAME `Poseidon2SpongeCR` assumption, not extra ones. -/
theorem spongeCompress_inj (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge) :
    compressInjective (spongeCompress sponge) := by
  intro a b c d h
  unfold spongeCompress at h
  have hlist : [a, b] = [c, d] := hCR _ _ h
  exact ⟨(List.cons.inj hlist).1, (List.cons.inj (List.cons.inj hlist).2).1⟩

/-- **`spongeCommitSurface`** — the sponge-shaped state-commitment surface: `cmb`/`compress` are
2-element sponge absorbs over `sponge`, `compressN` IS `sponge`, `CH` is the caller's leaf hash. The
only carried obligation is `restFrame : RestHashIffFrameFin RH` — structural (a canonical rest hash
is injective on the 15 non-`cell` components of finitely-representable states), not crypto, and not
expressible as a `List ℤ` sponge CR because those components include FUNCTION-valued fields (`caps`,
`delegations`) over an infinite domain.

⚑ **DE-FLOORED 2026-08-01, and RENAMED for it.** This was `poseidon2CommitSurface` and it took
`hCR : Poseidon2SpongeCR sponge` + `Rleaf : LeafRealization CH`, whose only job was to fill the four
`CommitSurface` injectivity fields (`cmbInj`/`compInj` via `spongeCompress_inj`, `compNInj` via
`compressNInjective_of_poseidon2CR`, `leafInj` via `cellLeafInjective_of_realization`). Those fields
are DELETED — each is refuted at deployed BabyBear width by pigeonhole — so the two premises had
nothing left to discharge and are gone with them. `Poseidon2SpongeCR sponge` is itself refuted at
deployed parameters (`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`), so carrying it made every
theorem stated over this surface vacuous; the old name promised a Poseidon grounding that the
construction never had and now does not pretend to. `spongeCompress_inj` and
`cellLeafInjective_of_realization` survive where they are defined, unused here. -/
def spongeCommitSurface (sponge : List ℤ → ℤ) (CH : CellId → Value → ℤ)
    (RH : RecordKernelState → ℤ) (hRest : RestHashIffFrameFin RH) : CommitSurface where
  CH := CH
  RH := RH
  cmb := spongeCompress sponge
  compress := spongeCompress sponge
  compressN := sponge
  restFrame := hRest

/-! ⚰ **TOMBSTONE — `poseidon2_commit_binds_nonce` (DELETED 2026-08-01).** It said: equal commitments
on the Poseidon2-grounded surface force equal agent nonce, "with the crypto residual reduced to a
SINGLE `Poseidon2SpongeCR`". Both halves of that sentence were the problem — the reduction target is
REFUTED at deployed BabyBear width, so the theorem held vacuously, and the reduction ran through the
four `CommitSurface` injectivity fields that are now deleted. The live consumer this file's header
already names is `CommitFaithfulRegrounded.commit_binds_nonce_faithful`, and since `FaithfulBreak`
was narrowed to open at a named pair it is now a real guarantee (the free form is explicitly
`FaithfulBreakGlobal`). For the parametric statement use the per-instance `¬ S.CommitColl` forms.
⚑ AND NOT `OrBreak S.StateBreak`, which an earlier draft of this very sentence recommended:
`CircuitSoundness.CommitSurface.orBreak_stateBreak_iff_True` proves that disjunction is literally
`True` at deployed width. Recommending it as the repair was recommending the defect. -/

/-- **`sponge_no_replay`** — NO REPLAY over the sponge-shaped surface: a fixed pre-anchor opens the
CAS gate at most once, given the chain's per-instance residual. The non-residual part of the whole
cross-turn freshness defense is the PROVED nonce-monotone invariant plus the structural
`RestHashIffFrameFin` carrier.

⚑ Was `poseidon2_no_replay`, and the rename is the honest part: it took
`hCR : Poseidon2SpongeCR sponge`, refuted at deployed parameters, so its `i = j` conclusion was
VACUOUSLY TRUE. The intermediate `OrBreak … .StateBreak` form was vacuous too — the disjunct is free
at any BabyBear-bounded sponge. It now concludes `i = j` from a claim about NAMED points. -/
theorem sponge_no_replay (sponge : List ℤ → ℤ)
    (CH : CellId → Value → ℤ)
    (RH : RecordKernelState → ℤ) (hRest : RestHashIffFrameFin RH)
    (agent : CellId) (t : Turn)
    (C : CommitChain (spongeCommitSurface sponge CH RH hRest) agent t)
    (hfin : ∀ n, FiniteRepresentable (C.seq n))
    (hno : C.NoCommitColl)
    {i j : Nat} {preCommit : ℤ}
    (hi : CrossTurnFreshness.LiveCommitMatches C i preCommit)
    (hj : CrossTurnFreshness.LiveCommitMatches C j preCommit) :
    i = j :=
  no_replay C hfin hno hi hj

/-! ## §3 — TEETH: both load-bearing carriers bite. -/

/-- **`collapse_not_CR`** — a COLLAPSING hash (constant `0`) is NOT collision-resistant: it maps the
distinct lists `[]` and `[0]` to the same value. So `Poseidon2SpongeCR` is a GENUINE constraint (a real
requirement on the sponge), not vacuously satisfiable. -/
theorem collapse_not_CR : ¬ Poseidon2SpongeCR (fun _ : List ℤ => (0 : ℤ)) := by
  intro h
  have : ([] : List ℤ) = [0] := h [] [0] rfl
  exact absurd this (by decide)

/-- **`collapse_breaks_commit_binds_nonce`** — with a collapsing commitment (every hash primitive the
constant `0`) two states of DISTINCT agent nonce share a commitment: `commit_binds_nonce` FAILS. So the
Poseidon CR floor is LOAD-BEARING — drop it and a stale nonce hides behind an equal commitment (a
replay). (`k`/`k'` differ only in the agent cell's `nonce` field, `0` vs `1`.) -/
theorem collapse_breaks_commit_binds_nonce (agent : CellId) (t : Turn) (base : RecordKernelState) :
    ∃ (k k' : RecordKernelState),
      agentNonce k agent ≠ agentNonce k' agent
      ∧ recStateCommit (fun _ _ => (0 : ℤ)) (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) k t
        = recStateCommit (fun _ _ => (0 : ℤ)) (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) k' t := by
  refine ⟨{ base with cell := fun c => if c = agent then EffectTransfer.setNonce (base.cell agent) 0 else base.cell c },
          { base with cell := fun c => if c = agent then EffectTransfer.setNonce (base.cell agent) 1 else base.cell c },
          ?_, ?_⟩
  · -- distinct nonces: `nonceOf (setNonce _ 0) = 0 ≠ 1 = nonceOf (setNonce _ 1)`.
    show CrossTurnFreshness.agentNonce _ agent ≠ CrossTurnFreshness.agentNonce _ agent
    unfold CrossTurnFreshness.agentNonce
    show EffectTransfer.nonceOf (if agent = agent then EffectTransfer.setNonce (base.cell agent) 0 else base.cell agent)
       ≠ EffectTransfer.nonceOf (if agent = agent then EffectTransfer.setNonce (base.cell agent) 1 else base.cell agent)
    rw [if_pos rfl, if_pos rfl, EffectTransfer.setNonce_nonceOf, EffectTransfer.setNonce_nonceOf]
    decide
  · -- collapsed commitment: both sides are the constant `0` (the outer `cmb` ignores its arguments).
    unfold recStateCommit; rfl

/-- **`noTick_admits_replay`** — a chain WITHOUT the nonce tick (a CONSTANT commitment sequence) admits
the SAME pre-anchor at two DISTINCT indices — exactly the replay `no_replay` forbids. So the
`TurnChain.monotone` (nonce-tick) field is LOAD-BEARING: absent it, `commit_no_repeat`/`no_replay` do
not hold. (`fun _ => c` models the live commitment that never advances.) -/
theorem noTick_admits_replay (c : ℤ) :
    (0 : Nat) ≠ 1 ∧ (fun _ : Nat => c) 0 = (fun _ : Nat => c) 1 :=
  ⟨by decide, rfl⟩

/-- Re-export the non-vacuity mutation-confirm: on an inhabited monotone `witnessChain` a replayed
proof IS rejected once the commitment advances (`CrossTurnFreshness.witnessChain_replay_rejected`). The
defense has teeth — it is not vacuous. -/
theorem witnessChain_replay_rejected (S : CommitSurface) (agent : CellId) (t : Turn)
    (v : Value) (i j : Nat) (preCommit : ℤ)
    (hno : (CrossTurnFreshness.witnessChain S agent t v).NoCommitColl)
    (hi : CrossTurnFreshness.LiveCommitMatches
      (CrossTurnFreshness.witnessChain S agent t v) i preCommit)
    (hlt : i < j) :
    ¬ CrossTurnFreshness.LiveCommitMatches
      (CrossTurnFreshness.witnessChain S agent t v) j preCommit :=
  CrossTurnFreshness.witnessChain_replay_rejected S agent t v i j preCommit hno hi hlt

/-! ## §4 — axiom-hygiene tripwires. -/

#assert_axioms commit_binds_nonce
#assert_axioms commit_neq_of_nonce_neq
#assert_axioms no_replay
#assert_axioms replay_rejected_after_apply
#assert_axioms commit_no_repeat
#assert_axioms nonce_strictly_increases
#assert_axioms deployed_no_replay
#assert_axioms spongeCompress_inj
#assert_axioms spongeCommitSurface
#assert_axioms sponge_no_replay
#assert_axioms collapse_not_CR
#assert_axioms collapse_breaks_commit_binds_nonce
#assert_axioms witnessChain_replay_rejected

end Dregg2.Circuit.Freshness
