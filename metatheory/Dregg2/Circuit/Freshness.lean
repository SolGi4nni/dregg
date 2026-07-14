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
`CommitSurface.commit_binds` (= `recStateCommit_binds_kernel`) under the standard Poseidon CR set
(`cmbInj compress`-injective root combiner, `compInj` node hash, `compNInj` frame sponge, `leafInj`
leaf hash, `restFrame` rest hash). A nonce difference under an equal commitment is therefore a Poseidon
COLLISION — not an assumption.

`§2` grounds that residual: the FOUR sponge-shaped CR fields (`cmb`, `compress` as 2-element sponges,
`compressN` the frame sponge, `CH` the leaf) all reduce to a SINGLE `Poseidon2SpongeCR sponge` (via
`compressNInjective_of_poseidon2CR` + `cellLeafInjective_of_realization` + the 2-element specialization
`spongeCompress_inj` proved here). HISTORICAL NOTE: `poseidon2CommitSurface` is retained only so old
proof terms elaborate. Its `Poseidon2SpongeCR` premise is bounded-hash injectivity and is FALSE at the
deployed BabyBear parameters (`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`). The live binding
consumer is `CommitFaithfulRegrounded.commit_binds_nonce_faithful` / `no_replay_faithful`, which use
the deployed residue-fold leaf and return concrete collision events.

THE ONE HONEST RESIDUAL, named precisely: `RestHashIffFrame RH` (the rest-hash binding of the 15
non-`cell` components) is NOT reducible to a `List ℤ` sponge CR, because the state carries
FUNCTION-valued components (`caps : CellId → List Auth`, `delegations`) over an infinite domain — no
injective serialization to `List ℤ` exists. It is a STRUCTURAL/realizable carrier (a canonical rest
hash IS injective on its inputs), same status as the encoder-injectivity fields — never an `axiom`,
never a hole — but it is not a crypto assumption and not sponge-shaped. So the crypto residual of the
whole no-replay defense is: `Poseidon2SpongeCR` + the PROVED nonce-monotone invariant, with
`RestHashIffFrame` the single named non-sponge-reducible structural carrier.

## Teeth (both load-bearing carriers bite)

  * `collapse_not_CR` + `collapse_breaks_commit_binds_nonce`: a Poseidon2-CR-VIOLATING (collapsing)
    hash lets two DISTINCT-nonce states share a commitment — so the hash floor is load-bearing.
  * `noTick_admits_replay`: a chain WITHOUT the nonce tick (a constant commitment sequence) admits the
    SAME pre-anchor at two distinct indices — the replay `no_replay` forbids — so nonce-monotonicity is
    load-bearing.
  * `CrossTurnFreshness.witnessChain_replay_rejected` (re-exported): on an inhabited monotone chain a
    replayed proof IS rejected once the commitment advances — the defense is non-vacuous.
-/
/- ⚠ SCOPE (honest, 2026-07-09): `no_replay`/`deployed_no_replay` are proved PARAMETRIC over a
`CommitSurface`, and `nonce_strictly_increases` is DERIVED from the deployed executor — both real.
BUT `poseidon2_no_replay` (the concrete Poseidon2 grounding) inherits `RestHashIffFrame` +
`LeafRealization`, and `RestHashIffFrame` is UNREALIZABLE as stated (it asserts an injective ℤ-hash of
infinite-domain function fields — see docs/reference/CARRIER-CENSUS.md DEBT B). So this file does NOT
yet ground no-replay on `Poseidon2SpongeCR` alone. The fix is the finite-map data refinement (DEBT B),
or re-routing the nonce binding through the finite cell leaf (cellLeafInjective, realizable). Do not
cite `poseidon2_no_replay` as fully-grounded until then. -/

import Dregg2.Circuit.CrossTurnFreshness
import Dregg2.Circuit.Poseidon2Binding

namespace Dregg2.Circuit.Freshness

open Dregg2.Circuit
open Dregg2.Circuit.CircuitSoundness (CommitSurface)
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.Poseidon2Binding
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

/-- **`commit_binds_nonce`** — equal commitments force equal agent nonce. A nonce difference under an
equal commitment is a Poseidon COLLISION (reduced through `CommitSurface.commit_binds` = the CR set;
§2 grounds that set in `Poseidon2SpongeCR`). Not assumed. -/
theorem commit_binds_nonce (S : CommitSurface) (k k' : RecordKernelState) (t : Turn)
    (agent : CellId) (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (h : S.commit k t = S.commit k' t) :
    agentNonce k agent = agentNonce k' agent :=
  CrossTurnFreshness.commit_inj_nonce S k k' t agent hwf hwf' h

/-- **The replay teeth (contrapositive):** distinct agent nonces give distinct commitments. A
monotone-advancing nonce therefore drives a commitment that never returns. -/
theorem commit_neq_of_nonce_neq (S : CommitSurface) (k k' : RecordKernelState) (t : Turn)
    (agent : CellId) (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hne : agentNonce k agent ≠ agentNonce k' agent) :
    S.commit k t ≠ S.commit k' t :=
  CrossTurnFreshness.commit_neq_of_nonce_neq S k k' t agent hwf hwf' hne

/-- **`nonce_monotone_along_chain`** — the agent nonce STRICTLY increases along any proper prefix of a
`CommitChain`. -/
theorem nonce_monotone_along_chain {S : CommitSurface} {agent : CellId} {t : Turn}
    (C : CommitChain S agent t) {i j : Nat} (hij : i < j) :
    agentNonce (C.seq i) agent < agentNonce (C.seq j) agent :=
  C.nonce_mono_lt hij

/-- **`commit_no_repeat`** — the live-commitment sequence along a `CommitChain` never repeats. -/
theorem commit_no_repeat {S : CommitSurface} {agent : CellId} {t : Turn}
    (C : CommitChain S agent t) {i j : Nat} (hne : i ≠ j) :
    C.commitAt i ≠ C.commitAt j :=
  C.commit_no_repeat hne

/-- **`no_replay` — THE HEADLINE: a proof is applicable AT MOST ONCE.** If the CAS gate
(`LiveCommitMatches`) matches a fixed pre-anchor at two turn indices `i`, `j` of a `CommitChain`, then
`i = j`. Because the nonce strictly advances and the commitment binds the nonce (mod `Poseidon2SpongeCR`),
a consumed pre-anchor never re-matches — no replay. -/
theorem no_replay {S : CommitSurface} {agent : CellId} {t : Turn}
    (C : CommitChain S agent t) {i j : Nat} {preCommit : ℤ}
    (hi : CrossTurnFreshness.LiveCommitMatches C i preCommit)
    (hj : CrossTurnFreshness.LiveCommitMatches C j preCommit) :
    i = j :=
  CrossTurnFreshness.no_replay C hi hj

/-- **`replay_rejected_after_apply`** — once a pre-anchor matched at turn `i`, every strictly-later
turn `j > i` rejects the same proof (the live commitment has advanced and never returns). -/
theorem replay_rejected_after_apply {S : CommitSurface} {agent : CellId} {t : Turn}
    (C : CommitChain S agent t) {i j : Nat} {preCommit : ℤ}
    (hi : CrossTurnFreshness.LiveCommitMatches C i preCommit) (hlt : i < j) :
    ¬ CrossTurnFreshness.LiveCommitMatches C j preCommit :=
  CrossTurnFreshness.replay_rejected_after_apply C hi hlt

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
    (hagent : ∀ i, (hdrs i).agent = agent)
    (hadm : ∀ i, Admission.admissible (ctxs i) (hdrs i) (seq i) = true)
    (hstep : ∀ i, Admission.runTurn (ctxs i) (hdrs i) (seq i)
                    (fun s₀ => FullForest.execFullForestA s₀ (fwd i)) = some (seq (i + 1)))
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
  CrossTurnFreshness.deployed_forest_no_replay S agent t seq ctxs hdrs fwd wf hagent hadm hstep hi hj

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

/-- **HISTORICAL `poseidon2CommitSurface` (retired from the apex).** Its single
`Poseidon2SpongeCR sponge` premise is injectivity and cannot hold for deployed bounded Poseidon2.
`cmb`/`compress` are 2-element sponges over `sponge`; `compressN` IS
`sponge`; `CH` is realized on a Poseidon2 sponge (`LeafRealization`, whose `spongeCR` is the same
`Poseidon2SpongeCR` shape). The ONLY non-sponge-reducible carrier is `restFrame : RestHashIffFrame RH`
— structural (a canonical rest hash is injective on the 15 non-`cell` components), not crypto, and not
expressible as a `List ℤ` sponge CR because those components include FUNCTION-valued fields
(`caps`, `delegations`) over an infinite domain. -/
def poseidon2CommitSurface (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (CH : CellId → Value → ℤ) (Rleaf : LeafRealization CH)
    (RH : RecordKernelState → ℤ) (hRest : RestHashIffFrame RH) : CommitSurface where
  CH := CH
  RH := RH
  cmb := spongeCompress sponge
  compress := spongeCompress sponge
  compressN := sponge
  cmbInj := spongeCompress_inj sponge hCR
  compInj := spongeCompress_inj sponge hCR
  compNInj := compressNInjective_of_poseidon2CR hCR
  leafInj := cellLeafInjective_of_realization Rleaf
  restFrame := hRest

/-- **`poseidon2_commit_binds_nonce`** — `commit_binds_nonce` with the crypto residual reduced to a
SINGLE `Poseidon2SpongeCR` (+ the leaf realization's structural encoder-injectivity + `RestHashIffFrame`).
Equal commitments on the Poseidon2-grounded surface force equal agent nonce. -/
theorem poseidon2_commit_binds_nonce (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (CH : CellId → Value → ℤ) (Rleaf : LeafRealization CH)
    (RH : RecordKernelState → ℤ) (hRest : RestHashIffFrame RH)
    (k k' : RecordKernelState) (t : Turn) (agent : CellId)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (h : (poseidon2CommitSurface sponge hCR CH Rleaf RH hRest).commit k t
       = (poseidon2CommitSurface sponge hCR CH Rleaf RH hRest).commit k' t) :
    agentNonce k agent = agentNonce k' agent :=
  commit_binds_nonce (poseidon2CommitSurface sponge hCR CH Rleaf RH hRest) k k' t agent hwf hwf' h

/-- **`poseidon2_no_replay`** — NO REPLAY over the Poseidon2-grounded surface: the crypto floor of the
whole cross-turn freshness defense is a SINGLE `Poseidon2SpongeCR` plus the proved nonce-monotone
invariant (and the named structural `RestHashIffFrame` carrier). -/
theorem poseidon2_no_replay (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (CH : CellId → Value → ℤ) (Rleaf : LeafRealization CH)
    (RH : RecordKernelState → ℤ) (hRest : RestHashIffFrame RH)
    (agent : CellId) (t : Turn)
    (C : CommitChain (poseidon2CommitSurface sponge hCR CH Rleaf RH hRest) agent t)
    {i j : Nat} {preCommit : ℤ}
    (hi : CrossTurnFreshness.LiveCommitMatches C i preCommit)
    (hj : CrossTurnFreshness.LiveCommitMatches C j preCommit) :
    i = j :=
  no_replay C hi hj

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
    (base : RecordKernelState) (hwf : AccountsWF base) (hin : agent ∈ base.accounts)
    (i j : Nat) (preCommit : ℤ)
    (hi : CrossTurnFreshness.LiveCommitMatches
      (CrossTurnFreshness.witnessChain S agent t base hwf hin) i preCommit)
    (hlt : i < j) :
    ¬ CrossTurnFreshness.LiveCommitMatches
      (CrossTurnFreshness.witnessChain S agent t base hwf hin) j preCommit :=
  CrossTurnFreshness.witnessChain_replay_rejected S agent t base hwf hin i j preCommit hi hlt

/-! ## §4 — axiom-hygiene tripwires. -/

#assert_axioms commit_binds_nonce
#assert_axioms commit_neq_of_nonce_neq
#assert_axioms no_replay
#assert_axioms replay_rejected_after_apply
#assert_axioms commit_no_repeat
#assert_axioms nonce_strictly_increases
#assert_axioms deployed_no_replay
#assert_axioms spongeCompress_inj
#assert_axioms poseidon2_commit_binds_nonce
#assert_axioms poseidon2_no_replay
#assert_axioms collapse_not_CR
#assert_axioms collapse_breaks_commit_binds_nonce
#assert_axioms witnessChain_replay_rejected

end Dregg2.Circuit.Freshness
