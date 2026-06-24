/-
# Dregg2.Circuit.CrossTurnFreshness — the CROSS-TURN no-replay theorem.

`CircuitSoundness.lightclient_unfoolable` proves SINGLE-TRANSITION soundness: a verifying batch
`(pi, π)` decodes to a genuine kernel step `pre ⟶ post` whose endpoint commitments ARE `pi.pre`/
`pi.post`. It takes `pi.turn` as a GIVEN; it says NOTHING about whether that transition is FRESH
(not already applied) or correctly ordered across turns. A light client that verifies `(pi, π)`
learns "this is a real transition", NOT "this is a fresh, unreplayed transition".

The cross-turn no-replay defense is NOT part of the apex; it rests on the DEPLOYED machinery:

  * the **commitment-chain CAS** (`proof_verify.rs`): the live stored commitment must equal the
    proof's pre-anchor; applying the proof advances the live commitment to the post-anchor. Modeled
    here by the `ChainHead` admission leg (`Admission.admissible`'s `prevReceipt = storedHead`) and,
    at the commitment level, by the freshness predicate `LiveCommitMatches` below.
  * **cell-nonce monotonicity** (`cell_state.rs:17` "Monotonic"): the agent's nonce is bound INTO the
    full-state commitment (it lives in `k.cell agent`, which `recStateCommit` binds via the leaf
    hash), and it STRICTLY INCREASES every turn (`Admission.commitPrologue_nonce`). So the commitment
    is injective in the nonce, and the commitment sequence along a turn-chain NEVER REPEATS.

This module models that and proves the genuine close:

  **commit-chain + nonce-monotone ⟹ each `(pre → post)` proof is applicable AT MOST ONCE.**

The argument: after applying a `(pre, post)` proof the live commitment is `post`; by
nonce-monotonicity `post`'s agent-nonce strictly exceeds `pre`'s; the commitment is injective in the
kernel (`CommitSurface.commit_binds`), hence in the nonce, so `commit post ≠ commit pre`; and by
monotone strictness no LATER state ever returns to `pre`'s commitment. So the CAS gate
(`live == pre`) fails forever after the first application — the proof cannot be replayed.

NO new axiom, NO hole, NO `:= True`. Everything rides on the already-proved `commit_binds` (the CR
set) plus the modeled monotone-nonce chain. The precise RESIDUAL — what connects this Lean model to
the deployed Rust CAS — is named at the foot (`§5`).
-/
import Dregg2.Circuit.CircuitSoundness
import Dregg2.Exec.Admission
import Dregg2.Exec.FullForest

namespace Dregg2.Circuit.CrossTurnFreshness

open Dregg2.Circuit
open Dregg2.Circuit.CircuitSoundness (CommitSurface)
open Dregg2.Circuit.StateCommit
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (FullActionA)
open Dregg2.Exec.EffectTransfer (nonceOf)

/-! ## §1 — the agent-nonce measure on a kernel state, and commitment-injectivity in it.

The replay-protection nonce of the turn's `actor` (= the agent that authors the turn). `recStateCommit`
binds the WHOLE `k.cell actor` `Value` (the leaf hash is injective in the `Value` — `cellLeafInjective`),
so equal commitments force equal agent-nonces. This is the bridge from "the commitment binds the
kernel" to "the commitment is injective in the nonce". -/

/-- The agent (turn-author) cell's stored replay nonce, read off a kernel state. -/
def agentNonce (k : RecordKernelState) (agent : CellId) : Int := nonceOf (k.cell agent)

/-- **`commit_inj_nonce` — the commitment is INJECTIVE in the agent nonce.** Two `AccountsWF` kernels
whose full-state commitments agree (at the same turn) have the SAME agent nonce. Immediate from
`CommitSurface.commit_binds` (equal commit ⟹ equal kernel ⟹ equal `cell agent` ⟹ equal nonce). This
is the load-bearing fact: a commitment cannot hide a different nonce. -/
theorem commit_inj_nonce (S : CommitSurface) (k k' : RecordKernelState) (t : Turn)
    (agent : CellId) (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (h : S.commit k t = S.commit k' t) :
    agentNonce k agent = agentNonce k' agent := by
  have hk : k = k' := S.commit_binds k k' t hwf hwf' h
  subst hk; rfl

/-- **`commit_neq_of_nonce_neq` — the contrapositive (the replay teeth).** If two `AccountsWF`
kernels carry DIFFERENT agent nonces, their full-state commitments DIFFER. A monotone-advancing
nonce therefore drives a commitment that never returns. -/
theorem commit_neq_of_nonce_neq (S : CommitSurface) (k k' : RecordKernelState) (t : Turn)
    (agent : CellId) (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hne : agentNonce k agent ≠ agentNonce k' agent) :
    S.commit k t ≠ S.commit k' t := by
  intro h
  exact hne (commit_inj_nonce S k k' t agent hwf hwf' h)

/-! ## §2 — the turn-chain model: a sequence of states with a strictly-increasing agent nonce.

A turn-chain is a function `seq : Nat → RecordKernelState` (the live kernel after `i` turns), each
`AccountsWF`, whose agent nonce is STRICTLY INCREASING (the deployed monotone nonce — each turn's
committed prologue bumps it by one, `Admission.commitPrologue_nonce`). We take the turn `t` at which
the commitment is read as fixed across the chain (the cross-turn freshness question is about the SAME
commitment surface evaluated along the chain). -/

/-- A turn-chain: indexed live kernels, all `AccountsWF`, with a strictly-monotone agent nonce. -/
structure TurnChain (S : CommitSurface) (agent : CellId) (t : Turn) where
  /-- the live kernel after `i` turns. -/
  seq      : Nat → RecordKernelState
  /-- every reachable kernel is structurally well-formed (preserved by `recKExec`). -/
  wf       : ∀ i, AccountsWF (seq i)
  /-- the agent nonce STRICTLY increases each turn (the deployed monotone nonce). -/
  monotone : ∀ i, agentNonce (seq i) agent < agentNonce (seq (i + 1)) agent

/-- The live commitment after `i` turns of a chain. -/
def TurnChain.commitAt {S : CommitSurface} {agent : CellId} {t : Turn}
    (C : TurnChain S agent t) (i : Nat) : ℤ := S.commit (C.seq i) t

/-- The agent nonce is monotone NON-strict across any prefix (`i ≤ j ⟹ nonce i ≤ nonce j`),
from strict step-monotonicity. -/
theorem TurnChain.nonce_mono_le {S : CommitSurface} {agent : CellId} {t : Turn}
    (C : TurnChain S agent t) {i j : Nat} (hij : i ≤ j) :
    agentNonce (C.seq i) agent ≤ agentNonce (C.seq j) agent := by
  -- `Nat.le_induction` on `i ≤ j`: base `j = i` reflexive; step adds one strict bump.
  induction j, hij using Nat.le_induction with
  | base => exact le_refl _
  | succ n hin ih =>
    have hstep := C.monotone n
    omega

/-- **The agent nonce is STRICTLY monotone across any proper prefix** (`i < j ⟹ nonce i < nonce j`).
The commitment-non-repetition fact rests on this. -/
theorem TurnChain.nonce_mono_lt {S : CommitSurface} {agent : CellId} {t : Turn}
    (C : TurnChain S agent t) {i j : Nat} (hij : i < j) :
    agentNonce (C.seq i) agent < agentNonce (C.seq j) agent := by
  -- `i < j` ⇒ `i + 1 ≤ j`; step-strict at `i`, then non-strict to `j`.
  have hstep := C.monotone i
  have hle := C.nonce_mono_le (show i + 1 ≤ j by omega)
  omega

/-! ## §3 — NO COMMITMENT REPEATS: the commitment sequence along a chain is injective.

The keystone. Because the agent nonce strictly increases and the commitment is injective in the
nonce, the live commitment NEVER returns to an earlier value. -/

/-- **`commit_no_repeat` — the commitment sequence has NO repeats.** For `i ≠ j`, the live
commitments at turns `i` and `j` DIFFER. (The nonces differ by strict monotonicity, and the
commitment is injective in the nonce.) This is the formal "the commitment never cycles". -/
theorem TurnChain.commit_no_repeat {S : CommitSurface} {agent : CellId} {t : Turn}
    (C : TurnChain S agent t) {i j : Nat} (hne : i ≠ j) :
    C.commitAt i ≠ C.commitAt j := by
  -- WLOG `i < j` (else swap); the nonces differ, so the commitments differ.
  rcases Nat.lt_or_ge i j with hlt | hge
  · have hnonce : agentNonce (C.seq i) agent ≠ agentNonce (C.seq j) agent :=
      ne_of_lt (C.nonce_mono_lt hlt)
    exact commit_neq_of_nonce_neq S (C.seq i) (C.seq j) t agent (C.wf i) (C.wf j) hnonce
  · have hji : j < i := lt_of_le_of_ne hge (fun h => hne h.symm)
    have hnonce : agentNonce (C.seq j) agent ≠ agentNonce (C.seq i) agent :=
      ne_of_lt (C.nonce_mono_lt hji)
    intro h
    exact commit_neq_of_nonce_neq S (C.seq j) (C.seq i) t agent (C.wf j) (C.wf i) hnonce h.symm

/-! ## §4 — the NO-REPLAY theorem: a proof is applicable at most once.

The deployed CAS reads the LIVE stored commitment and accepts a `(pre, post)` proof only when the
live commitment EQUALS the proof's pre-anchor. We model the live commitment as the chain's commitment
at the current turn index. The proof's pre-anchor is `pre`'s commitment. "Applicable at turn `i`"
means the live commitment at `i` equals the pre-anchor. -/

/-- **`LiveCommitMatches C i preCommit`** — the CAS gate: at turn index `i`, the chain's live
commitment equals the proof's pre-anchor `preCommit`. The deployed `proof_verify.rs` rejects the
proof unless this holds. -/
def LiveCommitMatches {S : CommitSurface} {agent : CellId} {t : Turn}
    (C : TurnChain S agent t) (i : Nat) (preCommit : ℤ) : Prop :=
  C.commitAt i = preCommit

/-- **`no_replay` — A PROOF IS APPLICABLE AT MOST ONCE.** If the CAS gate matches a fixed pre-anchor
`preCommit` at TWO turn indices `i` and `j`, then `i = j`: a given pre-anchor opens the gate at most
once along the whole chain. Because the live commitment never repeats (`commit_no_repeat`), two
matches of the SAME anchor force the SAME turn — there is no second moment at which a once-applied
proof re-matches. This is exactly "commit-chain + nonce-monotone ⟹ each proof applicable at most
once". -/
theorem no_replay {S : CommitSurface} {agent : CellId} {t : Turn}
    (C : TurnChain S agent t) {i j : Nat} {preCommit : ℤ}
    (hi : LiveCommitMatches C i preCommit) (hj : LiveCommitMatches C j preCommit) :
    i = j := by
  by_contra hne
  -- both match the same anchor ⇒ the two live commitments are equal ⇒ contradicts no-repeat.
  exact C.commit_no_repeat hne (by rw [hi, hj] : C.commitAt i = C.commitAt j)

/-- **`replay_rejected_after_apply` — the mutation-confirm, stated forward.** Suppose a proof's
pre-anchor matched at turn `i` (`LiveCommitMatches C i preCommit`). Then at EVERY strictly-later turn
`j > i` the gate is CLOSED for that anchor: the live commitment has advanced and never returns, so a
replay of the SAME proof is rejected (`¬ LiveCommitMatches C j preCommit`). The live commitment
`≠ pre` once it has advanced. -/
theorem replay_rejected_after_apply {S : CommitSurface} {agent : CellId} {t : Turn}
    (C : TurnChain S agent t) {i j : Nat} {preCommit : ℤ}
    (hi : LiveCommitMatches C i preCommit) (hlt : i < j) :
    ¬ LiveCommitMatches C j preCommit := by
  intro hj
  exact (Nat.ne_of_lt hlt) (no_replay C hi hj)

/-! ## §4b — the nonce-monotone bridge to the deployed prologue (the CAS realization check).

The chain's `monotone` field is REALIZED by the deployed committed prologue: each turn's
`commitPrologue` bumps the agent nonce by exactly one (`Admission.commitPrologue_nonce`), which is
`< the successor`. This lemma exhibits a single step of the realization so the `TurnChain.monotone`
obligation is GROUNDED, not free. -/

/-- A single committed-prologue step strictly increases the agent nonce (`+1`), so it discharges one
step of `TurnChain.monotone`. The deployed never-rolled-back prologue is exactly this bump. -/
theorem prologue_strictly_increases_nonce (s : RecChainedState) (agent : CellId) (fee : Int) :
    agentNonce s.kernel agent
      < agentNonce (Admission.commitPrologue s agent fee).kernel agent := by
  have h : agentNonce (Admission.commitPrologue s agent fee).kernel agent
      = agentNonce s.kernel agent + 1 := by
    unfold agentNonce
    exact Admission.commitPrologue_nonce s agent fee
  omega

/-! ## §4c — THE NO-REPLAY COMPOSITION (the payoff the reset-vector closure unblocks).

`Admission.runTurn` = admissible-gate ∘ committed-prologue ∘ rollback-able body. The replay defense
needs **every accepted turn to STRICTLY advance the AGENT's nonce** — that is what makes the accepted
state sequence a monotone `TurnChain`, to which `no_replay` applies. The prologue bumps the agent
nonce by `+1` (`prologue_strictly_increases_nonce`); the question is whether the BODY can roll it
back. With the two nonce-reset vectors now CLOSED at the executor —

  * `setField "nonce"` is REJECTED (`stateStepDev` reserved gate — `EffectsState.reservedField`), and
  * `incrementNonce` may only ADVANCE (`incrementNonceStep` monotone gate),

— no committed body effect can write the agent nonce DOWNWARD. We capture exactly that as a clean
body predicate and prove the composition; the predicate's discharge for the full forest-fold executor
is the named, mechanical residual (R2', below). -/

/-- **`BodyNonceNondecreasing body agent`** — the body never DECREASES the agent's stored nonce: on
any committed body step the post agent-nonce is `≥` the pre. This is now TRUE of the executor body
(the only two effects that touch a cell's `nonce` slot — `setFieldA`/`incrementNonceA` — can no longer
write it downward: `setFieldA "nonce"` is reserved-rejected and `incrementNonceA` is monotone-gated;
every other effect leaves the `nonce` slot fixed or, for the author's own transfer, bumps it up). The
clean hypothesis the composition rests on. -/
def BodyNonceNondecreasing (body : RecChainedState → Option RecChainedState) (agent : CellId) : Prop :=
  ∀ s₁ s', body s₁ = some s' → agentNonce s₁.kernel agent ≤ agentNonce s'.kernel agent

/-- **`runTurn_failed_strictly_advances` — the FAILED-body leg, FULLY PROVED.** An admissible turn
whose body FAILS still strictly advances the agent nonce: `runTurn` commits the prologue (never rolled
back), whose `+1` bump is in the result. No body hypothesis needed — the prologue alone advances. -/
theorem runTurn_failed_strictly_advances (ctx : Admission.AdmCtx) (h : Admission.TurnHdr)
    (s : RecChainedState) (body : RecChainedState → Option RecChainedState)
    (hadm : Admission.admissible ctx h s = true)
    (hbody : body (Admission.commitPrologue s h.agent h.fee) = none) :
    ∀ s', Admission.runTurn ctx h s body = some s' →
      agentNonce s.kernel h.agent < agentNonce s'.kernel h.agent := by
  intro s' hrun
  rw [Admission.runTurn_failed_body ctx h s body hadm hbody] at hrun
  cases hrun
  exact prologue_strictly_increases_nonce s h.agent h.fee

/-- **`runTurn_strictly_advances_agentNonce` — THE COMPOSITION (both body outcomes).** On an
admissible turn whose body is nonce-NONDECREASING (`BodyNonceNondecreasing`, true of the executor body
NOW that the reset vectors are closed), `runTurn` STRICTLY advances the agent nonce:
`agentNonce pre < agentNonce post`. The prologue bumps `+1`; the body, running on the post-prologue
state, only holds or raises it — so the net is strictly greater. This is exactly the `TurnChain.monotone`
obligation, discharged for the DEPLOYED `runTurn` (not just the abstract chain). -/
theorem runTurn_strictly_advances_agentNonce (ctx : Admission.AdmCtx) (h : Admission.TurnHdr)
    (s : RecChainedState) (body : RecChainedState → Option RecChainedState)
    (hadm : Admission.admissible ctx h s = true)
    (hmono : BodyNonceNondecreasing body h.agent) :
    ∀ s', Admission.runTurn ctx h s body = some s' →
      agentNonce s.kernel h.agent < agentNonce s'.kernel h.agent := by
  intro s' hrun
  -- the prologue's strict +1 bump.
  have hpro := prologue_strictly_increases_nonce s h.agent h.fee
  -- split on whether the body commits.
  cases hb : body (Admission.commitPrologue s h.agent h.fee) with
  | none =>
    -- failed body: runTurn = commitPrologue; the prologue advance IS the result.
    exact runTurn_failed_strictly_advances ctx h s body hadm hb s' hrun
  | some sb =>
    -- committing body: runTurn = sb; the body ran on the post-prologue state, only raising the nonce.
    have hrunsb : Admission.runTurn ctx h s body = some sb :=
      Admission.prologue_then_commit ctx h s body sb hadm hb
    have hbmono := hmono (Admission.commitPrologue s h.agent h.fee) sb hb
    rw [hrunsb] at hrun
    cases hrun
    -- agentNonce pre < agentNonce(prologue) ≤ agentNonce(body post) = agentNonce s'.
    omega

/-! ## §4c′ — DISCHARGE `BodyNonceNondecreasing` FOR THE LIVE EXECUTOR BODY (the assembly).

The composition above carries `BodyNonceNondecreasing body h.agent` as a HYPOTHESIS. Here we
DISCHARGE it for the actual deployed body — the `FullForest.execFullForestA` call-forest fold the
turn runs — by a genuine case-split over EVERY `execFullA` arm. No arm is assumed neutral: each is
proved against its dispatch target's real semantics.

THE PER-ARM TAXONOMY (verified against `TurnExecutorFull.execFullA`, not the census label):

  * **`cell`-UNCHANGED arms** (the dispatch leaves `kernel.cell` pointwise identical, so EVERY cell's
    `nonceOf` is preserved by `rfl`-grade reasoning): the per-asset ledger ops `balanceA`/`mintA`/
    `burnA`/`bridgeMintA` (edit `kernel.bal` only — `recKExecAsset`/`recKMintAsset`/`recKBurnAsset` are
    `{ k with bal := … }`), the authority ops `delegate`/`revoke`/`introduceA`/`delegateAttenA`/
    `attenuateA`/`revokeDelegationA`/`exerciseA`/`refreshDelegationA` (edit `caps`/`delegations`/epoch),
    the lifecycle ops `cellSealA`/`cellUnsealA`/`cellDestroyA`/`receiptArchiveA` (edit `lifecycle`/
    `deathCert`), the set ops `noteSpendA`/`noteCreateA` (edit `nullifiers`/`commitments`), and the
    log-only ops `emitEventA`/`pipelinedSendA`.
  * **field-write arms, written field `f ≠ "nonce"`** (so `nonceOf` is preserved by the
    `setField`-non-interference primitive `nonceOf_setField_of_ne`): `setPermissionsA` ("permissions"),
    `setVKA` ("verification_key"), `setProgramA` ("program"), `refusalA` ("refusal"), `heapWriteA`
    ("heap_root").
  * **the two NONCE-touching arms** (the replay-reset vectors the census flagged, now closed at the
    executor): `setFieldA` — REJECTED on a "nonce" write (`stateStepDev_reserved_fails`); committed
    only on `f ≠ "nonce"` (`stateStepDev_notReserved`), hence nonce-preserving; and `incrementNonceA`
    — only RAISES the written cell's nonce (`incrementNonceStep_advances`), the sole arm that moves the
    agent nonce, and it moves it UP.
  * **account-growth arms** `createCellA`/`createCellFromFactoryA`/`spawnA` — write ONLY the FRESH
    `newCell`'s cell record (born-empty / factory-installed). The creation gate forces
    `newCell ∉ accounts`; with the AGENT a live member (`agent ∈ accounts`), `newCell ≠ agent`, so the
    agent's cell is FRAMED OUT — its nonce preserved. (This is the side-condition the assembly carries:
    `agent ∈ accounts`, true post-prologue, supplied by admission.)
  * **`makeSovereignA` — the THIRD nonce-touching arm, now CLOSED at the executor** (see §4c″): the
    commitment-form rebind PRESERVES the reserved replay nonce (`makeSovereign_preserves_nonce`), so even
    making the AGENT self-sovereign holds (does not raise/lower) the agent nonce. NO carve-out: the
    formerly-needed `¬ forestTouchesSovereign` side-condition is GONE, no-replay is unconditional. -/

/-- **`nonceOf_setField_of_ne` — the field-write NON-INTERFERENCE primitive (the replay teeth at the
write level).** Writing a field `f` DISTINCT from `"nonce"` leaves the `nonce` read (`nonceOf`)
UNCHANGED. This is `EffectsState.setField_balOf`'s sibling for the nonce read instead of the balance
read — it is what makes every metadata field-write arm (`setPermissionsA`/`setVKA`/`setProgramA`/
`refusalA`/`heapWriteA`, and the non-reserved `setFieldA`) provably leave the agent nonce fixed. -/
theorem nonceOf_setField_of_ne (f : FieldName) (cell : Value) (v : Value)
    (hf : f ≠ EffectTransfer.nonceField) :
    nonceOf (EffectsState.setField f cell v) = nonceOf cell := by
  have hfn : (f == EffectTransfer.nonceField) = false := by
    simpa using beq_eq_false_iff_ne.2 hf
  -- the `nonce` scalar read is invariant under writing a DISTINCT field — list-recursion on the record,
  -- mirroring `setField_balOf`'s structure with `nonceField` in the role of `balanceField`.
  have hlist : ∀ fs : List (FieldName × Value),
      ((Value.record (EffectsState.setField.setFieldList f fs v)).scalar EffectTransfer.nonceField)
        = ((Value.record fs).scalar EffectTransfer.nonceField) := by
    intro fs
    induction fs with
    | nil =>
        simp only [EffectsState.setField.setFieldList, Value.scalar, Value.field]
        rw [List.find?_cons_of_neg (by simpa using hfn)]
    | cons hd tl ih =>
        obtain ⟨k, x⟩ := hd
        simp only [EffectsState.setField.setFieldList]
        by_cases hk : (k == f) = true
        · -- replaced field `f` (= k); the `nonce` lookup skips it either way (k = f ≠ "nonce").
          rw [if_pos hk]
          have hkn : k = f := by simpa using hk
          have hkb : (k == EffectTransfer.nonceField) = false := by rw [hkn]; exact hfn
          simp only [Value.scalar, Value.field]
          rw [List.find?_cons_of_neg (by simpa using hfn),
              List.find?_cons_of_neg (by simpa using hkb)]
        · -- kept this entry; recurse on the tail, both sides carry the same head.
          rw [if_neg hk]
          simp only [Value.scalar, Value.field] at ih ⊢
          by_cases hkb : (k == EffectTransfer.nonceField) = true
          · rw [List.find?_cons_of_pos (by simpa using hkb),
                List.find?_cons_of_pos (by simpa using hkb)]
          · rw [List.find?_cons_of_neg (by simpa using hkb),
                List.find?_cons_of_neg (by simpa using hkb)]
            exact ih
  unfold nonceOf EffectsState.setField
  cases cell with
  | record fs => rw [hlist fs]
  | int _  =>
      simp only [Value.scalar, Value.field]
      rw [List.find?_cons_of_neg (by simpa using hfn)]; rfl
  | dig _  =>
      simp only [Value.scalar, Value.field]
      rw [List.find?_cons_of_neg (by simpa using hfn)]; rfl
  | sym _  =>
      simp only [Value.scalar, Value.field]
      rw [List.find?_cons_of_neg (by simpa using hfn)]; rfl

/-- A `writeField` of a field `f ≠ "nonce"` leaves EVERY cell's `nonceOf` unchanged (the target's by
`nonceOf_setField_of_ne`, every bystander by the frame). The kernel-level lift of the primitive. -/
theorem nonceOf_writeField_of_ne (k : RecordKernelState) (f : FieldName) (target : CellId)
    (v : Value) (c : CellId) (hf : f ≠ EffectTransfer.nonceField) :
    nonceOf ((EffectsState.writeField k f target v).cell c) = nonceOf (k.cell c) := by
  unfold EffectsState.writeField
  by_cases hc : c = target
  · subst hc; simp only [if_pos rfl]; exact nonceOf_setField_of_ne f (k.cell c) v hf
  · simp only [if_neg hc]

/-- A committed `stateStep` of a field `f ≠ "nonce"` leaves every cell's `nonceOf` unchanged (the
post-state is exactly the `writeField`, `stateStep_factors`). The bridge the `setPermissionsA`/
`setVKA`/`setProgramA`/`refusalA` arms (and, via `stateStepGuarded`, `heapWriteA`/`setFieldA`) reuse. -/
theorem nonceOf_stateStep_of_ne {s s' : RecChainedState} {f : FieldName} {actor target : CellId}
    {v : Value} (c : CellId) (hf : f ≠ EffectTransfer.nonceField)
    (h : EffectsState.stateStep s f actor target v = some s') :
    nonceOf (s'.kernel.cell c) = nonceOf (s.kernel.cell c) := by
  obtain ⟨_, hs'⟩ := EffectsState.stateStep_factors h
  subst hs'
  exact nonceOf_writeField_of_ne s.kernel f target v c hf

/-- A committed per-asset mint edits ONLY `kernel.bal` (`recKMintAsset = { k with bal := … }`), so
the `cell` function — hence every cell's `nonceOf` — is unchanged. -/
theorem recKMintAsset_cell_frame {k k' : RecordKernelState} {actor cell : CellId} {a : AssetId}
    {amt : ℤ} (h : TurnExecutorFull.recKMintAsset k actor cell a amt = some k') :
    k'.cell = k.cell := by
  unfold TurnExecutorFull.recKMintAsset at h
  split at h
  · simp only [Option.some.injEq] at h; rw [← h]
  · exact absurd h (by simp)

/-- A committed per-asset burn edits ONLY `kernel.bal`, so the `cell` function is unchanged. -/
theorem recKBurnAsset_cell_frame {k k' : RecordKernelState} {actor cell : CellId} {a : AssetId}
    {amt : ℤ} (h : TurnExecutorFull.recKBurnAsset k actor cell a amt = some k') :
    k'.cell = k.cell := by
  unfold TurnExecutorFull.recKBurnAsset at h
  split at h
  · simp only [Option.some.injEq] at h; rw [← h]
  · exact absurd h (by simp)

/-! ## §4c″ — THE `makeSovereign` NONCE-RESET VECTOR, CLOSED AT THE EXECUTOR (the third reset vector).

The census reported "only the two known nonce-touching arms"; verifying the executor surfaced a THIRD.
`makeSovereignA actor target` (`TurnExecutorFull.makeSovereignStep`) drops `target`'s host-readable
record behind a 32-byte commitment (`makeSovereignKernel`/`sovereignRebind`). The OLD model replaced
the whole record with the commitment-ONLY literal `[(commitment, .dig …)]`, so the READABLE nonce fell
to `0` — and since the lifecycle stays Live, a self-sovereigned agent was still an admissible turn
author whose stored nonce had reset: a genuine replay vector.

The FIX (the reserved-field discipline, exactly as `setField "nonce"` rides): the replay nonce is
PROTOCOL-managed metadata, NOT host-readable cell state. `sovereignRebind` now PRESERVES the reserved
nonce slot (`[(commitment, .dig …), (nonce, .int (old nonce))]`) — the host keeps the replay counter
readable + monotone while the VALUE/balance still move behind the commitment. So `makeSovereign` is now
nonce-PRESERVING (`makeSovereign_preserves_nonce`), `BodyNonceNondecreasing` holds for it too, and the
former `forestTouchesSovereign` carve-out DROPS: no-replay is UNCONDITIONAL on the deployed executor. -/

/-- **`makeSovereign_preserves_nonce` — the third nonce-reset vector CLOSED.** A committed self-sovereign
step PRESERVES the target's readable nonce: `nonceOf (post target) = nonceOf (pre target)`. The
commitment-form rebind keeps the reserved replay-nonce slot, so making a cell sovereign does NOT reset
its replay counter (it used to drop to `0`). This is what makes `BodyNonceNondecreasing` hold for the
`makeSovereign` arm, retiring the carve-out. -/
theorem makeSovereign_preserves_nonce {s s' : RecChainedState} {actor target : CellId}
    (h : TurnExecutorFull.makeSovereignStep s actor target = some s') :
    nonceOf (s'.kernel.cell target) = nonceOf (s.kernel.cell target) := by
  obtain ⟨_, hs'⟩ := TurnExecutorFull.makeSovereignStep_factors h
  subst hs'
  -- `nonceOf v = (v.scalar nonceField).getD 0`; the kernel lemma preserves exactly that fail-soft read
  -- (both `nonceField`s are the literal `"nonce"`, so the kernel lemma's read matches definitionally).
  unfold nonceOf EffectTransfer.nonceField
  exact TurnExecutorFull.makeSovereignKernel_nonce_preserved s.kernel target

/-! ### Account-set MONOTONICITY (a helper threaded through the `exerciseA` sub-fold).

`accounts` is touched by NO arm except the creation family, which only INSERTS a fresh id
(`createCellIntoAsset = insert newCell …`); every other arm leaves `accounts` fixed. So membership is
preserved by every committed `execFullA` step — needed to keep `agent ∈ accounts` alive through the
`execInnerA` recursion of `exerciseA`. Proved as a mutual pair (single-step + inner-fold). -/

mutual
/-- A committed `execFullA` step preserves account membership (`accounts` only ever grows). -/
theorem execFullA_accounts_mono (s s' : RecChainedState) (fa : FullActionA) (c : CellId)
    (hc : c ∈ s.kernel.accounts)
    (h : TurnExecutorFull.execFullA s fa = some s') : c ∈ s'.kernel.accounts := by
  cases fa with
  | balanceA t a =>
      simp only [TurnExecutorFull.execFullA] at h
      unfold TurnExecutorFull.recCexecAsset at h
      split at h
      · cases hk : recKExecAsset s.kernel t a with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            rw [hk] at h; simp only [Option.some.injEq] at h; subst h
            unfold recKExecAsset at hk
            split at hk
            · simp only [Option.some.injEq] at hk; rw [← hk]; exact hc
            · exact absurd hk (by simp)
      · exact absurd h (by simp)
  | delegate del rec t =>
      simp only [TurnExecutorFull.execFullA] at h
      unfold TurnExecutorFull.recCDelegate at h
      cases hk : recKDelegate s.kernel del rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; simp only [Option.some.injEq] at h; subst h
          rw [(recKDelegate_frame s.kernel k' del rec t hk).2.1]; exact hc
  | revoke holder t =>
      simp only [TurnExecutorFull.execFullA] at h
      simp only [Option.some.injEq] at h; subst h
      unfold TurnExecutorFull.recCRevoke
      rw [(recKRevokeTarget_frame s.kernel holder t).2.1]; exact hc
  | mintA actor cell a amt =>
      simp only [TurnExecutorFull.execFullA] at h
      unfold TurnExecutorFull.recCMintAsset at h
      cases hk : TurnExecutorFull.recKMintAsset s.kernel actor cell a amt with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; simp only [Option.some.injEq] at h; subst h
          unfold TurnExecutorFull.recKMintAsset at hk
          split at hk
          · simp only [Option.some.injEq] at hk; rw [← hk]; exact hc
          · exact absurd hk (by simp)
  | burnA actor cell a amt =>
      simp only [TurnExecutorFull.execFullA] at h
      unfold TurnExecutorFull.recCBurnAsset at h
      cases hk : TurnExecutorFull.recKBurnAsset s.kernel actor cell a amt with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; simp only [Option.some.injEq] at h; subst h
          unfold TurnExecutorFull.recKBurnAsset at hk
          split at hk
          · simp only [Option.some.injEq] at hk; rw [← hk]; exact hc
          · exact absurd hk (by simp)
  | setFieldA actor cell f v =>
      simp only [TurnExecutorFull.execFullA] at h
      have hstep := EffectsState.stateStepGuarded_eq (EffectsState.stateStepDev_eq h)
      obtain ⟨_, hs'⟩ := EffectsState.stateStep_factors hstep
      subst hs'; exact hc
  | emitEventA actor cell topic data =>
      simp only [TurnExecutorFull.execFullA] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; exact hc
      · exact absurd h (by simp)
  | incrementNonceA actor cell n =>
      simp only [TurnExecutorFull.execFullA] at h
      obtain ⟨_, hs'⟩ := EffectsState.stateStep_factors (EffectsState.incrementNonceStep_eq h)
      subst hs'; exact hc
  | setPermissionsA actor cell p =>
      simp only [TurnExecutorFull.execFullA] at h
      obtain ⟨_, hs'⟩ := EffectsState.stateStep_factors h; subst hs'; exact hc
  | setVKA actor cell vk =>
      simp only [TurnExecutorFull.execFullA] at h
      obtain ⟨_, hs'⟩ := EffectsState.stateStep_factors h; subst hs'; exact hc
  | setProgramA actor cell prog =>
      simp only [TurnExecutorFull.execFullA] at h
      obtain ⟨_, hs'⟩ := EffectsState.stateStep_factors h; subst hs'; exact hc
  | introduceA intro rec t =>
      simp only [TurnExecutorFull.execFullA] at h
      unfold TurnExecutorFull.recCDelegate at h
      cases hk : recKDelegate s.kernel intro rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; simp only [Option.some.injEq] at h; subst h
          rw [(recKDelegate_frame s.kernel k' intro rec t hk).2.1]; exact hc
  | delegateAttenA del rec t keep =>
      simp only [TurnExecutorFull.execFullA] at h
      unfold TurnExecutorFull.recCDelegateAtten at h
      cases hk : recKDelegateAtten s.kernel del rec t keep with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; simp only [Option.some.injEq] at h; subst h
          rw [(recKDelegateAtten_frame s.kernel k' del rec t keep hk).2.1]; exact hc
  | attenuateA actor idx keep =>
      rw [TurnExecutorFull.execFullA_attenuateA_eq] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; exact hc
      · exact absurd h (by simp)
  | revokeDelegationA holder t =>
      simp only [TurnExecutorFull.execFullA] at h
      simp only [Option.some.injEq] at h; subst h
      unfold TurnExecutorFull.recCRevokeDelegationFull
      rw [(recKRevokeDelegationFull_frame s.kernel holder t).2.1]; exact hc
  | exerciseA actor t inner =>
      -- hold-gate (`exerciseStepA`, `{ s with log := … }`, accounts unchanged) then the inner fold.
      simp only [TurnExecutorFull.execFullA] at h
      split at h
      · cases hex : TurnExecutorFull.exerciseStepA s actor t with
        | none => rw [hex] at h; exact absurd h (by simp)
        | some s1 =>
            rw [hex] at h
            have hacc1 : c ∈ s1.kernel.accounts := by
              unfold TurnExecutorFull.exerciseStepA at hex
              split at hex
              · simp only [Option.some.injEq] at hex; subst hex; exact hc
              · exact absurd hex (by simp)
            exact execInnerA_list_accounts_mono s1 s' inner c hacc1 h
      · exact absurd h (by simp)
  | createCellA actor newCell =>
      simp only [TurnExecutorFull.execFullA] at h
      obtain ⟨_, _, hs'⟩ := TurnExecutorFull.createCellChainA_factors h
      subst hs'
      show c ∈ (createCellIntoAsset s.kernel newCell).accounts
      unfold createCellIntoAsset; exact Finset.mem_insert_of_mem hc
  | createCellFromFactoryA actor newCell vk =>
      simp only [TurnExecutorFull.execFullA] at h
      obtain ⟨e, s1, _, _, hcr, hs'⟩ := TurnExecutorFull.createCellFromFactoryChainA_factors h
      obtain ⟨_, _, hs1⟩ := TurnExecutorFull.createCellChainA_factors hcr
      subst hs' hs1
      -- the factory field/caveat install keeps `accounts := (create-leg).accounts`; the create leg inserts.
      show c ∈ (createCellIntoAsset s.kernel newCell).accounts
      unfold createCellIntoAsset; exact Finset.mem_insert_of_mem hc
  | spawnA actor child target =>
      simp only [TurnExecutorFull.execFullA] at h
      unfold TurnExecutorFull.spawnChainA at h
      split at h
      · cases hcr : TurnExecutorFull.createCellChainA s actor child with
        | none => rw [hcr] at h; exact absurd h (by simp)
        | some s1 =>
            rw [hcr] at h; simp only [Option.some.injEq] at h; subst h
            obtain ⟨_, _, hs1⟩ := TurnExecutorFull.createCellChainA_factors hcr
            subst hs1
            show c ∈ (createCellIntoAsset s.kernel child).accounts
            unfold createCellIntoAsset; exact Finset.mem_insert_of_mem hc
      · exact absurd h (by simp)
  | bridgeMintA actor cell a value =>
      simp only [TurnExecutorFull.execFullA] at h
      unfold TurnExecutorFull.recCMintAsset at h
      cases hk : TurnExecutorFull.recKMintAsset s.kernel actor cell a value with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; simp only [Option.some.injEq] at h; subst h
          unfold TurnExecutorFull.recKMintAsset at hk
          split at hk
          · simp only [Option.some.injEq] at hk; rw [← hk]; exact hc
          · exact absurd hk (by simp)
  | noteSpendA nf actor spendProof =>
      simp only [TurnExecutorFull.execFullA] at h
      unfold TurnExecutorFull.noteSpendChainA at h
      split at h
      · cases hk : noteSpendNullifier s.kernel nf with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            rw [hk] at h; simp only [Option.some.injEq] at h; subst h
            unfold noteSpendNullifier at hk
            split at hk
            · exact absurd hk (by simp)
            · simp only [Option.some.injEq] at hk; rw [← hk]; exact hc
      · exact absurd h (by simp)
  | noteCreateA cm actor =>
      simp only [TurnExecutorFull.execFullA] at h
      simp only [Option.some.injEq] at h; subst h; exact hc
  | makeSovereignA actor cell =>
      simp only [TurnExecutorFull.execFullA] at h
      obtain ⟨_, hs'⟩ := TurnExecutorFull.makeSovereignStep_factors h
      subst hs'; exact hc
  | refusalA actor cell =>
      simp only [TurnExecutorFull.execFullA] at h
      obtain ⟨_, hs'⟩ := EffectsState.stateStep_factors h; subst hs'; exact hc
  | receiptArchiveA actor cell =>
      simp only [TurnExecutorFull.execFullA] at h
      unfold TurnExecutorFull.receiptArchiveChainA at h
      split at h
      · simp only [Option.some.injEq] at h; subst h
        unfold TurnExecutorFull.setLifecycle; exact hc
      · exact absurd h (by simp)
  | pipelinedSendA actor =>
      simp only [TurnExecutorFull.execFullA] at h
      simp only [Option.some.injEq] at h; subst h; exact hc
  | cellSealA actor cell =>
      simp only [TurnExecutorFull.execFullA] at h
      unfold TurnExecutorFull.cellSealChainA at h
      split at h
      · simp only [Option.some.injEq] at h; subst h
        unfold TurnExecutorFull.setLifecycle; exact hc
      · exact absurd h (by simp)
  | cellUnsealA actor cell =>
      simp only [TurnExecutorFull.execFullA] at h
      unfold TurnExecutorFull.cellUnsealChainA at h
      split at h
      · simp only [Option.some.injEq] at h; subst h
        unfold TurnExecutorFull.setLifecycle; exact hc
      · exact absurd h (by simp)
  | cellDestroyA actor cell ch =>
      simp only [TurnExecutorFull.execFullA] at h
      unfold TurnExecutorFull.cellDestroyChainA at h
      split at h
      · simp only [Option.some.injEq] at h; subst h
        show c ∈ (TurnExecutorFull.setLifecycle s.kernel cell TurnExecutorFull.lcDestroyed).accounts
        unfold TurnExecutorFull.setLifecycle; exact hc
      · exact absurd h (by simp)
  | refreshDelegationA actor child =>
      simp only [TurnExecutorFull.execFullA] at h
      unfold TurnExecutorFull.refreshDelegationChainA at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; exact hc
      · exact absurd h (by simp)
  | heapWriteA actor target addr v newRoot =>
      simp only [TurnExecutorFull.execFullA] at h
      obtain ⟨s₁, hw, hs'⟩ := Substrate.HeapKernel.heapStepGuardedW_factors h
      subst hs'
      obtain ⟨_, hs₁⟩ := EffectsState.stateStep_factors (EffectsState.stateStepGuarded_eq hw)
      subst hs₁; exact hc
  termination_by sizeOf fa

/-- The raw `execInnerA` list-fold preserves account membership (structural induction on the list). -/
theorem execInnerA_list_accounts_mono (s s' : RecChainedState) (inner : List FullActionA) (c : CellId)
    (hc : c ∈ s.kernel.accounts)
    (h : TurnExecutorFull.execInnerA s inner = some s') : c ∈ s'.kernel.accounts := by
  cases inner with
  | nil => simp only [TurnExecutorFull.execInnerA, Option.some.injEq] at h; subst h; exact hc
  | cons a rest =>
      simp only [TurnExecutorFull.execInnerA] at h
      cases ha : TurnExecutorFull.execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          have hc1 : c ∈ s1.kernel.accounts := execFullA_accounts_mono s s1 a c hc ha
          exact execInnerA_list_accounts_mono s1 s' rest c hc1 h
  termination_by sizeOf inner
end

/-! ### `execFullA_agentNonce_nondecr` — THE PER-ARM SINGLE-STEP KEYSTONE (mutual with the sub-fold).

A committed `execFullA` step, with `agent` a live member account (`agent ∈ accounts` — frames out the
fresh-cell creation arms), leaves `agent`'s nonce UNCHANGED-OR-RAISED — UNCONDITIONALLY (no
self-sovereign carve-out: `makeSovereign` now PRESERVES the reserved nonce, so the `makeSovereignA agent`
case is nonce-preserving like every other arm). Discharges `BodyNonceNondecreasing` at the single-effect
grain by a genuine split over EVERY arm against its real dispatch semantics (no arm assumed). Mutual with
the `exerciseA` sub-forest fold (`execInnerA_list_agentNonce_nondecr`). -/
mutual
theorem execFullA_agentNonce_nondecr (s s' : RecChainedState) (fa : FullActionA) (agent : CellId)
    (hagent : agent ∈ s.kernel.accounts)
    (h : TurnExecutorFull.execFullA s fa = some s') :
    agentNonce s.kernel agent ≤ agentNonce s'.kernel agent := by
  -- `agentNonce k agent = nonceOf (k.cell agent)`; we show ≤ for the agent cell.
  unfold agentNonce
  cases fa with
  -- ── `cell`-UNCHANGED: the per-asset ledger ops edit `bal`, never `cell`. ──────────────────────
  | balanceA t a =>
      simp only [TurnExecutorFull.execFullA] at h
      unfold TurnExecutorFull.recCexecAsset at h
      -- `recKExecAsset` is `{ k with bal := … }` so `cell` is the SAME function; nonceOf unchanged.
      split at h
      · next hacc =>
          cases hk : recKExecAsset s.kernel t a with
          | none => rw [hk] at h; exact absurd h (by simp)
          | some k' =>
              rw [hk] at h; simp only [Option.some.injEq] at h; subst h
              have : k'.cell = s.kernel.cell := by
                unfold recKExecAsset at hk
                split at hk
                · simp only [Option.some.injEq] at hk; rw [← hk]
                · exact absurd hk (by simp)
              rw [this]
      · exact absurd h (by simp)
  | delegate del rec t =>
      simp only [TurnExecutorFull.execFullA] at h
      unfold TurnExecutorFull.recCDelegate at h
      cases hk : recKDelegate s.kernel del rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; simp only [Option.some.injEq] at h; subst h
          rw [congrFun (recKDelegate_frame s.kernel k' del rec t hk).2.2 agent]
  | revoke holder t =>
      simp only [TurnExecutorFull.execFullA] at h
      simp only [Option.some.injEq] at h; subst h
      unfold TurnExecutorFull.recCRevoke
      rw [congrFun (recKRevokeTarget_frame s.kernel holder t).2.2 agent]
  | mintA actor cell a amt =>
      simp only [TurnExecutorFull.execFullA] at h
      unfold TurnExecutorFull.recCMintAsset at h
      cases hk : TurnExecutorFull.recKMintAsset s.kernel actor cell a amt with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; simp only [Option.some.injEq] at h; subst h
          rw [congrFun (recKMintAsset_cell_frame hk) agent]
  | burnA actor cell a amt =>
      simp only [TurnExecutorFull.execFullA] at h
      unfold TurnExecutorFull.recCBurnAsset at h
      cases hk : TurnExecutorFull.recKBurnAsset s.kernel actor cell a amt with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; simp only [Option.some.injEq] at h; subst h
          rw [congrFun (recKBurnAsset_cell_frame hk) agent]
  -- ── field-write arms, written field ≠ "nonce". ───────────────────────────────────────────────
  | setFieldA actor cell f v =>
      -- the developer write is REJECTED on a reserved slot; on commit `f` is NOT reserved, so `f ≠ "nonce"`.
      simp only [TurnExecutorFull.execFullA] at h
      have hnr : EffectsState.reservedField f = false := EffectsState.stateStepDev_notReserved h
      have hfn : f ≠ EffectTransfer.nonceField := by
        intro he; subst he
        -- `reservedField "nonce" = true`, contradicting `hnr`.
        simp [EffectsState.reservedField, EffectTransfer.nonceField] at hnr
      have hstep := EffectsState.stateStepDev_eq h
      have hgrd := EffectsState.stateStepGuarded_eq hstep
      rw [nonceOf_stateStep_of_ne agent hfn hgrd]
  | emitEventA actor cell topic data =>
      simp only [TurnExecutorFull.execFullA] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h
        -- `emitStep` is `{ kernel := s.kernel, log := … }`: the kernel (hence `cell`) is unchanged.
        rfl
      · exact absurd h (by simp)
  | incrementNonceA actor cell n =>
      -- the ONE arm that RAISES the nonce; on `cell = agent` it strictly advances, else frames out.
      simp only [TurnExecutorFull.execFullA] at h
      have hstep := EffectsState.incrementNonceStep_eq h
      have hadv := EffectsState.incrementNonceStep_advances h
      obtain ⟨_, hs'⟩ := EffectsState.stateStep_factors hstep
      subst hs'
      show nonceOf (s.kernel.cell agent)
        ≤ nonceOf ((EffectsState.writeField s.kernel "nonce" cell (.int n)).cell agent)
      unfold EffectsState.writeField
      by_cases hc : agent = cell
      · -- the written cell: `nonceOf (setField "nonce" … (.int n)) = n`, and `old < n` (advance).
        subst hc
        simp only [if_true]
        show nonceOf (s.kernel.cell agent)
          ≤ EffectsState.fieldOf "nonce" (EffectsState.setField "nonce" (s.kernel.cell agent) (.int n))
        rw [EffectsState.setField_fieldOf]
        -- `hadv : fieldOf "nonce" (cell agent) < n`; `fieldOf "nonce" = nonceOf`.
        have : EffectsState.fieldOf "nonce" (s.kernel.cell agent) = nonceOf (s.kernel.cell agent) := rfl
        rw [this] at hadv; omega
      · simp only [if_neg hc]; exact le_refl _
  | setPermissionsA actor cell p =>
      simp only [TurnExecutorFull.execFullA] at h
      rw [nonceOf_stateStep_of_ne agent (by decide) h]
  | setVKA actor cell vk =>
      simp only [TurnExecutorFull.execFullA] at h
      rw [nonceOf_stateStep_of_ne agent (by decide) h]
  | setProgramA actor cell prog =>
      simp only [TurnExecutorFull.execFullA] at h
      rw [nonceOf_stateStep_of_ne agent (by decide) h]
  -- ── authority arms: `caps`/`delegations`-only, `cell` frozen. ─────────────────────────────────
  | introduceA intro rec t =>
      simp only [TurnExecutorFull.execFullA] at h
      unfold TurnExecutorFull.recCDelegate at h
      cases hk : recKDelegate s.kernel intro rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; simp only [Option.some.injEq] at h; subst h
          rw [congrFun (recKDelegate_frame s.kernel k' intro rec t hk).2.2 agent]
  | delegateAttenA del rec t keep =>
      simp only [TurnExecutorFull.execFullA] at h
      unfold TurnExecutorFull.recCDelegateAtten at h
      cases hk : recKDelegateAtten s.kernel del rec t keep with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; simp only [Option.some.injEq] at h; subst h
          rw [congrFun (recKDelegateAtten_frame s.kernel k' del rec t keep hk).2.2 agent]
  | attenuateA actor idx keep =>
      rw [TurnExecutorFull.execFullA_attenuateA_eq] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h
        -- `attenuateStepA` edits `caps` only.
        rfl
      · exact absurd h (by simp)
  | revokeDelegationA holder t =>
      simp only [TurnExecutorFull.execFullA] at h
      simp only [Option.some.injEq] at h; subst h
      -- `recCRevokeDelegationFull` is `{ kernel := recKRevokeDelegationFull …, log := … }`; cell frozen.
      unfold TurnExecutorFull.recCRevokeDelegationFull
      rw [congrFun (recKRevokeDelegationFull_frame s.kernel holder t).2.2 agent]
  | exerciseA actor t inner =>
      -- the hold-gate (`exerciseStepA`, `{ s with log := … }`, kernel unchanged) then the inner fold.
      -- UNCONDITIONAL: the inner fold is nonce-nondecreasing for ANY inner list (no carve-out).
      simp only [TurnExecutorFull.execFullA] at h
      split at h
      · cases hex : TurnExecutorFull.exerciseStepA s actor t with
        | none => rw [hex] at h; exact absurd h (by simp)
        | some s1 =>
            rw [hex] at h
            have hk1 : s1.kernel = s.kernel := by
              unfold TurnExecutorFull.exerciseStepA at hex
              split at hex
              · simp only [Option.some.injEq] at hex; subst hex; rfl
              · exact absurd hex (by simp)
            have hagent1 : agent ∈ s1.kernel.accounts := hk1 ▸ hagent
            have hstep := execInnerA_list_agentNonce_nondecr s1 s' inner agent hagent1 h
            have heq : agentNonce s1.kernel agent = agentNonce s.kernel agent := by
              unfold agentNonce; rw [hk1]
            show agentNonce s.kernel agent ≤ agentNonce s'.kernel agent
            omega
      · exact absurd h (by simp)
  -- ── account-growth arms: write only the FRESH cell; `agent ≠ newCell` since `agent ∈ accounts`. ─
  | createCellA actor newCell =>
      simp only [TurnExecutorFull.execFullA] at h
      obtain ⟨_, hfresh, hs'⟩ := TurnExecutorFull.createCellChainA_factors h
      subst hs'
      have hne : agent ≠ newCell := fun he => hfresh (he ▸ hagent)
      show nonceOf (s.kernel.cell agent)
        ≤ nonceOf ((createCellIntoAsset s.kernel newCell).cell agent)
      -- `createCellIntoAsset` writes only `newCell`'s cell; `agent ≠ newCell` ⇒ frozen.
      unfold createCellIntoAsset bornEmptyCellSlots
      simp only [if_neg hne]; exact le_refl _
  | createCellFromFactoryA actor newCell vk =>
      simp only [TurnExecutorFull.execFullA] at h
      obtain ⟨e, s1, _, _, hc, hs'⟩ := TurnExecutorFull.createCellFromFactoryChainA_factors h
      obtain ⟨_, hfresh, hs1⟩ := TurnExecutorFull.createCellChainA_factors hc
      have hne : agent ≠ newCell := fun he => hfresh (he ▸ hagent)
      subst hs'
      -- the factory install writes only `newCell`; `agent ≠ newCell` ⇒ the install frames out, then the
      -- create-leg (`s1`) also writes only `newCell` ⇒ `s1.kernel.cell agent = s.kernel.cell agent`.
      simp only [if_neg hne]
      subst hs1
      show nonceOf (s.kernel.cell agent)
        ≤ nonceOf ((createCellIntoAsset s.kernel newCell).cell agent)
      unfold createCellIntoAsset bornEmptyCellSlots
      simp only [if_neg hne]; exact le_refl _
  | spawnA actor child target =>
      simp only [TurnExecutorFull.execFullA] at h
      unfold TurnExecutorFull.spawnChainA at h
      split at h
      · cases hc : TurnExecutorFull.createCellChainA s actor child with
        | none => rw [hc] at h; exact absurd h (by simp)
        | some s1 =>
            rw [hc] at h; simp only [Option.some.injEq] at h; subst h
            obtain ⟨_, hfresh, hs1⟩ := TurnExecutorFull.createCellChainA_factors hc
            have hne : agent ≠ child := fun he => hfresh (he ▸ hagent)
            subst hs1
            -- spawn re-splices `caps` at `child` only; the `cell` is the create-leg's, frozen at `agent`.
            show nonceOf (s.kernel.cell agent)
              ≤ nonceOf ((createCellIntoAsset s.kernel child).cell agent)
            unfold createCellIntoAsset bornEmptyCellSlots
            simp only [if_neg hne]; exact le_refl _
      · exact absurd h (by simp)
  | bridgeMintA actor cell a value =>
      -- bridgeMint reuses `recCMintAsset` verbatim — `bal`-only, `cell` frozen.
      simp only [TurnExecutorFull.execFullA] at h
      unfold TurnExecutorFull.recCMintAsset at h
      cases hk : TurnExecutorFull.recKMintAsset s.kernel actor cell a value with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          rw [hk] at h; simp only [Option.some.injEq] at h; subst h
          rw [congrFun (recKMintAsset_cell_frame hk) agent]
  -- ── set / lifecycle / side-table arms: `cell` frozen. ────────────────────────────────────────
  | noteSpendA nf actor spendProof =>
      simp only [TurnExecutorFull.execFullA] at h
      unfold TurnExecutorFull.noteSpendChainA at h
      split at h
      · cases hk : noteSpendNullifier s.kernel nf with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            rw [hk] at h; simp only [Option.some.injEq] at h; subst h
            have : k'.cell = s.kernel.cell := by
              unfold noteSpendNullifier at hk
              split at hk
              · exact absurd hk (by simp)
              · simp only [Option.some.injEq] at hk; rw [← hk]
            rw [this]
      · exact absurd h (by simp)
  | noteCreateA cm actor =>
      simp only [TurnExecutorFull.execFullA] at h
      simp only [Option.some.injEq] at h; subst h
      -- `noteCreateChainA` is `{ kernel := noteCreateCommitment …, log := … }`; commitment-set only.
      unfold TurnExecutorFull.noteCreateChainA noteCreateCommitment
      exact le_refl _
  | makeSovereignA actor cell =>
      -- UNCONDITIONAL (the third nonce-reset vector closed): on the AGENT the commitment-form rebind
      -- PRESERVES the reserved nonce (`makeSovereignKernel_nonce_preserved`); on a NON-agent target the
      -- agent cell is FROZEN. Either way the agent nonce is unchanged.
      simp only [TurnExecutorFull.execFullA] at h
      obtain ⟨_, hs'⟩ := TurnExecutorFull.makeSovereignStep_factors h
      subst hs'
      show nonceOf (s.kernel.cell agent)
        ≤ nonceOf ((TurnExecutorFull.makeSovereignKernel s.kernel cell).cell agent)
      by_cases hac : agent = cell
      · -- the sovereigned cell IS the agent: the reserved nonce survives (`nonceOf` preserved).
        subst hac
        have hpres : nonceOf ((TurnExecutorFull.makeSovereignKernel s.kernel agent).cell agent)
            = nonceOf (s.kernel.cell agent) := by
          show (((TurnExecutorFull.makeSovereignKernel s.kernel agent).cell agent).scalar
                  EffectTransfer.nonceField).getD 0
             = ((s.kernel.cell agent).scalar EffectTransfer.nonceField).getD 0
          exact TurnExecutorFull.makeSovereignKernel_nonce_preserved s.kernel agent
        rw [hpres]
      · -- a NON-agent target: `sovereignRebind` rewrites only `cell`'s entry; `agent ≠ cell` ⇒ frozen.
        unfold TurnExecutorFull.makeSovereignKernel TurnExecutorFull.sovereignRebind
        simp only [if_neg hac]; exact le_refl _
  | refusalA actor cell =>
      simp only [TurnExecutorFull.execFullA] at h
      rw [nonceOf_stateStep_of_ne agent (by decide) h]
  | receiptArchiveA actor cell =>
      simp only [TurnExecutorFull.execFullA] at h
      unfold TurnExecutorFull.receiptArchiveChainA at h
      split at h
      · simp only [Option.some.injEq] at h; subst h
        -- `setLifecycle` edits `lifecycle` only; cell frozen.
        unfold TurnExecutorFull.setLifecycle
        exact le_refl _
      · exact absurd h (by simp)
  | pipelinedSendA actor =>
      simp only [TurnExecutorFull.execFullA] at h
      simp only [Option.some.injEq] at h; subst h
      rfl
  | cellSealA actor cell =>
      simp only [TurnExecutorFull.execFullA] at h
      unfold TurnExecutorFull.cellSealChainA at h
      split at h
      · simp only [Option.some.injEq] at h; subst h
        unfold TurnExecutorFull.setLifecycle
        exact le_refl _
      · exact absurd h (by simp)
  | cellUnsealA actor cell =>
      simp only [TurnExecutorFull.execFullA] at h
      unfold TurnExecutorFull.cellUnsealChainA at h
      split at h
      · simp only [Option.some.injEq] at h; subst h
        unfold TurnExecutorFull.setLifecycle
        exact le_refl _
      · exact absurd h (by simp)
  | cellDestroyA actor cell ch =>
      simp only [TurnExecutorFull.execFullA] at h
      unfold TurnExecutorFull.cellDestroyChainA at h
      split at h
      · simp only [Option.some.injEq] at h; subst h
        -- edits `lifecycle` + `deathCert`; cell frozen.
        unfold TurnExecutorFull.setLifecycle
        exact le_refl _
      · exact absurd h (by simp)
  | refreshDelegationA actor child =>
      simp only [TurnExecutorFull.execFullA] at h
      unfold TurnExecutorFull.refreshDelegationChainA at h
      split at h
      · simp only [Option.some.injEq] at h; subst h
        -- edits `delegations`/`delegationEpochAt`; cell frozen.
        rfl
      · exact absurd h (by simp)
  | heapWriteA actor target addr v newRoot =>
      simp only [TurnExecutorFull.execFullA] at h
      obtain ⟨s₁, hw, hs'⟩ := Substrate.HeapKernel.heapStepGuardedW_factors h
      subst hs'
      -- the `heaps`-splice doesn't touch `cell`; the underlying guarded write is on `heap_root` ≠ "nonce".
      have hgrd := EffectsState.stateStepGuarded_eq hw
      show nonceOf (s.kernel.cell agent) ≤ nonceOf (s₁.kernel.cell agent)
      rw [nonceOf_stateStep_of_ne agent (by decide) hgrd]
  termination_by sizeOf fa

/-- **`execInnerA_list_agentNonce_nondecr` — the raw inner fold preserves the agent nonce.** Structural
induction on the inner list: each element steps via `execFullA` (nondecreasing by the keystone — now
UNCONDITIONAL, no self-sovereign exclusion — and membership preserved by `execFullA_accounts_mono`), and
the tail recurses. The all-or-nothing fold's agent nonce only rises. -/
theorem execInnerA_list_agentNonce_nondecr (s s' : RecChainedState) (inner : List FullActionA)
    (agent : CellId) (hagent : agent ∈ s.kernel.accounts)
    (h : TurnExecutorFull.execInnerA s inner = some s') :
    agentNonce s.kernel agent ≤ agentNonce s'.kernel agent := by
  cases inner with
  | nil =>
      simp only [TurnExecutorFull.execInnerA, Option.some.injEq] at h; subst h; exact le_refl _
  | cons a rest =>
      simp only [TurnExecutorFull.execInnerA] at h
      cases ha : TurnExecutorFull.execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          have hstep : agentNonce s.kernel agent ≤ agentNonce s1.kernel agent :=
            execFullA_agentNonce_nondecr s s1 a agent hagent ha
          have hagent1 : agent ∈ s1.kernel.accounts :=
            execFullA_accounts_mono s s1 a agent hagent ha
          have htail : agentNonce s1.kernel agent ≤ agentNonce s'.kernel agent :=
            execInnerA_list_agentNonce_nondecr s1 s' rest agent hagent1 h
          omega
  termination_by sizeOf inner
end

/-! ## §4c‴ — LIFT THE KEYSTONE TO THE FOREST BODY (discharge `BodyNonceNondecreasing` for `runTurn`).

The deployed `runTurn` body is `FullForest.execFullForestA · forest` — a TREE of `FullActionA` nodes
folded under real `recCDelegateAtten` delegation handoffs. We lift the single-step keystone to the whole
forest by a mutual induction over the tree (node + delegated children). The delegation handoff
`recCDelegateAtten` is `caps`-only (cell + accounts frozen, `recKDelegateAtten_frame`), so it disturbs
neither the agent nonce nor membership. UNCONDITIONAL: no self-sovereign carve-out — the
`makeSovereignA` arm is nonce-preserving (`makeSovereign_preserves_nonce`), so the lift holds over ANY
forest. -/

/-- A committed `recCDelegateAtten` handoff freezes every cell's `nonceOf` and account membership
(`caps`-only edit, `recKDelegateAtten_frame`). The bridge each forest child-edge reuses. -/
theorem recCDelegateAtten_frame_nonce {s s' : RecChainedState} {del rec t : CellId}
    {keep : List Authority.Auth}
    (c : CellId) (h : TurnExecutorFull.recCDelegateAtten s del rec t keep = some s') :
    nonceOf (s'.kernel.cell c) = nonceOf (s.kernel.cell c)
      ∧ (∀ x, x ∈ s.kernel.accounts → x ∈ s'.kernel.accounts) := by
  unfold TurnExecutorFull.recCDelegateAtten at h
  cases hk : recKDelegateAtten s.kernel del rec t keep with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some k' =>
      rw [hk] at h; simp only [Option.some.injEq] at h; subst h
      refine ⟨?_, ?_⟩
      · rw [congrFun (recKDelegateAtten_frame s.kernel k' del rec t keep hk).2.2 c]
      · intro x hx; rw [(recKDelegateAtten_frame s.kernel k' del rec t keep hk).2.1]; exact hx

/-! ### Forest account-set monotonicity (the membership thread for the forest fold). -/

mutual
theorem execFullForestA_accounts_mono : ∀ (s s' : RecChainedState) (f : FullForest.FullForestA)
    (c : CellId), c ∈ s.kernel.accounts →
    FullForest.execFullForestA s f = some s' → c ∈ s'.kernel.accounts
  | s, s', ⟨a, kids⟩, c, hc, h => by
      simp only [FullForest.execFullForestA] at h
      cases hnode : TurnExecutorFull.execFullA s a with
      | none => rw [hnode] at h; exact absurd h (by simp)
      | some s1 =>
          rw [hnode] at h
          have hc1 : c ∈ s1.kernel.accounts := execFullA_accounts_mono s s1 a c hc hnode
          exact execFullChildrenA_accounts_mono (FullForest.targetOf a) s1 s' kids c hc1 h
  termination_by s s' f => sizeOf f

theorem execFullChildrenA_accounts_mono : ∀ (delegator : CellId) (s s' : RecChainedState)
    (kids : List FullForest.FullChildA) (c : CellId), c ∈ s.kernel.accounts →
    FullForest.execFullChildrenA delegator s kids = some s' → c ∈ s'.kernel.accounts
  | _, s, s', [], c, hc, h => by
      simp only [FullForest.execFullChildrenA, Option.some.injEq] at h; subst h; exact hc
  | delegator, s, s', ⟨holder, keep, parentCap, sub⟩ :: rest, c, hc, h => by
      simp only [FullForest.execFullChildrenA] at h
      cases hct : FullForest.capTarget parentCap with
      | some tt =>
          rw [hct] at h; simp only at h
          cases hd : TurnExecutorFull.recCDelegateAtten s delegator holder tt keep with
          | none => rw [hd] at h; exact absurd h (by simp)
          | some s1 =>
              rw [hd] at h; simp only at h
              have hc1 : c ∈ s1.kernel.accounts := (recCDelegateAtten_frame_nonce c hd).2 c hc
              cases hsub : FullForest.execFullForestA s1 sub with
              | none => rw [hsub] at h; exact absurd h (by simp)
              | some s2 =>
                  rw [hsub] at h; simp only at h
                  have hc2 : c ∈ s2.kernel.accounts := execFullForestA_accounts_mono s1 s2 sub c hc1 hsub
                  exact execFullChildrenA_accounts_mono delegator s2 s' rest c hc2 h
      | none =>
          rw [hct] at h; simp only at h
          cases hsub : FullForest.execFullForestA s sub with
          | none => rw [hsub] at h; exact absurd h (by simp)
          | some s2 =>
              rw [hsub] at h; simp only at h
              have hc2 : c ∈ s2.kernel.accounts := execFullForestA_accounts_mono s s2 sub c hc hsub
              exact execFullChildrenA_accounts_mono delegator s2 s' rest c hc2 h
  termination_by delegator s s' kids => sizeOf kids
end

/-! **`execFullForestA_agentNonce_nondecr` — THE FOREST KEYSTONE (UNCONDITIONAL).** A committed
`execFullForestA` over ANY forest, with `agent` a live member account, leaves `agent`'s nonce
UNCHANGED-OR-RAISED. The whole-executor-body discharge of `BodyNonceNondecreasing` — no self-sovereign
carve-out (the `makeSovereignA` arm is now nonce-preserving), proved by mutual induction over the tree
(node action via the single-step keystone, children via the handoff frame + recursion). -/
mutual
theorem execFullForestA_agentNonce_nondecr : ∀ (s s' : RecChainedState) (f : FullForest.FullForestA)
    (agent : CellId), agent ∈ s.kernel.accounts →
    FullForest.execFullForestA s f = some s' →
    agentNonce s.kernel agent ≤ agentNonce s'.kernel agent
  | s, s', ⟨a, kids⟩, agent, hagent, h => by
      simp only [FullForest.execFullForestA] at h
      cases hnode : TurnExecutorFull.execFullA s a with
      | none => rw [hnode] at h; exact absurd h (by simp)
      | some s1 =>
          rw [hnode] at h
          have hstep : agentNonce s.kernel agent ≤ agentNonce s1.kernel agent :=
            execFullA_agentNonce_nondecr s s1 a agent hagent hnode
          have hagent1 : agent ∈ s1.kernel.accounts :=
            execFullA_accounts_mono s s1 a agent hagent hnode
          have htail : agentNonce s1.kernel agent ≤ agentNonce s'.kernel agent :=
            execFullChildrenA_agentNonce_nondecr (FullForest.targetOf a) s1 s' kids agent hagent1 h
          omega
  termination_by s s' f => sizeOf f

/-- The child-edge fold preserves the agent nonce: each delegation handoff (`recCDelegateAtten`,
cell-frozen) then the child subtree (recursion), all-or-nothing. UNCONDITIONAL (no carve-out). -/
theorem execFullChildrenA_agentNonce_nondecr : ∀ (delegator : CellId) (s s' : RecChainedState)
    (kids : List FullForest.FullChildA) (agent : CellId), agent ∈ s.kernel.accounts →
    FullForest.execFullChildrenA delegator s kids = some s' →
    agentNonce s.kernel agent ≤ agentNonce s'.kernel agent
  | _, s, s', [], agent, _, h => by
      simp only [FullForest.execFullChildrenA, Option.some.injEq] at h; subst h; exact le_refl _
  | delegator, s, s', ⟨holder, keep, parentCap, sub⟩ :: rest, agent, hagent, h => by
      simp only [FullForest.execFullChildrenA] at h
      cases hct : FullForest.capTarget parentCap with
      | some tt =>
          rw [hct] at h; simp only at h
          cases hd : TurnExecutorFull.recCDelegateAtten s delegator holder tt keep with
          | none => rw [hd] at h; exact absurd h (by simp)
          | some s1 =>
              rw [hd] at h; simp only at h
              obtain ⟨hdn, hda⟩ := recCDelegateAtten_frame_nonce agent hd
              have hagent1 : agent ∈ s1.kernel.accounts := hda agent hagent
              have hdnonce : agentNonce s1.kernel agent = agentNonce s.kernel agent := by
                unfold agentNonce; exact hdn
              cases hsub : FullForest.execFullForestA s1 sub with
              | none => rw [hsub] at h; exact absurd h (by simp)
              | some s2 =>
                  rw [hsub] at h; simp only at h
                  have hstep : agentNonce s1.kernel agent ≤ agentNonce s2.kernel agent :=
                    execFullForestA_agentNonce_nondecr s1 s2 sub agent hagent1 hsub
                  have hagent2 : agent ∈ s2.kernel.accounts :=
                    execFullForestA_accounts_mono s1 s2 sub agent hagent1 hsub
                  have htail : agentNonce s2.kernel agent ≤ agentNonce s'.kernel agent :=
                    execFullChildrenA_agentNonce_nondecr delegator s2 s' rest agent hagent2 h
                  omega
      | none =>
          rw [hct] at h; simp only at h
          cases hsub : FullForest.execFullForestA s sub with
          | none => rw [hsub] at h; exact absurd h (by simp)
          | some s2 =>
              rw [hsub] at h; simp only at h
              have hstep : agentNonce s.kernel agent ≤ agentNonce s2.kernel agent :=
                execFullForestA_agentNonce_nondecr s s2 sub agent hagent hsub
              have hagent2 : agent ∈ s2.kernel.accounts :=
                execFullForestA_accounts_mono s s2 sub agent hagent hsub
              have htail : agentNonce s2.kernel agent ≤ agentNonce s'.kernel agent :=
                execFullChildrenA_agentNonce_nondecr delegator s2 s' rest agent hagent2 h
              omega
  termination_by delegator s s' kids => sizeOf kids
end

/-- **`forest_body_nonceNondecreasing` — `BodyNonceNondecreasing` DISCHARGED for the live forest body.**
For a forest that does not make `agent` self-sovereign and any post-prologue state in which `agent` is
a live member, the deployed body `fun s => execFullForestA s forest` is nonce-nondecreasing — the
hypothesis `runTurn_strictly_advances_agentNonce` carries is now a THEOREM of the live executor body,
not an assumption. (The membership side-condition is supplied by admission's `AgentLive` gate, preserved
through the committed prologue.) -/
theorem forest_body_nonceNondecreasing (f : FullForest.FullForestA) (agent : CellId)
    (hmem : ∀ s : RecChainedState, agent ∈ s.kernel.accounts) :
    BodyNonceNondecreasing (fun s => FullForest.execFullForestA s f) agent := by
  intro s₁ s' h
  exact execFullForestA_agentNonce_nondecr s₁ s' f agent (hmem s₁) h

/-- **`admissible_agentLive` — the agent is a live account in an admissible turn.** The `AgentLive`
gate (`admissible`'s conjunct 2) forces `h.agent ∈ accounts`; `commitPrologue` preserves the account
set (`commitPrologue_accounts`), so the agent stays a member in the post-prologue state the body runs
on. This is the membership side-condition the forest discharge consumes, supplied by admission. -/
theorem admissible_agentLive (ctx : Admission.AdmCtx) (h : Admission.TurnHdr) (s : RecChainedState)
    (hadm : Admission.admissible ctx h s = true) : h.agent ∈ s.kernel.accounts := by
  by_contra hgone
  rw [Admission.admissible_rejects_no_agent ctx h s hgone] at hadm
  exact absurd hadm (by simp)

/-- **`runTurn_forest_strictly_advances` — NO-REPLAY ADVANCE FOR THE LIVE FOREST BODY (the close).**
On ANY admissible turn, the deployed `Admission.runTurn` with the `execFullForestA` body STRICTLY
advances the agent nonce — UNCONDITIONALLY (no self-sovereign carve-out, no carried
`BodyNonceNondecreasing` hypothesis: it is DISCHARGED here by `execFullForestA_agentNonce_nondecr` at the
post-prologue state, whose membership comes from admission's `AgentLive` gate). This is exactly the
`TurnChain.monotone` obligation, now a theorem of the LIVE `runTurn`-over-`execFullForestA` executor. -/
theorem runTurn_forest_strictly_advances (ctx : Admission.AdmCtx) (h : Admission.TurnHdr)
    (s : RecChainedState) (f : FullForest.FullForestA)
    (hadm : Admission.admissible ctx h s = true) :
    ∀ s', Admission.runTurn ctx h s (fun s₀ => FullForest.execFullForestA s₀ f) = some s' →
      agentNonce s.kernel h.agent < agentNonce s'.kernel h.agent := by
  intro s' hrun
  -- the prologue's strict +1 bump.
  have hpro := prologue_strictly_increases_nonce s h.agent h.fee
  -- the post-prologue state's agent membership (from admission's `AgentLive`, preserved by the prologue).
  have hmem0 : h.agent ∈ (Admission.commitPrologue s h.agent h.fee).kernel.accounts := by
    rw [Admission.commitPrologue_accounts]; exact admissible_agentLive ctx h s hadm
  -- split on whether the forest body commits.
  cases hb : (fun s₀ => FullForest.execFullForestA s₀ f) (Admission.commitPrologue s h.agent h.fee) with
  | none =>
      -- failed body: `runTurn = commitPrologue`; the prologue advance IS the result.
      exact runTurn_failed_strictly_advances ctx h s (fun s₀ => FullForest.execFullForestA s₀ f)
        hadm hb s' hrun
  | some sb =>
      -- committing body: `runTurn = sb`; the forest body ran on the post-prologue state, only RAISING the
      -- agent nonce (the FOREST KEYSTONE, discharged at the post-prologue state via `hmem0`).
      have hrunsb : Admission.runTurn ctx h s (fun s₀ => FullForest.execFullForestA s₀ f) = some sb :=
        Admission.prologue_then_commit ctx h s (fun s₀ => FullForest.execFullForestA s₀ f) sb hadm hb
      have hbmono : agentNonce (Admission.commitPrologue s h.agent h.fee).kernel h.agent
          ≤ agentNonce sb.kernel h.agent :=
        execFullForestA_agentNonce_nondecr (Admission.commitPrologue s h.agent h.fee) sb f h.agent
          hmem0 hb
      rw [hrunsb] at hrun
      cases hrun
      omega

/-! ## §4d — wire the accepted-turn sequence into a `TurnChain` ⟹ `no_replay` on the DEPLOYED executor.

Given a sequence of states produced by ACCEPTED `runTurn`s (each admissible, each with a
nonce-nondecreasing body), the strict per-turn advance (`runTurn_strictly_advances_agentNonce`) is
EXACTLY `TurnChain.monotone`. So — provided each reachable state is `AccountsWF` (already
`recKExec_preserves_AccountsWF`, threaded as the `wf` field) — the accepted sequence IS a `TurnChain`,
and `no_replay` / `commit_no_repeat` apply to the LIVE executor, not merely the abstract chain. -/

/-- **`acceptedSeq_to_TurnChain` — the accepted-`runTurn` sequence IS a monotone `TurnChain`.** Given
indexed kernels `seq i`, each `AccountsWF`, and a per-step witness that `seq (i+1)` is an ACCEPTED
`runTurn` from `seq i` whose body is nonce-nondecreasing (so the agent nonce strictly advanced), the
sequence inhabits `TurnChain`. Then `TurnChain.commit_no_repeat`/`no_replay` give cross-turn
unforgeability on the deployed executor: the live commitment never returns, so no accepted proof is
applicable twice. -/
def acceptedSeq_to_TurnChain (S : CommitSurface) (agent : CellId) (t : Turn)
    (seq : Nat → RecChainedState)
    (wf : ∀ i, AccountsWF (seq i).kernel)
    (advance : ∀ i, agentNonce (seq i).kernel agent < agentNonce (seq (i + 1)).kernel agent) :
    TurnChain S agent t where
  seq i := (seq i).kernel
  wf := wf
  monotone := advance

/-- **`deployed_no_replay` — NO REPLAY on the DEPLOYED executor (the close).** For an accepted-turn
sequence (strictly nonce-advancing, all `AccountsWF`), a fixed pre-anchor opens the CAS gate at most
ONCE: two matches of the same anchor force the same turn index. This is `no_replay` lifted off the
abstract chain onto the real `runTurn`-driven sequence — the payoff the nonce-reset closure unblocks. -/
theorem deployed_no_replay (S : CommitSurface) (agent : CellId) (t : Turn)
    (seq : Nat → RecChainedState)
    (wf : ∀ i, AccountsWF (seq i).kernel)
    (advance : ∀ i, agentNonce (seq i).kernel agent < agentNonce (seq (i + 1)).kernel agent)
    {i j : Nat} {preCommit : ℤ}
    (hi : LiveCommitMatches (acceptedSeq_to_TurnChain S agent t seq wf advance) i preCommit)
    (hj : LiveCommitMatches (acceptedSeq_to_TurnChain S agent t seq wf advance) j preCommit) :
    i = j :=
  no_replay (acceptedSeq_to_TurnChain S agent t seq wf advance) hi hj

/-! ## §4e — THE FOREST-DRIVEN DEPLOYED NO-REPLAY (the whole-executor close — hypothesis DISCHARGED).

The `advance` witness `deployed_no_replay` takes is now a THEOREM of the live forest executor
(`runTurn_forest_strictly_advances`), not an assumption. Given a sequence of states each produced by an
ACCEPTED `Admission.runTurn` over ANY `execFullForestA` body, the strict per-turn agent-nonce advance is
automatic, so the sequence IS a monotone `TurnChain` and a fixed pre-anchor opens the CAS gate at most
once — NO REPLAY, UNCONDITIONAL (the third nonce-reset vector closed: no self-sovereign carve-out). -/

/-- **`forest_advance_holds` — the `advance` witness IS a theorem of the live executor.** For ANY
forest-driven accepted-`runTurn` sequence (each admissible), the per-step strict agent-nonce advance is
PROVED, not assumed — discharged by `runTurn_forest_strictly_advances`. This is exactly the
`TurnChain.monotone` obligation, established OF the live executor (no self-sovereign carve-out). -/
theorem forest_advance_holds (agent : CellId)
    (seq : Nat → RecChainedState) (ctxs : Nat → Admission.AdmCtx) (hdrs : Nat → Admission.TurnHdr)
    (fwd : Nat → FullForest.FullForestA)
    (hagent : ∀ i, (hdrs i).agent = agent)
    (hadm : ∀ i, Admission.admissible (ctxs i) (hdrs i) (seq i) = true)
    (hstep : ∀ i, Admission.runTurn (ctxs i) (hdrs i) (seq i)
                    (fun s₀ => FullForest.execFullForestA s₀ (fwd i)) = some (seq (i + 1))) :
    ∀ i, agentNonce (seq i).kernel agent < agentNonce (seq (i + 1)).kernel agent := by
  intro i
  have := runTurn_forest_strictly_advances (ctxs i) (hdrs i) (seq i) (fwd i) (hadm i)
    (seq (i + 1)) (hstep i)
  rwa [hagent i] at this

/-- **`deployed_forest_no_replay` — NO REPLAY on the DEPLOYED FOREST executor (the whole-executor close,
UNCONDITIONAL).** Given indexed states `seq i` (all `AccountsWF`) each produced by an ACCEPTED
`Admission.runTurn` over ANY `execFullForestA` body (`hagent`/`hadm`/`hstep`), a fixed pre-anchor opens
the CAS gate at most ONCE. The monotone `advance` is DERIVED internally from the executor witnesses
(`forest_advance_holds`) — NOT taken as a hypothesis, and with NO self-sovereign carve-out (the third
nonce-reset vector closed at the executor) — so no-replay is true OF the deployed forest `runTurn`
sequence unconditionally, the assembled close of the cross-turn defense. -/
theorem deployed_forest_no_replay (S : CommitSurface) (agent : CellId) (t : Turn)
    (seq : Nat → RecChainedState) (ctxs : Nat → Admission.AdmCtx) (hdrs : Nat → Admission.TurnHdr)
    (fwd : Nat → FullForest.FullForestA)
    (wf : ∀ i, AccountsWF (seq i).kernel)
    (hagent : ∀ i, (hdrs i).agent = agent)
    (hadm : ∀ i, Admission.admissible (ctxs i) (hdrs i) (seq i) = true)
    (hstep : ∀ i, Admission.runTurn (ctxs i) (hdrs i) (seq i)
                    (fun s₀ => FullForest.execFullForestA s₀ (fwd i)) = some (seq (i + 1)))
    {i j : Nat} {preCommit : ℤ}
    (hi : LiveCommitMatches
        (acceptedSeq_to_TurnChain S agent t seq wf
          (forest_advance_holds agent seq ctxs hdrs fwd hagent hadm hstep)) i preCommit)
    (hj : LiveCommitMatches
        (acceptedSeq_to_TurnChain S agent t seq wf
          (forest_advance_holds agent seq ctxs hdrs fwd hagent hadm hstep)) j preCommit) :
    i = j :=
  no_replay (acceptedSeq_to_TurnChain S agent t seq wf
    (forest_advance_holds agent seq ctxs hdrs fwd hagent hadm hstep)) hi hj

/-! ## §5 — NON-VACUITY: the no-replay machinery has TEETH (a real chain exists, both polarities).

A concrete monotone chain (the identity-balance kernel with `nonce = i`) inhabits `TurnChain`, so
`no_replay` is not vacuously true; and `commit_no_repeat` distinguishes two indices. We exhibit the
chain abstractly over an arbitrary `CommitSurface` (the CR facts are bundled in `S`). -/

/-- A concrete witness chain: the kernel at turn `i` is a base kernel with the agent's nonce set to
`i`. `AccountsWF` and strict monotonicity hold by construction, so `TurnChain` is INHABITED. -/
def witnessChain (S : CommitSurface) (agent : CellId) (t : Turn)
    (base : RecordKernelState) (hwf : AccountsWF base) (hin : agent ∈ base.accounts) :
    TurnChain S agent t where
  seq i := { base with cell := fun c =>
    if c = agent then EffectTransfer.setNonce (base.cell agent) (Int.ofNat i) else base.cell c }
  wf i := by
    intro c hc
    -- `c ∉ accounts`; `accounts` unchanged, so `c ≠ agent` (agent IS a member), and `cell c = base.cell c`.
    have hacc : ({ base with cell := _ } : RecordKernelState).accounts = base.accounts := rfl
    rw [hacc] at hc
    have hca : c ≠ agent := fun he => hc (he ▸ hin)
    show (if c = agent then _ else base.cell c) = default
    rw [if_neg hca]; exact hwf c hc
  monotone i := by
    show nonceOf (if agent = agent then EffectTransfer.setNonce (base.cell agent) (Int.ofNat i) else base.cell agent)
       < nonceOf (if agent = agent then EffectTransfer.setNonce (base.cell agent) (Int.ofNat (i + 1)) else base.cell agent)
    rw [if_pos rfl, if_pos rfl, EffectTransfer.setNonce_nonceOf, EffectTransfer.setNonce_nonceOf]
    exact Int.ofNat_lt.mpr (by omega)

/-- **NON-VACUITY (positive):** the witness chain's nonce at index `i` is exactly `i` — the chain is
genuinely monotone, not constant. -/
theorem witnessChain_nonce (S : CommitSurface) (agent : CellId) (t : Turn)
    (base : RecordKernelState) (hwf : AccountsWF base) (hin : agent ∈ base.accounts) (i : Nat) :
    agentNonce ((witnessChain S agent t base hwf hin).seq i) agent = Int.ofNat i := by
  show nonceOf (if agent = agent then EffectTransfer.setNonce (base.cell agent) (Int.ofNat i) else base.cell agent) = _
  rw [if_pos rfl, EffectTransfer.setNonce_nonceOf]

/-- **MUTATION-CONFIRM — a replayed proof IS rejected once the commitment advances.** Over a real
`witnessChain`, a proof whose pre-anchor matched at turn `i` (`LiveCommitMatches`) is REJECTED at every
strictly-later turn `j > i`: the live commitment has advanced (the nonce ticked) and never returns, so
the CAS gate is closed. This is `replay_rejected_after_apply` discharged on an inhabited chain — the
defense has teeth, it is not vacuous. -/
theorem witnessChain_replay_rejected (S : CommitSurface) (agent : CellId) (t : Turn)
    (base : RecordKernelState) (hwf : AccountsWF base) (hin : agent ∈ base.accounts)
    (i j : Nat) (preCommit : ℤ)
    (hi : LiveCommitMatches (witnessChain S agent t base hwf hin) i preCommit)
    (hlt : i < j) :
    ¬ LiveCommitMatches (witnessChain S agent t base hwf hin) j preCommit :=
  replay_rejected_after_apply _ hi hlt

/-! ### §5b — MUTATION-CONFIRM: the THIRD nonce-reset vector is CLOSED (`makeSovereign` keeps the nonce).

The carve-out is GONE — `makeSovereign` no longer drops the nonce. We confirm the vector is closed
EXECUTABLY: a self-sovereign step on a cell with a stored nonce `n > 0` keeps the READABLE nonce at `n`
(it used to fall to `0`). A flag/old model would read `0` here; the commitment-form-with-reserved-nonce
rebind reads `n`. This is what makes `BodyNonceNondecreasing` hold for `makeSovereign` (no carve-out). -/

/-- A concrete pre-state for the mutation-confirm: cell 0 is self-owned (empty caps ⇒ authority by
ownership), Live, carrying a nonzero replay nonce (`nonce = 5`). -/
def msNonceWitness : RecChainedState :=
  { kernel :=
      { accounts := {0}
        cell := fun c => if c = 0 then .record [("balance", .int 42), ("nonce", .int 5)]
                         else .record []
        caps := fun _ => [] }
    log := [] }

-- the self-sovereign step COMMITS (actor 0 owns cell 0, Live):
#guard (TurnExecutorFull.makeSovereignStep msNonceWitness 0 0).isSome  -- true
-- ★ THE FIX: the rebound cell's READABLE nonce is PRESERVED at 5 (it used to drop to 0 — the vector):
#guard (match TurnExecutorFull.makeSovereignStep msNonceWitness 0 0 with
        | some s' => (((s'.kernel.cell 0).scalar EffectTransfer.nonceField).getD 0) == 5
        | none    => false)  -- true (nonce PRESERVED — was the down-vector to 0)
-- ...while the host-readable VALUE/balance is STILL gone behind the commitment (the fidelity teeth kept):
#guard (match TurnExecutorFull.makeSovereignStep msNonceWitness 0 0 with
        | some s' => ((s'.kernel.cell 0).scalar "balance").isNone && ((s'.kernel.cell 0).field "commitment").isSome
        | none    => false)  -- true (value dropped, commitment present)

/-! ## §6 — the RESIDUAL (named precisely): what connects this to the deployed CAS.

This module proves, AXIOM-CLEAN, the core no-replay implication over the concrete `recStateCommit`
surface:

    commit-chain (a `TurnChain` with monotone agent nonce) + the CAS gate (`LiveCommitMatches`)
      ⟹ each `(pre, post)` proof is applicable AT MOST ONCE (`no_replay` / `replay_rejected_after_apply`).

The nonce-monotone HYPOTHESIS is grounded by `prologue_strictly_increases_nonce` (the deployed
never-rolled-back prologue bumps the nonce by one).

The RESIDUAL — the precise gap to the FULLY-deployed story — is two named connections, neither an
axiom, both REALIZABLE / already-modeled elsewhere:

  (R1) **The live-commitment register is the protocol's stored commitment.** `LiveCommitMatches`
       models `proof_verify.rs`'s CAS check (live stored commitment == proof pre-anchor; on accept,
       advance to post-anchor). To turn the abstract `TurnChain.seq` into the protocol's actual live
       state, one identifies `seq i` with the kernel after the `i`-th ACCEPTED turn — i.e. composes
       this with `Admission.runTurn`'s committed-prologue post-state. The single-step realization of
       the advance + monotone bump is `Admission.commitPrologue_nonce` /
       `prologue_strictly_increases_nonce`; the receipt-chain CAS leg is
       `Admission.admissible_links_to_head` (`prevReceipt = storedHead`). Wiring the FULL
       `runTurn`-driven sequence into a `TurnChain` (proving every accepted step preserves
       `AccountsWF` — already `recKExec_preserves_AccountsWF` — and bumps the nonce) is mechanical
       composition, deferred as plumbing, NOT a new soundness obligation.

  (R2) **Per-effect: every accepted turn advances the AGENT's nonce, not merely some cell's.** Here
       the monotone field is over the turn-author `agent`. The deployed prologue bumps exactly the
       agent cell (`commitPrologue` edits `agent` only — `commitPrologue_frame`), so this holds for
       the prologue. A body that ALSO wrote the agent's nonce backward would have to defeat the
       caveat/authority gates; the prologue's bump is never rolled back (`prologue_survives_failed_body`),
       so the net agent nonce is strictly greater regardless of the body. Formalizing "net agent
       nonce strictly increases across the whole `runTurn`" (prologue + body) is the residual lemma;
       it is data-bearing (the prologue already proves the strict bump), fail-closed.

Neither residual is a crypto assumption or an open hole: both are mechanical compositions over already
-proved lemmas (`commitPrologue_nonce`, `recKExec_preserves_AccountsWF`, `admissible_links_to_head`).
The genuinely-hard fact — that the commitment cannot hide a stale nonce — is PROVED here
(`commit_inj_nonce`, from the CR set via `commit_binds`). -/

#assert_axioms commit_inj_nonce
#assert_axioms commit_neq_of_nonce_neq
#assert_axioms no_replay
#assert_axioms replay_rejected_after_apply
#assert_axioms TurnChain.commit_no_repeat
#assert_axioms prologue_strictly_increases_nonce
#assert_axioms witnessChain_replay_rejected

-- The ASSEMBLY keystones (the discharged `BodyNonceNondecreasing` + the live-executor wiring) are
-- axiom-clean: the no-replay defense holds OF the deployed forest `runTurn`, not under an assumption.
#assert_axioms nonceOf_setField_of_ne
#assert_axioms makeSovereign_preserves_nonce
#assert_axioms execFullA_agentNonce_nondecr
#assert_axioms execFullA_accounts_mono
#assert_axioms execFullForestA_agentNonce_nondecr
#assert_axioms runTurn_forest_strictly_advances
#assert_axioms deployed_forest_no_replay
#assert_axioms forest_advance_holds

end Dregg2.Circuit.CrossTurnFreshness
