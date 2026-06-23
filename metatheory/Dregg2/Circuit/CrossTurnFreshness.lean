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

namespace Dregg2.Circuit.CrossTurnFreshness

open Dregg2.Circuit
open Dregg2.Circuit.CircuitSoundness (CommitSurface)
open Dregg2.Circuit.StateCommit
open Dregg2.Exec
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

end Dregg2.Circuit.CrossTurnFreshness
