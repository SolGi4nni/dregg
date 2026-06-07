/-
# Dregg2.Apps.BountyBoard — dregg1's bounty board as a verified cell-program (escrow post/claim/cancel).

`apps/bounty-board/` and `starbridge-apps/` (future) model a federated bounty workflow: a POSTER locks a
reward in escrow, a CLAIMANT receives it on completion, or the poster recovers it on cancel. Each step
is a single escrow `FullActionA` on the REAL `RecordKernelState` (`createEscrowA` / `releaseEscrowA` /
`refundEscrowA`), composed through the shipped credential-blind executor `execFullForestA`.

This is the ungated cell-program dual of `BountyBoardGated` (which runs the SAME escrow ops through
`execFullForestG` with a §8 credential gate). Here the load-bearing guarantees are kernel-native:

  * **CONSERVATION** — post/claim/cancel preserve the combined per-asset measure `recTotalAssetWithEscrow`
    (value parks into the holding store, then delivers or refunds — never minted or burned).
  * **LIVENESS (D3 teeth)** — claim/cancel to a non-live recipient/creator FAIL-CLOSED (value cannot
    vanish into a frozen cell).
  * **AUTHORITY (honest scope)** — a committed post is self-authorized; release/refund only moves a
    PARKED record (`release_only_parked` analogue).

Templates: `Apps/AtomicSwap.lean` (REAL-kernel escrow composition), `Apps/BountyBoardGated.lean` (the
domain ops and `#guard` witnesses).
-/
import Dregg2.Exec.RecordKernel
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Exec.FullForest

namespace Dregg2.Apps.BountyBoard

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest

/-! ## §1 — The bounty-board DOMAIN: poster, claimant, reward escrow. -/

/-- A bounty escrow id (dregg1's obligation / escrow key). -/
abbrev BountyId := Nat

/-- **`hasOpenBounty s id`** — is there an unresolved escrow record keyed by `id`? The decidable
lookup the board referee runs before claim/cancel. -/
def hasOpenBounty (s : RecChainedState) (id : BountyId) : Bool :=
  match s.kernel.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | some _ => true
  | none   => false

/-! ## §2 — The three CORE ops as REAL executor turns (post / claim / cancel). -/

/-- **post** — the poster LOCKS the reward (`createEscrowA`). Self-authorizes (`actor = poster = src`);
debits the poster's `asset` column and parks an unresolved record (recipient = claimant). -/
def bbPost (id : BountyId) (poster claimant : CellId) (asset : AssetId) (reward : Int) : FullForestA :=
  ⟨ .createEscrowA id poster poster claimant asset reward, [] ⟩

/-- **bbClaim** — the claimant RECEIVES the reward (`releaseEscrowA`). Credits the record's recipient
at the record's asset when the claimant is lifecycle-live. -/
def bbClaim (id : BountyId) (actor : CellId) : FullForestA :=
  ⟨ .releaseEscrowA id actor, [] ⟩

/-- **bbCancel** — the poster gets the reward BACK (`refundEscrowA`). Credits the record's creator
(refund target) when the poster is lifecycle-live. -/
def bbCancel (id : BountyId) (actor : CellId) : FullForestA :=
  ⟨ .refundEscrowA id actor, [] ⟩

/-! ## §3 — Per-asset ledger delta = 0 (escrow ops are combined-neutral). -/

theorem bbPost_delta_zero {id : BountyId} {poster claimant : CellId} {asset : AssetId} {reward : Int}
    (b : AssetId) :
    turnLedgerDeltaAsset (lowerForestA (bbPost id poster claimant asset reward)) b = 0 := by
  simp [bbPost, lowerForestA, lowerChildrenA, turnLedgerDeltaAsset, ledgerDeltaAsset]

theorem bbClaim_delta_zero {id : BountyId} {actor : CellId} (b : AssetId) :
    turnLedgerDeltaAsset (lowerForestA (bbClaim id actor)) b = 0 := by
  simp [bbClaim, lowerForestA, lowerChildrenA, turnLedgerDeltaAsset, ledgerDeltaAsset]

theorem bbCancel_delta_zero {id : BountyId} {actor : CellId} (b : AssetId) :
    turnLedgerDeltaAsset (lowerForestA (bbCancel id actor)) b = 0 := by
  simp [bbCancel, lowerForestA, lowerChildrenA, turnLedgerDeltaAsset, ledgerDeltaAsset]

/-! ## §4 — HEADLINE theorems: conservation + D3 liveness teeth. -/

theorem bb_post_conserves {s s' : RecChainedState} {id : BountyId} {poster claimant : CellId}
    {asset : AssetId} {reward : Int} (b : AssetId)
    (h : execFullForestA s (bbPost id poster claimant asset reward) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestA_conserves_per_asset s s' (bbPost id poster claimant asset reward) b h
    (bbPost_delta_zero (id:=id) (poster:=poster) (claimant:=claimant) (asset:=asset) (reward:=reward) b)

theorem bb_claim_conserves {s s' : RecChainedState} {id : BountyId} {actor : CellId} (b : AssetId)
    (h : execFullForestA s (bbClaim id actor) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestA_conserves_per_asset s s' (bbClaim id actor) b h
    (bbClaim_delta_zero (id:=id) (actor:=actor) b)

theorem bb_cancel_conserves {s s' : RecChainedState} {id : BountyId} {actor : CellId} (b : AssetId)
    (h : execFullForestA s (bbCancel id actor) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestA_conserves_per_asset s s' (bbCancel id actor) b h
    (bbCancel_delta_zero (id:=id) (actor:=actor) b)

/-- **`bb_claim_requires_live_claimant` — PROVED (D3 liveness).** Claiming into a non-live recipient
cell FAIL-CLOSED — the reward cannot be delivered into a frozen cell. -/
theorem bb_claim_requires_live_claimant (s : RecChainedState) (id : BountyId) (actor : CellId)
    {r : EscrowRecord}
    (hfind : s.kernel.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = some r)
    (hdead : cellLifecycleLive s.kernel r.recipient = false) :
    execFullForestA s (bbClaim id actor) = none := by
  have hchain : releaseEscrowChainA s id actor = none := by
    unfold releaseEscrowChainA
    by_cases hg : releaseSettleAuthB s.kernel id actor
    · rw [if_pos hg]
      rw [releaseEscrowKAsset_nonlive_fails hfind hdead]
    · rw [if_neg hg]
  rw [execFullForestA_eq_execFullTurnA]
  simp only [bbClaim, lowerForestA, lowerChildrenA, execFullTurnA, execFullA, hchain]

/-- **`bb_cancel_requires_live_poster` — PROVED (symmetric refund teeth).** -/
theorem bb_cancel_requires_live_poster (s : RecChainedState) (id : BountyId) (actor : CellId)
    {r : EscrowRecord}
    (hfind : s.kernel.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = some r)
    (hdead : cellLifecycleLive s.kernel r.creator = false) :
    execFullForestA s (bbCancel id actor) = none := by
  have hchain : refundEscrowChainA s id actor = none := by
    unfold refundEscrowChainA
    by_cases hg : refundSettleAuthB s.kernel id actor
    · rw [if_pos hg]
      rw [refundEscrowKAsset_nonlive_fails hfind hdead]
    · rw [if_neg hg]
  rw [execFullForestA_eq_execFullTurnA]
  simp only [bbCancel, lowerForestA, lowerChildrenA, execFullTurnA, execFullA, hchain]

/-! ## §5 — NON-VACUITY: a funded board + `#guard` witnesses (mirrors `BountyBoardGated.board0`). -/

/-- Poster cell `0` holds 100 of asset 0; claimant cell `1` holds 5. Both live; empty escrow store. -/
def board0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0 }
    log := [] }

abbrev bountyId : BountyId := 7
abbrev rewardAmt : Int := 40

def boardPosted : Option RecChainedState :=
  execFullForestA board0 (bbPost bountyId 0 1 0 rewardAmt)

-- A GOOD post COMMITS and parks the reward (poster's bare bal drops; combined measure fixed):
#guard (boardPosted.isSome)  --  true
#guard (boardPosted.map (fun s => s.kernel.bal 0 0)) == some 60  --  some 60
#guard (boardPosted.map (fun s => hasOpenBounty s bountyId)) == some true  --  some true
#guard (boardPosted.map (fun s => (recTotalAssetWithEscrow s.kernel 0,
                                   recTotalAssetWithEscrow s.kernel 1)))
      == some (105, 7)  --  some (105, 7) — combined conserved

-- Claim delivers to the live claimant:
#guard ((boardPosted.bind (fun s => execFullForestA s (bbClaim bountyId 1))).map
        (fun s => s.kernel.bal 1 0)) == some 45  --  some 45

-- Cancel refunds the live poster:
#guard ((boardPosted.bind (fun s => execFullForestA s (bbCancel bountyId 0))).map
        (fun s => s.kernel.bal 0 0)) == some 100  --  some 100

/-! ## §6 — Axiom-hygiene pins. -/

#assert_axioms bbPost_delta_zero
#assert_axioms bbClaim_delta_zero
#assert_axioms bbCancel_delta_zero
#assert_axioms bb_post_conserves
#assert_axioms bb_claim_conserves
#assert_axioms bb_cancel_conserves
#assert_axioms bb_claim_requires_live_claimant
#assert_axioms bb_cancel_requires_live_poster

end Dregg2.Apps.BountyBoard