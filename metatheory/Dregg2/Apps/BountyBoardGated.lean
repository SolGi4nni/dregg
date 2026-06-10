/-
# Dregg2.Apps.BountyBoardGated — a VALUE-MOVING bounty board as a VERIFIED USERSPACE APP, RE-POINTED
onto the REAL escrow FACTORY (W2 land-before-kill).

A bounty board is the canonical escrow workflow: a POSTER locks a reward, a CLAIMANT receives it on
completion, or the poster gets it back if it is cancelled. This app is RE-POINTED (W2) off the
off-ledger escrow VERB family (`createEscrowA`/`releaseEscrowA`/`refundEscrowA` over the `escrows`
side-table) onto the FACTORY-BORN escrow CELL: the locked reward is held in the escrow cell's OWN
per-asset `bal` column, the lifecycle lives in a SLOT governed by the factory's installed state machine
`admitTable [(open,released),(open,refunded)]`, and conservation is the ORDINARY per-asset move law —
NO side-table, NO bespoke `recTotalAsset`. (`Dregg2.Apps.EscrowFactory` is the factory; this
app instantiates it.) The witness that the factory replaces the verbs with NO loss of guarantee:

  * the CREDENTIAL/REVOCATION gate teeth are preserved VERBATIM (a forged or revoked credential rejects
    the whole gated turn) — they are orthogonal to which action runs, so they carry over the re-point;
  * the RELEASE-SAFETY contract (conservation / no-double-resolve / release-only-on-condition / value-
    not-stranded / settle-into-a-live-target) is RE-PROVED on the factory-born cell via the
    `EscrowFactory` keystones (which inherit the kernel move law) — the SAME guarantees the verb-era
    `bb_*_conserves` / `bb_*_requires_live_*` theorems carried, now on the factory shape.

## The ops (re-pointed)

  * **post**   — mint a factory escrow cell (`createCellFromFactoryA` ⇒ `EscrowFactory.mintEscrowCell`)
    carrying the deal terms + state machine, then FUND it with an ordinary move of the reward into the
    cell's `bal` column (`EscrowFactory.depositEscrow`). Conservation-neutral mint + conserving move.
  * **claim**  — RELEASE the held reward to the claimant (`EscrowFactory.releaseEscrow`, the probe's
    `escrowRelease`): OPEN→RELEASED + move `bal` out, gated on the condition witness.
  * **cancel** — REFUND the held reward to the poster (`EscrowFactory.refundEscrow`): OPEN→REFUNDED.

## The gate teeth (preserved) + the release-safety contract (re-proved on the factory shape)

  1. `bb_forged_rejected`             — a FORGED credential on ANY gated op ⇒ `none`, ∀ s (gate teeth);
  2. `bb_revoked_rejected`            — a credential whose nullifier sits in `s.kernel.revoked` ⇒ `none`;
  3. `bb_post_mint_conserves`         — minting the factory escrow cell is conservation-neutral;
  4. `bb_post_fund_conserves`         — funding it (the deposit move) conserves every asset;
  5. `bb_claim_conserves`             — a committed claim (release) conserves every asset;
  6. `bb_cancel_conserves`            — a committed cancel (refund) conserves every asset;
  7. `bb_no_double_resolve`           — once claimed, neither a second claim nor a cancel commits;
  8. `bb_claim_requires_condition`    — a claim with a wrong condition witness is rejected;
  9. `bb_claim_requires_live_claimant`— a claim into a non-account claimant is rejected (factory D3);
 10. `bb_cancel_requires_live_poster` — a cancel into a non-account poster is rejected (factory D3);
 11. `bb_open_claimable`/`bb_open_cancellable` — value-not-stranded: a funded OPEN bounty resolves.

RE-POINTED file — replaces the side-table escrow ops with `EscrowFactory`. Does NOT touch
`cell/src/capability.rs`/`seal.rs`, `Argus/Compile.lean`, or the Substrate/Dynamics files. Reuses ONLY
the gated-executor gate teeth + the `EscrowFactory`/probe keystones. `#assert_axioms`-pinned to
`{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Exec.GatedForestCfg
import Dregg2.Exec.CellExecutor
import Dregg2.Exec.CellReal
import Dregg2.Apps.EscrowFactory

namespace Dregg2.Apps.BountyBoardGated

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.StarbridgeGated
open Dregg2.Authority (Cap)
open Dregg2.Apps.EscrowFactory
open Dregg2.Verify.EscrowFactoryProbe

/-! ## §1 — Each bounty-board op as a GATED LEAF NODE through `execFullForestG`.

A bounty-board op is a single `FullActionA`, decorated with a credential (the WHO) and run through the
4-leg gate. `mkAuth cred []` supplies an admitting cap-mode, an empty caveat list, no chain, a
non-revoked nullifier — so `gateOK` reduces to the CREDENTIAL leg ∧ the not-revoked leg. -/

/-- A gated bounty-board node: credential `cred`, an action, no children — the production-entry shape. -/
def bbNode (cred : Authorization Dg Pf) (action : FullActionA) : DForest :=
  ⟨ mkAuth cred [], action, [] ⟩

/-- **post (mint leg)** — mint the factory escrow cell (`createCellFromFactoryA actor escrowCell vk`):
the cell is born carrying the escrow state machine + deal-term immutables. (The FUND leg — an ordinary
move of the reward into the cell — runs as a second gated op; conservation is per-leg.) -/
def postMintNode (cred : Authorization Dg Pf) (actor escrowCell : CellId) (vk : Int) : DForest :=
  bbNode cred (.createCellFromFactoryA actor escrowCell vk)

/-- **post (fund leg)** — fund the minted escrow cell: move `reward` of `asset` from the poster into the
escrow cell's `bal` column (`balanceA`, the deposit move). -/
def postFundNode (cred : Authorization Dg Pf) (poster escrowCell : CellId) (asset : AssetId)
    (reward : Int) : DForest :=
  bbNode cred (.balanceA { actor := poster, src := poster, dst := escrowCell, amt := reward } asset)

/-! ## §2 — The leaf-collapse bridge: a childless gated forest runs EXACTLY its single gated node. -/

/-- **`execFullForestG_leaf` (the load-bearing collapse).** A gated forest with NO children
runs EXACTLY its root gated node step. -/
theorem execFullForestG_leaf (s : RecChainedState) (na : DNodeAuth) (a : FullActionA) :
    execFullForestG s (⟨na, a, []⟩ : DForest) = execFullAGated s na a := by
  show (match execFullAGated s na a with
        | some s' => execFullChildrenG (targetOf a) s' ([] : List DChild)
        | none    => none) = execFullAGated s na a
  cases execFullAGated s na a with
  | none   => rfl
  | some _ => rfl

/-- **`execFullForestG_bbNode` — the bounty-op collapse.** A childless bounty-board op runs
`if gateOK then execFullA action else none`. -/
theorem execFullForestG_bbNode (s : RecChainedState) (cred : Authorization Dg Pf) (a : FullActionA) :
    execFullForestG s (bbNode cred a)
      = (if gateOK (mkAuth cred []) s = true then execFullA s a else none) := by
  rw [bbNode, execFullForestG_leaf, execFullAGated]

/-! ## §3 — The CREDENTIAL gate teeth (preserved verbatim across the re-point). -/

/-- The forged credential's gate leg is FALSE — independent of state, so `gateOK = false`. -/
theorem gateOK_forged_false (s : RecChainedState) : gateOK (mkAuth forgedCred []) s = false := by
  have hcred : credentialValidG (mkAuth forgedCred []) = false := by decide
  unfold gateOK
  rw [hcred]
  simp

/-- **`bb_forged_rejected` (gate teeth #1, preserved).** A bounty-board op (post-mint /
post-fund / claim / cancel — ANY action) with a FORGED credential is rejected by the production turn
entry, for EVERY pre-state `s`. The credential leg fail-closes ⇒ the whole forest rolls back. -/
theorem bb_forged_rejected (s : RecChainedState) (a : FullActionA) :
    execFullForestG s (bbNode forgedCred a) = none := by
  rw [bbNode]
  exact execFullForestG_unauthorized_fails s (mkAuth forgedCred []) a [] (gateOK_forged_false s)

/-- A FORGED post-mint is rejected (no minting an escrow cell without a credential). -/
theorem bb_forged_post_mint_rejected (s : RecChainedState) (actor escrowCell : CellId) (vk : Int) :
    execFullForestG s (postMintNode forgedCred actor escrowCell vk) = none :=
  bb_forged_rejected s (.createCellFromFactoryA actor escrowCell vk)

/-- A FORGED post-fund is rejected (no funding without a credential). -/
theorem bb_forged_post_fund_rejected (s : RecChainedState) (poster escrowCell : CellId)
    (asset : AssetId) (reward : Int) :
    execFullForestG s (postFundNode forgedCred poster escrowCell asset reward) = none :=
  bb_forged_rejected s
    (.balanceA { actor := poster, src := poster, dst := escrowCell, amt := reward } asset)

/-! ## §4 — The REVOCATION gate teeth (preserved verbatim). -/

/-- A gated bounty node carrying an explicit revocation NULLIFIER `nul`. -/
def bbNodeNul (cred : Authorization Dg Pf) (nul : Nat) (action : FullActionA) : DForest :=
  ⟨ { mkAuth cred [] with credNul := nul }, action, [] ⟩

/-- **`bb_revoked_rejected` (gate teeth #2, preserved).** A bounty-board op whose credential
nullifier `nul` is in the COMMITTED revocation registry `s.kernel.revoked` is REJECTED (`none`), for
EVERY pre-state `s` and ANY action — even with a genuine signature. Revocation reads committed state. -/
theorem bb_revoked_rejected (s : RecChainedState) (cred : Authorization Dg Pf) (nul : Nat)
    (a : FullActionA) (hrev : s.kernel.revoked.contains nul = true) :
    execFullForestG s (bbNodeNul cred nul a) = none := by
  rw [bbNodeNul]
  exact execFullForestG_unauthorized_fails s { mkAuth cred [] with credNul := nul } a []
    (gateOK_revoked_fails { mkAuth cred [] with credNul := nul } s hrev)

/-! ## §5 — The RELEASE-SAFETY CONTRACT, re-proved on the FACTORY-BORN cell.

These are the guarantees the verb-era `bb_*_conserves` / `bb_*_requires_live_*` carried, now re-pointed
onto the factory shape via the `EscrowFactory` keystones (which inherit the kernel per-asset move law).
The bounty escrow cell `e` holds its reward in `e`'s OWN `bal` column; `claim`/`cancel` are the probe's
`escrowRelease`/`escrowRefund` reading the installed state slot + moving `bal` out. -/

/-- **claim** — the claimant RECEIVES the held reward (release the factory escrow `e` to `beneficiary`,
gated on the condition `witness`). -/
def claim (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId) (witness : Int) :
    Option RecordKernelState :=
  EscrowFactory.releaseEscrow k e beneficiary asset witness

/-- **cancel** — the poster gets the held reward BACK (refund the factory escrow `e` to `depositor`). -/
def cancel (k : RecordKernelState) (e depositor : CellId) (asset : AssetId) :
    Option RecordKernelState :=
  EscrowFactory.refundEscrow k e depositor asset

/-- **`bb_post_mint_conserves` — THEOREM 3 (re-pointed).** Minting the factory escrow cell is
conservation-neutral for every asset (born EMPTY; the reward is funded separately). -/
theorem bb_post_mint_conserves {s s' : RecChainedState} {actor escrowCell : CellId} {vk : Int}
    (b : AssetId) (h : mintEscrowCell s actor escrowCell vk = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  mintEscrowCell_neutral b h

/-- **`bb_post_fund_conserves` — THEOREM 4 (re-pointed).** Funding the escrow cell (the deposit move)
conserves every asset — the reward leaves the poster's column and enters the escrow cell's column. -/
theorem bb_post_fund_conserves {k k' : RecordKernelState} {poster escrowCell : CellId} {asset : AssetId}
    {reward : Int} (h : depositEscrow k poster escrowCell asset reward = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b :=
  depositEscrow_conserves h b

/-- **`bb_claim_conserves` — THEOREM 5 (re-pointed).** A committed claim (release) conserves every
asset: the reward is DELIVERED from the held `bal` column, not conjured. -/
theorem bb_claim_conserves {k k' : RecordKernelState} {e beneficiary : CellId} {asset : AssetId}
    {witness : Int} (h : claim k e beneficiary asset witness = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b :=
  EscrowFactory.release_conserves h b

/-- **`bb_cancel_conserves` — THEOREM 6 (re-pointed).** A committed cancel (refund) conserves every
asset: the reward is refunded from the held column back to the poster. -/
theorem bb_cancel_conserves {k k' : RecordKernelState} {e depositor : CellId} {asset : AssetId}
    (h : cancel k e depositor asset = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b :=
  EscrowFactory.refund_conserves h b

/-- **`bb_no_double_resolve` — THEOREM 7 (the no-double-resolve teeth, factory shape).** Once a bounty
has been claimed (driven to RELEASED), neither a second claim nor a cancel commits — the installed state
machine fail-closes. The reward leaves the held column AT MOST ONCE. -/
theorem bb_no_double_resolve {k : RecordKernelState} {e tgt : CellId} {asset : AssetId} {witness : Int}
    (hres : escrowState k e = sReleased) :
    claim k e tgt asset witness = none ∧ cancel k e tgt asset = none :=
  EscrowFactory.no_double_resolve hres

/-- **`bb_claim_requires_condition` — THEOREM 8 (release-only-on-condition).** A claim whose supplied
condition witness ≠ the bounty's frozen `condition` slot is REJECTED — nobody collects without
discharging the bounty's completion condition. -/
theorem bb_claim_requires_condition {k : RecordKernelState} {e beneficiary : CellId} {asset : AssetId}
    {witness : Int} (hbad : witness ≠ escrowCondition k e) :
    claim k e beneficiary asset witness = none :=
  EscrowFactory.release_requires_condition hbad

/-- **`bb_claim_requires_live_claimant` — THEOREM 9 (the D3 liveness teeth, factory shape).** A claim
whose claimant is NOT a live account is REJECTED (`none`) — the reward cannot be moved into a non-account
(which would silently destroy it). The move's own fail-closed guard carries this. -/
theorem bb_claim_requires_live_claimant {k : RecordKernelState} {e claimant : CellId} {asset : AssetId}
    {witness : Int} (hdead : claimant ∉ k.accounts) :
    claim k e claimant asset witness = none :=
  EscrowFactory.release_requires_live_beneficiary hdead

/-- **`bb_cancel_requires_live_poster` — THEOREM 10 (the symmetric refund teeth).** A cancel whose
poster (refund target) is NOT a live account is REJECTED — the reward cannot be refunded into a
non-account. -/
theorem bb_cancel_requires_live_poster {k : RecordKernelState} {e poster : CellId} {asset : AssetId}
    (hdead : poster ∉ k.accounts) :
    cancel k e poster asset = none :=
  EscrowFactory.refund_requires_live_depositor hdead

/-- **`bb_open_claimable` — THEOREM 11 (value-not-stranded, claim side).** A funded OPEN bounty with the
correct condition and a `SettleReady` claimant CLAIMS (commits) — the reward is deliverable, not
trapped. -/
theorem bb_open_claimable {k : RecordKernelState} {e claimant : CellId} {asset : AssetId} {witness : Int}
    (hopen : escrowState k e = sOpen) (hcond : witness = escrowCondition k e)
    (hr : SettleReady k e claimant asset) :
    (claim k e claimant asset witness).isSome :=
  EscrowFactory.open_releasable hopen hcond hr

/-- **`bb_open_cancellable` — THEOREM 11 (value-not-stranded, cancel side).** A funded OPEN bounty with a
`SettleReady` poster CANCELS (commits) — the abort path always returns the reward. -/
theorem bb_open_cancellable {k : RecordKernelState} {e poster : CellId} {asset : AssetId}
    (hopen : escrowState k e = sOpen) (hr : SettleReady k e poster asset) :
    (cancel k e poster asset).isSome :=
  EscrowFactory.open_refundable hopen hr

/-! ## §6 — NON-VACUITY: a concrete factory-born bounty board, end to end + `#guard` witnesses.

`board0` PUBLISHES the bounty escrow factory at key 7 (reward 40, depositor=poster 0, beneficiary
1, condition 99, asset 0). The POSTER/minter is cell `0` (holds 100 of asset 0 + a node-cap to the
fresh escrow cell `3`); the CLAIMANT is cell `1` (holds 5 of asset 0). We POST (mint cell `3` from the
factory, then fund it with 40), then witness: a good gated mint COMMITS; a forged credential ⇒ `none`; a
revoked credential ⇒ `none`; a claim with the condition delivers 40 to the claimant; a wrong condition ⇒
`none`; a cancel refunds the poster; a double-claim fails; a claim into a non-account fails. Every
theorem witnessed REAL on the FACTORY-BORN cell. -/

/-- The funded bounty board: poster/minter `0` holds 100 of asset 0 + a node-cap to the fresh escrow
cell `3`; claimant `1` holds 5. Publishes the escrow factory at key 7. Empty revocation registry. -/
def board0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun c => if c = 0 then [Cap.node 3] else []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0
        factories := escrowRegistry 7 40 0 1 99 0 }
    log := [] }

/-- The id/key of the bounty escrow factory. -/
abbrev bountyVk : Int := 7
/-- The fresh escrow cell the factory mints for this bounty. -/
abbrev escrowCellId : CellId := 3
/-- The reward: 40 of asset 0. -/
abbrev rewardAmt : Int := 40

/-- POST: mint the factory escrow cell `3`, then fund it with 40 of asset 0 (poster = cell 0), each a
gated op through `execFullForestG`. -/
def boardPosted : Option RecChainedState :=
  (execFullForestG board0 (postMintNode goodCred 0 escrowCellId bountyVk)).bind
    (fun s => execFullForestG s (postFundNode goodCred 0 escrowCellId 0 rewardAmt))

-- the gate passes for the genuine credential, fails for the forged one:
#guard (gateOK (mkAuth goodCred []) board0)                       --  true
#guard (gateOK (mkAuth forgedCred []) board0) == false           --  false

-- (i) the POST mints + funds: the escrow cell `3` holds the locked 40 in ITS bal column:
#guard (boardPosted.isSome)                                                                --  true (posted!)
#guard (boardPosted.map (fun s => s.kernel.bal escrowCellId 0)) == some 40                  --  escrow holds 40
#guard (boardPosted.map (fun s => s.kernel.bal 0 0)) == some 60                             --  poster 100→60
#guard (boardPosted.map (fun s => escrowState s.kernel escrowCellId)) == some sOpen         --  OPEN
#guard (boardPosted.map (fun s => escrowCondition s.kernel escrowCellId)) == some 99        --  condition installed
-- ...and the minted cell carries the escrow state machine + deal-term immutables (factory keystone):
#guard (boardPosted.map (fun s => s.kernel.slotCaveats escrowCellId))
        == some (escrowFactoryEntry 40 0 1 99 0).caveats
-- ...and the COMBINED supply is FIXED (pure per-asset move conservation, NO side-table):
#guard (boardPosted.map (fun s => recTotalAsset s.kernel 0)) == some 105                    --  conserved

-- (ii) a FORGED post-mint ⇒ none (gate teeth):
#guard ((execFullForestG board0 (postMintNode forgedCred 0 escrowCellId bountyVk)).isSome) == false

-- (iii) a REVOKED post-mint ⇒ none: a board whose registry holds nullifier 5, minting with it rejects:
#guard ((execFullForestG
          { board0 with kernel := { board0.kernel with revoked := [5] } }
          (bbNodeNul goodCred 5 (.createCellFromFactoryA 0 escrowCellId bountyVk))).isSome) == false
-- ...and the SAME mint with a non-revoked nullifier (0) COMMITS (revocation is the sole reason above):
#guard ((execFullForestG
          { board0 with kernel := { board0.kernel with revoked := [5] } }
          (bbNodeNul goodCred 0 (.createCellFromFactoryA 0 escrowCellId bountyVk))).isSome)  --  true

-- (iv) a CLAIM (release with condition 99) delivers 40 to claimant 1 (5→45), advances to RELEASED:
#guard (boardPosted.bind (fun s => claim s.kernel escrowCellId 1 0 99) |>.map (fun k => k.bal 1 0)) == some 45
#guard (boardPosted.bind (fun s => claim s.kernel escrowCellId 1 0 99) |>.map (fun k => k.bal escrowCellId 0)) == some 0
#guard (boardPosted.bind (fun s => claim s.kernel escrowCellId 1 0 99) |>.map (fun k => escrowState k escrowCellId)) == some sReleased
#guard (boardPosted.bind (fun s => claim s.kernel escrowCellId 1 0 99) |>.map (fun k => recTotalAsset k 0)) == some 105

-- (v) a WRONG condition (7 ≠ 99) ⇒ none (release-only-on-condition):
#guard (boardPosted.bind (fun s => claim s.kernel escrowCellId 1 0 7) |>.isSome) == false

-- (vi) a CANCEL (refund) returns 40 to poster 0 (60→100) and advances to REFUNDED:
#guard (boardPosted.bind (fun s => cancel s.kernel escrowCellId 0 0) |>.map (fun k => k.bal 0 0)) == some 100
#guard (boardPosted.bind (fun s => cancel s.kernel escrowCellId 0 0) |>.map (fun k => escrowState k escrowCellId)) == some sRefunded

-- (vii) NO-DOUBLE-RESOLVE: claim then a second claim AND a cancel both fail:
#guard (boardPosted.bind (fun s => claim s.kernel escrowCellId 1 0 99) |>.bind (fun k => claim k escrowCellId 1 0 99) |>.isSome) == false
#guard (boardPosted.bind (fun s => claim s.kernel escrowCellId 1 0 99) |>.bind (fun k => cancel k escrowCellId 0 0) |>.isSome) == false

-- (viii) LIVENESS TEETH: a claim into a NON-ACCOUNT claimant (9) ⇒ none (cannot land in a non-account):
#guard (boardPosted.bind (fun s => claim s.kernel escrowCellId 9 0 99) |>.isSome) == false

/-! ## §DELETION — see `Dregg2.Apps.EscrowFactory` §DELETION for the W2 escrow-verb burn-down. This app
is now RE-POINTED onto the factory (one of the land-before-kill prerequisites discharged); the verb
deletion is the subsequent W2 commit, gated on the remaining escrow consumers re-pointing. -/

#assert_axioms execFullForestG_leaf
#assert_axioms execFullForestG_bbNode
#assert_axioms gateOK_forged_false
#assert_axioms bb_forged_rejected
#assert_axioms bb_forged_post_mint_rejected
#assert_axioms bb_forged_post_fund_rejected
#assert_axioms bb_revoked_rejected
#assert_axioms bb_post_mint_conserves
#assert_axioms bb_post_fund_conserves
#assert_axioms bb_claim_conserves
#assert_axioms bb_cancel_conserves
#assert_axioms bb_no_double_resolve
#assert_axioms bb_claim_requires_condition
#assert_axioms bb_claim_requires_live_claimant
#assert_axioms bb_cancel_requires_live_poster
#assert_axioms bb_open_claimable
#assert_axioms bb_open_cancellable

end Dregg2.Apps.BountyBoardGated
