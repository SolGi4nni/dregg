/-
# Dregg2.Apps.BountyBoardGated — a VALUE-MOVING bounty board as a VERIFIED USERSPACE APP on the ONE GATED executor.

A bounty board is the canonical escrow workflow: a POSTER locks a reward, a CLAIMANT receives it on
completion, or the poster gets it back if it is cancelled. Each step is ONE credential-gated turn —
a single leaf node `⟨ mkAuth cred [], <escrow FullActionA>, [] ⟩` run through the production turn
entry `Dregg2.Exec.FullForestAuth.execFullForestG` (the `dregg_exec_full_forest_auth` 4-leg gate:
credential ∧ cap-authority ∧ caveats-discharged ∧ not-revoked). The end-user theorems are therefore
about the EXECUTED, credential-gated turn — not a credential-blind toy.

This is the `AtomicSwap` ESCROW pattern (lock = `createEscrowA` parks held value, settle = release/refund
credits a cell) lifted onto the GATED executor, and the `NameserviceGated` GATED-single-node pattern
(local `Verifiable` instance, `mkAuth cred []`, `execFullForestG_leaf` collapse, forged/revoked ⇒ none,
per-asset conservation off `execFullForestG_conserves_per_asset`).

## The three ops (each a SINGLE gated leaf node through `execFullForestG`)

  * **post**   — the poster LOCKS the reward: `createEscrowA id poster poster claimant asset reward`.
    The poster self-authorizes (`actor == src == poster`), debits its `asset` column by `reward`, and
    parks an unresolved escrow record (recipient = the claimant) keyed by `id`. The reward leaves the
    poster's ledger but is CONSERVED into the off-ledger holding store (combined per-asset Δ = 0).
  * **claim**  — the claimant RECEIVES the reward: `releaseEscrowA id actor`. The kernel finds the
    unresolved record by `id`, credits its `recipient` (the claimant) `reward` of `asset`, and marks it
    resolved — IF the claimant is a LIVE account (the D3 settle-liveness gate). Combined per-asset Δ = 0
    (value moves OUT of the holding store back onto the ledger).
  * **cancel** — the poster gets the reward back: `refundEscrowA id actor`. Symmetric to claim, but the
    kernel credits the record's `creator` (the poster) — IF the poster is live.

## End-user theorems

  1. `bb_forged_rejected`            — a FORGED credential on ANY op ⇒ the whole gated turn rejects (`none`), ∀ s;
  2. `bb_revoked_rejected`           — a credential whose nullifier sits in `s.kernel.revoked` ⇒ `none`, ∀ s
                                       (poster or claimant — same gate, `gateOK_revoked_fails`);
  3. `bb_post_conserves`            — a COMMITTED post moves NO asset's combined supply (parked, not minted);
  4. `bb_claim_conserves`           — a COMMITTED claim moves NO asset's combined supply (delivered from the store);
  5. `bb_cancel_conserves`          — a COMMITTED cancel likewise conserves every asset;
  6. `bb_claim_requires_live_claimant` — the D3 LIVENESS TEETH: claiming to a Sealed/Destroyed claimant ⇒ `none`
                                       (reuse `releaseEscrowKAsset_nonlive_fails`) — value cannot be delivered into a
                                       frozen cell;
  7. `bb_cancel_requires_live_poster`  — the symmetric refund-side teeth (`refundEscrowKAsset_nonlive_fails`).

## App-level semantics (Hatchery bridge — §9)

Per-op teeth are obligations; §9 connects them to production crowns on `trajG`:
  * `bb_asset_conserved_forever` — reward-asset supply never drifts (`conservation%` shape);
  * `bb_board0_assets_conserved_forever` — the canonical funded-board witness;
  * `bb_revoked_rejected_forever` — revoked bounty credentials fail at every schedule index;
  * `bb_safety_forever` — composed conservation + revocation-registry persistence.

Plus a concrete FUNDED state (`board0`) whose `#guard`s witness non-vacuity: a good post COMMITS &
PARKS the reward (poster's ledger drops, combined measure fixed); a claim CREDITS the claimant; a cancel
REFUNDS the poster; a forged credential ⇒ `none`; a revoked credential ⇒ `none`; a claim to a SEALED
claimant ⇒ `none`. So every theorem is witnessed REAL, not vacuous.

Zero `sorry`/`admit`/`native_decide`/`axiom`. NEW file only — does NOT touch `AtomicSwap.lean`,
`NameserviceGated.lean`, `FullForestAuth.lean`, nor `Dregg2.lean`. Reuses ONLY the proved gated-executor
keystones + the proved kernel escrow conservation/liveness teeth. `#assert_axioms`-pinned to
`{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Exec.GatedForestCfg
import Dregg2.Exec.CellExecutor
import Dregg2.Exec.CellReal
import Dregg2.Verify.Catalog
import Dregg2.Verify.Contract

namespace Dregg2.Apps.BountyBoardGated

open Dregg2.Exec
open Dregg2.Exec (cellObsA trajG SchedG)
open Dregg2.Verify (gateRevoked asset_conserved_forever_production assetConserved composeContracts)
open Dregg2.Verify.Production (Contract Sched)
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.StarbridgeGated
open Dregg2.Exec.StarbridgeGated

/-! ## §1a — Domain carriers for Hatchery contracts. -/

/-- The reward asset class (asset `0` on `board0`). -/
abbrev rewardAsset : AssetId := 0

/-! ## §1 — Each bounty-board op as a GATED LEAF NODE through `execFullForestG`.

A bounty-board op is a single ESCROW `FullActionA`, decorated with a credential (the WHO) and run
through the 4-leg gate. `mkAuth cred []` (from `FullForestAuth.Demo`) supplies an admitting cap-mode
(`.unchecked (Guard.all [])`), an empty within-cell caveat list (the GATE's caveat leg vacuously
discharged), no chain, and a non-revoked nullifier — so `gateOK` reduces to the CREDENTIAL leg ∧ the
not-revoked leg. -/

/-- A gated bounty-board node: credential `cred`, an escrow `action`, no children — the production-entry
shape `⟨ mkAuth cred [], action, [] ⟩`. -/
def bbNode (cred : Authorization Dg Pf) (action : FullActionA) : DForest :=
  ⟨ mkAuth cred [], action, [] ⟩

/-- **post** — the poster LOCKS the reward (`createEscrowA id poster poster claimant asset reward`).
The poster self-authorizes (`actor == src == poster`); the reward is debited from the poster's `asset`
column and parked as an unresolved record (recipient = the claimant) keyed by `id`. -/
def postNode (cred : Authorization Dg Pf) (id : Nat) (poster claimant : CellId)
    (asset : AssetId) (reward : Int) : DForest :=
  bbNode cred (.createEscrowA id poster poster claimant asset reward)

/-- **claim** — the claimant RECEIVES the reward (`releaseEscrowA id actor`). The kernel credits the
parked record's `recipient` (the claimant) on a successful release — gated on the claimant being LIVE. -/
def claimNode (cred : Authorization Dg Pf) (id : Nat) (actor : CellId) : DForest :=
  bbNode cred (.releaseEscrowA id actor)

/-- **cancel** — the poster gets the reward BACK (`refundEscrowA id actor`). The kernel credits the
parked record's `creator` (the poster) on a successful refund — gated on the poster being LIVE. -/
def cancelNode (cred : Authorization Dg Pf) (id : Nat) (actor : CellId) : DForest :=
  bbNode cred (.refundEscrowA id actor)

/-! ## §2 — The leaf-collapse bridge: a childless gated forest runs EXACTLY its single gated node. -/

/-- **`execFullForestG_leaf` — PROVED (the load-bearing collapse).** A gated forest with NO children
runs EXACTLY its root gated node step: `execFullForestG s ⟨na, a, []⟩ = execFullAGated s na a`. (Both
branches of `execFullForestG`'s match collapse because `execFullChildrenG _ s' [] = some s'`.) The
bridge through which every bounty-board op's `none`/`some` is read off `execFullAGated` directly. -/
theorem execFullForestG_leaf (s : RecChainedState) (na : DNodeAuth) (a : FullActionA) :
    execFullForestG s (⟨na, a, []⟩ : DForest) = execFullAGated s na a := by
  show (match execFullAGated s na a with
        | some s' => execFullChildrenG (targetOf a) s' ([] : List DChild)
        | none    => none) = execFullAGated s na a
  cases execFullAGated s na a with
  | none   => rfl
  | some _ => rfl

/-- **`execFullForestG_bbNode` — the bounty-op collapse.** A childless bounty-board op runs
`if gateOK then execFullA action else none`. The unfolding every theorem below rests on. -/
theorem execFullForestG_bbNode (s : RecChainedState) (cred : Authorization Dg Pf) (a : FullActionA) :
    execFullForestG s (bbNode cred a)
      = (if gateOK (mkAuth cred []) s = true then execFullA s a else none) := by
  rw [bbNode, execFullForestG_leaf, execFullAGated]

/-! ## §3 — The CREDENTIAL gate: `goodCred` admits, `forgedCred` (and any forged cred) fail-closed.

`gateOK (mkAuth cred []) s = credentialValidG (mkAuth cred []) && capAuthorityG (mkAuth cred []) &&
caveatsDischarged (mkAuth cred []) s && revocationGate (mkAuth cred []) s`. For `mkAuth`: the cap mode
is `.unchecked (Guard.all [])` (admits), the within-cell caveat list is `[]` (vacuously discharged, no
chain), the nullifier is `0`. So `gateOK` is exactly the credential leg ∧ the not-revoked leg. -/

/-- The forged credential's gate leg is FALSE (`portalVerify (.signature 7 8) = decide (7 = 8) = false`)
— independent of state, so the whole gate `gateOK (mkAuth forgedCred []) s = false`. -/
theorem gateOK_forged_false (s : RecChainedState) : gateOK (mkAuth forgedCred []) s = false := by
  have hcred : credentialValidG (mkAuth forgedCred []) = false := by decide
  unfold gateOK
  rw [hcred]
  simp

/-! ## §4 — END-USER THEOREM 1: a FORGED credential ⇒ the whole gated turn REJECTS (∀ s, any op). -/

/-- **`bb_forged_rejected` — PROVED.** A bounty-board op (post/claim/cancel — ANY escrow action)
presented with a FORGED credential is rejected by the production turn entry: `execFullForestG s
(bbNode forgedCred a) = none`, for EVERY pre-state `s`. The credential leg fail-closes ⇒ the whole
forest rolls back — nobody can post/claim/cancel without a genuine credential. -/
theorem bb_forged_rejected (s : RecChainedState) (a : FullActionA) :
    execFullForestG s (bbNode forgedCred a) = none := by
  rw [bbNode]
  exact execFullForestG_unauthorized_fails s (mkAuth forgedCred []) a [] (gateOK_forged_false s)

/-- A FORGED post is rejected (the headline poster-side shape). -/
theorem bb_forged_post_rejected (s : RecChainedState) (id : Nat) (poster claimant : CellId)
    (asset : AssetId) (reward : Int) :
    execFullForestG s (postNode forgedCred id poster claimant asset reward) = none :=
  bb_forged_rejected s (.createEscrowA id poster poster claimant asset reward)

/-- A FORGED claim is rejected (no stealing the reward without a credential). -/
theorem bb_forged_claim_rejected (s : RecChainedState) (id : Nat) (actor : CellId) :
    execFullForestG s (claimNode forgedCred id actor) = none :=
  bb_forged_rejected s (.releaseEscrowA id actor)

/-! ## §5 — END-USER THEOREM 2: a REVOKED credential ⇒ the whole gated turn REJECTS (∀ s, any op).

The revocation leg reads the COMMITTED kernel registry `s.kernel.revoked` (adversary-uncontrollable).
If the credential's nullifier sits there, `gateOK = false` regardless of how valid the signature is —
so the whole forest rejects. We carry a nullifier-bearing node so the revocation registry can bite. -/

/-- A gated bounty node carrying an explicit revocation NULLIFIER `nul` (so the kernel registry can
identify and revoke this credential). All other auth fields as `mkAuth cred []`. -/
def bbNodeNul (cred : Authorization Dg Pf) (nul : Nat) (action : FullActionA) : DForest :=
  ⟨ { mkAuth cred [] with credNul := nul }, action, [] ⟩

/-- **`bb_revoked_rejected` — PROVED.** A bounty-board op whose credential nullifier `nul` is in the
COMMITTED revocation registry `s.kernel.revoked` is REJECTED by the gate (`none`), for EVERY pre-state
`s` and ANY escrow action — even with a genuine signature. A revoked poster cannot post, a revoked
claimant cannot claim; revocation reads committed state, so it cannot be bypassed. -/
theorem bb_revoked_rejected (s : RecChainedState) (cred : Authorization Dg Pf) (nul : Nat)
    (a : FullActionA) (hrev : s.kernel.revoked.contains nul = true) :
    execFullForestG s (bbNodeNul cred nul a) = none := by
  rw [bbNodeNul]
  exact execFullForestG_unauthorized_fails s { mkAuth cred [] with credNul := nul } a []
    (gateOK_revoked_fails { mkAuth cred [] with credNul := nul } s hrev)

/-! ## §6 — END-USER THEOREMS 3–5: a committed op CONSERVES every asset (per-asset combined measure).

A bounty-board op is a single escrow `FullActionA`, each of which has `ledgerDeltaAsset = 0` for EVERY
asset (the bal debit/credit is offset by the holding-store park/settle — COMBINED per-asset neutral).
So its per-asset turn delta is `0`, and `execFullForestG_conserves_per_asset` gives supply preservation
for free. The credential/revocation gate is balance-orthogonal: passing the gate moves no money, and
failing it commits nothing. -/

/-- The per-asset turn delta of any bounty-board op is `0` (an escrow create/release/refund is COMBINED
per-asset neutral) — for EVERY asset `b`. The conservation hypothesis, discharged per op. -/
theorem postNode_delta_zero (cred : Authorization Dg Pf) (id : Nat) (poster claimant : CellId)
    (asset : AssetId) (reward : Int) (b : AssetId) :
    turnLedgerDeltaAsset
      ((lowerForestG (postNode cred id poster claimant asset reward)).map Prod.snd) b = 0 := by
  simp [postNode, bbNode, lowerForestG, lowerChildrenG, turnLedgerDeltaAsset, ledgerDeltaAsset]

theorem claimNode_delta_zero (cred : Authorization Dg Pf) (id : Nat) (actor : CellId) (b : AssetId) :
    turnLedgerDeltaAsset ((lowerForestG (claimNode cred id actor)).map Prod.snd) b = 0 := by
  simp [claimNode, bbNode, lowerForestG, lowerChildrenG, turnLedgerDeltaAsset, ledgerDeltaAsset]

theorem cancelNode_delta_zero (cred : Authorization Dg Pf) (id : Nat) (actor : CellId) (b : AssetId) :
    turnLedgerDeltaAsset ((lowerForestG (cancelNode cred id actor)).map Prod.snd) b = 0 := by
  simp [cancelNode, bbNode, lowerForestG, lowerChildrenG, turnLedgerDeltaAsset, ledgerDeltaAsset]

/-- **`bb_post_conserves` — PROVED (END-USER THEOREM 3).** A COMMITTED post preserves EVERY asset's
combined supply `recTotalAssetWithEscrow b`: the reward leaves the poster's BAL ledger but is CONSERVED
into the off-ledger holding store — parked, never minted or burned. A one-liner off
`execFullForestG_conserves_per_asset` with the escrow-is-combined-neutral hypothesis discharged. -/
theorem bb_post_conserves (s s' : RecChainedState) (cred : Authorization Dg Pf) (id : Nat)
    (poster claimant : CellId) (asset : AssetId) (reward : Int) (b : AssetId)
    (h : execFullForestG s (postNode cred id poster claimant asset reward) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestG_conserves_per_asset s s' (postNode cred id poster claimant asset reward) b h
    (postNode_delta_zero cred id poster claimant asset reward b)

/-- **`bb_claim_conserves` — PROVED (END-USER THEOREM 4).** A COMMITTED claim preserves EVERY asset's
combined supply: the reward moves OUT of the holding store back onto the claimant's BAL ledger — the
combined total fixed. The reward is DELIVERED, not conjured. -/
theorem bb_claim_conserves (s s' : RecChainedState) (cred : Authorization Dg Pf) (id : Nat)
    (actor : CellId) (b : AssetId)
    (h : execFullForestG s (claimNode cred id actor) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestG_conserves_per_asset s s' (claimNode cred id actor) b h
    (claimNode_delta_zero cred id actor b)

/-- **`bb_cancel_conserves` — PROVED (END-USER THEOREM 5).** A COMMITTED cancel preserves EVERY asset's
combined supply: the reward is refunded from the holding store back to the poster — combined total fixed. -/
theorem bb_cancel_conserves (s s' : RecChainedState) (cred : Authorization Dg Pf) (id : Nat)
    (actor : CellId) (b : AssetId)
    (h : execFullForestG s (cancelNode cred id actor) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestG_conserves_per_asset s s' (cancelNode cred id actor) b h
    (cancelNode_delta_zero cred id actor b)

/-! ## §7 — END-USER THEOREMS 6–7: the D3 LIVENESS TEETH (claiming/cancelling into a DEAD cell ⇒ none).

The escrow settle-target gate (`META-FILL C`, hardened into `releaseEscrowKAsset`/`refundEscrowKAsset`):
a release/refund whose target cell is NOT lifecycle-live (Sealed/Destroyed) FAILS CLOSED — crediting a
frozen cell would silently DESTROY value (it vanishes from `recTotalAsset`, breaking conservation). So
claiming to a dead claimant, or cancelling to a dead poster, rejects the whole gated turn. These reuse
the kernel teeth `releaseEscrowKAsset_nonlive_fails`/`refundEscrowKAsset_nonlive_fails` directly. -/

/-- The gate-passing collapse for `goodCred`: when the genuine credential admits, a bounty-board op IS
its underlying `execFullA action`. The hinge for the liveness teeth (a kernel-level rejection of the
action then rejects the whole turn). -/
theorem bb_good_node_runs (s : RecChainedState) (a : FullActionA)
    (hgate : gateOK (mkAuth goodCred []) s = true) :
    execFullForestG s (bbNode goodCred a) = execFullA s a := by
  rw [execFullForestG_bbNode, if_pos hgate]

/-- **`bb_claim_requires_live_claimant` — PROVED (END-USER THEOREM 6, the D3 liveness teeth).** A claim
whose found escrow record's RECIPIENT (the claimant) is NOT lifecycle-live (`cellLifecycleLive = false`:
Sealed/Destroyed) is REJECTED by the gated turn (`none`) — EVEN with a genuine credential. The reward
cannot be delivered into a frozen cell (which would silently destroy it). Reuses the kernel teeth
`releaseEscrowKAsset_nonlive_fails`; the kernel rejection lifts through `releaseEscrowChainA` to
`execFullA`, then through the gate (which passed) to the whole forest. -/
theorem bb_claim_requires_live_claimant (s : RecChainedState) (id : Nat) (actor : CellId)
    {r : EscrowRecord}
    (hgate : gateOK (mkAuth goodCred []) s = true)
    (hfind : s.kernel.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = some r)
    (hdead : cellLifecycleLive s.kernel r.recipient = false) :
    execFullForestG s (claimNode goodCred id actor) = none := by
  rw [claimNode, bb_good_node_runs s (.releaseEscrowA id actor) hgate]
  show releaseEscrowChainA s id actor = none
  unfold releaseEscrowChainA
  by_cases hauth : releaseSettleAuthB s.kernel id actor
  · rw [if_pos hauth]
    rw [releaseEscrowKAsset_nonlive_fails hfind hdead]
  · rw [if_neg hauth]

/-- **`bb_cancel_requires_live_poster` — PROVED (END-USER THEOREM 7, the symmetric refund teeth).** A
cancel whose found escrow record's CREATOR (the poster/refund target) is NOT lifecycle-live is REJECTED
by the gated turn (`none`) — the reward cannot be refunded into a frozen poster cell. Reuses
`refundEscrowKAsset_nonlive_fails`. -/
theorem bb_cancel_requires_live_poster (s : RecChainedState) (id : Nat) (actor : CellId)
    {r : EscrowRecord}
    (hgate : gateOK (mkAuth goodCred []) s = true)
    (hfind : s.kernel.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = some r)
    (hdead : cellLifecycleLive s.kernel r.creator = false) :
    execFullForestG s (cancelNode goodCred id actor) = none := by
  rw [cancelNode, bb_good_node_runs s (.refundEscrowA id actor) hgate]
  show refundEscrowChainA s id actor = none
  unfold refundEscrowChainA
  by_cases hauth : refundSettleAuthB s.kernel id actor
  · rw [if_pos hauth]
    rw [refundEscrowKAsset_nonlive_fails hfind hdead]
  · rw [if_neg hauth]

/-! ## §8 — NON-VACUITY: a concrete FUNDED bounty board + `#guard` witnesses.

`board0` is a two-cell world: the POSTER is cell `0` (holds 100 of asset 0 + 7 of asset 1), the
CLAIMANT is cell `1` (holds 5 of asset 0). Both are live accounts (default lifecycle `0`); the escrow
store starts empty; the revocation registry is empty. Actor `0 == src 0` so the post self-authorizes,
and the credential gate is the load-bearing admission condition. On `board0` we exhibit: a GOOD post
COMMITS & parks the reward (poster's bal drops, combined measure fixed); a FORGED post ⇒ `none`; a
REVOKED post ⇒ `none`; a claim CREDITS the claimant; a cancel REFUNDS the poster; a claim to a SEALED
claimant ⇒ `none`. So every theorem above is witnessed REAL. -/

/-- The funded bounty board: poster `0` holds 100 of asset 0 (and 7 of asset 1), claimant `1` holds 5
of asset 0. Both live; empty escrow store; empty revocation registry. -/
def board0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0 }
    log := [] }

/-- The id of the demo bounty (the escrow key). -/
abbrev bountyId : Nat := 7
/-- The reward: 40 of asset 0. -/
abbrev rewardAmt : Int := 40

/-- The board AFTER a good post (the reward is parked: poster `0`'s asset-0 bal dropped to 60, an
unresolved record `id=7, creator=0, recipient=1, amount=40, asset=0` sits in the store). Used to
witness the claim/cancel settle steps off an actually-parked state. -/
def boardPosted : Option RecChainedState :=
  execFullForestG board0 (postNode goodCred bountyId 0 1 0 rewardAmt)

/-- A board whose CLAIMANT (cell 1) is SEALED (lifecycle `1`), but with the reward already parked for
it — the D3 liveness teeth fixture: a claim here must FAIL (cannot credit a frozen cell). -/
def boardSealedClaimant : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 0 then (if a = 0 then 60 else if a = 1 then 7 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0
        escrows := [{ id := bountyId, creator := 0, recipient := 1, amount := rewardAmt,
                      resolved := false, asset := 0 }]
        lifecycle := fun c => if c = 1 then 1 else 0 }    -- claimant SEALED
    log := [] }

-- The gate passes for the genuine credential on these states (the credential leg is the only live leg):
#guard (gateOK (mkAuth goodCred []) board0)                       --  true  (genuine credential admits)
#guard (gateOK (mkAuth forgedCred []) board0) == false           --  false (forged ⇒ fail-closed)

-- (i) a GOOD post COMMITS & parks the reward:
#guard ((execFullForestG board0 (postNode goodCred bountyId 0 1 0 rewardAmt)).isSome)              --  true (posted!)
-- ...the poster's asset-0 BAL dropped by the reward (100 → 60) — value genuinely LEFT the ledger:
#guard ((execFullForestG board0 (postNode goodCred bountyId 0 1 0 rewardAmt)).map
        (fun s => s.kernel.bal 0 0)) == some 60                                                    --  some 60
-- ...the holding store now holds the parked reward (one unresolved record of amount 40):
#guard ((execFullForestG board0 (postNode goodCred bountyId 0 1 0 rewardAmt)).map
        (fun s => s.kernel.escrows.length)) == some 1                                              --  some 1 (parked)
-- ...but the COMBINED per-asset measure is UNCHANGED (parked, not destroyed) — CONSERVATION witnessed:
#guard ((execFullForestG board0 (postNode goodCred bountyId 0 1 0 rewardAmt)).map
        (fun s => (recTotalAssetWithEscrow s.kernel 0, recTotalAssetWithEscrow s.kernel 1)))
        == some (105, 7)                                                                           --  some (105, 7) (FIXED)

-- (ii) a FORGED post ⇒ none (credential gate fail-closes), on any state:
#guard ((execFullForestG board0 (postNode forgedCred bountyId 0 1 0 rewardAmt)).isSome) == false  --  false

-- (iii) a REVOKED post ⇒ none: a board whose revocation registry holds nullifier 5, posting with that
--       nullifier is rejected even though the signature is genuine:
#guard ((execFullForestG
          { board0 with kernel := { board0.kernel with revoked := [5] } }
          (bbNodeNul goodCred 5 (.createEscrowA bountyId 0 0 1 0 rewardAmt))).isSome) == false     --  false (revoked)
-- ...and the SAME post with a non-revoked nullifier (0) on the SAME board COMMITS (revocation is the
--    sole reason for the rejection above, not a vacuous fail):
#guard ((execFullForestG
          { board0 with kernel := { board0.kernel with revoked := [5] } }
          (bbNodeNul goodCred 0 (.createEscrowA bountyId 0 0 1 0 rewardAmt))).isSome)              --  true (not revoked)

-- (iv) a CLAIM credits the claimant: post then claim — claimant `1`'s asset-0 bal rises 5 → 45:
#guard ((boardPosted.bind (fun s => execFullForestG s (claimNode goodCred bountyId 1))).map
        (fun s => s.kernel.bal 1 0)) == some 45                                                    --  some 45 (delivered!)
-- ...and the claim CONSERVES every asset (value came from the store, nothing minted):
#guard ((boardPosted.bind (fun s => execFullForestG s (claimNode goodCred bountyId 1))).map
        (fun s => (recTotalAssetWithEscrow s.kernel 0, recTotalAssetWithEscrow s.kernel 1)))
        == some (105, 7)                                                                           --  some (105, 7)
-- ...the record is now resolved (the store no longer holds an UNRESOLVED record for the bounty):
#guard ((boardPosted.bind (fun s => execFullForestG s (claimNode goodCred bountyId 1))).map
        (fun s => s.kernel.escrows.filter (fun r => !r.resolved) |>.length)) == some 0             --  some 0 (settled)

-- (v) a CANCEL refunds the poster: post then cancel — poster `0`'s asset-0 bal returns 60 → 100:
#guard ((boardPosted.bind (fun s => execFullForestG s (cancelNode goodCred bountyId 0))).map
        (fun s => s.kernel.bal 0 0)) == some 100                                                   --  some 100 (refunded!)
#guard ((boardPosted.bind (fun s => execFullForestG s (cancelNode goodCred bountyId 0))).map
        (fun s => (recTotalAssetWithEscrow s.kernel 0, recTotalAssetWithEscrow s.kernel 1)))
        == some (105, 7)                                                                           --  some (105, 7) (conserved)

-- (vi) LIVENESS TEETH: claiming to a SEALED claimant ⇒ none (the reward cannot land in a frozen cell):
#guard (cellLifecycleLive boardSealedClaimant.kernel 1) == false                                   --  false (claimant Sealed)
#guard ((execFullForestG boardSealedClaimant (claimNode goodCred bountyId 1)).isSome) == false     --  false (claim rejected)
-- ...and the SAME claim against the LIVE-claimant posted board COMMITS (sealing is the sole blocker):
#guard ((boardPosted.bind (fun s => execFullForestG s (claimNode goodCred bountyId 1))).isSome)    --  true (live ⇒ delivered)

/-! ## §9 — Hatchery bridge: production crowns on `trajG` (app semantics, not just per-op teeth). -/

/-- Per-baseline reward conservation contract (the bounty board's `conservation% rewardAsset` shape). -/
noncomputable def bbRewardConserved (s0 : RecChainedState) : Contract :=
  assetConserved s0 rewardAsset

/-- **`bb_asset_conserved_forever` — APP SEMANTICS (production crown).** From any baseline `s0`, along
EVERY adversarial production schedule, the reward asset's combined supply never drifts — the value-
moving bounty board inherits the Hatchery `conservation%` shape on `trajG`. -/
theorem bb_asset_conserved_forever (s0 : RecChainedState) (sched : SchedG) :
    ∀ n, cellObsA (trajG s0 sched n) rewardAsset = cellObsA s0 rewardAsset :=
  asset_conserved_forever_production s0 rewardAsset sched

/-- **`bb_board0_asset0_conserved_forever` — canonical funded-board witness (asset 0 baseline).** -/
theorem bb_board0_asset0_conserved_forever (sched : SchedG) :
    ∀ n, cellObsA (trajG board0 sched n) 0 = cellObsA board0 0 :=
  bb_asset_conserved_forever board0 sched

/-- **`bb_board0_asset1_conserved_forever` — canonical funded-board witness (asset 1 baseline).** -/
theorem bb_board0_asset1_conserved_forever (sched : SchedG) :
    ∀ n, cellObsA (trajG board0 sched n) 1 = cellObsA board0 1 :=
  fun n => asset_conserved_forever_production board0 1 sched n

/-- **`bb_revoked_rejected_forever` — APP SEMANTICS (revocation crown).** If nullifier `nul` is in the
committed revocation registry initially, EVERY bounty op with that credential is rejected at EVERY
index of EVERY production schedule — composed from `gateRevoked` persistence + `bb_revoked_rejected`. -/
theorem bb_revoked_rejected_forever (s : RecChainedState) (cred : Authorization Dg Pf) (nul : Nat)
    (a : FullActionA) (hinit : nul ∈ s.kernel.revoked) (sched : SchedG) :
    ∀ n, execFullForestG (trajG s sched n) (bbNodeNul cred nul a) = none := by
  intro n
  exact bb_revoked_rejected (trajG s sched n) cred nul a
    (List.contains_iff_mem.mpr ((gateRevoked nul).forever hinit sched n))

/-- **Composed bounty safety: reward conservation ∩ revocation-registry persistence.** -/
noncomputable def bbSafetyContract (s0 : RecChainedState) (nul : Nat) : Contract :=
  composeContracts (bbRewardConserved s0) (gateRevoked nul)

/-- **`bb_safety_forever` — COMPOSED PRODUCTION CROWN.** Reward supply fixed AND revoked nullifier
stays in the committed registry, at every `trajG` index — conservation + identity revocation shape. -/
theorem bb_safety_forever (s0 : RecChainedState) (nul : Nat) (s : RecChainedState)
    (hpay : cellObsA s rewardAsset = cellObsA s0 rewardAsset) (hrev : nul ∈ s.kernel.revoked)
    (sched : SchedG) :
    ∀ n, cellObsA (trajG s sched n) rewardAsset = cellObsA s0 rewardAsset ∧
         nul ∈ (trajG s sched n).kernel.revoked :=
  (bbSafetyContract s0 nul).forever (And.intro hpay hrev) sched

/-! ## §10 — Axiom-hygiene tripwires (the honesty pins). Every keystone depends ONLY on the three
standard kernel axioms `{propext, Classical.choice, Quot.sound}` — no `sorryAx`. (The portal soundness
is a Prop carrier in `FullForestAuth`, never an axiom, so it does not appear.) -/

#assert_axioms execFullForestG_leaf
#assert_axioms execFullForestG_bbNode
#assert_axioms gateOK_forged_false
#assert_axioms bb_forged_rejected
#assert_axioms bb_revoked_rejected
#assert_axioms bb_post_conserves
#assert_axioms bb_claim_conserves
#assert_axioms bb_cancel_conserves
#assert_axioms bb_claim_requires_live_claimant
#assert_axioms bb_cancel_requires_live_poster
#assert_axioms bbRewardConserved
#assert_axioms bb_asset_conserved_forever
#assert_axioms bb_board0_asset0_conserved_forever
#assert_axioms bb_board0_asset1_conserved_forever
#assert_axioms bb_revoked_rejected_forever
#assert_axioms bbSafetyContract
#assert_axioms bb_safety_forever

end Dregg2.Apps.BountyBoardGated
