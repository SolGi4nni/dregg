/-
# Dregg2.Apps.CrossChainBridgeGated — a CROSS-CHAIN BRIDGE on the ONE GATED executor.

A `starbridge`-shaped cross-chain bridge (the dregg1 bridge pattern: a user LOCKS value on the home
chain to mint a wrapped representation on a destination chain; the lock is FINALIZED when the foreign
confirmation arrives — the value genuinely LEAVES for the other chain — or CANCELLED on timeout — the
value RETURNS to the originator), modelled as REAL bridge moves on the production turn entry —
`Dregg2.Exec.FullForestAuth.execFullForestG` (the `dregg_exec_full_forest_auth` 4-leg gate: credential ∧
cap-authority ∧ caveats-discharged ∧ not-revoked).

This app exercises the **`bridgeLockA` / `bridgeFinalizeA` / `bridgeCancelA`** effects, which were not
yet covered by any verified gated app. Unlike a balance-NEUTRAL nameservice or a combined-NEUTRAL
escrow market, the bridge has a genuinely **DISCLOSED OUTFLOW** at finalize: the combined per-asset
measure DROPS by exactly the bridged amount at exactly the bridged asset (a burn-at-the-boundary), every
other asset literally fixed — so the headline guarantees are (a) lock COMBINED-conservation, (b) finalize
DISCLOSED-OUTFLOW (`recTotalAssetWithEscrow` down by `amount` at `asset`, no cross-asset laundering),
(c) cancel ROUND-TRIP conservation, and (d) the bridge-AUTHORITY tooth — only the recorded originator
may finalize/cancel, closing the "anyone-can-finalize-any-victim's-lock-by-id" hole.

## The three bridge ops (each a SINGLE credential-gated leaf node through `execFullForestG`)

  * **lock**     — `bridgeLockA jobId user user dest payAsset amount`: debit the user's ledger at
    `payAsset` and park a BRIDGE-tagged record keyed to the destination. COMBINED-NEUTRAL.
  * **finalize** — `bridgeFinalizeA jobId user payAsset amount`: the foreign confirmation arrived; mark
    the lock resolved WITHOUT a home-chain credit — the value LEFT for the destination. COMBINED DROPS
    by `amount` at `payAsset`. AUTHORITY: only the recorded creator (= the originator) may finalize.
  * **cancel**   — `bridgeCancelA jobId user`: timeout/failure; credit the originator back at the
    record's asset, mark resolved. COMBINED-NEUTRAL. AUTHORITY: only the recorded creator may cancel.

## The gated-executor keystones this app COMPOSES (it adds NO kernel theory)

  * `execFullForestG_leaf` — a childless gated forest runs EXACTLY its single gated node;
  * `execFullForestG_unauthorized_fails` — a false gate leg ⇒ whole-forest `none`;
  * `gateOK_forged_false` (local) — a forged credential's portal leg is `false`;
  * `gateOK_revoked_fails` — a revoked credential's nullifier in `s.kernel.revoked` ⇒ `none`;
  * `bridgeLockChainA_combined_neutral` / `bridgeFinalizeChainA_burns_combined` /
    `bridgeCancelChainA_combined_neutral` — the bridge ledger laws;
  * `bridgeFinalizeChainA_nonCreator_rejects` — the bridge-authority tooth.

## End-user theorems

  1. `br_forged_rejected`            — a FORGED credential ⇒ the whole gated op rejects (`none`), ∀s, ∀op;
  2. `br_revoked_rejected`           — a REVOKED credential ⇒ `none`, ∀s;
  3. `br_lock_conserves`             — a committed LOCK preserves EVERY asset's combined supply;
  4. `br_finalize_discloses_outflow` — a committed FINALIZE drops the combined measure by EXACTLY the
     bridged `amount` at the bridged `asset`, every other asset LITERALLY fixed (a disclosed burn);
  5. `br_cancel_conserves`           — a committed CANCEL preserves EVERY asset's combined supply;
  6. `br_finalize_requires_creator`  — AUTHORITY: only the recorded originator may finalize; a stranger
     who merely knows the `id` is fail-closed REJECTED (no stealing a victim's lock).

Plus a concrete funded bridge state (`br0`) whose `#guard`s witness the whole lifecycle non-vacuously:
a funded LOCK commits and parks, a FINALIZE burns the bridged value (combined drops), a CANCEL returns
it, a forged credential ⇒ `none`, a revoked credential ⇒ `none`, a STRANGER-finalize ⇒ `none`.

NEW file only — does NOT touch any existing app,
`FullForestAuth.lean`, `TurnExecutorFull.lean`, nor `Dregg2.lean`. Reuses ONLY the proved gated-executor
keystones + the proved bridge ledger/authority teeth.
-/
import Dregg2.Exec.GatedForestCfg

namespace Dregg2.Apps.CrossChainBridgeGated

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Exec.EffectsState
open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.StarbridgeGated

/-! ## §1 — The cross-chain bridge DOMAIN at the Demo carriers (the user, the destination, the asset). -/

/-- The bridging USER cell (locks the value; the recorded `creator`/originator — the only party allowed
to finalize/cancel). Cell `0`, so the bridge authority gate `authorizedB { actor := 0, src := 0, .. }`
holds via its reflexive `actor == src` arm — the §8 CREDENTIAL gate is the load-bearing admission
condition, not the cap-list. -/
abbrev user : CellId := 0

/-- The DESTINATION cell (the foreign-chain endpoint the value bridges to). Cell `1`. -/
abbrev dest : CellId := 1

/-- The bridged asset class (the currency being bridged). Asset `0`. -/
abbrev payAsset : AssetId := 0

/-- The bridge id keying this transfer's lock record (dregg1's `[u8;32]` bridge_id, modelled `Nat`). -/
abbrev jobId : Nat := 42

/-! ## §2 — Each bridge op as a GATED LEAF NODE through the production turn entry `execFullForestG`. -/

/-- A gated bridge node: credential `cred`, a bridge `action`, no children. The production turn-entry
shape `⟨ mkAuth cred [], action, [] ⟩`. -/
def brNode (cred : Authorization Dg Pf) (action : FullActionA) : DForest :=
  ⟨ mkAuth cred [], action, [] ⟩

/-- **lock** — the USER LOCKS the bridged value. `bridgeLockA jobId user user dest payAsset amount`:
debit the user's ledger at `payAsset` and park a BRIDGE-tagged record keyed to `dest`. -/
def lockNode (cred : Authorization Dg Pf) (amount : Int) : DForest :=
  brNode cred (.bridgeLockA jobId user user dest payAsset amount)

/-- **finalize** — the foreign confirmation arrived. `bridgeFinalizeA jobId user payAsset amount`: mark
the lock resolved WITHOUT a home-chain credit (the value LEFT for the destination). AUTHORITY: only the
recorded creator (= the originator) may finalize. -/
def finalizeNode (cred : Authorization Dg Pf) (amount : Int) : DForest :=
  brNode cred (.bridgeFinalizeA jobId user payAsset amount)

/-- **cancel** — timeout/failure. `bridgeCancelA jobId user`: credit the originator back, mark resolved.
AUTHORITY: only the recorded creator may cancel. -/
def cancelNode (cred : Authorization Dg Pf) : DForest :=
  brNode cred (.bridgeCancelA jobId user)

/-! ## §3 — The leaf-collapse bridge: a childless gated forest runs EXACTLY its single gated node. -/

/-- **`execFullForestG_leaf` — PROVED.** A gated forest with NO children runs EXACTLY its root gated node
step. -/
theorem execFullForestG_leaf (s : RecChainedState) (na : DNodeAuth) (a : FullActionA) :
    execFullForestG s (⟨na, a, []⟩ : DForest) = execFullAGated s na a := by
  show (match execFullAGated s na a with
        | some s' => execFullChildrenG (targetOf a) s' ([] : List DChild)
        | none    => none) = execFullAGated s na a
  cases execFullAGated s na a with
  | none   => rfl
  | some _ => rfl

/-- **`execFullForestG_brNode` — the bridge-op collapse.** A bridge op runs `if gateOK then execFullA
action else none`. -/
theorem execFullForestG_brNode (s : RecChainedState) (cred : Authorization Dg Pf) (action : FullActionA) :
    execFullForestG s (brNode cred action)
      = (if gateOK (mkAuth cred []) s = true then execFullA s action else none) := by
  rw [brNode, execFullForestG_leaf, execFullAGated]

/-! ## §4 — The CREDENTIAL gate: `goodCred` admits, `forgedCred` fail-closed (state-independent). -/

/-- **`gateOK_forged_false` — the forged-credential gate leg is FALSE.** -/
theorem gateOK_forged_false (s : RecChainedState) : gateOK (mkAuth forgedCred []) s = false := by
  have hcred : credentialValidG (mkAuth forgedCred []) = false := by decide
  unfold gateOK
  rw [hcred]
  simp

/-! ## §5 — END-USER THEOREM 1: a FORGED credential ⇒ the whole gated op REJECTS. -/

/-- **`br_forged_rejected` — PROVED (END-USER THEOREM 1).** A bridge op (ANY bridge action) presented
with a FORGED credential is rejected by the production turn entry, for EVERY pre-state `s`. -/
theorem br_forged_rejected (s : RecChainedState) (action : FullActionA) :
    execFullForestG s (brNode forgedCred action) = none := by
  rw [brNode]
  exact execFullForestG_unauthorized_fails s (mkAuth forgedCred []) action [] (gateOK_forged_false s)

theorem br_forged_lock_rejected (s : RecChainedState) (amount : Int) :
    execFullForestG s (lockNode forgedCred amount) = none :=
  br_forged_rejected s _
theorem br_forged_finalize_rejected (s : RecChainedState) (amount : Int) :
    execFullForestG s (finalizeNode forgedCred amount) = none :=
  br_forged_rejected s _
theorem br_forged_cancel_rejected (s : RecChainedState) :
    execFullForestG s (cancelNode forgedCred) = none :=
  br_forged_rejected s _

/-! ## §6 — END-USER THEOREM 2: a REVOKED credential ⇒ the whole gated op REJECTS. -/

/-- A NodeAuth identical to `mkAuth cred []` but carrying an explicit revocation nullifier `nul`. -/
def mkAuthRevoked (cred : Authorization Dg Pf) (nul : Nat) : DNodeAuth :=
  { mkAuth cred [] with credNul := nul }

/-- A bridge op whose credential carries the revocation nullifier `nul`. -/
def brNodeRevoked (cred : Authorization Dg Pf) (nul : Nat) (action : FullActionA) : DForest :=
  ⟨ mkAuthRevoked cred nul, action, [] ⟩

/-- **`br_revoked_rejected` — PROVED (END-USER THEOREM 2).** A bridge op whose credential nullifier `nul`
sits in the COMMITTED revocation registry `s.kernel.revoked` is rejected, for EVERY pre-state and EVERY
(even genuine) credential. A revoked key cannot lock/finalize/cancel, no matter how valid its signature. -/
theorem br_revoked_rejected (s : RecChainedState) (cred : Authorization Dg Pf) (nul : Nat)
    (action : FullActionA) (hrev : s.kernel.revoked.contains nul = true) :
    execFullForestG s (brNodeRevoked cred nul action) = none := by
  rw [brNodeRevoked]
  refine execFullForestG_unauthorized_fails s (mkAuthRevoked cred nul) action [] ?_
  exact gateOK_revoked_fails (mkAuthRevoked cred nul) s hrev

/-! ## §7 — END-USER THEOREMS 3–5: LOCK conserves, FINALIZE discloses outflow, CANCEL conserves.

These compose the gate-passing collapse with the proved bridge ledger laws. When the gate passes,
`execFullForestG s (lockNode goodCred amount) = bridgeLockChainA s jobId user user dest payAsset amount`
(`execFullA` dispatches `.bridgeLockA` to `bridgeLockChainA`), and similarly for finalize/cancel; then
the bridge ledger keystone applies. -/

/-- **`lock_runs_bridge` — the gate-passing collapse for a LOCK.** -/
theorem lock_runs_bridge (s : RecChainedState) (amount : Int) (hgate : gateOK (mkAuth goodCred []) s = true) :
    execFullForestG s (lockNode goodCred amount)
      = bridgeLockChainA s jobId user user dest payAsset amount := by
  rw [lockNode, execFullForestG_brNode, if_pos hgate]; rfl

/-- **`finalize_runs_bridge` — the gate-passing collapse for a FINALIZE.** -/
theorem finalize_runs_bridge (s : RecChainedState) (amount : Int)
    (hgate : gateOK (mkAuth goodCred []) s = true) :
    execFullForestG s (finalizeNode goodCred amount)
      = bridgeFinalizeChainA s jobId user payAsset amount := by
  rw [finalizeNode, execFullForestG_brNode, if_pos hgate]; rfl

/-- **`cancel_runs_bridge` — the gate-passing collapse for a CANCEL.** -/
theorem cancel_runs_bridge (s : RecChainedState) (hgate : gateOK (mkAuth goodCred []) s = true) :
    execFullForestG s (cancelNode goodCred)
      = bridgeCancelChainA s jobId user := by
  rw [cancelNode, execFullForestG_brNode, if_pos hgate]; rfl

/-- **`br_lock_conserves` — PROVED (END-USER THEOREM 3).** A COMMITTED bridge lock preserves EVERY
asset's COMBINED total supply: the bal-debit at `payAsset` is exactly offset by the holding-store rise,
so the lock moves no net money — the value is INACCESSIBLE in the lock, not minted/burned. -/
theorem br_lock_conserves (s s' : RecChainedState) (amount : Int) (b : AssetId)
    (hgate : gateOK (mkAuth goodCred []) s = true)
    (h : execFullForestG s (lockNode goodCred amount) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  rw [lock_runs_bridge s amount hgate] at h
  exact bridgeLockChainA_combined_neutral b h

/-- **`br_finalize_discloses_outflow` — PROVED (END-USER THEOREM 4, THE BRIDGE HEADLINE).** A COMMITTED
bridge finalize moves the COMBINED per-asset measure DOWN by EXACTLY the disclosed `amount` at the
disclosed `payAsset` (`b = payAsset`), leaving every OTHER asset LITERALLY fixed — the value genuinely
LEFT for the destination chain. NON-VACUOUS: the drop is a per-asset DISCLOSED OUTFLOW guarded by
`b = payAsset` (no cross-asset laundering at the bridge boundary). -/
theorem br_finalize_discloses_outflow (s s' : RecChainedState) (amount : Int) (b : AssetId)
    (hgate : gateOK (mkAuth goodCred []) s = true)
    (h : execFullForestG s (finalizeNode goodCred amount) = some s') :
    recTotalAssetWithEscrow s'.kernel b
      = recTotalAssetWithEscrow s.kernel b - (if b = payAsset then amount else 0) := by
  rw [finalize_runs_bridge s amount hgate] at h
  exact bridgeFinalizeChainA_burns_combined b h

/-- **`br_cancel_conserves` — PROVED (END-USER THEOREM 5).** A COMMITTED bridge cancel preserves EVERY
asset's combined supply (the value returns from the lock to the live, gate-checked originator). -/
theorem br_cancel_conserves (s s' : RecChainedState) (b : AssetId)
    (hgate : gateOK (mkAuth goodCred []) s = true)
    (h : execFullForestG s (cancelNode goodCred) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b := by
  rw [cancel_runs_bridge s hgate] at h
  exact bridgeCancelChainA_combined_neutral b h

/-! ## §8 — END-USER THEOREM 6: the BRIDGE-AUTHORITY tooth — only the recorded originator may finalize. -/

/-- **`br_finalize_requires_creator` — PROVED (END-USER THEOREM 6, AUTHORITY).** Finalizing a lock whose
parked record was created by someone OTHER than the caller (`r.creator ≠ actor` — read off the COMMITTED
`s.kernel.escrows` side-table, adversary-UNCONTROLLABLE) is rejected by the executor: `execFullForestG s
(finalizeNode goodCred amount) = none` — EVEN with a genuine, non-revoked credential. A stranger who
merely knows the bridge `id` cannot steal a victim's locked value. NON-VACUOUS: the rejection is keyed on
adversary-uncontrollable state (`hne`). -/
theorem br_finalize_requires_creator (s : RecChainedState) (amount : Int) (r : EscrowRecord)
    (hgate : gateOK (mkAuth goodCred []) s = true)
    (hfind : s.kernel.escrows.find? (fun r => decide (r.id = jobId ∧ r.resolved = false)) = some r)
    (hne : (r.creator == user) = false) :
    execFullForestG s (finalizeNode goodCred amount) = none := by
  rw [finalize_runs_bridge s amount hgate]
  exact bridgeFinalizeChainA_nonCreator_rejects hfind hne

/-! ## §9 — NON-VACUITY: a concrete FUNDED bridge + `#guard` witnesses (the gate + bridge are REAL).

`br0` is a funded bridge: the user (cell 0) holds 100 of `payAsset`, cell 1 (dest) is a LIVE account
holding 0, no locks parked yet, empty revocation registry, default Live lifecycle. We exhibit the whole
lifecycle: a funded LOCK commits (debits the user, parks the bridge record), a FINALIZE burns the bridged
value (the combined measure DROPS by 30), a CANCEL returns it; a forged credential ⇒ `none`; a revoked
credential ⇒ `none`; a stranger-finalize ⇒ `none`. -/

/-- A funded bridge: user (cell 0) holds 100 of `payAsset`, dest (cell 1) is a LIVE account. No locks
parked; empty revocation registry; default Live lifecycle. Actor 0 self-authorizes the lock
(`actor == src`), so the §8 CREDENTIAL gate is the load-bearing leg. -/
def br0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0 }
    log := [] }

/-- The bridge AFTER a funded lock (the value is parked, bridge-tagged) — the canonical post-lock state
on which FINALIZE/CANCEL are exercised. Built directly with the bridge-tagged record (the user is the
recorded creator). -/
def brLocked : RecChainedState :=
  { kernel :=
      { br0.kernel with
        escrows := [{ id := jobId, creator := user, recipient := dest,
                      amount := 30, resolved := false, asset := payAsset, bridge := true }]
        bal := fun c a => if c = 0 ∧ a = 0 then 70 else 0 }  -- 30 parked off the user's ledger
    log := [] }

/-- A bridge with the value locked but the recorded creator is cell 0 — a STRANGER (cell 9, who knows the
id) attempts to finalize. The `bridgeAuthOK` gate keys on the RECORDED creator, so the stranger's
finalize must be rejected. -/
def stranger : CellId := 9

-- The gate passes for the genuine credential, fails for the forged one:
#guard (gateOK (mkAuth goodCred []) br0)              --  true  (genuine credential admits)
#guard (gateOK (mkAuth forgedCred []) br0) == false   --  false (forged ⇒ fail-closed)

-- (i) a FUNDED lock COMMITS (the user locks 30 of the bridged asset):
#guard ((execFullForestG br0 (lockNode goodCred 30)).isSome)                         --  true (locked!)
-- ...the user's bare ledger DROPS by 30 (100 → 70), the holding-store RISES by 30:
#guard ((execFullForestG br0 (lockNode goodCred 30)).map (fun s => s.kernel.bal 0 0)) == some 70  --  some 70
#guard ((execFullForestG br0 (lockNode goodCred 30)).map (fun s => escrowHeldAsset s.kernel 0)) == some 30  --  some 30
-- ...but the COMBINED per-asset measure is UNCHANGED (conserved — value locked, not minted/burned):
#guard ((execFullForestG br0 (lockNode goodCred 30)).map (fun s => recTotalAssetWithEscrow s.kernel 0)) == some 100  --  some 100

-- (ii) a FORGED credential ⇒ none (credential gate fail-closes), even on the funded state:
#guard ((execFullForestG br0 (lockNode forgedCred 30)).isSome) == false              --  false

-- (iii) FINALIZE burns the bridged value (the value LEFT for the destination chain):
#guard ((execFullForestG brLocked (finalizeNode goodCred 30)).isSome)                 --  true (finalized!)
-- ...the COMBINED per-asset measure DROPS by 30 (100 → 70) — the disclosed outflow:
#guard ((execFullForestG brLocked (finalizeNode goodCred 30)).map (fun s => recTotalAssetWithEscrow s.kernel 0)) == some 70  --  some 70 (burned)

-- (iv) AUTHORITY: a STRANGER (cell 9, who knows the id) cannot finalize the user's lock ⇒ none:
#guard (brLocked.kernel.escrows.find? (fun r => decide (r.id = jobId ∧ r.resolved = false))).isSome  --  true (lock present)
#guard ((execFullForestG brLocked
          (brNode goodCred (.bridgeFinalizeA jobId stranger payAsset 30))).isSome) == false  --  false (stranger rejected)

-- (v) CANCEL returns the locked value to the originator (30 back onto cell 0's ledger: 70 → 100):
#guard ((execFullForestG brLocked (cancelNode goodCred)).isSome)                      --  true (cancelled!)
#guard ((execFullForestG brLocked (cancelNode goodCred)).map (fun s => s.kernel.bal 0 0)) == some 100  --  some 100 (returned)
#guard ((execFullForestG brLocked (cancelNode goodCred)).map (fun s => recTotalAssetWithEscrow s.kernel 0)) == some 100  --  some 100 (conserved)

-- (vi) REVOCATION: a revoked credential (nullifier 7 in the committed registry) ⇒ none, even genuine.
/-- A bridge whose revocation registry contains nullifier 7 (a revoked credential serial). -/
def brRevoked : RecChainedState :=
  { kernel := { br0.kernel with revoked := [7] }, log := [] }
#guard (brRevoked.kernel.revoked.contains 7)                                          --  true (7 is revoked)
#guard ((execFullForestG brRevoked (brNodeRevoked goodCred 7 (.bridgeLockA jobId user user dest payAsset 30))).isSome) == false  --  false

-- (vii) END-TO-END: lock then finalize ⇒ the bridged value has LEFT (combined 100 → 70):
#guard (((execFullForestG br0 (lockNode goodCred 30)).bind
          (fun s => execFullForestG s (finalizeNode goodCred 30))).map
        (fun s => recTotalAssetWithEscrow s.kernel 0)) == some 70  --  some 70 (left for the other chain)
-- ...lock then cancel ⇒ the value RETURNED (combined fixed at 100, user made whole):
#guard (((execFullForestG br0 (lockNode goodCred 30)).bind
          (fun s => execFullForestG s (cancelNode goodCred))).map
        (fun s => (recTotalAssetWithEscrow s.kernel 0, s.kernel.bal 0 0))) == some (100, 100)  --  conserved + whole

/-! ## §10 — Axiom-hygiene tripwires (the honesty pins). Every keystone depends ONLY on the three
standard kernel axioms `{propext, Classical.choice, Quot.sound}` — no `sorryAx`. -/

#assert_axioms execFullForestG_leaf
#assert_axioms execFullForestG_brNode
#assert_axioms gateOK_forged_false
#assert_axioms br_forged_rejected
#assert_axioms br_revoked_rejected
#assert_axioms lock_runs_bridge
#assert_axioms finalize_runs_bridge
#assert_axioms cancel_runs_bridge
#assert_axioms br_lock_conserves
#assert_axioms br_finalize_discloses_outflow
#assert_axioms br_cancel_conserves
#assert_axioms br_finalize_requires_creator

end Dregg2.Apps.CrossChainBridgeGated
