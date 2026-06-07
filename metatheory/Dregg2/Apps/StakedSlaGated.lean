/-
# Dregg2.Apps.StakedSlaGated — a STAKED SLA / SERVICE BOND on the ONE GATED executor.

A `starbridge`-shaped staked service-level-agreement (the dregg1 obligation pattern: a provider posts a
STAKE as a performance bond; the stake is RETURNED on fulfilment of the SLA, or SLASHED to the
beneficiary on breach), modelled as REAL obligation moves on the production turn entry —
`Dregg2.Exec.FullForestAuth.execFullForestG` (the `dregg_exec_full_forest_auth` 4-leg gate: credential ∧
cap-authority ∧ caveats-discharged ∧ not-revoked).

This app exercises the **`createObligationA` / `fulfillObligationA` / `slashObligationA`** effects, which
were not yet covered by any verified gated app. The obligation lifecycle reuses dregg1's shared
holding-store automaton: CREATE locks the stake off the obligor's ledger (combined-neutral), FULFIL
returns it to the obligor (the obligation analog of escrow REFUND), SLASH transfers it to the beneficiary
(the obligation analog of escrow RELEASE). So the headline guarantees are per-asset CONSERVATION across
the bond lifecycle plus the D3-liveness guarantee that you cannot SLASH a stake to a DEAD (Sealed)
beneficiary — the value would silently vanish.

## The three SLA ops (each a SINGLE credential-gated leaf node through `execFullForestG`)

  * **post-bond** — the PROVIDER posts the stake. `createObligationA bondId provider provider beneficiary
    stakeAsset stake` parks `stake` of `stakeAsset` off the provider's ledger keyed to the beneficiary as
    eventual slash target. (`obligor := provider` is the fulfil/return target, `beneficiary` the slash
    target.) Per-asset COMBINED-NEUTRAL (the bal-debit is exactly offset by the holding-store rise).
  * **fulfil**    — the SLA was MET. `fulfillObligationA bondId provider` returns the staked value to the
    obligor (= the record's `creator`/provider), marks resolved. Per-asset COMBINED-NEUTRAL.
  * **slash**     — the SLA was BREACHED. `slashObligationA bondId actor` transfers the stake to the
    beneficiary (= the record's `recipient`), marks resolved. Per-asset COMBINED-NEUTRAL. The D3
    SLASH-LIVENESS GATE fires here: the beneficiary MUST be a LIVE account — slashing to a Sealed
    beneficiary fail-closes (`none`).

## The gated-executor keystones this app COMPOSES (it adds NO kernel theory)

  * `execFullForestG_leaf` — a childless gated forest runs EXACTLY its single gated node;
  * `execFullForestG_unauthorized_fails` — a false gate leg ⇒ whole-forest `none`;
  * `gateOK_forged_false` (local) — a forged credential's portal leg is `false`;
  * `gateOK_revoked_fails` — a revoked credential's nullifier in `s.kernel.revoked` ⇒ `none`;
  * `execFullForestG_conserves_per_asset` — a per-asset-Δ-zero forest preserves every asset's combined
    supply; the obligation effects all have `ledgerDeltaAsset = 0`, so each op is combined-neutral.

## End-user theorems

  1. `sla_forged_rejected`              — a FORGED credential ⇒ the whole gated op rejects (`none`), ∀s, ∀op;
  2. `sla_revoked_rejected`            — a REVOKED credential ⇒ `none`, ∀s;
  3. `sla_post_conserves`              — a committed POST preserves EVERY asset's combined supply (stake locked, not minted/burned);
  4. `sla_fulfil_conserves`           — a committed FULFIL preserves EVERY asset's combined supply (stake returned, combined-neutral);
  5. `sla_slash_conserves`            — a committed SLASH preserves EVERY asset's combined supply (stake transferred, combined-neutral);
  6. `sla_slash_requires_live_beneficiary` — D3 LIVENESS: slashing a stake to a SEALED beneficiary ⇒ `none` (no slashing into a dead cell).

Plus a concrete bonded SLA state (`bond0`) whose `#guard`s witness the lifecycle non-vacuously: a funded
POST commits and parks, a FULFIL returns the stake, a SLASH pays the live beneficiary, a forged credential
⇒ `none`, a revoked credential ⇒ `none`, slashing to a SEALED beneficiary ⇒ `none`, and the lifecycle
CONSERVES.

Zero `sorry`/`admit`/`native_decide`/`axiom`. NEW file only — does NOT touch any existing app,
`FullForestAuth.lean`, `TurnExecutorFull.lean`, nor `Dregg2.lean`. Reuses ONLY the proved gated-executor
keystones + the proved obligation/escrow combined-conservation/liveness teeth.
-/
import Dregg2.Exec.GatedForestCfg

namespace Dregg2.Apps.StakedSlaGated

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Exec.EffectsState
open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.StarbridgeGated

/-! ## §1 — The staked-SLA DOMAIN at the Demo carriers (provider, beneficiary, the staked asset). -/

/-- The PROVIDER cell (posts the performance bond; the recorded `creator`/obligor — the fulfil/return
target). Cell `0`, so the obligation authority gate `authorizedB { actor := 0, src := 0, .. }` holds via
its reflexive `actor == src` arm — the §8 CREDENTIAL gate is the load-bearing admission condition. -/
abbrev provider : CellId := 0

/-- The BENEFICIARY cell (paid on breach; the obligation `recipient`/slash target). Cell `1`. The D3
slash-liveness gate checks THIS cell is LIVE before slashing into it. -/
abbrev beneficiary : CellId := 1

/-- The staked asset class (the currency the bond is denominated in). Asset `0`. -/
abbrev stakeAsset : AssetId := 0

/-- The bond id keying this SLA's stake record (dregg1's `[u8;32]` obligation_id, modelled `Nat`). -/
abbrev bondId : Nat := 42

/-! ## §2 — Each SLA op as a GATED LEAF NODE through the production turn entry `execFullForestG`. -/

/-- A gated SLA node: credential `cred`, an obligation `action`, no children. -/
def slaNode (cred : Authorization Dg Pf) (action : FullActionA) : DForest :=
  ⟨ mkAuth cred [], action, [] ⟩

/-- **post-bond** — the PROVIDER posts the stake. `createObligationA bondId provider provider beneficiary
stakeAsset stake`: park `stake` off the provider's ledger keyed to the beneficiary. -/
def postNode (cred : Authorization Dg Pf) (stake : Int) : DForest :=
  slaNode cred (.createObligationA bondId provider provider beneficiary stakeAsset stake)

/-- **fulfil** — the SLA was MET. `fulfillObligationA bondId provider`: return the stake to the obligor
(= the record's creator/provider), mark resolved. -/
def fulfilNode (cred : Authorization Dg Pf) : DForest :=
  slaNode cred (.fulfillObligationA bondId provider)

/-- **slash** — the SLA was BREACHED. `slashObligationA bondId beneficiary`: transfer the stake to the
beneficiary (= the record's recipient), mark resolved. The D3 slash-liveness gate fires inside
`releaseEscrowKAsset` — the beneficiary must be a LIVE account. -/
def slashNode (cred : Authorization Dg Pf) : DForest :=
  slaNode cred (.slashObligationA bondId beneficiary)

/-! ## §3 — The leaf-collapse bridge: a childless gated forest runs EXACTLY its single gated node. -/

/-- **`execFullForestG_leaf` — PROVED.** -/
theorem execFullForestG_leaf (s : RecChainedState) (na : DNodeAuth) (a : FullActionA) :
    execFullForestG s (⟨na, a, []⟩ : DForest) = execFullAGated s na a := by
  show (match execFullAGated s na a with
        | some s' => execFullChildrenG (targetOf a) s' ([] : List DChild)
        | none    => none) = execFullAGated s na a
  cases execFullAGated s na a with
  | none   => rfl
  | some _ => rfl

/-- **`execFullForestG_slaNode` — the SLA-op collapse.** A SLA op runs `if gateOK then execFullA action
else none`. -/
theorem execFullForestG_slaNode (s : RecChainedState) (cred : Authorization Dg Pf) (action : FullActionA) :
    execFullForestG s (slaNode cred action)
      = (if gateOK (mkAuth cred []) s = true then execFullA s action else none) := by
  rw [slaNode, execFullForestG_leaf, execFullAGated]

/-! ## §4 — The CREDENTIAL gate: `goodCred` admits, `forgedCred` fail-closed (state-independent). -/

/-- **`gateOK_forged_false` — the forged-credential gate leg is FALSE.** -/
theorem gateOK_forged_false (s : RecChainedState) : gateOK (mkAuth forgedCred []) s = false := by
  have hcred : credentialValidG (mkAuth forgedCred []) = false := by decide
  unfold gateOK
  rw [hcred]
  simp

/-! ## §5 — END-USER THEOREM 1: a FORGED credential ⇒ the whole gated op REJECTS. -/

/-- **`sla_forged_rejected` — PROVED (END-USER THEOREM 1).** A SLA op (ANY obligation action) presented
with a FORGED credential is rejected by the production turn entry, for EVERY pre-state `s`. -/
theorem sla_forged_rejected (s : RecChainedState) (action : FullActionA) :
    execFullForestG s (slaNode forgedCred action) = none := by
  rw [slaNode]
  exact execFullForestG_unauthorized_fails s (mkAuth forgedCred []) action [] (gateOK_forged_false s)

theorem sla_forged_post_rejected (s : RecChainedState) (stake : Int) :
    execFullForestG s (postNode forgedCred stake) = none :=
  sla_forged_rejected s _
theorem sla_forged_fulfil_rejected (s : RecChainedState) :
    execFullForestG s (fulfilNode forgedCred) = none :=
  sla_forged_rejected s _
theorem sla_forged_slash_rejected (s : RecChainedState) :
    execFullForestG s (slashNode forgedCred) = none :=
  sla_forged_rejected s _

/-! ## §6 — END-USER THEOREM 2: a REVOKED credential ⇒ the whole gated op REJECTS. -/

/-- A NodeAuth identical to `mkAuth cred []` but carrying an explicit revocation nullifier `nul`. -/
def mkAuthRevoked (cred : Authorization Dg Pf) (nul : Nat) : DNodeAuth :=
  { mkAuth cred [] with credNul := nul }

/-- A SLA op whose credential carries the revocation nullifier `nul`. -/
def slaNodeRevoked (cred : Authorization Dg Pf) (nul : Nat) (action : FullActionA) : DForest :=
  ⟨ mkAuthRevoked cred nul, action, [] ⟩

/-- **`sla_revoked_rejected` — PROVED (END-USER THEOREM 2).** A SLA op whose credential nullifier `nul`
sits in the COMMITTED revocation registry `s.kernel.revoked` is rejected, for EVERY pre-state and EVERY
(even genuine) credential. A revoked key cannot post/fulfil/slash, no matter how valid its signature. -/
theorem sla_revoked_rejected (s : RecChainedState) (cred : Authorization Dg Pf) (nul : Nat)
    (action : FullActionA) (hrev : s.kernel.revoked.contains nul = true) :
    execFullForestG s (slaNodeRevoked cred nul action) = none := by
  rw [slaNodeRevoked]
  refine execFullForestG_unauthorized_fails s (mkAuthRevoked cred nul) action [] ?_
  exact gateOK_revoked_fails (mkAuthRevoked cred nul) s hrev

/-! ## §7 — END-USER THEOREMS 3–5: POST / FULFIL / SLASH each CONSERVE every asset.

The obligation effects (`createObligationA`/`fulfillObligationA`/`slashObligationA`) all have
`ledgerDeltaAsset = 0` for EVERY asset — so a single-obligation leaf op's per-asset turn delta is `0`,
and `execFullForestG_conserves_per_asset` gives COMBINED-per-asset supply preservation for free. The
stake moves into/out of the off-ledger holding-store, never minted or burned. -/

/-- The per-asset turn delta of a POST is `0` for every asset (obligation create is combined-neutral). -/
theorem postNode_delta_zero (cred : Authorization Dg Pf) (stake : Int) (b : AssetId) :
    turnLedgerDeltaAsset ((lowerForestG (postNode cred stake)).map Prod.snd) b = 0 := by
  simp [postNode, slaNode, lowerForestG, lowerChildrenG, turnLedgerDeltaAsset, ledgerDeltaAsset]

/-- The per-asset turn delta of a FULFIL is `0` for every asset. -/
theorem fulfilNode_delta_zero (cred : Authorization Dg Pf) (b : AssetId) :
    turnLedgerDeltaAsset ((lowerForestG (fulfilNode cred)).map Prod.snd) b = 0 := by
  simp [fulfilNode, slaNode, lowerForestG, lowerChildrenG, turnLedgerDeltaAsset, ledgerDeltaAsset]

/-- The per-asset turn delta of a SLASH is `0` for every asset. -/
theorem slashNode_delta_zero (cred : Authorization Dg Pf) (b : AssetId) :
    turnLedgerDeltaAsset ((lowerForestG (slashNode cred)).map Prod.snd) b = 0 := by
  simp [slashNode, slaNode, lowerForestG, lowerChildrenG, turnLedgerDeltaAsset, ledgerDeltaAsset]

/-- **`sla_post_conserves` — PROVED (END-USER THEOREM 3).** A COMMITTED bond-post preserves EVERY asset's
COMBINED total supply: the provider's stake is LOCKED (bal-debit offset by the holding-store rise), never
minted — so posting a bond moves no net money. -/
theorem sla_post_conserves (s s' : RecChainedState) (cred : Authorization Dg Pf) (stake : Int)
    (b : AssetId) (h : execFullForestG s (postNode cred stake) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestG_conserves_per_asset s s' (postNode cred stake) b h (postNode_delta_zero cred stake b)

/-- **`sla_fulfil_conserves` — PROVED (END-USER THEOREM 4).** A COMMITTED fulfil preserves EVERY asset's
COMBINED total supply: the stake is RETURNED out of the holding-store onto the provider's ledger
(combined-neutral), never minted. -/
theorem sla_fulfil_conserves (s s' : RecChainedState) (cred : Authorization Dg Pf)
    (b : AssetId) (h : execFullForestG s (fulfilNode cred) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestG_conserves_per_asset s s' (fulfilNode cred) b h (fulfilNode_delta_zero cred b)

/-- **`sla_slash_conserves` — PROVED (END-USER THEOREM 5).** A COMMITTED slash preserves EVERY asset's
COMBINED total supply: the stake is TRANSFERRED out of the holding-store onto the beneficiary's ledger
(combined-neutral), never minted. So slashing moves no net money — it merely re-targets the parked stake. -/
theorem sla_slash_conserves (s s' : RecChainedState) (cred : Authorization Dg Pf)
    (b : AssetId) (h : execFullForestG s (slashNode cred) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestG_conserves_per_asset s s' (slashNode cred) b h (slashNode_delta_zero cred b)

/-! ## §8 — END-USER THEOREM 6: D3 LIVENESS — slashing to a SEALED beneficiary ⇒ none.

The D3 slash-liveness gate lives inside `releaseEscrowKAsset` (the slash dispatch target): a release
succeeds iff the parked record's recipient (= the beneficiary) is a LIVE account
(`r.recipient ∈ k.accounts ∧ cellLifecycleLive k r.recipient`). A SEALED cell has `lifecycle = 1`, so
`cellLifecycleLive = false` — slashing into a sealed beneficiary fail-closes (`none`). You cannot slash
into a dead cell; the value would silently vanish from `recTotalAsset`. -/

/-- **`slash_runs_release` — the gate-passing collapse for a SLASH.** When the genuine credential admits
and the credential is not revoked, the slash op IS its underlying `releaseEscrowChainA`. -/
theorem slash_runs_release (s : RecChainedState) (hgate : gateOK (mkAuth goodCred []) s = true) :
    execFullForestG s (slashNode goodCred) = releaseEscrowChainA s bondId beneficiary := by
  rw [slashNode, execFullForestG_slaNode, if_pos hgate]; rfl

/-- **`sla_slash_requires_live_beneficiary` — PROVED (END-USER THEOREM 6, D3 LIVENESS).** Slashing a
bond whose parked record names a beneficiary that is NOT a live, non-sealed account is rejected by the
executor: `execFullForestG s (slashNode goodCred) = none` — EVEN with a genuine, non-revoked credential.
The hypothesis `hdead` is exactly the negation of the D3 slash-liveness gate inside `releaseEscrowKAsset`;
when the located record's recipient (the beneficiary) is dead (e.g. a SEALED cell,
`cellLifecycleLive = false`), the release fail-closes and the whole gated turn rolls back. No slashing
into a dead beneficiary. NON-VACUOUS: `hdead` is forced by a Sealed beneficiary on the concrete
`bondSealed` state below. -/
theorem sla_slash_requires_live_beneficiary (s : RecChainedState) (r : EscrowRecord)
    (hgate : gateOK (mkAuth goodCred []) s = true)
    (hfind : s.kernel.escrows.find? (fun r => decide (r.id = bondId ∧ r.resolved = false)) = some r)
    (hdead : ¬ (r.recipient ∈ s.kernel.accounts ∧ cellLifecycleLive s.kernel r.recipient = true)) :
    execFullForestG s (slashNode goodCred) = none := by
  have hrel : releaseEscrowKAsset s.kernel bondId = none := by
    unfold releaseEscrowKAsset
    cases hf : s.kernel.escrows.find? (fun r => decide (r.id = bondId ∧ r.resolved = false)) with
    | none   => rfl
    | some r' =>
        rw [hf] at hfind; injection hfind with hr; subst hr
        show (if r'.recipient ∈ s.kernel.accounts ∧ cellLifecycleLive s.kernel r'.recipient = true then
                some (settleEscrowRawAsset s.kernel bondId r'.recipient r'.asset r'.amount) else none) = none
        rw [if_neg hdead]
  rw [slash_runs_release s hgate]
  unfold releaseEscrowChainA
  by_cases hauth : releaseSettleAuthB s.kernel bondId beneficiary
  · rw [if_pos hauth, hrel]
  · rw [if_neg hauth]

/-! ## §9 — NON-VACUITY: a concrete BONDED SLA + `#guard` witnesses (the gate + obligation are REAL).

`bond0` is a funded SLA: the provider (cell 0) holds 100 of the staked asset, the beneficiary (cell 1)
is a LIVE account holding 0, no bonds parked yet, empty revocation registry, default Live lifecycle. We
exhibit the whole lifecycle: POST commits (parks the stake), FULFIL returns it, SLASH pays the live
beneficiary; a FORGED credential ⇒ `none`; a REVOKED credential ⇒ `none`; slashing to a SEALED
beneficiary ⇒ `none`; and the lifecycle CONSERVES the staked asset. -/

/-- A funded SLA: provider (cell 0) holds 100 of `stakeAsset`, beneficiary (cell 1) is a LIVE account
holding 0. No bonds parked; empty revocation registry; default Live lifecycle. Actors 0/1 self-authorize
the obligation (`actor == src`), so the §8 CREDENTIAL gate is the load-bearing leg. -/
def bond0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0 }
    log := [] }

/-- An SLA with the stake parked but the beneficiary SEALED (`lifecycle 1 = 1`): the D3 slash-liveness
gate must reject a slash. Built by parking the record directly and sealing cell 1. -/
def bondSealed : RecChainedState :=
  { kernel :=
      { bond0.kernel with
        escrows := [{ id := bondId, creator := provider, recipient := beneficiary,
                      amount := 30, resolved := false, asset := stakeAsset }]
        bal := fun c a => if c = 0 ∧ a = 0 then 70 else 0   -- 30 staked off the provider's ledger
        lifecycle := fun c => if c = 1 then 1 else 0 }       -- beneficiary (cell 1) SEALED
    log := [] }

/-- An SLA with the stake parked and the beneficiary LIVE (the slash-permitting twin of `bondSealed`):
shows the D3 gate is DISCRIMINATING — same record, live beneficiary ⇒ slash COMMITS. -/
def bondStaked : RecChainedState :=
  { kernel :=
      { bond0.kernel with
        escrows := [{ id := bondId, creator := provider, recipient := beneficiary,
                      amount := 30, resolved := false, asset := stakeAsset }]
        bal := fun c a => if c = 0 ∧ a = 0 then 70 else 0 }  -- 30 staked, beneficiary LIVE (default)
    log := [] }

-- The gate passes for the genuine credential, fails for the forged one:
#guard (gateOK (mkAuth goodCred []) bond0)              --  true  (genuine credential admits)
#guard (gateOK (mkAuth forgedCred []) bond0) == false   --  false (forged ⇒ fail-closed)

-- (i) a FUNDED bond-post COMMITS (the provider stakes 30):
#guard ((execFullForestG bond0 (postNode goodCred 30)).isSome)                       --  true (posted!)
-- ...the provider's bare ledger DROPS by 30 (100 → 70), the holding-store RISES by 30:
#guard ((execFullForestG bond0 (postNode goodCred 30)).map (fun s => s.kernel.bal 0 0)) == some 70  --  some 70
#guard ((execFullForestG bond0 (postNode goodCred 30)).map (fun s => escrowHeldAsset s.kernel 0)) == some 30  --  some 30
-- ...but the COMBINED per-asset measure is UNCHANGED (conserved — stake locked, not minted/burned):
#guard ((execFullForestG bond0 (postNode goodCred 30)).map (fun s => recTotalAssetWithEscrow s.kernel 0)) == some 100  --  some 100

-- (ii) a FORGED credential ⇒ none (credential gate fail-closes), even on the funded state:
#guard ((execFullForestG bond0 (postNode forgedCred 30)).isSome) == false            --  false

-- (iii) FULFIL returns the stake to the provider (30 back onto cell 0's ledger: 70 → 100):
#guard ((execFullForestG bondStaked (fulfilNode goodCred)).isSome)                    --  true (fulfilled!)
#guard ((execFullForestG bondStaked (fulfilNode goodCred)).map (fun s => s.kernel.bal 0 0)) == some 100  --  some 100 (returned)
#guard ((execFullForestG bondStaked (fulfilNode goodCred)).map (fun s => recTotalAssetWithEscrow s.kernel 0)) == some 100  --  some 100

-- (iv) SLASH pays the LIVE beneficiary the staked value (30 onto cell 1's ledger):
#guard ((execFullForestG bondStaked (slashNode goodCred)).isSome)                     --  true (slashed!)
#guard ((execFullForestG bondStaked (slashNode goodCred)).map (fun s => s.kernel.bal 1 0)) == some 30  --  some 30 (beneficiary paid)
#guard ((execFullForestG bondStaked (slashNode goodCred)).map (fun s => recTotalAssetWithEscrow s.kernel 0)) == some 100  --  some 100 (conserved)

-- (v) D3 LIVENESS: slashing into a SEALED beneficiary ⇒ none (no slashing into a dead cell):
#guard (cellLifecycleLive bondSealed.kernel beneficiary) == false                     --  false (beneficiary sealed)
#guard ((execFullForestG bondSealed (slashNode goodCred)).isSome) == false            --  false (slash rejected)

-- (vi) REVOCATION: a revoked credential (nullifier 7 in the committed registry) ⇒ none, even genuine.
/-- An SLA whose revocation registry contains nullifier 7 (a revoked credential serial). -/
def bondRevoked : RecChainedState :=
  { kernel := { bond0.kernel with revoked := [7] }, log := [] }
#guard (bondRevoked.kernel.revoked.contains 7)                                        --  true (7 is revoked)
#guard ((execFullForestG bondRevoked (slaNodeRevoked goodCred 7 (.createObligationA bondId provider provider beneficiary stakeAsset 30))).isSome) == false  --  false

-- (vii) END-TO-END CONSERVATION: post then slash, the staked asset's combined supply is fixed at 100.
#guard (((execFullForestG bond0 (postNode goodCred 30)).bind
          (fun s => execFullForestG s (slashNode goodCred))).map
        (fun s => recTotalAssetWithEscrow s.kernel 0)) == some 100  --  some 100 (conserved end-to-end)
-- ...and the beneficiary ends up paid 30 on the bare ledger (the value came out of the holding-store):
#guard (((execFullForestG bond0 (postNode goodCred 30)).bind
          (fun s => execFullForestG s (slashNode goodCred))).map
        (fun s => s.kernel.bal 1 0)) == some 30  --  some 30 (beneficiary paid, end-to-end)

/-! ## §10 — Axiom-hygiene tripwires (the honesty pins). Every keystone depends ONLY on the three
standard kernel axioms `{propext, Classical.choice, Quot.sound}` — no `sorryAx`. -/

#assert_axioms execFullForestG_leaf
#assert_axioms execFullForestG_slaNode
#assert_axioms gateOK_forged_false
#assert_axioms sla_forged_rejected
#assert_axioms sla_revoked_rejected
#assert_axioms postNode_delta_zero
#assert_axioms fulfilNode_delta_zero
#assert_axioms slashNode_delta_zero
#assert_axioms sla_post_conserves
#assert_axioms sla_fulfil_conserves
#assert_axioms sla_slash_conserves
#assert_axioms slash_runs_release
#assert_axioms sla_slash_requires_live_beneficiary

end Dregg2.Apps.StakedSlaGated
