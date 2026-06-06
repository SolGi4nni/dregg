/-
# Dregg2.Apps.ComputeExchangeGated — a VALUE-MOVING COMPUTE MARKET on the ONE GATED executor.

A `starbridge-apps`-shaped compute exchange (the dregg1 marketplace pattern: a buyer pays for a
remote compute job, the provider is paid on delivery, refunded on failure), modelled as REAL ESCROW
moves on the production turn entry — `Dregg2.Exec.FullForestAuth.execFullForestG` (the
`dregg_exec_full_forest_auth` 4-leg gate: credential ∧ cap-authority ∧ caveats-discharged ∧
not-revoked). Unlike `NameserviceGated` (whose ops are balance-neutral `SetField`s), this app actually
MOVES PAYMENT — so the headline guarantee is per-asset CONSERVATION across the escrow lifecycle, and
the D3-liveness guarantee that you cannot settle a job to a DEAD (Sealed) provider.

## The three market ops (each a SINGLE credential-gated leaf node through `execFullForestG`)

A compute-exchange op is one escrow `FullActionA` on the payment ledger, decorated with a credential
(the WHO) and run through the 4-leg gate. The shape is `⟨ mkAuth cred [], <escrow action>, [] ⟩` — one
op = one gated turn, NOT a multi-node forest:

  * **order**  — the BUYER ESCROWS the job payment. `createEscrowA id buyer buyer provider asset amount`
    parks `amount` of `asset` off the buyer's ledger into the holding-store, keyed to the provider as
    eventual recipient. (`creator := buyer` is the refund target, `recipient := provider` the pay
    target.) Per-asset COMBINED-NEUTRAL (the bal-debit is exactly offset by the holding-store rise).
  * **settle** — the PROVIDER is PAID on delivery. `releaseEscrowA id provider` credits the parked
    record's `recipient` (= the provider) AT the record's asset and marks it resolved. Per-asset
    COMBINED-NEUTRAL (the holding-store drop is exactly offset by the provider's bal-credit). The D3
    SETTLE-LIVENESS GATE fires here: the provider MUST be a LIVE account — settling to a Sealed
    provider fail-closes (`none`).
  * **refund** — the BUYER is REFUNDED on failure. `refundEscrowA id actor` credits the parked
    record's `creator` (= the buyer) back, marks it resolved. Per-asset COMBINED-NEUTRAL.

## The gated-executor keystones this app COMPOSES (it adds NO kernel theory)

Each guarantee INSTANTIATES a proved keystone of the gated executor `FullForestAuth`:
  * `execFullForestG_leaf` — a childless gated forest runs EXACTLY its single gated node;
  * `execFullForestG_unauthorized_fails` — a false gate leg ⇒ whole-forest `none`;
  * `gateOK_forged_false` (here, local) — a forged credential's portal leg is `false`;
  * `gateOK_revoked_fails` — a revoked credential's nullifier in `s.kernel.revoked` ⇒ `none`;
  * `execFullForestG_conserves_per_asset` — a per-asset-Δ-zero forest preserves every asset's combined
    supply; and the escrow effects all have `ledgerDeltaAsset = 0`, so the escrow op is combined-neutral.

## End-user theorems (general ∀-state where possible; concrete `#guard` witnesses for non-vacuity)

  1. `cx_forged_rejected`              — a FORGED credential ⇒ the whole gated op rejects (`none`), ∀s, ∀op;
  2. `cx_revoked_rejected`            — a REVOKED credential (nullifier in the committed registry) ⇒ `none`, ∀s;
  3. `cx_order_conserves`            — a committed ORDER preserves EVERY asset's combined supply (payment escrowed, not minted/burned);
  4. `cx_settle_conserves`           — a committed SETTLE preserves EVERY asset's combined supply (payment released, combined-neutral);
  5. `cx_settle_requires_live_provider` — D3 LIVENESS: settling a job to a SEALED provider ⇒ `none` (no paying a dead cell).

Plus a concrete funded market state (`mkt0`) whose `#guard`s show: a funded ORDER commits (and parks),
a SETTLE pays the live provider, a REFUND returns to the buyer, a forged credential ⇒ `none`, a revoked
credential ⇒ `none`, settling to a SEALED provider ⇒ `none`, and the whole lifecycle CONSERVES.

Zero `sorry`/`admit`/`native_decide`/`axiom`. NEW file only — does NOT touch any existing app,
`FullForestAuth.lean`, nor `Dregg2.lean`. Reuses ONLY the proved gated-executor keystones + the proved
escrow combined-conservation/liveness teeth.

## App-level semantics (Hatchery bridge — §8b)

The per-op theorems above are obligations; §8b connects them to the production assurance stack:
  * `cx_pay_conserved_forever` — payment supply never drifts on `trajG` (Tier-4 `conservation%`);
  * `cx_revoked_rejected_forever` — a revoked market participant cannot order/settle/refund, ever;
  * `cx_revoked_pay_safety_forever` — composed Identity revocation + payment conservation
    (`CellContract.composeContracts` / `revokedPaySafety` in `Verify/Contract.lean`).
-/
import Dregg2.Exec.GatedForestCfg
import Dregg2.Exec.CellExecutor
import Dregg2.Exec.CellReal
import Dregg2.Verify.Catalog
import Dregg2.Verify.Contract

namespace Dregg2.Apps.ComputeExchangeGated

open Dregg2.Exec
open Dregg2.Exec (cellObsA trajG SchedG)
open Dregg2.Verify (gateRevoked asset_conserved_forever_production assetConserved
  revoked_pay_safety_forever)
open Dregg2.Verify.Production (Contract Sched)
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Exec.EffectsState
open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.StarbridgeGated
open Dregg2.Exec.StarbridgeGated

/-! ## §1 — The compute-market DOMAIN at the Demo carriers (buyer, provider, the job's payment asset). -/

/-- The BUYER cell (escrows the job payment; the `creator`/refund target). Cell `0`, so the escrow
authority gate `authorizedB { actor := 0, src := 0, .. }` holds via its reflexive `actor == src` arm —
the §8 CREDENTIAL gate is the load-bearing admission condition, not the cap-list. -/
abbrev buyer : CellId := 0

/-- The PROVIDER cell (paid on delivery; the escrow `recipient`/pay target). Cell `1`. The D3
settle-liveness gate checks THIS cell is LIVE before paying it. -/
abbrev provider : CellId := 1

/-- The payment asset class (the currency the job is priced in). Asset `0`. -/
abbrev payAsset : AssetId := 0

/-- The escrow id keying this job's payment record (dregg1's `[u8;32]` escrow_id, modelled `Nat`). -/
abbrev jobId : Nat := 42

/-! ## §2 — Each market op as a GATED LEAF NODE through the production turn entry `execFullForestG`.

A compute-exchange op is a single escrow `FullActionA`, decorated with a credential (the WHO) and run
through the 4-leg gate. `mkAuth cred []` (from `FullForestAuth.Demo`) supplies an admitting cap-mode
(`.unchecked (Guard.all [])`), an empty within-cell caveat list (so the gate's caveat leg is vacuously
discharged), no chain, and a non-revoked nullifier — so `gateOK` reduces to the CREDENTIAL leg
(`portalVerify cred`) ∧ NOT-REVOKED. One op = one gated turn (childless leaf). -/

/-- A gated compute-exchange node: credential `cred`, an escrow `action`, no children. The production
turn-entry shape `⟨ mkAuth cred [], action, [] ⟩`. -/
def cxNode (cred : Authorization Dg Pf) (action : FullActionA) : DForest :=
  ⟨ mkAuth cred [], action, [] ⟩

/-- **order** — the BUYER ESCROWS the job payment. `createEscrowA jobId buyer buyer provider payAsset
amount`: park `amount` of `payAsset` off the buyer's ledger into the holding-store, keyed to the
provider as eventual recipient. A genuine credential ⇒ the gate passes; the escrow lock then runs
(funded + fresh id ⇒ commits). -/
def orderNode (cred : Authorization Dg Pf) (amount : Int) : DForest :=
  cxNode cred (.createEscrowA jobId buyer buyer provider payAsset amount)

/-- **settle** — the PROVIDER is PAID on delivery. `releaseEscrowA jobId provider`: credit the parked
record's `recipient` (= the provider) AT the record's asset, mark resolved. The D3 settle-liveness gate
fires inside `releaseEscrowKAsset` — the provider must be a LIVE account. -/
def settleNode (cred : Authorization Dg Pf) : DForest :=
  cxNode cred (.releaseEscrowA jobId provider)

/-- **refund** — the BUYER is REFUNDED on failure. `refundEscrowA jobId buyer`: credit the parked
record's `creator` (= the buyer) back, mark resolved. -/
def refundNode (cred : Authorization Dg Pf) : DForest :=
  cxNode cred (.refundEscrowA jobId buyer)

/-! ## §3 — The leaf-collapse bridge: a childless gated forest runs EXACTLY its single gated node. -/

/-- **`execFullForestG_leaf` — PROVED (the load-bearing collapse).** A gated forest with NO children
runs EXACTLY its root gated node step: `execFullForestG s ⟨na, a, []⟩ = execFullAGated s na a`. (Both
branches of `execFullForestG`'s match collapse because `execFullChildrenG _ s' [] = some s'`.) The
bridge through which every market op's `none`/`some` is read off `execFullAGated` directly. -/
theorem execFullForestG_leaf (s : RecChainedState) (na : DNodeAuth) (a : FullActionA) :
    execFullForestG s (⟨na, a, []⟩ : DForest) = execFullAGated s na a := by
  show (match execFullAGated s na a with
        | some s' => execFullChildrenG (targetOf a) s' ([] : List DChild)
        | none    => none) = execFullAGated s na a
  cases execFullAGated s na a with
  | none   => rfl
  | some _ => rfl

/-- **`execFullForestG_cxNode` — the market-op collapse.** A compute-exchange op runs `if gateOK then
execFullA action else none`. The unfolding every theorem below rests on. -/
theorem execFullForestG_cxNode (s : RecChainedState) (cred : Authorization Dg Pf) (action : FullActionA) :
    execFullForestG s (cxNode cred action)
      = (if gateOK (mkAuth cred []) s = true then execFullA s action else none) := by
  rw [cxNode, execFullForestG_leaf, execFullAGated]

/-! ## §4 — The CREDENTIAL gate: `goodCred` admits, `forgedCred` (and any forged cred) fail-closed.

`gateOK (mkAuth cred []) s = credentialValidG (mkAuth cred []) && capAuthorityG (mkAuth cred []) &&
caveatsDischarged (mkAuth cred []) s && revocationGate (mkAuth cred []) s`. For `mkAuth`: the cap mode
is `.unchecked (Guard.all [])` (admits), the within-cell caveat list is `[]` (vacuously discharged, no
chain), the nullifier is `0`. So `gateOK` is exactly the credential leg `portalVerify cred` ∧
NOT-REVOKED. -/

/-- **`gateOK_forged_false` — the forged-credential gate leg is FALSE.** `portalVerify (.signature 7 8)
= decide (7 = 8) = false` — independent of state, so the whole gate `gateOK (mkAuth forgedCred []) s =
false`. -/
theorem gateOK_forged_false (s : RecChainedState) : gateOK (mkAuth forgedCred []) s = false := by
  have hcred : credentialValidG (mkAuth forgedCred []) = false := by decide
  unfold gateOK
  rw [hcred]
  simp

/-! ## §5 — END-USER THEOREM 1: a FORGED credential ⇒ the whole gated op REJECTS. -/

/-- **`cx_forged_rejected` — PROVED (END-USER THEOREM 1).** A compute-exchange op (ANY escrow action)
presented with a FORGED credential is rejected by the production turn entry: `execFullForestG s (cxNode
forgedCred action) = none`, for EVERY pre-state `s`. The §8 credential leg fail-closes ⇒ the whole forest
rolls back — nobody can order/settle/refund a job without a genuine credential. -/
theorem cx_forged_rejected (s : RecChainedState) (action : FullActionA) :
    execFullForestG s (cxNode forgedCred action) = none := by
  rw [cxNode]
  exact execFullForestG_unauthorized_fails s (mkAuth forgedCred []) action [] (gateOK_forged_false s)

/-- Specialization to the headline ops (the named-shape rejections). -/
theorem cx_forged_order_rejected (s : RecChainedState) (amount : Int) :
    execFullForestG s (orderNode forgedCred amount) = none :=
  cx_forged_rejected s _
theorem cx_forged_settle_rejected (s : RecChainedState) :
    execFullForestG s (settleNode forgedCred) = none :=
  cx_forged_rejected s _
theorem cx_forged_refund_rejected (s : RecChainedState) :
    execFullForestG s (refundNode forgedCred) = none :=
  cx_forged_rejected s _

/-! ## §6 — END-USER THEOREM 2: a REVOKED credential ⇒ the whole gated op REJECTS.

The revocation leg reads the COMMITTED kernel-state registry `s.kernel.revoked` (adversary-uncontrollable),
NOT the wire-supplied `rev`. A node whose nullifier sits in that registry fail-closes no matter how valid
its signature. (For `mkAuth`, the nullifier is `0` — a market built on `mkAuth` is revoked exactly when
`0 ∈ s.kernel.revoked`; the GENERAL `mkAuthRevoked` below carries an arbitrary nullifier.) -/

/-- A NodeAuth identical to `mkAuth cred []` but carrying an explicit revocation nullifier `nul` — the
serial the kernel-state registry `s.kernel.revoked` is checked against. -/
def mkAuthRevoked (cred : Authorization Dg Pf) (nul : Nat) : DNodeAuth :=
  { mkAuth cred [] with credNul := nul }

/-- A market op whose credential carries the revocation nullifier `nul`. -/
def cxNodeRevoked (cred : Authorization Dg Pf) (nul : Nat) (action : FullActionA) : DForest :=
  ⟨ mkAuthRevoked cred nul, action, [] ⟩

/-- **`cx_revoked_rejected` — PROVED (END-USER THEOREM 2).** A compute-exchange op whose credential
nullifier `nul` sits in the COMMITTED revocation registry `s.kernel.revoked` is rejected by the
production turn entry: `execFullForestG s (cxNodeRevoked cred nul action) = none`, for EVERY pre-state
`s` and EVERY (even genuine) credential. The revocation leg fail-closes ⇒ whole-forest rollback — a
revoked key cannot order/settle/refund, no matter how valid its signature. -/
theorem cx_revoked_rejected (s : RecChainedState) (cred : Authorization Dg Pf) (nul : Nat)
    (action : FullActionA) (hrev : s.kernel.revoked.contains nul = true) :
    execFullForestG s (cxNodeRevoked cred nul action) = none := by
  rw [cxNodeRevoked]
  refine execFullForestG_unauthorized_fails s (mkAuthRevoked cred nul) action [] ?_
  refine gateOK_revoked_fails (mkAuthRevoked cred nul) s ?_
  show s.kernel.revoked.contains nul = true
  exact hrev

/-! ## §7 — END-USER THEOREMS 3–4: a committed ORDER / SETTLE CONSERVES every asset.

The escrow effects (`createEscrowA`/`releaseEscrowA`/`refundEscrowA`) all have `ledgerDeltaAsset = 0`
for EVERY asset — so a single-escrow leaf op's per-asset turn delta is `0`, and
`execFullForestG_conserves_per_asset` gives COMBINED-per-asset supply preservation for free. The payment
moves into/out of the off-ledger holding-store, never minted or burned: Σ each asset in = Σ each asset
out across the escrow lifecycle. The credential/revocation gate is balance-orthogonal. -/

/-- The per-asset turn delta of any single escrow leaf op is `0` (escrow effects are combined-neutral —
`ledgerDeltaAsset = 0`) — for EVERY asset `b`. The conservation hypothesis, discharged once and reused. -/
theorem cxNode_delta_zero (cred : Authorization Dg Pf) (id : Nat) (actor creator recipient : CellId)
    (asset : AssetId) (amount : Int) (b : AssetId) :
    turnLedgerDeltaAsset
      ((lowerForestG (cxNode cred (.createEscrowA id actor creator recipient asset amount))).map Prod.snd) b = 0 := by
  simp [cxNode, lowerForestG, lowerChildrenG, turnLedgerDeltaAsset, ledgerDeltaAsset]

/-- The per-asset turn delta of a SETTLE (`releaseEscrowA`) leaf op is `0` for every asset. -/
theorem settleNode_delta_zero (cred : Authorization Dg Pf) (id : Nat) (actor : CellId) (b : AssetId) :
    turnLedgerDeltaAsset
      ((lowerForestG (cxNode cred (.releaseEscrowA id actor))).map Prod.snd) b = 0 := by
  simp [cxNode, lowerForestG, lowerChildrenG, turnLedgerDeltaAsset, ledgerDeltaAsset]

/-- The per-asset turn delta of a REFUND (`refundEscrowA`) leaf op is `0` for every asset. -/
theorem refundNode_delta_zero (cred : Authorization Dg Pf) (id : Nat) (actor : CellId) (b : AssetId) :
    turnLedgerDeltaAsset
      ((lowerForestG (cxNode cred (.refundEscrowA id actor))).map Prod.snd) b = 0 := by
  simp [cxNode, lowerForestG, lowerChildrenG, turnLedgerDeltaAsset, ledgerDeltaAsset]

/-- **`cx_order_conserves` — PROVED (END-USER THEOREM 3).** A COMMITTED order preserves EVERY asset's
COMBINED total supply: `recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b`, for
every asset `b`. The buyer's payment is ESCROWED (the bal-debit exactly offset by the holding-store
rise), never minted — so an order moves no net money. A one-liner off
`execFullForestG_conserves_per_asset` with the escrow-is-combined-neutral hypothesis from
`cxNode_delta_zero`. -/
theorem cx_order_conserves (s s' : RecChainedState) (cred : Authorization Dg Pf) (amount : Int)
    (b : AssetId) (h : execFullForestG s (orderNode cred amount) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestG_conserves_per_asset s s' (orderNode cred amount) b h
    (cxNode_delta_zero cred jobId buyer buyer provider payAsset amount b)

/-- **`cx_settle_conserves` — PROVED (END-USER THEOREM 4).** A COMMITTED settle preserves EVERY asset's
COMBINED total supply: the payment is RELEASED out of the holding-store onto the provider's ledger (the
holding-store drop exactly offset by the provider's bal-credit), never minted. So paying the provider
moves no net money. A one-liner off `execFullForestG_conserves_per_asset` with the escrow-is-neutral
hypothesis from `settleNode_delta_zero`. -/
theorem cx_settle_conserves (s s' : RecChainedState) (cred : Authorization Dg Pf)
    (b : AssetId) (h : execFullForestG s (settleNode cred) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestG_conserves_per_asset s s' (settleNode cred) b h
    (settleNode_delta_zero cred jobId provider b)

/-- **`cx_refund_conserves` — PROVED (the refund face of conservation).** A COMMITTED refund preserves
EVERY asset's combined supply (the payment returns from the holding-store to the buyer, combined-neutral).
The same shape as settle. -/
theorem cx_refund_conserves (s s' : RecChainedState) (cred : Authorization Dg Pf)
    (b : AssetId) (h : execFullForestG s (refundNode cred) = some s') :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  execFullForestG_conserves_per_asset s s' (refundNode cred) b h
    (refundNode_delta_zero cred jobId buyer b)

/-! ## §8 — END-USER THEOREM 5: D3 LIVENESS — settling to a SEALED provider ⇒ none.

The D3 settle-liveness gate lives inside `releaseEscrowKAsset`: a release succeeds iff the parked
record's recipient is a LIVE account (`r.recipient ∈ k.accounts ∧ cellLifecycleLive k r.recipient`). A
SEALED cell has `lifecycle = 1`, so `cellLifecycleLive = false` — settling a job to a sealed provider
fail-closes (`none`). You cannot pay a dead cell; the value would silently vanish from
`recTotalAsset`. This is the executor-enforced liveness face of the conservation guarantee. -/

/-- **`settle_runs_release` — the gate-passing collapse for a SETTLE.** When the genuine credential
admits and the credential is not revoked, the settle op IS its underlying `releaseEscrowChainA`:
`execFullForestG s (settleNode goodCred) = releaseEscrowChainA s jobId provider`. The hinge for the D3
liveness theorem: any liveness-rejection of the release rejects the whole turn. -/
theorem settle_runs_release (s : RecChainedState) (hgate : gateOK (mkAuth goodCred []) s = true) :
    execFullForestG s (settleNode goodCred) = releaseEscrowChainA s jobId provider := by
  rw [settleNode, execFullForestG_cxNode, if_pos hgate]
  rfl

/-- **`cx_settle_requires_live_provider` — PROVED (END-USER THEOREM 5, D3 LIVENESS).** Settling a job
whose parked record names a provider that is NOT a live, non-sealed account is rejected by the executor:
`execFullForestG s (settleNode goodCred) = none` — EVEN with a genuine, non-revoked credential. The
hypothesis `hdead` is exactly the negation of the D3 settle-liveness gate inside `releaseEscrowKAsset`;
when the located record's recipient is dead (e.g. a SEALED provider, `cellLifecycleLive = false`), the
release fail-closes and the whole gated turn rolls back. No paying a dead provider. NON-VACUOUS: `hdead`
is forced by a Sealed provider on the concrete `mktSealed` state below. -/
theorem cx_settle_requires_live_provider (s : RecChainedState) (r : EscrowRecord)
    (hgate : gateOK (mkAuth goodCred []) s = true)
    (hfind : s.kernel.escrows.find? (fun r => decide (r.id = jobId ∧ r.resolved = false)) = some r)
    (hdead : ¬ (r.recipient ∈ s.kernel.accounts ∧ cellLifecycleLive s.kernel r.recipient = true)) :
    execFullForestG s (settleNode goodCred) = none := by
  have hrel : releaseEscrowKAsset s.kernel jobId = none := by
    unfold releaseEscrowKAsset
    cases hf : s.kernel.escrows.find? (fun r => decide (r.id = jobId ∧ r.resolved = false)) with
    | none   => rfl
    | some r' =>
        rw [hf] at hfind; injection hfind with hr; subst hr
        show (if r'.recipient ∈ s.kernel.accounts ∧ cellLifecycleLive s.kernel r'.recipient = true then
                some (settleEscrowRawAsset s.kernel jobId r'.recipient r'.asset r'.amount) else none) = none
        rw [if_neg hdead]
  rw [settle_runs_release s hgate]
  unfold releaseEscrowChainA
  by_cases hauth : releaseSettleAuthB s.kernel jobId provider
  · rw [if_pos hauth, hrel]
  · rw [if_neg hauth]

/-! ## §9 — NON-VACUITY: a concrete FUNDED market + `#guard` witnesses (the gate + escrow are REAL).

`mkt0` is a funded market: the buyer (cell 0) holds 100 of the payment asset, the provider (cell 1) is
a LIVE account holding 0, no escrows parked yet, empty revocation registry, default Live lifecycle. On
`mkt0` and its successors we exhibit the whole lifecycle: ORDER commits (parks the payment), SETTLE pays
the live provider, REFUND returns to the buyer; a FORGED credential ⇒ `none`; a REVOKED credential ⇒
`none`; settling to a SEALED provider ⇒ `none`; and the lifecycle CONSERVES the payment asset. -/

/-- A funded compute market: buyer (cell 0) holds 100 of `payAsset`, provider (cell 1) is a LIVE account
holding 0. No escrows parked; empty revocation registry; default Live lifecycle for all cells. Actors
0/1 self-authorize the escrow (`actor == src`), so the §8 CREDENTIAL gate is the load-bearing leg. -/
def mkt0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0 }
    log := [] }

/-- The market AFTER a funded order (the payment is escrowed) — the canonical post-order state on which
SETTLE/REFUND are exercised. Computed by running the genuine-credential order through the gated executor. -/
def mktOrdered : Option RecChainedState := execFullForestG mkt0 (orderNode goodCred 30)

/-- A market with the payment already escrowed but the provider SEALED (`lifecycle 1 = 1`): the D3
settle-liveness gate must reject a settle. Built by parking the record directly and sealing cell 1. -/
def mktSealed : RecChainedState :=
  { kernel :=
      { mkt0.kernel with
        escrows := [{ id := jobId, creator := buyer, recipient := provider,
                      amount := 30, resolved := false, asset := payAsset }]
        bal := fun c a => if c = 0 ∧ a = 0 then 70 else 0   -- 30 parked off the buyer's ledger
        lifecycle := fun c => if c = 1 then 1 else 0 }       -- provider (cell 1) SEALED
    log := [] }

/-- A market with the payment escrowed and the provider LIVE (the settle-permitting twin of `mktSealed`):
shows the D3 gate is DISCRIMINATING — same record, live provider ⇒ settle COMMITS. -/
def mktParked : RecChainedState :=
  { kernel :=
      { mkt0.kernel with
        escrows := [{ id := jobId, creator := buyer, recipient := provider,
                      amount := 30, resolved := false, asset := payAsset }]
        bal := fun c a => if c = 0 ∧ a = 0 then 70 else 0 }  -- 30 parked, provider LIVE (default)
    log := [] }

-- The gate passes for the genuine credential, fails for the forged one (the credential leg is live):
#guard (gateOK (mkAuth goodCred []) mkt0)              --  true  (genuine credential admits)
#guard (gateOK (mkAuth forgedCred []) mkt0) == false   --  false (forged ⇒ fail-closed)

-- (i) a FUNDED order COMMITS (the buyer escrows 30 of the payment asset):
#guard ((execFullForestG mkt0 (orderNode goodCred 30)).isSome)                       --  true (ordered!)
-- ...the buyer's bare ledger DROPS by 30 (100 → 70), the holding-store RISES by 30:
#guard ((execFullForestG mkt0 (orderNode goodCred 30)).map (fun s => s.kernel.bal 0 0)) == some 70  --  some 70
#guard ((execFullForestG mkt0 (orderNode goodCred 30)).map (fun s => escrowHeldAsset s.kernel 0)) == some 30  --  some 30
-- ...but the COMBINED per-asset measure is UNCHANGED (conserved — payment escrowed, not minted/burned):
#guard ((execFullForestG mkt0 (orderNode goodCred 30)).map (fun s => recTotalAssetWithEscrow s.kernel 0)) == some 100  --  some 100

-- (ii) a FORGED credential ⇒ none (credential gate fail-closes), even on the funded state:
#guard ((execFullForestG mkt0 (orderNode forgedCred 30)).isSome) == false            --  false

-- (iii) SETTLE pays the LIVE provider its escrowed payment (30 of the asset onto cell 1's ledger):
#guard ((execFullForestG mktParked (settleNode goodCred)).isSome)                     --  true (paid!)
#guard ((execFullForestG mktParked (settleNode goodCred)).map (fun s => s.kernel.bal 1 0)) == some 30  --  some 30 (provider paid)
-- ...and the SETTLE conserves the combined measure (release is combined-neutral):
#guard ((execFullForestG mktParked (settleNode goodCred)).map (fun s => recTotalAssetWithEscrow s.kernel 0)) == some 100  --  some 100

-- (iv) D3 LIVENESS: settling to a SEALED provider ⇒ none (no paying a dead cell):
#guard (cellLifecycleLive mktSealed.kernel provider) == false                         --  false (provider sealed)
#guard ((execFullForestG mktSealed (settleNode goodCred)).isSome) == false            --  false (settle rejected)

-- (v) REFUND returns the payment to the BUYER (30 back onto cell 0's ledger: 70 → 100):
#guard ((execFullForestG mktParked (refundNode goodCred)).isSome)                     --  true (refunded!)
#guard ((execFullForestG mktParked (refundNode goodCred)).map (fun s => s.kernel.bal 0 0)) == some 100  --  some 100 (buyer made whole)
#guard ((execFullForestG mktParked (refundNode goodCred)).map (fun s => recTotalAssetWithEscrow s.kernel 0)) == some 100  --  some 100 (conserved)

-- (vi) REVOCATION: a revoked credential (nullifier 7 in the committed registry) ⇒ none, even genuine.
/-- A market whose revocation registry contains nullifier 7 (a revoked credential serial). -/
def mktRevoked : RecChainedState :=
  { kernel := { mkt0.kernel with revoked := [7] }, log := [] }
#guard (mktRevoked.kernel.revoked.contains 7)                                         --  true (7 is revoked)
#guard ((execFullForestG mktRevoked (cxNodeRevoked goodCred 7 (.createEscrowA jobId buyer buyer provider payAsset 30))).isSome) == false  --  false (revoked ⇒ none)

-- (vii) END-TO-END CONSERVATION: order then settle, the payment asset's combined supply is fixed at 100.
#guard (((execFullForestG mkt0 (orderNode goodCred 30)).bind
          (fun s => execFullForestG s (settleNode goodCred))).map
        (fun s => recTotalAssetWithEscrow s.kernel 0)) == some 100  --  some 100 (conserved end-to-end)
-- ...and the provider ends up paid 30 on the bare ledger (the value came out of the holding-store):
#guard (((execFullForestG mkt0 (orderNode goodCred 30)).bind
          (fun s => execFullForestG s (settleNode goodCred))).map
        (fun s => s.kernel.bal 1 0)) == some 30  --  some 30 (provider paid, end-to-end)

/-! ## §8b — Hatchery bridge: production crowns on `trajG` (app semantics, not just per-op teeth). -/

/-- Per-baseline payment conservation contract (the compute market's `conservation% payAsset` shape). -/
noncomputable def cxPayConserved (s0 : RecChainedState) : Contract :=
  assetConserved s0 payAsset

/-- **`cx_pay_conserved_forever` — APP SEMANTICS (production crown).** From any baseline `s0`, along
EVERY adversarial production schedule, the payment asset's combined supply never drifts — the value-
moving market inherits the Hatchery `conservation%` shape on `trajG`. -/
theorem cx_pay_conserved_forever (s0 : RecChainedState) (sched : SchedG) :
    ∀ n, cellObsA (trajG s0 sched n) payAsset = cellObsA s0 payAsset :=
  asset_conserved_forever_production s0 payAsset sched

/-- **`cx_mkt0_pay_conserved_forever` — the canonical funded-market production witness.** -/
theorem cx_mkt0_pay_conserved_forever (sched : SchedG) :
    ∀ n, cellObsA (trajG mkt0 sched n) payAsset = 100 :=
  fun n => by
    have h := cx_pay_conserved_forever mkt0 sched n
    simpa [mkt0, payAsset, cellObsA] using h

/-- **`cx_revoked_rejected_forever` — APP SEMANTICS (revocation crown).** If nullifier `nul` is in the
committed revocation registry initially, EVERY market op with that credential is rejected at EVERY
index of EVERY production schedule — composed from `gateRevoked` persistence + `cx_revoked_rejected`. -/
theorem cx_revoked_rejected_forever (s : RecChainedState) (cred : Authorization Dg Pf) (nul : Nat)
    (action : FullActionA) (hinit : nul ∈ s.kernel.revoked) (sched : SchedG) :
    ∀ n, execFullForestG (trajG s sched n) (cxNodeRevoked cred nul action) = none := by
  intro n
  exact cx_revoked_rejected (trajG s sched n) cred nul action
    (List.contains_iff_mem.mpr ((gateRevoked nul).forever hinit sched n))

/-- **`cx_revoked_pay_safety_forever` — COMPOSED APP CROWN (Identity ∩ ComputeExchange).** Revoked
nullifier stays in the committed registry AND the market payment asset's supply stays at the `mkt0`
baseline — one `revokedPaySafety` composed contract from `Verify/Contract.lean`. -/
theorem cx_revoked_pay_safety_forever (credNul : Nat) (s : RecChainedState)
    (hrev : credNul ∈ s.kernel.revoked)
    (hpay : cellObsA s payAsset = cellObsA mkt0 payAsset) (sched : SchedG) :
    ∀ n, credNul ∈ (trajG s sched n).kernel.revoked ∧
         cellObsA (trajG s sched n) payAsset = cellObsA mkt0 payAsset :=
  revoked_pay_safety_forever credNul mkt0 payAsset s hrev hpay sched

/-- **`cx_mkt0_revoked_pay_safety_forever` — funded-market composed witness (`s = mkt0`).** -/
theorem cx_mkt0_revoked_pay_safety_forever (credNul : Nat)
    (hrev : credNul ∈ mkt0.kernel.revoked) (sched : SchedG) :
    ∀ n, credNul ∈ (trajG mkt0 sched n).kernel.revoked ∧
         cellObsA (trajG mkt0 sched n) payAsset = 100 :=
  fun n => by
    have h := cx_revoked_pay_safety_forever credNul mkt0 hrev rfl sched n
    simpa [mkt0, payAsset, cellObsA] using h

/-! ## §10 — Axiom-hygiene tripwires (the honesty pins). Every keystone depends ONLY on the three
standard kernel axioms `{propext, Classical.choice, Quot.sound}` — no `sorryAx`. (The portal soundness
is a Prop carrier in `FullForestAuth`, never an axiom, so it does not appear.) -/

#assert_axioms execFullForestG_leaf
#assert_axioms execFullForestG_cxNode
#assert_axioms gateOK_forged_false
#assert_axioms cx_forged_rejected
#assert_axioms cx_revoked_rejected
#assert_axioms cxNode_delta_zero
#assert_axioms settleNode_delta_zero
#assert_axioms refundNode_delta_zero
#assert_axioms cx_order_conserves
#assert_axioms cx_settle_conserves
#assert_axioms cx_refund_conserves
#assert_axioms settle_runs_release
#assert_axioms cx_settle_requires_live_provider
#assert_axioms cx_pay_conserved_forever
#assert_axioms cx_mkt0_pay_conserved_forever
#assert_axioms cx_revoked_rejected_forever
#assert_axioms cx_revoked_pay_safety_forever
#assert_axioms cx_mkt0_revoked_pay_safety_forever

end Dregg2.Apps.ComputeExchangeGated
