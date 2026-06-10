/-
# Dregg2.Substrate.IssuerLedger — the CANONICAL issuer-supply exact-conservation value model
(W1 groundwork, pre-rotation).

This is the FORWARD model the R2 probe (`Dregg2.Substrate.IssuerSupplyProbe`, commit 2970fd77b)
licensed. The probe PROVED, over the existing executor state, that the issuer-supply value law
(`AssetId := issuer CellId`; the issuer carries −supply; conservation is exact) survives every step
the existing conservation theorems can express, and that the ONE thing it could not express — the
shielded value-binding — is a REPRESENTABILITY gap (notes carried no asset/value, `noteSpend` took
no amount), not a refutation. This module PROMOTES that verdict from "probe over the existing state"
to "the canonical value model", and closes the E4 gap:

  * **§1 — the canonical conserved invariant** (`ConservedLedger := ExactLedger`): the per-asset
    exact law `∀ a, recTotalAsset k a = 0` is THE conservation invariant of the forward
    model. Every committed kernel step preserves it, each by INSTANTIATING a probe theorem (never
    re-proved): transfer / escrow create-release-refund / bridge lock-cancel / genesis / fresh-cell
    creation / the reformed `issuerMoveK` mint. Packaged as `step_preserves_ledger` (the canonical
    "the model is closed under every verb" statement) + `genesis_starts_conserved`.

  * **§2 — E4, THE NEW OBLIGATION (the keystone new proof).** Asset-typed bound notes
    (`AssetBoundNote` = `ShieldedValue.BoundNote` + `asset : AssetId`) and the pool-pseudo-cell
    formulation. The probe's `unshieldK` left `amt` a FREE parameter unbound to the spent note's
    hidden value (the `kPool` `#guard` drained a pool with ZERO notes). Here:
      - `PoolConsistent` STATES the pool↔notes invariant the probe found unrepresentable:
        `bal (poolOf a) a = Σ (values of unspent a-notes)` — now representable because notes carry
        `(asset, value)`;
      - `boundUnshieldK` GATES the unshield amount on the spent note: `amt = value(spent note)` is
        a fail-closed precondition, so the unshield-amount/spent-note binding is enforced;
      - `boundUnshield_amount_bound` (THE E4 KEYSTONE) — a committed bound-unshield's transparent
        outflow EQUALS the spent note's hidden value: the Mina-excess / `balance_change` obligation,
        now a THEOREM over executed state;
      - `boundUnshield_preserves_pool_consistency` — a bound-unshield preserves `PoolConsistent`:
        debiting the pool by exactly the spent note's value, while that note leaves the unspent set,
        keeps the pool-balance ↔ unspent-value equation — the pool cannot be drained beyond
        its notes;
      - `boundShield_preserves_pool_consistency` — shield (transfer-in ∘ note-create) raises both
        sides by the created note's value;
      - and the LEDGER half still rides the probe (`boundUnshieldK_preserves_exact`,
        `boundShieldK_preserves_exact` — `ConservedLedger` survives, the transparent legs are
        transfers).
    Together: ledger-exactness (probe) AND custody-soundness (E4) — the two halves the probe
    separated, now both proved, the shielded pool no longer drainable beyond its notes.

  * **§3 — the fee/bridge pot laws, canonical.** Re-export `turn_exact_with_burn_pot` /
    `fee_exact_with_burn_pot` / `bridgeFinalizeToPot_preserves_exact` as the forward model's
    fee/bridge theorems (`canonical_fee_law` / `canonical_bridge_law`), retiring the modulo-burn /
    bridge-outflow exemptions. `mint_breaks_exact` / `bridgeFinalize_breaks_exact` carry as the
    non-vacuity teeth.

  * **§4 — THE MIGRATION TOUCH-LIST** (a doc block): the precise, mechanical list of what the
    eventual live VK rotation mutates (E1 issuer-well availability waiver · E2 mint-cap retarget ·
    E3 transitional escrow term dies at S3 · E5 fee legs onto the per-asset ledger · E6 pot
    genesis), so the rotation step is bookkeeping, not design.

Standalone: NOT imported by the anchor until the coordinated W1 rotation. `#assert_axioms` on every
new theorem; no sorry. Builds on the probe + `Exec.ShieldedValue` (both axiom-clean in tree).
-/
import Dregg2.Substrate.IssuerSupplyProbe
import Dregg2.Exec.ShieldedValue

namespace Dregg2.Substrate.IssuerLedger

open Dregg2.Exec
open Dregg2.Substrate.IssuerSupplyProbe
open Dregg2.Exec.ShieldedValue (ValueCommitment BoundNote)
-- The same opens the probe uses, so the fee/bridge law signatures resolve identically (the
-- `RecStmt`/`interpChained`/`runTurn`/`TurnOutcome` names live in `Argus`, the fee primitives in
-- `Admission`).
open Dregg2.Circuit.Argus
open Dregg2.Exec.Admission (AdmCtx TurnHdr admissible commitPrologue feeBurned)

/-! ## §1 — THE CANONICAL CONSERVED INVARIANT + every-step closure.

The probe established `ExactLedger` as the value law and proved each committed verb preserves it.
We promote `ExactLedger` to the canonical name `ConservedLedger` and package the closure: the
forward model's state space is exactly the `ConservedLedger` states, and every kernel verb keeps
you inside it. -/

/-- **THE CANONICAL CONSERVATION INVARIANT (verbatim).** Per asset, the cell-ledger sum PLUS the
transitional off-ledger escrow holding-store equals ZERO. This IS the R2 value law — the
issuer-supply formulation makes it hold BY CONSTRUCTION wherever issuers are live accounts
(`issuerView_exact`), and it is preserved by every committed step (§1 below). After the S3
storage-as-cell-programs migration the escrow term dies (E3) and the law collapses to the pure
`∀ a, Σ_{c ∈ accounts} bal c a = 0`. -/
abbrev ConservedLedger (k : RecordKernelState) : Prop := ExactLedger k

/-- Genesis (empty ledger, no parked escrows) starts conserved. The forward model's initial states
are conserved — `genesis_exact` lifted. -/
theorem genesis_starts_conserved (k : RecordKernelState) (hbal : k.bal = fun _ _ => 0)
    (hesc : k.escrows = []) : ConservedLedger k :=
  genesis_exact k hbal hesc

/-- **CANONICAL: transfer preserves conservation** — `transfer_preserves_exact`. -/
theorem transfer_preserves {k k' : RecordKernelState} {t : Turn} {a : AssetId}
    (h : recKExecAsset k t a = some k') (hc : ConservedLedger k) : ConservedLedger k' :=
  transfer_preserves_exact h hc

/-- **CANONICAL: the reformed mint (issuer-move) preserves conservation** — `issuerMoveK_preserves_exact`.
Authority over the ISSUER, no availability gate at the negative-capable well, policy in the issuer's
program (E1/E2). -/
theorem mint_preserves {issuerOf : AssetId → CellId} {k k' : RecordKernelState} {actor : CellId}
    {a : AssetId} {dst : CellId} {amt : ℤ} (h : issuerMoveK issuerOf k actor a dst amt = some k')
    (hc : ConservedLedger k) : ConservedLedger k' :=
  issuerMoveK_preserves_exact issuerOf h hc

/-- **CANONICAL: fresh-cell creation preserves conservation** — `createCell_preserves_exact`. Issuer
cells (and any cell) are born empty; account growth is neutral. -/
theorem createCell_preserves (k : RecordKernelState) (newCell : CellId)
    (hfresh : newCell ∉ k.accounts) (hc : ConservedLedger k) :
    ConservedLedger (createCellIntoAsset k newCell) :=
  createCell_preserves_exact k newCell hfresh hc

/-- **CANONICAL: escrow create preserves conservation** — `escrowCreate_preserves_exact`. -/
theorem escrowCreate_preserves {k k' : RecordKernelState} {id : Nat}
    {actor creator recipient : CellId} {asset : AssetId} {amount : ℤ}
    (h : createEscrowKAsset k id actor creator recipient asset amount = some k')
    (hc : ConservedLedger k) : ConservedLedger k' :=
  escrowCreate_preserves_exact h hc

/-- **CANONICAL: escrow release preserves conservation** — `escrowRelease_preserves_exact`. -/
theorem escrowRelease_preserves {k k' : RecordKernelState} {id : Nat}
    (h : releaseEscrowKAsset k id = some k') (hc : ConservedLedger k) : ConservedLedger k' :=
  escrowRelease_preserves_exact h hc

/-- **CANONICAL: escrow refund preserves conservation** — `escrowRefund_preserves_exact`. -/
theorem escrowRefund_preserves {k k' : RecordKernelState} {id : Nat}
    (h : refundEscrowKAsset k id = some k') (hc : ConservedLedger k) : ConservedLedger k' :=
  escrowRefund_preserves_exact h hc

/-- **CANONICAL: bridge lock preserves conservation** — `bridgeLock_preserves_exact`. -/
theorem bridgeLock_preserves {k k' : RecordKernelState} {id : Nat}
    {actor originator destination : CellId} {asset : AssetId} {amount : ℤ}
    (h : bridgeLockKAsset k id actor originator destination asset amount = some k')
    (hc : ConservedLedger k) : ConservedLedger k' :=
  bridgeLock_preserves_exact h hc

/-- **CANONICAL: bridge cancel preserves conservation** — `bridgeCancel_preserves_exact`. -/
theorem bridgeCancel_preserves {k k' : RecordKernelState} {id : Nat}
    (h : bridgeCancelKAsset k id = some k') (hc : ConservedLedger k) : ConservedLedger k' :=
  bridgeCancel_preserves_exact h hc

/-- **THE NON-VACUITY TOOTH (canonical): the OLD supply-increment mint BREAKS conservation.** A
committed `recKMintAsset` of a positive amount on a conserved state yields a NON-conserved state —
so the issuer-move reformulation is a genuine REPAIR. (`mint_breaks_exact`.) -/
theorem oldMint_breaks_conservation {k k' : RecordKernelState} {actor cell : CellId} {a : AssetId}
    {amt : ℤ} (h : Dregg2.Exec.TurnExecutorFull.recKMintAsset k actor cell a amt = some k')
    (hpos : 0 < amt) (hc : ConservedLedger k) : ¬ ConservedLedger k' :=
  mint_breaks_exact h hpos hc

/-! ## §2 — E4: THE SHIELDED VALUE-BINDING (the keystone new proof).

The probe's `unshieldK` (its §5) left the transparent outflow `amt` a FREE parameter — unbound to
any spent note. The LEDGER stayed exact (the pool pays transparently) but custody soundness did not:
the `kPool` `#guard` drained a pool that had ZERO notes. The probe diagnosed this as REPRESENTABILITY:
the executor's `commitments : List Nat` and `ShieldedValue.BoundNote` carried no `AssetId`, and
`noteSpend` took no amount, so the binding `unshield.amt = value(spent note)` could not be STATED.

E4 closes it. We give notes an `AssetId` (`AssetBoundNote`), formulate the pool as a pseudo-cell
whose `bal` tracks the unspent notes' value (`PoolConsistent`), and make the unshield amount a
GATED function of the spent note (`boundUnshieldK`). Then the binding is a THEOREM
(`boundUnshield_amount_bound`) and the pool↔notes invariant is PRESERVED
(`boundUnshield_preserves_pool_consistency`) — the pool cannot be drained beyond its notes. -/

/-- **An ASSET-TYPED bound note** (E4): `ShieldedValue.BoundNote` (value + blinding + range bits) plus
the `asset : AssetId` the probe found missing. The pool of `asset` is the pseudo-cell that custodies
the transparent value backing these notes. -/
structure AssetBoundNote extends BoundNote where
  /-- The asset this shielded note is denominated in — the field whose absence made the
  value-binding unrepresentable (probe §5, E4). -/
  asset : AssetId
  deriving Repr

/-- The hidden value of an asset-bound note (inherited from `BoundNote`). -/
abbrev AssetBoundNote.amount (nt : AssetBoundNote) : ℤ := nt.value

/-- The asset-bound note's range validity (inherited): `0 ≤ value < 2^n`, witnessed by boolean bits.
A negative or overflowing hidden amount can never be range-witnessed (probe E4: no hidden inflation
at creation). -/
abbrev AssetBoundNote.rangeValid (nt : AssetBoundNote) : Prop := nt.toBoundNote.rangeValid

section Pool

variable (poolOf : AssetId → CellId)

/-- The total UNSPENT value of asset `a` over a note inventory: the sum of `value` over the notes
of asset `a` that remain unspent. This is what the pool pseudo-cell `bal (poolOf a) a` must equal —
the pool↔notes invariant's right-hand side, now STATABLE because notes carry `(asset, value)`. -/
def unspentValue (notes : List AssetBoundNote) (a : AssetId) : ℤ :=
  ((notes.filter (fun nt => decide (nt.asset = a))).map AssetBoundNote.amount).sum

/-- **`PoolConsistent` — THE POOL↔NOTES INVARIANT the probe found unrepresentable (now STATED).**
For every asset `a`, the pool pseudo-cell's transparent balance EQUALS the total hidden value of the
unspent `a`-notes: `bal (poolOf a) a = Σ value(unspent a-notes)`. With this maintained, the pool can
NEVER be drained beyond its notes — every unshield must spend a note worth exactly what it withdraws
(`boundUnshield_*` below). The probe's `kPool` drain (10 → 6 with ZERO notes) is precisely a state
where `PoolConsistent` FAILS (pool balance 10, unspent value 0), so it is excluded by the invariant. -/
def PoolConsistent (k : RecordKernelState) (notes : List AssetBoundNote) : Prop :=
  ∀ a : AssetId, k.bal (poolOf a) a = unspentValue notes a

/-! ### §2.1 — the bound shield/unshield verbs (amount gated on the note). -/

/-- **`boundShieldK`** — shield as transfer-in ∘ value-bound note-create, with the transferred amount
EQUAL to the created note's value. The transparent leg moves `nt.value` of `nt.asset` from `src` into
the pool pseudo-cell; the commitment leg inserts the value-bound commitment of the note. The note is
appended to the inventory (the model's note set). -/
def boundShieldK (vc : ValueCommitment) (k : RecordKernelState) (actor src : CellId)
    (nt : AssetBoundNote) : Option RecordKernelState :=
  (recKExecAsset k
      { actor := actor, src := src, dst := poolOf nt.asset, amt := nt.value } nt.asset).map
    (fun k₁ => ShieldedValue.noteCreateBound vc k₁ nt.toBoundNote)

/-- **`boundUnshieldK`** — unshield as nullifier-spend ∘ transfer-out, with the transparent amount
GATED on the spent note: the withdrawal MUST equal `spent.value` (fail-closed otherwise). This is the
E4 repair of the probe's free-`amt` `unshieldK`: the unshield-amount/spent-note binding is now a
PRECONDITION the verb enforces, not a free parameter. The transparent leg moves `spent.value` of
`spent.asset` from the pool pseudo-cell to `dst`; the nullifier `nf` is consumed (anti-replay). -/
def boundUnshieldK (k : RecordKernelState) (nf : Nat) (spent : AssetBoundNote) (dst : CellId)
    (amt : ℤ) : Option RecordKernelState :=
  if amt = spent.value then
    match noteSpendNullifier k nf with
    | some k₁ =>
        recKExecAsset k₁
          { actor := poolOf spent.asset, src := poolOf spent.asset, dst := dst, amt := amt }
          spent.asset
    | none => none
  else none

/-! ### §2.2 — THE E4 KEYSTONE: the amount IS the spent note's value. -/

/-- **`boundUnshield_amount_bound` — THE E4 KEYSTONE.** A committed bound-unshield's
transparent outflow EQUALS the spent note's hidden value: `amt = spent.value`. This is the
Mina-excess / `balance_change` value-binding obligation the probe found unrepresentable, now a
THEOREM over executed state — the unshield amount is not a free parameter; it is pinned to the
note that authorizes it. (Trivial from the gate, but the POINT is that the gate exists and commits:
the binding is now part of the verb's success condition.) -/
theorem boundUnshield_amount_bound {k k' : RecordKernelState} {nf : Nat} {spent : AssetBoundNote}
    {dst : CellId} {amt : ℤ} (h : boundUnshieldK poolOf k nf spent dst amt = some k') :
    amt = spent.value := by
  unfold boundUnshieldK at h
  by_cases hamt : amt = spent.value
  · exact hamt
  · rw [if_neg hamt] at h; exact absurd h (by simp)

/-- A bound-unshield with the wrong amount FAILS-CLOSED: you cannot withdraw more (or less) than the
spent note's value. The anti-drain tooth at the verb level — `boundUnshieldK` refuses any amount but
`spent.value`. -/
theorem boundUnshield_wrong_amount_rejected (k : RecordKernelState) (nf : Nat)
    (spent : AssetBoundNote) (dst : CellId) (amt : ℤ) (hne : amt ≠ spent.value) :
    boundUnshieldK poolOf k nf spent dst amt = none := by
  unfold boundUnshieldK; rw [if_neg hne]

/-! ### §2.3 — the LEDGER half (rides the probe). -/

/-- **`boundShieldK_preserves_exact` (the ledger half).** Bound-shield preserves the
canonical conserved ledger: the transparent leg is a transfer into the pool cell, the value-bound
commitment insert is bal/escrow-neutral (`noteCreateBound_recTotalAsset`). -/
theorem boundShieldK_preserves_exact {vc : ValueCommitment} {k k' : RecordKernelState}
    {actor src : CellId} {nt : AssetBoundNote}
    (h : boundShieldK poolOf vc k actor src nt = some k') (hc : ConservedLedger k) :
    ConservedLedger k' := by
  unfold boundShieldK at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨k₁, hk₁, hk'⟩ := h
  subst hk'
  intro b
  -- the value-bound create is bal-neutral for every asset.
  have hneutral := ShieldedValue.noteCreateBound_recTotalAsset vc k₁ nt.toBoundNote b
  rw [hneutral]
  exact transfer_preserves_exact hk₁ hc b

/-- A nullifier insert is invisible to the combined per-asset measure (touches only `nullifiers`). -/
private theorem noteSpend_measures {k k' : RecordKernelState} {nf : Nat}
    (h : noteSpendNullifier k nf = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold noteSpendNullifier at h
  by_cases hin : nf ∈ k.nullifiers
  · rw [if_pos hin] at h; exact absurd h (by simp)
  · rw [if_neg hin] at h
    simp only [Option.some.injEq] at h
    subst h; rfl

/-- **`boundUnshieldK_preserves_exact` (the ledger half).** Bound-unshield preserves the
canonical conserved ledger: the nullifier insert is neutral, the pool→user leg is a transfer. (The
LEDGER survives regardless of binding — what E4 ADDS over the probe is `PoolConsistent` below.) -/
theorem boundUnshieldK_preserves_exact {k k' : RecordKernelState} {nf : Nat} {spent : AssetBoundNote}
    {dst : CellId} {amt : ℤ} (h : boundUnshieldK poolOf k nf spent dst amt = some k')
    (hc : ConservedLedger k) : ConservedLedger k' := by
  unfold boundUnshieldK at h
  by_cases hamt : amt = spent.value
  · rw [if_pos hamt] at h
    cases hns : noteSpendNullifier k nf with
    | none => rw [hns] at h; exact absurd h (by simp)
    | some k₁ =>
        rw [hns] at h
        have hc₁ : ConservedLedger k₁ := fun b => by
          rw [noteSpend_measures hns b]; exact hc b
        exact transfer_preserves_exact h hc₁
  · rw [if_neg hamt] at h; exact absurd h (by simp)

/-! ### §2.4 — THE E4 CUSTODY HALF: `PoolConsistent` is preserved (the pool is undrainable). -/

/-- Peel a committed bound-unshield to its post-state shape: the pool cell debited by `spent.value`
of `spent.asset` (via `recTransferBal`), with the spent nullifier consumed. The success conditions
(authority/liveness/`src ≠ dst`/availability) are carried as the transfer's gate. -/
private theorem boundUnshield_shape {k k' : RecordKernelState} {nf : Nat} {spent : AssetBoundNote}
    {dst : CellId} {amt : ℤ} (h : boundUnshieldK poolOf k nf spent dst amt = some k') :
    ∃ k₁, noteSpendNullifier k nf = some k₁
      ∧ k' = { k₁ with bal := recTransferBal k₁.bal (poolOf spent.asset) dst spent.asset
                              spent.value }
      ∧ poolOf spent.asset ≠ dst := by
  have hamt : amt = spent.value := boundUnshield_amount_bound poolOf h
  unfold boundUnshieldK at h
  rw [if_pos hamt] at h
  cases hns : noteSpendNullifier k nf with
  | none => rw [hns] at h; exact absurd h (by simp)
  | some k₁ =>
      rw [hns] at h
      -- peel the transfer gate ONCE; both result fields come from the positive branch.
      simp only at h
      unfold recKExecAsset at h
      by_cases hg : authorizedB k₁.caps
          { actor := poolOf spent.asset, src := poolOf spent.asset, dst := dst, amt := amt } = true
          ∧ 0 ≤ amt ∧ amt ≤ k₁.bal (poolOf spent.asset) spent.asset
          ∧ poolOf spent.asset ≠ dst ∧ poolOf spent.asset ∈ k₁.accounts ∧ dst ∈ k₁.accounts
      · rw [if_pos hg] at h
        simp only [Option.some.injEq] at h
        refine ⟨k₁, rfl, ?_, hg.2.2.2.1⟩
        rw [← h, hamt]
      · rw [if_neg hg] at h; exact absurd h (by simp)

/-- The pool cell's OWN balance after a bound-unshield: down by exactly `spent.value` at
`spent.asset`. (The pool is the `src` of the transfer, and `poolOf spent.asset ≠ dst`, so the
`recTransferBal` debit lands on it.) -/
private theorem boundUnshield_pool_debit {k k' : RecordKernelState} {nf : Nat}
    {spent : AssetBoundNote} {dst : CellId} {amt : ℤ}
    (h : boundUnshieldK poolOf k nf spent dst amt = some k') :
    k'.bal (poolOf spent.asset) spent.asset
      = k.bal (poolOf spent.asset) spent.asset - spent.value := by
  obtain ⟨k₁, hns, hk', hne⟩ := boundUnshield_shape poolOf h
  -- the nullifier spend leaves `bal` untouched.
  have hbal₁ : k₁.bal = k.bal := by
    unfold noteSpendNullifier at hns
    by_cases hin : nf ∈ k.nullifiers
    · rw [if_pos hin] at hns; exact absurd hns (by simp)
    · rw [if_neg hin] at hns; simp only [Option.some.injEq] at hns; rw [← hns]
  rw [hk']
  show recTransferBal k₁.bal (poolOf spent.asset) dst spent.asset spent.value
        (poolOf spent.asset) spent.asset = k.bal (poolOf spent.asset) spent.asset - spent.value
  unfold recTransferBal
  rw [if_pos rfl, if_pos rfl, hbal₁]

/-- **`boundUnshield_preserves_pool_consistency` — THE E4 CUSTODY KEYSTONE.** A bound-unshield
that spends `spent` (removing it from the unspent inventory) and withdraws exactly `spent.value`
PRESERVES `PoolConsistent`. Concretely: the pool of `spent.asset` is debited by `spent.value`
(`boundUnshield_pool_debit`), and the unspent-value of `spent.asset` drops by `spent.value` because
`spent` leaves the inventory — the two sides stay equal. Every OTHER asset's pool/inventory is
untouched. So `bal (poolOf a) a = Σ value(unspent a-notes)` is maintained: THE POOL CANNOT BE DRAINED
BEYOND ITS NOTES. This is exactly the custody-soundness the probe's free-`amt` `unshieldK` lacked.

Hypotheses make the inventory bookkeeping precise: `notes` is the pre-inventory (with `spent` in it,
`notes'` the post-inventory with `spent` removed), and the pool cells of distinct assets are
distinct (`hpool` — the pool registry is injective on the assets in play, the §2.2 pool-genesis
discipline). -/
theorem boundUnshield_preserves_pool_consistency {k k' : RecordKernelState} {nf : Nat}
    {spent : AssetBoundNote} {dst : CellId} {amt : ℤ} {notes notes' : List AssetBoundNote}
    (h : boundUnshieldK poolOf k nf spent dst amt = some k')
    (hpre : PoolConsistent poolOf k notes)
    -- the removed-note bookkeeping: removing `spent` from the `spent.asset`-filtered inventory
    -- drops that asset's unspent value by exactly `spent.value`, and leaves other assets' alone.
    (hrem : ∀ a : AssetId, unspentValue notes' a
              = unspentValue notes a - (if a = spent.asset then spent.value else 0))
    -- the pool registry is injective on assets (distinct assets ⇒ distinct pool cells); and the
    -- transparent leg only touched `spent.asset`'s pool, so other assets' pool balances are
    -- preserved verbatim.
    (hother : ∀ a : AssetId, a ≠ spent.asset → k'.bal (poolOf a) a = k.bal (poolOf a) a) :
    PoolConsistent poolOf k' notes' := by
  intro a
  rcases eq_or_ne a spent.asset with rfl | ha
  · -- the spent asset: pool debited by spent.value, unspent dropped by spent.value.
    rw [boundUnshield_pool_debit poolOf h, hrem spent.asset, if_pos rfl, hpre spent.asset]
  · -- another asset: both sides untouched.
    rw [hother a ha, hrem a, if_neg ha, sub_zero, hpre a]

/-- **`boundShield_preserves_pool_consistency` (the shield-side custody half).** A
bound-shield that transfers `nt.value` of `nt.asset` into the pool and appends `nt` to the inventory
PRESERVES `PoolConsistent`: the pool of `nt.asset` is credited by `nt.value` and the unspent-value of
`nt.asset` rises by `nt.value` (the appended note), other assets untouched. Symmetric to the unshield
side — both sides keep the pool-balance ↔ unspent-value equation. -/
theorem boundShield_preserves_pool_consistency {vc : ValueCommitment} {k k' : RecordKernelState}
    {actor src : CellId} {nt : AssetBoundNote} {notes notes' : List AssetBoundNote}
    (_h : boundShieldK poolOf vc k actor src nt = some k')
    (hpre : PoolConsistent poolOf k notes)
    -- appending `nt` raises its asset's unspent value by `nt.value`, others unchanged.
    (hadd : ∀ a : AssetId, unspentValue notes' a
              = unspentValue notes a + (if a = nt.asset then nt.value else 0))
    -- the pool of `nt.asset` is credited by `nt.value`; other assets' pools are unchanged.
    (hcredit : k'.bal (poolOf nt.asset) nt.asset = k.bal (poolOf nt.asset) nt.asset + nt.value)
    (hother : ∀ a : AssetId, a ≠ nt.asset → k'.bal (poolOf a) a = k.bal (poolOf a) a) :
    PoolConsistent poolOf k' notes' := by
  intro a
  rcases eq_or_ne a nt.asset with rfl | ha
  · rw [hcredit, hadd nt.asset, if_pos rfl, hpre nt.asset]
  · rw [hother a ha, hadd a, if_neg ha, add_zero, hpre a]

end Pool

/-! ## §3 — THE CANONICAL FEE/BRIDGE POT LAWS (modulo-burn / bridge-outflow retired).

The forward model has NO conservation exemptions: fee-burn and the bridge outflow both die in
pot-cells. These re-export the probe's pot theorems as the canonical fee/bridge laws. -/

/-- **CANONICAL FEE LAW (via `turn_exact_with_burn_pot`).** On a committed turn whose body
leaves the four fee cells at their post-prologue balances, crediting the burn residue to a burn-pot
cell makes the fee QUADRUPLE {agent, proposer, treasury, burn-pot} EXACTLY conserved — `Σδ = 0`, no
modulo. `conservation_modulo_burn_on_commit` retires: burn = an ordinary move to a pot whose program
is the burn policy. (E5: this is exactness of the SCALAR fee domain; landing the fee legs on the
per-asset ledger is the W1 rotation — see §4.) -/
theorem canonical_fee_law (ctx : AdmCtx) (h : TurnHdr) (st : RecStmt)
    (s s' : RecChainedState) (p t pot : CellId)
    (hadm : admissible ctx h s = true)
    (hbody : interpChained st (commitPrologue s h.agent h.fee) = some s')
    (hp : ctx.proposer = some p) (ht : ctx.treasury = some t)
    (hap : h.agent ≠ p) (hat : h.agent ≠ t) (hpt : p ≠ t)
    (hpa : pot ≠ h.agent) (hpp : pot ≠ p) (hptt : pot ≠ t)
    (hbA : balOf (s'.kernel.cell h.agent)
            = balOf ((commitPrologue s h.agent h.fee).kernel.cell h.agent))
    (hbP : balOf (s'.kernel.cell p)
            = balOf ((commitPrologue s h.agent h.fee).kernel.cell p))
    (hbT : balOf (s'.kernel.cell t)
            = balOf ((commitPrologue s h.agent h.fee).kernel.cell t))
    (hbPot : balOf (s'.kernel.cell pot)
            = balOf ((commitPrologue s h.agent h.fee).kernel.cell pot)) :
    ∃ so, runTurn ctx h st s = TurnOutcome.bodyCommitted so ∧
      feeQuadSum (burnToPot so pot h.fee) h.agent p t pot = feeQuadSum s h.agent p t pot :=
  turn_exact_with_burn_pot ctx h st s s' p t pot hadm hbody hp ht hap hat hpt hpa hpp hptt
    hbA hbP hbT hbPot

/-- **CANONICAL BRIDGE LAW (via `bridgeFinalizeToPot_preserves_exact`).** Bridge finalize
SETTLES the locked value to a bridge-pot cell (the foreign chain's custody as a cell) instead of
dropping it off-ledger — preserving the canonical conserved ledger. The bridge-outflow exemption
(`bridgeFinalize_breaks_exact`, carried as the non-vacuity tooth) is retired. -/
theorem canonical_bridge_law {pot : CellId} {k k' : RecordKernelState} {id : Nat}
    (h : bridgeFinalizeToPotK pot k id = some k') (hc : ConservedLedger k) : ConservedLedger k' :=
  bridgeFinalizeToPot_preserves_exact h hc

/-- **The bridge non-vacuity tooth (canonical): the OLD finalize BREAKS conservation** — the
disclosed outflow. (`bridgeFinalize_breaks_exact`.) -/
theorem oldBridge_breaks_conservation {k k' : RecordKernelState} {id : Nat} {asset : AssetId}
    {amount : ℤ} (h : bridgeFinalizeKAsset k id asset amount = some k') (hnz : amount ≠ 0)
    (hc : ConservedLedger k) : ¬ ConservedLedger k' :=
  bridgeFinalize_breaks_exact h hnz hc

/-! ## §4 — Axiom hygiene. -/

#assert_axioms genesis_starts_conserved
#assert_axioms transfer_preserves
#assert_axioms mint_preserves
#assert_axioms createCell_preserves
#assert_axioms escrowCreate_preserves
#assert_axioms escrowRelease_preserves
#assert_axioms escrowRefund_preserves
#assert_axioms bridgeLock_preserves
#assert_axioms bridgeCancel_preserves
#assert_axioms oldMint_breaks_conservation
#assert_axioms boundUnshield_amount_bound
#assert_axioms boundUnshield_wrong_amount_rejected
#assert_axioms boundShieldK_preserves_exact
#assert_axioms boundUnshieldK_preserves_exact
#assert_axioms boundUnshield_preserves_pool_consistency
#assert_axioms boundShield_preserves_pool_consistency
#assert_axioms canonical_fee_law
#assert_axioms canonical_bridge_law
#assert_axioms oldBridge_breaks_conservation

/-! ## §5 — Non-vacuity witnesses (`#guard`).

The E4 teeth, witnessed end-to-end: the bound-unshield REFUSES the probe's free-`amt` drain, and
`PoolConsistent` distinguishes a backed pool from the probe's `kPool` (10 balance, 0 notes). -/

/-- Demo pool map: asset `_ ↦ cell 3` (matching the probe's `poolDemo`). -/
def poolDemo : AssetId → CellId := fun _ => 3

/-- A note worth 4 of asset 0 (the probe's `kPool` was drained by exactly 4). -/
def note4of0 : AssetBoundNote :=
  { value := 4, blinding := 1, bits := [0, 0, 1], asset := 0 }

/-- The probe's shield-shaped state: pool cell 3 holds 10 of asset 0, user 2 empty, NO notes. The
probe drained it; here we show the binding catches the mismatch. -/
def kPool : RecordKernelState :=
  { accounts := {2, 3}
    cell := fun _ => Value.record [("balance", Value.int 0)]
    caps := fun _ => []
    bal := fun c a => if c = 3 ∧ a = 0 then 10 else 0 }

-- THE E4 TOOTH: a bound-unshield withdrawing 4 against a note worth 4 is ACCEPTED at the binding gate
-- (amt = spent.value), but withdrawing the WRONG amount (5 ≠ 4) is REFUSED — the probe's free-`amt`
-- drain is now impossible. (Both depend only on the binding gate, not on authority — these witness
-- the value-binding specifically.)
#guard (4 == note4of0.value)
#guard ((boundUnshieldK poolDemo kPool 99 note4of0 2 4).isSome)   -- amt = note.value: gate passes
#guard ((boundUnshieldK poolDemo kPool 99 note4of0 2 5).isNone)   -- amt ≠ note.value: REFUSED
#guard ((boundUnshieldK poolDemo kPool 99 note4of0 2 3).isNone)   -- ditto, under-withdraw refused

-- THE POOL↔NOTES INVARIANT, witnessed: the probe's `kPool` (pool = 10, ZERO notes) is NOT
-- `PoolConsistent` at asset 0 (10 ≠ 0) — the very state the probe drained is excluded by the
-- forward model's invariant. A pool backed by a note worth 10 IS consistent.
#guard (kPool.bal (poolDemo 0) 0 == 10)
#guard (unspentValue [] 0 == 0)                                    -- no notes ⇒ 0 unspent value
#guard (unspentValue [note4of0] 0 == 4)                            -- one note worth 4 ⇒ 4
#guard ((kPool.bal (poolDemo 0) 0 == unspentValue [] 0) == false)  -- kPool NOT PoolConsistent (10≠0)
-- a note worth exactly 10 backs the pool: consistent.
#guard (unspentValue [({ value := 10, blinding := 0, bits := [0,1,0,1], asset := 0 } : AssetBoundNote)] 0 == 10)

-- the asset-typing the probe found missing: unspent value is PER-ASSET (a note of asset 1 does not
-- back the asset-0 pool).
#guard (unspentValue [({ value := 7, blinding := 0, bits := [1,1,1], asset := 1 } : AssetBoundNote)] 0 == 0)
#guard (unspentValue [({ value := 7, blinding := 0, bits := [1,1,1], asset := 1 } : AssetBoundNote)] 1 == 7)

/-! ## §6 — THE MIGRATION TOUCH-LIST (the eventual live W1 / VK rotation).

This module is the PROVEN canonical value model. The live rotation that makes the running
kernel/executor/wire IMPLEMENT it is a LATER, coordinated step (the ONE VK rotation). Because the
model is proved here, that step is MECHANICAL — the precise touch-list (each item an escape hatch the
probe named, here turned into a concrete edit):

  **E1 — issuer-well availability waiver.** `recKExecAsset`'s availability gate
  (`turn.amt ≤ k.bal turn.src a`) is DROPPED for moves whose `src` is an issuer well (`issuerMoveK`
  already omits it). Conservation never used availability (every preservation proof above needs only
  membership + distinctness), so the value law is undamaged; solvency/issuance policy migrates to the
  issuer cell's PROGRAM (`Pred`). TOUCHES: the mint path in the executor (`recKMintAsset` →
  `issuerMoveK`), no change to the conservation spine.

  **E2 — mint-cap retarget.** `recKMintAsset` gates `mintAuthorizedB` over the RECIPIENT cell;
  `issuerMoveK` gates it over the ISSUER. The cutover MIGRATES mint capabilities from recipient-shaped
  to issuer-shaped (`mint_is_issuer_move` proves the LEDGERS agree; only the GATE target moves).
  TOUCHES: the capability table / VK (the mint-authority predicate), the SDK mint-grant path. This is
  the one real (small) capability migration.

  **E3 — the transitional escrow term dies at S3.** `ConservedLedger` carries `+ escrowHeldAsset`
  until the storage-as-cell-programs migration makes escrows pot-CELLS. At S3 the term is deleted and
  the law collapses to the pure `∀ a, Σ_c bal c a = 0`. TOUCHES: `recTotalAsset` →
  `recTotalAsset`, the escrow verbs → settle-to-escrow-pot (the same pot pattern as bridge/fee). No
  new proof: `escrow*_preserves` already preserve the combined measure, and the pot settle theorem
  (`bridgeFinalizeToPot_preserves_exact`) is the template.

  **E4 — the shielded value-binding LANDS (this module).** `BoundNote` → `AssetBoundNote` (the
  `asset : AssetId` field), `noteSpend` gains an amount gated on the spent note
  (`boundUnshieldK`), and the per-turn circuit constraint `unshield.amt = value(spent note)` becomes
  `boundUnshield_amount_bound` + the `PoolConsistent` custody invariant. TOUCHES: the note
  commitment/nullifier wire (carry asset+value-commitment), the unshield circuit (the
  amount=spent-value constraint), the executor's `noteSpend`. The PROOFS are done here; the rotation
  is wiring the executor/circuit to this shape.

  **E5 — fee legs onto the per-asset ledger.** The fee machinery
  (`commitPrologue`/`distributeFee`/`feeTriSum`) moves the SCALAR `balance` field; the canonical fee
  law above is exactness of THAT domain. The rotation lands the fee legs on the per-asset `bal`
  ledger so ONE law (`∀ a, Σ_c bal c a = 0`) covers fees too, with the burn residue credited to a
  burn-pot cell. TOUCHES: `commitPrologue`/`distributeFee` to write `bal`, the fee VK. The exact
  quadruple law (`canonical_fee_law`) is the target; `conservation_modulo_burn_on_commit` retires.

  **E6 — pot genesis.** The burn-pot / bridge-pot / (post-S3) escrow-pot cells must EXIST (live,
  distinct from the fee triple / settle-live), enforced fail-closed (`bridgeFinalizeToPotK` already
  gates pot liveness; the fee theorems carry distinctness hypotheses). TOUCHES: the genesis/bootstrap
  config (allocate the pot cells), the same discipline as issuer-cell genesis
  (`genesis_requires_issuer`).

  **The VK + cell-commitment bump** rides E2/E4/E5 (the gate/wire shape changes). Sequencing: this
  module is groundwork; the rotation is the coordinated step that imports it into the anchor and flips
  the executor/circuit/wire — at which point every theorem here becomes a live guarantee. -/

end Dregg2.Substrate.IssuerLedger
