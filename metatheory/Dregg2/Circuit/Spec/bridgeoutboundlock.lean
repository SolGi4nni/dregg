/-
# Dregg2.Circuit.Spec.bridgeoutboundlock — INDEPENDENT full-state spec + executor⟺spec for the
`bridge-outbound-lock` effect family (the `FullActionA.bridgeLockA` variant — Phase 1 of dregg1's
two-phase cross-chain bridge, `initiate_bridge`/`cell/src/note_bridge.rs`).

This is a LEAF module (imported by nothing; gated standalone). It is the `Transfer.lean` reference
pattern (`TransferSpec` + `recKExec_iff_spec` + `recTransfer_correct`) re-derived INDEPENDENTLY for
the bridge-outbound-LOCK effect that the unified action executor `execFullA` dispatches:

    execFullA s (.bridgeLockA id actor originator destination asset amount)
      = bridgeLockChainA s id actor originator destination asset amount      -- TurnExecutorFull:3549
    bridgeLockChainA s id actor originator destination asset amount
      = match bridgeLockKAsset s.kernel id actor originator destination asset amount with
        | some k' => some { kernel := k', log := escrowReceiptA actor :: s.log } | none => none

`bridgeLockKAsset` (`RecordKernel.lean:1720`) is the EXECUTABLE per-asset bridge lock. Its
admissibility guard is the conjunction (the REAL guard the executor checks — RICHER than the brief
"authorizedB + freshness + availability + originator∈accounts" sketch: it ALSO checks
non-negativity AND lifecycle-liveness of the debited originator, the D3 fail-closed teeth):

    authorizedB caps {actor, src:=originator, dst:=destination, amt:=amount} = true  -- (1) AUTHORITY
  ∧ 0 ≤ amount                                                                        -- (2) NON-NEGATIVITY
  ∧ amount ≤ k.bal originator asset                                                   -- (3) AVAILABILITY in asset
  ∧ originator ∈ k.accounts                                                           -- (4) ORIGINATOR LIVENESS (membership)
  ∧ cellLifecycleLive k originator = true                                            -- (5) ORIGINATOR LIVENESS (lifecycle, D3)
  ∧ ¬ (∃ r ∈ k.escrows, r.id = id)                                                  -- (6) ID FRESHNESS (dregg1 `AlreadyLocked`)

and on commit it produces `createBridgeRawAsset` (`RecordKernel.lean:1701`):
  * `bal` ledger: a SINGLE-cell, single-asset DEBIT of `amount` from `(originator, asset)`
    (`recBalCreditCell k.bal originator asset (-amount)`),
  * `escrows` store: PREPEND an unresolved, `bridge := true`-tagged `EscrowRecord {id,
    creator:=originator, recipient:=destination, amount, resolved:=false, asset, bridge:=true}`,
  * EVERY OTHER kernel field (15 of them) and the chained `log` (advanced by `escrowReceiptA actor ::`)
    are the FRAME.

## What is proved (the apex reference truth, BOTH directions)

  * `BridgeOutboundLockSpec st id actor originator destination asset amount st'` — the INDEPENDENT
    declarative full-state post-condition: the admissibility guard, the EXACT post-`bal` ledger
    (`recBalCreditCell … (-amount)`), the EXACT post-`escrows` store (the prepended unresolved
    bridge-tagged record), the chained `log` advanced by exactly `escrowReceiptA actor ::`, AND the
    FRAME — every one of the 15 OTHER RecordKernelState components LITERALLY unchanged (`accounts cell
    caps nullifiers revoked commitments queues swiss slotCaveats factories lifecycle deathCert
    delegate delegations sealedBoxes`). No frame clause mentions the executor. Missing ANY field
    reintroduces a ghost — all 17 kernel components + log are enumerated.

  * `createBridgeKAsset_correct` — the post-state helper (`createBridgeRawAsset`) validated
    DECLARATIVELY (the `bal` debit at `(originator,asset)`, the other-`(cell,asset)` ledger-frame, the
    `escrows` prepend of the bridge-tagged record), so the spec's `bal`/`escrows` clauses genuinely
    encode debit ∧ ledger-frame ∧ park-bridge-record rather than blind trust.

  * `bridgeLockChainA_iff_spec` — the ⟺ stated on the chained step `bridgeLockChainA`.
  * `execFullA_bridgeLockA_iff_spec` — execFullA ⟺ spec for the `bridgeLockA` variant (BOTH
    directions). The `→` VALIDATES the executor against the independent spec (all 17 kernel fields +
    log are checked, so a silently mutated field would make the proof FAIL); `←` reconstructs.

  * Post-state corollaries: `bridgeLock_debit` (per-asset debit at `(originator,asset)`),
    `bridgeLock_other_untouched` (per-asset ledger frame), `bridgeLock_parks_record` (the bridge-tagged
    record prepended).

  * Non-vacuity: `…_rejects_unauthorized`, `…_rejects_negative`, `…_rejects_overdraft`,
    `…_rejects_dead_originator`, `…_rejects_nonlive_originator`, `…_rejects_id_reuse` — each forged
    input fails a guard leg ⇒ the executor returns `none` ⇒ no spec post-state exists. A spec that
    accepts everything would be worthless.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Tactics

namespace Dregg2.Circuit.Spec.BridgeOutboundLock

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

/-! ## §1 — the admissibility guard (the `bridgeLockKAsset` `if`, extracted as a `Prop`).

Exactly the six conjuncts `bridgeLockKAsset` (`RecordKernel.lean:1720`) checks before it commits. The
AVAILABILITY conjunct reads the GENUINE per-asset ledger `k.bal originator asset`; the lock checks
ORIGINATOR liveness BOTH as membership (`∈ accounts`) and lifecycle (`cellLifecycleLive = true`, the
D3 fail-closed teeth — a Sealed/Destroyed but still-member cell cannot have value locked out of it),
plus an ID-FRESHNESS leg (dregg1's `AlreadyLocked` double-lock rejection). -/

/-- The full per-asset bridge-outbound-lock admissibility guard `bridgeLockKAsset` checks, as a
`Prop`. -/
def lockGuard (k : RecordKernelState) (id : Nat) (actor originator destination : CellId)
    (asset : AssetId) (amount : ℤ) : Prop :=
  authorizedB k.caps { actor := actor, src := originator, dst := destination, amt := amount } = true
    ∧ 0 ≤ amount ∧ amount ≤ k.bal originator asset ∧ originator ∈ k.accounts
    ∧ cellLifecycleLive k originator = true
    ∧ ¬ (∃ r ∈ k.escrows, r.id = id)

/-- The unresolved, BRIDGE-tagged `EscrowRecord` a lock parks (its declarative form, mirroring the
executor's literal). Stated HERE so the spec's `escrows` clause does not reference the executor's
body. The `bridge := true` tag is what distinguishes a bridge lock's resolution semantics (a finalize
BURNS for the other chain) from an ordinary escrow's (a release/refund SETTLES back). -/
def parkedBridgeRecord (id : Nat) (originator destination : CellId) (asset : AssetId) (amount : ℤ) :
    EscrowRecord :=
  { id := id, creator := originator, recipient := destination,
    amount := amount, resolved := false, asset := asset, bridge := true }

/-! ## §2 — the post-state helper, validated DECLARATIVELY.

`createBridgeRawAsset` (`RecordKernel.lean:1701`) is the post-state the executor installs on commit. We
pin EXACTLY what it does — debit `(originator,asset)` by `amount` on the `bal` ledger (leaving every
other `(cell,asset)` untouched) and PREPEND the unresolved bridge-tagged record onto `escrows` — so the
spec's `bal`/`escrows` clauses are genuine debit ∧ ledger-frame ∧ park-bridge-record, not blind
trust. -/

/-- **`createBridgeKAsset_correct`** — the lock post-state helper validated declaratively: the lock
debits `(originator,asset)` by `amount`, leaves every other `(cell,asset)` ledger entry untouched, and
prepends exactly the unresolved bridge-tagged record onto the holding-store. -/
theorem createBridgeKAsset_correct (k : RecordKernelState) (id : Nat) (originator destination : CellId)
    (asset : AssetId) (amount : ℤ) :
    (createBridgeRawAsset k id originator destination asset amount).bal originator asset
        = k.bal originator asset - amount
    ∧ (∀ c b, ¬ (c = originator ∧ b = asset) →
        (createBridgeRawAsset k id originator destination asset amount).bal c b = k.bal c b)
    ∧ (createBridgeRawAsset k id originator destination asset amount).escrows
        = parkedBridgeRecord id originator destination asset amount :: k.escrows := by
  refine ⟨?_, ?_, rfl⟩
  · show recBalCreditCell k.bal originator asset (-amount) originator asset
        = k.bal originator asset - amount
    unfold recBalCreditCell
    rw [if_pos ⟨rfl, rfl⟩]; ring
  · intro c b hcd
    show recBalCreditCell k.bal originator asset (-amount) c b = k.bal c b
    unfold recBalCreditCell
    rw [if_neg hcd]

/-! ## §3 — FULL-STATE SEMANTIC SPEC (the INDEPENDENT reference) + executor⟺spec.

`BridgeOutboundLockSpec` is the COMPLETE declarative post-state of a committed `bridgeLockA`,
written INDEPENDENTLY of the executor: the guard holds; the post-`bal` ledger is the single-cell
single-asset debit; the post-`escrows` store is the prepended unresolved bridge-tagged record; the
chained `log` advances by exactly `escrowReceiptA actor ::`; and EVERY OTHER state component — all 15
non-`bal`, non-`escrows` RecordKernelState fields — is LITERALLY unchanged (the FRAME). No frame clause
references `bridgeLockChainA`/`bridgeLockKAsset`/`createBridgeRawAsset`'s executor terms. -/

/-- **The full-state declarative spec of a committed `bridgeLockA`** — the INDEPENDENT reference
semantics. The guard holds (`lockGuard`); the post-`bal` ledger debits `(originator,asset)` by `amount`
(`recBalCreditCell`, validated by `createBridgeKAsset_correct`); the post-`escrows` store is
`parkedBridgeRecord :: st.escrows`; the chained `log` is `escrowReceiptA actor :: st.log`; and every one
of the 15 other RecordKernelState components is unchanged. -/
def BridgeOutboundLockSpec (st : RecChainedState) (id : Nat) (actor originator destination : CellId)
    (asset : AssetId) (amount : ℤ) (st' : RecChainedState) : Prop :=
  lockGuard st.kernel id actor originator destination asset amount
  ∧ st'.kernel.bal = recBalCreditCell st.kernel.bal originator asset (-amount)
  ∧ st'.kernel.escrows = parkedBridgeRecord id originator destination asset amount :: st.kernel.escrows
  ∧ st'.log = escrowReceiptA actor :: st.log
  -- THE FRAME: every non-`bal`, non-`escrows` RecordKernelState field, literally unchanged (15).
  ∧ st'.kernel.accounts = st.kernel.accounts
  ∧ st'.kernel.cell = st.kernel.cell
  ∧ st'.kernel.caps = st.kernel.caps
  ∧ st'.kernel.nullifiers = st.kernel.nullifiers
  ∧ st'.kernel.revoked = st.kernel.revoked
  ∧ st'.kernel.commitments = st.kernel.commitments
  ∧ st'.kernel.queues = st.kernel.queues
  ∧ st'.kernel.swiss = st.kernel.swiss
  ∧ st'.kernel.slotCaveats = st.kernel.slotCaveats
  ∧ st'.kernel.factories = st.kernel.factories
  ∧ st'.kernel.lifecycle = st.kernel.lifecycle
  ∧ st'.kernel.deathCert = st.kernel.deathCert
  ∧ st'.kernel.delegate = st.kernel.delegate
  ∧ st'.kernel.delegations = st.kernel.delegations
  ∧ st'.kernel.sealedBoxes = st.kernel.sealedBoxes

/-- **`bridgeLockChainA_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions)** on the chained
bridge-lock step. `bridgeLockChainA` commits a lock into `st'` IFF `st'` is EXACTLY the spec'd full
post-state. The `→` VALIDATES `bridgeLockChainA` against the independent spec — all 17 kernel
components (`bal` + `escrows` + the 15 frame fields) AND the log are checked, so a silently mutated
field would make the proof FAIL; the `←` reconstructs the committed state from the spec. -/
theorem bridgeLockChainA_iff_spec (st : RecChainedState) (id : Nat)
    (actor originator destination : CellId) (asset : AssetId) (amount : ℤ) (st' : RecChainedState) :
    bridgeLockChainA st id actor originator destination asset amount = some st'
      ↔ BridgeOutboundLockSpec st id actor originator destination asset amount st' := by
  unfold bridgeLockChainA BridgeOutboundLockSpec lockGuard
  unfold bridgeLockKAsset
  by_cases hg : authorizedB st.kernel.caps
        { actor := actor, src := originator, dst := destination, amt := amount } = true
      ∧ 0 ≤ amount ∧ amount ≤ st.kernel.bal originator asset ∧ originator ∈ st.kernel.accounts
      ∧ cellLifecycleLive st.kernel originator = true
      ∧ ¬ (∃ r ∈ st.kernel.escrows, r.id = id)
  · rw [if_pos hg]
    simp only [createBridgeRawAsset, parkedBridgeRecord]
    constructor
    · intro h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rintro ⟨_, hbal, hesc, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
      -- reconstruct st' from the spec: its kernel matches the lock post-state field-by-field,
      -- and its log matches `escrowReceiptA actor :: st.log`.
      obtain ⟨k', l'⟩ := st'
      obtain ⟨acc, cell, caps, esc, nul, rev, com, bal, q, sw, sc, fac, lc, dc, dg, dgs, sb⟩ := k'
      simp only at hbal hesc hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
      subst hbal hesc hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
      rfl
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hg', _⟩; exact absurd hg' hg

/-- **`execFullA_bridgeLockA_iff_spec` — the UNIFIED-ACTION executor corner.** `execFullA` dispatches
`.bridgeLockA …` to `bridgeLockChainA s …`, so committing the unified action into `st'` is EXACTLY the
full-state spec. This is the variant-level executor⟺spec. -/
theorem execFullA_bridgeLockA_iff_spec (st : RecChainedState) (id : Nat)
    (actor originator destination : CellId) (asset : AssetId) (amount : ℤ) (st' : RecChainedState) :
    execFullA st (.bridgeLockA id actor originator destination asset amount) = some st'
      ↔ BridgeOutboundLockSpec st id actor originator destination asset amount st' := by
  show bridgeLockChainA st id actor originator destination asset amount = some st'
        ↔ BridgeOutboundLockSpec st id actor originator destination asset amount st'
  exact bridgeLockChainA_iff_spec st id actor originator destination asset amount st'

/-! ## §4 — the post-state facts a committed step produces (debit / park / ledger-frame corollaries).

These read off `BridgeOutboundLockSpec` + `createBridgeKAsset_correct` to expose the genuine effect
(the per-asset debit at `(originator,asset)`, the parked bridge-tagged record, the untouched other
ledger entries). -/

/-- **`bridgeLock_debit`** — a committed lock debits the originator's asset-`asset` ledger by `amount`
(the value parked off-ledger into the bridge holding-store, now INACCESSIBLE awaiting the other
chain). -/
theorem bridgeLock_debit (st : RecChainedState) (id : Nat) (actor originator destination : CellId)
    (asset : AssetId) (amount : ℤ) (st' : RecChainedState)
    (h : execFullA st (.bridgeLockA id actor originator destination asset amount) = some st') :
    st'.kernel.bal originator asset = st.kernel.bal originator asset - amount := by
  obtain ⟨_, hbal, _⟩ :=
    (execFullA_bridgeLockA_iff_spec st id actor originator destination asset amount st').mp h
  rw [hbal]
  exact (createBridgeKAsset_correct st.kernel id originator destination asset amount).1

/-- **`bridgeLock_other_untouched`** — a committed lock leaves every other `(cell,asset)` ledger entry
untouched (the per-asset ledger frame — no cross-cell or cross-asset laundering at the lock). -/
theorem bridgeLock_other_untouched (st : RecChainedState) (id : Nat)
    (actor originator destination : CellId) (asset : AssetId) (amount : ℤ) (st' : RecChainedState)
    (h : execFullA st (.bridgeLockA id actor originator destination asset amount) = some st')
    (c : CellId) (b : AssetId) (hcd : ¬ (c = originator ∧ b = asset)) :
    st'.kernel.bal c b = st.kernel.bal c b := by
  obtain ⟨_, hbal, _⟩ :=
    (execFullA_bridgeLockA_iff_spec st id actor originator destination asset amount st').mp h
  rw [hbal]
  exact (createBridgeKAsset_correct st.kernel id originator destination asset amount).2.1 c b hcd

/-- **`bridgeLock_parks_record`** — a committed lock prepends exactly the unresolved bridge-tagged
record onto the holding-store (the off-ledger lock awaiting the other-chain confirmation). -/
theorem bridgeLock_parks_record (st : RecChainedState) (id : Nat)
    (actor originator destination : CellId) (asset : AssetId) (amount : ℤ) (st' : RecChainedState)
    (h : execFullA st (.bridgeLockA id actor originator destination asset amount) = some st') :
    st'.kernel.escrows = parkedBridgeRecord id originator destination asset amount :: st.kernel.escrows := by
  obtain ⟨_, _, hesc, _⟩ :=
    (execFullA_bridgeLockA_iff_spec st id actor originator destination asset amount st').mp h
  exact hesc

/-! ## §5 — NON-VACUITY: the executor REJECTS bad inputs (each guard leg, fail-closed).

A spec a worthless executor could meet (accept everything) would be vacuous. Here each forged input
fails a guard conjunct ⇒ `execFullA st (.bridgeLockA …) = none` ⇒ no spec post-state exists. -/

/-- **`bridgeLock_rejects_unauthorized` — PROVED.** An unauthorized actor's lock does NOT commit (the
AUTHORITY leg fails) ⇒ no `st'` satisfies the spec. -/
theorem bridgeLock_rejects_unauthorized (st : RecChainedState) (id : Nat)
    (actor originator destination : CellId) (asset : AssetId) (amount : ℤ)
    (hbad : authorizedB st.kernel.caps
        { actor := actor, src := originator, dst := destination, amt := amount } = false) :
    execFullA st (.bridgeLockA id actor originator destination asset amount) = none := by
  show bridgeLockChainA st id actor originator destination asset amount = none
  unfold bridgeLockChainA bridgeLockKAsset
  rw [if_neg (by rw [hbad]; rintro ⟨h, _⟩; exact absurd h (by simp))]

/-- **`bridgeLock_rejects_negative` — PROVED.** A negative-amount lock does NOT commit (the
NON-NEGATIVITY leg fails) — no value can be conjured by a negative bridge lock. -/
theorem bridgeLock_rejects_negative (st : RecChainedState) (id : Nat)
    (actor originator destination : CellId) (asset : AssetId) (amount : ℤ)
    (hbad : ¬ 0 ≤ amount) :
    execFullA st (.bridgeLockA id actor originator destination asset amount) = none := by
  show bridgeLockChainA st id actor originator destination asset amount = none
  unfold bridgeLockChainA bridgeLockKAsset
  rw [if_neg (by rintro ⟨_, h, _⟩; exact hbad h)]

/-- **`bridgeLock_rejects_overdraft` — PROVED.** A lock of more than the originator holds in asset
`asset` (`¬ amount ≤ k.bal originator asset`) does NOT commit (the AVAILABILITY leg fails). -/
theorem bridgeLock_rejects_overdraft (st : RecChainedState) (id : Nat)
    (actor originator destination : CellId) (asset : AssetId) (amount : ℤ)
    (hbad : ¬ amount ≤ st.kernel.bal originator asset) :
    execFullA st (.bridgeLockA id actor originator destination asset amount) = none := by
  show bridgeLockChainA st id actor originator destination asset amount = none
  unfold bridgeLockChainA bridgeLockKAsset
  rw [if_neg (by rintro ⟨_, _, h, _⟩; exact hbad h)]

/-- **`bridgeLock_rejects_dead_originator` — PROVED.** A lock out of a non-account originator does NOT
commit (the ORIGINATOR-MEMBERSHIP leg fails). -/
theorem bridgeLock_rejects_dead_originator (st : RecChainedState) (id : Nat)
    (actor originator destination : CellId) (asset : AssetId) (amount : ℤ)
    (hbad : originator ∉ st.kernel.accounts) :
    execFullA st (.bridgeLockA id actor originator destination asset amount) = none := by
  show bridgeLockChainA st id actor originator destination asset amount = none
  unfold bridgeLockChainA bridgeLockKAsset
  rw [if_neg (by rintro ⟨_, _, _, h, _⟩; exact hbad h)]

/-- **`bridgeLock_rejects_nonlive_originator` — PROVED (the D3 fail-closed teeth).** A lock out of a
Sealed/Destroyed originator (`cellLifecycleLive = false`) does NOT commit — even if it is still a
member, a frozen cell cannot have value locked out of it. -/
theorem bridgeLock_rejects_nonlive_originator (st : RecChainedState) (id : Nat)
    (actor originator destination : CellId) (asset : AssetId) (amount : ℤ)
    (hbad : cellLifecycleLive st.kernel originator = false) :
    execFullA st (.bridgeLockA id actor originator destination asset amount) = none := by
  show bridgeLockChainA st id actor originator destination asset amount = none
  unfold bridgeLockChainA
  rw [bridgeLockKAsset_nonlive_fails hbad]

/-- **`bridgeLock_rejects_id_reuse` — PROVED.** A lock whose `id` is ALREADY in use does NOT commit
(the ID-FRESHNESS leg fails — dregg1's `AlreadyLocked` double-lock rejection). Locks cannot collide on
the holding-store key. -/
theorem bridgeLock_rejects_id_reuse (st : RecChainedState) (id : Nat)
    (actor originator destination : CellId) (asset : AssetId) (amount : ℤ)
    (hbad : ∃ r ∈ st.kernel.escrows, r.id = id) :
    execFullA st (.bridgeLockA id actor originator destination asset amount) = none := by
  show bridgeLockChainA st id actor originator destination asset amount = none
  unfold bridgeLockChainA bridgeLockKAsset
  rw [if_neg (by rintro ⟨_, _, _, _, _, h⟩; exact h hbad)]

/-! ## §6 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms createBridgeKAsset_correct
#assert_axioms bridgeLockChainA_iff_spec
#assert_axioms execFullA_bridgeLockA_iff_spec
#assert_axioms bridgeLock_debit
#assert_axioms bridgeLock_other_untouched
#assert_axioms bridgeLock_parks_record
#assert_axioms bridgeLock_rejects_unauthorized
#assert_axioms bridgeLock_rejects_negative
#assert_axioms bridgeLock_rejects_overdraft
#assert_axioms bridgeLock_rejects_dead_originator
#assert_axioms bridgeLock_rejects_nonlive_originator
#assert_axioms bridgeLock_rejects_id_reuse

end Dregg2.Circuit.Spec.BridgeOutboundLock
