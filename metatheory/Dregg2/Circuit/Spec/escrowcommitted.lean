/-
# Dregg2.Circuit.Spec.escrowcommitted — INDEPENDENT full-state spec + executor⟺spec for the
`escrow-committed` (PRIVACY-escrow) effect family: `FullActionA.createCommittedEscrowA` /
`.releaseCommittedEscrowA` / `.refundCommittedEscrowA`.

This is a LEAF module (imported by nothing; gated standalone). It is the `Transfer.lean` reference
pattern (`TransferSpec` + `recKExec_iff_spec` + `recTransfer_correct`) re-derived INDEPENDENTLY for
the §8-portal-GATED committed-escrow effects that the unified action executor `execFullA` dispatches:

    execFullA s (.createCommittedEscrowA id actor creator recipient asset amount hidingProof)
      = createCommittedEscrowChainA s id actor creator recipient asset amount hidingProof  -- :3543
    createCommittedEscrowChainA s id actor creator recipient asset amount hidingProof          -- :2965
      = if hidingProof = true then createEscrowChainA s id actor creator recipient asset amount
        else none
    createEscrowChainA s id actor creator recipient asset amount                                -- :1986
      = match createEscrowKAsset s.kernel id actor creator recipient asset amount with
        | some k' => some { kernel := k', log := escrowReceiptA actor :: s.log } | none => none

    execFullA s (.releaseCommittedEscrowA id actor) = releaseEscrowChainA s id actor             -- :3545
    execFullA s (.refundCommittedEscrowA  id actor) = refundEscrowChainA  s id actor             -- :3546

So the committed-escrow create is the plain per-asset escrow lock (`createEscrowKAsset`,
`RecordKernel.lean:1490`) UNDER an ADDED §8 hiding-portal gate `hidingProof = true` (the executable
boolean shadow of the Pedersen range/opening proof, dregg1 `apply.rs:2125`) — FAIL-CLOSED when the
portal fails, the privacy boundary the plain escrow lacks. The release/refund variants are
dispatch-ALIASED to the plain per-asset escrow settle (`settleEscrowRawAsset`, `RecordKernel.lean:1481`).

## The create admissibility guard (the §8 portal ∧ the per-asset lock guard)

    hidingProof = true                                                            -- (0) §8 HIDING PORTAL
  ∧ authorizedB caps {actor, src:=creator, dst:=recipient, amt:=amount} = true    -- (1) AUTHORITY
  ∧ 0 ≤ amount                                                                     -- (2) NON-NEGATIVITY
  ∧ amount ≤ k.bal creator asset                                                   -- (3) AVAILABILITY in asset
  ∧ creator ∈ k.accounts                                                           -- (4) CREATOR LIVENESS
  ∧ ¬ (∃ r ∈ k.escrows, r.id = id)                                               -- (5) ID FRESHNESS

and on commit it produces `createEscrowRawAsset` (`RecordKernel.lean:1471`):
  * `bal` ledger: a SINGLE-cell, single-asset DEBIT of `amount` from `(creator, asset)`,
  * `escrows` store: PREPEND an unresolved `EscrowRecord {id, creator, recipient, amount,
    resolved:=false, asset}`,
  * EVERY OTHER kernel field (15 of them) and the chained `log` (advanced by `escrowReceiptA actor ::`)
    are the FRAME.

## What is proved (the apex reference truth, BOTH directions)

  * `CommittedEscrowCreateSpec` — the INDEPENDENT declarative full-state post-condition: the §8 portal
    ∧ the per-asset lock guard, the EXACT post-`bal` ledger (`recBalCreditCell … (-amount)`), the EXACT
    post-`escrows` store (the prepended unresolved record), the chained `log` advanced by exactly
    `escrowReceiptA actor ::`, AND the FRAME — every one of the 15 OTHER RecordKernelState components
    LITERALLY unchanged. No frame clause mentions the executor. All 17 kernel components + log enumerated.
  * `createCommittedEscrowKAsset_correct` — the post-state helper (`createEscrowRawAsset`) validated
    DECLARATIVELY (the `bal` debit at `(creator,asset)`, the other-`(cell,asset)` ledger-frame, the
    `escrows` prepend).
  * `createCommittedEscrowChainA_iff_spec` — the ⟺ on the chained step.
  * `execFullA_createCommittedEscrowA_iff_spec` — execFullA ⟺ spec for the create variant (BOTH
    directions). The `→` VALIDATES the executor against the independent spec (all 17 kernel fields + log
    are checked, so a silently mutated field would make the proof FAIL); `←` reconstructs.
  * `CommittedEscrowReleaseSpec` / `CommittedEscrowRefundSpec` + their `execFullA_…_iff_spec` — the
    settle variants' INDEPENDENT full-state specs (find the unresolved record by id, the target+lifecycle
    gate, the single-cell credit + mark-resolved, the FRAME, the log advance), proved BOTH directions.
  * Non-vacuity: the create's PRIVACY-BOUNDARY teeth (`…_rejects_no_hiding`) plus each lock-guard leg
    (`…_rejects_unauthorized`/`…_rejects_negative`/`…_rejects_overdraft`/`…_rejects_dead_creator`/
    `…_rejects_id_reuse`), and the settle's `…_rejects_missing_record`.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Tactics

namespace Dregg2.Circuit.Spec.EscrowCommitted

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

/-! ## §1 — the CREATE admissibility guard (§8 portal ∧ the `createEscrowKAsset` `if`).

Exactly the §8 hiding portal `hidingProof = true` (`createCommittedEscrowChainA`'s added `if`,
`TurnExecutorFull.lean:2965`) CONJOINED with the five conjuncts `createEscrowKAsset`
(`RecordKernel.lean:1490`) checks. The portal is the leg plain escrow LACKS — the committed variant is
not byte-identical to plain escrow. -/

/-- The full committed-escrow-create admissibility guard, as a `Prop`: the §8 hiding portal AND the
per-asset lock guard. -/
def createGuard (k : RecordKernelState) (id : Nat) (actor creator recipient : CellId)
    (asset : AssetId) (amount : ℤ) (hidingProof : Bool) : Prop :=
  hidingProof = true
    ∧ authorizedB k.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true
    ∧ 0 ≤ amount ∧ amount ≤ k.bal creator asset ∧ creator ∈ k.accounts
    ∧ ¬ (∃ r ∈ k.escrows, r.id = id)

/-- The unresolved `EscrowRecord` a create parks (its declarative form, mirroring the executor's
literal). Stated HERE so the spec's `escrows` clause does not reference the executor's body. -/
def parkedRecord (id : Nat) (creator recipient : CellId) (asset : AssetId) (amount : ℤ) :
    EscrowRecord :=
  { id := id, creator := creator, recipient := recipient,
    amount := amount, resolved := false, asset := asset }

/-! ## §2 — the create post-state helper, validated DECLARATIVELY.

`createEscrowRawAsset` (`RecordKernel.lean:1471`) is the post-state the committed create installs once
the portal discharges. We pin EXACTLY what it does — debit `(creator,asset)` by `amount` on the `bal`
ledger (leaving every other `(cell,asset)` untouched) and PREPEND the unresolved record onto `escrows`
— so the spec's `bal`/`escrows` clauses are genuine debit ∧ ledger-frame ∧ park-record. -/

/-- **`createCommittedEscrowKAsset_correct`** — the create post-state helper validated declaratively:
the lock debits `(creator,asset)` by `amount`, leaves every other `(cell,asset)` ledger entry
untouched, and prepends exactly the unresolved record onto the holding-store. -/
theorem createCommittedEscrowKAsset_correct (k : RecordKernelState) (id : Nat)
    (creator recipient : CellId) (asset : AssetId) (amount : ℤ) :
    (createEscrowRawAsset k id creator recipient asset amount).bal creator asset
        = k.bal creator asset - amount
    ∧ (∀ c b, ¬ (c = creator ∧ b = asset) →
        (createEscrowRawAsset k id creator recipient asset amount).bal c b = k.bal c b)
    ∧ (createEscrowRawAsset k id creator recipient asset amount).escrows
        = parkedRecord id creator recipient asset amount :: k.escrows := by
  refine ⟨?_, ?_, rfl⟩
  · show recBalCreditCell k.bal creator asset (-amount) creator asset = k.bal creator asset - amount
    unfold recBalCreditCell
    rw [if_pos ⟨rfl, rfl⟩]; ring
  · intro c b hcd
    show recBalCreditCell k.bal creator asset (-amount) c b = k.bal c b
    unfold recBalCreditCell
    rw [if_neg hcd]

/-! ## §3 — FULL-STATE SEMANTIC SPEC of the CREATE (the INDEPENDENT reference) + executor⟺spec.

`CommittedEscrowCreateSpec` is the COMPLETE declarative post-state of a committed
`createCommittedEscrowA`, written INDEPENDENTLY of the executor: the §8 portal AND the lock guard hold;
the post-`bal` ledger is the single-cell single-asset debit; the post-`escrows` store is the prepended
unresolved record; the chained `log` advances by exactly `escrowReceiptA actor ::`; and EVERY OTHER
state component — all 15 non-`bal`, non-`escrows` RecordKernelState fields — is LITERALLY unchanged (the
FRAME). No frame clause references the executor's terms. -/

/-- **The full-state declarative spec of a committed `createCommittedEscrowA`** — the INDEPENDENT
reference semantics. The §8 hiding portal AND the lock guard hold (`createGuard`); the post-`bal` ledger
debits `(creator,asset)` by `amount`; the post-`escrows` store is `parkedRecord :: st.escrows`; the
chained `log` is `escrowReceiptA actor :: st.log`; and every one of the 15 other RecordKernelState
components is unchanged. -/
def CommittedEscrowCreateSpec (st : RecChainedState) (id : Nat) (actor creator recipient : CellId)
    (asset : AssetId) (amount : ℤ) (hidingProof : Bool) (st' : RecChainedState) : Prop :=
  createGuard st.kernel id actor creator recipient asset amount hidingProof
  ∧ st'.kernel.bal = recBalCreditCell st.kernel.bal creator asset (-amount)
  ∧ st'.kernel.escrows = parkedRecord id creator recipient asset amount :: st.kernel.escrows
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

/-- **`createCommittedEscrowChainA_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions)** on the
chained committed-escrow-create step. `createCommittedEscrowChainA` commits a lock into `st'` IFF `st'`
is EXACTLY the spec'd full post-state. The `→` VALIDATES the executor against the independent spec —
the §8 portal, all 17 kernel components (`bal` + `escrows` + the 15 frame fields) AND the log are
checked, so a silently mutated field would make the proof FAIL; the `←` reconstructs. -/
theorem createCommittedEscrowChainA_iff_spec (st : RecChainedState) (id : Nat)
    (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ) (hidingProof : Bool)
    (st' : RecChainedState) :
    createCommittedEscrowChainA st id actor creator recipient asset amount hidingProof = some st'
      ↔ CommittedEscrowCreateSpec st id actor creator recipient asset amount hidingProof st' := by
  unfold createCommittedEscrowChainA CommittedEscrowCreateSpec createGuard
  by_cases hp : hidingProof = true
  · -- §8 portal discharges: fall through to the per-asset lock create.
    rw [if_pos hp]
    unfold createEscrowChainA createEscrowKAsset
    by_cases hg : authorizedB st.kernel.caps
          { actor := actor, src := creator, dst := recipient, amt := amount } = true
        ∧ 0 ≤ amount ∧ amount ≤ st.kernel.bal creator asset ∧ creator ∈ st.kernel.accounts
        ∧ ¬ (∃ r ∈ st.kernel.escrows, r.id = id)
    · rw [if_pos hg]
      simp only [createEscrowRawAsset, parkedRecord]
      constructor
      · intro h
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨⟨hp, hg⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
               rfl, rfl, rfl⟩
      · rintro ⟨_, hbal, hesc, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
        obtain ⟨k', l'⟩ := st'
        obtain ⟨acc, cell, caps, esc, nul, rev, com, bal, q, sw, sc, fac, lc, dc, dg, dgs, sb⟩ := k'
        simp only at hbal hesc hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
        subst hbal hesc hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
        rfl
    · rw [if_neg hg]
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨⟨_, hg'⟩, _⟩; exact absurd hg' hg
  · -- §8 portal FAILS — fail-closed: the create returns `none`, so no spec post-state exists.
    rw [if_neg hp]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨⟨hp', _⟩, _⟩; exact absurd hp' hp

/-- **`execFullA_createCommittedEscrowA_iff_spec` — the UNIFIED-ACTION executor corner.** `execFullA`
dispatches `.createCommittedEscrowA …` to `createCommittedEscrowChainA s …`, so committing the unified
action into `st'` is EXACTLY the full-state spec. This is the variant-level executor⟺spec. -/
theorem execFullA_createCommittedEscrowA_iff_spec (st : RecChainedState) (id : Nat)
    (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ) (hidingProof : Bool)
    (st' : RecChainedState) :
    execFullA st (.createCommittedEscrowA id actor creator recipient asset amount hidingProof) = some st'
      ↔ CommittedEscrowCreateSpec st id actor creator recipient asset amount hidingProof st' := by
  show createCommittedEscrowChainA st id actor creator recipient asset amount hidingProof = some st'
        ↔ CommittedEscrowCreateSpec st id actor creator recipient asset amount hidingProof st'
  exact createCommittedEscrowChainA_iff_spec st id actor creator recipient asset amount hidingProof st'

/-! ## §4 — the create post-state facts a committed step produces (debit / park / ledger-frame). -/

/-- **`committedCreate_debit`** — a committed create debits the creator's asset-`asset` ledger by
`amount` (the value parked off-ledger into the holding-store). -/
theorem committedCreate_debit (st : RecChainedState) (id : Nat) (actor creator recipient : CellId)
    (asset : AssetId) (amount : ℤ) (hidingProof : Bool) (st' : RecChainedState)
    (h : execFullA st (.createCommittedEscrowA id actor creator recipient asset amount hidingProof)
          = some st') :
    st'.kernel.bal creator asset = st.kernel.bal creator asset - amount := by
  obtain ⟨_, hbal, _⟩ :=
    (execFullA_createCommittedEscrowA_iff_spec st id actor creator recipient asset amount
      hidingProof st').mp h
  rw [hbal]
  exact (createCommittedEscrowKAsset_correct st.kernel id creator recipient asset amount).1

/-- **`committedCreate_other_untouched`** — a committed create leaves every other `(cell,asset)` ledger
entry untouched (the per-asset ledger frame). -/
theorem committedCreate_other_untouched (st : RecChainedState) (id : Nat)
    (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ) (hidingProof : Bool)
    (st' : RecChainedState)
    (h : execFullA st (.createCommittedEscrowA id actor creator recipient asset amount hidingProof)
          = some st')
    (c : CellId) (b : AssetId) (hcd : ¬ (c = creator ∧ b = asset)) :
    st'.kernel.bal c b = st.kernel.bal c b := by
  obtain ⟨_, hbal, _⟩ :=
    (execFullA_createCommittedEscrowA_iff_spec st id actor creator recipient asset amount
      hidingProof st').mp h
  rw [hbal]
  exact (createCommittedEscrowKAsset_correct st.kernel id creator recipient asset amount).2.1 c b hcd

/-- **`committedCreate_parks_record`** — a committed create prepends exactly the unresolved record onto
the holding-store (the off-ledger lock). -/
theorem committedCreate_parks_record (st : RecChainedState) (id : Nat)
    (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ) (hidingProof : Bool)
    (st' : RecChainedState)
    (h : execFullA st (.createCommittedEscrowA id actor creator recipient asset amount hidingProof)
          = some st') :
    st'.kernel.escrows = parkedRecord id creator recipient asset amount :: st.kernel.escrows := by
  obtain ⟨_, _, hesc, _⟩ :=
    (execFullA_createCommittedEscrowA_iff_spec st id actor creator recipient asset amount
      hidingProof st').mp h
  exact hesc

/-! ## §5 — the SETTLE (release / refund) variants: INDEPENDENT full-state specs + executor⟺spec.

`releaseCommittedEscrowA`/`refundCommittedEscrowA` dispatch to the plain per-asset escrow settle
(`releaseEscrowChainA`/`refundEscrowChainA`, `TurnExecutorFull.lean:3545,3546`), which look up the
unresolved record by `id`, gate on the SETTLE-LIVENESS of the target (`recipient` for release,
`creator` for refund — a LIVE account whose `lifecycle = 0`), then single-cell-credit the target at the
record's asset and mark the record resolved (`settleEscrowRawAsset`, `RecordKernel.lean:1481`, which
touches ONLY `bal` and `escrows`). The §8 release/refund portal is the theorem-layer carrier (same lock
automaton as plain escrow), so the executable settle is the SHARED body — and these specs are stated
over the SETTLE-found record, indexed by the chosen target field. -/

/-- The settle admissibility predicate (release/refund), parameterised by the chosen target picker
(`fun r => r.recipient` for release, `fun r => r.creator` for refund): an unresolved record matches
`id`, and its picked target is a LIVE account. Stated declaratively over the FOUND record. -/
def settleGuard (k : RecordKernelState) (id : Nat) (pick : EscrowRecord → CellId)
    (r : EscrowRecord) : Prop :=
  k.escrows.find? (fun x => decide (x.id = id ∧ x.resolved = false)) = some r
    ∧ pick r ∈ k.accounts ∧ cellLifecycleLive k (pick r) = true

/-- **The full-state declarative spec of a committed settle** (release: `pick = .recipient`; refund:
`pick = .creator`) — INDEPENDENT of the executor. The settle guard holds; the post-`bal` ledger credits
`(pick r, r.asset)` by `r.amount` (`recBalCreditCell`); the post-`escrows` store is the record marked
resolved (`markResolved`); the chained `log` advances by `escrowReceiptA actor ::`; and every one of the
15 other RecordKernelState components is unchanged (the FRAME). -/
def CommittedEscrowSettleSpec (st : RecChainedState) (id : Nat) (actor : CellId)
    (pick : EscrowRecord → CellId) (st' : RecChainedState) : Prop :=
  ∃ r : EscrowRecord,
    settleGuard st.kernel id pick r
    ∧ st'.kernel.bal = recBalCreditCell st.kernel.bal (pick r) r.asset r.amount
    ∧ st'.kernel.escrows = markResolved st.kernel.escrows id
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

/-- **`execFullA_releaseCommittedEscrowA_iff_spec` — EXECUTOR ⟺ SPEC (release).** `execFullA` dispatches
`.releaseCommittedEscrowA id actor` to `releaseEscrowChainA`, which credits the FOUND record's
`recipient`. The settle spec with `pick = .recipient` is met IFF the executor commits, both ways; the
`→` checks all 17 kernel fields + log against the independent spec. -/
theorem execFullA_releaseCommittedEscrowA_iff_spec (st : RecChainedState) (id : Nat) (actor : CellId)
    (st' : RecChainedState) :
    execFullA st (.releaseCommittedEscrowA id actor) = some st'
      ↔ CommittedEscrowSettleSpec st id actor (fun r => r.recipient) st' := by
  show releaseEscrowChainA st id actor = some st'
        ↔ CommittedEscrowSettleSpec st id actor (fun r => r.recipient) st'
  unfold releaseEscrowChainA releaseEscrowKAsset CommittedEscrowSettleSpec
  -- keep `settleGuard` FOLDED so the spec's `find?` is hidden from `rw [hfind]` (which reduces ONLY
  -- the executor's `match find? …` on the goal's left).
  cases hfind : st.kernel.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | none =>
      simp only []
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨r, hsg, _⟩
        have hf := hsg.1; rw [hfind] at hf; exact absurd hf (by simp)
  | some r =>
      simp only []
      by_cases hgate : r.recipient ∈ st.kernel.accounts ∧ cellLifecycleLive st.kernel r.recipient = true
      · rw [if_pos hgate]
        simp only [settleEscrowRawAsset]
        constructor
        · intro h
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨r, ⟨hfind, hgate.1, hgate.2⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                 rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · rintro ⟨r', hsg, hbal, hesc, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
                 h12, h13, h14, h15⟩
          have hf' := hsg.1
          rw [hfind] at hf'; simp only [Option.some.injEq] at hf'; subst hf'
          obtain ⟨k', l'⟩ := st'
          obtain ⟨acc, cell, caps, esc, nul, rev, com, bal, q, sw, sc, fac, lc, dc, dg, dgs, sb⟩ := k'
          simp only at hbal hesc hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
          subst hbal hesc hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
          rfl
      · rw [if_neg hgate]
        constructor
        · intro h; exact absurd h (by simp)
        · rintro ⟨r', hsg, _⟩
          have hf' := hsg.1; have hlive := hsg.2.1; have hlc := hsg.2.2
          rw [hfind] at hf'; simp only [Option.some.injEq] at hf'; subst hf'
          exact absurd ⟨hlive, hlc⟩ hgate

/-- **`execFullA_refundCommittedEscrowA_iff_spec` — EXECUTOR ⟺ SPEC (refund).** `execFullA` dispatches
`.refundCommittedEscrowA id actor` to `refundEscrowChainA`, which credits the FOUND record's `creator`.
The settle spec with `pick = .creator` is met IFF the executor commits, both ways. -/
theorem execFullA_refundCommittedEscrowA_iff_spec (st : RecChainedState) (id : Nat) (actor : CellId)
    (st' : RecChainedState) :
    execFullA st (.refundCommittedEscrowA id actor) = some st'
      ↔ CommittedEscrowSettleSpec st id actor (fun r => r.creator) st' := by
  show refundEscrowChainA st id actor = some st'
        ↔ CommittedEscrowSettleSpec st id actor (fun r => r.creator) st'
  unfold refundEscrowChainA refundEscrowKAsset CommittedEscrowSettleSpec
  cases hfind : st.kernel.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | none =>
      simp only []
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨r, hsg, _⟩
        have hf := hsg.1; rw [hfind] at hf; exact absurd hf (by simp)
  | some r =>
      simp only []
      by_cases hgate : r.creator ∈ st.kernel.accounts ∧ cellLifecycleLive st.kernel r.creator = true
      · rw [if_pos hgate]
        simp only [settleEscrowRawAsset]
        constructor
        · intro h
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨r, ⟨hfind, hgate.1, hgate.2⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                 rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · rintro ⟨r', hsg, hbal, hesc, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
                 h12, h13, h14, h15⟩
          have hf' := hsg.1
          rw [hfind] at hf'; simp only [Option.some.injEq] at hf'; subst hf'
          obtain ⟨k', l'⟩ := st'
          obtain ⟨acc, cell, caps, esc, nul, rev, com, bal, q, sw, sc, fac, lc, dc, dg, dgs, sb⟩ := k'
          simp only at hbal hesc hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
          subst hbal hesc hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
          rfl
      · rw [if_neg hgate]
        constructor
        · intro h; exact absurd h (by simp)
        · rintro ⟨r', hsg, _⟩
          have hf' := hsg.1; have hlive := hsg.2.1; have hlc := hsg.2.2
          rw [hfind] at hf'; simp only [Option.some.injEq] at hf'; subst hf'
          exact absurd ⟨hlive, hlc⟩ hgate

/-! ## §6 — NON-VACUITY: the executor REJECTS bad inputs (each guard leg, fail-closed).

A spec a worthless executor could meet (accept everything) would be vacuous. Each forged input fails a
guard conjunct ⇒ `execFullA st (.<variant> …) = none` ⇒ no spec post-state exists. The create's
HEADLINE is the §8 PRIVACY-BOUNDARY tooth (`…_rejects_no_hiding`) — the gate plain escrow LACKS. -/

/-- **`committedCreate_rejects_no_hiding` — PROVED (THE PRIVACY-BOUNDARY TEETH).** No committed-escrow
create commits without the §8 hiding portal (`hidingProof = false` ⇒ `none`). This is the gate plain
escrow does NOT have — the committed variant is NOT silently identical to plain escrow. -/
theorem committedCreate_rejects_no_hiding (st : RecChainedState) (id : Nat)
    (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ) (hidingProof : Bool)
    (hbad : hidingProof = false) :
    execFullA st (.createCommittedEscrowA id actor creator recipient asset amount hidingProof)
      = none := by
  show createCommittedEscrowChainA st id actor creator recipient asset amount hidingProof = none
  simp only [createCommittedEscrowChainA, hbad, if_neg (by decide : ¬ (false = true))]

/-- **`committedCreate_rejects_unauthorized` — PROVED.** An unauthorized actor's create does NOT commit
(the AUTHORITY leg fails) ⇒ no `st'` satisfies the spec. -/
theorem committedCreate_rejects_unauthorized (st : RecChainedState) (id : Nat)
    (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ)
    (hbad : authorizedB st.kernel.caps
        { actor := actor, src := creator, dst := recipient, amt := amount } = false) :
    execFullA st (.createCommittedEscrowA id actor creator recipient asset amount true) = none := by
  show createCommittedEscrowChainA st id actor creator recipient asset amount true = none
  unfold createCommittedEscrowChainA
  rw [if_pos rfl]
  unfold createEscrowChainA createEscrowKAsset
  rw [if_neg (by rw [hbad]; rintro ⟨h, _⟩; exact absurd h (by simp))]

/-- **`committedCreate_rejects_negative` — PROVED.** A negative-amount create does NOT commit (the
NON-NEGATIVITY leg fails) — no value can be conjured by a negative lock. -/
theorem committedCreate_rejects_negative (st : RecChainedState) (id : Nat)
    (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ)
    (hbad : ¬ 0 ≤ amount) :
    execFullA st (.createCommittedEscrowA id actor creator recipient asset amount true) = none := by
  show createCommittedEscrowChainA st id actor creator recipient asset amount true = none
  unfold createCommittedEscrowChainA
  rw [if_pos rfl]
  unfold createEscrowChainA createEscrowKAsset
  rw [if_neg (by rintro ⟨_, h, _⟩; exact hbad h)]

/-- **`committedCreate_rejects_overdraft` — PROVED.** A lock of more than the creator holds in asset
`asset` (`¬ amount ≤ k.bal creator asset`) does NOT commit (the AVAILABILITY leg fails). -/
theorem committedCreate_rejects_overdraft (st : RecChainedState) (id : Nat)
    (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ)
    (hbad : ¬ amount ≤ st.kernel.bal creator asset) :
    execFullA st (.createCommittedEscrowA id actor creator recipient asset amount true) = none := by
  show createCommittedEscrowChainA st id actor creator recipient asset amount true = none
  unfold createCommittedEscrowChainA
  rw [if_pos rfl]
  unfold createEscrowChainA createEscrowKAsset
  rw [if_neg (by rintro ⟨_, _, h, _⟩; exact hbad h)]

/-- **`committedCreate_rejects_dead_creator` — PROVED.** A lock out of a non-account creator does NOT
commit (the CREATOR-LIVENESS leg fails). -/
theorem committedCreate_rejects_dead_creator (st : RecChainedState) (id : Nat)
    (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ)
    (hbad : creator ∉ st.kernel.accounts) :
    execFullA st (.createCommittedEscrowA id actor creator recipient asset amount true) = none := by
  show createCommittedEscrowChainA st id actor creator recipient asset amount true = none
  unfold createCommittedEscrowChainA
  rw [if_pos rfl]
  unfold createEscrowChainA createEscrowKAsset
  rw [if_neg (by rintro ⟨_, _, _, h, _⟩; exact hbad h)]

/-- **`committedCreate_rejects_id_reuse` — PROVED.** A create whose `id` is ALREADY in use does NOT
commit (the ID-FRESHNESS leg fails) — locks cannot collide on the holding-store key. -/
theorem committedCreate_rejects_id_reuse (st : RecChainedState) (id : Nat)
    (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ)
    (hbad : ∃ r ∈ st.kernel.escrows, r.id = id) :
    execFullA st (.createCommittedEscrowA id actor creator recipient asset amount true) = none := by
  show createCommittedEscrowChainA st id actor creator recipient asset amount true = none
  unfold createCommittedEscrowChainA
  rw [if_pos rfl]
  unfold createEscrowChainA createEscrowKAsset
  rw [if_neg (by rintro ⟨_, _, _, _, h⟩; exact h hbad)]

/-- **`committedRelease_rejects_missing_record` — PROVED.** A release whose `id` matches NO unresolved
record does NOT commit (the lookup is `none` ⇒ fail-closed). -/
theorem committedRelease_rejects_missing_record (st : RecChainedState) (id : Nat) (actor : CellId)
    (hbad : st.kernel.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = none) :
    execFullA st (.releaseCommittedEscrowA id actor) = none := by
  show releaseEscrowChainA st id actor = none
  unfold releaseEscrowChainA releaseEscrowKAsset
  rw [hbad]

/-- **`committedRefund_rejects_missing_record` — PROVED.** A refund whose `id` matches NO unresolved
record does NOT commit (the lookup is `none` ⇒ fail-closed). -/
theorem committedRefund_rejects_missing_record (st : RecChainedState) (id : Nat) (actor : CellId)
    (hbad : st.kernel.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = none) :
    execFullA st (.refundCommittedEscrowA id actor) = none := by
  show refundEscrowChainA st id actor = none
  unfold refundEscrowChainA refundEscrowKAsset
  rw [hbad]

/-! ## §7 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms createCommittedEscrowKAsset_correct
#assert_axioms createCommittedEscrowChainA_iff_spec
#assert_axioms execFullA_createCommittedEscrowA_iff_spec
#assert_axioms committedCreate_debit
#assert_axioms committedCreate_other_untouched
#assert_axioms committedCreate_parks_record
#assert_axioms execFullA_releaseCommittedEscrowA_iff_spec
#assert_axioms execFullA_refundCommittedEscrowA_iff_spec
#assert_axioms committedCreate_rejects_no_hiding
#assert_axioms committedCreate_rejects_unauthorized
#assert_axioms committedCreate_rejects_negative
#assert_axioms committedCreate_rejects_overdraft
#assert_axioms committedCreate_rejects_dead_creator
#assert_axioms committedCreate_rejects_id_reuse
#assert_axioms committedRelease_rejects_missing_record
#assert_axioms committedRefund_rejects_missing_record

end Dregg2.Circuit.Spec.EscrowCommitted
