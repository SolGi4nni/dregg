/-
# Dregg2.Verify.ObligationFactoryProbe — the FALSIFICATION PROBE for the STANDING (recurring) OBLIGATION
as a factory-born cell-program.

THE CLAIM UNDER TEST (the house-capacity weld, `docs/HOUSE-CAPACITIES-WELD-PLAN.md` — the THIRD house
room, after the vault + allowance):
*a STANDING OBLIGATION — a first-class, schedule-enforced recurring commitment: a cell OWES a FIXED
amount to a beneficiary every PERIOD blocks (a subscription / salary / rent) — is NOT a new kernel
verb. It is a COMPOSITION: a scheduled-payment CELL whose program enforces the schedule + the fixed
amount, settled by the already-wired `CreateCellFromFactory` + `Transfer` (the periodic payment) +
`SetField` (advance the schedule cursor) triple.* An agent ENTERS an obligation the protocol itself
enforces on schedule: it can neither FORGE the terms (amount/period/beneficiary/start are frozen), nor
UNDERPAY a period (the amount is fixed), nor DISCHARGE EARLY (each period waits for its due block), nor
REPLAY a discharged period (the cursor is monotone). It rides the SAME committed-cell substrate as the
allowance factory (`Dregg2.Verify.AllowanceFactoryProbe`), and every gate it needs ALREADY EXISTS — the
fixed amount is exactly an `Immutable` term-pin, the schedule clock is the timelock height clock, the
one-shot-per-period tooth is the `Monotonic` cursor.

This probe finds out whether the rebuild GENUINELY captures the standing-obligation semantics. An honest
PARTIAL is as valuable as PASS; the verdict (§VERDICT) is PASS.

## The reframe (why a standing obligation is a factory cell, not a verb)

A standing obligation is an allowance with the per-epoch CEILING replaced by a FIXED per-period AMOUNT,
the spend op replaced by a scheduled DISCHARGE:

  * the payable VALUE lives in the obligation cell's OWN per-asset `bal` column (NOT a side-table) — a
    discharge is an ordinary `move` OUT (obligation ⇒ beneficiary). So conservation is the EXISTING
    per-asset move law `recKExecAsset_conserves_per_asset`, inherited verbatim;
  * the per-period `amount`, the `period`, the `start`, and the `beneficiary` are FROZEN DEAL TERMS —
    committed at factory-mint, never re-writable. The terms-pin IS the no-forge tooth: a tampered
    amount/period diverges from the committed digest and is rejected;
  * the schedule is the committed `nextDue` cursor measured against the discharge's block. Period `k`
    falls due at `start + k·period`; the cursor starts at `start` and advances by `period` each
    discharge. A discharge is admitted only when the block has REACHED the cursor (`atBlock ≥ nextDue`)
    — no early discharge — and moves exactly the committed `amount` — no under/over-pay;
  * the cursor is MONOTONE: a discharged period (whose due block sits below the advanced cursor) can
    never be replayed, and the discharged COUNT never regresses (the one-shot-per-period tooth).

## The obligation SHAPE (the reusable deliverable)

slots (fields on the obligation cell's record):
  * `state`           — 0 = open (live). A perpetual obligation has NO terminal (it pays forever)
  * `beneficiary`     — the payout target            (immutable after open)
  * `amount`          — the FIXED per-period amount    (immutable — the no-forge / fixed-amount tooth)
  * `period`          — the period length in blocks     (immutable)
  * `start`           — the block period 0 falls due     (immutable)
  * `nextDue`         — the committed schedule cursor     (monotone; the next undischarged period's block)
  * `dischargedCount` — periods discharged so far          (monotone; the one-shot-per-period nullifier)
plus the payable VALUE itself, held in the obligation cell's per-asset `bal` column. The
`obligationFactory` installs the four deal-term immutables + the two monotone cursors.

## The four obligation-safety keystones (all PROVED here)

  (a) CONSERVATION across discharges — every discharge is an ordinary per-asset `move`, so the kernel's
      value law applies VERBATIM; no bespoke quantity, no side-table.
  (b) THE FIXED AMOUNT (no under/over-pay) — a discharge whose moved amount ≠ the committed per-period
      `amount` is rejected (`none`). The obligor cannot quietly inflate or deflate what is owed.
  (c) NO FORGED / EARLY DISCHARGE — the schedule is DERIVED from the discharge's block, not asserted. A
      discharge whose block has NOT reached the current period's due block (`atBlock < nextDue`) is
      rejected (no early payment); the cursor advances only forward (no replay of a discharged period).
  (d) VALUE NOT STRANDED (open ∧ due ∧ funded ⇒ dischargeable) — a one-step liveness: any OPEN
      obligation whose current period is due, with a live distinct beneficiary and the amount held in
      its `bal` column, DISCHARGES. No due payment is structurally trapped.

NEW file only. Reuses ONLY the proved per-asset move conservation + the SlotCaveat vocabulary; mirrors
`Dregg2.Verify.AllowanceFactoryProbe` exactly (obligation = allowance with the per-epoch ceiling
replaced by a fixed per-period amount, the spend gate replaced by a due-block schedule gate). Every
keystone `#assert_axioms`-pinned to `{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Exec.RecordKernel
import Dregg2.Exec.EffectsState

namespace Dregg2.Verify.ObligationFactoryProbe

open Dregg2.Exec
open Dregg2.Exec.EffectsState (setField fieldOf setField_fieldOf)

/-! ## §1 — The obligation-cell SLOT layout (field names) + the lifecycle state. -/

/-- The lifecycle slot: 0 = open (live). A perpetual obligation has no terminal — it pays forever. -/
abbrev stateField : FieldName := "obligation.state"
/-- The payout target (frozen after open). The payable VALUE lives in the cell's `bal` column. -/
abbrev beneficiaryField : FieldName := "obligation.beneficiary"
/-- The FIXED per-period amount (frozen — the no-forge / fixed-amount tooth). -/
abbrev amountField : FieldName := "obligation.amount"
/-- The period length in blocks (frozen). -/
abbrev periodField : FieldName := "obligation.period"
/-- The block at which period 0 falls due (frozen). -/
abbrev startField : FieldName := "obligation.start"
/-- The committed `next_due` cursor (monotone; the next undischarged period's due block). -/
abbrev nextDueField : FieldName := "obligation.nextDue"
/-- The committed `discharged_count` (monotone; the one-shot-per-period nullifier). -/
abbrev dischargedCountField : FieldName := "obligation.dischargedCount"

/-- Lifecycle state literal: open (the only state — an obligation is perpetual). -/
abbrev sOpen : Int := 0

/-! ## §2 — The obligation FACTORY DESCRIPTOR: the published contract that mints obligation cells.

The `FactoryEntry` an obligation factory publishes. Its `caveats` ARE the obligation invariants — the
FOUR deal-term immutables (`beneficiary`, `amount`, `period`, `start` — the amount + schedule are
FROZEN, so a tampered amount/period diverges from the commitment) + the TWO monotone cursors (`nextDue`
advances only forward, `dischargedCount` never regresses — the one-shot-per-period tooth). A cell minted
by this factory carries these for its WHOLE LIFE; the executor enforces them on every `SetField`. -/

/-- **`obligationFactory beneficiary amount period start` — the obligation factory descriptor.**
Installs: the four deal-term immutables (the FROZEN amount + schedule), and the two monotone cursors.
Initial state OPEN, cursor at `start` (period 0's due block), zero periods discharged. -/
def obligationFactory (beneficiary amount period start : Int) : FactoryEntry where
  caveats :=
    [ SlotCaveat.immutable beneficiaryField
    , SlotCaveat.immutable amountField
    , SlotCaveat.immutable periodField
    , SlotCaveat.immutable startField
    , SlotCaveat.monotonic nextDueField
    , SlotCaveat.monotonic dischargedCountField ]
  initialFields :=
    [ (stateField, sOpen)
    , (beneficiaryField, beneficiary)
    , (amountField, amount)
    , (periodField, period)
    , (startField, start)
    , (nextDueField, start)
    , (dischargedCountField, 0) ]
  programVk := 0

/-- **`obligationFactory_conforms`.** The obligation factory's OWN published initial state satisfies its
OWN caveats (no balance smuggling; the immutables permit their first write; the monotone cursors born at
`start` / `0`). Every caveat is a TRANSITION caveat (immutable / monotonic), all of which permit the
genesis first write — so the factory conforms unconditionally. -/
theorem obligationFactory_conforms (beneficiary amount period start : Int) :
    (obligationFactory beneficiary amount period start).conforms = true := by
  unfold obligationFactory FactoryEntry.conforms FactoryEntry.initialFieldsNoBalance
  simp only [SlotCaveat.field, SlotCaveat.bornFresh, List.all_cons, List.all_nil,
    beneficiaryField, amountField, periodField,
    startField, nextDueField, dischargedCountField, stateField, balanceField]
  simp

/-! ## §3 — The obligation cell STATE: a record cell holding the payable value in its `bal` column. -/

/-- Read the obligation cell's frozen per-period amount slot. -/
def obligationAmount (k : RecordKernelState) (e : CellId) : Int := fieldOf amountField (k.cell e)

/-- Read the obligation cell's frozen period-length slot. -/
def obligationPeriod (k : RecordKernelState) (e : CellId) : Int := fieldOf periodField (k.cell e)

/-- Read the obligation cell's frozen start slot. -/
def obligationStart (k : RecordKernelState) (e : CellId) : Int := fieldOf startField (k.cell e)

/-- Read the obligation cell's committed `next_due` cursor (the next undischarged period's due block). -/
def obligationNextDue (k : RecordKernelState) (e : CellId) : Int := fieldOf nextDueField (k.cell e)

/-- Read the obligation cell's committed discharged-count. -/
def obligationDischarged (k : RecordKernelState) (e : CellId) : Int := fieldOf dischargedCountField (k.cell e)

/-! ## §4 — The obligation OPERATIONS as the 8-verb composition (write + move).

The obligation discharge is the allowance `spend` with the per-epoch ceiling replaced by the FIXED
amount and the epoch derivation replaced by the due-block schedule gate. A discharge of the current
period is admitted only when the block has reached the committed cursor (`atBlock ≥ nextDue`) and moves
exactly the committed `amount`; it advances `nextDue` by `period` and `dischargedCount` by 1. Both the
cursor advance and the count write are ORDINARY `setField`s; the value move is the ordinary
`recKExecAsset`. -/

/-- **`obligationSettle` — the body of a discharge: two `write`s (advance the cursor by `period` + the
discharged count by 1), then a `move` of `amount` out.** All ORDINARY verbs (`setField` + the per-asset
move `recKExecAsset`). Fail-closed (the move's guard: authorized, non-negative, sufficient balance,
distinct live cells). On success: the cursor reads `nextDue + period`, the count reads `count + 1`, and
the value moves to `beneficiary`. -/
def obligationSettle (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId)
    (newNextDue newCount amount : Int) : Option RecordKernelState :=
  let k1 : RecordKernelState :=
    { k with cell := fun c =>
        if c = e then
          setField dischargedCountField (setField nextDueField (k.cell e) (.int newNextDue)) (.int newCount)
        else k.cell c }
  recKExecAsset k1 { actor := e, src := e, dst := beneficiary, amt := amount } asset

/-- **`obligationDischarge` — the discharge op (advance the schedule cursor + the count + move to the
beneficiary), gated on the SCHEDULE + the FIXED AMOUNT.** Rejects (`none`) when: the discharge's block
has NOT reached the current period's due block (`atBlock < nextDue` — a premature discharge), or the
asserted `amount` ≠ the committed per-period `amount` (an under/over-pay). The schedule is DERIVED from
`atBlock` (the cursor only advances when the block reaches it), so an early discharge is structurally
impossible. On success advances `nextDue := nextDue + period`, `dischargedCount := count + 1`. -/
def obligationDischarge (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId)
    (atBlock amount : Int) : Option RecordKernelState :=
  let nextDue := obligationNextDue k e
  let period  := obligationPeriod k e
  let count   := obligationDischarged k e
  if nextDue ≤ atBlock ∧ amount = obligationAmount k e then
    obligationSettle k e beneficiary asset (nextDue + period) (count + 1) amount
  else none

/-! ## §5 — KEYSTONE (a): CONSERVATION across discharges (inherited from the ORDINARY move). -/

/-- **`obligationSettle_conserves` — KEYSTONE (a), PROVED.** A committed discharge preserves EVERY
asset's total supply: the moved value goes between two live accounts, and the two slot writes touch no
balance. The ordinary move conservation law — the obligation inherits it, no side-table. -/
theorem obligationSettle_conserves {k k' : RecordKernelState} {e beneficiary : CellId} {asset : AssetId}
    {newNextDue newCount amount : Int}
    (h : obligationSettle k e beneficiary asset newNextDue newCount amount = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold obligationSettle at h
  set k1 : RecordKernelState :=
    { k with cell := fun c =>
        if c = e then
          setField dischargedCountField (setField nextDueField (k.cell e) (.int newNextDue)) (.int newCount)
        else k.cell c } with hk1
  have hbal : k1.bal = k.bal := rfl
  have hacc : k1.accounts = k.accounts := rfl
  have hconv := recKExecAsset_conserves_per_asset k1 k'
    { actor := e, src := e, dst := beneficiary, amt := amount } asset h b
  have hk1tot : recTotalAsset k1 b = recTotalAsset k b := by
    unfold recTotalAsset; rw [hacc, hbal]
  rw [hk1tot] at hconv
  exact hconv

/-- **`obligationDischarge_conserves` — KEYSTONE (a) for a discharge.** A committed discharge preserves
every asset's supply (the value is DELIVERED from the held column, not conjured). -/
theorem obligationDischarge_conserves {k k' : RecordKernelState} {e beneficiary : CellId} {asset : AssetId}
    {atBlock amount : Int}
    (h : obligationDischarge k e beneficiary asset atBlock amount = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold obligationDischarge at h
  by_cases hg : obligationNextDue k e ≤ atBlock ∧ amount = obligationAmount k e
  · rw [if_pos hg] at h; exact obligationSettle_conserves h b
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §6 — KEYSTONE (b): THE FIXED AMOUNT (no under/over-pay).

The discharge's `amount = obligationAmount` conjunct is the fixed-amount tooth. A discharge whose
asserted amount differs from the committed per-period amount fail-closes to `none` — the obligor cannot
quietly inflate (overpay-then-claim) or deflate (underpay) what is owed. -/

/-- **`wrong_amount_rejected` — KEYSTONE (b), PROVED.** A discharge whose moved amount differs from the
committed per-period amount is rejected — the amount is FIXED, neither over- nor under-payable. -/
theorem wrong_amount_rejected (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId)
    (atBlock amount : Int) (hwrong : amount ≠ obligationAmount k e) :
    obligationDischarge k e beneficiary asset atBlock amount = none := by
  unfold obligationDischarge
  rw [if_neg]
  rintro ⟨_, heq⟩
  exact hwrong heq

/-! ## §7 — KEYSTONE (c): NO FORGED / EARLY DISCHARGE (the schedule is derived, not asserted).

The schedule cursor is the committed `nextDue` — a discharge is admitted only when the block has REACHED
it (`atBlock ≥ nextDue`). An early discharge is therefore structurally impossible: you cannot pay a
period before its due block, only a later BLOCK reaches the cursor. And because the cursor advances only
FORWARD (`nextDue := nextDue + period`, a `Monotonic` cursor on the factory cell), a discharged period
can never be replayed — the cursor has moved past its due block. -/

/-- **`early_discharge_rejected` — KEYSTONE (c), the premature-discharge tooth.** A discharge whose block
has NOT reached the current period's due block (`atBlock < nextDue`) is rejected — no early payment;
each period waits for its due block. -/
theorem early_discharge_rejected (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId)
    (atBlock amount : Int) (hearly : atBlock < obligationNextDue k e) :
    obligationDischarge k e beneficiary asset atBlock amount = none := by
  unfold obligationDischarge
  rw [if_neg]
  rintro ⟨hle, _⟩
  exact absurd hle (by simp [not_le]; exact hearly)

/-- **`replay_rejected` — the one-shot-per-period tooth (no double-discharge).** Once the cursor has
advanced past a period's due block (`nextDue` strictly above the old due block — the `Monotonic` factory
caveat only ever advances it forward), a second discharge presented at that old due block is rejected by
the early-discharge gate: the block is now `< nextDue`. So a discharged period is SPENT — exactly the
nullifier shape. (The constructive cursor-advance itself is witnessed concretely in §9 (v).) -/
theorem replay_rejected (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId)
    (oldDue amount : Int) (hspent : oldDue < obligationNextDue k e) :
    obligationDischarge k e beneficiary asset oldDue amount = none :=
  early_discharge_rejected k e beneficiary asset oldDue amount hspent

/-! ## §8 — KEYSTONE (d): VALUE NOT STRANDED (open ∧ due ∧ funded ⇒ dischargeable). -/

/-- The move-admissibility hypothesis bundle for a discharge: the obligation cell is authorized over
itself (it always is — `actor = src = e`), the amount is non-negative, the beneficiary is a distinct
live account, and the obligation cell is a live account holding the amount. -/
structure DischargeReady (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId) (amount : Int) :
    Prop where
  amount_nonneg : 0 ≤ amount
  funded        : amount ≤ k.bal e asset
  distinct      : e ≠ beneficiary
  e_live        : e ∈ k.accounts
  beneficiary_live : beneficiary ∈ k.accounts
  e_lifecycle   : cellLifecycleLive k e = true

/-- A discharge body COMMITS whenever the world is `DischargeReady` (the move's fail-closed guard is
discharged: `actor = src = e` self-authorizes, the held amount is available by hypothesis). -/
theorem obligationSettle_commits (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId)
    (newNextDue newCount amount : Int) (hr : DischargeReady k e beneficiary asset amount) :
    (obligationSettle k e beneficiary asset newNextDue newCount amount).isSome := by
  unfold obligationSettle
  set k1 : RecordKernelState :=
    { k with cell := fun c =>
        if c = e then
          setField dischargedCountField (setField nextDueField (k.cell e) (.int newNextDue)) (.int newCount)
        else k.cell c } with hk1
  have hbal : k1.bal = k.bal := rfl
  have hacc : k1.accounts = k.accounts := rfl
  have hauth : authorizedB k1.caps { actor := e, src := e, dst := beneficiary, amt := amount } = true := by
    unfold authorizedB; simp
  have hlife : cellLifecycleLive k1 e = true := hr.e_lifecycle
  unfold recKExecAsset
  rw [if_pos]
  · exact Option.isSome_some
  · refine ⟨hauth, hr.amount_nonneg, ?_, hr.distinct, ?_, ?_, ?_⟩
    · show amount ≤ k1.bal e asset; rw [hbal]; exact hr.funded
    · show e ∈ k1.accounts; rw [hacc]; exact hr.e_live
    · show beneficiary ∈ k1.accounts; rw [hacc]; exact hr.beneficiary_live
    · show cellLifecycleLive k1 e = true; exact hlife

/-- **`due_period_dischargeable` — KEYSTONE (d), PROVED.** An OPEN obligation whose current period is
DUE (`atBlock ≥ nextDue`), discharging exactly the committed amount, with a `DischargeReady`
beneficiary, DISCHARGES (commits) — the due payment is deliverable, not trapped. SCOPE: this is
one-step dischargeability (the structural analog of the kernel verbs' guarantee). -/
theorem due_period_dischargeable (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId)
    (atBlock : Int)
    (hdue : obligationNextDue k e ≤ atBlock)
    (hr : DischargeReady k e beneficiary asset (obligationAmount k e)) :
    (obligationDischarge k e beneficiary asset atBlock (obligationAmount k e)).isSome := by
  unfold obligationDischarge
  rw [if_pos ⟨hdue, rfl⟩]
  exact obligationSettle_commits k e beneficiary asset _ _ (obligationAmount k e) hr

/-! ## §9 — NON-VACUITY: a concrete obligation world + `#guard` witnesses. -/

/-- An obligation world. The OBLIGATION CELL is cell `0` holding 1000 of asset 0 (the payable value, in
its OWN `bal` column) with state OPEN, beneficiary 1, amount 50 (the FIXED per-period amount), period
100, start 1000, cursor at 1000 (period 0's due block), nothing discharged. The BENEFICIARY is cell `1`
(holds 5 of asset 0). All live. NO side-table. -/
def obligWorld : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun c =>
      if c = 0 then .record
        [ (stateField, .int sOpen), (beneficiaryField, .int 1), (amountField, .int 50)
        , (periodField, .int 100), (startField, .int 1000)
        , (nextDueField, .int 1000), (dischargedCountField, .int 0) ]
      else .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun c a => if c = 0 then (if a = 0 then 1000 else 0)
                      else if c = 1 then (if a = 0 then 5 else 0) else 0 }

/-- The discharge-ready bundle for discharging period 0 (amount 50) of obligWorld to beneficiary 1. -/
theorem obligWorld_discharge_ready : DischargeReady obligWorld 0 1 0 50 :=
  { amount_nonneg := by decide, funded := by decide, distinct := by decide,
    e_live := by decide, beneficiary_live := by decide, e_lifecycle := by decide }

-- (i) the obligation reads its committed terms (amount 50, period 100, start 1000, cursor 1000):
#guard (obligationAmount obligWorld 0 == 50)                                      -- true
#guard (obligationPeriod obligWorld 0 == 100)                                    -- true
#guard (obligationStart obligWorld 0 == 1000)                                    -- true
#guard (obligationNextDue obligWorld 0 == 1000)                                  -- true
#guard (obligationDischarged obligWorld 0 == 0)                                  -- true

-- (ii) an ON-SCHEDULE discharge of period 0 (block 1000 = the due block, amount 50) COMMITS, delivers 50
--      to beneficiary 1, advances the cursor + count; supply FIXED (pure move conservation):
#guard ((obligationDischarge obligWorld 0 1 0 1000 50).isSome)                    -- true (discharged!)
#guard ((obligationDischarge obligWorld 0 1 0 1000 50).map (fun s => s.bal 1 0)) == some 55    -- beneficiary 5→55
#guard ((obligationDischarge obligWorld 0 1 0 1000 50).map (fun s => s.bal 0 0)) == some 950   -- obligation 1000→950
#guard ((obligationDischarge obligWorld 0 1 0 1000 50).map (fun s => obligationNextDue s 0)) == some 1100
#guard ((obligationDischarge obligWorld 0 1 0 1000 50).map (fun s => obligationDischarged s 0)) == some 1
#guard ((obligationDischarge obligWorld 0 1 0 1000 50).map (fun s => recTotalAsset s 0)) == some 1005
#guard (recTotalAsset obligWorld 0 == 1005)

-- (iii) a discharge ONE BLOCK EARLY (block 999 < due block 1000) is REJECTED (KEYSTONE c — no early):
#guard ((obligationDischarge obligWorld 0 1 0 999 50).isSome) == false            -- false (premature)
-- ...but discharging LATE (block 1500 > 1000) is fine — the period is due (non-vacuity):
#guard ((obligationDischarge obligWorld 0 1 0 1500 50).isSome)                    -- true (still owed)

-- (iv) a WRONG amount is REJECTED (KEYSTONE b — the amount is FIXED): both overpay and underpay:
#guard ((obligationDischarge obligWorld 0 1 0 1000 51).isSome) == false           -- false (overpay 51 ≠ 50)
#guard ((obligationDischarge obligWorld 0 1 0 1000 49).isSome) == false           -- false (underpay 49 ≠ 50)
#guard ((obligationDischarge obligWorld 0 1 0 1000 0).isSome) == false            -- false (skip-pay 0 ≠ 50)

/-- The obligation world AFTER discharging period 0 (cursor 1100, count 1, balance 950, beneficiary 55). -/
def obligAfter0 : RecordKernelState :=
  { obligWorld with
    cell := fun c =>
      if c = 0 then Value.record
        [ (stateField, .int sOpen), (beneficiaryField, .int 1), (amountField, .int 50)
        , (periodField, .int 100), (startField, .int 1000)
        , (nextDueField, .int 1100), (dischargedCountField, .int 1) ]
      else obligWorld.cell c
    bal := fun c a => if c = 0 then (if a = 0 then 950 else 0)
                      else if c = 1 then (if a = 0 then 55 else 0) else 0 }

-- (v) NO REPLAY: with the cursor advanced to 1100, the just-discharged period 0 (due block 1000) cannot
--     be paid again at block 1000 (1000 < 1100, the cursor moved past) — a discharged period is spent:
#guard (obligationNextDue obligAfter0 0 == 1100)                                  -- cursor advanced
#guard ((obligationDischarge obligAfter0 0 1 0 1000 50).isSome) == false          -- false (replay rejected)
-- ...but period 1 (due block 1100) at block 1100 IS dischargeable (the schedule MARCHES):
#guard ((obligationDischarge obligAfter0 0 1 0 1100 50).isSome)                   -- true (period 1 due)
#guard ((obligationDischarge obligAfter0 0 1 0 1100 50).map (fun s => obligationNextDue s 0)) == some 1200
#guard ((obligationDischarge obligAfter0 0 1 0 1100 50).map (fun s => obligationDischarged s 0)) == some 2
#guard ((obligationDischarge obligAfter0 0 1 0 1100 50).map (fun s => s.bal 1 0)) == some 105  -- 55→105

-- (vi) the factory descriptor conforms (its own initial state is invariant-clean):
#guard ((obligationFactory 1 50 100 1000).conforms)                              -- true

/-! ## §VERDICT — PASS.

THE STANDING OBLIGATION IS FULLY CAPTURED as a factory-born cell-program + a schedule-safety contract,
with NO side-table and NO bespoke conserved quantity:

  * FACTORY (`obligationFactory`): four deal-term immutables (the FROZEN amount + schedule — no-forge)
    + the monotone `nextDue` cursor + the monotone `dischargedCount` — `obligationFactory_conforms`
    PROVED. Drawn entirely from the EXISTING SlotCaveat vocabulary; the fixed amount is an `Immutable`
    term-pin, the schedule clock the vault height clock, the one-shot-per-period tooth the `Monotonic`
    cursor. No new constraint kind needed.

  * KEYSTONE (a) CONSERVATION (`obligationSettle_conserves`, `obligationDischarge_conserves`),
    INHERITED from the ordinary per-asset move law `recKExecAsset_conserves_per_asset`.
  * KEYSTONE (b) THE FIXED AMOUNT / no-under-or-over-pay (`wrong_amount_rejected`): a discharge whose
    moved amount ≠ the committed per-period amount is rejected.
  * KEYSTONE (c) NO FORGED / EARLY DISCHARGE (`early_discharge_rejected` — a premature discharge;
    `replay_rejected` — once the cursor has advanced past a period's due block, a second discharge at
    that block is rejected, so a discharged period is SPENT): the schedule is DERIVED from the block, so
    an early discharge is structurally impossible.
  * KEYSTONE (d) NOT-STRANDED — PROVED as ONE-STEP dischargeability (`due_period_dischargeable` +
    `obligationSettle_commits`). SCOPE: scheduler-fairness eventual settlement is a consensus/GST
    liveness statement, the SAME boundary the vault/allowance keystones had.

  * NON-VACUITY: a concrete world witnesses an on-schedule discharge (delivers + conserves + advances),
    the early-discharge rejection (one block before due), the wrong-amount rejection (over/under/skip),
    the no-replay tooth (a discharged period rejected, the next period live), and the schedule marching
    forward — all `#guard`-witnessed with real commit/deliver/conserve transitions. No keystone is
    vacuous.

RESIDUALS (honest, the SAME the whole settlement family carries): (1) this probe models the obligation
cell-program at the kernel-state level (`recKExecAsset` + record slots); wiring it through the full
forest gated executor (the `immutable`/`monotonic` caveats enforced by the LIVE executor on every
`SetField`) is carried by `Dregg2.Apps.Obligation` (the factory re-establishes the keystones on the
MINTED cell via `createCellFromFactoryChainA`). (2) the SDK-builder constructing the only sensible
discharge turn (binding `beneficiary` as the move target, and advancing the cursor by exactly `period`)
is the same off-program binding the settlement family's payout target is. (3) eventual-settlement
liveness is consensus-layer. None is obligation-specific.
-/

#assert_axioms obligationFactory_conforms
#assert_axioms obligationSettle_conserves
#assert_axioms obligationDischarge_conserves
#assert_axioms wrong_amount_rejected
#assert_axioms early_discharge_rejected
#assert_axioms replay_rejected
#assert_axioms obligationSettle_commits
#assert_axioms due_period_dischargeable

end Dregg2.Verify.ObligationFactoryProbe
