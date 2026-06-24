/-
# Dregg2.Verify.AllowanceFactoryProbe — the FALSIFICATION PROBE for the rate-limited ALLOWANCE as a
factory-born cell-program.

THE CLAIM UNDER TEST (the house-capacity weld, `docs/HOUSE-CAPACITIES-WELD-PLAN.md` — the SECOND house
room, after the vault):
*an ALLOWANCE — a sub-capability that may spend up to a fixed per-epoch CEILING of value, the ceiling
enforced so it can be neither EXCEEDED nor FORGED, refilling each epoch — is NOT a new kernel verb. It
is a COMPOSITION: a rate-limited spending CELL whose program enforces the ceiling, settled by the
already-wired `CreateCellFromFactory` + `Transfer` (spend) + `SetField` (track) triple.* An agent hands
a sub-agent an allowance — pocket money the sub-agent literally CANNOT overspend within an epoch. It
rides the SAME committed-cell substrate as the vault factory (`Dregg2.Verify.VaultFactoryProbe`), and
every gate it needs ALREADY EXISTS — the per-epoch ceiling is exactly the trustline `drawn ≤ ceiling`
`boundedBy` shape, the epoch clock is the timelock height clock.

This probe finds out whether the rebuild GENUINELY captures the allowance semantics. An honest PARTIAL
is as valuable as PASS; the verdict (§VERDICT) is PASS.

## The reframe (why an allowance is a factory cell, not a verb)

A rate-limited allowance is a vault with the one-terminal lifecycle replaced by a PERPETUAL OPEN cell
carrying a committed spend counter, and the release gate replaced by a CEILING gate:

  * the spendable VALUE lives in the allowance cell's OWN per-asset `bal` column (NOT a side-table,
    NOT a second slot) — a spend is an ordinary `move` OUT (allowance ⇒ beneficiary). So conservation
    is the EXISTING per-asset move law `recKExecAsset_conserves_per_asset`, inherited verbatim;
  * the per-epoch ceiling `limit_per_epoch`, the `epoch_length`, the `start`, and the `beneficiary`
    are FROZEN DEAL TERMS — committed at factory-mint, never re-writable. The terms-pin IS the
    no-forge tooth: a tampered ceiling diverges from the committed digest and is rejected;
  * the headroom is the committed `spent_this_epoch` counter measured against the committed ceiling.
    The CEILING is `spent_this_epoch + amount ≤ limit_per_epoch`. A spend that would push the epoch's
    running total over the ceiling is rejected — exactly the trustline `drawn ≤ ceiling` bound;
  * the epoch index for a block `b ≥ start` is `(b - start) / epoch_length`. The budget refills (the
    counter resets to 0) ONLY when the spend's block genuinely crosses into a STRICTLY LATER epoch
    than the committed cursor — an early reset is structurally impossible (the epoch is DERIVED from
    the block, never asserted), a backdated stale-epoch spend is rejected.

## The allowance SHAPE (the reusable deliverable)

slots (fields on the allowance cell's record):
  * `state`         — 0 = open (live). A perpetual allowance has NO terminal (it refills forever)
  * `beneficiary`   — the spend target              (immutable after open)
  * `limit`         — the per-epoch ceiling          (immutable — the no-forge tooth)
  * `epochLength`   — the epoch length in blocks      (immutable)
  * `start`         — the block epoch 0 begins         (immutable)
  * `currentEpoch`  — the committed epoch cursor       (monotone; reset is a genuine boundary crossing)
  * `spentThisEpoch`— value spent so far this epoch    (bounded by `limit`, reset at the boundary)
plus the spendable VALUE itself, held in the allowance cell's per-asset `bal` column. The
`allowanceFactory` installs the four deal-term immutables + the monotone cursor + the spent counter.

## The four allowance-safety keystones (all PROVED here)

  (a) CONSERVATION across spends — every spend is an ordinary per-asset `move`, so the kernel's value
      law applies VERBATIM; no bespoke quantity, no side-table.
  (b) THE CEILING (no over-limit) — a spend whose `(spent_baseline + amount)` exceeds the committed
      `limit_per_epoch` is rejected (`none`). With the budget refilled iff the spend genuinely crosses
      an epoch boundary, cumulative spend WITHIN an epoch can never exceed the ceiling.
  (c) NO FORGED / EARLY REFILL — the epoch is DERIVED from the spend's block, not asserted. A spend
      still inside the committed epoch with the ceiling exhausted is rejected (no early reset); a
      backdated spend landing in an EARLIER epoch than the cursor is rejected (no stale headroom).
  (d) VALUE NOT STRANDED (open ∧ within-budget ⇒ spendable) — a one-step liveness: any OPEN allowance
      whose spend fits the remaining budget, with a live distinct beneficiary holding the value in its
      `bal` column, SPENDS. No within-budget value is structurally trapped.

NEW file only. Reuses ONLY the proved per-asset move conservation + the SlotCaveat vocabulary; mirrors
`Dregg2.Verify.VaultFactoryProbe` exactly (allowance = vault with the one-terminal lifecycle replaced
by a perpetual counter, the release gate replaced by a per-epoch ceiling). Every keystone
`#assert_axioms`-pinned to `{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Exec.RecordKernel
import Dregg2.Exec.EffectsState

namespace Dregg2.Verify.AllowanceFactoryProbe

open Dregg2.Exec
open Dregg2.Exec.EffectsState (setField fieldOf setField_fieldOf)

/-! ## §1 — The allowance-cell SLOT layout (field names) + the lifecycle state. -/

/-- The lifecycle slot: 0 = open (live). A perpetual allowance has no terminal — it refills forever. -/
abbrev stateField : FieldName := "allowance.state"
/-- The spend target (frozen after open). The spendable VALUE lives in the cell's `bal` column. -/
abbrev beneficiaryField : FieldName := "allowance.beneficiary"
/-- The per-epoch CEILING (frozen — the no-forge tooth). -/
abbrev limitField : FieldName := "allowance.limit"
/-- The epoch length in blocks (frozen). -/
abbrev epochLengthField : FieldName := "allowance.epochLength"
/-- The block at which epoch 0 begins (frozen). -/
abbrev startField : FieldName := "allowance.start"
/-- The committed `current_epoch` cursor (monotone; reset is a genuine boundary crossing). -/
abbrev currentEpochField : FieldName := "allowance.currentEpoch"
/-- The committed `spent_this_epoch` counter (bounded by `limit`, reset at the boundary). -/
abbrev spentThisEpochField : FieldName := "allowance.spentThisEpoch"

/-- Lifecycle state literal: open (the only state — an allowance is perpetual). -/
abbrev sOpen : Int := 0

/-! ## §2 — The allowance FACTORY DESCRIPTOR: the published contract that mints allowance cells.

The `FactoryEntry` an allowance factory publishes. Its `caveats` ARE the allowance invariants — the
FOUR deal-term immutables (`beneficiary`, `limit`, `epochLength`, `start` — the ceiling is FROZEN, so a
tampered ceiling diverges from the commitment), the MONOTONE epoch cursor (reset only forward, at a
genuine boundary), and the `boundedBy` spent counter `0 ≤ spentThisEpoch ≤ limit` (the per-epoch
ceiling, exactly the trustline `drawn ≤ ceiling` shape). A cell minted by this factory carries these
for its WHOLE LIFE; the executor enforces them on every `SetField` via `stateStepGuarded`/`caveatsAdmit`. -/

/-- **`allowanceFactory beneficiary limit epochLength start` — the allowance factory descriptor.**
Installs: the four deal-term immutables (the no-forge ceiling), the monotone epoch cursor, and the
`boundedBy spentThisEpoch 0 limit` per-epoch ceiling. Initial state OPEN, nothing spent, epoch 0. -/
def allowanceFactory (beneficiary limit epochLength start : Int) : FactoryEntry where
  caveats :=
    [ SlotCaveat.immutable beneficiaryField
    , SlotCaveat.immutable limitField
    , SlotCaveat.immutable epochLengthField
    , SlotCaveat.immutable startField
    , SlotCaveat.monotonic currentEpochField
    , SlotCaveat.boundedBy spentThisEpochField 0 limit ]
  initialFields :=
    [ (stateField, sOpen)
    , (beneficiaryField, beneficiary)
    , (limitField, limit)
    , (epochLengthField, epochLength)
    , (startField, start)
    , (currentEpochField, 0)
    , (spentThisEpochField, 0) ]
  programVk := 0

/-- **`allowanceFactory_conforms`.** The allowance factory's OWN published initial state satisfies its
OWN caveats (no balance smuggling; the immutables permit their first write; the monotone cursor born at
0; the `boundedBy [0,limit]` spent counter born at 0 — which requires `0 ≤ limit`, the well-formed
ceiling). -/
theorem allowanceFactory_conforms (beneficiary limit epochLength start : Int) (hlim : 0 ≤ limit) :
    (allowanceFactory beneficiary limit epochLength start).conforms = true := by
  unfold allowanceFactory FactoryEntry.conforms FactoryEntry.initialFieldsNoBalance
  simp only [SlotCaveat.field, SlotCaveat.bornFresh, List.all_cons, List.all_nil,
    List.find?, beneficiaryField, limitField, epochLengthField,
    startField, currentEpochField, spentThisEpochField, stateField, balanceField]
  simp only [String.reduceEq, beq_iff_eq, reduceCtorEq, Bool.and_true, Bool.true_and,
    decide_eq_true_eq, le_refl, decide_true, Bool.and_self]
  -- remaining: 0 ≤ limit (the boundedBy [0, limit] ceiling born at 0 needs the well-formed ceiling)
  simpa using hlim

/-! ## §3 — The allowance cell STATE: a record cell holding the spendable value in its `bal` column. -/

/-- Read the allowance cell's frozen per-epoch ceiling slot. -/
def allowanceLimit (k : RecordKernelState) (e : CellId) : Int := fieldOf limitField (k.cell e)

/-- Read the allowance cell's frozen epoch-length slot. -/
def allowanceEpochLength (k : RecordKernelState) (e : CellId) : Int := fieldOf epochLengthField (k.cell e)

/-- Read the allowance cell's frozen start slot. -/
def allowanceStart (k : RecordKernelState) (e : CellId) : Int := fieldOf startField (k.cell e)

/-- Read the allowance cell's committed current-epoch cursor. -/
def allowanceEpoch (k : RecordKernelState) (e : CellId) : Int := fieldOf currentEpochField (k.cell e)

/-- Read the allowance cell's committed spent-this-epoch counter. -/
def allowanceSpent (k : RecordKernelState) (e : CellId) : Int := fieldOf spentThisEpochField (k.cell e)

/-- The epoch a block falls in: `(block - start) / epochLength` for `block ≥ start`, else `0` (blocks
before `start` belong to epoch 0's pre-history). The schedule's ground truth the committed cursor is
checked against — a reset that does not match a genuine boundary crossing is rejected. Mirrors the
Rust `AllowanceTerms.epoch_of`. -/
def epochOf (start epochLength block : Int) : Int :=
  if block < start then 0 else (block - start) / epochLength

/-! ## §4 — The allowance OPERATIONS as the 8-verb composition (write + move).

The allowance spend is the vault `settle` with the lifecycle replaced by the cursor advance and the
release gate replaced by the per-epoch CEILING. The headroom baseline refills to 0 iff the spend's
block crosses into a strictly later epoch than the committed cursor; the ceiling is `baseline + amount
≤ limit`. Both the cursor advance and the spent-counter write are ORDINARY `setField`s; the value
move is the ordinary `recKExecAsset`. -/

/-- The spent baseline at the spend's epoch: `0` if the spend's epoch is STRICTLY LATER than the
committed cursor (the budget genuinely refilled), else the committed `spent_this_epoch`. This is the
ONLY place a reset happens, and it is gated on a genuine boundary crossing (`spendEpoch > cursor`). -/
def spentBaseline (cursor committedSpent spendEpoch : Int) : Int :=
  if cursor < spendEpoch then 0 else committedSpent

/-- **`allowanceSettle` — the body of a spend: two `write`s (advance the cursor + the spent counter),
then a `move` of `amount` out.** All ORDINARY verbs (`setField` + the per-asset move `recKExecAsset`).
Fail-closed (the move's guard: authorized, non-negative, sufficient balance, distinct live cells). On
success: the cursor reads the spend's epoch, the spent counter reads `baseline + amount`, and the
value moves to `beneficiary`. -/
def allowanceSettle (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId)
    (spendEpoch newSpent amount : Int) : Option RecordKernelState :=
  let k1 : RecordKernelState :=
    { k with cell := fun c =>
        if c = e then
          setField spentThisEpochField (setField currentEpochField (k.cell e) (.int spendEpoch)) (.int newSpent)
        else k.cell c }
  recKExecAsset k1 { actor := e, src := e, dst := beneficiary, amt := amount } asset

/-- **`allowanceSpend` — the spend op (advance the epoch cursor + the spent counter + move to the
beneficiary), gated on the per-epoch CEILING.** Rejects (`none`) when: the spend's epoch is EARLIER
than the committed cursor (a backdated stale-epoch spend, no past-headroom reuse), or the post-spend
running total `baseline + amount` would EXCEED the committed ceiling `limit`. The epoch is DERIVED from
`atBlock` (`epochOf start epochLength atBlock`), so an early reset is structurally impossible. -/
def allowanceSpend (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId)
    (atBlock amount : Int) : Option RecordKernelState :=
  let cursor   := allowanceEpoch k e
  let spendEp  := epochOf (allowanceStart k e) (allowanceEpochLength k e) atBlock
  let baseline := spentBaseline cursor (allowanceSpent k e) spendEp
  let newSpent := baseline + amount
  if cursor ≤ spendEp ∧ newSpent ≤ allowanceLimit k e then
    allowanceSettle k e beneficiary asset spendEp newSpent amount
  else none

/-! ## §5 — KEYSTONE (a): CONSERVATION across spends (inherited from the ORDINARY move). -/

/-- **`allowanceSettle_conserves` — KEYSTONE (a), PROVED.** A committed spend preserves EVERY asset's
total supply: the moved value goes between two live accounts, and the two slot writes touch no balance.
The ordinary move conservation law — the allowance inherits it, no side-table. -/
theorem allowanceSettle_conserves {k k' : RecordKernelState} {e beneficiary : CellId} {asset : AssetId}
    {spendEpoch newSpent amount : Int}
    (h : allowanceSettle k e beneficiary asset spendEpoch newSpent amount = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold allowanceSettle at h
  set k1 : RecordKernelState :=
    { k with cell := fun c =>
        if c = e then
          setField spentThisEpochField (setField currentEpochField (k.cell e) (.int spendEpoch)) (.int newSpent)
        else k.cell c } with hk1
  have hbal : k1.bal = k.bal := rfl
  have hacc : k1.accounts = k.accounts := rfl
  have hconv := recKExecAsset_conserves_per_asset k1 k'
    { actor := e, src := e, dst := beneficiary, amt := amount } asset h b
  have hk1tot : recTotalAsset k1 b = recTotalAsset k b := by
    unfold recTotalAsset; rw [hacc, hbal]
  rw [hk1tot] at hconv
  exact hconv

/-- **`allowanceSpend_conserves` — KEYSTONE (a) for a spend.** A committed spend preserves every
asset's supply (the value is DELIVERED from the held column, not conjured). -/
theorem allowanceSpend_conserves {k k' : RecordKernelState} {e beneficiary : CellId} {asset : AssetId}
    {atBlock amount : Int}
    (h : allowanceSpend k e beneficiary asset atBlock amount = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold allowanceSpend at h
  by_cases hg : allowanceEpoch k e ≤ epochOf (allowanceStart k e) (allowanceEpochLength k e) atBlock
      ∧ spentBaseline (allowanceEpoch k e) (allowanceSpent k e)
          (epochOf (allowanceStart k e) (allowanceEpochLength k e) atBlock) + amount
        ≤ allowanceLimit k e
  · rw [if_pos hg] at h; exact allowanceSettle_conserves h b
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §6 — KEYSTONE (b): THE CEILING (no over-limit spend).

The spend's `newSpent ≤ limit` conjunct is the per-epoch ceiling. A spend whose `(baseline + amount)`
exceeds the committed ceiling fail-closes to `none`. Because the baseline refills to 0 ONLY at a
genuine epoch boundary, the cumulative spend WITHIN an epoch can never exceed the ceiling. -/

/-- **`over_ceiling_rejected` — KEYSTONE (b), PROVED.** A spend whose post-spend running total exceeds
the committed per-epoch ceiling is rejected — the budget cannot be over-drawn. -/
theorem over_ceiling_rejected (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId)
    (atBlock amount : Int)
    (hover : allowanceLimit k e
        < spentBaseline (allowanceEpoch k e) (allowanceSpent k e)
            (epochOf (allowanceStart k e) (allowanceEpochLength k e) atBlock) + amount) :
    allowanceSpend k e beneficiary asset atBlock amount = none := by
  unfold allowanceSpend
  rw [if_neg]
  rintro ⟨_, hle⟩
  exact absurd hle (by simp [not_le]; exact hover)

/-- **`at_ceiling_spends` — the NON-VACUITY companion (any gate has a live boundary).** A spend at
EXACTLY the ceiling (`baseline + amount = limit`), in the current epoch, with a `SpendReady`
beneficiary, COMMITS — the ceiling is a `≤` bound, not a `<` one, so spending the last unit of budget
is live. Stated as the contrapositive bound; the live witness is in §9. -/
theorem ceiling_is_inclusive (limit baseline amount : Int) (hfit : baseline + amount = limit) :
    ¬ (limit < baseline + amount) := by rw [hfit]; exact lt_irrefl limit

/-! ## §7 — KEYSTONE (c): NO FORGED / EARLY REFILL (the epoch is derived, not asserted).

The epoch is `epochOf start epochLength atBlock` — DERIVED from the spend's block, never claimed. An
early reset is therefore structurally impossible: you cannot refill by asserting a later epoch, only a
later BLOCK yields a later epoch. A backdated spend whose block lands in an EARLIER epoch than the
committed cursor (reusing a closed epoch's headroom) is rejected by the `cursor ≤ spendEpoch` conjunct.
The ceiling-with-no-refill (the spend stays in the committed epoch with the budget exhausted) is the
KEYSTONE (b) rejection — same epoch ⇒ baseline = committed spent ⇒ over the ceiling. -/

/-- **`stale_epoch_rejected` — KEYSTONE (c), the backdated-spend tooth.** A spend whose block lands in
an epoch STRICTLY EARLIER than the committed cursor is rejected — no reaching back into a closed epoch
to reuse its headroom. -/
theorem stale_epoch_rejected (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId)
    (atBlock amount : Int)
    (hstale : epochOf (allowanceStart k e) (allowanceEpochLength k e) atBlock < allowanceEpoch k e) :
    allowanceSpend k e beneficiary asset atBlock amount = none := by
  unfold allowanceSpend
  rw [if_neg]
  rintro ⟨hle, _⟩
  exact absurd hle (by simp [not_le]; exact hstale)

/-- **`no_early_refill` — KEYSTONE (c), the early-reset tooth.** When the spend's block lands in the
SAME epoch as the committed cursor (no genuine boundary crossing), the budget does NOT refill: the
baseline is the committed `spent_this_epoch`, so a spend over the remaining headroom is rejected by the
ceiling. There is no way to refill early — only a later block (a later epoch) resets the counter. -/
theorem no_early_refill (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId)
    (atBlock amount : Int)
    (hsame : epochOf (allowanceStart k e) (allowanceEpochLength k e) atBlock = allowanceEpoch k e)
    (hover : allowanceLimit k e < allowanceSpent k e + amount) :
    allowanceSpend k e beneficiary asset atBlock amount = none := by
  apply over_ceiling_rejected
  -- in the same epoch the baseline is the committed spent (no refill).
  have hbase : spentBaseline (allowanceEpoch k e) (allowanceSpent k e)
      (epochOf (allowanceStart k e) (allowanceEpochLength k e) atBlock) = allowanceSpent k e := by
    unfold spentBaseline
    rw [hsame, if_neg (lt_irrefl _)]
  rw [hbase]; exact hover

/-! ## §8 — KEYSTONE (d): VALUE NOT STRANDED (open ∧ within-budget ⇒ spendable). -/

/-- The move-admissibility hypothesis bundle for a spend: the allowance cell is authorized over itself
(it always is — `actor = src = e`), the amount is non-negative, the beneficiary is a distinct live
account, and the allowance cell is a live account holding the amount. -/
structure SpendReady (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId) (amount : Int) :
    Prop where
  amount_nonneg : 0 ≤ amount
  funded        : amount ≤ k.bal e asset
  distinct      : e ≠ beneficiary
  e_live        : e ∈ k.accounts
  beneficiary_live : beneficiary ∈ k.accounts
  e_lifecycle   : cellLifecycleLive k e = true

/-- A spend body COMMITS whenever the world is `SpendReady` (the move's fail-closed guard is
discharged: `actor = src = e` self-authorizes, the held amount is available by hypothesis). -/
theorem allowanceSettle_commits (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId)
    (spendEpoch newSpent amount : Int) (hr : SpendReady k e beneficiary asset amount) :
    (allowanceSettle k e beneficiary asset spendEpoch newSpent amount).isSome := by
  unfold allowanceSettle
  set k1 : RecordKernelState :=
    { k with cell := fun c =>
        if c = e then
          setField spentThisEpochField (setField currentEpochField (k.cell e) (.int spendEpoch)) (.int newSpent)
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

/-- **`within_budget_spendable` — KEYSTONE (d), PROVED.** An OPEN allowance whose spend fits the
remaining budget (not stale, `baseline + amount ≤ limit`), with a `SpendReady` beneficiary, SPENDS
(commits) — the within-budget value is deliverable, not trapped. SCOPE: this is one-step spendability
(the structural analog of the kernel verbs' guarantee). -/
theorem within_budget_spendable (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId)
    (atBlock amount : Int)
    (hfresh : allowanceEpoch k e ≤ epochOf (allowanceStart k e) (allowanceEpochLength k e) atBlock)
    (hfit : spentBaseline (allowanceEpoch k e) (allowanceSpent k e)
        (epochOf (allowanceStart k e) (allowanceEpochLength k e) atBlock) + amount
      ≤ allowanceLimit k e)
    (hr : SpendReady k e beneficiary asset amount) :
    (allowanceSpend k e beneficiary asset atBlock amount).isSome := by
  unfold allowanceSpend
  rw [if_pos ⟨hfresh, hfit⟩]
  exact allowanceSettle_commits k e beneficiary asset _ _ amount hr

/-! ## §9 — NON-VACUITY: a concrete allowance world + `#guard` witnesses. -/

/-- An allowance world. The ALLOWANCE CELL is cell `0` holding 1000 of asset 0 (the spendable value,
in its OWN `bal` column) with state OPEN, beneficiary 1, limit 100 (per-epoch ceiling), epochLength
1000, start 10000, cursor at epoch 0, nothing spent. The BENEFICIARY is cell `1` (holds 5 of asset 0).
All live. NO side-table. -/
def allowWorld : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun c =>
      if c = 0 then .record
        [ (stateField, .int sOpen), (beneficiaryField, .int 1), (limitField, .int 100)
        , (epochLengthField, .int 1000), (startField, .int 10000)
        , (currentEpochField, .int 0), (spentThisEpochField, .int 0) ]
      else .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun c a => if c = 0 then (if a = 0 then 1000 else 0)
                      else if c = 1 then (if a = 0 then 5 else 0) else 0 }

/-- The spend-ready bundle for spending 40 of allowWorld's allowance to beneficiary 1. -/
theorem allowWorld_spend_ready : SpendReady allowWorld 0 1 0 40 :=
  { amount_nonneg := by decide, funded := by decide, distinct := by decide,
    e_live := by decide, beneficiary_live := by decide, e_lifecycle := by decide }

-- (i) the allowance reads its committed terms (ceiling 100, epoch length 1000, start 10000, epoch 0):
#guard (allowanceLimit allowWorld 0 == 100)                                      -- true
#guard (allowanceEpochLength allowWorld 0 == 1000)                               -- true
#guard (allowanceStart allowWorld 0 == 10000)                                    -- true
#guard (allowanceEpoch allowWorld 0 == 0)                                        -- true
#guard (allowanceSpent allowWorld 0 == 0)                                        -- true

-- (ii) epochOf is the schedule's ground truth (0 before start, +1 each epoch length):
#guard (epochOf 10000 1000 9999 == 0)                                            -- pre-start = epoch 0
#guard (epochOf 10000 1000 10000 == 0)                                           -- epoch 0 begins at start
#guard (epochOf 10000 1000 10999 == 0)                                           -- still epoch 0
#guard (epochOf 10000 1000 11000 == 1)                                           -- epoch 1 at start + length
#guard (epochOf 10000 1000 12500 == 2)                                           -- epoch 2

-- (iii) a WITHIN-BUDGET spend (40 of the 100 ceiling, at block 10500 = epoch 0) COMMITS, delivers 40
--       to beneficiary 1, advances the spent counter; supply FIXED (pure move conservation):
#guard ((allowanceSpend allowWorld 0 1 0 10500 40).isSome)                       -- true (spent!)
#guard ((allowanceSpend allowWorld 0 1 0 10500 40).map (fun s => s.bal 1 0)) == some 45    -- beneficiary 5→45
#guard ((allowanceSpend allowWorld 0 1 0 10500 40).map (fun s => s.bal 0 0)) == some 960   -- allowance 1000→960
#guard ((allowanceSpend allowWorld 0 1 0 10500 40).map (fun s => allowanceSpent s 0)) == some 40
#guard ((allowanceSpend allowWorld 0 1 0 10500 40).map (fun s => allowanceEpoch s 0)) == some 0
#guard ((allowanceSpend allowWorld 0 1 0 10500 40).map (fun s => recTotalAsset s 0)) == some 1005
#guard (recTotalAsset allowWorld 0 == 1005)

-- (iv) a spend AT EXACTLY the ceiling (100, with nothing yet spent) is LIVE (the ≤ boundary):
#guard ((allowanceSpend allowWorld 0 1 0 10500 100).isSome)                      -- true (whole budget)
-- ...but ONE over the ceiling (101) is REJECTED (KEYSTONE b — no over-limit):
#guard ((allowanceSpend allowWorld 0 1 0 10500 101).isSome) == false             -- false (over ceiling)

/-- The allowance world AFTER spending 90 in epoch 0 (cursor 0, spent 90 — 10 of headroom remain). -/
def allowSpent90 : RecordKernelState :=
  { allowWorld with
    cell := fun c =>
      if c = 0 then Value.record
        [ (stateField, .int sOpen), (beneficiaryField, .int 1), (limitField, .int 100)
        , (epochLengthField, .int 1000), (startField, .int 10000)
        , (currentEpochField, .int 0), (spentThisEpochField, .int 90) ]
      else allowWorld.cell c
    bal := fun c a => if c = 0 then (if a = 0 then 910 else 0)
                      else if c = 1 then (if a = 0 then 95 else 0) else 0 }

-- (v) with 90 already spent, exactly the remaining 10 is LIVE; 11 is over the ceiling (90+11=101>100):
#guard (allowanceSpent allowSpent90 0 == 90)                                     -- true
#guard ((allowanceSpend allowSpent90 0 1 0 10600 10).isSome)                     -- true (last 10)
#guard ((allowanceSpend allowSpent90 0 1 0 10600 11).isSome) == false            -- false (over by 1)
-- ...and STILL inside epoch 0 (10900 < 11000) the budget does NOT refill — no early reset:
#guard (epochOf 10000 1000 10900 == 0)                                           -- still epoch 0
#guard ((allowanceSpend allowSpent90 0 1 0 10900 11).isSome) == false            -- false (no early refill)

-- (vi) EPOCH ROLLOVER: at block 11000 (epoch 1) the budget REFILLS — a fresh 100 is spendable, the
--      cursor advances to 1, and the counter resets (baseline 0, not the committed 90):
#guard (epochOf 10000 1000 11000 == 1)                                           -- epoch 1
#guard ((allowanceSpend allowSpent90 0 1 0 11000 100).isSome)                    -- true (refilled!)
#guard ((allowanceSpend allowSpent90 0 1 0 11000 100).map (fun s => allowanceEpoch s 0)) == some 1
#guard ((allowanceSpend allowSpent90 0 1 0 11000 100).map (fun s => allowanceSpent s 0)) == some 100
#guard ((allowanceSpend allowSpent90 0 1 0 11000 100).map (fun s => s.bal 1 0)) == some 195  -- 95→195

/-- The allowance world AFTER the cursor has advanced into epoch 2 (a later-epoch spend committed). -/
def allowEpoch2 : RecordKernelState :=
  { allowWorld with
    cell := fun c =>
      if c = 0 then Value.record
        [ (stateField, .int sOpen), (beneficiaryField, .int 1), (limitField, .int 100)
        , (epochLengthField, .int 1000), (startField, .int 10000)
        , (currentEpochField, .int 2), (spentThisEpochField, .int 30) ]
      else allowWorld.cell c }

-- (vii) STALE-EPOCH: a backdated spend whose block lands in epoch 0 < cursor 2 is REJECTED (KEYSTONE c):
#guard (allowanceEpoch allowEpoch2 0 == 2)                                       -- cursor at epoch 2
#guard (epochOf 10000 1000 10500 == 0)                                           -- block 10500 = epoch 0
#guard ((allowanceSpend allowEpoch2 0 1 0 10500 5).isSome) == false              -- false (backdated)
-- ...a current-epoch (2) spend within the remaining 70 is LIVE (non-vacuity):
#guard (epochOf 10000 1000 12600 == 2)                                           -- block 12600 = epoch 2
#guard ((allowanceSpend allowEpoch2 0 1 0 12600 70).isSome)                      -- true (30+70=100 fits)

-- (viii) the factory descriptor conforms (its own initial state is invariant-clean):
#guard ((allowanceFactory 1 100 1000 10000).conforms)                            -- true

/-! ## §VERDICT — PASS.

THE RATE-LIMITED ALLOWANCE IS FULLY CAPTURED as a factory-born cell-program + a ceiling-safety
contract, with NO side-table and NO bespoke conserved quantity:

  * FACTORY (`allowanceFactory`): four deal-term immutables (the FROZEN ceiling — no-forge) + a
    monotone epoch cursor + the `boundedBy spentThisEpoch 0 limit` per-epoch ceiling —
    `allowanceFactory_conforms` PROVED. Drawn entirely from the EXISTING SlotCaveat vocabulary; the
    ceiling is exactly the trustline `drawn ≤ ceiling` shape, the epoch clock the vault height clock.
    No new constraint kind needed.

  * KEYSTONE (a) CONSERVATION (`allowanceSettle_conserves`, `allowanceSpend_conserves`), INHERITED
    from the ordinary per-asset move law `recKExecAsset_conserves_per_asset`.
  * KEYSTONE (b) THE CEILING / no-over-limit (`over_ceiling_rejected`, `ceiling_is_inclusive`): a spend
    whose `baseline + amount` exceeds the committed ceiling is rejected; the ceiling is an inclusive
    `≤` bound (the last unit of budget is spendable).
  * KEYSTONE (c) NO FORGED / EARLY REFILL (`stale_epoch_rejected` — a backdated spend; `no_early_refill`
    — the same-epoch budget does not reset): the epoch is DERIVED from the block, so an early reset is
    structurally impossible and a stale spend is rejected.
  * KEYSTONE (d) NOT-STRANDED — PROVED as ONE-STEP spendability (`within_budget_spendable` +
    `allowanceSettle_commits`). SCOPE: scheduler-fairness eventual settlement is a consensus/GST
    liveness statement, the SAME boundary the vault keystones had.

  * NON-VACUITY: a concrete world witnesses a within-budget spend (delivers + conserves), the exact
    ceiling boundary (live) vs one over (rejected), the early-reset rejection (no refill mid-epoch), the
    genuine epoch rollover (refills to full ceiling), and the stale-epoch backdating rejection — all
    `#guard`-witnessed with real commit/deliver/conserve transitions. No keystone is vacuous.

RESIDUALS (honest, the SAME the whole settlement family carries): (1) this probe models the allowance
cell-program at the kernel-state level (`recKExecAsset` + record slots); wiring it through the full
forest gated executor (the `boundedBy`/`monotonic` caveats enforced by the LIVE executor on every
`SetField`) is carried by `Dregg2.Apps.Allowance` (the factory re-establishes the keystones on the
MINTED cell via `createCellFromFactoryChainA`). (2) the SDK-builder constructing the only sensible spend
turn (binding `beneficiary` as the move target) is the same off-program binding the settlement family's
payout target is. (3) eventual-settlement liveness is consensus-layer. None is allowance-specific.
-/

#assert_axioms allowanceFactory_conforms
#assert_axioms allowanceSettle_conserves
#assert_axioms allowanceSpend_conserves
#assert_axioms over_ceiling_rejected
#assert_axioms ceiling_is_inclusive
#assert_axioms stale_epoch_rejected
#assert_axioms no_early_refill
#assert_axioms allowanceSettle_commits
#assert_axioms within_budget_spendable

end Dregg2.Verify.AllowanceFactoryProbe
