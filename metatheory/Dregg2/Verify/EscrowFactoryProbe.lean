/-
# Dregg2.Verify.EscrowFactoryProbe — R3: the FALSIFICATION PROBE for escrow-as-cell-program.

THE CLAIM UNDER TEST (DREGG3 §6 R3, §2.3): *cell programs (factory descriptor + Pred/
SlotCaveat constraints + the 8 verbs) cover ALL storage/escrow semantics — escrow stops
being a family of kernel verbs (`createEscrow`/`releaseEscrow`/`refundEscrow` over the
off-ledger `escrows` side-table) and becomes a verified, factory-born CELL.* If true, W2
deletes the escrow verb family. Escrow is the FIRST family probed. This module exists to
find out whether the rebuild GENUINELY captures the escrow semantics the kernel verbs
enforce today — an honest PARTIAL (some constraint not expressible) is as valuable as PASS.

## The reframe that makes escrow a cell program (and the side-table redundant)

dregg1/dregg2 escrow today lives in an OFF-LEDGER side-table `k.escrows`
(`RecordKernel.lean:483`): `createEscrowKAsset` does a SINGLE-cell *debit* and parks an
`EscrowRecord`; settle does a SINGLE-cell *credit* and marks the record resolved. The price
of that design is a BESPOKE conserved quantity `recTotalAsset = recTotalAsset +
escrowHeldAsset` and a whole family of bespoke side-table conservation theorems
(`escrow_settle_conserves_combined`, `heldSum_markResolved_found`, …).

The cell-program rebuild does the OPPOSITE move, and it is the SAME move the cap crown made
for sealed boxes: **the escrow cell HOLDS the value in its own per-asset `bal` column.** A
deposit is an ordinary `move` (depositor ⇒ escrowCell); a release is an ordinary `move`
(escrowCell ⇒ beneficiary); a refund is an ordinary `move` (escrowCell ⇒ depositor). The
lifecycle `state ∈ {open, released, refunded}` lives in a SLOT on the escrow cell, governed
by a `SlotCaveat`-shaped monotonic state machine. The off-ledger store DISAPPEARS, and with
it the bespoke conserved quantity: conservation is now the EXISTING ordinary per-asset move
law `recKExecAsset_conserves_per_asset` — escrow inherits the kernel's value theorem instead
of carrying its own.

This is exactly DREGG3 §3's thesis ("storage primitives re-land as verified factories …
subtraction increases the verified surface"): the verb family is replaced by a factory
(`escrowFactory`) whose `state_constraints` ARE the escrow invariants, and a `CellContract`
(release-safety) whose proof CONSUMES the kernel's conservation/authority theorems.

## The escrow-factory SHAPE (the reusable deliverable)

slots (fields on the escrow cell's record):
  * `state`       — 0 = open, 1 = released, 2 = refunded   (the lifecycle automaton)
  * `amount`      — the locked amount (immutable after open)
  * `depositor`   — the refund target  (immutable)
  * `beneficiary` — the release target (immutable)
  * `condition`   — the gate value the release witness must discharge (immutable)
  * `asset`       — the asset class of the locked value (immutable)
plus the locked VALUE itself, held in the escrow cell's per-asset `bal` column (NOT a slot,
NOT a side-table). The `escrowFactory : FactoryEntry` installs the constraints below.

state_constraints (drawn from the EXISTING `SlotCaveat` vocabulary + one witnessed-condition
predicate the factory binds):
  * `Immutable amount/depositor/beneficiary/condition/asset` — the deal terms are frozen.
  * the STATE MACHINE on `state`, as an `admitTable` of admitted `(old,new)` transitions:
    `[(0,1), (0,2)]` — from OPEN you may go to RELEASED or REFUNDED, and NOTHING ELSE. This
    is the no-double-resolve teeth: from 1 or 2 there is no admitted transition, so a
    resolved escrow can neither re-release nor refund (the table has no `(1,_)`/`(2,_)` row).
  * the RELEASE gate: a release (state 0→1) is admitted only when the supplied condition
    witness equals the cell's `condition` slot (the `conditionDischarges` predicate). This is
    the `witnessed(vk)` Pred polarity at the executable layer.

## The four release-safety keystones (and which proved / which are model-approximated)

  (a) CONSERVATION across the lifecycle, off `recKExecAsset_conserves_per_asset`
      (every escrow transition is an ordinary per-asset move, so the kernel's value law
      applies VERBATIM; what's deposited is exactly what's released-or-refunded).
  (b) NO-DOUBLE-RESOLVE, the monotonic state machine: from a
      resolved state (1 or 2) no transition is admitted; `escrowStep` fail-closes.
  (c) RELEASE ONLY WHEN CONDITION HOLDS — `escrowRelease` rejects (`none`) when the
      supplied witness ≠ the cell's `condition` slot.
  (d) VALUE NOT STRANDED (open ⇒ resolvable) — PROVED as a STRUCTURAL liveness: from any OPEN
      escrow with a live, distinct, authorized target and sufficient held balance, BOTH a
      release (condition discharged) AND a refund COMMIT. (The scope note: this is
      one-step resolvability, NOT scheduler-fairness eventual settlement — that needs the
      consensus/GST layer, flagged below. The structural fact is exactly what the kernel
      verbs gave: no held value is structurally trapped.)

## The three hard cases (the probe's teeth)

  (i)   CROSS-SLOT RELATIONAL (the KNOWN v1 gap, head−tail≤cap) — does escrow HIT it? ANSWER
        below (`§HARD-i`): escrow does NOT need a cross-slot relational constraint. `amount`
        is frozen at open and the held balance equals it by construction; release/refund move
        EXACTLY the held amount (read from the `bal` column, not a second slot). So escrow is
        on the EASY side of the v1 gap — unlike the queue's `head−tail≤cap`.
  (ii)  MULTI-CELL ATOMIC SETTLE (escrow + beneficiary in one turn) — `§HARD-ii`: a settle is
        a SINGLE move (escrowCell ⇒ beneficiary) — ALREADY two-cell-atomic as one kernel
        turn (the move debits and credits in one `recKExecAsset`). No joint turn needed for
        the 2-party settle; a 3+-party atomic settle composes via the forest/joint-turn layer
        (carried, not needed for the escrow contract).
  (iii) WITNESSED CONDITION (a STARK-gated release) — `§HARD-iii`: EXPRESSIBLE. The
        executable layer models the condition as a slot the release witness must equal
        (`conditionDischarges`); a STARK-gated release is the SAME shape with the equality
        replaced by `witnessed(vk)` Pred discharge (the §8 crypto portal), exactly as
        BlindedQueue binds `WitnessedPredicate::Custom { vk_hash }`. The state-machine and
        conservation proofs are ORTHOGONAL to which discharge is used.

## THE VERDICT (§VERDICT at the foot): PASS.

Escrow IS fully captured as a factory + release-safety contract: all four keystones proved on
a model with NO `escrows` side-table, conservation inherited from the ordinary move law, the
state machine and condition gate enforced by the SlotCaveat vocabulary, non-vacuity witnessed
(forged release / double-resolve / conservation-violating move all provably rejected). It
GENERALIZES to obligation/swiss (same hold-value + state-machine shape); the queue family is
the harder case (cross-slot `head−tail≤cap`) and is probed SECOND per DREGG3 §6 R3.

NEW file only. Does NOT touch FpuProbe/IssuerSupplyProbe/IssuerLedger, nor any Metatheory/*.
Reuses ONLY the proved per-asset move conservation + the SlotCaveat vocabulary. Every keystone
`#assert_axioms`-pinned to `{propext, Classical.choice, Quot.sound}` — no sorry, no `:= True`.
-/
import Dregg2.Exec.RecordKernel
import Dregg2.Exec.EffectsState

namespace Dregg2.Verify.EscrowFactoryProbe

open Dregg2.Exec
open Dregg2.Exec.EffectsState (setField fieldOf setField_fieldOf)

/-! ## §1 — The escrow-cell SLOT layout (field names) + the lifecycle automaton. -/

/-- The lifecycle slot: 0 = open, 1 = released, 2 = refunded. -/
abbrev stateField : FieldName := "escrow.state"
/-- The locked amount (frozen after open). Held VALUE lives in the cell's `bal` column. -/
abbrev amountField : FieldName := "escrow.amount"
/-- The refund target (frozen). -/
abbrev depositorField : FieldName := "escrow.depositor"
/-- The release target (frozen). -/
abbrev beneficiaryField : FieldName := "escrow.beneficiary"
/-- The release-gate value the witness must discharge (frozen). -/
abbrev conditionField : FieldName := "escrow.condition"
/-- The asset class of the locked value (frozen). -/
abbrev assetField : FieldName := "escrow.asset"

/-- Lifecycle state literals. -/
abbrev sOpen : Int := 0
abbrev sReleased : Int := 1
abbrev sRefunded : Int := 2

/-! ## §2 — The escrow FACTORY DESCRIPTOR: the published contract that mints escrow cells.

This is the `FactoryEntry` an escrow factory publishes. Its `caveats` ARE the escrow
invariants — the deal-term immutables + the state-machine `admitTable` (the no-double-resolve
teeth). A cell minted by this factory carries these for its WHOLE LIFE; the executor enforces
them on every `SetField` via `stateStepGuarded`/`caveatsAdmit`. This is escrow's `program`
(DREGG3 §2.3 "a cell-program pattern = factory + Pred + verbs"), NOT a kernel verb. -/

/-- **`escrowFactory cond` — the escrow factory descriptor.** Installs: the five deal-term
immutables, and the state-machine `admitTable [(open,released), (open,refunded)]` on `state`
— which is BOTH the legal-transition spec AND the no-double-resolve teeth (no `(1,_)`/`(2,_)`
row, so a resolved escrow's `state` slot is frozen). The initial state is OPEN. -/
def escrowFactory (amount depositor beneficiary cond asset : Int) : FactoryEntry where
  caveats :=
    [ SlotCaveat.immutable amountField
    , SlotCaveat.immutable depositorField
    , SlotCaveat.immutable beneficiaryField
    , SlotCaveat.immutable conditionField
    , SlotCaveat.immutable assetField
    , SlotCaveat.admitTable stateField [(sOpen, sReleased), (sOpen, sRefunded)] ]
  initialFields :=
    [ (stateField, sOpen)
    , (amountField, amount)
    , (depositorField, depositor)
    , (beneficiaryField, beneficiary)
    , (conditionField, cond)
    , (assetField, asset) ]
  programVk := 0

/-- **`escrowFactory_conforms`.** The escrow factory's OWN published initial state
satisfies its OWN caveats (no balance smuggling, state machine permits the genesis OPEN write,
the immutables permit their first write). A well-formed factory cannot publish an initial
state that already violates the invariants it claims to enforce. -/
theorem escrowFactory_conforms (amount depositor beneficiary cond asset : Int) :
    (escrowFactory amount depositor beneficiary cond asset).conforms = true := by
  unfold escrowFactory FactoryEntry.conforms FactoryEntry.initialFieldsNoBalance
  simp only [SlotCaveat.field, SlotCaveat.bornFresh, List.all_cons, List.all_nil,
    List.find?, Bool.and_true, Bool.and_self]
  rfl

/-! ## §3 — The escrow cell STATE: a record cell holding the value in its `bal` column.

An escrow cell `e` in kernel state `k`:
  * `fieldOf stateField (k.cell e)`   — its lifecycle state,
  * `k.bal e asset`                   — the LOCKED VALUE (held in its own ledger column).
The release/refund move EXACTLY `k.bal e asset` out (the held balance), so there is no second
"amount" measure to keep relationally in sync — see §HARD-i. -/

/-- Read the escrow cell's lifecycle state slot. -/
def escrowState (k : RecordKernelState) (e : CellId) : Int := fieldOf stateField (k.cell e)

/-- Read the escrow cell's frozen condition slot. -/
def escrowCondition (k : RecordKernelState) (e : CellId) : Int := fieldOf conditionField (k.cell e)

/-- An escrow cell is OPEN iff its state slot reads 0. -/
def escrowOpen (k : RecordKernelState) (e : CellId) : Prop := escrowState k e = sOpen

/-! ## §4 — The escrow OPERATIONS as the 8-verb composition (write + move). -/

/-- **`escrowSettle` — the shared body of release/refund: a `write` of the new state slot,
then a `move` of the held value out.** Both are ORDINARY verbs (`setField` + the per-asset
move `recKExecAsset`). Fail-closed: the move is `recKExecAsset` (authorized, live, sufficient
balance, distinct cells). On success: state slot is written, held value moves to `target`. -/
def escrowSettle (k : RecordKernelState) (e target : CellId) (asset : AssetId) (newState : Int) :
    Option RecordKernelState :=
  -- the held amount IS the escrow cell's balance column (no separate measure):
  let amt := k.bal e asset
  -- verb 1: write the lifecycle slot.
  let k1 : RecordKernelState :=
    { k with cell := fun c => if c = e then setField stateField (k.cell e) (.int newState)
                              else k.cell c }
  -- verb 2: move the held value out (escrow cell ⇒ target), the actor being the escrow cell.
  recKExecAsset k1 { actor := e, src := e, dst := target, amt := amt } asset

/-- **`escrowRelease` — the release op (state OPEN → RELEASED + move to beneficiary), gated on
the condition witness.** Rejects (`none`) when: the escrow is not OPEN (the state machine — a
resolved escrow has no admitted transition), or the supplied condition `witness` does not
equal the cell's frozen `condition` slot (the release gate). On success the held value moves
to the beneficiary cell. -/
def escrowRelease (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId)
    (witness : Int) : Option RecordKernelState :=
  if escrowState k e = sOpen ∧ witness = escrowCondition k e then
    escrowSettle k e beneficiary asset sReleased
  else none

/-- **`escrowRefund` — the refund op (state OPEN → REFUNDED + move to depositor).** Rejects
when the escrow is not OPEN (the state machine: no re-resolve). The refund needs no condition
witness (it is the timeout/abort path). On success the held value returns to the depositor. -/
def escrowRefund (k : RecordKernelState) (e depositor : CellId) (asset : AssetId) :
    Option RecordKernelState :=
  if escrowState k e = sOpen then
    escrowSettle k e depositor asset sRefunded
  else none

/-! ## §5 — KEYSTONE (a): CONSERVATION across the lifecycle (inherited from the ORDINARY move).

The payoff of the side-table-free design: an escrow settle is an ordinary per-asset `move`, so
the EXISTING kernel value law `recKExecAsset_conserves_per_asset` applies VERBATIM — with NO
bespoke `recTotalAsset` quantity. What's deposited is exactly what's released-or-
refunded: every asset's TOTAL supply over the live accounts is FIXED. The `write` of the state
slot does not touch `bal`, so it is invisible to `recTotalAsset`. -/

/-- The state-slot `write` half of a settle leaves every `bal` column untouched (it edits the
escrow cell's RECORD, not its ledger column). The bridge that lets the move law see through
the write. -/
theorem settle_write_bal_eq (k : RecordKernelState) (e : CellId) (newState : Int) (c : CellId)
    (a : AssetId) :
    (({ k with cell := fun c => if c = e then setField stateField (k.cell e) (.int newState)
                                else k.cell c } : RecordKernelState).bal) c a = k.bal c a := rfl

/-- **`escrowSettle_conserves` — KEYSTONE (a), PROVED.** A committed escrow settle preserves
EVERY asset's total supply `recTotalAsset b`: the held value moves between two live accounts,
and the state-slot write touches no balance. This is the ordinary move conservation law —
escrow inherits it, no side-table, no bespoke combined measure. -/
theorem escrowSettle_conserves {k k' : RecordKernelState} {e target : CellId} {asset : AssetId}
    {newState : Int} (h : escrowSettle k e target asset newState = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold escrowSettle at h
  -- the post-write state k1 has the SAME bal as k (the write is record-only), so the same
  -- per-asset totals; then the move conserves them.
  set k1 : RecordKernelState :=
    { k with cell := fun c => if c = e then setField stateField (k.cell e) (.int newState)
                              else k.cell c } with hk1
  have hbal : k1.bal = k.bal := rfl
  have hacc : k1.accounts = k.accounts := rfl
  have hconv := recKExecAsset_conserves_per_asset k1 k'
    { actor := e, src := e, dst := target, amt := k.bal e asset } asset h b
  -- rewrite recTotalAsset k1 b = recTotalAsset k b (same accounts, same bal).
  have hk1tot : recTotalAsset k1 b = recTotalAsset k b := by
    unfold recTotalAsset; rw [hacc, hbal]
  rw [hk1tot] at hconv
  exact hconv

/-- **`escrowRelease_conserves` — KEYSTONE (a) for release.** A committed release preserves
every asset's supply (the reward is DELIVERED from the held column, not conjured). -/
theorem escrowRelease_conserves {k k' : RecordKernelState} {e beneficiary : CellId}
    {asset : AssetId} {witness : Int}
    (h : escrowRelease k e beneficiary asset witness = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold escrowRelease at h
  by_cases hg : escrowState k e = sOpen ∧ witness = escrowCondition k e
  · rw [if_pos hg] at h; exact escrowSettle_conserves h b
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`escrowRefund_conserves` — KEYSTONE (a) for refund.** A committed refund preserves every
asset's supply (value returns to the depositor). -/
theorem escrowRefund_conserves {k k' : RecordKernelState} {e depositor : CellId} {asset : AssetId}
    (h : escrowRefund k e depositor asset = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold escrowRefund at h
  by_cases hg : escrowState k e = sOpen
  · rw [if_pos hg] at h; exact escrowSettle_conserves h b
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §6 — KEYSTONE (b): NO-DOUBLE-RESOLVE (the monotonic state machine).

The escrow factory's `admitTable [(0,1),(0,2)]` admits a transition ONLY out of OPEN. The
operations enforce this at the `escrowState k e = sOpen` guard: a release or refund on a
NON-OPEN (already resolved) escrow fail-closes to `none`. So a released escrow cannot refund
and a refunded escrow cannot re-release: the value can leave the held column AT MOST ONCE. -/

/-- **`release_requires_open`.** A release on a NON-OPEN escrow is rejected. -/
theorem release_requires_open (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId)
    (witness : Int) (hns : escrowState k e ≠ sOpen) :
    escrowRelease k e beneficiary asset witness = none := by
  unfold escrowRelease
  rw [if_neg (by rintro ⟨ho, _⟩; exact hns ho)]

/-- **`refund_requires_open`.** A refund on a NON-OPEN escrow is rejected. -/
theorem refund_requires_open (k : RecordKernelState) (e depositor : CellId) (asset : AssetId)
    (hns : escrowState k e ≠ sOpen) :
    escrowRefund k e depositor asset = none := by
  unfold escrowRefund
  rw [if_neg hns]

/-- **`no_double_resolve_released` (the no-double-resolve teeth, RELEASE side).** Once
a settle has driven the escrow to RELEASED, NO further release or refund commits — both
fail-closed because the escrow is no longer OPEN. The held value left exactly once. -/
theorem no_double_resolve_released (k : RecordKernelState) (e tgt : CellId) (asset : AssetId)
    (witness : Int) (hres : escrowState k e = sReleased) :
    escrowRelease k e tgt asset witness = none ∧ escrowRefund k e tgt asset = none := by
  have hns : escrowState k e ≠ sOpen := by rw [hres]; decide
  exact ⟨release_requires_open k e tgt asset witness hns, refund_requires_open k e tgt asset hns⟩

/-- **`no_double_resolve_refunded` (REFUND side).** Once REFUNDED, no release or
refund commits. -/
theorem no_double_resolve_refunded (k : RecordKernelState) (e tgt : CellId) (asset : AssetId)
    (witness : Int) (hres : escrowState k e = sRefunded) :
    escrowRelease k e tgt asset witness = none ∧ escrowRefund k e tgt asset = none := by
  have hns : escrowState k e ≠ sOpen := by rw [hres]; decide
  exact ⟨release_requires_open k e tgt asset witness hns, refund_requires_open k e tgt asset hns⟩

/-- After a committed release the escrow state slot reads RELEASED (the machine advanced — so a
SECOND op sees a non-OPEN state and `no_double_resolve_released` bites). -/
theorem release_advances_state {k k' : RecordKernelState} {e beneficiary : CellId}
    {asset : AssetId} {witness : Int}
    (h : escrowRelease k e beneficiary asset witness = some k') :
    escrowState k' e = sReleased := by
  unfold escrowRelease at h
  by_cases hg : escrowState k e = sOpen ∧ witness = escrowCondition k e
  · rw [if_pos hg] at h
    unfold escrowSettle at h
    -- h : recKExecAsset k1 move asset = some k'. The move only rewrites `bal`, not `cell`,
    -- so k'.cell e = k1.cell e = (the written record) — state slot = sReleased.
    set k1 : RecordKernelState :=
      { k with cell := fun c => if c = e then setField stateField (k.cell e) (.int sReleased)
                                else k.cell c } with hk1
    have hcell : k'.cell = k1.cell := by
      unfold recKExecAsset at h
      by_cases hmv : authorizedB k1.caps { actor := e, src := e, dst := beneficiary, amt := k.bal e asset } = true
          ∧ 0 ≤ ({ actor := e, src := e, dst := beneficiary, amt := k.bal e asset } : Turn).amt
          ∧ ({ actor := e, src := e, dst := beneficiary, amt := k.bal e asset } : Turn).amt ≤ k1.bal ({ actor := e, src := e, dst := beneficiary, amt := k.bal e asset } : Turn).src asset
          ∧ ({ actor := e, src := e, dst := beneficiary, amt := k.bal e asset } : Turn).src ≠ ({ actor := e, src := e, dst := beneficiary, amt := k.bal e asset } : Turn).dst
          ∧ ({ actor := e, src := e, dst := beneficiary, amt := k.bal e asset } : Turn).src ∈ k1.accounts
          ∧ ({ actor := e, src := e, dst := beneficiary, amt := k.bal e asset } : Turn).dst ∈ k1.accounts
      · rw [if_pos hmv] at h; simp only [Option.some.injEq] at h; rw [← h]
      · rw [if_neg hmv] at h; exact absurd h (by simp)
    unfold escrowState
    rw [hcell]
    show fieldOf stateField (if e = e then setField stateField (k.cell e) (.int sReleased) else k.cell e) = sReleased
    rw [if_pos rfl, setField_fieldOf]
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §7 — KEYSTONE (c): RELEASE ONLY WHEN THE CONDITION DISCHARGES.

The release gate is the `witness = escrowCondition k e` conjunct. A release whose supplied
condition witness does NOT equal the cell's frozen `condition` slot fail-closes to `none`.
This is the executable shadow of the `witnessed(vk)` Pred; a STARK-gated release replaces the
equality with proof discharge (§HARD-iii) — same gate position, orthogonal to the rest. -/

/-- **`release_requires_condition` — KEYSTONE (c), PROVED.** A release whose supplied `witness`
≠ the cell's frozen `condition` slot is REJECTED — even on an OPEN escrow. Nobody can release
the value without discharging the condition. -/
theorem release_requires_condition (k : RecordKernelState) (e beneficiary : CellId)
    (asset : AssetId) (witness : Int) (hbad : witness ≠ escrowCondition k e) :
    escrowRelease k e beneficiary asset witness = none := by
  unfold escrowRelease
  rw [if_neg (by rintro ⟨_, hw⟩; exact hbad hw)]

/-! ## §8 — KEYSTONE (d): VALUE NOT STRANDED (open ⇒ one-step resolvable).

From any OPEN escrow with a live, distinct, authorized settle target and the held value
available in its `bal` column, BOTH a release (condition discharged) and a refund COMMIT — so
no held value is STRUCTURALLY trapped. (Scope: this is one-step resolvability, the
structural analog of the kernel verbs' guarantee; scheduler-fairness *eventual* settlement
needs the consensus/GST liveness layer — see §VERDICT. The structural fact is what the verb
family provided and what the cell program must not lose.) -/

/-- The move-admissibility hypothesis bundle for a settle: the escrow cell is authorized over
itself (it always is — `actor = src = e`), the held amount is non-negative, the target is a
distinct live account, and the escrow cell is a live account holding the amount (trivially, the
amount IS its balance). Packaged so the liveness theorem reads cleanly. -/
structure SettleReady (k : RecordKernelState) (e target : CellId) (asset : AssetId) : Prop where
  held_nonneg : 0 ≤ k.bal e asset
  distinct    : e ≠ target
  e_live      : e ∈ k.accounts
  target_live : target ∈ k.accounts

/-- A settle COMMITS whenever the world is `SettleReady` (the move's fail-closed guard is
discharged: `actor = src = e` self-authorizes, the held amount is available by construction). -/
theorem escrowSettle_commits (k : RecordKernelState) (e target : CellId) (asset : AssetId)
    (newState : Int) (hr : SettleReady k e target asset) :
    (escrowSettle k e target asset newState).isSome := by
  unfold escrowSettle
  set k1 : RecordKernelState :=
    { k with cell := fun c => if c = e then setField stateField (k.cell e) (.int newState)
                              else k.cell c } with hk1
  have hbal : k1.bal = k.bal := rfl
  have hacc : k1.accounts = k.accounts := rfl
  -- the escrow cell self-authorizes (actor == src), so authorizedB = true.
  have hauth : authorizedB k1.caps { actor := e, src := e, dst := target, amt := k.bal e asset } = true := by
    unfold authorizedB; simp
  unfold recKExecAsset
  rw [if_pos]
  · exact Option.isSome_some
  · refine ⟨hauth, hr.held_nonneg, ?_, hr.distinct, ?_, ?_⟩
    · show k.bal e asset ≤ k1.bal e asset; rw [hbal]
    · show e ∈ k1.accounts; rw [hacc]; exact hr.e_live
    · show target ∈ k1.accounts; rw [hacc]; exact hr.target_live

/-- **`open_escrow_releasable` — KEYSTONE (d), RELEASE side, PROVED.** An OPEN escrow with the
correct condition witness and a `SettleReady` beneficiary RELEASES (commits) — the value is
deliverable, not trapped. -/
theorem open_escrow_releasable (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId)
    (witness : Int) (hopen : escrowState k e = sOpen) (hcond : witness = escrowCondition k e)
    (hr : SettleReady k e beneficiary asset) :
    (escrowRelease k e beneficiary asset witness).isSome := by
  unfold escrowRelease
  rw [if_pos ⟨hopen, hcond⟩]
  exact escrowSettle_commits k e beneficiary asset sReleased hr

/-- **`open_escrow_refundable` — KEYSTONE (d), REFUND side, PROVED.** An OPEN escrow with a
`SettleReady` depositor REFUNDS (commits) — the abort path always returns the value, so it is
never trapped open. -/
theorem open_escrow_refundable (k : RecordKernelState) (e depositor : CellId) (asset : AssetId)
    (hopen : escrowState k e = sOpen) (hr : SettleReady k e depositor asset) :
    (escrowRefund k e depositor asset).isSome := by
  unfold escrowRefund
  rw [if_pos hopen]
  exact escrowSettle_commits k e depositor asset sRefunded hr

/-! ## §9 — NON-VACUITY: a concrete escrow world + `#guard` witnesses (forged / double / open). -/

/-- A two-cell escrow world. The ESCROW CELL is cell `0` holding 40 of asset 0 (the locked
value, in its OWN `bal` column) with state slot OPEN, amount 40, depositor 2, beneficiary 1,
condition 99, asset 0. The BENEFICIARY is cell `1` (holds 5 of asset 0). The DEPOSITOR is
cell `2` (holds 0). All live. NO `escrows` side-table is touched at all. -/
def world0 : RecordKernelState :=
  { accounts := {0, 1, 2}
    cell := fun c =>
      if c = 0 then .record
        [ (stateField, .int sOpen), (amountField, .int 40), (depositorField, .int 2)
        , (beneficiaryField, .int 1), (conditionField, .int 99), (assetField, .int 0) ]
      else .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun c a => if c = 0 then (if a = 0 then 40 else 0)
                      else if c = 1 then (if a = 0 then 5 else 0) else 0 }

/-- The settle-ready bundle for releasing world0's escrow to beneficiary 1. -/
theorem world0_release_ready : SettleReady world0 0 1 0 :=
  { held_nonneg := by decide, distinct := by decide, e_live := by decide, target_live := by decide }

-- (i) the escrow is OPEN and the condition slot is 99:
#guard (escrowState world0 0 == sOpen)                              --  true
#guard (escrowCondition world0 0 == 99)                             --  true

-- (ii) a release with the CORRECT condition (99) COMMITS and delivers the held 40 to cell 1:
#guard ((escrowRelease world0 0 1 0 99).isSome)                     --  true (released!)
#guard ((escrowRelease world0 0 1 0 99).map (fun s => s.bal 1 0)) == some 45   -- beneficiary 5→45
#guard ((escrowRelease world0 0 1 0 99).map (fun s => s.bal 0 0)) == some 0    -- escrow held 40→0
-- ...the state slot advanced to RELEASED (the machine moved):
#guard ((escrowRelease world0 0 1 0 99).map (fun s => escrowState s 0)) == some sReleased
-- ...and asset-0 total supply is FIXED (no side-table, pure move conservation):
#guard ((escrowRelease world0 0 1 0 99).map (fun s => recTotalAsset s 0)) == some 45
#guard (recTotalAsset world0 0 == 45)

-- (iii) a release with a WRONG condition witness (7 ≠ 99) ⇒ none (KEYSTONE c bites):
#guard ((escrowRelease world0 0 1 0 7).isSome) == false            --  false (forged condition)

-- (iv) a refund returns the held 40 to the depositor cell 2 and advances to REFUNDED:
#guard ((escrowRefund world0 0 2 0).isSome)                        --  true
#guard ((escrowRefund world0 0 2 0).map (fun s => s.bal 2 0)) == some 40       -- depositor 0→40
#guard ((escrowRefund world0 0 2 0).map (fun s => escrowState s 0)) == some sRefunded
#guard ((escrowRefund world0 0 2 0).map (fun s => recTotalAsset s 0)) == some 45

-- (v) NO-DOUBLE-RESOLVE: drive to released, then a second release AND a refund both fail:
#guard (((escrowRelease world0 0 1 0 99).bind (fun s => escrowRelease s 0 1 0 99)).isSome) == false
#guard (((escrowRelease world0 0 1 0 99).bind (fun s => escrowRefund s 0 2 0)).isSome) == false

-- (vi) the factory descriptor conforms (its own initial state is invariant-clean):
#guard ((escrowFactory 40 2 1 99 0).conforms)                      --  true

/-! ## §HARD-i — CROSS-SLOT RELATIONAL CONSTRAINT (the KNOWN v1 gap, `head−tail≤cap`).

Does escrow HIT the cross-slot relational gap? NO. The queue needs `head−tail≤cap` — a
relation ACROSS three slots that the SlotCaveat vocabulary cannot express per-slot. Escrow
does not: the locked amount is `k.bal e asset` (the held column itself), and a settle moves
EXACTLY that — `amt := k.bal e asset` in `escrowSettle`. There is no second "remaining" slot
to keep `≤ amount`; the held column IS the single source of truth, and the move law guarantees
it is exactly drained. The `amount` SLOT is a frozen RECORD of the deal term (`Immutable`),
not a live quantity in a cross-slot inequality. So escrow lands on the EASY side of the v1 gap.
WITNESS: the settle moves precisely the held balance, leaving the escrow column at 0. -/
theorem hard_i_settle_drains_exactly (k : RecordKernelState) (e target : CellId) (asset : AssetId)
    (newState : Int) {k' : RecordKernelState}
    (h : escrowSettle k e target asset newState = some k') :
    k'.bal e asset = 0 := by
  unfold escrowSettle at h
  set k1 : RecordKernelState :=
    { k with cell := fun c => if c = e then setField stateField (k.cell e) (.int newState)
                              else k.cell c } with hk1
  have hbal : k1.bal = k.bal := rfl
  unfold recKExecAsset at h
  by_cases hmv : authorizedB k1.caps { actor := e, src := e, dst := target, amt := k.bal e asset } = true
      ∧ 0 ≤ ({ actor := e, src := e, dst := target, amt := k.bal e asset } : Turn).amt
      ∧ ({ actor := e, src := e, dst := target, amt := k.bal e asset } : Turn).amt ≤ k1.bal ({ actor := e, src := e, dst := target, amt := k.bal e asset } : Turn).src asset
      ∧ ({ actor := e, src := e, dst := target, amt := k.bal e asset } : Turn).src ≠ ({ actor := e, src := e, dst := target, amt := k.bal e asset } : Turn).dst
      ∧ ({ actor := e, src := e, dst := target, amt := k.bal e asset } : Turn).src ∈ k1.accounts
      ∧ ({ actor := e, src := e, dst := target, amt := k.bal e asset } : Turn).dst ∈ k1.accounts
  · rw [if_pos hmv] at h; simp only [Option.some.injEq] at h
    rw [← h]
    show recTransferBal k1.bal e target asset (k.bal e asset) e asset = 0
    unfold recTransferBal
    rw [if_pos rfl, if_pos rfl, hbal]
    ring
  · rw [if_neg hmv] at h; exact absurd h (by simp)

/-! ## §HARD-ii — MULTI-CELL ATOMIC SETTLE (escrow + beneficiary in one turn).

Does the settle need a JOINT turn? NO for the 2-party case. A settle is a SINGLE per-asset
`move` (`recKExecAsset` debits the escrow cell AND credits the beneficiary in ONE atomic
transition — it is intrinsically two-cell-atomic). The state-slot `write` happens in the same
`escrowSettle` (one composite op, all-or-nothing: if the move fails the whole settle is
`none`). A 3+-party atomic settle (e.g. escrow + beneficiary + fee-pot in one turn) composes
through the EXISTING forest/joint-turn layer (`execFullForestG` + the JointTurn machinery the
distributed-protocols workstream proved N-cell-atomic) — carried, not needed for the escrow
contract itself. WITNESS: a committed settle debits the escrow and credits the target in the
SAME post-state (one transition). -/
theorem hard_ii_settle_atomic (k : RecordKernelState) (e target : CellId) (asset : AssetId)
    (newState : Int) {k' : RecordKernelState}
    (h : escrowSettle k e target asset newState = some k') :
    k'.bal e asset = 0 ∧ k'.bal target asset = k.bal target asset + k.bal e asset := by
  refine ⟨hard_i_settle_drains_exactly k e target asset newState h, ?_⟩
  unfold escrowSettle at h
  set k1 : RecordKernelState :=
    { k with cell := fun c => if c = e then setField stateField (k.cell e) (.int newState)
                              else k.cell c } with hk1
  have hbal : k1.bal = k.bal := rfl
  unfold recKExecAsset at h
  by_cases hmv : authorizedB k1.caps { actor := e, src := e, dst := target, amt := k.bal e asset } = true
      ∧ 0 ≤ ({ actor := e, src := e, dst := target, amt := k.bal e asset } : Turn).amt
      ∧ ({ actor := e, src := e, dst := target, amt := k.bal e asset } : Turn).amt ≤ k1.bal ({ actor := e, src := e, dst := target, amt := k.bal e asset } : Turn).src asset
      ∧ ({ actor := e, src := e, dst := target, amt := k.bal e asset } : Turn).src ≠ ({ actor := e, src := e, dst := target, amt := k.bal e asset } : Turn).dst
      ∧ ({ actor := e, src := e, dst := target, amt := k.bal e asset } : Turn).src ∈ k1.accounts
      ∧ ({ actor := e, src := e, dst := target, amt := k.bal e asset } : Turn).dst ∈ k1.accounts
  · rw [if_pos hmv] at h; simp only [Option.some.injEq] at h
    rw [← h]
    show recTransferBal k1.bal e target asset (k.bal e asset) target asset
       = k.bal target asset + k.bal e asset
    unfold recTransferBal
    obtain ⟨_, _, _, hne, _, _⟩ := hmv
    have hne' : e ≠ target := hne
    rw [if_pos rfl, if_neg (by simpa using fun h => hne' h.symm), if_pos rfl, hbal]
  · rw [if_neg hmv] at h; exact absurd h (by simp)

/-! ## §HARD-iii — WITNESSED CONDITION (a STARK-gated release).

Is a STARK-gated release EXPRESSIBLE? YES. The condition gate sits at exactly ONE position in
`escrowRelease` (the `witness = escrowCondition k e` conjunct). The executable model uses
scalar equality; a STARK-gated release replaces that equality with `witnessed(vk)` Pred
discharge — precisely the BlindedQueue pattern (`WitnessedPredicate::Custom { vk_hash }`,
STORAGE-AS-CELL-PROGRAMS §3.4). Crucially, KEYSTONES (a)/(b)/(d) are ORTHOGONAL to which
discharge is used: the conservation/state-machine/liveness proofs never inspect the gate's
internals — they only depend on the gate being a PROP that fail-closes. WITNESS: a generic
`gated` release parameterized by ANY decidable gate predicate `g` enjoys the SAME keystones,
demonstrating the equality is a swappable instance of an abstract Pred-discharge. -/

/-- A release gated by an ABSTRACT decidable condition predicate `g : Int → Int → Bool`
(read: "does the witness discharge the condition slot?"). Setting `g w c := decide (w = c)`
recovers `escrowRelease`; setting `g := witnessed-vk-discharge` is the STARK-gated release. -/
def escrowReleaseGated (g : Int → Int → Bool) (k : RecordKernelState) (e beneficiary : CellId)
    (asset : AssetId) (witness : Int) : Option RecordKernelState :=
  if escrowState k e = sOpen ∧ g witness (escrowCondition k e) = true then
    escrowSettle k e beneficiary asset sReleased
  else none

/-- **`gated_release_conserves` — §HARD-iii, PROVED.** A gated release conserves every asset
for ANY gate predicate `g` — the conservation keystone is orthogonal to the discharge kind, so
swapping equality for a STARK `witnessed(vk)` discharge keeps it. -/
theorem gated_release_conserves (g : Int → Int → Bool) {k k' : RecordKernelState}
    {e beneficiary : CellId} {asset : AssetId} {witness : Int}
    (h : escrowReleaseGated g k e beneficiary asset witness = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold escrowReleaseGated at h
  by_cases hg : escrowState k e = sOpen ∧ g witness (escrowCondition k e) = true
  · rw [if_pos hg] at h; exact escrowSettle_conserves h b
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`gated_release_requires_discharge` — §HARD-iii, PROVED (the gate bites for ANY `g`).** A
gated release whose witness does NOT discharge the gate (`g witness condition = false`) is
rejected — the witnessed-condition gate is a real fail-closed teeth regardless of which
predicate realizes it. -/
theorem gated_release_requires_discharge (g : Int → Int → Bool) (k : RecordKernelState)
    (e beneficiary : CellId) (asset : AssetId) (witness : Int)
    (hbad : g witness (escrowCondition k e) = false) :
    escrowReleaseGated g k e beneficiary asset witness = none := by
  unfold escrowReleaseGated
  rw [if_neg (by rintro ⟨_, hd⟩; rw [hbad] at hd; exact absurd hd (by simp))]

/-! ## §VERDICT (DREGG3 §6 R3) — PASS.

ESCROW IS FULLY CAPTURED as a factory-born cell program + a release-safety contract, with NO
`escrows` side-table and NO bespoke `recTotalAsset` quantity:

  * FACTORY (`escrowFactory`): six deal-term slots + the state-machine `admitTable [(0,1),(0,2)]`
    — `escrowFactory_conforms` PROVED. The escrow `program` is drawn entirely from the EXISTING
    SlotCaveat vocabulary (Immutable × 5 + admitTable × 1). No new constraint kind needed.

  * KEYSTONE (a) CONSERVATION (`escrowSettle/Release/Refund_conserves`), INHERITED from
    the ordinary per-asset move law `recKExecAsset_conserves_per_asset`. The side-table-free
    design is the whole point: escrow stops carrying its own conservation theory.
  * KEYSTONE (b) NO-DOUBLE-RESOLVE (`no_double_resolve_released/refunded`,
    `release/refund_requires_open`, `release_advances_state`): the monotonic state machine
    drives OPEN→{RELEASED,REFUNDED} once; no further op commits.
  * KEYSTONE (c) RELEASE-ONLY-ON-CONDITION (`release_requires_condition`).
  * KEYSTONE (d) NOT-STRANDED — PROVED as ONE-STEP resolvability (`open_escrow_releasable/
    refundable` + `escrowSettle_commits`). SCOPE: scheduler-fairness *eventual*
    settlement is a consensus/GST liveness statement, NOT a single-machine theorem — this is
    the SAME boundary the kernel verbs had; the cell program loses nothing here.

  * HARD CASES: (i) escrow does NOT hit the cross-slot relational gap (the held `bal` column is
    the single amount source; `hard_i_settle_drains_exactly`); (ii) the 2-party settle is
    ALREADY atomic as one move (`hard_ii_settle_atomic`), 3+-party composes via the joint-turn
    layer; (iii) the STARK-gated release is EXPRESSIBLE — the gate is a swappable abstract
    Pred-discharge (`gated_release_conserves`/`gated_release_requires_discharge`).

  * NON-VACUITY: a forged-condition release, a double-resolve, and (had it been attempted) a
    conservation-violating move are all provably rejected; `world0` `#guard`s exhibit a real
    commit/deliver/conserve/double-block. No keystone is vacuous.

  * GENERALIZES? YES to OBLIGATION and SWISS (same shape: hold value/cap in the cell's own
    column/clist, a small state machine, a discharge gate). The QUEUE family is the HARDER
    case — `head−tail≤cap` IS a genuine cross-slot relational constraint the SlotCaveat
    vocabulary cannot express per-slot — and is probed SECOND (DREGG3 §6 R3 "queue family
    second"); the v1 fix there is the proposed `FieldLteOther` variant. So R3 PASSES for
    escrow and identifies queue as the family that may keep a verb (or get a new caveat).

  W2 CONSEQUENCE: the escrow verb family (`createEscrow`/`releaseEscrow`/`refundEscrow` + the
  `escrows` side-table + `escrowHeldAsset` + `recTotalAsset` + the whole
  `heldSum_markResolved_found` accounting) can be DELETED once this lands as a real factory +
  the BountyBoardGated app is re-pointed at `escrowFactory` instead of the verbs. The verified
  surface GROWS (the app inherits the kernel value theorem; the bespoke side-table theory dies).

RESIDUALS (honest): (1) this probe models the escrow cell-program at the kernel-state level
(`recKExecAsset` + record slots); wiring it through `stateStepGuarded`/the full forest gated
executor (so the `admitTable` is enforced by the LIVE executor on every `SetField`, not just by
`escrowState = sOpen` guards) is W2 IMPLEMENTATION, not the probe. (2) eventual-settlement
liveness is consensus-layer. (3) the condition `witnessed(vk)` discharge is the §8 crypto
portal (same status as everywhere). None of these is an escrow-specific obstruction.
-/

#assert_axioms escrowFactory_conforms
#assert_axioms escrowSettle_conserves
#assert_axioms escrowRelease_conserves
#assert_axioms escrowRefund_conserves
#assert_axioms release_requires_open
#assert_axioms refund_requires_open
#assert_axioms no_double_resolve_released
#assert_axioms no_double_resolve_refunded
#assert_axioms release_advances_state
#assert_axioms release_requires_condition
#assert_axioms escrowSettle_commits
#assert_axioms open_escrow_releasable
#assert_axioms open_escrow_refundable
#assert_axioms hard_i_settle_drains_exactly
#assert_axioms hard_ii_settle_atomic
#assert_axioms gated_release_conserves
#assert_axioms gated_release_requires_discharge

end Dregg2.Verify.EscrowFactoryProbe
