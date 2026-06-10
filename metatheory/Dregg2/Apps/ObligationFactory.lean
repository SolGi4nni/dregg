/-
# Dregg2.Apps.ObligationFactory — W2: the OBLIGATION family as a factory-born CELL PROGRAM.

THE CLAIM, DISCHARGED HERE (DREGG3 §6 R3 generalization, per the EscrowFactoryProbe §VERDICT
"GENERALIZES? YES to OBLIGATION"): *the obligation verb family
(`createObligation`/`fulfillObligation`/`slashObligation`) is escrow-shaped and needs NO new
constraint atom — it re-lands as a verified, factory-born CELL holding its BONDED value in its
own `bal` column, exactly as escrow holds the locked value.* The queue-probe verdict said
obligation is escrow-shaped; this module MAKES it so and proves the four obligation-safety
keystones, so W2 can DELETE the obligation verb family (§DELETION).

## The reframe (the SAME move escrow made)

An obligation in the verb world is a debit + an off-ledger record (the obligor posts a BOND,
parked in a side-table; fulfilment returns it, a slash forfeits it to the obligee). The price
is a bespoke held-value measure and bespoke conservation theory. The cell-program rebuild does
the OPPOSITE: **the obligation cell HOLDS the bond in its own per-asset `bal` column.** Posting
the bond is an ordinary `move` (obligor ⇒ obligationCell); a fulfilment is an ordinary `move`
(obligationCell ⇒ obligor, the bond returns); a slash is an ordinary `move`
(obligationCell ⇒ obligee, the bond is forfeit). The lifecycle `state ∈ {open, fulfilled,
slashed}` is a SLOT governed by a `SlotCaveat` state machine. No side-table; conservation is
the EXISTING ordinary per-asset move law `recKExecAsset_conserves_per_asset`.

## The obligation-factory SHAPE (mirrors escrow; deal terms are IMMUTABLE)

slots (fields on the obligation cell's record):
  * `state`       — 0 = open, 1 = fulfilled, 2 = slashed   (the lifecycle automaton)
  * `bond_amount` — the bonded amount (immutable after open; frozen RECORD of the deal term)
  * `obligor`     — who posted the bond, the fulfilment-return target  (immutable)
  * `obligee`     — the slash-forfeit target  (immutable)
  * `condition`   — the gate value the fulfilment witness must discharge (immutable)
  * `deadline`    — the slash gate value (immutable; the slash witness must reach it)
plus the BONDED VALUE itself, held in the obligation cell's per-asset `bal` column (NOT a slot,
NOT a side-table). The `obligationFactory : FactoryEntry` installs the constraints.

state_constraints (drawn ENTIRELY from the EXISTING `SlotCaveat` vocabulary — NO new atom):
  * `Immutable bond_amount/obligor/obligee/condition/deadline` — the deal terms are frozen.
  * the STATE MACHINE on `state`, as an `admitTable` of admitted `(old,new)` transitions:
    `[(0,1), (0,2)]` — from OPEN you may go to FULFILLED or SLASHED, and NOTHING ELSE. This is
    the no-double-resolve teeth: from 1 or 2 there is no admitted transition, so a resolved
    obligation can neither re-fulfil nor re-slash.
  * the FULFILMENT gate: a fulfilment (0→1) is admitted only when the supplied condition witness
    equals the cell's `condition` slot (the obligation was DISCHARGED).
  * the SLASH gate: a slash (0→2) is admitted only when the supplied witness equals the cell's
    `deadline` slot AND does NOT discharge the `condition` — i.e. an UNCONDITIONED slash (one
    that would forfeit a bond whose condition was actually met, or one with no deadline witness)
    is REJECTED. The bond can be forfeit only on a genuine, gated failure.

## The four obligation-safety keystones (mirroring escrow's four)

  (a) CONSERVATION across the lifecycle, off `recKExecAsset_conserves_per_asset`
      (every obligation transition is an ordinary per-asset move; what's bonded is exactly what's
      returned-or-forfeit).
  (b) NO-DOUBLE-RESOLVE, the monotonic state machine: from a resolved
      state (1 or 2) no transition is admitted; the op fail-closes.
  (c) FULFIL/SLASH GATED BY CONDITION/DEADLINE — `fulfilObligation` rejects when the
      supplied witness ≠ the `condition` slot; `slashObligation` rejects when the supplied witness
      ≠ the `deadline` slot OR when the condition WAS discharged (an unconditioned slash).
  (d) BOND NOT STRANDED (open ⇒ resolvable) — PROVED as one-step resolvability: from any OPEN
      obligation with a live, distinct, authorized target and the bonded value held, BOTH a
      fulfilment (condition discharged) AND a slash (deadline reached, condition failed) COMMIT,
      and a committed settle DRAINS the bond column to 0 (the bond is never trapped). HONEST
      SCOPE: one-step resolvability, NOT scheduler-fairness eventual settlement (consensus/GST).

## Non-vacuity

`obWorld` is a concrete obligation cell (bond 40, obligor 2, obligee 1, condition 99, deadline
77). `#guard` witnesses: a correct fulfilment (witness 99) returns the bond to the obligor and
advances to FULFILLED; a correct slash (deadline 77, condition NOT met) forfeits the bond to the
obligee and advances to SLASHED; a DOUBLE-RESOLVE (fulfil then fulfil/slash) is rejected; an
UNCONDITIONED slash (one whose deadline witness is wrong, AND one attempted while the condition
holds) is rejected. Both the §VERDICT teeth are exhibited as real rejections.

## §DELETION-READINESS (land-before-kill)

Enumerated at the foot (`§DELETION`). NOTHING is deleted here.

NEW file only. Imports the escrow factory executor + the escrow probe (for the proved per-asset
move-conservation lift and the `SlotCaveat`/`setField`/`fieldOf` vocabulary). Does NOT edit
`Dregg2.lean`, any shared mod/import file, or the kernel. Every keystone `#assert_axioms`-pinned
to `{propext, Classical.choice, Quot.sound}` — no sorry, no `:= True`, no `native_decide`.
-/
import Dregg2.Exec.RecordKernel
import Dregg2.Exec.EffectsState
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Apps.ObligationFactory

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Cap)
open Dregg2.Exec.EffectsState (setField fieldOf setField_fieldOf)

/-! ## §1 — The obligation-cell SLOT layout + the lifecycle automaton. -/

/-- The lifecycle slot: 0 = open, 1 = fulfilled, 2 = slashed. -/
abbrev stateField : FieldName := "obligation.state"
/-- The bonded amount (frozen after open). Held VALUE lives in the cell's `bal` column. -/
abbrev bondField : FieldName := "obligation.bond_amount"
/-- The obligor (frozen) — who posted the bond, the fulfilment-return target. -/
abbrev obligorField : FieldName := "obligation.obligor"
/-- The obligee (frozen) — the slash-forfeit target. -/
abbrev obligeeField : FieldName := "obligation.obligee"
/-- The fulfilment-gate value the witness must discharge (frozen). -/
abbrev conditionField : FieldName := "obligation.condition"
/-- The slash-gate value (the deadline witness must reach it) (frozen). -/
abbrev deadlineField : FieldName := "obligation.deadline"

/-- Lifecycle state literals. -/
abbrev sOpen : Int := 0
abbrev sFulfilled : Int := 1
abbrev sSlashed : Int := 2

/-! ## §2 — The obligation FACTORY DESCRIPTOR.

The `FactoryEntry` an obligation factory publishes. Its `caveats` ARE the obligation invariants:
the five deal-term immutables + the state-machine `admitTable [(open,fulfilled),(open,slashed)]`
(the no-double-resolve teeth). A cell minted by this factory carries these for its WHOLE LIFE;
the executor enforces them on every `SetField` via `stateStepGuarded`. Drawn ENTIRELY from the
existing SlotCaveat vocabulary (Immutable × 5 + admitTable × 1) — NO new constraint atom. -/

/-- **`obligationFactory` — the obligation factory descriptor.** Installs the five deal-term
immutables and the state-machine `admitTable [(open,fulfilled),(open,slashed)]` on `state`
(BOTH the legal-transition spec AND the no-double-resolve teeth). Initial state is OPEN. -/
def obligationFactory (bond obligor obligee cond deadline : Int) : FactoryEntry where
  caveats :=
    [ SlotCaveat.immutable bondField
    , SlotCaveat.immutable obligorField
    , SlotCaveat.immutable obligeeField
    , SlotCaveat.immutable conditionField
    , SlotCaveat.immutable deadlineField
    , SlotCaveat.admitTable stateField [(sOpen, sFulfilled), (sOpen, sSlashed)] ]
  initialFields :=
    [ (stateField, sOpen)
    , (bondField, bond)
    , (obligorField, obligor)
    , (obligeeField, obligee)
    , (conditionField, cond)
    , (deadlineField, deadline) ]
  programVk := 0

/-- **`obligationFactory_conforms`.** The factory's OWN published initial state satisfies
its OWN caveats (no balance smuggling, state machine permits the genesis OPEN write, the
immutables permit their first write). -/
theorem obligationFactory_conforms (bond obligor obligee cond deadline : Int) :
    (obligationFactory bond obligor obligee cond deadline).conforms = true := by
  unfold obligationFactory FactoryEntry.conforms FactoryEntry.initialFieldsNoBalance
  simp only [SlotCaveat.field, SlotCaveat.bornFresh, List.all_cons, List.all_nil,
    List.find?, Bool.and_true, Bool.and_self]
  rfl

/-! ## §3 — The obligation cell STATE: a record cell holding the bond in its `bal` column. -/

/-- Read the obligation cell's lifecycle state slot. -/
def obState (k : RecordKernelState) (e : CellId) : Int := fieldOf stateField (k.cell e)

/-- Read the obligation cell's frozen condition slot. -/
def obCondition (k : RecordKernelState) (e : CellId) : Int := fieldOf conditionField (k.cell e)

/-- Read the obligation cell's frozen deadline slot. -/
def obDeadline (k : RecordKernelState) (e : CellId) : Int := fieldOf deadlineField (k.cell e)

/-- An obligation cell is OPEN iff its state slot reads 0. -/
def obOpen (k : RecordKernelState) (e : CellId) : Prop := obState k e = sOpen

/-! ## §4 — The obligation OPERATIONS as the verb composition (write + move). -/

/-- **`obSettle` — the shared body of fulfil/slash: a `write` of the new state slot, then a
`move` of the bonded value out.** Both are ORDINARY verbs (`setField` + the per-asset move
`recKExecAsset`). Fail-closed (the move is `recKExecAsset`: authorized, live, sufficient balance,
distinct cells). On success the state slot is written and the bonded value moves to `target`. -/
def obSettle (k : RecordKernelState) (e target : CellId) (asset : AssetId) (newState : Int) :
    Option RecordKernelState :=
  let amt := k.bal e asset
  let k1 : RecordKernelState :=
    { k with cell := fun c => if c = e then setField stateField (k.cell e) (.int newState)
                              else k.cell c }
  recKExecAsset k1 { actor := e, src := e, dst := target, amt := amt } asset

/-- **`fulfilObligation` — the fulfilment op (state OPEN → FULFILLED + bond returns to obligor),
gated on the condition witness.** Rejects (`none`) when the obligation is not OPEN (the state
machine), or the supplied condition `witness` does not equal the cell's frozen `condition` slot
(the obligation was not discharged). On success the bond returns to the obligor. -/
def fulfilObligation (k : RecordKernelState) (e obligor : CellId) (asset : AssetId)
    (witness : Int) : Option RecordKernelState :=
  if obState k e = sOpen ∧ witness = obCondition k e then
    obSettle k e obligor asset sFulfilled
  else none

/-- **`slashObligation` — the slash op (state OPEN → SLASHED + bond forfeit to obligee).** Rejects
when the obligation is not OPEN (the state machine), OR the supplied `dlWitness` ≠ the cell's
frozen `deadline` slot, OR the `condWitness` DOES discharge the `condition` (an UNCONDITIONED
slash — forfeiting a bond whose condition was actually met — is rejected). On success the bond
is forfeit to the obligee. -/
def slashObligation (k : RecordKernelState) (e obligee : CellId) (asset : AssetId)
    (dlWitness condWitness : Int) : Option RecordKernelState :=
  if obState k e = sOpen ∧ dlWitness = obDeadline k e ∧ condWitness ≠ obCondition k e then
    obSettle k e obligee asset sSlashed
  else none

/-! ## §5 — KEYSTONE (a): CONSERVATION across the lifecycle (inherited from the ORDINARY move).

An obligation settle is an ordinary per-asset `move`, so the EXISTING kernel value law
`recKExecAsset_conserves_per_asset` applies VERBATIM — with NO bespoke held-value quantity. What's
bonded is exactly what's returned-or-forfeit; every asset's TOTAL supply is FIXED. The `write` of
the state slot does not touch `bal`, so it is invisible to `recTotalAsset`. -/

/-- **`obSettle_conserves` — KEYSTONE (a), PROVED.** A committed obligation settle preserves EVERY
asset's total supply: the bonded value moves between two live accounts, and the state-slot write
touches no balance. The ordinary move conservation law — inherited, no side-table. -/
theorem obSettle_conserves {k k' : RecordKernelState} {e target : CellId} {asset : AssetId}
    {newState : Int} (h : obSettle k e target asset newState = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold obSettle at h
  set k1 : RecordKernelState :=
    { k with cell := fun c => if c = e then setField stateField (k.cell e) (.int newState)
                              else k.cell c } with hk1
  have hbal : k1.bal = k.bal := rfl
  have hacc : k1.accounts = k.accounts := rfl
  have hconv := recKExecAsset_conserves_per_asset k1 k'
    { actor := e, src := e, dst := target, amt := k.bal e asset } asset h b
  have hk1tot : recTotalAsset k1 b = recTotalAsset k b := by
    unfold recTotalAsset; rw [hacc, hbal]
  rw [hk1tot] at hconv
  exact hconv

/-- **`fulfil_conserves` — KEYSTONE (a) for fulfilment.** A committed fulfilment preserves every
asset's supply (the bond is RETURNED from the held column, not conjured). -/
theorem fulfil_conserves {k k' : RecordKernelState} {e obligor : CellId} {asset : AssetId}
    {witness : Int} (h : fulfilObligation k e obligor asset witness = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold fulfilObligation at h
  by_cases hg : obState k e = sOpen ∧ witness = obCondition k e
  · rw [if_pos hg] at h; exact obSettle_conserves h b
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`slash_conserves` — KEYSTONE (a) for slash.** A committed slash preserves every asset's
supply (the bond is FORFEIT to the obligee, not destroyed). -/
theorem slash_conserves {k k' : RecordKernelState} {e obligee : CellId} {asset : AssetId}
    {dlWitness condWitness : Int}
    (h : slashObligation k e obligee asset dlWitness condWitness = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold slashObligation at h
  by_cases hg : obState k e = sOpen ∧ dlWitness = obDeadline k e ∧ condWitness ≠ obCondition k e
  · rw [if_pos hg] at h; exact obSettle_conserves h b
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §6 — KEYSTONE (b): NO-DOUBLE-RESOLVE (the monotonic state machine).

The factory's `admitTable [(0,1),(0,2)]` admits a transition ONLY out of OPEN. The operations
enforce it at the `obState k e = sOpen` guard: a fulfil or slash on a NON-OPEN (already resolved)
obligation fail-closes. So a fulfilled obligation cannot slash and a slashed one cannot re-fulfil:
the bond can leave the held column AT MOST ONCE. -/

/-- **`fulfil_requires_open`.** A fulfilment on a NON-OPEN obligation is rejected. -/
theorem fulfil_requires_open (k : RecordKernelState) (e obligor : CellId) (asset : AssetId)
    (witness : Int) (hns : obState k e ≠ sOpen) :
    fulfilObligation k e obligor asset witness = none := by
  unfold fulfilObligation
  rw [if_neg (by rintro ⟨ho, _⟩; exact hns ho)]

/-- **`slash_requires_open`.** A slash on a NON-OPEN obligation is rejected. -/
theorem slash_requires_open (k : RecordKernelState) (e obligee : CellId) (asset : AssetId)
    (dlWitness condWitness : Int) (hns : obState k e ≠ sOpen) :
    slashObligation k e obligee asset dlWitness condWitness = none := by
  unfold slashObligation
  rw [if_neg (by rintro ⟨ho, _⟩; exact hns ho)]

/-- **`no_double_resolve_fulfilled` (RESOLVE side).** Once a settle has driven the
obligation to FULFILLED, NO further fulfil or slash commits — both fail-closed.
The bond left exactly once. -/
theorem no_double_resolve_fulfilled (k : RecordKernelState) (e tgt : CellId) (asset : AssetId)
    (witness dlWitness condWitness : Int) (hres : obState k e = sFulfilled) :
    fulfilObligation k e tgt asset witness = none
    ∧ slashObligation k e tgt asset dlWitness condWitness = none := by
  have hns : obState k e ≠ sOpen := by rw [hres]; decide
  exact ⟨fulfil_requires_open k e tgt asset witness hns,
         slash_requires_open k e tgt asset dlWitness condWitness hns⟩

/-- **`no_double_resolve_slashed`.** Once SLASHED, no fulfil or slash commits. -/
theorem no_double_resolve_slashed (k : RecordKernelState) (e tgt : CellId) (asset : AssetId)
    (witness dlWitness condWitness : Int) (hres : obState k e = sSlashed) :
    fulfilObligation k e tgt asset witness = none
    ∧ slashObligation k e tgt asset dlWitness condWitness = none := by
  have hns : obState k e ≠ sOpen := by rw [hres]; decide
  exact ⟨fulfil_requires_open k e tgt asset witness hns,
         slash_requires_open k e tgt asset dlWitness condWitness hns⟩

/-- After a committed fulfilment the state slot reads FULFILLED (the machine advanced — so a
SECOND op sees a non-OPEN state and `no_double_resolve_fulfilled` bites). -/
theorem fulfil_advances_state {k k' : RecordKernelState} {e obligor : CellId} {asset : AssetId}
    {witness : Int} (h : fulfilObligation k e obligor asset witness = some k') :
    obState k' e = sFulfilled := by
  unfold fulfilObligation at h
  by_cases hg : obState k e = sOpen ∧ witness = obCondition k e
  · rw [if_pos hg] at h
    unfold obSettle at h
    set k1 : RecordKernelState :=
      { k with cell := fun c => if c = e then setField stateField (k.cell e) (.int sFulfilled)
                                else k.cell c } with hk1
    have hcell : k'.cell = k1.cell := by
      unfold recKExecAsset at h
      by_cases hmv : authorizedB k1.caps { actor := e, src := e, dst := obligor, amt := k.bal e asset } = true
          ∧ 0 ≤ ({ actor := e, src := e, dst := obligor, amt := k.bal e asset } : Turn).amt
          ∧ ({ actor := e, src := e, dst := obligor, amt := k.bal e asset } : Turn).amt ≤ k1.bal ({ actor := e, src := e, dst := obligor, amt := k.bal e asset } : Turn).src asset
          ∧ ({ actor := e, src := e, dst := obligor, amt := k.bal e asset } : Turn).src ≠ ({ actor := e, src := e, dst := obligor, amt := k.bal e asset } : Turn).dst
          ∧ ({ actor := e, src := e, dst := obligor, amt := k.bal e asset } : Turn).src ∈ k1.accounts
          ∧ ({ actor := e, src := e, dst := obligor, amt := k.bal e asset } : Turn).dst ∈ k1.accounts
      · rw [if_pos hmv] at h; simp only [Option.some.injEq] at h; rw [← h]
      · rw [if_neg hmv] at h; exact absurd h (by simp)
    unfold obState
    rw [hcell]
    show fieldOf stateField (if e = e then setField stateField (k.cell e) (.int sFulfilled) else k.cell e) = sFulfilled
    rw [if_pos rfl, setField_fieldOf]
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §7 — KEYSTONE (c): FULFIL/SLASH GATED BY CONDITION/DEADLINE.

The fulfilment gate is `witness = obCondition k e`; the slash gate is `dlWitness = obDeadline k e
∧ condWitness ≠ obCondition k e`. A fulfilment whose witness ≠ the frozen `condition` is rejected;
a slash is rejected unless the deadline witness is correct AND the condition was NOT discharged
(an UNCONDITIONED slash — one that would forfeit a met obligation — fail-closes). -/

/-- **`fulfil_requires_condition` — KEYSTONE (c), fulfil side, PROVED.** A fulfilment whose
supplied `witness` ≠ the cell's frozen `condition` slot is REJECTED — even on an OPEN obligation.
The bond cannot be returned without discharging the obligation. -/
theorem fulfil_requires_condition (k : RecordKernelState) (e obligor : CellId) (asset : AssetId)
    (witness : Int) (hbad : witness ≠ obCondition k e) :
    fulfilObligation k e obligor asset witness = none := by
  unfold fulfilObligation
  rw [if_neg (by rintro ⟨_, hw⟩; exact hbad hw)]

/-- **`slash_requires_deadline` — KEYSTONE (c), slash side (deadline), PROVED.** A slash whose
supplied `dlWitness` ≠ the cell's frozen `deadline` slot is REJECTED. The bond cannot be forfeit
without the deadline gate discharging. -/
theorem slash_requires_deadline (k : RecordKernelState) (e obligee : CellId) (asset : AssetId)
    (dlWitness condWitness : Int) (hbad : dlWitness ≠ obDeadline k e) :
    slashObligation k e obligee asset dlWitness condWitness = none := by
  unfold slashObligation
  rw [if_neg (by rintro ⟨_, hd, _⟩; exact hbad hd)]

/-- **`slash_rejects_when_condition_met` — KEYSTONE (c), slash side (UNCONDITIONED), PROVED.** A
slash whose `condWitness` DOES discharge the `condition` (the obligation was actually met) is
REJECTED — even with a correct deadline witness and an OPEN obligation. A bond that satisfied its
condition cannot be forfeit. THIS is the unconditioned-slash teeth. -/
theorem slash_rejects_when_condition_met (k : RecordKernelState) (e obligee : CellId)
    (asset : AssetId) (dlWitness condWitness : Int) (hmet : condWitness = obCondition k e) :
    slashObligation k e obligee asset dlWitness condWitness = none := by
  unfold slashObligation
  rw [if_neg (by rintro ⟨_, _, hbad⟩; exact hbad hmet)]

/-! ## §8 — KEYSTONE (d): BOND NOT STRANDED (open ⇒ one-step resolvable + drained).

From any OPEN obligation with a live, distinct, authorized settle target and the bonded value in
its `bal` column, BOTH a fulfilment (condition discharged) and a slash (deadline reached,
condition failed) COMMIT, and a committed settle DRAINS the bond column to 0 — so no bonded value
is STRUCTURALLY trapped. (SCOPE: one-step resolvability, the structural analog of the verb
guarantee; scheduler-fairness *eventual* settlement is the consensus/GST layer.) -/

/-- The move-admissibility bundle for an obligation settle (mirrors escrow's `SettleReady`): the
cell self-authorizes (`actor = src = e`), the bonded amount is non-negative, the target is a
distinct live account, and the cell is a live account holding the bond. -/
structure SettleReady (k : RecordKernelState) (e target : CellId) (asset : AssetId) : Prop where
  held_nonneg : 0 ≤ k.bal e asset
  distinct    : e ≠ target
  e_live      : e ∈ k.accounts
  target_live : target ∈ k.accounts

/-- An obligation settle COMMITS whenever the world is `SettleReady`. -/
theorem obSettle_commits (k : RecordKernelState) (e target : CellId) (asset : AssetId)
    (newState : Int) (hr : SettleReady k e target asset) :
    (obSettle k e target asset newState).isSome := by
  unfold obSettle
  set k1 : RecordKernelState :=
    { k with cell := fun c => if c = e then setField stateField (k.cell e) (.int newState)
                              else k.cell c } with hk1
  have hbal : k1.bal = k.bal := rfl
  have hacc : k1.accounts = k.accounts := rfl
  have hauth : authorizedB k1.caps { actor := e, src := e, dst := target, amt := k.bal e asset } = true := by
    unfold authorizedB; simp
  unfold recKExecAsset
  rw [if_pos]
  · exact Option.isSome_some
  · refine ⟨hauth, hr.held_nonneg, ?_, hr.distinct, ?_, ?_⟩
    · show k.bal e asset ≤ k1.bal e asset; rw [hbal]
    · show e ∈ k1.accounts; rw [hacc]; exact hr.e_live
    · show target ∈ k1.accounts; rw [hacc]; exact hr.target_live

/-- A committed obligation settle DRAINS the bond column to 0 (the bond left exactly — there is no
second "remaining" slot to keep in sync; the held column IS the single source of truth). The
factory-shape proof that the bond is never partially stranded. -/
theorem obSettle_drains_exactly (k : RecordKernelState) (e target : CellId) (asset : AssetId)
    (newState : Int) {k' : RecordKernelState}
    (h : obSettle k e target asset newState = some k') :
    k'.bal e asset = 0 := by
  unfold obSettle at h
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

/-- **`open_obligation_fulfilable` — KEYSTONE (d), FULFIL side, PROVED.** An OPEN obligation with
the correct condition witness and a `SettleReady` obligor FULFILS (commits) — the bond is
returnable, not trapped. -/
theorem open_obligation_fulfilable (k : RecordKernelState) (e obligor : CellId) (asset : AssetId)
    (witness : Int) (hopen : obState k e = sOpen) (hcond : witness = obCondition k e)
    (hr : SettleReady k e obligor asset) :
    (fulfilObligation k e obligor asset witness).isSome := by
  unfold fulfilObligation
  rw [if_pos ⟨hopen, hcond⟩]
  exact obSettle_commits k e obligor asset sFulfilled hr

/-- **`open_obligation_slashable` — KEYSTONE (d), SLASH side, PROVED.** An OPEN obligation past its
deadline (correct deadline witness) whose condition was NOT met and a `SettleReady` obligee SLASHES
(commits) — the forfeit path always delivers the bond, so it is never trapped open. -/
theorem open_obligation_slashable (k : RecordKernelState) (e obligee : CellId) (asset : AssetId)
    (dlWitness condWitness : Int) (hopen : obState k e = sOpen)
    (hdl : dlWitness = obDeadline k e) (hfail : condWitness ≠ obCondition k e)
    (hr : SettleReady k e obligee asset) :
    (slashObligation k e obligee asset dlWitness condWitness).isSome := by
  unfold slashObligation
  rw [if_pos ⟨hopen, hdl, hfail⟩]
  exact obSettle_commits k e obligee asset sSlashed hr

/-! ## §8b — The SETTLE-LIVENESS teeth (the bond can never move into a non-account).

In the factory shape the bond moves by an ordinary `recKExecAsset`, whose OWN fail-closed guard
requires `dst ∈ accounts`. A settle whose target is NOT a live account is rejected for FREE — the
bond can never be forfeit/returned into a frozen/absent cell (which would silently destroy it,
breaking conservation). -/

/-- **`settle_requires_live_target`.** A settle whose `target` is NOT a live account is
rejected (`none`) — the move cannot deliver the bond into a non-account. -/
theorem settle_requires_live_target {k : RecordKernelState} {e target : CellId} {asset : AssetId}
    {newState : Int} (hdead : target ∉ k.accounts) :
    obSettle k e target asset newState = none := by
  unfold obSettle recKExecAsset
  rw [if_neg]
  rintro ⟨_, _, _, _, _, htgt⟩
  exact hdead htgt

/-- **`fulfil_requires_live_obligor`.** A fulfilment whose obligor target is not a live
account is rejected. -/
theorem fulfil_requires_live_obligor {k : RecordKernelState} {e obligor : CellId} {asset : AssetId}
    {witness : Int} (hdead : obligor ∉ k.accounts) :
    fulfilObligation k e obligor asset witness = none := by
  unfold fulfilObligation
  by_cases hg : obState k e = sOpen ∧ witness = obCondition k e
  · rw [if_pos hg]; exact settle_requires_live_target hdead
  · rw [if_neg hg]

/-- **`slash_requires_live_obligee`.** A slash whose obligee target is not a live account
is rejected. -/
theorem slash_requires_live_obligee {k : RecordKernelState} {e obligee : CellId} {asset : AssetId}
    {dlWitness condWitness : Int} (hdead : obligee ∉ k.accounts) :
    slashObligation k e obligee asset dlWitness condWitness = none := by
  unfold slashObligation
  by_cases hg : obState k e = sOpen ∧ dlWitness = obDeadline k e ∧ condWitness ≠ obCondition k e
  · rw [if_pos hg]; exact settle_requires_live_target hdead
  · rw [if_neg hg]

/-! ## §9 — MINTING the obligation cell through the REAL factory executor.

`mintObligationCell` is `createCellFromFactoryChainA` over a kernel whose `factories` registry
publishes the obligation factory. The minted cell carries the factory's caveats (the state
machine + deal-term immutables) AND its initial fields (state=open + the frozen terms), installed
by the executor, for life — so the no-double-resolve teeth are enforced by `stateStepGuarded` on
every later `SetField`, exactly as escrow's. -/

/-- A kernel factory registry publishing the obligation factory at content-addressed key `vk`. -/
def obligationRegistry (vk : Nat) (bond obligor obligee cond deadline : Int) :
    List (Nat × FactoryEntry) :=
  [(vk, obligationFactory bond obligor obligee cond deadline)]

/-- The registry resolves the obligation factory at exactly its published key. -/
theorem obligationRegistry_finds (vk : Nat) (bond obligor obligee cond deadline : Int) :
    findFactory (obligationRegistry vk bond obligor obligee cond deadline) vk
      = some (obligationFactory bond obligor obligee cond deadline) := by
  simp [obligationRegistry, findFactory]

/-- Mint an obligation cell from the obligation factory at key `vk` (the real factory executor). -/
def mintObligationCell (s : RecChainedState) (actor obCell : CellId) (vk : Int) :
    Option RecChainedState :=
  createCellFromFactoryChainA s actor obCell vk

/-- **`mintObligationCell_installs_state_machine` (the factory keystone, obligation-
specialized).** A minted obligation cell carries EXACTLY the factory's caveats — the five deal-term
immutables PLUS the no-double-resolve state machine `admitTable [(open,fulfilled),(open,slashed)]`
— installed by the executor, so `stateStepGuarded` enforces them on every later `SetField`. -/
theorem mintObligationCell_installs_state_machine {s s' : RecChainedState} {actor obCell : CellId}
    {vk : Int} (e : FactoryEntry)
    (hreg : findFactory s.kernel.factories vk.toNat = some e)
    (h : mintObligationCell s actor obCell vk = some s') :
    s'.kernel.slotCaveats obCell = e.caveats := by
  obtain ⟨e', hfind, hcav⟩ := createCellFromFactoryChainA_installs_program h
  rw [hreg] at hfind
  rw [← (Option.some.injEq _ _).mp hfind] at hcav
  exact hcav

/-- **`mintObligationCell_caveats`.** When the registry IS `obligationRegistry vk …`, the
minted cell concretely carries the obligation state machine + deal-term immutables. -/
theorem mintObligationCell_caveats {s s' : RecChainedState} {actor obCell : CellId} {vk : Int}
    {bond obligor obligee cond deadline : Int}
    (hreg : s.kernel.factories = obligationRegistry vk.toNat bond obligor obligee cond deadline)
    (h : mintObligationCell s actor obCell vk = some s') :
    s'.kernel.slotCaveats obCell
      = (obligationFactory bond obligor obligee cond deadline).caveats := by
  have hfind : findFactory s.kernel.factories vk.toNat
      = some (obligationFactory bond obligor obligee cond deadline) := by
    rw [hreg]; exact obligationRegistry_finds vk.toNat bond obligor obligee cond deadline
  exact mintObligationCell_installs_state_machine _ hfind h

/-- **`mintObligationCell_neutral`.** Minting an obligation cell is conservation-NEUTRAL
for every asset (the cell is born EMPTY; the bond is posted SEPARATELY by an ordinary move). -/
theorem mintObligationCell_neutral {s s' : RecChainedState} {actor obCell : CellId} {vk : Int}
    (b : AssetId) (h : mintObligationCell s actor obCell vk = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  createCellFromFactoryChainA_neutral b h

/-- **`mintObligationCell_grows_accounts`.** A minted obligation cell IS a live account
(the mint has teeth; neutrality is not a no-op). -/
theorem mintObligationCell_grows_accounts {s s' : RecChainedState} {actor obCell : CellId} {vk : Int}
    (h : mintObligationCell s actor obCell vk = some s') :
    obCell ∈ s'.kernel.accounts :=
  createCellFromFactoryChainA_grows_accounts h

/-- **`mintObligationCell_unknown_factory_fails` (fail-closed).** Minting against an
unknown factory key never mints. The obligation program cannot be conjured without a published
factory. -/
theorem mintObligationCell_unknown_factory_fails (s : RecChainedState) (actor obCell : CellId)
    (vk : Int) (h : findFactory s.kernel.factories vk.toNat = none) :
    mintObligationCell s actor obCell vk = none :=
  createCellFromFactoryChainA_unknown_factory_fails s actor obCell vk h

/-- **`postBond` — fund the obligation cell: move `amt` of `asset` from the obligor into the
obligation cell's `bal` column.** An ordinary authorized per-asset move (`recKExecAsset`);
fail-closed (authorized, non-negative, sufficient balance, distinct live cells). -/
def postBond (k : RecordKernelState) (obligor obCell : CellId) (asset : AssetId) (amt : ℤ) :
    Option RecordKernelState :=
  recKExecAsset k { actor := obligor, src := obligor, dst := obCell, amt := amt } asset

/-- **`postBond_conserves`.** A committed bond posting preserves every asset's total
supply (the value moves between two live accounts — funding the bond, not minting it). -/
theorem postBond_conserves {k k' : RecordKernelState} {obligor obCell : CellId}
    {asset : AssetId} {amt : ℤ} (h : postBond k obligor obCell asset amt = some k')
    (b : AssetId) : recTotalAsset k' b = recTotalAsset k b :=
  recKExecAsset_conserves_per_asset k k'
    { actor := obligor, src := obligor, dst := obCell, amt := amt } asset h b

/-! ## §10 — NON-VACUITY: a factory-born obligation, end to end. -/

/-- A three-cell obligation world. The OBLIGATION CELL is cell `0` (bond 40 of asset 0 in its
OWN `bal` column, state OPEN, bond 40, obligor 2, obligee 1, condition 99, deadline 77). The
OBLIGEE is cell `1` (holds 5). The OBLIGOR is cell `2` (holds 0). All live. NO side-table. -/
def obWorld : RecordKernelState :=
  { accounts := {0, 1, 2}
    cell := fun c =>
      if c = 0 then .record
        [ (stateField, .int sOpen), (bondField, .int 40), (obligorField, .int 2)
        , (obligeeField, .int 1), (conditionField, .int 99), (deadlineField, .int 77) ]
      else .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun c a => if c = 0 then (if a = 0 then 40 else 0)
                      else if c = 1 then (if a = 0 then 5 else 0) else 0 }

/-- The settle-ready bundle for fulfilling obWorld's obligation to obligor 2. -/
theorem obWorld_fulfil_ready : SettleReady obWorld 0 2 0 :=
  { held_nonneg := by decide, distinct := by decide, e_live := by decide, target_live := by decide }

/-- The settle-ready bundle for slashing obWorld's obligation to obligee 1. -/
theorem obWorld_slash_ready : SettleReady obWorld 0 1 0 :=
  { held_nonneg := by decide, distinct := by decide, e_live := by decide, target_live := by decide }

-- (i) the obligation is OPEN; condition slot 99, deadline slot 77:
#guard (obState obWorld 0 == sOpen)                                 --  true
#guard (obCondition obWorld 0 == 99)                                --  true
#guard (obDeadline obWorld 0 == 77)                                 --  true

-- (ii) a fulfilment with the CORRECT condition (99) COMMITS, returns the bond 40 to obligor 2:
#guard ((fulfilObligation obWorld 0 2 0 99).isSome)                 --  true (fulfilled!)
#guard ((fulfilObligation obWorld 0 2 0 99).map (fun s => s.bal 2 0)) == some 40   -- obligor 0→40
#guard ((fulfilObligation obWorld 0 2 0 99).map (fun s => s.bal 0 0)) == some 0    -- bond drained
#guard ((fulfilObligation obWorld 0 2 0 99).map (fun s => obState s 0)) == some sFulfilled
#guard ((fulfilObligation obWorld 0 2 0 99).map (fun s => recTotalAsset s 0)) == some 45

-- (iii) a fulfilment with a WRONG condition (7 ≠ 99) ⇒ none (KEYSTONE c bites):
#guard ((fulfilObligation obWorld 0 2 0 7).isSome) == false

-- (iv) a CORRECT slash (deadline 77, condition NOT met via witness 7 ≠ 99) forfeits 40 to obligee 1:
#guard ((slashObligation obWorld 0 1 0 77 7).isSome)                --  true (slashed!)
#guard ((slashObligation obWorld 0 1 0 77 7).map (fun s => s.bal 1 0)) == some 45  -- obligee 5→45
#guard ((slashObligation obWorld 0 1 0 77 7).map (fun s => s.bal 0 0)) == some 0   -- bond drained
#guard ((slashObligation obWorld 0 1 0 77 7).map (fun s => obState s 0)) == some sSlashed
#guard ((slashObligation obWorld 0 1 0 77 7).map (fun s => recTotalAsset s 0)) == some 45

-- (v) UNCONDITIONED slash — wrong deadline (5 ≠ 77) ⇒ none (KEYSTONE c, deadline gate):
#guard ((slashObligation obWorld 0 1 0 5 7).isSome) == false
-- (v') UNCONDITIONED slash — condition WAS met (condWitness 99 = condition) ⇒ none (the teeth):
#guard ((slashObligation obWorld 0 1 0 77 99).isSome) == false

-- (vi) NO-DOUBLE-RESOLVE: fulfil then a second fulfil AND a slash both fail:
#guard (((fulfilObligation obWorld 0 2 0 99).bind (fun s => fulfilObligation s 0 2 0 99)).isSome) == false
#guard (((fulfilObligation obWorld 0 2 0 99).bind (fun s => slashObligation s 0 1 0 77 7)).isSome) == false
-- ...and slash then a second slash AND a fulfil both fail:
#guard (((slashObligation obWorld 0 1 0 77 7).bind (fun s => slashObligation s 0 1 0 77 7)).isSome) == false
#guard (((slashObligation obWorld 0 1 0 77 7).bind (fun s => fulfilObligation s 0 2 0 99)).isSome) == false

-- (vii) the factory descriptor conforms (its own initial state is invariant-clean):
#guard ((obligationFactory 40 2 1 99 77).conforms)                  --  true

/-! ## §10b — NON-VACUITY through the REAL factory executor (mint → post bond → resolve). -/

/-- The funder/minter holds a node-cap to the fresh obligation cell `3` (so the mint is
authorized) and funds the bond (cell `0` holds 100 of asset 0). The registry publishes the
obligation factory at key 7 (bond 40, obligor 2, obligee 1, condition 99, deadline 77). -/
def facWorld : RecChainedState :=
  { kernel :=
      { accounts := {0, 1, 2}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun c => if c = 0 then [Cap.node 3] else []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0
        factories := obligationRegistry 7 40 2 1 99 77 }
    log := [] }

/-- Mint obligation cell `3` from factory key 7, then post a bond of 40 of asset 0 (funder = 0). -/
def facBonded : Option RecordKernelState :=
  (mintObligationCell facWorld 0 3 7).bind (fun s => postBond s.kernel 0 3 0 40)

-- the factory resolves + conforms, the mint commits + grows accounts, born conservation-neutral:
#guard (findFactory facWorld.kernel.factories 7).isSome
#guard ((mintObligationCell facWorld 0 3 7).isSome)
#guard ((mintObligationCell facWorld 0 3 7).map (fun s => decide (3 ∈ s.kernel.accounts))) == some true
#guard ((mintObligationCell facWorld 0 3 7).map (fun s => recTotalAsset s.kernel 0)) == some 105

-- the minted cell carries the obligation state machine + deal terms and starts OPEN:
#guard ((mintObligationCell facWorld 0 3 7).map (fun s => s.kernel.slotCaveats 3))
        == some (obligationFactory 40 2 1 99 77).caveats
#guard ((mintObligationCell facWorld 0 3 7).map (fun s => obState s.kernel 3)) == some sOpen
#guard ((mintObligationCell facWorld 0 3 7).map (fun s => obCondition s.kernel 3)) == some 99
#guard ((mintObligationCell facWorld 0 3 7).map (fun s => obDeadline s.kernel 3)) == some 77

-- after posting the bond, the cell HOLDS 40 in its bal column (funder 100→60); supply fixed:
#guard (facBonded.map (fun k => k.bal 3 0)) == some 40
#guard (facBonded.map (fun k => k.bal 0 0)) == some 60
#guard (facBonded.map (fun k => recTotalAsset k 0)) == some 105

-- a CORRECT fulfilment (witness 99) returns 40 to obligor 2 and advances to FULFILLED:
#guard (facBonded.bind (fun k => fulfilObligation k 3 2 0 99) |>.map (fun s => s.bal 2 0)) == some 40
#guard (facBonded.bind (fun k => fulfilObligation k 3 2 0 99) |>.map (fun s => obState s 3)) == some sFulfilled
-- a CORRECT slash (deadline 77, condition not met) forfeits 40 to obligee 1 and advances to SLASHED:
#guard (facBonded.bind (fun k => slashObligation k 3 1 0 77 7) |>.map (fun s => s.bal 1 0)) == some 45
#guard (facBonded.bind (fun k => slashObligation k 3 1 0 77 7) |>.map (fun s => obState s 3)) == some sSlashed
-- an UNKNOWN factory key never mints (fail-closed):
#guard ((mintObligationCell facWorld 0 3 99).isSome) == false

/-! ## §DELETION — the W2 deletion-readiness note (land-before-kill).

THIS module is the LAND-BEFORE-KILL prerequisite for the obligation verb family. Once it is the
live obligation path (this module shipped + every obligation app re-pointed), W2 DELETES:

  WHAT W2 DELETES (the obligation side-table surface — `Dregg2.Exec.RecordKernel` /
  `…TurnExecutorFull`, and the Argus `CreateObligation`/`FulfillObligation`/`SlashObligation`
  effect welds in `Dregg2/Circuit/Argus/*` + `circuit/src/effect_vm/*`):
    (1) the THREE kernel arms / chain ops / `FullActionA` arms:
          • `createObligationKAsset` / `createObligationChainA` / the `.createObligationA` arm
            (replaced by `createCellFromFactoryA` over `obligationFactory` + `postBond`'s move);
          • `fulfillObligationKAsset` / `fulfillObligationChainA` / the `.fulfillObligationA` arm
            (replaced by `fulfilObligation` = `setFieldA` + the per-asset move);
          • `slashObligationKAsset` / `slashObligationChainA` / the `.slashObligationA` arm
            (replaced by `slashObligation` = the gated `setFieldA` + the per-asset move).
    (2) any OFF-LEDGER obligation side-table (the obligation tag on the SHARED `EscrowRecord`
        store, or a dedicated `obligations` field on `RecordKernelState`) — DISSOLVED into the
        minted cell's own `bal` column. (NOTE — the ORDERING CONSTRAINT: the obligation family
        SHARES `EscrowRecord`'s store with escrow/bridge per the EscrowFactory §DELETION; the
        shared field cannot be removed until escrow AND obligation AND bridge are all re-pointed.)
    (3) the obligation-specific held-value measure (`obligationHeldAsset` or the obligation summand
        of any combined `recTotalAssetWith…` quantity) and its accounting theory — COLLAPSED back
        to plain `recTotalAsset`, since obligation conservation is now the ordinary per-asset move
        law `recKExecAsset_conserves_per_asset`.
    (4) the obligation settle-liveness side teeth that read the side-table — SUBSUMED by the move's
        own fail-closed guard (`settle_requires_live_target` here) + the state machine.

  WHAT MUST BE RE-POINTED FIRST (the land-before-kill blockers — every obligation-verb consumer):
    • any `Dregg2.Apps.*` SLA/bond/staking app on the obligation verbs (e.g. `StakedSlaGated`,
      the bond/penalty apps) — re-point to `obligationFactory` + `postBond` + `fulfilObligation`/
      `slashObligation`. (Same re-point pattern as `BountyBoardGated` → `escrowFactoryEntry`.)
    • the SHARED-`EscrowRecord` twins (escrow/bridge): obligation joins escrow/swiss as a family
      that re-lands as a factory; the shared side-table field is deleted only AFTER all of them.

  NOT DELETED HERE (land-before-kill): nothing above is removed in this commit — we only prove the
  factory is a faithful replacement and enumerate the burn-down. The verb deletion is the
  SUBSEQUENT W2 commit, gated on the re-points above all landing green.
-/

#assert_axioms obligationFactory_conforms
#assert_axioms obligationRegistry_finds
#assert_axioms obSettle_conserves
#assert_axioms fulfil_conserves
#assert_axioms slash_conserves
#assert_axioms fulfil_requires_open
#assert_axioms slash_requires_open
#assert_axioms no_double_resolve_fulfilled
#assert_axioms no_double_resolve_slashed
#assert_axioms fulfil_advances_state
#assert_axioms fulfil_requires_condition
#assert_axioms slash_requires_deadline
#assert_axioms slash_rejects_when_condition_met
#assert_axioms obSettle_commits
#assert_axioms obSettle_drains_exactly
#assert_axioms open_obligation_fulfilable
#assert_axioms open_obligation_slashable
#assert_axioms settle_requires_live_target
#assert_axioms fulfil_requires_live_obligor
#assert_axioms slash_requires_live_obligee
#assert_axioms mintObligationCell_installs_state_machine
#assert_axioms mintObligationCell_caveats
#assert_axioms mintObligationCell_neutral
#assert_axioms mintObligationCell_grows_accounts
#assert_axioms mintObligationCell_unknown_factory_fails
#assert_axioms postBond_conserves

end Dregg2.Apps.ObligationFactory
