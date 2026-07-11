/-
# Dregg2.Circuit.RotatedKernelRefinementSetField — the VALUE-leg circuit→kernel refinement for
  `setField`, on the LIVE ROTATED circuit (the transfer template applied to a field-write effect).

## What this module closes (the `setField` VALUE rung)

`RotatedKernelRefinement.lean` builds the VALUE rung for `transfer`: the live rotated transfer
circuit FORCES the debit/credit movement + availability against the kernel leaf
`BalanceMovementSpec`. This module is the SAME bridge for `setField`, classified VALUE_FORCED: the
live rotated `setFieldV3 slot` descriptor's selector-gated write gate (`gFieldWriteP1 slot`) PINS the
written field column `fields[slot]_after = param1` onto an IN-COMMITMENT state-block column — exactly
the column the keystone's GROUP-4 sites absorb into the published `state_commit` (the same injective
binding `transfer`'s `bal_lo` rides). So the moved content of a `setFieldA` is genuinely circuit-
forced, and a wrong-value witness is UNSAT *because the gate forces the write*, not because the
decode asserts it.

The kernel leaf is `SetFieldSpec s actor cell f v s'` (the `.setFieldA` arm of `fullActionStep`):
the cell-map write `cell ↦ setField f cell v`, the 16-field kernel frame, the one-row receipt log,
and the 4-leg admissibility guard.

## The split (mirroring transfer's honest residual map)

  * FORCED by the circuit (the apex obligation): the written field column moves to `param1` (=`v`) —
    `setField_value_forced`. A decode claiming any other written value cannot ride a satisfying
    witness (`descriptorRefines_rejects_wrong_value`).
  * NAMED decode residual (the kernel side-tables + the cross-cell / whole-map shape the per-row
    value block cannot carry): the `setFieldCellMap` whole-map move, the `SetFieldGuard`
    (caveat/authority/membership/liveness), the 16-field frame, the receipt log. These are carried in
    `rotatedEncodesSF` exactly as transfer's `hledgerFrame`/`guard*`/`fr*`/`logAdv` legs are — named,
    not laundered. The MOVED-coordinate written value is checked against the circuit (the tooth), so
    the move is not a free assertion.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every new theorem. NEW file; imports are read-only.
-/
import Dregg2.Circuit.RotatedKernelRefinement
import Dregg2.Circuit.Emit.EffectVmEmitSetField

namespace Dregg2.Circuit.RotatedKernelRefinementSetField

open Dregg2.Circuit.Emit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitV2
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
open Dregg2.Circuit.Emit.EffectVmEmitSetField
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Spec.CellStateField
  (SetFieldSpec SetFieldGuard setFieldCellMap)
open Dregg2.Circuit.RotatedKernelRefinement (RotTableSide)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — the live rotated setField descriptor (per field slot).

`setFieldV3 slot = v3OfFrozen (setFieldTickFace slot)` (`EffectVmEmitRotationV3`) is exactly the descriptor
the rotated prover runs for a `setFieldA` writing slot `slot` (the registry's
`setFieldVmDescriptor2-{slot}R24`). `setFieldTickFace slot = setFieldVmDescriptor slot`
(`setFieldTickFace_eq_source`), so the source per-row gates / faithfulness theorems apply verbatim. -/

/-- The live rotated setField descriptor for written slot `slot` (the registry member). -/
def setFieldV3 (slot : Fin 8) : EffectVmDescriptor2 :=
  EffectVmEmitRotationV3.setFieldV3 slot

theorem setFieldV3_eq (slot : Fin 8) :
    setFieldV3 slot = v3OfFrozenSetField slot (EffectVmEmitRotationV3.setFieldTickFace slot) := rfl

/-- `setFieldTickFace slot` is graduable (it shares the per-effect descriptor's sites + ranges) — the
decidable side condition `rotV3Frozen_sound_v1` requires. -/
theorem setField_graduable (slot : Fin 8) :
    graduable (EffectVmEmitRotationV3.setFieldTickFace slot) = true :=
  EffectVmEmitRotationV3.graduable_setFieldTickFace slot

/-! ## §1 — the rotated→per-row decode chain (the witness side of the bridge).

`rotV3Frozen_sound_v1` lifts a `Satisfied2 hash (setFieldV3 slot) …` witness to the v1 denotation
`satisfiedVm hash (setFieldTickFace slot) (envAt t i) …` on every row. Its gates are exactly
`setFieldVmDescriptor slot`'s (`setFieldTickFace_eq_source`), all `.gate` (flag-free), so we extract
them at `false false` and feed `setFieldVm_faithful` to get the field-write intent. -/

/-- The per-row setField GATES hold at an ACTIVE row (`i` NOT the last row): the rotated witness gives
the v1 denotation at the i-dependent boundary flags; `setFieldRowGates` are all `.gate` constraints
which under the deployed `when_transition()` bind on every row but the last — so on a TRANSITION row
(`i + 1 ≠ t.rows.length`, `isLast` flag `false`) their body equation holds at `false false`. (The
`hnotlast` hypothesis is the faithful obligation that the designated active row is a genuine
transition row, not the wrap/pad row.) -/
theorem rotated_row_gates (slot : Fin 8) (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash (setFieldV3 slot) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length) :
    ∀ c ∈ setFieldRowGates slot, c.holdsVm (envAt t i) false false := by
  have hv1 : satisfiedVm hash (EffectVmEmitRotationV3.setFieldTickFace slot)
      (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
    rotV3FrozenSetField_sound_v1 slot permOut hash (EffectVmEmitRotationV3.setFieldTickFace slot) minit mfin maddrs t
      (setField_graduable slot) (hside.toFaithful hsat) i hi
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  intro c hc
  -- `setFieldTickFace slot = setFieldVmDescriptor slot`, whose constraints ARE `setFieldRowGates`.
  have hmem : c ∈ (EffectVmEmitRotationV3.setFieldTickFace slot).constraints := by
    rw [EffectVmEmitRotationV3.setFieldTickFace_eq_source]
    exact hc
  have hh := hv1.1 c hmem
  rw [hlastf] at hh
  -- the gate's `holdsVm` is the body equation; off the last row it IS the body equation.
  unfold setFieldRowGates gOtherFieldsAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_filter, List.mem_range, decide_eq_true_eq] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨j, _, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using hh

/-- **`rotated_row_cellSpec` — rotated witness ⟹ per-cell field-write spec on an active row `i`.**
From a `Satisfied2 hash (setFieldV3 slot)` witness (+ the table side conditions) and the decode of
row `i` to `(pre, post)` through `RowEncodesSF`, on an ACTIVE setField row the value block satisfies
`CellSetFieldSpec`: the slot is written to `param1`, the nonce ticks, every other column frozen. This
is the LIVE circuit's per-cell content. -/
theorem rotated_row_cellSpec (slot : Fin 8) (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash (setFieldV3 slot) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcanon : SetFieldRowCanon (envAt t i))
    (pre post : CellState)
    (hrow : IsSetFieldRow (envAt t i))
    (henc : RowEncodesSF slot (envAt t i) pre post) :
    CellSetFieldSpec slot pre ((envAt t i).loc (prmCol VALUE)) post := by
  have hgates := rotated_row_gates slot hash hside hsat i hi hnotlast
  have hint : SetFieldRowIntent slot (envAt t i) :=
    (setFieldVm_faithful slot (envAt t i) hrow hcanon).mp hgates
  exact intent_to_cellSpec slot (envAt t i) pre post henc hint

/-! ## §2 — `rotatedEncodesSF`: the witness active-row ⟷ kernel state decode.

`rotatedEncodesSF slot pre post` ties a satisfying setField witness's designated ACTIVE row `wi` (the
one whose `s_set_field = 1`) onto the kernel field-write boundary, and carries the residual the
per-cell circuit cannot witness:

  * `wi` + its `RowEncodesSF` decode + `IsSetFieldRow` — the circuit ROW this state encodes;
  * `cellPre`/`cellPost` — the decoded per-cell before/after `CellState`s;
  * `hwval` — the written value: `param1` of the active row IS the kernel write value `v`, read onto
    the decoded `cellPost.fields slot` (`cellPost.fields slot = v`);
  * `hcellMove` — the kernel cell-map move `setFieldCellMap` (the WHOLE-MAP residual the per-row block
    cannot carry: other cells, other fields). Its WRITTEN-SLOT value is forced by the circuit (the
    tooth `descriptorRefines_rejects_wrong_value`), so it is not a free assertion.
  * `guard`/`frame`/`logAdv` — the kernel `SetFieldGuard`, the 16-field frame, and the receipt log
    advance: the executor/record-layer legs the value block does not carry. NAMED, not assumed away. -/

/-- The decode relating a satisfying rotated setField witness's active row to a kernel `pre → post`
field-write of slot `slot` (field `slotName slot`) to value `v` by `actor` on `cell`. DATA-bearing
(`Type`, like transfer's `rotatedEncodes`): it exhibits the witnessing active row + its decoded
`CellState`s, then carries the boundary-tying + kernel-side residual as proof fields. -/
structure rotatedEncodesSF (slot : Fin 8) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (actor cell : CellId) (v : Int) : Type where
  -- the designated ACTIVE setField row + its decode.
  wi : Nat
  hwi : wi < t.rows.length
  -- the designated active row is a TRANSITION row, NOT the wrap/pad last row: the deployed gates run
  -- under `when_transition()`, so the write is forced only off the last row. Any real ≥2-row setField
  -- trace carries this (the prover pads a wrap row after the effect row).
  hwiNotLast : wi + 1 ≠ t.rows.length
  cellPre : CellState
  cellPost : CellState
  hwiRow : IsSetFieldRow (envAt t wi)
  hwiEnc : RowEncodesSF slot (envAt t wi) cellPre cellPost
  -- the designated active row's EXPLICIT canonicality envelope (`SetFieldRowCanon`) — the deployed
  -- range-check / field-representative invariant carried EXACTLY as the migrated source module
  -- (`EffectVmEmitSetField`) carries its `hcanon` hypothesis: every state-block cell of both windows a
  -- canonical BabyBear representative in `[0, p)`, the written-value param column `param1` canonical, and
  -- the pre-nonce tick in-field (`nonce_before + 1 < p`). Under the mod-p `holdsVm` denotation this is
  -- what lets the `≡ 0 [ZMOD p]` write-gate residual — strictly inside `(−p, p)` because both the field
  -- column and `param1` are canonical — be read back as the EXACT ℤ write `fields[slot]_after = param1`.
  -- Only the two balance limbs are range-checked by this descriptor (`saCol BALANCE_LO/HI`, 30 bits), so
  -- the rest of the envelope is NOT circuit-forced; it is a NAMED decode residual, not laundered —
  -- exactly transfer's honest relocation of the non-forced `guardAvail` leg.
  hwiCanon : SetFieldRowCanon (envAt t wi)
  -- the written value: the active row's `param1` IS the kernel write value `v`.
  hwval : (envAt t wi).loc (prmCol VALUE) = v
  -- the kernel cell-map move (the WHOLE-MAP residual; its written-slot value is circuit-forced).
  hcellMove : post.kernel.cell = setFieldCellMap pre.kernel.cell cell (slotName slot) v
  -- the receipt log advance (off the per-row block — the record-layer commitment).
  logAdv : post.log = { actor := actor, src := cell, dst := cell, amt := 0 } :: pre.log
  -- the 4-leg admissibility guard (the executor's domain restriction — the off-row guard).
  guard : SetFieldGuard pre actor cell (slotName slot) v
  -- the 16 non-`cell` kernel frame fields (the full `SetFieldSpec` frame residual).
  frAccounts : post.kernel.accounts = pre.kernel.accounts
  frCaps : post.kernel.caps = pre.kernel.caps
  frNullifiers : post.kernel.nullifiers = pre.kernel.nullifiers
  frRevoked : post.kernel.revoked = pre.kernel.revoked
  frCommitments : post.kernel.commitments = pre.kernel.commitments
  frBal : post.kernel.bal = pre.kernel.bal
  frSlotCaveats : post.kernel.slotCaveats = pre.kernel.slotCaveats
  frFactories : post.kernel.factories = pre.kernel.factories
  frLifecycle : post.kernel.lifecycle = pre.kernel.lifecycle
  frDeathCert : post.kernel.deathCert = pre.kernel.deathCert
  frDelegate : post.kernel.delegate = pre.kernel.delegate
  frDelegations : post.kernel.delegations = pre.kernel.delegations
  frDelegationEpoch : post.kernel.delegationEpoch = pre.kernel.delegationEpoch
  frDelegationEpochAt : post.kernel.delegationEpochAt = pre.kernel.delegationEpochAt
  frHeaps : post.kernel.heaps = pre.kernel.heaps
  frNullifierRoot : post.kernel.nullifierRoot = pre.kernel.nullifierRoot
  frRevokedRoot : post.kernel.revokedRoot = pre.kernel.revokedRoot
  frCommitmentsRoot : post.kernel.commitmentsRoot = pre.kernel.commitmentsRoot

/-! ## §3 — the apex obligation: the circuit FORCES the written value.

The selector-gated write gate `gFieldWrite slot` pins `fields[slot]_after ≡ param1 [ZMOD p]` on the
active row (the deployed mod-p `holdsVm` denotation); the decode reads `param1 = v` and
`cellPost.fields slot = post.fields ⟨…⟩`. Under the active row's canonicality envelope (the NAMED
`rotatedEncodesSF.hwiCanon` residual: the written field column and `param1` both canonical in `[0, p)`)
the mod-p congruence is read back as the EXACT ℤ write. So the WRITTEN slot value is forced by the
running circuit — not taken from the decode. -/

/-- **`setField_value_forced` — the written slot value is CIRCUIT-FORCED.** On the decoded active row
the gated write gate forces `cellPost.fields slot ≡ param1 [ZMOD p]`; under the named canonicality
residual (`hwiCanon`) this recovers the exact ℤ write `cellPost.fields slot = param1 = v`. So the moved
field content is pinned by the running circuit; a decode claiming a different written value is UNSAT
(the §4 tooth). -/
theorem setField_value_forced (slot : Fin 8) (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash (setFieldV3 slot) minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (v : Int)
    (henc : rotatedEncodesSF slot hash minit mfin maddrs t pre post actor cell v) :
    henc.cellPost.fields slot = v := by
  -- the per-cell spec forces the written slot to the row's `param1`.
  have hspec : CellSetFieldSpec slot henc.cellPre ((envAt t henc.wi).loc (prmCol VALUE)) henc.cellPost :=
    rotated_row_cellSpec slot hash hside hsat henc.wi henc.hwi henc.hwiNotLast henc.hwiCanon
      henc.cellPre henc.cellPost henc.hwiRow henc.hwiEnc
  -- `CellSetFieldSpec`'s first conjunct: `post.fields slot = param1`; read `param1 = v`.
  rw [hspec.1, henc.hwval]

/-! ## §4 — THE REFINEMENT: satisfying the live setField descriptor FORCES the kernel step.

The decode (`rotatedEncodesSF`) carries the kernel-only residual (the whole-map shape, the guard, the
frame, the log); the WITNESS (`Satisfied2`) forces the written value. We assemble `SetFieldSpec`. -/

/-- The circuit's written slot `slotName slot = "slotfield{i}"` is NEVER a protocol-reserved slot
(`nonce`/`permissions`/`verification_key`/`program`): the developer SetField namespace is disjoint
from the protocol slots. So the reserved leg of `SetFieldSpec` is discharged structurally for the
circuit-modeled write — the rotated setField descriptor only ever writes developer fields. -/
theorem reservedField_slotName (slot : Fin 8) :
    Dregg2.Exec.EffectsState.reservedField (slotName slot) = false := by
  fin_cases slot <;> decide

/-- **`setField_descriptorRefines` — THE CIRCUIT→KERNEL REFINEMENT for setField.** Satisfying the
LIVE rotated setField descriptor (`Satisfied2 hash (setFieldV3 slot) …`, with the chip/range table
side conditions) together with `rotatedEncodesSF` forces the KERNEL's `setField` step
`SetFieldSpec pre actor cell (slotName slot) v post` — the `.setFieldA` arm of `fullActionStep`. The
written-slot move is FORCED by the witness (`setField_value_forced`, riding the in-commitment write
column); the whole-map shape, the guard, the 16-field frame, and the log are the named decode
residual. The reserved-slot leg is `reservedField_slotName` (a developer slot, never a protocol one). -/
theorem setField_descriptorRefines (slot : Fin 8) (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash (setFieldV3 slot) minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (v : Int)
    (henc : rotatedEncodesSF slot hash minit mfin maddrs t pre post actor cell v) :
    SetFieldSpec pre actor cell (slotName slot) v post := by
  exact ⟨reservedField_slotName slot, henc.guard, henc.hcellMove, henc.logAdv,
    henc.frAccounts, henc.frCaps, henc.frNullifiers, henc.frRevoked, henc.frCommitments,
    henc.frBal, henc.frSlotCaveats, henc.frFactories, henc.frLifecycle, henc.frDeathCert,
    henc.frDelegate, henc.frDelegations, henc.frDelegationEpoch, henc.frDelegationEpochAt,
    henc.frHeaps, henc.frNullifierRoot, henc.frRevokedRoot, henc.frCommitmentsRoot⟩

/-- **The refinement, stated against `fullActionStep` directly.** `SetFieldSpec` IS the `.setFieldA`
arm of the kernel dispatcher, so a satisfying rotated setField witness forces
`fullActionStep pre (.setFieldA …) post`. -/
theorem setField_descriptorRefines_fullActionStep (slot : Fin 8) (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash (setFieldV3 slot) minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (v : Int)
    (henc : rotatedEncodesSF slot hash minit mfin maddrs t pre post actor cell v) :
    Dregg2.Circuit.ActionDispatch.fullActionStep pre (.setFieldA actor cell (slotName slot) v) post := by
  show SetFieldSpec pre actor cell (slotName slot) v post
  exact setField_descriptorRefines slot hash hside hsat pre post actor cell v henc

/-! ## §5 — BOTH-POLARITY TOOTH: a wrong-value witness is UNSAT.

The refinement is meaningful only if the circuit truly constrains the write. The converse: a decode
that claims a written-slot post-value DIFFERENT from the circuit-forced `param1 = v` cannot ride a
satisfying witness — the gated write gate FORCES the moved column, so the claim is contradictory. -/

/-- **`descriptorRefines_rejects_wrong_value` — the field-write tooth.** If a decode asserts a
post-`cellPost` whose written slot is NOT the genuine bound value `v`, then NO `Satisfied2` witness
realizes that decode: the assumption is `False`. The circuit pins the written column, so a
wrong-value setField is UNSAT. -/
theorem descriptorRefines_rejects_wrong_value (slot : Fin 8) (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash (setFieldV3 slot) minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (v : Int)
    (henc : rotatedEncodesSF slot hash minit mfin maddrs t pre post actor cell v)
    (hwrong : henc.cellPost.fields slot ≠ v) :
    False :=
  hwrong (setField_value_forced slot hash hside hsat pre post actor cell v henc)

/-- **The bystander-field polarity.** On the active row the OTHER seven field columns are FROZEN
(`gFieldPass`), so a decode whose `cellPost` mutates a non-`slot` field away from `cellPre` is
likewise UNSAT — the circuit freezes the bystander columns. -/
theorem descriptorRefines_rejects_moved_bystander (slot : Fin 8) (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash (setFieldV3 slot) minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (v : Int)
    (henc : rotatedEncodesSF slot hash minit mfin maddrs t pre post actor cell v)
    (j : Fin 8) (hj : j ≠ slot)
    (hwrong : henc.cellPost.fields j ≠ henc.cellPre.fields j) :
    False := by
  have hspec : CellSetFieldSpec slot henc.cellPre ((envAt t henc.wi).loc (prmCol VALUE)) henc.cellPost :=
    rotated_row_cellSpec slot hash hside hsat henc.wi henc.hwi henc.hwiNotLast henc.hwiCanon
      henc.cellPre henc.cellPost henc.hwiRow henc.hwiEnc
  exact hwrong (hspec.2.2.2.2.2.2 j hj)

/-! ## §6 — Axiom-hygiene tripwires. -/

#assert_axioms rotated_row_gates
#assert_axioms rotated_row_cellSpec
#assert_axioms reservedField_slotName
#assert_axioms setField_value_forced
#assert_axioms setField_descriptorRefines
#assert_axioms setField_descriptorRefines_fullActionStep
#assert_axioms descriptorRefines_rejects_wrong_value
#assert_axioms descriptorRefines_rejects_moved_bystander

end Dregg2.Circuit.RotatedKernelRefinementSetField
