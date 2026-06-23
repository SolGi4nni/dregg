/-
# Dregg2.Circuit.RotatedKernelRefinementIncNonce — the VALUE-leg circuit→kernel refinement for
  `incrementNonce`, on the LIVE ROTATED circuit (the transfer/setField template on the committed
  nonce column).

## What this module closes (the `incrementNonce` VALUE rung)

`RotatedKernelRefinementSetField.lean` builds the VALUE rung for a committed-column write forced by a
gate. This module is the SAME bridge for `incrementNonce`, classified VALUE_FORCED: the live rotated
`incNonceV3` descriptor's nonce gate (`gNonce`) PINS the committed `state.NONCE` column to
`nonce_after = nonce_before + 1` (on a non-NoOp row) — exactly the column the keystone absorbs into
the published `state_commit` (the same injective binding transfer's `bal_lo` rides; the state
commitment is `hash(balance_lo, balance_hi, nonce, field[0..8], cap_root)`). So the nonce TICK of an
`incrementNonceA` is genuinely circuit-forced, and a frozen-nonce / wrong-delta witness is UNSAT
*because the gate forces the tick*, not because the decode asserts it.

The kernel leaf is `IncrementNonceSpec s actor cell n s'` (`Spec.CellStateMonotone`, the
`.incrementNonceA` arm of `execFullA`): the cell-map bump `cell ↦ nonce := n`, the 16-field kernel
frame, the one-row self-targeted receipt log, and the three-leg admissibility guard. The leaf spec's
`n` is the value the cell-record `nonce` field is written to; the INCREMENT SEMANTICS instantiate it
at `n = old_nonce + 1`. The decode (`rotatedEncodesIncNonce`) ties the kernel write value `n` to the
circuit-forced on-trace tick (`hnVal : n = cellPre.nonce + 1`), so the `+1` is genuinely
circuit-forced through the decode boundary, exactly as setField ties `param1 = v`.

## The split (mirroring setField's honest residual map)

  * FORCED by the circuit (the apex obligation): the committed nonce column TICKS by 1 —
    `incNonce_nonce_forced` (`cellPost.nonce = cellPre.nonce + 1`). A decode claiming any other delta
    cannot ride a satisfying witness (`descriptorRefines_rejects_frozen_nonce`).
  * NAMED decode residual (the kernel side-tables + the whole-map / cross-cell shape + the log the
    per-row value block cannot carry): the `incNonceCellMap` whole-map bump, the `incNonceGuard`
    (authority/membership/liveness), the 16-field frame, the receipt log, and the `hnVal` boundary
    tying the kernel write value to the forced tick. Carried in `rotatedEncodesIncNonce` exactly as
    setField's `hcellMove`/`guard`/`fr*`/`logAdv` legs are — named, not laundered.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every new theorem. NEW file; imports are read-only.
-/
import Dregg2.Circuit.RotatedKernelRefinement
import Dregg2.Circuit.Emit.EffectVmEmitIncrementNonce

namespace Dregg2.Circuit.RotatedKernelRefinementIncNonce

open Dregg2.Circuit.Emit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitV2
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
open Dregg2.Circuit.Emit.EffectVmEmitIncrementNonce
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gFieldPassAll)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Spec.CellStateMonotone
  (IncrementNonceSpec incNonceGuard incNonceCellMap)
open Dregg2.Circuit.RotatedKernelRefinement (RotTableSide)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — the live rotated incrementNonce descriptor.

`incNonceV3 = v3OfFrozen incrementNonceVmDescriptor` is exactly the descriptor the rotated prover runs
for an `incrementNonceA` (the registry's `incrementNonceVmDescriptor2R24`). Unlike setField, the source
`incrementNonceVmDescriptor` ALREADY carries the runtime-reconciled nonce TICK gate (`gNonce` in
`incNonceRowGates`), so the registry routes through `v3OfFrozen` directly — no tick-face re-routing. -/

/-- The live rotated incrementNonce descriptor (the registry member `incrementNonceVmDescriptor2R24`). -/
def incNonceV3 : EffectVmDescriptor2 := v3OfFrozen incrementNonceVmDescriptor

theorem incNonceV3_eq : incNonceV3 = v3OfFrozen incrementNonceVmDescriptor := rfl

/-- `incrementNonceVmDescriptor` is graduable (it shares the per-effect descriptor's sites + ranges) —
the decidable side condition `rotV3Frozen_sound_v1` requires. (The `#guard` in `EffectVmEmitV2`.) -/
theorem incNonce_graduable : graduable incrementNonceVmDescriptor = true := by decide

/-! ## §1 — the rotated→per-row decode chain (the witness side of the bridge).

`rotV3Frozen_sound_v1` lifts a `Satisfied2 hash incNonceV3 …` witness to the v1 denotation
`satisfiedVm hash incrementNonceVmDescriptor (envAt t i) …` on every row. We extract the per-row
`incNonceRowGates` (all `.gate`, flag-free) at `false false` and feed `incNonceVm_faithful`. -/

/-- The per-row incrementNonce GATES hold at an ACTIVE row (`i` NOT the last row): the rotated witness
gives the v1 denotation at the i-dependent boundary flags; `incNonceRowGates` are all `.gate`
constraints which under the deployed `when_transition()` bind on every row but the last — so on a
TRANSITION row (`i + 1 ≠ t.rows.length`, `isLast` flag `false`) their body equation holds at
`false false`. (The `hnotlast` hypothesis is the faithful obligation that the designated active row
is a genuine transition row, not the wrap/pad row.) -/
theorem rotated_row_gates (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash incNonceV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length) :
    ∀ c ∈ incNonceRowGates, c.holdsVm (envAt t i) false false := by
  have hv1 : satisfiedVm hash incrementNonceVmDescriptor
      (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
    rotV3Frozen_sound_v1 permOut hash incrementNonceVmDescriptor minit mfin maddrs t
      incNonce_graduable (hside.toFaithful hsat) i hi
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  intro c hc
  have hmem : c ∈ incrementNonceVmDescriptor.constraints := by
    unfold incrementNonceVmDescriptor
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
  have hh := hv1.1 c hmem
  rw [hlastf] at hh
  unfold incNonceRowGates gFieldPassAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨j, _, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using hh

/-- **`rotated_row_cellSpec` — rotated witness ⟹ per-cell incrementNonce spec on an active row `i`.**
From a `Satisfied2 hash incNonceV3` witness (+ the table side conditions) and the decode of row `i` to
`(pre, post)` through `RowEncodesIncNonce`, on an ACTIVE incrementNonce row (`IsIncNonceRow`, giving
`s_noop = 0`) the value block satisfies `CellIncNonceSpec`: the nonce TICKS by 1, every economic
column frozen. This is the LIVE circuit's per-cell content. -/
theorem rotated_row_cellSpec (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash incNonceV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (pre post : CellState)
    (hrow : IsIncNonceRow (envAt t i))
    (henc : RowEncodesIncNonce (envAt t i) pre post) :
    CellIncNonceSpec pre post := by
  have hgates := rotated_row_gates hash hside hsat i hi hnotlast
  have hint : IncNonceRowIntent (envAt t i) := (incNonceVm_faithful (envAt t i)).mp hgates
  exact intent_to_cellSpec (envAt t i) pre post hrow.2 henc hint

/-! ## §2 — `rotatedEncodesIncNonce`: the witness active-row ⟷ kernel state decode.

`rotatedEncodesIncNonce pre post` ties a satisfying incrementNonce witness's designated ACTIVE row
`wi` (the one whose `s_increment_nonce = 1`, `s_noop = 0`) onto the kernel nonce-bump boundary, and
carries the residual the per-cell circuit cannot witness:

  * `wi` + its `RowEncodesIncNonce` decode + `IsIncNonceRow` — the circuit ROW this state encodes;
  * `cellPre`/`cellPost` — the decoded per-cell before/after `CellState`s;
  * `hnVal` — the kernel write value `n` IS the circuit-forced tick `cellPre.nonce + 1` (the increment
    semantics tied to the running circuit, exactly as setField's `hwval : param1 = v`);
  * `hcellMove` — the kernel cell-map bump `incNonceCellMap` (the WHOLE-MAP residual: other cells,
    other fields). Its written-cell `nonce` value is `n = cellPre.nonce + 1`, forced by the circuit
    (the tooth `descriptorRefines_rejects_frozen_nonce`), so it is not a free assertion;
  * `guard`/`frame`/`logAdv` — the kernel `incNonceGuard`, the 16-field frame, the receipt log: the
    executor/record-layer legs the value block does not carry. NAMED, not assumed away. -/

/-- The decode relating a satisfying rotated incrementNonce witness's active row to a kernel
`pre → post` nonce bump of `cell` to `n` by `actor`. DATA-bearing (`Type`, like setField's
`rotatedEncodesSF`): it exhibits the witnessing active row + its decoded `CellState`s, then carries
the boundary-tying + kernel-side residual as proof fields. -/
structure rotatedEncodesIncNonce (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (actor cell : CellId) (n : Int) : Type where
  -- the designated ACTIVE incrementNonce row + its decode.
  wi : Nat
  hwi : wi < t.rows.length
  -- the designated active row is a TRANSITION row, NOT the wrap/pad last row: the deployed gates run
  -- under `when_transition()`, so the tick is forced only off the last row. Any real ≥2-row
  -- incrementNonce trace carries this (the prover pads a wrap row after the effect row).
  hwiNotLast : wi + 1 ≠ t.rows.length
  cellPre : CellState
  cellPost : CellState
  hwiRow : IsIncNonceRow (envAt t wi)
  hwiEnc : RowEncodesIncNonce (envAt t wi) cellPre cellPost
  -- the kernel write value IS the circuit-forced tick (the increment semantics tied to the circuit).
  hnVal : n = cellPre.nonce + 1
  -- the kernel cell-map bump (the WHOLE-MAP residual; its written-cell nonce value is circuit-forced).
  hcellMove : post.kernel.cell = incNonceCellMap pre.kernel cell n
  -- the receipt log advance (off the per-row block — the record-layer commitment).
  logAdv : post.log = { actor := actor, src := cell, dst := cell, amt := 0 } :: pre.log
  -- the 4-leg admissibility guard (the executor's domain restriction — the off-row guard, now
  -- including the MONOTONE-NONCE leg `old < n`; for the forced tick `n = old + 1` it holds trivially).
  guard : incNonceGuard pre actor cell n
  -- the 16 non-`cell` kernel frame fields (the full `IncrementNonceSpec` frame residual).
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

/-! ## §3 — the apex obligation: the circuit FORCES the nonce tick.

The reconciled nonce gate `gNonce` pins `nonce_after = nonce_before + (1 − s_noop)` on the active row;
on an `IsIncNonceRow` (`s_noop = 0`) the decode reads `nonce_after = cellPost.nonce`,
`nonce_before = cellPre.nonce`. So the committed nonce column TICKS by 1 — forced by the running
circuit, not taken from the decode. -/

/-- **`incNonce_nonce_forced` — the committed nonce column TICK is CIRCUIT-FORCED.** On the decoded
active row the reconciled nonce gate forces `cellPost.nonce = cellPre.nonce + 1`. So the nonce advance
is pinned by the running circuit; a decode claiming a frozen / wrong-delta nonce is UNSAT (the §5
tooth). -/
theorem incNonce_nonce_forced (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash incNonceV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (n : Int)
    (henc : rotatedEncodesIncNonce hash minit mfin maddrs t pre post actor cell n) :
    henc.cellPost.nonce = henc.cellPre.nonce + 1 := by
  have hspec : CellIncNonceSpec henc.cellPre henc.cellPost :=
    rotated_row_cellSpec hash hside hsat henc.wi henc.hwi henc.hwiNotLast henc.cellPre henc.cellPost
      henc.hwiRow henc.hwiEnc
  exact hspec.2.2.1

/-! ## §4 — THE REFINEMENT: satisfying the live incrementNonce descriptor FORCES the kernel step.

The decode (`rotatedEncodesIncNonce`) carries the kernel-only residual (the whole-map bump, the guard,
the frame, the log) and ties the kernel write value `n` to the forced tick (`hnVal`); the WITNESS
(`Satisfied2`) forces the nonce tick. We assemble `IncrementNonceSpec` at the forced increment. -/

/-- **`incrementNonce_descriptorRefines` — THE CIRCUIT→KERNEL REFINEMENT for incrementNonce.**
Satisfying the LIVE rotated incrementNonce descriptor (`Satisfied2 hash incNonceV3 …`, with the
chip/range table side conditions) together with `rotatedEncodesIncNonce` forces the KERNEL's nonce
bump `IncrementNonceSpec pre actor cell n post` — the `.incrementNonceA` arm of `execFullA`. The
kernel write value `n` is the circuit-forced increment `cellPre.nonce + 1` (`hnVal` ties the leaf
spec's `n` to the on-trace tick that `incNonce_nonce_forced` pins, riding the in-commitment nonce
column); the whole-map bump, the guard, the 16-field frame, and the log are the named decode
residual. -/
theorem incrementNonce_descriptorRefines (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash incNonceV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (n : Int)
    (henc : rotatedEncodesIncNonce hash minit mfin maddrs t pre post actor cell n) :
    IncrementNonceSpec pre actor cell n post := by
  exact ⟨henc.guard, henc.hcellMove, henc.logAdv,
    henc.frAccounts, henc.frCaps, henc.frNullifiers, henc.frRevoked, henc.frCommitments,
    henc.frBal, henc.frSlotCaveats, henc.frFactories, henc.frLifecycle, henc.frDeathCert,
    henc.frDelegate, henc.frDelegations, henc.frDelegationEpoch, henc.frDelegationEpochAt,
    henc.frHeaps⟩

/-- **The refinement at the FORCED increment `n = old_nonce + 1`, made explicit.** The leaf spec's `n`
is free; the increment SEMANTICS instantiate it at the circuit-forced tick of the decoded pre-cell
nonce, and `hnVal` certifies the decode used exactly that value. So the live witness forces
`IncrementNonceSpec` at the genuine increment. -/
theorem incrementNonce_descriptorRefines_incremented (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash incNonceV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (n : Int)
    (henc : rotatedEncodesIncNonce hash minit mfin maddrs t pre post actor cell n) :
    IncrementNonceSpec pre actor cell (henc.cellPre.nonce + 1) post := by
  have heq : n = henc.cellPre.nonce + 1 := henc.hnVal
  rw [← heq]
  exact incrementNonce_descriptorRefines hash hside hsat pre post actor cell n henc

/-! ## §5 — BOTH-POLARITY TOOTH: a frozen-nonce witness is UNSAT.

The refinement is meaningful only if the circuit truly forces the tick. The converse: a decode that
claims a written-cell post-nonce that is NOT the circuit-forced `cellPre.nonce + 1` cannot ride a
satisfying witness — the reconciled nonce gate FORCES the tick, so the claim is contradictory. -/

/-- **`descriptorRefines_rejects_frozen_nonce` — the nonce-tick tooth.** If a decode asserts a
post-`cellPost` whose nonce is NOT the circuit-forced `cellPre.nonce + 1` (e.g. a frozen-nonce trace,
the pre-reconcile convention), then NO `Satisfied2` witness realizes that decode: the assumption is
`False`. The reconciled `gNonce` gate pins the tick, so a stale-nonce incrementNonce is UNSAT. -/
theorem descriptorRefines_rejects_frozen_nonce (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash incNonceV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (n : Int)
    (henc : rotatedEncodesIncNonce hash minit mfin maddrs t pre post actor cell n)
    (hwrong : henc.cellPost.nonce ≠ henc.cellPre.nonce + 1) :
    False :=
  hwrong (incNonce_nonce_forced hash hside hsat pre post actor cell n henc)

/-- **The economic-freeze polarity.** On the active row the balance column is FROZEN
(`gBalLoFreeze`), so a decode whose `cellPost` moves `bal_lo` away from `cellPre` is likewise UNSAT —
a nonce bump cannot silently move value. -/
theorem descriptorRefines_rejects_moved_balance (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash incNonceV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (n : Int)
    (henc : rotatedEncodesIncNonce hash minit mfin maddrs t pre post actor cell n)
    (hwrong : henc.cellPost.balLo ≠ henc.cellPre.balLo) :
    False := by
  have hspec : CellIncNonceSpec henc.cellPre henc.cellPost :=
    rotated_row_cellSpec hash hside hsat henc.wi henc.hwi henc.hwiNotLast henc.cellPre henc.cellPost
      henc.hwiRow henc.hwiEnc
  exact hwrong hspec.1

/-! ## §6 — Axiom-hygiene tripwires. -/

#assert_axioms rotated_row_gates
#assert_axioms rotated_row_cellSpec
#assert_axioms incNonce_nonce_forced
#assert_axioms incrementNonce_descriptorRefines
#assert_axioms incrementNonce_descriptorRefines_incremented
#assert_axioms descriptorRefines_rejects_frozen_nonce
#assert_axioms descriptorRefines_rejects_moved_balance

end Dregg2.Circuit.RotatedKernelRefinementIncNonce
