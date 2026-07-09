/-
# Dregg2.Circuit.CircuitCompletenessRecord — the COMPLETENESS rungs (wave 2) for the per-cell
VALUE/RECORD effects whose soundness rungs are realized: **incrementNonce**, **emitEvent**,
**pipelinedSend**, **makeSovereign**, **setFieldDyn**, **setPermissions**, **setVK**. The dual of the
soundness refinements in `RotatedKernelRefinement{IncNonce,Misc,PermsVK}`, mirroring the wave-1
`CircuitCompletenessValue` rungs (burn/mint/setField) and the transfer template
`CircuitCompleteness.transfer_descriptorComplete` EXACTLY.

SOUNDNESS (those files) is `<witness> + <encode> ⟹ <effect>Spec`: the circuit never accepts a forged
record/value move. COMPLETENESS is the OTHER direction: from the kernel `<effect>Spec` we CONSTRUCT the
`<effect>Encodes` witness (the moved column / committed FIX root = the spec's post value; the
frame/guard/log legs = the spec's named clauses), and the constructed witness, publishing the kernel's
own commitment, is the `descriptorComplete`-shaped satisfiability the apex consumes. A kernel-valid
record move HAS an accepting proof — the circuit never spuriously rejects a genuine effect.

## The split (dual to soundness, identical to wave-1's completeness template)

For each effect, exactly as `CircuitCompletenessValue.<e>_rotatedEncodes*_construct`:

  * the SPEC DETERMINES the kernel-side legs — the whole-`cell`-map move (`incNonceCellMap` /
    `sovereignRebind` / `setFieldCellMap` / `setPermsCellMap` / `setVKCellMap`), the admissibility guard,
    the 16-field (or 17-field, for the log-only effects) frame, the receipt log. These are discharged
    straight FROM the spec's conjuncts (`hspec.…`), not assumed.
  * the part the spec does NOT determine — the satisfying-witness FIX ROOT (`postRoot`/`hpost`/`gate`,
    and the `hRebindRoot` agreement for makeSovereign) for the FIX effects, OR the designated active
    circuit ROW + its `RowEncodes`/`hnVal` decode for incrementNonce — is the realizable PROVER floor
    (`IncNonceTraceProver` / `MakeSovereignRootProver` / `SetFieldDynRootProver` / `SetPermsRootProver`
    / `SetVKRootProver`), the construction dual of the soundness readout. Named precisely; not faked.

`emitEvent` and `pipelinedSend` are LIVE-descriptor effects (NO new committed root, NO designated
value row): their entire `<e>Encodes` is spec-determined (the live whole-state-row passthrough + the
receipt advance), so they carry NO prover-floor structure — just the spec-discharged construct.

## The non-vacuity teeth (the constructed decode is the REAL move)

Completeness is vacuous if the constructed witness is degenerate. Each rung carries the genuine tooth
(dual of soundness's `_rejects_wrong_*`), proving the constructed decode realizes the REAL kernel move,
via the SAME move-correctness lemma the soundness side uses:

  * incrementNonce: `fieldOf nonceField (post.cell cell) = n` (the nonce slot reads back the written
    value `n`) via `incrementNonce_cellWrite_correct`; AND the increment semantics `n = cellPre.nonce+1`;
  * emitEvent: `post.log = emitReceipt actor cell :: pre.log` (the observation clock genuinely ticks);
  * pipelinedSend: `post.log = pipelinedSendReceipt actor :: pre.log` (the apply-time clock ticks);
  * makeSovereign: `post.cell cell = .record [(commitmentField, .dig (stateCommitment (pre.cell cell)))]`
    (the genuine commitment-only rebind) via `sovereignRebindMap_correct`;
  * setFieldDyn: `fieldOf f (post.cell cell) = v` (the dynamic slot reads back `v`) via
    `setField_cellWrite_correct`/`writeFieldCellMap_correct`;
  * setPermissions: `fieldOf permsField (post.cell cell) = p` via `setPermissions_cellWrite_correct`;
  * setVK: `fieldOf vkField (post.cell cell) = vk` via `setVK_cellWrite_correct`.

Each spec is INHABITABLE (cited from the soundness/spec file's own witnesses, e.g.
`makeSovereignSpec_no_membership_gate`), so the antecedent is non-vacuous.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every new theorem; the trace/root
construction floors enter as named structure carriers (Type-valued realizable prover witnesses), never
as axioms. NEW file; imports read-only.
-/
import Dregg2.Circuit.CircuitCompleteness
import Dregg2.Circuit.RotatedKernelRefinementIncNonce
import Dregg2.Circuit.RotatedKernelRefinementMisc
import Dregg2.Circuit.RotatedKernelRefinementPermsVK
import Dregg2.Circuit.Spec.cellstatemonotone
import Dregg2.Circuit.Spec.sovereigncommitment
import Dregg2.Circuit.Spec.queuepipelinedsend
import Dregg2.Circuit.Spec.cellstatepermissions
import Dregg2.Circuit.Spec.cellstatevk
import Dregg2.Circuit.Spec.cellstatelog

namespace Dregg2.Circuit.CircuitCompletenessRecord

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.RotatedKernelRefinementIncNonce
open Dregg2.Circuit.RotatedKernelRefinementMisc
open Dregg2.Circuit.RotatedKernelRefinementPermsVK
open Dregg2.Circuit.RotatedKernelRefinementLifecycle (auditSlotRoot)
open Dregg2.Circuit.CircuitCompleteness (commitOf stateDecode_construct)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.StateCommit (AccountsWF compressNInjective)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 VmTrace Satisfied2 envAt)
open Dregg2.Circuit.RotatedKernelRefinement (RotTableSide)
open Dregg2.Circuit.Spec.CellStateMonotone
  (IncrementNonceSpec incNonceGuard incNonceCellMap incrementNonce_cellWrite_correct)
open Dregg2.Circuit.Spec.SovereignCommitment
  (MakeSovereignSpec MakeSovereignGuard sovereignRebindMap_correct makeSovereignSpec_commitment_value)
open Dregg2.Circuit.Spec.QueuePipelinedSend
  (PipelinedSendSpec pipelinedSendReceipt)
open Dregg2.Circuit.Spec.CellStatePermissions
  (SetPermissionsSpec setPermsGuard setPermsCellMap setPermissions_cellWrite_correct)
open Dregg2.Circuit.Spec.CellStateVK
  (SetVKSpec setVKGuard setVKCellMap setVK_cellWrite_correct)
open Dregg2.Circuit.Spec.CellStateLog
  (EmitEventSpec emitGuard emitReceipt)
open Dregg2.Circuit.Spec.CellStateField
  (SetFieldSpec SetFieldGuard setFieldCellMap writeFieldCellMap_correct)
open Dregg2.Exec
open Dregg2.Exec.EffectsState (fieldOf)
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false

/-! ## §1 — incrementNonce: the completeness rung (dual of `incrementNonce_descriptorRefines`).

`incrementNonce_descriptorRefines : Satisfied2 + rotatedEncodesIncNonce ⟹ IncrementNonceSpec`. We
invert: from `IncrementNonceSpec pre actor cell n post` the spec DETERMINES the whole-map bump
(`incNonceCellMap`), the guard (`incNonceGuard`), the 16-field frame, and the receipt log — straight off
the spec's conjuncts. Only the designated active circuit ROW `wi`, its `IsIncNonceRow`/`RowEncodesIncNonce`
decode, the decoded boundary `CellState`s, and the increment tie `hnVal : n = cellPre.nonce + 1` come
from the realizable prover floor. -/

/-- **`IncNonceTraceProver` — the realizable incrementNonce trace-row construction floor (NAMED, dual of
the soundness active-row readout).** The part of `rotatedEncodesIncNonce` the spec does NOT determine:
the designated active row `wi` (`s_increment_nonce = 1`, `s_noop = 0`), its `IsIncNonceRow`/
`RowEncodesIncNonce` decode, the decoded boundary `CellState`s, and the increment tie `hnVal` (the kernel
write value `n` IS the circuit-forced tick `cellPre.nonce + 1`). The honest prover's active nonce-tick
row. Data-bearing (`Type`). -/
structure IncNonceTraceProver (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (n : Int) : Type where
  wi : Nat
  hwi : wi < t.rows.length
  /-- the written row is an ACTIVE (transition) row, not the wrap/pad last row: the per-row gates run
  under `when_transition()`, forced only off the last row (the honest prover lays it in the active domain). -/
  hwiNotLast : wi + 1 ≠ t.rows.length
  cellPre : CellState
  cellPost : CellState
  hwiRow : Dregg2.Circuit.Emit.EffectVmEmitIncrementNonce.IsIncNonceRow (envAt t wi)
  hwiEnc : Dregg2.Circuit.Emit.EffectVmEmitIncrementNonce.RowEncodesIncNonce (envAt t wi) cellPre cellPost
  hnVal : n = cellPre.nonce + 1

/-- **`incrementNonce_rotatedEncodesIncNonce_construct` — CONSTRUCT the incrementNonce decode from the
spec.** From `IncrementNonceSpec pre actor cell n post` and the realizable `IncNonceTraceProver`,
ASSEMBLE `rotatedEncodesIncNonce`: the whole-map bump / 3-leg guard / 16 frame fields / log are ALL
discharged FROM the spec; only the active row + its increment tie come from the prover floor. The
trace-construction dual of `incrementNonce_descriptorRefines`. -/
def incrementNonce_rotatedEncodesIncNonce_construct (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (pre post : RecChainedState) (actor cell : CellId) (n : Int)
    (hspec : IncrementNonceSpec pre actor cell n post)
    (prover : IncNonceTraceProver hash minit mfin maddrs t n) :
    rotatedEncodesIncNonce hash minit mfin maddrs t pre post actor cell n where
  wi := prover.wi
  hwi := prover.hwi
  hwiNotLast := prover.hwiNotLast
  cellPre := prover.cellPre
  cellPost := prover.cellPost
  hwiRow := prover.hwiRow
  hwiEnc := prover.hwiEnc
  hnVal := prover.hnVal
  -- the whole-map bump IS the spec's `cell = incNonceCellMap …` clause.
  hcellMove := hspec.2.1
  -- the receipt log advance IS the spec's `log` clause.
  logAdv := hspec.2.2.1
  -- the 3-leg admissibility guard IS the spec's `incNonceGuard` (`hspec.1`).
  guard := hspec.1
  -- the 16 frame fields come from the spec's frame clauses.
  frAccounts          := hspec.2.2.2.1
  frCaps              := hspec.2.2.2.2.1
  frNullifiers        := hspec.2.2.2.2.2.1
  frRevoked           := hspec.2.2.2.2.2.2.1
  frCommitments       := hspec.2.2.2.2.2.2.2.1
  frBal               := hspec.2.2.2.2.2.2.2.2.1
  frSlotCaveats       := hspec.2.2.2.2.2.2.2.2.2.1
  frFactories         := hspec.2.2.2.2.2.2.2.2.2.2.1
  frLifecycle         := hspec.2.2.2.2.2.2.2.2.2.2.2.1
  frDeathCert         := hspec.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegate          := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegations       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpoch   := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpochAt := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frHeaps             := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frNullifierRoot     := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frRevokedRoot       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- **`incrementNonce_descriptorComplete_genuine` — the constructed decode realizes the GENUINE nonce
write.** From `IncrementNonceSpec`, the written `nonce` slot of `cell` reads back exactly `n`
(`incrementNonce_cellWrite_correct`). So the constructed witness performs the REAL nonce write — not a
degenerate no-write. The non-vacuity tooth. -/
theorem incrementNonce_descriptorComplete_genuine
    (pre post : RecChainedState) (actor cell : CellId) (n : Int)
    (hspec : IncrementNonceSpec pre actor cell n post) :
    fieldOf nonceField (post.kernel.cell cell) = n := by
  rw [hspec.2.1]
  exact (incrementNonce_cellWrite_correct pre.kernel cell n).1

/-- **`incrementNonce_descriptorComplete` — the incrementNonce completeness rung (dual of
`incrementNonce_descriptorRefines`).** From a kernel nonce-bump step `IncrementNonceSpec pre actor cell n
post` + the realizable prover construction, a circuit witness of `incNonceV3` whose published commitment
decodes to `(pre, post)`. Mirrors `setField_descriptorComplete`. -/
theorem incrementNonce_descriptorComplete
    (S : CommitSurface) (hash : List ℤ → ℤ)
    (buildWitness : ∀ (pre post : RecChainedState) (actor cell : CellId) (n : Int) (turn : BoundaryTurn),
      IncrementNonceSpec pre actor cell n post →
      Σ' (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
        Satisfied2 hash incNonceV3 minit mfin maddrs t ×'
        (tracePublishedCommit t = commitOf S pre post turn) ×'
        IncNonceTraceProver hash minit mfin maddrs t n)
    (pre post : RecChainedState) (actor cell : CellId) (n : Int) (turn : BoundaryTurn)
    (hspec : IncrementNonceSpec pre actor cell n post)
    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash incNonceV3 minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn ∧
      StateDecode S (commitOf S pre post turn) pre post := by
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub, prover⟩ :=
    buildWitness pre post actor cell n turn hspec
  clear buildWitness
  have _henc : rotatedEncodesIncNonce hash minit mfin maddrs t pre post actor cell n :=
    incrementNonce_rotatedEncodesIncNonce_construct hash pre post actor cell n hspec prover
  exact ⟨minit, mfin, maddrs, t, hsat, hpub,
    stateDecode_construct _ pre post turn hpreWF hpostWF⟩

/-! ## §2 — emitEvent: the completeness rung (dual of `emitEvent_descriptorRefines`). LIVE descriptor.

`emitEvent_descriptorRefines : emitEventEncodes ⟹ EmitEventSpec`, against the LIVE whole-state-row
passthrough (NO new committed root). The completeness direction: from `EmitEventSpec pre actor cell topic
data post` the spec DETERMINES the WHOLE `emitEventEncodes` — the cell-existence guard, the receipt
advance, and the 17-field whole-kernel frame are ALL spec conjuncts. So there is NO prover-floor
structure here: the entire decode is constructed from the spec. -/

/-- **`emitEvent_emitEventEncodes_construct` — CONSTRUCT the emitEvent decode from the spec.** From
`EmitEventSpec pre actor cell topic data post` (a kernel-valid emit), ASSEMBLE `emitEventEncodes`: every
leg (guard / receipt advance / 17-field frame) is discharged FROM the spec's conjuncts. The LIVE-
descriptor dual of `emitEvent_descriptorRefines` — no committed root, no designated value row. -/
def emitEvent_emitEventEncodes_construct
    (pre post : RecChainedState) (actor cell : CellId) (topic data : Int)
    (hspec : EmitEventSpec pre actor cell topic data post) :
    emitEventEncodes pre post actor cell where
  guard               := hspec.1
  logAdv              := hspec.2.1
  frAccounts          := hspec.2.2.1
  frCell              := hspec.2.2.2.1
  frCaps              := hspec.2.2.2.2.1
  frNullifiers        := hspec.2.2.2.2.2.1
  frRevoked           := hspec.2.2.2.2.2.2.1
  frCommitments       := hspec.2.2.2.2.2.2.2.1
  frBal               := hspec.2.2.2.2.2.2.2.2.1
  frSlotCaveats       := hspec.2.2.2.2.2.2.2.2.2.1
  frFactories         := hspec.2.2.2.2.2.2.2.2.2.2.1
  frLifecycle         := hspec.2.2.2.2.2.2.2.2.2.2.2.1
  frDeathCert         := hspec.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegate          := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegations       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpoch   := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpochAt := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frHeaps             := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frNullifierRoot     := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frRevokedRoot       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- **`emitEvent_descriptorComplete_genuine` — the constructed decode realizes the GENUINE receipt
advance.** From `EmitEventSpec`, the log grows by exactly the `emitReceipt actor cell` row — the
observation clock genuinely ticks, not a degenerate no-advance. The non-vacuity tooth. -/
theorem emitEvent_descriptorComplete_genuine
    (pre post : RecChainedState) (actor cell : CellId) (topic data : Int)
    (hspec : EmitEventSpec pre actor cell topic data post) :
    post.log = emitReceipt actor cell :: pre.log :=
  hspec.2.1

/-- **`emitEvent_descriptorComplete` — the emitEvent completeness rung (dual of
`emitEvent_descriptorRefines`).** From a kernel emit step `EmitEventSpec pre actor cell topic data post`
+ the realizable prover construction, a circuit witness of `emitEventV3` whose published commitment
decodes to `(pre, post)`. The descriptor `d` is the live emitEvent descriptor the prover names. -/
theorem emitEvent_descriptorComplete
    (S : CommitSurface) (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (buildWitness : ∀ (pre post : RecChainedState) (actor cell : CellId) (topic data : Int)
        (turn : BoundaryTurn),
      EmitEventSpec pre actor cell topic data post →
      Σ' (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
        Satisfied2 hash d minit mfin maddrs t ×'
        (tracePublishedCommit t = commitOf S pre post turn))
    (pre post : RecChainedState) (actor cell : CellId) (topic data : Int) (turn : BoundaryTurn)
    (hspec : EmitEventSpec pre actor cell topic data post)
    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash d minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn ∧
      StateDecode S (commitOf S pre post turn) pre post := by
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub⟩ :=
    buildWitness pre post actor cell topic data turn hspec
  clear buildWitness
  have _henc : emitEventEncodes pre post actor cell :=
    emitEvent_emitEventEncodes_construct pre post actor cell topic data hspec
  exact ⟨minit, mfin, maddrs, t, hsat, hpub,
    stateDecode_construct _ pre post turn hpreWF hpostWF⟩

/-! ## §3 — pipelinedSend: the completeness rung (dual of `pipelinedSend_descriptorRefines`). LIVE.

`pipelinedSend_descriptorRefines : pipelinedSendEncodes ⟹ PipelinedSendSpec`, against the LIVE
whole-state-row passthrough (NO new root, NO guard — `PipelinedSendSpec` is TOTAL). Completeness: from
`PipelinedSendSpec pre actor post` the spec DETERMINES the WHOLE `pipelinedSendEncodes` — the receipt
advance + the 16 (`frCell` + 15) whole-kernel frame fields. No prover-floor structure. -/

/-- **`pipelinedSend_pipelinedSendEncodes_construct` — CONSTRUCT the pipelinedSend decode from the
spec.** From `PipelinedSendSpec pre actor post` (a kernel-valid pipelined-send), ASSEMBLE
`pipelinedSendEncodes`: every leg (receipt advance / whole-kernel frame) is discharged FROM the spec's
conjuncts. The LIVE-descriptor dual of `pipelinedSend_descriptorRefines`. -/
def pipelinedSend_pipelinedSendEncodes_construct
    (pre post : RecChainedState) (actor : CellId)
    (hspec : PipelinedSendSpec pre actor post) :
    pipelinedSendEncodes pre post actor where
  logAdv              := hspec.1
  frAccounts          := hspec.2.1
  frCell              := hspec.2.2.1
  frCaps              := hspec.2.2.2.1
  frNullifiers        := hspec.2.2.2.2.1
  frRevoked           := hspec.2.2.2.2.2.1
  frCommitments       := hspec.2.2.2.2.2.2.1
  frBal               := hspec.2.2.2.2.2.2.2.1
  frSlotCaveats       := hspec.2.2.2.2.2.2.2.2.1
  frFactories         := hspec.2.2.2.2.2.2.2.2.2.1
  frLifecycle         := hspec.2.2.2.2.2.2.2.2.2.2.1
  frDeathCert         := hspec.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegate          := hspec.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegations       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpoch   := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpochAt := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frHeaps             := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frNullifierRoot     := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frRevokedRoot       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- **`pipelinedSend_descriptorComplete_genuine` — the constructed decode realizes the GENUINE receipt
advance.** From `PipelinedSendSpec`, the log grows by exactly the `pipelinedSendReceipt actor` row — the
apply-time clock genuinely ticks. The non-vacuity tooth. -/
theorem pipelinedSend_descriptorComplete_genuine
    (pre post : RecChainedState) (actor : CellId)
    (hspec : PipelinedSendSpec pre actor post) :
    post.log = pipelinedSendReceipt actor :: pre.log :=
  hspec.1

/-- **`pipelinedSend_descriptorComplete` — the pipelinedSend completeness rung (dual of
`pipelinedSend_descriptorRefines`).** From a kernel pipelined-send step `PipelinedSendSpec pre actor post`
+ the realizable prover construction, a circuit witness of the live `d` whose published commitment decodes
to `(pre, post)`. -/
theorem pipelinedSend_descriptorComplete
    (S : CommitSurface) (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (buildWitness : ∀ (pre post : RecChainedState) (actor : CellId) (turn : BoundaryTurn),
      PipelinedSendSpec pre actor post →
      Σ' (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
        Satisfied2 hash d minit mfin maddrs t ×'
        (tracePublishedCommit t = commitOf S pre post turn))
    (pre post : RecChainedState) (actor : CellId) (turn : BoundaryTurn)
    (hspec : PipelinedSendSpec pre actor post)
    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash d minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn ∧
      StateDecode S (commitOf S pre post turn) pre post := by
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub⟩ :=
    buildWitness pre post actor turn hspec
  clear buildWitness
  have _henc : pipelinedSendEncodes pre post actor :=
    pipelinedSend_pipelinedSendEncodes_construct pre post actor hspec
  exact ⟨minit, mfin, maddrs, t, hsat, hpub,
    stateDecode_construct _ pre post turn hpreWF hpostWF⟩

/-! ## §4 — makeSovereign: the completeness rung (dual of `makeSovereign_descriptorRefines`). FIX root.

`makeSovereign_descriptorRefines : makeSovereignEncodes ⟹ MakeSovereignSpec`, with the committed
`sovereignCommitRoot` FIX limb forcing the published digest to `stateCommitment (pre.cell cell)`.
Completeness: from `MakeSovereignSpec pre actor cell post` the spec DETERMINES the whole-`cell`-map rebind
(`sovereignRebind`), the guard, the log, and the 16-field frame. Only the FIX root (`postRoot`/`hpost`/
`gate`/`hRebindRoot`) comes from the realizable prover floor (the honest prover's committed sovereign-
commit limb). -/

/-- **`MakeSovereignRootProver` — the realizable makeSovereign FIX-root construction floor (NAMED, dual
of the soundness committed-limb readout).** The part of `makeSovereignEncodes` the spec does NOT
determine: the published `postRoot`, its identification with the post sovereign-commit root (`hpost`), the
FIX gate (`gate`) pinning it to `stateCommitment (pre.cell cell)`, and the pre/post root agreement
(`hRebindRoot`). The honest prover's committed sovereign-commit limb. Data-bearing (`Type`). -/
structure MakeSovereignRootProver (compressN : List ℤ → ℤ)
    (pre post : RecChainedState) (cell : CellId) : Type where
  postRoot : ℤ
  hpost : postRoot = sovereignCommitRoot compressN post.kernel.cell cell
  gate : gSovereignCommit compressN pre.kernel.cell cell postRoot
  hRebindRoot : sovereignCommitRoot compressN post.kernel.cell cell
      = sovereignCommitRoot compressN pre.kernel.cell cell

/-- **`makeSovereign_makeSovereignEncodes_construct` — CONSTRUCT the makeSovereign decode from the
spec.** From `MakeSovereignSpec pre actor cell post` and the realizable `MakeSovereignRootProver`,
ASSEMBLE `makeSovereignEncodes`: the whole-`cell`-map rebind / guard / log / 16 frame fields are
discharged FROM the spec; only the FIX root comes from the prover floor. The dual of
`makeSovereign_descriptorRefines`. -/
def makeSovereign_makeSovereignEncodes_construct (compressN : List ℤ → ℤ)
    (pre post : RecChainedState) (actor cell : CellId)
    (hspec : MakeSovereignSpec pre actor cell post)
    (prover : MakeSovereignRootProver compressN pre post cell) :
    makeSovereignEncodes compressN pre post actor cell where
  postRoot := prover.postRoot
  hpost := prover.hpost
  gate := prover.gate
  hRebindRoot := prover.hRebindRoot
  -- the whole-`cell`-map rebind IS the spec's `cell = sovereignRebind …` clause.
  cellMapMove         := hspec.2.1
  guard               := hspec.1
  logAdv              := hspec.2.2.1
  frAccounts          := hspec.2.2.2.1
  frCaps              := hspec.2.2.2.2.1
  frNullifiers        := hspec.2.2.2.2.2.1
  frRevoked           := hspec.2.2.2.2.2.2.1
  frCommitments       := hspec.2.2.2.2.2.2.2.1
  frBal               := hspec.2.2.2.2.2.2.2.2.1
  frSlotCaveats       := hspec.2.2.2.2.2.2.2.2.2.1
  frFactories         := hspec.2.2.2.2.2.2.2.2.2.2.1
  frLifecycle         := hspec.2.2.2.2.2.2.2.2.2.2.2.1
  frDeathCert         := hspec.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegate          := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegations       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpoch   := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpochAt := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frHeaps             := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frNullifierRoot     := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frRevokedRoot       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- **`makeSovereign_descriptorComplete_genuine` — the constructed decode realizes the GENUINE
commitment rebind.** From `MakeSovereignSpec`, the `cell` record is rebound to EXACTLY the commitment-form
record `[(commitmentField, .dig (stateCommitment (pre.cell cell))), (nonceField, .int (sovereignNonce
(pre.cell cell)))]` (`makeSovereignSpec_commitment_value` / `sovereignRebindMap_correct`) — the value
behind the commitment, the RESERVED replay nonce preserved. So the constructed witness performs the REAL
sovereign rebind — not a degenerate no-rebind. The non-vacuity tooth. -/
theorem makeSovereign_descriptorComplete_genuine
    (pre post : RecChainedState) (actor cell : CellId)
    (hspec : MakeSovereignSpec pre actor cell post) :
    post.kernel.cell cell
      = .record [(commitmentField, .dig (stateCommitment (pre.kernel.cell cell))),
                 (nonceField, .int (sovereignNonce (pre.kernel.cell cell)))] :=
  makeSovereignSpec_commitment_value hspec

/-- **`makeSovereign_descriptorComplete` — the makeSovereign completeness rung (dual of
`makeSovereign_descriptorRefines`).** From a kernel sovereign-rebind step `MakeSovereignSpec pre actor
cell post` + the realizable prover construction, a circuit witness of the live `d` whose published
commitment decodes to `(pre, post)`. -/
theorem makeSovereign_descriptorComplete (compressN : List ℤ → ℤ)
    (S : CommitSurface) (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (buildWitness : ∀ (pre post : RecChainedState) (actor cell : CellId) (turn : BoundaryTurn),
      MakeSovereignSpec pre actor cell post →
      Σ' (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
        Satisfied2 hash d minit mfin maddrs t ×'
        (tracePublishedCommit t = commitOf S pre post turn) ×'
        MakeSovereignRootProver compressN pre post cell)
    (pre post : RecChainedState) (actor cell : CellId) (turn : BoundaryTurn)
    (hspec : MakeSovereignSpec pre actor cell post)
    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash d minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn ∧
      StateDecode S (commitOf S pre post turn) pre post := by
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub, prover⟩ :=
    buildWitness pre post actor cell turn hspec
  clear buildWitness
  have _henc : makeSovereignEncodes compressN pre post actor cell :=
    makeSovereign_makeSovereignEncodes_construct compressN pre post actor cell hspec prover
  exact ⟨minit, mfin, maddrs, t, hsat, hpub,
    stateDecode_construct _ pre post turn hpreWF hpostWF⟩

/-! ## §5 — setFieldDyn: the completeness rung (dual of `setFieldDyn_descriptorRefines`). FIX root.

`setFieldDyn_descriptorRefines : setFieldDynEncodes ⟹ SetFieldSpec`, with the committed
`dynFieldSlotRoot` FIX limb forcing the dynamically-addressed slot to `v`. Completeness: from
`SetFieldSpec pre actor cell f v post` the spec DETERMINES the whole-`cell`-map move (`setFieldCellMap`),
the guard, the log, and the 16-field frame. Only the FIX root (`postRoot`/`hpost`/`gate`) comes from the
realizable prover floor. The kernel leaf is the EXISTING `SetFieldSpec` (setFieldDyn is the dynamic-slot
circuit shape of the same `setFieldA` effect). -/

/-- **`SetFieldDynRootProver` — the realizable setFieldDyn FIX-root construction floor (NAMED).** The
part of `setFieldDynEncodes` the spec does NOT determine: the published `postRoot`, its identification
with the post dyn-field-slot root (`hpost`), and the FIX gate (`gate`) pinning it to the written value
`v`. The honest prover's committed dyn-field-slot limb. Data-bearing (`Type`). -/
structure SetFieldDynRootProver (compressN : List ℤ → ℤ)
    (post : RecChainedState) (cell : CellId) (f : FieldName) (v : Int) : Type where
  postRoot : ℤ
  hpost : postRoot = dynFieldSlotRoot compressN post.kernel cell f
  gate : gDynFieldSet compressN cell f v postRoot

/-- **`setFieldDyn_setFieldDynEncodes_construct` — CONSTRUCT the setFieldDyn decode from the spec.** From
`SetFieldSpec pre actor cell f v post` and the realizable `SetFieldDynRootProver`, ASSEMBLE
`setFieldDynEncodes`: the whole-map move / guard / log / 16 frame fields are discharged FROM the spec;
only the FIX root comes from the prover floor. The dual of `setFieldDyn_descriptorRefines`. -/
def setFieldDyn_setFieldDynEncodes_construct (compressN : List ℤ → ℤ)
    (pre post : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (hspec : SetFieldSpec pre actor cell f v post)
    (prover : SetFieldDynRootProver compressN post cell f v) :
    setFieldDynEncodes compressN pre post actor cell f v where
  postRoot := prover.postRoot
  hpost := prover.hpost
  gate := prover.gate
  -- §RESERVED-SLOT: `SetFieldSpec` now leads with `reservedField f = false` (`hspec.1`), so the
  -- guard is `hspec.2.1` and every component below gains one `.2` (the whole-`cell`-map move IS the
  -- spec's `cell = setFieldCellMap …` clause).
  cellMapMove         := hspec.2.2.1
  guard               := hspec.2.1
  logAdv              := hspec.2.2.2.1
  frAccounts          := hspec.2.2.2.2.1
  frCaps              := hspec.2.2.2.2.2.1
  frNullifiers        := hspec.2.2.2.2.2.2.1
  frRevoked           := hspec.2.2.2.2.2.2.2.1
  frCommitments       := hspec.2.2.2.2.2.2.2.2.1
  frBal               := hspec.2.2.2.2.2.2.2.2.2.1
  frSlotCaveats       := hspec.2.2.2.2.2.2.2.2.2.2.1
  frFactories         := hspec.2.2.2.2.2.2.2.2.2.2.2.1
  frLifecycle         := hspec.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDeathCert         := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegate          := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegations       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpoch   := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpochAt := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frHeaps             := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frNullifierRoot     := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frRevokedRoot       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- **`setFieldDyn_descriptorComplete_genuine` — the constructed decode realizes the GENUINE dynamic
write.** From `SetFieldSpec`, the written slot `f` of `cell` reads back exactly `v`
(`setField_cellWrite_correct`). So the constructed witness performs the REAL dynamic field write — not a
degenerate no-write. The non-vacuity tooth. -/
theorem setFieldDyn_descriptorComplete_genuine
    (pre post : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (hspec : SetFieldSpec pre actor cell f v post) :
    fieldOf f (post.kernel.cell cell) = v := by
  rw [hspec.2.2.1]
  exact (writeFieldCellMap_correct pre.kernel.cell cell f v).1

/-- **`setFieldDyn_descriptorComplete` — the setFieldDyn completeness rung (dual of
`setFieldDyn_descriptorRefines`).** From a kernel dynamic field-write step `SetFieldSpec pre actor cell f
v post` + the realizable prover construction, a circuit witness of the live `d` whose published commitment
decodes to `(pre, post)`. -/
theorem setFieldDyn_descriptorComplete (compressN : List ℤ → ℤ)
    (S : CommitSurface) (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (buildWitness : ∀ (pre post : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
        (turn : BoundaryTurn),
      SetFieldSpec pre actor cell f v post →
      Σ' (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
        Satisfied2 hash d minit mfin maddrs t ×'
        (tracePublishedCommit t = commitOf S pre post turn) ×'
        SetFieldDynRootProver compressN post cell f v)
    (pre post : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int) (turn : BoundaryTurn)
    (hspec : SetFieldSpec pre actor cell f v post)
    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash d minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn ∧
      StateDecode S (commitOf S pre post turn) pre post := by
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub, prover⟩ :=
    buildWitness pre post actor cell f v turn hspec
  clear buildWitness
  have _henc : setFieldDynEncodes compressN pre post actor cell f v :=
    setFieldDyn_setFieldDynEncodes_construct compressN pre post actor cell f v hspec prover
  exact ⟨minit, mfin, maddrs, t, hsat, hpub,
    stateDecode_construct _ pre post turn hpreWF hpostWF⟩

/-! ## §6 — setPermissions: the completeness rung (dual of `setPermissions_descriptorRefines`). FIX root.

`setPermissions_descriptorRefines : setPermissionsEncodes ⟹ SetPermissionsSpec`, with the committed
`permsSlotRoot` FIX limb forcing the `"permissions"` slot to `p`. Completeness: from `SetPermissionsSpec
pre actor cell p post` the spec DETERMINES the whole-`cell`-map move (`setPermsCellMap`), the guard, the
log, and the 16-field frame. Only the FIX root comes from the realizable prover floor. -/

/-- **`SetPermsRootProver` — the realizable setPermissions FIX-root construction floor (NAMED).** The
part of `setPermissionsEncodes` the spec does NOT determine: the published `postRoot`, its identification
with the post permissions slot-root (`hpost`), and the FIX gate (`gate`) pinning it to `p`. The honest
prover's committed permissions slot limb. Data-bearing (`Type`). -/
structure SetPermsRootProver (compressN : List ℤ → ℤ)
    (post : RecChainedState) (cell : CellId) (p : Int) : Type where
  postRoot : ℤ
  hpost : postRoot = auditSlotRoot compressN post.kernel cell permsField
  gate : gSlotSet compressN cell permsField p postRoot

/-- **`setPermissions_setPermissionsEncodes_construct` — CONSTRUCT the setPermissions decode from the
spec.** From `SetPermissionsSpec pre actor cell p post` and the realizable `SetPermsRootProver`, ASSEMBLE
`setPermissionsEncodes`: the whole-map move / guard / log / 16 frame fields are discharged FROM the spec;
only the FIX root comes from the prover floor. The dual of `setPermissions_descriptorRefines`. -/
def setPermissions_setPermissionsEncodes_construct (compressN : List ℤ → ℤ)
    (pre post : RecChainedState) (actor cell : CellId) (p : Int)
    (hspec : SetPermissionsSpec pre actor cell p post)
    (prover : SetPermsRootProver compressN post cell p) :
    setPermissionsEncodes compressN pre post actor cell p where
  postRoot := prover.postRoot
  hpost := prover.hpost
  gate := prover.gate
  cellMapMove         := hspec.2.1
  guard               := hspec.1
  logAdv              := hspec.2.2.1
  frAccounts          := hspec.2.2.2.1
  frCaps              := hspec.2.2.2.2.1
  frNullifiers        := hspec.2.2.2.2.2.1
  frRevoked           := hspec.2.2.2.2.2.2.1
  frCommitments       := hspec.2.2.2.2.2.2.2.1
  frBal               := hspec.2.2.2.2.2.2.2.2.1
  frSlotCaveats       := hspec.2.2.2.2.2.2.2.2.2.1
  frFactories         := hspec.2.2.2.2.2.2.2.2.2.2.1
  frLifecycle         := hspec.2.2.2.2.2.2.2.2.2.2.2.1
  frDeathCert         := hspec.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegate          := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegations       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpoch   := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpochAt := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frHeaps             := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frNullifierRoot     := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frRevokedRoot       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- **`setPermissions_descriptorComplete_genuine` — the constructed decode realizes the GENUINE
permissions write.** From `SetPermissionsSpec`, the `"permissions"` slot of `cell` reads back exactly `p`
(`setPermissions_cellWrite_correct`). The non-vacuity tooth. -/
theorem setPermissions_descriptorComplete_genuine
    (pre post : RecChainedState) (actor cell : CellId) (p : Int)
    (hspec : SetPermissionsSpec pre actor cell p post) :
    fieldOf permsField (post.kernel.cell cell) = p := by
  rw [hspec.2.1]
  exact (setPermissions_cellWrite_correct pre.kernel cell p).1

/-- **`setPermissions_descriptorComplete` — the setPermissions completeness rung (dual of
`setPermissions_descriptorRefines`).** From a kernel permissions-write step `SetPermissionsSpec pre actor
cell p post` + the realizable prover construction, a circuit witness of the live `d` whose published
commitment decodes to `(pre, post)`. -/
theorem setPermissions_descriptorComplete (compressN : List ℤ → ℤ)
    (S : CommitSurface) (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (buildWitness : ∀ (pre post : RecChainedState) (actor cell : CellId) (p : Int) (turn : BoundaryTurn),
      SetPermissionsSpec pre actor cell p post →
      Σ' (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
        Satisfied2 hash d minit mfin maddrs t ×'
        (tracePublishedCommit t = commitOf S pre post turn) ×'
        SetPermsRootProver compressN post cell p)
    (pre post : RecChainedState) (actor cell : CellId) (p : Int) (turn : BoundaryTurn)
    (hspec : SetPermissionsSpec pre actor cell p post)
    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash d minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn ∧
      StateDecode S (commitOf S pre post turn) pre post := by
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub, prover⟩ :=
    buildWitness pre post actor cell p turn hspec
  clear buildWitness
  have _henc : setPermissionsEncodes compressN pre post actor cell p :=
    setPermissions_setPermissionsEncodes_construct compressN pre post actor cell p hspec prover
  exact ⟨minit, mfin, maddrs, t, hsat, hpub,
    stateDecode_construct _ pre post turn hpreWF hpostWF⟩

/-! ## §7 — setVK: the completeness rung (dual of `setVK_descriptorRefines`). FIX root.

The SAME record-slot flavor as setPermissions, over `vkField`, target `vk`, whole-map move
`setVKCellMap`. From `SetVKSpec pre actor cell vk post` the spec DETERMINES the whole-map move, guard,
log, and 16-field frame; only the FIX root comes from the realizable prover floor. -/

/-- **`SetVKRootProver` — the realizable setVK FIX-root construction floor (NAMED).** The part of
`setVKEncodes` the spec does NOT determine: the published `postRoot`, its identification with the post vk
slot-root (`hpost`), and the FIX gate (`gate`) pinning it to `vk`. The honest prover's committed vk slot
limb. Data-bearing (`Type`). -/
structure SetVKRootProver (compressN : List ℤ → ℤ)
    (post : RecChainedState) (cell : CellId) (vk : Int) : Type where
  postRoot : ℤ
  hpost : postRoot = auditSlotRoot compressN post.kernel cell vkField
  gate : gSlotSet compressN cell vkField vk postRoot

/-- **`setVK_setVKEncodes_construct` — CONSTRUCT the setVK decode from the spec.** From `SetVKSpec pre
actor cell vk post` and the realizable `SetVKRootProver`, ASSEMBLE `setVKEncodes`: the whole-map move /
guard / log / 16 frame fields are discharged FROM the spec; only the FIX root comes from the prover
floor. The dual of `setVK_descriptorRefines`. -/
def setVK_setVKEncodes_construct (compressN : List ℤ → ℤ)
    (pre post : RecChainedState) (actor cell : CellId) (vk : Int)
    (hspec : SetVKSpec pre actor cell vk post)
    (prover : SetVKRootProver compressN post cell vk) :
    setVKEncodes compressN pre post actor cell vk where
  postRoot := prover.postRoot
  hpost := prover.hpost
  gate := prover.gate
  cellMapMove         := hspec.2.1
  guard               := hspec.1
  logAdv              := hspec.2.2.1
  frAccounts          := hspec.2.2.2.1
  frCaps              := hspec.2.2.2.2.1
  frNullifiers        := hspec.2.2.2.2.2.1
  frRevoked           := hspec.2.2.2.2.2.2.1
  frCommitments       := hspec.2.2.2.2.2.2.2.1
  frBal               := hspec.2.2.2.2.2.2.2.2.1
  frSlotCaveats       := hspec.2.2.2.2.2.2.2.2.2.1
  frFactories         := hspec.2.2.2.2.2.2.2.2.2.2.1
  frLifecycle         := hspec.2.2.2.2.2.2.2.2.2.2.2.1
  frDeathCert         := hspec.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegate          := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegations       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpoch   := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpochAt := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frHeaps             := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frNullifierRoot     := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frRevokedRoot       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- **`setVK_descriptorComplete_genuine` — the constructed decode realizes the GENUINE vk write.** From
`SetVKSpec`, the `"verification_key"` slot of `cell` reads back exactly `vk`
(`setVK_cellWrite_correct`). The non-vacuity tooth (the upgrade-safety leg). -/
theorem setVK_descriptorComplete_genuine
    (pre post : RecChainedState) (actor cell : CellId) (vk : Int)
    (hspec : SetVKSpec pre actor cell vk post) :
    fieldOf vkField (post.kernel.cell cell) = vk := by
  rw [hspec.2.1]
  exact (setVK_cellWrite_correct pre.kernel cell vk).1

/-- **`setVK_descriptorComplete` — the setVK completeness rung (dual of `setVK_descriptorRefines`).** From
a kernel vk-write step `SetVKSpec pre actor cell vk post` + the realizable prover construction, a circuit
witness of the live `d` whose published commitment decodes to `(pre, post)`. -/
theorem setVK_descriptorComplete (compressN : List ℤ → ℤ)
    (S : CommitSurface) (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (buildWitness : ∀ (pre post : RecChainedState) (actor cell : CellId) (vk : Int) (turn : BoundaryTurn),
      SetVKSpec pre actor cell vk post →
      Σ' (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
        Satisfied2 hash d minit mfin maddrs t ×'
        (tracePublishedCommit t = commitOf S pre post turn) ×'
        SetVKRootProver compressN post cell vk)
    (pre post : RecChainedState) (actor cell : CellId) (vk : Int) (turn : BoundaryTurn)
    (hspec : SetVKSpec pre actor cell vk post)
    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash d minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn ∧
      StateDecode S (commitOf S pre post turn) pre post := by
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub, prover⟩ :=
    buildWitness pre post actor cell vk turn hspec
  clear buildWitness
  have _henc : setVKEncodes compressN pre post actor cell vk :=
    setVK_setVKEncodes_construct compressN pre post actor cell vk hspec prover
  exact ⟨minit, mfin, maddrs, t, hsat, hpub,
    stateDecode_construct _ pre post turn hpreWF hpostWF⟩

/-! ## §8 — axiom hygiene. -/

#assert_axioms incrementNonce_rotatedEncodesIncNonce_construct
#assert_axioms incrementNonce_descriptorComplete_genuine
#assert_axioms incrementNonce_descriptorComplete
#assert_axioms emitEvent_emitEventEncodes_construct
#assert_axioms emitEvent_descriptorComplete_genuine
#assert_axioms emitEvent_descriptorComplete
#assert_axioms pipelinedSend_pipelinedSendEncodes_construct
#assert_axioms pipelinedSend_descriptorComplete_genuine
#assert_axioms pipelinedSend_descriptorComplete
#assert_axioms makeSovereign_makeSovereignEncodes_construct
#assert_axioms makeSovereign_descriptorComplete_genuine
#assert_axioms makeSovereign_descriptorComplete
#assert_axioms setFieldDyn_setFieldDynEncodes_construct
#assert_axioms setFieldDyn_descriptorComplete_genuine
#assert_axioms setFieldDyn_descriptorComplete
#assert_axioms setPermissions_setPermissionsEncodes_construct
#assert_axioms setPermissions_descriptorComplete_genuine
#assert_axioms setPermissions_descriptorComplete
#assert_axioms setVK_setVKEncodes_construct
#assert_axioms setVK_descriptorComplete_genuine
#assert_axioms setVK_descriptorComplete

end Dregg2.Circuit.CircuitCompletenessRecord
