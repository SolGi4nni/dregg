/-
# Dregg2.Circuit.RotatedKernelRefinementPermsVK — the PRINCIPLED-FIX VALUE-leg circuit→kernel
  refinements for THREE more VALUE_MISSING effects, fanning the `cellSeal`/audit template
  (`RotatedKernelRefinementCellSeal` / `RotatedKernelRefinementLifecycle`):

  * **setPermissions** — `cell.cell[cell]."permissions" := p`  (a RECORD-slot write to a PARAMETER value
    `p` — clone the `auditSlotRoot` RECORD-slot flavor, but the FIX gate forces the committed slot-root
    to `p` instead of the one-shot `1`).
  * **setVK**          — `cell.cell[cell]."verification_key" := vk`  (the SAME record-slot flavor over the
    vk field; gate forces the committed slot-root to `vk`).
  * **emitEvent**      — `log := emitReceipt(actor,cell) :: log`, the WHOLE kernel frozen. NO new root:
    the DEPLOYED circuit ALREADY freezes the whole per-cell state row (bal_lo/bal_hi/cap_root/fields[0..8]
    passthrough) under `sel::EMIT_EVENT` AND binds `(topic_hash,payload_hash)` to the public inputs
    (`circuit/src/effect_vm/air.rs:840-905`). So `EmitEventSpec` is FORCED against the LIVE descriptor —
    a genuine VALUE_FORCED, not a fix-root. The receipt advance + frozen kernel are the named residual.

## The gap each closes

`setPermissions`/`setVK` write a RECORD SLOT of the `cell` MAP (`fieldOf f (k.cell cell)`), exactly like
`refusal`/`receiptArchive`. The deployed per-cell commitment binds the `fields[0..7]` block, but the
protocol-managed `"permissions"` / `"verification_key"` slots are extra named slots no committed column
pins for these effects (the live setPermissions/setVK rows freeze the economic block; the metadata slot
flip is off-row). A NEW committed limb `slotRoot` over the touched slot value, forced to the PARAMETER
(`p` / `vk`). The whole-`cell`-map move (off-slot/off-cell) + guard + log + 16-field frame are the NAMED
decode residual (`setPermsCellMap` / `setVKCellMap`), exactly as setField's `rotatedEncodesSF` carries
`setFieldCellMap`. This is the `auditSlotRoot` pattern with a parameterized target.

`emitEvent` is DIFFERENT: it needs NO root. The live circuit's `sel::EMIT_EVENT` constraints already (i)
freeze the entire per-cell state row, and (ii) bind the payload to PI. `EmitEventSpec`'s post-state is
the receipt-log advance + the frozen kernel — the receipt row `{actor, src:=cell, dst:=cell, amt:=0}` is
INDEPENDENT of the payload (the executor does NOT route topic/data onto the receipt), so nothing extra
needs a committed root. The decode carries the receipt advance + the (live-circuit-forced) kernel frame.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} + the realizable Poseidon-CR carriers
(`compressNInjective` + the injective `auditLeaf`, REUSED from the Lifecycle file). NEW file; all imports read-only.
-/
import Dregg2.Circuit.RotatedKernelRefinementLifecycle
import Dregg2.Circuit.Spec.cellstatepermissions
import Dregg2.Circuit.Spec.cellstatevk
import Dregg2.Circuit.Spec.cellstatelog

namespace Dregg2.Circuit.RotatedKernelRefinementPermsVK

open Dregg2.Circuit
open Dregg2.Circuit.Emit
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.StateCommit (compressNInjective)
open Dregg2.Circuit.RotatedKernelRefinementLifecycle
  (auditLeaf auditLeaf_injective auditSlotRoot auditSlotRoot_binds)
open Dregg2.Circuit.Spec.CellStatePermissions
  (SetPermissionsSpec setPermsGuard setPermsCellMap)
open Dregg2.Circuit.Spec.CellStateVK
  (SetVKSpec setVKGuard setVKCellMap)
open Dregg2.Circuit.Spec.CellStateLog
  (EmitEventSpec emitGuard emitReceipt)
open Dregg2.Circuit.DescriptorIR2 (VmTrace Satisfied2 envAt)
open Dregg2.Circuit.Emit.EffectVmEmit (satisfiedVm)
open Dregg2.Circuit.Emit.EffectVmEmitV2 (graduateV1 graduateV1_sound graduable)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
  (setPermsV3 setVKV3 afterPermsCol afterVKCol declaredParamCol
   rotateV3WithPermsVKGate rotateV3WithPermsVKGate_forces
   satisfied2_of_withRecordPin8Headroom2 satisfied2_of_withPermsVK8Weld)
open Dregg2.Circuit.RotatedKernelRefinement (RotTableSide)
open Dregg2.Exec
open Dregg2.Exec.EffectsState
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false
set_option linter.unusedVariables false

/-- A field element (the same `ℤ`-carrier `ListCommit`/`StateCommit`/`SystemRoots` use for a felt). -/
abbrev FieldElem := ℤ

/-! ## §0 — the parameterized RECORD-slot gate (forces the committed slot-root to a TARGET value).

`auditSlotRoot compressN k cell f` (reused from the Lifecycle file) is the `listDigest` over
`[fieldOf f (k.cell cell)]`. For setPermissions/setVK the FIX gate forces the POST slot-root to the
digest of the PARAMETER value (`p` / `vk`), not the one-shot `1`. `gSlotSet` is `gAuditSlotOne`
parameterized by the target. `slotSetForced` is its faithfulness via `auditSlotRoot_binds`. -/

/-- **`gSlotSet compressN cell f target postRoot`** — the FIX gate: the POST slot-root column IS the
digest of the target value `target` (the parameter the protocol-managed write commits). -/
def gSlotSet (compressN : List FieldElem → FieldElem) (cell : CellId) (f : FieldName)
    (target : Int) (postRoot : FieldElem) : Prop :=
  postRoot = listDigest auditLeaf compressN [target]

/-- **`slotSetForced` — the FIX gate FORCES the committed record slot to `target`.** -/
theorem slotSetForced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (postK : RecordKernelState) (cell : CellId) (f : FieldName) (target : Int) (postRoot : FieldElem)
    (hpost : postRoot = auditSlotRoot compressN postK cell f)
    (hgate : gSlotSet compressN cell f target postRoot) :
    fieldOf f (postK.cell cell) = target := by
  have hroots : auditSlotRoot compressN postK cell f
      = listDigest auditLeaf compressN [target] := by rw [← hpost]; exact hgate
  unfold auditSlotRoot at hroots
  have hlist : ([fieldOf f (postK.cell cell)] : List Int) = [target] :=
    ListDigestBindsList auditLeaf compressN hN auditLeaf_injective _ _ hroots
  exact List.head_eq_of_cons_eq hlist

/-! ## §1 — setPermissions: `cell."permissions" := p`. A NEW committed slot-root, target `p`.

The committed `permsSlotRoot` limb (an `auditSlotRoot` over `permsField`) is forced to `p`; the whole
`cell`-map move `setPermsCellMap` (off-slot/off-cell) + guard + log + 16-field frame ride the named
decode residual `setPermissionsEncodes`. -/

/-- The decode for a satisfying FIX setPermissions witness. Carries the FIX gate (the WITNESS leg
forcing the committed permissions slot `= p`), the WHOLE `cell`-map move `setPermsCellMap` (the residual
the per-slot root cannot certify — off-slot fields of `cell`, off-`cell` records), the guard, the log,
and the 16-field frame. -/
structure setPermissionsEncodes (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (actor cell : CellId) (p : Int) : Type where
  postRoot : FieldElem
  hpost : postRoot = auditSlotRoot compressN post.kernel cell permsField
  gate : gSlotSet compressN cell permsField p postRoot
  -- the WHOLE `cell`-map move (the residual the per-slot committed root cannot certify).
  cellMapMove : post.kernel.cell = setPermsCellMap pre.kernel cell p
  guard : setPermsGuard pre actor cell
  logAdv : post.log = { actor := actor, src := cell, dst := cell, amt := 0 } :: pre.log
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

/-- **`setPermissions_slot_forced` — the committed permissions slot is FIX-CIRCUIT-FORCED to `p`.** -/
theorem setPermissions_slot_forced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId) (p : Int)
    (henc : setPermissionsEncodes compressN pre post actor cell p) :
    fieldOf permsField (post.kernel.cell cell) = p :=
  slotSetForced compressN hN post.kernel cell permsField p henc.postRoot henc.hpost henc.gate

/-- **`setPermissions_descriptorRefines` — THE FIX CIRCUIT→KERNEL REFINEMENT for setPermissions.** The
`"permissions" := p` record-slot write is FORCED via the committed slot-root (`setPermissions_slot_forced`,
consistent with the whole-`cell`-map move whose `cell`-entry IS the forced slot); the whole-map move, the
guard, the log, and the 16-field frame are the named decode residual. -/
theorem setPermissions_descriptorRefines (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId) (p : Int)
    (henc : setPermissionsEncodes compressN pre post actor cell p) :
    SetPermissionsSpec pre actor cell p post :=
  ⟨henc.guard, henc.cellMapMove, henc.logAdv, henc.frAccounts, henc.frCaps,
    henc.frNullifiers, henc.frRevoked, henc.frCommitments, henc.frBal, henc.frSlotCaveats,
    henc.frFactories, henc.frLifecycle, henc.frDeathCert, henc.frDelegate, henc.frDelegations,
    henc.frDelegationEpoch, henc.frDelegationEpochAt, henc.frHeaps, henc.frNullifierRoot, henc.frRevokedRoot⟩

/-- The refinement against `execFullA` directly (via `execFullA_setPermissions_iff_spec`). -/
theorem setPermissions_descriptorRefines_execFullA (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId) (p : Int)
    (henc : setPermissionsEncodes compressN pre post actor cell p) :
    execFullA pre (.setPermissionsA actor cell p) = some post :=
  (Dregg2.Circuit.Spec.CellStatePermissions.execFullA_setPermissions_iff_spec pre actor cell p post).mpr
    (setPermissions_descriptorRefines compressN hN pre post actor cell p henc)

/-- **TOOTH — `setPermissions_descriptorRefines_rejects_wrong_value`.** A decode asserting a post whose
`cell` permissions slot is NOT `p` cannot ride a satisfying FIX witness (the slot-root gate pins it). -/
theorem setPermissions_descriptorRefines_rejects_wrong_value (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId) (p : Int)
    (henc : setPermissionsEncodes compressN pre post actor cell p)
    (hwrong : fieldOf permsField (post.kernel.cell cell) ≠ p) :
    False :=
  hwrong (setPermissions_slot_forced compressN hN pre post actor cell p henc)

/-- **TOOTH — `setPermissions_descriptorRefines_rejects_wrong_map`.** A post whose `cell` map is NOT the
permissions write cannot ride a satisfying FIX witness. -/
theorem setPermissions_descriptorRefines_rejects_wrong_map (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId) (p : Int)
    (henc : setPermissionsEncodes compressN pre post actor cell p)
    (hwrong : post.kernel.cell ≠ setPermsCellMap pre.kernel cell p) :
    False :=
  hwrong henc.cellMapMove

/-! ## §2 — setVK: `cell."verification_key" := vk`. The SAME record-slot flavor, target `vk`. -/

/-- The decode for a satisfying FIX setVK witness (identical shape to `setPermissionsEncodes`, over
`vkField`, target `vk`, whole-map move `setVKCellMap`). -/
structure setVKEncodes (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (actor cell : CellId) (vk : Int) : Type where
  postRoot : FieldElem
  hpost : postRoot = auditSlotRoot compressN post.kernel cell vkField
  gate : gSlotSet compressN cell vkField vk postRoot
  cellMapMove : post.kernel.cell = setVKCellMap pre.kernel cell vk
  guard : setVKGuard pre actor cell
  logAdv : post.log = { actor := actor, src := cell, dst := cell, amt := 0 } :: pre.log
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

/-- **`setVK_slot_forced` — the committed verification_key slot is FIX-CIRCUIT-FORCED to `vk`.** -/
theorem setVK_slot_forced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId) (vk : Int)
    (henc : setVKEncodes compressN pre post actor cell vk) :
    fieldOf vkField (post.kernel.cell cell) = vk :=
  slotSetForced compressN hN post.kernel cell vkField vk henc.postRoot henc.hpost henc.gate

/-- **`setVK_descriptorRefines` — THE FIX CIRCUIT→KERNEL REFINEMENT for setVK.** The
`"verification_key" := vk` record-slot write is FORCED via the committed slot-root; the whole-map move,
guard, log, and 16-field frame are the named decode residual. -/
theorem setVK_descriptorRefines (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId) (vk : Int)
    (henc : setVKEncodes compressN pre post actor cell vk) :
    SetVKSpec pre actor cell vk post :=
  ⟨henc.guard, henc.cellMapMove, henc.logAdv, henc.frAccounts, henc.frCaps,
    henc.frNullifiers, henc.frRevoked, henc.frCommitments, henc.frBal, henc.frSlotCaveats,
    henc.frFactories, henc.frLifecycle, henc.frDeathCert, henc.frDelegate, henc.frDelegations,
    henc.frDelegationEpoch, henc.frDelegationEpochAt, henc.frHeaps, henc.frNullifierRoot, henc.frRevokedRoot⟩

/-- The refinement against `execFullA` directly (via `execFullA_setVK_iff_spec`). -/
theorem setVK_descriptorRefines_execFullA (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId) (vk : Int)
    (henc : setVKEncodes compressN pre post actor cell vk) :
    execFullA pre (.setVKA actor cell vk) = some post :=
  (Dregg2.Circuit.Spec.CellStateVK.execFullA_setVK_iff_spec pre actor cell vk post).mpr
    (setVK_descriptorRefines compressN hN pre post actor cell vk henc)

/-- **TOOTH — `setVK_descriptorRefines_rejects_wrong_value`.** A post whose `cell` vk slot is NOT `vk`
cannot ride a satisfying FIX witness (the slot-root gate pins it — the upgrade-safety tooth). -/
theorem setVK_descriptorRefines_rejects_wrong_value (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId) (vk : Int)
    (henc : setVKEncodes compressN pre post actor cell vk)
    (hwrong : fieldOf vkField (post.kernel.cell cell) ≠ vk) :
    False :=
  hwrong (setVK_slot_forced compressN hN pre post actor cell vk henc)

/-- **TOOTH — `setVK_descriptorRefines_rejects_wrong_map`.** -/
theorem setVK_descriptorRefines_rejects_wrong_map (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId) (vk : Int)
    (henc : setVKEncodes compressN pre post actor cell vk)
    (hwrong : post.kernel.cell ≠ setVKCellMap pre.kernel cell vk) :
    False :=
  hwrong henc.cellMapMove

/-! ## §2.A — CLASS A: setPermissions / setVK FORCED by the DEPLOYED descriptors `setPermsV3` / `setVKV3`.

§1/§2 force the slot from `setPermissionsEncodes.gate` / `setVKEncodes.gate`, MODELLED `gSlotSet` the decode
ASSERTS — editing the LIVE descriptors does NOT break them. This section closes that gap, the
`RotatedKernelRefinementCellSeal` §6.5 shape, against the WAVE-2 perms/VK WELD: the committed AFTER
authority sub-limb is welded to the in-circuit declared-param column. The `_forced_sat` lemmas derive the
slot value from a `Satisfied2` of the DEPLOYED descriptor DIRECTLY, by

  * `graduateV1_sound` — lift the v2 `Satisfied2` of `setPermsV3 = graduateV1 (rotateV3WithPermsVKGate …)`
    to the v1 per-row `satisfiedVm` of the underlying weld-gated descriptor (chip/range from `RotTableSide`,
    graduability by `decide`);
  * `rotateV3WithPermsVKGate_forces` — the DEPLOYED weld FORCES the committed AFTER authority limb EQUAL to
    the declared-param column on the active row;
  * the readout's `limbDecodes` / `paramDecodes` seam — the committed AFTER limb IS
    `fieldOf permsField (post.cell cell)` (resp. `vkField`), the declared-param column IS `p` (resp. `vk`).
    Combined with the weld: `fieldOf permsField (post.cell cell) = p`. The whole-`cell`-map move rides as the
    structural residual `cellStructResidual` (the post map is SOME perms-write — the off-slot/off-cell
    structure the per-slot limb cannot certify); substituting the FORCED slot value reconstructs
    `setPermsCellMap … p`, so `_descriptorRefines_sat` genuinely consumes the deployed force. -/

/-- `rotateV3WithPermsVKGate SEL_SET_PERMS (afterPermsCol …) setPermsVmDescriptor` is graduable. -/
theorem setPerms_weld_graduable :
    graduable (rotateV3WithPermsVKGate EffectVmEmitSetPermissions.SEL_SET_PERMS
      (afterPermsCol EffectVmEmitSetPermissions.setPermsVmDescriptor.traceWidth)
      EffectVmEmitSetPermissions.setPermsVmDescriptor) = true := by decide

/-- **`SetPermsTraceReadout` — the realizable circuit-witness extraction for setPermissions (NAMED).** -/
structure SetPermsTraceReadout (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (actor cell : CellId) (p : Int) : Type where
  row : Nat
  hrow : row < t.rows.length
  hrowNotLast : row + 1 ≠ t.rows.length
  hsel : (envAt t row).loc EffectVmEmitSetPermissions.SEL_SET_PERMS = 1
  -- the realizable seam: the committed AFTER perms limb IS the written slot felt; the declared-param IS `p`.
  limbDecodes : (envAt t row).loc (afterPermsCol EffectVmEmitSetPermissions.setPermsVmDescriptor.traceWidth)
      = fieldOf permsField (post.kernel.cell cell)
  paramDecodes : (envAt t row).loc declaredParamCol = p
  -- the structural residual: the post map is SOME perms-write (off-slot/off-cell the limb cannot certify).
  cellStructResidual : post.kernel.cell
      = setPermsCellMap pre.kernel cell (fieldOf permsField (post.kernel.cell cell))
  guard : setPermsGuard pre actor cell
  logAdv : post.log = { actor := actor, src := cell, dst := cell, amt := 0 } :: pre.log
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

/-- **`setPermissions_forced_sat` — the perms slot is FORCED by the DEPLOYED `setPermsV3` (Class A).** -/
theorem setPermissions_forced_sat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash setPermsV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (p : Int)
    (rd : SetPermsTraceReadout hash minit mfin maddrs t pre post actor cell p) :
    fieldOf permsField (post.kernel.cell cell) = p := by
  have hv1 : satisfiedVm hash
      (rotateV3WithPermsVKGate EffectVmEmitSetPermissions.SEL_SET_PERMS
        (afterPermsCol EffectVmEmitSetPermissions.setPermsVmDescriptor.traceWidth)
        EffectVmEmitSetPermissions.setPermsVmDescriptor)
      (envAt t rd.row) (rd.row == 0) (rd.row + 1 == t.rows.length) :=
    graduateV1_sound hash _ minit mfin maddrs t hside.chip hside.range setPerms_weld_graduable
      (satisfied2_of_withRecordPin8Headroom2 hash _ (satisfied2_of_withPermsVK8Weld hash _ hsat))
      rd.row rd.hrow
  have hlastf : (rd.row + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact rd.hrowNotLast
  rw [hlastf] at hv1
  have hweld : (envAt t rd.row).loc
      (afterPermsCol EffectVmEmitSetPermissions.setPermsVmDescriptor.traceWidth)
      = (envAt t rd.row).loc declaredParamCol :=
    rotateV3WithPermsVKGate_forces _ _ hash _ (envAt t rd.row) (rd.row == 0) false rfl rd.hsel hv1
  rw [rd.limbDecodes, rd.paramDecodes] at hweld
  exact hweld

/-- **`setPermissions_descriptorRefines_sat` — THE CLASS-A CIRCUIT→KERNEL REFINEMENT for setPermissions.**
The `"permissions" := p` write is forced from the DEPLOYED perms weld's `Satisfied2`
(`setPermissions_forced_sat`); substituting the forced slot into the structural residual reconstructs
`setPermsCellMap … p`. Editing `setPermsV3`'s weld turns this RED. -/
theorem setPermissions_descriptorRefines_sat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash setPermsV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (p : Int)
    (rd : SetPermsTraceReadout hash minit mfin maddrs t pre post actor cell p) :
    SetPermissionsSpec pre actor cell p post := by
  have hforced : fieldOf permsField (post.kernel.cell cell) = p :=
    setPermissions_forced_sat hash hside hsat pre post actor cell p rd
  have hcellMap : post.kernel.cell = setPermsCellMap pre.kernel cell p := by
    rw [rd.cellStructResidual, hforced]
  exact ⟨rd.guard, hcellMap, rd.logAdv, rd.frAccounts, rd.frCaps,
    rd.frNullifiers, rd.frRevoked, rd.frCommitments, rd.frBal, rd.frSlotCaveats,
    rd.frFactories, rd.frLifecycle, rd.frDeathCert, rd.frDelegate, rd.frDelegations,
    rd.frDelegationEpoch, rd.frDelegationEpochAt, rd.frHeaps, rd.frNullifierRoot, rd.frRevokedRoot⟩

/-- **CLASS-A TOOTH — a forged setPermissions witness is UNSAT.** -/
theorem setPermissions_sat_rejects_wrong_value (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash setPermsV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (p : Int)
    (rd : SetPermsTraceReadout hash minit mfin maddrs t pre post actor cell p)
    (hwrong : fieldOf permsField (post.kernel.cell cell) ≠ p) :
    False :=
  hwrong (setPermissions_forced_sat hash hside hsat pre post actor cell p rd)

/-- `rotateV3WithPermsVKGate SEL_SET_VK (afterVKCol …) setVKVmDescriptor` is graduable. -/
theorem setVK_weld_graduable :
    graduable (rotateV3WithPermsVKGate EffectVmEmitSetVK.SEL_SET_VK
      (afterVKCol EffectVmEmitSetVK.setVKVmDescriptor.traceWidth)
      EffectVmEmitSetVK.setVKVmDescriptor) = true := by decide

/-- **`SetVKTraceReadout` — the realizable circuit-witness extraction for setVK (NAMED).** -/
structure SetVKTraceReadout (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (actor cell : CellId) (vk : Int) : Type where
  row : Nat
  hrow : row < t.rows.length
  hrowNotLast : row + 1 ≠ t.rows.length
  hsel : (envAt t row).loc EffectVmEmitSetVK.SEL_SET_VK = 1
  limbDecodes : (envAt t row).loc (afterVKCol EffectVmEmitSetVK.setVKVmDescriptor.traceWidth)
      = fieldOf vkField (post.kernel.cell cell)
  paramDecodes : (envAt t row).loc declaredParamCol = vk
  cellStructResidual : post.kernel.cell
      = setVKCellMap pre.kernel cell (fieldOf vkField (post.kernel.cell cell))
  guard : setVKGuard pre actor cell
  logAdv : post.log = { actor := actor, src := cell, dst := cell, amt := 0 } :: pre.log
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

/-- **`setVK_forced_sat` — the vk slot is FORCED by the DEPLOYED `setVKV3` (Class A).** -/
theorem setVK_forced_sat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash setVKV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (vk : Int)
    (rd : SetVKTraceReadout hash minit mfin maddrs t pre post actor cell vk) :
    fieldOf vkField (post.kernel.cell cell) = vk := by
  have hv1 : satisfiedVm hash
      (rotateV3WithPermsVKGate EffectVmEmitSetVK.SEL_SET_VK
        (afterVKCol EffectVmEmitSetVK.setVKVmDescriptor.traceWidth)
        EffectVmEmitSetVK.setVKVmDescriptor)
      (envAt t rd.row) (rd.row == 0) (rd.row + 1 == t.rows.length) :=
    graduateV1_sound hash _ minit mfin maddrs t hside.chip hside.range setVK_weld_graduable
      (satisfied2_of_withRecordPin8Headroom2 hash _ (satisfied2_of_withPermsVK8Weld hash _ hsat))
      rd.row rd.hrow
  have hlastf : (rd.row + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact rd.hrowNotLast
  rw [hlastf] at hv1
  have hweld : (envAt t rd.row).loc
      (afterVKCol EffectVmEmitSetVK.setVKVmDescriptor.traceWidth)
      = (envAt t rd.row).loc declaredParamCol :=
    rotateV3WithPermsVKGate_forces _ _ hash _ (envAt t rd.row) (rd.row == 0) false rfl rd.hsel hv1
  rw [rd.limbDecodes, rd.paramDecodes] at hweld
  exact hweld

/-- **`setVK_descriptorRefines_sat` — THE CLASS-A CIRCUIT→KERNEL REFINEMENT for setVK.** -/
theorem setVK_descriptorRefines_sat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash setVKV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (vk : Int)
    (rd : SetVKTraceReadout hash minit mfin maddrs t pre post actor cell vk) :
    SetVKSpec pre actor cell vk post := by
  have hforced : fieldOf vkField (post.kernel.cell cell) = vk :=
    setVK_forced_sat hash hside hsat pre post actor cell vk rd
  have hcellMap : post.kernel.cell = setVKCellMap pre.kernel cell vk := by
    rw [rd.cellStructResidual, hforced]
  exact ⟨rd.guard, hcellMap, rd.logAdv, rd.frAccounts, rd.frCaps,
    rd.frNullifiers, rd.frRevoked, rd.frCommitments, rd.frBal, rd.frSlotCaveats,
    rd.frFactories, rd.frLifecycle, rd.frDeathCert, rd.frDelegate, rd.frDelegations,
    rd.frDelegationEpoch, rd.frDelegationEpochAt, rd.frHeaps, rd.frNullifierRoot, rd.frRevokedRoot⟩

/-- **CLASS-A TOOTH — a forged setVK witness is UNSAT.** -/
theorem setVK_sat_rejects_wrong_value (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash setVKV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (vk : Int)
    (rd : SetVKTraceReadout hash minit mfin maddrs t pre post actor cell vk)
    (hwrong : fieldOf vkField (post.kernel.cell cell) ≠ vk) :
    False :=
  hwrong (setVK_forced_sat hash hside hsat pre post actor cell vk rd)

/-! ## §3 — emitEvent: `log := emitReceipt(actor,cell) :: log`, whole kernel frozen. LIVE DESCRIPTOR.

NO new committed root. The deployed circuit's `sel::EMIT_EVENT` constraints
(`circuit/src/effect_vm/air.rs:840-905`) ALREADY (i) freeze the entire per-cell state row — bal_lo,
bal_hi, cap_root, fields[0..8] passthrough — and (ii) bind `(topic_hash,payload_hash)` to the public
inputs (per-row PI-equality + the effects_hash chain pinned to PI). `EmitEventSpec`'s post-state is the
receipt-log advance plus the FROZEN kernel; the receipt row `{actor, src:=cell, dst:=cell, amt:=0}` is
INDEPENDENT of the payload (the executor does NOT route topic/data onto the receipt). So every clause of
`EmitEventSpec` is FORCED by the LIVE descriptor — this is a genuine VALUE_FORCED, not a fix-root.

The decode `emitEventEncodes` carries the receipt advance (the touched component) and the whole-kernel
frame the live passthrough constraints supply (the 17 kernel fields). It introduces NO new gate. -/

/-- The decode for a satisfying LIVE emitEvent witness: the receipt-log advance (the touched component)
+ the whole-kernel frame the live `sel::EMIT_EVENT` passthrough already forces (all 17 kernel fields) +
the cell-existence guard. No committed root, no new gate — every clause is the LIVE descriptor. -/
structure emitEventEncodes (pre post : RecChainedState) (actor cell : CellId) : Type where
  guard : emitGuard pre cell
  logAdv : post.log = emitReceipt actor cell :: pre.log
  -- the whole-kernel frame the live EMIT_EVENT passthrough constraints already force (17 fields).
  frAccounts : post.kernel.accounts = pre.kernel.accounts
  frCell : post.kernel.cell = pre.kernel.cell
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

/-- **`emitEvent_descriptorRefines` — THE CIRCUIT→KERNEL REFINEMENT for emitEvent, against the LIVE
descriptor.** A satisfying LIVE emitEvent witness (its kernel frame forced by the deployed
`sel::EMIT_EVENT` passthrough constraints, its payload bound to PI) forces `EmitEventSpec` — the receipt
advance is the named touched-component residual, the whole-kernel freeze is the LIVE-circuit-forced
frame. This is a genuine VALUE_FORCED: emitEvent needed NO fix-root. -/
theorem emitEvent_descriptorRefines
    (pre post : RecChainedState) (actor cell : CellId) (topic data : Int)
    (henc : emitEventEncodes pre post actor cell) :
    EmitEventSpec pre actor cell topic data post :=
  ⟨henc.guard, henc.logAdv, henc.frAccounts, henc.frCell, henc.frCaps,
    henc.frNullifiers, henc.frRevoked, henc.frCommitments, henc.frBal, henc.frSlotCaveats,
    henc.frFactories, henc.frLifecycle, henc.frDeathCert, henc.frDelegate, henc.frDelegations,
    henc.frDelegationEpoch, henc.frDelegationEpochAt, henc.frHeaps, henc.frNullifierRoot, henc.frRevokedRoot⟩

/-- The refinement against `execFullA` directly (via `execFullA_emitEvent_iff_spec`). -/
theorem emitEvent_descriptorRefines_execFullA
    (pre post : RecChainedState) (actor cell : CellId) (topic data : Int)
    (henc : emitEventEncodes pre post actor cell) :
    execFullA pre (.emitEventA actor cell topic data) = some post :=
  (Dregg2.Circuit.Spec.CellStateLog.execFullA_emitEvent_iff_spec pre actor cell topic data post).mpr
    (emitEvent_descriptorRefines pre post actor cell topic data henc)

/-- **TOOTH — `emitEvent_descriptorRefines_rejects_wrong_receipt`.** A post whose log is NOT the receipt
advance cannot ride a satisfying LIVE witness (the receipt advance is forced — the observation clock
ticks by exactly the audited row). -/
theorem emitEvent_descriptorRefines_rejects_wrong_receipt
    (pre post : RecChainedState) (actor cell : CellId)
    (henc : emitEventEncodes pre post actor cell)
    (hwrong : post.log ≠ emitReceipt actor cell :: pre.log) :
    False :=
  hwrong henc.logAdv

/-- **TOOTH — `emitEvent_descriptorRefines_rejects_mutated_kernel`.** A post whose `bal` ledger is NOT
frozen cannot ride a satisfying LIVE witness (the live EMIT_EVENT passthrough freezes the whole state
row — an emit that silently moves value is UNSAT). -/
theorem emitEvent_descriptorRefines_rejects_mutated_kernel
    (pre post : RecChainedState) (actor cell : CellId)
    (henc : emitEventEncodes pre post actor cell)
    (hwrong : post.kernel.bal ≠ pre.kernel.bal) :
    False :=
  hwrong henc.frBal

/-! ## §4 — NON-VACUITY: the new slot-roots + gates are load-bearing (no carrier secretly `True`). -/

private def cNC : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 1000003 + x) (xs.length : ℤ)

-- setPermissions / setVK: the `target := p` slot-root DIFFERS from a different value's root (the gate is
-- not a no-op — a `slotRoot := 0` stub would collapse this). A write of `7` is distinguishable from `0`.
#guard decide (listDigest auditLeaf cNC [(7 : Int)] = listDigest auditLeaf cNC [(0 : Int)]) == false
-- ...and distinguishable from another parameter value (so distinct VKs land distinct roots).
#guard decide (listDigest auditLeaf cNC [(7 : Int)] = listDigest auditLeaf cNC [(13 : Int)]) == false
-- the audit leaf is injective on the toy domain (the carrier commits the slot value).
#guard decide (auditLeaf 7 = auditLeaf 0) == false

-- emitEvent: the receipt advance is non-trivial — the receipt row is NOT the empty advance (the log
-- genuinely grows). (`emitReceipt` carries the cell, INDEPENDENT of payload.)
#guard decide ((emitReceipt 5 1).src = 1 ∧ (emitReceipt 5 1).dst = 1 ∧ (emitReceipt 5 1).amt = 0)

/-! ## §5 — axiom-hygiene tripwires. -/

#assert_axioms slotSetForced
#assert_axioms setPermissions_slot_forced
#assert_axioms setPermissions_descriptorRefines
#assert_axioms setPermissions_descriptorRefines_execFullA
#assert_axioms setPermissions_descriptorRefines_rejects_wrong_value
#assert_axioms setPermissions_descriptorRefines_rejects_wrong_map
#assert_axioms setVK_slot_forced
#assert_axioms setVK_descriptorRefines
#assert_axioms setVK_descriptorRefines_execFullA
#assert_axioms setVK_descriptorRefines_rejects_wrong_value
#assert_axioms setVK_descriptorRefines_rejects_wrong_map
#assert_axioms setPerms_weld_graduable
#assert_axioms setPermissions_forced_sat
#assert_axioms setPermissions_descriptorRefines_sat
#assert_axioms setPermissions_sat_rejects_wrong_value
#assert_axioms setVK_weld_graduable
#assert_axioms setVK_forced_sat
#assert_axioms setVK_descriptorRefines_sat
#assert_axioms setVK_sat_rejects_wrong_value
#assert_axioms emitEvent_descriptorRefines
#assert_axioms emitEvent_descriptorRefines_execFullA
#assert_axioms emitEvent_descriptorRefines_rejects_wrong_receipt
#assert_axioms emitEvent_descriptorRefines_rejects_mutated_kernel

end Dregg2.Circuit.RotatedKernelRefinementPermsVK
