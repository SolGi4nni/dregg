/-
# Dregg2.Circuit.FloorsNonVacuousWavePermsProgram — the PERMS / VK / PROGRAM / REVOKE `*TraceReadout`
  carriers are NON-VACUOUS.

Companion to `FloorsNonVacuousWave` (the `CellSealTraceReadout` template) and
`FloorsNonVacuousWaveLifecycle` (the lifecycle/audit examples). Each of the four refinement rungs
covered here —

  * `setPermissions_descriptorRefines_sat`  (premise `SetPermsTraceReadout`)
  * `setVK_descriptorRefines_sat`           (premise `SetVKTraceReadout`)
  * `setProgram_descriptorRefines_sat`      (premise `SetProgramTraceReadout`)
  * `revokeCapability_descriptorRefines_sat`(premise `RevokeCapabilityTraceReadout`)

— takes a `<E>TraceReadout` as a PREMISE; a secretly-uninhabitable premise makes its consuming rung
VACUOUSLY satisfiable. This module exhibits a CONCRETE inhabiting term per readout, so each readout is
`Nonempty` and its rung is NON-vacuous.

The shapes used:

  * setPerms / setVK — the CLASS-A weld readouts. The active row carries the selector hot; the AFTER
    perms/VK limb and the declared-param column both read `0`. The boundary's `cell`-map IS the
    declarative `setPermsCellMap …/setVKCellMap …` slot write at value `0`, so the seam value
    `fieldOf permsField (post.cell cell)` (resp. `vkField`) is genuinely `0` (by the slot write/read
    law `set*_cellWrite_correct`), the limb-decode matches, the param-decode matches, and the
    `cellStructResidual` is the slot-write reconstruction. Guard at the self-targeted live account `0`.

  * setProgram — the record-pin readout (LAST row only). With `compressN := cZero` the post program-slot
    `auditSlotRoot` and `listDigest auditLeaf cZero [0]` BOTH collapse to `0` — exactly the all-zero wrap
    row + all-zero `pub` the trace carries. The `cellMapMove` is the `setProgramCellMap …` slot write.

  * revokeCapability — the cap-remove readout. The decode seam is an IMPLICATION; setting
    `post.caps = removeEdgeCaps pre.caps holder target` makes its conclusion hold (`fun _ => rfl`). The
    `KernelFrameExceptCaps` is all-`rfl` (post differs from pre only on `caps` and `log`). No guard leg
    (the `RevokeSpec` admissibility slot is `trivial`).

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Every inhabitation is a CONSTRUCTED term;
no fresh axiom. NEW file; imports read-only.
-/
import Dregg2.Circuit.FloorsNonVacuousWave
import Dregg2.Circuit.FloorsNonVacuousWaveLifecycle
import Dregg2.Circuit.RotatedKernelRefinementPermsVK
import Dregg2.Circuit.RotatedKernelRefinementProgram
import Dregg2.Circuit.RotatedKernelRefinementCapFamily

namespace Dregg2.Circuit.FloorsNonVacuousWavePermsProgram

set_option autoImplicit false

open Dregg2.Circuit.DescriptorIR2 (VmTrace envAt zeroAsg)
open Dregg2.Circuit.FloorsNonVacuous (permOutZ)
open Dregg2.Circuit.FloorsNonVacuousWave (readoutTrace readoutTrace_rows_len readoutTrace_loc0
  readoutTrace_side)
open Dregg2.Circuit.FloorsNonVacuousWaveLifecycle (readoutTrace_loc1 readoutTrace_pub)
open Dregg2.Exec (RecChainedState CellId)
open Dregg2.Exec.EffectsState (fieldOf)
open Dregg2.Exec.TurnExecutorFull (permsField vkField programField authReceipt)

/-! ## §1 — `SetPermsTraceReadout` INHABITED.

The active row 0 carries `SEL_SET_PERMS = 26` hot; the AFTER perms limb (`afterPermsCol … = 272`) and
the declared-param column (`declaredParamCol = 68`) both read `0` (the row is zero off the selector). The
boundary's `cell`-map IS `setPermsCellMap pre 0 0` (the `permissions := 0` slot write at the live
self-targeted account `0`), so `fieldOf permsField (post.cell 0) = 0` (slot write/read law). The seams
match `0`; `cellStructResidual` is the slot-write reconstruction; the guard is self-authority + membership
+ liveness at `0`. -/

open Dregg2.Circuit.RotatedKernelRefinementPermsVK (SetPermsTraceReadout)
open Dregg2.Circuit.Emit.EffectVmEmitSetPermissions (SEL_SET_PERMS setPermsVmDescriptor)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (afterPermsCol afterVKCol declaredParamCol)
open Dregg2.Circuit.Spec.CellStatePermissions (setPermsCellMap setPermsGuard
  setPermissions_cellWrite_correct)

/-- The active row for setPerms: hot at `SEL_SET_PERMS (= 26)`, zero elsewhere. -/
def permsRow0 : Dregg2.Circuit.Assignment :=
  fun c => if c = SEL_SET_PERMS then 1 else 0

/-- The live self-targeted boundary: account `0`, `permissions := 0` slot write. -/
def permsPre : RecChainedState :=
  { kernel := { accounts := {0}, cell := fun _ => default, caps := fun _ => [] }, log := [] }

def permsPost : RecChainedState :=
  { kernel := { permsPre.kernel with cell := setPermsCellMap permsPre.kernel 0 0 },
    log := { actor := 0, src := 0, dst := 0, amt := 0 } :: permsPre.log }

/-- The seam value: `fieldOf permsField (post.cell 0) = 0` (the slot write/read law). -/
theorem permsPost_slot : fieldOf permsField (permsPost.kernel.cell 0) = 0 :=
  (setPermissions_cellWrite_correct permsPre.kernel 0 0).1

/-- **`SetPermsTraceReadout` is INHABITED.** (`p := 0`.) -/
def setPerms_readout :
    SetPermsTraceReadout (fun ins => (permOutZ ins).headD 0) (fun _ => 0) (fun _ => (0, 0)) []
      (readoutTrace permsRow0) permsPre permsPost 0 0 0 where
  row := 0
  hrow := by rw [readoutTrace_rows_len]; omega
  hrowNotLast := by rw [readoutTrace_rows_len]; omega
  hsel := by rw [readoutTrace_loc0]; simp [permsRow0]
  limbDecodes := by
    rw [readoutTrace_loc0]
    have hcol : (afterPermsCol setPermsVmDescriptor.traceWidth = SEL_SET_PERMS) = False := by decide
    simp only [permsRow0, hcol, if_false]
    exact (permsPost_slot).symm
  paramDecodes := by
    rw [readoutTrace_loc0]
    have hcol : (declaredParamCol = SEL_SET_PERMS) = False := by decide
    simp only [permsRow0, hcol, if_false]
  cellStructResidual := by rw [permsPost_slot]; rfl
  guard := by refine ⟨by decide, ?_, by decide⟩; decide
  logAdv := rfl
  frAccounts := rfl
  frCaps := rfl
  frNullifiers := rfl
  frRevoked := rfl
  frCommitments := rfl
  frBal := rfl
  frSlotCaveats := rfl
  frFactories := rfl
  frLifecycle := rfl
  frDeathCert := rfl
  frDelegate := rfl
  frDelegations := rfl
  frDelegationEpoch := rfl
  frDelegationEpochAt := rfl
  frHeaps := rfl
  frNullifierRoot := rfl
  frRevokedRoot := rfl

theorem setPerms_readout_inhabited :
    Nonempty (SetPermsTraceReadout (fun ins => (permOutZ ins).headD 0) (fun _ => 0) (fun _ => (0, 0)) []
      (readoutTrace permsRow0) permsPre permsPost 0 0 0) :=
  ⟨setPerms_readout⟩

#assert_axioms setPerms_readout

/-! ## §2 — `SetVKTraceReadout` INHABITED. Exactly the §1 shape, specialized to the VK slot. -/

open Dregg2.Circuit.RotatedKernelRefinementPermsVK (SetVKTraceReadout)
open Dregg2.Circuit.Emit.EffectVmEmitSetVK (SEL_SET_VK setVKVmDescriptor)
open Dregg2.Circuit.Spec.CellStateVK (setVKCellMap setVKGuard setVK_cellWrite_correct)

/-- The active row for setVK: hot at `SEL_SET_VK (= 27)`, zero elsewhere. -/
def vkRow0 : Dregg2.Circuit.Assignment :=
  fun c => if c = SEL_SET_VK then 1 else 0

/-- The live self-targeted boundary: account `0`, `verification_key := 0` slot write. -/
def vkPre : RecChainedState :=
  { kernel := { accounts := {0}, cell := fun _ => default, caps := fun _ => [] }, log := [] }

def vkPost : RecChainedState :=
  { kernel := { vkPre.kernel with cell := setVKCellMap vkPre.kernel 0 0 },
    log := { actor := 0, src := 0, dst := 0, amt := 0 } :: vkPre.log }

/-- The seam value: `fieldOf vkField (post.cell 0) = 0` (the slot write/read law). -/
theorem vkPost_slot : fieldOf vkField (vkPost.kernel.cell 0) = 0 :=
  (setVK_cellWrite_correct vkPre.kernel 0 0).1

/-- **`SetVKTraceReadout` is INHABITED.** (`vk := 0`.) -/
def setVK_readout :
    SetVKTraceReadout (fun ins => (permOutZ ins).headD 0) (fun _ => 0) (fun _ => (0, 0)) []
      (readoutTrace vkRow0) vkPre vkPost 0 0 0 where
  row := 0
  hrow := by rw [readoutTrace_rows_len]; omega
  hrowNotLast := by rw [readoutTrace_rows_len]; omega
  hsel := by rw [readoutTrace_loc0]; simp [vkRow0]
  limbDecodes := by
    rw [readoutTrace_loc0]
    have hcol : (afterVKCol setVKVmDescriptor.traceWidth = SEL_SET_VK) = False := by decide
    simp only [vkRow0, hcol, if_false]
    exact (vkPost_slot).symm
  paramDecodes := by
    rw [readoutTrace_loc0]
    have hcol : (declaredParamCol = SEL_SET_VK) = False := by decide
    simp only [vkRow0, hcol, if_false]
  cellStructResidual := by rw [vkPost_slot]; rfl
  guard := by refine ⟨by decide, ?_, by decide⟩; decide
  logAdv := rfl
  frAccounts := rfl
  frCaps := rfl
  frNullifiers := rfl
  frRevoked := rfl
  frCommitments := rfl
  frBal := rfl
  frSlotCaveats := rfl
  frFactories := rfl
  frLifecycle := rfl
  frDeathCert := rfl
  frDelegate := rfl
  frDelegations := rfl
  frDelegationEpoch := rfl
  frDelegationEpochAt := rfl
  frHeaps := rfl
  frNullifierRoot := rfl
  frRevokedRoot := rfl

theorem setVK_readout_inhabited :
    Nonempty (SetVKTraceReadout (fun ins => (permOutZ ins).headD 0) (fun _ => 0) (fun _ => (0, 0)) []
      (readoutTrace vkRow0) vkPre vkPost 0 0 0) :=
  ⟨setVK_readout⟩

#assert_axioms setVK_readout

/-! ## §3 — `SetProgramTraceReadout` INHABITED.

LAST row only. With `compressN := cZero` the post program-slot `auditSlotRoot` and the published-PI
`listDigest auditLeaf cZero [0]` BOTH collapse to `0` — exactly the all-zero wrap row (`readoutTrace_loc1`)
and all-zero `pub` (`readoutTrace_pub`) the trace carries. The `cellMapMove` is the `program := 0` slot
write; the guard is self-authority + membership + liveness at `0`. -/

open Dregg2.Circuit.RotatedKernelRefinementProgram (SetProgramTraceReadout setVKface)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (AFTER_BLOCK_OFF B_RECORD_DIGEST rotateV3)
open Dregg2.Circuit.RotatedKernelRefinementLifecycle (auditSlotRoot auditLeaf)
open Dregg2.Circuit.ListCommit (listDigest)
open Dregg2.Circuit.Spec.CellStateProgram (setProgramCellMap setProgramGuard)

/-- The constant-zero committer (the `cZero` of the lifecycle wave). -/
def cZero : List ℤ → ℤ := fun _ => 0

/-- The live self-targeted boundary: account `0`, `program := 0` slot write. -/
def progPre : RecChainedState :=
  { kernel := { accounts := {0}, cell := fun _ => default, caps := fun _ => [] }, log := [] }

def progPost : RecChainedState :=
  { kernel := { progPre.kernel with cell := setProgramCellMap progPre.kernel 0 0 },
    log := { actor := 0, src := 0, dst := 0, amt := 0 } :: progPre.log }

/-- **`SetProgramTraceReadout` is INHABITED.** (`prog := 0`, `compressN := cZero`.) -/
def setProgram_readout :
    SetProgramTraceReadout cZero (fun ins => (permOutZ ins).headD 0)
      (readoutTrace zeroAsg) progPre progPost 0 0 0 where
  lastRow := 1
  hlastRow := by rw [readoutTrace_rows_len]; omega
  hlastRowIsLast := by rw [readoutTrace_rows_len]
  recordLimbDecodes := by rw [readoutTrace_loc1]; rfl
  piAnchored := by rw [readoutTrace_pub]; rfl
  cellMapMove := rfl
  guard := by refine ⟨by decide, ?_, by decide⟩; decide
  logAdv := rfl
  frAccounts := rfl
  frCaps := rfl
  frNullifiers := rfl
  frRevoked := rfl
  frCommitments := rfl
  frBal := rfl
  frSlotCaveats := rfl
  frFactories := rfl
  frLifecycle := rfl
  frDeathCert := rfl
  frDelegate := rfl
  frDelegations := rfl
  frDelegationEpoch := rfl
  frDelegationEpochAt := rfl
  frHeaps := rfl
  frNullifierRoot := rfl
  frRevokedRoot := rfl

theorem setProgram_readout_inhabited :
    Nonempty (SetProgramTraceReadout cZero (fun ins => (permOutZ ins).headD 0)
      (readoutTrace zeroAsg) progPre progPost 0 0 0) :=
  ⟨setProgram_readout⟩

#assert_axioms setProgram_readout

/-! ## §4 — `RevokeCapabilityTraceReadout` INHABITED.

The active row 0 carries `sel.REVOKE_CAPABILITY = 24` hot. The decode seam `capsMoveDecodes` is an
IMPLICATION; setting `post.caps = removeEdgeCaps pre.caps 0 0` makes its conclusion hold for ANY hypothesis
(`fun _ => rfl`). The `KernelFrameExceptCaps` is all-`rfl` (post differs from pre only on `caps` and
`log`); the log advances by `authReceipt 0`. NO guard leg (the `RevokeSpec` admissibility slot is
`trivial`). -/

open Dregg2.Circuit.RotatedKernelRefinementCapFamily (RevokeCapabilityTraceReadout KernelFrameExceptCaps)
open Dregg2.Circuit.Spec.AuthorityRevocation (removeEdgeCaps)
open Dregg2.Circuit.Emit.EffectVmEmit.sel (REVOKE_CAPABILITY)

/-- The active row for revokeCapability: hot at `sel.REVOKE_CAPABILITY (= 24)`, zero elsewhere. -/
def revRow0 : Dregg2.Circuit.Assignment :=
  fun c => if c = REVOKE_CAPABILITY then 1 else 0

/-- The boundary: the cap-edge `(0,0)` removed, the receipt advanced. -/
def revPre : RecChainedState :=
  { kernel := { accounts := ∅, cell := fun _ => default, caps := fun _ => [] }, log := [] }

def revPost : RecChainedState :=
  { kernel := { revPre.kernel with caps := removeEdgeCaps revPre.kernel.caps 0 0 },
    log := authReceipt 0 :: revPre.log }

/-- The shared sixteen-field frame (post differs from pre only on `caps`, `log`). -/
def revFrame : KernelFrameExceptCaps revPre revPost :=
  { frAccounts := rfl, frCell := rfl, frNullifiers := rfl, frRevoked := rfl,
    frCommitments := rfl, frBal := rfl, frSlotCaveats := rfl, frFactories := rfl,
    frLifecycle := rfl, frDeathCert := rfl, frDelegate := rfl, frDelegations := rfl,
    frDelegationEpoch := rfl, frDelegationEpochAt := rfl, frHeaps := rfl,
    frNullifierRoot := rfl, frRevokedRoot := rfl }

/-- **`RevokeCapabilityTraceReadout` is INHABITED** (for EVERY `Cap8Scheme` — the decode seam
`capsMoveDecodes` is an implication discharged `fun _ => rfl`, scheme-independent).
(`holder = target = 0`.) -/
def revokeCapability_readout (S8 : Dregg2.Circuit.DeployedCapTree.Cap8Scheme) :
    RevokeCapabilityTraceReadout S8 (fun ins => (permOutZ ins).headD 0) (fun _ => 0) (fun _ => (0, 0)) []
      (readoutTrace revRow0) revPre revPost 0 0 where
  row := 0
  hrow := by rw [readoutTrace_rows_len]; omega
  hsel := by rw [readoutTrace_loc0]; simp [revRow0]
  capsMoveDecodes := fun _ => rfl
  logAdv := rfl
  frame := revFrame

theorem revokeCapability_readout_inhabited (S8 : Dregg2.Circuit.DeployedCapTree.Cap8Scheme) :
    Nonempty (RevokeCapabilityTraceReadout S8 (fun ins => (permOutZ ins).headD 0) (fun _ => 0)
      (fun _ => (0, 0)) [] (readoutTrace revRow0) revPre revPost 0 0) :=
  ⟨revokeCapability_readout S8⟩

#assert_axioms revokeCapability_readout

end Dregg2.Circuit.FloorsNonVacuousWavePermsProgram
