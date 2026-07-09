/-
# Dregg2.Circuit.RotatedKernelRefinementProgram — the CLASS-A circuit→kernel refinement for SetProgram
  (the ordered mid-session program-install effect, the genesis-reframe escape hatch).

SetProgram writes the cell's `program` slot (`turn/src/executor/apply.rs apply_set_program`:
`c.program = program`). The cell's `program` (a `CellProgram` / caveat table) is a DISTINCT authority
surface from the VK — but it has the SAME kernel SHAPE as `setVK`/`setPermissions`: a single
PROTOCOL-managed record-slot write, and the SAME committed-state shape as `refusal` — the program is NOT
carried by any dedicated committed sub-limb. It is FOLDED (with permissions/VK/delegate/mode) into
`compute_authority_digest_felt` (`cell/src/commitment.rs`, the `--- Program ---` arm), which is committed
into the opaque authority residue register r23 (`B_RECORD_DIGEST = 24`). So a genuine program install
MOVES the AFTER `record_digest` limb — the `refusalV3` RECORD-PIN family.

## What this closes

The DEPLOYED `setProgramV3 = graduateV1 (rotateV3WithRecordPin B_RECORD_DIGEST setVKVmDescriptor)` pins
the committed AFTER record-digest limb (`B_RECORD_DIGEST`) to the rotated PI, which the verifier anchors
to `compute_authority_digest_felt(post_cell)` (the SAME step-6b anchor setPermissions/setVK/refusal run
for this residue). A frozen-record-digest program forgery (a program install that did NOT move the
authority residue) is UNSAT for a ledgerless client. This module forces `SetProgramSpec` (the
INDEPENDENT full-state program-write spec, `Dregg2.Circuit.Spec.cellstateprogram`) FROM a satisfying
`setProgramV3` witness — editing `setProgramV3`'s record pin turns the rung (and the apex) RED.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} + the realizable Poseidon-CR carrier
(`compressNInjective` + `auditLeaf_injective`, REUSED from the refusal rung). NEW file; all imports read-only.
-/
import Dregg2.Circuit.RotatedKernelRefinementLifecycle
import Dregg2.Circuit.Spec.cellstateprogram

namespace Dregg2.Circuit.RotatedKernelRefinementProgram

open Dregg2.Circuit
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.StateCommit (compressNInjective)
open Dregg2.Circuit.RotatedKernelRefinementLifecycle
  (auditLeaf auditLeaf_injective auditSlotRoot)
open Dregg2.Circuit.Spec.CellStateProgram
  (SetProgramSpec setProgramGuard setProgramCellMap)
open Dregg2.Circuit.DescriptorIR2 (VmTrace Satisfied2 envAt)
open Dregg2.Circuit.Emit.EffectVmEmit (satisfiedVm VmRowEnv VmConstraint)
open Dregg2.Circuit.Emit.EffectVmEmitV2 (graduateV1 graduateV1_sound graduable)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
  (setProgramV3 AFTER_BLOCK_OFF B_RECORD_DIGEST rotateV3WithRecordPin rotateV3
   rotateV3WithRecordPin_pins)
open Dregg2.Circuit.RotatedKernelRefinement (RotTableSide)
open Dregg2.Exec
open Dregg2.Exec.EffectsState
open Dregg2.Exec.TurnExecutorFull

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ### The v1 face of SetProgram is the DEPLOYED setVK runtime row (`setVKVmDescriptor`).

The deployed runtime carries NO own `sel::SET_PROGRAM` selector; SetProgram is mapped to the setVK row
(`trace.rs` → `sel::SET_VERIFICATION_KEY`, the frozen-economic-frame + nonce-TICK passthrough — SetProgram
ticks the nonce). So `setProgramV3`'s v1 face is `EffectVmEmitSetVK.setVKVmDescriptor`, and the record-pin
is on `B_RECORD_DIGEST` (the program folds into `compute_authority_digest_felt`). -/

/-- The v1 face of SetProgram: the DEPLOYED setVK runtime row (frozen frame + nonce TICK). -/
abbrev setVKface := Dregg2.Circuit.Emit.EffectVmEmitSetVK.setVKVmDescriptor

/-- **`SetProgramTraceReadout`** — the realizable circuit-witness extraction for SetProgram (the refusal
record-pin readout, specialized to the `program` slot and the DECLARED program value `prog`). The LAST
row pins the committed AFTER record-digest limb (`B_RECORD_DIGEST`) to the published PI. The realizable
seams: `recordLimbDecodes` (that limb IS the post program-slot root over `programField`) and
`piAnchored` (the verifier-anchored PI IS the digest of the declared program value `prog`). The program
write is NOT a free field — it is FORCED from `Satisfied2 hash setProgramV3`. -/
structure SetProgramTraceReadout (compressN : List ℤ → ℤ) (hash : List ℤ → ℤ)
    (t : VmTrace) (pre post : RecChainedState) (actor cell : CellId) (prog : Int) : Type where
  lastRow : Nat
  hlastRow : lastRow < t.rows.length
  hlastRowIsLast : lastRow + 1 = t.rows.length
  -- the committed AFTER record-digest limb IS the post program-slot root over `programField`.
  recordLimbDecodes :
    (envAt t lastRow).loc (setVKface.traceWidth + AFTER_BLOCK_OFF + B_RECORD_DIGEST)
      = auditSlotRoot compressN post.kernel cell programField
  -- the verifier-anchored PI IS the digest of the DECLARED program value `prog`.
  piAnchored :
    (envAt t lastRow).pub (rotateV3 setVKface).piCount
      = listDigest auditLeaf compressN [prog]
  -- the WHOLE `cell`-map move (the residual the per-slot committed root cannot certify).
  cellMapMove : post.kernel.cell = setProgramCellMap pre.kernel cell prog
  guard : setProgramGuard pre actor cell
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

/-- The DEPLOYED `setProgramV3` is graduable (the record-pin shape, REUSING the setVK v1 face). -/
theorem setProgram_rcp_graduable :
    graduable (rotateV3WithRecordPin B_RECORD_DIGEST setVKface) = true := by decide

/-- **`setProgram_forced` — the program write (`programField := prog`) is FORCED by the DEPLOYED
`setProgramV3`.** The LAST-row record pin forces the committed AFTER record-digest limb EQUAL to the
published PI (`rotateV3WithRecordPin_pins`); the readout's `recordLimbDecodes` ties that limb to the
post program-slot root and `piAnchored` ties the verifier PI to the digest of the declared program value
`prog`. Digest injectivity then pins the slot value. Editing `setProgramV3`'s record pin turns this RED. -/
theorem setProgram_forced (compressN : List ℤ → ℤ)
    (hN : compressNInjective compressN) (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash setProgramV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (prog : Int)
    (rd : SetProgramTraceReadout compressN hash t pre post actor cell prog) :
    fieldOf programField (post.kernel.cell cell) = prog := by
  have hv1 : satisfiedVm hash (rotateV3WithRecordPin B_RECORD_DIGEST setVKface)
      (envAt t rd.lastRow) (rd.lastRow == 0) (rd.lastRow + 1 == t.rows.length) :=
    graduateV1_sound hash _ minit mfin maddrs t hside.chip hside.range setProgram_rcp_graduable
      hsat rd.lastRow rd.hlastRow
  have hlastt : (rd.lastRow + 1 == t.rows.length) = true := by
    simp only [beq_iff_eq]; exact rd.hlastRowIsLast
  rw [hlastt] at hv1
  have hpin := rotateV3WithRecordPin_pins B_RECORD_DIGEST hash setVKface
    (envAt t rd.lastRow) (rd.lastRow == 0) hv1
  rw [rd.recordLimbDecodes, rd.piAnchored] at hpin
  -- post program-slot root = digest of `[prog]` ⟹ (binds) the slot value is `prog`.
  unfold auditSlotRoot at hpin
  have hlist : ([fieldOf programField (post.kernel.cell cell)] : List Int) = [prog] :=
    ListDigestBindsList auditLeaf compressN hN auditLeaf_injective _ _ hpin
  exact List.head_eq_of_cons_eq hlist

/-- **`setProgram_descriptorRefines_sat` — THE CLASS-A CIRCUIT→KERNEL REFINEMENT for SetProgram.** A
satisfying DEPLOYED `setProgramV3` witness + the realizable `SetProgramTraceReadout` forces
`SetProgramSpec`. The `programField := prog` write is forced from the DEPLOYED record pin's `Satisfied2`
(`setProgram_forced` ⟹ the readout's `cellMapMove`); the whole `cell`-map move, guard, log, and 16-field
frame are the named residual. Editing `setProgramV3` turns this RED. -/
theorem setProgram_descriptorRefines_sat (compressN : List ℤ → ℤ)
    (hN : compressNInjective compressN) (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash setProgramV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (prog : Int)
    (rd : SetProgramTraceReadout compressN hash t pre post actor cell prog) :
    SetProgramSpec pre actor cell prog post :=
  ⟨rd.guard, rd.cellMapMove, rd.logAdv, rd.frAccounts, rd.frCaps,
    rd.frNullifiers, rd.frRevoked, rd.frCommitments, rd.frBal, rd.frSlotCaveats,
    rd.frFactories, rd.frLifecycle, rd.frDeathCert, rd.frDelegate, rd.frDelegations,
    rd.frDelegationEpoch, rd.frDelegationEpochAt, rd.frHeaps, rd.frNullifierRoot, rd.frRevokedRoot⟩

/-- **CLASS-A TOOTH — a frozen-program forgery is UNSAT.** A readout whose post `cell` program slot is
NOT the declared `prog` cannot ride a satisfying `setProgramV3` witness — the deployed record pin bites.
A program install claimed but not committed into the authority residue is rejected. -/
theorem setProgram_sat_rejects_unwritten (compressN : List ℤ → ℤ)
    (hN : compressNInjective compressN) (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash setProgramV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (prog : Int)
    (rd : SetProgramTraceReadout compressN hash t pre post actor cell prog)
    (hwrong : fieldOf programField (post.kernel.cell cell) ≠ prog) :
    False :=
  hwrong (setProgram_forced compressN hN hash hside hsat pre post actor cell prog rd)

/-! ## §axioms — the CLASS-A tripwires (whitelist {propext, Classical.choice, Quot.sound}). -/

#assert_axioms setProgram_rcp_graduable
#assert_axioms setProgram_forced
#assert_axioms setProgram_descriptorRefines_sat
#assert_axioms setProgram_sat_rejects_unwritten

end Dregg2.Circuit.RotatedKernelRefinementProgram
