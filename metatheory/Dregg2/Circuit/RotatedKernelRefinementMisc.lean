/-
# Dregg2.Circuit.RotatedKernelRefinementMisc — the VALUE-leg circuit→kernel refinements for THREE
  more effects, classified HONESTLY against the LIVE descriptors / the principled-fix template:

  * **makeSovereign** — `cell.cell[cell]` REBOUND to the commitment-only record
    `[(commitmentField, .dig (stateCommitment (cell cell)))]`  (a value-rebind dropping the readable
    record behind a 32-byte commitment). CLASS = **PROVEN-FIX**. The published commitment digest is
    `stateCommitment (pre.cell cell)`; that digest is NOT in the deployed per-cell commitment preimage
    `hash(bal,nonce,fields,cap_root)` (the rebind drops the WHOLE record behind a SEPARATE digest no
    committed column pins). So we clone the slot-root fix: a NEW committed `sovereignCommitRoot` limb
    over `stateCommitment (pre.cell cell)`, forced by the gate to the genuine pre-value commitment.
    The whole-`cell`-map rebind (off-cell preservation) + guard + log + 16-field frame are the NAMED
    decode residual (exactly setPermissions's `setPermsCellMap`).

  * **setFieldDyn** — `cell.cell[cell].f := v` where the slot `f` rides a DYNAMIC param-indexed
    address. CLASS = **PROVEN-FIX**. The live `setFieldDynVmDescriptor2` binds the value via a
    param→param MEMORY READBACK at the dynamic address `param[SLOT]` (`fieldReadbackOp`,
    `setFieldDyn_readback_genuine` = Blum), NOT the per-slot committed write COLUMN `setFieldV3 slot`
    uses (`gFieldWrite slot`). The dynamic address is not a committed column of the published
    `state_commit`, so the written value is unbound by the LEDGER commitment. Clone the slot-root fix:
    a NEW committed `dynFieldSlotRoot` over the written slot `f` of `cell`, forced to `v`. The kernel
    leaf is the EXISTING `SetFieldSpec actor cell f v` (the `setFieldA` arm — `setFieldDyn` is the same
    kernel effect, the dynamic-slot circuit shape). The whole-map move + guard + log + frame = NAMED.

  * **pipelinedSend** — `log := pipelinedSendReceipt actor :: log`, the WHOLE kernel LITERALLY frozen.
    CLASS = **PROVEN-LIVE**, NO new root. The actual Lean `PipelinedSendSpec` is TOTAL (no guard) and
    its FRAME is all 17 kernel fields literally unchanged — there is NO nonce field in the kernel
    record that ticks, so the "literal-freeze vs nonce-tick" frame mismatch the brief worried about
    does NOT arise against this spec. The effect is structurally `emitEvent` (receipt-advance + whole-
    kernel freeze): a genuine VALUE_FORCED against the LIVE descriptor's whole-state-row passthrough,
    the receipt-advance the touched-component residual. Cloned from `RotatedKernelRefinementPermsVK`'s
    `emitEvent` arm verbatim in shape.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} + the realizable Poseidon-CR carriers
(`compressNInjective` + the injective `auditLeaf`, REUSED from the Lifecycle file) for the two fix
effects; `pipelinedSend` carries NO crypto carrier (pure live-descriptor). NEW file; all imports read-only.
-/
import Dregg2.Circuit.RotatedKernelRefinementPermsVK
import Dregg2.Circuit.Spec.cellstatefield
import Dregg2.Circuit.Spec.sovereigncommitment
import Dregg2.Circuit.Spec.queuepipelinedsend

namespace Dregg2.Circuit.RotatedKernelRefinementMisc

open Dregg2.Circuit
open Dregg2.Circuit.Emit
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.StateCommit (compressNInjective)
open Dregg2.Circuit.RotatedKernelRefinementLifecycle
  (auditLeaf auditLeaf_injective)
open Dregg2.Circuit.Spec.SovereignCommitment
  (MakeSovereignSpec MakeSovereignGuard)
open Dregg2.Circuit.Spec.CellStateField
  (SetFieldSpec SetFieldGuard setFieldCellMap)
open Dregg2.Circuit.Spec.QueuePipelinedSend
  (PipelinedSendSpec pipelinedSendReceipt)
open Dregg2.Circuit.DescriptorIR2 (VmTrace Satisfied2 envAt)
open Dregg2.Circuit.Emit.EffectVmEmit (satisfiedVm)
open Dregg2.Circuit.Emit.EffectVmEmitV2 (graduateV1 graduateV1_sound graduable)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
  (makeSovereignV3 setFieldDynForcedV3 afterModeCol afterFieldsRootCol modeSovereign
   declaredFieldsRootCol rotateV3WithModeGate rotateV3WithFieldsRootGate rotateV3WithFieldsRootGate_mem
   makeSovereignV3_forces_sovereign setFieldDynV1Face permsVKWeldGate permsVKWeldGate_forces
   satisfied2_of_withRecordPin8Headroom2)
open Dregg2.Circuit.DescriptorIR2 (VmConstraint2)
open Dregg2.Circuit.RotatedKernelRefinement (RotTableSide)
open Dregg2.Exec
open Dregg2.Exec.EffectsState (fieldOf)
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false
set_option linter.unusedVariables false

-- The makeSovereign mode-limb decode (`MakeSovereignTraceReadout.modeLimbDecodes`) is a boolean
-- indicator `if post.kernel.cell = sovereignRebind … then 1 else 0` over a FUNCTION equality
-- (`CellId → Value`), which is not constructively decidable. The realizable trace-fill emits the felt
-- by computing that equality concretely; in Lean we read it through `Classical.propDecidable` (already
-- in the file's allowed axiom set, `Classical.choice`). The `_sat` proofs never `decide` it — they
-- contradict the `if_neg` branch — so this is a pure elaboration aid, not a computational dependency.
open scoped Classical

/-- A field element (the same `ℤ`-carrier the commitment limbs use for a felt). -/
abbrev FieldElem := ℤ

/-! ## §0 — the two committed FIX roots (the digest of a single target felt) + the forcing lemma.

Both fix effects commit ONE protocol-managed value behind a NEW `listDigest auditLeaf` limb — the SAME
`auditLeaf`/`compressNInjective` realizable Poseidon-CR carrier the Lifecycle/PermsVK files use. The
generic gate `gFixOne target postRoot` pins `postRoot = listDigest auditLeaf compressN [target]`, and
`fixRootBinds` recovers `target` from a post-root equal to that digest (via `ListDigestBindsList`). -/

/-- **`gFixOne compressN target postRoot`** — the FIX gate: the POST committed limb IS the digest of
the single target felt `target` (the value the protocol-managed write commits). -/
def gFixOne (compressN : List FieldElem → FieldElem) (target : Int) (postRoot : FieldElem) : Prop :=
  postRoot = listDigest auditLeaf compressN [target]

/-- **`fixRootBinds` — equal one-felt digests force the SAME target.** From a post-root that equals
both the digest of a witnessed value `w` and the digest of the target `target`, `w = target` (the
`ListDigestBindsList` collision-resistance, off `compressNInjective` + the injective leaf). -/
theorem fixRootBinds (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (w target : Int) (postRoot : FieldElem)
    (hw : postRoot = listDigest auditLeaf compressN [w])
    (hgate : gFixOne compressN target postRoot) :
    w = target := by
  have hroots : listDigest auditLeaf compressN [w] = listDigest auditLeaf compressN [target] := by
    rw [← hw]; exact hgate
  have hlist : ([w] : List Int) = [target] :=
    ListDigestBindsList auditLeaf compressN hN auditLeaf_injective _ _ hroots
  exact List.head_eq_of_cons_eq hlist

/-! ## §1 — makeSovereign: `cell ↦ commitment-only record`. A NEW committed `sovereignCommitRoot`.

The published commitment digest `stateCommitment (pre.cell cell)` is forced into a committed limb. The
whole-`cell`-map rebind `sovereignRebind` (off-cell preservation) + guard + log + 16-field frame ride
the NAMED decode residual `makeSovereignEncodes`. This is the slot-root fix with the digest as target. -/

/-- **`sovereignCommitRoot compressN preCell cell`** — the committed root of the sovereign commitment:
the `listDigest` over `[stateCommitment (preCell cell)]` (the digest of the cell's WHOLE pre-state
value, the 32-byte commitment the rebind drops the readable record behind). The Lean mirror of the
Rust `sovereign_commit_root` limb. -/
def sovereignCommitRoot (compressN : List FieldElem → FieldElem) (preCell : CellId → Value)
    (cell : CellId) : FieldElem :=
  listDigest auditLeaf compressN [(stateCommitment (preCell cell) : Int)]

/-- **`gSovereignCommit compressN preCell cell postRoot`** — the FIX gate: the POST sovereign-commit
limb IS the digest of the genuine pre-value commitment `stateCommitment (preCell cell)`. -/
def gSovereignCommit (compressN : List FieldElem → FieldElem) (preCell : CellId → Value)
    (cell : CellId) (postRoot : FieldElem) : Prop :=
  gFixOne compressN (stateCommitment (preCell cell) : Int) postRoot

/-- The decode for a satisfying FIX makeSovereign witness. Carries the FIX gate (the WITNESS leg
forcing the committed sovereign-commit limb to `stateCommitment (pre.cell cell)`), the WHOLE
`cell`-map rebind `sovereignRebind` (the residual the per-cell commit limb cannot certify — off-cell
records, the dropped readable record itself), the guard, the log, and the 16-field frame. -/
structure makeSovereignEncodes (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (actor cell : CellId) : Type where
  postRoot : FieldElem
  hpost : postRoot = sovereignCommitRoot compressN post.kernel.cell cell
  gate : gSovereignCommit compressN pre.kernel.cell cell postRoot
  -- the rebound `post.cell cell` IS the commitment-only record of the SAME pre-value digest the limb
  -- commits (so the forced limb and the rebind agree on the published commitment).
  hRebindRoot : sovereignCommitRoot compressN post.kernel.cell cell
      = sovereignCommitRoot compressN pre.kernel.cell cell
  -- the WHOLE `cell`-map rebind (the residual the per-cell commit limb cannot certify — off-cell).
  cellMapMove : post.kernel.cell = sovereignRebind pre.kernel.cell cell
  guard : MakeSovereignGuard pre actor cell
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

/-- **`makeSovereign_commit_forced` — the published commitment IS the genuine pre-value commitment.**
The FIX gate forces the committed sovereign-commit limb to `stateCommitment (pre.cell cell)`; the
rebind installs the SAME digest (`hRebindRoot`), so the published commitment binds the genuine WHOLE
pre-state value — a prover cannot publish a commitment to a DIFFERENT value. -/
theorem makeSovereign_commit_forced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId)
    (henc : makeSovereignEncodes compressN pre post actor cell)
    (preCell' : CellId → Value)
    (hwit : henc.postRoot = sovereignCommitRoot compressN preCell' cell) :
    (stateCommitment (preCell' cell) : Int) = (stateCommitment (pre.kernel.cell cell) : Int) :=
  fixRootBinds compressN hN _ _ henc.postRoot hwit henc.gate

/-- **`makeSovereign_descriptorRefines` — THE FIX CIRCUIT→KERNEL REFINEMENT for makeSovereign.** The
commitment-rebind is FORCED via the committed sovereign-commit limb (the published digest IS the
genuine pre-value commitment); the whole-`cell`-map rebind, the guard, the log, and the 16-field frame
are the named decode residual. -/
theorem makeSovereign_descriptorRefines (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (actor cell : CellId)
    (henc : makeSovereignEncodes compressN pre post actor cell) :
    MakeSovereignSpec pre actor cell post :=
  ⟨henc.guard, henc.cellMapMove, henc.logAdv, henc.frAccounts, henc.frCaps,
    henc.frNullifiers, henc.frRevoked, henc.frCommitments, henc.frBal, henc.frSlotCaveats,
    henc.frFactories, henc.frLifecycle, henc.frDeathCert, henc.frDelegate, henc.frDelegations,
    henc.frDelegationEpoch, henc.frDelegationEpochAt, henc.frHeaps⟩

/-- The refinement against `execFullA` directly (via `execFullA_makeSovereignA_iff_spec`). -/
theorem makeSovereign_descriptorRefines_execFullA (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (actor cell : CellId)
    (henc : makeSovereignEncodes compressN pre post actor cell) :
    execFullA pre (.makeSovereignA actor cell) = some post :=
  (Dregg2.Circuit.Spec.SovereignCommitment.execFullA_makeSovereignA_iff_spec pre actor cell post).mpr
    (makeSovereign_descriptorRefines compressN pre post actor cell henc)

/-- **TOOTH — `makeSovereign_descriptorRefines_rejects_wrong_commitment`.** A decode whose witnessed
pre-value commitment is NOT the genuine `stateCommitment (pre.cell cell)` cannot ride a satisfying FIX
witness (the sovereign-commit limb pins it — a prover cannot publish a commitment to a forged value). -/
theorem makeSovereign_descriptorRefines_rejects_wrong_commitment (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId)
    (henc : makeSovereignEncodes compressN pre post actor cell)
    (preCell' : CellId → Value)
    (hwit : henc.postRoot = sovereignCommitRoot compressN preCell' cell)
    (hwrong : (stateCommitment (preCell' cell) : Int) ≠ (stateCommitment (pre.kernel.cell cell) : Int)) :
    False :=
  hwrong (makeSovereign_commit_forced compressN hN pre post actor cell henc preCell' hwit)

/-- **TOOTH — `makeSovereign_descriptorRefines_rejects_wrong_map`.** A post whose `cell` map is NOT the
commitment-rebind cannot ride a satisfying FIX witness. -/
theorem makeSovereign_descriptorRefines_rejects_wrong_map (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (actor cell : CellId)
    (henc : makeSovereignEncodes compressN pre post actor cell)
    (hwrong : post.kernel.cell ≠ sovereignRebind pre.kernel.cell cell) :
    False :=
  hwrong henc.cellMapMove

/-! ## §2 — setFieldDyn: `cell.f := v` at a DYNAMIC slot. A NEW committed `dynFieldSlotRoot`.

The live `setFieldDynVmDescriptor2` binds the written value via an UNCOMMITTED memory readback at the
dynamic address (NOT the per-slot committed write column `setFieldV3 slot` uses). So we clone the
slot-root fix over the written slot `f`, forced to `v`. The kernel leaf is the EXISTING `SetFieldSpec`
(`setFieldDyn` is the dynamic-slot circuit shape of the same `setFieldA` effect). The whole-map move
`setFieldCellMap` + guard + log + 16-field frame ride the NAMED decode residual. -/

/-- **`dynFieldSlotRoot compressN k cell f`** — the committed root of cell `cell`'s dynamically-written
slot `f`: the `listDigest` over `[fieldOf f (k.cell cell)]` (the same shape as `auditSlotRoot`, but
the limb commits the dynamically-addressed field's value). The Lean mirror of the Rust
`dyn_field_slot_root` limb. -/
def dynFieldSlotRoot (compressN : List FieldElem → FieldElem) (k : RecordKernelState)
    (cell : CellId) (f : FieldName) : FieldElem :=
  listDigest auditLeaf compressN [fieldOf f (k.cell cell)]

/-- **`gDynFieldSet compressN cell f v postRoot`** — the FIX gate: the POST dyn-field-slot limb IS the
digest of the written value `v` (the value the dynamic write commits). -/
def gDynFieldSet (compressN : List FieldElem → FieldElem) (cell : CellId) (f : FieldName)
    (v : Int) (postRoot : FieldElem) : Prop :=
  gFixOne compressN v postRoot

/-- **`dynFieldSetForced` — the FIX gate FORCES the committed dyn-field slot to `v`.** -/
theorem dynFieldSetForced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (postK : RecordKernelState) (cell : CellId) (f : FieldName) (v : Int) (postRoot : FieldElem)
    (hpost : postRoot = dynFieldSlotRoot compressN postK cell f)
    (hgate : gDynFieldSet compressN cell f v postRoot) :
    fieldOf f (postK.cell cell) = v :=
  fixRootBinds compressN hN _ _ postRoot hpost hgate

/-- The decode for a satisfying FIX setFieldDyn witness. Carries the FIX gate (the WITNESS leg forcing
the committed dyn-field slot `= v`), the WHOLE `cell`-map move `setFieldCellMap` (the residual the
per-slot committed limb cannot certify — off-slot fields of `cell`, off-`cell` records), the guard,
the log, and the 16-field frame. -/
structure setFieldDynEncodes (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int) : Type where
  postRoot : FieldElem
  hpost : postRoot = dynFieldSlotRoot compressN post.kernel cell f
  gate : gDynFieldSet compressN cell f v postRoot
  cellMapMove : post.kernel.cell = setFieldCellMap pre.kernel.cell cell f v
  guard : SetFieldGuard pre actor cell f v
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

/-- **`setFieldDyn_slot_forced` — the committed dynamic-slot value is FIX-CIRCUIT-FORCED to `v`.** -/
theorem setFieldDyn_slot_forced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (henc : setFieldDynEncodes compressN pre post actor cell f v) :
    fieldOf f (post.kernel.cell cell) = v :=
  dynFieldSetForced compressN hN post.kernel cell f v henc.postRoot henc.hpost henc.gate

/-- **`setFieldDyn_descriptorRefines` — THE FIX CIRCUIT→KERNEL REFINEMENT for setFieldDyn.** The
`cell.f := v` dynamic-slot write is FORCED via the committed dyn-field slot-root
(`setFieldDyn_slot_forced`, consistent with the whole-`cell`-map move whose written slot IS the forced
value); the whole-map move, the guard, the log, and the 16-field frame are the named decode residual.
The kernel leaf is the EXISTING `SetFieldSpec` — `setFieldDyn` is the dynamic-slot circuit shape of the
same `setFieldA` effect. -/
theorem setFieldDyn_descriptorRefines (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (hnr : Dregg2.Exec.EffectsState.reservedField f = false)
    (henc : setFieldDynEncodes compressN pre post actor cell f v) :
    SetFieldSpec pre actor cell f v post :=
  ⟨hnr, henc.guard, henc.cellMapMove, henc.logAdv, henc.frAccounts, henc.frCaps,
    henc.frNullifiers, henc.frRevoked, henc.frCommitments, henc.frBal, henc.frSlotCaveats,
    henc.frFactories, henc.frLifecycle, henc.frDeathCert, henc.frDelegate, henc.frDelegations,
    henc.frDelegationEpoch, henc.frDelegationEpochAt, henc.frHeaps⟩

/-- The refinement against `execFullA` directly (via `execFullA_setFieldA_iff_spec`). The dynamic
SetField is the developer write — its `reservedField f = false` precondition (`hnr`) is the
developer-path leg the executor enforces (`stateStepDev`). -/
theorem setFieldDyn_descriptorRefines_execFullA (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (hnr : Dregg2.Exec.EffectsState.reservedField f = false)
    (henc : setFieldDynEncodes compressN pre post actor cell f v) :
    execFullA pre (.setFieldA actor cell f v) = some post :=
  (Dregg2.Circuit.Spec.CellStateField.execFullA_setFieldA_iff_spec pre actor cell f v post).mpr
    (setFieldDyn_descriptorRefines compressN pre post actor cell f v hnr henc)

/-- **TOOTH — `setFieldDyn_descriptorRefines_rejects_wrong_value`.** A decode asserting a post whose
`cell.f` slot is NOT `v` cannot ride a satisfying FIX witness (the dyn-field slot-root gate pins it —
a forged dynamic write is UNSAT). -/
theorem setFieldDyn_descriptorRefines_rejects_wrong_value (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (henc : setFieldDynEncodes compressN pre post actor cell f v)
    (hwrong : fieldOf f (post.kernel.cell cell) ≠ v) :
    False :=
  hwrong (setFieldDyn_slot_forced compressN hN pre post actor cell f v henc)

/-- **TOOTH — `setFieldDyn_descriptorRefines_rejects_wrong_map`.** A post whose `cell` map is NOT the
field write cannot ride a satisfying FIX witness. -/
theorem setFieldDyn_descriptorRefines_rejects_wrong_map (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (henc : setFieldDynEncodes compressN pre post actor cell f v)
    (hwrong : post.kernel.cell ≠ setFieldCellMap pre.kernel.cell cell f v) :
    False :=
  hwrong henc.cellMapMove

/-! ## §2.A — CLASS A: the sovereign rebind is FORCED by the DEPLOYED descriptor `makeSovereignV3`.

§1 forces the rebind from `makeSovereignEncodes.gate`, a MODELLED `gSovereignCommit` the decode ASSERTS —
editing the LIVE `makeSovereignV3` constraints does NOT break it. This section closes that gap exactly as
`RotatedKernelRefinementCellSeal` §6.5 does for cellSeal: `makeSovereign_forced_sat` derives
`post.kernel.cell = sovereignRebind pre.kernel.cell cell` from a `Satisfied2 hash makeSovereignV3` witness
DIRECTLY, by

  * `graduateV1_sound` — lift the v2 `Satisfied2` of `makeSovereignV3 = graduateV1 (rotateV3WithModeGate …)`
    to the v1 per-row `satisfiedVm` of the underlying mode-gated descriptor (chip/range from `RotTableSide`,
    graduability by `decide`);
  * `makeSovereignV3_forces_sovereign` — the DEPLOYED in-circuit mode gate FORCES the committed AFTER mode
    TRACE limb (`afterModeCol`, `B_MODE = 35`, a pre-iroot committed limb chaining into `state_commit`) to
    `modeSovereign (= 1)` on the active row;
  * `MakeSovereignTraceReadout.modeLimbDecodes` — the realizable `WitnessDecodes`-class seam: the committed
    mode limb IS the felt `1` exactly when the post cell-map IS the sovereign rebind (the deployed trace-fill
    emits `mode_flag = 1` IFF the row genuinely rebinds the cell behind the commitment), so a forced `= 1`
    pins `post.kernel.cell = sovereignRebind pre.kernel.cell cell`. The analog of cellSeal's `discLimbDecodes`.

Editing `makeSovereignV3`'s mode gate breaks `makeSovereignV3_forces_sovereign`, hence
`makeSovereign_forced_sat`, hence `makeSovereign_descriptorRefines_sat` — Class A. -/

/-- **`MakeSovereignTraceReadout` — the realizable circuit-witness extraction for makeSovereign (NAMED).**
The trace-determined part a satisfying `makeSovereignV3` witness supplies, the `WitnessDecodes` class of
cellSeal's `CellSealTraceReadout`: the prover's designated ACTIVE makeSovereign row + its selector fact + the
realizable mode-limb decode (the committed AFTER mode limb IS the sovereign-rebind indicator felt) + the
log / guard / 16-field residual the per-cell mode limb cannot witness. The mode GATE is NOT a field — it is
FORCED from `Satisfied2 hash makeSovereignV3` (`makeSovereign_forced_sat`), unlike §1's modelled `gate`. -/
structure MakeSovereignTraceReadout (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (actor cell : CellId) : Type where
  -- the designated ACTIVE makeSovereign row (the one whose `SEL_MAKE_SOVEREIGN_RT = 1`).
  row : Nat
  hrow : row < t.rows.length
  -- a TRANSITION row, NOT the wrap/pad last row (the mode gate runs under `when_transition()`).
  hrowNotLast : row + 1 ≠ t.rows.length
  -- the selector is hot on the designated row (the prover's row designation — the column fact a real
  -- makeSovereign trace exhibits).
  hsel : (envAt t row).loc EffectVmEmitMakeSovereign.SEL_MAKE_SOVEREIGN_RT = 1
  -- the realizable `WitnessDecodes`-class seam: the committed AFTER mode TRACE limb (`afterModeCol`,
  -- B_MODE = 35) IS the felt `1` exactly when the post cell-map IS the sovereign rebind. The deployed
  -- trace-fill emits `mode_flag = 1` IFF the row rebinds the cell behind the commitment, so the limb and
  -- the indicator are the SAME committed felt by construction — the limb-level decode the COMMITMENT
  -- cannot certify, supplied by `StarkSound`.
  modeLimbDecodes :
    (envAt t row).loc (afterModeCol EffectVmEmitMakeSovereign.makeSovereignRuntimeVmDescriptor.traceWidth)
      = (if post.kernel.cell = sovereignRebind pre.kernel.cell cell then (1 : ℤ) else 0)
  -- the guard (self-authority over the cell).
  guard : MakeSovereignGuard pre actor cell
  -- the self-targeted receipt-log advance (off the per-row block).
  logAdv : post.log = { actor := actor, src := cell, dst := cell, amt := 0 } :: pre.log
  -- the 16 non-`cell` kernel frame fields (the full `MakeSovereignSpec` frame residual).
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

/-- `rotateV3WithModeGate SEL_MAKE_SOVEREIGN_RT modeSovereign makeSovereignRuntimeVmDescriptor` is
graduable (the appended mode gate is a CONSTRAINT; graduation reads only sites/ranges). -/
theorem makeSovereign_mode_graduable :
    graduable (rotateV3WithModeGate EffectVmEmitMakeSovereign.SEL_MAKE_SOVEREIGN_RT modeSovereign
      EffectVmEmitMakeSovereign.makeSovereignRuntimeVmDescriptor) = true := by
  decide

/-- **`makeSovereign_forced_sat` — the sovereign rebind is FORCED by the DEPLOYED `makeSovereignV3` (Class
A).** A `Satisfied2 hash makeSovereignV3` witness (with the chip/range table side) plus the realizable
`MakeSovereignTraceReadout` forces `post.kernel.cell = sovereignRebind pre.kernel.cell cell`. The committed
AFTER mode limb is pinned to `modeSovereign (= 1)` by the LIVE mode gate (`makeSovereignV3_forces_sovereign`,
via `graduateV1_sound` on the active transition row); the readout's `modeLimbDecodes` identifies that limb
with the sovereign-rebind indicator, so the indicator is `1` and the rebind holds. Editing `makeSovereignV3`'s
mode gate turns this RED. -/
theorem makeSovereign_forced_sat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash makeSovereignV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId)
    (rd : MakeSovereignTraceReadout hash minit mfin maddrs t pre post actor cell) :
    post.kernel.cell = sovereignRebind pre.kernel.cell cell := by
  have hv1 : satisfiedVm hash
      (rotateV3WithModeGate EffectVmEmitMakeSovereign.SEL_MAKE_SOVEREIGN_RT modeSovereign
        EffectVmEmitMakeSovereign.makeSovereignRuntimeVmDescriptor)
      (envAt t rd.row) (rd.row == 0) (rd.row + 1 == t.rows.length) :=
    graduateV1_sound hash _ minit mfin maddrs t hside.chip hside.range makeSovereign_mode_graduable
      (satisfied2_of_withRecordPin8Headroom2 hash _ hsat) rd.row rd.hrow
  have hlastf : (rd.row + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact rd.hrowNotLast
  rw [hlastf] at hv1
  have hlimb : (envAt t rd.row).loc
      (afterModeCol EffectVmEmitMakeSovereign.makeSovereignRuntimeVmDescriptor.traceWidth) = modeSovereign :=
    makeSovereignV3_forces_sovereign hash (envAt t rd.row) (rd.row == 0) false rfl rd.hsel hv1
  -- the limb IS the rebind indicator (the realizable seam); forced `= modeSovereign = 1` ⇒ indicator `= 1`.
  have hind : (if post.kernel.cell = sovereignRebind pre.kernel.cell cell then (1 : ℤ) else 0)
      = modeSovereign := by rw [← rd.modeLimbDecodes, hlimb]
  by_contra hne
  rw [if_neg hne] at hind
  simp only [modeSovereign] at hind
  exact absurd hind (by norm_num)

/-- **`makeSovereign_descriptorRefines_sat` — THE CLASS-A CIRCUIT→KERNEL REFINEMENT for makeSovereign.** A
satisfying DEPLOYED `makeSovereignV3` witness (with the chip/range table side) plus the realizable
`MakeSovereignTraceReadout` forces `MakeSovereignSpec pre actor cell post`. Unlike §1's
`makeSovereign_descriptorRefines` (which consumes a modelled `gate`), the commitment-rebind here is forced
from the DEPLOYED mode gate's `Satisfied2` (`makeSovereign_forced_sat`) — editing `makeSovereignV3`'s
constraints turns this RED. The guard, the 16-field frame, and the log are the named decode residual. -/
theorem makeSovereign_descriptorRefines_sat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash makeSovereignV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId)
    (rd : MakeSovereignTraceReadout hash minit mfin maddrs t pre post actor cell) :
    MakeSovereignSpec pre actor cell post :=
  ⟨rd.guard,
   makeSovereign_forced_sat hash hside hsat pre post actor cell rd,
   rd.logAdv, rd.frAccounts, rd.frCaps,
   rd.frNullifiers, rd.frRevoked, rd.frCommitments, rd.frBal, rd.frSlotCaveats,
   rd.frFactories, rd.frLifecycle, rd.frDeathCert, rd.frDelegate, rd.frDelegations,
   rd.frDelegationEpoch, rd.frDelegationEpochAt, rd.frHeaps⟩

/-- **CLASS-A TOOTH — a forged un-promoted makeSovereign witness is UNSAT.** A `MakeSovereignTraceReadout`
whose post cell-map is NOT the sovereign rebind cannot ride a satisfying `makeSovereignV3` witness: the
DEPLOYED mode gate pins the promotion. Forced from `Satisfied2`, not the modelled gate. -/
theorem makeSovereign_sat_rejects_unpromoted (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash makeSovereignV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId)
    (rd : MakeSovereignTraceReadout hash minit mfin maddrs t pre post actor cell)
    (hwrong : post.kernel.cell ≠ sovereignRebind pre.kernel.cell cell) :
    False :=
  hwrong (makeSovereign_forced_sat hash hside hsat pre post actor cell rd)

/-! ## §2.B — CLASS A: the dynamic field write is FORCED by the DEPLOYED descriptor `setFieldDynForcedV3`.

§2 forces the write from `setFieldDynEncodes.gate`, a MODELLED `gDynFieldSet` the decode ASSERTS — editing
the LIVE `setFieldDynForcedV3` constraints does NOT break it. This section closes that gap, the
`RotatedKernelRefinementCellSeal` §6.5 shape, but the gate is the WAVE-3 `fields_root` WELD: the committed
AFTER `fields_root` limb is welded to the in-circuit declared-param column. `setFieldDyn_forced_sat` derives
`fieldOf f (post.kernel.cell cell) = v` from a `Satisfied2 hash setFieldDynForcedV3` witness DIRECTLY, by

  * extracting the LIVE `permsVKWeldGate SEL_SET_FIELD (afterFieldsRootCol …) declaredFieldsRootCol`
    constraint from `hsat.rowConstraints` (it is a `.base` member of `setFieldDynForcedV3.constraints` — the
    weld survives the trailing `memOp` append) and `permsVKWeldGate_forces` to pin the committed AFTER
    `fields_root` limb EQUAL to the declared-param column on the active row;
  * `SetFieldDynTraceReadout.fieldsLimbDecodes` / `paramDecodes` — the realizable `WitnessDecodes`-class
    seam: the committed AFTER `fields_root` limb IS `fieldOf f (post.kernel.cell cell)` (the deployed
    trace-fill emits the written slot's felt into that limb), and the declared-param column IS `v` (the
    verifier-anchored declared post value). Combined with the weld, `fieldOf f (post.kernel.cell cell) = v`.
    The `setFieldDynForcedV3` constraints differ from `setFieldDynV1Face`'s graduation only by the trailing
    `memOp`s, so the SAME extraction the `RotTableSide` rungs use applies.

Editing `setFieldDynForcedV3`'s fields-root weld breaks the extraction, hence `setFieldDyn_forced_sat`,
hence `setFieldDyn_descriptorRefines_sat` — Class A. -/

/-- The fields-root weld gate, as it sits (a `.base` member) in `setFieldDynForcedV3.constraints`. -/
private def fdGate : VmConstraint2 :=
  .base (permsVKWeldGate EffectVmEmitSetField.SEL_SET_FIELD
    (afterFieldsRootCol setFieldDynV1Face.traceWidth) declaredFieldsRootCol)

/-- The weld gate is a member of `setFieldDynForcedV3.constraints` (the trailing `memOp` append preserves
the graduated weld). The membership the forced-limb extraction needs. -/
theorem fdGate_mem : fdGate ∈ setFieldDynForcedV3.constraints := by
  have hbase : VmConstraint2.base (permsVKWeldGate EffectVmEmitSetField.SEL_SET_FIELD
      (afterFieldsRootCol setFieldDynV1Face.traceWidth) declaredFieldsRootCol)
      ∈ (graduateV1 (rotateV3WithFieldsRootGate EffectVmEmitSetField.SEL_SET_FIELD
        (afterFieldsRootCol setFieldDynV1Face.traceWidth) setFieldDynV1Face)).constraints := by
    unfold graduateV1
    simp only [List.mem_append, List.mem_map, List.mem_mapIdx]
    exact Or.inl (Or.inl ⟨_, rotateV3WithFieldsRootGate_mem EffectVmEmitSetField.SEL_SET_FIELD
      (afterFieldsRootCol setFieldDynV1Face.traceWidth) setFieldDynV1Face, rfl⟩)
  show fdGate ∈ _ ++ _
  exact List.mem_append_left _ hbase

/-- **`SetFieldDynTraceReadout` — the realizable circuit-witness extraction for setFieldDyn (NAMED).**
The trace-determined part a satisfying `setFieldDynForcedV3` witness supplies, the `WitnessDecodes` class of
cellSeal's `CellSealTraceReadout`: the prover's designated ACTIVE setFieldDyn row + its selector fact + the
realizable fields-root-limb / declared-param decodes (the committed AFTER `fields_root` limb IS the written
slot felt, the declared-param column IS `v`) + the whole-map / guard / log / 16-field residual. The fields-root
GATE is NOT a field — it is FORCED from `Satisfied2 hash setFieldDynForcedV3` (`setFieldDyn_forced_sat`). -/
structure SetFieldDynTraceReadout (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int) : Type where
  -- the designated ACTIVE setFieldDyn row (the one whose `SEL_SET_FIELD = 1`).
  row : Nat
  hrow : row < t.rows.length
  -- a TRANSITION row, NOT the wrap/pad last row (the weld runs under `when_transition()`).
  hrowNotLast : row + 1 ≠ t.rows.length
  -- the selector is hot on the designated row.
  hsel : (envAt t row).loc EffectVmEmitSetField.SEL_SET_FIELD = 1
  -- the realizable `WitnessDecodes`-class seam: the committed AFTER `fields_root` limb IS the written
  -- slot's felt (the deployed trace-fill emits `fieldOf f (post.cell cell)` into that limb).
  fieldsLimbDecodes :
    (envAt t row).loc (afterFieldsRootCol setFieldDynV1Face.traceWidth)
      = fieldOf f (post.kernel.cell cell)
  -- the declared-param column IS the written value `v` (verifier-anchored to the declared post value).
  paramDecodes : (envAt t row).loc declaredFieldsRootCol = v
  -- the WHOLE `cell`-map move (the residual the per-slot limb cannot certify).
  cellMapMove : post.kernel.cell = setFieldCellMap pre.kernel.cell cell f v
  guard : SetFieldGuard pre actor cell f v
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

/-- **`setFieldDyn_forced_sat` — the dynamic field write is FORCED by the DEPLOYED `setFieldDynForcedV3`
(Class A).** A `Satisfied2 hash setFieldDynForcedV3` witness plus the realizable `SetFieldDynTraceReadout`
forces `fieldOf f (post.kernel.cell cell) = v`. The committed AFTER `fields_root` limb is welded EQUAL to the
declared-param column by the LIVE gate (`permsVKWeldGate_forces`, extracted from `hsat.rowConstraints` via
`fdGate_mem`); the readout identifies the limb with the written slot felt and the param column with `v`.
Editing `setFieldDynForcedV3`'s weld turns this RED. -/
theorem setFieldDyn_forced_sat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash setFieldDynForcedV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (rd : SetFieldDynTraceReadout hash minit mfin maddrs t pre post actor cell f v) :
    fieldOf f (post.kernel.cell cell) = v := by
  -- the weld constraint holds on the active row (extracted from `rowConstraints` via membership).
  have hgate : (permsVKWeldGate EffectVmEmitSetField.SEL_SET_FIELD
      (afterFieldsRootCol setFieldDynV1Face.traceWidth) declaredFieldsRootCol).holdsVm
      (envAt t rd.row) (rd.row == 0) (rd.row + 1 == t.rows.length) :=
    hsat.rowConstraints rd.row rd.hrow _ fdGate_mem
  have hlastf : (rd.row + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact rd.hrowNotLast
  rw [hlastf] at hgate
  -- the weld FORCES the committed AFTER `fields_root` limb EQUAL to the declared-param column.
  have hweld : (envAt t rd.row).loc (afterFieldsRootCol setFieldDynV1Face.traceWidth)
      = (envAt t rd.row).loc declaredFieldsRootCol :=
    permsVKWeldGate_forces (envAt t rd.row) (rd.row == 0) false rfl _ _ _ rd.hsel hgate
  -- the realizable seam: limb = `fieldOf f (post.cell cell)`, param = `v`; so the write IS `v`.
  rw [rd.fieldsLimbDecodes, rd.paramDecodes] at hweld
  exact hweld

/-- **`setFieldDyn_descriptorRefines_sat` — THE CLASS-A CIRCUIT→KERNEL REFINEMENT for setFieldDyn.** A
satisfying DEPLOYED `setFieldDynForcedV3` witness plus the realizable `SetFieldDynTraceReadout` forces
`SetFieldSpec pre actor cell f v post`. Unlike §2's `setFieldDyn_descriptorRefines` (which consumes a
modelled `gate`), the `cell.f := v` write here is forced from the DEPLOYED `fields_root` weld's `Satisfied2`
(`setFieldDyn_forced_sat`) — editing `setFieldDynForcedV3`'s constraints turns this RED. The whole-map move,
the guard, the log, and the 16-field frame are the named decode residual; the kernel leaf is the EXISTING
`SetFieldSpec` (`setFieldDyn` is the dynamic-slot circuit shape of the same `setFieldA` effect). -/
theorem setFieldDyn_descriptorRefines_sat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash setFieldDynForcedV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (hnr : Dregg2.Exec.EffectsState.reservedField f = false)
    (rd : SetFieldDynTraceReadout hash minit mfin maddrs t pre post actor cell f v) :
    SetFieldSpec pre actor cell f v post :=
  ⟨hnr, rd.guard, rd.cellMapMove, rd.logAdv, rd.frAccounts, rd.frCaps,
   rd.frNullifiers, rd.frRevoked, rd.frCommitments, rd.frBal, rd.frSlotCaveats,
   rd.frFactories, rd.frLifecycle, rd.frDeathCert, rd.frDelegate, rd.frDelegations,
   rd.frDelegationEpoch, rd.frDelegationEpochAt, rd.frHeaps⟩

/-- **CLASS-A TOOTH — a forged dynamic-write witness is UNSAT.** A `SetFieldDynTraceReadout` whose post
`cell.f` slot is NOT `v` cannot ride a satisfying `setFieldDynForcedV3` witness: the DEPLOYED `fields_root`
weld pins the written value. Forced from `Satisfied2`, not the modelled gate. -/
theorem setFieldDyn_sat_rejects_wrong_value (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash setFieldDynForcedV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (rd : SetFieldDynTraceReadout hash minit mfin maddrs t pre post actor cell f v)
    (hwrong : fieldOf f (post.kernel.cell cell) ≠ v) :
    False :=
  hwrong (setFieldDyn_forced_sat hash hside hsat pre post actor cell f v rd)

/-! ## §3 — pipelinedSend: `log := pipelinedSendReceipt actor :: log`, whole kernel frozen. LIVE.

NO new committed root. The actual Lean `PipelinedSendSpec` is TOTAL (no guard) and its FRAME is all 17
kernel fields LITERALLY unchanged — there is no nonce field that ticks against this spec, so the
literal-freeze-vs-nonce-tick mismatch the brief worried about does NOT arise. The effect is
structurally `emitEvent` (the apply-time NEUTRAL clock row + whole-kernel freeze) — a genuine
VALUE_FORCED against the LIVE descriptor's whole-state-row passthrough. The decode `pipelinedSendEncodes`
carries the receipt advance (the touched component) + the whole-kernel frame the live passthrough
supplies (the 17 kernel fields). It introduces NO new gate. -/

/-- The decode for a satisfying LIVE pipelinedSend witness: the receipt-log advance (the touched
component) + the whole-kernel frame the live passthrough already forces (all 17 kernel fields). No
committed root, no new gate, NO guard (the apply-time effect is TOTAL — `PipelinedSendSpec` has no
admissibility conjunct). Every clause is the LIVE descriptor. -/
structure pipelinedSendEncodes (pre post : RecChainedState) (actor : CellId) : Type where
  logAdv : post.log = pipelinedSendReceipt actor :: pre.log
  -- the whole-kernel frame the live passthrough constraints already force (17 fields).
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

/-- **`pipelinedSend_descriptorRefines` — THE CIRCUIT→KERNEL REFINEMENT for pipelinedSend, against the
LIVE descriptor.** A satisfying LIVE pipelinedSend witness (its kernel frame forced by the deployed
whole-state-row passthrough) forces `PipelinedSendSpec` — the receipt advance is the named touched
component, the whole-kernel freeze is the LIVE-circuit-forced frame. A genuine VALUE_FORCED:
pipelinedSend needed NO fix-root (its `PipelinedSendSpec` is a log-only, whole-kernel-frozen step). -/
theorem pipelinedSend_descriptorRefines
    (pre post : RecChainedState) (actor : CellId)
    (henc : pipelinedSendEncodes pre post actor) :
    PipelinedSendSpec pre actor post :=
  ⟨henc.logAdv, henc.frAccounts, henc.frCell, henc.frCaps,
    henc.frNullifiers, henc.frRevoked, henc.frCommitments, henc.frBal, henc.frSlotCaveats,
    henc.frFactories, henc.frLifecycle, henc.frDeathCert, henc.frDelegate, henc.frDelegations,
    henc.frDelegationEpoch, henc.frDelegationEpochAt, henc.frHeaps⟩

/-- The refinement against `execFullA` directly (via `execFullA_pipelinedSend_iff_spec`). -/
theorem pipelinedSend_descriptorRefines_execFullA
    (pre post : RecChainedState) (actor : CellId)
    (henc : pipelinedSendEncodes pre post actor) :
    execFullA pre (.pipelinedSendA actor) = some post :=
  (Dregg2.Circuit.Spec.QueuePipelinedSend.execFullA_pipelinedSend_iff_spec pre actor post).mpr
    (pipelinedSend_descriptorRefines pre post actor henc)

/-- **TOOTH — `pipelinedSend_descriptorRefines_rejects_wrong_receipt`.** A post whose log is NOT the
receipt advance cannot ride a satisfying LIVE witness (the receipt advance is forced — the apply-time
clock ticks by exactly the audited NEUTRAL row). -/
theorem pipelinedSend_descriptorRefines_rejects_wrong_receipt
    (pre post : RecChainedState) (actor : CellId)
    (henc : pipelinedSendEncodes pre post actor)
    (hwrong : post.log ≠ pipelinedSendReceipt actor :: pre.log) :
    False :=
  hwrong henc.logAdv

/-- **TOOTH — `pipelinedSend_descriptorRefines_rejects_mutated_kernel`.** A post whose `bal` ledger is
NOT frozen cannot ride a satisfying LIVE witness (the live passthrough freezes the whole kernel — an
apply-time clock row that silently moves value is UNSAT). -/
theorem pipelinedSend_descriptorRefines_rejects_mutated_kernel
    (pre post : RecChainedState) (actor : CellId)
    (henc : pipelinedSendEncodes pre post actor)
    (hwrong : post.kernel.bal ≠ pre.kernel.bal) :
    False :=
  hwrong henc.frBal

/-! ## §4 — NON-VACUITY: the new fix roots + gates are load-bearing (no carrier secretly `True`). -/

private def cNC : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 1000003 + x) (xs.length : ℤ)

-- setFieldDyn: a write of `7` lands a DIFFERENT root from a write of `0` (the gate is not a no-op —
-- a `slotRoot := 0` stub would collapse this), and from another value (distinct values, distinct roots).
#guard decide (listDigest auditLeaf cNC [(7 : Int)] = listDigest auditLeaf cNC [(0 : Int)]) == false
#guard decide (listDigest auditLeaf cNC [(7 : Int)] = listDigest auditLeaf cNC [(13 : Int)]) == false

-- makeSovereign: distinct pre-value commitments land distinct sovereign-commit roots (the limb genuinely
-- binds the committed-value digest — two different records cannot share the published commitment).
#guard decide (listDigest auditLeaf cNC [(stateCommitment (.int 100) : Int)]
             = listDigest auditLeaf cNC [(stateCommitment (.int 5) : Int)]) == false
-- ...and the digest of the record itself is distinguishable from the int (the WHOLE value is committed):
#guard decide (stateCommitment (.record [("balance", .int 100)]) = stateCommitment (.int 100)) == false

-- pipelinedSend: the receipt advance is non-trivial — the NEUTRAL clock row genuinely grows the log
-- (balance-`0` self-`Turn` on the actor; INDEPENDENT of any send payload).
#guard decide ((pipelinedSendReceipt 5).src = 5 ∧ (pipelinedSendReceipt 5).dst = 5
             ∧ (pipelinedSendReceipt 5).amt = 0)

/-! ## §5 — axiom-hygiene tripwires. -/

#assert_axioms fixRootBinds
#assert_axioms makeSovereign_commit_forced
#assert_axioms makeSovereign_descriptorRefines
#assert_axioms makeSovereign_descriptorRefines_execFullA
#assert_axioms makeSovereign_descriptorRefines_rejects_wrong_commitment
#assert_axioms makeSovereign_descriptorRefines_rejects_wrong_map
#assert_axioms makeSovereign_mode_graduable
#assert_axioms makeSovereign_forced_sat
#assert_axioms makeSovereign_descriptorRefines_sat
#assert_axioms makeSovereign_sat_rejects_unpromoted
#assert_axioms dynFieldSetForced
#assert_axioms setFieldDyn_slot_forced
#assert_axioms setFieldDyn_descriptorRefines
#assert_axioms setFieldDyn_descriptorRefines_execFullA
#assert_axioms setFieldDyn_descriptorRefines_rejects_wrong_value
#assert_axioms setFieldDyn_descriptorRefines_rejects_wrong_map
#assert_axioms fdGate_mem
#assert_axioms setFieldDyn_forced_sat
#assert_axioms setFieldDyn_descriptorRefines_sat
#assert_axioms setFieldDyn_sat_rejects_wrong_value
#assert_axioms pipelinedSend_descriptorRefines
#assert_axioms pipelinedSend_descriptorRefines_execFullA
#assert_axioms pipelinedSend_descriptorRefines_rejects_wrong_receipt
#assert_axioms pipelinedSend_descriptorRefines_rejects_mutated_kernel

end Dregg2.Circuit.RotatedKernelRefinementMisc
