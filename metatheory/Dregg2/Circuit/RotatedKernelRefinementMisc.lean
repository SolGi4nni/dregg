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
effects; `pipelinedSend` carries NO crypto carrier (pure live-descriptor). No `sorry`, no `:= True`,
no `native_decide`, no fresh axiom. NEW file; all imports read-only.
-/
import Dregg2.Circuit.RotatedKernelRefinementPermsVK
import Dregg2.Circuit.Spec.cellstatefield
import Dregg2.Circuit.Spec.sovereigncommitment
import Dregg2.Circuit.Spec.queuepipelinedsend

namespace Dregg2.Circuit.RotatedKernelRefinementMisc

open Dregg2.Circuit
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
open Dregg2.Exec
open Dregg2.Exec.EffectsState (fieldOf)
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false
set_option linter.unusedVariables false

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
    (henc : setFieldDynEncodes compressN pre post actor cell f v) :
    SetFieldSpec pre actor cell f v post :=
  ⟨henc.guard, henc.cellMapMove, henc.logAdv, henc.frAccounts, henc.frCaps,
    henc.frNullifiers, henc.frRevoked, henc.frCommitments, henc.frBal, henc.frSlotCaveats,
    henc.frFactories, henc.frLifecycle, henc.frDeathCert, henc.frDelegate, henc.frDelegations,
    henc.frDelegationEpoch, henc.frDelegationEpochAt, henc.frHeaps⟩

/-- The refinement against `execFullA` directly (via `execFullA_setFieldA_iff_spec`). -/
theorem setFieldDyn_descriptorRefines_execFullA (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (henc : setFieldDynEncodes compressN pre post actor cell f v) :
    execFullA pre (.setFieldA actor cell f v) = some post :=
  (Dregg2.Circuit.Spec.CellStateField.execFullA_setFieldA_iff_spec pre actor cell f v post).mpr
    (setFieldDyn_descriptorRefines compressN pre post actor cell f v henc)

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
#assert_axioms dynFieldSetForced
#assert_axioms setFieldDyn_slot_forced
#assert_axioms setFieldDyn_descriptorRefines
#assert_axioms setFieldDyn_descriptorRefines_execFullA
#assert_axioms setFieldDyn_descriptorRefines_rejects_wrong_value
#assert_axioms setFieldDyn_descriptorRefines_rejects_wrong_map
#assert_axioms pipelinedSend_descriptorRefines
#assert_axioms pipelinedSend_descriptorRefines_execFullA
#assert_axioms pipelinedSend_descriptorRefines_rejects_wrong_receipt
#assert_axioms pipelinedSend_descriptorRefines_rejects_mutated_kernel

end Dregg2.Circuit.RotatedKernelRefinementMisc
