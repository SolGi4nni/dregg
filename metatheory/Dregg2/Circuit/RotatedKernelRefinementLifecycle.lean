/-
# Dregg2.Circuit.RotatedKernelRefinementLifecycle — the PRINCIPLED-FIX VALUE-leg circuit→kernel
  refinements for FOUR more VALUE_MISSING effects, fanning out the `cellSeal` template
  (`RotatedKernelRefinementCellSeal`):

  * **cellUnseal**  — `lifecycle[cell] := Live`  (the INVERSE of cellSeal; REUSES `lifecycleRoot`).
  * **cellDestroy** — `lifecycle[cell] := Destroyed` AND `deathCert[cell] := certHash` (TWO committed
    roots: `lifecycleRoot` reused + a NEW `deathCertRoot` limb).
  * **refusal**       — `cell.cell[cell]."refusal"  := 1`  (an audit RECORD slot; a NEW `auditSlotRoot`).
  * **receiptArchive**— `cell.cell[cell]."lifecycle":= 1`  (an audit RECORD slot; reuses `auditSlotRoot`).

## The gap each closes (same shape as cellSeal's genuinely-FALSE VALUE rung)

`cellSeal` was the FIRST VALUE_MISSING effect: its kernel write is `lifecycle := lifecycle[cell ↦ Sealed]`,
a kernel-owned SIDE-TABLE the deployed per-cell commitment `hash(bal_lo,bal_hi,nonce,fields[0..7],cap_root)`
binds NO column for. These four are the SAME class:

  * cellUnseal / cellDestroy(lifecycle leg) — the SAME `lifecycle` side-table cellSeal touches, written to
    `lcLive` / `lcDestroyed` instead of `lcSealed`. REUSE `lifecycleRoot` directly.
  * cellDestroy(deathCert leg) — a SECOND side-table `deathCert : CellId → Nat`. A SECOND committed limb
    `deathCertRoot`, cloned from `lifecycleRoot`.
  * refusal / receiptArchive — write a RECORD SLOT (`fieldOf f (cell.cell c)`), NOT a side-table. The
    deployed commitment binds the `fields[0..7]` block but the audit slots `"refusal"`/`"lifecycle"` are
    extra named slots the per-cell column does not pin. A NEW committed limb `auditSlotRoot` over the
    touched slot value, forced to `1`.

Each FIX adds a dedicated committed root limb (the SAME `ListCommit.listDigest` + `compressNInjective`
Poseidon-CR carrier the system_roots limbs use — NEVER a fresh axiom, NEVER `N_SYSTEM_ROOTS`+1), a gate
forcing the post root to the written value, and discharges the VALUE rung against it. ADDITIVE: nothing
in `recStateCommit`/`cellCommit`/`SystemRoots`/the existing descriptors/the reading modules is mutated.

## The shared Rust realization (ONE cutover for all four + cellSeal)

The five lifecycle/audit fixes share ONE realization: `cell_state.rs::compute_commitment` absorbs THREE
extra committed limbs — `lifecycle_root`, `death_cert_root`, `audit_slot_root` — the trace-fill emits
them from the kernel side-tables / audit slots, and ONE VK epoch rotation publishes the new commitment
shape (it changes once, covering cellSeal + all four here).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} + the realizable Poseidon-CR carriers
(`compressNInjective` + the injective leaf encoders, REUSED from cellSeal where possible). No `sorry`,
no `:= True`, no `native_decide`, no fresh axiom. NEW file; all imports read-only.
-/
import Dregg2.Circuit.RotatedKernelRefinementCellSeal
import Dregg2.Circuit.Spec.cellstateaudit

namespace Dregg2.Circuit.RotatedKernelRefinementLifecycle

open Dregg2.Circuit
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.StateCommit (compressNInjective)
open Dregg2.Circuit.RotatedKernelRefinementCellSeal
  (lifecycleLeaf lifecycleLeaf_injective lifecycleRoot lifecycleRoot_binds)
open Dregg2.Circuit.Spec.CellLifecycle
  (CellUnsealSpec CellUnsealGuard unsealLifecycleMap
   CellDestroySpec CellDestroyGuard destroyKernelMap destroyDeathCertMap
   cellLifecycleReceipt)
open Dregg2.Circuit.Spec.CellStateAudit
  (RefusalSpec ReceiptArchiveSpec auditGuard auditCellMap)
open Dregg2.Circuit.DescriptorIR2 (VmTrace Satisfied2 envAt)
open Dregg2.Circuit.Emit.EffectVmEmit (satisfiedVm VmRowEnv VmConstraint)
open Dregg2.Circuit.Emit.EffectVmEmitV2 (graduateV1 graduateV1_sound graduable)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
  (cellUnsealV3 cellDestroyV3 refusalV3 receiptArchiveV3
   afterDiscCol discLive discSealed discDestroyed discArchived AFTER_BLOCK_OFF B_RECORD_DIGEST
   rotateV3WithDiscGate rotateV3WithRecordPin rotateV3
   rotateV3WithDiscGate_forces_after rotateV3WithRecordPin_pins
   rotateV3WithRecordPin_constraints
   graduable_rotateV3WithDiscGate graduable_rotateV3WithRecordPin)
open Dregg2.Circuit.RotatedKernelRefinement (RotTableSide)
open Dregg2.Exec
open Dregg2.Exec.EffectsState
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false
set_option linter.unusedVariables false

/-- A field element (the same `ℤ`-carrier `ListCommit`/`StateCommit`/`SystemRoots` use for a felt;
the local alias, matching `RotatedKernelRefinementCellSeal.FieldElem`). -/
abbrev FieldElem := ℤ

/-! ## §1 — cellUnseal: `lifecycle[cell] := Live`. REUSES `lifecycleRoot` (same side-table, value `lcLive`).

The inverse of cellSeal. The committed `lifecycleRoot` limb is the SAME column; the FIX gate
`gLifecycleUnseal` forces the post lifecycle-root to the digest of `lifecycle[cell ↦ Live]`. -/

/-- The decode tying the FIX row's two committed lifecycle-root columns to the kernel pre/post
lifecycle of `cell` (same as cellSeal's `LifecycleRootRow`, reused for both unseal and destroy). -/
def LifecycleRootRow (compressN : List FieldElem → FieldElem)
    (preK postK : RecordKernelState) (cell : CellId) (preRoot postRoot : FieldElem) : Prop :=
  preRoot = lifecycleRoot compressN preK cell ∧ postRoot = lifecycleRoot compressN postK cell

/-- **`gLifecycleSet compressN preK cell target postRoot`** — the FIX gate body: the POST lifecycle-root
column IS the digest of the kernel whose `cell` entry is set to `target`. Generic over the target value
(`lcLive` for unseal, `lcDestroyed` for destroy) — the `gLifecycleSeal` of cellSeal, parameterized. -/
def gLifecycleSet (compressN : List FieldElem → FieldElem)
    (preK : RecordKernelState) (cell : CellId) (target : Nat) (postRoot : FieldElem) : Prop :=
  postRoot = lifecycleRoot compressN (setLifecycle preK cell target) cell

/-- **`lifecycleSetForced` — the FIX gate FORCES the committed lifecycle column to `target`.** -/
theorem lifecycleSetForced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (preK postK : RecordKernelState) (cell : CellId) (target : Nat) (preRoot postRoot : FieldElem)
    (henc : LifecycleRootRow compressN preK postK cell preRoot postRoot)
    (hgate : gLifecycleSet compressN preK cell target postRoot) :
    postK.lifecycle cell = target := by
  obtain ⟨_, hpost⟩ := henc
  have hroots : lifecycleRoot compressN postK cell
      = lifecycleRoot compressN (setLifecycle preK cell target) cell := by
    rw [← hpost]; exact hgate
  have hval := lifecycleRoot_binds compressN hN postK (setLifecycle preK cell target) cell hroots
  rw [hval]
  show (if cell = cell then target else preK.lifecycle cell) = target
  rw [if_pos rfl]

/-- **`unsealMapForced` — the post lifecycle MAP is `unsealLifecycleMap`.** The committed root forces the
`cell` entry to `lcLive`; the off-`cell` freeze residual carries the rest. -/
theorem unsealMapForced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (preK postK : RecordKernelState) (cell : CellId) (preRoot postRoot : FieldElem)
    (henc : LifecycleRootRow compressN preK postK cell preRoot postRoot)
    (hgate : gLifecycleSet compressN preK cell lcLive postRoot)
    (hframeOther : ∀ c, c ≠ cell → postK.lifecycle c = preK.lifecycle c) :
    postK.lifecycle = unsealLifecycleMap preK cell := by
  have hcell : postK.lifecycle cell = lcLive :=
    lifecycleSetForced compressN hN preK postK cell lcLive preRoot postRoot henc hgate
  funext c
  show postK.lifecycle c = (setLifecycle preK cell lcLive).lifecycle c
  show postK.lifecycle c = (if c = cell then lcLive else preK.lifecycle c)
  by_cases hc : c = cell
  · subst hc; rw [if_pos rfl]; exact hcell
  · rw [if_neg hc]; exact hframeOther c hc

/-- The active-row⟷kernel decode for a satisfying FIX cellUnseal witness. Carries the FIX gate (the
WITNESS leg), the off-`cell` freeze, the `CellUnsealGuard`, the log, and the 16-field frame as NAMED
residuals — exactly the `cellSealGenuineEncodes` shape. -/
structure cellUnsealEncodes (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (actor cell : CellId) : Type where
  preRoot : FieldElem
  postRoot : FieldElem
  hroots : LifecycleRootRow compressN pre.kernel post.kernel cell preRoot postRoot
  gate : gLifecycleSet compressN pre.kernel cell lcLive postRoot
  frameOther : ∀ c, c ≠ cell → post.kernel.lifecycle c = pre.kernel.lifecycle c
  guard : CellUnsealGuard pre actor cell
  logAdv : post.log = cellLifecycleReceipt actor cell :: pre.log
  frAccounts : post.kernel.accounts = pre.kernel.accounts
  frCell : post.kernel.cell = pre.kernel.cell
  frCaps : post.kernel.caps = pre.kernel.caps
  frNullifiers : post.kernel.nullifiers = pre.kernel.nullifiers
  frRevoked : post.kernel.revoked = pre.kernel.revoked
  frCommitments : post.kernel.commitments = pre.kernel.commitments
  frBal : post.kernel.bal = pre.kernel.bal
  frSlotCaveats : post.kernel.slotCaveats = pre.kernel.slotCaveats
  frFactories : post.kernel.factories = pre.kernel.factories
  frDeathCert : post.kernel.deathCert = pre.kernel.deathCert
  frDelegate : post.kernel.delegate = pre.kernel.delegate
  frDelegations : post.kernel.delegations = pre.kernel.delegations
  frDelegationEpoch : post.kernel.delegationEpoch = pre.kernel.delegationEpoch
  frDelegationEpochAt : post.kernel.delegationEpochAt = pre.kernel.delegationEpochAt
  frHeaps : post.kernel.heaps = pre.kernel.heaps

/-- **`cellUnseal_lifecycle_forced` — the committed lifecycle write is FIX-CIRCUIT-FORCED.** -/
theorem cellUnseal_lifecycle_forced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId)
    (henc : cellUnsealEncodes compressN pre post actor cell) :
    post.kernel.lifecycle = unsealLifecycleMap pre.kernel cell :=
  unsealMapForced compressN hN pre.kernel post.kernel cell henc.preRoot henc.postRoot
    henc.hroots henc.gate henc.frameOther

/-- **`cellUnseal_descriptorRefines` — THE FIX CIRCUIT→KERNEL REFINEMENT for cellUnseal.** -/
theorem cellUnseal_descriptorRefines (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId)
    (henc : cellUnsealEncodes compressN pre post actor cell) :
    CellUnsealSpec pre actor cell post := by
  refine ⟨henc.guard, ?_, henc.logAdv, henc.frAccounts, henc.frCell, henc.frCaps,
    henc.frNullifiers, henc.frRevoked, henc.frCommitments, henc.frBal, henc.frSlotCaveats,
    henc.frFactories, henc.frDeathCert, henc.frDelegate, henc.frDelegations,
    henc.frDelegationEpoch, henc.frDelegationEpochAt, henc.frHeaps⟩
  exact cellUnseal_lifecycle_forced compressN hN pre post actor cell henc

/-- The refinement against `execFullA` directly (via `cellUnseal_iff_spec`). -/
theorem cellUnseal_descriptorRefines_execFullA (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId)
    (henc : cellUnsealEncodes compressN pre post actor cell) :
    execFullA pre (.cellUnsealA actor cell) = some post :=
  (Dregg2.Circuit.Spec.CellLifecycle.cellUnseal_iff_spec pre actor cell post).mpr
    (cellUnseal_descriptorRefines compressN hN pre post actor cell henc)

/-- **TOOTH — `cellUnseal_descriptorRefines_rejects_unrevived`.** A decode asserting a post whose `cell`
lifecycle is NOT `lcLive` cannot ride a satisfying FIX witness (the lifecycle-root gate pins it). -/
theorem cellUnseal_descriptorRefines_rejects_unrevived (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId)
    (henc : cellUnsealEncodes compressN pre post actor cell)
    (hwrong : post.kernel.lifecycle cell ≠ lcLive) :
    False :=
  hwrong (lifecycleSetForced compressN hN pre.kernel post.kernel cell lcLive
    henc.preRoot henc.postRoot henc.hroots henc.gate)

/-- **TOOTH — `cellUnseal_descriptorRefines_rejects_wrong_map`.** -/
theorem cellUnseal_descriptorRefines_rejects_wrong_map (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId)
    (henc : cellUnsealEncodes compressN pre post actor cell)
    (hwrong : post.kernel.lifecycle ≠ unsealLifecycleMap pre.kernel cell) :
    False :=
  hwrong (cellUnseal_lifecycle_forced compressN hN pre post actor cell henc)

/-! ## §2 — cellDestroy: `lifecycle[cell] := Destroyed` AND `deathCert[cell] := certHash`.

TWO committed writes. The lifecycle leg REUSES `lifecycleRoot` (target `lcDestroyed`). The death-cert leg
needs a SECOND side-table root `deathCertRoot`, cloned from `lifecycleRoot`. Both forced. -/

/-- **`deathCertRoot compressN k cell`** — the committed root of cell `cell`'s `deathCert` entry: the
`listDigest` over `[k.deathCert cell]`. The Lean mirror of the Rust `death_cert_root` limb. A direct
clone of `lifecycleRoot` for the `deathCert : CellId → Nat` side-table (same injective leaf encoder). -/
def deathCertRoot (compressN : List FieldElem → FieldElem) (k : RecordKernelState) (cell : CellId) :
    FieldElem :=
  listDigest lifecycleLeaf compressN [k.deathCert cell]

/-- **`deathCertRoot_binds`** — equal death-cert roots (over the SAME `cell`) force the SAME entry. -/
theorem deathCertRoot_binds (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (k k' : RecordKernelState) (cell : CellId)
    (h : deathCertRoot compressN k cell = deathCertRoot compressN k' cell) :
    k.deathCert cell = k'.deathCert cell := by
  unfold deathCertRoot at h
  have hlist : ([k.deathCert cell] : List Nat) = [k'.deathCert cell] :=
    ListDigestBindsList lifecycleLeaf compressN hN lifecycleLeaf_injective _ _ h
  exact List.head_eq_of_cons_eq hlist

/-- **`gDeathCertSet compressN preK cell certHash postRoot`** — the FIX gate: the POST death-cert-root
column IS the digest of the kernel whose `cell` death-cert entry is set to `certHash`. -/
def gDeathCertSet (compressN : List FieldElem → FieldElem)
    (preK : RecordKernelState) (cell : CellId) (certHash : Nat) (postRoot : FieldElem) : Prop :=
  postRoot = deathCertRoot compressN
    { preK with deathCert := fun c => if c = cell then certHash else preK.deathCert c } cell

/-- **`deathCertSetForced` — the FIX gate FORCES the committed death-cert column to `certHash`.** -/
theorem deathCertSetForced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (preK postK : RecordKernelState) (cell : CellId) (certHash : Nat) (postRoot : FieldElem)
    (hpost : postRoot = deathCertRoot compressN postK cell)
    (hgate : gDeathCertSet compressN preK cell certHash postRoot) :
    postK.deathCert cell = certHash := by
  have hroots : deathCertRoot compressN postK cell
      = deathCertRoot compressN
          { preK with deathCert := fun c => if c = cell then certHash else preK.deathCert c } cell := by
    rw [← hpost]; exact hgate
  have hval := deathCertRoot_binds compressN hN postK
    { preK with deathCert := fun c => if c = cell then certHash else preK.deathCert c } cell hroots
  rw [hval]
  show (if cell = cell then certHash else preK.deathCert cell) = certHash
  rw [if_pos rfl]

/-- The decode for a satisfying FIX cellDestroy witness: TWO committed roots (lifecycle + death-cert),
their gates, the off-`cell` freezes for BOTH side-tables, the guard, the log, the 15-field frame. -/
structure cellDestroyEncodes (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (actor cell : CellId) (certHash : Nat) : Type where
  -- LIFECYCLE leg (reuses lifecycleRoot, target lcDestroyed).
  lcPreRoot : FieldElem
  lcPostRoot : FieldElem
  hlcRoots : LifecycleRootRow compressN pre.kernel post.kernel cell lcPreRoot lcPostRoot
  lcGate : gLifecycleSet compressN pre.kernel cell lcDestroyed lcPostRoot
  lcFrameOther : ∀ c, c ≠ cell → post.kernel.lifecycle c = pre.kernel.lifecycle c
  -- DEATH-CERT leg (new deathCertRoot).
  dcPostRoot : FieldElem
  hdcPost : dcPostRoot = deathCertRoot compressN post.kernel cell
  dcGate : gDeathCertSet compressN pre.kernel cell certHash dcPostRoot
  dcFrameOther : ∀ c, c ≠ cell → post.kernel.deathCert c = pre.kernel.deathCert c
  -- the admissibility guard + log + the 15-field frame (deathCert + lifecycle are FORCED, not framed).
  guard : CellDestroyGuard pre actor cell
  logAdv : post.log = cellLifecycleReceipt actor cell :: pre.log
  frAccounts : post.kernel.accounts = pre.kernel.accounts
  frCell : post.kernel.cell = pre.kernel.cell
  frCaps : post.kernel.caps = pre.kernel.caps
  frNullifiers : post.kernel.nullifiers = pre.kernel.nullifiers
  frRevoked : post.kernel.revoked = pre.kernel.revoked
  frCommitments : post.kernel.commitments = pre.kernel.commitments
  frBal : post.kernel.bal = pre.kernel.bal
  frSlotCaveats : post.kernel.slotCaveats = pre.kernel.slotCaveats
  frFactories : post.kernel.factories = pre.kernel.factories
  frDelegate : post.kernel.delegate = pre.kernel.delegate
  frDelegations : post.kernel.delegations = pre.kernel.delegations
  frDelegationEpoch : post.kernel.delegationEpoch = pre.kernel.delegationEpoch
  frDelegationEpochAt : post.kernel.delegationEpochAt = pre.kernel.delegationEpochAt
  frHeaps : post.kernel.heaps = pre.kernel.heaps

/-- **`cellDestroy_lifecycle_forced` — the destroyed lifecycle MAP is FIX-CIRCUIT-FORCED.** -/
theorem cellDestroy_lifecycle_forced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId) (certHash : Nat)
    (henc : cellDestroyEncodes compressN pre post actor cell certHash) :
    post.kernel.lifecycle = (destroyKernelMap pre.kernel cell certHash).lifecycle := by
  have hcell : post.kernel.lifecycle cell = lcDestroyed :=
    lifecycleSetForced compressN hN pre.kernel post.kernel cell lcDestroyed
      henc.lcPreRoot henc.lcPostRoot henc.hlcRoots henc.lcGate
  funext c
  show post.kernel.lifecycle c = (setLifecycle pre.kernel cell lcDestroyed).lifecycle c
  show post.kernel.lifecycle c = (if c = cell then lcDestroyed else pre.kernel.lifecycle c)
  by_cases hc : c = cell
  · subst hc; rw [if_pos rfl]; exact hcell
  · rw [if_neg hc]; exact henc.lcFrameOther c hc

/-- **`cellDestroy_deathCert_forced` — the death-cert MAP is FIX-CIRCUIT-FORCED.** -/
theorem cellDestroy_deathCert_forced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId) (certHash : Nat)
    (henc : cellDestroyEncodes compressN pre post actor cell certHash) :
    post.kernel.deathCert = (destroyKernelMap pre.kernel cell certHash).deathCert := by
  have hcell : post.kernel.deathCert cell = certHash :=
    deathCertSetForced compressN hN pre.kernel post.kernel cell certHash henc.dcPostRoot
      henc.hdcPost henc.dcGate
  funext c
  show post.kernel.deathCert c = destroyDeathCertMap pre.kernel cell certHash c
  show post.kernel.deathCert c = (if c = cell then certHash else pre.kernel.deathCert c)
  by_cases hc : c = cell
  · subst hc; rw [if_pos rfl]; exact hcell
  · rw [if_neg hc]; exact henc.dcFrameOther c hc

/-- **`cellDestroy_descriptorRefines` — THE FIX CIRCUIT→KERNEL REFINEMENT for cellDestroy.** BOTH the
lifecycle write (→Destroyed) AND the death-cert bind (→certHash) are FORCED via their committed roots;
the guard, log, and 15-field frame are the named decode residual. -/
theorem cellDestroy_descriptorRefines (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId) (certHash : Nat)
    (henc : cellDestroyEncodes compressN pre post actor cell certHash) :
    CellDestroySpec pre actor cell certHash post := by
  refine ⟨henc.guard, ?_, ?_, henc.logAdv, henc.frAccounts, henc.frCell, henc.frCaps,
    henc.frNullifiers, henc.frRevoked, henc.frCommitments, henc.frBal, henc.frSlotCaveats,
    henc.frFactories, henc.frDelegate, henc.frDelegations,
    henc.frDelegationEpoch, henc.frDelegationEpochAt, henc.frHeaps⟩
  · exact cellDestroy_lifecycle_forced compressN hN pre post actor cell certHash henc
  · exact cellDestroy_deathCert_forced compressN hN pre post actor cell certHash henc

/-- The refinement against `execFullA` directly (via `cellDestroy_iff_spec`). -/
theorem cellDestroy_descriptorRefines_execFullA (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId) (certHash : Nat)
    (henc : cellDestroyEncodes compressN pre post actor cell certHash) :
    execFullA pre (.cellDestroyA actor cell certHash) = some post :=
  (Dregg2.Circuit.Spec.CellLifecycle.cellDestroy_iff_spec pre actor cell certHash post).mpr
    (cellDestroy_descriptorRefines compressN hN pre post actor cell certHash henc)

/-- **TOOTH — `cellDestroy_descriptorRefines_rejects_undestroyed`.** A post whose `cell` lifecycle is
NOT `lcDestroyed` cannot ride a satisfying FIX witness. -/
theorem cellDestroy_descriptorRefines_rejects_undestroyed (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId) (certHash : Nat)
    (henc : cellDestroyEncodes compressN pre post actor cell certHash)
    (hwrong : post.kernel.lifecycle cell ≠ lcDestroyed) :
    False :=
  hwrong (lifecycleSetForced compressN hN pre.kernel post.kernel cell lcDestroyed
    henc.lcPreRoot henc.lcPostRoot henc.hlcRoots henc.lcGate)

/-- **TOOTH — `cellDestroy_descriptorRefines_rejects_wrong_cert`.** A post whose `cell` death-cert is
NOT `certHash` cannot ride a satisfying FIX witness (the death-cert-root gate bites — this is the bind
the deployed circuit cannot enforce). -/
theorem cellDestroy_descriptorRefines_rejects_wrong_cert (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId) (certHash : Nat)
    (henc : cellDestroyEncodes compressN pre post actor cell certHash)
    (hwrong : post.kernel.deathCert cell ≠ certHash) :
    False :=
  hwrong (deathCertSetForced compressN hN pre.kernel post.kernel cell certHash henc.dcPostRoot
    henc.hdcPost henc.dcGate)

/-! ## §3 — refusal / receiptArchive: an audit RECORD-SLOT write `cell.cell[cell].f := 1`.

These write a RECORD SLOT of the `cell` MAP (`fieldOf f (k.cell cell)`), NOT a side-table. The deployed
commitment binds `fields[0..7]` but the audit slots `"refusal"`/`"lifecycle"` are extra named slots no
committed column pins. A NEW committed limb `auditSlotRoot` over the touched slot value, forced to `1`.

The leaf encoder is `Int → FieldElem` (the slot value read by `fieldOf`); it is injective (`Int` IS the
felt carrier). The committed root FORCES the slot value `= 1` (the load-bearing audit write); the WHOLE
`cell`-map equality (off-cell records whole, `cell`'s other fields kept) is the NAMED decode residual
`cellMapMove`, exactly as setField's `rotatedEncodesSF` carries `setFieldCellMap`. -/

/-- The injective leaf encoder for an audit slot value (an `Int`, the felt carrier itself). -/
def auditLeaf : Int → FieldElem := id

theorem auditLeaf_injective : listLeafInjective auditLeaf := fun a b h => h

/-- **`auditSlotRoot compressN k cell f`** — the committed root of cell `cell`'s audit slot `f`: the
`listDigest` over `[fieldOf f (k.cell cell)]`. The Lean mirror of the Rust `audit_slot_root` limb. -/
def auditSlotRoot (compressN : List FieldElem → FieldElem) (k : RecordKernelState)
    (cell : CellId) (f : FieldName) : FieldElem :=
  listDigest auditLeaf compressN [fieldOf f (k.cell cell)]

/-- **`auditSlotRoot_binds`** — equal audit-slot roots (same `cell`, same `f`) force the SAME slot
value (off `compressNInjective` + the injective leaf). -/
theorem auditSlotRoot_binds (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (k k' : RecordKernelState) (cell : CellId) (f : FieldName)
    (h : auditSlotRoot compressN k cell f = auditSlotRoot compressN k' cell f) :
    fieldOf f (k.cell cell) = fieldOf f (k'.cell cell) := by
  unfold auditSlotRoot at h
  have hlist : ([fieldOf f (k.cell cell)] : List Int) = [fieldOf f (k'.cell cell)] :=
    ListDigestBindsList auditLeaf compressN hN auditLeaf_injective _ _ h
  exact List.head_eq_of_cons_eq hlist

/-- **`gAuditSlotOne compressN cell f postRoot`** — the FIX gate: the POST audit-slot-root column IS the
digest of the slot value `1` (the one-shot commitment flag every audit write stamps). -/
def gAuditSlotOne (compressN : List FieldElem → FieldElem) (cell : CellId) (f : FieldName)
    (postRoot : FieldElem) : Prop :=
  postRoot = listDigest auditLeaf compressN [(1 : Int)]

/-- **`auditSlotForced` — the FIX gate FORCES the committed audit slot to `1`.** -/
theorem auditSlotForced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (postK : RecordKernelState) (cell : CellId) (f : FieldName) (postRoot : FieldElem)
    (hpost : postRoot = auditSlotRoot compressN postK cell f)
    (hgate : gAuditSlotOne compressN cell f postRoot) :
    fieldOf f (postK.cell cell) = 1 := by
  have hroots : auditSlotRoot compressN postK cell f
      = listDigest auditLeaf compressN [(1 : Int)] := by rw [← hpost]; exact hgate
  unfold auditSlotRoot at hroots
  have hlist : ([fieldOf f (postK.cell cell)] : List Int) = [(1 : Int)] :=
    ListDigestBindsList auditLeaf compressN hN auditLeaf_injective _ _ hroots
  exact List.head_eq_of_cons_eq hlist

/-- The decode for a satisfying FIX audit-slot witness. Carries the FIX gate (the WITNESS leg forcing the
slot value `= 1`), the WHOLE `cell`-map move `cellMapMove` (the off-slot/off-cell residual the per-slot
root cannot witness — exactly setField's `setFieldCellMap`), the `auditGuard`, the log, and the 16-field
frame. Parameterized by the audit field `f` so the SAME structure serves refusal (`refusalField`) and
receiptArchive (`lifecycleField`). -/
structure auditEncodes (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (actor cell : CellId) (f : FieldName) : Type where
  postRoot : FieldElem
  hpost : postRoot = auditSlotRoot compressN post.kernel cell f
  gate : gAuditSlotOne compressN cell f postRoot
  -- the WHOLE `cell`-map move (the residual the per-slot committed root cannot certify).
  cellMapMove : post.kernel.cell = auditCellMap pre.kernel cell f
  guard : auditGuard pre actor cell
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

/-- **`audit_slot_forced` — the committed audit slot is FIX-CIRCUIT-FORCED to `1`.** The WITNESS gate
pins the slot value to the one-shot flag; this is the rung the deployed circuit is missing. -/
theorem audit_slot_forced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId) (f : FieldName)
    (henc : auditEncodes compressN pre post actor cell f) :
    fieldOf f (post.kernel.cell cell) = 1 :=
  auditSlotForced compressN hN post.kernel cell f henc.postRoot henc.hpost henc.gate

/-- **`refusal_descriptorRefines` — THE FIX CIRCUIT→KERNEL REFINEMENT for refusal.** The `"refusal" := 1`
audit-slot write is FORCED via the committed `auditSlotRoot`; the whole `cell`-map move, the guard, the
log, and the 16-field frame are the named decode residual. -/
theorem refusal_descriptorRefines (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId)
    (henc : auditEncodes compressN pre post actor cell refusalField) :
    RefusalSpec pre actor cell post :=
  ⟨henc.guard, henc.cellMapMove, henc.logAdv, henc.frAccounts, henc.frCaps,
    henc.frNullifiers, henc.frRevoked, henc.frCommitments, henc.frBal, henc.frSlotCaveats,
    henc.frFactories, henc.frLifecycle, henc.frDeathCert, henc.frDelegate, henc.frDelegations,
    henc.frDelegationEpoch, henc.frDelegationEpochAt, henc.frHeaps⟩

/-- The refinement against `execFullA` directly (via `execFullA_refusalA_iff_spec`). -/
theorem refusal_descriptorRefines_execFullA (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId)
    (henc : auditEncodes compressN pre post actor cell refusalField) :
    execFullA pre (.refusalA actor cell) = some post :=
  (Dregg2.Circuit.Spec.CellStateAudit.execFullA_refusalA_iff_spec pre actor cell post).mpr
    (refusal_descriptorRefines compressN hN pre post actor cell henc)

/-- **`receiptArchive_descriptorRefines` — THE FIX CIRCUIT→KERNEL REFINEMENT for receiptArchive.** The
`"lifecycle" := 1` RECORD-slot write is FORCED via the committed `auditSlotRoot` (over `lifecycleField`);
the whole `cell`-map move + guard + log + frame are the named decode residual. NOTE: this writes the
RECORD slot, NOT the `lifecycle` side-table (`frLifecycle` confirms the side-table is frozen). -/
theorem receiptArchive_descriptorRefines (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId)
    (henc : auditEncodes compressN pre post actor cell lifecycleField) :
    ReceiptArchiveSpec pre actor cell post :=
  ⟨henc.guard, henc.cellMapMove, henc.logAdv, henc.frAccounts, henc.frCaps,
    henc.frNullifiers, henc.frRevoked, henc.frCommitments, henc.frBal, henc.frSlotCaveats,
    henc.frFactories, henc.frLifecycle, henc.frDeathCert, henc.frDelegate, henc.frDelegations,
    henc.frDelegationEpoch, henc.frDelegationEpochAt, henc.frHeaps⟩

/-- The MODELLED record-slot refinement against the record-write `receiptArchiveRecordStep` (via
`receiptArchiveRecordStep_iff_spec`). Keyed off the record write, NOT the deployed `execFullA` arm
(which moves the lifecycle side-table). -/
theorem receiptArchive_descriptorRefines_recordStep (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId)
    (henc : auditEncodes compressN pre post actor cell lifecycleField) :
    Dregg2.Circuit.Spec.CellStateAudit.receiptArchiveRecordStep pre actor cell = some post :=
  (Dregg2.Circuit.Spec.CellStateAudit.receiptArchiveRecordStep_iff_spec pre actor cell post).mpr
    (receiptArchive_descriptorRefines compressN hN pre post actor cell henc)

/-- **TOOTH — `audit_descriptorRefines_rejects_unwritten`.** A decode asserting a post whose `cell`
audit slot `f` is NOT `1` cannot ride a satisfying FIX witness (the audit-slot-root gate bites). Covers
BOTH refusal (`f = refusalField`) and receiptArchive (`f = lifecycleField`). -/
theorem audit_descriptorRefines_rejects_unwritten (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId) (f : FieldName)
    (henc : auditEncodes compressN pre post actor cell f)
    (hwrong : fieldOf f (post.kernel.cell cell) ≠ 1) :
    False :=
  hwrong (audit_slot_forced compressN hN pre post actor cell f henc)

/-! ## §3.5 — CLASS A: the lifecycle/audit writes are FORCED by the DEPLOYED descriptors
  (`cellUnsealV3` / `cellDestroyV3` / `refusalV3`), not the modelled `g*` gates of §1–§3.

§1–§3 force each write from a MODELLED gate the decode ASSERTS (`gLifecycleSet` / `gDeathCertSet` /
`gAuditSlotOne`); editing the LIVE descriptor constraints does NOT break those. This section closes that
gap, EXACTLY as `RotatedKernelRefinementCellSeal.§6.5` does for cellSeal:

  * **cellUnseal** — `cellUnsealV3 = graduateV1 (rotateV3WithDiscGate SEL_CELLUNSEAL (some discSealed)
    discLive cellUnsealVmDescriptor)`. The DEPLOYED disc gate FORCES the committed AFTER disc limb
    (`afterDiscCol`, B_DISC = 32) to `discLive (= 0)` on the active transition row
    (`rotateV3WithDiscGate_forces_after`). The realizable `discLimbDecodes` seam ties that limb to the
    post lifecycle discriminant (`= (post.lifecycle cell : ℤ)`), so `post.lifecycle cell = lcLive`.
  * **cellDestroy** — `cellDestroyV3 = graduateV1 (rotateV3WithDiscGate SEL_CELLDESTROY none discDestroyed
    cellDestroyVmDescriptor)`. The disc gate forces AFTER disc `= discDestroyed (= 3)`, so
    `post.lifecycle cell = lcDestroyed` (the lifecycle leg). The death-cert leg is forced by the SAME
    record-pin route the §3 audit slot uses (`rotateV3WithRecordPin` on B_LIFECYCLE, folding the death-cert
    into `lifecycle_felt` — the `deathCertLimbDecodes`/`deathCertPiAnchored` seam).
  * **refusal** — `refusalV3 = graduateV1 (rotateV3WithRecordPin B_RECORD_DIGEST refusalVmDescriptor)`. A
    pure record-pin (NO disc gate): `rotateV3WithRecordPin_pins` FORCES the committed AFTER record-digest
    limb (`B_RECORD_DIGEST = 24`) EQUAL to the published rotated PI. The realizable seam ties that limb to
    the post audit-slot root (`recordLimbDecodes`) AND the verifier-anchored PI to the digest of slot
    value `1` (`piAnchored`, the `lifecycle_felt_cell`/`compute_authority_digest_felt`-anchor floor the
    deployed verifier supplies — the SAME `StarkSound`/`WitnessDecodes`-class carrier transfer/cellSeal
    use), so `fieldOf refusalField (post.cell cell) = 1`.

Editing the respective deployed descriptor's gate breaks its `*_forced` lemma, hence the
`*_descriptorRefines_sat`, hence the rung — Class A. Each seam is a NAMED realizable structure field
(`#assert_axioms`-clean), never a `sorry`/assumed-decode. -/

/-! ### cellUnseal — Class A from the DEPLOYED disc gate (`cellUnsealV3`). -/

/-- **`CellUnsealTraceReadout`** — the realizable circuit-witness extraction for cellUnseal, the
`WitnessDecodes` class of cellSeal's `CellSealTraceReadout`: the designated ACTIVE cellUnseal row + its
selector fact + the realizable disc-limb decode (the committed AFTER disc limb IS the post lifecycle
discriminant felt) + the whole-map / guard / log / 16-field residual. The disc GATE is NOT a field — it is
FORCED from `Satisfied2 hash cellUnsealV3` (`cellUnseal_forced`). -/
structure CellUnsealTraceReadout (hash : List ℤ → ℤ)
    (t : VmTrace) (pre post : RecChainedState) (actor cell : CellId) : Type where
  row : Nat
  hrow : row < t.rows.length
  hrowNotLast : row + 1 ≠ t.rows.length
  hsel : (envAt t row).loc Dregg2.Circuit.Emit.EffectVmEmitCellUnseal.SEL_CELLUNSEAL = 1
  -- the realizable seam: the committed AFTER disc TRACE limb IS the post lifecycle discriminant cast to ℤ.
  discLimbDecodes :
    (envAt t row).loc
      (afterDiscCol Dregg2.Circuit.Emit.EffectVmEmitCellUnseal.cellUnsealVmDescriptor.traceWidth)
      = ((post.kernel.lifecycle cell : Nat) : ℤ)
  frameOther : ∀ c, c ≠ cell → post.kernel.lifecycle c = pre.kernel.lifecycle c
  guard : CellUnsealGuard pre actor cell
  logAdv : post.log = cellLifecycleReceipt actor cell :: pre.log
  frAccounts : post.kernel.accounts = pre.kernel.accounts
  frCell : post.kernel.cell = pre.kernel.cell
  frCaps : post.kernel.caps = pre.kernel.caps
  frNullifiers : post.kernel.nullifiers = pre.kernel.nullifiers
  frRevoked : post.kernel.revoked = pre.kernel.revoked
  frCommitments : post.kernel.commitments = pre.kernel.commitments
  frBal : post.kernel.bal = pre.kernel.bal
  frSlotCaveats : post.kernel.slotCaveats = pre.kernel.slotCaveats
  frFactories : post.kernel.factories = pre.kernel.factories
  frDeathCert : post.kernel.deathCert = pre.kernel.deathCert
  frDelegate : post.kernel.delegate = pre.kernel.delegate
  frDelegations : post.kernel.delegations = pre.kernel.delegations
  frDelegationEpoch : post.kernel.delegationEpoch = pre.kernel.delegationEpoch
  frDelegationEpochAt : post.kernel.delegationEpochAt = pre.kernel.delegationEpochAt
  frHeaps : post.kernel.heaps = pre.kernel.heaps

/-- `cellUnsealV3`'s underlying disc-gated descriptor is graduable (the cellSeal `_disc_graduable`
analog). -/
theorem cellUnseal_disc_graduable :
    graduable (rotateV3WithDiscGate Dregg2.Circuit.Emit.EffectVmEmitCellUnseal.SEL_CELLUNSEAL
      (some discSealed) discLive
      Dregg2.Circuit.Emit.EffectVmEmitCellUnseal.cellUnsealVmDescriptor) = true := by decide

/-- **`cellUnseal_forced` — the revive (`lifecycle := Live`) is FORCED by the DEPLOYED `cellUnsealV3`.**
The committed AFTER disc limb is pinned to `discLive (= 0)` by the LIVE disc gate, and the readout's
`discLimbDecodes` identifies that limb with the post lifecycle discriminant — so the discriminant is
`0 = lcLive`. Editing `cellUnsealV3`'s disc gate turns this RED. -/
theorem cellUnseal_forced (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash cellUnsealV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId)
    (rd : CellUnsealTraceReadout hash t pre post actor cell) :
    post.kernel.lifecycle cell = lcLive := by
  have hv1 : satisfiedVm hash
      (rotateV3WithDiscGate Dregg2.Circuit.Emit.EffectVmEmitCellUnseal.SEL_CELLUNSEAL (some discSealed)
        discLive Dregg2.Circuit.Emit.EffectVmEmitCellUnseal.cellUnsealVmDescriptor)
      (envAt t rd.row) (rd.row == 0) (rd.row + 1 == t.rows.length) :=
    graduateV1_sound hash _ minit mfin maddrs t hside.chip hside.range cellUnseal_disc_graduable
      hsat rd.row rd.hrow
  have hlastf : (rd.row + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact rd.hrowNotLast
  rw [hlastf] at hv1
  have hlimb : (envAt t rd.row).loc
      (afterDiscCol Dregg2.Circuit.Emit.EffectVmEmitCellUnseal.cellUnsealVmDescriptor.traceWidth)
        = discLive :=
    rotateV3WithDiscGate_forces_after _ _ _ hash _ (envAt t rd.row) (rd.row == 0) false rfl rd.hsel hv1
  have hcast : ((post.kernel.lifecycle cell : Nat) : ℤ) = ((lcLive : Nat) : ℤ) := by
    rw [← rd.discLimbDecodes, hlimb]; rfl
  exact_mod_cast hcast

/-- **`cellUnseal_forced_map` — the post lifecycle MAP is `unsealLifecycleMap` (Class A, whole map).** -/
theorem cellUnseal_forced_map (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash cellUnsealV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId)
    (rd : CellUnsealTraceReadout hash t pre post actor cell) :
    post.kernel.lifecycle = unsealLifecycleMap pre.kernel cell := by
  have hcell : post.kernel.lifecycle cell = lcLive :=
    cellUnseal_forced hash hside hsat pre post actor cell rd
  funext c
  show post.kernel.lifecycle c = (setLifecycle pre.kernel cell lcLive).lifecycle c
  show post.kernel.lifecycle c = (if c = cell then lcLive else pre.kernel.lifecycle c)
  by_cases hc : c = cell
  · subst hc; rw [if_pos rfl]; exact hcell
  · rw [if_neg hc]; exact rd.frameOther c hc

/-- **`cellUnseal_descriptorRefines_sat` — THE CLASS-A CIRCUIT→KERNEL REFINEMENT for cellUnseal.** A
satisfying DEPLOYED `cellUnsealV3` witness + the realizable `CellUnsealTraceReadout` forces
`CellUnsealSpec`. The `lifecycle := Live` write is forced from the DEPLOYED disc gate's `Satisfied2`
(`cellUnseal_forced_map`) — editing `cellUnsealV3` turns this RED. -/
theorem cellUnseal_descriptorRefines_sat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash cellUnsealV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId)
    (rd : CellUnsealTraceReadout hash t pre post actor cell) :
    CellUnsealSpec pre actor cell post := by
  refine ⟨rd.guard, ?_, rd.logAdv, rd.frAccounts, rd.frCell, rd.frCaps,
    rd.frNullifiers, rd.frRevoked, rd.frCommitments, rd.frBal, rd.frSlotCaveats,
    rd.frFactories, rd.frDeathCert, rd.frDelegate, rd.frDelegations,
    rd.frDelegationEpoch, rd.frDelegationEpochAt, rd.frHeaps⟩
  exact cellUnseal_forced_map hash hside hsat pre post actor cell rd

/-- **CLASS-A TOOTH — a forged un-revived cellUnseal witness is UNSAT.** A readout whose post `cell`
lifecycle is NOT `lcLive` cannot ride a satisfying `cellUnsealV3` witness — the DEPLOYED disc gate pins
the revive. -/
theorem cellUnseal_sat_rejects_unrevived (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash cellUnsealV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId)
    (rd : CellUnsealTraceReadout hash t pre post actor cell)
    (hwrong : post.kernel.lifecycle cell ≠ lcLive) :
    False :=
  hwrong (cellUnseal_forced hash hside hsat pre post actor cell rd)

/-! ### cellDestroy — Class A: the lifecycle leg from the DEPLOYED disc gate (`cellDestroyV3`),
the death-cert leg from the DEPLOYED record pin (B_LIFECYCLE, the `lifecycle_felt` fold). -/

/-- **`CellDestroyTraceReadout`** — the realizable circuit-witness extraction for cellDestroy. TWO
deployed-forced legs:
  * the disc-limb decode (AFTER disc IS the post lifecycle discriminant) — the lifecycle leg;
  * the record-limb decode + PI anchor on B_LIFECYCLE — the death-cert leg (the deployed `lifecycle_felt`
    folds the death-cert; the verifier anchors the pinned PI to the post death-cert root).
Plus the whole-map freezes for BOTH side-tables + guard + log + 15-field residual. The gates are NOT
fields — both legs are FORCED from `Satisfied2 hash cellDestroyV3`. -/
structure CellDestroyTraceReadout (compressN : List FieldElem → FieldElem) (hash : List ℤ → ℤ)
    (t : VmTrace) (pre post : RecChainedState) (actor cell : CellId) (certHash : Nat) : Type where
  row : Nat
  hrow : row < t.rows.length
  hrowNotLast : row + 1 ≠ t.rows.length
  hsel : (envAt t row).loc Dregg2.Circuit.Emit.EffectVmEmitCellDestroy.SEL_CELLDESTROY = 1
  -- LIFECYCLE leg: the committed AFTER disc limb IS the post lifecycle discriminant.
  discLimbDecodes :
    (envAt t row).loc
      (afterDiscCol Dregg2.Circuit.Emit.EffectVmEmitCellDestroy.cellDestroyVmDescriptor.traceWidth)
      = ((post.kernel.lifecycle cell : Nat) : ℤ)
  lcFrameOther : ∀ c, c ≠ cell → post.kernel.lifecycle c = pre.kernel.lifecycle c
  -- DEATH-CERT leg: the LAST row pins the committed AFTER record limb (B_LIFECYCLE) to the published PI,
  -- the realizable seam ties that limb to the post death-cert root and the anchored PI to `certHash`'s root.
  lastRow : Nat
  hlastRow : lastRow < t.rows.length
  hlastRowIsLast : lastRow + 1 = t.rows.length
  recordLimbDecodes :
    (envAt t lastRow).loc (Dregg2.Circuit.Emit.EffectVmEmitCellDestroy.cellDestroyVmDescriptor.traceWidth
      + AFTER_BLOCK_OFF + Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_LIFECYCLE)
      = deathCertRoot compressN post.kernel cell
  piAnchored :
    (envAt t lastRow).pub
      (rotateV3 Dregg2.Circuit.Emit.EffectVmEmitCellDestroy.cellDestroyVmDescriptor).piCount
      = deathCertRoot compressN
          { pre.kernel with deathCert := fun c => if c = cell then certHash else pre.kernel.deathCert c }
          cell
  dcFrameOther : ∀ c, c ≠ cell → post.kernel.deathCert c = pre.kernel.deathCert c
  guard : CellDestroyGuard pre actor cell
  logAdv : post.log = cellLifecycleReceipt actor cell :: pre.log
  frAccounts : post.kernel.accounts = pre.kernel.accounts
  frCell : post.kernel.cell = pre.kernel.cell
  frCaps : post.kernel.caps = pre.kernel.caps
  frNullifiers : post.kernel.nullifiers = pre.kernel.nullifiers
  frRevoked : post.kernel.revoked = pre.kernel.revoked
  frCommitments : post.kernel.commitments = pre.kernel.commitments
  frBal : post.kernel.bal = pre.kernel.bal
  frSlotCaveats : post.kernel.slotCaveats = pre.kernel.slotCaveats
  frFactories : post.kernel.factories = pre.kernel.factories
  frDelegate : post.kernel.delegate = pre.kernel.delegate
  frDelegations : post.kernel.delegations = pre.kernel.delegations
  frDelegationEpoch : post.kernel.delegationEpoch = pre.kernel.delegationEpoch
  frDelegationEpochAt : post.kernel.delegationEpochAt = pre.kernel.delegationEpochAt
  frHeaps : post.kernel.heaps = pre.kernel.heaps

theorem cellDestroy_disc_graduable :
    graduable (rotateV3WithDiscGate Dregg2.Circuit.Emit.EffectVmEmitCellDestroy.SEL_CELLDESTROY
      none discDestroyed
      Dregg2.Circuit.Emit.EffectVmEmitCellDestroy.cellDestroyVmDescriptor) = true := by decide

/-- **`cellDestroy_lc_forced` — the destroy (`lifecycle := Destroyed`) is FORCED by `cellDestroyV3`.** -/
theorem cellDestroy_lc_forced (compressN : List FieldElem → FieldElem) (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash cellDestroyV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (certHash : Nat)
    (rd : CellDestroyTraceReadout compressN hash t pre post actor cell certHash) :
    post.kernel.lifecycle cell = lcDestroyed := by
  have hv1 : satisfiedVm hash
      (rotateV3WithDiscGate Dregg2.Circuit.Emit.EffectVmEmitCellDestroy.SEL_CELLDESTROY none
        discDestroyed Dregg2.Circuit.Emit.EffectVmEmitCellDestroy.cellDestroyVmDescriptor)
      (envAt t rd.row) (rd.row == 0) (rd.row + 1 == t.rows.length) :=
    graduateV1_sound hash _ minit mfin maddrs t hside.chip hside.range cellDestroy_disc_graduable
      hsat rd.row rd.hrow
  have hlastf : (rd.row + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact rd.hrowNotLast
  rw [hlastf] at hv1
  have hlimb : (envAt t rd.row).loc
      (afterDiscCol Dregg2.Circuit.Emit.EffectVmEmitCellDestroy.cellDestroyVmDescriptor.traceWidth)
        = discDestroyed :=
    rotateV3WithDiscGate_forces_after _ _ _ hash _ (envAt t rd.row) (rd.row == 0) false rfl rd.hsel hv1
  have hcast : ((post.kernel.lifecycle cell : Nat) : ℤ) = ((lcDestroyed : Nat) : ℤ) := by
    rw [← rd.discLimbDecodes, hlimb]; rfl
  exact_mod_cast hcast

/-- **The record pin survives inside the DISC gate.** `cellDestroyV3`'s underlying descriptor is
`rotateV3WithDiscGate … (rotateV3WithRecordPin B_LIFECYCLE …)` — the record pin's `.piBinding .last`
constraint is preserved (the disc gates only APPEND), so a satisfying LAST row carries the committed
AFTER record limb (B_LIFECYCLE) EQUAL to the published rotated PI. The disc-gate analog of
`rotateV3WithRecordPin_pins`. -/
theorem cellDestroyDiscGate_pins_record (hash : List ℤ → ℤ) (env : VmRowEnv)
    (isFirst : Bool)
    (h : satisfiedVm hash (rotateV3WithDiscGate Dregg2.Circuit.Emit.EffectVmEmitCellDestroy.SEL_CELLDESTROY
      none discDestroyed Dregg2.Circuit.Emit.EffectVmEmitCellDestroy.cellDestroyVmDescriptor)
      env isFirst true) :
    env.loc (Dregg2.Circuit.Emit.EffectVmEmitCellDestroy.cellDestroyVmDescriptor.traceWidth
        + AFTER_BLOCK_OFF + Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_LIFECYCLE)
      = env.pub (rotateV3 Dregg2.Circuit.Emit.EffectVmEmitCellDestroy.cellDestroyVmDescriptor).piCount := by
  have hmem : (VmConstraint.piBinding .last
      (Dregg2.Circuit.Emit.EffectVmEmitCellDestroy.cellDestroyVmDescriptor.traceWidth + AFTER_BLOCK_OFF
        + Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_LIFECYCLE)
      (rotateV3 Dregg2.Circuit.Emit.EffectVmEmitCellDestroy.cellDestroyVmDescriptor).piCount)
      ∈ (rotateV3WithDiscGate Dregg2.Circuit.Emit.EffectVmEmitCellDestroy.SEL_CELLDESTROY none discDestroyed
          Dregg2.Circuit.Emit.EffectVmEmitCellDestroy.cellDestroyVmDescriptor).constraints := by
    show _ ∈ ((rotateV3WithRecordPin Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_LIFECYCLE
        Dregg2.Circuit.Emit.EffectVmEmitCellDestroy.cellDestroyVmDescriptor).constraints ++ _ ++ _)
    rw [rotateV3WithRecordPin_constraints]
    simp only [List.mem_append, List.mem_cons]
    tauto
  have hpin := h.1 _ hmem
  simpa only [VmConstraint.holdsVm] using hpin rfl

/-- **`cellDestroy_dc_forced` — the death-cert bind (`deathCert := certHash`) is FORCED by the DEPLOYED
record pin (B_LIFECYCLE), riding inside `cellDestroyV3`'s disc gate.** The LAST-row pin forces the
committed AFTER record limb EQUAL to the published PI (`cellDestroyDiscGate_pins_record`); the readout's
`recordLimbDecodes` ties that limb to the post death-cert root and `piAnchored` ties the verifier PI to the
digest of the kernel with `deathCert[cell] := certHash`. Digest injectivity (`deathCertRoot_binds`) then
pins the death-cert entry. Editing `cellDestroyV3`'s record pin turns this RED. -/
theorem cellDestroy_dc_forced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash cellDestroyV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (certHash : Nat)
    (rd : CellDestroyTraceReadout compressN hash t pre post actor cell certHash) :
    post.kernel.deathCert cell = certHash := by
  -- lift to the v1 per-row `satisfiedVm` of the FULL disc-gated descriptor on the LAST row.
  have hv1 : satisfiedVm hash
      (rotateV3WithDiscGate Dregg2.Circuit.Emit.EffectVmEmitCellDestroy.SEL_CELLDESTROY none
        discDestroyed Dregg2.Circuit.Emit.EffectVmEmitCellDestroy.cellDestroyVmDescriptor)
      (envAt t rd.lastRow) (rd.lastRow == 0) (rd.lastRow + 1 == t.rows.length) :=
    graduateV1_sound hash _ minit mfin maddrs t hside.chip hside.range cellDestroy_disc_graduable
      hsat rd.lastRow rd.hlastRow
  have hlastt : (rd.lastRow + 1 == t.rows.length) = true := by
    simp only [beq_iff_eq]; exact rd.hlastRowIsLast
  rw [hlastt] at hv1
  -- the deployed record pin (inside the disc gate) forces the committed AFTER record limb = the PI.
  have hpin := cellDestroyDiscGate_pins_record hash (envAt t rd.lastRow) (rd.lastRow == 0) hv1
  -- chain the two realizable decodes: post death-cert root = PI = `certHash`-bind root ⟹ entry pinned.
  rw [rd.recordLimbDecodes, rd.piAnchored] at hpin
  have hval := deathCertRoot_binds compressN hN post.kernel
    { pre.kernel with deathCert := fun c => if c = cell then certHash else pre.kernel.deathCert c }
    cell hpin
  rw [hval]
  show (if cell = cell then certHash else pre.kernel.deathCert cell) = certHash
  rw [if_pos rfl]

/-- **`cellDestroy_descriptorRefines_sat` — THE CLASS-A CIRCUIT→KERNEL REFINEMENT for cellDestroy.** BOTH
legs forced from the DEPLOYED `cellDestroyV3`: the lifecycle write (→Destroyed) from the disc gate, the
death-cert bind (→certHash) from the record pin. Editing `cellDestroyV3` turns this RED. -/
theorem cellDestroy_descriptorRefines_sat (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash cellDestroyV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (certHash : Nat)
    (rd : CellDestroyTraceReadout compressN hash t pre post actor cell certHash) :
    CellDestroySpec pre actor cell certHash post := by
  refine ⟨rd.guard, ?_, ?_, rd.logAdv, rd.frAccounts, rd.frCell, rd.frCaps,
    rd.frNullifiers, rd.frRevoked, rd.frCommitments, rd.frBal, rd.frSlotCaveats,
    rd.frFactories, rd.frDelegate, rd.frDelegations,
    rd.frDelegationEpoch, rd.frDelegationEpochAt, rd.frHeaps⟩
  · -- the lifecycle MAP is `(destroyKernelMap …).lifecycle`.
    have hcell : post.kernel.lifecycle cell = lcDestroyed :=
      cellDestroy_lc_forced compressN hash hside hsat pre post actor cell certHash rd
    funext c
    show post.kernel.lifecycle c = (setLifecycle pre.kernel cell lcDestroyed).lifecycle c
    show post.kernel.lifecycle c = (if c = cell then lcDestroyed else pre.kernel.lifecycle c)
    by_cases hc : c = cell
    · subst hc; rw [if_pos rfl]; exact hcell
    · rw [if_neg hc]; exact rd.lcFrameOther c hc
  · -- the death-cert MAP is `(destroyKernelMap …).deathCert`.
    have hcell : post.kernel.deathCert cell = certHash :=
      cellDestroy_dc_forced compressN hN hash hside hsat pre post actor cell certHash rd
    funext c
    show post.kernel.deathCert c = destroyDeathCertMap pre.kernel cell certHash c
    show post.kernel.deathCert c = (if c = cell then certHash else pre.kernel.deathCert c)
    by_cases hc : c = cell
    · subst hc; rw [if_pos rfl]; exact hcell
    · rw [if_neg hc]; exact rd.dcFrameOther c hc

/-- **CLASS-A TOOTH — a Destroyed→Live resurrection forgery is UNSAT.** A readout whose post `cell`
lifecycle is NOT `lcDestroyed` cannot ride a satisfying `cellDestroyV3` witness. -/
theorem cellDestroy_sat_rejects_resurrection (compressN : List FieldElem → FieldElem) (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash cellDestroyV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (certHash : Nat)
    (rd : CellDestroyTraceReadout compressN hash t pre post actor cell certHash)
    (hwrong : post.kernel.lifecycle cell ≠ lcDestroyed) :
    False :=
  hwrong (cellDestroy_lc_forced compressN hash hside hsat pre post actor cell certHash rd)

/-- **CLASS-A TOOTH — a wrong-death-cert forgery is UNSAT.** A readout whose post `cell` death-cert is
NOT `certHash` cannot ride a satisfying `cellDestroyV3` witness (the record-pin bite). -/
theorem cellDestroy_sat_rejects_wrong_cert (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash cellDestroyV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (certHash : Nat)
    (rd : CellDestroyTraceReadout compressN hash t pre post actor cell certHash)
    (hwrong : post.kernel.deathCert cell ≠ certHash) :
    False :=
  hwrong (cellDestroy_dc_forced compressN hN hash hside hsat pre post actor cell certHash rd)

/-! ### refusal — Class A from the DEPLOYED record pin (`refusalV3`, B_RECORD_DIGEST). -/

/-- **`RefusalTraceReadout`** — the realizable circuit-witness extraction for refusal. The deployed
`refusalV3` is a pure record-pin (NO disc gate): the LAST row pins the committed AFTER record-digest limb
(B_RECORD_DIGEST = 24) to the published PI. The realizable seams: `recordLimbDecodes` (that limb IS the
post audit-slot root over `refusalField`) and `piAnchored` (the verifier-anchored PI IS the digest of slot
value `1`). The audit slot GATE is NOT a field — it is FORCED from `Satisfied2 hash refusalV3`. -/
structure RefusalTraceReadout (compressN : List FieldElem → FieldElem) (hash : List ℤ → ℤ)
    (t : VmTrace) (pre post : RecChainedState) (actor cell : CellId) : Type where
  lastRow : Nat
  hlastRow : lastRow < t.rows.length
  hlastRowIsLast : lastRow + 1 = t.rows.length
  -- the committed AFTER record-digest limb IS the post audit-slot root over `refusalField`.
  recordLimbDecodes :
    (envAt t lastRow).loc (Dregg2.Circuit.Emit.EffectVmEmitRefusal.refusalVmDescriptor.traceWidth
      + AFTER_BLOCK_OFF + B_RECORD_DIGEST)
      = auditSlotRoot compressN post.kernel cell refusalField
  -- the verifier-anchored PI IS the digest of slot value `1` (the one-shot audit flag).
  piAnchored :
    (envAt t lastRow).pub
      (rotateV3 Dregg2.Circuit.Emit.EffectVmEmitRefusal.refusalVmDescriptor).piCount
      = listDigest auditLeaf compressN [(1 : Int)]
  -- the WHOLE `cell`-map move (the residual the per-slot committed root cannot certify).
  cellMapMove : post.kernel.cell = auditCellMap pre.kernel cell refusalField
  guard : auditGuard pre actor cell
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

theorem refusal_rcp_graduable :
    graduable (rotateV3WithRecordPin B_RECORD_DIGEST
      Dregg2.Circuit.Emit.EffectVmEmitRefusal.refusalVmDescriptor) = true := by decide

/-- **`refusal_forced` — the audit write (`refusalField := 1`) is FORCED by the DEPLOYED `refusalV3`.**
The LAST-row record pin forces the committed AFTER record-digest limb EQUAL to the published PI
(`rotateV3WithRecordPin_pins`); the readout's `recordLimbDecodes` ties that limb to the post audit-slot
root and `piAnchored` ties the verifier PI to the digest of slot value `1`. Digest injectivity then pins
the slot value. Editing `refusalV3`'s record pin turns this RED. -/
theorem refusal_forced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash refusalV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId)
    (rd : RefusalTraceReadout compressN hash t pre post actor cell) :
    fieldOf refusalField (post.kernel.cell cell) = 1 := by
  have hv1 : satisfiedVm hash
      (rotateV3WithRecordPin B_RECORD_DIGEST Dregg2.Circuit.Emit.EffectVmEmitRefusal.refusalVmDescriptor)
      (envAt t rd.lastRow) (rd.lastRow == 0) (rd.lastRow + 1 == t.rows.length) :=
    graduateV1_sound hash _ minit mfin maddrs t hside.chip hside.range refusal_rcp_graduable
      hsat rd.lastRow rd.hlastRow
  have hlastt : (rd.lastRow + 1 == t.rows.length) = true := by
    simp only [beq_iff_eq]; exact rd.hlastRowIsLast
  rw [hlastt] at hv1
  have hpin := rotateV3WithRecordPin_pins B_RECORD_DIGEST hash
    Dregg2.Circuit.Emit.EffectVmEmitRefusal.refusalVmDescriptor (envAt t rd.lastRow)
    (rd.lastRow == 0) hv1
  rw [rd.recordLimbDecodes, rd.piAnchored] at hpin
  -- post audit-slot root = digest of `[1]` ⟹ (binds) the slot value is `1`.
  unfold auditSlotRoot at hpin
  have hlist : ([fieldOf refusalField (post.kernel.cell cell)] : List Int) = [(1 : Int)] :=
    ListDigestBindsList auditLeaf compressN hN auditLeaf_injective _ _ hpin
  exact List.head_eq_of_cons_eq hlist

/-- **`refusal_descriptorRefines_sat` — THE CLASS-A CIRCUIT→KERNEL REFINEMENT for refusal.** A satisfying
DEPLOYED `refusalV3` witness + the realizable `RefusalTraceReadout` forces `RefusalSpec`. The
`refusalField := 1` write is forced from the DEPLOYED record pin's `Satisfied2` (`refusal_forced`); the
whole `cell`-map move, guard, log, and 16-field frame are the named residual. Editing `refusalV3` turns
this RED. -/
theorem refusal_descriptorRefines_sat (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash refusalV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId)
    (rd : RefusalTraceReadout compressN hash t pre post actor cell) :
    RefusalSpec pre actor cell post :=
  ⟨rd.guard, rd.cellMapMove, rd.logAdv, rd.frAccounts, rd.frCaps,
    rd.frNullifiers, rd.frRevoked, rd.frCommitments, rd.frBal, rd.frSlotCaveats,
    rd.frFactories, rd.frLifecycle, rd.frDeathCert, rd.frDelegate, rd.frDelegations,
    rd.frDelegationEpoch, rd.frDelegationEpochAt, rd.frHeaps⟩

/-- **CLASS-A TOOTH — a frozen-audit-slot refusal forgery is UNSAT.** A readout whose post `cell` refusal
slot is NOT `1` cannot ride a satisfying `refusalV3` witness — the deployed record pin bites. -/
theorem refusal_sat_rejects_unwritten (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash refusalV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId)
    (rd : RefusalTraceReadout compressN hash t pre post actor cell)
    (hwrong : fieldOf refusalField (post.kernel.cell cell) ≠ 1) :
    False :=
  hwrong (refusal_forced compressN hN hash hside hsat pre post actor cell rd)

/-! ### receiptArchive — Class A from the DEPLOYED disc gate (`receiptArchiveV3`, AFTER disc = Archived).

GAP-1 RECONCILIATION. The deployed `apply_receipt_archive` moves the cell LIFECYCLE side-table to
`Archived` (`c.archive(checkpoint)`, `rotation_witness.rs::lifecycle_felt`); `receiptArchiveV3` realizes
this as a LIVE disc gate forcing the AFTER disc limb to `discArchived (= 4)` — NO trusted post-cell. The
spec the LIGHT CLIENT is owed is therefore the lifecycle-SIDE move (`lifecycle[cell] := Archived`),
EXACTLY the cellUnseal/cellDestroy shape — NOT the record-slot write `Spec.CellStateAudit.
ReceiptArchiveSpec` models for the toy executor (that spec stays as the executor's own bespoke fact;
the DEPLOYED disc is what `PI[38]`/`verify_vm_descriptor2` carries). `ReceiptArchiveLifecycleSpec` is
the reconciled deployed semantics; `receiptArchive_descriptorRefines_sat` forces it from
`Satisfied2 hash receiptArchiveV3` through the disc gate, the LIVE realization of
`RotatedKernelRefinementLifecycleDisc.receiptArchive_disc_forced`. -/

/-- The deployed `Archived` lifecycle discriminant. Reuses `TurnExecutorFull.lcArchived (= 4)` — the
SAME constant the executor's `receiptArchiveChainA` moves to (anti-drift; matches `discArchived`). -/
abbrev lcArchived : Nat := Dregg2.Exec.TurnExecutorFull.lcArchived

/-- The declarative post-`lifecycle` map of a committed deployed receiptArchive. Reuses the
cellstateaudit `archiveLifecycleMap` (so the disc-gate refinement lands EXACTLY the spec
`fullActionStep`/the executor weld consume). -/
abbrev archiveLifecycleMap (k : RecordKernelState) (cell : CellId) : CellId → Nat :=
  Dregg2.Circuit.Spec.CellStateAudit.archiveLifecycleMap k cell

/-- **`ReceiptArchiveLifecycleSpec` — the reconciled DEPLOYED full-state spec of `receiptArchive`.**
Reuses the cellstateaudit `ReceiptArchiveLifecycleSpec` (where the executor weld
`execFullA_receiptArchiveA_iff_lifecycleSpec` lives). The deployed `apply_receipt_archive` moves the
LIFECYCLE side-table to `Archived` (NOT a record slot); the three-leg `auditGuard`; every non-`lifecycle`
kernel component frozen (INCLUDING the `cell` record map). The spec the disc gate forces. -/
abbrev ReceiptArchiveLifecycleSpec (s : RecChainedState) (actor cell : CellId)
    (s' : RecChainedState) : Prop :=
  Dregg2.Circuit.Spec.CellStateAudit.ReceiptArchiveLifecycleSpec s actor cell s'

/-- **`ReceiptArchiveTraceReadout`** — the realizable circuit-witness extraction for receiptArchive, the
`cellUnseal` `CellUnsealTraceReadout` analog: the designated ACTIVE receiptArchive row + its selector
fact + the realizable disc-limb decode (the committed AFTER disc limb IS the post lifecycle discriminant
felt) + the whole-map / guard / log / 16-field residual. The disc GATE is NOT a field — it is FORCED from
`Satisfied2 hash receiptArchiveV3` (`receiptArchive_forced`). -/
structure ReceiptArchiveTraceReadout (hash : List ℤ → ℤ)
    (t : VmTrace) (pre post : RecChainedState) (actor cell : CellId) : Type where
  row : Nat
  hrow : row < t.rows.length
  hrowNotLast : row + 1 ≠ t.rows.length
  hsel : (envAt t row).loc Dregg2.Circuit.Emit.EffectVmEmitReceiptArchive.SEL_RECEIPT_ARCHIVE_RT = 1
  -- the realizable seam: the committed AFTER disc TRACE limb IS the post lifecycle discriminant cast to ℤ.
  discLimbDecodes :
    (envAt t row).loc
      (afterDiscCol
        Dregg2.Circuit.Emit.EffectVmEmitReceiptArchive.receiptArchiveActorVmDescriptor.traceWidth)
      = ((post.kernel.lifecycle cell : Nat) : ℤ)
  frameOther : ∀ c, c ≠ cell → post.kernel.lifecycle c = pre.kernel.lifecycle c
  guard : auditGuard pre actor cell
  logAdv : post.log = { actor := actor, src := cell, dst := cell, amt := 0 } :: pre.log
  frAccounts : post.kernel.accounts = pre.kernel.accounts
  frCell : post.kernel.cell = pre.kernel.cell
  frCaps : post.kernel.caps = pre.kernel.caps
  frNullifiers : post.kernel.nullifiers = pre.kernel.nullifiers
  frRevoked : post.kernel.revoked = pre.kernel.revoked
  frCommitments : post.kernel.commitments = pre.kernel.commitments
  frBal : post.kernel.bal = pre.kernel.bal
  frSlotCaveats : post.kernel.slotCaveats = pre.kernel.slotCaveats
  frFactories : post.kernel.factories = pre.kernel.factories
  frDeathCert : post.kernel.deathCert = pre.kernel.deathCert
  frDelegate : post.kernel.delegate = pre.kernel.delegate
  frDelegations : post.kernel.delegations = pre.kernel.delegations
  frDelegationEpoch : post.kernel.delegationEpoch = pre.kernel.delegationEpoch
  frDelegationEpochAt : post.kernel.delegationEpochAt = pre.kernel.delegationEpochAt
  frHeaps : post.kernel.heaps = pre.kernel.heaps

/-- `receiptArchiveV3`'s underlying disc-gated descriptor is graduable. -/
theorem receiptArchive_disc_graduable :
    graduable (rotateV3WithDiscGate
      Dregg2.Circuit.Emit.EffectVmEmitReceiptArchive.SEL_RECEIPT_ARCHIVE_RT none discArchived
      Dregg2.Circuit.Emit.EffectVmEmitReceiptArchive.receiptArchiveActorVmDescriptor) = true := by decide

/-- **`receiptArchive_forced` — the archive (`lifecycle := Archived`) is FORCED by `receiptArchiveV3`.**
The committed AFTER disc limb is pinned to `discArchived (= 4)` by the LIVE disc gate, and the readout's
`discLimbDecodes` identifies that limb with the post lifecycle discriminant — so the discriminant is
`4 = lcArchived`. Editing `receiptArchiveV3`'s disc gate turns this RED. -/
theorem receiptArchive_forced (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash receiptArchiveV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId)
    (rd : ReceiptArchiveTraceReadout hash t pre post actor cell) :
    post.kernel.lifecycle cell = lcArchived := by
  have hv1 : satisfiedVm hash
      (rotateV3WithDiscGate Dregg2.Circuit.Emit.EffectVmEmitReceiptArchive.SEL_RECEIPT_ARCHIVE_RT none
        discArchived Dregg2.Circuit.Emit.EffectVmEmitReceiptArchive.receiptArchiveActorVmDescriptor)
      (envAt t rd.row) (rd.row == 0) (rd.row + 1 == t.rows.length) :=
    graduateV1_sound hash _ minit mfin maddrs t hside.chip hside.range receiptArchive_disc_graduable
      hsat rd.row rd.hrow
  have hlastf : (rd.row + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact rd.hrowNotLast
  rw [hlastf] at hv1
  have hlimb : (envAt t rd.row).loc
      (afterDiscCol
        Dregg2.Circuit.Emit.EffectVmEmitReceiptArchive.receiptArchiveActorVmDescriptor.traceWidth)
        = discArchived :=
    rotateV3WithDiscGate_forces_after _ _ _ hash _ (envAt t rd.row) (rd.row == 0) false rfl rd.hsel hv1
  have hcast : ((post.kernel.lifecycle cell : Nat) : ℤ) = ((lcArchived : Nat) : ℤ) := by
    rw [← rd.discLimbDecodes, hlimb]; rfl
  exact_mod_cast hcast

/-- **`receiptArchive_forced_map` — the post lifecycle MAP is `archiveLifecycleMap` (Class A, whole
map).** -/
theorem receiptArchive_forced_map (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash receiptArchiveV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId)
    (rd : ReceiptArchiveTraceReadout hash t pre post actor cell) :
    post.kernel.lifecycle = archiveLifecycleMap pre.kernel cell := by
  have hcell : post.kernel.lifecycle cell = lcArchived :=
    receiptArchive_forced hash hside hsat pre post actor cell rd
  funext c
  show post.kernel.lifecycle c = (setLifecycle pre.kernel cell lcArchived).lifecycle c
  show post.kernel.lifecycle c = (if c = cell then lcArchived else pre.kernel.lifecycle c)
  by_cases hc : c = cell
  · subst hc; rw [if_pos rfl]; exact hcell
  · rw [if_neg hc]; exact rd.frameOther c hc

/-- **`receiptArchive_descriptorRefines_sat` — THE CLASS-A CIRCUIT→KERNEL REFINEMENT for receiptArchive.**
A satisfying DEPLOYED `receiptArchiveV3` witness + the realizable `ReceiptArchiveTraceReadout` forces the
reconciled `ReceiptArchiveLifecycleSpec` (`lifecycle := Archived` side-table move). The write is forced
from the DEPLOYED disc gate's `Satisfied2` (`receiptArchive_forced_map`) — editing `receiptArchiveV3`
turns this RED. This is the deployed-semantics reconciliation of GAP 1: the spec the light client is owed
is the lifecycle-side move the disc gate enforces, NOT the toy executor's record-slot write. -/
theorem receiptArchive_descriptorRefines_sat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash receiptArchiveV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId)
    (rd : ReceiptArchiveTraceReadout hash t pre post actor cell) :
    ReceiptArchiveLifecycleSpec pre actor cell post := by
  refine ⟨rd.guard, ?_, rd.logAdv, rd.frAccounts, rd.frCell, rd.frCaps,
    rd.frNullifiers, rd.frRevoked, rd.frCommitments, rd.frBal, rd.frSlotCaveats,
    rd.frFactories, rd.frDeathCert, rd.frDelegate, rd.frDelegations,
    rd.frDelegationEpoch, rd.frDelegationEpochAt, rd.frHeaps⟩
  exact receiptArchive_forced_map hash hside hsat pre post actor cell rd

/-- **CLASS-A TOOTH — a wrong-after-disc receiptArchive forgery is UNSAT.** A readout whose post `cell`
lifecycle is NOT `lcArchived` (a frozen disc, a wrong-disc claim) cannot ride a satisfying
`receiptArchiveV3` witness — the DEPLOYED disc gate pins the archive. -/
theorem receiptArchive_sat_rejects_wrong_after (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash receiptArchiveV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId)
    (rd : ReceiptArchiveTraceReadout hash t pre post actor cell)
    (hwrong : post.kernel.lifecycle cell ≠ lcArchived) :
    False :=
  hwrong (receiptArchive_forced hash hside hsat pre post actor cell rd)

/-! ## §4 — NON-VACUITY: the new roots + gates are load-bearing (no carrier secretly `True`). -/

private def cNC : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 1000003 + x) (xs.length : ℤ)

private def liveK : RecordKernelState :=
  { accounts := {}, cell := fun _ => .int 0, caps := default, lifecycle := fun _ => lcLive }
private def cell0 : CellId := 0

-- LIFECYCLE (unseal/destroy): the Destroyed entry's root DIFFERS from the Live entry's root.
#guard decide (lifecycleRoot cNC (setLifecycle liveK cell0 lcDestroyed) cell0
             = lifecycleRoot cNC liveK cell0) == false
-- ...and the Live (unseal target) root DIFFERS from the Sealed root.
#guard decide (lifecycleRoot cNC (setLifecycle liveK cell0 lcLive) cell0
             = lifecycleRoot cNC (setLifecycle liveK cell0 lcSealed) cell0) == false

-- ARCHIVE (receiptArchive): the Archived(4) lifecycle DIFFERS from Live and Sealed (the disc move is
-- not a no-op — a frozen-disc archive forgery moves the discriminant off the gate's mandated value).
#guard decide ((setLifecycle liveK cell0 lcArchived).lifecycle cell0
             = (setLifecycle liveK cell0 lcLive).lifecycle cell0) == false
#guard decide ((setLifecycle liveK cell0 lcArchived).lifecycle cell0
             = (setLifecycle liveK cell0 lcSealed).lifecycle cell0) == false
-- the reconciled deployed disc target IS the LifecycleDisc/RotationV3 Archived constant (anti-drift).
#guard lcArchived == 4
#guard decide ((discArchived : ℤ) = ((lcArchived : Nat) : ℤ))

-- DEATH-CERT: binding a cert (4242) MOVES the death-cert root (a `:= 0` stub would collapse this).
#guard decide (deathCertRoot cNC
                 { liveK with deathCert := fun c => if c = cell0 then 4242 else liveK.deathCert c } cell0
             = deathCertRoot cNC liveK cell0) == false
-- the death-cert leaf is injective on the toy domain.
#guard decide (lifecycleLeaf 4242 = lifecycleLeaf 0) == false

-- AUDIT SLOT: the `f := 1` root DIFFERS from an unwritten (0) slot root (the gate is not a no-op).
#guard decide (listDigest auditLeaf cNC [(1 : Int)]
             = listDigest auditLeaf cNC [(0 : Int)]) == false
-- the audit leaf is injective on the toy domain.
#guard decide (auditLeaf 1 = auditLeaf 0) == false

/-! ## §5 — axiom-hygiene tripwires. -/

#assert_axioms lifecycleSetForced
#assert_axioms unsealMapForced
#assert_axioms cellUnseal_lifecycle_forced
#assert_axioms cellUnseal_descriptorRefines
#assert_axioms cellUnseal_descriptorRefines_execFullA
#assert_axioms cellUnseal_descriptorRefines_rejects_unrevived
#assert_axioms cellUnseal_descriptorRefines_rejects_wrong_map
#assert_axioms deathCertRoot_binds
#assert_axioms deathCertSetForced
#assert_axioms cellDestroy_lifecycle_forced
#assert_axioms cellDestroy_deathCert_forced
#assert_axioms cellDestroy_descriptorRefines
#assert_axioms cellDestroy_descriptorRefines_execFullA
#assert_axioms cellDestroy_descriptorRefines_rejects_undestroyed
#assert_axioms cellDestroy_descriptorRefines_rejects_wrong_cert
#assert_axioms auditLeaf_injective
#assert_axioms auditSlotRoot_binds
#assert_axioms auditSlotForced
#assert_axioms audit_slot_forced
#assert_axioms refusal_descriptorRefines
#assert_axioms refusal_descriptorRefines_execFullA
#assert_axioms receiptArchive_descriptorRefines
#assert_axioms receiptArchive_descriptorRefines_recordStep
#assert_axioms audit_descriptorRefines_rejects_unwritten
-- CLASS-A (DEPLOYED-descriptor-forced) tripwires.
#assert_axioms cellUnseal_disc_graduable
#assert_axioms cellUnseal_forced
#assert_axioms cellUnseal_forced_map
#assert_axioms cellUnseal_descriptorRefines_sat
#assert_axioms cellUnseal_sat_rejects_unrevived
#assert_axioms cellDestroy_disc_graduable
#assert_axioms cellDestroy_lc_forced
#assert_axioms cellDestroyDiscGate_pins_record
#assert_axioms cellDestroy_dc_forced
#assert_axioms cellDestroy_descriptorRefines_sat
#assert_axioms cellDestroy_sat_rejects_resurrection
#assert_axioms cellDestroy_sat_rejects_wrong_cert
#assert_axioms refusal_rcp_graduable
#assert_axioms refusal_forced
#assert_axioms refusal_descriptorRefines_sat
#assert_axioms refusal_sat_rejects_unwritten
#assert_axioms receiptArchive_disc_graduable
#assert_axioms receiptArchive_forced
#assert_axioms receiptArchive_forced_map
#assert_axioms receiptArchive_descriptorRefines_sat
#assert_axioms receiptArchive_sat_rejects_wrong_after

end Dregg2.Circuit.RotatedKernelRefinementLifecycle
