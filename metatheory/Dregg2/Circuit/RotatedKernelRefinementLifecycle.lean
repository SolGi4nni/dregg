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

/-- The refinement against `execFullA` directly (via `execFullA_receiptArchiveA_iff_spec`). -/
theorem receiptArchive_descriptorRefines_execFullA (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId)
    (henc : auditEncodes compressN pre post actor cell lifecycleField) :
    execFullA pre (.receiptArchiveA actor cell) = some post :=
  (Dregg2.Circuit.Spec.CellStateAudit.execFullA_receiptArchiveA_iff_spec pre actor cell post).mpr
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
#assert_axioms receiptArchive_descriptorRefines_execFullA
#assert_axioms audit_descriptorRefines_rejects_unwritten

end Dregg2.Circuit.RotatedKernelRefinementLifecycle
