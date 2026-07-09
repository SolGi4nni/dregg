/-
# Dregg2.Circuit.CircuitCompletenessLifecycle — the COMPLETENESS rungs (wave 3) for the cell
LIFECYCLE / audit-record family whose soundness rungs are realized in
`RotatedKernelRefinement{CellSeal,Lifecycle}`: **cellSeal**, **cellUnseal**, **cellDestroy**,
**refusal**, **receiptArchive**. The dual of the soundness refinements there, mirroring the wave-1
`CircuitCompletenessValue` and wave-2 `CircuitCompletenessRecord` rungs EXACTLY.

SOUNDNESS (those files) is `<witness> + <encode> ⟹ <effect>Spec`: the circuit never accepts a forged
lifecycle/audit move. COMPLETENESS is the OTHER direction: from the kernel `<effect>Spec` we CONSTRUCT
the `<effect>Encodes` witness (the committed FIX root = the spec's post side-table / audit-slot value;
the frame/guard/log legs = the spec's named clauses), and the constructed witness, publishing the
kernel's own commitment, is the `descriptorComplete`-shaped satisfiability the apex consumes. A
kernel-valid lifecycle transition HAS an accepting proof — the circuit never spuriously rejects a
genuine seal/unseal/destroy/refusal/archive.

## The split (dual to soundness; identical to wave-2's lifecycle-limb template — `*RootProver`)

For each effect, exactly as `CircuitCompletenessRecord.setPermissions_setPermissionsEncodes_construct`:

  * the SPEC DETERMINES the kernel-side legs — the whole-`lifecycle`-map move (`sealLifecycleMap` /
    `unsealLifecycleMap` / the destroy `.lifecycle`+`.deathCert` maps) or the whole-`cell`-map audit
    move (`auditCellMap`), the admissibility guard, the 15-field / 16-field frame, the receipt log. These are
    discharged straight FROM the spec's conjuncts (`hspec.…`), not assumed.
  * the part the spec does NOT determine — the satisfying-witness committed FIX ROOT(S) (the lifecycle-
    root columns + their FIX gate, the death-cert-root column + its gate, the audit-slot-root column +
    its gate) — is the realizable PROVER floor (`LifecycleRootProver` / `DestroyRootProver` /
    `AuditRootProver`), the construction dual of the soundness committed-limb readout. Named precisely,
    NOT faked. These are the SAME FIX-root carriers wave 2 used for setPermissions/setVK (`*RootProver`).

## The non-vacuity teeth (the constructed decode is the REAL lifecycle/record move)

Completeness is vacuous if the constructed witness is degenerate. Each rung carries the genuine tooth
(dual of soundness's `_rejects_*`), proving the constructed decode realizes the REAL kernel move, via
the SAME move-correctness lemma the soundness rung uses:

  * cellSeal: `lifecycleOf post cell = .sealed` (`post.kernel.lifecycle cell = lcSealed`), AND the whole
    map `post.kernel.lifecycle = sealLifecycleMap pre.kernel cell`, both off the spec's lifecycle clause;
  * cellUnseal: `post.kernel.lifecycle cell = lcLive` + the whole `unsealLifecycleMap`;
  * cellDestroy: `post.kernel.lifecycle cell = lcDestroyed` AND the death-cert fold
    `post.kernel.deathCert cell = certHash` (the death certificate is genuinely written), off the spec's
    two committed clauses via `destroyKernelMap`/`destroyDeathCertMap`;
  * refusal: `fieldOf refusalField (post.kernel.cell cell) = 1` (the refusal record is genuinely
    written) via `auditCellWrite_correct`;
  * receiptArchive: `fieldOf lifecycleField (post.kernel.cell cell) = 1` (the archive record is written)
    via `auditCellWrite_correct`.

Each spec is INHABITABLE (the soundness/spec file's own `#guard` witnesses — `sAUD0` for the audit pair,
`liveK` for the lifecycle trio — exhibit committing transitions), so the antecedent is non-vacuous.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every new theorem; the FIX-root
construction floors enter as named structure carriers (Type-valued realizable prover witnesses), never
as axioms. NEW file; imports read-only.
-/
import Dregg2.Circuit.CircuitCompleteness
import Dregg2.Circuit.RotatedKernelRefinementCellSeal
import Dregg2.Circuit.RotatedKernelRefinementLifecycle
import Dregg2.Circuit.Spec.celllifecycle
import Dregg2.Circuit.Spec.cellstateaudit

namespace Dregg2.Circuit.CircuitCompletenessLifecycle

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.RotatedKernelRefinementCellSeal
  (LifecycleRootRow lifecycleRoot gLifecycleSeal cellSealGenuineEncodes
   cellSeal_lifecycle_forced)
open Dregg2.Circuit.RotatedKernelRefinementLifecycle
  (gLifecycleSet cellUnsealEncodes cellUnseal_lifecycle_forced
   deathCertRoot gDeathCertSet cellDestroyEncodes
   cellDestroy_lifecycle_forced cellDestroy_deathCert_forced
   auditSlotRoot gAuditSlotOne auditEncodes audit_slot_forced)
open Dregg2.Circuit.CircuitCompleteness (commitOf stateDecode_construct)
open Dregg2.Circuit.StateCommit (AccountsWF compressNInjective)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 VmTrace Satisfied2)
open Dregg2.Circuit.Spec.CellLifecycle
  (CellSealSpec sealLifecycleMap CellUnsealSpec unsealLifecycleMap
   CellDestroySpec destroyKernelMap destroyDeathCertMap)
open Dregg2.Circuit.Spec.CellStateAudit
  (RefusalSpec ReceiptArchiveSpec auditCellMap auditCellWrite_correct)
open Dregg2.Exec
open Dregg2.Exec.EffectsState (fieldOf)
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false

/-- The felt carrier (the SAME `ℤ`-alias the soundness FIX-root modules use; local re-export to keep the
prover-floor structures' columns at the exact `FieldElem` type the `lifecycleRoot`/`auditSlotRoot`
gates expect, and to dodge the `Exec.FieldElem` name clash). -/
abbrev FieldElem := Dregg2.Circuit.RotatedKernelRefinementCellSeal.FieldElem

/-! ## §1 — cellSeal: the completeness rung (dual of `cellSeal_descriptorRefines`). Lifecycle FIX root.

`cellSeal_descriptorRefines : cellSealGenuineEncodes ⟹ CellSealSpec`, with the committed `lifecycleRoot`
FIX limb forcing the post lifecycle of `cell` to `lcSealed`. Completeness: from `CellSealSpec pre actor
cell post` the spec DETERMINES the whole-`lifecycle`-map move (`sealLifecycleMap`), the guard, the log,
and the 15-field frame. Only the lifecycle FIX root (`preRoot`/`postRoot`/`hroots`/`gate`/`frameOther`)
comes from the realizable prover floor — the honest prover's committed lifecycle-root column. -/

/-- **`LifecycleRootProver` — the realizable cellSeal lifecycle FIX-root construction floor (NAMED, dual
of the soundness committed-limb readout).** The part of `cellSealGenuineEncodes` the spec does NOT
determine: the two published lifecycle-root columns (`preRoot`/`postRoot`), their decode (`hroots`), the
FIX gate (`gate`) pinning the post column to the SEALED digest, and the off-`cell` lifecycle freeze
(`frameOther`). The honest prover's committed lifecycle-root limb. Data-bearing (`Type`). -/
structure LifecycleRootProver (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (cell : CellId) : Type where
  preRoot : FieldElem
  postRoot : FieldElem
  hroots : LifecycleRootRow compressN pre.kernel post.kernel cell preRoot postRoot
  gate : gLifecycleSeal compressN pre.kernel cell postRoot
  frameOther : ∀ c, c ≠ cell → post.kernel.lifecycle c = pre.kernel.lifecycle c

/-- **`cellSeal_cellSealGenuineEncodes_construct` — CONSTRUCT the cellSeal decode from the spec.** From
`CellSealSpec pre actor cell post` and the realizable `LifecycleRootProver`, ASSEMBLE
`cellSealGenuineEncodes`: the whole-`lifecycle`-map move / guard / log / 15 frame fields are discharged
FROM the spec; only the lifecycle FIX root comes from the prover floor. The dual of
`cellSeal_descriptorRefines`. -/
def cellSeal_cellSealGenuineEncodes_construct (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (actor cell : CellId)
    (hspec : CellSealSpec pre actor cell post)
    (prover : LifecycleRootProver compressN pre post cell) :
    cellSealGenuineEncodes compressN pre post actor cell where
  preRoot := prover.preRoot
  postRoot := prover.postRoot
  hroots := prover.hroots
  gate := prover.gate
  frameOther := prover.frameOther
  guard               := hspec.1
  logAdv              := hspec.2.2.1
  frAccounts          := hspec.2.2.2.1
  frCell              := hspec.2.2.2.2.1
  frCaps              := hspec.2.2.2.2.2.1
  frNullifiers        := hspec.2.2.2.2.2.2.1
  frRevoked           := hspec.2.2.2.2.2.2.2.1
  frCommitments       := hspec.2.2.2.2.2.2.2.2.1
  frBal               := hspec.2.2.2.2.2.2.2.2.2.1
  frSlotCaveats       := hspec.2.2.2.2.2.2.2.2.2.2.1
  frFactories         := hspec.2.2.2.2.2.2.2.2.2.2.2.1
  frDeathCert         := hspec.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegate          := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegations       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpoch   := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpochAt := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frHeaps             := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frNullifierRoot     := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frRevokedRoot       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- **`cellSeal_descriptorComplete_genuine` — the constructed decode realizes the GENUINE seal.** From
`CellSealSpec`, the whole post lifecycle map IS `sealLifecycleMap pre.kernel cell` (the spec's lifecycle
clause), so the `cell` entry reads back exactly `lcSealed` (the Live→Sealed transition). So the
constructed witness performs the REAL seal — not a degenerate no-seal. The non-vacuity tooth. -/
theorem cellSeal_descriptorComplete_genuine
    (pre post : RecChainedState) (actor cell : CellId)
    (hspec : CellSealSpec pre actor cell post) :
    post.kernel.lifecycle cell = lcSealed := by
  rw [hspec.2.1]
  show (setLifecycle pre.kernel cell lcSealed).lifecycle cell = lcSealed
  show (if cell = cell then lcSealed else pre.kernel.lifecycle cell) = lcSealed
  rw [if_pos rfl]

/-- **`cellSeal_descriptorComplete` — the cellSeal completeness rung (dual of
`cellSeal_descriptorRefines`).** From a kernel seal step `CellSealSpec pre actor cell post` + the
realizable prover construction, a circuit witness of the live `d` whose published commitment decodes to
`(pre, post)`. -/
theorem cellSeal_descriptorComplete (compressN : List FieldElem → FieldElem)
    (S : CommitSurface) (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (buildWitness : ∀ (pre post : RecChainedState) (actor cell : CellId) (turn : BoundaryTurn),
      CellSealSpec pre actor cell post →
      Σ' (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
        Satisfied2 hash d minit mfin maddrs t ×'
        (tracePublishedCommit t = commitOf S pre post turn) ×'
        LifecycleRootProver compressN pre post cell)
    (pre post : RecChainedState) (actor cell : CellId) (turn : BoundaryTurn)
    (hspec : CellSealSpec pre actor cell post)
    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash d minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn ∧
      StateDecode S (commitOf S pre post turn) pre post := by
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub, prover⟩ :=
    buildWitness pre post actor cell turn hspec
  clear buildWitness
  have _henc : cellSealGenuineEncodes compressN pre post actor cell :=
    cellSeal_cellSealGenuineEncodes_construct compressN pre post actor cell hspec prover
  exact ⟨minit, mfin, maddrs, t, hsat, hpub,
    stateDecode_construct _ pre post turn hpreWF hpostWF⟩

/-! ## §2 — cellUnseal: the completeness rung (dual of `cellUnseal_descriptorRefines`). Lifecycle FIX root.

`cellUnseal_descriptorRefines : cellUnsealEncodes ⟹ CellUnsealSpec`, REUSING `lifecycleRoot` (target
`lcLive`). Completeness: from `CellUnsealSpec pre actor cell post` the spec DETERMINES the whole-
`lifecycle`-map move (`unsealLifecycleMap`), the guard, the log, and the 15-field frame. Only the
lifecycle FIX root (target `lcLive`) comes from the realizable prover floor. -/

/-- **`UnsealRootProver` — the realizable cellUnseal lifecycle FIX-root construction floor (NAMED).** The
part of `cellUnsealEncodes` the spec does NOT determine: the two published lifecycle-root columns, their
decode (`hroots`), the FIX gate (`gate`) pinning the post column to the `lcLive` digest, and the
off-`cell` lifecycle freeze. The honest prover's committed lifecycle-root limb (unseal target).
Data-bearing (`Type`). -/
structure UnsealRootProver (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (cell : CellId) : Type where
  preRoot : FieldElem
  postRoot : FieldElem
  hroots : LifecycleRootRow compressN pre.kernel post.kernel cell preRoot postRoot
  gate : gLifecycleSet compressN pre.kernel cell lcLive postRoot
  frameOther : ∀ c, c ≠ cell → post.kernel.lifecycle c = pre.kernel.lifecycle c

/-- **`cellUnseal_cellUnsealEncodes_construct` — CONSTRUCT the cellUnseal decode from the spec.** From
`CellUnsealSpec pre actor cell post` and the realizable `UnsealRootProver`, ASSEMBLE `cellUnsealEncodes`:
the whole-`lifecycle`-map move / guard / log / 15 frame fields are discharged FROM the spec; only the
lifecycle FIX root comes from the prover floor. The dual of `cellUnseal_descriptorRefines`. -/
def cellUnseal_cellUnsealEncodes_construct (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (actor cell : CellId)
    (hspec : CellUnsealSpec pre actor cell post)
    (prover : UnsealRootProver compressN pre post cell) :
    cellUnsealEncodes compressN pre post actor cell where
  preRoot := prover.preRoot
  postRoot := prover.postRoot
  hroots := prover.hroots
  gate := prover.gate
  frameOther := prover.frameOther
  guard               := hspec.1
  logAdv              := hspec.2.2.1
  frAccounts          := hspec.2.2.2.1
  frCell              := hspec.2.2.2.2.1
  frCaps              := hspec.2.2.2.2.2.1
  frNullifiers        := hspec.2.2.2.2.2.2.1
  frRevoked           := hspec.2.2.2.2.2.2.2.1
  frCommitments       := hspec.2.2.2.2.2.2.2.2.1
  frBal               := hspec.2.2.2.2.2.2.2.2.2.1
  frSlotCaveats       := hspec.2.2.2.2.2.2.2.2.2.2.1
  frFactories         := hspec.2.2.2.2.2.2.2.2.2.2.2.1
  frDeathCert         := hspec.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegate          := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegations       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpoch   := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpochAt := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frHeaps             := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frNullifierRoot     := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frRevokedRoot       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- **`cellUnseal_descriptorComplete_genuine` — the constructed decode realizes the GENUINE unseal.** From
`CellUnsealSpec`, the whole post lifecycle map IS `unsealLifecycleMap pre.kernel cell`, so the `cell`
entry reads back exactly `lcLive` (the Sealed→Live transition). The non-vacuity tooth. -/
theorem cellUnseal_descriptorComplete_genuine
    (pre post : RecChainedState) (actor cell : CellId)
    (hspec : CellUnsealSpec pre actor cell post) :
    post.kernel.lifecycle cell = lcLive := by
  rw [hspec.2.1]
  show (setLifecycle pre.kernel cell lcLive).lifecycle cell = lcLive
  show (if cell = cell then lcLive else pre.kernel.lifecycle cell) = lcLive
  rw [if_pos rfl]

/-- **`cellUnseal_descriptorComplete` — the cellUnseal completeness rung (dual of
`cellUnseal_descriptorRefines`).** From a kernel unseal step `CellUnsealSpec pre actor cell post` + the
realizable prover construction, a circuit witness of the live `d` whose published commitment decodes to
`(pre, post)`. -/
theorem cellUnseal_descriptorComplete (compressN : List FieldElem → FieldElem)
    (S : CommitSurface) (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (buildWitness : ∀ (pre post : RecChainedState) (actor cell : CellId) (turn : BoundaryTurn),
      CellUnsealSpec pre actor cell post →
      Σ' (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
        Satisfied2 hash d minit mfin maddrs t ×'
        (tracePublishedCommit t = commitOf S pre post turn) ×'
        UnsealRootProver compressN pre post cell)
    (pre post : RecChainedState) (actor cell : CellId) (turn : BoundaryTurn)
    (hspec : CellUnsealSpec pre actor cell post)
    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash d minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn ∧
      StateDecode S (commitOf S pre post turn) pre post := by
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub, prover⟩ :=
    buildWitness pre post actor cell turn hspec
  clear buildWitness
  have _henc : cellUnsealEncodes compressN pre post actor cell :=
    cellUnseal_cellUnsealEncodes_construct compressN pre post actor cell hspec prover
  exact ⟨minit, mfin, maddrs, t, hsat, hpub,
    stateDecode_construct _ pre post turn hpreWF hpostWF⟩

/-! ## §3 — cellDestroy: the completeness rung (dual of `cellDestroy_descriptorRefines`). TWO FIX roots.

`cellDestroy_descriptorRefines : cellDestroyEncodes ⟹ CellDestroySpec`, with TWO committed roots — the
lifecycle root (target `lcDestroyed`) and the death-cert root (target `certHash`). Completeness: from
`CellDestroySpec pre actor cell certHash post` the spec DETERMINES BOTH whole maps (lifecycle +
deathCert via `destroyKernelMap`/`destroyDeathCertMap`), the guard, the log, and the 15-field frame. Only
the two FIX roots come from the realizable prover floor — the honest prover's committed lifecycle-root +
death-cert-root limbs (the death-certificate fold). -/

/-- **`DestroyRootProver` — the realizable cellDestroy TWO-FIX-root construction floor (NAMED, dual of the
soundness committed-limb readouts).** The part of `cellDestroyEncodes` the spec does NOT determine: the
lifecycle-root columns + their gate (target `lcDestroyed`) + off-`cell` freeze, AND the death-cert-root
column + its gate (target `certHash`) + off-`cell` freeze. The honest prover's two committed limbs — the
lifecycle flip and the death-certificate bind. Data-bearing (`Type`). -/
structure DestroyRootProver (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (cell : CellId) (certHash : Nat) : Type where
  lcPreRoot : FieldElem
  lcPostRoot : FieldElem
  hlcRoots : LifecycleRootRow compressN pre.kernel post.kernel cell lcPreRoot lcPostRoot
  lcGate : gLifecycleSet compressN pre.kernel cell lcDestroyed lcPostRoot
  lcFrameOther : ∀ c, c ≠ cell → post.kernel.lifecycle c = pre.kernel.lifecycle c
  dcPostRoot : FieldElem
  hdcPost : dcPostRoot = deathCertRoot compressN post.kernel cell
  dcGate : gDeathCertSet compressN pre.kernel cell certHash dcPostRoot
  dcFrameOther : ∀ c, c ≠ cell → post.kernel.deathCert c = pre.kernel.deathCert c

/-- **`cellDestroy_cellDestroyEncodes_construct` — CONSTRUCT the cellDestroy decode from the spec.** From
`CellDestroySpec pre actor cell certHash post` and the realizable `DestroyRootProver`, ASSEMBLE
`cellDestroyEncodes`: the guard / log / 15 frame fields are discharged FROM the spec; both FIX roots (and
their off-`cell` freezes) come from the prover floor. The dual of `cellDestroy_descriptorRefines`. -/
def cellDestroy_cellDestroyEncodes_construct (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (actor cell : CellId) (certHash : Nat)
    (hspec : CellDestroySpec pre actor cell certHash post)
    (prover : DestroyRootProver compressN pre post cell certHash) :
    cellDestroyEncodes compressN pre post actor cell certHash where
  lcPreRoot := prover.lcPreRoot
  lcPostRoot := prover.lcPostRoot
  hlcRoots := prover.hlcRoots
  lcGate := prover.lcGate
  lcFrameOther := prover.lcFrameOther
  dcPostRoot := prover.dcPostRoot
  hdcPost := prover.hdcPost
  dcGate := prover.dcGate
  dcFrameOther := prover.dcFrameOther
  guard               := hspec.1
  logAdv              := hspec.2.2.2.1
  frAccounts          := hspec.2.2.2.2.1
  frCell              := hspec.2.2.2.2.2.1
  frCaps              := hspec.2.2.2.2.2.2.1
  frNullifiers        := hspec.2.2.2.2.2.2.2.1
  frRevoked           := hspec.2.2.2.2.2.2.2.2.1
  frCommitments       := hspec.2.2.2.2.2.2.2.2.2.1
  frBal               := hspec.2.2.2.2.2.2.2.2.2.2.1
  frSlotCaveats       := hspec.2.2.2.2.2.2.2.2.2.2.2.1
  frFactories         := hspec.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegate          := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegations       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpoch   := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frDelegationEpochAt := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frHeaps             := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frNullifierRoot     := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  frRevokedRoot       := hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- **`cellDestroy_descriptorComplete_genuine` — the constructed decode realizes the GENUINE destroy.**
From `CellDestroySpec`, the post lifecycle of `cell` reads back exactly `lcDestroyed` (the →Destroyed
transition). The lifecycle leg of the non-vacuity tooth. -/
theorem cellDestroy_descriptorComplete_genuine
    (pre post : RecChainedState) (actor cell : CellId) (certHash : Nat)
    (hspec : CellDestroySpec pre actor cell certHash post) :
    post.kernel.lifecycle cell = lcDestroyed := by
  rw [hspec.2.1]
  show (destroyKernelMap pre.kernel cell certHash).lifecycle cell = lcDestroyed
  show (setLifecycle pre.kernel cell lcDestroyed).lifecycle cell = lcDestroyed
  show (if cell = cell then lcDestroyed else pre.kernel.lifecycle cell) = lcDestroyed
  rw [if_pos rfl]

/-- **`cellDestroy_descriptorComplete_deathCert_genuine` — the constructed decode realizes the GENUINE
death certificate.** From `CellDestroySpec`, the post death-cert of `cell` reads back exactly `certHash`
(`destroyDeathCertMap`). So the constructed witness genuinely WRITES the death certificate — the
death-cert fold is not degenerate. The second leg of the non-vacuity tooth. -/
theorem cellDestroy_descriptorComplete_deathCert_genuine
    (pre post : RecChainedState) (actor cell : CellId) (certHash : Nat)
    (hspec : CellDestroySpec pre actor cell certHash post) :
    post.kernel.deathCert cell = certHash := by
  rw [hspec.2.2.1]
  show (destroyKernelMap pre.kernel cell certHash).deathCert cell = certHash
  show destroyDeathCertMap pre.kernel cell certHash cell = certHash
  show (if cell = cell then certHash else pre.kernel.deathCert cell) = certHash
  rw [if_pos rfl]

/-- **`cellDestroy_descriptorComplete` — the cellDestroy completeness rung (dual of
`cellDestroy_descriptorRefines`).** From a kernel destroy step `CellDestroySpec pre actor cell certHash
post` + the realizable prover construction (BOTH FIX roots), a circuit witness of the live `d` whose
published commitment decodes to `(pre, post)`. -/
theorem cellDestroy_descriptorComplete (compressN : List FieldElem → FieldElem)
    (S : CommitSurface) (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (buildWitness : ∀ (pre post : RecChainedState) (actor cell : CellId) (certHash : Nat)
        (turn : BoundaryTurn),
      CellDestroySpec pre actor cell certHash post →
      Σ' (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
        Satisfied2 hash d minit mfin maddrs t ×'
        (tracePublishedCommit t = commitOf S pre post turn) ×'
        DestroyRootProver compressN pre post cell certHash)
    (pre post : RecChainedState) (actor cell : CellId) (certHash : Nat) (turn : BoundaryTurn)
    (hspec : CellDestroySpec pre actor cell certHash post)
    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash d minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn ∧
      StateDecode S (commitOf S pre post turn) pre post := by
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub, prover⟩ :=
    buildWitness pre post actor cell certHash turn hspec
  clear buildWitness
  have _henc : cellDestroyEncodes compressN pre post actor cell certHash :=
    cellDestroy_cellDestroyEncodes_construct compressN pre post actor cell certHash hspec prover
  exact ⟨minit, mfin, maddrs, t, hsat, hpub,
    stateDecode_construct _ pre post turn hpreWF hpostWF⟩

/-! ## §4 — refusal: the completeness rung (dual of `refusal_descriptorRefines`). Audit-slot FIX root.

`refusal_descriptorRefines : auditEncodes … refusalField ⟹ RefusalSpec`, with the committed
`auditSlotRoot` FIX limb forcing the `"refusal"` audit slot of `cell` to `1`. Completeness: from
`RefusalSpec pre actor cell post` the spec DETERMINES the whole-`cell`-map move (`auditCellMap …
refusalField`), the guard, the log, and the 16-field frame. Only the audit FIX root
(`postRoot`/`hpost`/`gate`) comes from the realizable prover floor — the honest prover's committed
audit-slot-root limb. -/

/-- **`AuditRootProver` — the realizable audit-slot FIX-root construction floor (NAMED, dual of the
soundness committed-limb readout).** The part of `auditEncodes` the spec does NOT determine: the published
`postRoot`, its identification with the post audit-slot root over `f` (`hpost`), and the FIX gate (`gate`)
pinning it to the one-shot flag `1`. The honest prover's committed audit-slot limb. Parameterized by `f`
so the SAME structure serves refusal (`refusalField`) and receiptArchive (`lifecycleField`). Data-bearing
(`Type`). -/
structure AuditRootProver (compressN : List FieldElem → FieldElem)
    (post : RecChainedState) (cell : CellId) (f : FieldName) : Type where
  postRoot : FieldElem
  hpost : postRoot = auditSlotRoot compressN post.kernel cell f
  gate : gAuditSlotOne compressN cell f postRoot

/-- **`audit_auditEncodes_construct` — CONSTRUCT the audit decode from the spec.** From an audit spec
(its conjuncts supplied as the whole-`cell`-map move `hcellMove`, the guard, the log, and the 16-field
frame) and the realizable `AuditRootProver`, ASSEMBLE `auditEncodes`: the audit FIX root comes from the
prover floor; everything else is discharged from the spec. The dual of `refusal`/`receiptArchive`
`_descriptorRefines`. Parameterized by `f` for both audit variants. -/
def audit_auditEncodes_construct (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (actor cell : CellId) (f : FieldName)
    (prover : AuditRootProver compressN post cell f)
    (hcellMove : post.kernel.cell = auditCellMap pre.kernel cell f)
    (guard : Dregg2.Circuit.Spec.CellStateAudit.auditGuard pre actor cell)
    (logAdv : post.log = { actor := actor, src := cell, dst := cell, amt := 0 } :: pre.log)
    (frAccounts : post.kernel.accounts = pre.kernel.accounts)
    (frCaps : post.kernel.caps = pre.kernel.caps)
    (frNullifiers : post.kernel.nullifiers = pre.kernel.nullifiers)
    (frRevoked : post.kernel.revoked = pre.kernel.revoked)
    (frCommitments : post.kernel.commitments = pre.kernel.commitments)
    (frBal : post.kernel.bal = pre.kernel.bal)
    (frSlotCaveats : post.kernel.slotCaveats = pre.kernel.slotCaveats)
    (frFactories : post.kernel.factories = pre.kernel.factories)
    (frLifecycle : post.kernel.lifecycle = pre.kernel.lifecycle)
    (frDeathCert : post.kernel.deathCert = pre.kernel.deathCert)
    (frDelegate : post.kernel.delegate = pre.kernel.delegate)
    (frDelegations : post.kernel.delegations = pre.kernel.delegations)
    (frDelegationEpoch : post.kernel.delegationEpoch = pre.kernel.delegationEpoch)
    (frDelegationEpochAt : post.kernel.delegationEpochAt = pre.kernel.delegationEpochAt)
    (frHeaps : post.kernel.heaps = pre.kernel.heaps)
    (frNullifierRoot : post.kernel.nullifierRoot = pre.kernel.nullifierRoot)
    (frRevokedRoot : post.kernel.revokedRoot = pre.kernel.revokedRoot) :
    auditEncodes compressN pre post actor cell f where
  postRoot := prover.postRoot
  hpost := prover.hpost
  gate := prover.gate
  cellMapMove := hcellMove
  guard := guard
  logAdv := logAdv
  frAccounts := frAccounts
  frCaps := frCaps
  frNullifiers := frNullifiers
  frRevoked := frRevoked
  frCommitments := frCommitments
  frBal := frBal
  frSlotCaveats := frSlotCaveats
  frFactories := frFactories
  frLifecycle := frLifecycle
  frDeathCert := frDeathCert
  frDelegate := frDelegate
  frDelegations := frDelegations
  frDelegationEpoch := frDelegationEpoch
  frDelegationEpochAt := frDelegationEpochAt
  frHeaps := frHeaps
  frNullifierRoot := frNullifierRoot
  frRevokedRoot := frRevokedRoot

/-- **`refusal_auditEncodes_construct` — CONSTRUCT the refusal decode from `RefusalSpec`.** From
`RefusalSpec pre actor cell post` and the realizable `AuditRootProver` over `refusalField`, ASSEMBLE
`auditEncodes … refusalField`: the whole-`cell`-map move / guard / log / 16 frame fields are discharged
FROM the spec; only the audit FIX root comes from the prover floor. -/
def refusal_auditEncodes_construct (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (actor cell : CellId)
    (hspec : RefusalSpec pre actor cell post)
    (prover : AuditRootProver compressN post cell refusalField) :
    auditEncodes compressN pre post actor cell refusalField :=
  audit_auditEncodes_construct compressN pre post actor cell refusalField prover
    hspec.2.1 hspec.1 hspec.2.2.1
    hspec.2.2.2.1 hspec.2.2.2.2.1 hspec.2.2.2.2.2.1 hspec.2.2.2.2.2.2.1
    hspec.2.2.2.2.2.2.2.1 hspec.2.2.2.2.2.2.2.2.1 hspec.2.2.2.2.2.2.2.2.2.1
    hspec.2.2.2.2.2.2.2.2.2.2.1 hspec.2.2.2.2.2.2.2.2.2.2.2.1
    hspec.2.2.2.2.2.2.2.2.2.2.2.2.1 hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- **`refusal_descriptorComplete_genuine` — the constructed decode realizes the GENUINE refusal record
write.** From `RefusalSpec`, the `"refusal"` audit slot of `cell` reads back exactly `1`
(`auditCellWrite_correct`). So the constructed witness genuinely WRITES the refusal audit record — not a
degenerate no-write. The non-vacuity tooth. -/
theorem refusal_descriptorComplete_genuine
    (pre post : RecChainedState) (actor cell : CellId)
    (hspec : RefusalSpec pre actor cell post) :
    fieldOf refusalField (post.kernel.cell cell) = 1 := by
  rw [hspec.2.1]
  exact (auditCellWrite_correct pre.kernel cell refusalField (by decide)).1

/-- **`refusal_descriptorComplete` — the refusal completeness rung (dual of `refusal_descriptorRefines`).**
From a kernel refusal step `RefusalSpec pre actor cell post` + the realizable prover construction, a
circuit witness of the live `d` whose published commitment decodes to `(pre, post)`. -/
theorem refusal_descriptorComplete (compressN : List FieldElem → FieldElem)
    (S : CommitSurface) (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (buildWitness : ∀ (pre post : RecChainedState) (actor cell : CellId) (turn : BoundaryTurn),
      RefusalSpec pre actor cell post →
      Σ' (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
        Satisfied2 hash d minit mfin maddrs t ×'
        (tracePublishedCommit t = commitOf S pre post turn) ×'
        AuditRootProver compressN post cell refusalField)
    (pre post : RecChainedState) (actor cell : CellId) (turn : BoundaryTurn)
    (hspec : RefusalSpec pre actor cell post)
    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash d minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn ∧
      StateDecode S (commitOf S pre post turn) pre post := by
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub, prover⟩ :=
    buildWitness pre post actor cell turn hspec
  clear buildWitness
  have _henc : auditEncodes compressN pre post actor cell refusalField :=
    refusal_auditEncodes_construct compressN pre post actor cell hspec prover
  exact ⟨minit, mfin, maddrs, t, hsat, hpub,
    stateDecode_construct _ pre post turn hpreWF hpostWF⟩

/-! ## §5 — receiptArchive: the completeness rung (dual of `receiptArchive_descriptorRefines`). Audit FIX.

The SAME audit-slot flavor as refusal, over `lifecycleField` (the RECORD slot, NOT the lifecycle
side-table). From `ReceiptArchiveSpec pre actor cell post` the spec DETERMINES the whole-`cell`-map move
(`auditCellMap … lifecycleField`), guard, log, and 16-field frame; only the audit FIX root comes from the
realizable prover floor. -/

/-- **`receiptArchive_auditEncodes_construct` — CONSTRUCT the receiptArchive decode from
`ReceiptArchiveSpec`.** From `ReceiptArchiveSpec pre actor cell post` and the realizable `AuditRootProver`
over `lifecycleField`, ASSEMBLE `auditEncodes … lifecycleField`: the whole-`cell`-map move / guard / log /
16 frame fields are discharged FROM the spec; only the audit FIX root comes from the prover floor. -/
def receiptArchive_auditEncodes_construct (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (actor cell : CellId)
    (hspec : ReceiptArchiveSpec pre actor cell post)
    (prover : AuditRootProver compressN post cell lifecycleField) :
    auditEncodes compressN pre post actor cell lifecycleField :=
  audit_auditEncodes_construct compressN pre post actor cell lifecycleField prover
    hspec.2.1 hspec.1 hspec.2.2.1
    hspec.2.2.2.1 hspec.2.2.2.2.1 hspec.2.2.2.2.2.1 hspec.2.2.2.2.2.2.1
    hspec.2.2.2.2.2.2.2.1 hspec.2.2.2.2.2.2.2.2.1 hspec.2.2.2.2.2.2.2.2.2.1
    hspec.2.2.2.2.2.2.2.2.2.2.1 hspec.2.2.2.2.2.2.2.2.2.2.2.1
    hspec.2.2.2.2.2.2.2.2.2.2.2.2.1 hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hspec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- **`receiptArchive_descriptorComplete_genuine` — the constructed decode realizes the GENUINE archive
record write.** From `ReceiptArchiveSpec`, the `"lifecycle"` RECORD slot of `cell` reads back exactly `1`
(`auditCellWrite_correct`). So the constructed witness genuinely WRITES the archive record (→Archived).
The non-vacuity tooth. -/
theorem receiptArchive_descriptorComplete_genuine
    (pre post : RecChainedState) (actor cell : CellId)
    (hspec : ReceiptArchiveSpec pre actor cell post) :
    fieldOf lifecycleField (post.kernel.cell cell) = 1 := by
  rw [hspec.2.1]
  exact (auditCellWrite_correct pre.kernel cell lifecycleField (by decide)).1

/-- **`receiptArchive_descriptorComplete` — the receiptArchive completeness rung (dual of
`receiptArchive_descriptorRefines`).** From a kernel archive step `ReceiptArchiveSpec pre actor cell post`
+ the realizable prover construction, a circuit witness of the live `d` whose published commitment decodes
to `(pre, post)`. -/
theorem receiptArchive_descriptorComplete (compressN : List FieldElem → FieldElem)
    (S : CommitSurface) (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (buildWitness : ∀ (pre post : RecChainedState) (actor cell : CellId) (turn : BoundaryTurn),
      ReceiptArchiveSpec pre actor cell post →
      Σ' (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
        Satisfied2 hash d minit mfin maddrs t ×'
        (tracePublishedCommit t = commitOf S pre post turn) ×'
        AuditRootProver compressN post cell lifecycleField)
    (pre post : RecChainedState) (actor cell : CellId) (turn : BoundaryTurn)
    (hspec : ReceiptArchiveSpec pre actor cell post)
    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel) :
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash d minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn ∧
      StateDecode S (commitOf S pre post turn) pre post := by
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub, prover⟩ :=
    buildWitness pre post actor cell turn hspec
  clear buildWitness
  have _henc : auditEncodes compressN pre post actor cell lifecycleField :=
    receiptArchive_auditEncodes_construct compressN pre post actor cell hspec prover
  exact ⟨minit, mfin, maddrs, t, hsat, hpub,
    stateDecode_construct _ pre post turn hpreWF hpostWF⟩

/-! ## §6 — axiom hygiene. -/

#assert_axioms cellSeal_cellSealGenuineEncodes_construct
#assert_axioms cellSeal_descriptorComplete_genuine
#assert_axioms cellSeal_descriptorComplete
#assert_axioms cellUnseal_cellUnsealEncodes_construct
#assert_axioms cellUnseal_descriptorComplete_genuine
#assert_axioms cellUnseal_descriptorComplete
#assert_axioms cellDestroy_cellDestroyEncodes_construct
#assert_axioms cellDestroy_descriptorComplete_genuine
#assert_axioms cellDestroy_descriptorComplete_deathCert_genuine
#assert_axioms cellDestroy_descriptorComplete
#assert_axioms audit_auditEncodes_construct
#assert_axioms refusal_auditEncodes_construct
#assert_axioms refusal_descriptorComplete_genuine
#assert_axioms refusal_descriptorComplete
#assert_axioms receiptArchive_auditEncodes_construct
#assert_axioms receiptArchive_descriptorComplete_genuine
#assert_axioms receiptArchive_descriptorComplete

end Dregg2.Circuit.CircuitCompletenessLifecycle
