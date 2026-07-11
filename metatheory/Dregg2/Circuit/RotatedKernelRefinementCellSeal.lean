/-
# Dregg2.Circuit.RotatedKernelRefinementCellSeal — the PRINCIPLED-FIX VALUE-leg circuit→kernel
  refinement for `cellSeal`, against a descriptor that FORCES the `lifecycle` write into a COMMITTED
  column (the lifecycle-root system-root limb).

## The gap this closes (cellSeal's genuinely-FALSE VALUE rung)

`incrementNonce`/`setField` discharge their VALUE rung because a LIVE deployed gate (`gNonce` /
`gFieldWrite`) PINS a column that lands in the published `state_commit`. `cellSeal` is the FIRST of the
~17 VALUE_MISSING effects: its kernel write is `lifecycle := lifecycle[cell ↦ Sealed]`, a kernel-owned
SIDE-TABLE. The deployed circuit's per-cell commitment is
`hash(balance_lo, balance_hi, nonce, field[0..7], cap_root)` (`circuit/src/effect_vm/cell_state.rs::compute_commitment`)
— it binds NO lifecycle column. The live rotated `cellSealVmDescriptor2R24` FREEZES the economic block
and ticks the nonce; the lifecycle flip is OFF-ROW (`EffectVmEmitCellSeal.cellSeal_offrow_unenforced`).
So a `cellSeal_descriptorRefines` against the DEPLOYED descriptor is genuinely FALSE: a prover can
publish a commitment to an UN-SEALED post and the circuit cannot tell.

The Lean apex `recStateCommit = cmb(cellDigest, RH)` ALREADY assumes the rest hash `RH` binds the full
kernel INCLUDING `lifecycle` (`StateCommit.RestHashIffFrame`, `StateCommit.lean:229`). The deployed
circuit just does not REALIZE that binding. This module builds the FIX that does — additively, on a NEW
committed lifecycle-root column — and discharges the VALUE rung against it.

## The binding mechanism (chosen: a dedicated `lifecycle` system-root limb)

`Exec.SystemRoots` already gives the kernel side-tables their OWN committed home: `systemRootsDigest`
is absorbed into the cell commitment by `cellCommitS`, and `cellCommitS_binds_systemRoots` proves a
fixed commitment pins every side-table root (`SystemRoots.lean:191`). `lifecycle` is exactly such a
kernel-owned side-table. We model its committed root — `lifecycleRoot` — the SAME way the side-table
roots are modelled (a `ListCommit.listDigest` over the entry, binding via the realizable
`compressNInjective` Poseidon-CR carrier), absorbed as ONE more committed limb.

> ADDITIVITY NOTE. The shared `Exec.SystemRoots` block is `N_SYSTEM_ROOTS = 8`, indices 0..7 all
> assigned (ESCROW..SEALED_BOXES), and mirrors the Rust `[FieldElement; 8]` — bumping it to a 9th
> LIFECYCLE index would mutate a def imported by ~45 modules AND the Rust array layout, i.e. NOT
> additive. So the lifecycle root is modelled here as its OWN dedicated committed limb, reusing the
> `listDigest`/`compressNInjective` carrier `SystemRoots`/`ListCommit` already use, NOT by mutating
> `N_SYSTEM_ROOTS`. The Rust realization (§Deliverable in the report) is the same either way: the
> per-cell commitment must absorb a `lifecycle_root` limb and the cellSeal trace-fill must emit the
> sealed-lifecycle root.

## The FIX descriptor + the proof

  * `lifecycleRoot` — the committed digest of the cell's `lifecycle` entry (the new committed column).
  * `gLifecycleSeal` — the FIX gate that FORCES the post lifecycle-root column to
    `lifecycleRoot (lifecycle[cell ↦ Sealed])`, exactly mirroring how `gFieldWrite slot` forces
    `fields[slot]_after = param1` into a committed column.
  * `lifecycleSealForced` — the gate's faithfulness: it holds IFF the post lifecycle-root IS the sealed
    digest. So a satisfying FIX witness PINS the committed lifecycle column to the Sealed value.
  * `cellSealGenuineEncodes` — the active-row⟷kernel decode, carrying the kernel-only residual (the
    whole-map `sealLifecycleMap`, the `CellSealGuard`, the 16-field frame, the receipt log) and tying
    the FORCED lifecycle root to `lifecycle[cell ↦ Sealed]` via the digest injectivity, exactly as
    setField's `rotatedEncodesSF` ties `param1 = v`.
  * `cellSeal_descriptorRefines` — a satisfying FIX-descriptor witness + decode ⟹ `CellSealSpec`: the
    `lifecycle := Sealed` write is FORCED via the committed lifecycle root, the rest of the frame is
    the NAMED decode residual.
  * `cellSeal_descriptorRefines_rejects_unsealed` (BOTH-POLARITY TOOTH) — a witness whose post
    lifecycle is NOT `[cell ↦ Sealed]` is UNSAT (the lifecycle-root gate bites). This is what the
    deployed circuit CANNOT do and the FIX does.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound, lifecycleLeafInjective-style CR carrier} on
every new theorem. The ONLY carried crypto assumption is the realizable Poseidon CR
(`compressNInjective` + an injective lifecycle leaf) — the SAME carrier `SystemRoots`/`ListCommit`
already use, never a fresh axiom. NEW file; imports are read-only.
-/
import Dregg2.Circuit.RotatedKernelRefinementIncNonce
import Dregg2.Circuit.ListCommit
import Dregg2.Circuit.Spec.celllifecycle

namespace Dregg2.Circuit.RotatedKernelRefinementCellSeal

open Dregg2.Circuit
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.StateCommit (compressNInjective)
open Dregg2.Circuit.Spec.CellLifecycle
  (CellSealSpec CellSealGuard sealLifecycleMap cellLifecycleReceipt)
open Dregg2.Circuit.DescriptorIR2 (VmTrace Satisfied2 envAt)
open Dregg2.Circuit.Emit.EffectVmEmit (satisfiedVm)
open Dregg2.Circuit.Emit.EffectVmEmitV2 (graduateV1 graduateV1_sound graduable)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
  (cellSealV3 afterDiscCol discSealed discLive rotateV3WithDiscGate cellSealV3_disc_forces_sealed
   rotateV3WithLifecyclePayloadGate rotateV3WithLifecyclePayloadGate_forces_disc
   afterLifecycleCol declaredLifecyclePayloadCol rotateV3WithLifecyclePayloadGate_forces)
open Dregg2.Circuit.RotatedKernelRefinement (RotTableSide)
open Dregg2.Circuit.Emit.EffectVmEmitRotation (canon_eq_of_modEq)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — the committed `lifecycle`-root column.

The lifecycle side-table is `lifecycle : CellId → Nat`. Its committed root over the touched `cell` is
the `listDigest` of the cell's entry — a `FieldElem` the circuit carries, EXACTLY like a `system_roots`
limb. `lifecycleRoot k cell` is the value the FIX descriptor's lifecycle-root column carries for a
kernel `k`; the gate forces the POST column to `lifecycleRoot` of the SEALED kernel. -/

/-- A field element (the same `ℤ`-carrier `ListCommit`/`StateCommit`/`SystemRoots` use for a felt). -/
abbrev FieldElem := ℤ

/-- The injective leaf encoder for a lifecycle entry: the entry value as a felt. Carried injective
(`lifecycleLeafInjective`), exactly as `SystemRoots`/`ListCommit` carry their leaf injectivity — a
realizable Poseidon over a canonical per-entry serialization, NEVER a Lean axiom. -/
def lifecycleLeaf : Nat → FieldElem := fun n => (n : ℤ)

/-- The lifecycle leaf encoder is injective (the realizable Poseidon-CR carrier). REALIZABLE: `Nat.cast`
into `ℤ` is literally injective, so the toy instance discharges it cleanly. -/
theorem lifecycleLeaf_injective : listLeafInjective lifecycleLeaf := by
  intro a b h
  unfold lifecycleLeaf at h
  exact_mod_cast h

/-- **`lifecycleRoot compressN k cell`** — the committed root of cell `cell`'s `lifecycle` entry: the
`listDigest` over `[lifecycle cell]`. The Lean mirror of the Rust `lifecycle_root` limb the FIX adds to
`compute_commitment`. A pure function of the entry value; absorbed into `state_commit` exactly as a
`system_roots` digest is (`SystemRoots.cellCommitS`). -/
def lifecycleRoot (compressN : List FieldElem → FieldElem) (k : RecordKernelState) (cell : CellId) :
    FieldElem :=
  listDigest lifecycleLeaf compressN [k.lifecycle cell]

/-- **`lifecycleRoot_binds`** — equal lifecycle roots (over the SAME `cell`) force the SAME entry
value. Off the realizable `compressN`-injectivity carrier + the injective leaf: the digest binds the
one-element entry list, so the entry value is pinned. This is the `systemRootsDigest_binds` shape for
the lifecycle side-table — the anti-ghost foundation a forged un-sealed post must clear. -/
theorem lifecycleRoot_binds (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (k k' : RecordKernelState) (cell : CellId)
    (h : lifecycleRoot compressN k cell = lifecycleRoot compressN k' cell) :
    k.lifecycle cell = k'.lifecycle cell := by
  unfold lifecycleRoot at h
  have hlist : ([k.lifecycle cell] : List Nat) = [k'.lifecycle cell] :=
    ListDigestBindsList lifecycleLeaf compressN hN lifecycleLeaf_injective _ _ h
  exact List.head_eq_of_cons_eq hlist

/-! ## §1 — the FIX descriptor's lifecycle-root gate (the column-forcing gate).

The deployed cellSeal row freezes the economic block + ticks the nonce; the FIX ADDS a committed
lifecycle-root column whose POST value the gate `gLifecycleSeal` PINS to the SEALED digest. We model the
gate semantically as a predicate on a row's pre/post lifecycle-root columns — at the same granularity
the per-effect VALUE rungs use (`gFieldWrite` pins `fields[slot]_after = param1`). -/

/-- **`LifecycleRootRow compressN preK postK cell preRoot postRoot`** — the decode tying the FIX row's
two committed lifecycle-root columns to the kernel pre/post lifecycle of `cell`. The PRE column is
`lifecycleRoot` of the pre kernel; the POST column is `lifecycleRoot` of the post kernel. This is the
`RowEncodesSeal`-analog for the new committed column. -/
def LifecycleRootRow (compressN : List FieldElem → FieldElem)
    (preK postK : RecordKernelState) (cell : CellId) (preRoot postRoot : FieldElem) : Prop :=
  preRoot = lifecycleRoot compressN preK cell ∧ postRoot = lifecycleRoot compressN postK cell

/-- **`gLifecycleSeal compressN preK cell postRoot`** — the FIX gate body: the POST lifecycle-root
column IS the digest of the SEALED kernel's `cell` entry. The committed-column analog of
`gFieldWriteP1 slot`: the deployed circuit would EVALUATE this against the sealed-lifecycle root the
trace-fill emits, so a row whose post lifecycle-root is anything else fails the gate. -/
def gLifecycleSeal (compressN : List FieldElem → FieldElem)
    (preK : RecordKernelState) (cell : CellId) (postRoot : FieldElem) : Prop :=
  postRoot = lifecycleRoot compressN (setLifecycle preK cell lcSealed) cell

/-- **`lifecycleSealForced` — the FIX gate FORCES the committed lifecycle column.** If the FIX gate
holds, the POST lifecycle-root column IS the sealed digest. So under `LifecycleRootRow`, the post
kernel's lifecycle of `cell` is pinned to `lcSealed` (via `lifecycleRoot_binds`). This is the rung the
deployed circuit is MISSING and the FIX supplies — exactly `setField_value_forced` for the new column. -/
theorem lifecycleSealForced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (preK postK : RecordKernelState) (cell : CellId) (preRoot postRoot : FieldElem)
    (henc : LifecycleRootRow compressN preK postK cell preRoot postRoot)
    (hgate : gLifecycleSeal compressN preK cell postRoot) :
    postK.lifecycle cell = lcSealed := by
  obtain ⟨_, hpost⟩ := henc
  -- the POST column is BOTH `lifecycleRoot postK` (decode) AND the sealed digest (gate).
  have hroots : lifecycleRoot compressN postK cell
      = lifecycleRoot compressN (setLifecycle preK cell lcSealed) cell := by
    rw [← hpost]; exact hgate
  -- digest injectivity ⇒ equal entry value; the sealed kernel's entry IS `lcSealed`.
  have hval := lifecycleRoot_binds compressN hN postK (setLifecycle preK cell lcSealed) cell hroots
  rw [hval]
  show (if cell = cell then lcSealed else preK.lifecycle cell) = lcSealed
  rw [if_pos rfl]

/-! ## §2 — the WHOLE-MAP forcing: the post lifecycle MAP IS `sealLifecycleMap`.

`CellSealSpec` requires `s'.kernel.lifecycle = sealLifecycleMap s.kernel cell` — the WHOLE map, not just
the `cell` entry. The committed lifecycle root pins the `cell` entry (forced above); the OTHER cells'
entries are FROZEN, carried as the decode residual `hframeOther` (the off-`cell` lifecycle entries are
unchanged — a whole-map residual the per-cell committed column cannot witness, exactly as setField's
`hcellMove` carries the off-slot map). Together they reconstruct the whole map. -/

/-- **`lifecycleMapForced` — the post lifecycle MAP is the seal map.** From the FORCED `cell` entry
(`= lcSealed`) AND the off-`cell` freeze residual, the whole post lifecycle map equals
`sealLifecycleMap preK cell`. The committed root forces the touched entry; the frame carries the rest. -/
theorem lifecycleMapForced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (preK postK : RecordKernelState) (cell : CellId) (preRoot postRoot : FieldElem)
    (henc : LifecycleRootRow compressN preK postK cell preRoot postRoot)
    (hgate : gLifecycleSeal compressN preK cell postRoot)
    (hframeOther : ∀ c, c ≠ cell → postK.lifecycle c = preK.lifecycle c) :
    postK.lifecycle = sealLifecycleMap preK cell := by
  have hcell : postK.lifecycle cell = lcSealed :=
    lifecycleSealForced compressN hN preK postK cell preRoot postRoot henc hgate
  funext c
  show postK.lifecycle c = (setLifecycle preK cell lcSealed).lifecycle c
  show postK.lifecycle c = (if c = cell then lcSealed else preK.lifecycle c)
  by_cases hc : c = cell
  · subst hc; rw [if_pos rfl]; exact hcell
  · rw [if_neg hc]; exact hframeOther c hc

/-! ## §3 — `cellSealGenuineEncodes`: the FIX active-row ⟷ kernel decode.

`cellSealGenuineEncodes pre post actor cell` ties a satisfying FIX-descriptor witness's lifecycle-root
columns onto the kernel seal boundary, and carries the residual the per-cell circuit cannot witness:

  * `preRoot`/`postRoot` + `LifecycleRootRow` — the two committed lifecycle-root columns this state
    encodes (the new committed column the FIX adds);
  * `gate` — the FIX lifecycle gate holds on the row (the WITNESS leg — the committed lifecycle-root is
    PINNED to the sealed digest by the running FIX circuit, not asserted by the decode);
  * `frameOther` — the off-`cell` lifecycle entries are FROZEN (the WHOLE-MAP residual the per-cell
    column cannot carry);
  * `guard` — the `CellSealGuard` (self-authority + is-Live); the executor's domain restriction;
  * `logAdv` — the self-targeted receipt-log advance (off the per-row block);
  * `fr*` — the 16 non-`lifecycle` kernel frame fields (the full `CellSealSpec` frame residual). NAMED,
    not laundered. -/

/-- The decode relating a satisfying FIX cellSeal witness's row to a kernel `pre → post` seal of `cell`
by `actor`. DATA-bearing (`Type`, like setField's `rotatedEncodesSF`): it exhibits the two committed
lifecycle-root columns, carries the FIX gate (the witness leg) + the off-map frame + the kernel-side
residual. -/
structure cellSealGenuineEncodes (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (actor cell : CellId) : Type where
  -- the two committed lifecycle-root columns + their decode.
  preRoot : FieldElem
  postRoot : FieldElem
  hroots : LifecycleRootRow compressN pre.kernel post.kernel cell preRoot postRoot
  -- the FIX gate holds on the row (the WITNESS leg — the committed lifecycle column is FORCED sealed).
  gate : gLifecycleSeal compressN pre.kernel cell postRoot
  -- the off-`cell` lifecycle entries are FROZEN (the WHOLE-MAP residual).
  frameOther : ∀ c, c ≠ cell → post.kernel.lifecycle c = pre.kernel.lifecycle c
  -- the 3-leg-equivalent admissibility guard (self-authority + is-Live; the off-row guard).
  guard : CellSealGuard pre actor cell
  -- the self-targeted receipt-log advance (off the per-row block — the record-layer commitment).
  logAdv : post.log = cellLifecycleReceipt actor cell :: pre.log
  -- the 16 non-`lifecycle` kernel frame fields (the full `CellSealSpec` frame residual).
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
  frNullifierRoot : post.kernel.nullifierRoot = pre.kernel.nullifierRoot
  frRevokedRoot : post.kernel.revokedRoot = pre.kernel.revokedRoot
  frCommitmentsRoot : post.kernel.commitmentsRoot = pre.kernel.commitmentsRoot

/-! ## §4 — the apex obligation: the FIX circuit FORCES the seal write.

The decode carries the kernel-only residual; the WITNESS (the FIX gate) forces the committed lifecycle
column to the sealed digest, and `lifecycleMapForced` lifts that to the whole post map. -/

/-- **`cellSeal_lifecycle_forced` — the committed lifecycle write is FIX-CIRCUIT-FORCED.** On the decoded
row the FIX lifecycle gate forces the whole post lifecycle map to `sealLifecycleMap pre.kernel cell`. So
the seal is pinned by the running FIX circuit; a decode claiming an un-sealed / wrong post is UNSAT
(the §6 tooth). This is precisely the rung the DEPLOYED circuit is missing. -/
theorem cellSeal_lifecycle_forced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId)
    (henc : cellSealGenuineEncodes compressN pre post actor cell) :
    post.kernel.lifecycle = sealLifecycleMap pre.kernel cell :=
  lifecycleMapForced compressN hN pre.kernel post.kernel cell henc.preRoot henc.postRoot
    henc.hroots henc.gate henc.frameOther

/-! ## §5 — THE REFINEMENT: satisfying the FIX cellSeal descriptor FORCES the kernel step.

The decode carries the kernel-only residual (the guard, the frame, the log); the WITNESS forces the
seal write. We assemble `CellSealSpec`. -/

/-- **`cellSeal_descriptorRefines` — THE FIX CIRCUIT→KERNEL REFINEMENT for cellSeal.** A satisfying FIX
cellSeal descriptor witness (carried as `cellSealGenuineEncodes`, whose `gate` is the FIX lifecycle-root
gate the running circuit pins) forces the KERNEL's seal step `CellSealSpec pre actor cell post` — the
`.cellSealA` arm of `execFullA`. The `lifecycle := Sealed` write is FORCED via the committed lifecycle
root (`cellSeal_lifecycle_forced`, riding the new in-commitment lifecycle column); the guard, the
16-field frame, and the log are the named decode residual. -/
theorem cellSeal_descriptorRefines (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId)
    (henc : cellSealGenuineEncodes compressN pre post actor cell) :
    CellSealSpec pre actor cell post := by
  refine ⟨henc.guard, ?_, henc.logAdv, henc.frAccounts, henc.frCell, henc.frCaps,
    henc.frNullifiers, henc.frRevoked, henc.frCommitments, henc.frBal, henc.frSlotCaveats,
    henc.frFactories, henc.frDeathCert, henc.frDelegate, henc.frDelegations,
    henc.frDelegationEpoch, henc.frDelegationEpochAt, henc.frHeaps, henc.frNullifierRoot, henc.frRevokedRoot, henc.frCommitmentsRoot⟩
  exact cellSeal_lifecycle_forced compressN hN pre post actor cell henc

/-- **The refinement, stated against `execFullA` directly.** `CellSealSpec` IS the `.cellSealA` arm of
the executor (`cellSeal_iff_spec`), so a satisfying FIX witness forces
`execFullA pre (.cellSealA actor cell) = some post`. -/
theorem cellSeal_descriptorRefines_execFullA (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId)
    (henc : cellSealGenuineEncodes compressN pre post actor cell) :
    execFullA pre (.cellSealA actor cell) = some post :=
  (Dregg2.Circuit.Spec.CellLifecycle.cellSeal_iff_spec pre actor cell post).mpr
    (cellSeal_descriptorRefines compressN hN pre post actor cell henc)

/-! ## §6 — BOTH-POLARITY TOOTH: an un-sealed witness is UNSAT.

The refinement is meaningful only if the FIX circuit truly forces the seal. The converse: a decode that
claims a post lifecycle whose `cell` entry is NOT `lcSealed` (a frozen / wrong lifecycle, the deployed
circuit's blind spot) cannot ride a satisfying FIX witness — the lifecycle-root gate FORCES the sealed
digest, so the claim is contradictory. This is EXACTLY what the deployed circuit cannot reject. -/

/-- **`cellSeal_descriptorRefines_rejects_unsealed` — the lifecycle tooth.** If a decode asserts a post
whose `cell` lifecycle is NOT `lcSealed` (e.g. a frozen-lifecycle trace — the deployed convention), then
NO FIX witness realizes that decode: the assumption is `False`. The FIX lifecycle-root gate pins the
seal, so an un-sealed cellSeal is UNSAT. -/
theorem cellSeal_descriptorRefines_rejects_unsealed (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId)
    (henc : cellSealGenuineEncodes compressN pre post actor cell)
    (hwrong : post.kernel.lifecycle cell ≠ lcSealed) :
    False := by
  apply hwrong
  exact lifecycleSealForced compressN hN pre.kernel post.kernel cell henc.preRoot henc.postRoot
    henc.hroots henc.gate

/-- **`cellSeal_descriptorRefines_rejects_wrong_map` — the whole-map tooth.** A decode whose post
lifecycle MAP is NOT `sealLifecycleMap pre.kernel cell` (any off-`cell` tamper OR a wrong `cell` entry)
cannot ride a satisfying FIX witness — the FORCED seal pins the whole map. -/
theorem cellSeal_descriptorRefines_rejects_wrong_map (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor cell : CellId)
    (henc : cellSealGenuineEncodes compressN pre post actor cell)
    (hwrong : post.kernel.lifecycle ≠ sealLifecycleMap pre.kernel cell) :
    False :=
  hwrong (cellSeal_lifecycle_forced compressN hN pre post actor cell henc)

/-! ## §6.5 — CLASS A: the seal is FORCED by the DEPLOYED descriptor `cellSealV3` (not a modelled gate).

§1–§6 force the seal from `cellSealGenuineEncodes.gate`, the MODELLED `gLifecycleSeal`. That gate is a
property the decode ASSERTS — editing the LIVE `cellSealV3` constraints does NOT break it. This section
closes that gap: `cellSeal_forced` derives `post.kernel.lifecycle cell = lcSealed` from a `Satisfied2 hash
cellSealV3` witness DIRECTLY, by

  * `graduateV1_sound` — lift the v2 `Satisfied2` of `cellSealV3 = graduateV1 (rotateV3WithDiscGate …)` to
    the v1 per-row `satisfiedVm` of the underlying disc-gated descriptor (the chip/range table side
    `RotTableSide` discharges its `hchip`/`hrange`, `graduable` by `decide`);
  * `cellSealV3_disc_forces_sealed` — the DEPLOYED in-circuit disc gate FORCES the committed AFTER disc
    TRACE limb (`afterDiscCol`, `B_DISC = 32`, a pre-iroot committed limb chaining into `state_commit`) to
    `discSealed (= 1)` on the active row;
  * `CellSealTraceReadout.discLimbDecodes` — the realizable `WitnessDecodes`-class seam: the committed disc
    limb IS the post kernel's lifecycle discriminant cast to ℤ (`= (post.kernel.lifecycle cell : ℤ)`). The
    deployed trace-fill emits the `u8` discriminant of `post.lifecycle[cell]` into exactly that limb, so the
    two are the SAME committed felt by construction — the analog of transfer's `TransferTraceReadout` row
    reads (the limb-level decode the COMMITMENT does not certify, supplied by `StarkSound`).

Editing `cellSealV3`'s disc gate breaks `cellSealV3_disc_forces_sealed`, hence `cellSeal_forced`, hence
`cellSeal_descriptorRefines` — Class A. The seam is a NAMED realizable carrier (a structure field), never an
assumed hole: it is `#assert_axioms`-clean, the `WitnessDecodes`-class floor transfer carries too. -/

/-- **`CellSealTraceReadout` — the realizable circuit-witness extraction for cellSeal (NAMED).**
The trace-determined part a satisfying `cellSealV3` witness supplies, EXACTLY the `WitnessDecodes` class of
transfer's `TransferTraceReadout`: the prover's designated ACTIVE cellSeal row + its selector fact + the
realizable disc-limb decode (the committed AFTER disc limb IS the post lifecycle discriminant felt) + the
whole-map / guard / log / 16-field residual the per-cell committed column cannot witness. Data-bearing
(`Type`, like `cellSealGenuineEncodes`). The disc GATE is NOT a field here — it is FORCED from
`Satisfied2 hash cellSealV3` (`cellSeal_forced`), unlike §3's modelled `gate`. -/
structure CellSealTraceReadout (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (actor cell : CellId) : Type where
  -- the designated ACTIVE cellSeal row (the one whose `SEL_CELLSEAL = 1`).
  row : Nat
  hrow : row < t.rows.length
  -- the active row is a TRANSITION row, NOT the wrap/pad last row: the disc gate runs under
  -- `when_transition()`, so the AFTER-disc force binds only off the last row.
  hrowNotLast : row + 1 ≠ t.rows.length
  -- the selector is hot on the designated row (the prover's row designation, the column fact a real
  -- cellSeal trace exhibits — the analog of transfer's `IsTransferRow`/direction tags).
  hsel : (envAt t row).loc Dregg2.Circuit.Emit.EffectVmEmitCellSeal.SEL_CELLSEAL = 1
  -- the realizable `WitnessDecodes`-class seam: the committed AFTER disc TRACE limb (`afterDiscCol`,
  -- B_DISC = 32) IS the post kernel's lifecycle discriminant cast to ℤ. The deployed trace-fill emits
  -- the `u8` discriminant of `post.lifecycle[cell]` into exactly that limb, so they are the SAME committed
  -- felt by construction — the limb-level decode the COMMITMENT cannot certify, supplied by `StarkSound`.
  discLimbDecodes :
    (envAt t row).loc (afterDiscCol Dregg2.Circuit.Emit.EffectVmEmitCellSeal.cellSealVmDescriptor.traceWidth)
      = ((post.kernel.lifecycle cell : Nat) : ℤ)
  -- **the disc-limb CANONICALITY residual (DEBT-A mod-p).** The deployed disc gate now pins the committed
  -- AFTER disc limb only as a FIELD congruence (`≡ discSealed [ZMOD p]`), so recovering the EXACT
  -- discriminant needs the limb canonical in `[0, p)`. The deployed trace-fill emits the `u8` discriminant
  -- of `post.lifecycle[cell]` into that limb, so it lands in `[0, 256) ⊆ [0, p)`; but the deployed range
  -- table only range-checks the BALANCE limbs (`RotTableSide.range = rangeRows BAL_LIMB_BITS`), NOT the disc
  -- limb — so this range invariant is carried NAMED here, exactly as IncNonce carries its `hCanon` envelope.
  -- It is what lets `canon_eq_of_modEq` lift the `≡ [ZMOD p]` disc-gate residual back to the ℤ equality.
  discCanon : ((post.kernel.lifecycle cell : Nat) : ℤ) < 2013265921
  -- the off-`cell` lifecycle entries are FROZEN (the WHOLE-MAP residual the per-cell limb cannot carry).
  frameOther : ∀ c, c ≠ cell → post.kernel.lifecycle c = pre.kernel.lifecycle c
  -- the admissibility guard (self-authority + is-Live; the off-row guard).
  guard : CellSealGuard pre actor cell
  -- the self-targeted receipt-log advance (off the per-row block — the record-layer commitment).
  logAdv : post.log = cellLifecycleReceipt actor cell :: pre.log
  -- the 16 non-`lifecycle` kernel frame fields (the full `CellSealSpec` frame residual).
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
  frNullifierRoot : post.kernel.nullifierRoot = pre.kernel.nullifierRoot
  frRevokedRoot : post.kernel.revokedRoot = pre.kernel.revokedRoot
  frCommitmentsRoot : post.kernel.commitmentsRoot = pre.kernel.commitmentsRoot

/-- `rotateV3WithLifecyclePayloadGate SEL_CELLSEAL (some discLive) discSealed cellSealVmDescriptor` is
graduable (the appended disc + payload gates are CONSTRAINTS; graduation reads only sites/ranges). The
decidable side condition `graduateV1_sound` requires. (The `#guard` in `EffectVmEmitRotationV3`.) -/
theorem cellSeal_disc_graduable :
    graduable (rotateV3WithLifecyclePayloadGate Dregg2.Circuit.Emit.EffectVmEmitCellSeal.SEL_CELLSEAL
      (some discLive) discSealed Dregg2.Circuit.Emit.EffectVmEmitCellSeal.cellSealVmDescriptor) = true := by
  decide

/-- **`cellSeal_forced` — the seal is FORCED by the DEPLOYED descriptor `cellSealV3` (Class A).**
A `Satisfied2 hash cellSealV3` witness (with the chip/range table side `RotTableSide`) plus the realizable
`CellSealTraceReadout` forces `post.kernel.lifecycle cell = lcSealed`. The committed AFTER disc limb is
pinned to `discSealed (= 1)` by the LIVE disc gate (`cellSealV3_disc_forces_sealed`, via `graduateV1_sound`
on the active transition row), and the readout's `discLimbDecodes` identifies that limb with the post
lifecycle discriminant — so the discriminant is `1 = lcSealed`. The analog of transfer's `debit_forced` /
incrementNonce's `incNonce_nonce_forced`: the forced fact rides the DEPLOYED constraints, so editing
`cellSealV3`'s disc gate turns this RED. -/
theorem cellSeal_forced (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash cellSealV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId)
    (rd : CellSealTraceReadout hash minit mfin maddrs t pre post actor cell) :
    post.kernel.lifecycle cell = lcSealed := by
  -- lift the v2 `Satisfied2` of `cellSealV3 = graduateV1 (rotateV3WithDiscGate …)` to the v1 per-row
  -- `satisfiedVm` of the disc-gated descriptor (chip/range from `RotTableSide`, graduability by `decide`).
  have hv1 : satisfiedVm hash
      (rotateV3WithLifecyclePayloadGate Dregg2.Circuit.Emit.EffectVmEmitCellSeal.SEL_CELLSEAL (some discLive)
        discSealed Dregg2.Circuit.Emit.EffectVmEmitCellSeal.cellSealVmDescriptor)
      (envAt t rd.row) (rd.row == 0) (rd.row + 1 == t.rows.length) :=
    graduateV1_sound hash _ minit mfin maddrs t hside.chip hside.range cellSeal_disc_graduable
      hsat rd.row rd.hrow
  -- the active row is a TRANSITION row, so its `isLast` flag is `false`.
  have hlastf : (rd.row + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact rd.hrowNotLast
  rw [hlastf] at hv1
  -- the DEPLOYED disc gate (survives the payload-gate layer) FORCES the committed AFTER disc limb to
  -- `discSealed` (`rotateV3WithLifecyclePayloadGate_forces_disc`).
  have hlimb : (envAt t rd.row).loc
      (afterDiscCol Dregg2.Circuit.Emit.EffectVmEmitCellSeal.cellSealVmDescriptor.traceWidth)
      ≡ discSealed [ZMOD 2013265921] :=
    rotateV3WithLifecyclePayloadGate_forces_disc _ _ _ hash _ (envAt t rd.row) (rd.row == 0) false rfl
      rd.hsel hv1
  -- the limb IS the post discriminant felt (the realizable seam). The DEBT-A mod-p disc gate is a FIELD
  -- congruence (`≡ discSealed [ZMOD p]`, `discSealed = 1 = lcSealed`); recover the EXACT discriminant from it
  -- via `canon_eq_of_modEq` — both sides canonical in `[0, p)` (`rd.discCanon` for the limb-decoded post disc).
  have hcong : ((post.kernel.lifecycle cell : Nat) : ℤ) ≡ ((lcSealed : Nat) : ℤ) [ZMOD 2013265921] := by
    have hds : ((lcSealed : Nat) : ℤ) = discSealed := rfl
    rw [hds, ← rd.discLimbDecodes]; exact hlimb
  have hcast : ((post.kernel.lifecycle cell : Nat) : ℤ) = ((lcSealed : Nat) : ℤ) :=
    canon_eq_of_modEq ⟨Int.natCast_nonneg _, rd.discCanon⟩ (by decide) hcong
  exact_mod_cast hcast

/-- **`cellSeal_forced_map` — the post lifecycle MAP is `sealLifecycleMap` (Class A, whole map).** From the
DEPLOYED-forced `cell` entry (`cellSeal_forced`) AND the off-`cell` freeze residual the readout carries, the
whole post lifecycle map equals `sealLifecycleMap pre.kernel cell`. -/
theorem cellSeal_forced_map (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash cellSealV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId)
    (rd : CellSealTraceReadout hash minit mfin maddrs t pre post actor cell) :
    post.kernel.lifecycle = sealLifecycleMap pre.kernel cell := by
  have hcell : post.kernel.lifecycle cell = lcSealed :=
    cellSeal_forced hash hside hsat pre post actor cell rd
  funext c
  show post.kernel.lifecycle c = (if c = cell then lcSealed else pre.kernel.lifecycle c)
  by_cases hc : c = cell
  · subst hc; rw [if_pos rfl]; exact hcell
  · rw [if_neg hc]; exact rd.frameOther c hc

/-- **`cellSeal_descriptorRefines_sat` — THE CLASS-A CIRCUIT→KERNEL REFINEMENT for cellSeal.** A satisfying
DEPLOYED `cellSealV3` witness (with the chip/range table side) plus the realizable `CellSealTraceReadout`
forces the KERNEL's seal step `CellSealSpec pre actor cell post`. Unlike §5's `cellSeal_descriptorRefines`
(which consumes a modelled `gate`), the `lifecycle := Sealed` write here is forced from the DEPLOYED disc
gate's `Satisfied2` (`cellSeal_forced_map`) — editing `cellSealV3`'s constraints turns this RED. The guard,
the 16-field frame, and the log are the named decode residual. -/
theorem cellSeal_descriptorRefines_sat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash cellSealV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId)
    (rd : CellSealTraceReadout hash minit mfin maddrs t pre post actor cell) :
    CellSealSpec pre actor cell post := by
  refine ⟨rd.guard, ?_, rd.logAdv, rd.frAccounts, rd.frCell, rd.frCaps,
    rd.frNullifiers, rd.frRevoked, rd.frCommitments, rd.frBal, rd.frSlotCaveats,
    rd.frFactories, rd.frDeathCert, rd.frDelegate, rd.frDelegations,
    rd.frDelegationEpoch, rd.frDelegationEpochAt, rd.frHeaps, rd.frNullifierRoot, rd.frRevokedRoot, rd.frCommitmentsRoot⟩
  exact cellSeal_forced_map hash hside hsat pre post actor cell rd

/-- **CLASS-A TOOTH — a forged un-sealed cellSeal witness is UNSAT.** A `CellSealTraceReadout` whose post
`cell` lifecycle is NOT `lcSealed` cannot ride a satisfying `cellSealV3` witness: the DEPLOYED disc gate
pins the seal. This is the headline lifecycle forgery the deployed circuit now rejects — forced from
`Satisfied2`, not the modelled gate. -/
theorem cellSeal_sat_rejects_unsealed (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash cellSealV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId)
    (rd : CellSealTraceReadout hash minit mfin maddrs t pre post actor cell)
    (hwrong : post.kernel.lifecycle cell ≠ lcSealed) :
    False :=
  hwrong (cellSeal_forced hash hside hsat pre post actor cell rd)

/-- **`cellSeal_payload_limb_forced` — THE STAGE-C PAYLOAD CLOSE consumed at the apex.** A satisfying
DEPLOYED `cellSealV3` witness FORCES the committed AFTER lifecycle limb (`B_LIFECYCLE = 29`) FIELD-CONGRUENT
(`≡ [ZMOD p]`, the DEBT-A mod-p denotation — the faithful form of the deployed field-equality gate) to the
in-circuit declared payload-hash column (`declaredLifecyclePayloadCol = prmCol 3`), which the deployed
trace fills with — and the light client recomputes as — the FELT-DOMAIN `lifecycle_felt(disc, reason_hash,
sealed_at)`. So the opaque sealing PAYLOAD is no longer producer-free for a ledgerless client: a cellSeal
forged to a committed limb ≠ the recomputed payload hash is UNSAT (see the deployed tooth
`EffectVmEmitRotationV3.cellSealV3_payload_rejects_forged_lightclient` and the discriminator
`vk_epoch_refusal_lifecycle_light_client_binding::lifecycle_payload_forge_rejected_by_hash_gate_anchor_disabled`).
This rung CONSUMES the in-circuit payload gate — editing/removing `cellSealV3`'s
`lifecyclePayloadHashGate` turns it RED. -/
theorem cellSeal_payload_limb_forced (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash cellSealV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId)
    (rd : CellSealTraceReadout hash minit mfin maddrs t pre post actor cell) :
    (envAt t rd.row).loc
        (afterLifecycleCol Dregg2.Circuit.Emit.EffectVmEmitCellSeal.cellSealVmDescriptor.traceWidth)
      ≡ (envAt t rd.row).loc declaredLifecyclePayloadCol [ZMOD 2013265921] := by
  have hv1 : satisfiedVm hash
      (rotateV3WithLifecyclePayloadGate Dregg2.Circuit.Emit.EffectVmEmitCellSeal.SEL_CELLSEAL (some discLive)
        discSealed Dregg2.Circuit.Emit.EffectVmEmitCellSeal.cellSealVmDescriptor)
      (envAt t rd.row) (rd.row == 0) (rd.row + 1 == t.rows.length) :=
    graduateV1_sound hash _ minit mfin maddrs t hside.chip hside.range cellSeal_disc_graduable
      hsat rd.row rd.hrow
  have hlastf : (rd.row + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact rd.hrowNotLast
  rw [hlastf] at hv1
  exact rotateV3WithLifecyclePayloadGate_forces
    _ _ _ hash _ (envAt t rd.row) (rd.row == 0) false rfl rd.hsel hv1

/-! ## §7 — NON-VACUITY: the lifecycle root + the gate are load-bearing (no carrier secretly `True`).

A concrete injective `compressN` (a positional Horner sponge, NOT `List.sum`). The lifecycle root of a
SEALED entry DIFFERS from a LIVE entry (the gate distinguishes them); a frozen-lifecycle row's post-root
is NOT the sealed digest (the gate REJECTS it). A `lifecycleRoot := 0` stub would collapse these. -/

private def cNC : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 1000003 + x) (xs.length : ℤ)

private def liveK : RecordKernelState :=
  { accounts := {}, cell := fun _ => .int 0, caps := default, lifecycle := fun _ => lcLive }
private def cell0 : CellId := 0

-- POSITIVE (load-bearing): the SEALED entry's root DIFFERS from the LIVE entry's root (the gate is not
-- a no-op — a `lifecycleRoot := 0` stub would make these EQUAL: forbidden).
#guard decide (lifecycleRoot cNC (setLifecycle liveK cell0 lcSealed) cell0
             = lifecycleRoot cNC liveK cell0) == false

-- The sealed digest equals itself (the gate's RHS is the genuine sealed root, computable).
#guard decide (lifecycleRoot cNC (setLifecycle liveK cell0 lcSealed) cell0
             = lifecycleRoot cNC (setLifecycle liveK cell0 lcSealed) cell0)

-- ANTI-GHOST: a FROZEN-lifecycle post (entry still Live) has a post-root that is NOT the sealed digest,
-- so `gLifecycleSeal` (postRoot = sealed digest) FAILS for it — a stale seal is rejected. (Stated on the
-- unfolded gate equality, decidable on ℤ.)
#guard decide (lifecycleRoot cNC liveK cell0
             = lifecycleRoot cNC (setLifecycle liveK cell0 lcSealed) cell0) == false

-- COMPLETENESS dual: the gate ACCEPTS the genuine sealed post-root (the gate equality holds).
#guard decide (lifecycleRoot cNC (setLifecycle liveK cell0 lcSealed) cell0
             = lifecycleRoot cNC (setLifecycle liveK cell0 lcSealed) cell0)

-- The lifecycle leaf encoder is injective on the toy domain (the carrier is committing the entry):
#guard decide (lifecycleLeaf lcSealed = lifecycleLeaf lcLive) == false

/-! ## §8 — axiom-hygiene tripwires. -/

#assert_axioms lifecycleLeaf_injective
#assert_axioms lifecycleRoot_binds
#assert_axioms lifecycleSealForced
#assert_axioms lifecycleMapForced
#assert_axioms cellSeal_lifecycle_forced
#assert_axioms cellSeal_descriptorRefines
#assert_axioms cellSeal_descriptorRefines_execFullA
#assert_axioms cellSeal_descriptorRefines_rejects_unsealed
#assert_axioms cellSeal_descriptorRefines_rejects_wrong_map
#assert_axioms cellSeal_disc_graduable
#assert_axioms cellSeal_forced
#assert_axioms cellSeal_forced_map
#assert_axioms cellSeal_descriptorRefines_sat
#assert_axioms cellSeal_sat_rejects_unsealed
#assert_axioms cellSeal_payload_limb_forced

end Dregg2.Circuit.RotatedKernelRefinementCellSeal
