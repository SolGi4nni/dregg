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
already use, never a fresh axiom. No `sorry`, no `:= True`, no `native_decide`. NEW file; imports are
read-only.
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
    henc.frDelegationEpoch, henc.frDelegationEpochAt, henc.frHeaps⟩
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

end Dregg2.Circuit.RotatedKernelRefinementCellSeal
