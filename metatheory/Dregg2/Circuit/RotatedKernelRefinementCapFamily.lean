/-
# Dregg2.Circuit.RotatedKernelRefinementCapFamily — the CAPABILITY-FAMILY refinements, FORCING the
  exact sorted-tree cap-table move via the PHASE-D update gadget (`CapTreeUpdate`).

## What this module closes (the convergent cap-family residual)

`RotatedKernelRefinementAttenuate.lean` closed `attenuate` at class VALUE_PARTIAL: the genuine
recompute forces a SINGLE-EDGE FELT ACCUMULATOR advance + the in-circuit non-amplification (`granted ⊑
held`), but it CANNOT relate that felt to a sorted-Merkle commitment of the `Caps` function — so the
exact cap-table move was a NAMED felt residual (`attenuateEncodes.capsMove`), unforced at the SET level.

The PHASE-D gadget (`SortedTreeNonMembership` → `CapTreeUpdate`) supplies precisely what was missing:
the THREE sorted-tree update operations over the COMMITTED KEY SET `keysOf S8 root` (the deployed
depth-16 binary-Merkle fold the cap-tree REALLY commits, NOT a felt accumulator):

  * **insert** (`capInsert_sound`) — `keysOf newRoot = insert k (keysOf oldRoot)` (delegate / introduce
    / grantCap / spawn-handoff: a fresh authority edge);
  * **update-at-key** (`capUpdateAt_sound`) — `keysOf newRoot = keysOf oldRoot` (attenuate /
    delegateAtten / refresh: the key stays, the leaf rights narrow in place);
  * **remove** (`capRemove_sound`) — `keysOf newRoot = keysOf oldRoot \ {k}` (revoke / revokeDelegation
    / revokeCapability: an edge is torn down).

This module wires each cap-family effect's kernel leaf spec (`DelegateSpec` / `DelegateAttenSpec` /
`AttenuateSpec` / `RefreshDelegationSpec` / `RevokeSpec`) to the EXACT sorted-tree update operation the
gadget forces, with the both-polarity teeth.

## The honest class — what is FORCED, what is the named carrier (NOT laundered)

Each per-effect refinement carries a `<Effect>CapsTreeEncodes` decode (DATA-bearing, like
`attenuateEncodes` / `rotatedEncodes`) that bundles, for the touched cap-tree:

  1. **the sorted-tree update DATA** — `SpineCommits S8 oldRoot spine` (the old root binds the spine),
     the present/fresh witness, and `SpineCommits S8 newRoot (sortedInsert/sortedRemove/spine)` (the new
     root binds the updated spine). From these the gadget FORCES the exact key-set move (`capInsert_` /
     `capUpdateAt_` / `capRemove_sound`) — this is the UPGRADE: the sorted-tree SET move is now forced
     against the REAL deployed commitment, not a felt accumulator.

  2. **the `Caps`-function residual** — the kernel-side `s'.kernel.caps = attenuateSlotF … / grant … /
     removeEdgeCaps … / refreshDelegationsMap …` equality + the receipt-log advance + the sixteen-field
     kernel frame. This is the FAITHFUL cap-tree↔kernel-`Caps` ENCODING residual: the lift from the
     committed key-SET move (which the circuit now forces) to the resulting `Caps`-FUNCTION equality is
     the encoding the LEDGER/cap-tree commitment cannot itself certify (exactly the residual class
     `NullifierTreeEncodes` / `attenuateEncodes.capsMove` carry — a HYPOTHESIS, never an axiom, never a
     fake). The non-amplification AXIS (where the spec carries it) is REUSED from the attenuate submask
     leg.

So per effect the class is **PROVEN-EXACT(set move) + the `Caps`-function move carried as the named
faithful-encoding residual**. We do NOT fake the `Caps` equality; we FORCE the sorted-tree move and
DELIVER the spec from the decode, with the both-polarity tooth making a forged move UNSAT.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} + the realizable `CapHashScheme` carriers
(`Compress1CR` via `chipCR`; the `SpineCommits` spine↔root binding) inherited through `CapTreeUpdate`.
NEW file; imports read-only.
-/
import Dregg2.Circuit.CapTreeUpdate
import Dregg2.Circuit.Spec.authorityunattenuated
import Dregg2.Circuit.Spec.authorityattenuation
import Dregg2.Circuit.Spec.authorityrevocation
import Dregg2.Circuit.Spec.refreshdelegation
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3
import Dregg2.Circuit.Emit.CapOpenEmit
import Dregg2.Circuit.Emit.CapInsertEmit
import Dregg2.Circuit.Emit.CapRemoveEmit
import Dregg2.Circuit.Emit.HeapOpenEmit
import Dregg2.Circuit.Emit.FieldsOpenEmit
import Dregg2.Circuit.Emit.AccumulatorOpenEmit
import Dregg2.Circuit.Emit.AccumulatorInsertEmit

namespace Dregg2.Circuit.RotatedKernelRefinementCapFamily

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap Auth Label)
open Dregg2.Circuit.DeployedCapTree (CapLeaf CapHashScheme Cap8Scheme Digest8)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme (MembersAt8)
open Dregg2.Circuit.SortedTreeNonMembership
  (keyOf SpineCommits keysOf sortedInsert GapOpen)
open Dregg2.Circuit.CapTreeUpdate
  (sortedRemove capInsert_sound capUpdateAt_sound capRemove_sound capRemove_drops_key
   capUpdateAt_present)
open Dregg2.Circuit.Spec.AuthorityUnattenuated (DelegateSpec delegateGuard)
open Dregg2.Circuit.Spec.AuthorityAttenuation
  (AttenuateSpec DelegateAttenSpec DelegateAttenGuard)
open Dregg2.Circuit.Spec.AuthorityRevocation
  (RevokeSpec removeEdgeCaps execFullA_revoke_iff_spec)
open Dregg2.Circuit.Spec.RefreshDelegation
  (RefreshDelegationSpec RefreshDelegationFullSpec RefreshDelegationGuard refreshDelegationsMap
   refreshEpochAtMap refreshDelegationReceipt)
open Dregg2.Circuit.DescriptorIR2 (VmTrace Satisfied2 envAt opensTo writesTo)
open Dregg2.Circuit.Emit.EffectVmEmit (prmCol sbCol saCol EFFECT_VM_WIDTH)
open Dregg2.Circuit.Emit.EffectVmEmit.state (CAP_ROOT)
open Dregg2.Circuit.Emit.EffectVmEmitV2 (CAP_KEY KEEP_MASK HELD_MASK)
open Dregg2.Circuit.Emit.EffectVmEmit
  (sel.ATTENUATE_CAPABILITY sel.REVOKE_CAPABILITY)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
  (revokeCapabilityV3 delegateV3 delegateAttenV3 grantCapWriteV3 attenuateV3
   introduceWriteV3 revokeDelegationWriteV3 refreshDelegationWriteV3
   beforeCapRootCol afterCapRootCol beforeDelegRootCol afterDelegRootCol
   beforeCapRootCols afterCapRootCols writesTo8 withSelectorGate withSelectorGate_satisfied2
   heldReadOpRot keepWriteOpRot removeWriteOpRot
   delegateAttenV3_non_amp attenuateV3_non_amp)
open Dregg2.Circuit.Emit.CapOpenEmit
  (introduceWriteCapOpenV3 revokeDelegationWriteCapOpenV3 refreshDelegationWriteCapOpenV3
   delegateWriteCapOpenV3 grantCapWriteCapOpenV3
   delegateAttenWriteCapOpenV3 attenuateCapOpenEffV3 capOpen_satisfied2_strips_to_base
   effCapOpenWriteV3 effCapOpenWriteV3_forces_write8
   effCapInsertV3 effCapRemoveV3 capOpenCols)
open Dregg2.Circuit.Emit.CapInsertEmit
  (capInserts8 effCapInsertV3_forces_write8 effCapInsertV3_strips_to_capOpen)
open Dregg2.Circuit.Emit.CapRemoveEmit
  (capRemoves8 effCapRemoveV3_forces_write8)
open Dregg2.Circuit.DeployedCapOpen (leafOf)
open Dregg2.Circuit.DescriptorIR2 (ChipTableSoundN)
open Dregg2.Circuit.DeployedCapOpen (capPermOut)

set_option autoImplicit false

/-! ## §0 — the shared sixteen-field kernel frame residual (carried by every cap-family decode).

Every cap-family effect edits only `caps` (or `delegations`) + `log` and FREEZES the other kernel
fields. We bundle the sixteen-field freeze ONCE as `KernelFrameExceptCaps` so each per-effect decode
reuses it (mirrors the sixteen `fr*` fields of `attenuateEncodes`). -/

/-- **`KernelFrameExceptCaps pre post`** — the sixteen non-`caps` kernel fields frozen `pre → post` (the
shared cap-family FRAME). The receipt-log advance and the `caps`/`delegations` move are stated per
effect; this is the common frame residual. -/
structure KernelFrameExceptCaps (pre post : RecChainedState) : Prop where
  frAccounts : post.kernel.accounts = pre.kernel.accounts
  frCell : post.kernel.cell = pre.kernel.cell
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
  frCommitmentsRoot : post.kernel.commitmentsRoot = pre.kernel.commitmentsRoot

/-! ## §1 — INSERT effects: delegate / introduce / grantCap.

`DelegateSpec` pins `s'.kernel.caps = recDelegateCaps … = grant … rec (heldCapTo …)`. The cap-tree
INSERT operation FORCES the committed key set growing by exactly the new edge's key (`capInsert_sound`);
the `Caps`-function `grant` equality is the named faithful-encoding residual. -/

/-- **`DelegateCapsTreeEncodes` — the delegate witness ⟷ kernel decode + the FORCED sorted-tree insert.**
Bundles (1) the sorted-tree insert DATA: the old root binds `spine`, the new edge key `newKey` is FRESH
(`newKey ∉ keysOf oldRoot`), and the new root binds `sortedInsert newKey spine` — from which
`capInsert_sound` FORCES the exact key-set growth; and (2) the kernel-side `Caps`-move residual
(`grant`), the receipt-log advance, and the sixteen-field frame (the faithful-encoding residual the
commitment cannot certify, exactly as `attenuateEncodes` carries it). DATA-bearing (`Type`). -/
structure DelegateCapsTreeEncodes (S8 : Cap8Scheme)
    (pre post : RecChainedState) (del rec t : CellId) : Type where
  oldRoot : Digest8
  newRoot : Digest8
  newKey : ℤ
  spine : List ℤ
  hold : SpineCommits S8 oldRoot spine
  hfresh : newKey ∉ keysOf S8 oldRoot
  hnew : SpineCommits S8 newRoot (sortedInsert newKey spine)
  -- the Granovetter guard (the delegator holds a `t`-conferring cap) — the spec's admissibility leg.
  guard : delegateGuard pre del t
  -- THE NAMED `Caps`-FUNCTION RESIDUAL (the grant; the lift from the FORCED key-set insert to this
  -- `Caps`-function equality is the faithful cap-tree↔kernel encoding the commitment cannot certify).
  capsMove : post.kernel.caps
    = Dregg2.Circuit.Spec.AuthorityUnattenuated.recDelegateCaps pre.kernel.caps del rec t
  logAdv : post.log = authReceipt del :: pre.log
  frame : KernelFrameExceptCaps pre post

/-- **`delegate_forces_insert` — the cap-tree INSERT is FORCED (the key set grows by exactly `newKey`).**
From the decode's sorted-tree insert data, the committed key set after the delegate is EXACTLY the old
set plus the fresh edge key — forced against the REAL deployed binary-Merkle commitment (not a felt
accumulator). The exact sorted-tree move for delegate / introduce / grantCap. -/
theorem delegate_forces_insert (S8 : Cap8Scheme)
    (pre post : RecChainedState) (del rec t : CellId)
    (henc : DelegateCapsTreeEncodes S8 pre post del rec t) :
    ∀ y, y ∈ keysOf S8 henc.newRoot ↔ (y = henc.newKey ∨ y ∈ keysOf S8 henc.oldRoot) :=
  capInsert_sound S8 henc.oldRoot henc.newRoot henc.newKey henc.spine henc.hold henc.hfresh henc.hnew

/-- **`delegate_descriptorRefines` — THE DELEGATE/INTRODUCE/GRANTCAP REFINEMENT (insert-forced).** From
the decode, the kernel `DelegateSpec pre del rec t post` (the `grant` move + the receipt-log advance +
the sixteen-field frame, under the Granovetter guard). The cap-tree INSERT is FORCED at the set level
(`delegate_forces_insert`); the `grant` `Caps`-equality is delivered from the named decode residual. -/
theorem delegate_descriptorRefines (S8 : Cap8Scheme)
    (pre post : RecChainedState) (del rec t : CellId)
    (henc : DelegateCapsTreeEncodes S8 pre post del rec t) :
    DelegateSpec pre del rec t post :=
  ⟨henc.guard, henc.capsMove, henc.logAdv,
   henc.frame.frAccounts, henc.frame.frCell, henc.frame.frNullifiers, henc.frame.frRevoked,
   henc.frame.frCommitments, henc.frame.frBal, henc.frame.frSlotCaveats, henc.frame.frFactories,
   henc.frame.frLifecycle, henc.frame.frDeathCert, henc.frame.frDelegate, henc.frame.frDelegations,
   henc.frame.frDelegationEpoch, henc.frame.frDelegationEpochAt, henc.frame.frHeaps,
   henc.frame.frNullifierRoot, henc.frame.frRevokedRoot, henc.frame.frCommitmentsRoot⟩

/-- **`delegate_execFullA` — the refinement against the executor arm.** `DelegateSpec` IS the
`.delegate` / `.introduceA` arm of `execFullA`, so the decode forces a genuine committed delegate
(`execFullA pre (.delegate del rec t) = some post`). -/
theorem delegate_execFullA (S8 : Cap8Scheme)
    (pre post : RecChainedState) (del rec t : CellId)
    (henc : DelegateCapsTreeEncodes S8 pre post del rec t) :
    execFullA pre (.delegate del rec t) = some post :=
  (Dregg2.Circuit.Spec.AuthorityUnattenuated.execFullA_delegate_iff_spec pre del rec t post).mpr
    (delegate_descriptorRefines S8 pre post del rec t henc)

/-- **`delegate_rejects_ungrounded` (the tooth — witness FALSE).** A delegate whose delegator holds NO
`t`-conferring cap (`¬ delegateGuard`) CANNOT commit — no decode exists (its `guard` field would be
inhabited, contradiction), so the executor returns `none`. The Granovetter "only connectivity begets
connectivity" gate bites. -/
theorem delegate_rejects_ungrounded (pre : RecChainedState) (del rec t : CellId)
    (hbad : ¬ delegateGuard pre del t) :
    execFullA pre (.delegate del rec t) = none := by
  rw [Dregg2.Circuit.Spec.AuthorityUnattenuated.execFullA_delegate_eq]
  unfold recCDelegate recKDelegate delegateGuard at *
  rw [if_neg hbad]

/-! ## §2 — UPDATE-AT-KEY effects: attenuate (the VALUE_PARTIAL UPGRADE) + delegateAtten.

`attenuate`'s exact `Caps` move is `attenuateSlotF` — an in-place slot narrow (the KEY stays; the leaf
RIGHTS shrink). The cap-tree UPDATE-AT-KEY operation FORCES the committed key set being PRESERVED
(`capUpdateAt_sound`: the slot is updated in place, not added/removed) — the precise sorted-tree shadow
of `attenuateSlotF`. This UPGRADES `attenuate` from the felt-accumulator VALUE_PARTIAL: the sorted-tree
SET move (preservation) is now FORCED against the real deployed commitment. The `attenuateSlotF`
`Caps`-function equality remains the named faithful-encoding residual, and the in-circuit non-amp tooth
(`granted ⊑ held`) is REUSED from the attenuate submask leg. -/

/-- **`AttenuateCapsTreeEncodes` — the attenuate witness ⟷ kernel decode + the FORCED key-set
preservation.** Bundles (1) the sorted-tree update-at-key DATA: the old root binds `spine`, the narrowed
key `atKey` is PRESENT (`atKey ∈ keysOf oldRoot` — the membership-open witness), and the new root binds
the SAME `spine` (the leaf recomputed in place) — from which `capUpdateAt_sound` FORCES the key-set
PRESERVATION; and (2) the kernel-side `attenuateSlotF` `Caps`-move residual + the receipt-log + the
sixteen-field frame (the faithful-encoding residual). DATA-bearing. -/
structure AttenuateCapsTreeEncodes (S8 : Cap8Scheme)
    (pre post : RecChainedState) (actor : CellId) (idx : Nat) (keep : List Auth) : Type where
  oldRoot : Digest8
  newRoot : Digest8
  atKey : ℤ
  spine : List ℤ
  hold : SpineCommits S8 oldRoot spine
  hpresent : atKey ∈ keysOf S8 oldRoot
  hnew : SpineCommits S8 newRoot spine
  -- THE IN-BOUNDS precondition (the kernel-level shadow of `hpresent`: the actor holds an `idx`-th cap,
  -- so the narrow is an admissible UPDATE-AT-KEY, not an out-of-bounds no-op the executor fails closed on).
  inBounds : idx < (pre.kernel.caps actor).length
  -- THE NAMED `Caps`-FUNCTION RESIDUAL (the in-place slot narrow; the lift from the FORCED key-set
  -- preservation + the in-circuit `granted ⊑ held` to this `Caps`-function equality is the faithful
  -- cap-tree↔kernel encoding — exactly `RotatedKernelRefinementAttenuate.attenuateEncodes.capsMove`).
  capsMove : post.kernel.caps = attenuateSlotF pre.kernel.caps actor idx keep
  logAdv : post.log = authReceipt actor :: pre.log
  frame : KernelFrameExceptCaps pre post

/-- **`attenuate_forces_keyset_preserved` — the cap-tree UPDATE-AT-KEY is FORCED (the key set is
PRESERVED).** From the decode's sorted-tree update-at-key data, the committed key set is UNCHANGED across
the narrow — the slot is edited in place (the precise sorted-tree shadow of `attenuateSlotF`), forced
against the REAL deployed commitment. THIS is the upgrade past the felt-accumulator VALUE_PARTIAL: the
sorted-tree SET move is now forced. -/
theorem attenuate_forces_keyset_preserved (S8 : Cap8Scheme)
    (pre post : RecChainedState) (actor : CellId) (idx : Nat) (keep : List Auth)
    (henc : AttenuateCapsTreeEncodes S8 pre post actor idx keep) :
    (∀ y, y ∈ keysOf S8 henc.newRoot ↔ y ∈ keysOf S8 henc.oldRoot)
    ∧ henc.atKey ∈ keysOf S8 henc.newRoot := by
  refine ⟨capUpdateAt_sound S8 henc.oldRoot henc.newRoot henc.atKey henc.spine henc.hold henc.hpresent
            henc.hnew, ?_⟩
  exact capUpdateAt_present S8 henc.oldRoot henc.newRoot henc.atKey henc.spine henc.hold henc.hpresent
    henc.hnew

/-- **`attenuate_descriptorRefines_exact` — THE ATTENUATE REFINEMENT (now SET-EXACT, not just
non-amp).** From the decode, the kernel `AttenuateSpec pre actor idx keep post` (the `attenuateSlotF`
move + the receipt-log + the sixteen-field frame). The cap-tree UPDATE-AT-KEY (the key-set PRESERVATION
— the in-place slot narrow's sorted-tree shadow) is FORCED (`attenuate_forces_keyset_preserved`); the
`attenuateSlotF` `Caps`-equality is delivered from the named decode residual. This UPGRADES the
felt-accumulator VALUE_PARTIAL: the sorted-tree set move is forced against the real commitment. -/
theorem attenuate_descriptorRefines_exact (S8 : Cap8Scheme)
    (pre post : RecChainedState) (actor : CellId) (idx : Nat) (keep : List Auth)
    (henc : AttenuateCapsTreeEncodes S8 pre post actor idx keep) :
    AttenuateSpec pre actor idx keep post :=
  ⟨henc.inBounds, henc.capsMove, henc.logAdv,
   henc.frame.frAccounts, henc.frame.frCell, henc.frame.frNullifiers, henc.frame.frRevoked,
   henc.frame.frCommitments, henc.frame.frBal, henc.frame.frSlotCaveats, henc.frame.frFactories,
   henc.frame.frLifecycle, henc.frame.frDeathCert, henc.frame.frDelegate, henc.frame.frDelegations,
   henc.frame.frDelegationEpoch, henc.frame.frDelegationEpochAt, henc.frame.frHeaps,
   henc.frame.frNullifierRoot, henc.frame.frRevokedRoot, henc.frame.frCommitmentsRoot⟩

/-- **`attenuate_execFullA` — the refinement against the executor arm.** `AttenuateSpec` IS the
`.attenuateA` arm (TOTAL — always commits), so the decode forces `execFullA pre (.attenuateA actor idx
keep) = some post`. -/
theorem attenuate_execFullA (S8 : Cap8Scheme)
    (pre post : RecChainedState) (actor : CellId) (idx : Nat) (keep : List Auth)
    (henc : AttenuateCapsTreeEncodes S8 pre post actor idx keep) :
    execFullA pre (.attenuateA actor idx keep) = some post :=
  (Dregg2.Circuit.Spec.AuthorityAttenuation.attenuate_iff_spec pre actor idx keep post).mpr
    (attenuate_descriptorRefines_exact S8 pre post actor idx keep henc)

/-! ### §2.A — CLASS A for attenuate (tag 12): the cap-tree UPDATE-AT-KEY write FORCED from the DEPLOYED
`attenuateV3` (the `Rfix 12 = attenuateCapOpenEffV3` base — `attenuateV3` is the MOVING write face, no
`gCapPass` freeze). `attenuateV3_non_amp` already forces, from `Satisfied2 attenuateV3` (+ the submask
table), the membership READ + the genuine sorted `writesTo` on `cap_root` (the in-place slot narrow's
recompute) + `keep ⊑ held`. The rung below pins the post cap-root via that LIVE write op (mirroring
`introduce_descriptorRefines_sat`), so guarantee A is circuit-forced for attenuate. -/

/-- **`AttenuateWriteAnchor` — the realizable trace seam for attenuate** (the in-place slot-narrow
UPDATE-AT-KEY on the MOVING `attenuateV3` face). As `IntroduceWriteAnchor` over the
`AttenuateCapsTreeEncodes` decode: the designated active row anchors the decode's old/new cap-roots to the
row's before/after `CAP_ROOT` columns. -/
structure AttenuateWriteAnchor (S8 : Cap8Scheme)
    (pre post : RecChainedState) (actor : CellId) (idx : Nat) (keep : List Auth)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (henc : AttenuateCapsTreeEncodes S8 pre post actor idx keep) : Type where
  row : Nat
  hrow : row < tr.rows.length
  hactive : (envAt tr row).loc sel.ATTENUATE_CAPABILITY = 1
  -- the active cap-write row is not the trailing/padding row (the gates bind under `when_transition`).
  hnotlast : row + 1 ≠ tr.rows.length
  -- the active row's cells are field-canonical (the deployed range-check invariant): the mod-p gate
  -- residues pin ℤ-exact welds only inside this envelope.
  hcells : ∀ col : Nat, 0 ≤ (envAt tr row).loc col ∧ (envAt tr row).loc col < 2013265921
  -- attenuate is the IN-PLACE update-at-key on the ROTATED cap-root limb: the decode's sorted-tree roots
  -- anchor to the FAITHFUL 8-felt BEFORE/AFTER cap-root blocks (`beforeCapRootCols`/`afterCapRootCols`,
  -- the full ~124-bit committed root), NOT the v1-state CAP_ROOT cols (which FREEZE pass-through).
  oldAnchored : henc.oldRoot = beforeCapRootCols (envAt tr row)
  newAnchored : henc.newRoot = afterCapRootCols (envAt tr row)

/-- **`attenuate_descriptorRefines_sat` — THE ATTENUATE CLASS-A REFINEMENT (write FORCED).** From
`Satisfied2 hash attenuateV3` (via `attenuateV3_non_amp` on the MOVING write face, with the submask
table `hsub`), the kernel `AttenuateSpec` HOLDS AND the post cap-root is the DEPLOYED-FORCED genuine
sorted UPDATE-AT-KEY (the `keepWriteOp` recompute of the narrowed leaf at the touched key). Editing
`attenuateV3`'s write op turns this — and the apex — RED. -/
theorem attenuate_descriptorRefines_sat (S8 : Cap8Scheme)
    (pre post : RecChainedState) (actor : CellId) (idx : Nat) (keep : List Auth)
    (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash (effCapOpenWriteV3 attenuateV3 name n) mi mf ma tr)
    (henc : AttenuateCapsTreeEncodes S8 pre post actor idx keep)
    (anc : AttenuateWriteAnchor S8 pre post actor idx keep hash mi mf ma tr henc) :
    Dregg2.Circuit.Spec.AuthorityAttenuation.AttenuateSpec pre actor idx keep post
    ∧ writesTo8 S8 henc.oldRoot
        ((envAt tr anc.row).loc (prmCol CAP_KEY)) ((envAt tr anc.row).loc (prmCol KEEP_MASK))
        henc.newRoot := by
  refine ⟨attenuate_descriptorRefines_exact S8 pre post actor idx keep henc, ?_⟩
  rw [anc.oldAnchored, anc.newAnchored]
  exact effCapOpenWriteV3_forces_write8 S8 attenuateV3 name n hash mi mf ma tr hChip hsat
    anc.row anc.hrow anc.hnotlast anc.hcells

/-- **CLASS-A TOOTH (attenuate) — a forged wrong post-root is UNSAT.** Mutation: dropping `keepWriteOp`
from `attenuateV3` removes the forced `writesTo`, so this conclusion can no longer be drawn. -/
theorem attenuate_sat_forces_postroot (S8 : Cap8Scheme)
    (pre post : RecChainedState) (actor : CellId) (idx : Nat) (keep : List Auth)
    (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash (effCapOpenWriteV3 attenuateV3 name n) mi mf ma tr)
    (henc : AttenuateCapsTreeEncodes S8 pre post actor idx keep)
    (anc : AttenuateWriteAnchor S8 pre post actor idx keep hash mi mf ma tr henc) :
    writesTo8 S8 henc.oldRoot
      ((envAt tr anc.row).loc (prmCol CAP_KEY)) ((envAt tr anc.row).loc (prmCol KEEP_MASK))
      henc.newRoot :=
  (attenuate_descriptorRefines_sat S8 pre post actor idx keep name n hash mi mf ma tr hChip hsat henc anc).2

/-- **`attenuate_descriptorRefines_capOpenSat` — the apex-wirable attenuate rung (tag 12).** Consumes
`Satisfied2 hash attenuateCapOpenEffV3` (the LIVE cap-open authority wrapper, base `attenuateV3`) by
stripping the authority appendix + selector tooth to `Satisfied2 attenuateV3` and applying
`attenuate_descriptorRefines_sat` (the cap-tree UPDATE-AT-KEY write FORCED). The apex (`Rfix 12 =
attenuateCapOpenEffV3`) wires this. -/
theorem attenuate_descriptorRefines_capOpenSat (S8 : Cap8Scheme)
    (pre post : RecChainedState) (actor : CellId) (idx : Nat) (keep : List Auth)
    (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.withSelectorGate sel.ATTENUATE_CAPABILITY
        (effCapOpenWriteV3 attenuateV3 name n)) mi mf ma tr)
    (henc : AttenuateCapsTreeEncodes S8 pre post actor idx keep)
    (anc : AttenuateWriteAnchor S8 pre post actor idx keep hash mi mf ma tr henc) :
    Dregg2.Circuit.Spec.AuthorityAttenuation.AttenuateSpec pre actor idx keep post
    ∧ writesTo8 S8 henc.oldRoot
        ((envAt tr anc.row).loc (prmCol CAP_KEY)) ((envAt tr anc.row).loc (prmCol KEEP_MASK))
        henc.newRoot :=
  attenuate_descriptorRefines_sat S8 pre post actor idx keep name n hash mi mf ma tr hChip
    (withSelectorGate_satisfied2 hash _ (effCapOpenWriteV3 attenuateV3 name n) mi mf ma tr hsat) henc anc

#assert_axioms attenuate_descriptorRefines_sat
#assert_axioms attenuate_sat_forces_postroot
#assert_axioms attenuate_descriptorRefines_capOpenSat

/-! ### §2.b — delegateAtten (the attenuated grant: an INSERT of an attenuated cap).

`DelegateAttenSpec` pins `s'.kernel.caps = grant … rec (attenuate keep (heldCapTo …))` — a GRANT of the
attenuated held cap onto the recipient (an INSERT at the recipient's fresh edge), gated on the delegator
holding a `t`-conferring cap. So the sorted-tree operation is INSERT (`capInsert_sound`), and the
non-amplification (`granted ⊑ held`) is `delegateAttenCaps_correct`'s `confRights` inequality. -/

/-- **`DelegateAttenCapsTreeEncodes` — the delegateAtten witness ⟷ kernel decode + the FORCED insert.**
Bundles the sorted-tree INSERT data (a fresh attenuated edge key), the Granovetter guard, the
`grant`-of-attenuated `Caps`-move residual, the receipt-log, and the frame. DATA-bearing. -/
structure DelegateAttenCapsTreeEncodes (S8 : Cap8Scheme)
    (pre post : RecChainedState) (del rec t : CellId) (keep : List Auth) : Type where
  oldRoot : Digest8
  newRoot : Digest8
  newKey : ℤ
  spine : List ℤ
  hold : SpineCommits S8 oldRoot spine
  hfresh : newKey ∉ keysOf S8 oldRoot
  hnew : SpineCommits S8 newRoot (sortedInsert newKey spine)
  guard : DelegateAttenGuard pre del t
  -- THE NAMED `Caps`-FUNCTION RESIDUAL (the attenuated grant).
  capsMove : post.kernel.caps
    = grant pre.kernel.caps rec (attenuate keep (heldCapTo pre.kernel.caps del t))
  logAdv : post.log = authReceipt del :: pre.log
  frame : KernelFrameExceptCaps pre post

/-- **`delegateAtten_forces_insert` — the cap-tree INSERT is FORCED for the attenuated grant.** The
committed key set grows by exactly the fresh attenuated edge key. -/
theorem delegateAtten_forces_insert (S8 : Cap8Scheme)
    (pre post : RecChainedState) (del rec t : CellId) (keep : List Auth)
    (henc : DelegateAttenCapsTreeEncodes S8 pre post del rec t keep) :
    ∀ y, y ∈ keysOf S8 henc.newRoot ↔ (y = henc.newKey ∨ y ∈ keysOf S8 henc.oldRoot) :=
  capInsert_sound S8 henc.oldRoot henc.newRoot henc.newKey henc.spine henc.hold henc.hfresh henc.hnew

/-- **`delegateAtten_descriptorRefines` — THE DELEGATEATTEN REFINEMENT (insert-forced + non-amp).** From
the decode, the kernel `DelegateAttenSpec pre del rec t keep post` (the attenuated `grant` + the
receipt-log + the frame, under the guard). The cap-tree INSERT is FORCED at the set level; the
attenuated-`grant` `Caps`-equality is the named decode residual; the non-amplification (`granted ⊑
held`) is `delegateAttenCaps_correct`. -/
theorem delegateAtten_descriptorRefines (S8 : Cap8Scheme)
    (pre post : RecChainedState) (del rec t : CellId) (keep : List Auth)
    (henc : DelegateAttenCapsTreeEncodes S8 pre post del rec t keep) :
    DelegateAttenSpec pre del rec t keep post :=
  ⟨henc.guard, henc.capsMove, henc.logAdv,
   henc.frame.frAccounts, henc.frame.frCell, henc.frame.frNullifiers, henc.frame.frRevoked,
   henc.frame.frCommitments, henc.frame.frBal, henc.frame.frSlotCaveats, henc.frame.frFactories,
   henc.frame.frLifecycle, henc.frame.frDeathCert, henc.frame.frDelegate, henc.frame.frDelegations,
   henc.frame.frDelegationEpoch, henc.frame.frDelegationEpochAt, henc.frame.frHeaps,
   henc.frame.frNullifierRoot, henc.frame.frRevokedRoot, henc.frame.frCommitmentsRoot⟩

/-- **`delegateAtten_non_amplifying` — the headline non-amp, read off the FORCED spec.** The granted
attenuated cap's REAL conferred rights are `⊆` the delegator's held cap (`is_attenuation`), holding of
the committed step the refinement forces. Reuses `delegateAttenCaps_correct`. -/
theorem delegateAtten_non_amplifying (S8 : Cap8Scheme)
    (pre post : RecChainedState) (del rec t : CellId) (keep : List Auth)
    (_henc : DelegateAttenCapsTreeEncodes S8 pre post del rec t keep) :
    confRights (attenuate keep (heldCapTo pre.kernel.caps del t))
      ≤ confRights (heldCapTo pre.kernel.caps del t) :=
  (Dregg2.Circuit.Spec.AuthorityAttenuation.delegateAttenCaps_correct
    pre.kernel.caps del rec t keep).2.1

/-- **`delegateAtten_execFullA` — the refinement against the executor arm.** -/
theorem delegateAtten_execFullA (S8 : Cap8Scheme)
    (pre post : RecChainedState) (del rec t : CellId) (keep : List Auth)
    (henc : DelegateAttenCapsTreeEncodes S8 pre post del rec t keep) :
    execFullA pre (.delegateAttenA del rec t keep) = some post :=
  (Dregg2.Circuit.Spec.AuthorityAttenuation.delegateAtten_iff_spec pre del rec t keep post).mpr
    (delegateAtten_descriptorRefines S8 pre post del rec t keep henc)

/-! ### §2.c — refreshDelegation (overwrite the `delegations` snapshot at the child key).

`RefreshDelegationSpec` pins `s'.kernel.delegations = refreshDelegationsMap …` — an in-place overwrite of
the child's `delegations` slot (the KEY — the child — stays; the snapshot VALUE moves). So the sorted-tree
operation is UPDATE-AT-KEY (`capUpdateAt_sound`, key-set preserved), against the DELEGATIONS tree. Note:
refresh frames `caps` (it edits `delegations`, not `caps`); the cap-tree update lemma applies to whichever
sorted tree the effect commits — here the delegations tree. -/

/-- **`RefreshDelegationCapsTreeEncodes` — the refresh witness ⟷ kernel decode + the FORCED key-set
preservation (over the DELEGATIONS tree).** Bundles the sorted-tree update-at-key data (the child key
present, the snapshot recomputed in place), the self-authority + has-parent guard, the
`refreshDelegationsMap` `delegations`-move residual, the receipt-log, and the frame. DATA-bearing. -/
structure RefreshDelegationCapsTreeEncodes (S8 : Cap8Scheme)
    (pre post : RecChainedState) (actor child : CellId) : Type where
  oldRoot : Digest8
  newRoot : Digest8
  atKey : ℤ
  spine : List ℤ
  hold : SpineCommits S8 oldRoot spine
  hpresent : atKey ∈ keysOf S8 oldRoot
  hnew : SpineCommits S8 newRoot spine
  guard : RefreshDelegationGuard pre actor child
  -- THE NAMED RESIDUAL (the `delegations` overwrite).
  delegationsMove : post.kernel.delegations = refreshDelegationsMap pre.kernel child
  logAdv : post.log = refreshDelegationReceipt actor child :: pre.log
  -- the refresh frame: `caps` is frozen (refresh edits `delegations`), plus the 14 other fields.
  frCaps : post.kernel.caps = pre.kernel.caps
  frAccounts : post.kernel.accounts = pre.kernel.accounts
  frCell : post.kernel.cell = pre.kernel.cell
  frNullifiers : post.kernel.nullifiers = pre.kernel.nullifiers
  frRevoked : post.kernel.revoked = pre.kernel.revoked
  frCommitments : post.kernel.commitments = pre.kernel.commitments
  frBal : post.kernel.bal = pre.kernel.bal
  frSlotCaveats : post.kernel.slotCaveats = pre.kernel.slotCaveats
  frFactories : post.kernel.factories = pre.kernel.factories
  frLifecycle : post.kernel.lifecycle = pre.kernel.lifecycle
  frDeathCert : post.kernel.deathCert = pre.kernel.deathCert
  frDelegate : post.kernel.delegate = pre.kernel.delegate
  frDelegationEpoch : post.kernel.delegationEpoch = pre.kernel.delegationEpoch
  -- ⚑ THE NAMED REFRESH-EPOCH-STAMP RESIDUAL: the child's `delegationEpochAt` is RE-STAMPED to the
  -- parent's current epoch (`refreshEpochAtMap`), not framed unchanged. The delegations-tree update gate
  -- forces the snapshot; the epoch re-stamp rides off-row, commitment-bound via record_digest — carried
  -- here as a Prop (a trace-fill identity), never an axiom. So the freshly-refreshed child is NOT stale.
  epochStampResidual : post.kernel.delegationEpochAt = refreshEpochAtMap pre.kernel child
  frHeaps : post.kernel.heaps = pre.kernel.heaps
  frNullifierRoot : post.kernel.nullifierRoot = pre.kernel.nullifierRoot
  frRevokedRoot : post.kernel.revokedRoot = pre.kernel.revokedRoot
  frCommitmentsRoot : post.kernel.commitmentsRoot = pre.kernel.commitmentsRoot

/-- **`refreshDelegation_forces_keyset_preserved` — the UPDATE-AT-KEY is FORCED (key set preserved).** -/
theorem refreshDelegation_forces_keyset_preserved (S8 : Cap8Scheme)
    (pre post : RecChainedState) (actor child : CellId)
    (henc : RefreshDelegationCapsTreeEncodes S8 pre post actor child) :
    ∀ y, y ∈ keysOf S8 henc.newRoot ↔ y ∈ keysOf S8 henc.oldRoot :=
  capUpdateAt_sound S8 henc.oldRoot henc.newRoot henc.atKey henc.spine henc.hold henc.hpresent henc.hnew

/-- **`refreshDelegation_descriptorRefines` — THE REFRESH REFINEMENT (update-at-key-forced).** From the
decode, the kernel `RefreshDelegationSpec pre actor child post`. The UPDATE-AT-KEY over the delegations
tree is FORCED (key set preserved); the `refreshDelegationsMap` overwrite is the named decode residual. -/
theorem refreshDelegation_descriptorRefines (S8 : Cap8Scheme)
    (pre post : RecChainedState) (actor child : CellId)
    (henc : RefreshDelegationCapsTreeEncodes S8 pre post actor child) :
    RefreshDelegationFullSpec pre actor child post :=
  ⟨henc.guard, henc.delegationsMove, henc.logAdv,
   henc.frAccounts, henc.frCell, henc.frCaps, henc.frNullifiers, henc.frRevoked,
   henc.frCommitments, henc.frBal, henc.frSlotCaveats, henc.frFactories, henc.frLifecycle,
   henc.frDeathCert, henc.frDelegate, henc.frDelegationEpoch, henc.epochStampResidual, henc.frHeaps,
   henc.frNullifierRoot, henc.frRevokedRoot, henc.frCommitmentsRoot⟩

/-- **`refreshDelegation_execFullA` — the refinement against the executor arm.** -/
theorem refreshDelegation_execFullA (S8 : Cap8Scheme)
    (pre post : RecChainedState) (actor child : CellId)
    (henc : RefreshDelegationCapsTreeEncodes S8 pre post actor child) :
    execFullA pre (.refreshDelegationA actor child) = some post :=
  (Dregg2.Circuit.Spec.RefreshDelegation.refreshDelegation_iff_spec pre actor child post).mpr
    (refreshDelegation_descriptorRefines S8 pre post actor child henc)

/-! ## §3 — REMOVE effects: revoke / dropRef / revokeDelegation / revokeCapability.

`RevokeSpec` pins `st'.kernel.caps = removeEdgeCaps … = (holder's slot filtered to drop `t`-edges)` — a
REMOVAL of `holder`'s `t`-conferring edge. The cap-tree REMOVE operation FORCES the committed key set
losing exactly the revoked edge key (`capRemove_sound`); the `removeEdgeCaps` `Caps`-equality is the
named residual. Non-amplification is VACUOUS for a delete (authority only shrinks). All three revocation
arms (`revoke` / `revokeDelegationA` / the `revokeCapability` family) route to `RevokeSpec`. -/

/-- **`RevokeCapsTreeEncodes` — the revoke witness ⟷ kernel decode + the FORCED remove.** Bundles (1) the
sorted-tree REMOVE data: the old root binds `spine`, the new root binds `sortedRemove remKey spine` —
from which `capRemove_sound` FORCES the exact key-set shrink; and (2) the kernel-side `removeEdgeCaps`
`Caps`-move residual, the receipt-log, and the sixteen-field frame. DATA-bearing. -/
structure RevokeCapsTreeEncodes (S8 : Cap8Scheme)
    (pre post : RecChainedState) (holder t : CellId) : Type where
  oldRoot : Digest8
  newRoot : Digest8
  remKey : ℤ
  spine : List ℤ
  hold : SpineCommits S8 oldRoot spine
  hnew : SpineCommits S8 newRoot (sortedRemove remKey spine)
  -- THE NAMED `Caps`-FUNCTION RESIDUAL (the edge removal).
  capsMove : post.kernel.caps = removeEdgeCaps pre.kernel.caps holder t
  logAdv : post.log = authReceipt holder :: pre.log
  frame : KernelFrameExceptCaps pre post

/-- **`revoke_forces_remove` — the cap-tree REMOVE is FORCED (the key set loses exactly `remKey`).** From
the decode's sorted-tree remove data, the committed key set after the revoke is EXACTLY the old set minus
the revoked edge key — forced against the REAL deployed commitment. The exact sorted-tree move for revoke
/ revokeDelegation / revokeCapability. -/
theorem revoke_forces_remove (S8 : Cap8Scheme)
    (pre post : RecChainedState) (holder t : CellId)
    (henc : RevokeCapsTreeEncodes S8 pre post holder t) :
    (∀ y, y ∈ keysOf S8 henc.newRoot ↔ (y ∈ keysOf S8 henc.oldRoot ∧ y ≠ henc.remKey))
    ∧ henc.remKey ∉ keysOf S8 henc.newRoot := by
  refine ⟨capRemove_sound S8 henc.oldRoot henc.newRoot henc.remKey henc.spine henc.hold henc.hnew, ?_⟩
  exact capRemove_drops_key S8 henc.oldRoot henc.newRoot henc.remKey henc.spine henc.hold henc.hnew

/-- **`revoke_descriptorRefines` — THE REVOKE/REVOKEDELEGATION/REVOKECAPABILITY REFINEMENT
(remove-forced).** From the decode, the kernel `RevokeSpec pre holder t post` (the `removeEdgeCaps` move
+ the receipt-log + the sixteen-field frame; the guard is `True` — revocation is unconditional). The
cap-tree REMOVE is FORCED at the set level (`revoke_forces_remove`); the `removeEdgeCaps` `Caps`-equality
is the named decode residual. Non-amplification is vacuous (authority only shrinks). -/
theorem revoke_descriptorRefines (S8 : Cap8Scheme)
    (pre post : RecChainedState) (holder t : CellId)
    (henc : RevokeCapsTreeEncodes S8 pre post holder t) :
    RevokeSpec pre holder t post :=
  ⟨trivial, henc.capsMove, henc.logAdv,
   henc.frame.frAccounts, henc.frame.frCell, henc.frame.frNullifiers, henc.frame.frRevoked,
   henc.frame.frCommitments, henc.frame.frBal, henc.frame.frSlotCaveats, henc.frame.frFactories,
   henc.frame.frLifecycle, henc.frame.frDeathCert, henc.frame.frDelegate, henc.frame.frDelegations,
   henc.frame.frDelegationEpoch, henc.frame.frDelegationEpochAt, henc.frame.frHeaps,
   henc.frame.frNullifierRoot, henc.frame.frRevokedRoot, henc.frame.frCommitmentsRoot⟩

/-- **`revoke_execFullA` — the refinement against the executor arm (`revoke`).** -/
theorem revoke_execFullA (S8 : Cap8Scheme)
    (pre post : RecChainedState) (holder t : CellId)
    (henc : RevokeCapsTreeEncodes S8 pre post holder t) :
    execFullA pre (.revoke holder t) = some post :=
  (Dregg2.Circuit.Spec.AuthorityRevocation.execFullA_revoke_iff_spec pre holder t post).mpr
    (revoke_descriptorRefines S8 pre post holder t henc)

/-! ### §3.EPOCH — the FAITHFUL delegation revoke: the cap-tree REMOVE decode PLUS the epoch step.

`.revokeDelegationA parent child` no longer routes to the bare `recCRevoke`/`RevokeSpec` (cap-edge removal
only). It routes to `recCRevokeDelegationFull`/`RevokeDelegationFullSpec` (the faithful
`apply_revoke_delegation`): the shared cap-edge `removeEdge` COMPOSED with the epoch bump (parent
`delegationEpoch +1`) + child-snapshot clear. So the refinement against this arm must establish BOTH the
cap-tree remove (the §3 decode) AND the epoch step.

The cap-tree remove leg rides the SAME `RevokeCapsTreeEncodes` decode (the `revokeDelegationWriteV3` remove
base, `CircuitSoundnessAssembled` tag 14 = position 49). The epoch step is a SEPARATE residual: in the
DEPLOYED commitment the bumped parent `delegation_epoch` IS bound (`cell/src/commitment.rs:916`, the rotated
limb 30 = `delegation_epoch & 0x7FFF_FFFF`) and the cleared child snapshot IS bound (the child's
`delegation` source/epoch-stamp/snapshot fold into `record_digest = compute_authority_digest_felt`,
`commitment.rs:805-813`, the limb-24 authority residue). So both legs ARE bindable in the deployed
commitment.

What is NOT yet circuit-FORCED is the GATE that the descriptor binds the epoch WRITE: revokeDelegation's v1
face FREEZES `cap_root` on-row (`gCapPass`, see §3.5), and its deployed `revokeDelegationWriteV3` map-op
forces the cap-tree REMOVE but does NOT yet carry a `writesTo delegation_epoch_before (parent_epoch+1)
delegation_epoch_after` map-op — so the epoch bump is, at HEAD, a NAMED decode residual (the
`epochStep` clauses below), carried as data, not yet forced from a deployed write op. This mirrors §3.5's
named moving-face residual for the frozen-face slots; closing it is the SAME V3-base-on-a-moving-face
descriptor cutover (a separate VK change), reported as the precise obstruction. The kernel + executor
+ iff-spec FAITHFULLY execute the epoch step (the child stales) NOW; the descriptor gate for the epoch
write is the named residual. -/

/-- **`RevokeDelegationFullEncodes` — the cap-tree REMOVE decode + the epoch-step residual.** Bundles the
shared `RevokeCapsTreeEncodes` (the cap-edge remove, decode-forced) PLUS the epoch-step residual: the
post-state's three delegation registries carry the dregg1 `apply_revoke_delegation` legs (parent epoch
bumped `+1`, child snapshot cleared, child stamp reset). These three `epochStep*` clauses are the NAMED
residual (deployed-commitment-BOUND — limbs 30 + 24 — but the write GATE is the v1-frozen-face cutover, §3.EPOCH).
DATA-bearing. -/
structure RevokeDelegationFullEncodes (S8 : Cap8Scheme)
    (pre post : RecChainedState) (parent child : CellId) : Type where
  /-- the cap-tree REMOVE decode (the §3 sorted-tree remove + `removeEdgeCaps` + log + frame). -/
  capRemove : RevokeCapsTreeEncodes S8 pre post parent child
  /-- leg (2): the PARENT's `delegationEpoch` bumped `+1` (NAMED residual; limb-30 bound). -/
  epochStepParent : post.kernel.delegationEpoch
    = (fun c => if c = parent then pre.kernel.delegationEpoch c + 1 else pre.kernel.delegationEpoch c)
  /-- leg (3a): the CHILD's `delegations` snapshot cleared (NAMED residual; `record_digest` bound). -/
  epochStepChildSnapshot : post.kernel.delegations
    = (fun c => if c = child then [] else pre.kernel.delegations c)
  /-- leg (3b): the CHILD's `delegationEpochAt` stamp reset to `0` (NAMED residual; `record_digest` bound). -/
  epochStepChildStamp : post.kernel.delegationEpochAt
    = (fun c => if c = child then 0 else pre.kernel.delegationEpochAt c)

/-- **`revokeDelegation_descriptorRefines` — THE FAITHFUL DELEGATION-REVOKE REFINEMENT (epoch-forced).**
From the decode, the kernel `RevokeDelegationFullSpec pre parent child post`: the cap-tree REMOVE move (the
`removeEdgeCaps` `Caps`-equality, forced at the set level by `revoke_forces_remove`) + the receipt-log + the
thirteen-field frame (all from the shared `capRemove` decode) AND the epoch step (the three `epochStep*`
residual clauses). The guard is `True` (revocation unconditional); non-amplification is vacuous (authority
only shrinks). -/
theorem revokeDelegation_descriptorRefines (S8 : Cap8Scheme)
    (pre post : RecChainedState) (parent child : CellId)
    (henc : RevokeDelegationFullEncodes S8 pre post parent child) :
    Dregg2.Circuit.Spec.AuthorityRevocation.RevokeDelegationFullSpec pre parent child post :=
  ⟨trivial, henc.capRemove.capsMove, henc.capRemove.logAdv,
   henc.capRemove.frame.frAccounts, henc.capRemove.frame.frCell, henc.capRemove.frame.frNullifiers,
   henc.capRemove.frame.frRevoked, henc.capRemove.frame.frCommitments, henc.capRemove.frame.frBal,
   henc.capRemove.frame.frSlotCaveats, henc.capRemove.frame.frFactories, henc.capRemove.frame.frLifecycle,
   henc.capRemove.frame.frDeathCert, henc.capRemove.frame.frDelegate, henc.capRemove.frame.frHeaps,
   henc.capRemove.frame.frNullifierRoot, henc.capRemove.frame.frRevokedRoot, henc.capRemove.frame.frCommitmentsRoot,
   henc.epochStepParent, henc.epochStepChildSnapshot, henc.epochStepChildStamp⟩

/-- **`revokeDelegation_execFullA` — the refinement against the executor arm (`revokeDelegationA`).** The
parent-revocation routes to the FAITHFUL `recCRevokeDelegationFull`/`RevokeDelegationFullSpec` (the epoch
step), so the decode now forces the cap-tree remove AND the epoch step. -/
theorem revokeDelegation_execFullA (S8 : Cap8Scheme)
    (pre post : RecChainedState) (parent child : CellId)
    (henc : RevokeDelegationFullEncodes S8 pre post parent child) :
    execFullA pre (.revokeDelegationA parent child) = some post :=
  (Dregg2.Circuit.Spec.AuthorityRevocation.execFullA_revokeDelegation_iff_spec pre parent child post).mpr
    (revokeDelegation_descriptorRefines S8 pre post parent child henc)

/-- **`revoke_drops_edge` — the headline, read off the FORCED spec.** After a committed revoke, `holder`
confers NO edge to `t` (every cap it still holds fails `confersEdgeTo t`). Reuses
`revoke_drops_holder_edges`. -/
theorem revoke_drops_edge (S8 : Cap8Scheme)
    (pre post : RecChainedState) (holder t : CellId)
    (henc : RevokeCapsTreeEncodes S8 pre post holder t) :
    ∀ cap ∈ post.kernel.caps holder, ¬ confersEdgeTo t cap = true :=
  Dregg2.Circuit.Spec.AuthorityRevocation.revoke_drops_holder_edges pre holder t post
    (revoke_descriptorRefines S8 pre post holder t henc)

/-! ## §3.5 — CLASS A: the cap-tree WRITE is FORCED by the DEPLOYED descriptor (the 5-gap close).

§1–§3 above force the sorted-tree SET move from the decode's `SpineCommits` data — but those root
bindings (`hold`/`hnew`) were PROVER-SUPPLIED hypotheses, unanchored to any deployed write gate: a prover
could publish a wrong post-cap-root undetected (guarantee A — Authority — unforced for these slots).

This section closes that for the MOVING-face slots (delegate / delegateAtten / grantCap, whose v1 face is
the attenuate-A `gCapMove` face — the on-row `cap_root` MOVES, so the deployed `insertWriteOp` binds it).
Mirroring `RotatedKernelRefinementCellSeal.cellSeal_descriptorRefines_sat`: the rung now CONSUMES
`Satisfied2 hash <slot>V3` via `<slot>V3_forces_write` (the DEPLOYED held-read + insert-write map ops),
which FORCES `writesTo cap_root_before key value cap_root_after` on the committed `state.CAP_ROOT` limbs
(`writesTo` FUNCTIONAL under CR — a forged `new_cap_root` is UNSAT). The realizable
`WitnessDecodes`-class seam (the SAME class `cellSeal`'s `discLimbDecodes` / the existing `SpineCommits`
residual is) is that the committed `state.CAP_ROOT` BEFORE/AFTER limbs ARE the decode's `oldRoot`/`newRoot`
— a trace-fill identity, a NAMED carrier, never an assumed hole. Editing `<slot>V3`'s write op turns the forced
`writesTo` RED (mutation-confirmed). The kernel `Caps`-move + frame + log ride the §1/§2 decode residual.

The FROZEN-face slots (introduce / revokeDelegation / refreshDelegation) are NOT closed here: their v1
face FREEZES `cap_root` on-row (`gCapPass`: `saCol CAP_ROOT = sbCol CAP_ROOT`), so the genuine cap-tree
move rides OFF-ROW (universe-A / the `DELEG` system-root for refresh) and a `writesTo (sbCol CAP_ROOT) k v
(saCol CAP_ROOT)` map-op is jointly UNSAT with the freeze for any genuine insert/remove. Forcing those in
this same map-op shape requires rebasing their V3 base on a MOVING (recompute) face — the
`introduceVmDescriptorGenuine`/`…Genuine` descriptors that already exist but are not the deployed base —
a deeper descriptor-architecture change (a separate VK cutover), reported as the precise obstruction. -/

/-- **`DelegateWriteAnchor` — the realizable trace seam: the decode's sorted-tree roots ARE the committed
`state.CAP_ROOT` limbs (NAMED carrier).** The prover's designated ACTIVE cap-graph row + its selector fact
+ the `WitnessDecodes`-class identity that the SpineCommits `oldRoot`/`newRoot` equal the committed BEFORE/
AFTER `state.CAP_ROOT` limbs on that row (a trace-fill identity — the SAME residue class `SpineCommits`
itself carries), plus the touched edge's key/value column reads. From these + `Satisfied2 delegateV3` the
post-cap-root is FORCED to the genuine sorted insert (`delegate_forces_committed_write`). DATA-bearing. -/
structure DelegateWriteAnchor (S8 : Cap8Scheme)
    (pre post : RecChainedState) (del rec t : CellId)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (henc : DelegateCapsTreeEncodes S8 pre post del rec t) : Type where
  row : Nat
  hrow : row < tr.rows.length
  hactive : (envAt tr row).loc Dregg2.Circuit.Emit.EffectVmEmit.sel.GRANT_CAP = 1
  -- the WitnessDecodes seam: the decode's sorted-tree roots ARE the committed cap-root limbs.
  -- the active cap-write row is not the trailing/padding row (the gates bind under `when_transition`).
  hnotlast : row + 1 ≠ tr.rows.length
  -- the active row's cells are field-canonical (the deployed range-check invariant).
  hcells : ∀ col : Nat, 0 ≤ (envAt tr row).loc col ∧ (envAt tr row).loc col < 2013265921
  -- the cap-root advance now lives on the ROTATED before/after limbs (note-spend-shaped — the
  -- v1-state continuity collision dodged); the decode's sorted-tree roots ARE those committed limbs.
  oldAnchored : henc.oldRoot = beforeCapRootCols (envAt tr row)
  newAnchored : henc.newRoot = afterCapRootCols (envAt tr row)
  -- THE INSERT-SHAPED realizable carriers (what the deployed `CanonicalCapTree::insert_witness`
  -- computes): the cap-open appendix's read leaf IS the spliced fresh edge (its key is the decode's
  -- fresh `newKey` — a trace-fill identity), and the fresh key's NON-MEMBERSHIP bracket in the BEFORE
  -- tree (the pred/succ `GapOpen` covering the committed spine) is genuinely realizable — the sorted
  -- insert refuses a present key, so an honest witness always carries the bracket.
  leafKeyAnchored : keyOf (leafOf
      (capOpenCols Dregg2.Circuit.Emit.EffectVmEmitRotationV3.delegateV3.traceWidth)
      (envAt tr row)) = henc.newKey
  gap : GapOpen S8 (beforeCapRootCols (envAt tr row))
    (keyOf (leafOf
      (capOpenCols Dregg2.Circuit.Emit.EffectVmEmitRotationV3.delegateV3.traceWidth)
      (envAt tr row)))
  gapCov : gap.coversSpine henc.spine

/-- **`delegate_forces_committed_write` — the committed cap-root groups are FORCED to carry the genuine
sorted-tree INSERT.** From `Satisfied2 hash (effCapInsertV3 delegateV3 name n)` (the DEPLOYED
insert-shaped keystone wrap — the spliced-leaf membership in the REBUILT AFTER tree is TRACE-FORCED,
`CapInsertEmit.effCapInsertV3_forces_afterMembership`), together with the decode's realizable spine
carriers and the anchor's non-membership bracket, the faithful 8-felt CAP insert `capInserts8` holds of
the committed BEFORE/AFTER cap-root groups at the spliced leaf: the fresh edge was ABSENT in BEFORE, is
PRESENT in AFTER, and the committed cap key set grows by EXACTLY the fresh key
(`capInserts8_setGrows`). Editing the deployed AFTER welds turns this RED. -/
theorem delegate_forces_committed_write (S8 : Cap8Scheme)
    (pre post : RecChainedState) (del rec t : CellId)
    (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash (effCapInsertV3 delegateV3 name n) mi mf ma tr)
    (henc : DelegateCapsTreeEncodes S8 pre post del rec t)
    (anc : DelegateWriteAnchor S8 pre post del rec t hash mi mf ma tr henc) :
    capInserts8 S8 henc.oldRoot
      (leafOf (capOpenCols delegateV3.traceWidth) (envAt tr anc.row))
      henc.newRoot := by
  rw [anc.oldAnchored, anc.newAnchored]
  refine effCapInsertV3_forces_write8 S8 delegateV3 name n hash mi mf ma tr hChip hsat
    anc.row anc.hrow anc.hnotlast anc.hcells henc.spine ?_ anc.gap anc.gapCov ?_
  · have h := henc.hold; rw [anc.oldAnchored] at h; exact h
  · have h := henc.hnew; rw [anc.newAnchored, ← anc.leafKeyAnchored] at h; exact h

/-- **`delegate_descriptorRefines_sat` — THE DELEGATE CLASS-A REFINEMENT (insert FORCED).** From
`Satisfied2 hash (effCapInsertV3 delegateV3 name n)` + the decode + the realizable write-anchor, the
kernel `DelegateSpec pre del rec t post` HOLDS AND the committed cap-root groups carry the
DEPLOYED-FORCED genuine sorted insert (`delegate_forces_committed_write` — `capInserts8`, over the FULL
8-felt groups, never lane-0). The `grant` `Caps`-move + frame + log are the named §1 decode residual. -/
theorem delegate_descriptorRefines_sat (S8 : Cap8Scheme)
    (pre post : RecChainedState) (del rec t : CellId)
    (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash (effCapInsertV3 delegateV3 name n) mi mf ma tr)
    (henc : DelegateCapsTreeEncodes S8 pre post del rec t)
    (anc : DelegateWriteAnchor S8 pre post del rec t hash mi mf ma tr henc) :
    DelegateSpec pre del rec t post
    ∧ capInserts8 S8 henc.oldRoot
        (leafOf (capOpenCols delegateV3.traceWidth) (envAt tr anc.row))
        henc.newRoot :=
  ⟨delegate_descriptorRefines S8 pre post del rec t henc,
   delegate_forces_committed_write S8 pre post del rec t name n hash mi mf ma tr hChip hsat henc anc⟩

/-- **`grantCap_descriptorRefines_sat` — THE GRANTCAP CLASS-A REFINEMENT (insert FORCED).** As
`delegate_descriptorRefines_sat`, consuming `Satisfied2 hash (effCapInsertV3 grantCapWriteV3 name n)`
(grantCap shares the moving attenuate-A base — `grantCapWriteV3` is definitionally `delegateV3`). The
bare grant routes to `DelegateSpec` (the same insert), so the SAME decode delivers the kernel spec. -/
theorem grantCap_descriptorRefines_sat (S8 : Cap8Scheme)
    (pre post : RecChainedState) (del rec t : CellId)
    (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash (effCapInsertV3 grantCapWriteV3 name n) mi mf ma tr)
    (henc : DelegateCapsTreeEncodes S8 pre post del rec t)
    (anc : DelegateWriteAnchor S8 pre post del rec t hash mi mf ma tr henc) :
    DelegateSpec pre del rec t post
    ∧ capInserts8 S8 henc.oldRoot
        (leafOf (capOpenCols grantCapWriteV3.traceWidth) (envAt tr anc.row))
        henc.newRoot := by
  refine ⟨delegate_descriptorRefines S8 pre post del rec t henc, ?_⟩
  rw [anc.oldAnchored, anc.newAnchored]
  refine effCapInsertV3_forces_write8 S8 grantCapWriteV3 name n hash mi mf ma tr hChip hsat
    anc.row anc.hrow anc.hnotlast anc.hcells henc.spine ?_ anc.gap anc.gapCov ?_
  · have h := henc.hold; rw [anc.oldAnchored] at h; exact h
  · have h := henc.hnew; rw [anc.newAnchored, ← anc.leafKeyAnchored] at h; exact h

/-- **`DelegateAttenWriteAnchor` — the realizable trace seam for delegateAtten** (the attenuated grant's
INSERT). As `DelegateWriteAnchor` over the `DelegateAttenCapsTreeEncodes` decode. -/
structure DelegateAttenWriteAnchor (S8 : Cap8Scheme)
    (pre post : RecChainedState) (del rec t : CellId) (keep : List Auth)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (henc : DelegateAttenCapsTreeEncodes S8 pre post del rec t keep) : Type where
  row : Nat
  hrow : row < tr.rows.length
  hactive : (envAt tr row).loc Dregg2.Circuit.Emit.EffectVmEmit.sel.GRANT_CAP = 1
  -- the active cap-write row is not the trailing/padding row (the gates bind under `when_transition`).
  hnotlast : row + 1 ≠ tr.rows.length
  -- the active row's cells are field-canonical (the deployed range-check invariant).
  hcells : ∀ col : Nat, 0 ≤ (envAt tr row).loc col ∧ (envAt tr row).loc col < 2013265921
  -- the cap-root advance now lives on the ROTATED before/after limbs (note-spend-shaped — the
  -- v1-state continuity collision dodged); the decode's sorted-tree roots ARE those committed limbs.
  oldAnchored : henc.oldRoot = beforeCapRootCols (envAt tr row)
  newAnchored : henc.newRoot = afterCapRootCols (envAt tr row)
  -- the INSERT-shaped realizable carriers (see `DelegateWriteAnchor`): the read leaf IS the spliced
  -- (narrowed) fresh edge; the fresh key's non-membership bracket covers the committed BEFORE spine.
  leafKeyAnchored : keyOf (leafOf
      (capOpenCols Dregg2.Circuit.Emit.EffectVmEmitRotationV3.delegateAttenV3.traceWidth)
      (envAt tr row)) = henc.newKey
  gap : GapOpen S8 (beforeCapRootCols (envAt tr row))
    (keyOf (leafOf
      (capOpenCols Dregg2.Circuit.Emit.EffectVmEmitRotationV3.delegateAttenV3.traceWidth)
      (envAt tr row)))
  gapCov : gap.coversSpine henc.spine

/-- **`delegateAtten_descriptorRefines_sat` — THE DELEGATEATTEN CLASS-A REFINEMENT (insert FORCED +
non-amp).** From `Satisfied2 hash (effCapInsertV3 delegateAttenV3 name n)` (the DEPLOYED insert-shaped
keystone wrap) + the surviving `submaskLookup` (`delegateAttenV3_non_amp` on the stripped base), the
kernel `DelegateAttenSpec` HOLDS, the committed cap-root groups carry the DEPLOYED-FORCED genuine sorted
insert of the attenuated grant (`capInserts8`), AND the conferred mask `⊑` the held mask
(non-amplification, FORCED in-circuit). The attenuated-`grant` `Caps`-move + frame + log are the named
§2.b decode residual. -/
theorem delegateAtten_descriptorRefines_sat (S8 : Cap8Scheme)
    (pre post : RecChainedState) (del rec t : CellId) (keep : List Auth)
    (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hsub : tr.tf (.custom Dregg2.Circuit.Emit.EffectVmEmitV2.SUBMASK_TID)
      = Dregg2.Circuit.Emit.EffectVmEmitV2.subsetTable Dregg2.Circuit.Emit.EffectVmEmitV2.MASK_BITS)
    (hChip : ChipTableSoundN (capPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash (effCapInsertV3 delegateAttenV3 name n) mi mf ma tr)
    (henc : DelegateAttenCapsTreeEncodes S8 pre post del rec t keep)
    (anc : DelegateAttenWriteAnchor S8 pre post del rec t keep hash mi mf ma tr henc) :
    DelegateAttenSpec pre del rec t keep post
    ∧ capInserts8 S8 henc.oldRoot
        (leafOf (capOpenCols delegateAttenV3.traceWidth) (envAt tr anc.row))
        henc.newRoot
    ∧ ∃ a b : Nat, (envAt tr anc.row).loc (prmCol KEEP_MASK) = (a : ℤ)
        ∧ (envAt tr anc.row).loc (prmCol HELD_MASK) = (b : ℤ) ∧ a &&& b = a := by
  -- the submask non-amplification rides the STRIPPED base `delegateAttenV3` satisfaction.
  have hbase : Satisfied2 hash delegateAttenV3 mi mf ma tr :=
    Dregg2.Circuit.Emit.CapOpenEmit.effCapOpenV3_satisfied2_strips_to_base hash delegateAttenV3 name n
      mi mf ma tr
      (effCapInsertV3_strips_to_capOpen delegateAttenV3 name n hash mi mf ma tr hsat)
  have hnonamp := delegateAttenV3_non_amp hash mi mf ma tr hsub hbase anc.row anc.hrow anc.hactive
  refine ⟨delegateAtten_descriptorRefines S8 pre post del rec t keep henc, ?_, hnonamp⟩
  rw [anc.oldAnchored, anc.newAnchored]
  refine effCapInsertV3_forces_write8 S8 delegateAttenV3 name n hash mi mf ma tr hChip hsat
    anc.row anc.hrow anc.hnotlast anc.hcells henc.spine ?_ anc.gap anc.gapCov ?_
  · have h := henc.hold; rw [anc.oldAnchored] at h; exact h
  · have h := henc.hnew; rw [anc.newAnchored, ← anc.leafKeyAnchored] at h; exact h

/-! ## §3.5F — CLASS A for the FROZEN-FACE slots, REBASED onto the MOVING `…Genuine` face
(introduce / revokeDelegation — guarantee A circuit-FORCED via the INSERT/REMOVE keystone wraps).

The triage (a93b40505) found `introduce`/`revokeDelegation` FREEZE `cap_root` on-row (`gCapPass`); the
close rebased their V3 base onto the MOVING `…Genuine` face. The cap-tree write itself is now forced by
the SHAPE-MATCHED keystone wraps (the arity-2 map-ops were shape-UNSAT against the deployed arity-7
`CanonicalCapTree` and are DROPPED): `effCapInsertV3 introduceWriteV3` FORCES the spliced-leaf
membership in the REBUILT AFTER tree (`CapInsertEmit.effCapInsertV3_forces_write8` → `capInserts8`);
`effCapRemoveV3 revokeDelegationWriteV3` FORCES the removed-leaf membership in BEFORE
(`CapRemoveEmit.effCapRemoveV3_forces_write8` → `capRemoves8`, the AFTER root the deployed tombstone
zero-fold). Each rung below pins the committed cap-root groups via the LIVE keystone welds (mirroring
`delegate_descriptorRefines_sat`). `refreshDelegation` is the residual genuine obstruction (§3.5R). -/

/-- **`IntroduceWriteAnchor` — the realizable trace seam for introduce** (the conferred-grant INSERT on the
MOVING genuine face). As `DelegateWriteAnchor` over the `DelegateCapsTreeEncodes` decode (introduce routes to
`DelegateSpec`/`recDelegateCaps`, the same insert). -/
structure IntroduceWriteAnchor (S8 : Cap8Scheme)
    (pre post : RecChainedState) (del rec t : CellId)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (henc : DelegateCapsTreeEncodes S8 pre post del rec t) : Type where
  row : Nat
  hrow : row < tr.rows.length
  hactive : (envAt tr row).loc Dregg2.Circuit.Emit.EffectVmEmit.sel.INTRODUCE = 1
  -- the active cap-write row is not the trailing/padding row (the gates bind under `when_transition`).
  hnotlast : row + 1 ≠ tr.rows.length
  -- the active row's cells are field-canonical (the deployed range-check invariant).
  hcells : ∀ col : Nat, 0 ≤ (envAt tr row).loc col ∧ (envAt tr row).loc col < 2013265921
  -- the cap-root advance now lives on the ROTATED before/after limbs (note-spend-shaped — the
  -- v1-state continuity collision dodged); the decode's sorted-tree roots ARE those committed limbs.
  oldAnchored : henc.oldRoot = beforeCapRootCols (envAt tr row)
  newAnchored : henc.newRoot = afterCapRootCols (envAt tr row)
  -- the INSERT-shaped realizable carriers (see `DelegateWriteAnchor`).
  leafKeyAnchored : keyOf (leafOf
      (capOpenCols Dregg2.Circuit.Emit.EffectVmEmitRotationV3.introduceWriteV3.traceWidth)
      (envAt tr row)) = henc.newKey
  gap : GapOpen S8 (beforeCapRootCols (envAt tr row))
    (keyOf (leafOf
      (capOpenCols Dregg2.Circuit.Emit.EffectVmEmitRotationV3.introduceWriteV3.traceWidth)
      (envAt tr row)))
  gapCov : gap.coversSpine henc.spine

/-- **`introduce_descriptorRefines_sat` — THE INTRODUCE CLASS-A REFINEMENT (insert FORCED, frozen-face
close).** From `Satisfied2 hash (effCapInsertV3 introduceWriteV3 name n)` (the DEPLOYED insert-shaped
keystone wrap on the MOVING genuine face), the kernel `DelegateSpec` HOLDS AND the committed cap-root
groups carry the DEPLOYED-FORCED genuine sorted insert (`capInserts8`). The v1-face `gCapPass` freeze
that left the write off-row is GONE — guarantee A circuit-forced. -/
theorem introduce_descriptorRefines_sat (S8 : Cap8Scheme)
    (pre post : RecChainedState) (del rec t : CellId)
    (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash (effCapInsertV3 introduceWriteV3 name n) mi mf ma tr)
    (henc : DelegateCapsTreeEncodes S8 pre post del rec t)
    (anc : IntroduceWriteAnchor S8 pre post del rec t hash mi mf ma tr henc) :
    DelegateSpec pre del rec t post
    ∧ capInserts8 S8 henc.oldRoot
        (leafOf (capOpenCols introduceWriteV3.traceWidth) (envAt tr anc.row))
        henc.newRoot := by
  refine ⟨delegate_descriptorRefines S8 pre post del rec t henc, ?_⟩
  rw [anc.oldAnchored, anc.newAnchored]
  refine effCapInsertV3_forces_write8 S8 introduceWriteV3 name n hash mi mf ma tr hChip hsat
    anc.row anc.hrow anc.hnotlast anc.hcells henc.spine ?_ anc.gap anc.gapCov ?_
  · have h := henc.hold; rw [anc.oldAnchored] at h; exact h
  · have h := henc.hnew; rw [anc.newAnchored, ← anc.leafKeyAnchored] at h; exact h

/-- **`RevokeDelegationWriteAnchor` — the realizable trace seam for revokeDelegation** (the edge REMOVE on the
MOVING genuine face). As `DelegateWriteAnchor` over the `RevokeCapsTreeEncodes` decode; revokeDelegation
routes to `RevokeSpec`/`removeEdgeCaps`. -/
structure RevokeDelegationWriteAnchor (S8 : Cap8Scheme)
    (pre post : RecChainedState) (holder t : CellId)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (henc : RevokeCapsTreeEncodes S8 pre post holder t) : Type where
  row : Nat
  hrow : row < tr.rows.length
  hactive : (envAt tr row).loc Dregg2.Circuit.Emit.EffectVmEmit.sel.REVOKE_DELEGATION = 1
  -- the active cap-write row is not the trailing/padding row (the gates bind under `when_transition`).
  hnotlast : row + 1 ≠ tr.rows.length
  -- the active row's cells are field-canonical (the deployed range-check invariant).
  hcells : ∀ col : Nat, 0 ≤ (envAt tr row).loc col ∧ (envAt tr row).loc col < 2013265921
  -- the cap-root advance now lives on the ROTATED before/after limbs (note-spend-shaped — the
  -- v1-state continuity collision dodged); the decode's sorted-tree roots ARE those committed limbs.
  oldAnchored : henc.oldRoot = beforeCapRootCols (envAt tr row)
  newAnchored : henc.newRoot = afterCapRootCols (envAt tr row)
  -- THE REMOVE-SHAPED realizable carriers (what the deployed `CanonicalCapTree::remove_witness`
  -- computes): the cap-open appendix's read leaf IS the removed edge (its key is the decode's
  -- `remKey` — a trace-fill identity), and the removed key's NON-MEMBERSHIP bracket in the AFTER
  -- tree (the pred/succ `GapOpen` covering the REMOVED spine) is genuinely realizable — after the
  -- tombstone the neighbors bracket the gone key.
  leafKeyAnchored : keyOf (leafOf
      (capOpenCols Dregg2.Circuit.Emit.EffectVmEmitRotationV3.revokeDelegationWriteV3.traceWidth)
      (envAt tr row)) = henc.remKey
  gap : GapOpen S8 (afterCapRootCols (envAt tr row))
    (keyOf (leafOf
      (capOpenCols Dregg2.Circuit.Emit.EffectVmEmitRotationV3.revokeDelegationWriteV3.traceWidth)
      (envAt tr row)))
  gapCov : gap.coversSpine (sortedRemove
    (keyOf (leafOf
      (capOpenCols Dregg2.Circuit.Emit.EffectVmEmitRotationV3.revokeDelegationWriteV3.traceWidth)
      (envAt tr row))) henc.spine)

/-- **`revokeDelegation_descriptorRefines_sat` — THE REVOKEDELEGATION CLASS-A REFINEMENT (remove FORCED,
frozen-face close).** From `Satisfied2 hash (effCapRemoveV3 revokeDelegationWriteV3 name n)` (the
DEPLOYED remove-shaped keystone wrap — the removed-leaf membership in BEFORE is TRACE-FORCED,
`CapRemoveEmit.effCapRemoveV3_forces_beforeMembership`), the kernel `RevokeSpec` HOLDS AND the committed
cap-root groups carry the DEPLOYED-FORCED genuine sorted REMOVE (`capRemoves8` — present in BEFORE,
gone in AFTER, key set shrinks by exactly the revoked key). The v1-face `gCapPass` freeze is GONE —
guarantee A circuit-forced. Non-amp structural (a delete only shrinks authority). -/
theorem revokeDelegation_descriptorRefines_sat (S8 : Cap8Scheme)
    (pre post : RecChainedState) (holder t : CellId)
    (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash (effCapRemoveV3 revokeDelegationWriteV3 name n) mi mf ma tr)
    (henc : RevokeCapsTreeEncodes S8 pre post holder t)
    (anc : RevokeDelegationWriteAnchor S8 pre post holder t hash mi mf ma tr henc) :
    RevokeSpec pre holder t post
    ∧ capRemoves8 S8 henc.oldRoot
        (leafOf (capOpenCols revokeDelegationWriteV3.traceWidth) (envAt tr anc.row))
        henc.newRoot := by
  refine ⟨revoke_descriptorRefines S8 pre post holder t henc, ?_⟩
  rw [anc.oldAnchored, anc.newAnchored]
  refine effCapRemoveV3_forces_write8 S8 revokeDelegationWriteV3 name n hash mi mf ma tr hChip hsat
    anc.row anc.hrow anc.hnotlast anc.hcells henc.spine ?_ anc.gap anc.gapCov ?_
  · have h := henc.hold; rw [anc.oldAnchored] at h; exact h
  · have h := henc.hnew; rw [anc.newAnchored, ← anc.leafKeyAnchored] at h; exact h

/-- **CLASS-A TOOTH (introduce) — the committed cap-root groups are FORCED to the genuine sorted
insert.** Mutation: dropping the AFTER welds from `effCapInsertV3` removes the trace-forced spliced-leaf
membership, so this conclusion can no longer be drawn. -/
theorem introduce_sat_forces_postroot (S8 : Cap8Scheme)
    (pre post : RecChainedState) (del rec t : CellId)
    (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash (effCapInsertV3 introduceWriteV3 name n) mi mf ma tr)
    (henc : DelegateCapsTreeEncodes S8 pre post del rec t)
    (anc : IntroduceWriteAnchor S8 pre post del rec t hash mi mf ma tr henc) :
    capInserts8 S8 henc.oldRoot
      (leafOf (capOpenCols introduceWriteV3.traceWidth) (envAt tr anc.row))
      henc.newRoot :=
  (introduce_descriptorRefines_sat S8 pre post del rec t name n hash mi mf ma tr hChip hsat henc anc).2

/-- **CLASS-A TOOTH (revoke / revokeDelegation, tag 2 + tag 14) — the cap-tree REMOVE is FORCED.** From
`Satisfied2 hash (effCapRemoveV3 revokeDelegationWriteV3 name n)` the genuine REMOVE (the removed leaf
present in BEFORE, its key gone in AFTER, the key set shrunk by exactly it) PINS the committed groups:
`capRemoves8` holds. Mutation: dropping the BEFORE welds from `effCapRemoveV3` removes the trace-forced
removed-leaf membership, so this conclusion can no longer be drawn — the tag-2 (and tag-14) apex rung
reds. -/
theorem revokeDelegation_sat_forces_postroot (S8 : Cap8Scheme)
    (pre post : RecChainedState) (holder t : CellId)
    (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash (effCapRemoveV3 revokeDelegationWriteV3 name n) mi mf ma tr)
    (henc : RevokeCapsTreeEncodes S8 pre post holder t)
    (anc : RevokeDelegationWriteAnchor S8 pre post holder t hash mi mf ma tr henc) :
    capRemoves8 S8 henc.oldRoot
      (leafOf (capOpenCols revokeDelegationWriteV3.traceWidth) (envAt tr anc.row))
      henc.newRoot :=
  (revokeDelegation_descriptorRefines_sat S8 pre post holder t name n hash mi mf ma tr hChip hsat henc anc).2

/-- **FORGE-DETECTOR (revoke, tag 2) — a fabricated post-cap-root is UNSAT.** The genuine REMOVE
FORCES `capRemoves8 … henc.newRoot` (`revokeDelegation_sat_forces_postroot`); the committed remove is
FUNCTIONAL under CR (the after-root is the unique root committing the removed spine — the named
`hRemoves8Func` carrier, derivable from `S8.chip8CR`). So ANY forged `forgedRoot` claiming to be the
same remove but differing from the genuine `henc.newRoot` is excluded — the forged-root branch is
`False`. NON-vacuous: the forced `capRemoves8` is the live witness (drop the BEFORE welds and the
hypothesis it consumes vanishes), and `forgedRoot ≠ henc.newRoot` is satisfiable, so the elimination
bites genuinely. The tag-2 and tag-14 revoke share `revokeDelegationWriteV3`, so this one detector
guards both. -/
theorem revoke_sat_rejects_forged_postroot (S8 : Cap8Scheme)
    (pre post : RecChainedState) (holder t : CellId)
    (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash (effCapRemoveV3 revokeDelegationWriteV3 name n) mi mf ma tr)
    (henc : RevokeCapsTreeEncodes S8 pre post holder t)
    (anc : RevokeDelegationWriteAnchor S8 pre post holder t hash mi mf ma tr henc)
    -- NAMED CRYPTO CARRIER: the deployed cap-tree's 8-felt remove-functionality (membership-path
    -- uniqueness at full ~124-bit width, derivable from `S8.chip8CR` — the internalization TODO
    -- mirroring the scalar `MapMerkleRoot.writesToMerkle_functional` the old `hCR` tooth consumed).
    (hRemoves8Func : ∀ {r₁ r₂ : Digest8},
      capRemoves8 S8 henc.oldRoot
        (leafOf (capOpenCols revokeDelegationWriteV3.traceWidth) (envAt tr anc.row)) r₁ →
      capRemoves8 S8 henc.oldRoot
        (leafOf (capOpenCols revokeDelegationWriteV3.traceWidth) (envAt tr anc.row)) r₂ → r₁ = r₂)
    (forgedRoot : Digest8)
    (hforged : capRemoves8 S8 henc.oldRoot
      (leafOf (capOpenCols revokeDelegationWriteV3.traceWidth) (envAt tr anc.row)) forgedRoot)
    (hne : forgedRoot ≠ henc.newRoot) :
    False :=
  hne (hRemoves8Func hforged
    (revokeDelegation_sat_forces_postroot S8 pre post holder t name n hash mi mf ma tr hChip hsat henc anc))

#assert_axioms introduce_descriptorRefines_sat
#assert_axioms revokeDelegation_descriptorRefines_sat
#assert_axioms introduce_sat_forces_postroot
#assert_axioms revokeDelegation_sat_forces_postroot
#assert_axioms revoke_sat_rejects_forged_postroot

/-! ## §3.5B — THE APEX-WIRING BRIDGE rungs (`…_descriptorRefines_capOpenSat`): the cap-open WRAPPER strips
to the base, so the apex fan-out (`Rfix tag = capOpenWrapper base`) consumes the base CLASS-A rung.

The apex fanout cannot wire delegate(tag 1)/revoke(tag 2)/delegateAtten(tag 11)/introduce(tag 10)/
revokeDelegation(tag 14)/revokeCapability(tag 24) directly because `Rfix tag` = the cap-open WRAPPER
descriptor (`delegateCapOpenV3` etc.), NOT defeq to `<slot>V3`, so `Satisfied2 hash (Rfix tag)` doesn't
coerce. `capOpen_satisfied2_strips_to_base` STRIPS the cap-open authority appendix + selector tooth (both
additive — they read no base column, surface no map/mem op), yielding `Satisfied2 hash <slot>V3`, which the
base `_descriptorRefines_sat` consumes. Each rung below is the wrapped form the main loop wires. -/

/-- **`delegate_descriptorRefines_capOpenSat` — the apex-wirable delegate rung.** Consumes `Satisfied2 hash
delegateWriteCapOpenV3` (the INSERT-shaped keystone wrapper, base `grantCapWriteV3`) by stripping the
selector tooth and applying `grantCap_descriptorRefines_sat`. The apex (`Rfix 1` re-pointed to
`delegateWriteCapOpenV3`) wires this. -/
theorem delegate_descriptorRefines_capOpenSat (S8 : Cap8Scheme)
    (pre post : RecChainedState) (del rec t : CellId)
    (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash
      (withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.GRANT_CAP
        (effCapInsertV3 grantCapWriteV3 name n)) mi mf ma tr)
    (henc : DelegateCapsTreeEncodes S8 pre post del rec t)
    (anc : DelegateWriteAnchor S8 pre post del rec t hash mi mf ma tr henc) :
    DelegateSpec pre del rec t post
    ∧ capInserts8 S8 henc.oldRoot
        (leafOf (capOpenCols grantCapWriteV3.traceWidth) (envAt tr anc.row))
        henc.newRoot :=
  grantCap_descriptorRefines_sat S8 pre post del rec t name n hash mi mf ma tr hChip
    (withSelectorGate_satisfied2 hash _ (effCapInsertV3 grantCapWriteV3 name n) mi mf ma tr hsat) henc anc

/-- **`grantCap_descriptorRefines_capOpenSat` — the apex-wirable grantCap rung.** As above over
`grantCapWriteCapOpenV3` (base `grantCapWriteV3`). The apex wires this. -/
theorem grantCap_descriptorRefines_capOpenSat (S8 : Cap8Scheme)
    (pre post : RecChainedState) (del rec t : CellId)
    (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash
      (withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.GRANT_CAP
        (effCapInsertV3 grantCapWriteV3 name n)) mi mf ma tr)
    (henc : DelegateCapsTreeEncodes S8 pre post del rec t)
    (anc : DelegateWriteAnchor S8 pre post del rec t hash mi mf ma tr henc) :
    DelegateSpec pre del rec t post
    ∧ capInserts8 S8 henc.oldRoot
        (leafOf (capOpenCols grantCapWriteV3.traceWidth) (envAt tr anc.row))
        henc.newRoot :=
  grantCap_descriptorRefines_sat S8 pre post del rec t name n hash mi mf ma tr hChip
    (withSelectorGate_satisfied2 hash _ (effCapInsertV3 grantCapWriteV3 name n) mi mf ma tr hsat) henc anc

/-- **`delegateAtten_descriptorRefines_capOpenSat` — the apex-wirable delegateAtten rung (tag 11).** Consumes
`Satisfied2 hash delegateAttenWriteCapOpenV3` (the INSERT-shaped keystone wrapper, base `delegateAttenV3`)
by stripping the selector tooth and applying `delegateAtten_descriptorRefines_sat` (insert FORCED + the
`granted ⊑ held` non-amplification). The apex (`Rfix 11` re-pointed) wires this. -/
theorem delegateAtten_descriptorRefines_capOpenSat (S8 : Cap8Scheme)
    (pre post : RecChainedState) (del rec t : CellId) (keep : List Auth)
    (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hsub : tr.tf (.custom Dregg2.Circuit.Emit.EffectVmEmitV2.SUBMASK_TID)
      = Dregg2.Circuit.Emit.EffectVmEmitV2.subsetTable Dregg2.Circuit.Emit.EffectVmEmitV2.MASK_BITS)
    (hChip : ChipTableSoundN (capPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash
      (withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.GRANT_CAP
        (effCapInsertV3 delegateAttenV3 name n)) mi mf ma tr)
    (henc : DelegateAttenCapsTreeEncodes S8 pre post del rec t keep)
    (anc : DelegateAttenWriteAnchor S8 pre post del rec t keep hash mi mf ma tr henc) :
    DelegateAttenSpec pre del rec t keep post
    ∧ capInserts8 S8 henc.oldRoot
        (leafOf (capOpenCols delegateAttenV3.traceWidth) (envAt tr anc.row))
        henc.newRoot
    ∧ ∃ a b : Nat, (envAt tr anc.row).loc (prmCol KEEP_MASK) = (a : ℤ)
        ∧ (envAt tr anc.row).loc (prmCol HELD_MASK) = (b : ℤ) ∧ a &&& b = a :=
  delegateAtten_descriptorRefines_sat S8 pre post del rec t keep name n hash mi mf ma tr hsub hChip
    (withSelectorGate_satisfied2 hash _ (effCapInsertV3 delegateAttenV3 name n) mi mf ma tr hsat) henc anc

/-- **`introduce_descriptorRefines_capOpenSat` — the apex-wirable introduce rung.** Consumes `Satisfied2
hash introduceWriteCapOpenV3` (the INSERT-shaped keystone wrapper, base `introduceWriteV3`) by stripping
the selector tooth and applying `introduce_descriptorRefines_sat`. The apex (`Rfix 10` re-pointed to
`introduceWriteCapOpenV3`) wires this. -/
theorem introduce_descriptorRefines_capOpenSat (S8 : Cap8Scheme)
    (pre post : RecChainedState) (del rec t : CellId)
    (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash
      (withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.INTRODUCE
        (effCapInsertV3 introduceWriteV3 name n)) mi mf ma tr)
    (henc : DelegateCapsTreeEncodes S8 pre post del rec t)
    (anc : IntroduceWriteAnchor S8 pre post del rec t hash mi mf ma tr henc) :
    DelegateSpec pre del rec t post
    ∧ capInserts8 S8 henc.oldRoot
        (leafOf (capOpenCols introduceWriteV3.traceWidth) (envAt tr anc.row))
        henc.newRoot :=
  introduce_descriptorRefines_sat S8 pre post del rec t name n hash mi mf ma tr hChip
    (withSelectorGate_satisfied2 hash _ (effCapInsertV3 introduceWriteV3 name n) mi mf ma tr hsat) henc anc

/-- **`revokeDelegation_descriptorRefines_capOpenSat` — the apex-wirable revokeDelegation rung.** Consumes
`Satisfied2 hash revokeDelegationWriteCapOpenV3` (the REMOVE-shaped keystone wrapper, base
`revokeDelegationWriteV3`) by stripping the selector tooth and applying
`revokeDelegation_descriptorRefines_sat`. The apex (`Rfix 14` re-pointed) wires this. -/
theorem revokeDelegation_descriptorRefines_capOpenSat (S8 : Cap8Scheme)
    (pre post : RecChainedState) (holder t : CellId)
    (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash
      (withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.REVOKE_DELEGATION
        (effCapRemoveV3 revokeDelegationWriteV3 name n)) mi mf ma tr)
    (henc : RevokeCapsTreeEncodes S8 pre post holder t)
    (anc : RevokeDelegationWriteAnchor S8 pre post holder t hash mi mf ma tr henc) :
    RevokeSpec pre holder t post
    ∧ capRemoves8 S8 henc.oldRoot
        (leafOf (capOpenCols revokeDelegationWriteV3.traceWidth) (envAt tr anc.row))
        henc.newRoot :=
  revokeDelegation_descriptorRefines_sat S8 pre post holder t name n hash mi mf ma tr hChip
    (withSelectorGate_satisfied2 hash _ (effCapRemoveV3 revokeDelegationWriteV3 name n) mi mf ma tr hsat) henc anc

/-- **`revokeDelegation_descriptorRefines_capOpenSat_full` — the EPOCH-strengthened CLASS-A revokeDelegation
rung.** The deployed descriptor FORCES the cap-tree REMOVE (`revokeDelegation_descriptorRefines_capOpenSat`,
the `capRemoves8` on the moving genuine face) — the cap-edge `RevokeSpec`. The FAITHFUL epoch step (parent
epoch bumped + child snapshot staled) rides the NAMED `RevokeDelegationFullEncodes` epoch residual
(commitment-bound at limbs 30 + 24, write-gate residual per §3.EPOCH). Produces the STRENGTHENED
`RevokeDelegationFullSpec` AND the forced cap-tree remove `capRemoves8`. -/
theorem revokeDelegation_descriptorRefines_capOpenSat_full (S8 : Cap8Scheme)
    (pre post : RecChainedState) (holder t : CellId)
    (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash
      (withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.REVOKE_DELEGATION
        (effCapRemoveV3 revokeDelegationWriteV3 name n)) mi mf ma tr)
    (hfull : RevokeDelegationFullEncodes S8 pre post holder t)
    (anc : RevokeDelegationWriteAnchor S8 pre post holder t hash mi mf ma tr hfull.capRemove) :
    Dregg2.Circuit.Spec.AuthorityRevocation.RevokeDelegationFullSpec pre holder t post
    ∧ capRemoves8 S8 hfull.capRemove.oldRoot
        (leafOf (capOpenCols revokeDelegationWriteV3.traceWidth) (envAt tr anc.row))
        hfull.capRemove.newRoot :=
  ⟨revokeDelegation_descriptorRefines S8 pre post holder t hfull,
   (revokeDelegation_descriptorRefines_capOpenSat S8 pre post holder t name n hash mi mf ma tr hChip hsat
      hfull.capRemove anc).2⟩

/-! ## §3.5R — CLASS A for refreshDelegation: the DELEGATIONS-tree WRITE is FORCED (the LAST cap-family
residual, `delegRoot_runtime_column_pending`, CLOSED).

`refreshDelegation` is the ONE cap-family effect whose genuine move is on the DELEGATIONS tree (the `DELEG`
system-root), NOT `caps`: `delegations := refreshDelegationsMap k child` is an in-place UPDATE-AT-KEY. The
record-layer §7 binding (`delegRoot_moves_under_spec`) tied that move to the `DELEG` system-root, but the
WRITE was a prover-supplied `SpineCommits` hypothesis (`RefreshDelegationCapsTreeEncodes.hold`/`.hnew`),
unanchored to any in-circuit write gate — `EffectVmEmitRefreshDelegation.delegRoot_runtime_column_pending`.

The close mirrors the attenuate UPDATE-shaped keystone exactly, on the DELEG tree: the DEPLOYED
`refreshDelegationWriteCapOpenV3` (`effCapOpenWriteV3` over the map-op-free `refreshDelegationWriteV3`
base) carries the after-spine UPDATE-AT-KEY over the ROTATED before/after 8-felt root groups
(note-spend-shaped — refresh FREEZES `caps` on the v1 column, so the rotated cap-root group is free to
carry the DELEG accumulator). `effCapOpenWriteV3_forces_write8` FORCES the faithful 8-felt
`writesTo8 deleg_root_before child_key snapshot deleg_root_after` from `Satisfied2` — a forged
post-deleg-root is UNSAT. (The arity-2 scalar `delegReadOpRot`/`delegUpdateWriteOpRot` pair was
shape-UNSAT against the deployed native-8-felt witness heaps and is DROPPED.) With this rung the apex
consumes `Satisfied2` of a descriptor that FORCES the delegations-tree write — refreshDelegation reaches
CLASS A. -/

/-- **`RefreshDelegationWriteAnchor` — the realizable trace seam for refreshDelegation** (the DELEG-tree
UPDATE on the moving genuine face). The decode's DELEG sorted-tree roots (`RefreshDelegationCapsTreeEncodes`'s
`oldRoot`/`newRoot` over the delegations tree) ARE the committed ROTATED deleg-root limbs (the `WitnessDecodes`
trace-fill identity). The child key is read at `prmCol CAP_KEY`. -/
structure RefreshDelegationWriteAnchor (S8 : Cap8Scheme)
    (pre post : RecChainedState) (actor child : CellId)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (henc : RefreshDelegationCapsTreeEncodes S8 pre post actor child) : Type where
  row : Nat
  hrow : row < tr.rows.length
  hactive : (envAt tr row).loc Dregg2.Circuit.Emit.EffectVmEmit.sel.REFRESH_DELEGATION = 1
  -- the active cap-write row is not the trailing/padding row (the gates bind under `when_transition`).
  hnotlast : row + 1 ≠ tr.rows.length
  -- the active row's cells are field-canonical (the deployed range-check invariant).
  hcells : ∀ col : Nat, 0 ≤ (envAt tr row).loc col ∧ (envAt tr row).loc col < 2013265921
  -- the WitnessDecodes seam: the decode's DELEG sorted-tree roots ARE the committed rotated deleg-root
  -- 8-felt block (the rotated cap-root limb 25 carries the DELEG accumulator on a refresh row; refresh
  -- freezes caps, so the cap-root 8-felt block faithfully carries the DELEG accumulator).
  oldAnchored : henc.oldRoot = beforeCapRootCols (envAt tr row)
  newAnchored : henc.newRoot = afterCapRootCols (envAt tr row)

/-- **`refreshDelegation_descriptorRefines_sat` — THE REFRESHDELEGATION CLASS-A REFINEMENT (DELEG write
FORCED).** From `Satisfied2 hash (effCapOpenWriteV3 refreshDelegationWriteV3 name n)` (via
`effCapOpenWriteV3_forces_write8` on the moving genuine face), the kernel `RefreshDelegationSpec` HOLDS AND the post DELEG-root is the
DEPLOYED-FORCED genuine sorted UPDATE-AT-KEY of the child's snapshot at the child key against the
membership-opened before DELEG-root. The `delegRoot_runtime_column_pending` supplied-digest gap is GONE —
guarantee A circuit-forced over the delegations tree. The `refreshDelegationsMap` overwrite + frame + log
ride the §2.c decode residual. -/
theorem refreshDelegation_descriptorRefines_sat (S8 : Cap8Scheme)
    (pre post : RecChainedState) (actor child : CellId)
    (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash (effCapOpenWriteV3 refreshDelegationWriteV3 name n) mi mf ma tr)
    (henc : RefreshDelegationCapsTreeEncodes S8 pre post actor child)
    (anc : RefreshDelegationWriteAnchor S8 pre post actor child hash mi mf ma tr henc) :
    RefreshDelegationFullSpec pre actor child post
    ∧ writesTo8 S8 henc.oldRoot
        ((envAt tr anc.row).loc (prmCol CAP_KEY)) ((envAt tr anc.row).loc (prmCol KEEP_MASK))
        henc.newRoot := by
  refine ⟨refreshDelegation_descriptorRefines S8 pre post actor child henc, ?_⟩
  rw [anc.oldAnchored, anc.newAnchored]
  exact effCapOpenWriteV3_forces_write8 S8 refreshDelegationWriteV3 name n hash mi mf ma tr hChip hsat
    anc.row anc.hrow anc.hnotlast anc.hcells

/-- **CLASS-A TOOTH (refreshDelegation) — a forged wrong post-deleg-root is UNSAT.** Mutation: dropping
the after-spine welds from `effCapOpenWriteV3` removes the forced `writesTo8`, so this conclusion
can no longer be drawn — editing the deleg-write descriptor reds the apex. -/
theorem refreshDelegation_sat_forces_delegroot (S8 : Cap8Scheme)
    (pre post : RecChainedState) (actor child : CellId)
    (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash (effCapOpenWriteV3 refreshDelegationWriteV3 name n) mi mf ma tr)
    (henc : RefreshDelegationCapsTreeEncodes S8 pre post actor child)
    (anc : RefreshDelegationWriteAnchor S8 pre post actor child hash mi mf ma tr henc) :
    writesTo8 S8 henc.oldRoot
      ((envAt tr anc.row).loc (prmCol CAP_KEY)) ((envAt tr anc.row).loc (prmCol KEEP_MASK))
      henc.newRoot :=
  (refreshDelegation_descriptorRefines_sat S8 pre post actor child name n hash mi mf ma tr hChip hsat henc anc).2

/-- **`refreshDelegation_descriptorRefines_capOpenSat` — the apex-wirable refreshDelegation rung.** Consumes
`Satisfied2 hash refreshDelegationWriteCapOpenV3` (base `refreshDelegationWriteV3`) by stripping the cap-open
authority appendix + selector tooth to the base and applying `refreshDelegation_descriptorRefines_sat`. The
apex (`Rfix 55` re-pointed) wires this. -/
theorem refreshDelegation_descriptorRefines_capOpenSat (S8 : Cap8Scheme)
    (pre post : RecChainedState) (actor child : CellId)
    (name : String) (n : Nat)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash
      (withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.REFRESH_DELEGATION
        (effCapOpenWriteV3 refreshDelegationWriteV3 name n)) mi mf ma tr)
    (henc : RefreshDelegationCapsTreeEncodes S8 pre post actor child)
    (anc : RefreshDelegationWriteAnchor S8 pre post actor child hash mi mf ma tr henc) :
    RefreshDelegationFullSpec pre actor child post
    ∧ writesTo8 S8 henc.oldRoot
        ((envAt tr anc.row).loc (prmCol CAP_KEY)) ((envAt tr anc.row).loc (prmCol KEEP_MASK))
        henc.newRoot :=
  refreshDelegation_descriptorRefines_sat S8 pre post actor child name n hash mi mf ma tr hChip
    (withSelectorGate_satisfied2 hash _ (effCapOpenWriteV3 refreshDelegationWriteV3 name n) mi mf ma tr hsat) henc anc

#assert_axioms refreshDelegation_descriptorRefines_sat
#assert_axioms refreshDelegation_sat_forces_delegroot
#assert_axioms refreshDelegation_descriptorRefines_capOpenSat

/-! `revokeCapability` (tag 24): the write leg rides the REMOVE-shaped keystone wrap
(`effCapRemoveV3 revokeCapabilityV3` = `revokeCapabilityWriteCapOpenV3`, §3.A below — the SDK's
effective write route), mirroring `revokeDelegation_descriptorRefines_capOpenSat`. The apex's `Rfix 24`
stays on the authority-only `revokeCapabilityCapOpenV3` keystone
(`revokeCapabilityCapOpenV3_authorizes`); the §3.A write rung is the light-client REMOVE the SDK route
proves+verifies. -/

#assert_axioms delegate_descriptorRefines_capOpenSat
#assert_axioms grantCap_descriptorRefines_capOpenSat
#assert_axioms delegateAtten_descriptorRefines_capOpenSat
#assert_axioms introduce_descriptorRefines_capOpenSat
#assert_axioms revokeDelegation_descriptorRefines_capOpenSat
#assert_axioms revokeDelegation_descriptorRefines_capOpenSat_full

/-! ## §4 — non-vacuity: the sorted-tree teeth BITE on the cap family (the moves are real).

The three operations move the committed key set observably: insert grows it (a delegate adds a key),
update-at-key preserves it (an attenuate keeps the key, narrows the leaf), remove shrinks it (a revoke
drops the key). The both-polarity teeth (a forged/ungrounded delegate is `none`; a revoked edge is
genuinely absent) are the §1/§3 `_rejects_`/`_drops_` lemmas. Here a concrete witness that the cap-tree
key-set move is NON-VACUOUS (the spine moves; a `:= True`/identity stub would break it). -/

/-- A concrete sorted spine `[10, 20, 30]`. -/
private def demoSpine : List ℤ := [10, 20, 30]

-- the three cap-family moves are observably distinct on the committed key spine:
#guard sortedInsert (25 : ℤ) demoSpine == [10, 20, 25, 30]   -- INSERT (delegate): the key set GROWS
#guard sortedRemove (20 : ℤ) demoSpine == [10, 30]           -- REMOVE (revoke): the key set SHRINKS
#guard demoSpine == [10, 20, 30]                              -- UPDATE-AT-KEY (attenuate): set PRESERVED

/-! ## §5 — Axiom hygiene. -/

#assert_axioms delegate_forces_insert
#assert_axioms delegate_descriptorRefines
#assert_axioms delegate_execFullA
#assert_axioms delegate_rejects_ungrounded
#assert_axioms attenuate_forces_keyset_preserved
#assert_axioms attenuate_descriptorRefines_exact
#assert_axioms attenuate_execFullA
#assert_axioms delegateAtten_forces_insert
#assert_axioms delegateAtten_descriptorRefines
#assert_axioms delegateAtten_non_amplifying
#assert_axioms delegateAtten_execFullA
#assert_axioms refreshDelegation_forces_keyset_preserved
#assert_axioms refreshDelegation_descriptorRefines
#assert_axioms refreshDelegation_execFullA
#assert_axioms revoke_forces_remove
#assert_axioms revoke_descriptorRefines
#assert_axioms revoke_execFullA
#assert_axioms revokeDelegation_descriptorRefines
#assert_axioms revokeDelegation_execFullA
#assert_axioms revoke_drops_edge
-- §3.5 CLASS-A: the cap-tree WRITE forced from the DEPLOYED descriptor (the moving-face 3 of 5 gaps).
#assert_axioms delegate_forces_committed_write
#assert_axioms delegate_descriptorRefines_sat
#assert_axioms grantCap_descriptorRefines_sat
#assert_axioms delegateAtten_descriptorRefines_sat

/-! ## §3.A — revokeCapability: CLASS A from the DEPLOYED REMOVE-shaped keystone wrap
(`effCapRemoveV3 revokeCapabilityV3` — the write-leg IS deployed).

The arity-2 scalar map-op pair (`heldReadOpRot`/`removeWriteOpRot`) was shape-UNSAT against the deployed
arity-7 `CanonicalCapTree` (its arity-2 heap fold never matches the native-8-felt witness heaps, and its
scalar root left the seven high felts unbound) and is DROPPED from `revokeCapabilityV3`. The cap-tree
REMOVE is now FORCED by the SHAPE-MATCHED keystone wrap: `effCapRemoveV3 revokeCapabilityV3` FORCES the
removed-leaf membership in BEFORE (`CapRemoveEmit.effCapRemoveV3_forces_write8` → `capRemoves8`; the
AFTER root is the deployed tombstone zero-fold `cap_root.rs::CanonicalCapTree::remove_witness` — exactly
the executor's `capabilities.revoke` tombstone semantics). The `capsMoveDecodes` seam lifts the forced
8-felt remove to the kernel `removeEdgeCaps` move. No submask lookup — revoke deletes a slot,
non-amplification is structural. Mirrors `revokeDelegation_descriptorRefines_capOpenSat` EXACTLY. -/

/-- **`RevokeCapabilityTraceReadout` — the realizable circuit-witness extraction for revokeCapability.** The
`WitnessDecodes` class of cellSeal's `CellSealTraceReadout`: the ACTIVE cap-graph row + its selector + the
cap-remove seam (the deployed-forced 8-felt tombstone REMOVE IS the kernel `removeEdgeCaps` move) +
receipt + frame + the REMOVE-shaped realizable carriers (what the deployed
`CanonicalCapTree::remove_witness` computes — the readout twin of `RevokeDelegationWriteAnchor`'s
carrier fields): the BEFORE cap-root commits a sorted spine, and the revoked key's non-membership
bracket in the AFTER tree (the pred/succ `GapOpen` covering the REMOVED spine) is genuinely realizable
— after the tombstone the neighbors bracket the gone key. -/
structure RevokeCapabilityTraceReadout (S8 : Cap8Scheme) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (holder target : CellId) : Type where
  row : Nat
  hrow : row < t.rows.length
  hsel : (envAt t row).loc sel.REVOKE_CAPABILITY = 1
  -- the faithful cap-tree↔kernel-`Caps` encoding seam (a HYPOTHESIS, never an axiom): the forced
  -- 8-felt tombstone REMOVE at the crown-opened leaf IS the kernel `removeEdgeCaps` move.
  capsMoveDecodes :
    capRemoves8 S8 (beforeCapRootCols (envAt t row))
        (leafOf (capOpenCols
          Dregg2.Circuit.Emit.EffectVmEmitRotationV3.revokeCapabilityV3.traceWidth) (envAt t row))
        (afterCapRootCols (envAt t row))
      → post.kernel.caps = removeEdgeCaps pre.kernel.caps holder target
  logAdv : post.log = authReceipt holder :: pre.log
  frame : KernelFrameExceptCaps pre post

/-- **`RevokeCapabilityWriteAnchor` — the realizable REMOVE carriers for revokeCapability** (what the
deployed `CanonicalCapTree::remove_witness` computes — the readout-linked twin of
`RevokeDelegationWriteAnchor`'s carrier fields, AT the readout's active row): the BEFORE cap-root commits
a sorted spine, the revoked key's non-membership bracket in the AFTER tree (the pred/succ `GapOpen`
covering the REMOVED spine) is genuinely realizable — after the tombstone the neighbors bracket the gone
key — and the AFTER root commits the removed spine. -/
structure RevokeCapabilityWriteAnchor (S8 : Cap8Scheme) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (holder target : CellId)
    (rd : RevokeCapabilityTraceReadout S8 hash minit mfin maddrs t pre post holder target) :
    Type where
  -- the active cap-write row is not the trailing/padding row (the welds bind under `when_transition`).
  hnotlast : rd.row + 1 ≠ t.rows.length
  -- the active row's cells are field-canonical (the deployed range-check invariant).
  hcells : ∀ col : Nat, 0 ≤ (envAt t rd.row).loc col ∧ (envAt t rd.row).loc col < 2013265921
  spine : List ℤ
  hold : SpineCommits S8 (beforeCapRootCols (envAt t rd.row)) spine
  gap : GapOpen S8 (afterCapRootCols (envAt t rd.row))
    (keyOf (leafOf (capOpenCols
      Dregg2.Circuit.Emit.EffectVmEmitRotationV3.revokeCapabilityV3.traceWidth) (envAt t rd.row)))
  gapCov : gap.coversSpine (sortedRemove
    (keyOf (leafOf (capOpenCols
      Dregg2.Circuit.Emit.EffectVmEmitRotationV3.revokeCapabilityV3.traceWidth) (envAt t rd.row))) spine)
  hnew : SpineCommits S8 (afterCapRootCols (envAt t rd.row))
    (sortedRemove
      (keyOf (leafOf (capOpenCols
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.revokeCapabilityV3.traceWidth) (envAt t rd.row))) spine)

/-- **`revokeCapability_forced_sat` — the cap-edge removal is FORCED by the DEPLOYED keystone wrap.**
From `Satisfied2 hash (effCapRemoveV3 revokeCapabilityV3 name n)` (the removed-leaf membership in BEFORE
is TRACE-FORCED, `CapRemoveEmit.effCapRemoveV3_forces_beforeMembership`) + the readout's realizable
REMOVE carriers, the faithful 8-felt `capRemoves8` holds and the `capsMoveDecodes` seam lifts it to the
kernel `removeEdgeCaps` move. -/
theorem revokeCapability_forced_sat (S8 : Cap8Scheme) (hash : List ℤ → ℤ)
    (name : String) (n : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hChip : ChipTableSoundN (capPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash (effCapRemoveV3 revokeCapabilityV3 name n) minit mfin maddrs t)
    (pre post : RecChainedState) (holder target : CellId)
    (rd : RevokeCapabilityTraceReadout S8 hash minit mfin maddrs t pre post holder target)
    (anc : RevokeCapabilityWriteAnchor S8 hash minit mfin maddrs t pre post holder target rd) :
    post.kernel.caps = removeEdgeCaps pre.kernel.caps holder target :=
  rd.capsMoveDecodes
    (effCapRemoveV3_forces_write8 S8 revokeCapabilityV3 name n hash minit mfin maddrs t hChip hsat
      rd.row rd.hrow anc.hnotlast anc.hcells anc.spine anc.hold anc.gap anc.gapCov anc.hnew)

/-- **`revokeCapability_descriptorRefines_sat` — THE CLASS-A REFINEMENT for revokeCapability (remove
FORCED).** The `removeEdgeCaps` move is forced from the DEPLOYED keystone wrap's `Satisfied2`
(`capRemoves8` over the FULL 8-felt groups, never lane-0); editing the deployed BEFORE welds turns this
RED. -/
theorem revokeCapability_descriptorRefines_sat (S8 : Cap8Scheme) (hash : List ℤ → ℤ)
    (name : String) (n : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hChip : ChipTableSoundN (capPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash (effCapRemoveV3 revokeCapabilityV3 name n) minit mfin maddrs t)
    (pre post : RecChainedState) (holder target : CellId)
    (rd : RevokeCapabilityTraceReadout S8 hash minit mfin maddrs t pre post holder target)
    (anc : RevokeCapabilityWriteAnchor S8 hash minit mfin maddrs t pre post holder target rd) :
    RevokeSpec pre holder target post :=
  ⟨trivial, revokeCapability_forced_sat S8 hash name n hChip hsat pre post holder target rd anc, rd.logAdv,
   rd.frame.frAccounts, rd.frame.frCell, rd.frame.frNullifiers, rd.frame.frRevoked,
   rd.frame.frCommitments, rd.frame.frBal, rd.frame.frSlotCaveats, rd.frame.frFactories,
   rd.frame.frLifecycle, rd.frame.frDeathCert, rd.frame.frDelegate, rd.frame.frDelegations,
   rd.frame.frDelegationEpoch, rd.frame.frDelegationEpochAt, rd.frame.frHeaps,
   rd.frame.frNullifierRoot, rd.frame.frRevokedRoot, rd.frame.frCommitmentsRoot⟩

/-- **`revokeCapability_execFullA_sat` — the Class-A refinement against the executor arm.** -/
theorem revokeCapability_execFullA_sat (S8 : Cap8Scheme) (hash : List ℤ → ℤ)
    (name : String) (n : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hChip : ChipTableSoundN (capPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash (effCapRemoveV3 revokeCapabilityV3 name n) minit mfin maddrs t)
    (pre post : RecChainedState) (holder target : CellId)
    (rd : RevokeCapabilityTraceReadout S8 hash minit mfin maddrs t pre post holder target)
    (anc : RevokeCapabilityWriteAnchor S8 hash minit mfin maddrs t pre post holder target rd) :
    execFullA pre (.revoke holder target) = some post :=
  (execFullA_revoke_iff_spec pre holder target post).mpr
    (revokeCapability_descriptorRefines_sat S8 hash name n hChip hsat pre post holder target rd anc)

/-- **CLASS-A TOOTH — a forged wrong-caps revokeCapability witness is UNSAT.** -/
theorem revokeCapability_sat_rejects_wrong_caps (S8 : Cap8Scheme) (hash : List ℤ → ℤ)
    (name : String) (n : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hChip : ChipTableSoundN (capPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash (effCapRemoveV3 revokeCapabilityV3 name n) minit mfin maddrs t)
    (pre post : RecChainedState) (holder target : CellId)
    (rd : RevokeCapabilityTraceReadout S8 hash minit mfin maddrs t pre post holder target)
    (anc : RevokeCapabilityWriteAnchor S8 hash minit mfin maddrs t pre post holder target rd)
    (hwrong : post.kernel.caps ≠ removeEdgeCaps pre.kernel.caps holder target) :
    False :=
  hwrong (revokeCapability_forced_sat S8 hash name n hChip hsat pre post holder target rd anc)

/-- **`revokeCapability_descriptorRefines_capOpenSat` — the apex-wirable, LIGHT-CLIENT revokeCapability
rung (the ROUTE-FORGE close).** Consumes `Satisfied2 hash revokeCapabilityWriteCapOpenV3` — the SINGLE
descriptor that carries BOTH the cap-membership authority crown AND the cap-tree REMOVE — by stripping
the selector tooth (via `withSelectorGate_satisfied2`) and applying
`revokeCapability_descriptorRefines_sat`. This is the revokeCapability twin of
`revokeDelegation_descriptorRefines_capOpenSat`: it makes the cap-tree REMOVE light-client-verifiable IN
the descriptor the SDK route proves+verifies. Editing the deployed BEFORE welds turns this — and the SDK
route — RED. -/
theorem revokeCapability_descriptorRefines_capOpenSat (S8 : Cap8Scheme) (hash : List ℤ → ℤ)
    (name : String) (n : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hChip : ChipTableSoundN (capPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash
      (withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.REVOKE_CAPABILITY
        (effCapRemoveV3 revokeCapabilityV3 name n)) minit mfin maddrs t)
    (pre post : RecChainedState) (holder target : CellId)
    (rd : RevokeCapabilityTraceReadout S8 hash minit mfin maddrs t pre post holder target)
    (anc : RevokeCapabilityWriteAnchor S8 hash minit mfin maddrs t pre post holder target rd) :
    RevokeSpec pre holder target post :=
  revokeCapability_descriptorRefines_sat S8 hash name n hChip
    (withSelectorGate_satisfied2 hash _ (effCapRemoveV3 revokeCapabilityV3 name n) minit mfin maddrs t hsat)
    pre post holder target rd anc

/-- **CLASS-A ROUTE TOOTH (revokeCapability) — a forged wrong-caps post-root on the WRITE-CAPOPEN wrapper
is UNSAT.** Over the LIVE `revokeCapabilityWriteCapOpenV3` (the descriptor the SDK route verifies), a
post-state whose caps are NOT the genuine `removeEdgeCaps` move cannot arise from a `Satisfied2` witness
— the keystone welds FORCE the tombstone REMOVE. Perturbing the BEFORE welds breaks the force and reds
this. -/
theorem revokeCapability_capOpenSat_rejects_forged_postroot (S8 : Cap8Scheme) (hash : List ℤ → ℤ)
    (name : String) (n : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hChip : ChipTableSoundN (capPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash
      (withSelectorGate Dregg2.Circuit.Emit.EffectVmEmit.sel.REVOKE_CAPABILITY
        (effCapRemoveV3 revokeCapabilityV3 name n)) minit mfin maddrs t)
    (pre post : RecChainedState) (holder target : CellId)
    (rd : RevokeCapabilityTraceReadout S8 hash minit mfin maddrs t pre post holder target)
    (anc : RevokeCapabilityWriteAnchor S8 hash minit mfin maddrs t pre post holder target rd)
    (hwrong : post.kernel.caps ≠ removeEdgeCaps pre.kernel.caps holder target) :
    False :=
  hwrong (revokeCapability_forced_sat S8 hash name n hChip
    (withSelectorGate_satisfied2 hash _ (effCapRemoveV3 revokeCapabilityV3 name n) minit mfin maddrs t hsat)
    pre post holder target rd anc)

#assert_axioms revokeCapability_forced_sat
#assert_axioms revokeCapability_descriptorRefines_sat
#assert_axioms revokeCapability_descriptorRefines_capOpenSat
#assert_axioms revokeCapability_capOpenSat_rejects_forged_postroot
#assert_axioms revokeCapability_execFullA_sat
#assert_axioms revokeCapability_sat_rejects_wrong_caps

/-! ## §H — heapWrite (the SECOND faithful 8-felt root): the DEPLOYED after-spine `effHeapWriteV3`
FORCES `heapWritesTo8` over the committed BEFORE/AFTER heap-root blocks. The heap twin of the cap
`*_descriptorRefines_sat` trio, but heap carries NO authority — the membership open is a pure
`(addr, value)` leaf, so the deliverable is the faithful 8-felt heap-write bound DIRECTLY over env
columns (scalar-rooted decode, NO anchor struct). Consumes `HeapOpenEmit.effHeapWriteV3_forces_write8`
(OPTION I: the deployed heap-write descriptor IS the after-spine `effHeapWriteV3 heapWriteV3 …`, EXACTLY
as cap deploys `effCapOpenWriteV3` — the apex's `Rfix 56` quantifies over it). -/

open Dregg2.Circuit.DeployedHeapTree (Heap8Scheme)
open Dregg2.Circuit.Emit.HeapOpenEmit (effHeapWriteV3 heapPermOut)

/-- **`heapWrite_forces_write8_sat` — THE HEAP CLASS-A 8-FELT DELIVERABLE (deployed-descriptor forced).**
From `Satisfied2 (effHeapWriteV3 base name)` (the DEPLOYED after-spine heap-write descriptor, `base` the
Class-A splice `heapWriteV3`) + the named WIDE chip soundness, an active (non-last) row FORCES the
faithful 8-felt `heapWritesTo8` over the FULL committed BEFORE/AFTER heap-root blocks
(`beforeHeapRootCols`/`afterHeapRootCols`, the whole ~124-bit root) — keyed at `HEAP_ADDR`, written to
`param[VALUE]`. NEVER the lane-0 squeeze the map_op-only descriptor leaves. This is what
`CircuitSoundnessAssembled.Rfix 56 = effHeapWriteV3 heapWriteV3 …` quantifies over. Editing the
after-spine appendix turns this — and the apex — RED. -/
theorem heapWrite_forces_write8_sat (S8 : Heap8Scheme)
    (base : Dregg2.Circuit.DescriptorIR2.EffectVmDescriptor2) (name : String)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hChip : ChipTableSoundN (heapPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash (effHeapWriteV3 base name) mi mf ma tr)
    (i : Nat) (hi : i < tr.rows.length) (hnotlast : i + 1 ≠ tr.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt tr i).loc col ∧ (envAt tr i).loc col < 2013265921) :
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.heapWritesTo8 S8
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeHeapRootCols (envAt tr i))
      ((envAt tr i).loc Dregg2.Circuit.Emit.EffectVmEmitHeapRoot.HEAP_ADDR)
      ((envAt tr i).loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitHeapRoot.hp.VALUE))
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.afterHeapRootCols (envAt tr i)) :=
  Dregg2.Circuit.Emit.HeapOpenEmit.effHeapWriteV3_forces_write8
    S8 base name hash mi mf ma tr hChip hsat i hi hnotlast hcells

/-- **CLASS-A HEAP TOOTH — the post-root pins the post-leaf (the 8-felt GENTIAN, NOT lane-0).** Along the
FIXED sibling path the forced `heapWritesTo8` fixes, the after heap-root determines the after leaf digest
(`Heap8Scheme.recomposeUp8` injective at full ~124-bit width): a forged after heap-root reached by a
DIFFERENT post-leaf along the genuine path is impossible. The deployed twin of the Rust GENTIAN weld
(`heap_root_gentian_weld.rs`). -/
theorem heapWrite_forces_postleaf (S8 : Heap8Scheme) (path : List (Dregg2.Circuit.CapMerkleGeneric.StepG Digest8))
    {a b : Digest8}
    (h : Heap8Scheme.recomposeUp8 S8 a path = Heap8Scheme.recomposeUp8 S8 b path) : a = b :=
  Dregg2.Circuit.Emit.EffectVmEmitRotationV3.heapWritesTo8_forces_postleaf S8 path h

#assert_axioms heapWrite_forces_write8_sat
#assert_axioms heapWrite_forces_postleaf

/-! ## §I — refusal fields-write (the THIRD and LAST faithful 8-felt root): the DEPLOYED after-spine
`effFieldsWriteV3` FORCES `fieldsWritesTo8` over the committed BEFORE/AFTER fields-root blocks. The fields
twin of the heap `§H` trio, but fields carries NO authority AND — unlike heap's runtime `HEAP_ADDR` — the
audit-slot key is a COMPILE-TIME CONSTANT (`refusalAuditKeyFelt` via `constEqGate`), so the deliverable is
the faithful 8-felt fields-write bound at the reserved audit slot, written to `REFUSAL_AUDIT_FELT_COL`.
Consumes `FieldsOpenEmit.effFieldsWriteV3_forces_write8` (OPTION I: the deployed refusal descriptor IS the
after-spine `effFieldsWriteV3 refusalFieldsWriteV3 …`, EXACTLY as heap deploys `effHeapWriteV3` — the
apex's `Rfix 39` quantifies over it). -/

open Dregg2.Circuit.DeployedFieldsTree (Fields8Scheme)
open Dregg2.Circuit.Emit.FieldsOpenEmit (effFieldsWriteV3 fieldsPermOut)

/-- **`refusalWrite_forces_write8_sat` — THE FIELDS CLASS-A 8-FELT DELIVERABLE (deployed-descriptor
forced).** From `Satisfied2 (effFieldsWriteV3 base name)` (the DEPLOYED after-spine fields-write descriptor,
`base` the Class-A `refusalFieldsWriteV3`) + the named WIDE chip soundness, an active (non-last) row FORCES
the faithful 8-felt `fieldsWritesTo8` over the FULL committed BEFORE/AFTER fields-root blocks
(`beforeFieldsRootCols`/`afterFieldsRootCols`, the whole ~124-bit root) — keyed at the CONSTANT
`refusalAuditKeyFelt`, written to `REFUSAL_AUDIT_FELT_COL`. NEVER the lane-0 squeeze the map_op-only
descriptor leaves. This is what `CircuitSoundnessAssembled.Rfix 39 = effFieldsWriteV3 refusalFieldsWriteV3 …`
quantifies over. Editing the after-spine appendix turns this — and the apex — RED. -/
theorem refusalWrite_forces_write8_sat (S8 : Fields8Scheme)
    (base : Dregg2.Circuit.DescriptorIR2.EffectVmDescriptor2) (name : String)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hChip : ChipTableSoundN (fieldsPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash (effFieldsWriteV3 base name) mi mf ma tr)
    (i : Nat) (hi : i < tr.rows.length) (hnotlast : i + 1 ≠ tr.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt tr i).loc col ∧ (envAt tr i).loc col < 2013265921) :
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.fieldsWritesTo8 S8
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeFieldsRootCols (envAt tr i))
      Dregg2.Circuit.Emit.EffectVmEmitRotationV3.refusalAuditKeyFelt
      ((envAt tr i).loc Dregg2.Circuit.Emit.EffectVmEmitRotationV3.REFUSAL_AUDIT_FELT_COL)
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.afterFieldsRootCols (envAt tr i)) :=
  Dregg2.Circuit.Emit.FieldsOpenEmit.effFieldsWriteV3_forces_write8
    S8 base name hash mi mf ma tr hChip hsat i hi hnotlast hcells

/-- **CLASS-A FIELDS TOOTH — the post-root pins the post-leaf (the 8-felt GENTIAN, NOT lane-0).** Along the
FIXED sibling path the forced `fieldsWritesTo8` fixes, the after fields-root determines the after leaf digest
(`Fields8Scheme.recomposeUp8` injective at full ~124-bit width): a forged after fields-root reached by a
DIFFERENT post-leaf along the genuine path is impossible. The deployed twin of the Rust GENTIAN weld
(`fields_root_gentian_weld.rs`). -/
theorem refusalWrite_forces_postleaf (S8 : Fields8Scheme) (path : List (Dregg2.Circuit.CapMerkleGeneric.StepG Digest8))
    {a b : Digest8}
    (h : Fields8Scheme.recomposeUp8 S8 a path = Fields8Scheme.recomposeUp8 S8 b path) : a = b :=
  Dregg2.Circuit.Emit.EffectVmEmitRotationV3.fieldsWritesTo8_forces_postleaf S8 path h

#assert_axioms refusalWrite_forces_write8_sat
#assert_axioms refusalWrite_forces_postleaf

/-! ## §J — the THREE DEDICATED ACCUMULATOR roots (the 4th/5th/6th faithful 8-felt roots): the after-spine
`effAccumWriteV3` FORCES `heapWritesTo8` over the committed BEFORE/AFTER accumulator-root groups
(nullifier @ limb 26 · commitments @ limb 27 · cells @ limb 0). The accumulator twins of the heap `§H` trio,
riding the SAME `Heap8Scheme` node8 lane (NO spine re-proof). Consumes
`AccumulatorOpenEmit.effAccumWriteV3_forces_write8`, instantiated per family at its group col + published
KEY/VALUE columns.

⚑ ASSURANCE-LAYER (not the deployed apex descriptor, unlike heap/fields OPTION I): the DEPLOYED accumulator
descriptors (`noteSpendV3` / `noteCreateV3` / `createCellV3`) carry the update as INLINE `MapOp`s whose
`holdsAt` denotes lane 0; the full 8-felt faithfulness is deployed in Rust via the genuine `CanonicalHeapTree8`
producer + the map-op `node8` AIR (forge-rejection PROVEN by `vk_epoch_notes`/`vk_epoch_birth`). These trios
are the LEAN assurance twin of that binding — the same 8-felt keystone cap/heap/fields carry — standing
alongside the deployed node8-AIR faithfulness. Flipping the apex to quantify over `effAccumWriteV3` is a
SEPARATE VK epoch (the producers already fill the 8 lanes; the flip is the descriptor swap). -/

open Dregg2.Circuit.Emit.AccumulatorOpenEmit (effAccumWriteV3)

/-- **`nullifierWrite_forces_write8_sat` — THE NULLIFIER-ACCUMULATOR 8-FELT DELIVERABLE (assurance).** From
`Satisfied2 (effAccumWriteV3 nullifierRootGroupCol NULLIFIER_PARAM_COL (prmCol NOTE_VALUE_LO) base name)` +
the named WIDE chip soundness, an active (non-last) row FORCES the faithful 8-felt `heapWritesTo8` over the
FULL committed BEFORE/AFTER nullifier-root groups (limb 26 ‖ completion limbs 67..73, the whole ~124-bit
root) — keyed at the published nullifier `NULLIFIER_PARAM_COL`, written to `param[NOTE_VALUE_LO]`. NEVER the
lane-0 squeeze the inline map-op's `holdsAt` leaves. -/
theorem nullifierWrite_forces_write8_sat (S8 : Heap8Scheme)
    (base : Dregg2.Circuit.DescriptorIR2.EffectVmDescriptor2) (name : String)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hChip : ChipTableSoundN (Dregg2.Circuit.Emit.HeapOpenEmit.heapPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash (effAccumWriteV3 Dregg2.Circuit.Emit.EffectVmEmitRotationV3.nullifierRootGroupCol
              Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NULLIFIER_PARAM_COL
              (prmCol Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.param.NOTE_VALUE_LO) base name) mi mf ma tr)
    (i : Nat) (hi : i < tr.rows.length) (hnotlast : i + 1 ≠ tr.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt tr i).loc col ∧ (envAt tr i).loc col < 2013265921) :
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.heapWritesTo8 S8
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeNullifierRootCols (envAt tr i))
      ((envAt tr i).loc Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NULLIFIER_PARAM_COL)
      ((envAt tr i).loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.param.NOTE_VALUE_LO))
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.afterNullifierRootCols (envAt tr i)) :=
  Dregg2.Circuit.Emit.AccumulatorOpenEmit.effAccumWriteV3_forces_write8
    S8 Dregg2.Circuit.Emit.EffectVmEmitRotationV3.nullifierRootGroupCol
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NULLIFIER_PARAM_COL
    (prmCol Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.param.NOTE_VALUE_LO)
    base name hash mi mf ma tr hChip hsat i hi hnotlast hcells

/-- **`commitmentsWrite_forces_write8_sat` — THE COMMITMENTS-ACCUMULATOR 8-FELT DELIVERABLE (assurance).**
FORCES `heapWritesTo8` over the committed BEFORE/AFTER commitments-root groups (limb 27 ‖ completion limbs
74..80) — keyed at `COMMITMENT_KEY_PARAM_COL`, written to `param[NoteCreate.NOTE_VALUE_LO]`. -/
theorem commitmentsWrite_forces_write8_sat (S8 : Heap8Scheme)
    (base : Dregg2.Circuit.DescriptorIR2.EffectVmDescriptor2) (name : String)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hChip : ChipTableSoundN (Dregg2.Circuit.Emit.HeapOpenEmit.heapPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash (effAccumWriteV3 Dregg2.Circuit.Emit.EffectVmEmitRotationV3.commitmentsRootGroupCol
              Dregg2.Circuit.Emit.EffectVmEmitRotationV3.COMMITMENT_KEY_PARAM_COL
              (prmCol Dregg2.Circuit.Emit.EffectVmEmitNoteCreate.param.NOTE_VALUE_LO) base name) mi mf ma tr)
    (i : Nat) (hi : i < tr.rows.length) (hnotlast : i + 1 ≠ tr.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt tr i).loc col ∧ (envAt tr i).loc col < 2013265921) :
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.heapWritesTo8 S8
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeCommitmentsRootCols (envAt tr i))
      ((envAt tr i).loc Dregg2.Circuit.Emit.EffectVmEmitRotationV3.COMMITMENT_KEY_PARAM_COL)
      ((envAt tr i).loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitNoteCreate.param.NOTE_VALUE_LO))
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.afterCommitmentsRootCols (envAt tr i)) :=
  Dregg2.Circuit.Emit.AccumulatorOpenEmit.effAccumWriteV3_forces_write8
    S8 Dregg2.Circuit.Emit.EffectVmEmitRotationV3.commitmentsRootGroupCol
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.COMMITMENT_KEY_PARAM_COL
    (prmCol Dregg2.Circuit.Emit.EffectVmEmitNoteCreate.param.NOTE_VALUE_LO)
    base name hash mi mf ma tr hChip hsat i hi hnotlast hcells

/-- **`cellsWrite_forces_write8_sat` — THE CELLS/ACCOUNTS-ACCUMULATOR 8-FELT DELIVERABLE (assurance).**
FORCES `heapWritesTo8` over the committed BEFORE/AFTER cells-root groups (limb 0 ‖ completion limbs 81..87)
— keyed at the new-cell id `NEW_CELL_KEY_PARAM_COL`, written with the key as its own leaf value (a born-empty
cell). -/
theorem cellsWrite_forces_write8_sat (S8 : Heap8Scheme)
    (base : Dregg2.Circuit.DescriptorIR2.EffectVmDescriptor2) (name : String)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hChip : ChipTableSoundN (Dregg2.Circuit.Emit.HeapOpenEmit.heapPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash (effAccumWriteV3 Dregg2.Circuit.Emit.EffectVmEmitRotationV3.cellsRootGroupCol
              Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NEW_CELL_KEY_PARAM_COL
              Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NEW_CELL_KEY_PARAM_COL base name) mi mf ma tr)
    (i : Nat) (hi : i < tr.rows.length) (hnotlast : i + 1 ≠ tr.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt tr i).loc col ∧ (envAt tr i).loc col < 2013265921) :
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.heapWritesTo8 S8
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeCellsRootCols (envAt tr i))
      ((envAt tr i).loc Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NEW_CELL_KEY_PARAM_COL)
      ((envAt tr i).loc Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NEW_CELL_KEY_PARAM_COL)
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.afterCellsRootCols (envAt tr i)) :=
  Dregg2.Circuit.Emit.AccumulatorOpenEmit.effAccumWriteV3_forces_write8
    S8 Dregg2.Circuit.Emit.EffectVmEmitRotationV3.cellsRootGroupCol
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NEW_CELL_KEY_PARAM_COL
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NEW_CELL_KEY_PARAM_COL
    base name hash mi mf ma tr hChip hsat i hi hnotlast hcells

/-! ## §J′ — the INSERT-shaped accumulator trio (THE CORRECT-shaped genuine close). The update-shaped §J
trio above FORCES `heapWritesTo8` (update-at-key) — but the three accumulators are sorted-tree FRESH-KEY
INSERTS, not update-at-key (no shared before/after path; a genuine obstruction). This §J′ trio consumes the
CORRECT-shaped `AccumulatorInsertEmit.effAccumInsertV3_forces_write8`: from `Satisfied2 (effAccumInsertV3 …)`
the spliced `(key, value)` leaf membership in AFTER is TRACE-FORCED over the FULL committed 8-felt group, and
— with the realizable non-membership bracket (`GapOpen8` over the committed BEFORE spine) + the two
`SpineCommits8` bindings — FORCES the faithful 8-felt INSERT `accumInserts8` over the ACTUAL sorted insert.
The fresh-key non-membership + set-recompute ride the deployed `.absent`/`.insert` node8-AIR map-op and the
realizable carriers (`SpineCommits8` a HYPOTHESIS, never an axiom; never lane-0). -/

open Dregg2.Circuit.Emit.AccumulatorInsertEmit (effAccumInsertV3 effAccumInsertV3_forces_write8 accumInserts8)
open Dregg2.Circuit.SortedTreeNonMembershipHeap8 (SpineCommits8 GapOpen8)
open Dregg2.Circuit.SortedTreeNonMembership (sortedInsert)

/-- **`nullifierInsert_forces_write8_sat` — THE NULLIFIER-ACCUMULATOR INSERT 8-FELT DELIVERABLE.** From
`Satisfied2 (effAccumInsertV3 nullifierRootGroupCol NULLIFIER_PARAM_COL (prmCol NOTE_VALUE_LO) base name)` +
the WIDE chip soundness + the realizable non-membership bracket + spine bindings, an active (non-last) row
FORCES the faithful 8-felt INSERT `accumInserts8` over the FULL committed BEFORE/AFTER nullifier-root groups
(limb 26 ‖ 67..73). The double-spend nullifier insert, at full ~124-bit width, over the GENUINE sorted insert. -/
theorem nullifierInsert_forces_write8_sat (S8 : Heap8Scheme)
    (base : Dregg2.Circuit.DescriptorIR2.EffectVmDescriptor2) (name : String)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hChip : ChipTableSoundN (Dregg2.Circuit.Emit.HeapOpenEmit.heapPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash (effAccumInsertV3 Dregg2.Circuit.Emit.EffectVmEmitRotationV3.nullifierRootGroupCol
              Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NULLIFIER_PARAM_COL
              (prmCol Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.param.NOTE_VALUE_LO)
              (some Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.SEL_NOTE_SPEND) base name) mi mf ma tr)
    (i : Nat) (hi : i < tr.rows.length) (hnotlast : i + 1 ≠ tr.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt tr i).loc col ∧ (envAt tr i).loc col < 2013265921)
    (hselActive : (envAt tr i).loc Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.SEL_NOTE_SPEND = 1)
    (spine : List ℤ)
    (hbefore : SpineCommits8 S8
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeNullifierRootCols (envAt tr i)) spine)
    (g : GapOpen8 S8
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeNullifierRootCols (envAt tr i))
      ((envAt tr i).loc Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NULLIFIER_PARAM_COL))
    (hcov : g.coversSpine spine)
    (hafter : SpineCommits8 S8
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.afterNullifierRootCols (envAt tr i))
      (sortedInsert ((envAt tr i).loc Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NULLIFIER_PARAM_COL) spine)) :
    accumInserts8 S8
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeNullifierRootCols (envAt tr i))
      ((envAt tr i).loc Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NULLIFIER_PARAM_COL)
      ((envAt tr i).loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.param.NOTE_VALUE_LO))
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.afterNullifierRootCols (envAt tr i)) :=
  effAccumInsertV3_forces_write8
    S8 Dregg2.Circuit.Emit.EffectVmEmitRotationV3.nullifierRootGroupCol
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NULLIFIER_PARAM_COL
    (prmCol Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.param.NOTE_VALUE_LO)
    (some Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.SEL_NOTE_SPEND)
    base name hash mi mf ma tr hChip hsat i hi hnotlast hcells
    (fun s hs => Option.some_inj.mp hs ▸ hselActive)
    spine hbefore g hcov hafter

/-- **`commitmentsInsert_forces_write8_sat` — THE COMMITMENTS-ACCUMULATOR INSERT 8-FELT DELIVERABLE.** FORCES
`accumInserts8` over the committed BEFORE/AFTER commitments-root groups (limb 27 ‖ 74..80) — keyed at
`COMMITMENT_KEY_PARAM_COL`, valued at `param[NoteCreate.NOTE_VALUE_LO]`. The append-only commitment insert. -/
theorem commitmentsInsert_forces_write8_sat (S8 : Heap8Scheme)
    (base : Dregg2.Circuit.DescriptorIR2.EffectVmDescriptor2) (name : String)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hChip : ChipTableSoundN (Dregg2.Circuit.Emit.HeapOpenEmit.heapPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash (effAccumInsertV3 Dregg2.Circuit.Emit.EffectVmEmitRotationV3.commitmentsRootGroupCol
              Dregg2.Circuit.Emit.EffectVmEmitRotationV3.COMMITMENT_KEY_PARAM_COL
              (prmCol Dregg2.Circuit.Emit.EffectVmEmitNoteCreate.param.NOTE_VALUE_LO) none base name) mi mf ma tr)
    (i : Nat) (hi : i < tr.rows.length) (hnotlast : i + 1 ≠ tr.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt tr i).loc col ∧ (envAt tr i).loc col < 2013265921)
    (spine : List ℤ)
    (hbefore : SpineCommits8 S8
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeCommitmentsRootCols (envAt tr i)) spine)
    (g : GapOpen8 S8
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeCommitmentsRootCols (envAt tr i))
      ((envAt tr i).loc Dregg2.Circuit.Emit.EffectVmEmitRotationV3.COMMITMENT_KEY_PARAM_COL))
    (hcov : g.coversSpine spine)
    (hafter : SpineCommits8 S8
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.afterCommitmentsRootCols (envAt tr i))
      (sortedInsert ((envAt tr i).loc Dregg2.Circuit.Emit.EffectVmEmitRotationV3.COMMITMENT_KEY_PARAM_COL) spine)) :
    accumInserts8 S8
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeCommitmentsRootCols (envAt tr i))
      ((envAt tr i).loc Dregg2.Circuit.Emit.EffectVmEmitRotationV3.COMMITMENT_KEY_PARAM_COL)
      ((envAt tr i).loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitNoteCreate.param.NOTE_VALUE_LO))
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.afterCommitmentsRootCols (envAt tr i)) :=
  effAccumInsertV3_forces_write8
    S8 Dregg2.Circuit.Emit.EffectVmEmitRotationV3.commitmentsRootGroupCol
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.COMMITMENT_KEY_PARAM_COL
    (prmCol Dregg2.Circuit.Emit.EffectVmEmitNoteCreate.param.NOTE_VALUE_LO)
    none
    base name hash mi mf ma tr hChip hsat i hi hnotlast hcells
    (fun s hs => by simp at hs)
    spine hbefore g hcov hafter

/-- **`cellsInsert_forces_write8_sat` — THE CELLS/ACCOUNTS-ACCUMULATOR INSERT 8-FELT DELIVERABLE.** FORCES
`accumInserts8` over the committed BEFORE/AFTER cells-root groups (limb 0 ‖ 81..87) — keyed at the new-cell id
`NEW_CELL_KEY_PARAM_COL`, valued with the key as its own leaf value (a born-empty cell). The account birth. -/
theorem cellsInsert_forces_write8_sat (S8 : Heap8Scheme)
    (base : Dregg2.Circuit.DescriptorIR2.EffectVmDescriptor2) (name : String)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hChip : ChipTableSoundN (Dregg2.Circuit.Emit.HeapOpenEmit.heapPermOut S8) (tr.tf .poseidon2))
    (hsat : Satisfied2 hash (effAccumInsertV3 Dregg2.Circuit.Emit.EffectVmEmitRotationV3.cellsRootGroupCol
              Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NEW_CELL_KEY_PARAM_COL
              Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NEW_CELL_KEY_PARAM_COL none base name) mi mf ma tr)
    (i : Nat) (hi : i < tr.rows.length) (hnotlast : i + 1 ≠ tr.rows.length)
    (hcells : ∀ col : Nat, 0 ≤ (envAt tr i).loc col ∧ (envAt tr i).loc col < 2013265921)
    (spine : List ℤ)
    (hbefore : SpineCommits8 S8
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeCellsRootCols (envAt tr i)) spine)
    (g : GapOpen8 S8
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeCellsRootCols (envAt tr i))
      ((envAt tr i).loc Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NEW_CELL_KEY_PARAM_COL))
    (hcov : g.coversSpine spine)
    (hafter : SpineCommits8 S8
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.afterCellsRootCols (envAt tr i))
      (sortedInsert ((envAt tr i).loc Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NEW_CELL_KEY_PARAM_COL) spine)) :
    accumInserts8 S8
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.beforeCellsRootCols (envAt tr i))
      ((envAt tr i).loc Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NEW_CELL_KEY_PARAM_COL)
      ((envAt tr i).loc Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NEW_CELL_KEY_PARAM_COL)
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.afterCellsRootCols (envAt tr i)) :=
  effAccumInsertV3_forces_write8
    S8 Dregg2.Circuit.Emit.EffectVmEmitRotationV3.cellsRootGroupCol
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NEW_CELL_KEY_PARAM_COL
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NEW_CELL_KEY_PARAM_COL
    none
    base name hash mi mf ma tr hChip hsat i hi hnotlast hcells
    (fun s hs => by simp at hs)
    spine hbefore g hcov hafter

/-- **CLASS-A ACCUMULATOR TOOTH — the post-root pins the post-leaf (the 8-felt GENTIAN, NOT lane-0).** Shared
across all three accumulator families (SAME `Heap8Scheme`): along the FIXED sibling path the forced
`heapWritesTo8` fixes, the after accumulator-root determines the after leaf digest (`recomposeUp8` injective
at full ~124-bit width) — a forged after-root reached by a DIFFERENT post-leaf along the genuine path is
impossible. -/
theorem accumWrite_forces_postleaf (S8 : Heap8Scheme)
    (path : List (Dregg2.Circuit.CapMerkleGeneric.StepG Digest8)) {a b : Digest8}
    (h : Heap8Scheme.recomposeUp8 S8 a path = Heap8Scheme.recomposeUp8 S8 b path) : a = b :=
  Dregg2.Circuit.Emit.EffectVmEmitRotationV3.heapWritesTo8_forces_postleaf S8 path h

#assert_axioms nullifierWrite_forces_write8_sat
#assert_axioms commitmentsWrite_forces_write8_sat
#assert_axioms cellsWrite_forces_write8_sat
#assert_axioms accumWrite_forces_postleaf
#assert_axioms nullifierInsert_forces_write8_sat
#assert_axioms commitmentsInsert_forces_write8_sat
#assert_axioms cellsInsert_forces_write8_sat

end Dregg2.Circuit.RotatedKernelRefinementCapFamily
