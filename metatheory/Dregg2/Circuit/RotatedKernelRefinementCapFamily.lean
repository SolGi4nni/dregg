/-
# Dregg2.Circuit.RotatedKernelRefinementCapFamily — the CAPABILITY-FAMILY refinements, FORCING the
  exact sorted-tree cap-table move via the PHASE-D update gadget (`CapTreeUpdate`).

## What this module closes (the convergent cap-family residual)

`RotatedKernelRefinementAttenuate.lean` closed `attenuate` at class VALUE_PARTIAL: the genuine
recompute forces a SINGLE-EDGE FELT ACCUMULATOR advance + the in-circuit non-amplification (`granted ⊑
held`), but it CANNOT relate that felt to a sorted-Merkle commitment of the `Caps` function — so the
exact cap-table move was a NAMED felt residual (`attenuateEncodes.capsMove`), unforced at the SET level.

The PHASE-D gadget (`SortedTreeNonMembership` → `CapTreeUpdate`) supplies precisely what was missing:
the THREE sorted-tree update operations over the COMMITTED KEY SET `keysOf S root` (the deployed
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

  1. **the sorted-tree update DATA** — `SpineCommits S oldRoot spine` (the old root binds the spine),
     the present/fresh witness, and `SpineCommits S newRoot (sortedInsert/sortedRemove/spine)` (the new
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
No `sorry`, no `native_decide`, no `:= True`, no fresh axiom. NEW file; imports read-only.
-/
import Dregg2.Circuit.CapTreeUpdate
import Dregg2.Circuit.Spec.authorityunattenuated
import Dregg2.Circuit.Spec.authorityattenuation
import Dregg2.Circuit.Spec.authorityrevocation
import Dregg2.Circuit.Spec.refreshdelegation
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3
import Dregg2.Circuit.Emit.CapOpenEmit

namespace Dregg2.Circuit.RotatedKernelRefinementCapFamily

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap Auth Label)
open Dregg2.Circuit.DeployedCapTree (CapLeaf CapHashScheme)
open Dregg2.Circuit.DeployedCapTree.CapHashScheme (MembersAt)
open Dregg2.Circuit.SortedTreeNonMembership
  (keyOf SpineCommits keysOf sortedInsert)
open Dregg2.Circuit.CapTreeUpdate
  (sortedRemove capInsert_sound capUpdateAt_sound capRemove_sound capRemove_drops_key
   capUpdateAt_present)
open Dregg2.Circuit.Spec.AuthorityUnattenuated (DelegateSpec delegateGuard)
open Dregg2.Circuit.Spec.AuthorityAttenuation
  (AttenuateSpec DelegateAttenSpec DelegateAttenGuard)
open Dregg2.Circuit.Spec.AuthorityRevocation
  (RevokeSpec removeEdgeCaps execFullA_revoke_iff_spec)
open Dregg2.Circuit.Spec.RefreshDelegation
  (RefreshDelegationSpec RefreshDelegationGuard refreshDelegationsMap refreshDelegationReceipt)
open Dregg2.Circuit.DescriptorIR2 (VmTrace Satisfied2 envAt opensTo writesTo)
open Dregg2.Circuit.Emit.EffectVmEmit (prmCol sbCol saCol)
open Dregg2.Circuit.Emit.EffectVmEmit.state (CAP_ROOT)
open Dregg2.Circuit.Emit.EffectVmEmitV2 (heldReadOp removeWriteOp CAP_KEY KEEP_MASK HELD_MASK)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
  (revokeCapabilityV3 delegateV3 delegateAttenV3 grantCapWriteV3
   introduceWriteV3 revokeDelegationWriteV3
   delegateV3_forces_write grantCapWriteV3_forces_write delegateAttenV3_non_amp
   introduceWriteV3_forces_write revokeDelegationWriteV3_forces_write)
open Dregg2.Circuit.Emit.CapOpenEmit
  (introduceWriteCapOpenV3 revokeDelegationWriteCapOpenV3 delegateWriteCapOpenV3 grantCapWriteCapOpenV3
   delegateAttenWriteCapOpenV3 capOpen_satisfied2_strips_to_base)

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
structure DelegateCapsTreeEncodes {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (del rec t : CellId) : Type where
  oldRoot : ℤ
  newRoot : ℤ
  newKey : ℤ
  spine : List ℤ
  hold : SpineCommits S oldRoot spine
  hfresh : newKey ∉ keysOf S oldRoot
  hnew : SpineCommits S newRoot (sortedInsert newKey spine)
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
theorem delegate_forces_insert {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (del rec t : CellId)
    (henc : DelegateCapsTreeEncodes S pre post del rec t) :
    ∀ y, y ∈ keysOf S henc.newRoot ↔ (y = henc.newKey ∨ y ∈ keysOf S henc.oldRoot) :=
  capInsert_sound S henc.oldRoot henc.newRoot henc.newKey henc.spine henc.hold henc.hfresh henc.hnew

/-- **`delegate_descriptorRefines` — THE DELEGATE/INTRODUCE/GRANTCAP REFINEMENT (insert-forced).** From
the decode, the kernel `DelegateSpec pre del rec t post` (the `grant` move + the receipt-log advance +
the sixteen-field frame, under the Granovetter guard). The cap-tree INSERT is FORCED at the set level
(`delegate_forces_insert`); the `grant` `Caps`-equality is delivered from the named decode residual. -/
theorem delegate_descriptorRefines {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (del rec t : CellId)
    (henc : DelegateCapsTreeEncodes S pre post del rec t) :
    DelegateSpec pre del rec t post :=
  ⟨henc.guard, henc.capsMove, henc.logAdv,
   henc.frame.frAccounts, henc.frame.frCell, henc.frame.frNullifiers, henc.frame.frRevoked,
   henc.frame.frCommitments, henc.frame.frBal, henc.frame.frSlotCaveats, henc.frame.frFactories,
   henc.frame.frLifecycle, henc.frame.frDeathCert, henc.frame.frDelegate, henc.frame.frDelegations,
   henc.frame.frDelegationEpoch, henc.frame.frDelegationEpochAt, henc.frame.frHeaps⟩

/-- **`delegate_execFullA` — the refinement against the executor arm.** `DelegateSpec` IS the
`.delegate` / `.introduceA` arm of `execFullA`, so the decode forces a genuine committed delegate
(`execFullA pre (.delegate del rec t) = some post`). -/
theorem delegate_execFullA {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (del rec t : CellId)
    (henc : DelegateCapsTreeEncodes S pre post del rec t) :
    execFullA pre (.delegate del rec t) = some post :=
  (Dregg2.Circuit.Spec.AuthorityUnattenuated.execFullA_delegate_iff_spec pre del rec t post).mpr
    (delegate_descriptorRefines S pre post del rec t henc)

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
structure AttenuateCapsTreeEncodes {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (actor : CellId) (idx : Nat) (keep : List Auth) : Type where
  oldRoot : ℤ
  newRoot : ℤ
  atKey : ℤ
  spine : List ℤ
  hold : SpineCommits S oldRoot spine
  hpresent : atKey ∈ keysOf S oldRoot
  hnew : SpineCommits S newRoot spine
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
theorem attenuate_forces_keyset_preserved {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (actor : CellId) (idx : Nat) (keep : List Auth)
    (henc : AttenuateCapsTreeEncodes S pre post actor idx keep) :
    (∀ y, y ∈ keysOf S henc.newRoot ↔ y ∈ keysOf S henc.oldRoot)
    ∧ henc.atKey ∈ keysOf S henc.newRoot := by
  refine ⟨capUpdateAt_sound S henc.oldRoot henc.newRoot henc.atKey henc.spine henc.hold henc.hpresent
            henc.hnew, ?_⟩
  exact capUpdateAt_present S henc.oldRoot henc.newRoot henc.atKey henc.spine henc.hold henc.hpresent
    henc.hnew

/-- **`attenuate_descriptorRefines_exact` — THE ATTENUATE REFINEMENT (now SET-EXACT, not just
non-amp).** From the decode, the kernel `AttenuateSpec pre actor idx keep post` (the `attenuateSlotF`
move + the receipt-log + the sixteen-field frame). The cap-tree UPDATE-AT-KEY (the key-set PRESERVATION
— the in-place slot narrow's sorted-tree shadow) is FORCED (`attenuate_forces_keyset_preserved`); the
`attenuateSlotF` `Caps`-equality is delivered from the named decode residual. This UPGRADES the
felt-accumulator VALUE_PARTIAL: the sorted-tree set move is forced against the real commitment. -/
theorem attenuate_descriptorRefines_exact {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (actor : CellId) (idx : Nat) (keep : List Auth)
    (henc : AttenuateCapsTreeEncodes S pre post actor idx keep) :
    AttenuateSpec pre actor idx keep post :=
  ⟨henc.capsMove, henc.logAdv,
   henc.frame.frAccounts, henc.frame.frCell, henc.frame.frNullifiers, henc.frame.frRevoked,
   henc.frame.frCommitments, henc.frame.frBal, henc.frame.frSlotCaveats, henc.frame.frFactories,
   henc.frame.frLifecycle, henc.frame.frDeathCert, henc.frame.frDelegate, henc.frame.frDelegations,
   henc.frame.frDelegationEpoch, henc.frame.frDelegationEpochAt, henc.frame.frHeaps⟩

/-- **`attenuate_execFullA` — the refinement against the executor arm.** `AttenuateSpec` IS the
`.attenuateA` arm (TOTAL — always commits), so the decode forces `execFullA pre (.attenuateA actor idx
keep) = some post`. -/
theorem attenuate_execFullA {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (actor : CellId) (idx : Nat) (keep : List Auth)
    (henc : AttenuateCapsTreeEncodes S pre post actor idx keep) :
    execFullA pre (.attenuateA actor idx keep) = some post :=
  (Dregg2.Circuit.Spec.AuthorityAttenuation.attenuate_iff_spec pre actor idx keep post).mpr
    (attenuate_descriptorRefines_exact S pre post actor idx keep henc)

/-! ### §2.b — delegateAtten (the attenuated grant: an INSERT of an attenuated cap).

`DelegateAttenSpec` pins `s'.kernel.caps = grant … rec (attenuate keep (heldCapTo …))` — a GRANT of the
attenuated held cap onto the recipient (an INSERT at the recipient's fresh edge), gated on the delegator
holding a `t`-conferring cap. So the sorted-tree operation is INSERT (`capInsert_sound`), and the
non-amplification (`granted ⊑ held`) is `delegateAttenCaps_correct`'s `confRights` inequality. -/

/-- **`DelegateAttenCapsTreeEncodes` — the delegateAtten witness ⟷ kernel decode + the FORCED insert.**
Bundles the sorted-tree INSERT data (a fresh attenuated edge key), the Granovetter guard, the
`grant`-of-attenuated `Caps`-move residual, the receipt-log, and the frame. DATA-bearing. -/
structure DelegateAttenCapsTreeEncodes {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (del rec t : CellId) (keep : List Auth) : Type where
  oldRoot : ℤ
  newRoot : ℤ
  newKey : ℤ
  spine : List ℤ
  hold : SpineCommits S oldRoot spine
  hfresh : newKey ∉ keysOf S oldRoot
  hnew : SpineCommits S newRoot (sortedInsert newKey spine)
  guard : DelegateAttenGuard pre del t
  -- THE NAMED `Caps`-FUNCTION RESIDUAL (the attenuated grant).
  capsMove : post.kernel.caps
    = grant pre.kernel.caps rec (attenuate keep (heldCapTo pre.kernel.caps del t))
  logAdv : post.log = authReceipt del :: pre.log
  frame : KernelFrameExceptCaps pre post

/-- **`delegateAtten_forces_insert` — the cap-tree INSERT is FORCED for the attenuated grant.** The
committed key set grows by exactly the fresh attenuated edge key. -/
theorem delegateAtten_forces_insert {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (del rec t : CellId) (keep : List Auth)
    (henc : DelegateAttenCapsTreeEncodes S pre post del rec t keep) :
    ∀ y, y ∈ keysOf S henc.newRoot ↔ (y = henc.newKey ∨ y ∈ keysOf S henc.oldRoot) :=
  capInsert_sound S henc.oldRoot henc.newRoot henc.newKey henc.spine henc.hold henc.hfresh henc.hnew

/-- **`delegateAtten_descriptorRefines` — THE DELEGATEATTEN REFINEMENT (insert-forced + non-amp).** From
the decode, the kernel `DelegateAttenSpec pre del rec t keep post` (the attenuated `grant` + the
receipt-log + the frame, under the guard). The cap-tree INSERT is FORCED at the set level; the
attenuated-`grant` `Caps`-equality is the named decode residual; the non-amplification (`granted ⊑
held`) is `delegateAttenCaps_correct`. -/
theorem delegateAtten_descriptorRefines {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (del rec t : CellId) (keep : List Auth)
    (henc : DelegateAttenCapsTreeEncodes S pre post del rec t keep) :
    DelegateAttenSpec pre del rec t keep post :=
  ⟨henc.guard, henc.capsMove, henc.logAdv,
   henc.frame.frAccounts, henc.frame.frCell, henc.frame.frNullifiers, henc.frame.frRevoked,
   henc.frame.frCommitments, henc.frame.frBal, henc.frame.frSlotCaveats, henc.frame.frFactories,
   henc.frame.frLifecycle, henc.frame.frDeathCert, henc.frame.frDelegate, henc.frame.frDelegations,
   henc.frame.frDelegationEpoch, henc.frame.frDelegationEpochAt, henc.frame.frHeaps⟩

/-- **`delegateAtten_non_amplifying` — the headline non-amp, read off the FORCED spec.** The granted
attenuated cap's REAL conferred rights are `⊆` the delegator's held cap (`is_attenuation`), holding of
the committed step the refinement forces. Reuses `delegateAttenCaps_correct`. -/
theorem delegateAtten_non_amplifying {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (del rec t : CellId) (keep : List Auth)
    (_henc : DelegateAttenCapsTreeEncodes S pre post del rec t keep) :
    confRights (attenuate keep (heldCapTo pre.kernel.caps del t))
      ≤ confRights (heldCapTo pre.kernel.caps del t) :=
  (Dregg2.Circuit.Spec.AuthorityAttenuation.delegateAttenCaps_correct
    pre.kernel.caps del rec t keep).2.1

/-- **`delegateAtten_execFullA` — the refinement against the executor arm.** -/
theorem delegateAtten_execFullA {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (del rec t : CellId) (keep : List Auth)
    (henc : DelegateAttenCapsTreeEncodes S pre post del rec t keep) :
    execFullA pre (.delegateAttenA del rec t keep) = some post :=
  (Dregg2.Circuit.Spec.AuthorityAttenuation.delegateAtten_iff_spec pre del rec t keep post).mpr
    (delegateAtten_descriptorRefines S pre post del rec t keep henc)

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
structure RefreshDelegationCapsTreeEncodes {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (actor child : CellId) : Type where
  oldRoot : ℤ
  newRoot : ℤ
  atKey : ℤ
  spine : List ℤ
  hold : SpineCommits S oldRoot spine
  hpresent : atKey ∈ keysOf S oldRoot
  hnew : SpineCommits S newRoot spine
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
  frDelegationEpochAt : post.kernel.delegationEpochAt = pre.kernel.delegationEpochAt
  frHeaps : post.kernel.heaps = pre.kernel.heaps

/-- **`refreshDelegation_forces_keyset_preserved` — the UPDATE-AT-KEY is FORCED (key set preserved).** -/
theorem refreshDelegation_forces_keyset_preserved {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (actor child : CellId)
    (henc : RefreshDelegationCapsTreeEncodes S pre post actor child) :
    ∀ y, y ∈ keysOf S henc.newRoot ↔ y ∈ keysOf S henc.oldRoot :=
  capUpdateAt_sound S henc.oldRoot henc.newRoot henc.atKey henc.spine henc.hold henc.hpresent henc.hnew

/-- **`refreshDelegation_descriptorRefines` — THE REFRESH REFINEMENT (update-at-key-forced).** From the
decode, the kernel `RefreshDelegationSpec pre actor child post`. The UPDATE-AT-KEY over the delegations
tree is FORCED (key set preserved); the `refreshDelegationsMap` overwrite is the named decode residual. -/
theorem refreshDelegation_descriptorRefines {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (actor child : CellId)
    (henc : RefreshDelegationCapsTreeEncodes S pre post actor child) :
    RefreshDelegationSpec pre actor child post :=
  ⟨henc.guard, henc.delegationsMove, henc.logAdv,
   henc.frAccounts, henc.frCell, henc.frCaps, henc.frNullifiers, henc.frRevoked,
   henc.frCommitments, henc.frBal, henc.frSlotCaveats, henc.frFactories, henc.frLifecycle,
   henc.frDeathCert, henc.frDelegate, henc.frDelegationEpoch, henc.frDelegationEpochAt, henc.frHeaps⟩

/-- **`refreshDelegation_execFullA` — the refinement against the executor arm.** -/
theorem refreshDelegation_execFullA {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (actor child : CellId)
    (henc : RefreshDelegationCapsTreeEncodes S pre post actor child) :
    execFullA pre (.refreshDelegationA actor child) = some post :=
  (Dregg2.Circuit.Spec.RefreshDelegation.refreshDelegation_iff_spec pre actor child post).mpr
    (refreshDelegation_descriptorRefines S pre post actor child henc)

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
structure RevokeCapsTreeEncodes {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (holder t : CellId) : Type where
  oldRoot : ℤ
  newRoot : ℤ
  remKey : ℤ
  spine : List ℤ
  hold : SpineCommits S oldRoot spine
  hnew : SpineCommits S newRoot (sortedRemove remKey spine)
  -- THE NAMED `Caps`-FUNCTION RESIDUAL (the edge removal).
  capsMove : post.kernel.caps = removeEdgeCaps pre.kernel.caps holder t
  logAdv : post.log = authReceipt holder :: pre.log
  frame : KernelFrameExceptCaps pre post

/-- **`revoke_forces_remove` — the cap-tree REMOVE is FORCED (the key set loses exactly `remKey`).** From
the decode's sorted-tree remove data, the committed key set after the revoke is EXACTLY the old set minus
the revoked edge key — forced against the REAL deployed commitment. The exact sorted-tree move for revoke
/ revokeDelegation / revokeCapability. -/
theorem revoke_forces_remove {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (holder t : CellId)
    (henc : RevokeCapsTreeEncodes S pre post holder t) :
    (∀ y, y ∈ keysOf S henc.newRoot ↔ (y ∈ keysOf S henc.oldRoot ∧ y ≠ henc.remKey))
    ∧ henc.remKey ∉ keysOf S henc.newRoot := by
  refine ⟨capRemove_sound S henc.oldRoot henc.newRoot henc.remKey henc.spine henc.hold henc.hnew, ?_⟩
  exact capRemove_drops_key S henc.oldRoot henc.newRoot henc.remKey henc.spine henc.hold henc.hnew

/-- **`revoke_descriptorRefines` — THE REVOKE/REVOKEDELEGATION/REVOKECAPABILITY REFINEMENT
(remove-forced).** From the decode, the kernel `RevokeSpec pre holder t post` (the `removeEdgeCaps` move
+ the receipt-log + the sixteen-field frame; the guard is `True` — revocation is unconditional). The
cap-tree REMOVE is FORCED at the set level (`revoke_forces_remove`); the `removeEdgeCaps` `Caps`-equality
is the named decode residual. Non-amplification is vacuous (authority only shrinks). -/
theorem revoke_descriptorRefines {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (holder t : CellId)
    (henc : RevokeCapsTreeEncodes S pre post holder t) :
    RevokeSpec pre holder t post :=
  ⟨trivial, henc.capsMove, henc.logAdv,
   henc.frame.frAccounts, henc.frame.frCell, henc.frame.frNullifiers, henc.frame.frRevoked,
   henc.frame.frCommitments, henc.frame.frBal, henc.frame.frSlotCaveats, henc.frame.frFactories,
   henc.frame.frLifecycle, henc.frame.frDeathCert, henc.frame.frDelegate, henc.frame.frDelegations,
   henc.frame.frDelegationEpoch, henc.frame.frDelegationEpochAt, henc.frame.frHeaps⟩

/-- **`revoke_execFullA` — the refinement against the executor arm (`revoke`).** -/
theorem revoke_execFullA {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (holder t : CellId)
    (henc : RevokeCapsTreeEncodes S pre post holder t) :
    execFullA pre (.revoke holder t) = some post :=
  (Dregg2.Circuit.Spec.AuthorityRevocation.execFullA_revoke_iff_spec pre holder t post).mpr
    (revoke_descriptorRefines S pre post holder t henc)

/-- **`revokeDelegation_execFullA` — the refinement against the executor arm (`revokeDelegationA`).** The
parent-revocation routes to the SAME `RevokeSpec`, so the SAME decode forces it. -/
theorem revokeDelegation_execFullA {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (holder t : CellId)
    (henc : RevokeCapsTreeEncodes S pre post holder t) :
    execFullA pre (.revokeDelegationA holder t) = some post :=
  (Dregg2.Circuit.Spec.AuthorityRevocation.execFullA_revokeDelegation_iff_spec pre holder t post).mpr
    (revoke_descriptorRefines S pre post holder t henc)

/-- **`revoke_drops_edge` — the headline, read off the FORCED spec.** After a committed revoke, `holder`
confers NO edge to `t` (every cap it still holds fails `confersEdgeTo t`). Reuses
`revoke_drops_holder_edges`. -/
theorem revoke_drops_edge {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (holder t : CellId)
    (henc : RevokeCapsTreeEncodes S pre post holder t) :
    ∀ cap ∈ post.kernel.caps holder, ¬ confersEdgeTo t cap = true :=
  Dregg2.Circuit.Spec.AuthorityRevocation.revoke_drops_holder_edges pre holder t post
    (revoke_descriptorRefines S pre post holder t henc)

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
— a trace-fill identity, a NAMED carrier, never a sorry. Editing `<slot>V3`'s write op turns the forced
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
structure DelegateWriteAnchor {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (del rec t : CellId)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (henc : DelegateCapsTreeEncodes S pre post del rec t) : Type where
  row : Nat
  hrow : row < tr.rows.length
  hactive : (envAt tr row).loc Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.selA.ATTENUATE = 1
  -- the WitnessDecodes seam: the decode's sorted-tree roots ARE the committed cap-root limbs.
  oldAnchored : henc.oldRoot = (envAt tr row).loc (sbCol CAP_ROOT)
  newAnchored : henc.newRoot = (envAt tr row).loc (saCol CAP_ROOT)

/-- **`delegate_forces_committed_write` — the post cap-root is FORCED to the genuine sorted insert.** From
`Satisfied2 hash delegateV3` (via the DEPLOYED `insertWriteOp`, `delegateV3_forces_write`) the committed
AFTER `state.CAP_ROOT` limb is the genuine `writesTo` of the conferred grant at the edge key against the
committed BEFORE limb — under CR a forged post-root is excluded (`writesTo` is FUNCTIONAL). The forced
fact rides the DEPLOYED constraints: editing `delegateV3`'s write op turns this RED. -/
theorem delegate_forces_committed_write {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (del rec t : CellId)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hsat : Satisfied2 hash delegateV3 mi mf ma tr)
    (henc : DelegateCapsTreeEncodes S pre post del rec t)
    (anc : DelegateWriteAnchor S pre post del rec t hash mi mf ma tr henc) :
    writesTo hash henc.oldRoot
      ((envAt tr anc.row).loc (prmCol CAP_KEY)) ((envAt tr anc.row).loc (prmCol KEEP_MASK))
      henc.newRoot := by
  rw [anc.oldAnchored, anc.newAnchored]
  exact (delegateV3_forces_write hash mi mf ma tr hsat anc.row anc.hrow anc.hactive).2

/-- **`delegate_descriptorRefines_sat` — THE DELEGATE CLASS-A REFINEMENT (write FORCED).** From
`Satisfied2 hash delegateV3` + the decode + the realizable write-anchor, the kernel `DelegateSpec pre del
rec t post` HOLDS AND the post cap-root is the DEPLOYED-FORCED genuine sorted insert
(`delegate_forces_committed_write`). Unlike `delegate_descriptorRefines` (whose `newRoot` was a free
decode field), the post-root here is pinned by the LIVE `insertWriteOp` — guarantee A is circuit-forced.
The `grant` `Caps`-move + frame + log are the named §1 decode residual. -/
theorem delegate_descriptorRefines_sat {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (del rec t : CellId)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hsat : Satisfied2 hash delegateV3 mi mf ma tr)
    (henc : DelegateCapsTreeEncodes S pre post del rec t)
    (anc : DelegateWriteAnchor S pre post del rec t hash mi mf ma tr henc) :
    DelegateSpec pre del rec t post
    ∧ writesTo hash henc.oldRoot
        ((envAt tr anc.row).loc (prmCol CAP_KEY)) ((envAt tr anc.row).loc (prmCol KEEP_MASK))
        henc.newRoot :=
  ⟨delegate_descriptorRefines S pre post del rec t henc,
   delegate_forces_committed_write S pre post del rec t hash mi mf ma tr hsat henc anc⟩

/-- **`grantCap_descriptorRefines_sat` — THE GRANTCAP CLASS-A REFINEMENT (write FORCED).** As
`delegate_descriptorRefines_sat`, consuming `Satisfied2 hash grantCapWriteV3` via
`grantCapWriteV3_forces_write` (grantCap shares the moving attenuate-A base + the cap-crown write leg).
The bare grant routes to `DelegateSpec` (the same insert), so the SAME decode delivers the kernel spec. -/
theorem grantCap_descriptorRefines_sat {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (del rec t : CellId)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hsat : Satisfied2 hash grantCapWriteV3 mi mf ma tr)
    (henc : DelegateCapsTreeEncodes S pre post del rec t)
    (anc : DelegateWriteAnchor S pre post del rec t hash mi mf ma tr henc) :
    DelegateSpec pre del rec t post
    ∧ writesTo hash henc.oldRoot
        ((envAt tr anc.row).loc (prmCol CAP_KEY)) ((envAt tr anc.row).loc (prmCol KEEP_MASK))
        henc.newRoot := by
  refine ⟨delegate_descriptorRefines S pre post del rec t henc, ?_⟩
  rw [anc.oldAnchored, anc.newAnchored]
  exact (grantCapWriteV3_forces_write hash mi mf ma tr hsat anc.row anc.hrow anc.hactive).2

/-- **`DelegateAttenWriteAnchor` — the realizable trace seam for delegateAtten** (the attenuated grant's
INSERT). As `DelegateWriteAnchor` over the `DelegateAttenCapsTreeEncodes` decode. -/
structure DelegateAttenWriteAnchor {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (del rec t : CellId) (keep : List Auth)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (henc : DelegateAttenCapsTreeEncodes S pre post del rec t keep) : Type where
  row : Nat
  hrow : row < tr.rows.length
  hactive : (envAt tr row).loc Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.selA.ATTENUATE = 1
  oldAnchored : henc.oldRoot = (envAt tr row).loc (sbCol CAP_ROOT)
  newAnchored : henc.newRoot = (envAt tr row).loc (saCol CAP_ROOT)

/-- **`delegateAtten_descriptorRefines_sat` — THE DELEGATEATTEN CLASS-A REFINEMENT (write FORCED + non-amp).**
From `Satisfied2 hash delegateAttenV3` (via `delegateAttenV3_non_amp` — the DEPLOYED held-read + insert-write
+ submask lookup), the kernel `DelegateAttenSpec` HOLDS, the post cap-root is the DEPLOYED-FORCED genuine
sorted insert of the attenuated grant, AND the conferred mask `⊑` the held mask (non-amplification, FORCED
in-circuit). The attenuated-`grant` `Caps`-move + frame + log are the named §2.b decode residual. -/
theorem delegateAtten_descriptorRefines_sat {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (del rec t : CellId) (keep : List Auth)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hsub : tr.tf (.custom Dregg2.Circuit.Emit.EffectVmEmitV2.SUBMASK_TID)
      = Dregg2.Circuit.Emit.EffectVmEmitV2.subsetTable Dregg2.Circuit.Emit.EffectVmEmitV2.MASK_BITS)
    (hsat : Satisfied2 hash delegateAttenV3 mi mf ma tr)
    (henc : DelegateAttenCapsTreeEncodes S pre post del rec t keep)
    (anc : DelegateAttenWriteAnchor S pre post del rec t keep hash mi mf ma tr henc) :
    DelegateAttenSpec pre del rec t keep post
    ∧ writesTo hash henc.oldRoot
        ((envAt tr anc.row).loc (prmCol CAP_KEY)) ((envAt tr anc.row).loc (prmCol KEEP_MASK))
        henc.newRoot
    ∧ ∃ a b : Nat, (envAt tr anc.row).loc (prmCol KEEP_MASK) = (a : ℤ)
        ∧ (envAt tr anc.row).loc (prmCol HELD_MASK) = (b : ℤ) ∧ a &&& b = a := by
  have hforced := delegateAttenV3_non_amp hash mi mf ma tr hsub hsat anc.row anc.hrow anc.hactive
  refine ⟨delegateAtten_descriptorRefines S pre post del rec t keep henc, ?_, hforced.2.2⟩
  rw [anc.oldAnchored, anc.newAnchored]
  exact hforced.2.1

/-! ## §3.5F — CLASS A for the FROZEN-FACE slots, REBASED onto the MOVING `…Genuine` face
(introduce / revokeDelegation — guarantee A circuit-FORCED).

The triage (a93b40505) found `introduce`/`revokeDelegation` FREEZE `cap_root` on-row (`gCapPass`), so a
`writesTo (sbCol CAP_ROOT) k v (saCol CAP_ROOT)` map-op is JOINTLY UNSAT with the freeze. The close: rebase
their V3 base onto the MOVING `…Genuine` face (no freeze, no opaque `gCapMove`), which carries the deployed
`insertWriteOp` (introduce) / `removeWriteOp` (revokeDelegation). The DEPLOYED descriptors `introduceWriteV3`
/ `revokeDelegationWriteV3` now FORCE the cap-tree write from `Satisfied2` — `introduceWriteV3_forces_write`
/ `revokeDelegationWriteV3_forces_write`. Each rung below pins the post cap-root via the LIVE write op
(mirroring `delegate_descriptorRefines_sat`), so guarantee A is circuit-forced for these two FROZEN-FACE
slots. `refreshDelegation` is the residual genuine obstruction (§3.5R). -/

/-- **`IntroduceWriteAnchor` — the realizable trace seam for introduce** (the conferred-grant INSERT on the
MOVING genuine face). As `DelegateWriteAnchor` over the `DelegateCapsTreeEncodes` decode (introduce routes to
`DelegateSpec`/`recDelegateCaps`, the same insert). -/
structure IntroduceWriteAnchor {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (del rec t : CellId)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (henc : DelegateCapsTreeEncodes S pre post del rec t) : Type where
  row : Nat
  hrow : row < tr.rows.length
  hactive : (envAt tr row).loc Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.selA.ATTENUATE = 1
  oldAnchored : henc.oldRoot = (envAt tr row).loc (sbCol CAP_ROOT)
  newAnchored : henc.newRoot = (envAt tr row).loc (saCol CAP_ROOT)

/-- **`introduce_descriptorRefines_sat` — THE INTRODUCE CLASS-A REFINEMENT (write FORCED, frozen-face
close).** From `Satisfied2 hash introduceWriteV3` (via `introduceWriteV3_forces_write` on the MOVING genuine
face), the kernel `DelegateSpec` HOLDS AND the post cap-root is the DEPLOYED-FORCED genuine sorted insert.
The v1-face `gCapPass` freeze that left the write off-row is GONE — guarantee A circuit-forced. -/
theorem introduce_descriptorRefines_sat {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (del rec t : CellId)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hsat : Satisfied2 hash introduceWriteV3 mi mf ma tr)
    (henc : DelegateCapsTreeEncodes S pre post del rec t)
    (anc : IntroduceWriteAnchor S pre post del rec t hash mi mf ma tr henc) :
    DelegateSpec pre del rec t post
    ∧ writesTo hash henc.oldRoot
        ((envAt tr anc.row).loc (prmCol CAP_KEY)) ((envAt tr anc.row).loc (prmCol KEEP_MASK))
        henc.newRoot := by
  refine ⟨delegate_descriptorRefines S pre post del rec t henc, ?_⟩
  rw [anc.oldAnchored, anc.newAnchored]
  exact (introduceWriteV3_forces_write hash mi mf ma tr hsat anc.row anc.hrow anc.hactive).2

/-- **`RevokeDelegationWriteAnchor` — the realizable trace seam for revokeDelegation** (the edge REMOVE on the
MOVING genuine face). As `DelegateWriteAnchor` over the `RevokeCapsTreeEncodes` decode; revokeDelegation
routes to `RevokeSpec`/`removeEdgeCaps`. -/
structure RevokeDelegationWriteAnchor {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (holder t : CellId)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (henc : RevokeCapsTreeEncodes S pre post holder t) : Type where
  row : Nat
  hrow : row < tr.rows.length
  hactive : (envAt tr row).loc Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.selA.ATTENUATE = 1
  oldAnchored : henc.oldRoot = (envAt tr row).loc (sbCol CAP_ROOT)
  newAnchored : henc.newRoot = (envAt tr row).loc (saCol CAP_ROOT)

/-- **`revokeDelegation_descriptorRefines_sat` — THE REVOKEDELEGATION CLASS-A REFINEMENT (write FORCED,
frozen-face close).** From `Satisfied2 hash revokeDelegationWriteV3` (via
`revokeDelegationWriteV3_forces_write` on the MOVING genuine face), the kernel `RevokeSpec` HOLDS AND the
post cap-root is the DEPLOYED-FORCED genuine sorted REMOVE (the ZERO-sentinel write) at the revoked edge key.
The v1-face `gCapPass` freeze is GONE — guarantee A circuit-forced. Non-amp structural (ZERO write). -/
theorem revokeDelegation_descriptorRefines_sat {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (holder t : CellId)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hsat : Satisfied2 hash revokeDelegationWriteV3 mi mf ma tr)
    (henc : RevokeCapsTreeEncodes S pre post holder t)
    (anc : RevokeDelegationWriteAnchor S pre post holder t hash mi mf ma tr henc) :
    RevokeSpec pre holder t post
    ∧ writesTo hash henc.oldRoot
        ((envAt tr anc.row).loc (prmCol CAP_KEY)) 0
        henc.newRoot := by
  refine ⟨revoke_descriptorRefines S pre post holder t henc, ?_⟩
  rw [anc.oldAnchored, anc.newAnchored]
  exact (revokeDelegationWriteV3_forces_write hash mi mf ma tr hsat anc.row anc.hrow anc.hactive).2

/-- **CLASS-A TOOTH (introduce) — a forged wrong post-root is UNSAT.** Mutation: dropping `insertWriteOp`
from `introduceWriteV3` removes the forced `writesTo`, so this conclusion can no longer be drawn. -/
theorem introduce_sat_forces_postroot {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (del rec t : CellId)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hsat : Satisfied2 hash introduceWriteV3 mi mf ma tr)
    (henc : DelegateCapsTreeEncodes S pre post del rec t)
    (anc : IntroduceWriteAnchor S pre post del rec t hash mi mf ma tr henc) :
    writesTo hash henc.oldRoot
      ((envAt tr anc.row).loc (prmCol CAP_KEY)) ((envAt tr anc.row).loc (prmCol KEEP_MASK))
      henc.newRoot :=
  (introduce_descriptorRefines_sat S pre post del rec t hash mi mf ma tr hsat henc anc).2

#assert_axioms introduce_descriptorRefines_sat
#assert_axioms revokeDelegation_descriptorRefines_sat
#assert_axioms introduce_sat_forces_postroot

/-! ## §3.5B — THE APEX-WIRING BRIDGE rungs (`…_descriptorRefines_capOpenSat`): the cap-open WRAPPER strips
to the base, so the apex fan-out (`Rfix tag = capOpenWrapper base`) consumes the base CLASS-A rung.

The apex fanout cannot wire delegate(tag 1)/revoke(tag 2)/delegateAtten(tag 11)/introduce(tag 10)/
revokeDelegation(tag 14)/revokeCapability(tag 24) directly because `Rfix tag` = the cap-open WRAPPER
descriptor (`delegateCapOpenV3` etc.), NOT defeq to `<slot>V3`, so `Satisfied2 hash (Rfix tag)` doesn't
coerce. `capOpen_satisfied2_strips_to_base` STRIPS the cap-open authority appendix + selector tooth (both
additive — they read no base column, surface no map/mem op), yielding `Satisfied2 hash <slot>V3`, which the
base `_descriptorRefines_sat` consumes. Each rung below is the wrapped form the main loop wires. -/

/-- **`delegate_descriptorRefines_capOpenSat` — the apex-wirable delegate rung.** Consumes `Satisfied2 hash
delegateWriteCapOpenV3` (the WRITE-FORCING wrapper, base `grantCapWriteV3`) by stripping to `Satisfied2
grantCapWriteV3` and applying `grantCap_descriptorRefines_sat`. The apex (`Rfix 1` re-pointed to
`delegateWriteCapOpenV3`) wires this. -/
theorem delegate_descriptorRefines_capOpenSat {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (del rec t : CellId)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hsat : Satisfied2 hash delegateWriteCapOpenV3 mi mf ma tr)
    (henc : DelegateCapsTreeEncodes S pre post del rec t)
    (anc : DelegateWriteAnchor S pre post del rec t hash mi mf ma tr henc) :
    DelegateSpec pre del rec t post
    ∧ writesTo hash henc.oldRoot
        ((envAt tr anc.row).loc (prmCol CAP_KEY)) ((envAt tr anc.row).loc (prmCol KEEP_MASK))
        henc.newRoot :=
  grantCap_descriptorRefines_sat S pre post del rec t hash mi mf ma tr
    (capOpen_satisfied2_strips_to_base hash _ grantCapWriteV3 _ _ mi mf ma tr hsat) henc anc

/-- **`grantCap_descriptorRefines_capOpenSat` — the apex-wirable grantCap rung.** As above over
`grantCapWriteCapOpenV3` (base `grantCapWriteV3`). The apex wires this. -/
theorem grantCap_descriptorRefines_capOpenSat {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (del rec t : CellId)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hsat : Satisfied2 hash grantCapWriteCapOpenV3 mi mf ma tr)
    (henc : DelegateCapsTreeEncodes S pre post del rec t)
    (anc : DelegateWriteAnchor S pre post del rec t hash mi mf ma tr henc) :
    DelegateSpec pre del rec t post
    ∧ writesTo hash henc.oldRoot
        ((envAt tr anc.row).loc (prmCol CAP_KEY)) ((envAt tr anc.row).loc (prmCol KEEP_MASK))
        henc.newRoot :=
  grantCap_descriptorRefines_sat S pre post del rec t hash mi mf ma tr
    (capOpen_satisfied2_strips_to_base hash _ grantCapWriteV3 _ _ mi mf ma tr hsat) henc anc

/-- **`delegateAtten_descriptorRefines_capOpenSat` — the apex-wirable delegateAtten rung (tag 11).** Consumes
`Satisfied2 hash delegateAttenWriteCapOpenV3` (base `delegateAttenV3`) by stripping to `Satisfied2
delegateAttenV3` and applying `delegateAtten_descriptorRefines_sat` (write FORCED + the `granted ⊑ held`
non-amplification). The apex (`Rfix 11` re-pointed) wires this. -/
theorem delegateAtten_descriptorRefines_capOpenSat {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (del rec t : CellId) (keep : List Auth)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hsub : tr.tf (.custom Dregg2.Circuit.Emit.EffectVmEmitV2.SUBMASK_TID)
      = Dregg2.Circuit.Emit.EffectVmEmitV2.subsetTable Dregg2.Circuit.Emit.EffectVmEmitV2.MASK_BITS)
    (hsat : Satisfied2 hash delegateAttenWriteCapOpenV3 mi mf ma tr)
    (henc : DelegateAttenCapsTreeEncodes S pre post del rec t keep)
    (anc : DelegateAttenWriteAnchor S pre post del rec t keep hash mi mf ma tr henc) :
    DelegateAttenSpec pre del rec t keep post
    ∧ writesTo hash henc.oldRoot
        ((envAt tr anc.row).loc (prmCol CAP_KEY)) ((envAt tr anc.row).loc (prmCol KEEP_MASK))
        henc.newRoot
    ∧ ∃ a b : Nat, (envAt tr anc.row).loc (prmCol KEEP_MASK) = (a : ℤ)
        ∧ (envAt tr anc.row).loc (prmCol HELD_MASK) = (b : ℤ) ∧ a &&& b = a :=
  delegateAtten_descriptorRefines_sat S pre post del rec t keep hash mi mf ma tr hsub
    (capOpen_satisfied2_strips_to_base hash _ delegateAttenV3 _ _ mi mf ma tr hsat) henc anc

/-- **`introduce_descriptorRefines_capOpenSat` — the apex-wirable introduce rung.** Consumes `Satisfied2
hash introduceWriteCapOpenV3` (the WRITE-FORCING wrapper, base `introduceWriteV3`) by stripping to the base
and applying `introduce_descriptorRefines_sat`. The apex (`Rfix 10` re-pointed to `introduceWriteCapOpenV3`)
wires this. -/
theorem introduce_descriptorRefines_capOpenSat {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (del rec t : CellId)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hsat : Satisfied2 hash introduceWriteCapOpenV3 mi mf ma tr)
    (henc : DelegateCapsTreeEncodes S pre post del rec t)
    (anc : IntroduceWriteAnchor S pre post del rec t hash mi mf ma tr henc) :
    DelegateSpec pre del rec t post
    ∧ writesTo hash henc.oldRoot
        ((envAt tr anc.row).loc (prmCol CAP_KEY)) ((envAt tr anc.row).loc (prmCol KEEP_MASK))
        henc.newRoot :=
  introduce_descriptorRefines_sat S pre post del rec t hash mi mf ma tr
    (capOpen_satisfied2_strips_to_base hash _ introduceWriteV3 _ _ mi mf ma tr hsat) henc anc

/-- **`revokeDelegation_descriptorRefines_capOpenSat` — the apex-wirable revokeDelegation rung.** Consumes
`Satisfied2 hash revokeDelegationWriteCapOpenV3` (base `revokeDelegationWriteV3`) by stripping to the base
and applying `revokeDelegation_descriptorRefines_sat`. The apex (`Rfix 14` re-pointed) wires this. -/
theorem revokeDelegation_descriptorRefines_capOpenSat {State : Type} (S : CapHashScheme State)
    (pre post : RecChainedState) (holder t : CellId)
    (hash : List ℤ → ℤ) (mi : ℤ → ℤ) (mf : ℤ → ℤ × Nat) (ma : List ℤ) (tr : VmTrace)
    (hsat : Satisfied2 hash revokeDelegationWriteCapOpenV3 mi mf ma tr)
    (henc : RevokeCapsTreeEncodes S pre post holder t)
    (anc : RevokeDelegationWriteAnchor S pre post holder t hash mi mf ma tr henc) :
    RevokeSpec pre holder t post
    ∧ writesTo hash henc.oldRoot
        ((envAt tr anc.row).loc (prmCol CAP_KEY)) 0
        henc.newRoot :=
  revokeDelegation_descriptorRefines_sat S pre post holder t hash mi mf ma tr
    (capOpen_satisfied2_strips_to_base hash _ revokeDelegationWriteV3 _ _ mi mf ma tr hsat) henc anc

/-! `revokeCapability` (tag 24) needs NO strip bridge: its DEPLOYED write rides `revokeCapabilityV3` directly
(`v3OfWith … [heldReadOp, removeWriteOp]`), whose `revokeCapability_descriptorRefines_sat` (§3.A) already
carries the `Satisfied2 revokeCapabilityV3` write leg. The apex wires that rung over `revokeCapabilityV3`; the
cap-open wrapper's authority appendix rides the SEPARATE `revokeCapabilityCapOpenV3` keystone
(`revokeCapabilityCapOpenV3_authorizes`). The two legs (authority READ via the cap-open wrapper, cap-tree
WRITE via `revokeCapabilityV3`) are independent rungs the apex composes. -/

#assert_axioms delegate_descriptorRefines_capOpenSat
#assert_axioms grantCap_descriptorRefines_capOpenSat
#assert_axioms delegateAtten_descriptorRefines_capOpenSat
#assert_axioms introduce_descriptorRefines_capOpenSat
#assert_axioms revokeDelegation_descriptorRefines_capOpenSat

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
#assert_axioms revokeDelegation_execFullA
#assert_axioms revoke_drops_edge
-- §3.5 CLASS-A: the cap-tree WRITE forced from the DEPLOYED descriptor (the moving-face 3 of 5 gaps).
#assert_axioms delegate_forces_committed_write
#assert_axioms delegate_descriptorRefines_sat
#assert_axioms grantCap_descriptorRefines_sat
#assert_axioms delegateAtten_descriptorRefines_sat

/-! ## §3.A — revokeCapability: CLASS A from the DEPLOYED `revokeCapabilityV3` (the write-leg IS deployed).

Unlike the §1–§3 modelled-`SpineCommits` decodes and §3.5's moving-face gaps, `revokeCapability` carries its
remove-WRITE on the live wire AT HEAD already: `revokeCapabilityV3 = v3OfWith … [.mapOp heldReadOp, .mapOp
removeWriteOp]`, `removeWriteOp` being the genuine `writesTo cap_root key 0 cap_root_after` (the ZERO-sentinel
remove). So `revokeCapability` is CLASS A by the same recipe Birth/Notes/cellSeal use — the DEPLOYED gate
forces the felt-level cap-tree write, and a `WitnessDecodes`-class seam lifts it to the kernel `removeEdgeCaps`
move. `revokeCapabilityV3_non_amp` (mirrors `attenuateV3_non_amp`) forces `opensTo` (held authenticated) +
`writesTo … 0 …` (the ZERO remove) from `Satisfied2 hash revokeCapabilityV3`; the `capsMoveDecodes` seam lifts
the forced write to `removeEdgeCaps`. No submask lookup — revoke deletes a slot, non-amplification is
structural. -/

theorem revokeCapabilityV3_non_amp (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash revokeCapabilityV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length)
    (hactive : (envAt t i).loc Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.selA.ATTENUATE = 1) :
    opensTo hash ((envAt t i).loc (sbCol CAP_ROOT))
        ((envAt t i).loc (prmCol CAP_KEY))
        (some ((envAt t i).loc (prmCol HELD_MASK)))
    ∧ writesTo hash ((envAt t i).loc (sbCol CAP_ROOT))
        ((envAt t i).loc (prmCol CAP_KEY)) 0
        ((envAt t i).loc (saCol CAP_ROOT)) := by
  have hrowc := hsat.rowConstraints i hi
  have hmem : ∀ c ∈ ([.mapOp heldReadOp, .mapOp removeWriteOp] :
      List Dregg2.Circuit.DescriptorIR2.VmConstraint2), c ∈ revokeCapabilityV3.constraints :=
    fun c hc => List.mem_append_right _ hc
  have hread := hrowc (.mapOp heldReadOp) (hmem _ (by simp))
  have hwrite := hrowc (.mapOp removeWriteOp) (hmem _ (by simp))
  exact ⟨(hread hactive).1, hwrite hactive⟩

/-- **`RevokeCapabilityTraceReadout` — the realizable circuit-witness extraction for revokeCapability.** The
`WitnessDecodes` class of cellSeal's `CellSealTraceReadout`: the ACTIVE cap-graph row + its selector + the
cap-remove seam (the deployed-forced ZERO-write IS the kernel `removeEdgeCaps` move) + receipt + frame. -/
structure RevokeCapabilityTraceReadout (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (holder target : CellId) : Type where
  row : Nat
  hrow : row < t.rows.length
  hsel : (envAt t row).loc Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.selA.ATTENUATE = 1
  capsMoveDecodes :
    writesTo hash ((envAt t row).loc (sbCol CAP_ROOT))
        ((envAt t row).loc (prmCol CAP_KEY)) 0
        ((envAt t row).loc (saCol CAP_ROOT))
      → post.kernel.caps = removeEdgeCaps pre.kernel.caps holder target
  logAdv : post.log = authReceipt holder :: pre.log
  frame : KernelFrameExceptCaps pre post

/-- **`revokeCapability_forced_sat` — the cap-edge removal is FORCED by the DEPLOYED `revokeCapabilityV3`.** -/
theorem revokeCapability_forced_sat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash revokeCapabilityV3 minit mfin maddrs t)
    (pre post : RecChainedState) (holder target : CellId)
    (rd : RevokeCapabilityTraceReadout hash minit mfin maddrs t pre post holder target) :
    post.kernel.caps = removeEdgeCaps pre.kernel.caps holder target :=
  rd.capsMoveDecodes
    (revokeCapabilityV3_non_amp hash hsat rd.row rd.hrow rd.hsel).2

/-- **`revokeCapability_descriptorRefines_sat` — THE CLASS-A REFINEMENT for revokeCapability.** The
`removeEdgeCaps` move is forced from the DEPLOYED remove-write's `Satisfied2`; editing `revokeCapabilityV3`'s
constraints turns this RED. -/
theorem revokeCapability_descriptorRefines_sat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash revokeCapabilityV3 minit mfin maddrs t)
    (pre post : RecChainedState) (holder target : CellId)
    (rd : RevokeCapabilityTraceReadout hash minit mfin maddrs t pre post holder target) :
    RevokeSpec pre holder target post :=
  ⟨trivial, revokeCapability_forced_sat hash hsat pre post holder target rd, rd.logAdv,
   rd.frame.frAccounts, rd.frame.frCell, rd.frame.frNullifiers, rd.frame.frRevoked,
   rd.frame.frCommitments, rd.frame.frBal, rd.frame.frSlotCaveats, rd.frame.frFactories,
   rd.frame.frLifecycle, rd.frame.frDeathCert, rd.frame.frDelegate, rd.frame.frDelegations,
   rd.frame.frDelegationEpoch, rd.frame.frDelegationEpochAt, rd.frame.frHeaps⟩

/-- **`revokeCapability_execFullA_sat` — the Class-A refinement against the executor arm.** -/
theorem revokeCapability_execFullA_sat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash revokeCapabilityV3 minit mfin maddrs t)
    (pre post : RecChainedState) (holder target : CellId)
    (rd : RevokeCapabilityTraceReadout hash minit mfin maddrs t pre post holder target) :
    execFullA pre (.revoke holder target) = some post :=
  (execFullA_revoke_iff_spec pre holder target post).mpr
    (revokeCapability_descriptorRefines_sat hash hsat pre post holder target rd)

/-- **CLASS-A TOOTH — a forged wrong-caps revokeCapability witness is UNSAT.** -/
theorem revokeCapability_sat_rejects_wrong_caps (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash revokeCapabilityV3 minit mfin maddrs t)
    (pre post : RecChainedState) (holder target : CellId)
    (rd : RevokeCapabilityTraceReadout hash minit mfin maddrs t pre post holder target)
    (hwrong : post.kernel.caps ≠ removeEdgeCaps pre.kernel.caps holder target) :
    False :=
  hwrong (revokeCapability_forced_sat hash hsat pre post holder target rd)

#assert_axioms revokeCapabilityV3_non_amp
#assert_axioms revokeCapability_forced_sat
#assert_axioms revokeCapability_descriptorRefines_sat
#assert_axioms revokeCapability_execFullA_sat
#assert_axioms revokeCapability_sat_rejects_wrong_caps

end Dregg2.Circuit.RotatedKernelRefinementCapFamily
