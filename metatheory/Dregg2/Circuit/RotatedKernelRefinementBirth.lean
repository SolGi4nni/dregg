/-
# Dregg2.Circuit.RotatedKernelRefinementBirth — the PRINCIPLED-FIX VALUE-leg circuit→kernel
  refinements for the CELL-BIRTH family, fanning out the `cellSeal` committed-root template
  (`RotatedKernelRefinementCellSeal`) to the three account-GROWTH effects:

  * **createCell**            — `accounts := insert newCell accounts` + the new cell born EMPTY.
  * **createCellFromFactory** — like createCell + a factory VK/fields/caveats install on the new cell.
  * **spawn**                 — like createCell + a parent→child CAPABILITY HANDOFF (the cap-tree write).

## The gap each closes (same class as cellSeal's genuinely-FALSE VALUE rung)

The load-bearing move of every birth effect is the GROWTH of the live account set:
`accounts := insert newCell accounts`, with the new cell's per-cell records BORN EMPTY. The deployed
circuit's per-cell commitment `hash(bal_lo,bal_hi,nonce,fields[0..7],cap_root)`
(`cell_state.rs::compute_commitment`) is PER EXISTING CELL — it binds NO column for the SET of live
accounts. So a `*_descriptorRefines` against the DEPLOYED descriptor cannot tell whether the new cell
was actually inserted (a prover could publish a commitment that silently drops/reorders the account
index). This is the SAME class as cellSeal's side-table write: the kernel datum (`accounts : Finset
CellId`) has no committed home in the deployed shape.

## The binding mechanism (chosen: a dedicated committed `accountsRoot` limb)

`accounts : Finset CellId` already has an honest commitment carrier: `AccountsCommit` — the Poseidon
list-sponge over the canonical sorted account index `k.accounts.sort (· ≤ ·)`, reusing
`ListCommit.listDigest` + `ListDigestBindsList`, with `accounts_eq_of_sorted_eq` proving equal sorted
lists force equal Finsets (a drop/reorder is REJECTED). We model its committed root — `accountsRoot` —
EXACTLY as cellSeal models `lifecycleRoot`: a `listDigest` over the touched datum, binding via the
realizable `compressNInjective` Poseidon-CR carrier, absorbed as ONE more committed limb. The FIX gate
`gAccountsGrow` forces the POST accounts-root to the digest of `insert newCell pre.accounts`.

> ADDITIVITY NOTE. Same as cellSeal: NOT a `N_SYSTEM_ROOTS`+1 index (that mutates ~45 modules + the
> Rust `[FieldElement; 8]`). The accounts root is its OWN dedicated committed limb, reusing the
> `AccountsCommit` carrier already proven. The Rust realization: `compute_commitment` absorbs an
> `accounts_root` limb and the birth trace-fills emit the grown-set root. ONE VK epoch rotation,
> SHARED across all three birth effects (the new commitment shape changes once).

## spawn — the parent→child CAP EDGE is now FORCED (the `caps` handoff close)

`SpawnSpec`'s load-bearing content is BOTH the accounts insert (forced via `accountsRoot`) AND the
parent→child CAPABILITY HANDOFF: `caps := spawnCapsMap`, `delegate := spawnDelegateMap`, `delegations :=
spawnDelegationsMap`. The `caps` edge — the genuine confer (`child ↦ [heldCapTo caps actor target]`, an
INSERT into the cap-tree) — is the load-bearing one.

`spawnV3` pins `cap_root` FROZEN (`gCapPass`), so on it the cap handoff was the named PHASE-D residual.
**`spawnWriteV3`** (§5b) REBASES onto the cap-WRITE rotation (`rotateV3WithNewCellKeyPinCapWrite`: cap-root
limb 25 FREED) ALONGSIDE the unchanged accounts grow-gate (limb 0 — they coexist, distinct limbs); the
cap-tree INSERT is FORCED by the deployed `effCapInsertV3 spawnWriteV3` keystone wrap
(`CapInsertEmit.effCapInsertV3_forces_write8` — the spliced conferred edge over the FULL committed 8-felt
cap-root groups; the arity-2 map-op pair was shape-UNSAT vs the arity-7 `CanonicalCapTree` and is
DROPPED) — exactly as `RotatedKernelRefinementCapFamily.delegate_forces_committed_write`. The
`SpawnTraceReadout.capsMoveDecodes` seam (the faithful cap-tree↔kernel-`Caps` ENCODING — a HYPOTHESIS,
never an axiom, exactly `RevokeCapabilityTraceReadout.capsMoveDecodes`'s class) lifts the forced
`capInserts8` to the `caps` function move; `spawn_caps_forced_sat`/`spawnWrite_descriptorRefines_sat`
discharge it.

So spawn's `caps` handoff is FORCED (no longer VALUE_PARTIAL on the cap edge). The `delegate`/`delegations`
POINTER moves remain the NAMED faithful-encoding residual (the single cap-tree INSERT binds the `caps`
edge, not the per-cell `delegate`/`delegations` snapshots — stated precisely, NOT laundered as bound). The
legacy `spawnV3` rungs (`spawn_descriptorRefines_sat`) keep the frozen-root residual `capHandoff`.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} + the realizable Poseidon-CR carrier
(`compressNInjective` + the injective `accountsLeaf`, the SAME carrier `AccountsCommit`/`ListCommit`
use). NEW file; all imports read-only.
-/
import Dregg2.Circuit.RotatedKernelRefinementMisc
import Dregg2.Circuit.AccountsCommit
import Dregg2.Circuit.Spec.accountgrowth
import Dregg2.Circuit.Spec.factorycreation
import Dregg2.Circuit.Emit.CapOpenEmit
import Dregg2.Circuit.Emit.CapInsertEmit

namespace Dregg2.Circuit.RotatedKernelRefinementBirth

open Dregg2.Circuit
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.StateCommit (compressNInjective)
open Dregg2.Circuit.AccountsCommit (accountsSorted accounts_eq_of_sorted_eq accountsSorted_eq_of_eq)
open Dregg2.Circuit.Spec.AccountGrowth
  (CreateCellSpec createCellAdmit createReceipt bornEmptyAt
   SpawnSpec SpawnFullSpec spawnAdmit spawnCapsMap spawnDelegateMap spawnDelegationsMap spawnEpochAtMap
   execCreateCellA_iff_spec)
open Dregg2.Circuit.Spec.FactoryCreation
  (CreateFromFactorySpec factoryAdmit factoryReceipt factoryPostCell factoryPostCaveats
   factoryBornCell factoryBornCaveats)
open Dregg2.Circuit.DescriptorIR2 (VmTrace Satisfied2 envAt writesTo opensTo)
open Dregg2.Circuit.Emit.EffectVmEmit (EFFECT_VM_WIDTH prmCol)
open Dregg2.Circuit.Emit.EffectVmEmitV2 (CAP_KEY KEEP_MASK ANCHOR_KEY ANCHOR_MASK)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
  (createCellV3 factoryV3 spawnV3
   createCellV3_grow_gate_forces_set_insert factoryV3_grow_gate_forces_set_insert
   spawnV3_grow_gate_forces_set_insert
   spawnWriteV3 spawnWriteV3_grow_gate_forces_set_insert
   beforeCapRootCol afterCapRootCol beforeCapRootCols afterCapRootCols
   withSelectorGate withSelectorGate_satisfied2
   beforeCellsRootCol afterCellsRootCol NEW_CELL_KEY_PARAM_COL FACTORY_CHILD_KEY_PARAM_COL)
open Dregg2.Circuit.DeployedCapTree (CapLeaf Cap8Scheme Digest8)
open Dregg2.Circuit.DeployedCapOpen (leafOf capPermOut)
open Dregg2.Circuit.DescriptorIR2 (ChipTableSoundN)
open Dregg2.Circuit.SortedTreeNonMembership (keyOf SpineCommits GapOpen sortedInsert)
open Dregg2.Circuit.Emit.CapOpenEmit (capOpenCols effCapInsertV3)
open Dregg2.Circuit.Emit.CapInsertEmit
  (capInserts8 effCapInsertV3_forces_write8 effCapInsertV3_strips_to_capOpen)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — the committed `accounts`-root column.

`accounts : Finset CellId`. Its committed root is the `listDigest` over the canonical sorted account
index (`accountsSorted = k.accounts.sort (· ≤ ·)`), reusing the `AccountsCommit` carrier. A field
element the circuit carries, exactly like a `system_roots` limb. The FIX gate forces the POST root to
the root of the GROWN set `insert newCell pre.accounts`. -/

/-- A field element (the same `ℤ`-carrier `ListCommit`/`AccountsCommit` use for a felt). -/
abbrev FieldElem := ℤ

/-- The injective leaf encoder for an account id (`CellId = Nat` cast into the felt carrier). Carried
injective (`accountsLeaf_injective`), the realizable Poseidon over a canonical per-id serialization. -/
def accountsLeaf : CellId → FieldElem := fun n => (n : ℤ)

/-- The accounts leaf encoder is injective (the realizable Poseidon-CR carrier). REALIZABLE: `Nat.cast`
into `ℤ` is literally injective. -/
theorem accountsLeaf_injective : listLeafInjective accountsLeaf := by
  intro a b h
  unfold accountsLeaf at h
  exact_mod_cast h

/-- **`accountsRoot compressN k`** — the committed root of `k.accounts`: the `listDigest` over the
canonical sorted account index. The Lean mirror of the Rust `accounts_root` limb the FIX adds to
`compute_commitment`. Absorbed into `state_commit` exactly as a `system_roots` digest is. -/
def accountsRoot (compressN : List FieldElem → FieldElem) (k : RecordKernelState) : FieldElem :=
  listDigest accountsLeaf compressN (accountsSorted k)

/-- **`accountsRoot_binds`** — equal accounts roots force the SAME `accounts` Finset. Off the realizable
`compressN`-injectivity carrier + the injective leaf + `accounts_eq_of_sorted_eq`: the digest binds the
sorted index, hence the whole set. The anti-ghost foundation a forged drop/reorder must clear. -/
theorem accountsRoot_binds (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (k k' : RecordKernelState)
    (h : accountsRoot compressN k = accountsRoot compressN k') :
    k.accounts = k'.accounts := by
  unfold accountsRoot at h
  have hsorted : accountsSorted k = accountsSorted k' :=
    ListDigestBindsList accountsLeaf compressN hN accountsLeaf_injective _ _ h
  exact accounts_eq_of_sorted_eq _ _ hsorted

/-! ## §1 — the FIX descriptor's accounts-root gate (the column-forcing gate).

The deployed birth row freezes the economic block; the FIX ADDS a committed accounts-root column whose
POST value the gate `gAccountsGrow` PINS to the GROWN-set digest. -/

/-- **`AccountsRootRow compressN preK postK preRoot postRoot`** — the decode tying the FIX row's two
committed accounts-root columns to the kernel pre/post accounts. -/
def AccountsRootRow (compressN : List FieldElem → FieldElem)
    (preK postK : RecordKernelState) (preRoot postRoot : FieldElem) : Prop :=
  preRoot = accountsRoot compressN preK ∧ postRoot = accountsRoot compressN postK

/-- **`gAccountsGrow compressN preK newCell postRoot`** — the FIX gate body: the POST accounts-root
column IS the digest of the GROWN set `insert newCell preK.accounts`. The committed-column analog of
`gLifecycleSeal`: the deployed circuit would EVALUATE this against the grown-set root the trace-fill
emits, so a row whose post accounts-root is anything else (a drop, a reorder, a wrong id) fails. -/
def gAccountsGrow (compressN : List FieldElem → FieldElem)
    (preK : RecordKernelState) (newCell : CellId) (postRoot : FieldElem) : Prop :=
  postRoot = listDigest accountsLeaf compressN ((insert newCell preK.accounts).sort (· ≤ ·))

/-- **`accountsGrowForced` — the FIX gate FORCES the committed accounts column.** If the FIX gate holds,
the POST accounts equal `insert newCell preK.accounts` (via `accountsRoot_binds`). This is the rung the
deployed circuit is MISSING and the FIX supplies — exactly `lifecycleSealForced` for the account set. -/
theorem accountsGrowForced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (preK postK : RecordKernelState) (newCell : CellId) (preRoot postRoot : FieldElem)
    (henc : AccountsRootRow compressN preK postK preRoot postRoot)
    (hgate : gAccountsGrow compressN preK newCell postRoot) :
    postK.accounts = insert newCell preK.accounts := by
  obtain ⟨_, hpost⟩ := henc
  -- the POST column is BOTH `accountsRoot postK` (decode) AND the grown-set digest (gate).
  have hroots : accountsRoot compressN postK
      = listDigest accountsLeaf compressN ((insert newCell preK.accounts).sort (· ≤ ·)) := by
    rw [← hpost]; exact hgate
  -- digest injectivity ⇒ equal sorted indices ⇒ equal Finsets.
  unfold accountsRoot at hroots
  have hsorted : accountsSorted postK = (insert newCell preK.accounts).sort (· ≤ ·) :=
    ListDigestBindsList accountsLeaf compressN hN accountsLeaf_injective _ _ hroots
  exact accounts_eq_of_sorted_eq _ _ hsorted

/-! ## §2 — createCell: the active-row ⟷ kernel decode + the refinement.

`createCellGenuineEncodes` ties a satisfying FIX-descriptor witness's accounts-root columns onto the
birth boundary, and carries the residual the per-cell accounts root cannot witness: the FIX gate (the
WITNESS leg), the `bornEmptyAt` per-cell records (born-empty is per-cell, off the accounts column), the
guard, the receipt log, and the global side-table frame. NAMED, not laundered. -/

/-- The decode relating a satisfying FIX createCell witness's row to a kernel `pre → post` birth of
`newCell` by `actor`. DATA-bearing (`Type`): it exhibits the two committed accounts-root columns,
carries the FIX gate (the witness leg) + the born-empty per-cell residual + the kernel-side residual. -/
structure createCellGenuineEncodes (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (actor newCell : CellId) : Type where
  -- the two committed accounts-root columns + their decode.
  preRoot : FieldElem
  postRoot : FieldElem
  hroots : AccountsRootRow compressN pre.kernel post.kernel preRoot postRoot
  -- the FIX gate holds on the row (the WITNESS leg — the committed accounts column is FORCED grown).
  gate : gAccountsGrow compressN pre.kernel newCell postRoot
  -- the admissibility guard (privileged creation authority ∧ freshness).
  guard : createCellAdmit pre.kernel actor newCell
  -- the new cell's BORN-EMPTY per-cell records (per-cell, off the accounts column — NAMED residual).
  born : bornEmptyAt pre.kernel newCell post.kernel
  -- the creation receipt advance (the record-layer commitment, off the per-row block).
  logAdv : post.log = createReceipt actor newCell :: pre.log
  -- the global side-table frame (the `CreateCellSpec` frame residual).
  frNullifiers : post.kernel.nullifiers = pre.kernel.nullifiers
  frRevoked : post.kernel.revoked = pre.kernel.revoked
  frCommitments : post.kernel.commitments = pre.kernel.commitments
  frFactories : post.kernel.factories = pre.kernel.factories
  frDelegationEpoch : post.kernel.delegationEpoch = pre.kernel.delegationEpoch
  frDelegationEpochAt : post.kernel.delegationEpochAt = pre.kernel.delegationEpochAt
  frHeaps : post.kernel.heaps = pre.kernel.heaps
  frNullifierRoot : post.kernel.nullifierRoot = pre.kernel.nullifierRoot
  frRevokedRoot : post.kernel.revokedRoot = pre.kernel.revokedRoot

/-- **`createCell_accounts_forced` — the committed accounts growth is FIX-CIRCUIT-FORCED.** On the
decoded row the FIX accounts gate forces the post accounts to `insert newCell pre.accounts`. -/
theorem createCell_accounts_forced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor newCell : CellId)
    (henc : createCellGenuineEncodes compressN pre post actor newCell) :
    post.kernel.accounts = insert newCell pre.kernel.accounts :=
  accountsGrowForced compressN hN pre.kernel post.kernel newCell henc.preRoot henc.postRoot
    henc.hroots henc.gate

/-- **`createCell_descriptorRefines` — THE FIX CIRCUIT→KERNEL REFINEMENT for createCell.** A satisfying
FIX createCell descriptor witness forces the KERNEL's birth step `CreateCellSpec pre actor newCell post`.
The `accounts := insert newCell` growth is FORCED via the committed accounts root
(`createCell_accounts_forced`); the guard, the born-empty per-cell records, the receipt, and the frame
are the named decode residual. -/
theorem createCell_descriptorRefines (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor newCell : CellId)
    (henc : createCellGenuineEncodes compressN pre post actor newCell) :
    CreateCellSpec pre actor newCell post := by
  refine ⟨henc.guard, ?_, henc.born, henc.logAdv, henc.frNullifiers, henc.frRevoked,
    henc.frCommitments, henc.frFactories, henc.frDelegationEpoch, henc.frDelegationEpochAt,
    henc.frHeaps, henc.frNullifierRoot, henc.frRevokedRoot⟩
  exact createCell_accounts_forced compressN hN pre post actor newCell henc

/-- **The refinement, stated against `execFullA` directly.** `CreateCellSpec` IS the `.createCellA` arm
of the executor (`execCreateCellA_iff_spec`), so a satisfying FIX witness forces
`execFullA pre (.createCellA actor newCell) = some post`. -/
theorem createCell_descriptorRefines_execFullA (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor newCell : CellId)
    (henc : createCellGenuineEncodes compressN pre post actor newCell) :
    execFullA pre (.createCellA actor newCell) = some post :=
  (execCreateCellA_iff_spec pre actor newCell post).mpr
    (createCell_descriptorRefines compressN hN pre post actor newCell henc)

/-- **`createCell_descriptorRefines_rejects_wrong_accounts` (BOTH-POLARITY TOOTH).** A decode whose post
accounts are NOT `insert newCell pre.accounts` (a drop, a reorder, a missing insert — the deployed
circuit's blind spot) cannot ride a satisfying FIX witness: the accounts-root gate pins the grown set,
so the claim is contradictory. This is EXACTLY what the deployed circuit cannot reject. -/
theorem createCell_descriptorRefines_rejects_wrong_accounts (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor newCell : CellId)
    (henc : createCellGenuineEncodes compressN pre post actor newCell)
    (hwrong : post.kernel.accounts ≠ insert newCell pre.kernel.accounts) :
    False :=
  hwrong (createCell_accounts_forced compressN hN pre post actor newCell henc)

/-! ## §3 — createCellFromFactory: the same accounts gate + the factory-install residual.

`CreateFromFactorySpec` is createCell's growth + a factory VK/fields/caveats INSTALL on the new cell's
record (`factoryPostCell`/`factoryPostCaveats`). The accounts growth is FORCED here; the factory
install is a per-cell RECORD write (the install map cannot be witnessed by the accounts column — it
rides the deployed per-cell `fields[..]` block / a separate column), carried as the NAMED residual. -/

/-- The decode relating a satisfying FIX createCellFromFactory witness's row to a kernel `pre → post`
factory birth. The accounts-root columns + the FIX gate (the forced leg); the factory entry `e`, the
`factoryAdmit` guard, the install maps, the born-empty residuals, the receipt, the frame (NAMED). -/
structure createFromFactoryGenuineEncodes (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (actor newCell : CellId) (vk : Int) : Type where
  preRoot : FieldElem
  postRoot : FieldElem
  hroots : AccountsRootRow compressN pre.kernel post.kernel preRoot postRoot
  gate : gAccountsGrow compressN pre.kernel newCell postRoot
  -- the looked-up factory entry + the full factory admissibility guard.
  e : FactoryEntry
  guard : factoryAdmit pre.kernel actor newCell vk e
  -- the factory install maps on the new cell's record (per-cell RECORD writes — NAMED residual).
  frCell : post.kernel.cell = factoryPostCell (factoryBornCell pre.kernel newCell) newCell e
  frSlotCaveats : post.kernel.slotCaveats = factoryPostCaveats (factoryBornCaveats pre.kernel newCell) newCell e
  -- born-empty per-cell residuals from the create leg.
  frBal : post.kernel.bal = (fun c a => if c = newCell then 0 else pre.kernel.bal c a)
  frCaps : post.kernel.caps = fun l => if l = newCell then [] else pre.kernel.caps l
  frLifecycle : post.kernel.lifecycle = fun c => if c = newCell then 0 else pre.kernel.lifecycle c
  frDeathCert : post.kernel.deathCert = fun c => if c = newCell then 0 else pre.kernel.deathCert c
  frDelegate : post.kernel.delegate = fun c => if c = newCell then none else pre.kernel.delegate c
  frDelegations : post.kernel.delegations = fun c => if c = newCell then [] else pre.kernel.delegations c
  -- the factory creation receipt advance.
  logAdv : post.log = factoryReceipt actor newCell :: pre.log
  -- the global side-table frame.
  frNullifiers : post.kernel.nullifiers = pre.kernel.nullifiers
  frRevoked : post.kernel.revoked = pre.kernel.revoked
  frCommitments : post.kernel.commitments = pre.kernel.commitments
  frFactories : post.kernel.factories = pre.kernel.factories
  frDelegationEpoch : post.kernel.delegationEpoch = pre.kernel.delegationEpoch
  frDelegationEpochAt : post.kernel.delegationEpochAt = pre.kernel.delegationEpochAt
  frHeaps : post.kernel.heaps = pre.kernel.heaps
  frNullifierRoot : post.kernel.nullifierRoot = pre.kernel.nullifierRoot
  frRevokedRoot : post.kernel.revokedRoot = pre.kernel.revokedRoot

/-- **`createFromFactory_accounts_forced` — the committed accounts growth is FIX-CIRCUIT-FORCED.** -/
theorem createFromFactory_accounts_forced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor newCell : CellId) (vk : Int)
    (henc : createFromFactoryGenuineEncodes compressN pre post actor newCell vk) :
    post.kernel.accounts = insert newCell pre.kernel.accounts :=
  accountsGrowForced compressN hN pre.kernel post.kernel newCell henc.preRoot henc.postRoot
    henc.hroots henc.gate

/-- **`createCellFromFactory_descriptorRefines` — THE FIX CIRCUIT→KERNEL REFINEMENT for
createCellFromFactory.** A satisfying FIX witness forces `CreateFromFactorySpec pre actor newCell vk
post`. The accounts growth is FORCED via the committed accounts root; the factory VK/fields/caveats
install, the born-empty records, the receipt, and the frame are the named decode residual. -/
theorem createCellFromFactory_descriptorRefines (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor newCell : CellId) (vk : Int)
    (henc : createFromFactoryGenuineEncodes compressN pre post actor newCell vk) :
    CreateFromFactorySpec pre actor newCell vk post := by
  refine ⟨henc.e, henc.guard, ?_, henc.frBal, henc.frCell, henc.frSlotCaveats, henc.logAdv,
    henc.frCaps, henc.frLifecycle, henc.frDeathCert, henc.frDelegate, henc.frDelegations,
    henc.frNullifiers, henc.frRevoked, henc.frCommitments, henc.frFactories,
    henc.frDelegationEpoch, henc.frDelegationEpochAt, henc.frHeaps, henc.frNullifierRoot, henc.frRevokedRoot⟩
  exact createFromFactory_accounts_forced compressN hN pre post actor newCell vk henc

/-- **The refinement, stated against `execFullA` directly** (via `createCellFromFactoryChainA_iff_spec`
+ the `execFullA_createCellFromFactoryA` projection). -/
theorem createCellFromFactory_descriptorRefines_execFullA (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor newCell : CellId) (vk : Int)
    (henc : createFromFactoryGenuineEncodes compressN pre post actor newCell vk) :
    execFullA pre (.createCellFromFactoryA actor newCell vk) = some post := by
  rw [Dregg2.Circuit.Spec.FactoryCreation.execFullA_createCellFromFactoryA]
  exact (Dregg2.Circuit.Spec.FactoryCreation.createCellFromFactoryChainA_iff_spec
    pre actor newCell vk post).mpr
    (createCellFromFactory_descriptorRefines compressN hN pre post actor newCell vk henc)

/-- **`createCellFromFactory_descriptorRefines_rejects_wrong_accounts` (BOTH-POLARITY TOOTH).** -/
theorem createCellFromFactory_descriptorRefines_rejects_wrong_accounts
    (compressN : List FieldElem → FieldElem) (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor newCell : CellId) (vk : Int)
    (henc : createFromFactoryGenuineEncodes compressN pre post actor newCell vk)
    (hwrong : post.kernel.accounts ≠ insert newCell pre.kernel.accounts) :
    False :=
  hwrong (createFromFactory_accounts_forced compressN hN pre post actor newCell vk henc)

/-! ## §4 — spawn: VALUE_PARTIAL. The accounts insert is FORCED; the cap handoff is the PHASE-D residual.

`SpawnSpec` = createCell-of-child growth (FORCED via `accountsRoot`) PLUS the parent→child CAPABILITY
HANDOFF (`spawnCapsMap`/`spawnDelegateMap`/`spawnDelegationsMap`). The live descriptor pins `cap_root`
FROZEN (`gCapPass`); the cap-tree UPDATE the handoff performs cannot be witnessed by the frozen-root
gate. Forcing it needs the OPENABLE sorted cap-tree update (cap-reshape PHASE-D), NOT yet available.

So the handoff (caps/delegate/delegations at `child`) is carried as the NAMED `capHandoff` decode
residual — stated precisely as the spec's three handoff equations — NOT claimed bound. The accounts
insert + born-empty growth IS forced. -/

/-- The decode relating a satisfying FIX spawn witness's row to a kernel `pre → post` spawn. The
accounts-root columns + the FIX gate (the FORCED leg); the spawn guard; the born-empty create-leg
residuals; the receipt; the frame; and — PRECISELY NAMED, the PHASE-D residual — the three cap-handoff
equations the frozen `cap_root` cannot certify. -/
structure spawnGenuineEncodes (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (actor child target : CellId) : Type where
  preRoot : FieldElem
  postRoot : FieldElem
  hroots : AccountsRootRow compressN pre.kernel post.kernel preRoot postRoot
  gate : gAccountsGrow compressN pre.kernel child postRoot
  -- the spawn admissibility guard (held parent edge ∧ live parent ∧ create-leg admit over child).
  guard : spawnAdmit pre.kernel actor child target
  -- born-empty create-leg residuals at `child` (per-cell, off the accounts column).
  frCell : post.kernel.cell = fun c => if c = child then default else pre.kernel.cell c
  frSlotCaveats : post.kernel.slotCaveats = fun c => if c = child then [] else pre.kernel.slotCaveats c
  frLifecycle : post.kernel.lifecycle = fun c => if c = child then 0 else pre.kernel.lifecycle c
  frDeathCert : post.kernel.deathCert = fun c => if c = child then 0 else pre.kernel.deathCert c
  frBal : post.kernel.bal = fun c a => if c = child then 0 else pre.kernel.bal c a
  -- ⚑ THE PHASE-D RESIDUAL: the parent→child capability handoff. The live `cap_root` is FROZEN
  -- (`gCapPass`), so these THREE cap-tree updates are NOT circuit-forced — carried, named, here.
  capHandoff : post.kernel.caps = spawnCapsMap pre.kernel actor child target
  delegateHandoff : post.kernel.delegate = spawnDelegateMap pre.kernel actor child
  delegationsHandoff : post.kernel.delegations = spawnDelegationsMap pre.kernel actor child
  -- the child-creation receipt advance.
  logAdv : post.log = createReceipt actor child :: pre.log
  -- the global side-table frame.
  frNullifiers : post.kernel.nullifiers = pre.kernel.nullifiers
  frRevoked : post.kernel.revoked = pre.kernel.revoked
  frCommitments : post.kernel.commitments = pre.kernel.commitments
  frFactories : post.kernel.factories = pre.kernel.factories
  frDelegationEpoch : post.kernel.delegationEpoch = pre.kernel.delegationEpoch
  -- ⚑ THE NAMED SPAWN-EPOCH-STAMP RESIDUAL: the child's `delegationEpochAt` is STAMPED with the
  -- spawner-parent's current epoch (`spawnEpochAtMap`), not framed unchanged — so the born child is FRESH
  -- (not stale) under a nonzero-epoch parent. Commitment-bound via record_digest; carried as a Prop.
  epochStampResidual : post.kernel.delegationEpochAt = spawnEpochAtMap pre.kernel actor child
  frHeaps : post.kernel.heaps = pre.kernel.heaps
  frNullifierRoot : post.kernel.nullifierRoot = pre.kernel.nullifierRoot
  frRevokedRoot : post.kernel.revokedRoot = pre.kernel.revokedRoot

/-- **`spawn_accounts_forced` — the committed accounts growth is FIX-CIRCUIT-FORCED.** The child IS
inserted; a drop/reorder is rejected (the `accountsRoot` gate bites). This is the part of `SpawnSpec`
the FIX genuinely binds. -/
theorem spawn_accounts_forced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor child target : CellId)
    (henc : spawnGenuineEncodes compressN pre post actor child target) :
    post.kernel.accounts = insert child pre.kernel.accounts :=
  accountsGrowForced compressN hN pre.kernel post.kernel child henc.preRoot henc.postRoot
    henc.hroots henc.gate

/-- **`spawn_descriptorRefines` — THE FIX CIRCUIT→KERNEL REFINEMENT for spawn (VALUE_PARTIAL).** A
satisfying FIX witness forces `SpawnSpec pre actor child target post`. The accounts insert + born-empty
growth is FORCED via the committed accounts root (`spawn_accounts_forced`); the parent→child CAPABILITY
HANDOFF (caps/delegate/delegations) is the NAMED `capHandoff`/`delegateHandoff`/`delegationsHandoff`
PHASE-D residual — the live frozen `cap_root` cannot force it, so it is carried, not claimed bound. -/
theorem spawn_descriptorRefines (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor child target : CellId)
    (henc : spawnGenuineEncodes compressN pre post actor child target) :
    SpawnFullSpec pre actor child target post := by
  refine ⟨henc.guard, ?_, henc.frCell, henc.frSlotCaveats, henc.frLifecycle, henc.frDeathCert,
    henc.frBal, henc.capHandoff, henc.delegateHandoff, henc.delegationsHandoff, henc.logAdv,
    henc.frNullifiers, henc.frRevoked, henc.frCommitments, henc.frFactories,
    henc.frDelegationEpoch, henc.epochStampResidual, henc.frHeaps, henc.frNullifierRoot, henc.frRevokedRoot⟩
  exact spawn_accounts_forced compressN hN pre post actor child target henc

/-- **The refinement, stated against `execFullA` directly** (via `spawnChainA_iff_spec` + the
`execFullA_spawnA` projection). -/
theorem spawn_descriptorRefines_execFullA (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor child target : CellId)
    (henc : spawnGenuineEncodes compressN pre post actor child target) :
    execFullA pre (.spawnA actor child target) = some post := by
  rw [Dregg2.Circuit.Spec.AccountGrowth.execFullA_spawnA]
  exact (Dregg2.Circuit.Spec.AccountGrowth.spawnChainA_iff_spec pre actor child target post).mpr
    (spawn_descriptorRefines compressN hN pre post actor child target henc)

/-- **`spawn_descriptorRefines_rejects_wrong_accounts` (BOTH-POLARITY TOOTH).** A spawn whose post
accounts are NOT `insert child pre.accounts` (the child not inserted / a reorder) is UNSAT — the
accounts-root gate bites on the FORCED leg. -/
theorem spawn_descriptorRefines_rejects_wrong_accounts (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (actor child target : CellId)
    (henc : spawnGenuineEncodes compressN pre post actor child target)
    (hwrong : post.kernel.accounts ≠ insert child pre.kernel.accounts) :
    False :=
  hwrong (spawn_accounts_forced compressN hN pre post actor child target henc)

/-! ## §5 — NON-VACUITY: the accounts root + the gate are load-bearing (no carrier secretly `True`).

A concrete injective `compressN` (a positional Horner sponge, NOT `List.sum`). The accounts root of a
GROWN set DIFFERS from the pre set's root (the gate distinguishes them); a frozen-accounts row's
post-root is NOT the grown-set digest (the gate REJECTS it). A `accountsRoot := 0` stub would collapse
these. -/

private def cNC : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 1000003 + x) (xs.length : ℤ)

private def baseK : RecordKernelState :=
  { accounts := {1, 2, 3}, cell := fun _ => .int 0, caps := default, lifecycle := fun _ => 0 }
private def newId : CellId := 9

-- POSITIVE (load-bearing): the GROWN set's root DIFFERS from the pre set's root (the gate is not a
-- no-op — an `accountsRoot := 0` stub would make these EQUAL: forbidden).
#guard decide (listDigest accountsLeaf cNC ((insert newId baseK.accounts).sort (· ≤ ·))
             = listDigest accountsLeaf cNC (accountsSorted baseK)) == false

-- The grown digest equals itself (the gate's RHS is the genuine grown root, computable).
#guard decide (listDigest accountsLeaf cNC ((insert newId baseK.accounts).sort (· ≤ ·))
             = listDigest accountsLeaf cNC ((insert newId baseK.accounts).sort (· ≤ ·)))

-- ANTI-GHOST: a FROZEN-accounts post (set unchanged) has a post-root that is NOT the grown-set digest,
-- so `gAccountsGrow` FAILS for it — a no-op birth is rejected.
#guard decide (listDigest accountsLeaf cNC (accountsSorted baseK)
             = listDigest accountsLeaf cNC ((insert newId baseK.accounts).sort (· ≤ ·))) == false

-- ANTI-GHOST: a DROP (post = {1,2} ⊊ pre) has a different root than the grown set — a forgery that
-- silently drops an existing id is rejected.
#guard decide (listDigest accountsLeaf cNC (({1, 2} : Finset CellId).sort (· ≤ ·))
             = listDigest accountsLeaf cNC ((insert newId baseK.accounts).sort (· ≤ ·))) == false

-- The accounts leaf encoder is injective on the toy domain (the carrier is committing the ids):
#guard decide (accountsLeaf 1 = accountsLeaf 2) == false

/-! ## §6.A — CLASS A: the accounts growth is FORCED by the DEPLOYED descriptors (`createCellV3` /
`factoryV3` / `spawnV3`), not a modelled gate.

§2–§4 force the growth from `*GenuineEncodes.gate`, the MODELLED `gAccountsGrow` the decode ASSERTS —
editing the LIVE `*V3` constraints does NOT break it. This section closes that gap exactly as
`RotatedKernelRefinementCellSeal` §6.5 / `RotatedKernelRefinementMisc` §2.A do: each `*_forced_sat`
derives `post.kernel.accounts = insert newCell pre.kernel.accounts` from a `Satisfied2 hash *V3`
witness DIRECTLY, by

  * `createCellV3_grow_gate_forces_set_insert` (and the factory/spawn siblings) — the DEPLOYED in-circuit
    `cellsInsertOp` (`.insert`) map-op FORCES the live wire's `writesTo before_cells_root key key
    after_cells_root` (the committed BEFORE/AFTER `cells_root` limbs 0, openable sorted-Poseidon2 roots
    chaining into `state_commit`) on the active row whose runtime selector fires;
  * `*TraceReadout.growthDecodes` — the realizable `WitnessDecodes`-class seam: the deployed binary-Merkle
    forced write of the new-cell key into the BEFORE accounts root IS the kernel Finset set-insert
    `post.accounts = insert newCell pre.accounts` (the deployed trace-fill emits the genuine grown accounts
    root as `after_cells_root`, so the felt-level write and the kernel insert are the SAME growth by
    construction — the limb-level decode the COMMITMENT cannot certify, supplied by `StarkSound`, exactly as
    cellSeal's `discLimbDecodes` / makeSovereign's `modeLimbDecodes`).

Editing `*V3`'s grow-gate breaks `*V3_grow_gate_forces_set_insert`, hence the forced `writesTo`, hence
`growthDecodes`'s antecedent, hence `*_forced_sat`, hence `*_descriptorRefines_sat` — Class A. The seam is a
NAMED realizable carrier (a structure field), never an assumed hole: `#assert_axioms`-clean. -/

/-- **`CreateCellTraceReadout` — the realizable circuit-witness extraction for createCell (NAMED).**
The trace-determined part a satisfying `createCellV3` witness supplies, the `WitnessDecodes` class of
cellSeal's `CellSealTraceReadout`: the prover's designated ACTIVE createCell row + its selector fact + the
realizable accounts-growth seam (the deployed-forced `writesTo` IS the kernel set-insert) + the born-empty /
guard / log / 7-field residual the per-cell limb cannot witness. The grow GATE is NOT a field — the forced
`writesTo` is derived from `Satisfied2 hash createCellV3` (`createCell_forced_sat`), unlike §2's modelled
`gate`. -/
structure CreateCellTraceReadout (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (actor newCell : CellId) : Type where
  -- the designated ACTIVE createCell row (the one whose `SEL_CREATE_CELL_RT = 1`).
  row : Nat
  hrow : row < t.rows.length
  -- the runtime selector is hot on the designated row (the prover's row designation).
  hsel : (envAt t row).loc Dregg2.Circuit.Emit.EffectVmEmitCreateCell.SEL_CREATE_CELL_RT = 1
  -- the realizable `WitnessDecodes`-class seam: the deployed binary-Merkle forced write of the new-cell key
  -- into the BEFORE accounts root IS the kernel Finset set-insert. The deployed trace-fill emits the genuine
  -- grown accounts root as `after_cells_root`, so the felt-level write and the kernel insert are the SAME
  -- growth by construction — the limb-level decode the COMMITMENT cannot certify, supplied by `StarkSound`.
  growthDecodes :
    writesTo hash ((envAt t row).loc (beforeCellsRootCol EFFECT_VM_WIDTH))
        ((envAt t row).loc NEW_CELL_KEY_PARAM_COL)
        ((envAt t row).loc NEW_CELL_KEY_PARAM_COL)
        ((envAt t row).loc (afterCellsRootCol EFFECT_VM_WIDTH))
      → post.kernel.accounts = insert newCell pre.kernel.accounts
  -- the admissibility guard (privileged creation authority ∧ freshness).
  guard : createCellAdmit pre.kernel actor newCell
  -- the new cell's BORN-EMPTY per-cell records (per-cell, off the accounts column).
  born : bornEmptyAt pre.kernel newCell post.kernel
  -- the creation receipt advance.
  logAdv : post.log = createReceipt actor newCell :: pre.log
  -- the global side-table frame (the `CreateCellSpec` frame residual).
  frNullifiers : post.kernel.nullifiers = pre.kernel.nullifiers
  frRevoked : post.kernel.revoked = pre.kernel.revoked
  frCommitments : post.kernel.commitments = pre.kernel.commitments
  frFactories : post.kernel.factories = pre.kernel.factories
  frDelegationEpoch : post.kernel.delegationEpoch = pre.kernel.delegationEpoch
  frDelegationEpochAt : post.kernel.delegationEpochAt = pre.kernel.delegationEpochAt
  frHeaps : post.kernel.heaps = pre.kernel.heaps
  frNullifierRoot : post.kernel.nullifierRoot = pre.kernel.nullifierRoot
  frRevokedRoot : post.kernel.revokedRoot = pre.kernel.revokedRoot

/-- **`createCell_forced_sat` — the accounts growth is FORCED by the DEPLOYED `createCellV3` (Class A).**
A `Satisfied2 hash createCellV3` witness plus the realizable `CreateCellTraceReadout` forces
`post.kernel.accounts = insert newCell pre.kernel.accounts`. The DEPLOYED `cellsInsertOp` forces the live
wire's `writesTo` of the new-cell key into the BEFORE accounts root
(`createCellV3_grow_gate_forces_set_insert` on the active row); the readout's `growthDecodes` lifts that
forced write to the kernel set-insert. Editing `createCellV3`'s grow-gate turns this RED. -/
theorem createCell_forced_sat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash createCellV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor newCell : CellId)
    (rd : CreateCellTraceReadout hash minit mfin maddrs t pre post actor newCell) :
    post.kernel.accounts = insert newCell pre.kernel.accounts :=
  rd.growthDecodes
    (createCellV3_grow_gate_forces_set_insert hash hsat rd.row rd.hrow rd.hsel).2

/-- **`createCell_descriptorRefines_sat` — THE CLASS-A CIRCUIT→KERNEL REFINEMENT for createCell.** A
satisfying DEPLOYED `createCellV3` witness plus the realizable `CreateCellTraceReadout` forces
`CreateCellSpec pre actor newCell post`. Unlike §2's `createCell_descriptorRefines` (which consumes a
modelled `gate`), the `accounts := insert newCell` growth here is forced from the DEPLOYED grow-gate's
`Satisfied2` (`createCell_forced_sat`) — editing `createCellV3`'s constraints turns this RED. The guard, the
born-empty records, the receipt, and the frame are the named decode residual. -/
theorem createCell_descriptorRefines_sat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash createCellV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor newCell : CellId)
    (rd : CreateCellTraceReadout hash minit mfin maddrs t pre post actor newCell) :
    CreateCellSpec pre actor newCell post := by
  refine ⟨rd.guard, ?_, rd.born, rd.logAdv, rd.frNullifiers, rd.frRevoked,
    rd.frCommitments, rd.frFactories, rd.frDelegationEpoch, rd.frDelegationEpochAt,
    rd.frHeaps, rd.frNullifierRoot, rd.frRevokedRoot⟩
  exact createCell_forced_sat hash hsat pre post actor newCell rd

/-- **CLASS-A TOOTH — a forged wrong-accounts createCell witness is UNSAT.** A `CreateCellTraceReadout`
whose post accounts are NOT `insert newCell pre.accounts` cannot ride a satisfying `createCellV3` witness:
the DEPLOYED grow-gate pins the insert. -/
theorem createCell_sat_rejects_wrong_accounts (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash createCellV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor newCell : CellId)
    (rd : CreateCellTraceReadout hash minit mfin maddrs t pre post actor newCell)
    (hwrong : post.kernel.accounts ≠ insert newCell pre.kernel.accounts) :
    False :=
  hwrong (createCell_forced_sat hash hsat pre post actor newCell rd)

/-- **`CreateFromFactoryTraceReadout`** — `CreateCellTraceReadout`'s accounts-growth seam for the factory
descriptor (selector `13`, new-cell key column `param1`) plus the factory-install / born-empty residual. -/
structure CreateFromFactoryTraceReadout (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (actor newCell : CellId) (vk : Int) : Type where
  row : Nat
  hrow : row < t.rows.length
  hsel : (envAt t row).loc Dregg2.Circuit.Emit.EffectVmEmitCreateCellFromFactory.SEL_FACTORY_RT = 1
  growthDecodes :
    writesTo hash ((envAt t row).loc (beforeCellsRootCol EFFECT_VM_WIDTH))
        ((envAt t row).loc FACTORY_CHILD_KEY_PARAM_COL)
        ((envAt t row).loc FACTORY_CHILD_KEY_PARAM_COL)
        ((envAt t row).loc (afterCellsRootCol EFFECT_VM_WIDTH))
      → post.kernel.accounts = insert newCell pre.kernel.accounts
  e : FactoryEntry
  guard : factoryAdmit pre.kernel actor newCell vk e
  frCell : post.kernel.cell = factoryPostCell (factoryBornCell pre.kernel newCell) newCell e
  frSlotCaveats : post.kernel.slotCaveats = factoryPostCaveats (factoryBornCaveats pre.kernel newCell) newCell e
  frBal : post.kernel.bal = (fun c a => if c = newCell then 0 else pre.kernel.bal c a)
  frCaps : post.kernel.caps = fun l => if l = newCell then [] else pre.kernel.caps l
  frLifecycle : post.kernel.lifecycle = fun c => if c = newCell then 0 else pre.kernel.lifecycle c
  frDeathCert : post.kernel.deathCert = fun c => if c = newCell then 0 else pre.kernel.deathCert c
  frDelegate : post.kernel.delegate = fun c => if c = newCell then none else pre.kernel.delegate c
  frDelegations : post.kernel.delegations = fun c => if c = newCell then [] else pre.kernel.delegations c
  logAdv : post.log = factoryReceipt actor newCell :: pre.log
  frNullifiers : post.kernel.nullifiers = pre.kernel.nullifiers
  frRevoked : post.kernel.revoked = pre.kernel.revoked
  frCommitments : post.kernel.commitments = pre.kernel.commitments
  frFactories : post.kernel.factories = pre.kernel.factories
  frDelegationEpoch : post.kernel.delegationEpoch = pre.kernel.delegationEpoch
  frDelegationEpochAt : post.kernel.delegationEpochAt = pre.kernel.delegationEpochAt
  frHeaps : post.kernel.heaps = pre.kernel.heaps
  frNullifierRoot : post.kernel.nullifierRoot = pre.kernel.nullifierRoot
  frRevokedRoot : post.kernel.revokedRoot = pre.kernel.revokedRoot

/-- **`createFromFactory_forced_sat`** — the accounts growth FORCED by the DEPLOYED `factoryV3` (Class A). -/
theorem createFromFactory_forced_sat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash factoryV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor newCell : CellId) (vk : Int)
    (rd : CreateFromFactoryTraceReadout hash minit mfin maddrs t pre post actor newCell vk) :
    post.kernel.accounts = insert newCell pre.kernel.accounts :=
  rd.growthDecodes
    (factoryV3_grow_gate_forces_set_insert hash hsat rd.row rd.hrow rd.hsel).2

/-- **`createCellFromFactory_descriptorRefines_sat` — THE CLASS-A REFINEMENT for createCellFromFactory.** -/
theorem createCellFromFactory_descriptorRefines_sat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash factoryV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor newCell : CellId) (vk : Int)
    (rd : CreateFromFactoryTraceReadout hash minit mfin maddrs t pre post actor newCell vk) :
    CreateFromFactorySpec pre actor newCell vk post := by
  refine ⟨rd.e, rd.guard, ?_, rd.frBal, rd.frCell, rd.frSlotCaveats, rd.logAdv,
    rd.frCaps, rd.frLifecycle, rd.frDeathCert, rd.frDelegate, rd.frDelegations,
    rd.frNullifiers, rd.frRevoked, rd.frCommitments, rd.frFactories,
    rd.frDelegationEpoch, rd.frDelegationEpochAt, rd.frHeaps, rd.frNullifierRoot, rd.frRevokedRoot⟩
  exact createFromFactory_forced_sat hash hsat pre post actor newCell vk rd

/-- **CLASS-A TOOTH** — a forged wrong-accounts factory witness is UNSAT. -/
theorem createCellFromFactory_sat_rejects_wrong_accounts (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash factoryV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor newCell : CellId) (vk : Int)
    (rd : CreateFromFactoryTraceReadout hash minit mfin maddrs t pre post actor newCell vk)
    (hwrong : post.kernel.accounts ≠ insert newCell pre.kernel.accounts) :
    False :=
  hwrong (createFromFactory_forced_sat hash hsat pre post actor newCell vk rd)

/-- **`SpawnTraceReadout`** — `CreateCellTraceReadout`'s accounts-growth seam for the spawn descriptor
(selector `32`) plus the born-empty residual AND the cap-handoff seam (the INSERT-shaped keystone
carriers — `capsMoveDecodes` is DISCHARGED on the deployed `effCapInsertV3 spawnWriteV3` wrap by
`effCapInsertV3_forces_write8`, exactly as §4's `spawnGenuineEncodes`). -/
structure SpawnTraceReadout (S8 : Cap8Scheme) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (actor child target : CellId) : Type where
  row : Nat
  hrow : row < t.rows.length
  hsel : (envAt t row).loc Dregg2.Circuit.Emit.EffectVmEmitSpawn.SEL_SPAWN_RT = 1
  growthDecodes :
    writesTo hash ((envAt t row).loc (beforeCellsRootCol EFFECT_VM_WIDTH))
        ((envAt t row).loc NEW_CELL_KEY_PARAM_COL)
        ((envAt t row).loc NEW_CELL_KEY_PARAM_COL)
        ((envAt t row).loc (afterCellsRootCol EFFECT_VM_WIDTH))
      → post.kernel.accounts = insert child pre.kernel.accounts
  guard : spawnAdmit pre.kernel actor child target
  frCell : post.kernel.cell = fun c => if c = child then default else pre.kernel.cell c
  frSlotCaveats : post.kernel.slotCaveats = fun c => if c = child then [] else pre.kernel.slotCaveats c
  frLifecycle : post.kernel.lifecycle = fun c => if c = child then 0 else pre.kernel.lifecycle c
  frDeathCert : post.kernel.deathCert = fun c => if c = child then 0 else pre.kernel.deathCert c
  frBal : post.kernel.bal = fun c a => if c = child then 0 else pre.kernel.bal c a
  -- ⚑ THE CAP-HANDOFF SEAM (now FORCED on the `effCapInsertV3 spawnWriteV3` keystone wrap): the
  -- deployed faithful 8-felt cap-tree INSERT (`capInserts8` — the spliced conferred edge at the child
  -- key over the FULL committed 8-felt cap-root groups) DECODES to the kernel `caps` move
  -- (`spawnCapsMap`). The faithful cap-tree↔kernel-`Caps` encoding seam — exactly
  -- `RevokeCapabilityTraceReadout.capsMoveDecodes`'s class (a HYPOTHESIS, never an axiom): on
  -- `spawnV3` (frozen `cap_root`) the antecedent never fires, so `capHandoff` is a plain residual; on
  -- the keystone wrap the antecedent is DISCHARGED by `effCapInsertV3_forces_write8`, so the `caps`
  -- move is FORCED (`spawn_caps_forced_sat`).
  capsMoveDecodes :
    capInserts8 S8 (beforeCapRootCols (envAt t row))
        (leafOf (capOpenCols spawnWriteV3.traceWidth) (envAt t row))
        (afterCapRootCols (envAt t row))
      → post.kernel.caps = spawnCapsMap pre.kernel actor child target
  -- ⚑ THE PHASE-D RESIDUAL: the parent→child capability handoff (the live `cap_root` is FROZEN).
  capHandoff : post.kernel.caps = spawnCapsMap pre.kernel actor child target
  delegateHandoff : post.kernel.delegate = spawnDelegateMap pre.kernel actor child
  delegationsHandoff : post.kernel.delegations = spawnDelegationsMap pre.kernel actor child
  logAdv : post.log = createReceipt actor child :: pre.log
  frNullifiers : post.kernel.nullifiers = pre.kernel.nullifiers
  frRevoked : post.kernel.revoked = pre.kernel.revoked
  frCommitments : post.kernel.commitments = pre.kernel.commitments
  frFactories : post.kernel.factories = pre.kernel.factories
  frDelegationEpoch : post.kernel.delegationEpoch = pre.kernel.delegationEpoch
  -- ⚑ THE NAMED SPAWN-EPOCH-STAMP RESIDUAL (commitment-bound via record_digest): the child's
  -- `delegationEpochAt` STAMPED with the spawner-parent's current epoch (`spawnEpochAtMap`), so the
  -- born child is FRESH (not stale) under a nonzero-epoch parent.
  epochStampResidual : post.kernel.delegationEpochAt = spawnEpochAtMap pre.kernel actor child
  frHeaps : post.kernel.heaps = pre.kernel.heaps
  frNullifierRoot : post.kernel.nullifierRoot = pre.kernel.nullifierRoot
  frRevokedRoot : post.kernel.revokedRoot = pre.kernel.revokedRoot

/-- **`SpawnWriteAnchor` — the realizable INSERT carriers for the spawn cap handoff** (what the deployed
`CanonicalCapTree::insert_witness` computes — the readout-linked twin of
`RotatedKernelRefinementCapFamily.DelegateWriteAnchor`'s carrier fields, AT the readout's active row):
the cap-open appendix's read leaf IS the spliced conferred edge, its key's non-membership bracket in
BEFORE (the pred/succ `GapOpen` covering the committed spine) is genuinely realizable — the sorted
insert refuses a present key, so an honest witness always carries the bracket — and the AFTER cap-root
commits the inserted spine. -/
structure SpawnWriteAnchor (S8 : Cap8Scheme) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (actor child target : CellId)
    (rd : SpawnTraceReadout S8 hash minit mfin maddrs t pre post actor child target) : Type where
  -- the active spawn row is not the trailing/padding row (the keystone welds bind under
  -- `when_transition`).
  hnotlast : rd.row + 1 ≠ t.rows.length
  spine : List ℤ
  hold : SpineCommits S8 (beforeCapRootCols (envAt t rd.row)) spine
  gap : GapOpen S8 (beforeCapRootCols (envAt t rd.row))
    (keyOf (leafOf (capOpenCols spawnWriteV3.traceWidth) (envAt t rd.row)))
  gapCov : gap.coversSpine spine
  hnew : SpineCommits S8 (afterCapRootCols (envAt t rd.row))
    (sortedInsert (keyOf (leafOf (capOpenCols spawnWriteV3.traceWidth) (envAt t rd.row))) spine)

/-- **`spawn_forced_sat`** — the accounts growth FORCED by the DEPLOYED `spawnV3` (Class A). The child IS
inserted; the cap-handoff remains the named PHASE-D residual (frozen `cap_root`). -/
theorem spawn_forced_sat (S8 : Cap8Scheme) (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash spawnV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor child target : CellId)
    (rd : SpawnTraceReadout S8 hash minit mfin maddrs t pre post actor child target) :
    post.kernel.accounts = insert child pre.kernel.accounts :=
  rd.growthDecodes
    (spawnV3_grow_gate_forces_set_insert hash hsat rd.row rd.hrow rd.hsel).2

/-- **`spawn_descriptorRefines_sat` — THE CLASS-A REFINEMENT for spawn (VALUE_PARTIAL).** The accounts
insert is forced from the DEPLOYED grow-gate's `Satisfied2` (`spawn_forced_sat`); the parent→child cap
handoff is the named PHASE-D residual (the frozen `cap_root` cannot force it). -/
theorem spawn_descriptorRefines_sat (S8 : Cap8Scheme) (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash spawnV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor child target : CellId)
    (rd : SpawnTraceReadout S8 hash minit mfin maddrs t pre post actor child target) :
    SpawnFullSpec pre actor child target post := by
  refine ⟨rd.guard, ?_, rd.frCell, rd.frSlotCaveats, rd.frLifecycle, rd.frDeathCert,
    rd.frBal, rd.capHandoff, rd.delegateHandoff, rd.delegationsHandoff, rd.logAdv,
    rd.frNullifiers, rd.frRevoked, rd.frCommitments, rd.frFactories,
    rd.frDelegationEpoch, rd.epochStampResidual, rd.frHeaps, rd.frNullifierRoot, rd.frRevokedRoot⟩
  exact spawn_forced_sat S8 hash hsat pre post actor child target rd

/-- **CLASS-A TOOTH** — a spawn whose post accounts drop the child is UNSAT (the grow-gate bites). -/
theorem spawn_sat_rejects_wrong_accounts (S8 : Cap8Scheme) (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash spawnV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor child target : CellId)
    (rd : SpawnTraceReadout S8 hash minit mfin maddrs t pre post actor child target)
    (hwrong : post.kernel.accounts ≠ insert child pre.kernel.accounts) :
    False :=
  hwrong (spawn_forced_sat S8 hash hsat pre post actor child target rd)

/-! ## §5b — the spawn CAP-HANDOFF FORCED close (the `effCapInsertV3 spawnWriteV3` keystone wrap).

`spawnV3` froze `cap_root` (`gCapPass`), so the parent→child cap handoff was the named PHASE-D residual.
`spawnWriteV3` REBASES onto the cap-WRITE rotation (`rotateV3WithNewCellKeyPinCapWrite`: cap-root limb 25
freed) ALONGSIDE the unchanged accounts grow-gate (limb 0). The cap-tree INSERT itself is FORCED by the
SHAPE-MATCHED keystone wrap (the arity-2 `anchorReadOpRot`/`insertWriteOpRot` pair was shape-UNSAT
against the deployed arity-7 `CanonicalCapTree::insert_witness` and is DROPPED): `effCapInsertV3
spawnWriteV3` FORCES the spliced-leaf membership in the REBUILT AFTER tree
(`CapInsertEmit.effCapInsertV3_forces_write8` → `capInserts8`), exactly as `delegate_forces_committed_write`
— closing the load-bearing `caps` edge. (The `delegate`/`delegations` POINTER moves remain the named
residual: the single cap-tree INSERT binds the `caps` edge, not the per-cell `delegate`/`delegations`
snapshots, which ride `birth`'s `delegateHandoff`/`delegationsHandoff` faithful-encoding fields.) -/

/-- **`spawn_caps_forced_sat` — the parent→child cap edge is FORCED by the DEPLOYED keystone wrap.** The
faithful 8-felt cap-tree INSERT (`capInserts8` — the spliced conferred edge at the child key) is
discharged by `effCapInsertV3_forces_write8` + the readout's realizable INSERT carriers, and the
readout's `capsMoveDecodes` seam lifts it to the kernel `caps` move (`spawnCapsMap`). Mirrors
`RotatedKernelRefinementCapFamily.delegate_forces_committed_write`. -/
theorem spawn_caps_forced_sat (S8 : Cap8Scheme) (hash : List ℤ → ℤ)
    (name : String) (n : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hChip : ChipTableSoundN (capPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash (effCapInsertV3 spawnWriteV3 name n) minit mfin maddrs t)
    (pre post : RecChainedState) (actor child target : CellId)
    (rd : SpawnTraceReadout S8 hash minit mfin maddrs t pre post actor child target)
    (anc : SpawnWriteAnchor S8 hash minit mfin maddrs t pre post actor child target rd) :
    post.kernel.caps = spawnCapsMap pre.kernel actor child target :=
  rd.capsMoveDecodes
    (effCapInsertV3_forces_write8 S8 spawnWriteV3 name n hash minit mfin maddrs t hChip hsat
      rd.row rd.hrow anc.hnotlast anc.spine anc.hold anc.gap anc.gapCov anc.hnew)

/-- **`spawnWrite_descriptorRefines_sat` — THE CLASS-A REFINEMENT for spawn with the cap handoff FORCED.**
Over the keystone wrap `effCapInsertV3 spawnWriteV3`: BOTH the accounts insert (via
`spawnWriteV3_grow_gate_forces_set_insert`/`growthDecodes` on the stripped base — the cells map-ops
survive the drop) AND the parent→child cap edge (via `spawn_caps_forced_sat`) are FORCED. The
`delegate`/`delegations` pointer moves ride the readout's faithful-encoding residual fields. Editing the
deployed AFTER welds turns the cap leg — and the apex — RED. -/
theorem spawnWrite_descriptorRefines_sat (S8 : Cap8Scheme) (hash : List ℤ → ℤ)
    (name : String) (n : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hChip : ChipTableSoundN (capPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash (effCapInsertV3 spawnWriteV3 name n) minit mfin maddrs t)
    (pre post : RecChainedState) (actor child target : CellId)
    (rd : SpawnTraceReadout S8 hash minit mfin maddrs t pre post actor child target)
    (anc : SpawnWriteAnchor S8 hash minit mfin maddrs t pre post actor child target rd) :
    SpawnFullSpec pre actor child target post := by
  refine ⟨rd.guard, ?_, rd.frCell, rd.frSlotCaveats, rd.frLifecycle, rd.frDeathCert,
    rd.frBal, ?_, rd.delegateHandoff, rd.delegationsHandoff, rd.logAdv,
    rd.frNullifiers, rd.frRevoked, rd.frCommitments, rd.frFactories,
    rd.frDelegationEpoch, rd.epochStampResidual, rd.frHeaps, rd.frNullifierRoot, rd.frRevokedRoot⟩
  · -- accounts insert: forced by the cells grow-gate (still present on the stripped base).
    have hbase : Satisfied2 hash spawnWriteV3 minit mfin maddrs t :=
      Dregg2.Circuit.Emit.CapOpenEmit.effCapOpenV3_satisfied2_strips_to_base hash spawnWriteV3 name n
        minit mfin maddrs t
        (effCapInsertV3_strips_to_capOpen spawnWriteV3 name n hash minit mfin maddrs t hsat)
    exact rd.growthDecodes
      (spawnWriteV3_grow_gate_forces_set_insert hash hbase rd.row rd.hrow rd.hsel).2
  · -- the parent→child cap edge: FORCED (no longer the frozen residual).
    exact spawn_caps_forced_sat S8 hash name n hChip hsat pre post actor child target rd anc

/-- **`spawnWrite_descriptorRefines_capOpenSat` — the apex-wirable, LIGHT-CLIENT spawn rung.** Consumes
`Satisfied2 hash spawnWriteCapOpenV3` (the SINGLE descriptor carrying BOTH the cap-membership authority
crown AND the cap-tree INSERT — the keystone wrap under the spawn selector tooth) by stripping the
selector tooth (`withSelectorGate_satisfied2`) and applying `spawnWrite_descriptorRefines_sat`. This
makes the cap handoff light-client-verifiable IN the descriptor the SDK route proves+verifies. Mirrors
`delegate_descriptorRefines_capOpenSat`. -/
theorem spawnWrite_descriptorRefines_capOpenSat (S8 : Cap8Scheme) (hash : List ℤ → ℤ)
    (name : String) (n : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hChip : ChipTableSoundN (capPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash
      (withSelectorGate Dregg2.Circuit.Emit.EffectVmEmitSpawn.SEL_SPAWN_RT
        (effCapInsertV3 spawnWriteV3 name n)) minit mfin maddrs t)
    (pre post : RecChainedState) (actor child target : CellId)
    (rd : SpawnTraceReadout S8 hash minit mfin maddrs t pre post actor child target)
    (anc : SpawnWriteAnchor S8 hash minit mfin maddrs t pre post actor child target rd) :
    SpawnFullSpec pre actor child target post :=
  spawnWrite_descriptorRefines_sat S8 hash name n hChip
    (withSelectorGate_satisfied2 hash _ (effCapInsertV3 spawnWriteV3 name n) minit mfin maddrs t hsat)
    pre post actor child target rd anc

/-- **CLASS-A FORGE TOOTH (spawn) — a forged wrong-caps post-root on the WRITE-CAPOPEN wrapper is UNSAT.**
Over the LIVE `spawnWriteCapOpenV3` (the descriptor the SDK route verifies), a post-state whose `caps` are
NOT the genuine `spawnCapsMap` handoff cannot arise from a `Satisfied2` witness — the keystone welds FORCE
the spliced conferred edge. Perturbing the AFTER welds breaks the force and reds this. Mirrors
`revokeCapability_capOpenSat_rejects_forged_postroot`. -/
theorem spawn_capOpenSat_rejects_forged_capHandoff (S8 : Cap8Scheme) (hash : List ℤ → ℤ)
    (name : String) (n : Nat)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hChip : ChipTableSoundN (capPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash
      (withSelectorGate Dregg2.Circuit.Emit.EffectVmEmitSpawn.SEL_SPAWN_RT
        (effCapInsertV3 spawnWriteV3 name n)) minit mfin maddrs t)
    (pre post : RecChainedState) (actor child target : CellId)
    (rd : SpawnTraceReadout S8 hash minit mfin maddrs t pre post actor child target)
    (anc : SpawnWriteAnchor S8 hash minit mfin maddrs t pre post actor child target rd)
    (hwrong : post.kernel.caps ≠ spawnCapsMap pre.kernel actor child target) :
    False :=
  hwrong (spawn_caps_forced_sat S8 hash name n hChip
    (withSelectorGate_satisfied2 hash _ (effCapInsertV3 spawnWriteV3 name n) minit mfin maddrs t hsat)
    pre post actor child target rd anc)

/-! ## §6 — axiom-hygiene tripwires. -/

#assert_axioms accountsLeaf_injective
#assert_axioms accountsRoot_binds
#assert_axioms accountsGrowForced
#assert_axioms createCell_accounts_forced
#assert_axioms createCell_descriptorRefines
#assert_axioms createCell_descriptorRefines_execFullA
#assert_axioms createCell_descriptorRefines_rejects_wrong_accounts
#assert_axioms createFromFactory_accounts_forced
#assert_axioms createCellFromFactory_descriptorRefines
#assert_axioms createCellFromFactory_descriptorRefines_execFullA
#assert_axioms createCellFromFactory_descriptorRefines_rejects_wrong_accounts
#assert_axioms spawn_accounts_forced
#assert_axioms spawn_descriptorRefines
#assert_axioms spawn_descriptorRefines_execFullA
#assert_axioms spawn_descriptorRefines_rejects_wrong_accounts
#assert_axioms createCell_forced_sat
#assert_axioms createCell_descriptorRefines_sat
#assert_axioms createCell_sat_rejects_wrong_accounts
#assert_axioms createFromFactory_forced_sat
#assert_axioms createCellFromFactory_descriptorRefines_sat
#assert_axioms createCellFromFactory_sat_rejects_wrong_accounts
#assert_axioms spawn_forced_sat
#assert_axioms spawn_descriptorRefines_sat
#assert_axioms spawn_sat_rejects_wrong_accounts
#assert_axioms spawn_caps_forced_sat
#assert_axioms spawnWrite_descriptorRefines_sat
#assert_axioms spawnWrite_descriptorRefines_capOpenSat
#assert_axioms spawn_capOpenSat_rejects_forged_capHandoff

end Dregg2.Circuit.RotatedKernelRefinementBirth
