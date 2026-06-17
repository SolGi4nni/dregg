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

## spawn — HONEST scope: the cap handoff is the NAMED phase-D residual, NOT forced

`SpawnSpec`'s load-bearing content is BOTH the accounts insert (forced here, via `accountsRoot`) AND
the parent→child CAPABILITY HANDOFF: `caps := spawnCapsMap`, `delegate := spawnDelegateMap`,
`delegations := spawnDelegationsMap` — writes into the per-cell capability side-tables. The live
descriptor pins `cap_root` FROZEN (`gCapPass`); the handoff is an UPDATE to that committed cap-tree
that the FROZEN-root gate structurally cannot witness. Forcing it requires the OPENABLE sorted cap-tree
update (cap-reshape PHASE-D), which is NOT yet available. So `spawn` is **VALUE_PARTIAL**: the accounts
insert + born-empty growth is FORCED via `accountsRoot`; the cap handoff (+ the `delegate`/`delegations`
moves) is carried as the NAMED decode residual `capHandoff` — stated precisely, NOT laundered as bound.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} + the realizable Poseidon-CR carrier
(`compressNInjective` + the injective `accountsLeaf`, the SAME carrier `AccountsCommit`/`ListCommit`
use). No `sorry`, no `:= True`, no `native_decide`, no fresh axiom. NEW file; all imports read-only.
-/
import Dregg2.Circuit.RotatedKernelRefinementMisc
import Dregg2.Circuit.AccountsCommit
import Dregg2.Circuit.Spec.accountgrowth
import Dregg2.Circuit.Spec.factorycreation

namespace Dregg2.Circuit.RotatedKernelRefinementBirth

open Dregg2.Circuit
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.StateCommit (compressNInjective)
open Dregg2.Circuit.AccountsCommit (accountsSorted accounts_eq_of_sorted_eq accountsSorted_eq_of_eq)
open Dregg2.Circuit.Spec.AccountGrowth
  (CreateCellSpec createCellAdmit createReceipt bornEmptyAt
   SpawnSpec spawnAdmit spawnCapsMap spawnDelegateMap spawnDelegationsMap
   execCreateCellA_iff_spec)
open Dregg2.Circuit.Spec.FactoryCreation
  (CreateFromFactorySpec factoryAdmit factoryReceipt factoryPostCell factoryPostCaveats
   factoryBornCell factoryBornCaveats)
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
    henc.frHeaps⟩
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
    henc.frDelegationEpoch, henc.frDelegationEpochAt, henc.frHeaps⟩
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
  frDelegationEpochAt : post.kernel.delegationEpochAt = pre.kernel.delegationEpochAt
  frHeaps : post.kernel.heaps = pre.kernel.heaps

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
    SpawnSpec pre actor child target post := by
  refine ⟨henc.guard, ?_, henc.frCell, henc.frSlotCaveats, henc.frLifecycle, henc.frDeathCert,
    henc.frBal, henc.capHandoff, henc.delegateHandoff, henc.delegationsHandoff, henc.logAdv,
    henc.frNullifiers, henc.frRevoked, henc.frCommitments, henc.frFactories,
    henc.frDelegationEpoch, henc.frDelegationEpochAt, henc.frHeaps⟩
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

end Dregg2.Circuit.RotatedKernelRefinementBirth
