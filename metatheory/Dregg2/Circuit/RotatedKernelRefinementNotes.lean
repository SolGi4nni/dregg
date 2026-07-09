/-
# Dregg2.Circuit.RotatedKernelRefinementNotes — the PRINCIPLED-FIX VALUE-leg circuit→kernel
  refinements for the NOTE family, fanning out the committed-list-root template
  (`RotatedKernelRefinementBirth`'s `accountsRoot`, `ListCommit.listDigest`) to the two
  shielded-set GROWTH effects:

  * **noteSpend**   — `nullifiers := nf :: nullifiers` (the spent-note nullifier set-insert), under a
    DOUBLE-SPEND freshness gate (`nf ∉ pre.nullifiers`), balance FROZEN.
  * **noteCreate**  — `commitments := cm :: commitments` (the note-commitment set-insert), no guard,
    balance FROZEN.

## The gap each closes (the same class as Birth's missing accounts column)

The load-bearing move of every note effect is the GROWTH of a tracked SHIELDED set:
`nullifiers := nf :: nullifiers` (spend) / `commitments := cm :: commitments` (create), with the
per-asset `bal` ledger FROZEN (note effects move SETS, never value — they are balance-neutral). The
deployed circuit's per-cell commitment `hash(bal_lo,bal_hi,nonce,fields[0..7],cap_root)`
(`cell_state.rs::compute_commitment`) is PER EXISTING CELL — it binds NO column for the `nullifiers`
SET nor the `commitments` SET. So a `*_descriptorRefines` against the DEPLOYED descriptor cannot tell
whether the note's nullifier/commitment was actually inserted (a prover could publish a commitment that
silently drops/reorders the shielded index). Worse, a PRIOR audit found the live note descriptor forces
a TRANSPARENT bal CREDIT that DIVERGES from the frozen-bal spec — so this is a genuine FIX, not a
live-realize. This is the SAME class as Birth's account-growth: the kernel datum (`nullifiers : List
Nat` / `commitments : List Nat`) has no committed home in the deployed shape.

## The binding mechanism (chosen: dedicated committed `nullifiersRoot` / `commitmentsRoot` limbs)

`nullifiers`/`commitments` are ALREADY ordered `List Nat`, so their committed root is the
`ListCommit.listDigest` over the list DIRECTLY (no Finset/sort step — simpler than Birth's accounts
root). The FIX gate forces the POST root to the digest of `nf :: pre.nullifiers` (spend) /
`cm :: pre.commitments` (create), binding via the realizable `compressNInjective` Poseidon-CR carrier +
the injective `Nat → ℤ` leaf (`ListDigestBindsList`). A drop/reorder is REJECTED (the digest pins the
WHOLE ordered post-list). Absorbed as ONE more committed limb each — exactly Birth's `accountsRoot`.

> ADDITIVITY NOTE. Same as Birth: NOT a `N_SYSTEM_ROOTS`+1 index. Each note root is its OWN dedicated
> committed limb, reusing the `ListCommit` carrier already proven. The Rust realization:
> `compute_commitment` absorbs a `nullifiers_root` limb and a `commitments_root` limb, and the note
> trace-fills emit the grown-list root. ONE VK epoch rotation, shared across the note family.

## noteSpend — HONEST scope: the SET-INSERT is FORCED; the FRESHNESS non-membership is CARRIED

`NoteSpendSpec`'s guard is `spendProof = true ∧ nf ∉ pre.nullifiers` (the no-double-spend gate). The
committed `nullifiersRoot` FORCES the set-insert `post.nullifiers = nf :: pre.nullifiers` — but it does
NOT, by itself, force `nf ∉ pre.nullifiers`: the root binds the list VALUE, and a list may carry a
repeated head, so non-membership of the committed pre-list is not derivable from the root alone. Forcing
it in-circuit needs a sorted-set NON-MEMBERSHIP OPEN (the same sorted cap-tree open cap-reshape PHASE-D
supplies), which is NOT yet available. So `noteSpend` is **VALUE_PARTIAL**: the set-insert is FORCED via
`nullifiersRoot`; the freshness `nf ∉ pre.nullifiers` AND the `spendProof = true` proof gate are carried
as the NAMED `freshness`/`proof` decode residuals — stated precisely, NOT laundered as bound. (The
both-polarity tooth `…_rejects_double` is still genuine: GIVEN the carried freshness, a `nf ∈
pre.nullifiers` witness is contradictory — the freshness residual BITES.)

## noteCreate — PROVEN-FIX: the set-insert is FORCED (no guard to carry)

`NoteCreateASpec` has NO guard (append-only; `noteCreateAdmit = True`). So the committed
`commitmentsRoot` FORCES the WHOLE load-bearing content: `post.commitments = cm :: pre.commitments`.
The receipt and the global frame are the named decode residual; there is no freshness/authority to
carry. A wrong/duplicate-misplaced commitment insert is REJECTED (the root gate bites).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} + the realizable Poseidon-CR carrier
(`compressNInjective` + the injective `noteLeaf`, the SAME carrier `ListCommit` uses). NEW file; all imports read-only.
-/
import Dregg2.Circuit.RotatedKernelRefinementMisc
import Dregg2.Circuit.ListCommit
import Dregg2.Circuit.Spec.notenullifier
import Dregg2.Circuit.Spec.notecommitment

namespace Dregg2.Circuit.RotatedKernelRefinementNotes

open Dregg2.Circuit
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.StateCommit (compressNInjective)
open Dregg2.Circuit.Spec.NoteNullifier
  (NoteSpendSpec noteSpendGuard noteSpendReceipt execFullA_noteSpend_iff_spec)
open Dregg2.Circuit.Spec.NoteCommitment
  (NoteCreateASpec noteCreateAdmit noteCreateReceipt execNoteCreateA_iff_spec)
open Dregg2.Circuit.DescriptorIR2 (VmTrace Satisfied2 envAt opensTo writesTo)
open Dregg2.Circuit.Emit.EffectVmEmit (prmCol EFFECT_VM_WIDTH)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
  (noteSpendV3 noteCreateV3
   noteSpendV3_grow_gate_forces_set_insert noteCreateV3_grow_gate_forces_set_insert
   beforeNullifierRootCol afterNullifierRootCol beforeCommitmentsRootCol afterCommitmentsRootCol
   NULLIFIER_PARAM_COL COMMITMENT_KEY_PARAM_COL)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — the committed shielded-list root column (shared by both note effects).

`nullifiers : List Nat` and `commitments : List Nat` are ALREADY ordered lists, so their committed
root is the `listDigest` over the list directly (no Finset/sort step). A field element the circuit
carries, exactly like a `system_roots` limb. The FIX gate forces the POST root to the digest of the
GROWN list `x :: preList`. -/

/-- A field element (the same `ℤ`-carrier `ListCommit` uses for a felt). -/
abbrev FieldElem := ℤ

/-- The injective leaf encoder for a note id (`Nat` cast into the felt carrier). The realizable
Poseidon over a canonical per-id serialization; `Nat.cast` into `ℤ` is literally injective. -/
def noteLeaf : Nat → FieldElem := fun n => (n : ℤ)

/-- **`noteLeaf_injective`** — the note-leaf encoder is injective (the realizable Poseidon-CR carrier).
REALIZABLE: `Nat.cast` into `ℤ` is literally injective. -/
theorem noteLeaf_injective : listLeafInjective noteLeaf := by
  intro a b h
  unfold noteLeaf at h
  exact_mod_cast h

/-- **`noteListRoot compressN xs`** — the committed root of a shielded `List Nat` `xs`: the
`listDigest` over the list. The Lean mirror of the Rust `nullifiers_root` / `commitments_root` limb the
FIX adds to `compute_commitment`. Absorbed into `state_commit` exactly as a `system_roots` digest. -/
def noteListRoot (compressN : List FieldElem → FieldElem) (xs : List Nat) : FieldElem :=
  listDigest noteLeaf compressN xs

/-- **`noteListRoot_binds`** — equal note-list roots force the SAME `List Nat`. Off the realizable
`compressN`-injectivity carrier + the injective leaf (`ListDigestBindsList`): the digest binds the
whole ordered list. The anti-ghost foundation a forged drop/reorder must clear. -/
theorem noteListRoot_binds (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (xs ys : List Nat)
    (h : noteListRoot compressN xs = noteListRoot compressN ys) :
    xs = ys :=
  ListDigestBindsList noteLeaf compressN hN noteLeaf_injective _ _ h

/-! ## §1 — the FIX descriptor's note-root gate (the column-forcing gate).

The deployed note row freezes the economic block; the FIX ADDS a committed note-root column whose POST
value the gate `gNoteGrow` PINS to the GROWN-list digest `x :: preList`. -/

/-- **`NoteRootRow compressN preList postList preRoot postRoot`** — the decode tying the FIX row's two
committed note-root columns to the kernel pre/post shielded lists. -/
def NoteRootRow (compressN : List FieldElem → FieldElem)
    (preList postList : List Nat) (preRoot postRoot : FieldElem) : Prop :=
  preRoot = noteListRoot compressN preList ∧ postRoot = noteListRoot compressN postList

/-- **`gNoteGrow compressN preList x postRoot`** — the FIX gate body: the POST note-root column IS the
digest of the GROWN list `x :: preList`. The committed-column analog of Birth's `gAccountsGrow`: the
deployed circuit would EVALUATE this against the grown-list root the trace-fill emits, so a row whose
post note-root is anything else (a drop, a reorder, a wrong id) fails. -/
def gNoteGrow (compressN : List FieldElem → FieldElem)
    (preList : List Nat) (x : Nat) (postRoot : FieldElem) : Prop :=
  postRoot = listDigest noteLeaf compressN (x :: preList)

/-- **`noteGrowForced` — the FIX gate FORCES the committed note column.** If the FIX gate holds, the
POST list equals `x :: preList` (via `noteListRoot_binds`). This is the rung the deployed circuit is
MISSING and the FIX supplies — exactly `accountsGrowForced` for a shielded list. -/
theorem noteGrowForced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (preList postList : List Nat) (x : Nat) (preRoot postRoot : FieldElem)
    (henc : NoteRootRow compressN preList postList preRoot postRoot)
    (hgate : gNoteGrow compressN preList x postRoot) :
    postList = x :: preList := by
  obtain ⟨_, hpost⟩ := henc
  -- the POST column is BOTH `noteListRoot postList` (decode) AND the grown-list digest (gate).
  have hroots : noteListRoot compressN postList = noteListRoot compressN (x :: preList) := by
    rw [← hpost]; exact hgate
  exact noteListRoot_binds compressN hN _ _ hroots

/-! ## §2 — noteSpend: the active-row ⟷ kernel decode + the refinement (VALUE_PARTIAL).

`noteSpendGenuineEncodes` ties a satisfying FIX-descriptor witness's nullifiers-root columns onto the
spend boundary, and carries the residual the committed root cannot witness: the FIX gate (the WITNESS
leg, forcing the set-insert), the FRESHNESS `nf ∉ pre.nullifiers` (the sorted non-membership open is
PHASE-D — carried, NOT forced), the `spendProof = true` proof gate, the receipt log, and the global
side-table frame. NAMED, not laundered. -/

/-- The decode relating a satisfying FIX noteSpend witness's row to a kernel `pre → post` spend of
`nf` by `actor`. DATA-bearing (`Type`): it exhibits the two committed nullifiers-root columns, carries
the FIX gate (the witness leg — the set-insert FORCED) + the FRESHNESS + proof residual + the
kernel-side residual. -/
structure noteSpendGenuineEncodes (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool) : Type where
  -- the two committed nullifiers-root columns + their decode.
  preRoot : FieldElem
  postRoot : FieldElem
  hroots : NoteRootRow compressN pre.kernel.nullifiers post.kernel.nullifiers preRoot postRoot
  -- the FIX gate holds on the row (the WITNESS leg — the nullifier set-insert is FORCED grown).
  gate : gNoteGrow compressN pre.kernel.nullifiers nf postRoot
  -- ⚑ THE PHASE-D RESIDUAL #1: the DOUBLE-SPEND FRESHNESS. The committed root binds the LIST VALUE,
  -- not its non-membership; forcing `nf ∉ pre.nullifiers` in-circuit needs the sorted NON-MEMBERSHIP
  -- OPEN (cap-reshape PHASE-D), NOT yet available — carried, named, here.
  freshness : nf ∉ pre.kernel.nullifiers
  -- ⚑ THE PHASE-D RESIDUAL #2: the §8 spending proof gate (the theorem-layer portal, off the ledger).
  proof : spendProof = true
  -- the spend receipt advance (the record-layer commitment, off the per-row block).
  logAdv : post.log = noteSpendReceipt actor :: pre.log
  -- the global side-table frame (the `NoteSpendSpec` frame residual — balance FROZEN here).
  frAccounts : post.kernel.accounts = pre.kernel.accounts
  frCell : post.kernel.cell = pre.kernel.cell
  frCaps : post.kernel.caps = pre.kernel.caps
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

/-- **`noteSpend_nullifiers_forced` — the committed nullifier set-insert is FIX-CIRCUIT-FORCED.** On the
decoded row the FIX nullifiers gate forces the post nullifiers to `nf :: pre.nullifiers`. -/
theorem noteSpend_nullifiers_forced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
    (henc : noteSpendGenuineEncodes compressN pre post nf actor spendProof) :
    post.kernel.nullifiers = nf :: pre.kernel.nullifiers :=
  noteGrowForced compressN hN pre.kernel.nullifiers post.kernel.nullifiers nf
    henc.preRoot henc.postRoot henc.hroots henc.gate

/-- **`noteSpend_descriptorRefines` — THE FIX CIRCUIT→KERNEL REFINEMENT for noteSpend (VALUE_PARTIAL).**
A satisfying FIX noteSpend descriptor witness forces the KERNEL's spend step `NoteSpendSpec pre nf actor
spendProof post`. The `nullifiers := nf :: …` set-insert is FORCED via the committed nullifiers root
(`noteSpend_nullifiers_forced`); the FRESHNESS `nf ∉ pre.nullifiers` (the sorted non-membership open is
PHASE-D) and the `spendProof = true` proof gate are carried as the named `freshness`/`proof` decode
residuals; the receipt + the (balance-frozen) frame complete it. -/
theorem noteSpend_descriptorRefines (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
    (henc : noteSpendGenuineEncodes compressN pre post nf actor spendProof) :
    NoteSpendSpec pre nf actor spendProof post := by
  refine ⟨⟨henc.proof, henc.freshness⟩, ?_, henc.logAdv, henc.frAccounts, henc.frCell, henc.frCaps,
    henc.frRevoked, henc.frCommitments, henc.frBal, henc.frSlotCaveats, henc.frFactories,
    henc.frLifecycle, henc.frDeathCert, henc.frDelegate, henc.frDelegations, henc.frDelegationEpoch,
    henc.frDelegationEpochAt, henc.frHeaps, henc.frNullifierRoot, henc.frRevokedRoot⟩
  exact noteSpend_nullifiers_forced compressN hN pre post nf actor spendProof henc

/-- **The refinement, stated against `execFullA` directly.** `NoteSpendSpec` IS the `.noteSpendA` arm
of the executor (`execFullA_noteSpend_iff_spec`), so a satisfying FIX witness forces
`execFullA pre (.noteSpendA nf actor spendProof) = some post`. -/
theorem noteSpend_descriptorRefines_execFullA (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
    (henc : noteSpendGenuineEncodes compressN pre post nf actor spendProof) :
    execFullA pre (.noteSpendA nf actor spendProof) = some post :=
  (execFullA_noteSpend_iff_spec pre nf actor spendProof post).mpr
    (noteSpend_descriptorRefines compressN hN pre post nf actor spendProof henc)

/-- **`noteSpend_descriptorRefines_rejects_wrong_nullifiers` (BOTH-POLARITY TOOTH #1).** A decode whose
post nullifiers are NOT `nf :: pre.nullifiers` (a drop, a reorder, a missing insert — the deployed
circuit's blind spot) cannot ride a satisfying FIX witness: the nullifiers-root gate pins the grown
list, so the claim is contradictory. This is EXACTLY what the deployed circuit cannot reject. -/
theorem noteSpend_descriptorRefines_rejects_wrong_nullifiers (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
    (henc : noteSpendGenuineEncodes compressN pre post nf actor spendProof)
    (hwrong : post.kernel.nullifiers ≠ nf :: pre.kernel.nullifiers) :
    False :=
  hwrong (noteSpend_nullifiers_forced compressN hN pre post nf actor spendProof henc)

/-- **`noteSpend_descriptorRefines_rejects_double` (BOTH-POLARITY TOOTH #2 — the SECURITY CRUX).** A
DOUBLE-SPEND witness (`nf ∈ pre.nullifiers`) is REJECTED: the carried `freshness` residual is exactly
`nf ∉ pre.nullifiers`, so a double-spend claim is contradictory. The no-double-spend tooth BITES on the
freshness residual. (HONEST: this bites on the CARRIED freshness — the in-circuit non-membership open
that would make it FORCED rather than carried is PHASE-D.) -/
theorem noteSpend_descriptorRefines_rejects_double (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
    (henc : noteSpendGenuineEncodes compressN pre post nf actor spendProof)
    (hdouble : nf ∈ pre.kernel.nullifiers) :
    False :=
  henc.freshness hdouble

/-! ## §3 — noteCreate: PROVEN-FIX. The whole load-bearing set-insert is FORCED; NO guard to carry.

`noteCreateGenuineEncodes` ties a satisfying FIX-descriptor witness's commitments-root columns onto the
create boundary. `NoteCreateASpec` has NO guard (append-only — `noteCreateAdmit = True`), so the
committed `commitmentsRoot` FORCES the WHOLE load-bearing content `post.commitments = cm ::
pre.commitments`. The receipt + the (balance-frozen) frame are the named decode residual. -/

/-- The decode relating a satisfying FIX noteCreate witness's row to a kernel `pre → post` create of
`cm` by `actor`. DATA-bearing (`Type`): it exhibits the two committed commitments-root columns, carries
the FIX gate (the witness leg — the commitment set-insert FORCED) + the kernel-side residual. There is
NO guard to carry (`noteCreate` is unconditional). -/
structure noteCreateGenuineEncodes (compressN : List FieldElem → FieldElem)
    (pre post : RecChainedState) (cm : Nat) (actor : CellId) : Type where
  -- the two committed commitments-root columns + their decode.
  preRoot : FieldElem
  postRoot : FieldElem
  hroots : NoteRootRow compressN pre.kernel.commitments post.kernel.commitments preRoot postRoot
  -- the FIX gate holds on the row (the WITNESS leg — the commitment set-insert is FORCED grown).
  gate : gNoteGrow compressN pre.kernel.commitments cm postRoot
  -- the create receipt advance (the record-layer commitment, off the per-row block).
  logAdv : post.log = noteCreateReceipt actor :: pre.log
  -- the global side-table frame (the `NoteCreateASpec` frame residual — balance FROZEN here).
  frAccounts : post.kernel.accounts = pre.kernel.accounts
  frCell : post.kernel.cell = pre.kernel.cell
  frCaps : post.kernel.caps = pre.kernel.caps
  frNullifiers : post.kernel.nullifiers = pre.kernel.nullifiers
  frRevoked : post.kernel.revoked = pre.kernel.revoked
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

/-- **`noteCreate_commitments_forced` — the committed commitment set-insert is FIX-CIRCUIT-FORCED.** On
the decoded row the FIX commitments gate forces the post commitments to `cm :: pre.commitments`. -/
theorem noteCreate_commitments_forced (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (cm : Nat) (actor : CellId)
    (henc : noteCreateGenuineEncodes compressN pre post cm actor) :
    post.kernel.commitments = cm :: pre.kernel.commitments :=
  noteGrowForced compressN hN pre.kernel.commitments post.kernel.commitments cm
    henc.preRoot henc.postRoot henc.hroots henc.gate

/-- **`noteCreate_descriptorRefines` — THE FIX CIRCUIT→KERNEL REFINEMENT for noteCreate (PROVEN-FIX).**
A satisfying FIX noteCreate descriptor witness forces the KERNEL's create step `NoteCreateASpec pre cm
actor post`. The `commitments := cm :: …` set-insert — the WHOLE load-bearing content — is FORCED via
the committed commitments root (`noteCreate_commitments_forced`); the (trivial) guard, the receipt, and
the (balance-frozen) frame are the named decode residual. There is no freshness/authority to carry. -/
theorem noteCreate_descriptorRefines (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (cm : Nat) (actor : CellId)
    (henc : noteCreateGenuineEncodes compressN pre post cm actor) :
    NoteCreateASpec pre cm actor post := by
  refine ⟨trivial, ?_, henc.logAdv, henc.frAccounts, henc.frCell, henc.frCaps, henc.frNullifiers,
    henc.frRevoked, henc.frBal, henc.frSlotCaveats, henc.frFactories, henc.frLifecycle,
    henc.frDeathCert, henc.frDelegate, henc.frDelegations, henc.frDelegationEpoch,
    henc.frDelegationEpochAt, henc.frHeaps, henc.frNullifierRoot, henc.frRevokedRoot⟩
  exact noteCreate_commitments_forced compressN hN pre post cm actor henc

/-- **The refinement, stated against `execFullA` directly.** `NoteCreateASpec` IS the `.noteCreateA`
arm of the executor (`execNoteCreateA_iff_spec`), so a satisfying FIX witness forces
`execFullA pre (.noteCreateA cm actor) = some post`. -/
theorem noteCreate_descriptorRefines_execFullA (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (cm : Nat) (actor : CellId)
    (henc : noteCreateGenuineEncodes compressN pre post cm actor) :
    execFullA pre (.noteCreateA cm actor) = some post :=
  (execNoteCreateA_iff_spec pre cm actor post).mpr
    (noteCreate_descriptorRefines compressN hN pre post cm actor henc)

/-- **`noteCreate_descriptorRefines_rejects_wrong_commitments` (BOTH-POLARITY TOOTH).** A decode whose
post commitments are NOT `cm :: pre.commitments` (a wrong/duplicate-misplaced insert, a drop, a reorder
— the deployed circuit's blind spot) cannot ride a satisfying FIX witness: the commitments-root gate
pins the grown list, so the claim is contradictory. This is EXACTLY what the deployed circuit cannot
reject. -/
theorem noteCreate_descriptorRefines_rejects_wrong_commitments (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (cm : Nat) (actor : CellId)
    (henc : noteCreateGenuineEncodes compressN pre post cm actor)
    (hwrong : post.kernel.commitments ≠ cm :: pre.kernel.commitments) :
    False :=
  hwrong (noteCreate_commitments_forced compressN hN pre post cm actor henc)

/-! ## §4 — NON-VACUITY: the note root + the gate are load-bearing (no carrier secretly `True`).

A concrete injective `compressN` (a positional Horner sponge, NOT `List.sum`). The note root of a GROWN
list DIFFERS from the pre list's root (the gate distinguishes them); a frozen-list row's post-root is
NOT the grown-list digest (the gate REJECTS it). A `noteListRoot := 0` stub would collapse these. -/

private def cNC : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 1000003 + x) (xs.length : ℤ)

private def preNf : List Nat := [7, 3, 1]
private def newNf : Nat := 9

-- POSITIVE (load-bearing): the GROWN list's root DIFFERS from the pre list's root (the gate is not a
-- no-op — a `noteListRoot := 0` stub would make these EQUAL: forbidden).
#guard decide (listDigest noteLeaf cNC (newNf :: preNf) = listDigest noteLeaf cNC preNf) == false

-- The grown digest equals itself (the gate's RHS is the genuine grown root, computable).
#guard decide (listDigest noteLeaf cNC (newNf :: preNf) = listDigest noteLeaf cNC (newNf :: preNf))

-- ANTI-GHOST: a FROZEN-list post (list unchanged) has a post-root that is NOT the grown-list digest,
-- so `gNoteGrow` FAILS for it — a no-op note insert is rejected.
#guard decide (listDigest noteLeaf cNC preNf = listDigest noteLeaf cNC (newNf :: preNf)) == false

-- ANTI-GHOST: a DROP (post = [3, 1] ⊊ pre, an existing id silently removed) has a different root than
-- the grown list — a forgery that drops an existing entry is rejected.
#guard decide (listDigest noteLeaf cNC [3, 1] = listDigest noteLeaf cNC (newNf :: preNf)) == false

-- ANTI-GHOST: a REORDER (post = [3, 9, 7, 1], the new id mis-placed) is rejected — the digest pins the
-- WHOLE ordered list, not just membership.
#guard decide (listDigest noteLeaf cNC [3, 9, 7, 1] = listDigest noteLeaf cNC (newNf :: preNf)) == false

-- The note leaf encoder is injective on the toy domain (the carrier is committing the ids):
#guard decide (noteLeaf 1 = noteLeaf 2) == false

/-! ## §4.A — CLASS A: the shielded-set growth is FORCED by the DEPLOYED descriptors (`noteSpendV3` /
`noteCreateV3`), not a modelled gate.

§2–§3 force the growth from `*GenuineEncodes.gate`, the MODELLED `gNoteGrow` the decode ASSERTS —
editing the LIVE `*V3` constraints does NOT break it. This section closes that gap exactly as Birth's §6.A
/ `RotatedKernelRefinementCellSeal` §6.5 do: each `*_forced_sat` derives the shielded set-insert from a
`Satisfied2 hash *V3` witness DIRECTLY, by

  * `noteSpendV3_grow_gate_forces_set_insert` / `noteCreateV3_grow_gate_forces_set_insert` — the DEPLOYED
    in-circuit `.insert` map-op FORCES the live wire's `writesTo before_root key value after_root` (the
    committed BEFORE/AFTER nullifier/commitment root limbs — limb 26 / limb 27, openable sorted-Poseidon2
    roots chaining into `state_commit`) on the active row whose runtime selector fires;
  * `*TraceReadout.growthDecodes` — the realizable `WitnessDecodes`-class seam: the deployed forced write of
    the note id (with its note-value leaf) into the BEFORE shielded root IS the kernel list set-insert (the
    deployed trace-fill emits the genuine grown root as `after_root`, so the felt-level write and the kernel
    cons are the SAME growth by construction — the limb-level decode the COMMITMENT cannot certify, supplied
    by `StarkSound`, exactly as cellSeal's `discLimbDecodes`).

Editing `*V3`'s grow-gate breaks `*V3_grow_gate_forces_set_insert`, hence the forced `writesTo`, hence
`growthDecodes`'s antecedent, hence `*_forced_sat`, hence `*_descriptorRefines_sat` — Class A. -/

/-- **`NoteSpendTraceReadout`** — the realizable circuit-witness extraction for noteSpend (NAMED), the
`WitnessDecodes` class of cellSeal's `CellSealTraceReadout`. The grow GATE is NOT a field — the forced
`writesTo` is derived from `Satisfied2 hash noteSpendV3` (`noteSpend_forced_sat`). The FRESHNESS
`nf ∉ pre.nullifiers` and the `spendProof = true` gate remain the named PHASE-D residuals (VALUE_PARTIAL),
exactly as §2's `noteSpendGenuineEncodes`. -/
structure NoteSpendTraceReadout (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool) : Type where
  row : Nat
  hrow : row < t.rows.length
  hsel : (envAt t row).loc Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.SEL_NOTE_SPEND = 1
  -- the realizable `WitnessDecodes`-class seam: the deployed forced write of the spent nullifier into the
  -- BEFORE nullifier root IS the kernel list set-insert `post.nullifiers = nf :: pre.nullifiers`.
  growthDecodes :
    writesTo hash ((envAt t row).loc (beforeNullifierRootCol EFFECT_VM_WIDTH))
        ((envAt t row).loc NULLIFIER_PARAM_COL)
        ((envAt t row).loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.param.NOTE_VALUE_LO))
        ((envAt t row).loc (afterNullifierRootCol EFFECT_VM_WIDTH))
      → post.kernel.nullifiers = nf :: pre.kernel.nullifiers
  -- ⚑ THE PHASE-D RESIDUAL #1: the DOUBLE-SPEND FRESHNESS (the sorted non-membership open is PHASE-D).
  freshness : nf ∉ pre.kernel.nullifiers
  -- ⚑ THE PHASE-D RESIDUAL #2: the §8 spending proof gate.
  proof : spendProof = true
  logAdv : post.log = noteSpendReceipt actor :: pre.log
  frAccounts : post.kernel.accounts = pre.kernel.accounts
  frCell : post.kernel.cell = pre.kernel.cell
  frCaps : post.kernel.caps = pre.kernel.caps
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

/-- **`noteSpend_forced_sat`** — the nullifier set-insert FORCED by the DEPLOYED `noteSpendV3` (Class A). -/
theorem noteSpend_forced_sat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash noteSpendV3 minit mfin maddrs t)
    (pre post : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
    (rd : NoteSpendTraceReadout hash minit mfin maddrs t pre post nf actor spendProof) :
    post.kernel.nullifiers = nf :: pre.kernel.nullifiers :=
  rd.growthDecodes
    (noteSpendV3_grow_gate_forces_set_insert hash hsat rd.row rd.hrow rd.hsel).2

/-- **`noteSpend_descriptorRefines_sat` — THE CLASS-A REFINEMENT for noteSpend (VALUE_PARTIAL).** The
nullifier set-insert is forced from the DEPLOYED grow-gate's `Satisfied2` (`noteSpend_forced_sat`); the
FRESHNESS and the proof gate are the named PHASE-D residuals. -/
theorem noteSpend_descriptorRefines_sat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash noteSpendV3 minit mfin maddrs t)
    (pre post : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
    (rd : NoteSpendTraceReadout hash minit mfin maddrs t pre post nf actor spendProof) :
    NoteSpendSpec pre nf actor spendProof post := by
  refine ⟨⟨rd.proof, rd.freshness⟩, ?_, rd.logAdv, rd.frAccounts, rd.frCell, rd.frCaps,
    rd.frRevoked, rd.frCommitments, rd.frBal, rd.frSlotCaveats, rd.frFactories,
    rd.frLifecycle, rd.frDeathCert, rd.frDelegate, rd.frDelegations, rd.frDelegationEpoch,
    rd.frDelegationEpochAt, rd.frHeaps, rd.frNullifierRoot, rd.frRevokedRoot⟩
  exact noteSpend_forced_sat hash hsat pre post nf actor spendProof rd

/-- **CLASS-A TOOTH** — a forged wrong-nullifiers noteSpend witness is UNSAT (the grow-gate bites). -/
theorem noteSpend_sat_rejects_wrong_nullifiers (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash noteSpendV3 minit mfin maddrs t)
    (pre post : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
    (rd : NoteSpendTraceReadout hash minit mfin maddrs t pre post nf actor spendProof)
    (hwrong : post.kernel.nullifiers ≠ nf :: pre.kernel.nullifiers) :
    False :=
  hwrong (noteSpend_forced_sat hash hsat pre post nf actor spendProof rd)

/-- **`NoteCreateTraceReadout`** — the realizable circuit-witness extraction for noteCreate (NAMED),
PROVEN-FIX: the whole load-bearing set-insert is forced (no guard to carry). -/
structure NoteCreateTraceReadout (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (cm : Nat) (actor : CellId) : Type where
  row : Nat
  hrow : row < t.rows.length
  hsel : (envAt t row).loc Dregg2.Circuit.Emit.EffectVmEmitNoteCreate.SEL_NOTE_CREATE = 1
  growthDecodes :
    writesTo hash ((envAt t row).loc (beforeCommitmentsRootCol EFFECT_VM_WIDTH))
        ((envAt t row).loc COMMITMENT_KEY_PARAM_COL)
        ((envAt t row).loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitNoteCreate.param.NOTE_VALUE_LO))
        ((envAt t row).loc (afterCommitmentsRootCol EFFECT_VM_WIDTH))
      → post.kernel.commitments = cm :: pre.kernel.commitments
  logAdv : post.log = noteCreateReceipt actor :: pre.log
  frAccounts : post.kernel.accounts = pre.kernel.accounts
  frCell : post.kernel.cell = pre.kernel.cell
  frCaps : post.kernel.caps = pre.kernel.caps
  frNullifiers : post.kernel.nullifiers = pre.kernel.nullifiers
  frRevoked : post.kernel.revoked = pre.kernel.revoked
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

/-- **`noteCreate_forced_sat`** — the commitment set-insert FORCED by the DEPLOYED `noteCreateV3` (Class A;
the whole load-bearing content, no guard). -/
theorem noteCreate_forced_sat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash noteCreateV3 minit mfin maddrs t)
    (pre post : RecChainedState) (cm : Nat) (actor : CellId)
    (rd : NoteCreateTraceReadout hash minit mfin maddrs t pre post cm actor) :
    post.kernel.commitments = cm :: pre.kernel.commitments :=
  rd.growthDecodes
    (noteCreateV3_grow_gate_forces_set_insert hash hsat rd.row rd.hrow rd.hsel)

/-- **`noteCreate_descriptorRefines_sat` — THE CLASS-A REFINEMENT for noteCreate (PROVEN-FIX).** -/
theorem noteCreate_descriptorRefines_sat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash noteCreateV3 minit mfin maddrs t)
    (pre post : RecChainedState) (cm : Nat) (actor : CellId)
    (rd : NoteCreateTraceReadout hash minit mfin maddrs t pre post cm actor) :
    NoteCreateASpec pre cm actor post := by
  refine ⟨trivial, ?_, rd.logAdv, rd.frAccounts, rd.frCell, rd.frCaps, rd.frNullifiers,
    rd.frRevoked, rd.frBal, rd.frSlotCaveats, rd.frFactories, rd.frLifecycle,
    rd.frDeathCert, rd.frDelegate, rd.frDelegations, rd.frDelegationEpoch,
    rd.frDelegationEpochAt, rd.frHeaps, rd.frNullifierRoot, rd.frRevokedRoot⟩
  exact noteCreate_forced_sat hash hsat pre post cm actor rd

/-- **CLASS-A TOOTH** — a forged wrong-commitments noteCreate witness is UNSAT (the grow-gate bites). -/
theorem noteCreate_sat_rejects_wrong_commitments (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash noteCreateV3 minit mfin maddrs t)
    (pre post : RecChainedState) (cm : Nat) (actor : CellId)
    (rd : NoteCreateTraceReadout hash minit mfin maddrs t pre post cm actor)
    (hwrong : post.kernel.commitments ≠ cm :: pre.kernel.commitments) :
    False :=
  hwrong (noteCreate_forced_sat hash hsat pre post cm actor rd)

/-! ## §5 — axiom-hygiene tripwires. -/

#assert_axioms noteLeaf_injective
#assert_axioms noteListRoot_binds
#assert_axioms noteGrowForced
#assert_axioms noteSpend_nullifiers_forced
#assert_axioms noteSpend_descriptorRefines
#assert_axioms noteSpend_descriptorRefines_execFullA
#assert_axioms noteSpend_descriptorRefines_rejects_wrong_nullifiers
#assert_axioms noteSpend_descriptorRefines_rejects_double
#assert_axioms noteCreate_commitments_forced
#assert_axioms noteCreate_descriptorRefines
#assert_axioms noteCreate_descriptorRefines_execFullA
#assert_axioms noteCreate_descriptorRefines_rejects_wrong_commitments
#assert_axioms noteSpend_forced_sat
#assert_axioms noteSpend_descriptorRefines_sat
#assert_axioms noteSpend_sat_rejects_wrong_nullifiers
#assert_axioms noteCreate_forced_sat
#assert_axioms noteCreate_descriptorRefines_sat
#assert_axioms noteCreate_sat_rejects_wrong_commitments

end Dregg2.Circuit.RotatedKernelRefinementNotes
