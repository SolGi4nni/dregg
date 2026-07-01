/-
# Dregg2.Circuit.RotatedKernelRefinementNotesFresh — noteSpend's DOUBLE-SPEND FRESHNESS,
  FORCED in-circuit by the sorted-Merkle NON-MEMBERSHIP open (PHASE-D, the security crux closed).

## What this file does (the phase-D payoff for noteSpend)

`RotatedKernelRefinementNotes.lean` proved `noteSpend_descriptorRefines` as VALUE_PARTIAL: the
nullifier set-insert `post.nullifiers = nf :: pre.nullifiers` is FORCED via the committed
`nullifiersRoot`, but the no-double-spend FRESHNESS `nf ∉ pre.nullifiers` was CARRIED as a named
`freshness` field — the committed list-root binds the LIST VALUE, not its non-membership.

`SortedTreeNonMembership.lean` now supplies the missing gadget: the in-circuit sorted-Merkle
non-membership open (`nonMembership_sound`), whose satisfaction proves a key ABSENT from the committed
sorted tree. THIS file consumes it to FORCE the freshness, replacing the carried field:

    a non-membership open of `nf`'s key against the committed nullifier tree ⟹ `nf ∉ pre.nullifiers`.

So `noteSpendFresh_descriptorRefines` is the STRENGTHENED refinement: the freshness is no longer
carried — it is DERIVED from the open. The double-spend hole closes IN-CIRCUIT.

## The binding (the faithful nullifier-tree encoding)

The kernel's `nullifiers : List Nat` is committed as a sorted-Merkle nullifier tree (the deployed
nullifier accumulator). `NullifierTreeEncodes S8 root pre` says: the tree at `root` commits a key set
that EQUALS the kernel nullifier set under the injective key map (`nfKey = noteLeaf = Nat ↪ ℤ`). Then
`keysOf S8 root = nfKey '' pre.nullifiers` (the committed keys are exactly the nullifier keys), so a key
absent from `keysOf` is a nullifier absent from `pre.nullifiers`. This is the SAME faithful-encoding
discipline `DeployedFaithful` carries for the cap-tree, here for the nullifier set.

## The both-polarity TOOTH (the security crux)

`noteSpendFresh_rejects_double` — a DOUBLE-SPEND (`nf ∈ pre.nullifiers`) makes the non-membership open
UNSAT: the open would prove `nfKey nf ∉ keysOf S8 root`, but the faithful encoding puts `nfKey nf` IN
`keysOf S8 root` (since `nf ∈ pre.nullifiers`) — contradiction. The freshness gate now BITES IN-CIRCUIT
(on the FORCED open, not a carried field) — the no-double-spend security crux, closed.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} + the realizable carriers already in play
(`CapHashScheme.chipCR` via the deployed cap/nullifier tree; `compressNInjective` + `noteLeaf_injective`
from `RotatedKernelRefinementNotes`; `SpineCommits`/`NullifierTreeEncodes` are HYPOTHESES, never axioms).
NEW file; all imports read-only.
-/
import Dregg2.Circuit.SortedTreeNonMembership
import Dregg2.Circuit.RotatedKernelRefinementNotes

namespace Dregg2.Circuit.RotatedKernelRefinementNotesFresh

open Dregg2.Circuit
open Dregg2.Circuit.SortedTreeNonMembership
  (keyOf keysOf SpineCommits GapOpen nonMembership_sound
   NonMemberRowInner nonMemberRowInner_sound)
open Dregg2.Circuit.DeployedCapTree (CapLeaf CapHashScheme Cap8Scheme Digest8)
open Dregg2.Circuit.RotatedKernelRefinementNotes (noteLeaf noteLeaf_injective)
open Dregg2.Circuit.StateCommit (compressNInjective)
open Dregg2.Circuit.Spec.NoteNullifier (NoteSpendSpec noteSpendReceipt)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — the nullifier sort key + the faithful nullifier-tree encoding.

A nullifier `nf : Nat` sorts into the tree at key `nfKey nf = (nf : ℤ)` (the SAME injective leaf map
`noteLeaf` the nullifiers-root limb uses — `Nat ↪ ℤ`, literally injective). The committed nullifier
tree at `root` faithfully encodes the kernel nullifier set when its committed key set is EXACTLY the
nullifier keys. -/

/-- **`nfKey nf`** — the sort key of a nullifier in the nullifier tree: `(nf : ℤ)` (the same injective
`noteLeaf` map the nullifiers-root commits, so the tree's sort key and the root's leaf encode coincide). -/
def nfKey (nf : Nat) : ℤ := noteLeaf nf

/-- `nfKey` is injective (`Nat ↪ ℤ`, the realizable map). -/
theorem nfKey_injective : Function.Injective nfKey := by
  intro a b h; exact noteLeaf_injective h

/-- **`NullifierTreeEncodes S8 root nulls`** — the (named, realizable) faithful encoding: the committed
nullifier tree at `root` commits a key set EQUAL to the kernel nullifier keys. Concretely: a key `k`
is in the committed tree (`k ∈ keysOf S8 root`) IFF `k = nfKey nf` for some `nf ∈ nulls`. The SAME
faithful-encoding discipline `DeployedFaithful` carries for the cap-tree; a HYPOTHESIS (the deployed
nullifier-accumulator commitment), never an axiom. -/
def NullifierTreeEncodes (S8 : Cap8Scheme) (root : Digest8) (nulls : List Nat) : Prop :=
  ∀ k : ℤ, k ∈ keysOf S8 root ↔ ∃ nf, nf ∈ nulls ∧ nfKey nf = k

/-- **`absent_key_absent_nullifier`** — the bridge from tree-absence to nullifier-absence: under the
faithful encoding, if `nfKey nf` is absent from the committed tree, then `nf` is absent from the kernel
nullifier set. The freshness `nf ∉ nulls` DERIVED from a non-membership open (not carried). -/
theorem absent_key_absent_nullifier (S8 : Cap8Scheme) (root : Digest8)
    (nulls : List Nat) (nf : Nat)
    (henc : NullifierTreeEncodes S8 root nulls)
    (habsent : nfKey nf ∉ keysOf S8 root) :
    nf ∉ nulls := by
  intro hmem
  exact habsent ((henc (nfKey nf)).mpr ⟨nf, hmem, rfl⟩)

/-! ## §1 — freshness FORCED by an abstract non-membership open (the `GapOpen` form).

Given a faithful nullifier tree, a `GapOpen` valid against its committed spine FORCES `nf ∉ nulls`:
`nonMembership_sound` proves the key absent from the tree, `absent_key_absent_nullifier` lifts it to
nullifier-absence. The freshness is no longer carried — it is the OUTPUT of the open. -/

/-- **`freshness_forced` — THE FRESHNESS, FORCED by the non-membership open.** Given the faithful
nullifier-tree encoding, the spine↔root binding, and a `GapOpen` for `nfKey nf` valid against the
committed spine, the nullifier `nf` is FRESH (`nf ∉ nulls`). This replaces the carried `freshness`
field of `noteSpendGenuineEncodes`. -/
theorem freshness_forced (S8 : Cap8Scheme) (root : Digest8)
    (nulls : List Nat) (nf : Nat) (spine : List ℤ)
    (henc : NullifierTreeEncodes S8 root nulls)
    (hc : SpineCommits S8 root spine)
    (g : GapOpen S8 root (nfKey nf)) (hv : g.coversSpine spine) :
    nf ∉ nulls := by
  have habsent : nfKey nf ∉ keysOf S8 root :=
    nonMembership_sound S8 root (nfKey nf) spine hc g hv
  exact absent_key_absent_nullifier S8 root nulls nf henc habsent

/-! ## §2 — the STRENGTHENED noteSpend encode: freshness FORCED, not carried.

`noteSpendFreshEncodes` mirrors `noteSpendGenuineEncodes` but REMOVES the carried `freshness` field,
replacing it with the non-membership open ingredients (the faithful tree, the spine binding, the gap
open). Everything else (the nullifiers-root set-insert, the proof gate, the receipt, the frame) is
inherited from the base `noteSpendGenuineEncodes` minus freshness. -/

/-- The phase-D strengthened noteSpend decode: carries the base set-insert encode WITHOUT freshness,
plus the non-membership open ingredients that FORCE freshness. The freshness is DERIVED
(`derivedFresh`), not a field. -/
structure noteSpendFreshEncodes (S8 : Cap8Scheme)
    (compressN : List RotatedKernelRefinementNotes.FieldElem → RotatedKernelRefinementNotes.FieldElem)
    (pre post : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool) : Type where
  -- the committed nullifiers-root columns + their decode (the set-insert leg).
  preRoot : RotatedKernelRefinementNotes.FieldElem
  postRoot : RotatedKernelRefinementNotes.FieldElem
  hroots : RotatedKernelRefinementNotes.NoteRootRow compressN
    pre.kernel.nullifiers post.kernel.nullifiers preRoot postRoot
  -- the FIX gate (the WITNESS leg — the nullifier set-insert is FORCED grown).
  gate : RotatedKernelRefinementNotes.gNoteGrow compressN pre.kernel.nullifiers nf postRoot
  -- ⚑ THE PHASE-D OPEN (replaces the carried freshness): the faithful nullifier tree + the spine
  -- binding + a non-membership open of `nfKey nf` against the committed nullifier tree at `nfTreeRoot`.
  nfTreeRoot : Digest8
  spine : List ℤ
  treeEnc : NullifierTreeEncodes S8 nfTreeRoot pre.kernel.nullifiers
  spineCommits : SpineCommits S8 nfTreeRoot spine
  gapOpen : GapOpen S8 nfTreeRoot (nfKey nf)
  gapValid : gapOpen.coversSpine spine
  -- the §8 spending proof gate (the theorem-layer portal, still carried — orthogonal to freshness).
  proof : spendProof = true
  -- the spend receipt advance.
  logAdv : post.log = noteSpendReceipt actor :: pre.log
  -- the global side-table frame (balance FROZEN).
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

/-- **`noteSpendFresh_freshness` — the freshness is FORCED (not carried).** On the strengthened decode,
the non-membership open FORCES `nf ∉ pre.nullifiers` (via `freshness_forced`). This is exactly the
phase-D residual the base file CARRIED, now DERIVED. -/
theorem noteSpendFresh_freshness (S8 : Cap8Scheme)
    (compressN : List RotatedKernelRefinementNotes.FieldElem → RotatedKernelRefinementNotes.FieldElem)
    (pre post : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
    (henc : noteSpendFreshEncodes S8 compressN pre post nf actor spendProof) :
    nf ∉ pre.kernel.nullifiers :=
  freshness_forced S8 henc.nfTreeRoot pre.kernel.nullifiers nf henc.spine
    henc.treeEnc henc.spineCommits henc.gapOpen henc.gapValid

/-- **`noteSpendFresh_to_base` — the strengthened decode REBUILDS the base decode** (with the FORCED
freshness in the freshness slot). So everything the base `noteSpend_descriptorRefines` proves carries
over — but now the freshness is in-circuit-forced, not assumed. -/
def noteSpendFresh_to_base (S8 : Cap8Scheme)
    (compressN : List RotatedKernelRefinementNotes.FieldElem → RotatedKernelRefinementNotes.FieldElem)
    (pre post : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
    (henc : noteSpendFreshEncodes S8 compressN pre post nf actor spendProof) :
    RotatedKernelRefinementNotes.noteSpendGenuineEncodes compressN pre post nf actor spendProof where
  preRoot := henc.preRoot
  postRoot := henc.postRoot
  hroots := henc.hroots
  gate := henc.gate
  freshness := noteSpendFresh_freshness S8 compressN pre post nf actor spendProof henc
  proof := henc.proof
  logAdv := henc.logAdv
  frAccounts := henc.frAccounts
  frCell := henc.frCell
  frCaps := henc.frCaps
  frRevoked := henc.frRevoked
  frCommitments := henc.frCommitments
  frBal := henc.frBal
  frSlotCaveats := henc.frSlotCaveats
  frFactories := henc.frFactories
  frLifecycle := henc.frLifecycle
  frDeathCert := henc.frDeathCert
  frDelegate := henc.frDelegate
  frDelegations := henc.frDelegations
  frDelegationEpoch := henc.frDelegationEpoch
  frDelegationEpochAt := henc.frDelegationEpochAt
  frHeaps := henc.frHeaps

/-- **`noteSpendFresh_descriptorRefines` — THE PHASE-D REFINEMENT for noteSpend (freshness FORCED).**
A satisfying STRENGTHENED noteSpend descriptor witness forces the KERNEL's spend step `NoteSpendSpec
pre nf actor spendProof post` — with the no-double-spend freshness `nf ∉ pre.nullifiers` now FORCED by
the in-circuit non-membership open (`freshness_forced`), NOT carried. The VALUE_PARTIAL residual the
base file named is CLOSED: this is VALUE-COMPLETE up to the §8 proof gate (orthogonal, theorem-layer). -/
theorem noteSpendFresh_descriptorRefines (S8 : Cap8Scheme)
    (compressN : List RotatedKernelRefinementNotes.FieldElem → RotatedKernelRefinementNotes.FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
    (henc : noteSpendFreshEncodes S8 compressN pre post nf actor spendProof) :
    NoteSpendSpec pre nf actor spendProof post :=
  RotatedKernelRefinementNotes.noteSpend_descriptorRefines compressN hN pre post nf actor spendProof
    (noteSpendFresh_to_base S8 compressN pre post nf actor spendProof henc)

/-- **The phase-D refinement, against `execFullA` directly.** -/
theorem noteSpendFresh_descriptorRefines_execFullA (S8 : Cap8Scheme)
    (compressN : List RotatedKernelRefinementNotes.FieldElem → RotatedKernelRefinementNotes.FieldElem)
    (hN : compressNInjective compressN)
    (pre post : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
    (henc : noteSpendFreshEncodes S8 compressN pre post nf actor spendProof) :
    execFullA pre (.noteSpendA nf actor spendProof) = some post :=
  RotatedKernelRefinementNotes.noteSpend_descriptorRefines_execFullA compressN hN pre post nf actor
    spendProof (noteSpendFresh_to_base S8 compressN pre post nf actor spendProof henc)

/-! ## §3 — the both-polarity TOOTH: a DOUBLE-SPEND makes the open UNSAT (the security crux). -/

/-- **`noteSpendFresh_rejects_double` (THE SECURITY CRUX — the freshness now BITES IN-CIRCUIT).** A
DOUBLE-SPEND witness (`nf ∈ pre.nullifiers`) cannot ride a satisfying strengthened decode: the
non-membership open FORCES `nf ∉ pre.nullifiers` (via `noteSpendFresh_freshness`), contradicting the
double-spend. Unlike the base `noteSpend_descriptorRefines_rejects_double` (which bit on the CARRIED
freshness), this bites on the FORCED open — the no-double-spend gate is now an IN-CIRCUIT gate. The
double-spend hole is closed. -/
theorem noteSpendFresh_rejects_double (S8 : Cap8Scheme)
    (compressN : List RotatedKernelRefinementNotes.FieldElem → RotatedKernelRefinementNotes.FieldElem)
    (pre post : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
    (henc : noteSpendFreshEncodes S8 compressN pre post nf actor spendProof)
    (hdouble : nf ∈ pre.kernel.nullifiers) :
    False :=
  (noteSpendFresh_freshness S8 compressN pre post nf actor spendProof henc) hdouble

/-- **`noteSpendFresh_gapOpen_unsat_on_double` (the open ITSELF is unsatisfiable on a double-spend).**
Stated at the gadget level: a faithful nullifier tree containing `nf` (because `nf ∈ pre.nullifiers`)
admits NO valid non-membership open of `nfKey nf` — the security crux at the open's own boundary. This
is what the deployed circuit cannot reject without the non-membership gadget. -/
theorem noteSpendFresh_gapOpen_unsat_on_double (S8 : Cap8Scheme)
    (root : Digest8) (nulls : List Nat) (nf : Nat) (spine : List ℤ)
    (henc : NullifierTreeEncodes S8 root nulls)
    (hc : SpineCommits S8 root spine)
    (hdouble : nf ∈ nulls)
    (g : GapOpen S8 root (nfKey nf)) (hv : g.coversSpine spine) :
    False :=
  (freshness_forced S8 root nulls nf spine henc hc g hv) hdouble

/-! ## §4 — Axiom hygiene. -/

#assert_axioms nfKey_injective
#assert_axioms absent_key_absent_nullifier
#assert_axioms freshness_forced
#assert_axioms noteSpendFresh_freshness
#assert_axioms noteSpendFresh_descriptorRefines
#assert_axioms noteSpendFresh_descriptorRefines_execFullA
#assert_axioms noteSpendFresh_rejects_double
#assert_axioms noteSpendFresh_gapOpen_unsat_on_double

end Dregg2.Circuit.RotatedKernelRefinementNotesFresh
