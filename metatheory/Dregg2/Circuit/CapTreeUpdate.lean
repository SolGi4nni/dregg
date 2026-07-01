/-
# Dregg2.Circuit.CapTreeUpdate — the THREE sorted-tree UPDATE operations the capability family needs,
  over the deployed cap-tree, CONSUMING the PHASE-D non-membership gadget.

## What this file builds (generic, LAW#1-clean — no Rust constraints; over the gadget's interface)

`SortedTreeNonMembership.lean` (the PHASE-D keystone) gives the in-circuit sorted-Merkle moves over the
COMMITTED KEY SET `keysOf S8 root` (the leaf `slot_hash` keys the depth-16 binary-Merkle fold commits):

  * `nonMembership_sound` — a valid gap open ⟹ `k ∉ keysOf S8 root` (a key is ABSENT);
  * `update_sound` — old root binds `spine` + `k` fresh + new root binds `sortedInsert k spine` ⟹
    `keysOf newRoot = insert k (keysOf oldRoot)` (the INSERT update).

The capability family performs THREE sorted-tree update operations. This file states all three over the
SAME gadget interface (`SpineCommits` + `keysOf`), each as a SET-LEVEL move FORCED by the gadget:

  * **insert** (`capInsert_sound`) — add a cap leaf at a FRESH key → `keysOf` grows by exactly that key.
    A thin specialization of the gadget's `update_sound`.
  * **update-at-key / narrow** (`capUpdateAt_sound`) — membership-open an EXISTING key, recompute its
    leaf with the narrowed rights, rebind the root at the SAME spine → `keysOf` is UNCHANGED (the key
    set is preserved; the LEAF VALUE moves, witnessed by the present-key membership). This is the
    attenuate / delegateAtten / refresh shape (the key stays; the rights narrow).
  * **remove** (`capRemove_sound`) — membership-open the key, rebind the root at `sortedRemove k spine`
    → `keysOf` loses exactly that key. This is the revoke / revokeDelegation / revokeCapability shape.

The combinatorial cores (`sortedRemove` preserves sortedness, removes exactly the key) are proved here
UNCONDITIONALLY, mirroring the gadget's `sortedInsert` lemmas; the root-binding is the realizable
`SpineCommits` carrier (a HYPOTHESIS, never an axiom — the SAME residue the gadget carries).

## What this does NOT do (the honest seam — named, carried by the consumers)

These operations move the sorted-tree KEY SET `keysOf S8 root`. The kernel cap-family specs pin a `Caps`
FUNCTION (`Label → List Cap`) move (`attenuateSlotF`/`grant`/`removeEdgeCaps`/`refreshDelegationsMap`).
The lift from the committed key-set move to the resulting `Caps`-function equality is the FAITHFUL
cap-tree↔kernel-caps encoding residual — exactly what `RotatedKernelRefinementAttenuate.capsMove`
carries, and what `DeployedCapTree.DeployedFaithful` is the membership-side analog of. This file is the
KEY-SET LAYER; `RotatedKernelRefinementCapFamily.lean` consumes it under a NAMED faithful-encoding
carrier to deliver the per-effect `Caps`-function spec. We do NOT fake that lift here.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} + the realizable `CapHashScheme` carriers
inherited from `DeployedCapTree`/`SortedTreeNonMembership` (`Compress1CR` via `chipCR`; the
`SpineCommits` spine↔root binding, a HYPOTHESIS). NEW file; imports read-only.
-/
import Dregg2.Circuit.SortedTreeNonMembership

namespace Dregg2.Circuit.CapTreeUpdate

open Dregg2.Circuit.DeployedCapTree (CapLeaf CapHashScheme Cap8Scheme Digest8)
open Dregg2.Circuit.DeployedCapTree.CapHashScheme (MembersAt)
open Dregg2.Circuit.SortedTreeNonMembership
  (keyOf SpineCommits keysOf keysOf_eq_spine sortedInsert mem_sortedInsert sortedInsert_sorted
   update_sound nonMembership_sound GapOpen)
open Dregg2.Crypto.NonMembership (Sorted)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — INSERT (delegate / introduce / grantCap / spawn-handoff): grow the key set by a fresh key.

A thin re-statement of the gadget's `update_sound` as the cap-family INSERT operation: given the OLD
root binds the spine, the inserted key `k` is FRESH (its non-membership, the output of
`nonMembership_sound`), and the NEW root binds `sortedInsert k spine`, the committed key set grows by
EXACTLY `k`. The granted⊑held non-amplification is the SEPARATE submask leg (the attenuate non-amp
tooth); this operation forces only the SET move. -/

/-- **`capInsert_sound` — THE INSERT OPERATION (FORCED key-set move).** Old root binds `spine`, `k` is
fresh, new root binds `sortedInsert k spine` ⟹ `keysOf newRoot = insert k (keysOf oldRoot)` (the
committed key set grows by exactly the fresh key, in sorted order). The cap-family insert (delegate /
introduce / grantCap / spawn-handoff): a new authority edge lands at a fresh slot. -/
theorem capInsert_sound (S8 : Cap8Scheme) (oldRoot newRoot : Digest8) (k : ℤ)
    (spine : List ℤ)
    (hold : SpineCommits S8 oldRoot spine)
    (hfresh : k ∉ keysOf S8 oldRoot)
    (hnew : SpineCommits S8 newRoot (sortedInsert k spine)) :
    ∀ y, y ∈ keysOf S8 newRoot ↔ (y = k ∨ y ∈ keysOf S8 oldRoot) :=
  update_sound S8 oldRoot newRoot k spine hold hfresh hnew

/-! ## §2 — UPDATE-AT-KEY / NARROW (attenuate / delegateAtten / refresh): preserve the key set, move
the leaf value.

The update-at-key operation membership-opens an EXISTING key `k` (the present-key witness) and rebinds
the root at the SAME key spine (the leaf VALUE recomputed with the narrowed rights). The committed KEY
SET is therefore UNCHANGED — the operation edits a leaf in place, it does not add or remove a key. The
present-key membership is the input (`k ∈ keysOf S8 oldRoot`); the new root binding `SpineCommits S
newRoot spine` (the SAME spine) is the recompute output. -/

/-- **`capUpdateAt_sound` — THE UPDATE-AT-KEY OPERATION (FORCED key-set PRESERVATION).** Old root binds
`spine`, the updated key `k` is PRESENT (`k ∈ keysOf S8 oldRoot` — the membership-open witness), and the
NEW root binds the SAME `spine` (the leaf recomputed in place with the narrowed rights). Then the
committed key set is UNCHANGED (`keysOf newRoot = keysOf oldRoot`). The cap-family narrow (attenuate /
delegateAtten / refresh): the key stays; the leaf value (rights) moves. The leaf-VALUE move itself is
the named faithful-encoding residual the consumers carry — this lemma forces the SET preservation. -/
theorem capUpdateAt_sound (S8 : Cap8Scheme) (oldRoot newRoot : Digest8) (k : ℤ)
    (spine : List ℤ)
    (hold : SpineCommits S8 oldRoot spine)
    (hpresent : k ∈ keysOf S8 oldRoot)
    (hnew : SpineCommits S8 newRoot spine) :
    ∀ y, y ∈ keysOf S8 newRoot ↔ y ∈ keysOf S8 oldRoot := by
  intro y
  rw [keysOf_eq_spine S8 newRoot spine hnew, keysOf_eq_spine S8 oldRoot spine hold]

/-- **`capUpdateAt_present` — the updated key is STILL present after the in-place narrow.** The key set
is preserved (`capUpdateAt_sound`), so the narrowed key remains committed (the rights moved, the slot
did not vanish). -/
theorem capUpdateAt_present (S8 : Cap8Scheme) (oldRoot newRoot : Digest8) (k : ℤ)
    (spine : List ℤ)
    (hold : SpineCommits S8 oldRoot spine)
    (hpresent : k ∈ keysOf S8 oldRoot)
    (hnew : SpineCommits S8 newRoot spine) :
    k ∈ keysOf S8 newRoot :=
  (capUpdateAt_sound S8 oldRoot newRoot k spine hold hpresent hnew k).mpr hpresent

/-! ## §3 — REMOVE (revoke / revokeDelegation / revokeCapability): shrink the key set by exactly the key.

The remove operation membership-opens the key `k` and rebinds the root at `sortedRemove k spine` (the
spine with `k` deleted). The committed key set loses EXACTLY `k`. Non-amplification is VACUOUS for a
delete (authority only shrinks). The combinatorial heart — `sortedRemove` preserves sortedness and
shrinks the set by exactly `k` — is proved UNCONDITIONALLY here, mirroring the gadget's `sortedInsert`
lemmas. -/

/-- **`sortedRemove k xs`** — delete `k` from a sorted `ℤ` list (drops every occurrence; in a sorted
list with distinct keys there is at most one). The spine edit a tree remove performs. -/
def sortedRemove (k : ℤ) : List ℤ → List ℤ
  | [] => []
  | x :: t => if x = k then sortedRemove k t else x :: sortedRemove k t

/-- `sortedRemove` REMOVES exactly the key: `y` is in the result iff `y ∈ xs ∧ y ≠ k`. -/
theorem mem_sortedRemove (k : ℤ) (xs : List ℤ) (y : ℤ) :
    y ∈ sortedRemove k xs ↔ (y ∈ xs ∧ y ≠ k) := by
  induction xs with
  | nil => simp [sortedRemove]
  | cons x t ih =>
    unfold sortedRemove
    by_cases hxk : x = k
    · subst hxk
      rw [if_pos rfl, ih]
      simp only [List.mem_cons]
      constructor
      · rintro ⟨hy, hne⟩; exact ⟨Or.inr hy, hne⟩
      · rintro ⟨hy | hy, hne⟩
        · exact absurd hy hne
        · exact ⟨hy, hne⟩
    · rw [if_neg hxk]
      simp only [List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨hy, hne⟩)
        · exact ⟨Or.inl rfl, fun h => hxk h⟩
        · exact ⟨Or.inr hy, hne⟩
      · rintro ⟨hy | hy, hne⟩
        · exact Or.inl hy
        · exact Or.inr ⟨hy, hne⟩

/-- `sortedRemove` keeps the spine SORTED (deleting elements from a strictly-increasing list keeps it
strictly increasing). The structural core of the remove update. -/
theorem sortedRemove_sorted (k : ℤ) (xs : List ℤ) (hs : Sorted xs) :
    Sorted (sortedRemove k xs) := by
  induction xs with
  | nil => simp [sortedRemove, Sorted]
  | cons x t ih =>
    have hst : Sorted t := (List.pairwise_cons.mp hs).2
    have hxt : ∀ y ∈ t, x < y := (List.pairwise_cons.mp hs).1
    unfold sortedRemove
    by_cases hxk : x = k
    · rw [if_pos hxk]; exact ih hst
    · rw [if_neg hxk]
      refine List.pairwise_cons.mpr ⟨?_, ih hst⟩
      intro y hy
      have : y ∈ t := ((mem_sortedRemove k t y).mp hy).1
      exact hxt y this

/-- **`capRemove_sound` — THE REMOVE OPERATION (FORCED key-set move).** Old root binds `spine`, the new
root binds `sortedRemove k spine` (the spine with `k` deleted — the realizing chip recompute on the
sibling path). Then the committed key set loses EXACTLY `k` (`keysOf newRoot = keysOf oldRoot \ {k}`).
The cap-family remove (revoke / revokeDelegation / revokeCapability): an authority edge is torn down.
Non-amplification is vacuous (authority only shrinks). -/
theorem capRemove_sound (S8 : Cap8Scheme) (oldRoot newRoot : Digest8) (k : ℤ)
    (spine : List ℤ)
    (hold : SpineCommits S8 oldRoot spine)
    (hnew : SpineCommits S8 newRoot (sortedRemove k spine)) :
    ∀ y, y ∈ keysOf S8 newRoot ↔ (y ∈ keysOf S8 oldRoot ∧ y ≠ k) := by
  intro y
  rw [keysOf_eq_spine S8 newRoot _ hnew, keysOf_eq_spine S8 oldRoot spine hold, mem_sortedRemove]

/-- **`capRemove_drops_key`** — corollary: after the remove, the deleted key is ABSENT
(`k ∉ keysOf S8 newRoot`). The edge is genuinely gone. -/
theorem capRemove_drops_key (S8 : Cap8Scheme) (oldRoot newRoot : Digest8) (k : ℤ)
    (spine : List ℤ)
    (hold : SpineCommits S8 oldRoot spine)
    (hnew : SpineCommits S8 newRoot (sortedRemove k spine)) :
    k ∉ keysOf S8 newRoot := by
  intro hmem
  exact ((capRemove_sound S8 oldRoot newRoot k spine hold hnew k).mp hmem).2 rfl

/-- **`capRemove_preserves_sorted`** — the new spine the remove commits to is itself sorted (so the
tree stays a sorted-Merkle tree the next open/insert/remove can ride). -/
theorem capRemove_preserves_sorted (S8 : Cap8Scheme) (oldRoot : Digest8) (k : ℤ)
    (spine : List ℤ)
    (hold : SpineCommits S8 oldRoot spine) :
    Sorted (sortedRemove k spine) :=
  sortedRemove_sorted k spine hold.sorted

/-! ## §4 — non-vacuity: the three operations are LOAD-BEARING (the moves are real, not no-ops).

`sortedRemove` shrinks the set by exactly the deleted key; re-removing an absent key is a no-op; the
key set moves observably (insert grows, remove shrinks, update-at-key preserves). A `:= True` or
identity stub would break these `#guard`s. -/

/-- A concrete sorted spine `[10, 20, 30]`. -/
private def demoSpine : List ℤ := [10, 20, 30]

-- REMOVE shrinks the set by exactly the key:
#guard sortedRemove (20 : ℤ) demoSpine == [10, 30]        -- 20 deleted from the middle
#guard sortedRemove (10 : ℤ) demoSpine == [20, 30]        -- the min deleted
#guard sortedRemove (30 : ℤ) demoSpine == [10, 20]        -- the max deleted
-- ...and removing an ABSENT key is a no-op (the set shrinks by at most k):
#guard sortedRemove (25 : ℤ) demoSpine == [10, 20, 30]    -- 25 absent ⇒ unchanged
-- INSERT then REMOVE round-trips (the operations are genuine inverses on the key set):
#guard sortedRemove (25 : ℤ) (sortedInsert (25 : ℤ) demoSpine) == [10, 20, 30]

/-! ## §5 — Axiom hygiene. -/

#assert_axioms capInsert_sound
#assert_axioms capUpdateAt_sound
#assert_axioms capUpdateAt_present
#assert_axioms mem_sortedRemove
#assert_axioms sortedRemove_sorted
#assert_axioms capRemove_sound
#assert_axioms capRemove_drops_key
#assert_axioms capRemove_preserves_sorted

end Dregg2.Circuit.CapTreeUpdate
