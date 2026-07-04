/-
# Dregg2.Circuit.SortedTreeNonMembershipHeap8 — THE Heap8Scheme sorted-Merkle NON-MEMBERSHIP open
  (the accumulator-insert twin of `SortedTreeNonMembership`, over the `Heap8Scheme` node8 lane the
  three DEDICATED accumulator roots — nullifier / commitments / cells — ride).

## Why this file exists (the INSERT-shaped keystone's non-membership half)

`SortedTreeNonMembership.lean` builds the sorted-Merkle non-membership open over `Cap8Scheme` +
`CapLeaf` (keyed by `slot_hash`). The three accumulator roots, however, ride the `Heap8Scheme`
node8 lane (`heapLeafDigest8`/`heapNodeOf8`/`recomposeUp8`/`MembersAt8`, a 2-felt `(addr, value)`
leaf keyed by `addr`), NOT the cap lane — so the cap non-membership does NOT apply verbatim.

This file is the FAITHFUL Heap8 twin: `GapOpen8`/`SpineCommits8`/`keysOf8`/`nonMembership_sound8`/
`update_sound8`, keyed by the heap leaf's `addr` (leaf `.1`). The COMBINATORIAL heart is REUSED
(not re-proved): `Crypto.NonMembership.sorted_gap_excludes` (the adjacent-neighbor bracketing) and
`SortedTreeNonMembership.sortedInsert`/`mem_sortedInsert`/`sortedInsert_sorted` (the fresh-key
splice over `List ℤ`) are both scheme-INDEPENDENT and imported directly. The SOLE new material is
the scheme-specific wrapping over `Heap8Scheme.MembersAt8`.

This is the honest model of the deployed sorted INSERT (`heap_root.rs::CanonicalHeapTree8::
insert_witness`): a FRESH key is spliced into the sorted leaf list — non-membership of the key in
BEFORE (predecessor/successor bracketing), membership of the spliced `(key, value)` leaf in AFTER,
and the set grows by exactly the fresh key (`update_sound8`). NO shared before/after path (the tree
rebuilds); NEVER the update-at-key shared-spine the accumulators are NOT.

## The crypto residue (named precisely, HONEST)

Exactly the same ONE carrier the cap twin names: `SpineCommits8 S8 root spine` — "the sorted key
spine `spine` is what `root` commits to" (the realizable sorted-list↔root binding, the deployed
`compute_canonical_heap_root_8` discipline: the root IS the binary-Merkle fold of the sorted padded
leaf list, whose leaf KEYS are `spine`). It is a HYPOTHESIS, never an axiom; it enters ONLY at the
spine↔root step. The bracketing (`GapOpen8.excludesSpine`) is UNCONDITIONAL combinatorics; the two
neighbor `MembersAt8` openings ride the proven `Heap8Scheme` recompose soundness — no new chip seam.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; `SpineCommits8` is a HYPOTHESIS, never
an axiom; the Poseidon-CR floor enters only through the `Heap8Scheme` node8 carrier already in play.
-/
import Dregg2.Circuit.SortedTreeNonMembership
import Dregg2.Circuit.DeployedHeapTree

namespace Dregg2.Circuit.SortedTreeNonMembershipHeap8

open Dregg2.Circuit.DeployedCapTree (Digest8)
open Dregg2.Circuit.DeployedHeapTree (Heap8Scheme)
open Dregg2.Circuit.DeployedHeapTree.Heap8Scheme (MembersAt8)
open Dregg2.Crypto.NonMembership (Sorted Adjacent sorted_gap_excludes head_lt_of_sorted)
open Dregg2.Circuit.SortedTreeNonMembership (sortedInsert mem_sortedInsert sortedInsert_sorted)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — the sort key + the committed key spine (over the heap leaf `addr`). -/

/-- **`keyOfH e`** — the sort key of a heap leaf: its `addr` (`e.1`), the sorted-position key of the
`Heap8Scheme` binary-Merkle fold (`heap_root.rs::HeapLeaf::addr`). -/
def keyOfH (e : ℤ × ℤ) : ℤ := e.1

/-- **`SpineCommits8 S8 root spine`** — the (named, realizable) binding: the sorted key spine `spine`
is what the 8-felt heap `root` commits to. Concretely: `spine` is the sorted list of `addr` keys of
the leaf set whose depth binary-Merkle fold (`recomposeUp8`/`MembersAt8`) is `root`, AND every present
leaf opens at a key in `spine` while every key in `spine` is opened by a present leaf. The deployed
`compute_canonical_heap_root_8` discipline. A HYPOTHESIS, never an axiom — the Heap8 twin of
`SortedTreeNonMembership.SpineCommits`. -/
structure SpineCommits8 (S8 : Heap8Scheme) (root : Digest8) (spine : List ℤ) : Prop where
  /-- The committed key spine is strictly increasing (sorted-by-`addr`). -/
  sorted : Sorted spine
  /-- The root binds the spine: a leaf opens at key `k` IFF `k` is a spine key. -/
  present_iff : ∀ k : ℤ, (∃ e : ℤ × ℤ, keyOfH e = k ∧ MembersAt8 S8 root e) ↔ k ∈ spine

/-- **`keysOf8 S8 root`** — the committed key set of the 8-felt heap tree at `root`: the keys at which
a leaf opens. The non-membership target. -/
def keysOf8 (S8 : Heap8Scheme) (root : Digest8) : Set ℤ :=
  { k | ∃ e : ℤ × ℤ, keyOfH e = k ∧ MembersAt8 S8 root e }

/-- Under `SpineCommits8`, the abstract committed key set IS the spine (membership coincide). -/
theorem keysOf8_eq_spine (S8 : Heap8Scheme) (root : Digest8) (spine : List ℤ)
    (hc : SpineCommits8 S8 root spine) : ∀ k, k ∈ keysOf8 S8 root ↔ k ∈ spine :=
  fun k => hc.present_iff k

/-! ## §1 — the covering-gap open (the four non-membership shapes, over DEPLOYED `MembersAt8` openings). -/

/-- **`GapOpen8 S8 root k`** — a non-membership covering-gap open for key `k` against the 8-felt heap
tree at `root`. Each present-neighbor is a DEPLOYED `MembersAt8` opening; the gap shape says where `k`
sits relative to the present neighbors. The witness a `Satisfied2` non-membership row produces. The
Heap8 twin of `SortedTreeNonMembership.GapOpen`. -/
inductive GapOpen8 (S8 : Heap8Scheme) (root : Digest8) (k : ℤ) where
  /-- The tree is EMPTY (the spine is `[]`): everything is absent. -/
  | empty
  /-- `k` is BELOW the minimum present key: the head leaf `b` opens with `k < keyOfH b`. -/
  | below (b : ℤ × ℤ) (hopen : MembersAt8 S8 root b) (hlt : k < keyOfH b)
  /-- `k` is strictly BETWEEN two ADJACENT present neighbors `a`, `b` (the predecessor/successor
  bracketing — the accumulator-insert non-membership heart). -/
  | inner (a b : ℤ × ℤ) (hoa : MembersAt8 S8 root a) (hob : MembersAt8 S8 root b)
      (hlo : keyOfH a < k) (hhi : k < keyOfH b)
  /-- `k` is ABOVE the maximum present key: the last leaf `a` opens with `keyOfH a < k`. -/
  | above (a : ℤ × ℤ) (hopen : MembersAt8 S8 root a) (hgt : keyOfH a < k)

namespace GapOpen8

variable {S8 : Heap8Scheme} {root : Digest8} {k : ℤ}

/-- **`coversSpine g spine`** — the gap's claim is VALID against the committed key spine. -/
def coversSpine : GapOpen8 S8 root k → List ℤ → Prop
  | .empty, spine => spine = []
  | .below b _ _, spine => spine.head? = some (keyOfH b)
  | .inner a b _ _ _ _, spine => Adjacent spine (keyOfH a) (keyOfH b)
  | .above a _ _, spine => spine.getLast? = some (keyOfH a)

/-- **`GapOpen8.excludesSpine` — THE COMBINATORIAL KEYSTONE.** A gap open valid against the SORTED
spine proves `k ∉ spine`: the `inner` case is LITERALLY `sorted_gap_excludes`; the boundary cases ride
the same strict order. UNCONDITIONAL — no crypto. Verbatim the cap twin, over `Heap8Scheme`. -/
theorem excludesSpine (g : GapOpen8 S8 root k) {spine : List ℤ}
    (hs : Sorted spine) (hv : g.coversSpine spine) : k ∉ spine := by
  cases g with
  | empty =>
    simp only [coversSpine] at hv; subst hv; simp
  | below b _ hlt =>
    simp only [coversSpine] at hv
    cases spine with
    | nil => simp
    | cons x t =>
      have hx : x = keyOfH b := by simpa using hv
      subst hx
      intro hmem
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact absurd hlt (lt_irrefl _)
      · exact absurd ((head_lt_of_sorted hs k htail).trans hlt) (lt_irrefl _)
  | inner a b _ _ hlo hhi =>
    simp only [coversSpine] at hv
    exact sorted_gap_excludes spine (keyOfH a) (keyOfH b) k hs hv hlo hhi
  | above a _ hgt =>
    simp only [coversSpine] at hv
    obtain ⟨pre, rfl⟩ := List.getLast?_eq_some_iff.mp hv
    intro hmem
    rcases List.mem_append.mp hmem with hpre | hlast
    · have hlt : k < keyOfH a := (List.pairwise_append.mp hs).2.2 k hpre (keyOfH a) (by simp)
      exact absurd (hlt.trans hgt) (lt_irrefl _)
    · rw [List.mem_singleton.mp hlast] at hgt
      exact absurd hgt (lt_irrefl _)

end GapOpen8

/-! ## §2 — THE KEYSTONE: `nonMembership_sound8` (a valid gap open ⟹ `k ∉ keysOf8 root`). -/

/-- **`nonMembership_sound8` — THE KEYSTONE.** Given the (realizable) spine↔root binding
`SpineCommits8` and a gap open VALID against that spine, the queried key `k` is ABSENT from the
committed 8-felt heap tree (`k ∉ keysOf8 S8 root`). The Heap8 twin of the cap `nonMembership_sound`. -/
theorem nonMembership_sound8 (S8 : Heap8Scheme) (root : Digest8) (k : ℤ)
    (spine : List ℤ) (hc : SpineCommits8 S8 root spine)
    (g : GapOpen8 S8 root k) (hv : g.coversSpine spine) :
    k ∉ keysOf8 S8 root := by
  have habsent : k ∉ spine := g.excludesSpine hc.sorted hv
  intro hmem
  exact habsent ((keysOf8_eq_spine S8 root spine hc k).mp hmem)

/-! ## §3 — the in-row UPDATE (`update_sound8`): the fresh-key insert binds the new root. -/

/-- **`update_sound8` — THE IN-ROW INSERT KEYSTONE.** Given the OLD root binds the sorted spine, `k`
is FRESH (non-membership over the OLD root), and the NEW root binds the INSERTED spine
(`sortedInsert k spine` — the realizing chip recompose, the deployed `insert_witness` fold), the new
committed key set is EXACTLY the old set plus `k`. The insert is FAITHFUL: it grows the set by exactly
the fresh key, in sorted order. The Heap8 twin of the cap `update_sound`, reusing `mem_sortedInsert`. -/
theorem update_sound8 (S8 : Heap8Scheme) (oldRoot newRoot : Digest8) (k : ℤ)
    (spine : List ℤ)
    (hold : SpineCommits8 S8 oldRoot spine)
    (hfresh : k ∉ keysOf8 S8 oldRoot)
    (hnew : SpineCommits8 S8 newRoot (sortedInsert k spine)) :
    ∀ y, y ∈ keysOf8 S8 newRoot ↔ (y = k ∨ y ∈ keysOf8 S8 oldRoot) := by
  intro y
  rw [keysOf8_eq_spine S8 newRoot _ hnew, keysOf8_eq_spine S8 oldRoot spine hold,
      mem_sortedInsert]

/-- **`update_preserves_sorted8`** — corollary: the new spine the insert commits to is itself sorted
(so the tree stays a sorted-Merkle tree the next open/insert can ride). -/
theorem update_preserves_sorted8 (S8 : Heap8Scheme) (oldRoot : Digest8) (k : ℤ)
    (spine : List ℤ)
    (hold : SpineCommits8 S8 oldRoot spine) (hfresh : k ∉ spine) :
    Sorted (sortedInsert k spine) :=
  sortedInsert_sorted k spine hold.sorted hfresh

#assert_axioms keysOf8_eq_spine
#assert_axioms GapOpen8.excludesSpine
#assert_axioms nonMembership_sound8
#assert_axioms update_sound8
#assert_axioms update_preserves_sorted8

/-! ## §4 — NON-VACUITY: the gap open is load-bearing (witness TRUE and FALSE). -/

/-- A concrete sorted spine over `ℤ`: `[10, 20, 30]`. -/
private def demoSpine : List ℤ := [10, 20, 30]

private theorem demoSpine_sorted : Sorted demoSpine := by
  simp [demoSpine, Sorted, List.pairwise_cons]

/-- `20` and `30` are adjacent in the spine. -/
private theorem demoSpine_adjacent : Adjacent demoSpine 20 30 := ⟨[10], [], rfl⟩

/-- **Witness TRUE — the bracketing EXCLUDES `25`.** -/
private theorem demo_excludes_25 : (25 : ℤ) ∉ demoSpine :=
  sorted_gap_excludes demoSpine 20 30 25 demoSpine_sorted demoSpine_adjacent
    (by norm_num) (by norm_num)

-- ANTI-GHOST: a PRESENT key (20) is in the spine — no valid gap can exclude it.
#guard decide ((20 : ℤ) ∈ demoSpine)
#guard decide ((25 : ℤ) ∈ demoSpine) == false

-- The INSERT grows the set by exactly the fresh key, in sorted order:
#guard sortedInsert (25 : ℤ) demoSpine == [10, 20, 25, 30]
#guard sortedInsert (5 : ℤ) demoSpine == [5, 10, 20, 30]
#guard sortedInsert (40 : ℤ) demoSpine == [10, 20, 30, 40]
-- ...and re-inserting a PRESENT key is a no-op (the set grows by at most k):
#guard sortedInsert (20 : ℤ) demoSpine == [10, 20, 30]

end Dregg2.Circuit.SortedTreeNonMembershipHeap8
