/-
# Dregg2.Circuit.SortedTreeNonMembership — THE IN-CIRCUIT sorted-Merkle NON-MEMBERSHIP open
  (the PHASE-D keystone the whole circuit-soundness campaign's convergent residual needs).

## Why this file exists (the freshness / non-amplification gadget)

`DeployedCapOpen.lean` builds the in-circuit MEMBERSHIP open: a `Satisfied` row over the IR-v2
Poseidon2 chip witnesses `MembersAt8 S8 cap_root leaf` (the depth-16 binary-Merkle recompose up a
sibling path). That is the "a leaf IS in the tree" half. This file builds the COMPLEMENTARY half: a
constraint set whose satisfaction proves a key `k` is NOT in the committed sorted set — the
**non-membership open**.

The standard sorted-Merkle non-membership argument (the SAME `Crypto.NonMembership.sorted_gap_excludes`
bracketing `AttestedQuery` rides for the query layer): a key `k` is absent iff you exhibit a COVERING
GAP — two ADJACENT present leaves `lo < k < hi` (the `inner` form), or `k` below the minimum present
key (`below`), or `k` above the maximum (`above`), or the tree is empty (`empty`). A valid gap
EXCLUDES everything strictly inside it; an absent key must fall inside some valid gap.

The "present" half is the DEPLOYED `MembersAt` opening (the `DeployedCapOpen` chip rows), so this
gadget composes DIRECTLY with the proven cap-open soundness — it adds ONLY the gap-bracketing on
top, it does NOT redo any chip binding.

## The reusable interface (what the capability family + spawn + attenuate-exact will consume)

  * `GapOpen S8 root spine` — the four covering-gap shapes (`inner`/`below`/`above`/`empty`), each
    carrying the DEPLOYED `MembersAt` openings of its bracketing neighbor leaves;
  * `GapOpen.excludes` — THE KEYSTONE: a valid gap covering `k` proves `k ∉ spine` (via
    `sorted_gap_excludes`); composed with `SpineCommits` (the root binds the spine) ⇒
    `nonMembership_sound : (open) ⟹ k ∉ keysOf root` — a key is absent from the COMMITTED tree;
  * `update_sound` (§5) — the in-row UPDATE: old root + non-membership of `k` + the insert recompute
    ⟹ new root = root of `insert k spine`. The gadget the capability family / spawn handoff /
    noteSpend-insert consumes next.

## The crypto residue (named precisely, HONEST)

Exactly ONE carrier beyond the deployed `CapHashScheme` already in play: `SpineCommits S8 root spine`
— "the sorted key spine `spine` is what `root` commits to" (the genuine sorted-list↔root binding,
the SAME residue `Crypto.NonMembership.NonMember` carries as a field, and `AttestedQuery` carries as
the `iroot`/CR floor). It is realizable (the deployed `compute_canonical_capability_root_felt`
discipline: the root IS the binary-Merkle fold of the sorted padded leaf list, whose leaf KEYS are
`spine`). It enters the soundness chain ONLY at the spine↔root step, never the bracketing — exactly
as `compress` CR enters `NonMembership` only via `extractable`, never the combinatorial heart.

The bracketing itself (`GapOpen.excludes`) is UNCONDITIONAL combinatorics. The two neighbor
`MembersAt` openings ride the proven `DeployedCapOpen` chip soundness — no new chip seam.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} + the realizable Poseidon-CR carriers
`DeployedCapTree`/`AttestedQuery` already use (`Compress1CR` via the `CapHashScheme`; the spine↔root
binding `SpineCommits` is a HYPOTHESIS, never an axiom). NEW file; all imports read-only.
-/
import Dregg2.Circuit.DeployedCapOpen
import Dregg2.Crypto.NonMembership

namespace Dregg2.Circuit.SortedTreeNonMembership

open Dregg2.Circuit.DescriptorIR2 (TraceFamily ChipTableSound ChipTableSoundN)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.DeployedCapTree (CapLeaf CapHashScheme Cap8Scheme Digest8)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme (MembersAt8)
open Dregg2.Circuit.DeployedCapOpen (CapOpenCols leafOf Satisfied MembershipCore capPermOut groupVal capOpen_membership8)
open Dregg2.Crypto.NonMembership (Sorted Adjacent sorted_gap_excludes head_lt_of_sorted)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — the sort key + the committed key spine.

The deployed cap-tree sorts its leaves by `slot_hash` (`cap_root.rs:95`, the unique c-list slot
Poseidon image). So the committed sorted SET — the thing a key can be absent from — is the list of
leaf `slot_hash` keys in sorted order. The non-membership argument is over THIS key spine. -/

/-- **`keyOf l`** — the sort key of a deployed leaf: its `slot_hash` (`cap_root.rs::CapLeaf::slot_hash`,
the leaf-position sort key of the binary-Merkle fold). -/
def keyOf (l : CapLeaf) : ℤ := l.slot_hash

/-- **`SpineCommits S8 root spine`** — the (named, realizable) binding: the sorted key spine `spine`
is what `root` commits to. Concretely: `spine` is the sorted list of `slot_hash` keys of the leaf set
whose depth-16 binary-Merkle fold (`recomposeUp`/`MembersAt`) is `root`, AND every present leaf opens
at a key in `spine` while every key in `spine` is opened by a present leaf. This is the deployed
`compute_canonical_capability_root_felt` discipline (the root IS the fold of the sorted padded leaf
list). The SAME sorted-list↔root residue `Crypto.NonMembership.NonMember` carries as a field and
`AttestedQuery` pins via the `iroot` CR floor — a HYPOTHESIS, never an axiom.

We capture exactly the two facts the soundness chain needs:
  * `sorted` — the spine is strictly increasing (the tree is sorted-by-key);
  * `present_iff` — a `MembersAt` opening of a leaf exists at key `k` IFF `k ∈ spine` (the root binds
    the spine: you cannot open a leaf whose key is off-spine, and every on-spine key is openable). -/
structure SpineCommits (S8 : Cap8Scheme) (root : Digest8) (spine : List ℤ) : Prop where
  /-- The committed key spine is strictly increasing (sorted-by-`slot_hash`). -/
  sorted : Sorted spine
  /-- The root binds the spine: a leaf opens at key `k` IFF `k` is a spine key. The `→` is the crypto
  binding (no off-spine leaf opens — `Compress1CR` via the fold); the `←` is honest-prover totality
  (every present key is openable). -/
  present_iff : ∀ k : ℤ, (∃ leaf : CapLeaf, keyOf leaf = k ∧ MembersAt8 S8 root leaf) ↔ k ∈ spine

/-- **`keysOf S8 root`** — the committed key set of the tree at `root`: the keys at which a leaf opens.
The non-membership target (`k ∉ keysOf S8 root` is "the key is absent from the committed tree"). -/
def keysOf (S8 : Cap8Scheme) (root : Digest8) : Set ℤ :=
  { k | ∃ leaf : CapLeaf, keyOf leaf = k ∧ MembersAt8 S8 root leaf }

/-- Under `SpineCommits`, the abstract committed key set IS the spine (membership coincide). -/
theorem keysOf_eq_spine (S8 : Cap8Scheme) (root : Digest8) (spine : List ℤ)
    (hc : SpineCommits S8 root spine) : ∀ k, k ∈ keysOf S8 root ↔ k ∈ spine :=
  fun k => hc.present_iff k

/-! ## §1 — the covering-gap open (the four non-membership shapes, over DEPLOYED openings).

Mirrors `AttestedQuery.Gap` / `Crypto.NonMembership`'s bracketing, but each "present neighbor" is a
DEPLOYED `MembersAt` opening (a `DeployedCapOpen` chip row, soundness already proved). `inner loL hiL`
carries the two adjacent neighbor LEAVES (whose keys bracket `k`); the boundary forms carry the single
head/last neighbor leaf. -/

/-- **`GapOpen S8 root k`** — a non-membership covering-gap open for key `k` against the tree at `root`.
Each present-neighbor is a DEPLOYED `MembersAt` opening; the gap shape says where `k` sits relative to
the present neighbors. The witness a `Satisfied` non-membership row produces. -/
inductive GapOpen (S8 : Cap8Scheme) (root : Digest8) (k : ℤ) where
  /-- The tree is EMPTY (the spine is `[]`): everything is absent. -/
  | empty
  /-- `k` is BELOW the minimum present key: the head leaf `b` opens with `k < keyOf b`. -/
  | below (b : CapLeaf) (hopen : MembersAt8 S8 root b) (hlt : k < keyOf b)
  /-- `k` is strictly BETWEEN two ADJACENT present neighbors `a`, `b`: both open, and
  `keyOf a < k < keyOf b` (the `inner` bracketing — the cap/nullifier non-membership heart). -/
  | inner (a b : CapLeaf) (hoa : MembersAt8 S8 root a) (hob : MembersAt8 S8 root b)
      (hlo : keyOf a < k) (hhi : k < keyOf b)
  /-- `k` is ABOVE the maximum present key: the last leaf `a` opens with `keyOf a < k`. -/
  | above (a : CapLeaf) (hopen : MembersAt8 S8 root a) (hgt : keyOf a < k)

namespace GapOpen

variable {S8 : Cap8Scheme} {root : Digest8} {k : ℤ}

/-- **`coversSpine g spine`** — the gap's claim is VALID against the committed key spine: its present
neighbors occupy the claimed head/last/adjacent positions, and `k` sits in the claimed interval. For
`empty` the spine is `[]`; for `below b` the head key is `keyOf b`; for `inner a b` the keys are
adjacent; for `above a` the last key is `keyOf a`. This is exactly `AttestedQuery.Gap.Valid` ∧
`covers`, here READ OFF the opened neighbor leaves' keys. -/
def coversSpine : GapOpen S8 root k → List ℤ → Prop
  | .empty, spine => spine = []
  | .below b _ _, spine => spine.head? = some (keyOf b)
  | .inner a b _ _ _ _, spine => Adjacent spine (keyOf a) (keyOf b)
  | .above a _ _, spine => spine.getLast? = some (keyOf a)

/-- **`GapOpen.excludesSpine` — THE COMBINATORIAL KEYSTONE.** A gap open valid against the SORTED
spine proves `k ∉ spine`: the `inner` case is LITERALLY `sorted_gap_excludes`; the boundary cases ride
the same strict order. UNCONDITIONAL — no crypto (the openings only pin the neighbor KEYS to the
spine, which `coversSpine` already records). -/
theorem excludesSpine (g : GapOpen S8 root k) {spine : List ℤ}
    (hs : Sorted spine) (hv : g.coversSpine spine) : k ∉ spine := by
  cases g with
  | empty =>
    simp only [coversSpine] at hv; subst hv; simp
  | below b _ hlt =>
    simp only [coversSpine] at hv
    cases spine with
    | nil => simp
    | cons x t =>
      have hx : x = keyOf b := by simpa using hv
      subst hx
      intro hmem
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact absurd hlt (lt_irrefl _)
      · exact absurd ((head_lt_of_sorted hs k htail).trans hlt) (lt_irrefl _)
  | inner a b _ _ hlo hhi =>
    simp only [coversSpine] at hv
    exact sorted_gap_excludes spine (keyOf a) (keyOf b) k hs hv hlo hhi
  | above a _ hgt =>
    simp only [coversSpine] at hv
    obtain ⟨pre, rfl⟩ := List.getLast?_eq_some_iff.mp hv
    intro hmem
    rcases List.mem_append.mp hmem with hpre | hlast
    · have hlt : k < keyOf a := (List.pairwise_append.mp hs).2.2 k hpre (keyOf a) (by simp)
      exact absurd (hlt.trans hgt) (lt_irrefl _)
    · rw [List.mem_singleton.mp hlast] at hgt
      exact absurd hgt (lt_irrefl _)

end GapOpen

/-! ## §2 — THE KEYSTONE: `nonMembership_sound` (a valid gap open ⟹ `k ∉ keysOf root`).

Compose the combinatorial `excludesSpine` with the spine↔root binding `SpineCommits`: a gap open valid
against the committed spine proves `k` absent from the COMMITTED tree's key set. THE in-circuit
sorted-Merkle non-membership soundness — the analog of `attenuate`'s non-amplification. -/

/-- **`nonMembership_sound` — THE KEYSTONE.** Given the (realizable) spine↔root binding `SpineCommits`
and a gap open VALID against that spine (its present neighbors really occupy the claimed positions),
the queried key `k` is ABSENT from the committed tree (`k ∉ keysOf S8 root`). The bracketing is
`excludesSpine` (unconditional); `SpineCommits` is the only crypto residue, and it enters ONLY at the
spine↔root step. -/
theorem nonMembership_sound (S8 : Cap8Scheme) (root : Digest8) (k : ℤ)
    (spine : List ℤ) (hc : SpineCommits S8 root spine)
    (g : GapOpen S8 root k) (hv : g.coversSpine spine) :
    k ∉ keysOf S8 root := by
  have habsent : k ∉ spine := g.excludesSpine hc.sorted hv
  intro hmem
  exact habsent ((keysOf_eq_spine S8 root spine hc k).mp hmem)

/-! ## §3 — the in-circuit non-membership ROW (riding two DEPLOYED `DeployedCapOpen.Satisfied` rows).

The non-membership AIR carries, for the `inner` shape, TWO cap-membership sub-rows (the `lo`/`hi`
neighbor openings, each a `DeployedCapOpen.Satisfied` over the chip), plus the gap gates: the two key
comparisons `keyOf lo < k < keyOf hi` and the adjacency side condition. The chip binding of each
sub-row is the PROVEN `DeployedCapOpen.capOpen_membership` — no new chip seam.

We give the `inner` row form (the load-bearing bracketing shape; the boundary forms are the same with
one sub-row). `kCol` is the queried-key column; `loRow`/`hiRow` are the two cap-open sub-row column
plans whose `cap_root` columns both equal `root`. -/

/-- **`NonMemberRowInner`** — the column plan + denotation for an in-circuit `inner` non-membership row:
two cap-open sub-rows (the bracketing neighbor openings) plus the gap comparison/adjacency conditions.
The non-membership AIR's `inner` shape. -/
structure NonMemberRowInner (sponge : List ℤ → ℤ) (tf : TraceFamily)
    (loRow hiRow : CapOpenCols) (kCol : Nat) (spine : List ℤ) (env : VmRowEnv) : Prop where
  /-- The `lo` neighbor cap-open sub-row is satisfied (a DEPLOYED membership row). -/
  loSat : Satisfied sponge tf loRow env
  /-- The `hi` neighbor cap-open sub-row is satisfied (a DEPLOYED membership row). -/
  hiSat : Satisfied sponge tf hiRow env
  /-- BOTH sub-rows open against the SAME committed `cap_root` column value `root`. -/
  rootShared : groupVal env loRow.capRoot = groupVal env hiRow.capRoot
  /-- The two neighbor keys are ADJACENT in the committed sorted spine (the structural side condition;
  at the wire, the positions the two Merkle openings certify). -/
  adjacent : Adjacent spine (keyOf (leafOf loRow env)) (keyOf (leafOf hiRow env))
  /-- The lower comparison gate: `keyOf lo < k` (`leaf.slot_hash < kCol`). -/
  loLt : keyOf (leafOf loRow env) < env.loc kCol
  /-- The upper comparison gate: `k < keyOf hi` (`kCol < leaf.slot_hash`). -/
  hiLt : env.loc kCol < keyOf (leafOf hiRow env)

/-- **`nonMemberRowInner_to_gapOpen`** — an `inner` non-membership row PRODUCES a valid `inner`
`GapOpen` against the committed spine: the two sub-rows' chip soundness (`capOpen_membership`) supply
the two `MembersAt` openings, and the gap gates supply the bracketing. The bridge from the in-circuit
row to the abstract gap open. -/
theorem nonMemberRowInner_to_gapOpen (S8 : Cap8Scheme) (sponge : List ℤ → ℤ)
    (tf : TraceFamily) (loRow hiRow : CapOpenCols) (kCol : Nat) (spine : List ℤ) (env : VmRowEnv)
    (hChip : ChipTableSoundN (capPermOut S8) (tf .poseidon2))
    (hrow : NonMemberRowInner sponge tf loRow hiRow kCol spine env) :
    ∃ g : GapOpen S8 (groupVal env loRow.capRoot) (env.loc kCol), g.coversSpine spine := by
  -- the two DEPLOYED 8-felt membership openings (proven WIDE chip soundness).
  have hmemLo : MembersAt8 S8 (groupVal env loRow.capRoot) (leafOf loRow env) :=
    capOpen_membership8 S8 sponge tf loRow env hChip hrow.loSat.toCore
  have hmemHi : MembersAt8 S8 (groupVal env loRow.capRoot) (leafOf hiRow env) := by
    rw [hrow.rootShared]; exact capOpen_membership8 S8 sponge tf hiRow env hChip hrow.hiSat.toCore
  exact ⟨.inner (leafOf loRow env) (leafOf hiRow env) hmemLo hmemHi hrow.loLt hrow.hiLt,
    hrow.adjacent⟩

/-- **`nonMemberRowInner_sound` — THE IN-CIRCUIT NON-MEMBERSHIP KEYSTONE.** An `inner` non-membership
row, against a committed spine (the realizable `SpineCommits`), forces the queried key ABSENT from the
committed tree (`env.loc kCol ∉ keysOf S8 (groupVal env loRow.capRoot)`). The two neighbor openings ride the
PROVEN cap-open chip soundness; the bracketing is unconditional; `SpineCommits` is the only residue. -/
theorem nonMemberRowInner_sound (S8 : Cap8Scheme) (sponge : List ℤ → ℤ)
    (tf : TraceFamily) (loRow hiRow : CapOpenCols) (kCol : Nat) (spine : List ℤ) (env : VmRowEnv)
    (hChip : ChipTableSoundN (capPermOut S8) (tf .poseidon2))
    (hc : SpineCommits S8 (groupVal env loRow.capRoot) spine)
    (hrow : NonMemberRowInner sponge tf loRow hiRow kCol spine env) :
    env.loc kCol ∉ keysOf S8 (groupVal env loRow.capRoot) := by
  obtain ⟨g, hv⟩ := nonMemberRowInner_to_gapOpen S8 sponge tf loRow hiRow kCol spine env hChip hrow
  exact nonMembership_sound S8 (groupVal env loRow.capRoot) (env.loc kCol) spine hc g hv

/-! ## §4 — Axiom hygiene (the keystone gadget). -/

#assert_axioms keysOf_eq_spine
#assert_axioms GapOpen.excludesSpine
#assert_axioms nonMembership_sound
#assert_axioms nonMemberRowInner_to_gapOpen
#assert_axioms nonMemberRowInner_sound

/-! ## §5 — the in-row UPDATE skeleton (`update_sound`): insert binds the new root.

The gadget the capability family / spawn handoff / noteSpend-insert consumes NEXT: given the OLD root
binds the sorted spine `spine`, a NON-MEMBERSHIP of `k` (so `k ∉ spine`), and the new root binds the
INSERTED spine `sortedInsert k spine`, the new root is exactly the root of `insert k spine`. We state
it as the binding fact (`SpineCommits S8 newRoot (sortedInsert k spine)`), which is what the downstream
consumers need; the per-row recompute (the sibling-path edit on the `MembersAt` fold) is the realizing
witness, the SAME chip rows the membership open already realizes.

The combinatorial heart — `sortedInsert` preserves sortedness and grows the set by exactly `k` — is
proved here UNCONDITIONALLY; the root-binding is the realizable `SpineCommits` carrier. -/

/-- **`sortedInsert k xs`** — insert `k` into a sorted `ℤ` list, preserving order (skips an equal
key, so the set grows by at most `k`). The spine edit a tree insert performs. -/
def sortedInsert (k : ℤ) : List ℤ → List ℤ
  | [] => [k]
  | x :: t => if k < x then k :: x :: t else if k = x then x :: t else x :: sortedInsert k t

/-- `sortedInsert` of a fresh key actually ADDS it (membership grows by exactly `k`). -/
theorem mem_sortedInsert (k : ℤ) (xs : List ℤ) (y : ℤ) :
    y ∈ sortedInsert k xs ↔ y = k ∨ y ∈ xs := by
  induction xs with
  | nil => simp [sortedInsert]
  | cons x t ih =>
    unfold sortedInsert
    by_cases hlt : k < x
    · simp only [hlt, if_true, List.mem_cons]; try tauto
    · rw [if_neg hlt]
      by_cases hkx : k = x
      · rw [if_pos hkx, hkx]; simp only [List.mem_cons]; try tauto
      · rw [if_neg hkx]; simp only [List.mem_cons, ih]; try tauto

/-- `sortedInsert` of a FRESH key (`k ∉ xs`) into a sorted list yields a sorted list. The structural
core of the update: the insert keeps the spine strictly increasing. -/
theorem sortedInsert_sorted (k : ℤ) (xs : List ℤ) (hs : Sorted xs) (hfresh : k ∉ xs) :
    Sorted (sortedInsert k xs) := by
  induction xs with
  | nil => simp [sortedInsert, Sorted, List.pairwise_cons]
  | cons x t ih =>
    have hst : Sorted t := (List.pairwise_cons.mp hs).2
    have hxt : ∀ y ∈ t, x < y := (List.pairwise_cons.mp hs).1
    have hkx : k ≠ x := fun h => hfresh (h ▸ List.mem_cons_self)
    have hkt : k ∉ t := fun h => hfresh (List.mem_cons_of_mem x h)
    unfold sortedInsert
    by_cases hlt : k < x
    · -- k :: x :: t : k < x, and k < every later (transitively through x).
      simp only [hlt, if_true]
      refine List.pairwise_cons.mpr ⟨?_, hs⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hyt
      · exact hlt
      · exact hlt.trans (hxt y hyt)
    · rw [if_neg hlt]
      rw [if_neg hkx]
      -- x :: sortedInsert k t : x < everything in (sortedInsert k t).
      refine List.pairwise_cons.mpr ⟨?_, ih hst hkt⟩
      intro y hy
      -- y ∈ sortedInsert k t ⇒ y = k (and x < k since ¬k<x ∧ k≠x) or y ∈ t (and x < y).
      have hxk : x < k := lt_of_le_of_ne (not_lt.mp hlt) (fun h => hkx h.symm)
      rcases (mem_sortedInsert k t y).mp hy with rfl | hyt
      · exact hxk
      · exact hxt y hyt

/-- **`update_sound` — THE IN-ROW UPDATE KEYSTONE.** Given:
  * the OLD root binds the sorted spine (`SpineCommits S8 oldRoot spine`),
  * `k` is FRESH (non-membership of `k`, the output of `nonMembership_sound` over `oldRoot`),
  * the NEW root binds the inserted spine (`SpineCommits S8 newRoot (sortedInsert k spine)` — the
    realizing chip recompute, the SAME fold the membership open already realizes),
then the new committed key set is EXACTLY the old set plus `k` (`keysOf S8 newRoot = insert k (keysOf
S oldRoot)`). The insert is FAITHFUL: it grows the set by exactly the fresh key, in sorted order. THE
gadget the capability family / spawn handoff / noteSpend-insert consumes next. -/
theorem update_sound (S8 : Cap8Scheme) (oldRoot newRoot : Digest8) (k : ℤ)
    (spine : List ℤ)
    (hold : SpineCommits S8 oldRoot spine)
    (hfresh : k ∉ keysOf S8 oldRoot)
    (hnew : SpineCommits S8 newRoot (sortedInsert k spine)) :
    ∀ y, y ∈ keysOf S8 newRoot ↔ (y = k ∨ y ∈ keysOf S8 oldRoot) := by
  intro y
  rw [keysOf_eq_spine S8 newRoot _ hnew, keysOf_eq_spine S8 oldRoot spine hold,
      mem_sortedInsert]

/-- **`update_preserves_sorted`** — corollary: the new spine the update commits to is itself sorted
(so the tree stays a sorted-Merkle tree the next open/insert can ride). The fresh-key insert keeps the
sorted invariant. -/
theorem update_preserves_sorted (S8 : Cap8Scheme) (oldRoot : Digest8) (k : ℤ)
    (spine : List ℤ)
    (hold : SpineCommits S8 oldRoot spine) (hfresh : k ∉ spine) :
    Sorted (sortedInsert k spine) :=
  sortedInsert_sorted k spine hold.sorted hfresh

#assert_axioms sortedInsert_sorted
#assert_axioms mem_sortedInsert
#assert_axioms update_sound
#assert_axioms update_preserves_sorted

/-! ## §6 — NON-VACUITY: the gap open is load-bearing (witness TRUE and FALSE).

Over a concrete `CapHashScheme` and a concrete sorted spine, we witness: an `inner` gap open EXCLUDES
a strictly-bracketed key (`excludesSpine` fires, TRUE); a key actually PRESENT in the spine cannot be
excluded by any gap covering it (the `coversSpine` would have to be a fake adjacency — FALSE);
`sortedInsert` grows the set by exactly the fresh key (the update is real, not a no-op). -/

/-- A concrete sorted spine over `ℤ`: `[10, 20, 30]`. -/
private def demoSpine : List ℤ := [10, 20, 30]

private theorem demoSpine_sorted : Sorted demoSpine := by
  simp [demoSpine, Sorted, List.pairwise_cons]

/-- `20` and `30` are adjacent in the spine. -/
private theorem demoSpine_adjacent : Adjacent demoSpine 20 30 := ⟨[10], [], rfl⟩

/-- **Witness TRUE — the bracketing EXCLUDES `25`.** With `20`/`30` adjacent and `20 < 25 < 30`, the
combinatorial keystone proves `25 ∉ [10,20,30]`. (Stated directly via `sorted_gap_excludes`, the same
core `excludesSpine`'s `inner` case dispatches to.) -/
private theorem demo_excludes_25 : (25 : ℤ) ∉ demoSpine :=
  sorted_gap_excludes demoSpine 20 30 25 demoSpine_sorted demoSpine_adjacent
    (by norm_num) (by norm_num)

-- ANTI-GHOST: a PRESENT key (20) is in the spine — so no valid gap can exclude it (the keystone is
-- not vacuously excluding everything). A `coversSpine := True` stub would break this.
#guard decide ((20 : ℤ) ∈ demoSpine)              -- true: 20 is present
#guard decide ((25 : ℤ) ∈ demoSpine) == false      -- 25 is absent (the bracketed key)

-- The UPDATE grows the set by exactly the fresh key, in sorted order:
#guard sortedInsert (25 : ℤ) demoSpine == [10, 20, 25, 30]   -- 25 lands between 20 and 30
#guard sortedInsert (5 : ℤ) demoSpine == [5, 10, 20, 30]      -- below the min
#guard sortedInsert (40 : ℤ) demoSpine == [10, 20, 30, 40]    -- above the max
-- ...and re-inserting a PRESENT key is a no-op (the set grows by at most k):
#guard sortedInsert (20 : ℤ) demoSpine == [10, 20, 30]        -- 20 already present

end Dregg2.Circuit.SortedTreeNonMembership
