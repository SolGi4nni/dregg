/-
# Dregg2.Circuit.SortedTreeInsertWide8 — the INSERT-side leaf-schema widening (felt-width site #10):
  the sorted-tree FRESH-KEY INSERT (`update_sound8` analogue) re-keyed from a 1-felt (~31-bit,
  birthday-collidable) key to the FULL 8-felt `Digest8Key`, so the accumulator's insert/exclude
  duality binds on the WHOLE digest. The insert-side twin of `SortedTreeNonMembershipWide8`'s
  non-membership widening — together they close the felt-width site-#10 LEAN side end-to-end.

## What was already proven (do not re-derive)

  * `Circuit/SortedTreeNonMembershipWide8.lean` — the `[LinearOrder K]`-GENERIC key-widened
    non-membership wrapper (`keyOfW`/`SpineCommitsW`/`keysOfW`/`keysOfW_eq_spine`/`GapOpenW`/
    `GapOpenW.excludesSpine`/`nonMembership_soundW`), instantiated at `K := Digest8Key`. THIS file
    reuses that wrapper's `SpineCommitsW`/`keysOfW`/`keysOfW_eq_spine` (the sorted-key-spine↔root
    binding + committed-key-set), and its `nonMembership_soundW` for the DUALITY capstone.
  * `Crypto/Digest8KeySpike.lean` — `Digest8Key := Lex (Fin 8 → ℤ)` with its synthesized noncomputable
    `LinearOrder`, and the concrete multi-felt bracket teeth (`keyLo`/`keyE`/`keyHi`, `keyLo_lt_keyE`
    decided at felt 7, `keyE_lt_keyHi` at felt 0, `spikeLeaves`/`spikeLeaves_sorted`/`spike_member`/
    `spike_excluded`).

## Why the insert side needed its own file (the residual `SortedTreeNonMembershipWide8` NAMED)

The `SortedTreeNonMembershipWide8` module doc listed as an un-closed residual "the update/insert
keystone (`update_sound8` analogue), needs the mechanical `ℤ → [LinearOrder K]` generalization of
`SortedTreeNonMembership.{mem_sortedInsert,sortedInsert_sorted}`". Those two combinatorial lemmas
(and `sortedInsert` itself) are `List ℤ`-typed in `SortedTreeNonMembership.lean`, even though their
PROOFS never touch ℤ arithmetic — they ride only `<`, `≤`, `.trans`, `lt_irrefl`, `lt_of_le_of_ne`,
`List.pairwise_cons`. So the generalization is mechanical: this file re-authors the generic
`[LinearOrder K]` core ONCE (`sortedInsertW`/`mem_sortedInsertW`/`sortedInsert_sortedW`) — the
insert-side analogue of `NonMembership.sorted_gap_excludes` being generic — then instantiates. The
deployed narrow `SortedTreeNonMembership.sortedInsert`/`Heap8.update_sound8` are the definitional
`K := ℤ` shadow of `sortedInsertW`/`update_soundW` (same definition, same proof, `K` pinned to `ℤ`).
(The shared `SortedTreeNonMembership.lean` foundation is not edited — the generic core lives here,
additively, to keep the hyperactive tree untouched.)

## What this file adds

  * `sortedInsertW` / `mem_sortedInsertW` / `sortedInsert_sortedW` — the `[LinearOrder K]`-GENERIC
    fresh-key sorted splice + its two combinatorial keystones (insert ADDS exactly `k`; a fresh-key
    insert PRESERVES sortedness). The mechanical widening of the ℤ `sortedInsert` lemma family.
  * `update_soundW` / `update_preserves_sortedW` — the `[LinearOrder K]`-GENERIC insert wrapper over
    `SpineCommitsW`/`keysOfW`: OLD root binds `spine` + `k` fresh + NEW root binds
    `sortedInsertW k spine` ⟹ the committed key set GROWS BY EXACTLY `k`, in sorted order. The
    generic twin of `SortedTreeNonMembershipHeap8.update_sound8`.
  * `insert_then_no_nonmembershipW` — THE INSERT/EXCLUDE DUALITY (generic): after inserting `k`, any
    non-membership `GapOpenW` for `k` against the NEW root is CONTRADICTORY (`k` is now present via
    `update_soundW`, absent via `nonMembership_soundW` — impossible). The insert-side complement of
    the accumulator's `present_no_witness`.
  * INSTANTIATED at `K := Digest8Key`: `update_sound_digest8` / `update_preserves_sorted_digest8` /
    `insert_then_no_nonmembership_digest8` — the insert soundness AT the full 8-felt lex key, indexed
    by all 8 felts, not the ~31-bit addr felt.
  * NON-VACUITY at the wrapper level (`demo_insert_grows`/`demo_keyE_present_after`/
    `demo_insert_strict_growth`/`demo_after_sorted`/`demo_insert_eq`/`demo_no_rewitness`): a REAL
    8-felt insert of `keyE` into the committed `[keyLo, keyHi]` grows the set to exactly
    `[keyLo, keyE, keyHi]`, `keyE` becomes a member (absent before, present after — genuine strict
    growth), the new spine stays sorted, and a subsequent non-membership query on `keyE` is REFUTED —
    all with the `keyLo < keyE` bracket decided at felt 7 (a limb a 1-felt projection discards).

## Honest scope (residuals, NOT closed here)

This closes the felt-width site-#10 LEAN side: the compare-gadget (`LexCompare8Emit`), the
non-membership leaf-widening (`SortedTreeNonMembershipWide8`), and now the insert-side (`update_sound8`
analogue) are all proven. NOT here (named residuals, NON-Lean / gated): the value-widening
(`hash_many → hash_many_8`, `felt_to_bytes32 → digest8_to_bytes32`, Rust-calls-Lean); the widened
in-circuit chip ROW re-emit (Rust, the realizing chip for the abstract `Opens`); and the EMBER-GATED
frozen kernel flip (`NullifierAccumulator.lean:12-23`, "do NOT fire piecemeal"). The deploy stays
gated; the DEPLOYED sorted-tree descriptor bytes are untouched (byte-safe additive).

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The `Digest8Key` `LinearOrder` is
noncomputable (well-founded first-differing-index comparison ⇒ `Classical.choice`, in the triple);
`sortedInsertW`'s `if`-splice is driven by the ORDER, not a computable compare (the AIR gadget
implements the compare). NEW file; all imports read-only. No `sorry`/`admit`/`native_decide`.
-/
import Dregg2.Circuit.SortedTreeNonMembershipWide8
import Dregg2.Crypto.Digest8KeySpike
import Dregg2.Tactics

namespace Dregg2.Circuit.SortedTreeInsertWide8

open Dregg2.Crypto.NonMembership (Sorted)
open Dregg2.Circuit.SortedTreeNonMembershipWide8 (keyOfW SpineCommitsW keysOfW keysOfW_eq_spine
  GapOpenW nonMembership_soundW)
open Dregg2.Crypto.Digest8KeySpike (Digest8Key keyLo keyE keyHi spikeLeaves spikeLeaves_sorted
  keyLo_lt_keyE keyE_lt_keyHi keyLo_lt_keyHi spike_member spike_excluded)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — the `[LinearOrder K]`-GENERIC fresh-key sorted splice + its combinatorial keystones.

The mechanical `ℤ → [LinearOrder K]` generalization of `SortedTreeNonMembership.sortedInsert`/
`mem_sortedInsert`/`sortedInsert_sorted`. The proofs never touch ℤ arithmetic — they ride only the
linear order — so they port verbatim at any `[LinearOrder K]` (e.g. the 8-felt lex key). -/

section Generic

variable {K : Type*} [LinearOrder K] {V : Type*} {Root : Type*}

/-- **`sortedInsertW k xs`** — insert `k` into a sorted `K` list, preserving order (skips an equal
key, so the set grows by at most `k`). The spine edit a tree insert performs. Widening the ℤ
`SortedTreeNonMembership.sortedInsert` to any `[LinearOrder K]`; at `K := Digest8Key` the splice is
driven by the 8-limb lex order. -/
def sortedInsertW (k : K) : List K → List K
  | [] => [k]
  | x :: t => if k < x then k :: x :: t else if k = x then x :: t else x :: sortedInsertW k t

/-- **`mem_sortedInsertW`** — `sortedInsertW` of a fresh key actually ADDS it (membership grows by
exactly `k`). The generic twin of `SortedTreeNonMembership.mem_sortedInsert`. -/
theorem mem_sortedInsertW (k : K) (xs : List K) (y : K) :
    y ∈ sortedInsertW k xs ↔ y = k ∨ y ∈ xs := by
  induction xs with
  | nil => simp [sortedInsertW]
  | cons x t ih =>
    unfold sortedInsertW
    by_cases hlt : k < x
    · simp only [hlt, if_true, List.mem_cons]; try tauto
    · rw [if_neg hlt]
      by_cases hkx : k = x
      · rw [if_pos hkx, hkx]; simp only [List.mem_cons]; try tauto
      · rw [if_neg hkx]; simp only [List.mem_cons, ih]; try tauto

/-- **`sortedInsert_sortedW`** — `sortedInsertW` of a FRESH key (`k ∉ xs`) into a sorted list yields a
sorted list. The structural core of the update: the insert keeps the spine strictly increasing. The
generic twin of `SortedTreeNonMembership.sortedInsert_sorted`. -/
theorem sortedInsert_sortedW (k : K) (xs : List K) (hs : Sorted xs) (hfresh : k ∉ xs) :
    Sorted (sortedInsertW k xs) := by
  induction xs with
  | nil => simp [sortedInsertW, Sorted, List.pairwise_cons]
  | cons x t ih =>
    have hst : Sorted t := (List.pairwise_cons.mp hs).2
    have hxt : ∀ y ∈ t, x < y := (List.pairwise_cons.mp hs).1
    have hkx : k ≠ x := fun h => hfresh (h ▸ List.mem_cons_self)
    have hkt : k ∉ t := fun h => hfresh (List.mem_cons_of_mem x h)
    unfold sortedInsertW
    by_cases hlt : k < x
    · simp only [hlt, if_true]
      refine List.pairwise_cons.mpr ⟨?_, hs⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hyt
      · exact hlt
      · exact hlt.trans (hxt y hyt)
    · rw [if_neg hlt]
      rw [if_neg hkx]
      refine List.pairwise_cons.mpr ⟨?_, ih hst hkt⟩
      intro y hy
      have hxk : x < k := lt_of_le_of_ne (not_lt.mp hlt) (fun h => hkx h.symm)
      rcases (mem_sortedInsertW k t y).mp hy with rfl | hyt
      · exact hxk
      · exact hxt y hyt

/-! ## §1 — the `[LinearOrder K]`-GENERIC insert wrapper over `SpineCommitsW`/`keysOfW`. -/

/-- **`update_soundW` — THE GENERIC INSERT KEYSTONE.** Given the OLD root binds the sorted `spine`,
`k` is FRESH (non-membership over the OLD root, the output of `nonMembership_soundW`), and the NEW root
binds the INSERTED spine (`sortedInsertW k spine` — the realizing chip recompose), the new committed
key set is EXACTLY the old set plus `k`. FAITHFUL: it grows the set by exactly the fresh key, in
sorted order. The `[LinearOrder K]`-generic twin of `SortedTreeNonMembershipHeap8.update_sound8`;
instantiating `K := ℤ` recovers the deployed narrow keystone. -/
theorem update_soundW (Opens : Root → K × V → Prop) (oldRoot newRoot : Root) (k : K)
    (spine : List K)
    (hold : SpineCommitsW Opens oldRoot spine)
    (hfresh : k ∉ keysOfW Opens oldRoot)
    (hnew : SpineCommitsW Opens newRoot (sortedInsertW k spine)) :
    ∀ y, y ∈ keysOfW Opens newRoot ↔ (y = k ∨ y ∈ keysOfW Opens oldRoot) := by
  intro y
  rw [keysOfW_eq_spine Opens newRoot _ hnew, keysOfW_eq_spine Opens oldRoot spine hold,
      mem_sortedInsertW]

/-- **`update_preserves_sortedW`** — corollary: the new spine the insert commits to is itself sorted
(so the tree stays a sorted-Merkle tree the next open/insert can ride). The fresh-key insert keeps the
sorted invariant. -/
theorem update_preserves_sortedW (Opens : Root → K × V → Prop) (oldRoot : Root) (k : K)
    (spine : List K)
    (hold : SpineCommitsW Opens oldRoot spine) (hfresh : k ∉ spine) :
    Sorted (sortedInsertW k spine) :=
  sortedInsert_sortedW k spine hold.sorted hfresh

/-! ## §2 — THE INSERT/EXCLUDE DUALITY (generic): after insert, `k` admits no non-membership. -/

/-- **`insert_then_no_nonmembershipW` — THE DUALITY CAPSTONE (generic).** After inserting the fresh
key `k` (old root binds `spine`, `k` fresh, new root binds `sortedInsertW k spine`), ANY non-membership
covering-gap open for `k` valid against the NEW root's spine is CONTRADICTORY: `update_soundW` makes
`k` PRESENT in the new committed set, while `nonMembership_soundW` (from the leaf-widening) would make
that same gap prove `k` ABSENT — impossible. The insert-side complement of the accumulator's
`present_no_witness`: once a key is inserted, a subsequent non-membership query on it correctly FAILS
(admits no witness). Closes the accumulator's insert/exclude duality at the full key `K`. -/
theorem insert_then_no_nonmembershipW (Opens : Root → K × V → Prop) (oldRoot newRoot : Root) (k : K)
    (spine : List K)
    (hold : SpineCommitsW Opens oldRoot spine)
    (hfresh : k ∉ keysOfW Opens oldRoot)
    (hnew : SpineCommitsW Opens newRoot (sortedInsertW k spine))
    (g : GapOpenW Opens newRoot k) (hv : g.coversSpine (sortedInsertW k spine)) : False := by
  have hpresent : k ∈ keysOfW Opens newRoot :=
    (update_soundW Opens oldRoot newRoot k spine hold hfresh hnew k).mpr (Or.inl rfl)
  have habsent : k ∉ keysOfW Opens newRoot :=
    nonMembership_soundW Opens newRoot k (sortedInsertW k spine) hnew g hv
  exact habsent hpresent

end Generic

/-! ## §3 — INSTANTIATION at the 8-felt lex key `Digest8Key`: the insert-widening keystones. -/

/-- **`update_sound_digest8` — the insert keystone AT THE FULL 8-FELT KEY.** A fresh-key insert of an
8-felt lex key grows the committed set by EXACTLY that key, indexed by all 8 felts, not the ~31-bit
addr felt. The `Digest8Key` instantiation of `update_soundW`; the insert-side leaf-widening of
`SortedTreeNonMembershipHeap8.update_sound8`. -/
theorem update_sound_digest8 {V Root : Type*}
    (Opens : Root → Digest8Key × V → Prop) (oldRoot newRoot : Root) (k : Digest8Key)
    (spine : List Digest8Key)
    (hold : SpineCommitsW Opens oldRoot spine)
    (hfresh : k ∉ keysOfW Opens oldRoot)
    (hnew : SpineCommitsW Opens newRoot (sortedInsertW k spine)) :
    ∀ y, y ∈ keysOfW Opens newRoot ↔ (y = k ∨ y ∈ keysOfW Opens oldRoot) :=
  update_soundW Opens oldRoot newRoot k spine hold hfresh hnew

/-- **`update_preserves_sorted_digest8`** — the fresh-key insert of an 8-felt key keeps the committed
spine sorted (the 8-limb lex order preserved). -/
theorem update_preserves_sorted_digest8 {V Root : Type*}
    (Opens : Root → Digest8Key × V → Prop) (oldRoot : Root) (k : Digest8Key)
    (spine : List Digest8Key)
    (hold : SpineCommitsW Opens oldRoot spine) (hfresh : k ∉ spine) :
    Sorted (sortedInsertW k spine) :=
  update_preserves_sortedW Opens oldRoot k spine hold hfresh

/-- **`insert_then_no_nonmembership_digest8` — the insert/exclude DUALITY at the full 8-felt key.**
After inserting an 8-felt lex key, any non-membership open for it against the new root is refuted. The
`Digest8Key` instantiation of `insert_then_no_nonmembershipW`. -/
theorem insert_then_no_nonmembership_digest8 {V Root : Type*}
    (Opens : Root → Digest8Key × V → Prop) (oldRoot newRoot : Root) (k : Digest8Key)
    (spine : List Digest8Key)
    (hold : SpineCommitsW Opens oldRoot spine)
    (hfresh : k ∉ keysOfW Opens oldRoot)
    (hnew : SpineCommitsW Opens newRoot (sortedInsertW k spine))
    (g : GapOpenW Opens newRoot k) (hv : g.coversSpine (sortedInsertW k spine)) : False :=
  insert_then_no_nonmembershipW Opens oldRoot newRoot k spine hold hfresh hnew g hv

/-! ## §4 — NON-VACUITY at the wrapper level: a real 8-felt insert grows the committed set by keyE. -/

/-- The demo opening predicate over a `Bool`-indexed root (`false` = BEFORE, `true` = AFTER): a widened
leaf `(key, val)` opens IFF its 8-felt key is in the committed spine of that root. BEFORE binds the
spike spine `[keyLo, keyHi]`; AFTER binds the grown `sortedInsertW keyE spikeLeaves`. -/
def insOpens : Bool → Digest8Key × ℤ → Prop :=
  fun r e => if r then e.1 ∈ sortedInsertW keyE spikeLeaves else e.1 ∈ spikeLeaves

/-- The BEFORE root binds the sorted spike spine `[keyLo, keyHi]`. -/
theorem insOpens_before_spine : SpineCommitsW insOpens false spikeLeaves :=
  { sorted := spikeLeaves_sorted
    present_iff := fun k =>
      ⟨fun ⟨_e, he, hmem⟩ => he ▸ hmem, fun hk => ⟨(k, 0), rfl, hk⟩⟩ }

/-- The AFTER root binds the GROWN spine `sortedInsertW keyE spikeLeaves` — sorted by
`sortedInsert_sortedW` (the fresh `keyE` bracketed by `spike_excluded`). -/
theorem insOpens_after_spine : SpineCommitsW insOpens true (sortedInsertW keyE spikeLeaves) :=
  { sorted := sortedInsert_sortedW keyE spikeLeaves spikeLeaves_sorted spike_excluded
    present_iff := fun k =>
      ⟨fun ⟨_e, he, hmem⟩ => he ▸ hmem, fun hk => ⟨(k, 0), rfl, hk⟩⟩ }

/-- `keyE` is ABSENT from the BEFORE committed key set (the fresh key, bracketed `keyLo < keyE < keyHi`
at felts 7 and 0). Rides `spike_excluded`. -/
theorem insOpens_keyE_fresh : keyE ∉ keysOfW insOpens false := by
  rintro ⟨_e, he, hmem⟩
  exact spike_excluded (he ▸ hmem)

/-- **★ NON-VACUITY (wrapper level).** The widened insert keystone FIRES: a real 8-felt insert of
`keyE` into the committed `[keyLo, keyHi]` grows the committed key set by EXACTLY `keyE`. -/
theorem demo_insert_grows :
    ∀ y, y ∈ keysOfW insOpens true ↔ (y = keyE ∨ y ∈ keysOfW insOpens false) :=
  update_sound_digest8 insOpens false true keyE spikeLeaves
    insOpens_before_spine insOpens_keyE_fresh insOpens_after_spine

/-- **★ MEMBERSHIP TOOTH.** After the insert, the fresh `keyE` IS a member of the committed set (the
`y = keyE` disjunct) — the inserted key becomes present. -/
theorem demo_keyE_present_after : keyE ∈ keysOfW insOpens true :=
  (demo_insert_grows keyE).mpr (Or.inl rfl)

/-- **★ STRICT GROWTH.** The insert is not a no-op: `keyE` is PRESENT after and ABSENT before — a
genuine distinct-key growth on a real 8-felt key (the `keyLo < keyE` bracket decided at felt 7, a limb
a 1-felt projection discards). -/
theorem demo_insert_strict_growth :
    keyE ∈ keysOfW insOpens true ∧ keyE ∉ keysOfW insOpens false :=
  ⟨demo_keyE_present_after, insOpens_keyE_fresh⟩

/-- **★ SORTED-PRESERVATION TOOTH.** The grown spine stays sorted (the 8-limb lex order preserved). -/
theorem demo_after_sorted : Sorted (sortedInsertW keyE spikeLeaves) :=
  update_preserves_sorted_digest8 insOpens false keyE spikeLeaves insOpens_before_spine spike_excluded

/-- **★ CONCRETE SPINE.** The grown 8-felt-keyed spine is EXACTLY `[keyLo, keyE, keyHi]`: `keyE` lands
in its felt-7 bracket between `keyLo` and `keyHi`. The `if`-splice reduces via the ORDER proofs
(`keyLo_lt_keyE`, `keyE_lt_keyHi`) — the noncomputable lex `LinearOrder` never needs to compute. -/
theorem demo_insert_eq : sortedInsertW keyE spikeLeaves = [keyLo, keyE, keyHi] := by
  show sortedInsertW keyE [keyLo, keyHi] = [keyLo, keyE, keyHi]
  simp only [sortedInsertW]
  split_ifs with c1 c2 c3 c4 <;>
    first
      | rfl
      | exact absurd c1 (not_lt.mpr keyLo_lt_keyE.le)
      | exact absurd c2 keyLo_lt_keyE.ne'
      | exact absurd keyE_lt_keyHi c3

/-- **★ DUALITY TOOTH (the capstone, concrete).** Over the committed 8-felt tree, once `keyE` is
inserted, ANY non-membership covering-gap open for `keyE` against the AFTER root is REFUTED — the
insert/exclude duality fires: an inserted key admits no subsequent non-membership witness. -/
theorem demo_no_rewitness (g : GapOpenW insOpens true keyE)
    (hv : g.coversSpine (sortedInsertW keyE spikeLeaves)) : False :=
  insert_then_no_nonmembership_digest8 insOpens false true keyE spikeLeaves
    insOpens_before_spine insOpens_keyE_fresh insOpens_after_spine g hv

/-! ## §5 — axiom hygiene: every insert-widening keystone rests on the kernel triple only. -/

#assert_axioms mem_sortedInsertW
#assert_axioms sortedInsert_sortedW
#assert_axioms update_soundW
#assert_axioms update_preserves_sortedW
#assert_axioms insert_then_no_nonmembershipW
#assert_axioms update_sound_digest8
#assert_axioms update_preserves_sorted_digest8
#assert_axioms insert_then_no_nonmembership_digest8
#assert_axioms demo_insert_grows
#assert_axioms demo_keyE_present_after
#assert_axioms demo_insert_strict_growth
#assert_axioms demo_after_sorted
#assert_axioms demo_insert_eq
#assert_axioms demo_no_rewitness

end Dregg2.Circuit.SortedTreeInsertWide8
