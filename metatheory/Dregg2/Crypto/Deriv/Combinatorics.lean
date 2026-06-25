/-
# Dregg2.Crypto.Deriv.Combinatorics — Stage 3 scaffolding: the GENERIC subset/sublist combinatorics
# underpinning Brzozowski finiteness `up to similarity`.

The ITP'25 `finiteness-derivatives` finiteness proof rests on a tower of GENERIC (regex-free) list
combinatorics: `subset_up_to` (`⊆[R]`, set inclusion modulo a relation, `SubsetUpTo.lean`) and
`neSublists` (non-empty sublists, `NeSublists.lean`). NONE of it mentions regexes — so it ports to
dregg VERBATIM (no `PredRE`-specific reasoning), and is the foundation the `pieces`/`neSubsets`
overapproximation (the named Stage-3 combinatorial wall) is built on.

This file banks that generic foundation kernel-clean, so the remaining Stage-3 work is the
regex-specific closure (`pieces` + `der_pieces`) ALONE, not also re-deriving the list combinatorics.

`#assert_axioms`-clean, `sorry`-free. Faithful re-instantiation of ITP'25 `SubsetUpTo.lean` +
`NeSublists.lean` (read-only blueprint, no import).
-/
import Mathlib.Data.List.Sublists
import Dregg2.Tactics

namespace Dregg2.Crypto.Deriv.Combinatorics

open List

/-! ## `subset_up_to` — set inclusion modulo a relation `R` (ITP'25 `SubsetUpTo.lean`). -/

/-- **`MemUpTo R x ys`** — `x` is in `ys` modulo `R`: some `y ∈ ys` with `R x y`. -/
@[simp] def MemUpTo (R : α → α → Prop) (x : α) (ys : List α) : Prop := ∃ y, R x y ∧ y ∈ ys

@[inherit_doc] notation x " ∈[ " R " ] " ys => MemUpTo R x ys

/-- **`SubsetUpTo R xs ys`** — every element of `xs` is in `ys` modulo `R`. -/
@[simp] def SubsetUpTo (R : α → α → Prop) (xs ys : List α) : Prop := ∀ x ∈ xs, x ∈[ R ] ys

@[inherit_doc] notation xs " ⊆[ " R " ] " ys => SubsetUpTo R xs ys

theorem subset_up_to_refl {R : α → α → Prop} {xs : List α} (hr : ∀ x, R x x) :
    xs ⊆[ R ] xs := fun x h => ⟨x, hr x, h⟩

theorem subset_up_to_trans {R : α → α → Prop} {xs ys zs : List α}
    (ht : ∀ a b c, R a b → R b c → R a c)
    (h1 : xs ⊆[ R ] ys) (h2 : ys ⊆[ R ] zs) : xs ⊆[ R ] zs :=
  fun r hr =>
    have ⟨g1, g2, g3⟩ := h1 r hr
    have ⟨i1, i2, i3⟩ := h2 g1 g3
    ⟨i1, ht _ _ _ g2 i2, i3⟩

theorem subset_to_subset_up_to {R : α → α → Prop} {xs ys : List α}
    (hr : ∀ x, R x x) (h : xs ⊆ ys) : xs ⊆[ R ] ys :=
  fun g g1 => ⟨g, hr g, h g1⟩

/-! ## `neSublists` — non-empty sublists (ITP'25 `NeSublists.lean`). Fully generic. -/

/-- **`neSublists xs`** — all NON-EMPTY sublists of `xs`. -/
@[simp] def neSublists : List α → List (List α)
  | []    => []
  | x::xs => [[x]] ++ map (x :: ·) (neSublists xs) ++ neSublists xs

theorem neSublists_completeness {xs ys : List α} :
    xs <+ ys ∧ xs ≠ [] → xs ∈ neSublists ys := fun ⟨h, ne⟩ =>
  match h with
  | Sublist.slnil => False.elim (ne rfl)
  | Sublist.cons a h1 => by
    simp only [neSublists, cons_append, mem_cons, mem_append, mem_map]
    exact Or.inr <| Or.inr (neSublists_completeness ⟨h1, ne⟩)
  | @Sublist.cons_cons _ l1 l2 a h1 => by
    match l1 with
    | [] => exact mem_of_mem_head? rfl
    | l::ls =>
      simp only [neSublists, cons_append, nil_append, mem_cons, mem_append, mem_map]
      exact Or.inr <| Or.inl ⟨l::ls, neSublists_completeness ⟨h1, cons_ne_nil l ls⟩, rfl⟩

theorem neSublists_correctness {xs ys : List α} :
    xs ∈ neSublists ys → xs <+ ys ∧ xs ≠ [] := fun h => by
  match ys with
  | [] => simp only [neSublists, not_mem_nil] at h
  | y::ys =>
    simp only [neSublists, singleton_append] at h
    simp only [cons_append, mem_cons, mem_append, mem_map] at h
    match h with
    | Or.inl h1 =>
      subst h1
      simp only [cons_sublist_cons, nil_sublist, ne_eq, cons_ne_self, not_false_eq_true, and_self]
    | Or.inr h1 =>
      match h1 with
      | Or.inl ⟨g1, g2, g3⟩ =>
        subst g3
        simp only [cons_sublist_cons, ne_eq]
        exact ⟨(neSublists_correctness g2).1, cons_ne_nil y g1⟩
      | Or.inr h2 =>
        exact ⟨Sublist.cons y (neSublists_correctness h2).1, (neSublists_correctness h2).2⟩

theorem neSublists_characterization {xs ys : List α} :
    xs ∈ neSublists ys ↔ xs <+ ys ∧ xs ≠ [] :=
  ⟨neSublists_correctness, neSublists_completeness⟩

theorem neSub_ne {xs ys : List α} (h : xs ∈ neSublists ys) : xs ≠ [] :=
  (neSublists_correctness h).2

theorem neSublists_append {x y xs ys : List α}
    (h : x ∈ neSublists xs) (h1 : y ∈ neSublists ys) :
    (x ++ y) ∈ neSublists (xs ++ ys) :=
  have ⟨y_sub, y_ne⟩ := neSublists_characterization.mp h1
  have hh := Sublist.append (neSublists_characterization.mp h).1 y_sub
  neSublists_characterization.mpr ⟨hh, append_ne_nil_of_right_ne_nil x y_ne⟩

theorem neSublists_unitality {xs : List α} (ne : xs ≠ []) : xs ∈ neSublists xs :=
  neSublists_characterization.mpr ⟨Sublist.refl xs, ne⟩

theorem neSublists_singleton {x : α} {xs : List α} (h : x ∈ xs) : [x] ∈ neSublists xs :=
  match xs with
  | [] => False.elim ((mem_nil_iff x).mp h)
  | _::_ => neSublists_characterization.mpr ⟨singleton_sublist.mpr h, cons_ne_nil x []⟩

theorem neSublists_extend {x : α} {xs ys : List α} (h : xs ∈ neSublists ys) :
    xs ∈ neSublists (x::ys) :=
  have ⟨h1, h2⟩ := neSublists_characterization.mp h
  neSublists_characterization.mpr ⟨Sublist.cons x h1, h2⟩

theorem neSublists_appendL {x xs ys : List α} (h : x ∈ neSublists xs) :
    x ∈ neSublists (xs ++ ys) :=
  let ⟨x_sub, x_ne⟩ := neSublists_characterization.mp h
  neSublists_characterization.mpr ⟨sublist_append_of_sublist_left x_sub, x_ne⟩

theorem neSublists_appendR {x xs ys : List α} (h : x ∈ neSublists ys) :
    x ∈ neSublists (xs ++ ys) :=
  let ⟨x_sub, x_ne⟩ := neSublists_characterization.mp h
  neSublists_characterization.mpr ⟨sublist_append_of_sublist_right x_sub, x_ne⟩

end Dregg2.Crypto.Deriv.Combinatorics

/-! ## Axiom hygiene. -/

#assert_all_clean [
  Dregg2.Crypto.Deriv.Combinatorics.subset_up_to_refl,
  Dregg2.Crypto.Deriv.Combinatorics.subset_up_to_trans,
  Dregg2.Crypto.Deriv.Combinatorics.neSublists_characterization,
  Dregg2.Crypto.Deriv.Combinatorics.neSublists_append,
  Dregg2.Crypto.Deriv.Combinatorics.neSublists_singleton,
  Dregg2.Crypto.Deriv.Combinatorics.neSublists_extend
]
