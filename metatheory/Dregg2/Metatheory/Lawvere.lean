/-
# Dregg2.Metatheory.Lawvere — the LAWVERE HYPERDOCTRINE triple `∃_a ⊣ q_a* ⊣ ∀_a`.

Lawvere (*Adjointness in Foundations*, 1969; *Equality in Hyperdoctrines*, 1970) read
quantifiers as ADJOINTS to the reindexing (substitution) functor `f*`: along `f : α → β`,
existential quantification is its LEFT adjoint `∃_f` and universal quantification its RIGHT
adjoint `∀_f`, giving the celebrated triple

      ∃_f  ⊣  f*  ⊣  ∀_f .

`Metatheory.Disputation` and `project-adjunction-thesis-verdict` (memory) record that the
dregg2 knowledge layer is exactly such a hyperdoctrine: `Predicate ⊣ Witness` is the BASE
tripos, and KNOWLEDGE is a *graded* family of per-agent Lawvere adjunctions `∃_a ⊣ q_a* ⊣ ∀_a`
along the indistinguishability quotient, with `Kₐ = ∀_a`. This module makes that triple
concrete and pins what genuinely holds, in TWO clearly-separated parts.

## PART A — the POSETAL Set-doctrine SPECIAL CASE (fully provable).

The fibres are the *power-set posets* `(Set α, ⊆)`; reindexing along `f : α → β` is
`f* = Set.preimage f`. We prove the full triple as `GaloisConnection`s (the posetal /
preorder-enriched shape of an adjunction):

  * `∃_f ⊣ f*`     — `Set.image_preimage : GaloisConnection (image f) (preimage f)`;
  * `f* ⊣ ∀_f`     — `Set.preimage_kernImage : GaloisConnection (preimage f) (kernImage f)`,
                     where `∀_f = Set.kernImage f`;
  * **Frobenius reciprocity** `∃_f (S ∩ f⁻¹ T) = ∃_f S ∩ T` (`Set.image_inter_preimage`);
  * **Beck–Chevalley** (posetal): `g* ∘ ∃_f = ∃_q ∘ p*` for a pullback square — proved from a
    faithful set-level pullback predicate (commuting + surjective comparison onto the fibre
    product), with the `⊇` half free from commuting and the `⊆` half the pullback content.

TEETH (this is the *special* case, and we show its edges):
  * Beck–Chevalley FAILS on a concrete NON-pullback finite (`Fin`) square;
  * a NON-monotone reindexing breaks the Galois connection (concretely on `Fin 2`).

## PART B — the FAITHFUL RELATION-FORM (the genuinely deeper, previously-deferred fibre).

The epistemic fibre of `Metatheory.EpistemicConsensus.Frame`: `∀_a = Knows` is a box-modality
over an indistinguishability relation `R` that, for **Byzantine** agents, is REFLEXIVE but NOT
necessarily symmetric or transitive — emphatically NOT an equivalence. We build the relational
quantifiers

  * `relExists R`  (`∃_R`, the relational image / diamond `◇`),
  * `relForall R`  (`∀_R = Knows`, the box `□`),

and prove the genuine general adjunction `∃_R ⊣ ∀_R` that holds for ANY relation; that
reflexivity already yields the modal `T`-axioms; and that the graph of a function recovers
Part A's first adjunction `∃_f ⊣ f*` (so Part B *contains* Part A — it is not a relabeling).

TEETH (why Part B is genuinely DIFFERENT from the clean Part-A triple):
  * for an EQUIVALENCE relation the box `∀_R` is IDEMPOTENT (S4 / a quotient interior) — the
    clean situation in which the further right adjoint (the `kernImage`-style closure) exists;
  * for a merely-REFLEXIVE Byzantine relation, `∀_R ∘ ∀_R ≠ ∀_R` (S4 BREAKS) — proved on a
    concrete reflexive-non-transitive `Fin 3` relation; and the diamond `∃_R` FAILS to preserve
    binary meets there. So the clean `kernImage` triple of Part A does NOT lift to the Byzantine
    fibre: that triple was special to the *function/quotient* (equivalence) structure.

The teeth are concrete (`Fin`)
DISCRIMINATING models, so nothing is vacuous.
-/
import Metatheory.EpistemicConsensus
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Order.GaloisConnection.Basic

namespace Dregg2.Metatheory.Lawvere

open Set

universe u v

/-! ###############################################################################
# PART A — the POSETAL Set-doctrine special case.
##################################################################################

The Lawvere hyperdoctrine `Set : αᵒᵖ → Poset`, `α ↦ (Set α, ⊆)`, `f ↦ f* = preimage f`.
Reindexing has BOTH adjoints, and the existential one satisfies Frobenius + Beck–Chevalley.
This is the **special / degenerate fibre**: the base poset is a complete BOOLEAN algebra and
`f*` is a frame homomorphism, which is *exactly* what gives the clean two-sided triple. -/

namespace PartA

variable {α : Type u} {β : Type v}

/-! ### §A.1 The quantifier triple `∃_f ⊣ f* ⊣ ∀_f`.

`∃_f = image f`, `f* = preimage f`, `∀_f = kernImage f`. The two adjunctions are the posetal
shape (`GaloisConnection`) of the left/right adjointness of the quantifiers. -/

/-- `∃_f`, existential quantification along `f` — the LEFT adjoint to reindexing. -/
def existsAlong (f : α → β) : Set α → Set β := Set.image f

/-- `f* = `reindexing/substitution along `f`. -/
def reindex (f : α → β) : Set β → Set α := Set.preimage f

/-- `∀_f`, universal quantification along `f` — the RIGHT adjoint to reindexing.
`∀_f T = {y | f⁻¹{y} ⊆ T}` = `Set.kernImage f`. -/
def forallAlong (f : α → β) : Set α → Set β := Set.kernImage f

/-- **`∃_f ⊣ f*` (LEFT adjoint), PROVED.** The posetal adjunction
`∃_f S ⊆ T ↔ S ⊆ f* T` is `Set.image_preimage`. -/
theorem existsAlong_adj_reindex (f : α → β) :
    GaloisConnection (existsAlong f) (reindex f) :=
  Set.image_preimage

/-- **`f* ⊣ ∀_f` (RIGHT adjoint), PROVED.** The posetal adjunction
`f* T₁ ⊆ T₂ ↔ T₁ ⊆ ∀_f T₂` is `Set.preimage_kernImage`. Together with
`existsAlong_adj_reindex` this is the full Lawvere triple `∃_f ⊣ f* ⊣ ∀_f`. -/
theorem reindex_adj_forallAlong (f : α → β) :
    GaloisConnection (reindex f) (forallAlong f) :=
  Set.preimage_kernImage

/-- **The triple, packaged: both adjunctions at once — PROVED.** -/
theorem lawvere_triple (f : α → β) :
    GaloisConnection (existsAlong f) (reindex f) ∧
    GaloisConnection (reindex f) (forallAlong f) :=
  ⟨existsAlong_adj_reindex f, reindex_adj_forallAlong f⟩

/-- The unit of `∃_f ⊣ f*`: `S ⊆ f⁻¹(f S)` (every element lands in the preimage of its image).
A direct adjunction consequence — sanity that the connection has content. -/
theorem reindex_existsAlong_unit (f : α → β) (S : Set α) :
    S ⊆ reindex f (existsAlong f S) :=
  (existsAlong_adj_reindex f).le_u_l S

/-- The counit of `f* ⊣ ∀_f`: `f⁻¹(∀_f T) ⊆ T`. -/
theorem reindex_forallAlong_counit (f : α → β) (T : Set α) :
    reindex f (forallAlong f T) ⊆ T :=
  (reindex_adj_forallAlong f).l_u_le T

/-! ### §A.2 Frobenius reciprocity (posetal).

The hyperdoctrine's *Frobenius / projection formula*: `∃_f` is a map of `f*`-modules,
`∃_f (S ∩ f* T) = ∃_f S ∩ T`. In Set this is `Set.image_inter_preimage`. -/

/-- **Frobenius reciprocity, PROVED.** `∃_f (S ∩ f⁻¹ T) = ∃_f S ∩ T`. -/
theorem frobenius (f : α → β) (S : Set α) (T : Set β) :
    existsAlong f (S ∩ reindex f T) = existsAlong f S ∩ T :=
  Set.image_inter_preimage f S T

/-! ### §A.3 Beck–Chevalley (posetal).

For a pullback square

```
      p
   P ───→ A
   │      │
 q │      │ f
   ↓      ↓
   C ───→ B
      g
```

the Beck–Chevalley condition is the mate identity `g* ∘ ∃_f = ∃_q ∘ p*`, i.e.
`g⁻¹(f '' S) = q '' (p⁻¹ S)`. We encode a faithful *set-level pullback square* and prove BC
from it. The `⊇` half is free from commuting; the `⊆` half is exactly the pullback property
(every fibre-product element is hit by the comparison `⟨p,q⟩`). -/

/-- A commuting square `f ∘ p = g ∘ q` that is a **pullback in Set**, encoded faithfully by the
comparison map `⟨p,q⟩ : P → {(a,c) | f a = g c}` being SURJECTIVE (its injectivity is not needed
for the posetal Beck–Chevalley, only the existence/surjectivity of mediating elements). -/
structure PullbackSq {P A C B : Type u} (f : A → B) (g : C → B) (p : P → A) (q : P → C) :
    Prop where
  /-- the square commutes. -/
  comm : ∀ x : P, f (p x) = g (q x)
  /-- the comparison `⟨p,q⟩` is surjective onto the fibre product: every compatible pair lifts. -/
  lift : ∀ a c, f a = g c → ∃ x : P, p x = a ∧ q x = c

variable {P A C B : Type u}

/-- **Beck–Chevalley, PROVED (posetal).** For a Set-pullback square, reindexing commutes with
existential quantification along the opposite legs: `g* ∘ ∃_f = ∃_q ∘ p*`, i.e.

      g⁻¹ (f '' S) = q '' (p⁻¹ S)   for all `S ⊆ A`.

This is the load-bearing coherence of the hyperdoctrine. -/
theorem beck_chevalley {f : A → B} {g : C → B} {p : P → A} {q : P → C}
    (sq : PullbackSq f g p q) (S : Set A) :
    reindex g (existsAlong f S) = existsAlong q (reindex p S) := by
  apply Set.ext
  intro c
  constructor
  · -- ⊆ : c with g c = f a, a ∈ S; lift (a,c) to x ∈ P, then x ∈ p⁻¹ S and q x = c.
    rintro hc
    rw [reindex, Set.mem_preimage, existsAlong, Set.mem_image] at hc
    obtain ⟨a, haS, hfa⟩ := hc
    obtain ⟨x, hpx, hqx⟩ := sq.lift a c hfa
    refine ⟨x, ?_, hqx⟩
    rw [reindex, Set.mem_preimage, hpx]; exact haS
  · -- ⊇ : free from commuting. c = q x with p x ∈ S ⇒ g c = f (p x) ∈ f '' S.
    rintro ⟨x, hx, hqx⟩
    rw [reindex, Set.mem_preimage] at hx
    rw [reindex, Set.mem_preimage, existsAlong, Set.mem_image]
    exact ⟨p x, hx, by rw [sq.comm x, hqx]⟩

/-- The canonical Set-pullback always satisfies `PullbackSq`: `P := {(a,c) // f a = g c}`,
`p := fst`, `q := snd`. So Beck–Chevalley is non-vacuous — there is a real model of the
hypothesis (instantiated concretely in §A.4). -/
def canonicalPullback {A C B : Type u} (f : A → B) (g : C → B) :
    PullbackSq f g (fun x : {ac : A × C // f ac.1 = g ac.2} => x.1.1)
      (fun x : {ac : A × C // f ac.1 = g ac.2} => x.1.2) where
  comm := fun x => x.2
  lift := fun a c h => ⟨⟨(a, c), h⟩, rfl, rfl⟩

/-! ### §A.4 TEETH: Beck–Chevalley FAILS on a concrete non-pullback square. -/

namespace BCFails

/-- A concrete COMMUTING-but-NOT-pullback finite square over `Fin _`.

  `A = Fin 2`, `C = Fin 1`, `B = Fin 1`, `P = Fin 1`.
  `f : Fin 2 → Fin 1` is the constant `0`; `g : Fin 1 → Fin 1` is the constant `0`.
  `p : Fin 1 → Fin 2` picks the element `0`; `q : Fin 1 → Fin 1` is the identity.

The square commutes (`f (p x) = 0 = g (q x)`), but it is NOT a pullback: the fibre product
`{(a,c) | f a = g c}` is all of `Fin 2 × Fin 1` (two compatible pairs `(0,0)` and `(1,0)`),
yet the single point of `P` only covers `(0,0)` — the pair `(1,0)` is NOT lifted. Beck–Chevalley
then fails on `S := {1}`: `g⁻¹(f '' {1}) = Fin 1` (everything, since `f '' {1} = {0} = B`), but
`q '' (p⁻¹ {1}) = ∅` (because `p` only hits `0 ∉ {1}`). -/
def f : Fin 2 → Fin 1 := fun _ => 0
def g : Fin 1 → Fin 1 := fun _ => 0
def p : Fin 1 → Fin 2 := fun _ => 0
def q : Fin 1 → Fin 1 := fun _ => 0

/-- The square COMMUTES — so the failure below is genuinely about the *pullback* property, not
about non-commuting. -/
theorem square_commutes : ∀ x : Fin 1, f (p x) = g (q x) := by
  intro x; rfl

/-- **Beck–Chevalley FAILS here — PROVED.** With `S := {1} ⊆ Fin 2`:
`reindex g (existsAlong f S) = univ` but `existsAlong q (reindex p S) = ∅`, so they differ. -/
theorem beck_chevalley_fails :
    reindex g (existsAlong f ({1} : Set (Fin 2))) ≠ existsAlong q (reindex p ({1} : Set (Fin 2))) := by
  intro h
  -- LHS contains 0 (in fact everything); RHS is empty. Derive 0 ∈ ∅.
  have h0L : (0 : Fin 1) ∈ reindex g (existsAlong f ({1} : Set (Fin 2))) := by
    -- g 0 = 0 ∈ f '' {1}  since f 1 = 0 and 1 ∈ {1}.
    rw [reindex, Set.mem_preimage, existsAlong, Set.mem_image]
    exact ⟨1, rfl, rfl⟩
  rw [h] at h0L
  -- RHS membership: 0 = q x with p x ∈ {1}; but p x = 0 ≠ 1.
  rw [existsAlong, Set.mem_image] at h0L
  obtain ⟨x, hx, _⟩ := h0L
  rw [reindex, Set.mem_preimage, p] at hx
  -- hx : (0 : Fin 2) ∈ ({1} : Set (Fin 2))
  exact absurd hx (by decide)

/-- Witness that this square is genuinely NOT a pullback: the pair `(1,0)` is compatible
(`f 1 = g 0`) but has no lift in `P` (every `p x = 0 ≠ 1`). So `PullbackSq f g p q` is FALSE —
the BC hypothesis really is unmet (not merely unverified). -/
theorem not_pullback : ¬ PullbackSq f g p q := by
  intro sq
  obtain ⟨x, hpx, _⟩ := sq.lift 1 0 rfl
  rw [p] at hpx
  exact absurd hpx (by decide)

end BCFails

/-! ### §A.5 TEETH: a NON-monotone reindexing breaks the Galois connection.

The triple needs reindexing to be MONOTONE (order-preserving) — every adjoint is. We exhibit a
concrete order-reversing "reindexing-like" map `c` on `Set (Fin 2)` together with a candidate
left adjoint `l` for which the Galois condition `l S ⊆ T ↔ S ⊆ c T` FAILS, by showing `c` is not
monotone (no monotone-`u` map can sit on the right of a Galois connection). -/

namespace NonMonotone

/-- An order-REVERSING map on `Set (Fin 2)`: complementation `c T := Tᶜ`. (Used as a stand-in
for a "reindexing" that fails to preserve order.) -/
def c : Set (Fin 2) → Set (Fin 2) := fun T => Tᶜ

/-- `c` is NOT monotone — PROVED. `∅ ⊆ univ` but `c univ = ∅ ⊄ univᶜ`... concretely
`c ∅ = univ ⊄ ∅ = c univ` even though `∅ ⊆ univ`. -/
theorem c_not_monotone : ¬ Monotone c := by
  intro hmono
  have : c (∅ : Set (Fin 2)) ⊆ c (Set.univ : Set (Fin 2)) := hmono (Set.empty_subset _)
  -- c ∅ = univ, c univ = ∅, so univ ⊆ ∅, hence 0 ∈ ∅.
  rw [c, c, Set.compl_empty, Set.compl_univ] at this
  exact (this (Set.mem_univ (0 : Fin 2)))

/-- **A non-monotone reindexing admits NO Galois left adjoint — PROVED.** If some `l` made
`GaloisConnection l c` then `c` would be monotone (`gc.monotone_u`); but `c` is not. So the
connection is impossible — the triple genuinely requires monotone reindexing. -/
theorem no_galois_with_nonmonotone_reindex :
    ¬ ∃ l : Set (Fin 2) → Set (Fin 2), GaloisConnection l c := by
  rintro ⟨l, gc⟩
  exact c_not_monotone gc.monotone_u

end NonMonotone

end PartA

/-! ###############################################################################
# PART B — the FAITHFUL relation-form: the Byzantine epistemic fibre.
##################################################################################

Now the previously-deferred, genuinely-deeper fibre. The carrier is the indistinguishability
relation of `Metatheory.EpistemicConsensus.Frame`: `Frame.Knows i φ w = ∀ w', Indist i w' w → φ w'`.
We work over a single agent's relation `R : Ω → Ω → Prop`. For a Byzantine agent `R` is
REFLEXIVE (`indist_refl`) but NOT necessarily symmetric or transitive.

We build the relational quantifiers and prove the genuine adjunction; then we show the clean
Part-A `kernImage` triple does NOT survive the loss of the equivalence structure. -/

namespace PartB

variable {Ω : Type u}

/-- `∃_R` — the relational image / diamond `◇_R`. `relExists R S` = the worlds REACHED from `S`
along `R`: `{w | ∃ s, R s w ∧ s ∈ S}`. (When `R` is the graph of a function `f`, this is `f '' S`;
see `relExists_graph_eq_image`.) -/
def relExists (R : Ω → Ω → Prop) (S : Set Ω) : Set Ω := {w | ∃ s, R s w ∧ s ∈ S}

/-- `∀_R = Knows` — the box `□_R`. `relForall R T` = the worlds ALL of whose `R`-successors lie
in `T`: `{s | ∀ w, R s w → w ∈ T}`. This is precisely `Frame.Knows` along `R` (modulo the
argument order of `Indist`); it is the genuine universal/`∀` modality of the epistemic fibre. -/
def relForall (R : Ω → Ω → Prop) (T : Set Ω) : Set Ω := {s | ∀ w, R s w → w ∈ T}

/-! ### §B.1 The genuine general adjunction `∃_R ⊣ ∀_R` (holds for ANY relation). -/

/-- **`∃_R ⊣ ∀_R`, PROVED for ARBITRARY `R`.** The relational diamond is left adjoint to the
relational box: `relExists R S ⊆ T ↔ S ⊆ relForall R T`. NO equivalence/reflexivity hypothesis is
needed — this is the profunctor/modal adjunction in full generality, and it is the deep fact the
Byzantine fibre DOES keep. -/
theorem relExists_adj_relForall (R : Ω → Ω → Prop) :
    GaloisConnection (relExists R) (relForall R) := by
  intro S T
  constructor
  · -- → : assume ∃_R S ⊆ T. For s ∈ S, w with R s w, then w ∈ ∃_R S ⊆ T.
    intro h s hs
    rw [relForall, Set.mem_setOf_eq]
    intro w hsw
    exact h ⟨s, hsw, hs⟩
  · -- ← : assume S ⊆ ∀_R T. For w ∈ ∃_R S, get s ∈ S with R s w; s ∈ ∀_R T gives w ∈ T.
    rintro h w ⟨s, hsw, hsS⟩
    exact (h hsS) w hsw

/-- The unit `S ⊆ ∀_R (∃_R S)` and counit `∃_R (∀_R T) ⊆ T` of the relational adjunction —
direct consequences, certifying it has content. -/
theorem relForall_relExists_unit (R : Ω → Ω → Prop) (S : Set Ω) :
    S ⊆ relForall R (relExists R S) :=
  (relExists_adj_relForall R).le_u_l S

theorem relExists_relForall_counit (R : Ω → Ω → Prop) (T : Set Ω) :
    relExists R (relForall R T) ⊆ T :=
  (relExists_adj_relForall R).l_u_le T

/-! ### §B.2 PART B contains PART A (not a relabeling): the graph of a function recovers `∃_f ⊣ f*`.

The graph relation `R s w := f s = w` (of an endo-function `f : Ω → Ω`) reduces the relational
quantifiers to Part A's first adjunction: `∃_R = ∃_f = image f` and `∀_R = f* = preimage f`. So the
relational fibre is a STRICT generalization of the function fibre — Part B is genuinely a wider
setting that CONTAINS Part A, not a relabeling of it. -/

/-- **`∃_{graph f}` is `Set.image f` — PROVED.** With `R s w := f s = w`, the relational image is
exactly the set image, so Part B's diamond restricts to Part A's `∃_f`. -/
theorem relExists_graph_eq_image (f : Ω → Ω) (S : Set Ω) :
    relExists (fun s w => f s = w) S = Set.image f S := by
  apply Set.ext; intro w
  simp only [relExists, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨s, hfs, hsS⟩; exact ⟨s, hsS, hfs⟩
  · rintro ⟨s, hsS, hfs⟩; exact ⟨s, hfs, hsS⟩

/-- **`∀_{graph f}` is `Set.preimage f` — PROVED.** With `R s w := f s = w`, the relational box is
exactly the preimage `f* = f⁻¹`, recovering Part A's reindexing. Hence `∃_{graph f} ⊣ ∀_{graph f}`
IS the Part-A adjunction `∃_f ⊣ f*`. -/
theorem relForall_graph_eq_preimage (f : Ω → Ω) (T : Set Ω) :
    relForall (fun s w => f s = w) T = Set.preimage f T := by
  apply Set.ext; intro s
  simp only [relForall, Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · intro h; exact h (f s) rfl
  · intro h w hw; rw [← hw]; exact h

/-! ### §B.3 Reflexivity gives the modal `T`-axioms (the honest-agent core).

`indist_refl` is the only S5 fact `EpistemicConsensus` keeps. It already yields the `T`-axioms:
`□φ → φ` (Knows is veridical) and `φ → ◇φ`. These hold for the Byzantine relation too — it is
still reflexive. -/

/-- **Modal `T` for the box (`□φ → φ`, Knows is veridical) — PROVED from reflexivity.** -/
theorem relForall_le_self {R : Ω → Ω → Prop} (hrefl : ∀ w, R w w) (T : Set Ω) :
    relForall R T ⊆ T := by
  intro s hs
  exact hs s (hrefl s)

/-- **Modal `T` for the diamond (`φ → ◇φ`) — PROVED from reflexivity.** -/
theorem self_le_relExists {R : Ω → Ω → Prop} (hrefl : ∀ w, R w w) (S : Set Ω) :
    S ⊆ relExists R S := by
  intro w hw
  exact ⟨w, hrefl w, hw⟩

/-! ### §B.4 TEETH — the clean Part-A `kernImage` triple does NOT lift to the Byzantine fibre.

This is the substance that makes Part B *different*, not a relabeling. In Part A, `f*` had BOTH a
left adjoint (`∃_f`) and a right adjoint (`∀_f = kernImage`) because `f*` is a frame homomorphism
(equivalently: the function fibre is a QUOTIENT, an equivalence). The box `relForall R` is an
**interior operator (idempotent, S4)** EXACTLY when `R` is reflexive+transitive — and the genuine
quotient (equivalence) is what underwrites the kernImage closure. We show:

  * for an EQUIVALENCE `R`, `relForall R` is idempotent (`□□T = □T`);
  * for a merely-REFLEXIVE Byzantine `R` (reflexive, NOT transitive), `□□T ≠ □T` — S4 BREAKS;
  * and the diamond `∃_R` FAILS to preserve binary meets there (so no clean frame-hom reindexing,
    hence no clean `kernImage`-style further adjoint).

These are concrete on `Fin 3`. -/

/-- **For an equivalence relation the box is IDEMPOTENT (S4) — PROVED.** If `R` is reflexive and
transitive then `relForall R (relForall R T) = relForall R T` (an interior operator). This is the
CLEAN situation — the one Part A's `kernImage` triple lives in. (Symmetry is not even needed for
idempotence; reflexive+transitive = a *preorder* suffices, which is the S4 frame.) -/
theorem relForall_idem_of_preorder {R : Ω → Ω → Prop}
    (hrefl : ∀ w, R w w) (htrans : ∀ a b c, R a b → R b c → R a c) (T : Set Ω) :
    relForall R (relForall R T) = relForall R T := by
  apply Set.ext; intro s
  simp only [relForall, Set.mem_setOf_eq]
  constructor
  · -- □□T ⊆ □T : apply the inner box at the reflexive successor.
    intro h w hsw
    exact h w hsw w (hrefl w)
  · -- □T ⊆ □□T : transitivity closes the two-step reachability.
    intro h w hsw v hwv
    exact h v (htrans s w v hsw hwv)

namespace S4Breaks

/-- A REFLEXIVE but NON-TRANSITIVE (hence non-equivalence) Byzantine relation on `Fin 3`:
`R a b` holds iff `a = b` (reflexive) OR the pair is one of the two "indistinguishability edges"
`0 ∼ 1` and `1 ∼ 2`. Crucially `R 0 1` and `R 1 2` hold but `R 0 2` does NOT — transitivity fails,
modeling a Byzantine agent whose confusion does not chain. -/
def R : Fin 3 → Fin 3 → Prop := fun a b =>
  a = b ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2)

/-- `R` is reflexive — so it IS a faithful indistinguishability relation (it satisfies the only
S5 law `EpistemicConsensus` retains), just not an equivalence. -/
theorem R_refl : ∀ w, R w w := fun _ => Or.inl rfl

/-- `R` is NOT transitive — PROVED. `R 0 1` and `R 1 2` but not `R 0 2`. This is the Byzantine
defect: confusion does not chain. -/
theorem R_not_trans : ¬ (∀ a b c, R a b → R b c → R a c) := by
  intro htrans
  have h01 : R 0 1 := Or.inr (Or.inl ⟨rfl, rfl⟩)
  have h12 : R 1 2 := Or.inr (Or.inr ⟨rfl, rfl⟩)
  have h02 : R 0 2 := htrans 0 1 2 h01 h12
  -- R 0 2 = (0=2) ∨ (0=0∧2=1) ∨ (0=1∧2=2): all disjuncts false.
  rcases h02 with h | h | h
  · exact absurd h (by decide)
  · exact absurd h.2 (by decide)
  · exact absurd h.1 (by decide)

/-- **`R` is a genuine Byzantine indistinguishability relation: reflexive but NOT an equivalence
(it fails transitivity) — PROVED.** This certifies the teeth below are about the *real* gap
between the equivalence (quotient) fibre of Part A and the Byzantine fibre, not a relabeling. -/
theorem R_byzantine_not_equiv :
    (∀ w, R w w) ∧ ¬ (∀ a b c, R a b → R b c → R a c) :=
  ⟨R_refl, R_not_trans⟩

/-- decidability of `R` so we can `decide` membership in the boxes. -/
instance instDecR : DecidableRel R := fun a b => by unfold R; exact inferInstance

/-- The separating target set for the S4 break: `U := {0, 1}` (worlds `0` and `1`). It contains
ALL direct `R`-successors of world `0` (namely `0` and `1`), but does NOT contain world `2`. -/
def U : Set (Fin 3) := {0, 1}

instance : DecidablePred (· ∈ U) := fun w => by unfold U; exact inferInstance

/-- `0 ∈ □U` — PROVED. Every direct successor of `0` (i.e. `0` and `1`) lies in `U = {0,1}`.
We unfold the box to the concrete decidable `Fin 3` proposition and `decide`. -/
theorem zero_mem_box : (0 : Fin 3) ∈ relForall R U := by
  show ∀ w, R 0 w → w ∈ U
  decide

/-- `0 ∉ □□U` — PROVED. The successor `1` of `0` is NOT in `□U` (because `1`'s successor `2 ∉ U`),
so `0` cannot have all its successors in `□U`. This is the FAILURE of positive introspection (the
modal "4" axiom) caused by `R 0 1`, `R 1 2`, `¬ R 0 2` — the Byzantine non-transitivity. -/
theorem zero_not_mem_box_box : (0 : Fin 3) ∉ relForall R (relForall R U) := by
  show ¬ ∀ w, R 0 w → (∀ v, R w v → v ∈ U)
  decide

/-- **`□□U ≠ □U` — the concrete S4 failure, PROVED.**

`□U = {s | every R-successor of s is in {0,1}}`; one computes `0 ∈ □U` (successors `{0,1} ⊆ U`).
`□□U = {s | every R-successor of s is in □U}`; but `0`'s successor `1 ∉ □U` (since `1 →R 2 ∉ U`),
so `0 ∉ □□U`. The two boxes therefore DISAGREE at world `0`. Hence on a reflexive-but-NON-transitive
(Byzantine) relation the box `∀_R` is NOT idempotent — the clean S4/interior structure of
`relForall_idem_of_preorder` (and with it Part A's `kernImage` closure) genuinely FAILS. -/
theorem box_box_ne_box :
    relForall R (relForall R U) ≠ relForall R U := by
  intro h
  -- `0 ∈ □U` (proved) but `0 ∉ □□U` (proved); the equality `h` makes them coincide. Contradiction.
  exact zero_not_mem_box_box (h.symm ▸ zero_mem_box)

end S4Breaks

namespace DiamondNotMeet

open S4Breaks (R)

/-- **The diamond `∃_R` FAILS to preserve binary meets for the Byzantine relation — PROVED.**

For Part A, the right-adjoint `kernImage` exists because `f* = preimage` preserves ALL meets AND
joins (a frame homomorphism). The relational `∃_R` (diamond) is a LEFT adjoint, so it preserves
joins but generally NOT meets. We exhibit `∃_R (S₁ ∩ S₂) ≠ ∃_R S₁ ∩ ∃_R S₂` concretely with
OVERLAPPING images: `S₁ := {0}`, `S₂ := {1}`. Then `∃_R {0} = {0,1}` (successors of `0`) and
`∃_R {1} = {1,2}` (successors of `1`), so their meet is `{1}`. But `S₁ ∩ S₂ = {0} ∩ {1} = ∅`, so
`∃_R (S₁ ∩ S₂) = ∅ ≠ {1}`: the diamond manufactures an element `1` in the meet of the images that
is NOT in the image of the meet. So `∃_R` is not a meet-homomorphism, hence there is no clean
`kernImage`-style two-sided closure in the Byzantine fibre. -/
def S1 : Set (Fin 3) := {0}
def S2 : Set (Fin 3) := {1}

instance : DecidablePred (· ∈ S1) := fun w => by unfold S1; exact inferInstance
instance : DecidablePred (· ∈ S2) := fun w => by unfold S2; exact inferInstance

/-- `1 ∈ ∃_R S1 ∩ ∃_R S2` — PROVED. World `1` is reached from `0 ∈ S1` (via `R 0 1`) and from
`1 ∈ S2` (via `R 1 1`), so it lies in BOTH images, hence in their meet. We unfold the diamond to
its concrete decidable `Fin 3` form and `decide`. -/
theorem one_mem_inter_dia : (1 : Fin 3) ∈ relExists R S1 ∩ relExists R S2 := by
  show (∃ s, R s 1 ∧ s ∈ S1) ∧ (∃ s, R s 1 ∧ s ∈ S2)
  decide

/-- `1 ∉ ∃_R (S1 ∩ S2)` — PROVED. `S1 ∩ S2 = {0} ∩ {1} = ∅`, and the diamond of the empty set is
empty: there is no source `s` for world `1`. -/
theorem one_not_mem_dia_inter : (1 : Fin 3) ∉ relExists R (S1 ∩ S2) := by
  show ¬ ∃ s, R s 1 ∧ s ∈ S1 ∩ S2
  decide

/-- **The diamond `∃_R` FAILS to preserve binary meets — PROVED.** `1 ∈ ∃_R S1 ∩ ∃_R S2` but
`1 ∉ ∃_R (S1 ∩ S2)`, so `∃_R (S1 ∩ S2) ≠ ∃_R S1 ∩ ∃_R S2`: the diamond is not a meet-homomorphism.
(For Part A's function fibre, by contrast, the right adjoint `kernImage = ∀_f` exists precisely
because reindexing `f*` preserves all meets and joins — a frame homomorphism. The Byzantine fibre
has no such clean two-sided closure.) -/
theorem diamond_not_inf :
    relExists R (S1 ∩ S2) ≠ relExists R S1 ∩ relExists R S2 := by
  intro h
  exact one_not_mem_dia_inter (h.symm ▸ one_mem_inter_dia)

end DiamondNotMeet

/-! ### §B.5 The de Morgan ◇/□ MATE (`◇ = ¬□¬`), faithfully for ANY relation.

In modal logic the diamond is the de Morgan dual of the box: `◇φ = ¬□¬φ`. The SUBTLETY for a
faithful relational reading is the DIRECTION of `R`. Our `relExists R S = {w | ∃ s, R s w ∧ s ∈ S}`
pushes `S` FORWARD along `R` (predecessors-in-`S`), whereas `relForall R T = {s | ∀ w, R s w → w ∈ T}`
quantifies over `R`-SUCCESSORS. So `(relForall R Sᶜ)ᶜ` is the diamond of the CONVERSE relation, not
of `R` itself. We make this precise: the mate holds with the converse `Rᵒᵖ`, for EVERY relation, and
we show by concrete teeth that the *naive same-`R*` mate `relExists R = (relForall R ·ᶜ)ᶜ` FAILS on a
non-symmetric (Byzantine) relation — so the converse is genuinely load-bearing, not cosmetic. -/

/-- The CONVERSE / opposite relation `Rᵒᵖ s w := R w s`. -/
def converse (R : Ω → Ω → Prop) : Ω → Ω → Prop := fun s w => R w s

/-- **The de Morgan ◇/□ MATE, PROVED for ARBITRARY `R`.** `◇ = ¬□¬`, in the faithful relational
form that respects direction: `relExists (Rᵒᵖ) S = (relForall R Sᶜ)ᶜ`. Equivalently the diamond of
`R` is `¬□¬` of the CONVERSE box. No symmetry/reflexivity is assumed — pure classical de Morgan over
the successor quantifier. -/
theorem relExists_converse_eq_compl_relForall_compl (R : Ω → Ω → Prop) (S : Set Ω) :
    relExists (converse R) S = (relForall R Sᶜ)ᶜ := by
  apply Set.ext; intro s
  rw [Set.mem_compl_iff]
  show (∃ w, R s w ∧ w ∈ S) ↔ ¬ (∀ w, R s w → w ∈ Sᶜ)
  constructor
  · -- ∃ w, R s w ∧ w ∈ S  ⇒  ¬ ∀ w, R s w → w ∈ Sᶜ
    rintro ⟨w, hsw, hwS⟩ hcon
    exact (hcon w hsw) hwS
  · -- ¬ ∀ w, R s w → w ∈ Sᶜ  ⇒  ∃ w, R s w ∧ w ∈ S
    intro hcon
    by_contra hne
    apply hcon
    intro w hsw
    rw [Set.mem_compl_iff]
    intro hwS
    exact hne ⟨w, hsw, hwS⟩

/-- **The MATE, written the other way: `◇_R = ¬□_{Rᵒᵖ}¬`, PROVED.** `relExists R S = (relForall Rᵒᵖ Sᶜ)ᶜ`.
This is the same de Morgan law solved for `relExists R` (apply the previous lemma to `Rᵒᵖ` and use
`converse (converse R) = R`). -/
theorem relExists_eq_compl_relForall_converse_compl (R : Ω → Ω → Prop) (S : Set Ω) :
    relExists R S = (relForall (converse R) Sᶜ)ᶜ := by
  have h := relExists_converse_eq_compl_relForall_compl (converse R) S
  -- converse (converse R) = R definitionally.
  simpa [converse] using h

/-- **The box as the de Morgan dual of the diamond: `□_R = ¬◇_{Rᵒᵖ}¬`, PROVED.** The mate read the
other direction: `relForall R T = (relExists (Rᵒᵖ) Tᶜ)ᶜ`. -/
theorem relForall_eq_compl_relExists_converse_compl (R : Ω → Ω → Prop) (T : Set Ω) :
    relForall R T = (relExists (converse R) Tᶜ)ᶜ := by
  rw [relExists_converse_eq_compl_relForall_compl, compl_compl, compl_compl]

namespace MateNeedsConverse

open S4Breaks (R instDecR)

/-- The separating witness set for the naive-mate failure: `S := {1}`. -/
def Smate : Set (Fin 3) := {1}

instance : DecidablePred (· ∈ Smate) := fun w => by unfold Smate; exact inferInstance
instance : DecidablePred (· ∈ (Smate : Set (Fin 3))ᶜ) := fun w => by
  unfold Smate; exact inferInstance

/-- `2 ∈ relExists R {1}` — PROVED. World `2` is an `R`-successor of `1 ∈ {1}` (`R 1 2`), so it is
reached forward along `R`. -/
theorem two_mem_relExists : (2 : Fin 3) ∈ relExists R Smate := by
  show ∃ s, R s 2 ∧ s ∈ Smate
  decide

/-- `2 ∉ (relForall R {1}ᶜ)ᶜ` — PROVED, equivalently `2 ∈ relForall R {1}ᶜ`. World `2`'s only
`R`-successor is `2` itself, which lies in `{1}ᶜ`; so all of `2`'s successors avoid `{1}`. -/
theorem two_not_mem_naive_mate :
    (2 : Fin 3) ∉ (relForall R (Smate : Set (Fin 3))ᶜ)ᶜ := by
  -- `2 ∉ Xᶜ` ↔ `2 ∈ X`; show membership in the box directly.
  rw [Set.mem_compl_iff, not_not]
  show ∀ w, R 2 w → w ∈ (Smate : Set (Fin 3))ᶜ
  decide

/-- **The NAIVE same-`R` mate FAILS — PROVED.** `relExists R S ≠ (relForall R Sᶜ)ᶜ` on the Byzantine
(non-symmetric) relation with `S = {1}`: world `2` lies in the forward-diamond `◇_R{1}` (it is an
`R`-successor of `1`) but NOT in `(□_R {1}ᶜ)ᶜ` (which is the diamond of the CONVERSE — predecessors).
So `◇ = ¬□¬` is only faithful with the converse relation; on a non-symmetric relation the directions
genuinely differ. (For a SYMMETRIC `R`, `converse R = R` and the two coincide — recovering the
classical S5 mate.) -/
theorem naive_mate_fails :
    relExists R Smate ≠ (relForall R (Smate : Set (Fin 3))ᶜ)ᶜ := by
  intro h
  exact two_not_mem_naive_mate (h ▸ two_mem_relExists)

/-- For a SYMMETRIC relation the naive same-`R` mate DOES hold — the converse is `R` itself. This
certifies the teeth above are about asymmetry, not a defect of the law: `relExists R S = (relForall R Sᶜ)ᶜ`
whenever `R` is symmetric. -/
theorem naive_mate_holds_of_symm {R : Ω → Ω → Prop} (hsymm : ∀ a b, R a b → R b a) (S : Set Ω) :
    relExists R S = (relForall R Sᶜ)ᶜ := by
  have hReq : converse R = R := by
    funext a b
    show R b a = R a b
    exact propext ⟨fun h => hsymm b a h, fun h => hsymm a b h⟩
  rw [← relExists_converse_eq_compl_relForall_compl, hReq]

end MateNeedsConverse

/-! ### §B.6 Relational FROBENIUS reciprocity for `∃_R ⊣ ∀_R`.

The hyperdoctrine projection formula in Part A was the EQUALITY `∃_f(S ∩ f*T) = ∃_f S ∩ T`, available
because `f*` is a frame homomorphism. For a general relation the literal posetal equality
`relExists R (S ∩ relForall R T) = relExists R S ∩ T` FAILS (non-functional `R`). What genuinely holds
— and is the honest relational Frobenius / projection LAX law — is the `⊆` half, valid for EVERY `R`:

      relExists R (S ∩ relForall R T) ⊆ relExists R S ∩ T.

We prove it, prove that on a SURJECTIVE-image / functional structure the reverse also holds
(recovering the Part-A equality via the graph), and add teeth showing the reverse — hence the naive
posetal equality — FAILS on the Byzantine relation. -/

/-- **Relational Frobenius reciprocity (the LAX `⊆` half), PROVED for ARBITRARY `R`.**
`relExists R (S ∩ relForall R T) ⊆ relExists R S ∩ T`. This is the genuine projection formula that
survives the loss of functoriality: any world reached from a source that is in `S` AND knows `T` is
both in `∃_R S` and (being a successor of a `T`-knower) in `T`. -/
theorem frobenius_le (R : Ω → Ω → Prop) (S T : Set Ω) :
    relExists R (S ∩ relForall R T) ⊆ relExists R S ∩ T := by
  rintro w ⟨s, hsw, hsS, hsT⟩
  refine ⟨⟨s, hsw, hsS⟩, ?_⟩
  exact hsT w hsw

/-- The reverse inclusion holds when every source's `R`-successors are forced into `T` once a single
named successor is — concretely, when `R` is the **graph of a function** (each source has a UNIQUE
successor). Then `relExists R (S ∩ relForall R T) = relExists R S ∩ T`, recovering Part A's Frobenius
equality inside the relational fibre. -/
theorem frobenius_eq_graph (f : Ω → Ω) (S T : Set Ω) :
    relExists (fun s w => f s = w) (S ∩ relForall (fun s w => f s = w) T)
      = relExists (fun s w => f s = w) S ∩ T := by
  apply Set.Subset.antisymm (frobenius_le _ S T)
  rintro w ⟨⟨s, hfs, hsS⟩, hwT⟩
  refine ⟨s, hfs, hsS, ?_⟩
  -- s's unique successor is f s = w ∈ T.
  intro v hv
  rw [← hv, hfs]; exact hwT

namespace FrobeniusFails

open S4Breaks (R instDecR)

/-- Frobenius witnesses: source set `S := {0}`, target set `T := {1}`. -/
def Sf : Set (Fin 3) := {0}
def Tf : Set (Fin 3) := {1}

instance : DecidablePred (· ∈ Sf) := fun w => by unfold Sf; exact inferInstance
instance : DecidablePred (· ∈ Tf) := fun w => by unfold Tf; exact inferInstance

/-- `1 ∈ relExists R S ∩ T` — PROVED. `1` is an `R`-successor of `0 ∈ S` (`R 0 1`) and `1 ∈ T`. -/
theorem one_mem_rhs : (1 : Fin 3) ∈ relExists R Sf ∩ Tf := by
  show (∃ s, R s 1 ∧ s ∈ Sf) ∧ (1 : Fin 3) ∈ Tf
  decide

/-- `1 ∉ relExists R (S ∩ relForall R T)` — PROVED. The only source for `1` in `S = {0}` is `0`, but
`0 ∉ relForall R T = □_R{1}` (because `0`'s successor `1`... wait, `0` also sees `0 ∉ {1}`), so the
intersection `S ∩ □_R T` is empty over the relevant source. Hence `1` has no qualifying source. -/
theorem one_not_mem_lhs : (1 : Fin 3) ∉ relExists R (Sf ∩ relForall R Tf) := by
  show ¬ ∃ s, R s 1 ∧ s ∈ Sf ∧ (∀ w, R s w → w ∈ Tf)
  decide

/-- **The naive posetal Frobenius EQUALITY FAILS — PROVED.**
`relExists R (S ∩ relForall R T) ≠ relExists R S ∩ T` on the Byzantine relation with `S = {0}`,
`T = {1}`: world `1` is in the RHS (it is an `R`-successor of the `S`-element `0`, and `1 ∈ T`) but
NOT in the LHS (the only `S`-source `0` does NOT know `T` — `0` also `R`-sees `0 ∉ T`). So the
reverse (`⊇`) of `frobenius_le` is false here; only the LAX `⊆` half is a theorem for general `R`.
(For the function/graph fibre the equality is restored — `frobenius_eq_graph`.) -/
theorem frobenius_eq_fails :
    relExists R (Sf ∩ relForall R Tf) ≠ relExists R Sf ∩ Tf := by
  intro h
  exact one_not_mem_lhs (h ▸ one_mem_rhs)

end FrobeniusFails

/-! ### §B.7 Relational composition functoriality / Beck–Chevalley.

`relExists` is a (covariant) FUNCTOR from the category of relations (under composition) to
endomaps of `Set Ω`, and `relForall` is the corresponding CONTRAVARIANT functor (it reverses
composition). With `relComp R S` meaning "apply `S`, then `R`" (function-composition order,
`(R∘S) a c := ∃ b, S a b ∧ R b c`):

  * `relExists (R ∘ S) = relExists R ∘ relExists S`   (∃ is functorial / covariant in the relation);
  * `relForall (R ∘ S) = relForall S ∘ relForall R`   (□ reverses composition / is contravariant).

These are the relational Beck–Chevalley / functoriality coherences. They hold for ANY relations,
with no pullback hypothesis — composition of relations is total, so the relational fibre satisfies
the coherence UNCONDITIONALLY (contrast Part A, where Beck–Chevalley needed a genuine pullback). -/

/-- Relation composition in function-composition order: `relComp R S` first applies `S`, then `R`.
`(R ∘ S) a c := ∃ b, S a b ∧ R b c`. -/
def relComp (R S : Ω → Ω → Prop) : Ω → Ω → Prop := fun a c => ∃ b, S a b ∧ R b c

/-- **∃ is FUNCTORIAL in the relation (relational Beck–Chevalley for the diamond), PROVED.**
`relExists (relComp R S) = relExists R ∘ relExists S` for ALL relations — no pullback needed. -/
theorem relExists_comp (R S : Ω → Ω → Prop) :
    relExists (relComp R S) = relExists R ∘ relExists S := by
  funext X
  apply Set.ext; intro c
  simp only [relComp, relExists, Function.comp_apply, Set.mem_setOf_eq]
  constructor
  · -- ∃ a, (∃ b, S a b ∧ R b c) ∧ a ∈ X  ⇒  ∃ b, R b c ∧ (∃ a, S a b ∧ a ∈ X)
    rintro ⟨a, ⟨b, hSab, hRbc⟩, haX⟩
    exact ⟨b, hRbc, a, hSab, haX⟩
  · -- ∃ b, R b c ∧ (∃ a, S a b ∧ a ∈ X)  ⇒  ∃ a, (∃ b, S a b ∧ R b c) ∧ a ∈ X
    rintro ⟨b, hRbc, a, hSab, haX⟩
    exact ⟨a, ⟨b, hSab, hRbc⟩, haX⟩

/-- **□ REVERSES composition (contravariant functoriality / box Beck–Chevalley), PROVED.**
`relForall (relComp R S) = relForall S ∘ relForall R` for ALL relations. The box of a composite is
the box of the FIRST step applied to the box of the SECOND — the order flips, as a right adjoint /
contravariant assignment must. -/
theorem relForall_comp (R S : Ω → Ω → Prop) :
    relForall (relComp R S) = relForall S ∘ relForall R := by
  funext T
  apply Set.ext; intro a
  simp only [relComp, relForall, Function.comp_apply, Set.mem_setOf_eq]
  constructor
  · -- (∀ c, (∃ b, S a b ∧ R b c) → c ∈ T)  ⇒  ∀ b, S a b → ∀ c, R b c → c ∈ T
    intro h b hSab c hRbc
    exact h c ⟨b, hSab, hRbc⟩
  · -- ∀ b, S a b → ∀ c, R b c → c ∈ T  ⇒  ∀ c, (∃ b, S a b ∧ R b c) → c ∈ T
    rintro h c ⟨b, hSab, hRbc⟩
    exact h b hSab c hRbc

/-- **Functoriality is genuinely COMPATIBLE with the adjunction: the composite still adjoins.**
`relExists (R ∘ S) ⊣ relForall (R ∘ S)`, and by the two functoriality laws this is exactly
`(relExists R ∘ relExists S) ⊣ (relForall S ∘ relForall R)` — the adjunction of a composite of
adjunctions, with the right adjoints composing in reverse. A non-vacuous corollary tying §B.1 to
§B.7. -/
theorem comp_adjunction (R S : Ω → Ω → Prop) :
    GaloisConnection (relExists R ∘ relExists S) (relForall S ∘ relForall R) := by
  rw [← relExists_comp, ← relForall_comp]
  exact relExists_adj_relForall (relComp R S)

namespace CompFunctorial

open S4Breaks (R instDecR)

/-- A SECOND concrete relation on `Fin 3` to compose with the Byzantine `R`, so the functoriality
laws are exercised on a non-trivial composite (not just `R ∘ R`). `Q a b` holds iff `a = b` or the
single extra edge `2 ∼ 0`. -/
def Q : Fin 3 → Fin 3 → Prop := fun a b => a = b ∨ (a = 2 ∧ b = 0)

instance instDecQ : DecidableRel Q := fun a b => by unfold Q; exact inferInstance

/-- A discriminating probe set. -/
def W : Set (Fin 3) := {2}

instance : DecidablePred (· ∈ W) := fun w => by unfold W; exact inferInstance

/-- The composite diamond is NON-TRIVIAL here — `relExists (relComp R Q) {2}` actually reaches new
worlds, so the functoriality law `relExists_comp` is not asserting an identity on trivial data.
`relComp R Q` first does `Q` (so `2 → 0` and `2 → 2`), then `R` (so `0 → {0,1}`, `2 → 2`); starting
from `{2}` this reaches `{0,1,2}`. We verify `1 ∈ relExists (relComp R Q) {2}` — a world UNREACHABLE
by `R` alone from `{2}` (since `R 2 1` is false), proving the composite is genuinely richer. -/
theorem one_mem_comp_dia : (1 : Fin 3) ∈ relExists (relComp R Q) W := by
  show ∃ a, (∃ b, Q a b ∧ R b 1) ∧ a ∈ W
  decide

/-- And `1 ∉ relExists R {2}` — confirming the composite reaches strictly more than `R` alone, so
`relExists_comp` (which equates the composite diamond with `relExists R ∘ relExists Q`) carries real
content on this data. -/
theorem one_not_mem_single_dia : (1 : Fin 3) ∉ relExists R W := by
  show ¬ ∃ s, R s 1 ∧ s ∈ W
  decide

/-- **Functoriality VERIFIED on the concrete composite — PROVED.** The general law `relExists_comp`
specialized to `R`, `Q`, `{2}` gives `relExists (relComp R Q) {2} = (relExists R ∘ relExists Q) {2}`;
combined with `one_mem_comp_dia` this exhibits `1` on the right-hand side too, certifying the law is
non-vacuous on discriminating data (the composite genuinely reaches `1`, unreachable by `R` alone). -/
theorem comp_dia_reaches_one :
    (1 : Fin 3) ∈ (relExists R ∘ relExists Q) W := by
  rw [← relExists_comp]; exact one_mem_comp_dia

end CompFunctorial

end PartB

/-! ###############################################################################
# Kernel-clean pins (`#assert_axioms`).
##################################################################################
Every keystone of BOTH parts is pinned to the kernel triple `{propext, Classical.choice,
Quot.sound}`. A `sorryAx` or stray `axiom` would fail the pin and the build. -/

-- PART A: the posetal triple, Frobenius, Beck–Chevalley, and the teeth.
#assert_axioms PartA.existsAlong_adj_reindex
#assert_axioms PartA.reindex_adj_forallAlong
#assert_axioms PartA.lawvere_triple
#assert_axioms PartA.frobenius
#assert_axioms PartA.beck_chevalley
#assert_axioms PartA.canonicalPullback
#assert_axioms PartA.BCFails.beck_chevalley_fails
#assert_axioms PartA.BCFails.not_pullback
#assert_axioms PartA.NonMonotone.c_not_monotone
#assert_axioms PartA.NonMonotone.no_galois_with_nonmonotone_reindex

-- PART B: the relational adjunction, the Part-A bridge, the T-axioms, and the teeth.
#assert_axioms PartB.relExists_adj_relForall
#assert_axioms PartB.relExists_graph_eq_image
#assert_axioms PartB.relForall_graph_eq_preimage
#assert_axioms PartB.relForall_le_self
#assert_axioms PartB.self_le_relExists
#assert_axioms PartB.relForall_idem_of_preorder
#assert_axioms PartB.S4Breaks.R_not_trans
#assert_axioms PartB.S4Breaks.box_box_ne_box
#assert_axioms PartB.DiamondNotMeet.diamond_not_inf

-- PART B frontier: de Morgan mate, relational Frobenius, composition functoriality, + their teeth.
#assert_axioms PartB.relExists_converse_eq_compl_relForall_compl
#assert_axioms PartB.relExists_eq_compl_relForall_converse_compl
#assert_axioms PartB.relForall_eq_compl_relExists_converse_compl
#assert_axioms PartB.MateNeedsConverse.naive_mate_fails
#assert_axioms PartB.MateNeedsConverse.naive_mate_holds_of_symm
#assert_axioms PartB.frobenius_le
#assert_axioms PartB.frobenius_eq_graph
#assert_axioms PartB.FrobeniusFails.frobenius_eq_fails
#assert_axioms PartB.relExists_comp
#assert_axioms PartB.relForall_comp
#assert_axioms PartB.comp_adjunction
#assert_axioms PartB.CompFunctorial.comp_dia_reaches_one

end Dregg2.Metatheory.Lawvere
