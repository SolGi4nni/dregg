/-
# Metatheory.Categorical — deriving the abstract spec from categorical first principles.

`Dregg2.*` postulates its spec structures as fields or named constructions. This module
takes minimal categorical axioms and derives them as consequences (kernel-clean,
`#assert_axioms`-pinned, zero `sorry`).

- **§1 Conservation.** From "`Σ` is a lax monoidal functor `C ⥤ Discrete M`" we derive
  `Σ̃(A⊗B) = Σ̃A + Σ̃B` (tensorator `μ`) and `Σ̃ I = 0` (unit `ε`), recovering
  `Dregg2.Core.Conservation.tensor_add`/`unit_zero` as consequences. No-free-copy follows:
  a copy map `Δ : A ⟶ A⊗A` forces `Σ̃A = 0` in a cancellative `M`.
- **§2 The verify/find seam.** `Predicate ⊣ Witness` as a `GaloisConnection`; attenuation,
  demand/supply round-trips, and closure idempotence as standard adjunction consequences.
- **§3 Coalgebra and pullbacks.** The cell as an `F`-coalgebra; the hyperedge/JointTurn as
  a (wide) pullback — stated via `CategoryTheory.Limits`. Final-coalgebra existence is OPEN
  (closed in `Metatheory.Open.FinalCoalgebra`).

Honesty caveat (§1): functoriality into a discrete target is thin — the coherence diagrams
are vacuous (every diagram in a discrete category commutes). The honest content of
"conservation = a lax monoidal functor to `Discrete M`" is monoid-hom on counts plus
invariance on morphisms. We derive precisely that and no more.
-/
import Dregg2.Core
import Dregg2.Laws
import Dregg2.Tactics
import Dregg2.Finality
import Dregg2.Confluence
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Hom.Lattice

namespace Metatheory

open CategoryTheory MonoidalCategory

universe u v w

/-! # §1. Conservation, derived from a lax monoidal functor to a discrete monoid.

`Dregg2.Core` postulates the conservation measure's two monoid-hom equations as fields.
Here we derive them from the single datum that conservation is a lax monoidal functor
`Σ : C ⥤ Discrete M` — extracted by reading off the coherence morphisms `ε`/`μ` through
`Discrete.eq_of_hom`. -/

section Conservation

open Functor.LaxMonoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {M : Type w} [AddCommMonoid M]

/-- The conservation measure read off a lax monoidal functor to the discrete monoid:
`Σ̃ A := (Σ.obj A).as` — the count assigned to a cell. -/
def measure (Sig : C ⥤ Discrete M) (A : C) : M := (Sig.obj A).as

/-- The unit law `Σ̃ I = 0`, derived (not assumed). The lax-monoidal unit coherence morphism
`ε Σ : 𝟙_(Discrete M) ⟶ Σ.obj (𝟙_ C)` is, in a discrete category, an equality of objects
(`Discrete.eq_of_hom`). This recovers `Dregg2.Core.Conservation.unit_zero` as a theorem. -/
theorem measure_unit (Sig : C ⥤ Discrete M) [Sig.LaxMonoidal] :
    measure Sig (𝟙_ C) = 0 := by
  -- `ε Sig : 𝟙_ (Discrete M) ⟶ Sig.obj (𝟙_ C)` is a morphism in a discrete category…
  have h := Discrete.eq_of_hom (ε Sig)
  -- …so it forces `(𝟙_ (Discrete M)).as = (Sig.obj (𝟙_ C)).as`. The LHS is `0`.
  simpa [measure, Discrete.addMonoidal_tensorUnit_as] using h.symm

/-- The additivity law `Σ̃(A⊗B) = Σ̃A + Σ̃B`, derived (not assumed). The lax-monoidal
tensorator `μ Σ A B` is an equality by `Discrete.eq_of_hom`. Recovers
`Dregg2.Core.Conservation.tensor_add` as a consequence of the functor's coherence. -/
theorem measure_tensor (Sig : C ⥤ Discrete M) [Sig.LaxMonoidal] (A B : C) :
    measure Sig (A ⊗ B) = measure Sig A + measure Sig B := by
  have h := Discrete.eq_of_hom (μ Sig A B)
  simpa [measure, Discrete.addMonoidal_tensorObj_as] using h.symm

set_option linter.unusedSectionVars false in
/-- Invariance along ordinary turns `Σ̃ A = Σ̃ B`, derived. Any morphism `f : A ⟶ B` in
`C` is sent by `Σ` to a morphism in the discrete target, which by `Discrete.eq_of_hom` is
the equation `Σ̃ A = Σ̃ B`. Recovers `Dregg2.Core.conservation_ordinary` as bare
functoriality into a discrete category. Needs neither `MonoidalCategory C` nor
`AddCommMonoid M`; the unused-section-variable linter is locally silenced. -/
theorem measure_invariant (Sig : C ⥤ Discrete M) {A B : C} (f : A ⟶ B) :
    measure Sig A = measure Sig B :=
  Discrete.eq_of_hom (Sig.map f)

/-- No-free-copy, derived categorically. A copy map `copy : A ⟶ A ⊗ A` is sent by `Σ`
to a morphism forcing `Σ̃A = Σ̃A + Σ̃A`; in a cancellative `M` that gives `Σ̃A = 0`.
No conservation-respecting duplication of a non-empty resource is possible. This is the
categorical source of `Dregg2.Core.withholding_no_free_copy`. (We use the bare morphism
rather than `ComonObj` because `Mathlib.CategoryTheory.Monoidal.Comon_` is not in this
lib's pinned mathlib slice; the argument needs only `Σ.map copy`.) -/
theorem no_free_copy [IsCancelAdd M]
    (Sig : C ⥤ Discrete M) [Sig.LaxMonoidal] (A : C) (copy : A ⟶ A ⊗ A) :
    measure Sig A = 0 := by
  -- the copy map, mapped through `Sig`, is invariant: `Σ̃ A = Σ̃ (A ⊗ A)`.
  have hinv : measure Sig A = measure Sig (A ⊗ A) := measure_invariant Sig copy
  -- additivity unfolds the target: `Σ̃ (A ⊗ A) = Σ̃ A + Σ̃ A`.
  rw [measure_tensor Sig A A] at hinv
  -- `Σ̃ A = Σ̃ A + Σ̃ A` ⟹ `Σ̃ A = 0` by left-cancellation.
  exact left_eq_add.mp hinv

/-! ### §1(a): conservation is substructurality (the absence of a natural Δ).

`no_free_copy` shows a single copy morphism forces `Σ̃A = 0`. The structural reading:
- **Linear (no copy):** a family `δ A : A ⟶ A ⊗ A` forces every count to `0`. A
  cartesian (diagonal-bearing) structure is incompatible with non-trivial conservation.
- **Affine (no discard):** a discard `wk A : A ⟶ I` forces `Σ̃A = Σ̃I = 0`. Conservation
  tolerates neither contraction nor weakening — the linear discipline. -/

set_option linter.unusedSectionVars false in
/-- No-free-discard (affine reading), derived. A discard `wk : A ⟶ 𝟙_ C` forces `Σ̃A = 0`
via `Σ̃A = Σ̃I = 0`. No counted resource may be silently dropped. Needs no cancellativity. -/
theorem no_free_discard (Sig : C ⥤ Discrete M) [Sig.LaxMonoidal] (A : C)
    (wk : A ⟶ 𝟙_ C) : measure Sig A = 0 := by
  rw [measure_invariant Sig wk]; exact measure_unit Sig

/-- A global diagonal collapses the whole measure (linear reading), derived. If `C` carries
diagonal components `δ A : A ⟶ A ⊗ A` for every object, then `∀ A, Σ̃A = 0`. Any
non-trivial conservation measure therefore witnesses the absence of a global diagonal:
a cartesian monoidal category admits no faithful conservation. -/
theorem diagonal_collapses_measure [IsCancelAdd M]
    (Sig : C ⥤ Discrete M) [Sig.LaxMonoidal]
    (δ : ∀ A : C, A ⟶ A ⊗ A) : ∀ A : C, measure Sig A = 0 :=
  fun A => no_free_copy Sig A (δ A)

/-- A non-zero count forbids a global diagonal: a conservation functor with any non-zero
count witnesses that `C` is genuinely substructural (non-cartesian) on the resource
fragment. The absence of a natural copy and a non-trivial conservation are contradictory. -/
theorem nonzero_count_forbids_diagonal [IsCancelAdd M]
    (Sig : C ⥤ Discrete M) [Sig.LaxMonoidal]
    {A : C} (hA : measure Sig A ≠ 0) : ¬ ∃ δ : ∀ A : C, A ⟶ A ⊗ A, True :=
  fun ⟨δ, _⟩ => hA (diagonal_collapses_measure Sig δ A)

/-- Bridge to the postulated spec: every lax monoidal functor `Σ : C ⥤ Discrete M` induces
the monoid-hom data that `Dregg2.Core.Conservation` postulates as fields. `unit_zero` and
`tensor_add` are now theorems (`measure_unit`/`measure_tensor`). The full `Conservation`
structure additionally carries mint/burn bookkeeping (operational, not categorical); we
derive only the monoid-hom core. -/
theorem conservation_core_derived (Sig : C ⥤ Discrete M) [Sig.LaxMonoidal] :
    (measure Sig (𝟙_ C) = 0) ∧
      (∀ A B : C, measure Sig (A ⊗ B) = measure Sig A + measure Sig B) :=
  ⟨measure_unit Sig, measure_tensor Sig⟩

end Conservation

/-! ### §1 honesty caveat.

`measure_unit`/`measure_tensor`/`measure_invariant` are the entire content of "`Σ` is a
monoidal functor to `Discrete M`": the coherence diagrams are vacuous (every diagram in a
discrete category commutes). We have derived monoid-hom + invariance, and only that. -/

/-! # §2. The verify/find seam, derived as a Galois connection.

We take "the seam is a `GaloisConnection demand supply`" as the single datum and derive
the seam's operational laws — attenuation, round-trips, closure idempotence — as standard
adjunction consequences. None is separately postulated; each is `GaloisConnection.*`. -/

section Seam

variable {Demand : Type u} {Supply : Type v}
-- `Supply` is a `PartialOrder` (closure idempotence uses antisymmetry);
-- `Demand` a `Preorder` suffices for the round-trips.
variable [Preorder Demand] [PartialOrder Supply]

/-- The verify/find seam as a single categorical datum: `realizes` and `verifies` form a
`GaloisConnection` (`realizes ⊣ verifies`). This is the abstract `Predicate ⊣ Witness` of
`Dregg2.Laws`, stated as the seam's defining property. -/
structure Seam where
  /-- Left adjoint: the (strongest) demand a supply realizes. -/
  realizes : Supply → Demand
  /-- Right adjoint: the (weakest) supply that verifies a demand. -/
  verifies : Demand → Supply
  /-- The adjunction: `realizes s ≤ d ↔ s ≤ verifies d` (demand⊣supply). -/
  adj : GaloisConnection realizes verifies

variable (S : Seam (Demand := Demand) (Supply := Supply))

/-- Attenuation is monotone: the right adjoint `verifies` is monotone (`GaloisConnection.monotone_u`).
A weaker demand is verified by a weaker supply. -/
theorem seam_attenuate_monotone : Monotone S.verifies :=
  S.adj.monotone_u

/-- `realizes` is monotone too — `GaloisConnection.monotone_l`. -/
theorem seam_realizes_monotone : Monotone S.realizes :=
  S.adj.monotone_l

/-- Supply round-trip (adjunction unit): `s ≤ verifies (realizes s)` — supply re-verified
after demand-extraction is at least as strong. `GaloisConnection.le_u_l`. -/
theorem seam_unit (s : Supply) : s ≤ S.verifies (S.realizes s) :=
  S.adj.le_u_l s

/-- Demand round-trip (adjunction counit): `realizes (verifies d) ≤ d`. Together with
`seam_unit` this is the full unit/counit of `realizes ⊣ verifies`. `GaloisConnection.l_u_le`. -/
theorem seam_counit (d : Demand) : S.realizes (S.verifies d) ≤ d :=
  S.adj.l_u_le d

/-- The verification closure is idempotent: `verifies ∘ realizes` applied twice equals applied
once. Standard adjunction consequence (`GaloisConnection.u_l_u_eq_u`). -/
theorem seam_closure_idem (s : Supply) :
    S.verifies (S.realizes (S.verifies (S.realizes s)))
      = S.verifies (S.realizes s) :=
  -- `u (l (u b)) = u b` (`GaloisConnection.u_l_u_eq_u`) at `b := realizes s`.
  S.adj.u_l_u_eq_u (S.realizes s)

/-- The abstract seam round-trip: `realizes s ≤ d → s ≤ verifies d`. Specializes to the
`Dregg2.Laws.predicate_witness_galois` connection in the real system. -/
theorem seam_roundtrip (s : Supply) (d : Demand)
    (h : S.realizes s ≤ d) : s ≤ S.verifies d :=
  (S.adj s d).mp h

end Seam

/-! # §4. Ordering / finality, derived as a bounded lattice.

Taking "finality is a `Lattice τ` and commit = the join `a ⊔ b`" as the single datum, the
mathlib lattice laws specialize to `Dregg2.Finality.Tier`: `crossTierJoin` is the lattice
join (`tier_commit_eq_crossTierJoin`), commit is monotone (`commit_monotone`), and
no-downgrade holds (`tier_crossTierJoin_no_downgrade`). The `commitAtMax_*_def` lemmas are
join-unfolds (bricks for the two `Tier`-touching results), not independent derivations. -/

section Finality

variable {τ : Type u} [Lattice τ]

/-- The cross-tier commit rule as the lattice join: a turn touching tiers `a` and `b`
commits at `a ⊔ b`. This recovers `Dregg2.Finality.crossTierJoin` as the lattice operation. -/
def commitAtMax (a b : τ) : τ := a ⊔ b

/-- `a ≤ commitAtMax a b` — the join's left bound (`le_sup_left`), brick for
`tier_crossTierJoin_no_downgrade`. Not an independent finality rule — a join unfold. -/
theorem commitAtMax_le_left_def (a b : τ) : a ≤ commitAtMax a b := le_sup_left

/-- `b ≤ commitAtMax a b` — the join's right bound (`le_sup_right`). -/
theorem commitAtMax_le_right_def (a b : τ) : b ≤ commitAtMax a b := le_sup_right

/-- `commitAtMax` is monotone: strengthening either participant's tier can only strengthen
the commit. This is `sup_le_sup` specialized to the Tier order; one of the two results this
section exports (via `tier_commit_eq_crossTierJoin`). -/
theorem commit_monotone : Monotone (fun p : τ × τ => commitAtMax p.1 p.2) :=
  fun _ _ h => sup_le_sup h.1 h.2

/-- `commitAtMax` unfolds to `sup_assoc`/`sup_comm`: N-cell commits are independent of
grouping/order. Mathlib lattice laws restated at `commitAtMax`; not independent derivations. -/
theorem commitAtMax_assoc_def (a b c : τ) :
    commitAtMax (commitAtMax a b) c = commitAtMax a (commitAtMax b c) := sup_assoc a b c
theorem commitAtMax_comm_def (a b : τ) : commitAtMax a b = commitAtMax b a := sup_comm a b

/-- `commitAtMax a b ≤ ⊤` — the join's top bound (`le_top`). A commit cannot exceed the
strongest tier. Join unfold, not an independent derivation. -/
theorem commitAtMax_le_top_def [OrderTop τ] (a b : τ) : commitAtMax a b ≤ ⊤ := le_top

/-- The bottom tier `⊥` is the commit-identity: committing with a `⊥`-tier participant
leaves the tier unchanged. Derived from `BoundedOrder`. -/
theorem commit_bot_identity [OrderBot τ] (a : τ) : commitAtMax ⊥ a = a := by
  simp [commitAtMax]

/-! ### §4 bridge: the abstract finality lattice is `Dregg2.Finality.Tier`.

`Dregg2.Finality.Tier` is a `LinearOrder`, and its `crossTierJoin` is the lattice join. We
also derive the bounded structure `Dregg2` leaves implicit: the ladder has `⊥ = causal`
and `⊤ = constitutional`. -/

open Dregg2.Finality in
/-- The four-tier ladder has a strongest tier (`OrderTop`): `constitutional` dominates all. -/
instance tierOrderTop : OrderTop Dregg2.Finality.Tier where
  top := Dregg2.Finality.Tier.constitutional
  le_top t := by cases t <;> decide

open Dregg2.Finality in
/-- The four-tier ladder has a weakest tier (`OrderBot`): `causal` is below every tier. -/
instance tierOrderBot : OrderBot Dregg2.Finality.Tier where
  bot := Dregg2.Finality.Tier.causal
  bot_le t := by cases t <;> decide

/-- The tier ladder is a `BoundedOrder` — `causal ≤ t ≤ constitutional` for every `t`.
Combines `tierOrderTop` and `tierOrderBot`. -/
instance tierBoundedOrder : BoundedOrder Dregg2.Finality.Tier where

/-- `commitAtMax` on `Tier` equals `Dregg2.Finality.crossTierJoin` (definitionally, since
`Tier`'s `⊔` is `max`). The derived monotonicity laws therefore apply to the actual system. -/
theorem tier_commit_eq_crossTierJoin (a b : Dregg2.Finality.Tier) :
    commitAtMax a b = Dregg2.Finality.crossTierJoin a b := rfl

/-- The concrete cross-tier commit never downgrades either participant: both bounds hold. -/
theorem tier_crossTierJoin_no_downgrade (a b : Dregg2.Finality.Tier) :
    a ≤ Dregg2.Finality.crossTierJoin a b ∧ b ≤ Dregg2.Finality.crossTierJoin a b :=
  ⟨commitAtMax_le_left_def a b, commitAtMax_le_right_def a b⟩

end Finality

/-! # §5. I-confluence, derived as a sub-join-semilattice.

`Dregg2.Confluence` defines `IConfluent I := ∀ x y, I x → I y → I (x ⊔ y)`. The
categorical reading: the coordination-free fragment `{x // I x}` is a sub-join-semilattice,
and we exhibit its sub-LUB structure. -/

section IConfluence

variable {S : Type u} [SemilatticeSup S]

/-- `I` is **I-confluent** iff it is preserved by the `⊔` of the CvRDT merge-state
(concurrent invariant-preserving versions merge safely). Mirrors `Dregg2.Confluence.IConfluent`. -/
def IConfluent (I : S → Prop) : Prop := ∀ x y, I x → I y → I (x ⊔ y)

/-- **Closed under the invariant-merge join** — the sub-(join-semi)lattice closure
condition: the fragment `{x // I x}` is stable under `⊔`. -/
def ClosedUnderJoin (I : S → Prop) : Prop := ∀ x y, I x → I y → I (x ⊔ y)

/-- `IConfluent I ↔ ClosedUnderJoin I` is a definitional unfold (both unfold to
`∀ x y, I x → I y → I (x ⊔ y)`). Not a derivation — two names for one condition. The
genuine content of §5 is `confJoin_lub` and `tier1Eligible_closedUnderJoin`. -/
theorem iconfluent_eq_closed_def (I : S → Prop) : IConfluent I ↔ ClosedUnderJoin I :=
  Iff.rfl

/-- The binary join of the coordination-free fragment: given I-confluence, two `I`-states
merge within `I`, the `⊔` of the sub-join-semilattice. -/
def confJoin (I : S → Prop) (h : IConfluent I) (x y : {a // I a}) : {a // I a} :=
  ⟨x.1 ⊔ y.1, h x.1 y.1 x.2 y.2⟩

/-- The fragment's join equals the ambient join: the inclusion `{x // I x} ↪ S` preserves
`⊔`. The fragment is a genuine sub-join-semilattice. -/
theorem confJoin_incl (I : S → Prop) (h : IConfluent I) (x y : {a // I a}) :
    (confJoin I h x y).1 = x.1 ⊔ y.1 := rfl

/-- Each input is below the fragment join — the merge dominates both concurrent versions. -/
theorem confJoin_le_left (I : S → Prop) (h : IConfluent I) (x y : {a // I a}) :
    x.1 ≤ (confJoin I h x y).1 := le_sup_left
theorem confJoin_le_right (I : S → Prop) (h : IConfluent I) (x y : {a // I a}) :
    y.1 ≤ (confJoin I h x y).1 := le_sup_right

/-- The fragment join is least: any `I`-state `z` above both `x` and `y` is above their
merge. This establishes `confJoin` as the join of the sub-semilattice. -/
theorem confJoin_lub (I : S → Prop) (h : IConfluent I) (x y z : {a // I a})
    (hx : x.1 ≤ z.1) (hy : y.1 ≤ z.1) : (confJoin I h x y).1 ≤ z.1 :=
  sup_le hx hy

/-- A `Dregg2.Confluence.Tier1Eligible` invariant satisfies `ClosedUnderJoin`: its
coordination-free fragment is a sub-join-semilattice. Routes through
`Dregg2.Confluence.admits_sound` (the real module's tier-1 soundness). -/
theorem tier1Eligible_closedUnderJoin {S' : Type u} [Dregg2.Confluence.MergeState S']
    (I : Dregg2.Confluence.Invariant S') (h : Dregg2.Confluence.Tier1Eligible I) :
    ClosedUnderJoin (S := S') I :=
  fun x y hx hy => Dregg2.Confluence.admits_sound I h x y hx hy

end IConfluence

/-! # §3. The cell as a coalgebra; the hyperedge as a (wide) pullback.

We re-state `Dregg2.Boundary.TurnCoalg.step` as a coalgebra of the endofunctor
`F X = Obs × (Adm → X)`, and the JointTurn/hyperedge binding as a pullback limit, giving
the cell a universal-property characterization. Final-coalgebra existence is OPEN. -/

section Coalgebra

variable {Obs Adm X Y Z : Type u}

/-- The object action of the behaviour endofunctor `F X = Obs × (Adm → X)` — a Moore/DFA
shape (output-on-state × input-indexed transition). -/
def Fobj (Obs Adm X : Type u) : Type u := Obs × (Adm → X)

/-- The functorial lift of `f : X → Y` to `F X → F Y`: relabel successors, leave
the observation fixed. `Fmap id = id` and `Fmap (g∘f) = Fmap g ∘ Fmap f` hold definitionally.
Spelled with plain functions rather than `Type u ⥤ Type u` because this mathlib slice wraps
`Type`-category morphisms in `ConcreteCategory.Fun`. -/
def Fmap (f : X → Y) : Fobj Obs Adm X → Fobj Obs Adm Y :=
  fun p => (p.1, fun a => f (p.2 a))

@[simp] theorem Fmap_id : Fmap (Obs := Obs) (Adm := Adm) (id : X → X) = id := rfl
@[simp] theorem Fmap_comp (g : Y → Z) (f : X → Y) :
    Fmap (Obs := Obs) (Adm := Adm) (g ∘ f) = Fmap g ∘ Fmap f := rfl

/-- A cell as an `F`-coalgebra: a carrier `V` with structure map `str : V → F V`. This
re-states `Dregg2.Boundary.TurnCoalg` as an endofunctor coalgebra. (`Mathlib.CategoryTheory.
Endofunctor.Algebra` is not in this lib's pinned mathlib slice, so it is spelled by hand.) -/
structure Cell (Obs Adm : Type u) where
  /-- The carrier (state space of cells). -/
  V : Type u
  /-- The endofunctor-coalgebra structure map `V → F V`. -/
  str : V → Fobj Obs Adm V

/-- The observation and successor of a cell-coalgebra, recovered from its structure map
(matching `TurnCoalg.obs`/`TurnCoalg.next`). -/
def Cell.obs (c : Cell Obs Adm) (x : c.V) : Obs := (c.str x).1
def Cell.next (c : Cell Obs Adm) (x : c.V) (a : Adm) : c.V := (c.str x).2 a

/-- A coalgebra morphism / functional bisimulation `c ⟶ d`: a carrier map `f` commuting
with the structure maps (`F.map f ∘ c.str = d.str ∘ f`). -/
structure CoalgHom (c d : Cell Obs Adm) where
  /-- The underlying carrier map. -/
  f : c.V → d.V
  /-- The coalgebra-square: `f` intertwines the two structure maps. -/
  commutes : Fmap f ∘ c.str = d.str ∘ f

/-- Every cell has the identity coalgebra morphism (the square commutes by `Fmap_id`):
every cell bisimulates itself. Categorical source of `Dregg2.Boundary.sound_refl`. -/
theorem cell_self_bisim (c : Cell Obs Adm) :
    ∃ h : CoalgHom c c, h.f = id :=
  ⟨⟨id, by simp⟩, rfl⟩

/-! ### The hyperedge / JointTurn as a wide pullback.

The joint state space over a shared interface is the pullback of the participants'
projections; a many-participant hyperedge is the wide pullback. Stated via `IsPullback`. -/

variable {𝒞 : Type u} [Category.{v} 𝒞]

/-- The two-party JointTurn as a pullback: `J` is the universal object whose two views agree
on the shared interface (`j₁ ≫ π₁ = j₂ ≫ π₂`) and through which every agreeing pair factors
uniquely. States the universal property without postulating a chosen `J`. -/
def IsJointTurn {I P₁ P₂ J : 𝒞} (j₁ : J ⟶ P₁) (j₂ : J ⟶ P₂)
    (π₁ : P₁ ⟶ I) (π₂ : P₂ ⟶ I) : Prop :=
  IsPullback j₁ j₂ π₁ π₂

/-- The JointTurn pullback square commutes: `j₁ ≫ π₁ = j₂ ≫ π₂`. Read off `IsPullback.w`. -/
theorem jointTurn_interface_agrees {I P₁ P₂ J : 𝒞}
    {j₁ : J ⟶ P₁} {j₂ : J ⟶ P₂} {π₁ : P₁ ⟶ I} {π₂ : P₂ ⟶ I}
    (h : IsJointTurn j₁ j₂ π₁ π₂) : j₁ ≫ π₁ = j₂ ≫ π₂ :=
  h.w

/-- The JointTurn is universal: any agreeing pair `(w₁, w₂)` factors through `J` by a
unique mediator. The binding is determined, not chosen (`IsPullback` lift). -/
theorem jointTurn_universal {I P₁ P₂ J : 𝒞}
    {j₁ : J ⟶ P₁} {j₂ : J ⟶ P₂} {π₁ : P₁ ⟶ I} {π₂ : P₂ ⟶ I}
    (h : IsJointTurn j₁ j₂ π₁ π₂)
    {W : 𝒞} (w₁ : W ⟶ P₁) (w₂ : W ⟶ P₂) (hw : w₁ ≫ π₁ = w₂ ≫ π₂) :
    ∃ m : W ⟶ J, m ≫ j₁ = w₁ ∧ m ≫ j₂ = w₂ :=
  ⟨h.lift w₁ w₂ hw, h.lift_fst w₁ w₂ hw, h.lift_snd w₁ w₂ hw⟩

/-- The mediator is unique: two maps `W ⟶ J` that reproduce both views must agree
(`IsPullback.hom_ext`). Together with `jointTurn_universal` this is the full UP. -/
theorem jointTurn_mediator_unique {I P₁ P₂ J : 𝒞}
    {j₁ : J ⟶ P₁} {j₂ : J ⟶ P₂} {π₁ : P₁ ⟶ I} {π₂ : P₂ ⟶ I}
    (h : IsJointTurn j₁ j₂ π₁ π₂)
    {W : 𝒞} {m m' : W ⟶ J}
    (e₁ : m ≫ j₁ = m' ≫ j₁) (e₂ : m ≫ j₂ = m' ≫ j₂) : m = m' :=
  h.hom_ext e₁ e₂

/-! ### The N-ary hyperedge as a wide pullback.

A real hyperedge binds N participants indexed by `ι` into one joint turn over `I`. The
categorical content is the wide pullback of the cospan `(πᵢ : Pᵢ ⟶ I)ᵢ`. We state the
universal property by hand (rather than via `HasWidePullback`) as a cone-with-unique-mediator
bundle — `agree`/`fac`/`uniq` are its UP laws. `ι` plays the role of `TurnId`; `mathlib`'s
`WidePullbackShape ι = Option ι` is this diagram shape. -/

/-- An N-ary joint turn: `J` with legs `legs i : J ⟶ Pᵢ` is the wide pullback over
`proj i : Pᵢ ⟶ I` iff (agree) all views of the interface coincide, and (universal) every
agreeing `W` factors through `J` by a unique mediator. -/
structure IsWideJointTurn {ι : Type w} {I J : 𝒞} (P : ι → 𝒞)
    (legs : ∀ i, J ⟶ P i) (proj : ∀ i, P i ⟶ I) where
  /-- All participants agree on the interface: a single shared boundary arrow `J ⟶ I`. -/
  agree : ∀ i i', legs i ≫ proj i = legs i' ≫ proj i'
  /-- Existence of the mediator for any agreeing cone `(W, views)`. -/
  lift {W : 𝒞} (views : ∀ i, W ⟶ P i)
    (hv : ∀ i i', views i ≫ proj i = views i' ≫ proj i') : W ⟶ J
  /-- The mediator reproduces every view. -/
  fac {W : 𝒞} (views : ∀ i, W ⟶ P i)
    (hv : ∀ i i', views i ≫ proj i = views i' ≫ proj i') (i : ι) :
    lift views hv ≫ legs i = views i
  /-- The mediator is unique: any two maps reproducing all views agree. -/
  uniq {W : 𝒞} {m m' : W ⟶ J} (e : ∀ i, m ≫ legs i = m' ≫ legs i) : m = m'

variable {ι : Type w}

/-- All N participants see the same interface: every pair `legs i ≫ proj i = legs i' ≫ proj i'`
follows from `agree`. -/
theorem wideJointTurn_interface_agrees {I J : 𝒞} {P : ι → 𝒞}
    {legs : ∀ i, J ⟶ P i} {proj : ∀ i, P i ⟶ I}
    (h : IsWideJointTurn P legs proj) (i i' : ι) :
    legs i ≫ proj i = legs i' ≫ proj i' :=
  h.agree i i'

/-- The N-ary hyperedge is universal: any `W` with pairwise-agreeing views factors through
`J` via a mediator reproducing every view. The wide-pullback `lift`/`fac`. -/
theorem wideJointTurn_universal {I J : 𝒞} {P : ι → 𝒞}
    {legs : ∀ i, J ⟶ P i} {proj : ∀ i, P i ⟶ I}
    (h : IsWideJointTurn P legs proj)
    {W : 𝒞} (views : ∀ i, W ⟶ P i)
    (hv : ∀ i i', views i ≫ proj i = views i' ≫ proj i') :
    ∃ m : W ⟶ J, ∀ i, m ≫ legs i = views i :=
  ⟨h.lift views hv, h.fac views hv⟩

/-- The N-ary mediator is unique (wide-pullback `uniq`). With `wideJointTurn_universal` this
is the complete existence-and-uniqueness universal property of the hyperedge. -/
theorem wideJointTurn_mediator_unique {I J : 𝒞} {P : ι → 𝒞}
    {legs : ∀ i, J ⟶ P i} {proj : ∀ i, P i ⟶ I}
    (h : IsWideJointTurn P legs proj)
    {W : 𝒞} {m m' : W ⟶ J} (e : ∀ i, m ≫ legs i = m' ≫ legs i) : m = m' :=
  h.uniq e

/-- `IsJointTurn` is the `ι = Bool` case of `IsWideJointTurn`: the ordinary pullback
is the `N = 2` wide pullback, so `IsWideJointTurn` faithfully generalises it. -/
noncomputable def isJointTurn_to_wide {I P₁ P₂ J : 𝒞}
    {j₁ : J ⟶ P₁} {j₂ : J ⟶ P₂} {π₁ : P₁ ⟶ I} {π₂ : P₂ ⟶ I}
    (h : IsJointTurn j₁ j₂ π₁ π₂) :
    IsWideJointTurn (ι := Bool) (I := I) (J := J)
      (fun b => match b with | true => P₂ | false => P₁)
      (fun b => match b with | true => j₂ | false => j₁)
      (fun b => match b with | true => π₂ | false => π₁) where
  agree i i' := by
    cases i <;> cases i' <;> first | rfl | exact h.w | exact h.w.symm
  lift views hv := h.lift (views false) (views true) (hv false true)
  fac views hv i := by
    cases i
    · exact h.lift_fst (views false) (views true) (hv false true)
    · exact h.lift_snd (views false) (views true) (hv false true)
  uniq {W m m'} e := h.hom_ext (e false) (e true)

/-! ### §3: the final coalgebra `νF` — the OPEN sharpened.

Even with `νF`'s existence still open, we can prove its universal property and the
uniqueness of the anamorphism. The OPEN is narrowed to: construct the carrier. -/

/-- Coalgebra morphism composition (the category of `F`-coalgebras has composition;
identity is `cell_self_bisim`). Needed to state finality. -/
def CoalgHom.comp {c d e : Cell Obs Adm} (g : CoalgHom d e) (f : CoalgHom c d) :
    CoalgHom c e where
  f := g.f ∘ f.f
  commutes := by
    have hf := f.commutes; have hg := g.commutes
    -- Fmap (g∘f) = Fmap g ∘ Fmap f, then paste the two squares.
    rw [Fmap_comp]
    calc (Fmap g.f ∘ Fmap f.f) ∘ c.str
        = Fmap g.f ∘ (Fmap f.f ∘ c.str) := by rfl
      _ = Fmap g.f ∘ (d.str ∘ f.f) := by rw [hf]
      _ = (Fmap g.f ∘ d.str) ∘ f.f := by rfl
      _ = (e.str ∘ g.f) ∘ f.f := by rw [hg]
      _ = e.str ∘ (g.f ∘ f.f) := by rfl

/-- **`IsFinalCell νF` — the terminal `F`-coalgebra universal property, stated.** `νF` is
final iff from *every* cell `c` there is a coalgebra morphism into it (the **anamorphism**
`ana c`), and any two such morphisms agree (**uniqueness** — the heart of coinduction).
This is `Dregg2.Boundary`'s "live codata into which every behaviour unfolds" as a precise
predicate; the OPEN below is only whether such a `νF` *exists*. -/
structure IsFinalCell (νF : Cell Obs Adm) : Prop where
  /-- The anamorphism: every cell unfolds into `νF`. -/
  ana : ∀ c : Cell Obs Adm, Nonempty (CoalgHom c νF)
  /-- Uniqueness: any two coalgebra morphisms `c ⟶ νF` have equal carrier maps. -/
  uniq : ∀ {c : Cell Obs Adm} (g h : CoalgHom c νF), g.f = h.f

/-- **DERIVED: the anamorphism is unique (coinduction).** If `νF` is final, then for every
cell the unfold into `νF` is a `Subsingleton` of carrier maps — there is *at most one*
behaviour-preserving map into the final coalgebra. This **uniqueness** is exactly the
coinduction principle: two states with the same `νF`-image are behaviourally equal. We
prove it *conditionally* on finality (the genuine content), leaving only existence open. -/
theorem ana_unique {νF : Cell Obs Adm} (hfin : IsFinalCell νF) (c : Cell Obs Adm) :
    ∀ g h : CoalgHom c νF, g.f = h.f :=
  fun g h => hfin.uniq g h

/-- **DERIVED: `νF` is unique up to the carrier maps it forces (terminal objects are
essentially unique).** If two cells are *both* final, the anamorphisms between them compose
to the identity on carriers — they are mutually inverse functional bisimulations, hence the
final behaviour is canonical. We extract the round-trip carrier equation (`ana ∘ ana = id`),
the computational core of terminal-uniqueness, from `uniq` applied to the two endomorphism
candidates `ana_{c→c}` and `𝟙`. -/
theorem final_unique_roundtrip {ν₁ ν₂ : Cell Obs Adm}
    (h₁ : IsFinalCell ν₁) (h₂ : IsFinalCell ν₂)
    (a₁₂ : CoalgHom ν₁ ν₂) (a₂₁ : CoalgHom ν₂ ν₁) :
    a₂₁.f ∘ a₁₂.f = id := by
  -- `a₂₁ ∘ a₁₂ : ν₁ ⟶ ν₁` and the identity are both coalg-morphisms `ν₁ ⟶ ν₁`;
  -- finality of `ν₁` forces their carriers equal.
  have := h₁.uniq (CoalgHom.comp a₂₁ a₁₂) ⟨id, by simp⟩
  simpa [CoalgHom.comp] using this

/-
OPEN (`§3`, the anamorphism / final-coalgebra **existence** — now SHARPENED). The cell type
`Dregg2.Boundary` *wants* is the **final** `behaviour`-coalgebra `νF` — the unique behaviour
into which every coalgebra anamorphs (the "live codata, never bottoms out" of `§2`).

What is now PROVED (no longer open): the universal property is fully stated (`IsFinalCell`),
its **uniqueness half is a theorem** — the anamorphism is unique (`ana_unique`, the
coinduction principle) and the final object is canonical up to a carrier round-trip
(`final_unique_roundtrip`), both *conditional on finality*, which is the genuine categorical
content of coinduction. The category of `F`-coalgebras has identities (`cell_self_bisim`)
and composition (`CoalgHom.comp`). The hyperedge has its (wide) pullback universal property
PROVED (`wideJointTurn_universal`/`wideJointTurn_mediator_unique`).

What remains OPEN is **strictly the construction of the carrier** — an *inhabitant* of
`IsFinalCell` for `F X = Obs × (Adm → X)`:

    ∃ νF : Cell Obs Adm, IsFinalCell νF

The precise named categorical lemma the construction needs is one of:
  * **Adámek's terminal-coalgebra theorem** — `νF = lim (… → F²1 → F1 → 1)`, the limit of
    the ω^op-chain of `F`-iterates of the terminal object, which converges because
    `F X = Obs × (Adm → X)` preserves ω^op-limits (it is a finite product of a constant and
    a representable, both continuous); or
  * a **guarded-recursion `▷` backend** giving `νF` as a coinductive type directly.
Either is a module of its own (needs `CategoryTheory.Limits` ω-chains, not built here as a
ready `HasLimit` instance for this `F`). We do NOT axiomatize it; we have moved the OPEN from
"what is `νF`?" to "construct the carrier; its universal property and uniqueness are done."
The behavioural content the system actually uses — bisimulation-as-coalgebra-morphism,
reflexivity, composition, and the step-completeness safety invariant — is already proved
(`cell_self_bisim`/`CoalgHom.comp`/`ana_unique` here; `stepComplete_preserves` in
`Dregg2.Boundary`) without needing `νF` to exist. Concretely the missing existence fact is:

    a terminal object `νF` in the category `(Cell Obs Adm, CoalgHom)` exists

— i.e. a cell `νF` together with, for every cell `c`, a UNIQUE coalgebra morphism
`anaF c : CoalgHom c νF` — from which the anamorphism and its uniqueness (the coinduction
principle underlying `Dregg2.Boundary.IsBisim`) would follow. We do NOT axiomatize it; we
record it as the precise open hypothesis the full derivation still needs. The *behavioural*
content the system actually uses — bisimulation-as-coalgebra-morphism, reflexivity, and the
step-completeness safety invariant — is already proved (`cell_self_bisim` here;
`stepComplete_preserves` in `Dregg2.Boundary`) without needing `νF` to exist. -/

end Coalgebra

/-! # §6. The boundary law as a square — tying the verify-seam (§2) to the cell (§3).

§2 derived the verify/find seam as a `GaloisConnection realizes ⊣ verifies`; §3 derived the
cell as an `F`-coalgebra with observation `Cell.obs`. They meet at the **cell boundary**: a
cell observes a *demand*, and each state is backed by a *supply*. The "boundary law" of
`Dregg2.Boundary` — that a cell's observation is *consistent with* what its supply verifies —
is DERIVED here as a **commuting square** that is *precisely the seam adjunction read at the
coalgebra's observation*. No separate boundary postulate: §3's observation passes through
§2's adjunction by construction. -/

section Boundary

variable {Demand Supply Adm : Type u} [Preorder Demand] [PartialOrder Supply]

/-- **The cell-boundary square (the §2⊗§3 datum).** A cell `c` whose observation is a
*demand*, equipped with a backing-supply map `adm : c.V → Supply` (the witness/supply each
state holds), is **seam-consistent** at the seam `S` iff its boundary obeys the adjunction:
whenever the demand a state observes is realized by its supply (`realizes (adm x) ≤ obs x`),
that supply suffices to verify the observation (`adm x ≤ verifies (obs x)`). This is the
square `realizes ⊣ verifies` *transported along the coalgebra's observation*. -/
def SeamConsistent (S : Seam (Demand := Demand) (Supply := Supply))
    (c : Cell Demand Adm) (adm : c.V → Supply) : Prop :=
  ∀ x : c.V, S.realizes (adm x) ≤ c.obs x → adm x ≤ S.verifies (c.obs x)

/-- **DERIVED: every cell is seam-consistent — the boundary square commutes for free.** The
cell-boundary law is *exactly* the seam adjunction `realizes s ≤ d ↔ s ≤ verifies d` read at
`d := c.obs x`, `s := adm x`. So §3's coalgebra and §2's Galois seam **agree at the
boundary by construction**: the boundary law is not an extra axiom, it is the adjunction. -/
theorem seamConsistent_of_adj (S : Seam (Demand := Demand) (Supply := Supply))
    (c : Cell Demand Adm) (adm : c.V → Supply) : SeamConsistent S c adm :=
  fun x h => (S.adj (adm x) (c.obs x)).mp h

/-- **DERIVED: the boundary closure square is idempotent at every observation.** Re-running
the verify→realize seam on a cell's observation reaches a fixed point in one round — the
seam closure (`seam_closure_idem`) instantiated at the coalgebra's `obs`. The cell boundary
*stabilises*: a once-verified observation needs no re-verification across turns. -/
theorem seam_boundary_closure (S : Seam (Demand := Demand) (Supply := Supply))
    (c : Cell Demand Adm) (x : c.V) :
    S.verifies (S.realizes (S.verifies (S.realizes (S.verifies (c.obs x)))))
      = S.verifies (S.realizes (S.verifies (c.obs x))) :=
  S.adj.u_l_u_eq_u (S.realizes (S.verifies (c.obs x)))

end Boundary

/-! # Axiom-hygiene: pin the DERIVED keystones as kernel-clean. -/

-- §1 conservation, derived from the lax monoidal functor:
#assert_axioms measure_unit
#assert_axioms measure_tensor
#assert_axioms measure_invariant
#assert_axioms no_free_copy
#assert_axioms conservation_core_derived

-- §2 the verify/find seam, derived from the Galois connection:
#assert_axioms seam_attenuate_monotone
#assert_axioms seam_realizes_monotone
#assert_axioms seam_unit
#assert_axioms seam_counit
#assert_axioms seam_closure_idem
#assert_axioms seam_roundtrip

-- §3 the cell coalgebra & the hyperedge pullback (universal properties):
#assert_axioms Fmap_id
#assert_axioms Fmap_comp
#assert_axioms cell_self_bisim
#assert_axioms jointTurn_interface_agrees
#assert_axioms jointTurn_universal
#assert_axioms wideJointTurn_universal
#assert_axioms wideJointTurn_mediator_unique
#assert_axioms ana_unique

-- §4 finality: the mathlib lattice laws specialize to the Tier order. The load-bearing exports
-- are `commit_monotone` and the `Tier`-touching `tier_commit_eq_crossTierJoin` /
-- `tier_crossTierJoin_no_downgrade`; the `commitAtMax_*_def` lemmas are join-unfolds beneath them.
#assert_axioms commitAtMax_le_left_def
#assert_axioms commit_monotone
#assert_axioms tier_commit_eq_crossTierJoin
#assert_axioms tier_crossTierJoin_no_downgrade

-- §5 I-confluence, derived as a sub-join-semilattice (closed-under-⊔):
#assert_axioms iconfluent_eq_closed_def
#assert_axioms confJoin_incl
#assert_axioms confJoin_lub
#assert_axioms tier1Eligible_closedUnderJoin

-- §6 the boundary law as a square (the seam adjunction ⊗ the cell coalgebra):
#assert_axioms seamConsistent_of_adj
#assert_axioms seam_boundary_closure

/-! # Coda — how this moves the spec from postulated toward derived.

`Dregg2.Core.Conservation` postulates `unit_zero`/`tensor_add` as *fields*; here
(`measure_unit`/`measure_tensor`) they are **theorems** about a lax monoidal functor
`Σ : C ⥤ Discrete M`, and `withholding_no_free_copy` has a **categorical proof**
(`no_free_copy`) from *(comonoid copy map) + (cancellative discrete target)*. `Dregg2.Laws`
constructs the `Predicate ⊣ Witness` connection; here its operational laws (attenuation,
round-trips, closure) are **consequences** of the seam's defining `GaloisConnection`.
`Dregg2.Boundary` gives a structure map; here the cell is an `F`-coalgebra and the hyperedge
a **pullback** — now also a **wide pullback** for N participants (`wideJointTurn_universal`/
`wideJointTurn_mediator_unique`) — with the binding's universal property PROVED and only the
final-coalgebra existence (`νF`) honestly OPEN (its uniqueness/coinduction, `ana_unique`, is
proved *conditionally on finality*).

**The three judgements, each now a categorical structure.** §1 conservation is
*substructurality* — the absence of a natural diagonal `Δ`/discard is conservation
(`diagonal_collapses_measure`/`no_free_discard`, the linear/affine reading). §4 derives
`Dregg2.Finality`'s **second judgement** (ordering/finality) as a **bounded lattice**: the
cross-tier commit is the lattice *join* (`commitAtMax = crossTierJoin`), *no-downgrade IS
monotonicity* (`commit_monotone`), and the ladder is bounded (`tierBoundedOrder`, with the
derived `OrderTop`/`OrderBot` `Dregg2` leaves implicit) — the mathlib lattice/`BoundedOrder`
laws specializing to the Tier order, the `commitAtMax_*_def` lemmas being join-unfolds beneath
the `Tier`-touching results. §5 derives `Dregg2.Confluence`'s **third judgement** (I-confluence)
as a **sub-join-semilattice**: `IConfluent` and `closed-under-⊔` are the same condition under
two names (`iconfluent_eq_closed_def`, a definitional unfold), with the coordination-free
fragment exhibited as a
join-subalgebra (`confJoin`/`confJoin_lub`) and tier-1 eligibility shown to BE that closure
(`tier1Eligible_closedUnderJoin`). §6 ties §2⊗§3: the **cell-boundary law is the seam
adjunction read at the coalgebra's observation** (`seamConsistent_of_adj`) — not an extra
postulate, the adjunction itself.

The honest caveat (`study-category §5`): the conservation derivation's target is *discrete*,
so it is **thin** — what is genuinely derived is *monoid-hom + invariance*, the real content
the `Dregg2.Core` docstring already names; the "strong monoidal functor" packaging is
decorative and we do not oversell it. The §4/§5 lattice derivations are honest order theory
(no thinness caveat); the §6 boundary square is the genuine adjunction, faithfully
transported. The ONE deep OPEN remains the final-coalgebra *existence* (Adámek / guarded
recursion), with its universal property and uniqueness already proved. This is a START at
"the abstract spec is derived from categorical first principles," substantially advanced —
all three judgements are now derived structures, not postulates — but not the finished
derivation. -/

end Metatheory
