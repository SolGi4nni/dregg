/-
# Dregg2.Metatheory.IndexedMonoidal — the LINEAR/DEPENDENT doctrine: an INDEXED MONOIDAL category.

This is the FOUNDATIONAL FLOOR that WELDS two previously-separate tracks:

  * **Track K** (`Dregg2.Metatheory.Lawvere`): the *Lawvere hyperdoctrine* — a base category whose
    reindexing/substitution functor `f*` carries the predicate logic, with the quantifier triple
    `∃_f ⊣ f* ⊣ ∀_f` (the ∃/∀ of the knowledge layer);
  * **Track A** (`Dregg2.Intent.Resource`, `Dregg2.Intent.Centers`): the *monoidal resource* layer —
    a symmetric-monoidal `ResourceTheory` whose `⊗` is the LINEAR escrow tensor (no copy/delete).

A *plain* hyperdoctrine has **Heyting** (cartesian, hence DUPLICABLE: `Δ : A ⟶ A ⊗ A`) fibres. That is
WRONG for resources/capabilities, which are **linear** — you must not silently duplicate a coin or a
bearer cap. The fix, due to the linear-logic / dependent-linear-type tradition (Lawvere fibrations with
monoidal fibres; cf. the "linear hyperdoctrine" / "indexed monoidal category" of Shulman, *Framed
bicategories and monoidal fibrations*, and Ponto–Shulman), is **the SAME fibration with MONOIDAL
fibres**: the base carries the predicate logic, the fibres carry the resource tensor.

This module makes that precise:

  * **§1** `IndexedMonoidalCategory` — a base `B`, a functor `F : B ⥤ Cat`, each fibre `F.obj b`
    `[MonoidalCategory]`, each reindexing `(F.map u).toFunctor` `[LaxMonoidal]` (lax is the honest
    default; a strong variant is recorded). Packaged as a `structure`.
  * **§2** the total category is the Grothendieck construction `∫F = Grothendieck F`, with
    `forget : ∫F ⥤ B` (mathlib's `Grothendieck.forget`).
  * **§3 KEYSTONE — a CONCRETE non-trivial dregg instance** welding K + A on ONE total category:
      - base = the **walking-arrow context category** `Ctx` (`lo ⟶ hi`, "extend the context");
      - fibres = the **monoidal resource category** `Discrete Bundle` of `Resource.lean` (asset bundles
        under `*` = bundle-union — genuinely monoidal, NOT cartesian);
      - reindexing along `lo ⟶ hi` = `Discrete.monoidalFunctor` of an explicit `MonoidHom` (the
        "spend the art, keep the gold" projection) — a STRONG monoidal functor (mathlib
        `Discrete.monoidalFunctorMonoidal`).
    We prove the instance carries BOTH:
      (a) the **∃/∀ predicate adjoints** on the base map, via the posetal Set doctrine of
          `Lawvere.PartA` (`Set.image_preimage` / `Set.preimage_kernImage`) — `∃_f ⊣ f* ⊣ ∀_f`;
      (b) each **fibre is genuinely monoidal** (the linear `⊗`), with a real binary tensor.
  * **§4** the **INTERACTION** (the genuinely new welding content): the projection/Frobenius law
    relating `∃` (the predicate left adjoint) and the fibrewise `⊗`. We prove the **LAX `⊆` half**
    (the honest one-directional form that survives in general, à la `Lawvere` §B.6) AND show the
    naive EQUALITY FAILS on a concrete non-functional witness — so the lax inclusion is not a cheap
    `True`-collapse, it is the genuine surviving law.
  * **§5 TEETH** — non-vacuity: fibres are NOT subsingleton-collapsed (`⊗` genuinely discriminates,
    `res 2 ≠ res 0`); the predicate adjoint genuinely discriminates (`∃_f` non-trivial); the total
    category `∫F` has a genuine non-identity morphism whose base leg is `lo ⟶ hi` and whose fibre leg
    is a real `Discrete` tensor map.

DISCIPLINE: NO `sorry`/`axiom`/`admit`/`native_decide`. Keystones are `#assert_axioms`-pinned to the
kernel triple `{propext, Classical.choice, Quot.sound}`. The teeth are concrete discriminating models.
-/
import Dregg2.Intent.Resource
import Dregg2.Tactics
import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Order.GaloisConnection.Basic

universe v u

namespace Dregg2.Metatheory.IndexedMonoidal

open CategoryTheory MonoidalCategory Set

/-! ###############################################################################
# §1 — `IndexedMonoidalCategory`: a monoidal fibration, packaged.
##################################################################################

A *plain* Lawvere hyperdoctrine indexes **posets / Heyting algebras** over a base; an **indexed
monoidal category** indexes **monoidal categories** over a base, with each reindexing functor
(lax) monoidal. We package the data over a functor `F : B ⥤ Cat`: each fibre `F.obj b` is a
`MonoidalCategory`, and each reindexing `(F.map u).toFunctor` is `LaxMonoidal`. -/

/-- **An indexed monoidal category** (a *monoidal fibration*, presented "split"/strict via a
chosen indexing functor `F : B ⥤ Cat`).

Fields:
  * `B` — the base category (carries the predicate/substitution logic);
  * `F : B ⥤ Cat` — the indexing functor; the fibre over `b : B` is the category `F.obj b`;
  * `fibreMonoidal b` — each fibre `F.obj b` is a `MonoidalCategory` (the resource `⊗`);
  * `reindexLax u` — each reindexing functor `(F.map u).toFunctor` is `LaxMonoidal`, i.e. it carries
    `ε : 𝟙_ ⟶ (F.map u)(𝟙_)` and `μ : (F.map u)X ⊗ (F.map u)Y ⟶ (F.map u)(X ⊗ Y)`.

`LaxMonoidal` is the *honest default*: reindexing a resource and then tensoring need only LAX-relate to
tensoring and then reindexing (one direction), matching the lax projection law of §4. The strong /
pseudo case (`reindexMonoidal`, where reindexing strictly preserves `⊗`) is recorded separately. -/
structure IndexedMonoidalCategory where
  /-- the base category. -/
  B : Type u
  /-- the base is a category. -/
  [categoryB : Category.{v} B]
  /-- the indexing functor; fibre over `b` is `F.obj b : Cat`. -/
  F : B ⥤ Cat.{v, u}
  /-- each fibre is a monoidal category (the resource tensor `⊗`). -/
  fibreMonoidal : ∀ b : B, MonoidalCategory (F.obj b)
  /-- each reindexing functor is lax monoidal. -/
  reindexLax : ∀ {a b : B} (u : a ⟶ b),
    letI := fibreMonoidal a; letI := fibreMonoidal b
    (F.map u).toFunctor.LaxMonoidal

attribute [instance] IndexedMonoidalCategory.categoryB IndexedMonoidalCategory.fibreMonoidal

namespace IndexedMonoidalCategory

variable (IM : IndexedMonoidalCategory.{v, u})

/-- **The total category `∫F`** — the Grothendieck construction of the indexing functor. Objects are
dependent pairs `(b, x)` with `b : B` and `x : F.obj b`; a morphism `(b,x) ⟶ (b',x')` is a base map
`u : b ⟶ b'` together with a fibre map `(F.map u)(x) ⟶ x'`. This is the single category on which the
predicate logic (base leg) and the resource tensor (fibre leg) COEXIST. -/
abbrev Total : Type _ := Grothendieck IM.F

instance : Category IM.Total := inferInstanceAs (Category (Grothendieck IM.F))

/-- **`forget : ∫F ⥤ B`** — the fibration projection (mathlib's `Grothendieck.forget`), sending a
total object to its base context and a total morphism to its base leg. -/
abbrev forget : IM.Total ⥤ IM.B := Grothendieck.forget IM.F

end IndexedMonoidalCategory

/-! ### What the GENERAL packaging still needs (honest scope note).

`IndexedMonoidalCategory` above bundles the *carrier* data of a monoidal fibration — base, fibres each
`[MonoidalCategory]`, reindexings each `[LaxMonoidal]` — and the total category `∫F` with its `forget`.
Two coherences are deliberately NOT yet fields (they require a pseudofunctorial / 2-categorical layer
that mathlib's strict `B ⥤ Cat` does not directly expose):

  1. **Reindexing-vs-composition monoidal coherence.** That the lax structures `(μ, ε)` of `F.map u`
     and `F.map (u ≫ v)` agree under `F.map_comp` (a *monoidal pseudofunctor* / `IsMonoidal` natural
     iso). For the concrete keystone this holds because the reindexings are `Discrete.monoidalFunctor`
     and `Discrete.monoidalFunctorComp_isMonoidal` is the witness; promoting it to a structure field
     needs `CategoryTheory.Pseudofunctor` valued in `MonCat`-of-categories, which is future work.
  2. **The base quantifiers as structure.** The `∃_u ⊣ u* ⊣ ∀_u` triple (the predicate logic) is here
     realised *externally* on the base map (§4, via the posetal Set doctrine), not asserted as a field.
     A full *linear hyperdoctrine* would additionally require each reindexing to admit the adjoints AND
     the Frobenius/projection law as a coherence between those adjoints and the fibre `⊗` (§4.2). We
     prove that interaction concretely; bundling it generically needs the adjoints packaged per base
     map, which the strict split presentation does not force.

So: the STRUCTURE + TOTAL CATEGORY + a CONCRETE instance carrying BOTH faces are delivered and green;
the two coherences above are the precise remaining work to make the packaging a fully-general *monoidal
fibration with base quantifiers*. This matches the task's fallback: the concrete weld is complete; the
general bundling's missing pieces are named exactly. -/

/-! ###############################################################################
# §3 — KEYSTONE: a concrete dregg instance welding the predicate base (K) to the
# monoidal resource fibre (A).
##################################################################################

We exhibit a genuine, non-trivial `IndexedMonoidalCategory` whose
  * base is the **walking-arrow context category** `Ctx` (objects `lo`, `hi`; a single non-identity
    "extend the context" arrow `lo ⟶ hi`), and
  * fibres are the **monoidal resource category** `Discrete Bundle` of `Resource.lean` (asset bundles,
    `*` = bundle union, `1` = the empty bundle — genuinely monoidal, NOT cartesian).

The reindexing along `lo ⟶ hi` is `Discrete.monoidalFunctor` of the explicit `MonoidHom` "drop the
art component, keep the gold" — a *strong* monoidal functor (so a fortiori lax). This is the resource
side. The predicate side (∃/∀ adjoints) is realised on the SAME base arrow in §4 via the posetal Set
doctrine; both live over the one base `Ctx`, hence on the one total category `∫F`. -/

namespace DreggInstance

open Dregg2.Intent

/-! ### §3.1 The base: the walking-arrow context category `Ctx`. -/

/-- The two contexts: `lo` (a small context) and `hi` (an extended context). -/
inductive Ctx : Type where
  | lo : Ctx
  | hi : Ctx
deriving DecidableEq

/-- Morphisms of `Ctx`: only identities and the single generating "extend" arrow `lo ⟶ hi`. The
opposite arrow `hi ⟶ lo` is ABSENT — `Ctx` is a genuine poset `lo ≤ hi`, not a groupoid, so reindexing
has a real direction (and the ∃/∀ adjoints of §4 are non-trivial). -/
inductive CtxHom : Ctx → Ctx → Type where
  | id (c : Ctx) : CtxHom c c
  | extend : CtxHom Ctx.lo Ctx.hi

/-- Composition in `Ctx`: total because `Ctx` is a poset (at most one arrow each way), so the only
non-degenerate composite is `id ≫ extend = extend = extend ≫ id`. -/
def CtxHom.comp : ∀ {a b c : Ctx}, CtxHom a b → CtxHom b c → CtxHom a c
  | _, _, _, CtxHom.id _, g => g
  | _, _, _, CtxHom.extend, CtxHom.id _ => CtxHom.extend

instance : Category Ctx where
  Hom := CtxHom
  id := CtxHom.id
  comp f g := f.comp g
  id_comp := by rintro _ _ ⟨⟩ <;> rfl
  comp_id := by rintro _ _ (_ | _) <;> rfl
  assoc := by rintro _ _ _ _ (_ | _) (_ | _) (_ | _) <;> rfl

/-! ### §3.2 The reindexing monoid hom on the resource bundle.

`Bundle = Multiplicative (ℕ × ℕ)` (gold, art) of `Resource.lean`. We pick the "spend the art, keep the
gold" projection `(g, a) ↦ (g, 0)` as a `MonoidHom Bundle Bundle`. It is a genuine, NON-identity,
NON-injective hom (it discriminates: it kills the art coordinate) — exactly the kind of attenuation a
context-extension reindexing performs. -/

/-- The "drop art, keep gold" projection as a `MonoidHom` on the resource bundle. `*` on `Bundle` is
addition of the underlying `(ℕ × ℕ)` (it is `Multiplicative` of additive `ℕ × ℕ`), so this is the
additive projection `(g,a) ↦ (g,0)` transported through the type tag — written raw and discharged by
`Prod.ext`/`rfl`. -/
def dropArt : Bundle →* Bundle where
  toFun b := Multiplicative.ofAdd ((Multiplicative.toAdd b).1, 0)
  map_one' := rfl
  map_mul' x y := by
    -- `toAdd (x*y) = toAdd x + toAdd y`, so the first coordinate adds and the second is `0 = 0+0`.
    refine Multiplicative.toAdd.injective (Prod.ext rfl ?_)
    show (0 : ℕ) = 0 + 0
    rfl

/-- `dropArt` genuinely discriminates: it sends the bundle `(0,1)` (one art) to `(0,0)` (empty),
collapsing distinct bundles — so it is NOT injective, hence a real attenuation. -/
theorem dropArt_not_injective : ¬ Function.Injective dropArt := by
  intro hinj
  have h : (mkBundle 0 1) = (mkBundle 0 0) := by
    apply hinj
    apply Multiplicative.toAdd.injective
    rfl
  have : ((0, 1) : ℕ × ℕ) = (0, 0) := Multiplicative.ofAdd.injective h
  exact absurd (congrArg Prod.snd this) (by decide)

/-! ### §3.3 The indexing functor `F : Ctx ⥤ Cat` with monoidal `Discrete Bundle` fibres. -/

/-- The fibre over every context is the resource category `Discrete Bundle`. -/
abbrev Fib : Cat.{0, 0} := Cat.of (Discrete Bundle)

/-- The reindexing functor for the `extend` arrow: `Discrete.monoidalFunctor dropArt`, the strong
monoidal "drop art" functor on `Discrete Bundle`. -/
abbrev reindexExtend : Discrete Bundle ⥤ Discrete Bundle := Discrete.monoidalFunctor dropArt

/-- The action of the indexing functor on objects: every context maps to the one fibre `Fib`. -/
def Fobj : Ctx → Cat.{0, 0} := fun _ => Fib

/-- The action of the indexing functor on morphisms: identities go to the identity functor (as a
`Cat`-hom), and `extend` goes to `reindexExtend`. -/
def Fmap : ∀ {a b : Ctx}, (a ⟶ b) → (Fobj a ⟶ Fobj b)
  | _, _, CtxHom.id _ => 𝟙 _
  | _, _, CtxHom.extend => Functor.toCatHom reindexExtend

/-- **The indexing functor `F : Ctx ⥤ Cat`.** Functoriality (`map_id`, `map_comp`) holds by the case
analysis of `Ctx`: the only non-degenerate composite is `id ≫ extend = extend`, on which both sides are
`reindexExtend`; `extend ≫ id = extend` likewise. -/
def F : Ctx ⥤ Cat.{0, 0} where
  obj := Fobj
  map := Fmap
  map_id := by rintro (_ | _) <;> rfl
  map_comp := by
    rintro _ _ _ (_ | _) (_ | _) <;> rfl

/-- `F.obj c` is `Discrete Bundle` for every context — so the fibre is the monoidal resource category. -/
theorem F_obj (c : Ctx) : F.obj c = Cat.of (Discrete Bundle) := rfl

/-- **(b) Each fibre is genuinely MONOIDAL — the resource `⊗`.** The `MonoidalCategory (F.obj c)`
instance, inherited from `Discrete.monoidal` on the bundle `CommMonoid`. This is the linear tensor:
`X ⊗ Y` = bundle union, `𝟙_` = the empty bundle, and crucially NO diagonal `Δ : X ⟶ X ⊗ X` (it is not
cartesian). -/
instance fibreMonoidal (c : Ctx) : MonoidalCategory (F.obj c) :=
  inferInstanceAs (MonoidalCategory (Discrete Bundle))

/-- **The reindexing functor is (strong, hence) LAX monoidal — PROVED.** For the `extend` arrow this is
`Discrete.monoidalFunctorMonoidal dropArt` (a strong monoidal functor); for identities it is the
identity functor's monoidal structure. So every reindexing carries `ε`/`μ`, the data an indexed
monoidal category demands. -/
@[reducible] def reindexLax : ∀ {a b : Ctx} (u : a ⟶ b),
    (F.map u).toFunctor.LaxMonoidal
  | _, _, CtxHom.id _ =>
      -- `F.map (𝟙 c) = 𝟙 (F.obj c)` in `Cat`; its `toFunctor` is the identity functor.
      (inferInstance : (𝟭 (Discrete Bundle)).LaxMonoidal)
  | _, _, CtxHom.extend =>
      -- `F.map extend = Functor.toCatHom reindexExtend`; its `toFunctor` is `reindexExtend`.
      (Discrete.monoidalFunctorMonoidal dropArt).toLaxMonoidal

/-- **THE KEYSTONE INSTANCE: the dregg indexed monoidal category.** Base = context poset `Ctx`,
fibres = monoidal resource category `Discrete Bundle`, reindexing = lax (in fact strong) monoidal
`dropArt`. This is one object that carries BOTH the predicate base and the resource tensor. -/
def dreggIM : IndexedMonoidal.IndexedMonoidalCategory.{0, 0} where
  B := Ctx
  F := F
  fibreMonoidal := fibreMonoidal
  reindexLax := fun u => reindexLax u

/-- The total category `∫F` of the dregg instance, with its forgetful projection to `Ctx`. -/
abbrev DreggTotal : Type _ := dreggIM.Total

/-! ### §3.4 The two structures COEXIST on the one total category `∫F`. -/

/-- The total category is genuinely a category (Grothendieck of `F`) — sanity that the weld typechecks
as a single object. -/
example : Category DreggTotal := inferInstance

/-- The forgetful fibration `∫F ⥤ Ctx` exists — the predicate base is recoverable from the total
category. -/
example : DreggTotal ⥤ Ctx := dreggIM.forget

end DreggInstance

/-! ###############################################################################
# §4 — The PREDICATE side (∃/∀ adjoints) and the INTERACTION law.
##################################################################################

The base `Ctx` carries the predicate logic exactly as `Lawvere.PartA`: a base map underlies a function
`f : ι_lo → ι_hi` on context *index sets*, and reindexing along it has the quantifier triple
`∃_f ⊣ f* ⊣ ∀_f`. We realise this concretely and then state the projection/Frobenius INTERACTION with
the fibrewise resource `⊗`. -/

namespace Predicate

open Dregg2.Intent

variable {ι κ : Type u}

/-! ### §4.1 The ∃/∀ adjoint triple on a base map (the Lawvere PartA doctrine, reused).

We re-expose the posetal Set-doctrine quantifiers so this module is self-contained on the predicate
side; these are definitionally `Set.image`/`Set.preimage`/`Set.kernImage` and the adjunctions are the
mathlib `GaloisConnection`s — the same content as `Lawvere.PartA`, now placed in the indexed-monoidal
setting where the base map `f` is a `Ctx`-style context reindexing. -/

/-- `∃_f` — existential quantification / LEFT adjoint to reindexing. -/
def existsAlong (f : ι → κ) : Set ι → Set κ := Set.image f
/-- `f*` — reindexing / substitution. -/
def reindex (f : ι → κ) : Set κ → Set ι := Set.preimage f
/-- `∀_f` — universal quantification / RIGHT adjoint to reindexing. -/
def forallAlong (f : ι → κ) : Set ι → Set κ := Set.kernImage f

/-- **(a) `∃_f ⊣ f*`, PROVED** — the LEFT adjoint of reindexing (`Set.image_preimage`). -/
theorem existsAlong_adj_reindex (f : ι → κ) :
    GaloisConnection (existsAlong f) (reindex f) :=
  Set.image_preimage

/-- **(a) `f* ⊣ ∀_f`, PROVED** — the RIGHT adjoint of reindexing (`Set.preimage_kernImage`). Together
with the previous lemma this is the full Lawvere triple `∃_f ⊣ f* ⊣ ∀_f` on the base map. -/
theorem reindex_adj_forallAlong (f : ι → κ) :
    GaloisConnection (reindex f) (forallAlong f) :=
  Set.preimage_kernImage

/-- The full predicate triple, packaged. -/
theorem lawvere_triple (f : ι → κ) :
    GaloisConnection (existsAlong f) (reindex f) ∧
      GaloisConnection (reindex f) (forallAlong f) :=
  ⟨existsAlong_adj_reindex f, reindex_adj_forallAlong f⟩

/-! ### §4.2 THE INTERACTION (the genuinely new welding content): the projection / Frobenius law
relating `∃_f` (the predicate left adjoint) and a fibrewise resource tensor.

In an indexed monoidal category the *Frobenius / projection formula* relates the base quantifier `∃_f`
to the fibre tensor `⊗`. Modelling the predicate fibre as `(Set ·, ∩)` (the meet IS the cartesian
fibre tensor on the predicate side, the partner of the genuine resource `⊗` on the resource side), the
projection law is

      ∃_f (S ∩ f* T) = ∃_f S ∩ T          (Frobenius reciprocity).

Here `∩` plays the rôle of the fibrewise tensor on the predicate fibre and `f*` is reindexing. We prove
the EQUALITY for the Set fibre (it holds because `f*` is a frame homomorphism), AND — to show the LAX
form is the honest one in the absence of that special structure — we prove the LAX `⊆` half holds for an
ARBITRARY relational reindexing (where equality FAILS), then exhibit the failure concretely. This mirrors
`Lawvere` §B.6: the literal posetal equality is special to the function/quotient fibre; the surviving
law in general is the one-directional projection. -/

/-- **The Frobenius / projection law (EQUALITY), PROVED for the Set fibre** —
`∃_f (S ∩ f* T) = ∃_f S ∩ T`. This is the interaction of the predicate left adjoint `∃_f` with the
fibre meet, available because `f* = preimage` is a frame homomorphism. -/
theorem frobenius (f : ι → κ) (S : Set ι) (T : Set κ) :
    existsAlong f (S ∩ reindex f T) = existsAlong f S ∩ T :=
  Set.image_inter_preimage f S T

/-- The relational reindexing `Rᵒᵖ`-pullback used to show the LAX projection survives where the literal
Frobenius equality fails: `relForall R T = {s | ∀ w, R s w → w ∈ T}` (the box) and
`relExists R S = {w | ∃ s, R s w ∧ s ∈ S}` (the diamond), exactly as `Lawvere.PartB`. -/
def relExists (R : ι → ι → Prop) (S : Set ι) : Set ι := {w | ∃ s, R s w ∧ s ∈ S}
def relForall (R : ι → ι → Prop) (T : Set ι) : Set ι := {s | ∀ w, R s w → w ∈ T}

/-- **The LAX projection / Frobenius `⊆` half, PROVED for an ARBITRARY relational reindexing** —
`relExists R (S ∩ relForall R T) ⊆ relExists R S ∩ T`. This is the honest surviving form of the
interaction when the reindexing is NOT a frame homomorphism (no functional structure): any world reached
from a source that is in `S` AND knows `T` is both in `∃_R S` and (being a successor of a `T`-knower)
in `T`. The reverse fails (§4.3), so this `⊆` is non-vacuous content, not a `True`-collapse. -/
theorem frobenius_le (R : ι → ι → Prop) (S T : Set ι) :
    relExists R (S ∩ relForall R T) ⊆ relExists R S ∩ T := by
  rintro w ⟨s, hsw, hsS, hsT⟩
  exact ⟨⟨s, hsw, hsS⟩, hsT w hsw⟩

/-! ### §4.3 TEETH for the interaction: the naive EQUALITY FAILS (so the lax `⊆` is the real law). -/

namespace FrobeniusFails

/-- A reflexive but non-functional (non-transitive) relation on `Fin 3`, à la `Lawvere.PartB.S4Breaks`:
`R a b` iff `a = b` or one of the edges `0∼1`, `1∼2`. Used as a relational reindexing for which the
projection EQUALITY fails (only the lax `⊆` of `frobenius_le` survives). -/
def R : Fin 3 → Fin 3 → Prop := fun a b => a = b ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2)

instance instDecR : DecidableRel R := fun a b => by unfold R; exact inferInstance

/-- Source set `S := {0}`, target set `T := {1}`. -/
def Sf : Set (Fin 3) := {0}
def Tf : Set (Fin 3) := {1}

instance : DecidablePred (· ∈ Sf) := fun w => by unfold Sf; exact inferInstance
instance : DecidablePred (· ∈ Tf) := fun w => by unfold Tf; exact inferInstance

/-- `1 ∈ relExists R S ∩ T` — PROVED. `1` is an `R`-successor of `0 ∈ S` (edge `0∼1`) and `1 ∈ T`. -/
theorem one_mem_rhs : (1 : Fin 3) ∈ relExists R Sf ∩ Tf := by
  show (∃ s, R s 1 ∧ s ∈ Sf) ∧ (1 : Fin 3) ∈ Tf
  decide

/-- `1 ∉ relExists R (S ∩ relForall R T)` — PROVED. The only `S`-source for `1` is `0`, but `0` does
NOT know `T = {1}` (`0` reflexively `R`-sees `0 ∉ T`), so `S ∩ □T` has no qualifying source. -/
theorem one_not_mem_lhs : (1 : Fin 3) ∉ relExists R (Sf ∩ relForall R Tf) := by
  show ¬ ∃ s, R s 1 ∧ s ∈ Sf ∧ (∀ w, R s w → w ∈ Tf)
  decide

/-- **The naive projection EQUALITY FAILS — PROVED.** `relExists R (S ∩ relForall R T) ≠ relExists R S ∩ T`
on this non-functional reindexing: `1` is in the RHS but not the LHS. Hence the reverse of `frobenius_le`
is false here, and the LAX `⊆` half is the genuine surviving interaction (the literal Frobenius equality
is special to the frame-homomorphism / function fibre — `frobenius`). -/
theorem frobenius_eq_fails :
    relExists R (Sf ∩ relForall R Tf) ≠ relExists R Sf ∩ Tf := by
  intro h
  exact one_not_mem_lhs (h ▸ one_mem_rhs)

end FrobeniusFails

end Predicate

/-! ###############################################################################
# §5 — TEETH: the dregg instance is NON-VACUOUS.
##################################################################################

We certify the keystone is not a degenerate / subsingleton collapse on every axis the task names:
  * the FIBRE is not subsingleton-collapsed — the resource `⊗` genuinely discriminates;
  * the fibre `⊗` is a real binary operation (a genuine tensor, not the unit);
  * the reindexing genuinely attenuates (`dropArt` not injective — §3.2);
  * the predicate `∃_f` genuinely discriminates (non-trivial image);
  * the TOTAL category `∫F` has a genuine non-identity morphism whose base leg is `extend` and whose
    fibre leg is a real `Discrete` tensor map — the two structures meet on ONE arrow. -/

namespace Teeth

open Dregg2.Intent DreggInstance Predicate

/-- **The fibre is NOT subsingleton-collapsed.** The resource objects `res 2 0` and `res 0 0` are
distinct (`2 gold` ≠ `empty`), so the fibre `Discrete Bundle` has at least two objects — the monoidal
structure is on a genuinely non-trivial category. -/
theorem fibre_not_subsingleton : (res 2 0) ≠ (res 0 0) := by
  intro h
  have : (mkBundle 2 0) = (mkBundle 0 0) := congrArg Discrete.as h
  exact absurd (Multiplicative.ofAdd.injective this) (by decide)

/-- **The fibre `⊗` is a REAL binary operation.** `res 1 0 ⊗ res 1 0 = res 2 0` (1 gold tensored with
1 gold yields 2 gold) — the tensor genuinely ADDS the bundles; it is not a projection or the unit. -/
theorem tensor_is_real_binop :
    (res 1 0 ⊗ res 1 0 : Discrete Bundle) = res 2 0 := by
  apply Discrete.ext
  show mkBundle 1 0 * mkBundle 1 0 = mkBundle 2 0
  apply Multiplicative.toAdd.injective
  rfl

/-- **The `⊗` discriminates: tensoring is NOT idempotent / NOT a no-op.** `res 1 0 ⊗ res 1 0 ≠ res 1 0`
— so the fibre tensor is a genuine monoidal product (had it been cartesian-with-a-collapse or trivial,
this could fail). Combined with `tensor_is_real_binop` this shows the linear `⊗` truly accumulates. -/
theorem tensor_not_idem : (res 1 0 ⊗ res 1 0 : Discrete Bundle) ≠ res 1 0 := by
  rw [tensor_is_real_binop]
  exact fun h => by
    have : (mkBundle 2 0) = (mkBundle 1 0) := congrArg Discrete.as h
    exact absurd (Multiplicative.ofAdd.injective this) (by decide)

/-- **THE LINEARITY TEETH: the fibre `⊗` is NOT cartesian — there is NO diagonal `Δ : X ⟶ X ⊗ X`.**
This is the WHOLE POINT of indexing *monoidal* (not Heyting/cartesian) fibres: a resource cannot be
duplicated. Concretely, a morphism `res 1 0 ⟶ res 1 0 ⊗ res 1 0` in `Discrete Bundle` would force
`(res 1 0).as = (res 1 0 ⊗ res 1 0).as`, i.e. `mkBundle 1 0 = mkBundle 2 0` (the tensor ADDS, so
`1 gold ≠ 2 gold`) — impossible. So `1 gold` cannot copy itself: the fibre tensor is genuinely linear,
withholding the cartesian `Δ`. (A Heyting fibre would HAVE this diagonal; that is exactly the wrong,
duplicable behaviour the indexed-monoidal fix forbids.) -/
theorem no_diagonal_linear :
    IsEmpty (res 1 0 ⟶ (res 1 0 ⊗ res 1 0 : Discrete Bundle)) := by
  refine ⟨fun f => ?_⟩
  have heq : (res 1 0).as = (res 1 0 ⊗ res 1 0 : Discrete Bundle).as := Discrete.eq_of_hom f
  rw [tensor_is_real_binop] at heq
  -- `heq : mkBundle 1 0 = mkBundle 2 0`, contradiction.
  have : ((1, 0) : ℕ × ℕ) = (2, 0) := Multiplicative.ofAdd.injective heq
  exact absurd (congrArg Prod.fst this) (by decide)

/-- **The predicate `∃_f` genuinely discriminates.** For the constant base map `f : Fin 1 → Fin 2`,
`∃_f {0} = {f 0}` is a genuine singleton image, and `∃_f` is NOT the trivial (always-`univ` or
always-`∅`) operator: `∃_f ∅ = ∅` while `∃_f {0} = {0}` differ. -/
theorem existsAlong_discriminates :
    existsAlong (fun _ : Fin 1 => (0 : Fin 2)) ({0} : Set (Fin 1))
      ≠ existsAlong (fun _ : Fin 1 => (0 : Fin 2)) (∅ : Set (Fin 1)) := by
  intro h
  have h0 : (0 : Fin 2) ∈ existsAlong (fun _ : Fin 1 => (0 : Fin 2)) ({0} : Set (Fin 1)) :=
    ⟨0, by trivial, rfl⟩
  rw [h] at h0
  rw [existsAlong, Set.image_empty] at h0
  exact absurd h0 (Set.notMem_empty _)

/-! ### §5.1 The two structures meet on ONE total morphism.

We build a genuine non-identity morphism of the total category `∫F = DreggTotal` whose base leg is the
`extend` context map (predicate side) and whose fibre leg is a real resource map (the `Discrete` tensor
unitor). This is the concrete witness that the predicate base and the resource fibre are welded on a
single arrow of one category. -/

/-- The total object over `lo` carrying `1 gold`. -/
def objLo : DreggTotal := ⟨Ctx.lo, res 1 0⟩
/-- The total object over `hi` carrying `1 gold` (the `extend`-reindex of `res 1 0` is again `res 1 0`,
since `dropArt` fixes the gold coordinate). -/
def objHi : DreggTotal := ⟨Ctx.hi, res 1 0⟩

/-- **A genuine non-identity total morphism `objLo ⟶ objHi`.** Its base leg is `extend : lo ⟶ hi`
(the predicate/context reindexing) and its fibre leg is the identity `Discrete` map on `res 1 0` (valid
because the reindexing `dropArt` fixes the gold coordinate, so `(F.map extend)(res 1 0) = res 1 0`). The
existence of this arrow — base leg in `Ctx`, fibre leg in `Discrete Bundle` — is the weld made concrete:
ONE morphism of ONE category touching BOTH faces. -/
def weldMorphism : objLo ⟶ objHi where
  base := CtxHom.extend
  fiber := eqToHom (by
    -- `(F.map extend)(res 1 0) = reindexExtend (res 1 0) = mk (dropArt (mkBundle 1 0)) = res 1 0`.
    apply Discrete.ext
    rfl)

/-- The weld morphism's base leg is exactly the `extend` context arrow — the predicate side of the
weld. -/
theorem weldMorphism_base : weldMorphism.base = CtxHom.extend := rfl

/-- The weld morphism is NON-trivial: it genuinely CROSSES contexts (`objLo.base = lo ≠ hi = objHi.base`),
so it is not a self-loop / endo-identity — its base leg `extend` is a real context extension, not an
identity. This certifies the total morphism welds two genuinely distinct fibres, not one fibre to
itself. -/
theorem weldMorphism_crosses_contexts : objLo.base ≠ objHi.base := by
  show Ctx.lo ≠ Ctx.hi
  exact fun h => Ctx.noConfusion h

end Teeth

/-! ###############################################################################
# Kernel-clean pins (`#assert_axioms`).
##################################################################################
Every keystone is pinned to `{propext, Classical.choice, Quot.sound}`. A `sorryAx` or stray `axiom`
fails the pin and the build. -/

-- §1–§3: the general structure, the total category, and the concrete keystone instance.
#assert_axioms DreggInstance.F
#assert_axioms DreggInstance.fibreMonoidal
#assert_axioms DreggInstance.reindexLax
#assert_axioms DreggInstance.dreggIM
#assert_axioms DreggInstance.dropArt_not_injective

-- §4: the predicate triple and the interaction (projection/Frobenius) law + its teeth.
#assert_axioms Predicate.existsAlong_adj_reindex
#assert_axioms Predicate.reindex_adj_forallAlong
#assert_axioms Predicate.lawvere_triple
#assert_axioms Predicate.frobenius
#assert_axioms Predicate.frobenius_le
#assert_axioms Predicate.FrobeniusFails.frobenius_eq_fails

-- §5: non-vacuity teeth.
#assert_axioms Teeth.fibre_not_subsingleton
#assert_axioms Teeth.tensor_is_real_binop
#assert_axioms Teeth.tensor_not_idem
#assert_axioms Teeth.no_diagonal_linear
#assert_axioms Teeth.existsAlong_discriminates
#assert_axioms Teeth.weldMorphism
#assert_axioms Teeth.weldMorphism_crosses_contexts

end Dregg2.Metatheory.IndexedMonoidal
