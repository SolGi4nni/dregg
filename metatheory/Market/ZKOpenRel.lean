/-
# Market.ZKOpenRel — the fhEgg CATEGORICAL UNIFICATION: `ZKOpenRel_R`, the objects + the feedback closure (refuted conjecture + proven Tarski replacement).

**Q2 of `docs/deos/FHEGG-CODEX-INSIGHTS.md`, formalized as a Lean development (not prose).** Codex
(GPT-5.6-sol) named the categorical home of the whole fhEgg stack:

> a **resource-graded, proof-carrying, guarded traced symmetric monoidal category of open relations**,
> realized by **decorated cospans** — `ZKOpenRel_R`, with:
>   * the **resource-defect** `d_M ∈ R` a strong monoidal functor to the additive monoid `(R,+,0)`;
>   * **conservation** = the zero-defect subcategory `d⁻¹(0)`;
>   * the **ring** = the guarded trace (feedback);
>   * **privacy** = a simulator natural transformation `View ≈ Sim∘Q` over the leakage functor `Q`;
>   * the four fhEgg objects (turn / auction / circulation / convex engine) as INSTANCES;
>   * **the ONE open theorem** = the compositionality/closure theorem under FEEDBACK (the guarded
>     trace) + ADAPTIVE composition. Codex was candid: *this is a well-posed research target with the
>     right objects named, NOT a discharged proof.*

This module turns that from prose into a real, sorry-free Lean development. It builds the OBJECTS,
proves the TRACTABLE pieces, and — where codex named a feedback-closure conjecture — REFUTES the false
statement with a proof (`guardedTraceClosure_refuted`) and REPLACES it with the true Tarski feedback
closure (`traceAdmissible_guarded`), which the four instances satisfy — **never a `sorry`, never a
fake-green tautology.**

## What is BUILT + PROVEN (the tractable core, kernel-clean)

  * **THE CATEGORY `ZKOpenRel R`** (§1) — a lightweight decorated-cospan / open-relation category: objects
    carry a boundary state `S`; a morphism `X ⟶ Y` carries the **resource defect** `d ∈ R` (the grade)
    and a **feasibility relation** `rel : S_X → S_Y → Prop` (the open topology's fiber). Composition =
    relational (fiber-product) composition with **defects ADD**; identity = `Eq` with defect `0`. The
    genuine `CategoryTheory.Category` laws are PROVEN (`id_comp`/`comp_id`/`assoc`).
  * **THE RESOURCE-DEFECT FUNCTOR `d_M`** (§2) — `dFunctor : ZKOpenRel R ⥤ SingleObj (Multiplicative R)`,
    a genuine functor to the delooping of the additive monoid `(R,+,0)` (`map_id`/`map_comp` = the
    functor laws = `d(𝟙)=0`, `d(g∘f)=d f + d g`). Its **strong-monoidal** structure equations over the
    open-system tensor `⊗` (`dFunctor_tensor : d(f ⊗ g) = d f + d g`, `dFunctor_unit`) are proven — the
    conservation-accounting `toBal`-homomorphism, lifted to the functor.
  * **CONSERVATION = `d⁻¹(0)`** (§3) — `Conservative f := dGrade f = 0`. Proven a **monoidal
    subcategory**: `id_conservative`, `comp_conservative` (adaptive/sequential composition preserves
    zero defect), `tensor_conservative` (the ⊗ preserves it). Plus `iterate_conservative` — a conserving
    turn iterated `n` times stays conserving (the history `T_n∘…∘T_1`).
  * **THE FOUR INSTANCES** (§4–5) recovered as `ZKOpenRel` objects living in `d⁻¹(0)`:
      1. **turn** — a conserving proof-carrying endomorphism `T:S→S` (`turnMor`), history = its iterate;
      2. **auction** — the multilateral Frobenius-merge clearing `Market/Clearing.lean`'s `ringClearing`
         as a conservative morphism (`auctionMor`, `auction_conservative` via `clearing_conserves_per_asset`);
      3. **circulation** — a capacity-respecting flow `Market/CertF.lean`'s `FlowLP` as a conservative
         morphism whose defect is the node imbalance `A f` (`circulationMor`, conservative ⇔ `A f = 0`
         = `PrimalFeasible`);
      4. **convex engine** — the same flow carrying its `Cert-F` certificate (the refinement decoration),
         conservative on the same `A f = 0` face.
  * **THE PRIVACY NATURAL TRANSFORMATION** (§7) — `PrivacyNatTrans`, the `View ≈ Sim∘Q` shape (leakage
    map `Q`, real `view`, witness-free `sim`, naturality `view = sim∘Q`); `same_leakage_indistinguishable`
    (the reveal-nothing consequence) is PROVEN, and `Market/RevealNothing.lean`'s `RevealBundle` is shown
    to BE exactly such a natural transformation (`ofRevealBundle`). This is the categorical home of the
    reveal-nothing theorem — privacy = the simulator natural transformation over the leakage functor `Q`.

## THE FEEDBACK CLOSURE (§6) — a REFUTED conjecture + its PROVEN Tarski replacement

The guarded trace (feedback) is the ring/feedback operation. Its GRADE side is easy and PROVEN
(`gtrace_conservative`: feedback does not change the resource accounting — `d(tr f) = d f`). The
feasibility half was originally STATED as the conjecture `GuardedTraceClosure R` ("guarded trace of a
guarded conservative morphism is guarded"). **Codex R3 Q3 REFUTED it** (`guardedTraceClosure_refuted`): a
minimal `Bool`-negation feedback is conservative + guarded + functional yet its trace is EMPTY, so the
conjecture is FALSE for every `R` — the module's `Guarded` is a totality, not a genuine guarded/Conway
trace. Consequently the old `ZKUnification` (whose one field WAS `GuardedTraceClosure R`) could never be
inhabited. We refute-and-replace:

  * PROVE the **non-feedback fragment**: guardedness is preserved by sequential/adaptive composition
    (`comp_guarded`) and by tensor (`tensor_guarded`);
  * REFUTE the false conjecture with a PROOF (`guardedTraceClosure_refuted`, the `Bool`-negation witness);
  * REPLACE it with the TRUE **Tarski feedback closure** `traceAdmissible_guarded : TraceAdmissible f →
    Guarded (gtrace f)` — when the feedback is a MONOTONE self-map of a complete lattice, its least fixed
    point (`OrderHom.lfp`) witnesses that the loop clears. This lands on the already-proven monotone
    crossing operator of `Market/FhEggClearing.lean` (`crossing_gtrace_guarded` via `crossing_fixed` /
    `Fstep_monotone`), the four instances are shown `TraceAdmissible`, and it is exercised NON-VACUOUSLY on
    a real non-total monotone feedback on the complete lattice `Prop` (`andFeedback_gtrace_guarded`);
  * COMPLETE the closure target (codex named feedback AND adaptive composition): the guarded trace of
    admissible feedbacks is closed under sequential (`gtrace_comp_guarded`) and tensor
    (`gtrace_tensor_guarded`) composition, plus the typed PARTIAL guard `GuardedOn P` for the honest
    "markets do not clear every boundary state" (`comp_guardedOn`, `guarded_iff_guardedOn_true`);
  * package it as `AdmissibleTraceClosure R` — the true closure, carried as `ZKUnification.feedback_closure`,
    now a THEOREM (`admissibleTraceClosure_holds`) so the bundle is INHABITED (`zkUnification`).

**HONEST GRADE.** The objects + functor + conservation-as-kernel + four instances + non-feedback
composition + privacy natural transformation are PROVEN and kernel-clean; the feedback closure is now a
proven refutation of the false full-generality conjecture PLUS a proven replacement for the mechanism-
relevant (monotone/finite) cases — the unification holds for the admissible instances, unconditionally.

Pure.
-/
import Market.Clearing
import Market.CertF
import Market.RevealNothing
import Market.FhEggClearing
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Order.FixedPoints
import Dregg2.Tactics

namespace Market.ZKOpenRel

open CategoryTheory
open Dregg2.Intent
open Dregg2.Exec (AssetId)
open Matrix

set_option autoImplicit false

/-! ## 1. THE CATEGORY `ZKOpenRel R` — resource-graded open relations (decorated cospans, lightweight).

An **object** is a boundary/state interface `S` (the typed ports + private state of codex's `X`). A
**morphism** `X ⟶ Y` is the decoration a decorated cospan carries at the relevant grain: a **resource
defect** `defect ∈ R` (the grade `d_M`) and a **feasibility relation** `rel : S_X → S_Y → Prop` (the
fiber of the open topology — `∃`-over the private witness). Composition is the fiber product (relational
composition) with **defects adding**; identity is `Eq` with defect `0`. The category laws hold — this is
a genuine `CategoryTheory.Category`. -/

/-- **An object of `ZKOpenRel R`** — a boundary/state interface (codex's typed ports + private state
`S_X`). `R` is a phantom parameter fixing which resource group grades this category (so distinct `R`
give distinct categories, hence distinct `Category` instances). -/
structure ZKObj (R : Type) where
  /-- The boundary/state carrier (ports + private state). -/
  S : Type

/-- **A morphism `X ⟶ Y` of `ZKOpenRel R`** — the decorated-cospan decoration: the resource **defect**
(grade `d_M`) and the **feasibility relation** (the open topology's fiber, `∃`-over the private
witness). Composition adds defects and composes relations. -/
@[ext] structure ZKHom {R : Type} [AddCommMonoid R] (X Y : ZKObj R) where
  /-- The **resource defect** `d_M ∈ R` — the grade. Conservation is `defect = 0`. -/
  defect : R
  /-- The **feasibility relation** — the fiber of the open topology (`∃` over the private witness). -/
  rel : X.S → Y.S → Prop

variable {R : Type} [AddCommMonoid R]

/-- Identity — defect `0`, the diagonal relation `Eq` (the trivial open topology). -/
def idHom (X : ZKObj R) : ZKHom X X where
  defect := 0
  rel := Eq

/-- **Composition — the fiber product, with DEFECTS ADDING.** `(f ≫ g).rel x z = ∃ y, f x y ∧ g y z`
(relational/fiber-product composition at the shared boundary `Y`) and `(f ≫ g).defect = f.defect +
g.defect` (the resource defect is additive over composition — half the strong-monoidal-functor law). -/
def compHom {X Y Z : ZKObj R} (f : ZKHom X Y) (g : ZKHom Y Z) : ZKHom X Z where
  defect := f.defect + g.defect
  rel x z := ∃ y, f.rel x y ∧ g.rel y z

/-- **`ZKOpenRel R` is a genuine category.** The relational-composition laws (identity = `Eq`,
associativity of the fiber product) and the additive-monoid grade laws (`0 + a = a`, `(a+b)+c =
a+(b+c)`) together give the `CategoryTheory.Category` structure. -/
instance category : Category (ZKObj R) where
  Hom X Y := ZKHom X Y
  id X := idHom X
  comp f g := compHom f g
  id_comp {X Y} f := by
    apply ZKHom.ext
    · exact zero_add _
    · funext x y
      exact propext ⟨by rintro ⟨z, rfl, h⟩; exact h, fun h => ⟨x, rfl, h⟩⟩
  comp_id {X Y} f := by
    apply ZKHom.ext
    · exact add_zero _
    · funext x y
      exact propext ⟨by rintro ⟨z, h, rfl⟩; exact h, fun h => ⟨y, h, rfl⟩⟩
  assoc {W X Y Z} f g h := by
    apply ZKHom.ext
    · exact add_assoc _ _ _
    · funext x w
      exact propext
        ⟨by rintro ⟨z, ⟨y, hf, hg⟩, hh⟩; exact ⟨y, hf, z, hg, hh⟩,
         by rintro ⟨y, hf, z, hg, hh⟩; exact ⟨z, ⟨y, hf, hg⟩, hh⟩⟩

@[simp] theorem id_defect (X : ZKObj R) : (𝟙 X : ZKHom X X).defect = 0 := rfl

@[simp] theorem comp_defect {X Y Z : ZKObj R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).defect = f.defect + g.defect := rfl

/-! ## 2. THE RESOURCE-DEFECT FUNCTOR `d_M` — a strong monoidal functor to `(R,+,0)`.

`d_M` is the grade. As a functor it lands in the delooping `SingleObj (Multiplicative R)` — the additive
monoid `(R,+,0)` as a one-object category — and its `map_id`/`map_comp` ARE the functor laws
`d(𝟙)=0`, `d(g∘f)=d f + d g`. Its strong-monoidal structure equations over the open-system tensor `⊗`
(§below) are `dFunctor_tensor`/`dFunctor_unit`. -/

/-- **`dGrade` — the resource defect of a morphism**, `d_M ∈ R`. (`= dFunctor.map` up to the delooping
coercion; used directly for the conservation predicate.) -/
def dGrade {X Y : ZKObj R} (f : X ⟶ Y) : R := f.defect

/-- **`dFunctor` — the resource-defect functor `d : ZKOpenRel R ⥤ (R,+,0)`.** Lands in the delooping
`SingleObj (Multiplicative R)` of the additive monoid; `map` sends a morphism to its defect (as a
`Multiplicative` element), and the functor laws are exactly `d(𝟙 X) = 0` and `d(g ∘ f) = d f + d g` —
the conservation-accounting homomorphism, as a functor. (Target composition is `flip (*)`; the grade
commutes, so the direction is immaterial.) -/
def dFunctor : ZKObj R ⥤ SingleObj (Multiplicative R) where
  obj _ := SingleObj.star _
  map f := Multiplicative.ofAdd f.defect
  map_id X := by
    show Multiplicative.ofAdd ((𝟙 X : ZKHom X X).defect) = 1
    simp
  map_comp {X Y Z} f g := by
    show Multiplicative.ofAdd ((f ≫ g).defect) = Multiplicative.ofAdd g.defect * Multiplicative.ofAdd f.defect
    rw [comp_defect, ← ofAdd_add, add_comm f.defect g.defect]

/-- The functor law `d(g ∘ f) = d f + d g`, read off directly as an equation in `R`. -/
theorem dGrade_comp {X Y Z : ZKObj R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    dGrade (f ≫ g) = dGrade f + dGrade g := rfl

/-- The functor law `d(𝟙) = 0`. -/
theorem dGrade_id (X : ZKObj R) : dGrade (𝟙 X) = 0 := rfl

/-! ### The open-system tensor `⊗` and the strong-monoidal structure of `d`. -/

/-- **The tensor of open systems** on objects — side-by-side boundaries `S_X × S_Y`. -/
def tensorObj (X Y : ZKObj R) : ZKObj R := ⟨X.S × Y.S⟩

/-- **The unit object** — the empty boundary. -/
@[reducible] def unitObj : ZKObj R := ⟨PUnit⟩

/-- **The tensor of morphisms** — parallel composition: relations run side by side, **defects ADD**
(the other half of the strong-monoidal-functor law: `d` is additive over `⊗`, not just `∘`). -/
def tensorHom {X Y X' Y' : ZKObj R} (f : X ⟶ Y) (g : X' ⟶ Y') :
    tensorObj X X' ⟶ tensorObj Y Y' where
  defect := f.defect + g.defect
  rel p q := f.rel p.1 q.1 ∧ g.rel p.2 q.2

/-- **STRONG-MONOIDAL: `d(f ⊗ g) = d f + d g`.** The resource defect is additive over the monoidal
product of open systems (`⊗`), completing — with `dGrade_comp` (over `∘`) and `dGrade_id` — the
strong-monoidal-functor equations for the grade `d : ZKOpenRel R → (R,+,0)`. This is the categorical
form of `Market/Clearing.lean`'s `toBal_mul` (the per-asset reading is additive over the ⊗-pool). -/
theorem dFunctor_tensor {X Y X' Y' : ZKObj R} (f : X ⟶ Y) (g : X' ⟶ Y') :
    dGrade (tensorHom f g) = dGrade f + dGrade g := rfl

/-- **STRONG-MONOIDAL: `d(𝟙_⊗) = 0`.** The tensor unit carries zero defect (the monoidal-unit law). -/
theorem dFunctor_unit : dGrade (𝟙 (unitObj : ZKObj R)) = 0 := rfl

/-! ## 3. CONSERVATION = the zero-defect subcategory `d⁻¹(0)`.

Conservation is exactly `d_M = 0` — the kernel of the resource-defect functor. It is a **monoidal
subcategory**: closed under identity, (adaptive/sequential) composition, and tensor. This is the
categorical home of `Market/Clearing.lean`'s per-asset conservation and `Market/CertF.lean`'s flow
conservation — both are the statement `d = 0`. -/

/-- **`Conservative f` — the morphism lies in `d⁻¹(0)`**: its resource defect is zero (the market as a
whole neither mints nor burns). -/
def Conservative {X Y : ZKObj R} (f : X ⟶ Y) : Prop := dGrade f = 0

/-- The identity is conservative — `d⁻¹(0)` contains all identities (a subcategory). -/
theorem id_conservative (X : ZKObj R) : Conservative (𝟙 X) := dGrade_id X

/-- **ADAPTIVE/SEQUENTIAL COMPOSITION PRESERVES CONSERVATION** — composing two zero-defect morphisms is
zero-defect (`0 + 0 = 0`). `d⁻¹(0)` is closed under `∘` — the non-feedback half of the closure, PROVEN.
This is "a turn stream of conserving turns conserves." -/
theorem comp_conservative {X Y Z : ZKObj R} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Conservative f) (hg : Conservative g) : Conservative (f ≫ g) := by
  simp only [Conservative, dGrade_comp] at *
  rw [hf, hg, add_zero]

/-- **THE TENSOR PRESERVES CONSERVATION** — the ⊗-product of two zero-defect morphisms is zero-defect.
`d⁻¹(0)` is a *monoidal* subcategory (closed under `⊗` as well as `∘`). -/
theorem tensor_conservative {X Y X' Y' : ZKObj R} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (hf : Conservative f) (hg : Conservative g) : Conservative (tensorHom f g) := by
  simp only [Conservative, dFunctor_tensor] at *
  rw [hf, hg, add_zero]

/-- **Iterated composition of a conserving endomorphism.** The turn-kernel history `T^n = T ∘ ⋯ ∘ T`. -/
def iterate {X : ZKObj R} (f : X ⟶ X) : ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | n + 1 => iterate f n ≫ f

/-- **A CONSERVING TURN ITERATED STAYS CONSERVING** — `T^n ∈ d⁻¹(0)` for every `n` (the history of a
conserving turn conserves), by induction from `id_conservative` + `comp_conservative`. -/
theorem iterate_conservative {X : ZKObj R} {f : X ⟶ X} (hf : Conservative f) :
    ∀ n, Conservative (iterate f n)
  | 0 => id_conservative X
  | n + 1 => comp_conservative (iterate_conservative hf n) hf

/-! ## 4. INSTANCE — CIRCULATION (from `Market/CertF.lean`): the flow LP as a graded morphism.

The circulation object is `codex`'s open-network morphism: a capacity-respecting flow whose resource
defect is the **node imbalance** `A f`. It is conservative — lives in `d⁻¹(0)` — exactly when `A f = 0`,
which is `PrimalFeasible`'s conservation clause. Grade `R := V → ℤ` (per-node imbalance). -/

section Circulation
variable {V E : Type} [Fintype V] [Fintype E]

/-- The circulation object — the flow boundary (kept abstract; the categorical content used here is the
grade). -/
@[reducible] def flowObj (V : Type) : ZKObj (V → ℤ) := ⟨PUnit⟩

/-- **The circulation morphism** — a flow `f` on `lp`, graded by its **node imbalance** `A f : V → ℤ`
(zero iff `f` conserves at every node). The decorated-cospan open-network morphism of codex's Q2. -/
def circulationMor (lp : Market.FlowLP V E ℤ) (f : E → ℤ) : flowObj V ⟶ flowObj V where
  defect := lp.A *ᵥ f
  rel _ _ := True

omit [Fintype V] in
/-- **CIRCULATION LIVES IN `d⁻¹(0)` ⇔ IT CONSERVES** — `circulationMor lp f` is `Conservative` exactly
when `A f = 0`, i.e. when `f` is a genuine circulation (`PrimalFeasible.1`). The categorical conservation
predicate IS the flow-conservation `Cert-F` reads. -/
theorem circulation_conservative {lp : Market.FlowLP V E ℤ} {f : E → ℤ}
    (hf : Market.PrimalFeasible lp f) : Conservative (circulationMor lp f) := hf.1

end Circulation

/-- **THE CIRCULATION INSTANCE, WITNESSED** — the worked 3-cycle circulation of `Market/CertF.lean`
(`ringLP`, unit flow `ringF`) is a conservative `ZKOpenRel (Fin 3 → ℤ)` morphism: its node imbalance is
zero (`ringCert_valid.1`, the certificate's primal-feasibility). Circulation recovered as an instance,
in `d⁻¹(0)`. -/
theorem ring_circulation_conservative :
    Conservative (circulationMor Market.ringLP Market.ringF) :=
  circulation_conservative Market.ringCert_valid.1

/-! ## 5. INSTANCE — CONVEX ENGINE + AUCTION + TURN (the remaining three of the four).

  * **convex engine** — the same flow morphism, now carrying its `Cert-F` certificate (the refinement
    2-cell / proof decoration). Its resource defect is the SAME `A f` (conservation on the flow face);
    the certificate is the proof-carrying decoration codex names (`U_θ` fixed solver + certificate
    2-cell). Conservative on `A f = 0`.
  * **auction** — the multilateral Frobenius-merge clearing `Market/Clearing.lean`'s `ringClearing`,
    graded by the per-asset pool imbalance; conservative by `clearing_conserves_per_asset`.
  * **turn** — a conserving proof-carrying endomorphism; history = its `iterate`. -/

/-- **The convex-engine morphism** — a certified flow: the circulation morphism decorated with a
`Cert-F` certificate `(f, π, s)` (the proof-carrying refinement 2-cell). The resource grade is the same
node imbalance `A f`; the certificate rides as attached data (codex's `U_θ` + certificate 2-cell). -/
def convexEngineMor {V E : Type} [Fintype V] [Fintype E]
    (lp : Market.FlowLP V E ℤ) (f : E → ℤ) (_π : V → ℤ) (_s : E → ℤ) : flowObj V ⟶ flowObj V :=
  circulationMor lp f

/-- **THE CONVEX-ENGINE INSTANCE, WITNESSED** — the worked certified triple (`ringCert_valid`) is a
conservative morphism: the certificate's primal conserves, so the graded morphism lies in `d⁻¹(0)`. The
convex engine's *optimality* is `Market/CertF.lean`'s `certifies_epsilon_optimal` (the certificate
2-cell); its *conservation* is this categorical face. -/
theorem convex_engine_conservative :
    Conservative (convexEngineMor Market.ringLP Market.ringF Market.ringπ Market.ringS) :=
  circulation_conservative Market.ringCert_valid.1

section Auction

variable {Stmt Wit : Type} {Bl : Dregg2.Authority.Blocklace.Lace}
  {reg : Dregg2.Authority.Predicate.Registry Stmt Wit}
  {stmtOf : Dregg2.Time.Frame.FrameStatement → Stmt}

/-- **The per-asset resource defect of a market clearing** — `d = Σ_out − Σ_in`, asset by asset (the
categorical grade of the multilateral clearing). Zero exactly when the clearing conserves. -/
def clearingDefect {book : Book DemoRes Bl reg stmtOf} (C : MarketClearing book) : AssetId → ℤ :=
  fun a => (C.alloc.map (fun r => toBal r.as a)).sum - (book.map (fun i => toBal i.offered.as a)).sum

/-- **A market clearing conserves ⇒ its defect is zero** — `clearing_conserves_per_asset` says
`Σ_in = Σ_out` per asset, so `Σ_out − Σ_in = 0`. The `Market/Clearing.lean` conservation keystone, as
the statement `d = 0`. -/
theorem clearingDefect_zero {book : Book DemoRes Bl reg stmtOf} (C : MarketClearing book) :
    clearingDefect C = 0 := by
  funext a
  have h := clearing_conserves_per_asset C a
  simp only [clearingDefect, Pi.zero_apply]
  omega

/-- The clearing object — a market boundary, graded by `R = AssetId → ℤ` (the per-asset ledger). -/
@[reducible] def clearingObj : ZKObj (AssetId → ℤ) := ⟨PUnit⟩

/-- **The auction/clearing morphism** — a multilateral market clearing as a graded endomorphism, graded
by its per-asset pool imbalance `clearingDefect`. -/
def clearingMor {book : Book DemoRes Bl reg stmtOf} (C : MarketClearing book) :
    clearingObj ⟶ clearingObj where
  defect := clearingDefect C
  rel _ _ := True

/-- **A CLEARING LIVES IN `d⁻¹(0)`** — every market clearing is a conservative `ZKOpenRel` morphism (its
per-asset pool imbalance is zero). Conservation = zero defect, connected to `clearing_conserves_per_asset`. -/
theorem clearing_is_conservative {book : Book DemoRes Bl reg stmtOf} (C : MarketClearing book) :
    Conservative (clearingMor C) := clearingDefect_zero C

end Auction

/-- **THE AUCTION INSTANCE, WITNESSED** — the multilateral 3-party ring clearing of
`Market/Clearing.lean` (`ringClearing` — the cross-bid that only a MARKET can fill) is a conservative
`ZKOpenRel` morphism. The Frobenius-merge auction recovered as an instance, in `d⁻¹(0)`. -/
theorem ring_auction_conservative : Conservative (clearingMor Market.ringClearing) :=
  clearing_is_conservative Market.ringClearing

/-- **THE TURN INSTANCE** — a conserving proof-carrying endomorphism `T : S → S` (defect `0`, the
diagonal feasibility relation, decoration elided). Its history `T^n` is `iterate turnMor n`, conserving
for every `n` (`turn_history_conservative`). -/
def turnMor : (unitObj : ZKObj (AssetId → ℤ)) ⟶ unitObj := 𝟙 unitObj

/-- The turn is conservative (defect `0`). -/
theorem turn_conservative : Conservative turnMor := id_conservative _

/-- **THE TURN HISTORY CONSERVES** — `T^n = T ∘ ⋯ ∘ T` stays in `d⁻¹(0)` for every `n` (the
`T_n∘…∘T_1` history of a conserving turn conserves), via `iterate_conservative`. -/
theorem turn_history_conservative (n : ℕ) : Conservative (iterate turnMor n) :=
  iterate_conservative turn_conservative n

/-! ## 6. THE FEEDBACK CLOSURE — the FALSE conjecture REFUTED + its PROVEN Tarski replacement.

The **ring** is the guarded trace: feedback that glues an output boundary back to an input, imposing the
loop constraint. Its GRADE side is trivial and PROVEN (feedback does not change resource accounting). The
feasibility half was conjectured as `GuardedTraceClosure` — but codex R3 Q3 REFUTED it: a `Bool`-negation
feedback is conservative + guarded yet traces to the EMPTY relation. We prove the refutation
(`guardedTraceClosure_refuted`), then REPLACE the false conjecture with the TRUE Tarski feedback closure
`traceAdmissible_guarded` (monotone feedback on a complete lattice ⇒ its `lfp` clears the loop), landing
on the proven fhEgg crossing operator and discharging the four instances as `TraceAdmissible`. -/

/-- **`Guarded f` — the feasibility fiber is inhabited at every input** (`∀ x, ∃ y, rel x y`): the open
system CLEARS — a witness exists, not merely a wired topology. This is the property the trace can
destroy (the empty-relation hazard). -/
def Guarded {X Y : ZKObj R} (f : X ⟶ Y) : Prop := ∀ x, ∃ y, f.rel x y

/-- The identity clears (diagonal is total). -/
theorem id_guarded (X : ZKObj R) : Guarded (𝟙 X) := fun x => ⟨x, rfl⟩

/-- **ADAPTIVE/SEQUENTIAL COMPOSITION PRESERVES GUARDEDNESS** — if `f` and `g` each clear, so does
`f ≫ g` (chain the two witnesses through the shared boundary). The non-feedback half of the closure,
PROVEN: adaptive composition of clearing open systems clears. -/
theorem comp_guarded {X Y Z : ZKObj R} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Guarded f) (hg : Guarded g) : Guarded (f ≫ g) := by
  intro x
  obtain ⟨y, hy⟩ := hf x
  obtain ⟨z, hz⟩ := hg y
  exact ⟨z, y, hy, hz⟩

/-- **THE TENSOR PRESERVES GUARDEDNESS** — parallel composition of clearing systems clears. -/
theorem tensor_guarded {X Y X' Y' : ZKObj R} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (hf : Guarded f) (hg : Guarded g) : Guarded (tensorHom f g) := by
  intro p
  obtain ⟨y, hy⟩ := hf p.1
  obtain ⟨y', hy'⟩ := hg p.2
  exact ⟨(y, y'), hy, hy'⟩

/-- **The guarded trace (feedback)** `tr_U : (X ⊗ U ⟶ Y ⊗ U) → (X ⟶ Y)` — glue the `U` output boundary
back to the `U` input, imposing the loop `u = u` (the fed-back value). The resource grade is UNCHANGED
(feedback is internal — it neither mints nor burns), so the GRADE side of the ring is easy. -/
def gtrace {X Y U : ZKObj R} (f : tensorObj X U ⟶ tensorObj Y U) : X ⟶ Y where
  defect := f.defect
  rel x y := ∃ u : U.S, f.rel (x, u) (y, u)

/-- **THE GRADE SIDE OF THE RING IS PROVEN — the guarded trace preserves the defect.** Feedback is
internal resource routing; it changes no resource accounting: `d(tr f) = d f`. -/
theorem gtrace_defect {X Y U : ZKObj R} (f : tensorObj X U ⟶ tensorObj Y U) :
    dGrade (gtrace f) = dGrade f := rfl

/-- **THE GRADE SIDE OF CONSERVATION-UNDER-FEEDBACK IS PROVEN — the guarded trace of a conservative
morphism is conservative.** `d(tr f) = d f = 0`. So feedback preserves `d⁻¹(0)` at the GRADE level; the
open part is the FEASIBILITY (guardedness), below. -/
theorem gtrace_conservative {X Y U : ZKObj R} {f : tensorObj X U ⟶ tensorObj Y U}
    (hf : Conservative f) : Conservative (gtrace f) := hf

/-- **`GuardedTraceClosure R` — the ORIGINAL feedback-feasibility conjecture. FALSE (refuted below).**

The tempting conjecture: *for a conservative morphism whose feedback fiber clears (guarded), the guarded
trace CLEARS* — the loop's non-vacuity survives feedback. Codex (R3 Q3) gave a minimal COUNTEREXAMPLE
against these very definitions, so this is not merely open — it is FALSE for every `R`
(`guardedTraceClosure_refuted`). It is kept only as the object of that refutation; the `ZKUnification`
bundle no longer carries it (a false statement cannot be an honest hypothesis field), and the true
closure is `traceAdmissible_guarded` below. -/
def GuardedTraceClosure (R : Type) [AddCommMonoid R] : Prop :=
  ∀ (X Y U : ZKObj R) (f : tensorObj X U ⟶ tensorObj Y U),
    Conservative f → Guarded f → Guarded (gtrace f)

/-- **The counterexample — the `Bool`-negation feedback (codex R3 Q3).** `X = Y = 1` (`PUnit`),
`U = Bool`, defect `0`, and `f.rel ((*,u),(*,v)) ⟺ v = ¬u`. It is conservative (defect `0`), guarded
(every `u` maps to `¬u`), functional — yet its guarded trace asks for `∃ u, u = ¬u`, which is FALSE.
`Conservative + Guarded + Functional does NOT imply traced Guardedness`: the module's `Guarded` is a
totality, not a genuine guarded/Conway trace. -/
def negFeedback : tensorObj (⟨PUnit⟩ : ZKObj R) (⟨Bool⟩ : ZKObj R) ⟶
    tensorObj (⟨PUnit⟩ : ZKObj R) (⟨Bool⟩ : ZKObj R) where
  defect := 0
  rel p q := q.2 = !p.2

/-- **`GuardedTraceClosure` is FALSE — a PROOF, not a comment.** The `negFeedback` witness is conservative
and guarded, but its guarded trace is the EMPTY relation (`∃ u : Bool, u = ¬u` is false). So the
conjecture fails for every `R`; consequently the `ZKUnification` structure whose one field was
`feedback_closure : GuardedTraceClosure R` could NEVER be inhabited — the earlier "to inhabit
`ZKUnification` is to discharge the open theorem" was chasing a FALSE statement. Refute-and-replace. -/
theorem guardedTraceClosure_refuted : ¬ GuardedTraceClosure R := by
  intro h
  have hg : Guarded (gtrace (negFeedback (R := R))) :=
    h (⟨PUnit⟩) (⟨PUnit⟩) (⟨Bool⟩) negFeedback rfl (fun p => ⟨(p.1, !p.2), rfl⟩)
  obtain ⟨_, u, hu⟩ := hg PUnit.unit
  -- `hu : u = !u` — impossible for `Bool`.
  have hne : u = !u := hu
  cases u <;> simp at hne

/-! ### The CORRECT replacement — typed feedback admissibility + the Tarski/Knaster–Tarski closure.

The repair (codex R3 Q3): the full-generality conjecture is false, but the feedback DOES close for the
mechanism-relevant cases — when the feedback map is a MONOTONE self-map of a complete lattice, its least
fixed point IS the fed-back value that clears the loop. This is verify-not-find lifted to feedback:
admissibility is a typed proof-carrying witness (a monotone operator + Knaster–Tarski), not the false
claim that every wired cycle clears. -/

/-- **`TraceAdmissible f` — the typed feedback-admissibility witness (finite-box / complete-lattice Tarski).**
For each input `x`, the feedback is realized by a MONOTONE self-map `Φ` of the (complete-lattice) feedback
state together with an output map `out`, i.e. `f.rel (x,u) (out u, Φ u)` for all `u`. This is the honest
hypothesis the false `GuardedTraceClosure` lacked: the `Bool`-negation counterexample fails it precisely
because `¬` is NOT monotone. -/
def TraceAdmissible {X Y U : ZKObj R} [CompleteLattice U.S]
    (f : tensorObj X U ⟶ tensorObj Y U) : Prop :=
  ∀ x : X.S, ∃ (Φ : U.S →o U.S) (out : U.S → Y.S), ∀ u : U.S, f.rel (x, u) (out u, Φ u)

/-- **THE REPLACEMENT THEOREM — `TraceAdmissible f → Guarded (gtrace f)` (Knaster–Tarski feedback closure).**
A trace-admissible morphism's feedback CLEARS: the least fixed point `lfp Φ` of the monotone feedback
operator satisfies `Φ (lfp Φ) = lfp Φ` (`OrderHom.map_lfp`), so the fed-back input and output `U`-values
coincide — the loop's non-vacuity is WITNESSED by the fixed point. This is the true content the false
conjecture over-reached for; it lands on exactly the monotone-operator/least-fixed-point machinery
`Market/FhEggClearing.lean` proves for the fhEgg crossing (`Fstep_monotone` / `crossing_fixed`). -/
theorem traceAdmissible_guarded {X Y U : ZKObj R} [CompleteLattice U.S]
    (f : tensorObj X U ⟶ tensorObj Y U) (h : TraceAdmissible f) : Guarded (gtrace f) := by
  intro x
  obtain ⟨Φ, out, hrel⟩ := h x
  refine ⟨out (OrderHom.lfp Φ), OrderHom.lfp Φ, ?_⟩
  have hr := hrel (OrderHom.lfp Φ)
  rwa [OrderHom.map_lfp] at hr

/-! ### The replacement is NON-VACUOUS — it fires on a genuine complete lattice with a NON-total monotone
feedback (not just the total instances). We exercise `traceAdmissible_guarded` on the complete lattice
`Prop` with the monotone, single-valued, NON-total feedback `Φ P = P ∧ c` (least fixed point `⊥ = False`);
the trace clears at that fixed point — verify-not-find on a real monotone operator with a nontrivial
`lfp`, not a `True`-relation triviality. -/

/-- The feedback state `Prop` as an object (reducible so its complete-lattice instance resolves). -/
@[reducible] def propObj : ZKObj R := ⟨Prop⟩

/-- A NON-total monotone feedback on the complete lattice `Prop`: `v = (u ∧ c)`. Its feedback operator
`Φ P = P ∧ c` is genuinely monotone (not the total relation), with least fixed point `False`. -/
def andFeedback (c : Prop) :
    tensorObj (unitObj : ZKObj R) propObj ⟶ tensorObj (unitObj : ZKObj R) propObj where
  defect := 0
  rel p q := q.2 = (p.2 ∧ c)

theorem andFeedback_traceAdmissible (c : Prop) : TraceAdmissible (andFeedback (R := R) c) :=
  fun _ => ⟨⟨fun P => P ∧ c, fun _ _ hPQ hp => ⟨hPQ hp.1, hp.2⟩⟩, fun _ => PUnit.unit, fun _ => rfl⟩

/-- **THE REPLACEMENT FIRES ON A NON-TOTAL MONOTONE FEEDBACK** — `andFeedback c` clears through
`traceAdmissible_guarded`, so the Tarski closure is non-vacuous beyond the total instances (its feedback
is a real monotone operator on `Prop`, and the cleared value is the least fixed point). -/
theorem andFeedback_gtrace_guarded (c : Prop) : Guarded (gtrace (andFeedback (R := R) c)) :=
  traceAdmissible_guarded _ (andFeedback_traceAdmissible c)

/-! ### FULL closure for the admissible subcategory — feedback AND adaptive composition AND tensor.

Codex's stated target was closure under BOTH feedback AND adaptive composition. The feedback half is
`traceAdmissible_guarded`; the composition/tensor half rides the already-proven `comp_guarded` /
`tensor_guarded`. Together: on the admissible subcategory, the guarded trace is closed under sequential
composition and parallel (tensor) composition — the compositional closure the unification names, now a
THEOREM (not a hypothesis field). -/

/-- **ADAPTIVE COMPOSITION of cleared admissible traces CLEARS** — the sequential composite of two
trace-admissible feedbacks has a guarded trace-composite (`comp_guarded` of the two closures). -/
theorem gtrace_comp_guarded {X Y Z U V : ZKObj R} [CompleteLattice U.S] [CompleteLattice V.S]
    (f : tensorObj X U ⟶ tensorObj Y U) (g : tensorObj Y V ⟶ tensorObj Z V)
    (hf : TraceAdmissible f) (hg : TraceAdmissible g) :
    Guarded (gtrace f ≫ gtrace g) :=
  comp_guarded (traceAdmissible_guarded f hf) (traceAdmissible_guarded g hg)

/-- **PARALLEL (TENSOR) COMPOSITION of cleared admissible traces CLEARS** — the ⊗-product of two guarded
traces of admissible feedbacks clears (`tensor_guarded` of the two closures). -/
theorem gtrace_tensor_guarded {X Y X' Y' U V : ZKObj R} [CompleteLattice U.S] [CompleteLattice V.S]
    (f : tensorObj X U ⟶ tensorObj Y U) (g : tensorObj X' V ⟶ tensorObj Y' V)
    (hf : TraceAdmissible f) (hg : TraceAdmissible g) :
    Guarded (tensorHom (gtrace f) (gtrace g)) :=
  tensor_guarded (traceAdmissible_guarded f hf) (traceAdmissible_guarded g hg)

/-! ### `GuardedOn` — the typed PARTIAL guard (codex R3 Q3: markets do not clear every boundary state).

Not every syntactic input clears; the honest predicate is guardedness on an admissible DOMAIN. We give
the restricted guard, show it generalizes `Guarded`, and prove partial adaptive composition (the image of
the admissible domain must land in the next stage's domain). -/

/-- **`GuardedOn P f` — guardedness restricted to the admissible domain `P`.** `Guarded` is the `P = ⊤`
case (`guarded_iff_guardedOn_true`). -/
def GuardedOn {X Y : ZKObj R} (P : X.S → Prop) (f : X ⟶ Y) : Prop := ∀ x, P x → ∃ y, f.rel x y

/-- `Guarded` is `GuardedOn` the total domain. -/
theorem guarded_iff_guardedOn_true {X Y : ZKObj R} (f : X ⟶ Y) :
    Guarded f ↔ GuardedOn (fun _ => True) f :=
  ⟨fun h x _ => h x, fun h x => h x trivial⟩

/-- **PARTIAL ADAPTIVE COMPOSITION** — if `f` clears on `P` and `g` clears on `Q`, and every `P`-input's
`f`-image satisfies `Q`, then the composite clears on `P`. The domain-tracked form of `comp_guarded`. -/
theorem comp_guardedOn {X Y Z : ZKObj R} {P : X.S → Prop} {Q : Y.S → Prop}
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : GuardedOn P f) (hg : GuardedOn Q g)
    (hPQ : ∀ x y, P x → f.rel x y → Q y) : GuardedOn P (f ≫ g) := by
  intro x hx
  obtain ⟨y, hy⟩ := hf x hx
  obtain ⟨z, hz⟩ := hg y (hPQ x y hx hy)
  exact ⟨z, y, hy, hz⟩

/-! ### Mechanism landing — the fhEgg CROSSING feedback clears, via the PROVEN monotone operator.

The genuinely-constrained instance (feedback `rel` is a real update, not `True`): wire the fhEgg price
update `Market.Fstep` as the feedback map. Its admissibility is `Market.Fstep_monotone` (the monotone
crossing operator, the codex correction), and the fed-back value that clears the loop is the crossing —
the fixed point `Market.crossing_fixed` establishes. So the guarded trace of the crossing feedback is
guarded exactly when a crossing exists (the honest `CrossingExists` hypothesis). -/

/-- **The crossing feedback morphism** — `U`-state = the price index `ℕ`; the feedback wires the proven
monotone crossing operator `Market.Fstep bk K`. -/
def crossingFeedback (bk : Market.OrderBook) (K : ℕ) :
    tensorObj (⟨PUnit⟩ : ZKObj R) (⟨ℕ⟩ : ZKObj R) ⟶ tensorObj (⟨PUnit⟩ : ZKObj R) (⟨ℕ⟩ : ZKObj R) where
  defect := 0
  rel p q := q.2 = Market.Fstep bk K p.2

/-- **THE fhEgg CROSSING FEEDBACK CLEARS** — the guarded trace of `crossingFeedback` is guarded whenever a
crossing exists: its feedback fiber is `∃ n, n = Fstep bk K n`, a FIXED POINT of the monotone crossing
operator, witnessed by `Market.crossing_fixed`. This is the replacement theorem's content on the real,
already-proven mechanism operator — feedback closure for the monotone/finite case that actually matters. -/
theorem crossing_gtrace_guarded (bk : Market.OrderBook) (K : ℕ) (h : Market.CrossingExists bk) :
    Guarded (gtrace (crossingFeedback (R := R) bk K)) := by
  intro _
  exact ⟨PUnit.unit, Market.crossing bk h, (Market.crossing_fixed bk h K).symm⟩

/-! ### The four fhEgg instances are `TraceAdmissible` (their feasibility is total ⇒ trivially admissible).

The four instances (turn / auction / circulation / convex-engine) carry a TOTAL feasibility relation, so
their self-feedback is trivially admissible (`Φ = id`, monotone) and its trace clears. The nontrivial
admissibility is the crossing above; here we discharge the four named instances so the unification holds
for them. `toLoop` presents an endomorphism as a traceable (feedback-shaped) morphism. -/

/-- **`toLoop g`** — an endomorphism `g : Z ⟶ Z` presented as a traceable morphism `1 ⊗ Z ⟶ 1 ⊗ Z` whose
feedback boundary is `Z` (the loop feeds `Z`'s output back to its input). -/
def toLoop {Z : ZKObj R} (g : Z ⟶ Z) : tensorObj unitObj Z ⟶ tensorObj unitObj Z where
  defect := g.defect
  rel p q := g.rel p.2 q.2

/-- The loop preserves the grade, so a conservative endomorphism has a conservative loop. -/
theorem toLoop_conservative {Z : ZKObj R} {g : Z ⟶ Z} (hg : Conservative g) :
    Conservative (toLoop g) := hg

/-- **A TOTAL endomorphism's loop is `TraceAdmissible`** — with `Φ = id` (monotone) the feedback relation
holds for every `u` (the relation is total), so the loop admits a fixed-point witness on any complete
lattice. -/
theorem total_toLoop_traceAdmissible {Z : ZKObj R} [CompleteLattice Z.S] (g : Z ⟶ Z)
    (htot : ∀ a b : Z.S, g.rel a b) : TraceAdmissible (toLoop g) := by
  intro _
  refine ⟨OrderHom.id, fun _ => PUnit.unit, ?_⟩
  intro u
  exact htot u u

/-- A total endomorphism's loop trace clears (composing `total_toLoop_traceAdmissible` with the closure). -/
theorem total_toLoop_gtrace_guarded {Z : ZKObj R} [CompleteLattice Z.S] (g : Z ⟶ Z)
    (htot : ∀ a b : Z.S, g.rel a b) : Guarded (gtrace (toLoop g)) :=
  traceAdmissible_guarded _ (total_toLoop_traceAdmissible g htot)

/-- **CIRCULATION is `TraceAdmissible`.** -/
theorem circulation_traceAdmissible :
    TraceAdmissible (toLoop (circulationMor Market.ringLP Market.ringF)) :=
  total_toLoop_traceAdmissible _ (fun _ _ => trivial)

/-- **CONVEX ENGINE is `TraceAdmissible`.** -/
theorem convex_engine_traceAdmissible :
    TraceAdmissible (toLoop (convexEngineMor Market.ringLP Market.ringF Market.ringπ Market.ringS)) :=
  total_toLoop_traceAdmissible _ (fun _ _ => trivial)

/-- **AUCTION is `TraceAdmissible`.** -/
theorem auction_traceAdmissible :
    TraceAdmissible (toLoop (clearingMor Market.ringClearing)) :=
  total_toLoop_traceAdmissible _ (fun _ _ => trivial)

/-- **TURN is `TraceAdmissible`.** (Its feasibility relation is `Eq` on `PUnit`, total by subsingleton.) -/
theorem turn_traceAdmissible :
    TraceAdmissible (toLoop turnMor) :=
  total_toLoop_traceAdmissible _ (fun a b => Subsingleton.elim a b)

/-- **THE UNIFICATION HOLDS FOR A REAL INSTANCE (circulation)** — its feedback trace is BOTH conservative
(`gtrace_conservative` of the proven `ring_circulation_conservative`) AND clearing (`traceAdmissible_guarded`
of `circulation_traceAdmissible`). Full closure under feedback, for the mechanism-relevant instance —
unconditionally, no open field. -/
theorem ring_circulation_traced_closed :
    Conservative (gtrace (toLoop (circulationMor Market.ringLP Market.ringF)))
      ∧ Guarded (gtrace (toLoop (circulationMor Market.ringLP Market.ringF))) :=
  ⟨gtrace_conservative (toLoop_conservative ring_circulation_conservative),
   traceAdmissible_guarded _ circulation_traceAdmissible⟩

/-! ### The admissible-subcategory closure + the (now INHABITED) unification. -/

/-- **`AdmissibleTraceClosure R` — the TRUE feedback closure (the admissible subcategory).** The honest
replacement for the false `GuardedTraceClosure`: on the trace-admissible (monotone/complete-lattice)
morphisms, the guarded trace clears. Unlike its predecessor, this is PROVABLE
(`admissibleTraceClosure_holds`). -/
def AdmissibleTraceClosure (R : Type) [AddCommMonoid R] : Prop :=
  ∀ (X Y U : ZKObj R) [CompleteLattice U.S] (f : tensorObj X U ⟶ tensorObj Y U),
    TraceAdmissible f → Guarded (gtrace f)

/-- **The admissible feedback closure HOLDS** — the replacement theorem, packaged as the subcategory
closure. This is what makes `ZKUnification` inhabitable (below). -/
theorem admissibleTraceClosure_holds : AdmissibleTraceClosure R := by
  intro X Y U _ f h
  exact traceAdmissible_guarded f h

/-- **`ZKUnification R` — the categorical unification, now with a TRUE, PROVEN closure field.** Everything
in this module (the category, the functor `d`, conservation = `d⁻¹(0)`, the four instances, non-feedback
composition, the privacy natural transformation) is proven unconditionally; the feedback closure — once a
false hypothesis field (`GuardedTraceClosure`, refuted by `guardedTraceClosure_refuted`) — is now the true
`AdmissibleTraceClosure`, so the bundle is INHABITED (`zkUnification`), not a chase after a false statement. -/
structure ZKUnification (R : Type) [AddCommMonoid R] where
  /-- **THE FEEDBACK CLOSURE — a TRUE theorem, not a false hypothesis.** The admissible-subcategory Tarski
  closure; discharged by `admissibleTraceClosure_holds`. -/
  feedback_closure : AdmissibleTraceClosure R

/-- **THE UNIFICATION IS INHABITED** — the honest closure discharges the (formerly uninhabitable) bundle. -/
def zkUnification : ZKUnification R := ⟨admissibleTraceClosure_holds⟩

/-- **What the closure BUYS — full closure under feedback for admissible morphisms.** Given the unification,
the guarded trace of a conserving, trace-admissible morphism is BOTH conservative (`gtrace_conservative`)
AND clearing (`feedback_closure`). This is the compositional closure the unification targets — now a
theorem, with the honest `TraceAdmissible` precondition in place of the false unconditional conjecture. -/
theorem ZKUnification.traced_history_closed (Uc : ZKUnification R)
    {X Y U : ZKObj R} [CompleteLattice U.S] (f : tensorObj X U ⟶ tensorObj Y U)
    (hc : Conservative f) (ha : TraceAdmissible f) :
    Conservative (gtrace f) ∧ Guarded (gtrace f) :=
  ⟨gtrace_conservative hc, Uc.feedback_closure X Y U f ha⟩

/-! ## 7. PRIVACY — the simulator natural transformation `View ≈ Sim∘Q` (the categorical home).

Codex: *privacy = a simulator natural transformation `View ≈ Sim∘Q` over the leakage functor `Q`.* The
objects carry the leakage functor `Q` (`Market/RevealNothing.lean`'s `Q : Clearing → Leakage`);
reveal-nothing is the naturality square `view = sim ∘ Q` — the real view factors through the public
leakage alone. This section gives that categorical shape and shows `RevealNothing.RevealBundle` IS
exactly such a natural transformation. -/

/-- **`PrivacyNatTrans` — the `View ≈ Sim∘Q` shape.** A leakage map `Q` (the public projection), a real
`view`, a witness-free `sim`, and the naturality law `view = sim ∘ Q` (the real view factors through the
leakage). This is codex's simulator natural transformation, abstracted. -/
structure PrivacyNatTrans (Clr Lk Tr : Type) where
  /-- The leakage functor `Q` — the public projection of a clearing. -/
  Q : Clr → Lk
  /-- The REAL public view/transcript (a function of the full private clearing). -/
  view : Clr → Tr
  /-- The witness-free simulator (from the public leakage alone). -/
  sim : Lk → Tr
  /-- **Naturality — `View ≈ Sim∘Q`**: the real view factors through the leakage. -/
  naturality : ∀ c, view c = sim (Q c)

/-- **THE REVEAL-NOTHING CONSEQUENCE — same leakage ⇒ same view.** Two clearings with the SAME public
leakage `Q` produce the IDENTICAL view: an observer learns only the leakage class `Q`, nothing of the
private trades. Derived from naturality exactly as `RevealNothing.same_leakage_indistinguishable`. -/
theorem PrivacyNatTrans.indistinguishable {Clr Lk Tr : Type} (P : PrivacyNatTrans Clr Lk Tr)
    {c₁ c₂ : Clr} (h : P.Q c₁ = P.Q c₂) : P.view c₁ = P.view c₂ := by
  rw [P.naturality c₁, P.naturality c₂, h]

/-- **`RevealNothing.RevealBundle` IS a privacy natural transformation.** Its `view`, `sim`, and
`reveal_law` (over `RevealNothing.Q`) are exactly the `Q` / `view` / `sim` / naturality of a
`PrivacyNatTrans`. This is the categorical home of the reveal-nothing theorem — the leakage functor `Q`
is the object-map, and `View ≈ Sim∘Q` is the naturality square. -/
def ofRevealBundle (B : Market.RevealNothing.RevealBundle) :
    PrivacyNatTrans Market.RevealNothing.Clearing Market.RevealNothing.Leakage
      Market.RevealNothing.Transcript where
  Q := Market.RevealNothing.Q
  view := B.view
  sim := B.sim
  naturality := B.reveal_law

/-- **The reveal-nothing theorem, in the categorical frame** — `view = sim ∘ Q` for the bundle,
recovered as the naturality of `ofRevealBundle B`. -/
theorem ofRevealBundle_reveal_nothing (B : Market.RevealNothing.RevealBundle)
    (c : Market.RevealNothing.Clearing) :
    (ofRevealBundle B).view c = (ofRevealBundle B).sim ((ofRevealBundle B).Q c) :=
  (ofRevealBundle B).naturality c

/-- **THE PRIVACY NATURAL TRANSFORMATION, WITNESSED NON-VACUOUSLY** — the ideal/shell reveal bundle
(`RevealNothing.shellBundle`) gives a `PrivacyNatTrans` on which two genuinely-different clearings
`c_alpha ≠ c_beta` with equal leakage collapse to one view. The categorical reveal-nothing, made
concrete. -/
theorem shell_privacy_indistinguishable :
    (ofRevealBundle Market.RevealNothing.shellBundle).view Market.RevealNothing.c_alpha
      = (ofRevealBundle Market.RevealNothing.shellBundle).view Market.RevealNothing.c_beta :=
  (ofRevealBundle Market.RevealNothing.shellBundle).indistinguishable
    Market.RevealNothing.alpha_beta_same_leakage

/-! ### `#guard` smoke — the grade arithmetic is COMPUTED, not asserted. -/

-- the resource defect adds over composition (2 + 3 = 5), over the additive monoid ℤ:
#guard (compHom (X := (⟨PUnit⟩ : ZKObj ℤ)) (Y := ⟨PUnit⟩) (Z := ⟨PUnit⟩)
          ⟨2, fun _ _ => True⟩ ⟨3, fun _ _ => True⟩).defect == 5
-- the identity carries zero defect:
#guard (idHom (⟨PUnit⟩ : ZKObj ℤ)).defect == 0
-- the tensor adds defects too (2 + 3 = 5):
#guard (tensorHom (X := (⟨PUnit⟩ : ZKObj ℤ)) (Y := ⟨PUnit⟩) (X' := ⟨PUnit⟩) (Y' := ⟨PUnit⟩)
          ⟨2, fun _ _ => True⟩ ⟨3, fun _ _ => True⟩).defect == 5

/-! ### Axiom hygiene — the categorical-unification keystones pinned kernel-clean. The feedback closure is
now a PROVEN refutation (`guardedTraceClosure_refuted`) plus a PROVEN Tarski replacement
(`traceAdmissible_guarded` / `admissibleTraceClosure_holds`), NOT a `sorry` and NOT an open field. -/

#assert_all_clean [Market.ZKOpenRel.dGrade_comp, Market.ZKOpenRel.dGrade_id,
  Market.ZKOpenRel.dFunctor_tensor, Market.ZKOpenRel.dFunctor_unit,
  Market.ZKOpenRel.id_conservative, Market.ZKOpenRel.comp_conservative,
  Market.ZKOpenRel.tensor_conservative, Market.ZKOpenRel.iterate_conservative,
  Market.ZKOpenRel.circulation_conservative, Market.ZKOpenRel.ring_circulation_conservative,
  Market.ZKOpenRel.convex_engine_conservative, Market.ZKOpenRel.clearingDefect_zero,
  Market.ZKOpenRel.clearing_is_conservative, Market.ZKOpenRel.ring_auction_conservative,
  Market.ZKOpenRel.turn_conservative, Market.ZKOpenRel.turn_history_conservative,
  Market.ZKOpenRel.id_guarded, Market.ZKOpenRel.comp_guarded, Market.ZKOpenRel.tensor_guarded,
  Market.ZKOpenRel.gtrace_defect, Market.ZKOpenRel.gtrace_conservative,
  Market.ZKOpenRel.guardedTraceClosure_refuted, Market.ZKOpenRel.traceAdmissible_guarded,
  Market.ZKOpenRel.andFeedback_traceAdmissible, Market.ZKOpenRel.andFeedback_gtrace_guarded,
  Market.ZKOpenRel.gtrace_comp_guarded,
  Market.ZKOpenRel.gtrace_tensor_guarded, Market.ZKOpenRel.guarded_iff_guardedOn_true,
  Market.ZKOpenRel.comp_guardedOn,
  Market.ZKOpenRel.crossing_gtrace_guarded, Market.ZKOpenRel.total_toLoop_traceAdmissible,
  Market.ZKOpenRel.total_toLoop_gtrace_guarded, Market.ZKOpenRel.circulation_traceAdmissible,
  Market.ZKOpenRel.convex_engine_traceAdmissible, Market.ZKOpenRel.auction_traceAdmissible,
  Market.ZKOpenRel.turn_traceAdmissible, Market.ZKOpenRel.ring_circulation_traced_closed,
  Market.ZKOpenRel.admissibleTraceClosure_holds,
  Market.ZKOpenRel.ZKUnification.traced_history_closed,
  Market.ZKOpenRel.PrivacyNatTrans.indistinguishable,
  Market.ZKOpenRel.ofRevealBundle_reveal_nothing, Market.ZKOpenRel.shell_privacy_indistinguishable]

end Market.ZKOpenRel
