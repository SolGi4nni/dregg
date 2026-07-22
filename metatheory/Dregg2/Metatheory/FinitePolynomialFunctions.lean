/-
# Finite polynomial functions: interpolation and the table exponential

Over a finite field, every function `F^σ → F` is represented extensionally by a
multivariate polynomial.  This is the finite, exact fragment in which polynomial
functions form a cartesian closed category: an exponential from coordinates `σ`
to coordinates `τ` is the table object with coordinates `(σ → F) × τ`.

This module deliberately proves only the algebraic core.  It does not identify
formal polynomials intensionally: distinct polynomials may induce the same finite
function (for example modulo `X_i^q - X_i`).
-/
import Dregg2.Tactics
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.FieldTheory.Finite.Basic

namespace Dregg2.Metatheory.FinitePolynomialFunctions

open scoped BigOperators

noncomputable section

variable {F : Type*} [Field F] [Fintype F]
variable {σ τ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype ρ]

/-- The Kronecker indicator of the point `a : F^σ`. -/
def pointIndicator (a : σ → F) : MvPolynomial σ F :=
  ∏ i : σ, (1 - (MvPolynomial.X i - MvPolynomial.C (a i)) ^ (Fintype.card F - 1))

/-- The point indicator evaluates to one at its selected point. -/
@[simp] theorem eval_pointIndicator_self (a : σ → F) :
    MvPolynomial.eval a (pointIndicator a) = 1 := by
  classical
  have hq : Fintype.card F - 1 ≠ 0 := Nat.sub_ne_zero_of_lt Fintype.one_lt_card
  simp [pointIndicator, hq]

/-- The point indicator evaluates to zero away from its selected point. -/
theorem eval_pointIndicator_of_ne (a x : σ → F) (hxa : x ≠ a) :
    MvPolynomial.eval x (pointIndicator a) = 0 := by
  classical
  have hcoord : ∃ i : σ, x i ≠ a i := by
    by_contra h
    push Not at h
    exact hxa (funext h)
  obtain ⟨i, hi⟩ := hcoord
  rw [pointIndicator, MvPolynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have hdiff : x i - a i ≠ 0 := sub_ne_zero.mpr hi
  simp only [map_sub, map_one, map_pow, MvPolynomial.eval_X, MvPolynomial.eval_C]
  rw [FiniteField.pow_card_sub_one_eq_one _ hdiff, sub_self]

/-- The finite set of all field-valued points, with the noncomputable `Fintype`
choice kept out of the public theorem assumptions. -/
def allPoints (σ F : Type*) [Finite σ] [Finite F] : Finset (σ → F) := by
  letI := Fintype.ofFinite (σ → F)
  exact Finset.univ

@[simp] theorem mem_allPoints (x : σ → F) : x ∈ allPoints σ F := by
  classical
  simp [allPoints]

/-- The explicit multivariate interpolation polynomial of an arbitrary finite table. -/
def interpolate (f : (σ → F) → F) : MvPolynomial σ F :=
  ∑ a ∈ allPoints σ F, MvPolynomial.C (f a) * pointIndicator a

/-- Exact interpolation: the constructed polynomial evaluates to the original table. -/
@[simp] theorem eval_interpolate (f : (σ → F) → F) (x : σ → F) :
    MvPolynomial.eval x (interpolate f) = f x := by
  classical
  rw [interpolate, MvPolynomial.eval_sum]
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C]
  rw [Finset.sum_eq_single x]
  · simp
  · intro y hy hyx
    rw [eval_pointIndicator_of_ne y x (Ne.symm hyx), mul_zero]
  · simp

/-- Evaluation onto finite tables is surjective. -/
theorem polynomial_representation_surjective :
    Function.Surjective
      (fun p : MvPolynomial σ F => fun x : σ → F => MvPolynomial.eval x p) := by
  intro f
  exact ⟨interpolate f, funext (eval_interpolate f)⟩

/-- Coordinatewise interpolation represents every function between finite field powers. -/
def interpolateVector (f : (σ → F) → (τ → F)) : τ → MvPolynomial σ F :=
  fun j => interpolate (fun x => f x j)

/-- Coordinatewise interpolation has exactly the requested vector-valued denotation. -/
@[simp] theorem eval_interpolateVector
    (f : (σ → F) → (τ → F)) (x : σ → F) (j : τ) :
    MvPolynomial.eval x (interpolateVector f j) = f x j := by
  simp [interpolateVector]

/-- Evaluation from vectors of polynomials onto all functions between finite powers is surjective. -/
theorem vector_polynomial_representation_surjective :
    Function.Surjective
      (fun ps : τ → MvPolynomial σ F =>
        fun x : σ → F => fun j : τ => MvPolynomial.eval x (ps j)) := by
  intro f
  refine ⟨interpolateVector f, ?_⟩
  funext x j
  exact eval_interpolateVector f x j

/-- Coordinate indices for the table exponential `F^σ ⇒ F^τ`.

A point of `F^(ExpCoord σ τ F)` is definitionally a table
`(σ → F) → (τ → F)`, up to reassociation of arguments. -/
abbrev ExpCoord (σ τ F : Type*) := (σ → F) × τ

/-- Evaluate a table point at an input point. -/
def tableEval (table : ExpCoord σ τ F → F) (x : σ → F) : τ → F :=
  fun j => table (x, j)

/-- Curry an arbitrary set-function on finite field powers into its table point. -/
def tableCurry (f : (ρ → F) × (σ → F) → (τ → F)) (z : ρ → F) :
    ExpCoord σ τ F → F :=
  fun xj => f (z, xj.1) xj.2

/-- β for the table exponential. -/
@[simp] theorem table_beta
    (f : (ρ → F) × (σ → F) → (τ → F)) (z : ρ → F) (x : σ → F) :
    tableEval (tableCurry f z) x = f (z, x) := by
  funext j
  rfl

/-- Uncurry a table-valued function by applying its table component. -/
def tableUncurry (g : (ρ → F) → (ExpCoord σ τ F → F)) :
    (ρ → F) × (σ → F) → (τ → F) :=
  fun zx => tableEval (g zx.1) zx.2

/-- η for the table exponential. -/
@[simp] theorem table_eta
    (g : (ρ → F) → (ExpCoord σ τ F → F)) (z : ρ → F) :
    tableCurry (tableUncurry g) z = g z := by
  funext xj
  rfl

/-- A product point `F^α × F^β` packed as a point of `F^(α ⊕ β)`. -/
def pack {α β : Type*} (x : α → F) (y : β → F) : α ⊕ β → F :=
  Sum.elim x y

/-- The scalar coordinate of the exponential evaluation morphism as a finite table. -/
def tableEvalCoordinate (j : τ)
    (z : ExpCoord σ τ F ⊕ σ → F) : F :=
  let parts := Equiv.sumArrowEquivProdArrow (ExpCoord σ τ F) σ F z
  tableEval parts.1 parts.2 j

/-- The exponential evaluation map itself is polynomial representable. -/
def tableEvalPolynomial (j : τ) :
    MvPolynomial (ExpCoord σ τ F ⊕ σ) F := by
  letI := Fintype.ofFinite (ExpCoord σ τ F ⊕ σ)
  exact interpolate (tableEvalCoordinate j)

/-- The polynomial evaluator agrees exactly with table lookup. -/
@[simp] theorem eval_tableEvalPolynomial (j : τ)
    (table : ExpCoord σ τ F → F) (x : σ → F) :
    MvPolynomial.eval (pack table x) (tableEvalPolynomial j) = tableEval table x j := by
  letI := Fintype.ofFinite (ExpCoord σ τ F ⊕ σ)
  simp only [tableEvalPolynomial, eval_interpolate, tableEvalCoordinate, tableEval]
  apply congrArg (fun y : σ → F => table (y, j))
  funext i
  exact Equiv.sumArrowEquivProdArrow_apply_snd (pack table x) i

#assert_all_clean [eval_pointIndicator_self, eval_pointIndicator_of_ne, eval_interpolate,
  polynomial_representation_surjective, eval_interpolateVector,
  vector_polynomial_representation_surjective, table_beta, table_eta,
  eval_tableEvalPolynomial]

end

end Dregg2.Metatheory.FinitePolynomialFunctions

namespace Dregg2.Metatheory.FinitePolynomialFunctions.FiniteHOL

/-!
## A finite extensional higher-order calculus

The table exponential above is not merely a representation lemma for untyped
functions.  This section uses it as the arrow object of a small, intrinsically
typed simply-typed lambda calculus.  Every type denotes a finite field power:

* `unit` has no coordinates;
* `scalar` has one coordinate;
* a product has the disjoint union of its coordinates;
* an arrow has one coordinate for every input point and output coordinate.

Thus an arrow value is *definitionally* its finite extensional table.  Lambda
abstraction fills that table and application performs table lookup.  The
typing indices rule out ill-typed terms before denotation, while the equations
below prove the expected beta laws and connect application to the polynomial
evaluator proved in the first part of this file.
-/

noncomputable section

/-- Object types of the finite extensional calculus. -/
inductive Ty where
  | unit
  | scalar
  | prod (left right : Ty)
  | arr (domain codomain : Ty)
  deriving DecidableEq, Repr

/-- Coordinates of the finite field power interpreting a type. -/
def Coord (F : Type) : Ty → Type
  | .unit => Empty
  | .scalar => PUnit
  | .prod A B => Coord F A ⊕ Coord F B
  | .arr A B => ExpCoord (Coord F A) (Coord F B) F

/-- The extensional value of a type: one field element per coordinate. -/
abbrev Val (F : Type) (A : Ty) := Coord F A → F

variable {F : Type} [Field F] [Fintype F]

/-- All coordinate objects are finite. -/
instance coordFinite : (A : Ty) → Finite (Coord F A)
  | .unit => inferInstanceAs (Finite Empty)
  | .scalar => inferInstanceAs (Finite PUnit)
  | .prod A B => by
      letI := coordFinite A
      letI := coordFinite B
      exact inferInstanceAs (Finite (Coord F A ⊕ Coord F B))
  | .arr A B => by
      letI := coordFinite A
      letI := coordFinite B
      exact inferInstanceAs (Finite ((Coord F A → F) × Coord F B))

/-- A chosen enumeration of the coordinates, used only by interpolation. -/
noncomputable instance coordFintype (A : Ty) : Fintype (Coord F A) :=
  Fintype.ofFinite (Coord F A)

/-- Extensional values are finite as well, including higher-order tables. -/
instance valFinite (A : Ty) : Finite (Val F A) := inferInstance

/-- The arrow interpretation is exactly the table exponential constructed above. -/
theorem arrow_is_table_exponential (A B : Ty) :
    Val F (.arr A B) = (ExpCoord (Coord F A) (Coord F B) F → F) := by
  rfl

/-- Well-typed de Bruijn variables. -/
inductive Var : List Ty → Ty → Type where
  | zero : Var (A :: Γ) A
  | succ : Var Γ A → Var (B :: Γ) A

/-- Intrinsically typed terms. -/
inductive Tm (F : Type) : List Ty → Ty → Type where
  | var : Var Γ A → Tm F Γ A
  | unit : Tm F Γ .unit
  | scalar : F → Tm F Γ .scalar
  | pair : Tm F Γ A → Tm F Γ B → Tm F Γ (.prod A B)
  | fst : Tm F Γ (.prod A B) → Tm F Γ A
  | snd : Tm F Γ (.prod A B) → Tm F Γ B
  | lam : Tm F (A :: Γ) B → Tm F Γ (.arr A B)
  | app : Tm F Γ (.arr A B) → Tm F Γ A → Tm F Γ B

/-- Semantic environments, in the same order as a de Bruijn context. -/
def Env (F : Type) : List Ty → Type
  | [] => PUnit
  | A :: Γ => Val F A × Env F Γ

/-- Lookup is total because the variable carries its typing derivation. -/
def lookup : Var Γ A → Env F Γ → Val F A
  | .zero, env => env.1
  | .succ x, env => lookup x env.2

/-- Extensional denotation of an intrinsically typed term.

In the `lam` branch, `xj.1` is the input value and `xj.2` is the requested
output coordinate.  In the `app` branch, the same pair performs table lookup.
-/
def denote : Tm F Γ A → Env F Γ → Val F A
  | .var x, env => lookup x env
  | .unit, _ => fun i => nomatch i
  | .scalar c, _ => fun _ => c
  | .pair left right, env => fun
      | Sum.inl i => denote left env i
      | Sum.inr j => denote right env j
  | .fst pair, env => fun i => denote pair env (Sum.inl i)
  | .snd pair, env => fun j => denote pair env (Sum.inr j)
  | .lam body, env => fun xj => denote body (xj.1, env) xj.2
  | .app fn arg, env => fun j => denote fn env (denote arg env, j)

/-! ### Definitional computation laws. -/

@[simp] theorem denote_var_zero (env : Env F (A :: Γ)) :
    denote (.var (.zero : Var (A :: Γ) A)) env = env.1 := by
  rfl

@[simp] theorem denote_var_succ (x : Var Γ A) (env : Env F (B :: Γ)) :
    denote (.var (.succ x)) env = denote (.var x) env.2 := by
  rfl

/-- Product beta, first projection. -/
@[simp] theorem denote_fst_pair (left : Tm F Γ A) (right : Tm F Γ B)
    (env : Env F Γ) :
    denote (.fst (.pair left right)) env = denote left env := by
  rfl

/-- Product beta, second projection. -/
@[simp] theorem denote_snd_pair (left : Tm F Γ A) (right : Tm F Γ B)
    (env : Env F Γ) :
    denote (.snd (.pair left right)) env = denote right env := by
  rfl

/-- Function beta: applying a lambda extends its environment by the argument value. -/
@[simp] theorem denote_app_lam (body : Tm F (A :: Γ) B) (arg : Tm F Γ A)
    (env : Env F Γ) :
    denote (.app (.lam body) arg) env = denote body (denote arg env, env) := by
  rfl

/-- Extensional product eta. -/
theorem product_eta (value : Val F (.prod A B)) :
    (fun ij => match ij with
      | Sum.inl i => value (Sum.inl i)
      | Sum.inr j => value (Sum.inr j)) = value := by
  funext ij
  cases ij <;> rfl

/-- Extensional function eta for the table arrow. -/
theorem arrow_eta (table : Val F (.arr A B)) :
    (fun xj => tableEval table xj.1 xj.2) = table := by
  funext xj
  rfl

/-- Term application is precisely evaluation in the table exponential. -/
theorem denote_app_is_tableEval (fn : Tm F Γ (.arr A B)) (arg : Tm F Γ A)
    (env : Env F Γ) :
    denote (.app fn arg) env = tableEval (denote fn env) (denote arg env) := by
  rfl

/-! ### Finite higher-order formulas. -/

/-- A small extensional HOL over the typed term language.  Quantifiers range over
the entire finite interpretation of their type, including function tables. -/
inductive Formula (F : Type) : List Ty → Type where
  | top : Formula F Γ
  | bottom : Formula F Γ
  | equal : Tm F Γ A → Tm F Γ A → Formula F Γ
  | and : Formula F Γ → Formula F Γ → Formula F Γ
  | or : Formula F Γ → Formula F Γ → Formula F Γ
  | imp : Formula F Γ → Formula F Γ → Formula F Γ
  | not : Formula F Γ → Formula F Γ
  | forall_ (A : Ty) : Formula F (A :: Γ) → Formula F Γ
  | exists_ (A : Ty) : Formula F (A :: Γ) → Formula F Γ

/-- Truth semantics for finite HOL.  Equality is extensional equality of field-power
values, so equality at arrow type compares the complete function tables. -/
def Satisfies : Formula F Γ → Env F Γ → Prop
  | .top, _ => True
  | .bottom, _ => False
  | .equal left right, env => denote left env = denote right env
  | .and p q, env => Satisfies p env ∧ Satisfies q env
  | .or p q, env => Satisfies p env ∨ Satisfies q env
  | .imp p q, env => Satisfies p env → Satisfies q env
  | .not p, env => ¬ Satisfies p env
  | .forall_ A p, env => ∀ x : Val F A, Satisfies p (x, env)
  | .exists_ A p, env => ∃ x : Val F A, Satisfies p (x, env)

/-- Quantification at arrow type is genuinely quantification over all finite tables. -/
theorem satisfies_forall_arrow (p : Formula F (.arr A B :: Γ)) (env : Env F Γ) :
    Satisfies (.forall_ (.arr A B) p) env ↔
      ∀ table : ExpCoord (Coord F A) (Coord F B) F → F, Satisfies p (table, env) := by
  rfl

/-! ### Polynomial realization of higher-order application. -/

/-- The coordinate polynomial that realizes application at a HOL arrow type. -/
def applicationPolynomial (A B : Ty) (j : Coord F B) :
    MvPolynomial (Coord F (.arr A B) ⊕ Coord F A) F :=
  tableEvalPolynomial j

/-- The application polynomial evaluates to exact extensional table lookup. -/
@[simp] theorem eval_applicationPolynomial (A B : Ty) (j : Coord F B)
    (table : Val F (.arr A B)) (arg : Val F A) :
    MvPolynomial.eval (pack table arg) (applicationPolynomial A B j) = table (arg, j) := by
  exact eval_tableEvalPolynomial j table arg

/-- Consequently, each coordinate of a denoted STLC application is represented by
the application polynomial evaluated on the denotations of function and argument. -/
theorem eval_applicationPolynomial_denote (fn : Tm F Γ (.arr A B))
    (arg : Tm F Γ A) (env : Env F Γ) (j : Coord F B) :
    MvPolynomial.eval (pack (denote fn env) (denote arg env))
        (applicationPolynomial A B j) = denote (.app fn arg) env j := by
  exact eval_applicationPolynomial A B j (denote fn env) (denote arg env)

#assert_all_clean [arrow_is_table_exponential, denote_var_zero, denote_var_succ,
  denote_fst_pair, denote_snd_pair, denote_app_lam, product_eta, arrow_eta,
  denote_app_is_tableEval, satisfies_forall_arrow, eval_applicationPolynomial,
  eval_applicationPolynomial_denote]

end

end Dregg2.Metatheory.FinitePolynomialFunctions.FiniteHOL
