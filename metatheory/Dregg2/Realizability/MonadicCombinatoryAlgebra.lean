/-
# Dregg2.Realizability.MonadicCombinatoryAlgebra

This file isolates a first, deliberately small effectful-realizability interface.  Computations
are not identified with total Lean functions: `PartialComputation α` is an explicit proposition
of possible results together with a proof that at most one result is possible.  Its bind is the
ordered relational composite, so the intermediate computation cannot be commuted or discarded.

`MonadicCombinatoryAlgebra` packages return, sequential bind, effectful application, and exact
monadic K/S equations.  `UnaryTerm` and `BracketAbstraction` state the corresponding (restricted,
but genuine) bracket-abstraction theorem.  Every existing relational `PCA` has such a model:
application is interpreted as its subsingleton partial-result computation, and ordinary S/K
bracket abstraction proves the effectful equation.

The separator section keeps two obligations distinct.  Closure under successful application is
the realizability separator law; `Progressive` additionally says accepted programs applied to
accepted inputs actually take a step; `Consistent` says the separator is proper.  The adapter
preserves all three predicates but does not manufacture a proper separator for an arbitrary PCA.
In particular, the one-point PCA proves the algebraic interface non-vacuous while also exposing
why separator consistency is real additional structure.
-/
import Dregg2.Realizability.PCA

namespace Dregg2.Realizability

universe u v w

/-! ## Subsingleton partial computations and their sequential monad -/

/-- A partial computation represented extensionally by its possible results.  Functionality
ensures that the proposition contains at most one result, while allowing divergence (no result). -/
structure PartialComputation (α : Type u) where
  Holds : α → Prop
  functional : ∀ {x y}, Holds x → Holds y → x = y

namespace PartialComputation

/-- Extensional equality of subsingleton partial computations. -/
theorem ext {α : Type u} {p q : PartialComputation α}
    (h : ∀ x, p.Holds x ↔ q.Holds x) : p = q := by
  cases p with
  | mk pp hp =>
    cases q with
    | mk qq hq =>
      have hpq : pp = qq := funext fun x => propext (h x)
      subst qq
      rfl

/-- The terminating computation with result `a`. -/
def ret {α : Type u} (a : α) : PartialComputation α where
  Holds := fun x => x = a
  functional := fun hx hy => hx.trans hy.symm

/-- Sequential bind.  The existential witness is the result of the first computation and the
second computation is selected only after that witness has been produced. -/
def bind {α : Type u} {β : Type v} (m : PartialComputation α)
    (k : α → PartialComputation β) : PartialComputation β where
  Holds := fun b => ∃ a, m.Holds a ∧ (k a).Holds b
  functional := by
    rintro b c ⟨a, ha, hb⟩ ⟨a', ha', hc⟩
    have haa' : a = a' := m.functional ha ha'
    subst a'
    exact (k a).functional hb hc

@[simp] theorem holds_ret_iff {α : Type u} {a x : α} :
    (ret a).Holds x ↔ x = a := Iff.rfl

/-- The exact observation rule for sequential bind. -/
@[simp] theorem holds_bind_iff {α : Type u} {β : Type v}
    (m : PartialComputation α) (k : α → PartialComputation β) (b : β) :
    (bind m k).Holds b ↔ ∃ a, m.Holds a ∧ (k a).Holds b := Iff.rfl

@[simp] theorem ret_bind {α : Type u} {β : Type v} (a : α)
    (k : α → PartialComputation β) : bind (ret a) k = k a := by
  apply ext
  intro b
  constructor
  · rintro ⟨x, hx, hb⟩
    subst x
    exact hb
  · intro hb
    exact ⟨a, rfl, hb⟩

@[simp] theorem bind_ret {α : Type u} (m : PartialComputation α) :
    bind m ret = m := by
  apply ext
  intro a
  constructor
  · rintro ⟨x, hx, hxa⟩
    subst x
    exact hx
  · intro ha
    exact ⟨a, ha, rfl⟩

@[simp] theorem bind_assoc {α : Type u} {β : Type v} {γ : Type w}
    (m : PartialComputation α) (k : α → PartialComputation β)
    (h : β → PartialComputation γ) :
    bind (bind m k) h = bind m (fun a => bind (k a) h) := by
  apply ext
  intro c
  constructor
  · rintro ⟨b, ⟨a, ha, hb⟩, hc⟩
    exact ⟨a, ha, b, hb, hc⟩
  · rintro ⟨a, ha, b, hb, hc⟩
    exact ⟨b, ⟨a, ha, hb⟩, hc⟩

/-- A computation terminates when it has a result. -/
def Defined {α : Type u} (m : PartialComputation α) : Prop := ∃ a, m.Holds a

theorem defined_bind_iff {α : Type u} {β : Type v} (m : PartialComputation α)
    (k : α → PartialComputation β) :
    Defined (bind m k) ↔ ∃ a, m.Holds a ∧ Defined (k a) := by
  constructor
  · rintro ⟨b, a, ha, hb⟩
    exact ⟨a, ha, b, hb⟩
  · rintro ⟨a, ha, b, hb⟩
    exact ⟨b, a, ha, hb⟩

end PartialComputation

/-! ## Exact monad and effectful combinatory-algebra law carriers -/

/-- Operations and exact monad equations used by the effectful application interface. -/
structure MonadLawCarrier (M : Type u → Type u) where
  ret : {α : Type u} → α → M α
  bind : {α β : Type u} → M α → (α → M β) → M β
  ret_bind : ∀ {α β : Type u} (a : α) (k : α → M β), bind (ret a) k = k a
  bind_ret : ∀ {α : Type u} (m : M α), bind m ret = m
  bind_assoc : ∀ {α β γ : Type u} (m : M α) (k : α → M β) (h : β → M γ),
    bind (bind m k) h = bind m (fun a => bind (k a) h)

/-- The partial-computation operations satisfy the exact monad equations. -/
def partialMonadLawCarrier : MonadLawCarrier (PartialComputation : Type u → Type u) where
  ret := PartialComputation.ret
  bind := PartialComputation.bind
  ret_bind := PartialComputation.ret_bind
  bind_ret := PartialComputation.bind_ret
  bind_assoc := PartialComputation.bind_assoc

/-- An observation interface for a functional partial monad.  The two observation equations make
the operational order of return and bind explicit, independently of equality in `M α`. -/
structure PartialMonadObservation (M : Type u → Type u) (L : MonadLawCarrier M) where
  Runs : {α : Type u} → M α → α → Prop
  functional : ∀ {α : Type u} {m : M α} {x y}, Runs m x → Runs m y → x = y
  runs_ret_iff : ∀ {α : Type u} {a x : α}, Runs (L.ret a) x ↔ x = a
  runs_bind_iff : ∀ {α β : Type u} {m : M α} {k : α → M β} {b : β},
    Runs (L.bind m k) b ↔ ∃ a, Runs m a ∧ Runs (k a) b

/-- Membership is the canonical observation of an explicit partial computation. -/
def partialMonadObservation : PartialMonadObservation
    (PartialComputation : Type u → Type u) partialMonadLawCarrier where
  Runs := PartialComputation.Holds
  functional := by
    intro α m x y hx hy
    exact m.functional hx hy
  runs_ret_iff := Iff.rfl
  runs_bind_iff := Iff.rfl

/-- A monadic combinatory algebra with sequential, call-by-value effectful application.

The final S equation fixes the evaluation order: first `f x`, then `g x`, then application of
the first result to the second. -/
structure MonadicCombinatoryAlgebra where
  Carrier : Type u
  M : Type u → Type u
  monad : MonadLawCarrier M
  observe : PartialMonadObservation M monad
  app : Carrier → Carrier → M Carrier

  k : Carrier
  kArg : Carrier → Carrier
  app_k : ∀ x, app k x = monad.ret (kArg x)
  app_kArg : ∀ x y, app (kArg x) y = monad.ret x

  s : Carrier
  sArg : Carrier → Carrier
  sArg₂ : Carrier → Carrier → Carrier
  app_s : ∀ f, app s f = monad.ret (sArg f)
  app_sArg : ∀ f g, app (sArg f) g = monad.ret (sArg₂ f g)
  app_s_result : ∀ f g x,
    app (sArg₂ f g) x =
      monad.bind (app f x) (fun fx =>
        monad.bind (app g x) (fun gx => app fx gx))

namespace MonadicCombinatoryAlgebra

/-- Successful effectful application. -/
def Applies (A : MonadicCombinatoryAlgebra.{u}) (f x y : A.Carrier) : Prop :=
  A.observe.Runs (A.app f x) y

/-- The S law gives operational progress through three ordered successful applications. -/
theorem s_progress (A : MonadicCombinatoryAlgebra.{u}) {f g x fx gx r : A.Carrier}
    (hfx : A.Applies f x fx) (hgx : A.Applies g x gx) (hr : A.Applies fx gx r) :
    A.Applies (A.sArg₂ f g) x r := by
  unfold Applies
  rw [A.app_s_result, A.observe.runs_bind_iff]
  exact ⟨fx, hfx, (A.observe.runs_bind_iff).2 ⟨gx, hgx, hr⟩⟩

/-- Conversely, a successful S application exposes all three sequential intermediate results. -/
theorem s_factor (A : MonadicCombinatoryAlgebra.{u}) {f g x r : A.Carrier}
    (h : A.Applies (A.sArg₂ f g) x r) :
    ∃ fx gx, A.Applies f x fx ∧ A.Applies g x gx ∧ A.Applies fx gx r := by
  unfold Applies at h ⊢
  rw [A.app_s_result, A.observe.runs_bind_iff] at h
  rcases h with ⟨fx, hfx, hrest⟩
  rw [A.observe.runs_bind_iff] at hrest
  rcases hrest with ⟨gx, hgx, hr⟩
  exact ⟨fx, gx, hfx, hgx, hr⟩

/-! ## Unary effectful terms and bracket abstraction -/

/-- Terms over one distinguished variable and arbitrary carrier constants. -/
inductive UnaryTerm (A : MonadicCombinatoryAlgebra.{u}) where
  | var
  | const (a : A.Carrier)
  | app (f x : UnaryTerm A)

/-- Sequential call-by-value interpretation of a unary effectful term. -/
def UnaryTerm.eval (A : MonadicCombinatoryAlgebra.{u}) :
    UnaryTerm A → A.Carrier → A.M A.Carrier
  | .var, x => A.monad.ret x
  | .const a, _ => A.monad.ret a
  | .app f x, a =>
      A.monad.bind (f.eval A a) (fun fv =>
        A.monad.bind (x.eval A a) (fun xv => A.app fv xv))

/-- Exact bracket abstraction for unary terms.  This is a law carrier rather than an assertion
that arbitrary metatheoretic functions are representable. -/
structure BracketAbstraction (A : MonadicCombinatoryAlgebra.{u}) where
  bracket : UnaryTerm A → A.Carrier
  app_bracket : ∀ t x, A.app (bracket t) x = t.eval A x

/-! ## Separators, progress, and consistency -/

/-- An effectful realizability separator: it contains the combinatory basis and is closed under
every successful application whose program and input are already accepted. -/
structure Separator (A : MonadicCombinatoryAlgebra.{u}) where
  Accepts : A.Carrier → Prop
  accepts_k : Accepts A.k
  accepts_s : Accepts A.s
  application_closed : ∀ {f x y}, Accepts f → Accepts x → A.Applies f x y → Accepts y

namespace Separator

/-- Accepted application never gets stuck.  This is intentionally stronger than closure, which
only constrains a result when one exists. -/
def Progressive {A : MonadicCombinatoryAlgebra.{u}} (S : Separator A) : Prop :=
  ∀ {f x}, S.Accepts f → S.Accepts x → ∃ y, A.Applies f x y

/-- A separator is consistent when it is proper: at least one carrier is not accepted. -/
def Consistent {A : MonadicCombinatoryAlgebra.{u}} (S : Separator A) : Prop :=
  ∃ rejected, ¬ S.Accepts rejected

/-- The maximal separator, useful as an algebraic non-vacuity witness. -/
def total (A : MonadicCombinatoryAlgebra.{u}) : Separator A where
  Accepts := fun _ => True
  accepts_k := trivial
  accepts_s := trivial
  application_closed := by simp

theorem total_not_consistent_of_subsingleton (A : MonadicCombinatoryAlgebra.{u})
    [Subsingleton A.Carrier] : ¬ (total A).Consistent := by
  rintro ⟨a, ha⟩
  exact ha trivial

end Separator

end MonadicCombinatoryAlgebra

/-! ## Adapter from the existing relational PCA -/

namespace PCA

/-- Relational PCA application as an explicit subsingleton partial computation. -/
def computation (P : PCA.{u}) (f x : P.Carrier) : PartialComputation P.Carrier where
  Holds := fun y => P.App f x y
  functional := P.app_functional

/-- Every relational PCA induces a monadic combinatory algebra over partial computations. -/
def toMonadicCombinatoryAlgebra (P : PCA.{u}) : MonadicCombinatoryAlgebra.{u} where
  Carrier := P.Carrier
  M := PartialComputation
  monad := partialMonadLawCarrier
  observe := partialMonadObservation
  app := P.computation
  k := P.k
  kArg := P.kArg
  app_k := by
    intro x
    apply PartialComputation.ext
    intro y
    constructor
    · intro hy
      exact P.app_functional hy (P.app_k x)
    · intro hy
      subst y
      exact P.app_k x
  app_kArg := by
    intro x y
    apply PartialComputation.ext
    intro z
    constructor
    · intro hz
      exact P.app_functional hz (P.app_kArg x y)
    · intro hz
      subst z
      exact P.app_kArg x y
  s := P.s
  sArg := P.sArg
  sArg₂ := P.sArg₂
  app_s := by
    intro f
    apply PartialComputation.ext
    intro y
    constructor
    · intro hy
      exact P.app_functional hy (P.app_s f)
    · intro hy
      subst y
      exact P.app_s f
  app_sArg := by
    intro f g
    apply PartialComputation.ext
    intro y
    constructor
    · intro hy
      exact P.app_functional hy (P.app_sArg f g)
    · intro hy
      subst y
      exact P.app_sArg f g
  app_s_result := by
    intro f g x
    apply PartialComputation.ext
    intro r
    constructor
    · intro hr
      rcases P.app_s_factor hr with ⟨fx, gx, hfx, hgx, hfg⟩
      exact ⟨fx, hfx, gx, hgx, hfg⟩
    · rintro ⟨fx, hfx, gx, hgx, hfg⟩
      exact P.app_s_result hfx hgx hfg

@[simp] theorem computation_holds_iff (P : PCA.{u}) {f x y : P.Carrier} :
    (P.computation f x).Holds y ↔ P.App f x y := Iff.rfl

theorem computation_ident (P : PCA.{u}) (x : P.Carrier) :
    P.computation P.ident x = PartialComputation.ret x := by
  apply PartialComputation.ext
  intro y
  constructor
  · intro hy
    exact P.app_functional hy (P.app_ident x)
  · intro hy
    subst y
    exact P.app_ident x

/-- PCA composition is exactly ordered monadic bind: run `e`, then run `d` on its result. -/
theorem computation_compose (P : PCA.{u}) (d e x : P.Carrier) :
    P.computation (P.compose d e) x =
      PartialComputation.bind (P.computation e x) (fun y => P.computation d y) := by
  apply PartialComputation.ext
  intro z
  exact P.app_compose_iff

/-- Ordinary S/K bracket abstraction, now read as an effectful bracket compiler. -/
def bracket (P : PCA.{u}) :
    MonadicCombinatoryAlgebra.UnaryTerm P.toMonadicCombinatoryAlgebra → P.Carrier
  | .var => P.ident
  | .const a => P.kArg a
  | .app f x => P.sArg₂ (P.bracket f) (P.bracket x)

/-- The existing PCA laws prove exact sequential effectful bracket abstraction. -/
def bracketAbstraction (P : PCA.{u}) :
    MonadicCombinatoryAlgebra.BracketAbstraction P.toMonadicCombinatoryAlgebra where
  bracket := P.bracket
  app_bracket := by
    intro t x
    induction t with
    | var => exact P.computation_ident x
    | const a =>
        exact P.toMonadicCombinatoryAlgebra.app_kArg a x
    | app f a ihf iha =>
        change P.computation (P.sArg₂ (P.bracket f) (P.bracket a)) x =
          PartialComputation.bind (f.eval P.toMonadicCombinatoryAlgebra x) (fun fv =>
            PartialComputation.bind (a.eval P.toMonadicCombinatoryAlgebra x) (fun xv =>
              P.computation fv xv))
        rw [← ihf, ← iha]
        exact P.toMonadicCombinatoryAlgebra.app_s_result (P.bracket f) (P.bracket a) x

/-- A PCA separator has the same application-closure condition before and after the adapter. -/
structure Separator (P : PCA.{u}) where
  Accepts : P.Carrier → Prop
  accepts_k : Accepts P.k
  accepts_s : Accepts P.s
  application_closed : ∀ {f x y}, Accepts f → Accepts x → P.App f x y → Accepts y

def Separator.toMonadic {P : PCA.{u}} (S : P.Separator) :
    MonadicCombinatoryAlgebra.Separator P.toMonadicCombinatoryAlgebra where
  Accepts := S.Accepts
  accepts_k := S.accepts_k
  accepts_s := S.accepts_s
  application_closed := by
    intro f x y hf hx hy
    change P.App f x y at hy
    exact S.application_closed hf hx hy

theorem Separator.progressive_iff {P : PCA.{u}} (S : P.Separator) :
    S.toMonadic.Progressive ↔
      ∀ {f x}, S.Accepts f → S.Accepts x → ∃ y, P.App f x y := by
  constructor
  · intro h f x hf hx
    rcases h hf hx with ⟨y, hy⟩
    exact ⟨y, hy⟩
  · intro h f x hf hx
    rcases h hf hx with ⟨y, hy⟩
    exact ⟨y, hy⟩

theorem Separator.consistent_iff {P : PCA.{u}} (S : P.Separator) :
    S.toMonadic.Consistent ↔ ∃ rejected, ¬ S.Accepts rejected := by
  constructor <;> intro h <;> exact h

/-! ## Concrete non-vacuity -/

/-- The one-point PCA adapter is a concrete monadic combinatory algebra. -/
def unitMonadicCombinatoryAlgebra : MonadicCombinatoryAlgebra := unitPCA.toMonadicCombinatoryAlgebra

/-- In the concrete model every effectful application terminates with the unique result. -/
theorem unitMonadic_application_total
    (f x : unitMonadicCombinatoryAlgebra.Carrier) :
    ∃ y, unitMonadicCombinatoryAlgebra.Applies f x y := by
  refine ⟨(), ?_⟩
  change unitPCA.App f x ()
  trivial

/-- Consequently its maximal separator is progressive. -/
theorem unitMonadic_total_separator_progressive :
    (MonadicCombinatoryAlgebra.Separator.total unitMonadicCombinatoryAlgebra).Progressive := by
  intro f x hf hx
  exact unitMonadic_application_total f x

#assert_all_clean [PartialComputation.ext, PartialComputation.holds_ret_iff,
  PartialComputation.holds_bind_iff, PartialComputation.ret_bind,
  PartialComputation.bind_ret, PartialComputation.bind_assoc,
  PartialComputation.defined_bind_iff, partialMonadLawCarrier,
  partialMonadObservation, MonadicCombinatoryAlgebra.s_progress,
  MonadicCombinatoryAlgebra.s_factor,
  MonadicCombinatoryAlgebra.Separator.total_not_consistent_of_subsingleton,
  computation_holds_iff, computation_ident, computation_compose,
  bracketAbstraction, Separator.progressive_iff, Separator.consistent_iff,
  unitMonadic_application_total, unitMonadic_total_separator_progressive]

end PCA
end Dregg2.Realizability
