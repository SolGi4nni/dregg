/-
# Dregg2.Realizability.PCA — an honest relational partial-combinatory-algebra core.

This is the first executable/formal slice of the realizability route.  Application is a
ternary relation, rather than a total Lean function: `App f x y` says that `f x` is defined and
returns `y`.  Functionality makes that result unique.  The chosen curried stages for `K` and `S`
avoid hiding choice in the interface, while the final two `S` laws state exact Kleene equality:

  `S f g x` is defined with result `r` iff `f x`, `g x`, and `(f x) (g x)` are defined and the
  last application returns `r`.

The file derives identity and composition trackers from `S` and `K`; these are the only
combinatory facts needed by the indexed realizability-preorder layer.  `unitPCA` witnesses that
the interface is inhabited.  This file does NOT assert that a tripos or topos has been built.
-/
import Dregg2.Tactics

namespace Dregg2.Realizability

universe u

/-- A relational partial combinatory algebra with chosen curried `K`/`S` stages.

`app_s_result` and `app_s_factor` are the two directions of Kleene equality for `S`.  The
separate stage fields record that `K x`, `S f`, and `S f g` are always defined without using a
noncomputable choice operator. -/
structure PCA where
  Carrier : Type u
  App : Carrier → Carrier → Carrier → Prop
  app_functional : ∀ {f x y z}, App f x y → App f x z → y = z

  k : Carrier
  kArg : Carrier → Carrier
  app_k : ∀ x, App k x (kArg x)
  app_kArg : ∀ x y, App (kArg x) y x

  s : Carrier
  sArg : Carrier → Carrier
  sArg₂ : Carrier → Carrier → Carrier
  app_s : ∀ f, App s f (sArg f)
  app_sArg : ∀ f g, App (sArg f) g (sArg₂ f g)
  app_s_result : ∀ {f g x fx gx r},
    App f x fx → App g x gx → App fx gx r → App (sArg₂ f g) x r
  app_s_factor : ∀ {f g x r}, App (sArg₂ f g) x r →
    ∃ fx gx, App f x fx ∧ App g x gx ∧ App fx gx r

namespace PCA

/-- Definedness of partial application. -/
def Defined (P : PCA) (f x : P.Carrier) : Prop := ∃ y, P.App f x y

/-- The identity combinator `I = S K K`. -/
def ident (P : PCA) : P.Carrier := P.sArg₂ P.k P.k

/-- `I x = x`, derived solely from the `S` and `K` laws. -/
theorem app_ident (P : PCA) (x : P.Carrier) : P.App P.ident x x := by
  exact P.app_s_result (P.app_k x) (P.app_k x) (P.app_kArg x (P.kArg x))

/-- A composition tracker.  `compose d e` behaves as `fun x ⇒ d (e x)` wherever that
partial composite is defined.  This is the specialized `S (K d) e` combinator. -/
def compose (P : PCA) (d e : P.Carrier) : P.Carrier := P.sArg₂ (P.kArg d) e

/-- Forward evaluation of the derived composition combinator. -/
theorem app_compose (P : PCA) {d e x y z : P.Carrier}
    (he : P.App e x y) (hd : P.App d y z) :
    P.App (P.compose d e) x z := by
  exact P.app_s_result (P.app_kArg d x) he hd

/-- Exactness of derived composition: it has no outcomes besides a genuine two-step partial
application. -/
theorem app_compose_iff (P : PCA) {d e x z : P.Carrier} :
    P.App (P.compose d e) x z ↔ ∃ y, P.App e x y ∧ P.App d y z := by
  constructor
  · intro h
    rcases P.app_s_factor h with ⟨dx, y, hdx, he, hd⟩
    have hdx_eq : dx = d := P.app_functional hdx (P.app_kArg d x)
    subst dx
    exact ⟨y, he, hd⟩
  · rintro ⟨y, he, hd⟩
    exact P.app_compose he hd

/-- Definedness of composition is exactly existence of the intermediate result. -/
theorem defined_compose_iff (P : PCA) {d e x : P.Carrier} :
    P.Defined (P.compose d e) x ↔
      ∃ y z, P.App e x y ∧ P.App d y z := by
  simp only [Defined, P.app_compose_iff]
  constructor
  · rintro ⟨z, y, he, hd⟩
    exact ⟨y, z, he, hd⟩
  · rintro ⟨y, z, he, hd⟩
    exact ⟨z, y, he, hd⟩

/-! ## A concrete non-vacuity witness -/

/-- The one-element total PCA.  It is intentionally simple: its purpose is to prove that the
relational interface is consistent/inhabited, not to serve as the computational model used by
later realizability constructions. -/
def unitPCA : PCA where
  Carrier := Unit
  App := fun _ _ _ => True
  app_functional := by
    intro f x y z hy hz
    exact Subsingleton.elim y z
  k := ()
  kArg := fun _ => ()
  app_k := by simp
  app_kArg := by simp
  s := ()
  sArg := fun _ => ()
  sArg₂ := fun _ _ => ()
  app_s := by simp
  app_sArg := by simp
  app_s_result := by simp
  app_s_factor := by
    intro f g x r h
    exact ⟨(), (), trivial, trivial, trivial⟩

theorem unitPCA_application_total (f x : unitPCA.Carrier) :
    ∃ y, unitPCA.App f x y := ⟨(), trivial⟩

#assert_all_clean [app_ident, app_compose, app_compose_iff, defined_compose_iff,
  unitPCA_application_total]

end PCA
end Dregg2.Realizability
