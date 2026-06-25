/-
# Dregg2.Crypto.Deriv.TTerm — Stage 3 scaffolding: transition terms (the SYMBOLIC derivative carrier).

Brzozowski finiteness is alphabet-INDEPENDENT: it bounds the SYMBOLIC derivative's state space, where
one symbolic step yields the LIST of all possible next-states across the alphabet (not one `der a`).
The ITP'25 `finiteness-derivatives` proof carries this via TRANSITION TERMS (`TTerm.lean`): a binary
tree branching on alphabet predicates with regex leaves; `leaves` collects the reachable states. This
is the structure the symbolic `derivative`/`step` build on, and over which `pieces` over-approximates.

`TTerm` and all its monad/`leaves`/`lift_*` laws are FULLY GENERIC (over the branch/leaf types) — so
this ports VERBATIM from ITP'25 `TTerm.lean` (read-only blueprint). Banked kernel-clean so the
symbolic `derivative`/`step` + `pieces` (the named Stage-3 closure) sit on a finished monad layer.

`#assert_axioms`-clean, `sorry`-free.
-/
import Mathlib.Data.List.Basic
import Dregg2.Tactics

namespace Dregg2.Crypto.Deriv

open List

/-- **`TTerm α β`** — transition terms: a binary tree branching on a `condition : α` (an alphabet
predicate) with `β` leaves (the regex states). ITP'25 `TTerm.lean:17`. -/
inductive TTerm (α β : Type) : Type where
  /-- A leaf state. -/
  | Leaf : β → TTerm α β
  /-- A branch on `condition`: `_then` if it holds, `_else` otherwise. -/
  | Node (condition : α) (_then : TTerm α β) (_else : TTerm α β) : TTerm α β
  deriving Repr, DecidableEq

namespace TTerm

/-- Place a value into a leaf (the monad `pure`). -/
@[simp] def pure (b : β) : TTerm α β := TTerm.Leaf b

/-- Flatten a nested `TTerm`. -/
@[simp] def join (b : TTerm α (TTerm α β)) : TTerm α β :=
  match b with
  | Leaf b => b
  | Node p f g => Node p (join f) (join g)

/-- Map a function over every leaf (functor `fmap`). -/
@[simp] def fmap (f : β → γ) (b : TTerm α β) : TTerm α γ :=
  match b with
  | Leaf b => pure (f b)
  | Node p a b => Node p (fmap f a) (fmap f b)

@[simp] theorem fmap_id (b : TTerm α β) : fmap id b = b :=
  match b with
  | Leaf b => rfl
  | Node p a b => by simp only [fmap, TTerm.fmap_id a, TTerm.fmap_id b]

@[simp] theorem fmap_compose (f : β → γ) (g : γ → δ) (b : TTerm α β) :
    fmap (g ∘ f) b = fmap g (fmap f b) :=
  match b with
  | Leaf b => rfl
  | Node p a b => by
    simp only [fmap]
    rw [TTerm.fmap_compose f g a, TTerm.fmap_compose f g b]

/-- Bind: replace leaves with new `TTerm`s. -/
@[simp] def bind (f : β → TTerm α γ) : TTerm α β → TTerm α γ := fun b => join (fmap f b)

instance : Monad (TTerm α) where
  pure {β : Type} (b : β) := pure b
  bind q e := join (fmap e q)

end TTerm

open TTerm

/-- Lift a unary op over leaves. -/
def lift_unary (op : β → β') (g : TTerm α β) : TTerm α β' := fmap op g

/-- Lift a binary op over the product of two terms' leaves. -/
def lift_binary (op : β → β → β') (l r : TTerm α β) : TTerm α β' :=
  bind (fun x => lift_unary (op x) r) l

/-- Collect all leaves of a `TTerm` (the reachable states). -/
@[simp] def leaves : TTerm α β → List β
  | TTerm.Leaf r     => [r]
  | TTerm.Node _ f g => leaves f ++ leaves g

@[simp] theorem leaves_unary (op : β → β) (g : TTerm α β) :
    leaves (lift_unary op g) = map op (leaves g) :=
  match g with
  | TTerm.Leaf g     => rfl
  | TTerm.Node _ f g => by
    simp only [lift_unary, leaves, map_append] at *
    rw [← leaves_unary op f, ← leaves_unary op g]
    rfl

/-- `productWith op xs ys` — apply `op` to every pair of the Cartesian product. -/
@[simp] def List.productWith (op : α → α → α) (xs ys : List α) : List α :=
  map (Function.uncurry op) (xs.product ys)

@[simp] theorem leaves_fmap {op : β → γ} {g : TTerm α β} :
    leaves (TTerm.fmap op g) = map op (leaves g) := by
  match g with
  | TTerm.Leaf r     => rfl
  | TTerm.Node _ f g =>
    simp only [leaves, TTerm.fmap]
    rw [leaves_fmap, leaves_fmap]
    exact Eq.symm map_append

@[simp] theorem productWith_append {op : β → β → β} {ff gg g : TTerm α β} :
    List.productWith op (leaves ff ++ leaves gg) (leaves g) =
      List.productWith op (leaves ff) (leaves g) ++ List.productWith op (leaves gg) (leaves g) := by
  simp only [List.productWith, List.product, List.flatMap_append, map_append]

@[simp] theorem leaves_binary (op : β → β → β) (f g : TTerm α β) :
    leaves (lift_binary op f g) = List.productWith op (leaves f) (leaves g) := by
  match f with
  | TTerm.Leaf r =>
    simp only [lift_binary, TTerm.bind, TTerm.fmap, TTerm.pure, lift_unary, List.productWith, leaves]
    match g with
    | TTerm.Leaf s     => simp only [TTerm.fmap, List.product, leaves]; rfl
    | TTerm.Node p f g =>
      simp only [leaves, leaves_fmap, List.product, map_append, List.flatMap_cons, List.flatMap_nil,
        append_nil, map_map, TTerm.join, TTerm.fmap, leaves_fmap]; rfl
  | TTerm.Node pp ff gg =>
    simp only [leaves, productWith_append]
    simp only [← leaves_binary op ff g, ← leaves_binary op gg g]; rfl

end Dregg2.Crypto.Deriv

/-! ## Axiom hygiene. -/

#assert_all_clean [
  Dregg2.Crypto.Deriv.TTerm.fmap_id,
  Dregg2.Crypto.Deriv.TTerm.fmap_compose,
  Dregg2.Crypto.Deriv.leaves_unary,
  Dregg2.Crypto.Deriv.leaves_fmap,
  Dregg2.Crypto.Deriv.leaves_binary
]
