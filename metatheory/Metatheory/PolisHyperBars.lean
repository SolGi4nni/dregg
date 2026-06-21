/-
# Metatheory.PolisHyperBars — composition + monotone amendment lift for the politician floor.

gpt5.5's answer to Q5 (`docs/POLIS-HYPERPROPERTY-FRONTIER.md`): Boolean hyperbars first, quantale
grades only when budgets/cost demand them. A `Bar` is a bare floor (the forbidden set; more bars =
more restrictive); `or` composes; `NoWeaken old new := old.violates ⊆ new.violates` is the
politician-floor form of the constitution's **amendment non-regression**. The point: `or` PRESERVES
`NoWeaken`, so the politician floor (the or-fold of its capture-shapes) is monotone-amendable — the
constitution's `amendment_stream_nonregression` lifts to the composed hyperproperty floor.
-/
import Metatheory.Polis

namespace Metatheory.PolisHyperBars

open Metatheory.Polis

variable {Trace : Type}

/-- A bare politician floor: the set of captured (forbidden) traces. The decidable,
exactly-floor-violation `CaptureBar` is its enforced refinement; `barOf` forgets to this. -/
structure Bar (Trace : Type) where
  violates : Trace → Prop

/-- The floor a `CaptureBar` enforces, as a bare `Bar`. -/
def barOf {v : Trace → Prop} (_ : CaptureBar Trace v) : Bar Trace := ⟨v⟩

/-- Union of floors — a trace is captured by the combined floor iff EITHER bar captures it. -/
def Bar.or (b₁ b₂ : Bar Trace) : Bar Trace := ⟨fun τ => b₁.violates τ ∨ b₂.violates τ⟩

/-- **Non-regression at the politician-floor level**: a later floor forbids everything the earlier
one did (`oldViolations ⊆ newViolations`). The constitution's `amendment_stream_nonregression`,
ported to the politician hyperbar. -/
def NoWeaken (old new : Bar Trace) : Prop := ∀ τ, old.violates τ → new.violates τ

theorem NoWeaken.rfl' (b : Bar Trace) : NoWeaken b b := fun _ h => h

theorem NoWeaken.trans' {a b c : Bar Trace} (h₁ : NoWeaken a b) (h₂ : NoWeaken b c) :
    NoWeaken a c := fun τ h => h₂ τ (h₁ τ h)

/-- **`or` PRESERVES non-regression** — strengthening one component (or adding a bar) never weakens
the union floor. So the politician floor is monotone-amendable: amendment non-regression lifts to
the composed hyperproperty floor. -/
theorem NoWeaken.or_mono {old new : Bar Trace} (h : NoWeaken old new) (c : Bar Trace) :
    NoWeaken (old.or c) (new.or c) :=
  fun _ hv => hv.imp (h _) id

/-- Adding a bar only strengthens the floor (the union forbids a superset). -/
theorem NoWeaken.le_or (b c : Bar Trace) : NoWeaken b (b.or c) := fun _ h => Or.inl h

/-- An amendment STREAM over politician floors preserves the frozen minimum: along any sequence of
`NoWeaken`-amendments from a `b₀` that already covers `floorMin`, every stage still covers
`floorMin`. The hyperbar form of `Metatheory.Polis.amendment_stream_nonregression`. -/
theorem amendment_stream_nonregression_hyper
    (floorMin : Bar Trace) (ams : Nat → Bar Trace → Bar Trace)
    (mono : ∀ n b, NoWeaken b (ams n b))
    (b₀ : Bar Trace) (h₀ : NoWeaken floorMin b₀) :
    ∀ n, NoWeaken floorMin ((fun b => Nat.rec b (fun k bk => ams k bk) n) b₀) := by
  intro n
  induction n with
  | zero => exact h₀
  | succ k ih => exact ih.trans' (mono k _)

end Metatheory.PolisHyperBars
