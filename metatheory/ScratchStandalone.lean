import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace ScratchStandalone

set_option autoImplicit false

-- === copies of the deployed objects (MapMerkleRoot / MapOpsColumnLayout / Heap) ===
def mapNode (hash : List ℤ → ℤ) (l r : ℤ) : ℤ := hash [l, r]

def foldLevel (hash : List ℤ → ℤ) : List ℤ → List ℤ
  | [] => []
  | [x] => [x]
  | l :: r :: rest => mapNode hash l r :: foldLevel hash rest

def perfectRoot (hash : List ℤ → ℤ) : Nat → List ℤ → ℤ
  | 0,     xs => xs.headD 0
  | d + 1, xs => perfectRoot hash d (foldLevel hash xs)

def pathPos : List (Bool × ℤ) → Nat
  | [] => 0
  | (false, _) :: rest => pathPos rest
  | (true, _) :: rest => 2 ^ rest.length + pathPos rest

def pathRecompute (hash : List ℤ → ℤ) (leaf : ℤ) : List (Bool × ℤ) → ℤ
  | [] => leaf
  | (false, sib) :: rest => mapNode hash (pathRecompute hash leaf rest) sib
  | (true, sib) :: rest => mapNode hash sib (pathRecompute hash leaf rest)

def leafOf (hash : List ℤ → ℤ) (e : ℤ × ℤ) : ℤ := hash [e.1, e.2]

def IsSpongeColl (h : List ℤ → ℤ) (p : List ℤ × List ℤ) : Prop :=
  p.1 ≠ p.2 ∧ h p.1 = h p.2

-- === the new material under test ===
def stepNode (b : Bool) (rec sib : ℤ) : List ℤ := if b then [sib, rec] else [rec, sib]

def pathCollFind (hash : List ℤ → ℤ) :
    List (Bool × ℤ) → List ℤ → ℤ → List ℤ × List ℤ
  | [], xs, leaf => ([leaf], [xs.headD 0])
  | (b, sib) :: rest, xs, leaf =>
      if stepNode b (pathRecompute hash leaf rest) sib
          = [perfectRoot hash rest.length (xs.take (2 ^ rest.length)),
             perfectRoot hash rest.length (xs.drop (2 ^ rest.length))] then
        (if b then pathCollFind hash rest (xs.drop (2 ^ rest.length)) leaf
         else pathCollFind hash rest (xs.take (2 ^ rest.length)) leaf)
      else
        (stepNode b (pathRecompute hash leaf rest) sib,
         [perfectRoot hash rest.length (xs.take (2 ^ rest.length)),
          perfectRoot hash rest.length (xs.drop (2 ^ rest.length))])

theorem pathCollFind_len_le (hash : List ℤ → ℤ) :
    ∀ (steps : List (Bool × ℤ)) (xs : List ℤ) (leaf : ℤ),
      (pathCollFind hash steps xs leaf).1.length
        + (pathCollFind hash steps xs leaf).2.length ≤ 4 := by
  intro steps
  induction steps with
  | nil => intro xs leaf; simp [pathCollFind]
  | cons step rest ih =>
    obtain ⟨b, sib⟩ := step
    intro xs leaf
    by_cases hAB : stepNode b (pathRecompute hash leaf rest) sib
        = [perfectRoot hash rest.length (xs.take (2 ^ rest.length)),
           perfectRoot hash rest.length (xs.drop (2 ^ rest.length))]
    · rw [pathCollFind, if_pos hAB]
      cases b
      · simpa using ih (xs.take (2 ^ rest.length)) leaf
      · simpa using ih (xs.drop (2 ^ rest.length)) leaf
    · rw [pathCollFind, if_neg hAB]
      cases b <;> simp [stepNode]

/-! ### TEETH -/

theorem pathBinds_unconditional_false :
    ¬ (∀ (hash : List ℤ → ℤ) (steps : List (Bool × ℤ)) (xs : List ℤ) (leaf : ℤ),
        xs.length = 2 ^ steps.length →
        pathRecompute hash leaf steps = perfectRoot hash steps.length xs →
        xs[pathPos steps]? = some leaf) := by
  intro hall
  have h := hall (fun _ => 0) [(false, 0)] [1, 2] 5 rfl rfl
  simp only [pathPos, List.getElem?_cons_zero, Option.some.injEq] at h
  omega

theorem pathColl_refutable :
    IsSpongeColl (fun _ => 0) (pathCollFind (fun _ => (0 : ℤ)) [(false, 0)] [1, 2] 5) := by
  refine ⟨?_, rfl⟩
  decide

def leafPre (e : ℤ × ℤ) : List ℤ := [e.1, e.2]

theorem leafOf_binds_or_collides (hash : List ℤ → ℤ) {e₁ e₂ : ℤ × ℤ}
    (h : leafOf hash e₁ = leafOf hash e₂) :
    e₁ = e₂ ∨ IsSpongeColl hash (leafPre e₁, leafPre e₂) := by
  by_cases hpre : leafPre e₁ = leafPre e₂
  · refine Or.inl ?_
    obtain ⟨a₁, b₁⟩ := e₁
    obtain ⟨a₂, b₂⟩ := e₂
    simp only [leafPre, List.cons.injEq, and_true] at hpre
    simp_all
  · exact Or.inr ⟨hpre, h⟩

theorem leafColl_refutable :
    IsSpongeColl (fun _ => 0) (leafPre ((1 : ℤ), (2 : ℤ)), leafPre ((3 : ℤ), (4 : ℤ))) := by
  refine ⟨?_, rfl⟩
  decide

-- the non-vacuity tooth needs the S3; restate it locally against a stub of the S2
theorem fires_shape (hash : List ℤ → ℤ) :
    ¬ IsSpongeColl hash (pathCollFind hash [(false, (5 : ℤ))] [3, 5] 3) := by
  intro hc
  exact hc.1 rfl

end ScratchStandalone
