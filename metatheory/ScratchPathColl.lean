import Dregg2.Circuit.MapOpsColumnLayout
import Dregg2.Crypto.SpongeCarrierReduction

namespace ScratchPathColl

open Dregg2.Circuit.MapOpsColumnLayout
open Dregg2.Circuit.MapMerkleRoot (mapNode foldLevel perfectRoot foldLevel_length_half)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Crypto.SpongeCarrierReduction (IsSpongeColl)
open Dregg2.Substrate

set_option autoImplicit false

def stepNode (b : Bool) (rec sib : ℤ) : List ℤ := if b then [sib, rec] else [rec, sib]

theorem pathRecompute_cons (hash : List ℤ → ℤ) (b : Bool) (sib : ℤ)
    (rest : List (Bool × ℤ)) (leaf : ℤ) :
    pathRecompute hash leaf ((b, sib) :: rest)
      = hash (stepNode b (pathRecompute hash leaf rest) sib) := by
  cases b <;> rfl

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

theorem pathRecompute_binds_updates_or_collides (hash : List ℤ → ℤ) :
    ∀ (steps : List (Bool × ℤ)) (xs : List ℤ) (leaf : ℤ),
      xs.length = 2 ^ steps.length →
      pathRecompute hash leaf steps = perfectRoot hash steps.length xs →
      (xs[pathPos steps]? = some leaf ∧
        ∀ leaf', pathRecompute hash leaf' steps
          = perfectRoot hash steps.length (xs.set (pathPos steps) leaf'))
      ∨ IsSpongeColl hash (pathCollFind hash steps xs leaf) := by
  intro steps
  induction steps with
  | nil =>
    intro xs leaf hlen hroot
    simp only [List.length_nil, pow_zero] at hlen
    obtain ⟨x, rfl⟩ : ∃ x, xs = [x] := by
      cases xs with
      | nil => simp at hlen
      | cons a t =>
        cases t with
        | nil => exact ⟨a, rfl⟩
        | cons b t' => simp at hlen
    have hx : leaf = x := hroot
    refine Or.inl ⟨?_, ?_⟩
    · simp [pathPos, hx]
    · intro leaf'; rfl
  | cons step rest ih =>
    obtain ⟨b, sib⟩ := step
    intro xs leaf hlen hroot
    simp only [List.length_cons] at hlen
    have hp2 : 2 ^ (rest.length + 1) = 2 ^ rest.length + 2 ^ rest.length := by
      rw [pow_succ]; ring
    obtain ⟨L, R, rfl, hL, hR⟩ :
        ∃ L R : List ℤ, xs = L ++ R ∧ L.length = 2 ^ rest.length
          ∧ R.length = 2 ^ rest.length := by
      refine ⟨xs.take (2 ^ rest.length), xs.drop (2 ^ rest.length),
        (List.take_append_drop _ _).symm, ?_, ?_⟩
      · rw [List.length_take]; omega
      · rw [List.length_drop]; omega
    have hposlt := pathPos_lt rest
    have htake : (L ++ R).take (2 ^ rest.length) = L := List.take_left' hL
    have hdrop : (L ++ R).drop (2 ^ rest.length) = R := List.drop_left' hL
    have hcol : hash (stepNode b (pathRecompute hash leaf rest) sib)
        = hash [perfectRoot hash rest.length L, perfectRoot hash rest.length R] := by
      rw [← pathRecompute_cons hash b sib rest leaf, hroot]
      simp only [List.length_cons]
      exact perfectRoot_append hash rest.length L R hL hR
    cases b with
    | false =>
      by_cases hAB : stepNode false (pathRecompute hash leaf rest) sib
          = [perfectRoot hash rest.length L, perfectRoot hash rest.length R]
      · have hrec : pathRecompute hash leaf rest = perfectRoot hash rest.length L := by
          simpa [stepNode] using (List.cons.inj hAB).1
        have hsib : sib = perfectRoot hash rest.length R := by
          have h2 := (List.cons.inj hAB).2
          simpa [stepNode] using (List.cons.inj h2).1
        rcases ih L leaf hL hrec with ⟨hmem, hupd⟩ | hcoll
        · refine Or.inl ⟨?_, ?_⟩
          · simp only [pathPos]
            rw [List.getElem?_append_left (by omega)]
            exact hmem
          · intro leaf'
            simp only [pathRecompute, pathPos, List.length_cons]
            rw [set_append_left' L R _ _ (by omega)]
            rw [perfectRoot_append hash rest.length _ R
              (by rw [List.length_set]; exact hL) hR]
            rw [hupd leaf', hsib]
        · refine Or.inr ?_
          simp only [pathCollFind, htake, hdrop, if_pos hAB, Bool.false_eq_true, if_false]
          exact hcoll
      · refine Or.inr ?_
        simp only [pathCollFind, htake, hdrop, if_neg hAB]
        exact ⟨hAB, hcol⟩
    | true =>
      by_cases hAB : stepNode true (pathRecompute hash leaf rest) sib
          = [perfectRoot hash rest.length L, perfectRoot hash rest.length R]
      · have hsib : sib = perfectRoot hash rest.length L := by
          simpa [stepNode] using (List.cons.inj hAB).1
        have hrec : pathRecompute hash leaf rest = perfectRoot hash rest.length R := by
          have h2 := (List.cons.inj hAB).2
          simpa [stepNode] using (List.cons.inj h2).1
        rcases ih R leaf hR hrec with ⟨hmem, hupd⟩ | hcoll
        · refine Or.inl ⟨?_, ?_⟩
          · simp only [pathPos]
            rw [List.getElem?_append_right (by omega)]
            rw [show 2 ^ rest.length + pathPos rest - L.length = pathPos rest by omega]
            exact hmem
          · intro leaf'
            simp only [pathRecompute, pathPos, List.length_cons]
            rw [show 2 ^ rest.length + pathPos rest = L.length + pathPos rest by omega]
            rw [set_append_right' L R _ _]
            rw [perfectRoot_append hash rest.length L _ hL
              (by rw [List.length_set]; exact hR)]
            rw [hupd leaf', hsib]
        · refine Or.inr ?_
          simp only [pathCollFind, htake, hdrop, if_pos hAB, if_true]
          exact hcoll
      · refine Or.inr ?_
        simp only [pathCollFind, htake, hdrop, if_neg hAB]
        exact ⟨hAB, hcol⟩

theorem pathRecompute_binds_updates' (hash : List ℤ → ℤ)
    (steps : List (Bool × ℤ)) (xs : List ℤ) (leaf : ℤ)
    (hlen : xs.length = 2 ^ steps.length)
    (hroot : pathRecompute hash leaf steps = perfectRoot hash steps.length xs)
    (hno : ¬ IsSpongeColl hash (pathCollFind hash steps xs leaf)) :
    xs[pathPos steps]? = some leaf ∧
    ∀ leaf', pathRecompute hash leaf' steps
      = perfectRoot hash steps.length (xs.set (pathPos steps) leaf') :=
  (pathRecompute_binds_updates_or_collides hash steps xs leaf hlen hroot).resolve_right hno

theorem noPathColl_of_CR {hash : List ℤ → ℤ} (hCR : Poseidon2SpongeCR hash)
    {steps : List (Bool × ℤ)} {xs : List ℤ} {leaf : ℤ} :
    ¬ IsSpongeColl hash (pathCollFind hash steps xs leaf) :=
  fun hc => hc.1 (hCR _ _ hc.2)

theorem noPathColl_self {hash : List ℤ → ℤ} {steps : List (Bool × ℤ)} {xs : List ℤ} {leaf : ℤ}
    (hno : ¬ IsSpongeColl hash (pathCollFind hash steps xs leaf)) :
    ¬ IsSpongeColl hash (pathCollFind hash steps xs leaf) := hno

/-! ### leaf side -/

def leafPre (e : ℤ × ℤ) : List ℤ := [e.1, e.2]

theorem leafOf_binds_or_collides (hash : List ℤ → ℤ) {e₁ e₂ : ℤ × ℤ}
    (h : Heap.leafOf hash e₁ = Heap.leafOf hash e₂) :
    e₁ = e₂ ∨ IsSpongeColl hash (leafPre e₁, leafPre e₂) := by
  by_cases hpre : leafPre e₁ = leafPre e₂
  · refine Or.inl ?_
    obtain ⟨a₁, b₁⟩ := e₁
    obtain ⟨a₂, b₂⟩ := e₂
    simp only [leafPre, List.cons.injEq, and_true] at hpre
    simp_all
  · exact Or.inr ⟨hpre, h⟩

theorem leafOf_injective' (hash : List ℤ → ℤ) {e₁ e₂ : ℤ × ℤ}
    (hno : ¬ IsSpongeColl hash (leafPre e₁, leafPre e₂))
    (h : Heap.leafOf hash e₁ = Heap.leafOf hash e₂) : e₁ = e₂ :=
  (leafOf_binds_or_collides hash h).resolve_right hno

theorem noLeafColl_of_CR {hash : List ℤ → ℤ} (hCR : Poseidon2SpongeCR hash) {e₁ e₂ : ℤ × ℤ} :
    ¬ IsSpongeColl hash (leafPre e₁, leafPre e₂) :=
  fun hc => hc.1 (hCR _ _ hc.2)

theorem noLeafColl_self {hash : List ℤ → ℤ} {e₁ e₂ : ℤ × ℤ}
    (hno : ¬ IsSpongeColl hash (leafPre e₁, leafPre e₂)) :
    ¬ IsSpongeColl hash (leafPre e₁, leafPre e₂) := hno

/-! ### TEETH -/

/-- LOAD-BEARING: dropping the per-instance side condition is REFUTED. -/
theorem pathBinds_unconditional_false :
    ¬ (∀ (hash : List ℤ → ℤ) (steps : List (Bool × ℤ)) (xs : List ℤ) (leaf : ℤ),
        xs.length = 2 ^ steps.length →
        pathRecompute hash leaf steps = perfectRoot hash steps.length xs →
        xs[pathPos steps]? = some leaf) := by
  intro hall
  have h := hall (fun _ => 0) [(false, 0)] [1, 2] 5 rfl rfl
  simp only [pathPos, List.getElem?_cons_zero, Option.some.injEq] at h
  omega

/-- REFUTABLE: the new side condition genuinely FAILS at a broken sponge. -/
theorem pathColl_refutable :
    IsSpongeColl (fun _ => 0) (pathCollFind (fun _ => (0 : ℤ)) [(false, 0)] [1, 2] 5) := by
  refine ⟨?_, rfl⟩
  decide

/-- NON-VACUOUS: at an honest opening the side condition HOLDS for EVERY hash (no CR needed),
so the ported binding genuinely FIRES at deployed parameters. -/
theorem path_binds_fires (hash : List ℤ → ℤ) :
    ([3, 5] : List ℤ)[pathPos [(false, (5 : ℤ))]]? = some 3 :=
  (pathRecompute_binds_updates' hash [(false, (5 : ℤ))] [3, 5] 3 rfl rfl
    (by intro hc; exact hc.1 rfl)).1

theorem leafColl_refutable :
    IsSpongeColl (fun _ => 0) (leafPre ((1 : ℤ), (2 : ℤ)), leafPre ((3 : ℤ), (4 : ℤ))) := by
  refine ⟨?_, rfl⟩
  decide

end ScratchPathColl
