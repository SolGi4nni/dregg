/-
# Dregg2.Authority.ClearanceGraph — compartment clearance as an explicit dominance relation.

Phase A foundation for `Apps/CompartmentWorkflowMandate`: a finite clearance graph whose
`dominates` relation is stored as explicit `(high, low)` edges and closed under reflexivity
and transitivity. An actor holding labels `L` may read a compartment label `ℓ` when some
`a ∈ L` dominates `ℓ`; conjunctive clearance checks every required label.

Pure, computable, `#eval`-able.
-/
import Dregg2.Tactics

namespace Dregg2.Authority.ClearanceGraph

/-! ## Labels — named strings or numeric ids. -/

/-- A clearance/compartment label: either a numeric id or a human-readable name. -/
inductive Label where
  | id    (n : Nat)
  | named (s : String)
  deriving Repr, DecidableEq

instance : BEq Label := ⟨fun a b => decide (a = b)⟩

/-! ## The clearance graph + the dominance relation. -/

/-- **`Graph`** — a finite edge list `(dominator, dominated)`: the left label's clearance is
at least the right label's (may read down). Dominance is the reflexive, transitive closure
of these edges. -/
structure Graph where
  edges : List (Label × Label)
  deriving Repr, DecidableEq

abbrev ClearanceGraph := Graph

/-- **`Dominates`** — the reflexive, transitive closure of `edges`. -/
inductive Dominates (edges : List (Label × Label)) : Label → Label → Prop where
  | refl (a : Label) : Dominates edges a a
  | step {a b c : Label} (h : (a, b) ∈ edges) (h' : Dominates edges b c) : Dominates edges a c

/-- **`dominates`** — explicit dominance over a clearance graph. -/
def dominates (g : ClearanceGraph) (a b : Label) : Prop :=
  Dominates g.edges a b

/-- Fuel-bounded reachability search (computable dominance on finite graphs). -/
def dominatesFuel (edges : List (Label × Label)) (a b : Label) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
    if a == b then true
    else edges.any (fun p => p.1 == a && dominatesFuel edges p.2 b fuel)

/-- Decidable dominance check for finite graphs. -/
def dominatesD (g : ClearanceGraph) (a b : Label) : Bool :=
  dominatesFuel g.edges a b (g.edges.length + 1)

/-- Transitivity at the inductive layer. -/
theorem Dominates.trans {edges : List (Label × Label)} {a b c : Label}
    (hab : Dominates edges a b) (hbc : Dominates edges b c) : Dominates edges a c := by
  revert c
  induction hab with
  | refl _ => intro c hbc; exact hbc
  | step hedge hrest ih => intro c hbc; exact Dominates.step hedge (ih hbc)

/-- **`dominates_refl`** — every label dominates itself. -/
theorem dominates_refl (g : ClearanceGraph) (a : Label) : dominates g a a :=
  Dominates.refl a

/-- **`dominates_trans`** — dominance is transitive. -/
theorem dominates_trans (g : ClearanceGraph) {a b c : Label}
    (hab : dominates g a b) (hbc : dominates g b c) : dominates g a c :=
  Dominates.trans hab hbc

/-! ## `dominatesD` soundness (decidable check ⇒ Prop). -/

theorem dominates_of_dominatesFuel (g : ClearanceGraph) :
    ∀ (a b : Label) (fuel : Nat), dominatesFuel g.edges a b fuel = true → dominates g a b := by
  intro a b fuel h
  induction fuel generalizing a b with
  | zero => simp [dominatesFuel] at h
  | succ fuel ih =>
    simp only [dominatesFuel] at h
    by_cases heq : a == b
    · exact beq_iff_eq.mp heq ▸ Dominates.refl b
    · rw [if_neg heq] at h
      rcases List.any_eq_true.mp h with ⟨p, hp, hstep⟩
      have ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hstep
      rcases p with ⟨src, mid⟩
      have ha : src = a := by simpa [beq_iff_eq] using h1
      subst ha
      exact Dominates.step hp (ih mid b h2)

theorem dominates_of_dominatesD (g : ClearanceGraph) {a b : Label}
    (h : dominatesD g a b = true) : dominates g a b := by
  unfold dominatesD at h
  exact dominates_of_dominatesFuel g a b (g.edges.length + 1) h

/-! ## Read checks. -/

/-- **`mayRead`** — an actor may access a compartment label when some held label dominates it. -/
def mayRead (g : ClearanceGraph) (actorLabels : List Label) (box : Label) : Bool :=
  actorLabels.any (fun a => dominatesD g a box)

/-- **`needsAll`** — conjunctive clearance: every required box label must be readable. -/
def needsAll (g : ClearanceGraph) (actorLabels : List Label) (required : List Label) : Bool :=
  required.all (fun box => mayRead g actorLabels box)

theorem mayRead_of_dominatesD (g : ClearanceGraph) (actorLabels : List Label) (a box : Label)
    (ha : a ∈ actorLabels) (hdom : dominatesD g a box = true) : mayRead g actorLabels box = true := by
  simp only [mayRead, List.any_eq_true]
  exact ⟨a, ha, hdom⟩

theorem needsAll_of_mayRead (g : ClearanceGraph) (actorLabels : List Label)
    (required : List Label) (h : ∀ box, box ∈ required → mayRead g actorLabels box = true) :
    needsAll g actorLabels required = true := by
  simp only [needsAll, List.all_eq_true]
  intro box hbox
  exact h box hbox

/-! ## Demo graph + non-vacuous guards. -/

/-- A tiny three-level clearance ladder: `top` ⊐ `mid` ⊐ `low`. -/
def demo : ClearanceGraph :=
  { edges :=
      [ (Label.named "top", Label.named "mid")
      , (Label.named "mid", Label.named "low") ] }

#guard dominatesD demo (Label.named "top") (Label.named "low")
#guard dominatesD demo (Label.named "low") (Label.named "top") == false
#guard mayRead demo [Label.named "mid"] (Label.named "low")
#guard needsAll demo [Label.named "top"] [Label.named "low", Label.named "mid"]
#guard needsAll demo [Label.named "mid"] [Label.named "top"] == false

#assert_axioms dominates_refl
#assert_axioms dominates_trans
#assert_axioms dominates_of_dominatesD

end Dregg2.Authority.ClearanceGraph