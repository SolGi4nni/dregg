/-
# Metatheory.PolisDatalog — a REAL derivation closure (forward-chaining Datalog), not a 2-fact stub.

dregg's theory of knowledge coordination IS the derivation circuit (biscuit's Datalog). The polis's
`Discharged`/`Reaches` were grounded on a two-fact stand-in — a toy. This file gives the genuine
object: a forward-chaining Datalog engine (`facts` + `rules` ⊢ `goal` via the least-fixpoint
consequence closure), decidable, and *multi-step* — a goal derived through a CHAIN of rules, not a
single check. Viability/knowledge then = real derivability:

  * `Derivable rules facts goal` — the goal is in the consequence closure (it can be DERIVED).
  * **multi-step**: a goal reached through `a ← b ← c` is derivable though it is no direct fact.
  * **coalition**: a rule whose body needs facts from several agents is derivable only by POOLING
    their facts — neither alone suffices.
  * **equivocation**: a goal NOT in the closure cannot be claimed — you can't derive what doesn't
    follow.

This is the engine the polis viability (`KnowReaches`) and the cross-vat discharge gate should both
be — one derivation object. (Ground atoms are `Nat` here for a runnable, `decide`-checked engine; the
engine is generic in the rule-base.)
-/

namespace Metatheory.PolisDatalog

/-- A ground atom (a derivable fact). -/
abbrev Atom := Nat

/-- A Datalog rule: `head` holds if every atom in `body` is derivable. -/
structure Rule where
  head : Atom
  body : List Atom
deriving Repr, DecidableEq

/-- One round of forward chaining: add the head of every rule whose whole body is already known. -/
def fire (rules : List Rule) (known : List Atom) : List Atom :=
  known ++ (rules.filter (fun r => r.body.all (fun a => known.contains a))).map (·.head)

/-- The `k`-round consequence set from `facts` under `rules`. The (bounded) derivation closure. -/
def deriveWithin (rules : List Rule) (facts : List Atom) : Nat → List Atom
  | 0 => facts
  | k + 1 => fire rules (deriveWithin rules facts k)

/-- **The goal is derivable within `k` rounds.** Decidable. -/
def Derivable (rules : List Rule) (facts : List Atom) (goal : Atom) (k : Nat) : Prop :=
  goal ∈ deriveWithin rules facts k

instance (rules) (facts) (goal) (k) : Decidable (Derivable rules facts goal k) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- A round only ADDS atoms: the closure is monotone in the round budget. -/
theorem fire_superset (rules : List Rule) (known : List Atom) (a : Atom) (h : a ∈ known) :
    a ∈ fire rules known := by
  unfold fire; exact List.mem_append_left _ h

theorem deriveWithin_mono (rules : List Rule) (facts : List Atom) (k : Nat) (a : Atom)
    (h : a ∈ deriveWithin rules facts k) : a ∈ deriveWithin rules facts (k + 1) := by
  cases k with
  | zero => exact fire_superset rules facts a h
  | succ j => exact fire_superset rules _ a h

/-! ## A concrete rule-base: real multi-step derivation. -/

/-- Atoms: `c=2 → b=1 → a=0` is a derivation chain; `goal=10` needs the coalition facts `3` and `4`. -/
def chainRules : List Rule :=
  [⟨0, [1]⟩,        -- a ← b
   ⟨1, [2]⟩,        -- b ← c
   ⟨10, [3, 4]⟩]    -- goal ← factX ∧ factY  (a conjunctive / coalition rule)

/-- **Multi-step derivation**: from the single fact `c=2`, the engine derives `a=0` through the chain
`a ← b ← c` — `a` is NOT a fact, it is *derived* over two rounds. -/
theorem multi_step_derivation : Derivable chainRules [2] 0 2 := by decide

/-- One round is not enough — `a` needs the full chain (genuine multi-step, not a one-shot check). -/
theorem one_step_insufficient : ¬ Derivable chainRules [2] 0 1 := by decide

/-! ## Coalition: pooling facts derives what neither agent can alone. -/

/-- Agent X knows `factX = 3`; agent Y knows `factY = 4`. -/
def factsX : List Atom := [3]
def factsY : List Atom := [4]

/-- **Coalition** — the pooled facts `X ∪ Y` derive `goal=10` (the conjunctive rule fires). -/
theorem coalition_derives : Derivable chainRules (factsX ++ factsY) 10 1 := by decide
/-- Neither agent's facts alone derive the goal (the body is not fully known). -/
theorem X_alone_cannot : ¬ Derivable chainRules factsX 10 5 := by decide
theorem Y_alone_cannot : ¬ Derivable chainRules factsY 10 5 := by decide

/-! ## Equivocation: you cannot claim a goal that does not follow. -/

/-- **Equivocation refused** — `goal=10` is NOT derivable from `X`'s facts (no closure round adds it),
so X cannot honestly claim it. You can only derive what follows. -/
theorem equivocation_underivable : ¬ Derivable chainRules factsX 10 5 := X_alone_cannot

/-! ## Viability/knowledge = real derivability. -/

/-- **Knowledge-viability** for a goal: the goal is *derivable* (within `k`) from the agent's facts
under the rule-base — the real consequence closure, not a single discharge check. This is what the
polis `Reaches`/`Discharged` should be: derivability in the actual Datalog engine. -/
def KnowReaches (rules : List Rule) (facts : List Atom) (goal : Atom) (k : Nat) : Prop :=
  Derivable rules facts goal k

/-- A coalition keeps a goal viable (derivable) even where a single agent's knowledge cannot —
knowledge coordination as a viability path, over the genuine derivation closure. -/
theorem coalition_restores_viability :
    KnowReaches chainRules (factsX ++ factsY) 10 1 ∧ ¬ KnowReaches chainRules factsX 10 5 :=
  ⟨coalition_derives, X_alone_cannot⟩

-- Watch the engine run (the consequence closure, kernel-evaluated):
#eval deriveWithin chainRules [2] 2          -- [2, 1, 0, ...] — c, then b, then a (the chain)
#eval decide (Derivable chainRules [2] 0 2)  -- true  (a derived via a ← b ← c)
#eval decide (Derivable chainRules factsX 10 5)            -- false (X alone cannot)
#eval decide (Derivable chainRules (factsX ++ factsY) 10 1) -- true  (coalition derives the goal)

end Metatheory.PolisDatalog
