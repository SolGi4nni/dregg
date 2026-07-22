/-
# Dregg2.Logic.FiniteLogicPlan -- one finite Boolean denotation, two exact plans

This module is a small, self-contained denotational slice for the corrected
logic compiler.  Source truth is Boolean.  The ordinary lowering uses exact
Boolean primitives.  A second lowering is available for a conjunction of
equalities over bounded natural inputs: it adds nonnegative `Nat.dist`
residuals and performs one final zero test.

The additive lowering is deliberately narrow.  Its primitive law requires the
declared input bound, and its proof uses the zero-sum-free property of natural
numbers.  Nothing here interprets an arbitrary finite-field sum as
conjunction.

The interpreter is parametric in a carrier and a set of primitive operations.
`PrimitiveLaws` is the only assumption used by the refinement theorems.  A
transparent Boolean implementation proves those laws non-vacuously.  The cost
model is a vector: it keeps equality decisions, Boolean gates, residual
formation, additions, and the final zero decision separate.

Pure.  No axioms.
-/

import Mathlib.Data.Nat.Dist
import Mathlib.Data.List.Defs
import Mathlib.Tactic
import Dregg2.Tactics

namespace Dregg2.Logic.FiniteLogicPlan

set_option autoImplicit false

/-! ## 1. Backend-neutral finite source semantics -/

/-- A finite program environment.  The source language can name finitely many
indices even though representing the environment as a total function keeps
lookup semantics uncluttered. -/
abbrev Env := Nat → Nat

/-- Natural-valued source terms used by equality atoms. -/
inductive Term where
  | var : Nat → Term
  | lit : Nat → Term
  deriving DecidableEq, Repr

def Term.eval (env : Env) : Term → Nat
  | .var i => env i
  | .lit n => n

/-- A finite Boolean formula language.  `all` and `any` below are finite fold
constructors, so quantification is never implicit or unbounded. -/
inductive Formula where
  | top
  | bot
  | eq : Term → Term → Formula
  | not : Formula → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  deriving DecidableEq, Repr

def Formula.eval (env : Env) : Formula → Bool
  | .top => true
  | .bot => false
  | .eq lhs rhs => decide (lhs.eval env = rhs.eval env)
  | .not p => !(p.eval env)
  | .and p q => p.eval env && q.eval env
  | .or p q => p.eval env || q.eval env

/-- Optimized finite conjunction.  A singleton introduces no identity gate. -/
def Formula.all : List Formula → Formula
  | [] => .top
  | [p] => p
  | p :: q :: ps => .and p (Formula.all (q :: ps))
termination_by ps => ps.length

/-- Optimized finite disjunction.  A singleton introduces no identity gate. -/
def Formula.any : List Formula → Formula
  | [] => .bot
  | [p] => p
  | p :: q :: ps => .or p (Formula.any (q :: ps))
termination_by ps => ps.length

theorem Formula.eval_all (env : Env) (ps : List Formula) :
    (Formula.all ps).eval env = ps.all (Formula.eval env) := by
  induction ps with
  | nil => simp [Formula.all, Formula.eval]
  | cons p ps ih =>
      cases ps with
      | nil => simp [Formula.all]
      | cons q qs => simp [Formula.all, Formula.eval, ih]

theorem Formula.eval_any (env : Env) (ps : List Formula) :
    (Formula.any ps).eval env = ps.any (Formula.eval env) := by
  induction ps with
  | nil => simp [Formula.any, Formula.eval]
  | cons p ps ih =>
      cases ps with
      | nil => simp [Formula.any]
      | cons q qs => simp [Formula.any, Formula.eval, ih]

/-- A finite family of equality atoms. -/
def allEq (pairs : List (Term × Term)) : Formula :=
  Formula.all (pairs.map fun pair => .eq pair.1 pair.2)

/-- A finite family of equality alternatives. -/
def anyEq (pairs : List (Term × Term)) : Formula :=
  Formula.any (pairs.map fun pair => .eq pair.1 pair.2)

/-! ## 2. Plans, an abstract interpreter, and primitive laws -/

/-- The backend plan language.  `allEqResidual` is the only residual operation:
it represents one additive fold of nonnegative equality residuals followed by
one zero decision.  Every other connective remains Boolean. -/
inductive LogicPlan where
  | bit : Bool → LogicPlan
  | eq : Term → Term → LogicPlan
  | not : LogicPlan → LogicPlan
  | and : LogicPlan → LogicPlan → LogicPlan
  | or : LogicPlan → LogicPlan → LogicPlan
  | allEqResidual : (bound : Nat) → List (Term × Term) → LogicPlan
  deriving DecidableEq, Repr

/-- Backend primitives and the Boolean observation of their carrier. -/
structure PrimitiveOps (Carrier : Type*) where
  bit : Bool → Carrier
  eqNat : Nat → Nat → Carrier
  not : Carrier → Carrier
  and : Carrier → Carrier → Carrier
  or : Carrier → Carrier → Carrier
  allEqResidual : Nat → List (Nat × Nat) → Carrier
  observe : Carrier → Bool

/-- The public range premise required by the additive residual primitive. -/
def PairsBounded (bound : Nat) (pairs : List (Nat × Nat)) : Prop :=
  ∀ pair ∈ pairs, pair.1 ≤ bound ∧ pair.2 ≤ bound

/-- Exact observable laws for each backend primitive. -/
structure PrimitiveLaws {Carrier : Type*} (ops : PrimitiveOps Carrier) : Prop where
  observe_bit : ∀ b, ops.observe (ops.bit b) = b
  observe_eq : ∀ lhs rhs, ops.observe (ops.eqNat lhs rhs) = decide (lhs = rhs)
  observe_not : ∀ x, ops.observe (ops.not x) = !(ops.observe x)
  observe_and : ∀ x y, ops.observe (ops.and x y) = (ops.observe x && ops.observe y)
  observe_or : ∀ x y, ops.observe (ops.or x y) = (ops.observe x || ops.observe y)
  observe_allEqResidual : ∀ bound pairs, PairsBounded bound pairs →
    ops.observe (ops.allEqResidual bound pairs) =
      pairs.all fun pair => decide (pair.1 = pair.2)

def evalPairs (env : Env) (pairs : List (Term × Term)) : List (Nat × Nat) :=
  pairs.map fun pair => (pair.1.eval env, pair.2.eval env)

/-- Execute a plan using only the declared primitive interface. -/
def LogicPlan.run {Carrier : Type*} (ops : PrimitiveOps Carrier) (env : Env) :
    LogicPlan → Carrier
  | .bit b => ops.bit b
  | .eq lhs rhs => ops.eqNat (lhs.eval env) (rhs.eval env)
  | .not p => ops.not (p.run ops env)
  | .and p q => ops.and (p.run ops env) (q.run ops env)
  | .or p q => ops.or (p.run ops env) (q.run ops env)
  | .allEqResidual bound pairs => ops.allEqResidual bound (evalPairs env pairs)

/-- The total exact-Boolean lowering. -/
def lowerBool : Formula → LogicPlan
  | .top => .bit true
  | .bot => .bit false
  | .eq lhs rhs => .eq lhs rhs
  | .not p => .not (lowerBool p)
  | .and p q => .and (lowerBool p) (lowerBool q)
  | .or p q => .or (lowerBool p) (lowerBool q)

/-- The optimized additive lowering for a finite conjunction of equalities. -/
def lowerAllEqResidual (bound : Nat) (pairs : List (Term × Term)) : LogicPlan :=
  .allEqResidual bound pairs

/-- Bounds on the evaluated source terms, phrased exactly as the primitive law
expects them. -/
def TermsBounded (env : Env) (bound : Nat) (pairs : List (Term × Term)) : Prop :=
  PairsBounded bound (evalPairs env pairs)

theorem lowerBool_refines {Carrier : Type*} (ops : PrimitiveOps Carrier)
    (laws : PrimitiveLaws ops) (env : Env) (p : Formula) :
    ops.observe ((lowerBool p).run ops env) = p.eval env := by
  induction p with
  | top => exact laws.observe_bit true
  | bot => exact laws.observe_bit false
  | eq lhs rhs => exact laws.observe_eq (lhs.eval env) (rhs.eval env)
  | not p ih =>
      calc
        ops.observe ((lowerBool (Formula.not p)).run ops env) =
            !(ops.observe ((lowerBool p).run ops env)) :=
          laws.observe_not ((lowerBool p).run ops env)
        _ = (Formula.not p).eval env := by simp [Formula.eval, ih]
  | and p q ihp ihq =>
      calc
        ops.observe ((lowerBool (Formula.and p q)).run ops env) =
            (ops.observe ((lowerBool p).run ops env) &&
              ops.observe ((lowerBool q).run ops env)) :=
          laws.observe_and ((lowerBool p).run ops env) ((lowerBool q).run ops env)
        _ = (Formula.and p q).eval env := by simp [Formula.eval, ihp, ihq]
  | or p q ihp ihq =>
      calc
        ops.observe ((lowerBool (Formula.or p q)).run ops env) =
            (ops.observe ((lowerBool p).run ops env) ||
              ops.observe ((lowerBool q).run ops env)) :=
          laws.observe_or ((lowerBool p).run ops env) ((lowerBool q).run ops env)
        _ = (Formula.or p q).eval env := by simp [Formula.eval, ihp, ihq]

theorem eval_allEq (env : Env) (pairs : List (Term × Term)) :
    (allEq pairs).eval env =
      (evalPairs env pairs).all fun pair => decide (pair.1 = pair.2) := by
  rw [allEq, Formula.eval_all]
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
      rcases pair with ⟨lhs, rhs⟩
      simp [evalPairs, Formula.eval, ih]

theorem eval_anyEq (env : Env) (pairs : List (Term × Term)) :
    (anyEq pairs).eval env =
      (evalPairs env pairs).any fun pair => decide (pair.1 = pair.2) := by
  rw [anyEq, Formula.eval_any]
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
      rcases pair with ⟨lhs, rhs⟩
      simp [evalPairs, Formula.eval, ih]

/-- Semantic preservation of the additive fast path.  The range premise is
visible in the theorem and cannot be dropped by a backend. -/
theorem lowerAllEqResidual_refines {Carrier : Type*} (ops : PrimitiveOps Carrier)
    (laws : PrimitiveLaws ops) (env : Env) (bound : Nat)
    (pairs : List (Term × Term)) (hbound : TermsBounded env bound pairs) :
    ops.observe ((lowerAllEqResidual bound pairs).run ops env) =
      (allEq pairs).eval env := by
  rw [lowerAllEqResidual, LogicPlan.run,
    laws.observe_allEqResidual bound (evalPairs env pairs) hbound]
  exact (eval_allEq env pairs).symm

/-! ## 3. A transparent implementation of the primitive laws -/

/-- Nonnegative natural equality residual. -/
def eqResidual (pair : Nat × Nat) : Nat := Nat.dist pair.1 pair.2

/-- The actual additive fold performed by the residual primitive. -/
def residualSum (pairs : List (Nat × Nat)) : Nat :=
  (pairs.map eqResidual).sum

theorem eqResidual_eq_zero_iff (pair : Nat × Nat) :
    eqResidual pair = 0 ↔ pair.1 = pair.2 := by
  rcases pair with ⟨lhs, rhs⟩
  constructor
  · exact Nat.eq_of_dist_eq_zero
  · exact Nat.dist_eq_zero

theorem residualSum_eq_zero_iff (pairs : List (Nat × Nat)) :
    residualSum pairs = 0 ↔ ∀ pair ∈ pairs, pair.1 = pair.2 := by
  induction pairs with
  | nil => simp [residualSum]
  | cons pair pairs ih =>
      change eqResidual pair + residualSum pairs = 0 ↔
        ∀ candidate ∈ pair :: pairs, candidate.1 = candidate.2
      rw [Nat.add_eq_zero_iff, eqResidual_eq_zero_iff, ih]
      simp

theorem decide_residualSum_eq_zero (pairs : List (Nat × Nat)) :
    decide (residualSum pairs = 0) =
      pairs.all fun pair => decide (pair.1 = pair.2) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, List.all_eq_true]
  exact residualSum_eq_zero_iff pairs

def withinBound (bound : Nat) (pairs : List (Nat × Nat)) : Bool :=
  pairs.all fun pair => decide (pair.1 ≤ bound ∧ pair.2 ≤ bound)

/-- Concrete additive implementation: validate the declared ranges, add all
nonnegative distances, then test the aggregate once. -/
def transparentAllEqResidual (bound : Nat) (pairs : List (Nat × Nat)) : Bool :=
  withinBound bound pairs && decide (residualSum pairs = 0)

def transparentOps : PrimitiveOps Bool where
  bit := id
  eqNat := fun lhs rhs => decide (lhs = rhs)
  not := Bool.not
  and := Bool.and
  or := Bool.or
  allEqResidual := transparentAllEqResidual
  observe := id

theorem withinBound_eq_true {bound : Nat} {pairs : List (Nat × Nat)}
    (hbound : PairsBounded bound pairs) : withinBound bound pairs = true := by
  rw [withinBound, List.all_eq_true]
  intro pair hpair
  exact decide_eq_true (hbound pair hpair)

/-- The abstract primitive specification has a concrete model. -/
theorem transparentPrimitiveLaws : PrimitiveLaws transparentOps := by
  constructor
  · intro b; rfl
  · intro lhs rhs; rfl
  · intro x; rfl
  · intro x y; rfl
  · intro x y; rfl
  · intro bound pairs hbound
    simp only [transparentOps, transparentAllEqResidual, id_eq]
    rw [withinBound_eq_true hbound, Bool.true_and, decide_residualSum_eq_zero]

/-! ## 4. Vector-valued exact costs -/

/-- Symbolic work counts.  These axes are intentionally not collapsed into a
single context-free score. -/
structure Cost where
  eqTests : Nat := 0
  boolNots : Nat := 0
  boolAnds : Nat := 0
  boolOrs : Nat := 0
  residualEvals : Nat := 0
  additions : Nat := 0
  zeroTests : Nat := 0
  deriving DecidableEq, Repr

namespace Cost

/-- Costs are equal exactly when all seven independent axes are equal. -/
@[ext]
theorem ext (lhs rhs : Cost)
    (heqTests : lhs.eqTests = rhs.eqTests)
    (hboolNots : lhs.boolNots = rhs.boolNots)
    (hboolAnds : lhs.boolAnds = rhs.boolAnds)
    (hboolOrs : lhs.boolOrs = rhs.boolOrs)
    (hresidualEvals : lhs.residualEvals = rhs.residualEvals)
    (hadditions : lhs.additions = rhs.additions)
    (hzeroTests : lhs.zeroTests = rhs.zeroTests) : lhs = rhs := by
  cases lhs
  cases rhs
  simp_all

protected def add (lhs rhs : Cost) : Cost where
  eqTests := lhs.eqTests + rhs.eqTests
  boolNots := lhs.boolNots + rhs.boolNots
  boolAnds := lhs.boolAnds + rhs.boolAnds
  boolOrs := lhs.boolOrs + rhs.boolOrs
  residualEvals := lhs.residualEvals + rhs.residualEvals
  additions := lhs.additions + rhs.additions
  zeroTests := lhs.zeroTests + rhs.zeroTests

instance instAddCost : Add Cost := ⟨Cost.add⟩

@[simp] theorem add_eqTests (lhs rhs : Cost) :
    (lhs + rhs).eqTests = lhs.eqTests + rhs.eqTests := rfl

@[simp] theorem add_boolNots (lhs rhs : Cost) :
    (lhs + rhs).boolNots = lhs.boolNots + rhs.boolNots := rfl

@[simp] theorem add_boolAnds (lhs rhs : Cost) :
    (lhs + rhs).boolAnds = lhs.boolAnds + rhs.boolAnds := rfl

@[simp] theorem add_boolOrs (lhs rhs : Cost) :
    (lhs + rhs).boolOrs = lhs.boolOrs + rhs.boolOrs := rfl

@[simp] theorem add_residualEvals (lhs rhs : Cost) :
    (lhs + rhs).residualEvals = lhs.residualEvals + rhs.residualEvals := rfl

@[simp] theorem add_additions (lhs rhs : Cost) :
    (lhs + rhs).additions = lhs.additions + rhs.additions := rfl

@[simp] theorem add_zeroTests (lhs rhs : Cost) :
    (lhs + rhs).zeroTests = lhs.zeroTests + rhs.zeroTests := rfl

def eqOne : Cost := { eqTests := 1 }
def notOne : Cost := { boolNots := 1 }
def andOne : Cost := { boolAnds := 1 }
def orOne : Cost := { boolOrs := 1 }

def residualFold (n : Nat) : Cost where
  residualEvals := n
  additions := n - 1
  zeroTests := 1

end Cost

/-- Exact compositional cost of a plan. -/
def LogicPlan.cost : LogicPlan → Cost
  | .bit _ => {}
  | .eq _ _ => Cost.eqOne
  | .not p => p.cost + Cost.notOne
  | .and p q => p.cost + q.cost + Cost.andOne
  | .or p q => p.cost + q.cost + Cost.orOne
  | .allEqResidual _ pairs => Cost.residualFold pairs.length

def boolAllEqCost (n : Nat) : Cost where
  eqTests := n
  boolAnds := n - 1

def boolAnyEqCost (n : Nat) : Cost where
  eqTests := n
  boolOrs := n - 1

theorem lowerBool_allEq_cost (pairs : List (Term × Term)) :
    (lowerBool (allEq pairs)).cost = boolAllEqCost pairs.length := by
  induction pairs with
  | nil => simp [allEq, Formula.all, lowerBool, LogicPlan.cost, boolAllEqCost]
  | cons pair pairs ih =>
      cases pairs with
      | nil => simp [allEq, Formula.all, lowerBool, LogicPlan.cost, boolAllEqCost,
          Cost.eqOne]
      | cons next rest =>
          simp only [allEq, List.map_cons, Formula.all, lowerBool, LogicPlan.cost]
          change Cost.eqOne + (lowerBool (allEq (next :: rest))).cost +
              Cost.andOne = boolAllEqCost (pair :: next :: rest).length
          rw [ih]
          rcases pair with ⟨lhs, rhs⟩
          ext <;>
            simp [boolAllEqCost, Cost.eqOne, Cost.andOne]
          all_goals omega

theorem lowerBool_anyEq_cost (pairs : List (Term × Term)) :
    (lowerBool (anyEq pairs)).cost = boolAnyEqCost pairs.length := by
  induction pairs with
  | nil => simp [anyEq, Formula.any, lowerBool, LogicPlan.cost, boolAnyEqCost]
  | cons pair pairs ih =>
      cases pairs with
      | nil => simp [anyEq, Formula.any, lowerBool, LogicPlan.cost, boolAnyEqCost,
          Cost.eqOne]
      | cons next rest =>
          simp only [anyEq, List.map_cons, Formula.any, lowerBool, LogicPlan.cost]
          change Cost.eqOne + (lowerBool (anyEq (next :: rest))).cost +
              Cost.orOne = boolAnyEqCost (pair :: next :: rest).length
          rw [ih]
          rcases pair with ⟨lhs, rhs⟩
          ext <;>
            simp [boolAnyEqCost, Cost.eqOne, Cost.orOne]
          all_goals omega

theorem lowerAllEqResidual_cost (bound : Nat) (pairs : List (Term × Term)) :
    (lowerAllEqResidual bound pairs).cost = Cost.residualFold pairs.length := rfl

/-! ## 5. Three-element all/any equality examples -/

def threeAgainstFive : List (Term × Term) :=
  [(.var 0, .lit 5), (.var 1, .lit 5), (.var 2, .lit 5)]

def allIsFive : Formula := allEq threeAgainstFive
def anyIsFive : Formula := anyEq threeAgainstFive
def allIsFiveResidual (bound : Nat) : LogicPlan :=
  lowerAllEqResidual bound threeAgainstFive

def allFiveEnv : Env
  | 0 | 1 | 2 => 5
  | _ => 0

def oneFiveEnv : Env
  | 0 => 5
  | 1 => 8
  | 2 => 9
  | _ => 0

#guard allIsFive.eval allFiveEnv == true
#guard allIsFive.eval oneFiveEnv == false
#guard anyIsFive.eval oneFiveEnv == true
#guard (allIsFiveResidual 10).run transparentOps allFiveEnv == true
#guard (allIsFiveResidual 10).run transparentOps oneFiveEnv == false

theorem allFive_terms_bounded : TermsBounded allFiveEnv 10 threeAgainstFive := by
  simp [TermsBounded, PairsBounded, evalPairs, threeAgainstFive, allFiveEnv,
    Term.eval]

theorem oneFive_terms_bounded : TermsBounded oneFiveEnv 10 threeAgainstFive := by
  simp [TermsBounded, PairsBounded, evalPairs, threeAgainstFive, oneFiveEnv,
    Term.eval]

theorem allIsFive_residual_refines_allFive :
    (allIsFiveResidual 10).run transparentOps allFiveEnv = allIsFive.eval allFiveEnv := by
  exact lowerAllEqResidual_refines transparentOps transparentPrimitiveLaws
    allFiveEnv 10 threeAgainstFive allFive_terms_bounded

theorem allIsFive_residual_refines_oneFive :
    (allIsFiveResidual 10).run transparentOps oneFiveEnv = allIsFive.eval oneFiveEnv := by
  exact lowerAllEqResidual_refines transparentOps transparentPrimitiveLaws
    oneFiveEnv 10 threeAgainstFive oneFive_terms_bounded

theorem allIsFive_boolean_cost :
    (lowerBool allIsFive).cost =
      { eqTests := 3, boolAnds := 2 : Cost } := by
  rw [allIsFive, lowerBool_allEq_cost]
  rfl

theorem anyIsFive_boolean_cost :
    (lowerBool anyIsFive).cost =
      { eqTests := 3, boolOrs := 2 : Cost } := by
  rw [anyIsFive, lowerBool_anyEq_cost]
  rfl

theorem allIsFive_residual_cost :
    (allIsFiveResidual 10).cost =
      { residualEvals := 3, additions := 2, zeroTests := 1 : Cost } := by decide

/-! ### Axiom hygiene -/

#assert_axioms Formula.eval_all
#assert_axioms Formula.eval_any
#assert_axioms lowerBool_refines
#assert_axioms eval_allEq
#assert_axioms eval_anyEq
#assert_axioms lowerAllEqResidual_refines
#assert_axioms eqResidual_eq_zero_iff
#assert_axioms residualSum_eq_zero_iff
#assert_axioms decide_residualSum_eq_zero
#assert_axioms transparentPrimitiveLaws
#assert_axioms lowerBool_allEq_cost
#assert_axioms lowerBool_anyEq_cost
#assert_axioms lowerAllEqResidual_cost
#assert_axioms allIsFive_residual_refines_allFive
#assert_axioms allIsFive_residual_refines_oneFive
#assert_axioms allIsFive_boolean_cost
#assert_axioms anyIsFive_boolean_cost
#assert_axioms allIsFive_residual_cost

end Dregg2.Logic.FiniteLogicPlan
