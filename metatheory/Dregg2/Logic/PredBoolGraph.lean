/-
# Dregg2.Logic.PredBoolGraph -- exact Boolean-graph lowering for live predicates

This module connects the live `Exec.PredAlgebra.Pred` policy language to the
field-generic, sound Boolean constraint graph in `Logic.BoolGraph`.  It does not
invent another policy language: `PredAtom` is only a reified view of every
non-connective `Pred` constructor, and `lower` preserves every Boolean/list
constructor structurally.

Concrete atom gadgets are deliberately separated from the Boolean theorem.
An `AtomPlan` supplies one field residual per reified leaf and proves that the
residual vanishes exactly when the existing executable leaf evaluator returns
`true`.  Under that premise, the full lowered graph accepts exactly when the
original live predicate evaluator accepts.  Thus future atom gadgets cannot
silently change `not`, `allOf`, or `anyOf` semantics, and no finite-field
zero-sum convention is used for Boolean connectives.
-/

import Dregg2.Exec.PredAlgebra
import Dregg2.Logic.BoolGraph

namespace Dregg2.Logic.PredBoolGraph

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra

open Dregg2.Logic.BoolGraph

/-! ## A complete reified view of `Pred` leaves -/

/-- Every non-connective constructor of `Pred`, with no duplicate evaluation
semantics.  The `.constraint` case contains the full `StateConstraint` catalog;
the remaining cases are precisely the typed symbol/digest/value leaves added by
`PredAlgebra` itself. -/
inductive PredAtom where
  | constraint (c : StateConstraint)
  | symEq (f : FieldName) (s : Nat)
  | symMemberOf (f : FieldName) (set : List Nat)
  | digEq (f : FieldName) (d : Nat)
  | digFieldEq (f g : FieldName)
  | fieldEqField (f g : FieldName)
  | symUnchanged (f : FieldName)
  | symChanged (f : FieldName)
  | digUnchanged (f : FieldName)
  | digChanged (f : FieldName)
  deriving Repr

/-- The leaf view delegates to exactly the same executable operations as
`Pred.eval`.  This definition is intentionally Boolean: it is the specification
against which a field residual gadget must be proved. -/
def PredAtom.eval : PredAtom → Value → Value → Bool
  | .constraint c,      o, n => evalConstraint c o n
  | .symEq f s,         _, n => n.symField f == some s
  | .symMemberOf f set, _, n => match n.symField f with
                                | some x => set.contains x
                                | none => false
  | .digEq f d,         _, n => n.digField f == some d
  | .digFieldEq f g,    _, n => match n.digField f, n.digField g with
                                | some a, some b => a == b
                                | _, _ => false
  | .fieldEqField f g,  _, n => match n.field f, n.field g with
                                | some a, some b => Value.beq a b
                                | _, _ => false
  | .symUnchanged f,    o, n => match o.symField f with
                                | none => true
                                | some a => n.symField f == some a
  | .symChanged f,      o, n => match o.symField f, n.symField f with
                                | some a, some b => !(a == b)
                                | _, _ => false
  | .digUnchanged f,    o, n => match o.digField f with
                                | none => true
                                | some a => n.digField f == some a
  | .digChanged f,      o, n => match o.digField f, n.digField f with
                                | some a, some b => !(a == b)
                                | _, _ => false

/-! ## Structural lowering (including exact list folds) -/

mutual
/-- Lower a live predicate to the corrected one-means-true Boolean graph source.
`allOf` and `anyOf` lower to binary gate chains, never to a field sum/product
whose zero set changes with the characteristic. -/
def lower : Pred → Formula PredAtom
  | .atom c          => .atom (.constraint c)
  | .tt              => .top
  | .ff              => .bot
  | .and p q         => .and (lower p) (lower q)
  | .or p q          => .or (lower p) (lower q)
  | .not p           => .not (lower p)
  | .allOf ps        => lowerAll ps
  | .anyOf ps        => lowerAny ps
  | .symEq f s       => .atom (.symEq f s)
  | .symMemberOf f s => .atom (.symMemberOf f s)
  | .digEq f d       => .atom (.digEq f d)
  | .digFieldEq f g  => .atom (.digFieldEq f g)
  | .fieldEqField f g => .atom (.fieldEqField f g)
  | .symUnchanged f  => .atom (.symUnchanged f)
  | .symChanged f    => .atom (.symChanged f)
  | .digUnchanged f  => .atom (.digUnchanged f)
  | .digChanged f    => .atom (.digChanged f)
/-- The empty conjunction is top, matching `Pred.evalAll [] = true`. -/
def lowerAll : List Pred → Formula PredAtom
  | []      => .top
  | p :: ps => .and (lower p) (lowerAll ps)
/-- The empty disjunction is bottom, matching `Pred.evalAny [] = false`. -/
def lowerAny : List Pred → Formula PredAtom
  | []      => .bot
  | p :: ps => .or (lower p) (lowerAny ps)
end

/-! ## Atom plans and the fundamental preservation theorem -/

variable {F : Type*} [Field F]

/-- A concrete lowering plan for leaves at one transition.  It may contain any
field representation/gadget design, but must discharge the only semantic
obligation the Boolean compiler needs: zero residual iff the existing leaf
evaluator is true. -/
structure AtomPlan (F : Type*) [Field F] (old new : Value) where
  residual : PredAtom → F
  exact : ∀ a, residual a = 0 ↔ a.eval old new = true

mutual
/-- Fundamental theorem: the structural lowering has exactly the live
`Pred.eval` truth value, assuming only exactness of each concrete atom gadget. -/
theorem lower_eval_iff {old new : Value} (plan : AtomPlan F old new) (p : Pred) :
    Eval plan.residual (lower p) ↔ p.eval old new = true := by
  cases p with
  | atom c => exact plan.exact (.constraint c)
  | tt => simp [lower, Eval, Pred.eval]
  | ff => simp [lower, Eval, Pred.eval]
  | and p q =>
      simp only [lower, Eval, Pred.eval, Bool.and_eq_true]
      rw [lower_eval_iff plan p, lower_eval_iff plan q]
  | or p q =>
      simp only [lower, Eval, Pred.eval, Bool.or_eq_true]
      rw [lower_eval_iff plan p, lower_eval_iff plan q]
  | not p =>
      change (¬ Eval plan.residual (lower p)) ↔ (!p.eval old new) = true
      simpa using not_congr (lower_eval_iff plan p)
  | allOf ps => exact lowerAll_eval_iff plan ps
  | anyOf ps => exact lowerAny_eval_iff plan ps
  | symEq f s => exact plan.exact (.symEq f s)
  | symMemberOf f set => exact plan.exact (.symMemberOf f set)
  | digEq f d => exact plan.exact (.digEq f d)
  | digFieldEq f g => exact plan.exact (.digFieldEq f g)
  | fieldEqField f g => exact plan.exact (.fieldEqField f g)
  | symUnchanged f => exact plan.exact (.symUnchanged f)
  | symChanged f => exact plan.exact (.symChanged f)
  | digUnchanged f => exact plan.exact (.digUnchanged f)
  | digChanged f => exact plan.exact (.digChanged f)
/-- Exact preservation for an `allOf` gate chain, including the empty case. -/
theorem lowerAll_eval_iff {old new : Value} (plan : AtomPlan F old new) (ps : List Pred) :
    Eval plan.residual (lowerAll ps) ↔ Pred.evalAll ps old new = true := by
  cases ps with
  | nil => simp [lowerAll, Eval, Pred.evalAll]
  | cons p ps =>
      simp only [lowerAll, Eval, Pred.evalAll, Bool.and_eq_true]
      rw [lower_eval_iff plan p, lowerAll_eval_iff plan ps]
/-- Exact preservation for an `anyOf` gate chain, including the empty case. -/
theorem lowerAny_eval_iff {old new : Value} (plan : AtomPlan F old new) (ps : List Pred) :
    Eval plan.residual (lowerAny ps) ↔ Pred.evalAny ps old new = true := by
  cases ps with
  | nil => simp [lowerAny, Eval, Pred.evalAny]
  | cons p ps =>
      simp only [lowerAny, Eval, Pred.evalAny, Bool.or_eq_true]
      rw [lower_eval_iff plan p, lowerAny_eval_iff plan ps]
end

/-! ## Exact compiled acceptance -/

/-- A satisfying lowered graph exposes output one exactly when the live
predicate evaluator returns true.  This strengthens mere acceptance equivalence
by applying to every satisfying graph assignment. -/
theorem graph_output_one_iff {old new : Value} (plan : AtomPlan F old new) (p : Pred)
    {out : F} (hgraph : Graph plan.residual (lower p) out) :
    out = 1 ↔ p.eval old new = true :=
  (graph_sound hgraph).2.trans (lower_eval_iff plan p)

/-- Main bridge theorem: corrected field-graph acceptance is exactly the
existing executable `Pred` decision, for every field and every atom plan that
proves its residuals faithful. -/
theorem accepts_lower_iff {old new : Value} (plan : AtomPlan F old new) (p : Pred) :
    Accepts plan.residual (lower p) ↔ p.eval old new = true :=
  (compile_exact plan.residual (lower p)).trans (lower_eval_iff plan p)

/-- Totality of the Boolean layer: once residuals are supplied, a satisfying
graph assignment exists independently of whether the predicate accepts. -/
theorem lower_graph_complete {old new : Value} (plan : AtomPlan F old new) (p : Pred) :
    ∃ out, Graph plan.residual (lower p) out :=
  graph_complete plan.residual (lower p)

#assert_all_clean [
  lower_eval_iff,
  lowerAll_eval_iff,
  lowerAny_eval_iff,
  graph_output_one_iff,
  accepts_lower_iff,
  lower_graph_complete
]

end Dregg2.Logic.PredBoolGraph
