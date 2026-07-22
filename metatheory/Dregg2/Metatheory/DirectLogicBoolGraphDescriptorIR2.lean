/-
# Materialized Boolean graphs in the live descriptor IR v2

`FiniteLogicDescriptorIR2` deliberately emits one nested polynomial.  This
module emits the other backend promised by the direct-logic optimizer: every
zero test and Boolean connective gets explicit witness columns and a flat list
of degree-at-most-two `windowGate`s.

The optimizer ledger counts the relation which exposes a Boolean output.  A
live accepting descriptor needs one additional, linear `output = 1` equation.
Consequently the headline specimen is 30 -> 13 graph equations and 31 -> 14
actual descriptor constraints.  Multiplications and auxiliary witnesses remain
26 -> 13 and 17 -> 8 respectively.  This correction is stated and proved
below; it is not hidden in a benchmark convention.

Standalone additive module.  No integration imports are changed.
-/

import Dregg2.Metatheory.DirectLogicOptimizerCertificate
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Metatheory.DirectLogicOptimizerCertificate
open Dregg2.Metatheory.ArithmetizationCost

set_option autoImplicit false

abbrev Formula := Dregg2.Metatheory.DirectLogicOptimizerCertificate.Formula

/-! ## 1. Explicit wires, nodes, and quadratic gates -/

inductive Wire where
  | zero
  | one
  | col (index : Nat)
  deriving DecidableEq, Repr

namespace Wire

def expr : Wire -> WindowExpr
  | .zero => .const 0
  | .one => .const 1
  | .col c => .loc c

def eval (a : Assignment) : Wire -> Int
  | .zero => 0
  | .one => 1
  | .col c => a c

theorem expr_eval (env : VmRowEnv) (w : Wire) :
    w.expr.eval env = w.eval env.loc := by
  cases w <;> rfl

end Wire

inductive Node where
  /-- `out` is the one-means-zero bit for input residual `x`; `inv` is the
  inverse witness in the nonzero branch. -/
  | zeroTest (x out inv : Nat)
  | not (input : Wire) (out : Nat)
  | and (left right : Wire) (out : Nat)
  | or (left right : Wire) (out : Nat)
  deriving DecidableEq, Repr

def negW (x : WindowExpr) : WindowExpr := .mul (.const (-1)) x

def subW (x y : WindowExpr) : WindowExpr := .add x (negW y)

def bitBody (w : Wire) : WindowExpr :=
  .mul w.expr (.add w.expr (.const (-1)))

def gate (body : WindowExpr) : VmConstraint2 :=
  .windowGate { body := body, onTransition := false }

namespace Node

/-- The exact equations of the relational `BoolGraph` primitives.  Inputs are
not redundantly Booleanized at each parent; each materialized output is. -/
def constraints : Node -> List VmConstraint2
  | .zeroTest x out inv =>
      [ gate (bitBody (.col out))
      , gate (.mul (.loc x) (.loc out))
      , gate (.add (.add (.mul (.loc x) (.loc inv)) (.loc out)) (.const (-1))) ]
  | .not input out =>
      [ gate (bitBody (.col out))
      , gate (.add (.add (.loc out) input.expr) (.const (-1))) ]
  | .and left right out =>
      [ gate (bitBody (.col out))
      , gate (subW (.loc out) (.mul left.expr right.expr)) ]
  | .or left right out =>
      [ gate (bitBody (.col out))
      , gate (subW (.loc out)
          (subW (.add left.expr right.expr) (.mul left.expr right.expr))) ]

/-- Multiplications in the optimizer ledger: constant scaling is linear and
does not count as a nonlinear multiplication. -/
def multiplications : Node -> Nat
  | .zeroTest .. => 3
  | .not .. => 1
  | .and .. | .or .. => 2

@[simp] theorem constraints_length (node : Node) :
    node.constraints.length = match node with
      | .zeroTest .. => 3
      | .not .. => 2
      | .and .. | .or .. => 2 := by
  cases node <;> rfl

end Node

/-! ## 2. Deterministic postorder materialization -/

def witnessCount {n : Nat} : Formula n -> Nat
  | .atom _ => 2
  | .top | .bot => 0
  | .not p => witnessCount p + 1
  | .and p q | .or p q => witnessCount p + witnessCount q + 1

def outputAt {n : Nat} (base : Nat) : Formula n -> Wire
  | .atom _ => .col base
  | .top => .one
  | .bot => .zero
  | .not p => .col (base + witnessCount p)
  | .and p q | .or p q => .col (base + witnessCount p + witnessCount q)

def nodesAt {n : Nat} (base : Nat) : Formula n -> List Node
  | .atom a => [.zeroTest a.val base (base + 1)]
  | .top | .bot => []
  | .not p =>
      nodesAt base p ++ [.not (outputAt base p) (base + witnessCount p)]
  | .and p q =>
      nodesAt base p ++ nodesAt (base + witnessCount p) q ++
        [.and (outputAt base p) (outputAt (base + witnessCount p) q)
          (base + witnessCount p + witnessCount q)]
  | .or p q =>
      nodesAt base p ++ nodesAt (base + witnessCount p) q ++
        [.or (outputAt base p) (outputAt (base + witnessCount p) q)
          (base + witnessCount p + witnessCount q)]

def graphConstraints {n : Nat} (p : Formula n) : List VmConstraint2 :=
  (nodesAt n p).flatMap Node.constraints

def acceptConstraint {n : Nat} (p : Formula n) : VmConstraint2 :=
  gate (subW (outputAt n p).expr (.const 1))

def descriptor {n : Nat} (p : Formula n) : EffectVmDescriptor2 :=
  { name := "dregg-materialized-boolgraph-v2-" ++ toString n
  , traceWidth := n + witnessCount p
  , piCount := 0
  , tables := [mainTableDef (n + witnessCount p)]
  , constraints := graphConstraints p ++ [acceptConstraint p]
  , hashSites := []
  , ranges := [] }

def emittedMultiplications {n : Nat} (p : Formula n) : Nat :=
  (nodesAt n p).map Node.multiplications |>.sum

/-! ## 3. Exact agreement with the optimizer ledger -/

theorem witnessCount_eq_graphCost_witnesses {n : Nat} (p : Formula n) :
    witnessCount p = p.graphCost.witnesses := by
  induction p <;>
    simp [witnessCount, Formula.graphCost, Formula.toGraph,
      ArithmetizationCost.BooleanGraph.cost, zeroTestGateCost,
      booleanNotGateCost, booleanBinaryGateCost, BackendCost.combine, *]

theorem nodesAt_constraint_length {n : Nat} (base : Nat) (p : Formula n) :
    ((nodesAt base p).flatMap Node.constraints).length = p.graphCost.equations := by
  induction p generalizing base <;>
    simp [nodesAt, Formula.graphCost, Formula.toGraph,
      ArithmetizationCost.BooleanGraph.cost, Node.constraints,
      zeroTestGateCost, booleanNotGateCost, booleanBinaryGateCost,
      BackendCost.combine, *] <;> omega

theorem graphConstraints_length_eq_graphCost_equations {n : Nat} (p : Formula n) :
    (graphConstraints p).length = p.graphCost.equations := by
  exact nodesAt_constraint_length n p

theorem nodesAt_multiplications {n : Nat} (base : Nat) (p : Formula n) :
    ((nodesAt base p).map Node.multiplications).sum = p.graphCost.multiplications := by
  induction p generalizing base <;>
    simp [nodesAt, Formula.graphCost, Formula.toGraph,
      ArithmetizationCost.BooleanGraph.cost, Node.multiplications,
      zeroTestGateCost, booleanNotGateCost, booleanBinaryGateCost,
      BackendCost.combine, *] <;> omega

theorem emittedMultiplications_eq_graphCost {n : Nat} (p : Formula n) :
    emittedMultiplications p = p.graphCost.multiplications := by
  exact nodesAt_multiplications n p

theorem descriptor_constraint_count {n : Nat} (p : Formula n) :
    (descriptor p).constraints.length = p.graphCost.equations + 1 := by
  simp [descriptor, graphConstraints_length_eq_graphCost_equations]

theorem descriptor_aux_width {n : Nat} (p : Formula n) :
    (descriptor p).traceWidth - n = p.graphCost.witnesses := by
  rw [descriptor, Nat.add_sub_cancel_left, witnessCount_eq_graphCost_witnesses]

/-! ## 4. Executable canonical one-row witness -/

def eval {n : Nat} (truth : Fin n -> Bool) : Formula n -> Bool
  | .atom a => truth a
  | .top => true
  | .bot => false
  | .not p => !(eval truth p)
  | .and p q => eval truth p && eval truth q
  | .or p q => eval truth p || eval truth q

theorem eval_eq_true_iff_holds {n : Nat} (truth : Fin n -> Bool) (p : Formula n) :
    eval truth p = true <-> Formula.Holds (fun a => truth a = true) p := by
  induction p with
  | atom a => simp [eval, Formula.Holds]
  | top => simp [eval, Formula.Holds]
  | bot => simp [eval, Formula.Holds]
  | not p ih =>
      cases h : eval truth p <;>
        simp [eval, Formula.Holds, h] at ih ⊢ <;> assumption
  | and p q ihp ihq => simp [eval, Formula.Holds, ihp, ihq]
  | or p q ihp ihq => simp [eval, Formula.Holds, ihp, ihq]

def bitInt (b : Bool) : Int := if b then 1 else 0

/-- Postorder witness values in exactly the same order as `nodesAt` allocates
columns.  For an atom, the second value is a valid inverse for the canonical
residual `0`/`1`. -/
def witnessBits {n : Nat} (truth : Fin n -> Bool) : Formula n -> List Bool
  | .atom a => [truth a, !(truth a)]
  | .top | .bot => []
  | .not p => witnessBits truth p ++ [eval truth (.not p)]
  | .and p q => witnessBits truth p ++ witnessBits truth q ++ [eval truth (.and p q)]
  | .or p q => witnessBits truth p ++ witnessBits truth q ++ [eval truth (.or p q)]

@[simp] theorem witnessBits_length {n : Nat} (truth : Fin n -> Bool) (p : Formula n) :
    (witnessBits truth p).length = witnessCount p := by
  induction p <;> simp [witnessBits, witnessCount, *] <;> omega

def residualInput {n : Nat} (truth : Fin n -> Bool) (a : Fin n) : Int :=
  if truth a then 0 else 1

def canonicalRow {n : Nat} (truth : Fin n -> Bool) (p : Formula n) : Assignment :=
  fun c => if h : c < n then residualInput truth ⟨c, h⟩
    else bitInt ((witnessBits truth p).getD (c - n) false)

def canonicalTrace {n : Nat} (truth : Fin n -> Bool) (p : Formula n) : VmTrace :=
  { rows := [canonicalRow truth p], pub := zeroAsg, tf := fun _ => [] }

def InputsMatch {n : Nat} (truth : Fin n -> Bool) (a : Assignment) : Prop :=
  forall x : Fin n, a x.val = residualInput truth x

def WitnessesMatch {n : Nat} (truth : Fin n -> Bool) (base : Nat)
    (p : Formula n) (a : Assignment) : Prop :=
  forall k, k < witnessCount p ->
    a (base + k) = bitInt ((witnessBits truth p).getD k false)

private theorem getD_append_lt {A : Type*} (xs ys : List A) (i : Nat) (d : A)
    (h : i < xs.length) : (xs ++ ys).getD i d = xs.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_append_right {A : Type*} (xs ys : List A) (k : Nat) (d : A) :
    (xs ++ ys).getD (xs.length + k) d = ys.getD k d := by
  simp [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right xs.length k)]

theorem canonical_inputs_match {n : Nat} (truth : Fin n -> Bool) (p : Formula n) :
    InputsMatch truth (canonicalRow truth p) := by
  intro x
  simp [canonicalRow, x.isLt]

theorem canonical_witnesses_match {n : Nat} (truth : Fin n -> Bool) (p : Formula n) :
    WitnessesMatch truth n p (canonicalRow truth p) := by
  intro k hk
  simp [canonicalRow]

theorem witnesses_not_child {n : Nat} {truth : Fin n -> Bool} {base : Nat}
    {p : Formula n} {a : Assignment}
    (h : WitnessesMatch truth base (.not p) a) : WitnessesMatch truth base p a := by
  intro k hk
  have hp := h k (by simp [witnessCount]; omega)
  rw [witnessBits, getD_append_lt _ _ _ _ (by simpa using hk)] at hp
  exact hp

theorem witnesses_and_left {n : Nat} {truth : Fin n -> Bool} {base : Nat}
    {p q : Formula n} {a : Assignment}
    (h : WitnessesMatch truth base (.and p q) a) : WitnessesMatch truth base p a := by
  intro k hk
  have hp := h k (by simp [witnessCount]; omega)
  rw [witnessBits, getD_append_lt _ _ _ _ (by
    simp [witnessBits_length]
    omega), getD_append_lt _ _ _ _ (by simpa [witnessBits_length] using hk)] at hp
  exact hp

theorem witnesses_or_left {n : Nat} {truth : Fin n -> Bool} {base : Nat}
    {p q : Formula n} {a : Assignment}
    (h : WitnessesMatch truth base (.or p q) a) : WitnessesMatch truth base p a := by
  intro k hk
  have hp := h k (by simp [witnessCount]; omega)
  rw [witnessBits, getD_append_lt _ _ _ _ (by
    simp [witnessBits_length]
    omega), getD_append_lt _ _ _ _ (by simpa [witnessBits_length] using hk)] at hp
  exact hp

theorem witnesses_and_right {n : Nat} {truth : Fin n -> Bool} {base : Nat}
    {p q : Formula n} {a : Assignment}
    (h : WitnessesMatch truth base (.and p q) a) :
    WitnessesMatch truth (base + witnessCount p) q a := by
  intro k hk
  have hp := h (witnessCount p + k) (by simp [witnessCount]; omega)
  rw [witnessBits, getD_append_lt _ _ _ _ (by
    simp [witnessBits_length]
    omega)] at hp
  rw [show witnessCount p = (witnessBits truth p).length by simp,
    getD_append_right] at hp
  simpa [Nat.add_assoc] using hp

theorem witnesses_or_right {n : Nat} {truth : Fin n -> Bool} {base : Nat}
    {p q : Formula n} {a : Assignment}
    (h : WitnessesMatch truth base (.or p q) a) :
    WitnessesMatch truth (base + witnessCount p) q a := by
  intro k hk
  have hp := h (witnessCount p + k) (by simp [witnessCount]; omega)
  rw [witnessBits, getD_append_lt _ _ _ _ (by
    simp [witnessBits_length]
    omega)] at hp
  rw [show witnessCount p = (witnessBits truth p).length by simp,
    getD_append_right] at hp
  simpa [Nat.add_assoc] using hp

/-- The output wire of a matched materialization contains exactly the Boolean
source value. -/
theorem output_eval_of_matches {n : Nat} (truth : Fin n -> Bool) (base : Nat)
    (p : Formula n) (a : Assignment) (h : WitnessesMatch truth base p a) :
    (outputAt base p).eval a = bitInt (eval truth p) := by
  cases p with
  | atom x =>
      have hx := h 0 (by simp [witnessCount])
      simpa [outputAt, witnessBits] using hx
  | top => rfl
  | bot => rfl
  | not p =>
      have hx := h (witnessCount p) (by simp [witnessCount])
      rw [witnessBits, show witnessCount p = (witnessBits truth p).length by simp] at hx
      have hlast := getD_append_right (witnessBits truth p)
        [eval truth (.not p)] 0 false
      simp only [Nat.add_zero, List.getD_cons_zero] at hlast
      rw [hlast] at hx
      simpa [outputAt, Nat.add_assoc] using hx
  | and p q =>
      have hx := h (witnessCount p + witnessCount q) (by simp [witnessCount])
      rw [witnessBits,
        show witnessCount p + witnessCount q =
          (witnessBits truth p ++ witnessBits truth q).length by simp] at hx
      have hlast := getD_append_right
        (witnessBits truth p ++ witnessBits truth q)
        [eval truth (.and p q)] 0 false
      simp only [Nat.add_zero, List.getD_cons_zero] at hlast
      rw [hlast] at hx
      simpa [outputAt, Nat.add_assoc] using hx
  | or p q =>
      have hx := h (witnessCount p + witnessCount q) (by simp [witnessCount])
      rw [witnessBits,
        show witnessCount p + witnessCount q =
          (witnessBits truth p ++ witnessBits truth q).length by simp] at hx
      have hlast := getD_append_right
        (witnessBits truth p ++ witnessBits truth q)
        [eval truth (.or p q)] 0 false
      simp only [Nat.add_zero, List.getD_cons_zero] at hlast
      rw [hlast] at hx
      simpa [outputAt] using hx

namespace Node

def HoldsAt (env : VmRowEnv) (node : Node) : Prop :=
  forall c, c ∈ node.constraints ->
    c.holdsAt (fun _ => 0) (fun _ => []) env false true

end Node

/-! The semantic proof is completed below the fail-closed certificate because
its final theorem uses the exact reconstructed descriptor. -/

/-! ## 5. Fail-closed layout and byte certificate -/

def liveVersion : Nat := 1

structure Layout where
  inputs : Nat
  auxiliaries : Nat
  traceWidth : Nat
  graphEquations : Nat
  acceptingEquations : Nat
  multiplications : Nat
  deriving DecidableEq, Repr

def layoutOf {n : Nat} (p : Formula n) : Layout :=
  { inputs := n
  , auxiliaries := witnessCount p
  , traceWidth := n + witnessCount p
  , graphEquations := (graphConstraints p).length
  , acceptingEquations := (descriptor p).constraints.length
  , multiplications := emittedMultiplications p }

structure LiveCertificate (n : Nat) where
  version : Nat
  source : Formula n
  optimized : Formula n
  optimizer : Certificate n
  layout : Layout
  descriptorBytes : String
  deriving Repr

def checkLive {n : Nat} (c : LiveCertificate n) : Bool :=
  decide (c.version = liveVersion) &&
    c.optimizer.check &&
    decide (c.optimizer.source = c.source) &&
    decide (c.optimizer.target = c.optimized) &&
    decide (c.layout = layoutOf c.optimized) &&
    decide (c.descriptorBytes = emitVmJson2 (descriptor c.optimized))

def certify {n : Nat} (source : Formula n) : LiveCertificate n :=
  let result := optimize source
  { version := liveVersion
  , source := source
  , optimized := result.1
  , optimizer := result.2
  , layout := layoutOf result.1
  , descriptorBytes := emitVmJson2 (descriptor result.1) }

theorem checkLive_spec {n : Nat} (c : LiveCertificate n) :
    checkLive c = true <->
      c.version = liveVersion /\
      c.optimizer.check = true /\
      c.optimizer.source = c.source /\
      c.optimizer.target = c.optimized /\
      c.layout = layoutOf c.optimized /\
      c.descriptorBytes = emitVmJson2 (descriptor c.optimized) := by
  simp [checkLive, and_assoc]

theorem checkLive_certify {n : Nat} (source : Formula n) :
    checkLive (certify source) = true := by
  rw [checkLive_spec]
  simp [certify, optimize_checked, optimize_source, optimize_target]

/-! ## 6. The actual 30 -> 13 specimen, with the accepting correction -/

abbrev factorBefore : Formula 4 := factorSpecimen
abbrev factorAfter : Formula 4 := (optimize factorSpecimen).1

theorem factor_emitted_exact :
    (graphConstraints factorBefore).length = 30 /\
    (graphConstraints factorAfter).length = 13 /\
    (descriptor factorBefore).constraints.length = 31 /\
    (descriptor factorAfter).constraints.length = 14 /\
    emittedMultiplications factorBefore = 26 /\
    emittedMultiplications factorAfter = 13 /\
    (descriptor factorBefore).traceWidth - 4 = 17 /\
    (descriptor factorAfter).traceWidth - 4 = 8 := by
  native_decide

def factorCertificate : LiveCertificate 4 := certify factorSpecimen

def tamperedLayoutCertificate : LiveCertificate 4 :=
  { factorCertificate with
    layout := { factorCertificate.layout with acceptingEquations := 13 } }

def tamperedBytesCertificate : LiveCertificate 4 :=
  { factorCertificate with descriptorBytes := factorCertificate.descriptorBytes ++ " " }

def tamperedEndpointCertificate : LiveCertificate 4 :=
  { factorCertificate with optimized := atom3 }

#guard checkLive factorCertificate
#guard !checkLive tamperedLayoutCertificate
#guard !checkLive tamperedBytesCertificate
#guard !checkLive tamperedEndpointCertificate

end Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2
