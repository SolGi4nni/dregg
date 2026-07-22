/-
# Dregg2.Logic.FheLogicSchedule -- a physical schedule for finite Boolean logic

This module connects `FiniteLogicPlan` to a small physical scheduling IR.  The
IR records choices which matter to an FHE implementation but not to source
truth: scalar versus SIMD equality batches, arithmetic versus public-LUT
kernels, a scalar binary chain, an in-lane rotate tree, or a bounded high-fan-in
reduction primitive.

The semantic theorems are deliberately backend-neutral.  They prove that the
schedule denotes the same Boolean result as the finite source plan.  A separate
`BackendLaws` interface names the implementation obligations: lane packing,
public LUTs, rotations, high-fan-in reductions, residual arithmetic, and the
final Boolean observation must realize that denotation.

`Cost` is an exact symbolic ledger for the instructions named by this IR.  It
is not a latency model, a noise theorem, a no-wrap theorem, an FHE security
claim, or evidence that the current fhEgg backend implements every choice.
In particular, `highFanIn` is a typed capability request, not an assertion that
TFHE, BFV, or a deployed GPU kernel provides it at the recorded arity.

Pure.  No axioms.
-/

import Mathlib.Tactic
import Dregg2.Logic.FiniteLogicPlan
import Dregg2.Tactics

namespace Dregg2.Logic.FheLogicSchedule

set_option autoImplicit false

open Dregg2.Logic.FiniteLogicPlan

/-! ## 1. Typed physical choices -/

/-- Whether a batch of equality bits is reduced conjunctively or disjunctively. -/
inductive EqualityMode where
  | all
  | any
  deriving DecidableEq, Repr

/-- A scheduled equality kernel.  `publicLut` is a request for a public truth
table, not a cryptographic claim about its implementation. -/
inductive EqualityKernel where
  | arithmetic
  | publicLut
  deriving DecidableEq, Repr

/-- A scheduled Boolean gate kernel. -/
inductive GateKernel where
  | arithmetic
  | publicLut
  deriving DecidableEq, Repr

/-- Physical placement of `n` equality tests.  The positive-width proof makes
division-by-zero schedules unrepresentable. -/
inductive Packing (n : Nat) where
  | scalar
  | simd (lanes : Nat) (positive : 0 < lanes)

/-- Physical reduction of `n` Boolean results.

`packedRotateTree` requires the entire batch to fit in the declared lane width.
`highFanIn` requires the batch to fit in the primitive's declared arity.  These
proofs rule out malformed schedules, while semantic correctness of an actual
kernel remains in `BackendLaws`. -/
inductive Reduction (n : Nat) where
  | binaryChain (kernel : GateKernel)
  | packedRotateTree (lanes : Nat) (positive : 0 < lanes) (fits : n ≤ lanes)
  | highFanIn (arity : Nat) (atLeastTwo : 2 ≤ arity) (fits : n ≤ arity)
      (kernel : GateKernel)

/-- A rotate-tree may only consume a SIMD batch with the same lane width.  The
other reductions can consume either scalar or packed equality results. -/
def Compatible {n : Nat} : Packing n → Reduction n → Prop
  | .scalar, .packedRotateTree _ _ _ => False
  | .simd lanes _, .packedRotateTree reductionLanes _ _ =>
      lanes = reductionLanes
  | _, _ => True

/-- One well-typed physical equality/reduction schedule. -/
structure EqualitySchedule where
  mode : EqualityMode
  pairs : List (Term × Term)
  equalityKernel : EqualityKernel
  packing : Packing pairs.length
  reduction : Reduction pairs.length
  compatible : Compatible packing reduction

/-- Physical Boolean plans.  `residual` retains the bounded additive primitive
from `FiniteLogicPlan`; it is not silently treated as finite-field arithmetic. -/
inductive PhysicalPlan where
  | bit (value : Bool)
  | equalityReduce (schedule : EqualitySchedule)
  | not (kernel : GateKernel) (input : PhysicalPlan)
  | and (kernel : GateKernel) (left right : PhysicalPlan)
  | or (kernel : GateKernel) (left right : PhysicalPlan)
  | residual (bound : Nat) (pairs : List (Term × Term))

/-! ## 2. Reference denotation -/

def EqualityMode.reduce (mode : EqualityMode) (bits : List Bool) : Bool :=
  match mode with
  | .all => bits.all id
  | .any => bits.any id

def equalityBits (env : Env) (pairs : List (Term × Term)) : List Bool :=
  (evalPairs env pairs).map fun pair => decide (pair.1 = pair.2)

def EqualitySchedule.denote (env : Env) (schedule : EqualitySchedule) : Bool :=
  schedule.mode.reduce (equalityBits env schedule.pairs)

def PhysicalPlan.denote (env : Env) : PhysicalPlan → Bool
  | .bit value => value
  | .equalityReduce schedule => schedule.denote env
  | .not _ input => !(input.denote env)
  | .and _ left right => left.denote env && right.denote env
  | .or _ left right => left.denote env || right.denote env
  | .residual bound pairs =>
      transparentAllEqResidual bound (evalPairs env pairs)

/-! ## 3. Total structural scheduling and semantic preservation -/

/-- Policy for structural scheduling.  The generic compiler uses scalar
singleton equalities; batch-specific compilers below expose SIMD and n-ary
reduction choices. -/
structure Policy where
  equalityKernel : EqualityKernel
  notKernel : GateKernel
  andKernel : GateKernel
  orKernel : GateKernel
  deriving DecidableEq, Repr

def conservativePolicy : Policy where
  equalityKernel := .arithmetic
  notKernel := .arithmetic
  andKernel := .arithmetic
  orKernel := .arithmetic

def singletonEqualitySchedule (kernel : EqualityKernel) (lhs rhs : Term) :
    EqualitySchedule where
  mode := .all
  pairs := [(lhs, rhs)]
  equalityKernel := kernel
  packing := .scalar
  reduction := .binaryChain .arithmetic
  compatible := by simp [Compatible]

/-- Schedule every source constructor without changing tree shape. -/
def schedule (policy : Policy) : LogicPlan → PhysicalPlan
  | .bit value => .bit value
  | .eq lhs rhs =>
      .equalityReduce (singletonEqualitySchedule policy.equalityKernel lhs rhs)
  | .not input => .not policy.notKernel (schedule policy input)
  | .and left right =>
      .and policy.andKernel (schedule policy left) (schedule policy right)
  | .or left right =>
      .or policy.orKernel (schedule policy left) (schedule policy right)
  | .allEqResidual bound pairs => .residual bound pairs

@[simp] theorem singletonEqualitySchedule_denote (env : Env)
    (kernel : EqualityKernel) (lhs rhs : Term) :
    (singletonEqualitySchedule kernel lhs rhs).denote env =
      decide (lhs.eval env = rhs.eval env) := by
  simp [singletonEqualitySchedule, EqualitySchedule.denote, equalityBits,
    EqualityMode.reduce, evalPairs]

/-- The physical scheduler preserves the exact transparent meaning of every
finite source plan, including fail-closed range validation on residual plans. -/
theorem schedule_refines_plan (policy : Policy) (env : Env) (plan : LogicPlan) :
    (schedule policy plan).denote env = plan.run transparentOps env := by
  induction plan with
  | bit value => rfl
  | eq lhs rhs =>
      simp [schedule, PhysicalPlan.denote, LogicPlan.run, transparentOps]
  | not input ih =>
      simp [schedule, PhysicalPlan.denote, LogicPlan.run, transparentOps, ih]
  | and left right ihLeft ihRight =>
      simp [schedule, PhysicalPlan.denote, LogicPlan.run, transparentOps,
        ihLeft, ihRight]
  | or left right ihLeft ihRight =>
      simp [schedule, PhysicalPlan.denote, LogicPlan.run, transparentOps,
        ihLeft, ihRight]
  | allEqResidual bound pairs => rfl

/-- The scheduler composed with the total Boolean lowering preserves source
formula truth. -/
theorem schedule_lowerBool_refines (policy : Policy) (env : Env) (formula : Formula) :
    (schedule policy (lowerBool formula)).denote env = formula.eval env := by
  rw [schedule_refines_plan]
  simpa [transparentOps] using
    lowerBool_refines transparentOps transparentPrimitiveLaws env formula

/-- Build one optimized, well-typed equality/reduction plan. -/
def compileEqualityReduction (mode : EqualityMode)
    (pairs : List (Term × Term)) (equalityKernel : EqualityKernel)
    (packing : Packing pairs.length) (reduction : Reduction pairs.length)
    (compatible : Compatible packing reduction) : PhysicalPlan :=
  .equalityReduce {
    mode, pairs, equalityKernel, packing, reduction, compatible
  }

theorem compile_allEq_refines (env : Env) (pairs : List (Term × Term))
    (equalityKernel : EqualityKernel) (packing : Packing pairs.length)
    (reduction : Reduction pairs.length)
    (compatible : Compatible packing reduction) :
    (compileEqualityReduction .all pairs equalityKernel packing reduction
      compatible).denote env = (allEq pairs).eval env := by
  rw [eval_allEq]
  simp [compileEqualityReduction, PhysicalPlan.denote, EqualitySchedule.denote,
    EqualityMode.reduce, equalityBits]

theorem compile_anyEq_refines (env : Env) (pairs : List (Term × Term))
    (equalityKernel : EqualityKernel) (packing : Packing pairs.length)
    (reduction : Reduction pairs.length)
    (compatible : Compatible packing reduction) :
    (compileEqualityReduction .any pairs equalityKernel packing reduction
      compatible).denote env = (anyEq pairs).eval env := by
  rw [eval_anyEq]
  simp [compileEqualityReduction, PhysicalPlan.denote, EqualitySchedule.denote,
    EqualityMode.reduce, equalityBits]

/-! ## 4. Named backend correctness boundary -/

/-- Operations supplied by a concrete execution backend.  Scheduling metadata
is visible to `equalityReduce`, so an implementation may select SIMD, LUT,
rotation, or high-fan-in kernels without changing this interface. -/
structure BackendOps (Carrier : Type*) where
  bit : Bool → Carrier
  equalityReduce : EqualitySchedule → Env → Carrier
  not : GateKernel → Carrier → Carrier
  and : GateKernel → Carrier → Carrier → Carrier
  or : GateKernel → Carrier → Carrier → Carrier
  residual : Nat → List (Term × Term) → Env → Carrier
  observe : Carrier → Bool

/-- Every implementation-sensitive fact is explicit here.  In particular,
`observe_equalityReduce` is where SIMD lane order, public-LUT truth tables,
rotate trees, and high-fan-in reduction correctness must be proved.  This
module supplies no FHE security, noise, key-management, or timing theorem. -/
structure BackendLaws {Carrier : Type*} (ops : BackendOps Carrier) : Prop where
  observe_bit : ∀ value, ops.observe (ops.bit value) = value
  observe_equalityReduce : ∀ schedule env,
    ops.observe (ops.equalityReduce schedule env) = schedule.denote env
  observe_not : ∀ kernel input,
    ops.observe (ops.not kernel input) = !(ops.observe input)
  observe_and : ∀ kernel left right,
    ops.observe (ops.and kernel left right) =
      (ops.observe left && ops.observe right)
  observe_or : ∀ kernel left right,
    ops.observe (ops.or kernel left right) =
      (ops.observe left || ops.observe right)
  observe_residual : ∀ bound pairs env,
    ops.observe (ops.residual bound pairs env) =
      transparentAllEqResidual bound (evalPairs env pairs)

def PhysicalPlan.execute {Carrier : Type*} (ops : BackendOps Carrier) (env : Env) :
    PhysicalPlan → Carrier
  | .bit value => ops.bit value
  | .equalityReduce schedule => ops.equalityReduce schedule env
  | .not kernel input => ops.not kernel (input.execute ops env)
  | .and kernel left right =>
      ops.and kernel (left.execute ops env) (right.execute ops env)
  | .or kernel left right =>
      ops.or kernel (left.execute ops env) (right.execute ops env)
  | .residual bound pairs => ops.residual bound pairs env

theorem execute_refines_denote {Carrier : Type*} (ops : BackendOps Carrier)
    (laws : BackendLaws ops) (env : Env) (plan : PhysicalPlan) :
    ops.observe (plan.execute ops env) = plan.denote env := by
  induction plan with
  | bit value => exact laws.observe_bit value
  | equalityReduce schedule => exact laws.observe_equalityReduce schedule env
  | not kernel input ih =>
      rw [PhysicalPlan.execute, laws.observe_not, ih]
      rfl
  | and kernel left right ihLeft ihRight =>
      rw [PhysicalPlan.execute, laws.observe_and, ihLeft, ihRight]
      rfl
  | or kernel left right ihLeft ihRight =>
      rw [PhysicalPlan.execute, laws.observe_or, ihLeft, ihRight]
      rfl
  | residual bound pairs => exact laws.observe_residual bound pairs env

theorem execute_scheduled_source {Carrier : Type*} (ops : BackendOps Carrier)
    (laws : BackendLaws ops) (policy : Policy) (env : Env) (formula : Formula) :
    ops.observe ((schedule policy (lowerBool formula)).execute ops env) =
      formula.eval env := by
  calc
    ops.observe ((schedule policy (lowerBool formula)).execute ops env) =
        (schedule policy (lowerBool formula)).denote env :=
      execute_refines_denote ops laws env (schedule policy (lowerBool formula))
    _ = formula.eval env := schedule_lowerBool_refines policy env formula

/-! ## 5. Exact symbolic instruction ledger -/

/-- Ceiling division, used only with a positive SIMD width supplied by `Packing`. -/
def ceilDiv (n width : Nat) : Nat := (n + width - 1) / width

/-- Depth of an ideal balanced binary reduction in this symbolic IR. -/
def balancedDepth (n : Nat) : Nat :=
  if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

def Packing.batchCount {n : Nat} : Packing n → Nat
  | .scalar => n
  | .simd lanes _ => ceilDiv n lanes

def Packing.laneBatchCount {n : Nat} : Packing n → Nat
  | .scalar => 0
  | .simd lanes _ => ceilDiv n lanes

/-- The axes are not collapsed into a context-free runtime estimate.

* `logicalEqualities` counts source equality atoms.
* `work` counts scheduled physical primitive calls.
* `depth` counts dependency stages in the idealized schedule.
* `rotations` counts explicit rotate/combine stages.
* `bootstraps` and `publicLuts` count requested LUT/PBS primitives.
* `laneBatches` counts SIMD ciphertext-sized equality batches.
-/
structure Cost where
  logicalEqualities : Nat := 0
  work : Nat := 0
  depth : Nat := 0
  rotations : Nat := 0
  bootstraps : Nat := 0
  publicLuts : Nat := 0
  laneBatches : Nat := 0
  deriving DecidableEq, Repr

def gateCalls (n : Nat) : Nat := n - 1

def GateKernel.bootstrapCount (kernel : GateKernel) (calls : Nat) : Nat :=
  match kernel with
  | .arithmetic => 0
  | .publicLut => calls

def EqualityKernel.bootstrapCount (kernel : EqualityKernel) (calls : Nat) : Nat :=
  match kernel with
  | .arithmetic => 0
  | .publicLut => calls

def Reduction.cost {n : Nat} : Reduction n → Cost
  | .binaryChain kernel =>
      let calls := gateCalls n
      { work := calls
        depth := calls
        bootstraps := kernel.bootstrapCount calls
        publicLuts := kernel.bootstrapCount calls }
  | .packedRotateTree _ _ _ =>
      let levels := balancedDepth n
      { work := levels, depth := levels, rotations := levels }
  | .highFanIn _ _ _ kernel =>
      let calls := if n ≤ 1 then 0 else 1
      { work := calls
        depth := calls
        bootstraps := kernel.bootstrapCount calls
        publicLuts := kernel.bootstrapCount calls }

def EqualitySchedule.cost (schedule : EqualitySchedule) : Cost :=
  let batches := schedule.packing.batchCount
  let reductionCost := schedule.reduction.cost
  { logicalEqualities := schedule.pairs.length
    work := batches + reductionCost.work
    depth := (if schedule.pairs.isEmpty then 0 else 1) + reductionCost.depth
    rotations := reductionCost.rotations
    bootstraps :=
      schedule.equalityKernel.bootstrapCount batches + reductionCost.bootstraps
    publicLuts :=
      schedule.equalityKernel.bootstrapCount batches + reductionCost.publicLuts
    laneBatches := schedule.packing.laneBatchCount }

def Cost.unary (input : Cost) (kernel : GateKernel) : Cost :=
  { logicalEqualities := input.logicalEqualities
    work := input.work + 1
    depth := input.depth + 1
    rotations := input.rotations
    bootstraps := input.bootstraps + kernel.bootstrapCount 1
    publicLuts := input.publicLuts + kernel.bootstrapCount 1
    laneBatches := input.laneBatches }

def Cost.binary (left right : Cost) (kernel : GateKernel) : Cost :=
  { logicalEqualities := left.logicalEqualities + right.logicalEqualities
    work := left.work + right.work + 1
    depth := max left.depth right.depth + 1
    rotations := left.rotations + right.rotations
    bootstraps := left.bootstraps + right.bootstraps + kernel.bootstrapCount 1
    publicLuts := left.publicLuts + right.publicLuts + kernel.bootstrapCount 1
    laneBatches := left.laneBatches + right.laneBatches }

def PhysicalPlan.cost : PhysicalPlan → Cost
  | .bit _ => {}
  | .equalityReduce schedule => schedule.cost
  | .not kernel input => Cost.unary input.cost kernel
  | .and kernel left right => Cost.binary left.cost right.cost kernel
  | .or kernel left right => Cost.binary left.cost right.cost kernel
  | .residual _ pairs =>
      { logicalEqualities := pairs.length
        work := pairs.length + (pairs.length - 1) + 1
        depth := pairs.length + 1 }

theorem equalityReduction_cost (schedule : EqualitySchedule) :
    (PhysicalPlan.equalityReduce schedule).cost = schedule.cost := rfl

theorem scheduled_not_cost (kernel : GateKernel) (input : PhysicalPlan) :
    (PhysicalPlan.not kernel input).cost = Cost.unary input.cost kernel := rfl

theorem scheduled_and_cost (kernel : GateKernel) (left right : PhysicalPlan) :
    (PhysicalPlan.and kernel left right).cost =
      Cost.binary left.cost right.cost kernel := rfl

theorem scheduled_or_cost (kernel : GateKernel) (left right : PhysicalPlan) :
    (PhysicalPlan.or kernel left right).cost =
      Cost.binary left.cost right.cost kernel := rfl

/-! ## 6. Concrete semantic and accounting teeth -/

def eightAgainstOne : List (Term × Term) :=
  [(.var 0, .lit 1), (.var 1, .lit 1), (.var 2, .lit 1), (.var 3, .lit 1),
   (.var 4, .lit 1), (.var 5, .lit 1), (.var 6, .lit 1), (.var 7, .lit 1)]

def allOneEnv : Env
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => 1
  | _ => 0

def oneMismatchEnv : Env
  | 3 => 9
  | 0 | 1 | 2 | 4 | 5 | 6 | 7 => 1
  | _ => 0

def scalarEight : PhysicalPlan :=
  compileEqualityReduction .all eightAgainstOne .arithmetic .scalar
    (.binaryChain .arithmetic) (by simp [Compatible])

def packedRotateEight : PhysicalPlan :=
  compileEqualityReduction .all eightAgainstOne .arithmetic
    (.simd 8 (by decide))
    (.packedRotateTree 8 (by decide) (by decide))
    (by simp [Compatible])

def highFanInLutEight : PhysicalPlan :=
  compileEqualityReduction .all eightAgainstOne .publicLut
    (.simd 8 (by decide))
    (.highFanIn 8 (by decide) (by decide) .publicLut)
    (by simp [Compatible])

#guard scalarEight.denote allOneEnv == true
#guard scalarEight.denote oneMismatchEnv == false
#guard packedRotateEight.denote allOneEnv == true
#guard packedRotateEight.denote oneMismatchEnv == false
#guard highFanInLutEight.denote allOneEnv == true
#guard highFanInLutEight.denote oneMismatchEnv == false

theorem scalarEight_cost : scalarEight.cost =
    { logicalEqualities := 8, work := 15, depth := 8 : Cost } := by decide

theorem packedRotateEight_cost : packedRotateEight.cost =
    { logicalEqualities := 8, work := 4, depth := 4, rotations := 3,
      laneBatches := 1 : Cost } := by decide

theorem highFanInLutEight_cost : highFanInLutEight.cost =
    { logicalEqualities := 8, work := 2, depth := 2, bootstraps := 2,
      publicLuts := 2, laneBatches := 1 : Cost } := by decide

theorem scalarEight_refines (env : Env) :
    scalarEight.denote env = (allEq eightAgainstOne).eval env := by
  exact compile_allEq_refines env eightAgainstOne .arithmetic .scalar
    (.binaryChain .arithmetic) (by simp [Compatible])

theorem packedRotateEight_refines (env : Env) :
    packedRotateEight.denote env = (allEq eightAgainstOne).eval env := by
  exact compile_allEq_refines env eightAgainstOne .arithmetic
    (.simd 8 (by decide)) (.packedRotateTree 8 (by decide) (by decide))
    (by simp [Compatible])

theorem highFanInLutEight_refines (env : Env) :
    highFanInLutEight.denote env = (allEq eightAgainstOne).eval env := by
  exact compile_allEq_refines env eightAgainstOne .publicLut
    (.simd 8 (by decide))
    (.highFanIn 8 (by decide) (by decide) .publicLut)
    (by simp [Compatible])

/-! ### Axiom hygiene -/

#assert_all_clean [
  singletonEqualitySchedule_denote,
  schedule_refines_plan,
  schedule_lowerBool_refines,
  compile_allEq_refines,
  compile_anyEq_refines,
  execute_refines_denote,
  execute_scheduled_source,
  equalityReduction_cost,
  scheduled_not_cost,
  scheduled_and_cost,
  scheduled_or_cost,
  scalarEight_cost,
  packedRotateEight_cost,
  highFanInLutEight_cost,
  scalarEight_refines,
  packedRotateEight_refines,
  highFanInLutEight_refines
]

end Dregg2.Logic.FheLogicSchedule
