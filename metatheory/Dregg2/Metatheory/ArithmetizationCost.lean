/-
# Symbolic costs for corrected FOL and finite HOL arithmetization

This file gives a backend-neutral, executable cost ledger for the sound
constructions in `FOLArithmetizationCorrected`, `Logic.BoolGraph`, and
`FinitePolynomialFunctions`.  It deliberately proves symbolic recurrences,
not benchmark claims.

The five coordinates separate facts that are otherwise easy to conflate:

* field equations emitted by the relation;
* nontrivial field multiplications;
* prover-supplied wires (including inverse witnesses);
* maximum equation degree;
* extensional table cells that must be represented or visited.

Costs compose by adding the first, second, third, and fifth coordinates while
taking the maximum degree.  Hence a chain of quadratic gates remains
quadratic even though its total work grows linearly.

Standalone artifact: no central import is modified.
-/
import Dregg2.Metatheory.FOLArithmetizationCorrected
import Dregg2.Logic.BoolGraph
import Dregg2.Metatheory.FinitePolynomialFunctions

namespace Dregg2.Metatheory.ArithmetizationCost

open Dregg2.Metatheory.FOLArithmetizationCorrected

/-! ## A compositional vector cost -/

/-- A symbolic relation cost.  `witnesses` counts all fresh prover wires,
including inverse witnesses; `tableCells` records dense extensional data and
is not silently equated with field equations. -/
@[ext]
structure BackendCost where
  equations : Nat
  multiplications : Nat
  witnesses : Nat
  maxDegree : Nat
  tableCells : Nat
  deriving DecidableEq, Repr

namespace BackendCost

def zero : BackendCost := ⟨0, 0, 0, 0, 0⟩

/-- Sequential/graph composition: additive work, maximum local degree. -/
def combine (a b : BackendCost) : BackendCost where
  equations := a.equations + b.equations
  multiplications := a.multiplications + b.multiplications
  witnesses := a.witnesses + b.witnesses
  maxDegree := max a.maxDegree b.maxDegree
  tableCells := a.tableCells + b.tableCells

/-- `n` independent copies of one relation fragment. -/
def scale (n : Nat) (c : BackendCost) : BackendCost where
  equations := n * c.equations
  multiplications := n * c.multiplications
  witnesses := n * c.witnesses
  maxDegree := if n = 0 then 0 else c.maxDegree
  tableCells := n * c.tableCells

@[simp] theorem zero_equations : zero.equations = 0 := rfl
@[simp] theorem zero_multiplications : zero.multiplications = 0 := rfl
@[simp] theorem zero_witnesses : zero.witnesses = 0 := rfl
@[simp] theorem zero_degree : zero.maxDegree = 0 := rfl
@[simp] theorem zero_cells : zero.tableCells = 0 := rfl

@[simp] theorem combine_equations (a b : BackendCost) :
    (combine a b).equations = a.equations + b.equations := rfl
@[simp] theorem combine_multiplications (a b : BackendCost) :
    (combine a b).multiplications = a.multiplications + b.multiplications := rfl
@[simp] theorem combine_witnesses (a b : BackendCost) :
    (combine a b).witnesses = a.witnesses + b.witnesses := rfl
@[simp] theorem combine_degree (a b : BackendCost) :
    (combine a b).maxDegree = max a.maxDegree b.maxDegree := rfl
@[simp] theorem combine_cells (a b : BackendCost) :
    (combine a b).tableCells = a.tableCells + b.tableCells := rfl

@[simp] theorem scale_equations (n : Nat) (c : BackendCost) :
    (scale n c).equations = n * c.equations := rfl
@[simp] theorem scale_multiplications (n : Nat) (c : BackendCost) :
    (scale n c).multiplications = n * c.multiplications := rfl
@[simp] theorem scale_witnesses (n : Nat) (c : BackendCost) :
    (scale n c).witnesses = n * c.witnesses := rfl
@[simp] theorem scale_degree (n : Nat) (c : BackendCost) :
    (scale n c).maxDegree = if n = 0 then 0 else c.maxDegree := rfl
@[simp] theorem scale_cells (n : Nat) (c : BackendCost) :
    (scale n c).tableCells = n * c.tableCells := rfl

theorem combine_assoc (a b c : BackendCost) :
    combine (combine a b) c = combine a (combine b c) := by
  ext <;> simp [combine, Nat.add_assoc, max_assoc]

theorem combine_comm (a b : BackendCost) : combine a b = combine b a := by
  ext <;> simp [combine, Nat.add_comm, max_comm]

theorem degree_combine_le {d : Nat} {ca cb : BackendCost}
    (ha : ca.maxDegree ≤ d) (hb : cb.maxDegree ≤ d) :
    (combine ca cb).maxDegree ≤ d := by
  simp only [combine_degree, max_le_iff]
  exact ⟨ha, hb⟩

end BackendCost

open BackendCost

/-! ## Primitive corrected gates -/

/-- One materialized linear addition gate for the positive/no-wrap route. -/
def positiveAndGateCost : BackendCost := ⟨1, 0, 1, 1, 0⟩

/-- One materialized multiplication gate for the positive/no-wrap route. -/
def positiveOrGateCost : BackendCost := ⟨1, 1, 1, 2, 0⟩

/-- Exact cost of the three equations in `BoolGraph.ZeroGate` after sharing
already-constrained inputs: one bit wire, one inverse wire, three products. -/
def zeroTestGateCost : BackendCost := ⟨3, 3, 2, 2, 0⟩

/-- A shared-input Boolean binary gate: constrain the fresh output bit and its
quadratic defining equation. -/
def booleanBinaryGateCost : BackendCost := ⟨2, 2, 1, 2, 0⟩

/-- Negation needs one output-bit equation plus one linear defining equation. -/
def booleanNotGateCost : BackendCost := ⟨2, 1, 1, 2, 0⟩

/-! ## Positive formula structure and exact bounded folds -/

namespace Positive

open PositiveFormula

def atomCount {Atom : Type*} : PositiveFormula Atom → Nat
  | .top | .bottom => 0
  | .atom _ => 1
  | .and p q | .or p q => atomCount p + atomCount q

def andCount {Atom : Type*} : PositiveFormula Atom → Nat
  | .top | .bottom | .atom _ => 0
  | .and p q => andCount p + andCount q + 1
  | .or p q => andCount p + andCount q

def orCount {Atom : Type*} : PositiveFormula Atom → Nat
  | .top | .bottom | .atom _ => 0
  | .and p q => orCount p + orCount q
  | .or p q => orCount p + orCount q + 1

def connectiveCount {Atom : Type*} (p : PositiveFormula Atom) : Nat :=
  andCount p + orCount p

/-- Cost of a materialized positive/no-wrap formula, parameterized by its
atomic relations.  This route has no inverse witnesses unless atoms do. -/
def cost {Atom : Type*} (atomCost : Atom → BackendCost) :
    PositiveFormula Atom → BackendCost
  | .top | .bottom => zero
  | .atom a => atomCost a
  | .and p q => combine (combine (cost atomCost p) (cost atomCost q)) positiveAndGateCost
  | .or p q => combine (combine (cost atomCost p) (cost atomCost q)) positiveOrGateCost

/-- Pure syntax/gate cost, excluding application-specific atom relations. -/
def skeletonCost {Atom : Type*} : PositiveFormula Atom → BackendCost
  | .top | .bottom | .atom _ => zero
  | .and p q => combine (combine (skeletonCost p) (skeletonCost q)) positiveAndGateCost
  | .or p q => combine (combine (skeletonCost p) (skeletonCost q)) positiveOrGateCost

@[simp] theorem skeleton_equations {Atom : Type*} (p : PositiveFormula Atom) :
    (skeletonCost p).equations = connectiveCount p := by
  induction p with
  | top => rfl
  | bottom => rfl
  | atom => rfl
  | and p q ihp ihq =>
      simp [skeletonCost, connectiveCount, andCount, orCount, ihp, ihq,
        positiveAndGateCost, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  | or p q ihp ihq =>
      simp [skeletonCost, connectiveCount, andCount, orCount, ihp, ihq,
        positiveOrGateCost, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem skeleton_multiplications {Atom : Type*} (p : PositiveFormula Atom) :
    (skeletonCost p).multiplications = orCount p := by
  induction p <;>
    simp [skeletonCost, orCount, positiveAndGateCost, positiveOrGateCost,
      *, Nat.add_assoc]

@[simp] theorem skeleton_witnesses {Atom : Type*} (p : PositiveFormula Atom) :
    (skeletonCost p).witnesses = connectiveCount p := by
  induction p with
  | top => rfl
  | bottom => rfl
  | atom => rfl
  | and p q ihp ihq =>
      simp [skeletonCost, connectiveCount, andCount, orCount, ihp, ihq,
        positiveAndGateCost, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  | or p q ihp ihq =>
      simp [skeletonCost, connectiveCount, andCount, orCount, ihp, ihq,
        positiveOrGateCost, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem skeleton_degree_le_two {Atom : Type*} (p : PositiveFormula Atom) :
    (skeletonCost p).maxDegree ≤ 2 := by
  induction p with
  | top => simp [skeletonCost, zero]
  | bottom => simp [skeletonCost, zero]
  | atom => simp [skeletonCost, zero]
  | and p q ihp ihq =>
      exact degree_combine_le (degree_combine_le ihp ihq) (by decide)
  | or p q ihp ihq =>
      exact degree_combine_le (degree_combine_le ihp ihq) (by decide)

/-- The exact equation recurrence for a grounded universal fold. -/
theorem all_equations {Atom : Type*} (atomCost : Atom → BackendCost)
    (ps : List (PositiveFormula Atom)) :
    (cost atomCost (PositiveFormula.all ps)).equations =
      (ps.map (fun p => (cost atomCost p).equations)).sum + ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simp [PositiveFormula.all, cost, ih, positiveAndGateCost, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]

/-- Universal folds add no connective multiplications. -/
theorem all_multiplications {Atom : Type*} (atomCost : Atom → BackendCost)
    (ps : List (PositiveFormula Atom)) :
    (cost atomCost (PositiveFormula.all ps)).multiplications =
      (ps.map (fun p => (cost atomCost p).multiplications)).sum := by
  induction ps <;> simp [PositiveFormula.all, cost, *, positiveAndGateCost]

/-- The exact equation recurrence for a grounded existential fold. -/
theorem any_equations {Atom : Type*} (atomCost : Atom → BackendCost)
    (ps : List (PositiveFormula Atom)) :
    (cost atomCost (PositiveFormula.any ps)).equations =
      (ps.map (fun p => (cost atomCost p).equations)).sum + ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simp [PositiveFormula.any, cost, ih, positiveOrGateCost, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]

/-- Existential products contribute exactly one multiplication per range item. -/
theorem any_multiplications {Atom : Type*} (atomCost : Atom → BackendCost)
    (ps : List (PositiveFormula Atom)) :
    (cost atomCost (PositiveFormula.any ps)).multiplications =
      (ps.map (fun p => (cost atomCost p).multiplications)).sum + ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simp [PositiveFormula.any, cost, ih, positiveOrGateCost, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]

end Positive

/-! ## Exact Boolean graph counts -/

namespace BooleanGraph

open Dregg2.Logic.BoolGraph

def atomCount {Atom : Type*} : Formula Atom → Nat
  | .atom _ => 1
  | .top | .bot => 0
  | .not p => atomCount p
  | .and p q | .or p q => atomCount p + atomCount q

def notCount {Atom : Type*} : Formula Atom → Nat
  | .atom _ | .top | .bot => 0
  | .not p => notCount p + 1
  | .and p q | .or p q => notCount p + notCount q

def binaryCount {Atom : Type*} : Formula Atom → Nat
  | .atom _ | .top | .bot => 0
  | .not p => binaryCount p
  | .and p q | .or p q => binaryCount p + binaryCount q + 1

/-- Shared-wire constraint-graph cost corresponding to `BoolGraph.Graph`.
Inputs are not re-Booleanized at every parent gate. -/
def cost {Atom : Type*} : Formula Atom → BackendCost
  | .atom _ => zeroTestGateCost
  | .top | .bot => zero
  | .not p => combine (cost p) booleanNotGateCost
  | .and p q | .or p q => combine (combine (cost p) (cost q)) booleanBinaryGateCost

theorem equations_exact {Atom : Type*} (p : Formula Atom) :
    (cost p).equations = 3 * atomCount p + 2 * notCount p + 2 * binaryCount p := by
  induction p <;>
    simp [cost, atomCount, notCount, binaryCount, zeroTestGateCost,
      booleanNotGateCost, booleanBinaryGateCost, *, Nat.mul_add,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem multiplications_exact {Atom : Type*} (p : Formula Atom) :
    (cost p).multiplications =
      3 * atomCount p + notCount p + 2 * binaryCount p := by
  induction p <;>
    simp [cost, atomCount, notCount, binaryCount, zeroTestGateCost,
      booleanNotGateCost, booleanBinaryGateCost, *, Nat.mul_add,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem witnesses_exact {Atom : Type*} (p : Formula Atom) :
    (cost p).witnesses = 2 * atomCount p + notCount p + binaryCount p := by
  induction p <;>
    simp [cost, atomCount, notCount, binaryCount, zeroTestGateCost,
      booleanNotGateCost, booleanBinaryGateCost, *, Nat.mul_add,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem degree_le_two {Atom : Type*} (p : Formula Atom) : (cost p).maxDegree ≤ 2 := by
  induction p with
  | atom => simp [cost, zeroTestGateCost]
  | top => simp [cost, zero]
  | bot => simp [cost, zero]
  | not p ih => exact degree_combine_le ih (by decide)
  | and p q ihp ihq => exact degree_combine_le (degree_combine_le ihp ihq) (by decide)
  | or p q ihp ihq => exact degree_combine_le (degree_combine_le ihp ihq) (by decide)

/-- Both `AndFoldGraph` and `OrFoldGraph` add one shared binary gate per list
element (including the gate against the constant base case). -/
def foldCost (n : Nat) : BackendCost := scale n booleanBinaryGateCost

@[simp] theorem fold_equations (n : Nat) : (foldCost n).equations = 2 * n := by
  simp [foldCost, booleanBinaryGateCost, Nat.mul_comm]

@[simp] theorem fold_multiplications (n : Nat) :
    (foldCost n).multiplications = 2 * n := by
  simp [foldCost, booleanBinaryGateCost, Nat.mul_comm]

@[simp] theorem fold_witnesses (n : Nat) : (foldCost n).witnesses = n := by
  simp [foldCost, booleanBinaryGateCost]

end BooleanGraph

/-! ## Enumeration versus a witness-selected existential -/

/-- Enumerate all `n` candidates, compile the body for every candidate, then
OR their Boolean result bits. -/
def enumeratedExistsCost (n : Nat) (body : BackendCost) : BackendCost :=
  combine (scale n body) (BooleanGraph.foldCost n)

/-- One-hot witness-selected existential over a public table.

There are `n` Boolean selector equations, one one-hot equation, `coordinates`
linear output equations, and `n * coordinates` selector/table products.  The
body is checked once.  This cost is sound only when the surrounding relation
also proves that the selected value is in the statement-fixed table; that
obligation is precisely what the one-hot selector accounts for. -/
def selectedExistsCost (n coordinates : Nat) (body : BackendCost) : BackendCost :=
  combine body
    { equations := n + 1 + coordinates
      multiplications := n + n * coordinates
      witnesses := n + coordinates
      maxDegree := 2
      tableCells := n * coordinates }

@[simp] theorem enumerated_multiplications (n : Nat) (body : BackendCost) :
    (enumeratedExistsCost n body).multiplications =
      n * body.multiplications + 2 * n := by
  simp [enumeratedExistsCost]

@[simp] theorem selected_multiplications (n coordinates : Nat) (body : BackendCost) :
    (selectedExistsCost n coordinates body).multiplications =
      body.multiplications + n + n * coordinates := by
  simp [selectedExistsCost, Nat.add_assoc]

@[simp] theorem enumerated_equations (n : Nat) (body : BackendCost) :
    (enumeratedExistsCost n body).equations = n * body.equations + 2 * n := by
  simp [enumeratedExistsCost]

@[simp] theorem selected_equations (n coordinates : Nat) (body : BackendCost) :
    (selectedExistsCost n coordinates body).equations =
      body.equations + (n + 1 + coordinates) := by
  rfl

@[simp] theorem selected_table_cells (n coordinates : Nat) (body : BackendCost) :
    (selectedExistsCost n coordinates body).tableCells =
      body.tableCells + n * coordinates := by
  rfl

/-! ## Finite extensional HOL: exact table-size growth -/

namespace FiniteHOL

open Dregg2.Metatheory.FinitePolynomialFunctions.FiniteHOL

/-- Number of field coordinates in the extensional interpretation of a type,
for a field of cardinality `q`. -/
def coordCount (q : Nat) : Ty → Nat
  | .unit => 0
  | .scalar => 1
  | .prod A B => coordCount q A + coordCount q B
  | .arr A B => q ^ coordCount q A * coordCount q B

/-- Number of extensional values of a type. -/
def valueCount (q : Nat) (A : Ty) : Nat := q ^ coordCount q A

@[simp] theorem coord_unit (q : Nat) : coordCount q .unit = 0 := rfl
@[simp] theorem coord_scalar (q : Nat) : coordCount q .scalar = 1 := rfl
@[simp] theorem coord_prod (q : Nat) (A B : Ty) :
    coordCount q (.prod A B) = coordCount q A + coordCount q B := rfl
@[simp] theorem coord_arrow (q : Nat) (A B : Ty) :
    coordCount q (.arr A B) = valueCount q A * coordCount q B := rfl

/-- The coordinate recurrence as an instance-independent finite cardinality. -/
private theorem natCard_coord {F : Type} [Field F] [Fintype F] (A : Ty) :
    Nat.card (Coord F A) = coordCount (Fintype.card F) A := by
  induction A with
  | unit => simp [Coord, coordCount]
  | scalar => simp [Coord, coordCount]
  | prod A B ihA ihB =>
      change Nat.card (Coord F A ⊕ Coord F B) =
        coordCount (Fintype.card F) A + coordCount (Fintype.card F) B
      rw [Nat.card_sum, ihA, ihB]
  | arr A B ihA ihB =>
      change Nat.card ((Coord F A → F) × Coord F B) =
        Fintype.card F ^ coordCount (Fintype.card F) A *
          coordCount (Fintype.card F) B
      rw [Nat.card_prod, Nat.card_fun, ihA, ihB, Nat.card_eq_fintype_card]

/-- The coordinate recurrence agrees with the actual finite field-power model. -/
theorem card_coord {F : Type} [Field F] [Fintype F] (A : Ty) :
    Fintype.card (Coord F A) = coordCount (Fintype.card F) A := by
  rw [← Nat.card_eq_fintype_card]
  exact natCard_coord A

/-- Consequently the value count is exact, including at function types.
`Val` exports a `Finite` instance but no privileged enumeration, so `Nat.card`
states this invariant without adding an arbitrary `Fintype` choice. -/
theorem card_value {F : Type} [Field F] [Fintype F] (A : Ty) :
    Nat.card (Val F A) = valueCount (Fintype.card F) A := by
  change Nat.card (Coord F A → F) =
    Fintype.card F ^ coordCount (Fintype.card F) A
  rw [Nat.card_fun, natCard_coord, Nat.card_eq_fintype_card]

/-- A dense application table has one cell per input value and output
coordinate.  This is an exact representation size, not a complexity guess. -/
def applicationTableCost (q : Nat) (A B : Ty) : BackendCost :=
  { zero with tableCells := valueCount q A * coordCount q B }

@[simp] theorem application_cells (q : Nat) (A B : Ty) :
    (applicationTableCost q A B).tableCells = coordCount q (.arr A B) := by
  rfl

/-- First-order scalar-to-scalar tables contain exactly `q` cells. -/
theorem scalar_function_cells (q : Nat) :
    (applicationTableCost q .scalar .scalar).tableCells = q := by
  simp [applicationTableCost, valueCount, coordCount]

/-- Quantifying over scalar functions already ranges over `q^q` functions. -/
theorem scalar_function_value_count (q : Nat) :
    valueCount q (.arr .scalar .scalar) = q ^ q := by
  simp [valueCount, coordCount]

/-- A functional taking an arbitrary scalar function as input has `q^q`
table cells even with scalar output: the second-order exponential is literal. -/
theorem second_order_function_cells (q : Nat) :
    (applicationTableCost q (.arr .scalar .scalar) .scalar).tableCells = q ^ q := by
  simp [applicationTableCost, valueCount, coordCount]

/-- At the next order the exact tower is `q^(q^q)`. -/
theorem third_order_function_cells (q : Nat) :
    (applicationTableCost q (.arr (.arr .scalar .scalar) .scalar) .scalar).tableCells =
      q ^ (q ^ q) := by
  simp [applicationTableCost, valueCount, coordCount]

/-- Coordinatewise extensional equality: zero-test every coordinate, then AND
the result bits. -/
def equalityCost (coordinates : Nat) : BackendCost :=
  combine (scale coordinates zeroTestGateCost) (BooleanGraph.foldCost coordinates)

@[simp] theorem equality_equations (coordinates : Nat) :
    (equalityCost coordinates).equations = 5 * coordinates := by
  simp [equalityCost, zeroTestGateCost, Nat.mul_comm]
  omega

@[simp] theorem equality_multiplications (coordinates : Nat) :
    (equalityCost coordinates).multiplications = 5 * coordinates := by
  simp [equalityCost, zeroTestGateCost, Nat.mul_comm]
  omega

/-- Structural cost of evaluating a finite HOL formula by full extensional
enumeration.  A quantified body is emitted once per value of its quantified
type, followed by a Boolean fold of the same length. -/
noncomputable def formulaCost {F : Type} (q : Nat) :
    {Γ : List Ty} → Formula F Γ → BackendCost
  | _, .top | _, .bottom => zero
  | _, @Formula.equal _ _ A _ _ => equalityCost (coordCount q A)
  | _, .and p r | _, .or p r | _, .imp p r =>
      combine (combine (formulaCost q p) (formulaCost q r)) booleanBinaryGateCost
  | _, .not p => combine (formulaCost q p) booleanNotGateCost
  | _, .forall_ A p | _, .exists_ A p =>
      combine (scale (valueCount q A) (formulaCost q p))
        (BooleanGraph.foldCost (valueCount q A))

@[simp] theorem formulaCost_forall {F : Type} (q : Nat) {Γ : List Ty}
    (A : Ty) (p : Formula F (A :: Γ)) :
    formulaCost q (.forall_ A p) =
      combine (scale (valueCount q A) (formulaCost q p))
        (BooleanGraph.foldCost (valueCount q A)) := by
  rfl

@[simp] theorem forall_equations {F : Type} (q : Nat) {Γ : List Ty}
    (A : Ty) (p : Formula F (A :: Γ)) :
    (formulaCost q (.forall_ A p)).equations =
      valueCount q A * (formulaCost q p).equations + 2 * valueCount q A := by
  simp [formulaCost]

@[simp] theorem exists_multiplications {F : Type} (q : Nat) {Γ : List Ty}
    (A : Ty) (p : Formula F (A :: Γ)) :
    (formulaCost q (.exists_ A p)).multiplications =
      valueCount q A * (formulaCost q p).multiplications + 2 * valueCount q A := by
  simp [formulaCost]

/-- A scalar quantifier is linear in `q` copies of its body. -/
theorem scalar_forall_equations {F : Type} (q : Nat) {Γ : List Ty}
    (p : Formula F (.scalar :: Γ)) :
    (formulaCost q (.forall_ .scalar p)).equations =
      q * (formulaCost q p).equations + 2 * q := by
  simp [valueCount, coordCount]

/-- A quantifier over scalar functions emits exactly `q^q` copies/fold gates.
This is the formal performance boundary of full extensional HOL. -/
theorem function_forall_equations {F : Type} (q : Nat) {Γ : List Ty}
    (p : Formula F (.arr .scalar .scalar :: Γ)) :
    (formulaCost q (.forall_ (.arr .scalar .scalar) p)).equations =
      (q ^ q) * (formulaCost q p).equations + 2 * (q ^ q) := by
  simp [valueCount, coordCount]

end FiniteHOL

#assert_all_clean [
  BackendCost.combine_assoc,
  BackendCost.combine_comm,
  Positive.skeleton_equations,
  Positive.skeleton_multiplications,
  Positive.skeleton_witnesses,
  Positive.skeleton_degree_le_two,
  Positive.all_equations,
  Positive.all_multiplications,
  Positive.any_equations,
  Positive.any_multiplications,
  BooleanGraph.equations_exact,
  BooleanGraph.multiplications_exact,
  BooleanGraph.witnesses_exact,
  BooleanGraph.degree_le_two,
  enumerated_multiplications,
  selected_multiplications,
  FiniteHOL.card_coord,
  FiniteHOL.card_value,
  FiniteHOL.scalar_function_cells,
  FiniteHOL.scalar_function_value_count,
  FiniteHOL.second_order_function_cells,
  FiniteHOL.third_order_function_cells,
  FiniteHOL.equality_equations,
  FiniteHOL.equality_multiplications,
  FiniteHOL.forall_equations,
  FiniteHOL.exists_multiplications,
  FiniteHOL.scalar_forall_equations,
  FiniteHOL.function_forall_equations]

end Dregg2.Metatheory.ArithmetizationCost
