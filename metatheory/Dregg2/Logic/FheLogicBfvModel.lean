/-
# Dregg2.Logic.FheLogicBfvModel -- theorem model for the executable BFV fragment

This file is the pure model paired with
`fhegg-fhe/src/fhir/logic_schedule.rs`.  It proves two facts used by that
executable fragment:

* the exact ring identities used by the canonical-bit BFV interpreter preserve
  every finite Boolean program; and
* the centered, bounded residual `sum_i (x_i-y_i)^2` is zero in the plaintext
  ring exactly when every natural equality is true.

The second statement includes the public bound calculation implemented by the
Rust compiler.  No positivity is inferred inside `ZMod p`: positivity is proved
for the natural residual first, the entire sum is bounded strictly below the
centered window, and only then is it cast into the field.

The cost structure mirrors the primitive calls in the Rust interpreter.  It is
an exact symbolic ledger, not a latency, noise, or FHE security theorem.  This
module does not prove that the Rust implementation refines these definitions.

Pure.  No axioms.
-/

import Mathlib.Data.Nat.Dist
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Dregg2.Metatheory.FOLArithmetizationCorrected
import Dregg2.Tactics

namespace Dregg2.Logic.FheLogicBfvModel

set_option autoImplicit false

/-! ## 1. Canonical-bit Boolean BFV model -/

def encodeBool {R : Type*} [Zero R] [One R] : Bool → R
  | false => 0
  | true => 1

/-- The exact source fragment accepted by the Rust BFV interpreter. -/
inductive BooleanProgram where
  | constant : Bool → BooleanProgram
  | input : Nat → BooleanProgram
  | eq : BooleanProgram → BooleanProgram → BooleanProgram
  | not : BooleanProgram → BooleanProgram
  | and : BooleanProgram → BooleanProgram → BooleanProgram
  | or : BooleanProgram → BooleanProgram → BooleanProgram
  deriving DecidableEq, Repr

def BooleanProgram.evalBool (env : Nat → Bool) : BooleanProgram → Bool
  | .constant value => value
  | .input index => env index
  | .eq left right => decide (left.evalBool env = right.evalBool env)
  | .not inner => !(inner.evalBool env)
  | .and left right => left.evalBool env && right.evalBool env
  | .or left right => left.evalBool env || right.evalBool env

/-- Arithmetic executed by the Rust backend.  The equality expression is
written with a duplicated product to match the two ciphertext additions:
`1 - x - y + (xy + xy)`. -/
def BooleanProgram.evalRing {R : Type*} [CommRing R] (env : Nat → Bool) :
    BooleanProgram → R
  | .constant value => encodeBool value
  | .input index => encodeBool (env index)
  | .eq left right =>
      1 - left.evalRing env - right.evalRing env +
        (left.evalRing env * right.evalRing env +
          left.evalRing env * right.evalRing env)
  | .not inner => 1 - inner.evalRing env
  | .and left right => left.evalRing env * right.evalRing env
  | .or left right =>
      left.evalRing env + right.evalRing env -
        left.evalRing env * right.evalRing env

/-- Exact value semantics of every Boolean program over every commutative
ring.  No field ordering or positivity premise is used. -/
theorem BooleanProgram.evalRing_correct {R : Type*} [CommRing R]
    (env : Nat → Bool) (program : BooleanProgram) :
    program.evalRing (R := R) env =
      encodeBool (R := R) (program.evalBool env) := by
  induction program with
  | constant value => rfl
  | input index => rfl
  | eq left right ihLeft ihRight =>
      simp only [BooleanProgram.evalRing, BooleanProgram.evalBool]
      rw [ihLeft, ihRight]
      cases hLeft : left.evalBool env <;>
        cases hRight : right.evalBool env <;>
        simp [encodeBool]
  | not inner ih =>
      simp only [BooleanProgram.evalRing, BooleanProgram.evalBool]
      rw [ih]
      cases hInput : inner.evalBool env <;>
        simp [encodeBool]
  | and left right ihLeft ihRight =>
      simp only [BooleanProgram.evalRing, BooleanProgram.evalBool]
      rw [ihLeft, ihRight]
      cases hLeft : left.evalBool env <;>
        cases hRight : right.evalBool env <;>
        simp [encodeBool]
  | or left right ihLeft ihRight =>
      simp only [BooleanProgram.evalRing, BooleanProgram.evalBool]
      rw [ihLeft, ihRight]
      cases hLeft : left.evalBool env <;>
        cases hRight : right.evalBool env <;>
        simp [encodeBool]

/-! ## 2. Exact Rust-operation ledger -/

structure Cost where
  logicalInputReads : Nat := 0
  encryptedConstantReads : Nat := 0
  ciphertextAdditions : Nat := 0
  ciphertextSubtractions : Nat := 0
  ciphertextMultiplications : Nat := 0
  relinearizations : Nat := 0
  maximumMultiplicativeDepth : Nat := 0
  boundaryZeroDecisions : Nat := 0
  deriving DecidableEq, Repr

def Cost.merge (left right : Cost) : Cost where
  logicalInputReads := left.logicalInputReads + right.logicalInputReads
  encryptedConstantReads :=
    left.encryptedConstantReads + right.encryptedConstantReads
  ciphertextAdditions := left.ciphertextAdditions + right.ciphertextAdditions
  ciphertextSubtractions :=
    left.ciphertextSubtractions + right.ciphertextSubtractions
  ciphertextMultiplications :=
    left.ciphertextMultiplications + right.ciphertextMultiplications
  relinearizations := left.relinearizations + right.relinearizations
  maximumMultiplicativeDepth :=
    max left.maximumMultiplicativeDepth right.maximumMultiplicativeDepth
  boundaryZeroDecisions :=
    left.boundaryZeroDecisions + right.boundaryZeroDecisions

def Cost.withMulGate (cost : Cost) : Cost where
  logicalInputReads := cost.logicalInputReads
  encryptedConstantReads := cost.encryptedConstantReads
  ciphertextAdditions := cost.ciphertextAdditions
  ciphertextSubtractions := cost.ciphertextSubtractions
  ciphertextMultiplications := cost.ciphertextMultiplications + 1
  relinearizations := cost.relinearizations + 1
  maximumMultiplicativeDepth := cost.maximumMultiplicativeDepth + 1
  boundaryZeroDecisions := cost.boundaryZeroDecisions

def BooleanProgram.cost : BooleanProgram → Cost
  | .constant _ => { encryptedConstantReads := 1 }
  | .input _ => { logicalInputReads := 1 }
  | .not inner =>
      let cost := inner.cost
      { cost with
        encryptedConstantReads := cost.encryptedConstantReads + 1
        ciphertextSubtractions := cost.ciphertextSubtractions + 1 }
  | .and left right => (Cost.merge left.cost right.cost).withMulGate
  | .or left right =>
      let cost := (Cost.merge left.cost right.cost).withMulGate
      { cost with
        ciphertextAdditions := cost.ciphertextAdditions + 1
        ciphertextSubtractions := cost.ciphertextSubtractions + 1 }
  | .eq left right =>
      let cost := (Cost.merge left.cost right.cost).withMulGate
      { cost with
        encryptedConstantReads := cost.encryptedConstantReads + 1
        ciphertextAdditions := cost.ciphertextAdditions + 2
        ciphertextSubtractions := cost.ciphertextSubtractions + 2 }

def eqInputs (left right : Nat) : BooleanProgram :=
  .eq (.input left) (.input right)

/-- Balanced conjunction of eight equality atoms, matching the Rust
comparison specimen. -/
def eightEqualityBoolean : BooleanProgram :=
  .and
    (.and
      (.and (eqInputs 0 1) (eqInputs 2 3))
      (.and (eqInputs 4 5) (eqInputs 6 7)))
    (.and
      (.and (eqInputs 8 9) (eqInputs 10 11))
      (.and (eqInputs 12 13) (eqInputs 14 15)))

theorem eightEqualityBoolean_cost : eightEqualityBoolean.cost =
    { logicalInputReads := 16
      encryptedConstantReads := 8
      ciphertextAdditions := 16
      ciphertextSubtractions := 16
      ciphertextMultiplications := 15
      relinearizations := 15
      maximumMultiplicativeDepth := 4 : Cost } := by decide

/-! ## 3. Centered squared-equality residual -/

def squaredDistance (pair : Nat × Nat) : Nat :=
  Nat.dist pair.1 pair.2 ^ 2

def residualSum (pairs : List (Nat × Nat)) : Nat :=
  (pairs.map squaredDistance).sum

theorem squaredDistance_eq_zero_iff (pair : Nat × Nat) :
    squaredDistance pair = 0 ↔ pair.1 = pair.2 := by
  rcases pair with ⟨left, right⟩
  change Nat.dist left right ^ 2 = 0 ↔ left = right
  rw [sq_eq_zero_iff]
  constructor
  · intro hzero
    unfold Nat.dist at hzero
    omega
  · rintro rfl
    simp

theorem residualSum_eq_zero_iff (pairs : List (Nat × Nat)) :
    residualSum pairs = 0 ↔ ∀ pair ∈ pairs, pair.1 = pair.2 := by
  induction pairs with
  | nil => simp [residualSum]
  | cons pair pairs ih =>
      change squaredDistance pair + residualSum pairs = 0 ↔
        ∀ candidate ∈ pair :: pairs, candidate.1 = candidate.2
      rw [Nat.add_eq_zero_iff, squaredDistance_eq_zero_iff, ih]
      simp

/-- Public range premise mirrored by the Rust declarations. -/
def PairsBounded (bound : Nat) (pairs : List (Nat × Nat)) : Prop :=
  ∀ pair ∈ pairs, pair.1 ≤ bound ∧ pair.2 ≤ bound

theorem squaredDistance_le {bound : Nat} {pair : Nat × Nat}
    (hbound : pair.1 ≤ bound ∧ pair.2 ≤ bound) :
    squaredDistance pair ≤ bound ^ 2 := by
  rcases pair with ⟨left, right⟩
  have hdist : Nat.dist left right ≤ bound := by
    unfold Nat.dist
    omega
  exact Nat.pow_le_pow_left hdist 2

/-- Static public bound used by the Rust no-wrap compiler. -/
theorem residualSum_le (bound : Nat) (pairs : List (Nat × Nat))
    (hbound : PairsBounded bound pairs) :
    residualSum pairs ≤ pairs.length * bound ^ 2 := by
  induction pairs with
  | nil => simp [residualSum]
  | cons pair pairs ih =>
      have hpair : squaredDistance pair ≤ bound ^ 2 :=
        squaredDistance_le (hbound pair (by simp))
      have htail : PairsBounded bound pairs := by
        intro candidate hcandidate
        exact hbound candidate (by simp [hcandidate])
      have ih' := ih htail
      have hadd := Nat.add_le_add hpair ih'
      simpa [residualSum, Nat.succ_mul, Nat.add_comm] using hadd

/-- Actual arithmetic polynomial executed by the BFV residual backend. -/
def fieldResidual (p : Nat) (pairs : List (Nat × Nat)) : ZMod p :=
  (pairs.map fun pair : Nat × Nat =>
    ((pair.1 : ZMod p) - (pair.2 : ZMod p)) ^ 2).sum

theorem cast_squaredDistance (p : Nat) (pair : Nat × Nat) :
    (squaredDistance pair : ZMod p) =
      ((pair.1 : ZMod p) - (pair.2 : ZMod p)) ^ 2 := by
  rcases pair with ⟨left, right⟩
  rcases le_total left right with hle | hle
  · rw [squaredDistance, Nat.dist_eq_sub_of_le hle, Nat.cast_pow,
      Nat.cast_sub hle]
    ring
  · rw [squaredDistance, Nat.dist_eq_sub_of_le_right hle, Nat.cast_pow,
      Nat.cast_sub hle]

theorem fieldResidual_eq_cast (p : Nat) (pairs : List (Nat × Nat)) :
    fieldResidual p pairs = (residualSum pairs : ZMod p) := by
  induction pairs with
  | nil => simp [fieldResidual, residualSum]
  | cons pair pairs ih =>
      change
        ((pair.1 : ZMod p) - (pair.2 : ZMod p)) ^ 2 + fieldResidual p pairs =
          ((squaredDistance pair + residualSum pairs : Nat) : ZMod p)
      rw [Nat.cast_add, ih, cast_squaredDistance]

/-- The exact centered-window certificate used by the executable backend. -/
def NoWrapCertificate (p bound : Nat) (pairs : List (Nat × Nat)) : Prop :=
  pairs.length * bound ^ 2 < (p - 1) / 2

/-- Soundness of the deployed residual polynomial.  The theorem never appeals
to an order on `ZMod p`: it bounds the exact natural residual before casting. -/
theorem fieldResidual_eq_zero_iff_of_certificate
    {p bound : Nat} {pairs : List (Nat × Nat)}
    (hp : 2 < p)
    (hbounded : PairsBounded bound pairs)
    (hcertificate : NoWrapCertificate p bound pairs) :
    fieldResidual p pairs = 0 ↔
      ∀ pair ∈ pairs, pair.1 = pair.2 := by
  rw [fieldResidual_eq_cast]
  have hresidual : residualSum pairs < p := by
    have hle := residualSum_le bound pairs hbounded
    unfold NoWrapCertificate at hcertificate
    have hcenter : (p - 1) / 2 < p := by omega
    omega
  rw [Dregg2.Metatheory.FOLArithmetizationCorrected.zmod_natCast_eq_zero_iff_of_lt
    hresidual]
  exact residualSum_eq_zero_iff pairs

/-- Rust-operation ledger of the residual path.  The final zero decision is a
required external boundary and therefore remains zero in this execution cost. -/
def residualCost (pairCount : Nat) : Cost :=
  { logicalInputReads := 2 * pairCount
    ciphertextAdditions := pairCount - 1
    ciphertextSubtractions := pairCount
    ciphertextMultiplications := pairCount
    relinearizations := pairCount
    maximumMultiplicativeDepth := if pairCount = 0 then 0 else 1 }

theorem eightEqualityResidual_cost : residualCost 8 =
    { logicalInputReads := 16
      ciphertextAdditions := 7
      ciphertextSubtractions := 8
      ciphertextMultiplications := 8
      relinearizations := 8
      maximumMultiplicativeDepth := 1 : Cost } := by decide

theorem eightEqualityResidual_strictly_fewer_multiplications :
    (residualCost 8).ciphertextMultiplications <
      eightEqualityBoolean.cost.ciphertextMultiplications := by decide

theorem eightEqualityResidual_strictly_smaller_depth :
    (residualCost 8).maximumMultiplicativeDepth <
      eightEqualityBoolean.cost.maximumMultiplicativeDepth := by decide

#assert_all_clean [
  BooleanProgram.evalRing_correct,
  eightEqualityBoolean_cost,
  squaredDistance_eq_zero_iff,
  residualSum_eq_zero_iff,
  squaredDistance_le,
  residualSum_le,
  cast_squaredDistance,
  fieldResidual_eq_cast,
  fieldResidual_eq_zero_iff_of_certificate,
  eightEqualityResidual_cost,
  eightEqualityResidual_strictly_fewer_multiplications,
  eightEqualityResidual_strictly_smaller_depth
]

end Dregg2.Logic.FheLogicBfvModel
