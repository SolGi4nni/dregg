/-
# Market.PrivateBookBfvSliceDescriptor

The first executable, native-field proof slice of the exact private-book BFV
opening relation.  This is deliberately a *coefficient slice*, not a random
linear projection: all 4096 secret coefficients participate in the exact
negacyclic equation for `(order=0, ciphertext-poly=0, modulus=0, coeff=0)`.

The trace also carries the complete Lean-authored Dark Bazaar relation and
binds the ordered public-key coefficients into an eight-lane Poseidon2 chain.
The selected BFV message coefficient is chosen by fresh quantity one-hots tied
to the same private order columns that produce the public eight-lane book root.

Production geometry is `4 orders × 2 ciphertext polynomials × 3 moduli × 4096
coefficients = 98,304` exact equations.  This descriptor proves one complete
4096-term equation.  The remaining 98,303 slices are a mechanical family lift;
an NTT lowering is the performance follow-up, not a semantic substitute.
-/
import Market.DarkBazaarPrivateDescriptor
import Market.PrivateBookBfvBindingAir
import Dregg2.Circuit.DescriptorIR2

namespace Market.PrivateBookBfvSliceDescriptor

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 TableId WindowExpr WindowConstraint
    chipLookupTupleN emitVmJson2)
open Market.DarkBazaarPrivateDescriptor
open Dregg2.Crypto.WgpuBfvNttSpec (Poly negacyclicMul negacyclicTerm rhsIndex)

set_option autoImplicit false

/-! ## Fixed production slice and exact integer radix. -/

def DEGREE : Nat := 4096
def RADIX : Int := 32768
def MODULUS : Int := 68719403009
def MODULUS_LIMBS : List Int := [24577, 32765, 63]
def MODULUS_MINUS_ONE_LIMBS : List Int := [24576, 32765, 63]

/-- The exact public-key schedule carried by row `i`: coefficient zero is
ordinary, then rows `1..4095` consume `pk[4096-i]` with a negative sign.  This
is the schoolbook `X^4096 = -1` coefficient-zero equation used by the imported
full 98,304-equation semantics, not a host-selected projection. -/
theorem coefficientZero_negacyclic_schedule {q : Nat} (u pk : Poly q 4096) :
    negacyclicMul u pk (0 : Fin 4096) =
      u 0 * pk 0 + ∑ i : Fin 4095,
        -(u i.succ * pk ⟨4095 - i.val, by
          have hi := i.isLt
          omega⟩) := by
  rw [Dregg2.Crypto.WgpuBfvNttSpec.negacyclicMul_apply, Fin.sum_univ_succ]
  simp [negacyclicTerm, rhsIndex]

/-- Domain separation for the ordered public-key coefficient chain. -/
def PK_CHAIN_DOMAIN : Int := 1346523979
/-- Packs `(order=0, poly=0, modulus=0, coefficient=0)` into one fixed tag. -/
def SLICE_TAG : Int := 1111903040

/-! ## Extended trace layout.  Columns `0..181` are exactly the existing
Dark Bazaar descriptor, so its full private root and clearing constraints are
included byte-for-byte below. -/

def QTY_SEL_BASE : Nat := TRACE_WIDTH
def QTY_SEL (order qty : Nat) : Nat := QTY_SEL_BASE + 16 * order + qty

def NEG : Nat := 245
def LAST : Nat := 246
def INDEX : Nat := 247
def U_SHIFT : Nat := 248
def U_BIT_BASE : Nat := 249
def U_BIT (b : Nat) : Nat := U_BIT_BASE + b
def ERROR_SHIFT : Nat := 255
def ERROR_BIT_BASE : Nat := 256
def ERROR_BIT (b : Nat) : Nat := ERROR_BIT_BASE + b
def REDUCTION_SHIFT : Nat := 262
def REDUCTION_BIT_BASE : Nat := 263
def REDUCTION_BIT (b : Nat) : Nat := REDUCTION_BIT_BASE + b

def PK_BASE : Nat := 270
def PK (limb : Nat) : Nat := PK_BASE + limb
def PK_SLACK_BASE : Nat := 273
def PK_SLACK (limb : Nat) : Nat := PK_SLACK_BASE + limb
def PK_CAN_CARRY_BASE : Nat := 276
def PK_CAN_CARRY (limb : Nat) : Nat := PK_CAN_CARRY_BASE + limb

def ACC_BEFORE_BASE : Nat := 278
def ACC_BEFORE (limb : Nat) : Nat := ACC_BEFORE_BASE + limb
def ACC_AFTER_BASE : Nat := 281
def ACC_AFTER (limb : Nat) : Nat := ACC_AFTER_BASE + limb
def ACC_SLACK_BASE : Nat := 284
def ACC_SLACK (limb : Nat) : Nat := ACC_SLACK_BASE + limb
def ACC_CAN_CARRY_BASE : Nat := 287
def ACC_CAN_CARRY (limb : Nat) : Nat := ACC_CAN_CARRY_BASE + limb

def ARITH_CARRY_SHIFT_BASE : Nat := 289
def ARITH_CARRY_SHIFT (limb : Nat) : Nat := ARITH_CARRY_SHIFT_BASE + limb

def PREV_PK_ROOT_BASE : Nat := 292
def PREV_PK_ROOT (lane : Nat) : Nat := PREV_PK_ROOT_BASE + lane
def NEXT_PK_ROOT_BASE : Nat := 300
def NEXT_PK_ROOT (lane : Nat) : Nat := NEXT_PK_ROOT_BASE + lane

def PK_BIT_BASE : Nat := 308
def PK_BIT (limb bit : Nat) : Nat := PK_BIT_BASE + 15 * limb + bit
def PK_SLACK_BIT_BASE : Nat := 353
def PK_SLACK_BIT (limb bit : Nat) : Nat := PK_SLACK_BIT_BASE + 15 * limb + bit
def ACC_AFTER_BIT_BASE : Nat := 398
def ACC_AFTER_BIT (limb bit : Nat) : Nat := ACC_AFTER_BIT_BASE + 15 * limb + bit
def ACC_SLACK_BIT_BASE : Nat := 443
def ACC_SLACK_BIT (limb bit : Nat) : Nat := ACC_SLACK_BIT_BASE + 15 * limb + bit
def ARITH_CARRY_BIT_BASE : Nat := 488
def ARITH_CARRY_BIT (limb bit : Nat) : Nat := ARITH_CARRY_BIT_BASE + 9 * limb + bit

def BFV_TRACE_WIDTH : Nat := 515

/-! ## Exact deployed SIMD-message table, modulus 0 / coefficient 0.

The 128 entries are ordered `kind * 16 + quantity`.  They are extracted from
the real `fhe.rs` encoder by equal-randomness subtraction and are independently
differential-tested by the Rust producer. -/

def MESSAGE_COEFF0 : List Int :=
  [ 0, 64737485388, 60755567768, 56773650148, 52791732528, 48809814908, 44827897288
  , 40845979668, 36864062048, 32882144428, 28900226808, 24918309188, 20936391568
  , 16954473948, 12972556328, 8990638708, 37735010824, 2768701020, 36521794225
  , 1555484421, 35308577626, 342267822, 34095361027, 67848454232, 32882144428
  , 66635237633, 31668927829, 65422021034, 30455711230, 64208804435, 29242494631
  , 62995587836, 6750618640, 9519319661, 12288020682, 15056721703, 17825422724
  , 20594123745, 23362824766, 26131525787, 28900226808, 31668927829, 34437628850
  , 37206329871, 39975030892, 42743731913, 45512432934, 48281133955, 44485629465
  , 16269938302, 56773650148, 28557958985, 342267822, 40845979668, 12630288505
  , 53134000351, 24918309188, 65422021034, 37206329871, 8990638708, 49494350554
  , 21278659391, 61782371237, 33566680074, 13501237281, 54004949127, 25789257964
  , 66292969810, 38077278647, 9861587484, 50365299330, 22149608167, 62653320013
  , 34437628850, 6221937687, 46725649533, 18509958370, 59013670216, 30797979053
  , 2582287890, 51236248106, 54004949127, 56773650148, 59542351169, 62311052190
  , 65079753211, 67848454232, 1897752244, 4666453265, 7435154286, 10203855307
  , 12972556328, 15741257349, 18509958370, 21278659391, 24047360412, 20251855922
  , 54004949127, 19038639323, 52791732528, 17825422724, 51578515929, 16612206125
  , 50365299330, 15398989526, 49152082731, 14185772927, 47938866132, 12972556328
  , 46725649533, 11759339729, 45512432934, 57986866747, 54004949127, 50023031507
  , 46041113887, 42059196267, 38077278647, 34095361027, 30113443407, 26131525787
  , 22149608167, 18167690547, 14185772927, 10203855307, 6221937687, 2240020067
  , 66977505456 ]

def messageCoeff (kind qty : Nat) : Int :=
  MESSAGE_COEFF0.getD (16 * kind + qty) 0

def messageLimb (limb kind qty : Nat) : Int :=
  (messageCoeff kind qty / RADIX ^ limb) % RADIX

/-! ## Polynomial helpers. -/

def signedU : EmittedExpr :=
  mul (sub (v U_SHIFT) (c 32)) (sub (c 1) (weighted 2 (v NEG)))

def signedError : EmittedExpr := sub (v ERROR_SHIFT) (c 32)
def signedReduction : EmittedExpr := sub (v REDUCTION_SHIFT) (c 64)
def signedCarry (limb : Nat) : EmittedExpr :=
  sub (v (ARITH_CARRY_SHIFT limb)) (c 256)

def messageLimbExpr (limb : Nat) : EmittedExpr :=
  sumE ((List.range 8).flatMap fun kind =>
    (List.range 16).map fun qty =>
      weighted (messageLimb limb kind qty)
        (mul (v (KIND 0 kind)) (v (QTY_SEL 0 qty))))

def bitBodies (col : Nat) (bit : Nat → Nat) (bits : Nat) : List EmittedExpr :=
  recompose col bit bits :: (List.range bits).map (fun b => binaryBody (bit b))

def limbBitBodies (col : Nat → Nat) (bit : Nat → Nat → Nat) : List EmittedExpr :=
  (List.range 3).flatMap fun limb => bitBodies (col limb) (bit limb) 15

def qtySelectorBodies (order : Nat) : List EmittedExpr :=
  ((List.range 16).map fun qty => binaryBody (QTY_SEL order qty)) ++
  [ sub (sumE ((List.range 16).map fun qty => v (QTY_SEL order qty))) (c 1)
  , sub (v (QTY order))
      (sumE ((List.range 16).map (fun (qty : Nat) =>
        weighted (Int.ofNat qty) (v (QTY_SEL order qty))))) ]

def canonicalBodies (value slack carry : Nat → Nat) : List EmittedExpr :=
  [ sub
      (sub (add (v (value 0)) (v (slack 0))) (c (MODULUS_MINUS_ONE_LIMBS.getD 0 0)))
      (weighted RADIX (v (carry 0)))
  , sub
      (sub (add (add (v (value 1)) (v (slack 1))) (v (carry 0)))
        (c (MODULUS_MINUS_ONE_LIMBS.getD 1 0)))
      (weighted RADIX (v (carry 1)))
  , sub (add (add (v (value 2)) (v (slack 2))) (v (carry 1)))
      (c (MODULUS_MINUS_ONE_LIMBS.getD 2 0))
  , binaryBody (carry 0)
  , binaryBody (carry 1) ]

def arithmeticBody (limb : Nat) : EmittedExpr :=
  let carryIn := if limb = 0 then c 0 else signedCarry (limb - 1)
  let carryOut := signedCarry limb
  let error := if limb = 0 then signedError else c 0
  sub
    (add
      (add
        (add
          (add (v (ACC_BEFORE limb)) (mul signedU (v (PK limb))))
          (neg (mul signedReduction (c (MODULUS_LIMBS.getD limb 0)))))
        carryIn)
      (mul (v LAST) (add error (messageLimbExpr limb))))
    (add (v (ACC_AFTER limb)) (weighted RADIX carryOut))

def bfvRowBodies : List EmittedExpr :=
  [binaryBody NEG, binaryBody LAST] ++
  bitBodies U_SHIFT U_BIT 6 ++
  bitBodies ERROR_SHIFT ERROR_BIT 6 ++
  bitBodies REDUCTION_SHIFT REDUCTION_BIT 7 ++
  ((List.range 4).flatMap qtySelectorBodies) ++
  limbBitBodies PK PK_BIT ++
  limbBitBodies PK_SLACK PK_SLACK_BIT ++
  limbBitBodies ACC_AFTER ACC_AFTER_BIT ++
  limbBitBodies ACC_SLACK ACC_SLACK_BIT ++
  ((List.range 3).flatMap fun limb =>
    bitBodies (ARITH_CARRY_SHIFT limb) (ARITH_CARRY_BIT limb) 9) ++
  canonicalBodies PK PK_SLACK PK_CAN_CARRY ++
  canonicalBodies ACC_AFTER ACC_SLACK ACC_CAN_CARRY ++
  (List.range 3).map arithmeticBody ++
  [signedCarry 2]

/-! ## Ordered public-key commitment and trace continuity. -/

def pkChainInputs : List EmittedExpr :=
  [c PK_CHAIN_DOMAIN, c SLICE_TAG, v INDEX, v (PK 0), v (PK 1), v (PK 2)] ++
  (List.range 8).map (fun lane => v (PREV_PK_ROOT lane)) ++ [c 0, c 0]

def pkChainLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2,
    chipLookupTupleN pkChainInputs ((List.range 8).map NEXT_PK_ROOT)⟩

def wneg (x : WindowExpr) : WindowExpr := .mul (.const (-1)) x
def wsub (x y : WindowExpr) : WindowExpr := .add x (wneg y)

/-- Continuity for arbitrary absolute trace columns.  The embedded v1
`.transition hi lo` constructor is deliberately *not* used here: its indices
address the fixed EffectVM state-before/state-after faces rather than raw
columns. -/
def columnTransition (nextCol localCol : Nat) : VmConstraint2 :=
  .windowGate ⟨wsub (.nxt nextCol) (.loc localCol), true⟩

def holdDarkBazaar : List VmConstraint2 :=
  (List.range TRACE_WIDTH).map fun col => columnTransition col col

def accumulatorTransitions : List VmConstraint2 :=
  (List.range 3).map fun limb => columnTransition (ACC_BEFORE limb) (ACC_AFTER limb)

def pkChainTransitions : List VmConstraint2 :=
  (List.range 8).map fun lane => columnTransition (PREV_PK_ROOT lane) (NEXT_PK_ROOT lane)

def indexTransition : VmConstraint2 :=
  .windowGate ⟨wsub (.nxt INDEX) (.add (.loc INDEX) (.const 1)), true⟩

def negTransition : VmConstraint2 :=
  .windowGate ⟨wsub (.nxt NEG) (.const 1), true⟩

def lastTransition : VmConstraint2 :=
  .windowGate ⟨.loc LAST, true⟩

def firstPins : List VmConstraint2 :=
  [ .base (.boundary .first (v INDEX))
  , .base (.boundary .first (v NEG)) ] ++
  (List.range 3).map (fun limb => .base (.boundary .first (v (ACC_BEFORE limb)))) ++
  (List.range 8).map (fun lane => .base (.boundary .first (v (PREV_PK_ROOT lane))))

def lastPins : List VmConstraint2 :=
  [ .base (.boundary .last (sub (v INDEX) (c 4095)))
  , .base (.boundary .last (sub (v NEG) (c 1)))
  , .base (.boundary .last (sub (v LAST) (c 1))) ] ++
  (List.range 8).map (fun lane =>
    .base (.piBinding .last (NEXT_PK_ROOT lane) (12 + lane))) ++
  (List.range 3).map (fun limb =>
    .base (.piBinding .last (ACC_AFTER limb) (20 + limb)))

def bfvAllRows : List VmConstraint2 :=
  bfvRowBodies.map (fun body => .base (.gate body)) ++
  bfvRowBodies.map (fun body => .base (.boundary .last body))

/-- The executable native-PQ relation.  Rust fills this layout; every equation,
range tooth, continuity law, commitment lookup, and public pin is Lean-authored. -/
def privateBookBfvSliceDescriptor : EffectVmDescriptor2 :=
  { name := "private-book-bfv-slice-o0-c0-q0-k0::exact-wide-v1"
  , traceWidth := BFV_TRACE_WIDTH
  , piCount := 23
  , tables := []
  , constraints :=
      darkBazaarPrivateN4K4Descriptor.constraints ++
      [pkChainLookup] ++ holdDarkBazaar ++ accumulatorTransitions ++
      pkChainTransitions ++ [indexTransition, negTransition, lastTransition] ++
      firstPins ++ lastPins ++ bfvAllRows
  , hashSites := []
  , ranges := [] }

#guard BFV_TRACE_WIDTH == 515
#guard pkChainInputs.length == 16
#guard MESSAGE_COEFF0.length == 128
#guard privateBookBfvSliceDescriptor.piCount == 23
#guard privateBookBfvSliceDescriptor.traceWidth == 515
#guard (emitVmJson2 privateBookBfvSliceDescriptor).contains "window_gate"
#guard (emitVmJson2 privateBookBfvSliceDescriptor).contains "\"table\":1"
#guard !(emitVmJson2 privateBookBfvSliceDescriptor).contains "68719403010"

#assert_all_clean [
  Market.PrivateBookBfvSliceDescriptor.coefficientZero_negacyclic_schedule]

end Market.PrivateBookBfvSliceDescriptor
