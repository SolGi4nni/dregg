/-
# Market.PrivateBookBfvButterflyAir -- executable 48-column BFV butterfly slice

`PrivateBookBfvNttFamily` fixed the production row budget but deliberately left
the butterfly AIR open.  This file makes that row concrete.  The 48 columns are
exactly the inventory already budgeted there:

* eight schedule/routing coordinates;
* six residues in three radix-`2^14` limbs;
* one three-limb product quotient;
* two modular-add/subtract reduction bits;
* five product carries, three add carries, and three subtract carries;
* four read/write permutation-bus tags; and
* first/last-stage selectors.

The descriptor is Lean-authored IR2.  Its row equations use small limb
convolutions, so no `q0^2` value is ever embedded in BabyBear.  A complete
12-row, `N = 8` forward transform over the first production BFV modulus is
generated here, checked by the kernel executable `Satisfied2` decider, and
joined by an exact cross-stage multiset/permutation check.  Mutating arithmetic,
the canonical schedule, the stage bus, or the row count rejects.

This is a descriptor *slice*, not the complete `2^20` family proof.  Its two
custom tables are fixed by the executable gate below; a production emission
still needs a committed/faithed permutation-table semantics in the Rust IR2
consumer, the first-stage twist/bit-reversal ingress, inverse normalization,
terminal BFV quotient rows, and the recursive key-certificate join.
-/
import Market.PrivateBookBfvNttFamily
import Dregg2.Circuit.DecideSatisfied2
import Dregg2.Tactics

namespace Market.PrivateBookBfvButterflyAir

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRange)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.DecideSatisfied2
open Market.PrivateBookBfvNttFamily

set_option autoImplicit false

/-! ## 1. The exact 48-column row -/

def RADIX : Nat := 2 ^ 14
def CARRY_SHIFT : Int := 32768
def N : Nat := 8
def LOG_N : Nat := 3
def Q : Nat := Q0
def PSI : Nat := PSI0

-- Eight schedule/routing coordinates.
def DIRECTION : Nat := 0
def STAGE : Nat := 1
def BUTTERFLY : Nat := 2
def MODULUS_ROW : Nat := 3
def TRANSFORM : Nat := 4
def LEFT_INDEX : Nat := 5
def RIGHT_INDEX : Nat := 6
def TWIDDLE_INDEX : Nat := 7

-- Six three-limb canonical residues.
def LEFT_INPUT : Nat := 8
def RIGHT_INPUT : Nat := 11
def TWIDDLE : Nat := 14
def TWIDDLED_RIGHT : Nat := 17
def LEFT_OUTPUT : Nat := 20
def RIGHT_OUTPUT : Nat := 23

-- Product quotient and the two add/subtract reduction flags.
def PRODUCT_QUOTIENT : Nat := 26
def ADD_REDUCE : Nat := 29
def SUB_REDUCE : Nat := 30

-- 5 product + 3 add + 3 subtract carries.
def PRODUCT_CARRY : Nat := 31
def ADD_CARRY : Nat := 36
def SUB_CARRY : Nat := 39

-- Four tags consumed by the cross-stage permutation bus.
def READ_LEFT_TAG : Nat := 42
def READ_RIGHT_TAG : Nat := 43
def WRITE_LEFT_TAG : Nat := 44
def WRITE_RIGHT_TAG : Nat := 45

-- The two formerly-reserved columns now pin the transform boundary stages.
def FIRST_STAGE : Nat := 46
def LAST_STAGE : Nat := 47

def TRACE_WIDTH : Nat := 48

theorem trace_width_matches_family :
    TRACE_WIDTH = PrivateBookBfvNttFamily.NTT_TRACE_WIDTH := by
  norm_num [TRACE_WIDTH, PrivateBookBfvNttFamily.NTT_TRACE_WIDTH]

def limbNat (x limb : Nat) : Nat := (x / RADIX ^ limb) % RADIX
def limbInt (x limb : Nat) : Int := Int.ofNat (limbNat x limb)
def qLimb (limb : Nat) : Int := limbInt Q limb

#guard [qLimb 0, qLimb 1, qLimb 2] == [8193, 16379, 255]

/-- The worst three-limb product equation remains strictly inside one
BabyBear representative even after both signed carry terms.  Together with the
14/8/16-bit range teeth below, this is the numeric headroom needed to lift a
zero field residue back to the intended integer limb equality. -/
theorem product_limb_equation_headroom :
    3 * (RADIX - 1) ^ 2 + CARRY_SHIFT + (RADIX - 1) +
      (qLimb 0 + qLimb 1 + qLimb 2) * (RADIX - 1) +
      Int.ofNat RADIX * CARRY_SHIFT < 2013265921 := by
  norm_num [RADIX, CARRY_SHIFT, qLimb, limbInt, limbNat, Q, Q0]

/-! ## 2. Lean-authored row equations -/

def ev (col : Nat) : EmittedExpr := .var col
def ec (value : Int) : EmittedExpr := .const value
def eadd (left right : EmittedExpr) : EmittedExpr := .add left right
def emul (left right : EmittedExpr) : EmittedExpr := .mul left right
def eneg (value : EmittedExpr) : EmittedExpr := emul (ec (-1)) value
def esub (left right : EmittedExpr) : EmittedExpr := eadd left (eneg right)

def residueLimb (base limb : Nat) : EmittedExpr := ev (base + limb)
def carryValue (base limb : Nat) : EmittedExpr :=
  esub (ev (base + limb)) (ec CARRY_SHIFT)

def conv3Expr (left right degree : Nat) : EmittedExpr :=
  match degree with
  | 0 => emul (residueLimb left 0) (residueLimb right 0)
  | 1 => eadd
      (emul (residueLimb left 0) (residueLimb right 1))
      (emul (residueLimb left 1) (residueLimb right 0))
  | 2 => eadd
      (eadd
        (emul (residueLimb left 0) (residueLimb right 2))
        (emul (residueLimb left 1) (residueLimb right 1)))
      (emul (residueLimb left 2) (residueLimb right 0))
  | 3 => eadd
      (emul (residueLimb left 1) (residueLimb right 2))
      (emul (residueLimb left 2) (residueLimb right 1))
  | 4 => emul (residueLimb left 2) (residueLimb right 2)
  | _ => ec 0

def quotientTimesQExpr (degree : Nat) : EmittedExpr :=
  match degree with
  | 0 => emul (residueLimb PRODUCT_QUOTIENT 0) (ec (qLimb 0))
  | 1 => eadd
      (emul (residueLimb PRODUCT_QUOTIENT 0) (ec (qLimb 1)))
      (emul (residueLimb PRODUCT_QUOTIENT 1) (ec (qLimb 0)))
  | 2 => eadd
      (eadd
        (emul (residueLimb PRODUCT_QUOTIENT 0) (ec (qLimb 2)))
        (emul (residueLimb PRODUCT_QUOTIENT 1) (ec (qLimb 1))))
      (emul (residueLimb PRODUCT_QUOTIENT 2) (ec (qLimb 0)))
  | 3 => eadd
      (emul (residueLimb PRODUCT_QUOTIENT 1) (ec (qLimb 2)))
      (emul (residueLimb PRODUCT_QUOTIENT 2) (ec (qLimb 1)))
  | 4 => emul (residueLimb PRODUCT_QUOTIENT 2) (ec (qLimb 2))
  | _ => ec 0

/-- One degree of `right * twiddle = twiddled + quotient * q`, with an exact
signed radix carry.  The degree-four carry is separately forced to zero. -/
def productBody (degree : Nat) : EmittedExpr :=
  let carryIn := if degree = 0 then ec 0 else carryValue PRODUCT_CARRY (degree - 1)
  let carryOut := carryValue PRODUCT_CARRY degree
  let residue := if degree < 3 then residueLimb TWIDDLED_RIGHT degree else ec 0
  esub
    (esub (eadd (conv3Expr RIGHT_INPUT TWIDDLE degree) carryIn) residue)
    (eadd (quotientTimesQExpr degree) (emul (ec (Int.ofNat RADIX)) carryOut))

/-- `left + twiddled = left_output + add_reduce * q`. -/
def addBody (limb : Nat) : EmittedExpr :=
  let carryIn := if limb = 0 then ec 0 else carryValue ADD_CARRY (limb - 1)
  let carryOut := carryValue ADD_CARRY limb
  esub
    (eadd (eadd (residueLimb LEFT_INPUT limb)
      (residueLimb TWIDDLED_RIGHT limb)) carryIn)
    (eadd (eadd (residueLimb LEFT_OUTPUT limb)
      (emul (ev ADD_REDUCE) (ec (qLimb limb))))
      (emul (ec (Int.ofNat RADIX)) carryOut))

/-- `left - twiddled + sub_reduce * q = right_output`. -/
def subBody (limb : Nat) : EmittedExpr :=
  let carryIn := if limb = 0 then ec 0 else carryValue SUB_CARRY (limb - 1)
  let carryOut := carryValue SUB_CARRY limb
  esub
    (eadd
      (eadd (esub (residueLimb LEFT_INPUT limb)
        (residueLimb TWIDDLED_RIGHT limb))
        (emul (ev SUB_REDUCE) (ec (qLimb limb))))
      carryIn)
    (eadd (residueLimb RIGHT_OUTPUT limb)
      (emul (ec (Int.ofNat RADIX)) carryOut))

def boolBody (col : Nat) : EmittedExpr :=
  emul (ev col) (esub (ev col) (ec 1))

def stagePoly : EmittedExpr :=
  emul (ev STAGE) (emul (esub (ev STAGE) (ec 1)) (esub (ev STAGE) (ec 2)))

def butterflyPoly : EmittedExpr :=
  emul (ev BUTTERFLY)
    (emul (esub (ev BUTTERFLY) (ec 1))
      (emul (esub (ev BUTTERFLY) (ec 2)) (esub (ev BUTTERFLY) (ec 3))))

def stage0Selector : EmittedExpr :=
  emul (esub (ev STAGE) (ec 1)) (esub (ev STAGE) (ec 2))
def stage1Selector : EmittedExpr :=
  emul (ev STAGE) (esub (ev STAGE) (ec 2))
def stage2Selector : EmittedExpr :=
  emul (ev STAGE) (esub (ev STAGE) (ec 1))

def butterflyCube : EmittedExpr :=
  emul (ev BUTTERFLY) (emul (ev BUTTERFLY) (ev BUTTERFLY))
def butterflySquare : EmittedExpr := emul (ev BUTTERFLY) (ev BUTTERFLY)

/-- Stage 1's left-index map is `[0,1,4,5]`; multiplied by three it is the
integer polynomial `-2b^3 + 9b^2 - 4b`. -/
def stage1LeftTimes3 : EmittedExpr :=
  eadd (eadd (emul (ec (-2)) butterflyCube)
    (emul (ec 9) butterflySquare)) (emul (ec (-4)) (ev BUTTERFLY))

def routingBodies : List EmittedExpr :=
  [ emul stage0Selector (esub (ev LEFT_INDEX) (emul (ec 2) (ev BUTTERFLY)))
  , emul stage1Selector
      (esub (emul (ec 3) (ev LEFT_INDEX)) stage1LeftTimes3)
  , emul stage2Selector (esub (ev LEFT_INDEX) (ev BUTTERFLY))
  , emul stage0Selector (esub (esub (ev RIGHT_INDEX) (ev LEFT_INDEX)) (ec 1))
  , emul stage1Selector (esub (esub (ev RIGHT_INDEX) (ev LEFT_INDEX)) (ec 2))
  , emul stage2Selector (esub (esub (ev RIGHT_INDEX) (ev LEFT_INDEX)) (ec 4)) ]

def selectorBodies : List EmittedExpr :=
  [ boolBody FIRST_STAGE, boolBody LAST_STAGE
  , esub (emul (ec 2) (ev FIRST_STAGE)) stage0Selector
  , esub (emul (ec 2) (ev LAST_STAGE)) stage2Selector ]

def rowBodies : List EmittedExpr :=
  [ ev DIRECTION, ev MODULUS_ROW, ev TRANSFORM,
    stagePoly, butterflyPoly, boolBody ADD_REDUCE, boolBody SUB_REDUCE ] ++
  routingBodies ++ selectorBodies ++
  (List.range 5).map productBody ++
  (List.range 3).map addBody ++
  (List.range 3).map subBody ++
  [carryValue PRODUCT_CARRY 4, carryValue ADD_CARRY 2, carryValue SUB_CARRY 2]

/-- A base `.gate` fires on transition rows; duplicating it at `.last` makes
the exact same body cover the wrap row too. -/
def allRowGate (body : EmittedExpr) : List VmConstraint2 :=
  [.base (.gate body), .base (.boundary .last body)]

def arithmeticConstraints : List VmConstraint2 := rowBodies.flatMap allRowGate

/-! ## 3. Canonical schedule and stage-bus lookups -/

def SCHEDULE_TID : Nat := 512
def BUS_TID : Nat := 513

def halfAt (stage : Nat) : Nat := 2 ^ stage
def lenAt (stage : Nat) : Nat := 2 * halfAt stage
def leftIndex (stage butterfly : Nat) : Nat :=
  (butterfly / halfAt stage) * lenAt stage + butterfly % halfAt stage
def rightIndex (stage butterfly : Nat) : Nat := leftIndex stage butterfly + halfAt stage
def twiddleIndex (stage butterfly : Nat) : Nat :=
  (butterfly % halfAt stage) * (N / lenAt stage)

def twiddleValue (stage butterfly : Nat) : Nat :=
  ((PSI : ZMod Q) ^ (2 * twiddleIndex stage butterfly)).val

def readLeftTag (stage butterfly : Nat) : Nat := stage * N + leftIndex stage butterfly
def readRightTag (stage butterfly : Nat) : Nat := stage * N + rightIndex stage butterfly
def writeLeftTag (stage butterfly : Nat) : Nat :=
  (stage + 1) * N + leftIndex stage butterfly
def writeRightTag (stage butterfly : Nat) : Nat :=
  (stage + 1) * N + rightIndex stage butterfly

def scheduleRow (stage butterfly : Nat) : List Int :=
  [0, Int.ofNat stage, Int.ofNat butterfly, 0, 0,
    Int.ofNat (leftIndex stage butterfly), Int.ofNat (rightIndex stage butterfly),
    Int.ofNat (twiddleIndex stage butterfly)] ++
  (List.range 3).map (limbInt (twiddleValue stage butterfly)) ++
  [ Int.ofNat (readLeftTag stage butterfly), Int.ofNat (readRightTag stage butterfly),
    Int.ofNat (writeLeftTag stage butterfly), Int.ofNat (writeRightTag stage butterfly),
    if stage = 0 then 1 else 0, if stage = LOG_N - 1 then 1 else 0 ]

def scheduleTable : Table :=
  (List.range LOG_N).flatMap fun stage =>
    (List.range (N / 2)).map (scheduleRow stage)

def scheduleTuple : List EmittedExpr :=
  [ev DIRECTION, ev STAGE, ev BUTTERFLY, ev MODULUS_ROW, ev TRANSFORM,
    ev LEFT_INDEX, ev RIGHT_INDEX, ev TWIDDLE_INDEX] ++
  (List.range 3).map (residueLimb TWIDDLE) ++
  [ev READ_LEFT_TAG, ev READ_RIGHT_TAG, ev WRITE_LEFT_TAG, ev WRITE_RIGHT_TAG,
    ev FIRST_STAGE, ev LAST_STAGE]

def scheduleLookup : VmConstraint2 := .lookup ⟨.custom SCHEDULE_TID, scheduleTuple⟩

def busTuple (tag residue : Nat) : List EmittedExpr :=
  [ev tag] ++ (List.range 3).map (residueLimb residue)

def busLookups : List VmConstraint2 :=
  [ .lookup ⟨.custom BUS_TID, busTuple READ_LEFT_TAG LEFT_INPUT⟩
  , .lookup ⟨.custom BUS_TID, busTuple READ_RIGHT_TAG RIGHT_INPUT⟩
  , .lookup ⟨.custom BUS_TID, busTuple WRITE_LEFT_TAG LEFT_OUTPUT⟩
  , .lookup ⟨.custom BUS_TID, busTuple WRITE_RIGHT_TAG RIGHT_OUTPUT⟩ ]

def wneg (value : WindowExpr) : WindowExpr := .mul (.const (-1)) value
def wsub (left right : WindowExpr) : WindowExpr := .add left (wneg right)

/-- With `b ∈ {0,1,2,3}`, `e=b(b-1)(b-2)` is zero except at `b=3`, where
it is six.  These two transition equations implement the exact 4-row stage
odometer without an additional selector column. -/
def butterflyEnd6 : WindowExpr :=
  .mul (.loc BUTTERFLY)
    (.mul (wsub (.loc BUTTERFLY) (.const 1))
      (wsub (.loc BUTTERFLY) (.const 2)))

def stageTransition : VmConstraint2 :=
  .windowGate ⟨wsub (.mul (.const 6) (.nxt STAGE))
    (.add (.mul (.const 6) (.loc STAGE)) butterflyEnd6), true⟩

def butterflyTransition : VmConstraint2 :=
  .windowGate ⟨wsub (.mul (.const 6) (.nxt BUTTERFLY))
    (wsub (.mul (.const 6) (.add (.loc BUTTERFLY) (.const 1)))
      (.mul (.const 4) butterflyEnd6)), true⟩

def boundaryPins : List VmConstraint2 :=
  [ .base (.boundary .first (ev STAGE))
  , .base (.boundary .first (ev BUTTERFLY))
  , .base (.boundary .last (esub (ev STAGE) (ec (Int.ofNat (LOG_N - 1)))))
  , .base (.boundary .last (esub (ev BUTTERFLY) (ec (Int.ofNat (N / 2 - 1))))) ]

def limbRanges : List VmRange :=
  ([LEFT_INPUT, RIGHT_INPUT, TWIDDLE, TWIDDLED_RIGHT, LEFT_OUTPUT, RIGHT_OUTPUT,
      PRODUCT_QUOTIENT].flatMap fun base =>
    [⟨base, 14⟩, ⟨base + 1, 14⟩, ⟨base + 2, 8⟩])

def scheduleRanges : List VmRange :=
  [ ⟨DIRECTION, 1⟩, ⟨STAGE, 2⟩, ⟨BUTTERFLY, 2⟩, ⟨MODULUS_ROW, 2⟩,
    ⟨TRANSFORM, 2⟩, ⟨LEFT_INDEX, 3⟩, ⟨RIGHT_INDEX, 3⟩,
    ⟨TWIDDLE_INDEX, 3⟩, ⟨ADD_REDUCE, 1⟩, ⟨SUB_REDUCE, 1⟩,
    ⟨READ_LEFT_TAG, 5⟩, ⟨READ_RIGHT_TAG, 5⟩,
    ⟨WRITE_LEFT_TAG, 5⟩, ⟨WRITE_RIGHT_TAG, 5⟩,
    ⟨FIRST_STAGE, 1⟩, ⟨LAST_STAGE, 1⟩ ]

def carryRanges : List VmRange :=
  (List.range 5).map (fun limb => ⟨PRODUCT_CARRY + limb, 16⟩) ++
  (List.range 3).map (fun limb => ⟨ADD_CARRY + limb, 16⟩) ++
  (List.range 3).map (fun limb => ⟨SUB_CARRY + limb, 16⟩)

def butterflyDescriptor : EffectVmDescriptor2 :=
  { name := "private-book-bfv-odd-ntt-butterfly-q0-n8::exact-48-v1"
  , traceWidth := TRACE_WIDTH
  , piCount := 0
  , tables :=
      [ ⟨.custom SCHEDULE_TID, "bfv_ntt_q0_n8_schedule", 17, .mainRow⟩
      , ⟨.custom BUS_TID, "bfv_ntt_q0_n8_stage_bus", 4, .mainRow⟩ ]
  , constraints := arithmeticConstraints ++ [scheduleLookup] ++ busLookups ++
      [stageTransition, butterflyTransition] ++ boundaryPins
  , hashSites := []
  , ranges := limbRanges ++ scheduleRanges ++ carryRanges }

#guard TRACE_WIDTH == 48
#guard rowBodies.length == 31
#guard arithmeticConstraints.length == 62
#guard scheduleTuple.length == 17
#guard scheduleTable.length == 12
#guard butterflyDescriptor.traceWidth == 48
#guard butterflyDescriptor.constraints.length == 73
#guard butterflyDescriptor.ranges.length == 48
#guard (emitVmJson2 butterflyDescriptor).contains "window_gate"
#guard (emitVmJson2 butterflyDescriptor).contains "bfv_ntt_q0_n8_stage_bus"

/-! ### Production-degree public-carrier descriptor

The executable q0/N=8 tooth above contains small-domain polynomial odometers
and routing equations.  Those equations are intentionally not reused at
N=4096.  The production-degree descriptor keeps the exact limb arithmetic and
the schedule/bus lookup tuple, while the native strict carrier fixes the
24,576-row schedule multiset, row order, every boundary multiset, and the real
transform ingress/egress.

This descriptor is therefore an exact *identity for that public carrier*, not
a claim that generic IR2 currently gives prover-supplied custom tables a
committed LogUp meaning.  Until that seam lands, it must not be used as a
standalone hiding-proof authority.
-/

def productionRowBodies : List EmittedExpr :=
  [ ev DIRECTION, ev MODULUS_ROW, ev TRANSFORM,
    boolBody ADD_REDUCE, boolBody SUB_REDUCE ] ++
  (List.range 5).map productBody ++
  (List.range 3).map addBody ++
  (List.range 3).map subBody ++
  [carryValue PRODUCT_CARRY 4, carryValue ADD_CARRY 2, carryValue SUB_CARRY 2]

def productionArithmeticConstraints : List VmConstraint2 :=
  productionRowBodies.flatMap allRowGate

/-- Exact bit widths of the production q0/N=4096 schedule carrier.  Boundary
tags range through `13*N-1 = 53247`, hence the 16-bit tag lanes. -/
def productionScheduleRanges : List VmRange :=
  [ ⟨DIRECTION, 1⟩, ⟨STAGE, 4⟩, ⟨BUTTERFLY, 11⟩, ⟨MODULUS_ROW, 2⟩,
    ⟨TRANSFORM, 2⟩, ⟨LEFT_INDEX, 12⟩, ⟨RIGHT_INDEX, 12⟩,
    ⟨TWIDDLE_INDEX, 12⟩, ⟨ADD_REDUCE, 1⟩, ⟨SUB_REDUCE, 1⟩,
    ⟨READ_LEFT_TAG, 16⟩, ⟨READ_RIGHT_TAG, 16⟩,
    ⟨WRITE_LEFT_TAG, 16⟩, ⟨WRITE_RIGHT_TAG, 16⟩,
    ⟨FIRST_STAGE, 1⟩, ⟨LAST_STAGE, 1⟩ ]

def productionQ0N4096Descriptor : EffectVmDescriptor2 :=
  { name := "private-book-bfv-odd-ntt-butterfly-q0-n4096::public-carrier-48-v1"
  , traceWidth := TRACE_WIDTH
  , piCount := 0
  , tables :=
      [ ⟨.custom SCHEDULE_TID, "bfv_ntt_q0_n4096_schedule", 17, .mainRow⟩
      , ⟨.custom BUS_TID, "bfv_ntt_q0_n4096_stage_bus", 4, .mainRow⟩ ]
  , constraints := productionArithmeticConstraints ++ [scheduleLookup] ++ busLookups
  , hashSites := []
  , ranges := limbRanges ++ productionScheduleRanges ++ carryRanges }

#guard productionRowBodies.length == 19
#guard productionArithmeticConstraints.length == 38
#guard productionQ0N4096Descriptor.constraints.length == 43
#guard productionQ0N4096Descriptor.ranges.length == 48
#guard 13 * 4096 < 2 ^ 16
#guard (emitVmJson2 productionQ0N4096Descriptor).contains "bfv_ntt_q0_n4096_schedule"

/-! ## 4. Executable witness and exact permutation check -/

def bitReverse3 : Nat → Nat
  | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 6
  | 4 => 1 | 5 => 5 | 6 => 3 | 7 => 7
  | _ => 0

def inputValue (index : Nat) : Nat :=
  (3 * index * index + 5 * index + 7) % Q

/-- Rust's forward path twists first, then applies the in-place bit-reversal
permutation before the first butterfly stage. -/
def initialState (index : Nat) : Nat :=
  let source := bitReverse3 index
  (((inputValue source : ZMod Q) * (PSI : ZMod Q) ^ source)).val

def stateStep (stage : Nat) (state : Nat → Nat) (index : Nat) : Nat :=
  let half := halfAt stage
  let len := lenAt stage
  let localPos := index % len
  let left := if localPos < half then index else index - half
  let right := left + half
  let twiddle := ((PSI : ZMod Q) ^ (2 * ((localPos % half) * (N / len)))).val
  let product := (state right * twiddle) % Q
  if localPos < half then (state left + product) % Q
  else (state left + Q - product) % Q

def stateAt : Nat → Nat → Nat
  | 0 => initialState
  | stage + 1 => stateStep stage (stateAt stage)

def conv3Int (left right : Nat) : Nat → Int
  | 0 => limbInt left 0 * limbInt right 0
  | 1 => limbInt left 0 * limbInt right 1 + limbInt left 1 * limbInt right 0
  | 2 => limbInt left 0 * limbInt right 2 + limbInt left 1 * limbInt right 1 +
      limbInt left 2 * limbInt right 0
  | 3 => limbInt left 1 * limbInt right 2 + limbInt left 2 * limbInt right 1
  | 4 => limbInt left 2 * limbInt right 2
  | _ => 0

def quotientQInt (quotient : Nat) : Nat → Int
  | 0 => limbInt quotient 0 * qLimb 0
  | 1 => limbInt quotient 0 * qLimb 1 + limbInt quotient 1 * qLimb 0
  | 2 => limbInt quotient 0 * qLimb 2 + limbInt quotient 1 * qLimb 1 +
      limbInt quotient 2 * qLimb 0
  | 3 => limbInt quotient 1 * qLimb 2 + limbInt quotient 2 * qLimb 1
  | 4 => limbInt quotient 2 * qLimb 2
  | _ => 0

def productCarries (right twiddle product quotient : Nat) : List Int :=
  let c0 := (conv3Int right twiddle 0 - limbInt product 0 - quotientQInt quotient 0) /
    Int.ofNat RADIX
  let c1 := (conv3Int right twiddle 1 + c0 - limbInt product 1 -
    quotientQInt quotient 1) / Int.ofNat RADIX
  let c2 := (conv3Int right twiddle 2 + c1 - limbInt product 2 -
    quotientQInt quotient 2) / Int.ofNat RADIX
  let c3 := (conv3Int right twiddle 3 + c2 - quotientQInt quotient 3) /
    Int.ofNat RADIX
  let c4 := (conv3Int right twiddle 4 + c3 - quotientQInt quotient 4) /
    Int.ofNat RADIX
  [c0, c1, c2, c3, c4]

def addCarries (left product output reduce : Nat) : List Int :=
  let c0 := (limbInt left 0 + limbInt product 0 - limbInt output 0 -
    Int.ofNat reduce * qLimb 0) / Int.ofNat RADIX
  let c1 := (limbInt left 1 + limbInt product 1 + c0 - limbInt output 1 -
    Int.ofNat reduce * qLimb 1) / Int.ofNat RADIX
  let c2 := (limbInt left 2 + limbInt product 2 + c1 - limbInt output 2 -
    Int.ofNat reduce * qLimb 2) / Int.ofNat RADIX
  [c0, c1, c2]

def subCarries (left product output reduce : Nat) : List Int :=
  let c0 := (limbInt left 0 - limbInt product 0 + Int.ofNat reduce * qLimb 0 -
    limbInt output 0) / Int.ofNat RADIX
  let c1 := (limbInt left 1 - limbInt product 1 + Int.ofNat reduce * qLimb 1 + c0 -
    limbInt output 1) / Int.ofNat RADIX
  let c2 := (limbInt left 2 - limbInt product 2 + Int.ofNat reduce * qLimb 2 + c1 -
    limbInt output 2) / Int.ofNat RADIX
  [c0, c1, c2]

def honestRow (stage butterfly : Nat) : Assignment := fun column =>
  let leftIndex := leftIndex stage butterfly
  let rightIndex := rightIndex stage butterfly
  let left := stateAt stage leftIndex
  let right := stateAt stage rightIndex
  let twiddle := twiddleValue stage butterfly
  let product := (right * twiddle) % Q
  let quotient := (right * twiddle - product) / Q
  let leftOutput := (left + product) % Q
  let rightOutput := (left + Q - product) % Q
  let addReduce := if Q ≤ left + product then 1 else 0
  let subReduce := if left < product then 1 else 0
  if column = DIRECTION then 0
  else if column = STAGE then Int.ofNat stage
  else if column = BUTTERFLY then Int.ofNat butterfly
  else if column = MODULUS_ROW then 0
  else if column = TRANSFORM then 0
  else if column = LEFT_INDEX then Int.ofNat leftIndex
  else if column = RIGHT_INDEX then Int.ofNat rightIndex
  else if column = TWIDDLE_INDEX then Int.ofNat (twiddleIndex stage butterfly)
  else if LEFT_INPUT ≤ column && column < LEFT_INPUT + 3 then
    limbInt left (column - LEFT_INPUT)
  else if RIGHT_INPUT ≤ column && column < RIGHT_INPUT + 3 then
    limbInt right (column - RIGHT_INPUT)
  else if TWIDDLE ≤ column && column < TWIDDLE + 3 then
    limbInt twiddle (column - TWIDDLE)
  else if TWIDDLED_RIGHT ≤ column && column < TWIDDLED_RIGHT + 3 then
    limbInt product (column - TWIDDLED_RIGHT)
  else if LEFT_OUTPUT ≤ column && column < LEFT_OUTPUT + 3 then
    limbInt leftOutput (column - LEFT_OUTPUT)
  else if RIGHT_OUTPUT ≤ column && column < RIGHT_OUTPUT + 3 then
    limbInt rightOutput (column - RIGHT_OUTPUT)
  else if PRODUCT_QUOTIENT ≤ column && column < PRODUCT_QUOTIENT + 3 then
    limbInt quotient (column - PRODUCT_QUOTIENT)
  else if column = ADD_REDUCE then Int.ofNat addReduce
  else if column = SUB_REDUCE then Int.ofNat subReduce
  else if PRODUCT_CARRY ≤ column && column < PRODUCT_CARRY + 5 then
    (productCarries right twiddle product quotient).getD (column - PRODUCT_CARRY) 0 + CARRY_SHIFT
  else if ADD_CARRY ≤ column && column < ADD_CARRY + 3 then
    (addCarries left product leftOutput addReduce).getD (column - ADD_CARRY) 0 + CARRY_SHIFT
  else if SUB_CARRY ≤ column && column < SUB_CARRY + 3 then
    (subCarries left product rightOutput subReduce).getD (column - SUB_CARRY) 0 + CARRY_SHIFT
  else if column = READ_LEFT_TAG then Int.ofNat (readLeftTag stage butterfly)
  else if column = READ_RIGHT_TAG then Int.ofNat (readRightTag stage butterfly)
  else if column = WRITE_LEFT_TAG then Int.ofNat (writeLeftTag stage butterfly)
  else if column = WRITE_RIGHT_TAG then Int.ofNat (writeRightTag stage butterfly)
  else if column = FIRST_STAGE then if stage = 0 then 1 else 0
  else if column = LAST_STAGE then if stage = LOG_N - 1 then 1 else 0
  else 0

def honestRows : List Assignment :=
  (List.range LOG_N).flatMap fun stage =>
    (List.range (N / 2)).map (honestRow stage)

def busRow (boundary index : Nat) : List Int :=
  [Int.ofNat (boundary * N + index)] ++
    (List.range 3).map (limbInt (stateAt boundary index))

def busTable : Table :=
  (List.range (LOG_N + 1)).flatMap fun boundary =>
    (List.range N).map (busRow boundary)

def butterflyTrace (rows : List Assignment) : VmTrace :=
  { rows := rows
  , pub := zeroAsg
  , tf := fun table =>
      match table with
      | .custom tid =>
          if tid = SCHEDULE_TID then scheduleTable
          else if tid = BUS_TID then busTable
          else []
      | _ => [] }

def busItem (tag residue : Nat) (row : Assignment) : List Int :=
  [row tag] ++ (List.range 3).map (fun limb => row (residue + limb))

def stageWrites (rows : List Assignment) (stage : Nat) : List (List Int) :=
  (rows.filter fun row => row STAGE = Int.ofNat stage).flatMap fun row =>
    [busItem WRITE_LEFT_TAG LEFT_OUTPUT row, busItem WRITE_RIGHT_TAG RIGHT_OUTPUT row]

def stageReads (rows : List Assignment) (stage : Nat) : List (List Int) :=
  (rows.filter fun row => row STAGE = Int.ofNat stage).flatMap fun row =>
    [busItem READ_LEFT_TAG LEFT_INPUT row, busItem READ_RIGHT_TAG RIGHT_INPUT row]

/-- Exact multiset equality, not membership-only: every output cell of stages
0 and 1 occurs exactly once as an input cell of the following stage. -/
def permutationBusGate (rows : List Assignment) : Bool :=
  (List.range (LOG_N - 1)).all fun stage =>
    decide ((stageWrites rows stage).Perm (stageReads rows (stage + 1)))

def butterflyAirGate (rows : List Assignment) : Bool :=
  decideSatisfied2 trivialMapDec (fun _ => 0) butterflyDescriptor
    (fun _ => 0) (fun _ => (0, 0)) [] (butterflyTrace rows)

/-- The executable slice accepts only when the Lean-authored IR2 denotation and
the exact cross-stage permutation agree. -/
def butterflySliceGate (rows : List Assignment) : Bool :=
  butterflyAirGate rows && permutationBusGate rows

/-- Exact-integer evaluation of the same bodies emitted into IR2.  This is a
witness-generation tooth, not a second hand-authored arithmetic relation. -/
def integerRowGate (row : Assignment) : Bool :=
  rowBodies.all fun body => decide (body.eval row = 0)

def integerWitnessGate (rows : List Assignment) : Bool := rows.all integerRowGate

def mutateColumn (row : Assignment) (column : Nat) (delta : Int) : Assignment := fun c =>
  if c = column then row c + delta else row c

def arithmeticMutation : List Assignment :=
  honestRows.mapIdx fun index row =>
    if index = 5 then mutateColumn row TWIDDLED_RIGHT 1 else row

def scheduleMutation : List Assignment :=
  honestRows.mapIdx fun index row =>
    if index = 4 then mutateColumn row LEFT_INDEX 1 else row

def busMutation : List Assignment :=
  honestRows.mapIdx fun index row =>
    if index = 4 then mutateColumn row LEFT_INPUT 1 else row

def omittedRow : List Assignment := honestRows.eraseIdx 7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem honest_slice_accepts : butterflySliceGate honestRows = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem honest_integer_witness_exact : integerWitnessGate honestRows = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem arithmetic_mutation_refused : butterflySliceGate arithmeticMutation = false := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem arithmetic_mutation_breaks_integer_equation :
    integerWitnessGate arithmeticMutation = false := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem schedule_mutation_refused : butterflySliceGate scheduleMutation = false := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem permutation_mutation_refused : permutationBusGate busMutation = false := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem omitted_row_refused : butterflySliceGate omittedRow = false := by
  decide

/-- Acceptance cannot drop the permutation conjunct: the public executable
gate literally returns both the AIR verdict and exact multiset equality. -/
theorem accepted_implies_permutation {rows : List Assignment}
    (h : butterflySliceGate rows = true) : permutationBusGate rows = true := by
  simp only [butterflySliceGate, Bool.and_eq_true] at h
  exact h.2

theorem accepted_implies_air {rows : List Assignment}
    (h : butterflySliceGate rows = true) : butterflyAirGate rows = true := by
  simp only [butterflySliceGate, Bool.and_eq_true] at h
  exact h.1

/-! ## 5. Fixed q0 threshold-share terminal relation

The transform table above is still a public/verifier-visible carrier.  The
next fixed descriptor is deliberately narrower: it proves the terminal
coefficient identity used by a q0 threshold-decryption share while hiding the
product, smudge, complement, quotient, and carries.  Eight public context
lanes bind the proof to the exact transform carrier selected by the host
verifier; they do not by themselves prove that carrier's still-open committed
LogUp relation.

All large values use the same radix `2^14` as the butterfly rows.  The signed
values are offset exactly as the protocol does:

* `smudgeShift = smudge + 2^80`;
* `quotientShift = quotient + 2^63`.

Consequently the limb equation contains the fixed positive offset
`q0 * 2^63 - 2^80`.  A separate complement chain proves
`smudgeShift + smudgeComplement = 2^81`, which is precisely the inclusive
signed interval `[-2^80, 2^80]`.
-/

def TERM_LAMBDA : Nat := 0
def TERM_PRODUCT : Nat := 3
def TERM_H : Nat := 6
def TERM_SMUDGE_SHIFT : Nat := 9
def TERM_SMUDGE_COMPLEMENT : Nat := 15
def TERM_QUOTIENT_SHIFT : Nat := 21
def TERM_EQ_CARRY_SHIFT : Nat := 26
def TERM_COMPLEMENT_CARRY : Nat := 34
def TERM_CONTEXT : Nat := 40
def TERM_PRODUCT_SLACK : Nat := 48
def TERM_PRODUCT_CAN_CARRY : Nat := 51
def TERM_TRACE_WIDTH : Nat := 53

def TERM_CARRY_SHIFT : Int := 32768
def TERM_Q_LIMBS : List Int := [8193, 16379, 255]
def TERM_Q_MINUS_ONE_LIMBS : List Int := [8192, 16379, 255]
def TERM_OFFSET_LIMBS : List Int := [0, 0, 0, 0, 128, 14784, 16383, 1]
def TERM_DOUBLE_BOUND_LIMBS : List Int := [0, 0, 0, 0, 0, 2048]

def termLimb (base limb : Nat) : EmittedExpr := ev (base + limb)

def termConv3 (left right degree : Nat) : EmittedExpr :=
  match degree with
  | 0 => emul (termLimb left 0) (termLimb right 0)
  | 1 => eadd
      (emul (termLimb left 0) (termLimb right 1))
      (emul (termLimb left 1) (termLimb right 0))
  | 2 => eadd
      (eadd
        (emul (termLimb left 0) (termLimb right 2))
        (emul (termLimb left 1) (termLimb right 1)))
      (emul (termLimb left 2) (termLimb right 0))
  | 3 => eadd
      (emul (termLimb left 1) (termLimb right 2))
      (emul (termLimb left 2) (termLimb right 1))
  | 4 => emul (termLimb left 2) (termLimb right 2)
  | _ => ec 0

def termQuotientTimesQ (degree : Nat) : EmittedExpr :=
  let pieces := (List.range 3).filterMap fun qlimb =>
    if qlimb ≤ degree ∧ degree - qlimb < 5 then
      some (emul (ec (TERM_Q_LIMBS.getD qlimb 0))
        (termLimb TERM_QUOTIENT_SHIFT (degree - qlimb)))
    else none
  pieces.foldl eadd (ec 0)

def termSignedEqCarry (degree : Nat) : EmittedExpr :=
  esub (ev (TERM_EQ_CARRY_SHIFT + degree)) (ec TERM_CARRY_SHIFT)

def termEquationBody (degree : Nat) : EmittedExpr :=
  let carryIn := if degree = 0 then ec 0 else termSignedEqCarry (degree - 1)
  let carryOut := termSignedEqCarry degree
  let smudge := if degree < 6 then termLimb TERM_SMUDGE_SHIFT degree else ec 0
  let h := if degree < 3 then termLimb TERM_H degree else ec 0
  esub
    (eadd
      (esub
        (eadd
          (eadd (termConv3 TERM_LAMBDA TERM_PRODUCT degree) smudge)
          (ec (TERM_OFFSET_LIMBS.getD degree 0)))
        (eadd h (termQuotientTimesQ degree)))
      carryIn)
    (emul (ec (Int.ofNat RADIX)) carryOut)

def termComplementBody (degree : Nat) : EmittedExpr :=
  let carryIn := if degree = 0 then ec 0 else ev (TERM_COMPLEMENT_CARRY + degree - 1)
  let carryOut := ev (TERM_COMPLEMENT_CARRY + degree)
  esub
    (eadd
      (esub
        (eadd (termLimb TERM_SMUDGE_SHIFT degree)
          (termLimb TERM_SMUDGE_COMPLEMENT degree))
        (ec (TERM_DOUBLE_BOUND_LIMBS.getD degree 0)))
      carryIn)
    (emul (ec (Int.ofNat RADIX)) carryOut)

def termProductCanonicalBodies : List EmittedExpr :=
  [ esub
      (esub
        (eadd (termLimb TERM_PRODUCT 0) (termLimb TERM_PRODUCT_SLACK 0))
        (ec (TERM_Q_MINUS_ONE_LIMBS.getD 0 0)))
      (emul (ec (Int.ofNat RADIX)) (ev TERM_PRODUCT_CAN_CARRY))
  , esub
      (esub
        (eadd
          (eadd (termLimb TERM_PRODUCT 1) (termLimb TERM_PRODUCT_SLACK 1))
          (ev TERM_PRODUCT_CAN_CARRY))
        (ec (TERM_Q_MINUS_ONE_LIMBS.getD 1 0)))
      (emul (ec (Int.ofNat RADIX)) (ev (TERM_PRODUCT_CAN_CARRY + 1)))
  , esub
      (eadd
        (eadd (termLimb TERM_PRODUCT 2) (termLimb TERM_PRODUCT_SLACK 2))
        (ev (TERM_PRODUCT_CAN_CARRY + 1)))
      (ec (TERM_Q_MINUS_ONE_LIMBS.getD 2 0))
  , boolBody TERM_PRODUCT_CAN_CARRY
  , boolBody (TERM_PRODUCT_CAN_CARRY + 1) ]

def termBodies : List EmittedExpr :=
  (List.range 8).map termEquationBody ++
  (List.range 6).map termComplementBody ++
  (List.range 6).map (fun degree => boolBody (TERM_COMPLEMENT_CARRY + degree)) ++
  termProductCanonicalBodies ++
  [termSignedEqCarry 7]

def TERM_RANGE_TID_BASE : Nat := 768
def termRangeTid (bits : Nat) : TableId := .custom (TERM_RANGE_TID_BASE + bits)
def termRangeLookup (bits col : Nat) : VmConstraint2 :=
  .lookup ⟨termRangeTid bits, [ev col]⟩

def termRangeTables : List TableDef :=
  [8, 12, 14, 16].map fun bits =>
    ⟨termRangeTid bits, "bfv_terminal_range_" ++ toString bits, 1, .rangeLimb bits⟩

def termLimbRanges : List VmConstraint2 :=
  ([TERM_LAMBDA, TERM_PRODUCT, TERM_H, TERM_PRODUCT_SLACK].flatMap fun base =>
    [termRangeLookup 14 base, termRangeLookup 14 (base + 1), termRangeLookup 8 (base + 2)]) ++
  ([TERM_SMUDGE_SHIFT, TERM_SMUDGE_COMPLEMENT].flatMap fun base =>
    (List.range 5).map (fun limb => termRangeLookup 14 (base + limb)) ++
      [termRangeLookup 12 (base + 5)]) ++
  ((List.range 4).map fun limb => termRangeLookup 14 (TERM_QUOTIENT_SHIFT + limb)) ++
  [termRangeLookup 8 (TERM_QUOTIENT_SHIFT + 4)] ++
  ((List.range 8).map fun degree => termRangeLookup 16 (TERM_EQ_CARRY_SHIFT + degree))

def termPublicPins : List VmConstraint2 :=
  ((List.range 3).map fun limb =>
    .base (.piBinding .first (TERM_LAMBDA + limb) limb)) ++
  ((List.range 3).map fun limb =>
    .base (.piBinding .first (TERM_H + limb) (3 + limb))) ++
  ((List.range 8).map fun lane =>
    .base (.piBinding .first (TERM_CONTEXT + lane) (6 + lane)))

/-- Lean-authored fixed-schema hiding relation for one production q0 terminal
share coefficient.  There is no caller-selected modulus, range, trace height,
or FRI knob in this descriptor. -/
def thresholdTerminalQ0Descriptor : EffectVmDescriptor2 :=
  { name := "private-book-bfv-threshold-terminal-q0-b80::exact-limb-v1"
  , traceWidth := TERM_TRACE_WIDTH
  , piCount := 14
  , tables := termRangeTables
  , constraints := termBodies.flatMap allRowGate ++ termLimbRanges ++ termPublicPins
  , hashSites := []
  , ranges := [] }

#guard TERM_TRACE_WIDTH == 53
#guard termBodies.length == 26
#guard termLimbRanges.length == 37
#guard thresholdTerminalQ0Descriptor.piCount == 14
#guard thresholdTerminalQ0Descriptor.traceWidth == 53
#guard (emitVmJson2 thresholdTerminalQ0Descriptor).contains "bfv_terminal_range_16"

/-- The largest unsigned convolution plus shifted-carry term stays below the
BabyBear modulus.  This is the numeric headroom needed before the standard
range-table/FRI soundness floor lifts a zero field residue to the intended
integer limb equation. -/
theorem terminal_equation_headroom :
    3 * (RADIX - 1) ^ 2 + 2 * (RADIX - 1) + 32768 +
      (8193 + 16379 + 255) * (RADIX - 1) + RADIX * 32768 < 2013265921 := by
  norm_num [RADIX]

#assert_all_clean [
  Market.PrivateBookBfvButterflyAir.trace_width_matches_family,
  Market.PrivateBookBfvButterflyAir.product_limb_equation_headroom,
  Market.PrivateBookBfvButterflyAir.honest_slice_accepts,
  Market.PrivateBookBfvButterflyAir.honest_integer_witness_exact,
  Market.PrivateBookBfvButterflyAir.arithmetic_mutation_refused,
  Market.PrivateBookBfvButterflyAir.arithmetic_mutation_breaks_integer_equation,
  Market.PrivateBookBfvButterflyAir.schedule_mutation_refused,
  Market.PrivateBookBfvButterflyAir.permutation_mutation_refused,
  Market.PrivateBookBfvButterflyAir.omitted_row_refused,
  Market.PrivateBookBfvButterflyAir.accepted_implies_permutation,
  Market.PrivateBookBfvButterflyAir.accepted_implies_air,
  Market.PrivateBookBfvButterflyAir.terminal_equation_headroom]

end Market.PrivateBookBfvButterflyAir
