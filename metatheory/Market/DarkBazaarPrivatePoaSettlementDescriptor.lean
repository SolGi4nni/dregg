/-
# PoA Dark Bazaar private settlement descriptor — transition-bound v3

V2 bound the fixed hidden N=4/K=4 book proof to one receipt digest.  That was
an identity join, not a settlement statement.  V3 keeps every v1 market tooth
and adds a public settlement surface authored from the actual Lean judge:

* all eight lanes of the judge's input, successor, public-view and receipt
  digests are independently public;
* the exact public before/after escrow and custody scalars are public;
* debit, credit, quote calculation and both per-asset conservation equations
  are constraints, not prose;
* every settlement scalar is range-constrained below 2^28 and the quote tick
  below 2^20.  This is an explicit v3 family limit, chosen so every integer
  consequence lies strictly inside BabyBear and cannot be satisfied by field
  wraparound.

The private order book remains absent from the public vector and is hidden
from the verifier by the Rust HidingFRI configuration.  The trace producer
still receives the opening.  `ProverVisibilityGrade.verifierShieldedProducerVisible`
is therefore a typed public grade fixed by the AIR; this file makes no
house-blind or no-single-viewer claim.
-/
import Market.DarkBazaarPrivateDescriptor

namespace Market.DarkBazaarPrivatePoaSettlementDescriptor

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 Satisfied2 TraceFamily VmConstraint2 emitVmJson2)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Market.DarkBazaarPrivateDescriptor

set_option autoImplicit false

def VERSION : Nat := 3

/-- Privacy is a statement field, not an adjective attached by a caller. -/
inductive ProverVisibilityGrade where
  | verifierShieldedProducerVisible
  | noSingleViewer
deriving DecidableEq, Repr

def ProverVisibilityGrade.code : ProverVisibilityGrade → Nat
  | .verifierShieldedProducerVisible => 1
  | .noSingleViewer => 2

def PROVEN_VISIBILITY : ProverVisibilityGrade :=
  .verifierShieldedProducerVisible

def STATE_VALUE_BITS : Nat := 28
def QUOTE_TICK_BITS : Nat := 20
def STATE_VALUE_LIMIT : Nat := 2 ^ STATE_VALUE_BITS
def QUOTE_TICK_LIMIT : Nat := 2 ^ QUOTE_TICK_BITS

/-- Public arithmetic projection extracted from the independently run Lean
judge output.  `before*` is the exact public input state; `after*` is the exact
public successor. -/
structure SettlementTransition where
  beforeBaseEscrow : Nat
  afterBaseEscrow : Nat
  beforeBuyerBaseCustody : Nat
  afterBuyerBaseCustody : Nat
  beforeQuoteEscrow : Nat
  afterQuoteEscrow : Nat
  beforeSellerQuoteCustody : Nat
  afterSellerQuoteCustody : Nat
  quoteTick : Nat
  quoteAmount : Nat
deriving DecidableEq, Repr

def SettlementTransition.InRange (transition : SettlementTransition) : Prop :=
  transition.beforeBaseEscrow < STATE_VALUE_LIMIT ∧
  transition.afterBaseEscrow < STATE_VALUE_LIMIT ∧
  transition.beforeBuyerBaseCustody < STATE_VALUE_LIMIT ∧
  transition.afterBuyerBaseCustody < STATE_VALUE_LIMIT ∧
  transition.beforeQuoteEscrow < STATE_VALUE_LIMIT ∧
  transition.afterQuoteEscrow < STATE_VALUE_LIMIT ∧
  transition.beforeSellerQuoteCustody < STATE_VALUE_LIMIT ∧
  transition.afterSellerQuoteCustody < STATE_VALUE_LIMIT ∧
  transition.quoteTick < QUOTE_TICK_LIMIT ∧
  transition.quoteAmount < STATE_VALUE_LIMIT

/-- The exact public transition relation enforced by the five v3 arithmetic
gates.  `pStar` and `vStar` are the already-proved v1 clearing output. -/
def SettlementTransition.Valid (transition : SettlementTransition)
    (pStar vStar : Nat) : Prop :=
  transition.InRange ∧
  transition.beforeBaseEscrow = transition.afterBaseEscrow + vStar ∧
  transition.afterBuyerBaseCustody =
    transition.beforeBuyerBaseCustody + vStar ∧
  transition.beforeQuoteEscrow =
    transition.afterQuoteEscrow + transition.quoteAmount ∧
  transition.afterSellerQuoteCustody =
    transition.beforeSellerQuoteCustody + transition.quoteAmount ∧
  transition.quoteAmount = transition.quoteTick * (pStar + 1) * vStar

/-- Custody changes by exactly the two clearing amounts, not merely by some
conserving reallocation. -/
theorem SettlementTransition.valid_exact_custody
    {transition : SettlementTransition} {pStar vStar : Nat}
    (valid : transition.Valid pStar vStar) :
    transition.afterBuyerBaseCustody - transition.beforeBuyerBaseCustody = vStar ∧
    transition.afterSellerQuoteCustody - transition.beforeSellerQuoteCustody =
      transition.quoteAmount := by
  rcases valid with ⟨_, _, hbuyer, _, hseller, _⟩
  omega

/-- Conservation is a consequence of exact debit and credit, rather than the
only property asserted about the transition. -/
theorem SettlementTransition.valid_conserves_custody
    {transition : SettlementTransition} {pStar vStar : Nat}
    (valid : transition.Valid pStar vStar) :
    transition.afterBaseEscrow + transition.afterBuyerBaseCustody =
      transition.beforeBaseEscrow + transition.beforeBuyerBaseCustody ∧
    transition.afterQuoteEscrow + transition.afterSellerQuoteCustody =
      transition.beforeQuoteEscrow + transition.beforeSellerQuoteCustody := by
  rcases valid with ⟨_, hbase, hbuyer, hquote, hseller, _⟩
  omega

/-- The quote debit is the authored tick at the proved clearing bucket times
the proved clearing volume. -/
theorem SettlementTransition.valid_quote_amount
    {transition : SettlementTransition} {pStar vStar : Nat}
    (valid : transition.Valid pStar vStar) :
    transition.quoteAmount = transition.quoteTick * (pStar + 1) * vStar :=
  valid.2.2.2.2.2

/-- Every operand of every settlement equality is an honest integer strictly
below BabyBear.  Thus a `Valid` transition cannot hide a debit, credit or quote
mint behind one field-modulus wrap. -/
theorem SettlementTransition.valid_no_wrap_envelope
    {transition : SettlementTransition} {pStar vStar : Nat}
    (valid : transition.Valid pStar vStar) :
    transition.beforeBaseEscrow < 2013265921 ∧
    transition.afterBaseEscrow + vStar < 2013265921 ∧
    transition.afterBuyerBaseCustody < 2013265921 ∧
    transition.beforeBuyerBaseCustody + vStar < 2013265921 ∧
    transition.beforeQuoteEscrow < 2013265921 ∧
    transition.afterQuoteEscrow + transition.quoteAmount < 2013265921 ∧
    transition.afterSellerQuoteCustody < 2013265921 ∧
    transition.beforeSellerQuoteCustody + transition.quoteAmount < 2013265921 ∧
    transition.quoteAmount < 2013265921 ∧
    transition.quoteTick * (pStar + 1) * vStar < 2013265921 := by
  rcases valid with ⟨hrange, hbase, hbuyer, hquote, hseller, hamount⟩
  rcases hrange with ⟨hbb, hab, hbc, hac, hbq, haq, hsc, hasc, _, ha⟩
  have hlimit : STATE_VALUE_LIMIT < 2013265921 := by decide
  constructor
  · exact hbb.trans hlimit
  constructor
  · rw [← hbase]
    exact hbb.trans hlimit
  constructor
  · exact hac.trans hlimit
  constructor
  · rw [← hbuyer]
    exact hac.trans hlimit
  constructor
  · exact hbq.trans hlimit
  constructor
  · rw [← hquote]
    exact hbq.trans hlimit
  constructor
  · exact hasc.trans hlimit
  constructor
  · rw [← hseller]
    exact hasc.trans hlimit
  constructor
  · exact ha.trans hlimit
  · rw [← hamount]
    exact ha.trans hlimit

/-! ## Column and public-input layout -/

def DIGEST_COUNT : Nat := 4
def DIGEST_LANES : Nat := DIGEST_COUNT * DIGEST_WIDTH
def JUDGE_DIGEST_BASE : Nat := Market.DarkBazaarPrivateDescriptor.TRACE_WIDTH
def INPUT_DIGEST (lane : Nat) : Nat := JUDGE_DIGEST_BASE + lane
def SUCCESSOR_DIGEST (lane : Nat) : Nat := JUDGE_DIGEST_BASE + 8 + lane
def PUBLIC_VIEW_DIGEST (lane : Nat) : Nat := JUDGE_DIGEST_BASE + 16 + lane
def RECEIPT_DIGEST (lane : Nat) : Nat := JUDGE_DIGEST_BASE + 24 + lane

def VISIBILITY : Nat := JUDGE_DIGEST_BASE + DIGEST_LANES
def SCALAR_BASE : Nat := VISIBILITY + 1
def SCALAR_COUNT : Nat := 10
def SCALAR (field : Nat) : Nat := SCALAR_BASE + field

def BEFORE_BASE_ESCROW : Nat := SCALAR 0
def AFTER_BASE_ESCROW : Nat := SCALAR 1
def BEFORE_BUYER_BASE_CUSTODY : Nat := SCALAR 2
def AFTER_BUYER_BASE_CUSTODY : Nat := SCALAR 3
def BEFORE_QUOTE_ESCROW : Nat := SCALAR 4
def AFTER_QUOTE_ESCROW : Nat := SCALAR 5
def BEFORE_SELLER_QUOTE_CUSTODY : Nat := SCALAR 6
def AFTER_SELLER_QUOTE_CUSTODY : Nat := SCALAR 7
def QUOTE_TICK : Nat := SCALAR 8
def QUOTE_AMOUNT : Nat := SCALAR 9

def RANGE_BIT_BASE : Nat := SCALAR_BASE + SCALAR_COUNT
def STATE_RANGE_TARGETS : Nat := 9
def STATE_RANGE_COLUMN (target : Nat) : Nat :=
  if target < 8 then SCALAR target else QUOTE_AMOUNT
def STATE_RANGE_BIT (target bit : Nat) : Nat :=
  RANGE_BIT_BASE + STATE_VALUE_BITS * target + bit
def QUOTE_TICK_BIT (bit : Nat) : Nat :=
  RANGE_BIT_BASE + STATE_VALUE_BITS * STATE_RANGE_TARGETS + bit

def TRACE_WIDTH : Nat :=
  RANGE_BIT_BASE + STATE_VALUE_BITS * STATE_RANGE_TARGETS + QUOTE_TICK_BITS
def PI_BASE : Nat := 12
def DIGEST_PI_BASE : Nat := PI_BASE
def VISIBILITY_PI : Nat := DIGEST_PI_BASE + DIGEST_LANES
def SCALAR_PI_BASE : Nat := VISIBILITY_PI + 1
def PI_COUNT : Nat := SCALAR_PI_BASE + SCALAR_COUNT

structure PublicStatement where
  privateBook : Market.DarkBazaarPrivateDescriptor.PublicStatement
  inputDigest : Fin 8 → Int
  successorDigest : Fin 8 → Int
  publicViewDigest : Fin 8 → Int
  receiptDigest : Fin 8 → Int
  visibility : ProverVisibilityGrade
  transition : SettlementTransition
deriving DecidableEq, Repr

def digestPins : List VmConstraint2 :=
  (List.range 8).map (fun lane =>
    .base (.piBinding .first (INPUT_DIGEST lane) (DIGEST_PI_BASE + lane))) ++
  (List.range 8).map (fun lane =>
    .base (.piBinding .first (SUCCESSOR_DIGEST lane) (DIGEST_PI_BASE + 8 + lane))) ++
  (List.range 8).map (fun lane =>
    .base (.piBinding .first (PUBLIC_VIEW_DIGEST lane) (DIGEST_PI_BASE + 16 + lane))) ++
  (List.range 8).map (fun lane =>
    .base (.piBinding .first (RECEIPT_DIGEST lane) (DIGEST_PI_BASE + 24 + lane)))

def settlementPins : List VmConstraint2 :=
  [.base (.piBinding .first VISIBILITY VISIBILITY_PI)] ++
  (List.range SCALAR_COUNT).map fun field =>
    .base (.piBinding .first (SCALAR field) (SCALAR_PI_BASE + field))

def v3PublicPins : List VmConstraint2 := digestPins ++ settlementPins

def rangeBodiesFor (col bitBase bits : Nat) : List EmittedExpr :=
  recompose col (fun bit => bitBase + bit) bits ::
    (List.range bits).map (fun bit => binaryBody (bitBase + bit))

def rangeBodies : List EmittedExpr :=
  ((List.range STATE_RANGE_TARGETS).flatMap fun target =>
    rangeBodiesFor (STATE_RANGE_COLUMN target)
      (STATE_RANGE_BIT target 0) STATE_VALUE_BITS) ++
  rangeBodiesFor QUOTE_TICK (QUOTE_TICK_BIT 0) QUOTE_TICK_BITS

def privacyBody : EmittedExpr :=
  sub (v VISIBILITY) (c (PROVEN_VISIBILITY.code : Int))

/-- These are the five exact public settlement equations. -/
def settlementBodies : List EmittedExpr :=
  [ sub (v BEFORE_BASE_ESCROW) (add (v AFTER_BASE_ESCROW) (v VSTAR))
  , sub (v AFTER_BUYER_BASE_CUSTODY)
      (add (v BEFORE_BUYER_BASE_CUSTODY) (v VSTAR))
  , sub (v BEFORE_QUOTE_ESCROW) (add (v AFTER_QUOTE_ESCROW) (v QUOTE_AMOUNT))
  , sub (v AFTER_SELLER_QUOTE_CUSTODY)
      (add (v BEFORE_SELLER_QUOTE_CUSTODY) (v QUOTE_AMOUNT))
  , sub (v QUOTE_AMOUNT)
      (mul (mul (v QUOTE_TICK) (add (v PSTAR) (c 1))) (v VSTAR)) ]

def v3SemanticBodies : List EmittedExpr :=
  privacyBody :: (rangeBodies ++ settlementBodies)

/-- V3 is additive over the complete v1 relation.  The descriptor is authored
here; Rust only interprets its emitted JSON. -/
def darkBazaarPrivatePoaSettlementN4K4Descriptor : EffectVmDescriptor2 :=
  { name := "dark-bazaar-private-poa-settlement-n4k4::transition-v3"
  , traceWidth := TRACE_WIDTH
  , piCount := PI_COUNT
  , tables := []
  , constraints := Market.DarkBazaarPrivateDescriptor.hashLookups ++
      Market.DarkBazaarPrivateDescriptor.semanticBodies.map
        (fun body => .base (.gate body)) ++
      v3SemanticBodies.map (fun body => .base (.gate body)) ++
      Market.DarkBazaarPrivateDescriptor.publicPins ++ v3PublicPins ++
      Market.DarkBazaarPrivateDescriptor.semanticBodies.map
        (fun body => .base (.boundary .last body)) ++
      v3SemanticBodies.map (fun body => .base (.boundary .last body))
  , hashSites := []
  , ranges := [] }

theorem descriptor_trace_width :
    darkBazaarPrivatePoaSettlementN4K4Descriptor.traceWidth = 496 := rfl

theorem descriptor_pi_count :
    darkBazaarPrivatePoaSettlementN4K4Descriptor.piCount = 55 := rfl

theorem digest_pins_length : digestPins.length = 32 := by decide

theorem settlement_pins_length : settlementPins.length = 11 := by decide

theorem settlement_bodies_length : settlementBodies.length = 5 := rfl

theorem state_range_last_target_is_quote_amount :
    STATE_RANGE_COLUMN 8 = QUOTE_AMOUNT := rfl

set_option maxRecDepth 100000 in
theorem range_bodies_length : rangeBodies.length = 282 := by decide

set_option maxRecDepth 100000 in
theorem v3_semantic_bodies_length : v3SemanticBodies.length = 288 := by decide

theorem visibility_is_not_house_blind :
    PROVEN_VISIBILITY ≠ ProverVisibilityGrade.noSingleViewer := by decide

theorem v1_constraints_subset :
    ∀ constraint ∈
        Market.DarkBazaarPrivateDescriptor.darkBazaarPrivateN4K4Descriptor.constraints,
      constraint ∈ darkBazaarPrivatePoaSettlementN4K4Descriptor.constraints := by
  intro constraint member
  simp only [Market.DarkBazaarPrivateDescriptor.darkBazaarPrivateN4K4Descriptor,
    darkBazaarPrivatePoaSettlementN4K4Descriptor, List.mem_append,
    List.mem_map] at member ⊢
  aesop

theorem v3_public_pin_sound
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash darkBazaarPrivatePoaSettlementN4K4Descriptor
      dbM0 dbF0 [] (constTrace a pis tf))
    {col pi : Nat}
    (member : VmConstraint2.base (.piBinding .first col pi) ∈ v3PublicPins) :
    a col ≡ pis pi [ZMOD BABYBEAR_MODULUS] := by
  have constraintMember :
      VmConstraint2.base (.piBinding .first col pi) ∈
        darkBazaarPrivatePoaSettlementN4K4Descriptor.constraints := by
    simp only [darkBazaarPrivatePoaSettlementN4K4Descriptor, List.mem_append,
      List.mem_map]
    aesop
  have row := hsat.rowConstraints 0 (by simp [constTrace]) _ constraintMember
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm,
    BABYBEAR_MODULUS] using row

theorem v3_semantic_gate_vanishes
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash darkBazaarPrivatePoaSettlementN4K4Descriptor
      dbM0 dbF0 [] (constTrace a pis tf))
    {body : EmittedExpr} (member : body ∈ v3SemanticBodies) :
    body.eval a ≡ 0 [ZMOD BABYBEAR_MODULUS] := by
  have constraintMember : VmConstraint2.base (.gate body) ∈
      darkBazaarPrivatePoaSettlementN4K4Descriptor.constraints := by
    simp only [darkBazaarPrivatePoaSettlementN4K4Descriptor, List.mem_append,
      List.mem_map]
    aesop
  have row := hsat.rowConstraints 0 (by simp [constTrace]) _ constraintMember
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm,
    BABYBEAR_MODULUS] using row

/-- The typed grade is an actual AIR gate. -/
theorem visibility_gate_mem : privacyBody ∈ v3SemanticBodies := by
  simp [v3SemanticBodies]

/-- All five exact transition equations are emitted as gates. -/
theorem settlement_gate_mem (body : EmittedExpr) (member : body ∈ settlementBodies) :
    body ∈ v3SemanticBodies := by
  simp [v3SemanticBodies, member]

#assert_axioms SettlementTransition.valid_exact_custody
#assert_axioms SettlementTransition.valid_conserves_custody
#assert_axioms SettlementTransition.valid_quote_amount
#assert_axioms SettlementTransition.valid_no_wrap_envelope
#assert_axioms descriptor_trace_width
#assert_axioms descriptor_pi_count
#assert_axioms digest_pins_length
#assert_axioms settlement_pins_length
#assert_axioms settlement_bodies_length
#assert_axioms state_range_last_target_is_quote_amount
#assert_axioms range_bodies_length
#assert_axioms v3_semantic_bodies_length
#assert_axioms visibility_is_not_house_blind
#assert_axioms v1_constraints_subset
#assert_axioms v3_public_pin_sound
#assert_axioms v3_semantic_gate_vanishes
#assert_axioms visibility_gate_mem
#assert_axioms settlement_gate_mem

end Market.DarkBazaarPrivatePoaSettlementDescriptor
