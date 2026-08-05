/-
# PoA Dark Bazaar private settlement descriptor — anchored v4

## What changed, and why the v3 public statement was 60% decoration

V3 published fifty-five public inputs.  Thirty-two of them were the eight lanes
each of the Lean judge's `input`, `successor`, `public_view` and `receipt`
digests, and **no constraint of any kind named those columns**: not a gate body,
not a boundary body, not a lookup tuple.  `hashSites` was `[]`.  They were tied
to the trace by a `pi_binding` and to the circuit by nothing.  V3's own docblock
said it "binds the exact input, successor, public-view, and receipt digests";
`scripts/check-descriptor-anchor-inertness.py` measured thirty-three decorative
anchors and was right.

A verifier that checked the STARK against those public inputs — the ordinary
thing a light client, an aggregator or a recursive verifier does — learned
nothing whatsoever about them.  A prover could publish any thirty-two field
elements alongside a completely honest book, clearing and settlement, and every
gate still vanished.

⚑ **Those digests are not derivable in this AIR, and that is a fact about them,
not a budget.**  `Dregg2.Games.PathOfAngels.DarkBazaarJudgeWire.digestString`
(`:738`) computes each one as `CommitmentTreeWide.hashTo8 domain (UTF-8 bytes of
a canonical JSON string)` — `OutputWire.ofTransition` (`:752-758`) hashes
`successor.toJson`, `input.claim.toJson`, and a JSON preimage that embeds the
other three digests in hex.  Recomputing them in-circuit means running a JSON
serializer and a several-hundred-byte sponge inside a four-row fixed-width
BabyBear trace.  Absorbing them as chip *inputs* instead would be worse than
leaving them alone: it would move the inertness census to zero while the values
stayed free witnesses, which is precisely the co-occurrence-is-not-derivation
laundering `LightClientAnchorConnectivity` refuses.

So V4 stops publishing a statement this circuit cannot make, and publishes one
it can:

* the four judge-digest column blocks and their thirty-two pins are **DELETED**;
* eight new `ANCHOR` lanes are published, and they are the **image**, under the
  deployed Poseidon2 chip, of the rows this proof already exhibits — the private
  book root, the clearing output, the ten settlement scalars and the visibility
  grade.  Two staged arity-16 absorbs, forced by `chip_lookup_sound_N` exactly
  as `DarkBazaarPrivateDescriptor.rootLookup` forces the book root.

Every v1 market tooth and every v3 settlement tooth is retained: exact debit,
exact credit, authored quote calculation, both per-asset conservation
consequences, and the 2^28 / 2^20 range family that keeps every integer
consequence strictly inside BabyBear.

## Flag day

`dark-bazaar-private-poa-settlement-n4k4::transition-v3` is GONE, replaced by
`::anchored-v4`.  Trace width 496 → 480, public inputs 55 → 31.  The descriptor
JSON re-emits and the verifying key rotates; no v3 proof, statement or public
vector loads against v4, and none should.  The four judge digests keep being
checked where they can actually be checked — host-side in
`circuit-prove/src/dark_bazaar_private_poa_settlement.rs`, against a judge the
verifier runs itself — and are no longer laundered through the proof's public
inputs as though the AIR had attested them.

The private order book remains absent from the public vector and hidden from the
verifier by the Rust HidingFRI configuration.  The trace producer still receives
the opening.  `ProverVisibilityGrade.verifierShieldedProducerVisible` is
therefore a typed public grade fixed by the AIR; this file makes no house-blind
or no-single-viewer claim.
-/
import Market.DarkBazaarPrivateDescriptor

namespace Market.DarkBazaarPrivatePoaSettlementDescriptor

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 Satisfied2 TraceFamily VmConstraint2 TableId
    ChipTableSoundN chipLookupTupleN chip_lookup_sound_N emitVmJson2)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Market.DarkBazaarPrivateDescriptor

set_option autoImplicit false

def VERSION : Nat := 4

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

/-- The exact public transition relation enforced by the five v4 arithmetic
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

/-! ## Column and public-input layout

The thirty-two judge-digest columns v3 carried at 181..212 are gone.  In their
place sit the sixteen columns of the two-stage settlement anchor: eight
intermediate `HALF` lanes and the eight published `ANCHOR` lanes. -/

/-- Stage-1 domain tag, ASCII `DBH1`, distinct from
`DarkBazaarPrivateDescriptor.ROOT_DOMAIN_TAG` (`DBGR`). -/
def HALF_DOMAIN_TAG : Int := 1145194545

/-- Stage-2 domain tag, ASCII `DBA1`. -/
def ANCHOR_DOMAIN_TAG : Int := 1145192753

def HALF_BASE : Nat := Market.DarkBazaarPrivateDescriptor.TRACE_WIDTH
def HALF (lane : Nat) : Nat := HALF_BASE + lane
def ANCHOR_BASE : Nat := HALF_BASE + DIGEST_WIDTH
def ANCHOR (lane : Nat) : Nat := ANCHOR_BASE + lane

def VISIBILITY : Nat := ANCHOR_BASE + DIGEST_WIDTH
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

def ANCHOR_PI_BASE : Nat := 12
def VISIBILITY_PI : Nat := ANCHOR_PI_BASE + DIGEST_WIDTH
def SCALAR_PI_BASE : Nat := VISIBILITY_PI + 1
def PI_COUNT : Nat := SCALAR_PI_BASE + SCALAR_COUNT

structure PublicStatement where
  privateBook : Market.DarkBazaarPrivateDescriptor.PublicStatement
  settlementAnchor : Fin 8 → Int
  visibility : ProverVisibilityGrade
  transition : SettlementTransition
deriving DecidableEq, Repr

/-! ## The settlement anchor — two staged absorbs on the deployed chip

Twenty-one values constitute the settlement: the eight lanes of the private book
root, the ten settlement scalars, the visibility grade, and the two clearing
outputs `p*` and `V*`.  The deployed chip admits only
`CHIP_ADMITTED_ARITIES = [0, 2, 3, 4, 7, 11, 16]`, so twenty-one values plus
domain separation is two absorbs, each at arity sixteen — the same arity the
already-deployed `rootLookup` uses.

Stage 1 takes the book root and the first six scalars; stage 2 takes stage 1's
eight output lanes, the remaining four scalars, the visibility grade and the
clearing.  Nothing is dropped and nothing is truncated: the published anchor is
a function of all twenty-one. -/

def halfInputExprs : List EmittedExpr :=
  [c HALF_DOMAIN_TAG] ++
    (List.range DIGEST_WIDTH).map (fun lane => v (ROOT lane)) ++
    (List.range 6).map (fun field => v (SCALAR field)) ++
    [c 0]

def halfDigestCols : List Nat := (List.range DIGEST_WIDTH).map HALF

def halfLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, chipLookupTupleN halfInputExprs halfDigestCols⟩

def anchorInputExprs : List EmittedExpr :=
  [c ANCHOR_DOMAIN_TAG] ++
    (List.range DIGEST_WIDTH).map (fun lane => v (HALF lane)) ++
    (List.range 4).map (fun field => v (SCALAR (6 + field))) ++
    [v VISIBILITY, v PSTAR, v VSTAR]

def anchorDigestCols : List Nat := (List.range DIGEST_WIDTH).map ANCHOR

def anchorLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, chipLookupTupleN anchorInputExprs anchorDigestCols⟩

/-- The two settlement absorbs, in stage order. -/
def settlementHashLookups : List VmConstraint2 := [halfLookup, anchorLookup]

/-! ## Public pins -/

def anchorPins : List VmConstraint2 :=
  (List.range DIGEST_WIDTH).map fun lane =>
    .base (.piBinding .first (ANCHOR lane) (ANCHOR_PI_BASE + lane))

def settlementPins : List VmConstraint2 :=
  [.base (.piBinding .first VISIBILITY VISIBILITY_PI)] ++
  (List.range SCALAR_COUNT).map fun field =>
    .base (.piBinding .first (SCALAR field) (SCALAR_PI_BASE + field))

def v4PublicPins : List VmConstraint2 := anchorPins ++ settlementPins

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

def v4SemanticBodies : List EmittedExpr :=
  privacyBody :: (rangeBodies ++ settlementBodies)

/-- V4 is additive over the complete v1 relation.  The descriptor is authored
here; Rust only interprets its emitted JSON. -/
def darkBazaarPrivatePoaSettlementN4K4Descriptor : EffectVmDescriptor2 :=
  { name := "dark-bazaar-private-poa-settlement-n4k4::anchored-v4"
  , traceWidth := TRACE_WIDTH
  , piCount := PI_COUNT
  , tables := []
  , constraints := Market.DarkBazaarPrivateDescriptor.hashLookups ++
      settlementHashLookups ++
      Market.DarkBazaarPrivateDescriptor.semanticBodies.map
        (fun body => .base (.gate body)) ++
      v4SemanticBodies.map (fun body => .base (.gate body)) ++
      Market.DarkBazaarPrivateDescriptor.publicPins ++ v4PublicPins ++
      Market.DarkBazaarPrivateDescriptor.semanticBodies.map
        (fun body => .base (.boundary .last body)) ++
      v4SemanticBodies.map (fun body => .base (.boundary .last body))
  , hashSites := []
  , ranges := [] }

theorem descriptor_trace_width :
    darkBazaarPrivatePoaSettlementN4K4Descriptor.traceWidth = 480 := rfl

theorem descriptor_pi_count :
    darkBazaarPrivatePoaSettlementN4K4Descriptor.piCount = 31 := rfl

/-- ⚑ The two settlement absorbs are at an arity the deployed chip AIR admits.
At any other arity the lookup has no satisfying assignment and the descriptor is
unprovable — `chipLookupTupleN`'s `hAdm` autoParam refuses to elaborate, so this
is belt-and-braces on a condition already discharged at the construction site. -/
theorem settlement_absorb_arities_are_admitted :
    Dregg2.Circuit.DescriptorIR2.ChipArityAdmitted halfInputExprs.length ∧
    Dregg2.Circuit.DescriptorIR2.ChipArityAdmitted anchorInputExprs.length := by
  constructor <;> decide

theorem half_absorb_is_arity_sixteen : halfInputExprs.length = 16 := by decide

theorem anchor_absorb_is_arity_sixteen : anchorInputExprs.length = 16 := by decide

theorem anchor_pins_length : anchorPins.length = 8 := by decide

theorem settlement_pins_length : settlementPins.length = 11 := by decide

theorem settlement_bodies_length : settlementBodies.length = 5 := rfl

theorem state_range_last_target_is_quote_amount :
    STATE_RANGE_COLUMN 8 = QUOTE_AMOUNT := rfl

set_option maxRecDepth 100000 in
theorem range_bodies_length : rangeBodies.length = 282 := by decide

set_option maxRecDepth 100000 in
theorem v4_semantic_bodies_length : v4SemanticBodies.length = 288 := by decide

theorem visibility_is_not_house_blind :
    PROVEN_VISIBILITY ≠ ProverVisibilityGrade.noSingleViewer := by decide

/-- ⚑ **THE JUDGE DIGESTS ARE GONE FROM THE PUBLIC VECTOR.** V3 published 55;
V4 publishes 31, and the 24 that survive from v3 are the ten scalars, the
visibility grade and the twelve v1 lanes.  The difference is exactly the
thirty-two unbindable digest lanes, replaced by eight derived anchor lanes. -/
theorem v4_publishes_thirty_one_and_v3_published_fifty_five :
    darkBazaarPrivatePoaSettlementN4K4Descriptor.piCount = 31 ∧
    55 - 32 + 8 = 31 := by decide

theorem v1_constraints_subset :
    ∀ constraint ∈
        Market.DarkBazaarPrivateDescriptor.darkBazaarPrivateN4K4Descriptor.constraints,
      constraint ∈ darkBazaarPrivatePoaSettlementN4K4Descriptor.constraints := by
  intro constraint member
  simp only [Market.DarkBazaarPrivateDescriptor.darkBazaarPrivateN4K4Descriptor,
    darkBazaarPrivatePoaSettlementN4K4Descriptor, List.mem_append,
    List.mem_map] at member ⊢
  aesop

theorem v4_public_pin_sound
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash darkBazaarPrivatePoaSettlementN4K4Descriptor
      dbM0 dbF0 [] (constTrace a pis tf))
    {col pi : Nat}
    (member : VmConstraint2.base (.piBinding .first col pi) ∈ v4PublicPins) :
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

theorem v4_semantic_gate_vanishes
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash darkBazaarPrivatePoaSettlementN4K4Descriptor
      dbM0 dbF0 [] (constTrace a pis tf))
    {body : EmittedExpr} (member : body ∈ v4SemanticBodies) :
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
theorem visibility_gate_mem : privacyBody ∈ v4SemanticBodies := by
  simp [v4SemanticBodies]

/-- All five exact transition equations are emitted as gates. -/
theorem settlement_gate_mem (body : EmittedExpr) (member : body ∈ settlementBodies) :
    body ∈ v4SemanticBodies := by
  simp [v4SemanticBodies, member]

/-! ## §A — the anchor is DERIVED, not carried

These are the positive statements that replace v3's thirty-two `pi_binding`s.
They are the `DarkBazaarPrivateDescriptor.wide_root_lookup_sound` idiom, and the
same lever — `chip_lookup_sound_N` against a `ChipTableSoundN` chip table — that
`LightClientSolStakeFoldAir` uses to make Solana's published trust anchor the
image of the stake rows rather than a number beside them. -/

theorem half_lookup_mem :
    halfLookup ∈ darkBazaarPrivatePoaSettlementN4K4Descriptor.constraints := by
  simp [darkBazaarPrivatePoaSettlementN4K4Descriptor, settlementHashLookups]

theorem anchor_lookup_mem :
    anchorLookup ∈ darkBazaarPrivatePoaSettlementN4K4Descriptor.constraints := by
  simp [darkBazaarPrivatePoaSettlementN4K4Descriptor, settlementHashLookups]

/-- Stage 1: the eight `HALF` columns are the genuine permutation image of the
domain tag, the eight book-root lanes and the first six settlement scalars. -/
theorem half_lookup_sound
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash darkBazaarPrivatePoaSettlementN4K4Descriptor
      dbM0 dbF0 [] (constTrace a pis tf)) :
    halfDigestCols.map a = permOut (halfInputExprs.map (·.eval a)) := by
  have hrow := hsat.rowConstraints 0 (by simp [constTrace]) halfLookup half_lookup_mem
  have hlookup :
      (chipLookupTupleN halfInputExprs halfDigestCols).map (·.eval a) ∈
        tf TableId.poseidon2 := by
    simpa [halfLookup, VmConstraint2.holdsAt,
      Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt] using hrow
  exact chip_lookup_sound_N permOut (tf TableId.poseidon2) hChip a
    halfInputExprs halfDigestCols (by decide) hlookup

/-- ⚑⚑ **THE PUBLISHED SETTLEMENT ANCHOR IS THE IMAGE OF THE EXHIBITED ROWS.**

Stage 2: the eight `ANCHOR` columns — the ones `anchorPins` publishes as PI
12..19 — are the genuine permutation image of stage 1's output, the remaining
four settlement scalars, the visibility grade and the clearing `p*`/`V*`.
Composed with `half_lookup_sound` and with
`DarkBazaarPrivateDescriptor.wide_root_lookup_sound`, the published anchor is a
function of the private book itself.

⚠ This is the statement v3 could not make about any of its thirty-two digest
lanes, and it is stronger than the connectivity census can see: the census
measures co-occurrence, and co-occurrence would have been satisfied just as well
by absorbing a free witness.  What makes this derivation is `chip_lookup_sound_N`
forcing the whole `permOut` block column-for-column against a chip table whose
rows the prover re-derives from the genuine permutation. -/
theorem anchor_lookup_sound
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash darkBazaarPrivatePoaSettlementN4K4Descriptor
      dbM0 dbF0 [] (constTrace a pis tf)) :
    anchorDigestCols.map a = permOut (anchorInputExprs.map (·.eval a)) := by
  have hrow := hsat.rowConstraints 0 (by simp [constTrace]) anchorLookup anchor_lookup_mem
  have hlookup :
      (chipLookupTupleN anchorInputExprs anchorDigestCols).map (·.eval a) ∈
        tf TableId.poseidon2 := by
    simpa [anchorLookup, VmConstraint2.holdsAt,
      Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt] using hrow
  exact chip_lookup_sound_N permOut (tf TableId.poseidon2) hChip a
    anchorInputExprs anchorDigestCols (by decide) hlookup

/-- …and the value the verifier reads out of the public vector is that image.
Every published anchor lane equals the corresponding permutation output lane,
modulo BabyBear.  A prover who wants a different published anchor must move a
settlement row, the clearing, the book root or the visibility grade — or find a
Poseidon2 collision. -/
theorem published_anchor_is_the_permutation_image
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash darkBazaarPrivatePoaSettlementN4K4Descriptor
      dbM0 dbF0 [] (constTrace a pis tf)) :
    anchorDigestCols.map a = permOut (anchorInputExprs.map (·.eval a)) ∧
    ∀ lane : Fin 8,
      pis (ANCHOR_PI_BASE + lane.val) ≡ a (ANCHOR lane.val) [ZMOD BABYBEAR_MODULUS] := by
  refine ⟨anchor_lookup_sound permOut hChip hsat, fun lane => ?_⟩
  have hpin : VmConstraint2.base
      (.piBinding .first (ANCHOR lane.val) (ANCHOR_PI_BASE + lane.val)) ∈ v4PublicPins := by
    simp only [v4PublicPins, anchorPins, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl ⟨lane.val, lane.isLt, rfl⟩
  exact (v4_public_pin_sound hsat hpin).symm

/-! ## §B — the visibility grade, and the one honest residue

`VISIBILITY` is PI-bound and forced to the constant 1 by a ONE-COLUMN gate.  A
one-column gate joins nothing, so a pure connectivity census scores the column a
singleton and calls it decorative.  That verdict is a measurement artifact and
the theorem below is why: the published grade is not merely *joined* to
something, it is *equal to a constant* in every satisfying assignment, which is
strictly more than any anchor in the light-client census can say.

⚠ Do not read this as licence to pin an anchor to a constant and call it bound.
It is meaningful here only because the grade IS a family constant — every proof
of this descriptor carries the same one — and the AIR is what fixes it. -/

/-- The published visibility grade is the constant 1, not a prover choice. -/
theorem visibility_pi_is_forced_to_the_proven_grade
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash darkBazaarPrivatePoaSettlementN4K4Descriptor
      dbM0 dbF0 [] (constTrace a pis tf)) :
    pis VISIBILITY_PI ≡ (PROVEN_VISIBILITY.code : Int) [ZMOD BABYBEAR_MODULUS] := by
  have hgate := v4_semantic_gate_vanishes hsat visibility_gate_mem
  have hpin : VmConstraint2.base
      (.piBinding .first VISIBILITY VISIBILITY_PI) ∈ v4PublicPins := by
    simp [v4PublicPins, settlementPins]
  have hcol := v4_public_pin_sound hsat hpin
  have hval : a VISIBILITY ≡ (PROVEN_VISIBILITY.code : Int) [ZMOD BABYBEAR_MODULUS] := by
    have h := hgate
    simp only [privacyBody, sub, neg, add, mul, v, c, EmittedExpr.eval] at h
    simpa using h.add_right (PROVEN_VISIBILITY.code : Int)
  exact hcol.symm.trans hval

/-- The anchor absorbs the visibility grade, so the published anchor changes if
the grade does.  Together with the gate above, the grade is both forced and
welded rather than carried. -/
theorem visibility_is_absorbed_by_the_anchor :
    v VISIBILITY ∈ anchorInputExprs := by
  simp [anchorInputExprs]

#assert_axioms SettlementTransition.valid_exact_custody
#assert_axioms SettlementTransition.valid_conserves_custody
#assert_axioms SettlementTransition.valid_quote_amount
#assert_axioms SettlementTransition.valid_no_wrap_envelope
#assert_axioms descriptor_trace_width
#assert_axioms descriptor_pi_count
#assert_axioms settlement_absorb_arities_are_admitted
#assert_axioms half_absorb_is_arity_sixteen
#assert_axioms anchor_absorb_is_arity_sixteen
#assert_axioms anchor_pins_length
#assert_axioms settlement_pins_length
#assert_axioms settlement_bodies_length
#assert_axioms state_range_last_target_is_quote_amount
#assert_axioms range_bodies_length
#assert_axioms v4_semantic_bodies_length
#assert_axioms visibility_is_not_house_blind
#assert_axioms v4_publishes_thirty_one_and_v3_published_fifty_five
#assert_axioms v1_constraints_subset
#assert_axioms v4_public_pin_sound
#assert_axioms v4_semantic_gate_vanishes
#assert_axioms visibility_gate_mem
#assert_axioms settlement_gate_mem
#assert_axioms half_lookup_mem
#assert_axioms anchor_lookup_mem
#assert_axioms half_lookup_sound
#assert_axioms anchor_lookup_sound
#assert_axioms published_anchor_is_the_permutation_image
#assert_axioms visibility_pi_is_forced_to_the_proven_grade
#assert_axioms visibility_is_absorbed_by_the_anchor

end Market.DarkBazaarPrivatePoaSettlementDescriptor
