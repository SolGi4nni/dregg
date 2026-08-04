/-
# Path of Angels — Dark Bazaar semantic core

Dark Bazaar is a sealed, uniform-price batch exchange for expedition salvage and
ship resources.  The executable transition consumes only a public settlement
claim: authored market identity, private-book commitment, exact escrow/order
nullifiers, and the declared `(bucket, volume)` output.  A plaintext order book is
not a field of the claim, the state, or `applySettlement`.

The private book appears only under the proof-erased proposition
`ClaimHasValidPrivateOpening`.  One opaque capability,
`CombinedPrivateSettlementAuthorization`, is indexed by the exact whole public
claim.  A privately constructed `VerifiedSettlementEvidence` packages that
capability with its ordinary kernel-visible existential validity certificate.
There are not two proof-indexed tokens whose witnesses are silently identified
by proof irrelevance.  This module proves public state-machine consequences
conditionally on that evidence; it does not claim transcript security,
malicious-MPC security, or independent operators merely because the verifier
boundary is named.

Settlement is real accounting rather than a flow declared equal by construction.
Escrow balances are sums derived from intrinsically well-formed owned notes; the
transition removes exact notes, credits counterparties' custody balances, and
consumes both asset and stable private-order nullifiers.  Rebatching under another
batch id or source root cannot spend the same underlying inputs twice within the
same threaded/shared `BazaarState`; global protection requires a global registry.
-/
import Dregg2.Games.PathOfAngels.Core
import Market.FhEggClearing
import Market.MpcClearingSecurity
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.DarkBazaar

set_option autoImplicit false

/-! ## Concrete wire integer and protocol maxima -/

/- This semantic module chooses unsigned 64-bit wire integers.  Deployments may
refine these constants downward, but may not silently widen them without a wire
epoch/change. -/
namespace Wire

def u64Max : Nat := 18446744073709551615
def maxBuckets : Nat := 65536
def maxQuoteTick : Nat := 4294967295
def maxOrders : Nat := 4096
def maxOrderQuantity : Nat := 4294967295
def maxAllowedOutputs : Nat := 65536
def maxOutputVolume : Nat := 4294967295
def maxNoteAmount : Nat := u64Max
def maxCustodyBalance : Nat := u64Max
def maxBatchId : Nat := u64Max

def isU64 (value : Nat) : Prop := value ≤ u64Max

end Wire

/-! ## Authored identities and positive price schedule -/

structure BatchId where
  value : Nat
deriving DecidableEq, Repr

structure ParticipantId where
  value : Digest32
deriving DecidableEq

structure AssetNullifier where
  value : Digest32
deriving DecidableEq

structure OrderNullifier where
  value : Digest32
deriving DecidableEq

/-- Assets which can be exchanged without giving the market authority to invent
a new world resource.  A relic must already have a PoA `RelicId`. -/
inductive AssetRef where
  | relic (id : RelicId)
  | supplies
  | intel
  | munitions
  | propellant
deriving DecidableEq, Repr

/-- Bucket zero is not zero quote.  Authored bucket `b` denotes the positive
quote price `(b + 1) * quoteTick`. -/
structure PriceSchedule where
  buckets : Nat
  buckets_pos : 0 < buckets
  quoteTick : Nat
  quoteTick_pos : 0 < quoteTick
deriving DecidableEq

def PriceSchedule.quoteAt (schedule : PriceSchedule) (bucket : Nat) : Nat :=
  (bucket + 1) * schedule.quoteTick

theorem PriceSchedule.quoteAt_pos (schedule : PriceSchedule) (bucket : Nat) :
    0 < schedule.quoteAt bucket := by
  simp only [PriceSchedule.quoteAt]
  exact Nat.mul_pos (Nat.succ_pos bucket) schedule.quoteTick_pos

/-- The replay identity excludes proof transcripts and transport envelopes. -/
structure BatchKey where
  federationId : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  batchId : BatchId
  sourceRoot : Digest32
deriving DecidableEq

/-- The only private-clearing result opened to the public state machine. -/
structure ClearingOutput where
  bucket : Nat
  volume : Nat
deriving DecidableEq, Repr

/-- Stable authored market identity.  Batch-local replay coordinates are not
part of this identity. -/
structure StableMarketIdentity where
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  seller : ParticipantId
  buyer : ParticipantId
  parties_distinct : seller ≠ buyer
  baseAsset : AssetRef
  quoteAsset : AssetRef
  assets_distinct : baseAsset ≠ quoteAsset
deriving DecidableEq

/-- Complete state-authored market policy.  In particular, `allowedOutputs` is
looked up from state during admission; a claim cannot authorize its own output by
supplying a looser policy.  `maxPublicAssetInputs` is an explicit executable wire
and admission bound, while `maxOrders` bounds both private orders and public
order nullifiers. -/
structure MarketPolicy where
  pricing : PriceSchedule
  maxOrders : Nat
  maxOrderQuantity : Nat
  maxPublicAssetInputs : Nat
  allowedOutputs : Finset ClearingOutput
deriving DecidableEq

/-- A proposed batch repeats the complete authored identity and policy so that
the verifier can bind them into the private statement.  Admission accepts the
proposal only when both exactly equal the versions held in `BazaarState`.
Capacity is deliberately absent: it comes from escrow notes actually held. -/
structure BatchSpec where
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  batchId : BatchId
  sourceRoot : Digest32
  seller : ParticipantId
  buyer : ParticipantId
  parties_distinct : seller ≠ buyer
  baseAsset : AssetRef
  quoteAsset : AssetRef
  assets_distinct : baseAsset ≠ quoteAsset
  pricing : PriceSchedule
  maxOrders : Nat
  maxOrderQuantity : Nat
  /-- An authored finite set, not a range silently widened by the market. -/
  allowedOutputs : Finset ClearingOutput

def BatchSpec.stableIdentity (spec : BatchSpec) : StableMarketIdentity where
  federationId := spec.federationId
  contentRoot := spec.contentRoot
  activationDigest := spec.activationDigest
  contentSession := spec.contentSession
  contentEpoch := spec.contentEpoch
  seller := spec.seller
  buyer := spec.buyer
  parties_distinct := spec.parties_distinct
  baseAsset := spec.baseAsset
  quoteAsset := spec.quoteAsset
  assets_distinct := spec.assets_distinct

def BatchSpec.marketPolicy (spec : BatchSpec) : MarketPolicy where
  pricing := spec.pricing
  maxOrders := spec.maxOrders
  maxOrderQuantity := spec.maxOrderQuantity
  maxPublicAssetInputs := 2 * spec.maxOrders
  allowedOutputs := spec.allowedOutputs

def BatchSpec.key (spec : BatchSpec) : BatchKey where
  federationId := spec.federationId
  contentSession := spec.contentSession
  contentEpoch := spec.contentEpoch
  batchId := spec.batchId
  sourceRoot := spec.sourceRoot

/-! ## Public settlement claim and exact nullifiers -/

/-- A public escrow input.  Ownership, asset kind, amount, and the exact spend
nullifier are all explicit. -/
structure AssetInput where
  nullifier : AssetNullifier
  owner : ParticipantId
  asset : AssetRef
  amount : Nat
deriving DecidableEq

/-- The executable public carrier.  It contains a commitment and declared output,
never the private order book or private fills. -/
structure SettlementClaim where
  spec : BatchSpec
  privateBookCommitment : Digest32
  output : ClearingOutput
  baseInputs : Finset AssetInput
  quoteInputs : Finset AssetInput
  orderNullifiers : Finset OrderNullifier

def SettlementClaim.baseAmount (claim : SettlementClaim) : Nat :=
  claim.output.volume

def SettlementClaim.quotePrice (claim : SettlementClaim) : Nat :=
  claim.spec.pricing.quoteAt claim.output.bucket

def SettlementClaim.quoteAmount (claim : SettlementClaim) : Nat :=
  claim.quotePrice * claim.output.volume

def SettlementClaim.allAssetInputs (claim : SettlementClaim) : Finset AssetInput :=
  claim.baseInputs ∪ claim.quoteInputs

def SettlementClaim.assetNullifiers (claim : SettlementClaim) : Finset AssetNullifier :=
  claim.allAssetInputs.image AssetInput.nullifier

theorem SettlementClaim.quotePrice_pos (claim : SettlementClaim) :
    0 < claim.quotePrice :=
  claim.spec.pricing.quoteAt_pos claim.output.bucket

theorem SettlementClaim.quoteAmount_eq_authored_tick (claim : SettlementClaim) :
    claim.quoteAmount =
      ((claim.output.bucket + 1) * claim.spec.pricing.quoteTick) * claim.output.volume := rfl

/-! ## Executable semantic wire-range predicates -/

def PriceSchedule.WireBounded (schedule : PriceSchedule) : Prop :=
  schedule.buckets ≤ Wire.maxBuckets ∧
    schedule.quoteTick ≤ Wire.maxQuoteTick

instance PriceSchedule.instDecidableWireBounded (schedule : PriceSchedule) :
    Decidable schedule.WireBounded := by
  unfold PriceSchedule.WireBounded
  infer_instance

def ClearingOutput.WireBounded (output : ClearingOutput)
    (pricing : PriceSchedule) : Prop :=
  output.bucket < pricing.buckets ∧
    output.bucket ≤ Wire.u64Max ∧
    output.volume ≤ Wire.maxOutputVolume ∧
    pricing.quoteAt output.bucket ≤ Wire.u64Max ∧
    pricing.quoteAt output.bucket * output.volume ≤ Wire.u64Max

instance ClearingOutput.instDecidableWireBounded (output : ClearingOutput)
    (pricing : PriceSchedule) : Decidable (output.WireBounded pricing) := by
  unfold ClearingOutput.WireBounded
  infer_instance

def AssetInput.WireBounded (input : AssetInput) : Prop :=
  0 < input.amount ∧ input.amount ≤ Wire.maxNoteAmount

instance AssetInput.instDecidableWireBounded (input : AssetInput) :
    Decidable input.WireBounded := by
  unfold AssetInput.WireBounded
  infer_instance

end Dregg2.Games.PathOfAngels.DarkBazaar

namespace Dregg2.Games.PathOfAngels

def EpochId.WireBounded (epoch : EpochId) : Prop :=
  epoch.value ≤ DarkBazaar.Wire.u64Max

instance EpochId.instDecidableWireBounded (epoch : EpochId) :
    Decidable epoch.WireBounded := by
  unfold EpochId.WireBounded
  infer_instance

def RelicId.WireBounded (relic : RelicId) : Prop :=
  relic.value ≤ DarkBazaar.Wire.u64Max

instance RelicId.instDecidableWireBounded (relic : RelicId) :
    Decidable relic.WireBounded := by
  unfold RelicId.WireBounded
  infer_instance

end Dregg2.Games.PathOfAngels

namespace Dregg2.Games.PathOfAngels.DarkBazaar

def AssetRef.WireBounded (asset : AssetRef) : Prop :=
  match asset with
  | AssetRef.relic id => RelicId.WireBounded id
  | AssetRef.supplies => True
  | AssetRef.intel => True
  | AssetRef.munitions => True
  | AssetRef.propellant => True

instance AssetRef.instDecidableWireBounded (asset : AssetRef) :
    Decidable asset.WireBounded := by
  cases asset <;> simp only [AssetRef.WireBounded] <;> infer_instance

def StableMarketIdentity.WireBounded (identity : StableMarketIdentity) : Prop :=
  identity.contentEpoch.WireBounded ∧
    identity.baseAsset.WireBounded ∧ identity.quoteAsset.WireBounded

instance StableMarketIdentity.instDecidableWireBounded
    (identity : StableMarketIdentity) : Decidable identity.WireBounded := by
  unfold StableMarketIdentity.WireBounded
  infer_instance

def MarketPolicy.WireBounded (policy : MarketPolicy) : Prop :=
  policy.pricing.WireBounded ∧
    policy.maxOrders ≤ Wire.maxOrders ∧
    policy.maxOrderQuantity ≤ Wire.maxOrderQuantity ∧
    policy.maxPublicAssetInputs ≤ Wire.u64Max ∧
    policy.allowedOutputs.card ≤ Wire.maxAllowedOutputs ∧
    policy.allowedOutputs.filter
      (fun output => output.WireBounded policy.pricing) =
        policy.allowedOutputs

instance MarketPolicy.instDecidableWireBounded (policy : MarketPolicy) :
    Decidable policy.WireBounded := by
  unfold MarketPolicy.WireBounded
  infer_instance

def BatchSpec.WireBounded (spec : BatchSpec) : Prop :=
  spec.stableIdentity.WireBounded ∧
    spec.batchId.value ≤ Wire.maxBatchId ∧ spec.marketPolicy.WireBounded

instance BatchSpec.instDecidableWireBounded (spec : BatchSpec) :
    Decidable spec.WireBounded := by
  unfold BatchSpec.WireBounded
  infer_instance

def SettlementClaim.WireBounded (claim : SettlementClaim) : Prop :=
  claim.spec.WireBounded ∧
    claim.output.WireBounded claim.spec.pricing ∧
    claim.baseInputs.filter AssetInput.WireBounded = claim.baseInputs ∧
    claim.quoteInputs.filter AssetInput.WireBounded = claim.quoteInputs ∧
    claim.baseInputs.card + claim.quoteInputs.card ≤
      claim.spec.marketPolicy.maxPublicAssetInputs ∧
    claim.orderNullifiers.card ≤ claim.spec.maxOrders

instance SettlementClaim.instDecidableWireBounded (claim : SettlementClaim) :
    Decidable claim.WireBounded := by
  unfold SettlementClaim.WireBounded
  infer_instance

theorem SettlementClaim.quotePrice_fits_u64 (claim : SettlementClaim)
    (h : claim.WireBounded) : claim.quotePrice ≤ Wire.u64Max :=
  h.2.1.2.2.2.1

theorem SettlementClaim.quoteAmount_fits_u64 (claim : SettlementClaim)
    (h : claim.WireBounded) : claim.quoteAmount ≤ Wire.u64Max :=
  h.2.1.2.2.2.2

/-! ## Raw List/Nat boundary before Finset construction -/

/-- Lengths available to an outer byte decoder before it allocates collection
payloads.  That decoder is outside this semantic module; it must run
`allocationChecks` on the declared header before allocating the lists below.
The `RawSettlementClaim` value itself is the post-allocation List/Nat boundary,
so this module does **not** misdescribe a Finset check as a byte preallocation
guard. -/
structure RawCollectionHeader where
  allowedOutputsLength : Nat
  baseInputsLength : Nat
  quoteInputsLength : Nat
  orderNullifiersLength : Nat

def RawCollectionHeader.allocationChecks (header : RawCollectionHeader)
    (maxOrders : Nat) : Bool :=
  decide (maxOrders ≤ Wire.maxOrders) &&
  decide (header.allowedOutputsLength ≤ Wire.maxAllowedOutputs) &&
  decide (header.baseInputsLength + header.quoteInputsLength ≤ 2 * maxOrders) &&
  decide (header.orderNullifiersLength ≤ maxOrders)

/-- No Finset exists at this boundary. -/
structure RawSettlementClaim where
  identity : StableMarketIdentity
  buckets : Nat
  quoteTick : Nat
  maxOrders : Nat
  maxOrderQuantity : Nat
  batchId : BatchId
  sourceRoot : Digest32
  header : RawCollectionHeader
  allowedOutputs : List ClearingOutput
  privateBookCommitment : Digest32
  output : ClearingOutput
  baseInputs : List AssetInput
  quoteInputs : List AssetInput
  orderNullifiers : List OrderNullifier

def RawSettlementClaim.headerMatches (raw : RawSettlementClaim) : Bool :=
  decide (raw.header.allowedOutputsLength = raw.allowedOutputs.length) &&
  decide (raw.header.baseInputsLength = raw.baseInputs.length) &&
  decide (raw.header.quoteInputsLength = raw.quoteInputs.length) &&
  decide (raw.header.orderNullifiersLength = raw.orderNullifiers.length)

def RawSettlementClaim.scalarChecks (raw : RawSettlementClaim) : Bool :=
  decide (0 < raw.buckets) &&
  (decide (raw.buckets ≤ Wire.maxBuckets) &&
  (decide (0 < raw.quoteTick) &&
  (decide (raw.quoteTick ≤ Wire.maxQuoteTick) &&
  (decide raw.identity.WireBounded &&
  (decide (raw.maxOrders ≤ Wire.maxOrders) &&
  (decide (raw.maxOrderQuantity ≤ Wire.maxOrderQuantity) &&
  (decide (raw.batchId.value ≤ Wire.maxBatchId) &&
   decide (raw.output.bucket < raw.buckets ∧
    raw.output.bucket ≤ Wire.u64Max ∧
    raw.output.volume ≤ Wire.maxOutputVolume ∧
    (raw.output.bucket + 1) * raw.quoteTick ≤ Wire.u64Max ∧
    ((raw.output.bucket + 1) * raw.quoteTick) * raw.output.volume ≤
      Wire.u64Max))))))))

def RawSettlementClaim.collectionChecks (raw : RawSettlementClaim) : Bool :=
  decide raw.allowedOutputs.Nodup &&
  raw.allowedOutputs.all (fun output => decide
    (output.bucket < raw.buckets ∧
      output.bucket ≤ Wire.u64Max ∧
      output.volume ≤ Wire.maxOutputVolume ∧
      (output.bucket + 1) * raw.quoteTick ≤ Wire.u64Max ∧
      ((output.bucket + 1) * raw.quoteTick) * output.volume ≤ Wire.u64Max)) &&
  decide raw.baseInputs.Nodup &&
  raw.baseInputs.all (fun input => decide input.WireBounded) &&
  decide raw.quoteInputs.Nodup &&
  raw.quoteInputs.all (fun input => decide input.WireBounded) &&
  decide raw.orderNullifiers.Nodup

def RawSettlementClaim.wireChecks (raw : RawSettlementClaim) : Bool :=
  raw.headerMatches && (raw.scalarChecks && raw.collectionChecks)

theorem RawSettlementClaim.wireChecks_positive
    (raw : RawSettlementClaim) (h : raw.wireChecks = true) :
    0 < raw.buckets ∧ 0 < raw.quoteTick := by
  simp only [RawSettlementClaim.wireChecks, Bool.and_eq_true] at h
  have hscalar := h.2.1
  simp only [RawSettlementClaim.scalarChecks, Bool.and_eq_true,
    decide_eq_true_eq] at hscalar
  exact ⟨hscalar.1, hscalar.2.2.1⟩

def RawSettlementClaim.batchSpec (raw : RawSettlementClaim)
    (buckets_pos : 0 < raw.buckets) (quoteTick_pos : 0 < raw.quoteTick) :
    BatchSpec where
  federationId := raw.identity.federationId
  contentRoot := raw.identity.contentRoot
  activationDigest := raw.identity.activationDigest
  contentSession := raw.identity.contentSession
  contentEpoch := raw.identity.contentEpoch
  batchId := raw.batchId
  sourceRoot := raw.sourceRoot
  seller := raw.identity.seller
  buyer := raw.identity.buyer
  parties_distinct := raw.identity.parties_distinct
  baseAsset := raw.identity.baseAsset
  quoteAsset := raw.identity.quoteAsset
  assets_distinct := raw.identity.assets_distinct
  pricing := {
    buckets := raw.buckets
    buckets_pos := buckets_pos
    quoteTick := raw.quoteTick
    quoteTick_pos := quoteTick_pos
  }
  maxOrders := raw.maxOrders
  maxOrderQuantity := raw.maxOrderQuantity
  allowedOutputs := raw.allowedOutputs.toFinset

/-- Ordering is semantic: declared-length allocation guard first, then raw
scalar/list validation, and only inside both successful branches are Finsets
constructed.  Freshness filters run later in `admissionChecks`. -/
def RawSettlementClaim.decode (raw : RawSettlementClaim) : Option SettlementClaim :=
  if _halloc : raw.header.allocationChecks raw.maxOrders = true then
    if hwire : raw.wireChecks = true then
      let positive := raw.wireChecks_positive hwire
      some {
        spec := raw.batchSpec positive.1 positive.2
        privateBookCommitment := raw.privateBookCommitment
        output := raw.output
        baseInputs := raw.baseInputs.toFinset
        quoteInputs := raw.quoteInputs.toFinset
        orderNullifiers := raw.orderNullifiers.toFinset
      }
    else none
  else none

noncomputable def RawSettlementClaim.ofClaim
    (claim : SettlementClaim) : RawSettlementClaim where
  identity := claim.spec.stableIdentity
  buckets := claim.spec.pricing.buckets
  quoteTick := claim.spec.pricing.quoteTick
  maxOrders := claim.spec.maxOrders
  maxOrderQuantity := claim.spec.maxOrderQuantity
  batchId := claim.spec.batchId
  sourceRoot := claim.spec.sourceRoot
  header := {
    allowedOutputsLength := claim.spec.allowedOutputs.card
    baseInputsLength := claim.baseInputs.card
    quoteInputsLength := claim.quoteInputs.card
    orderNullifiersLength := claim.orderNullifiers.card
  }
  allowedOutputs := claim.spec.allowedOutputs.toList
  privateBookCommitment := claim.privateBookCommitment
  output := claim.output
  baseInputs := claim.baseInputs.toList
  quoteInputs := claim.quoteInputs.toList
  orderNullifiers := claim.orderNullifiers.toList

theorem RawSettlementClaim.decode_allocation_refused
    (raw : RawSettlementClaim)
    (h : raw.header.allocationChecks raw.maxOrders = false) :
    raw.decode = none := by
  simp [RawSettlementClaim.decode, h]

theorem RawSettlementClaim.decode_wire_refused
    (raw : RawSettlementClaim)
    (halloc : raw.header.allocationChecks raw.maxOrders = true)
    (hwire : raw.wireChecks = false) : raw.decode = none := by
  simp [RawSettlementClaim.decode, halloc, hwire]

theorem RawSettlementClaim.decode_identity_wire_refused
    (raw : RawSettlementClaim) (h : ¬ raw.identity.WireBounded) :
    raw.decode = none := by
  simp [RawSettlementClaim.decode, RawSettlementClaim.wireChecks,
    RawSettlementClaim.scalarChecks, h]

theorem RawSettlementClaim.decode_success_implies_guards
    {raw : RawSettlementClaim} {claim : SettlementClaim}
    (h : raw.decode = some claim) :
    raw.header.allocationChecks raw.maxOrders = true ∧
      raw.wireChecks = true := by
  unfold RawSettlementClaim.decode at h
  split at h
  · rename_i halloc
    split at h
    · rename_i hwire
      exact ⟨halloc, hwire⟩
    · contradiction
  · contradiction

theorem RawSettlementClaim.decode_ofClaim
    (claim : SettlementClaim)
    (halloc : (RawSettlementClaim.ofClaim claim).header.allocationChecks
      claim.spec.maxOrders = true)
    (hwire : (RawSettlementClaim.ofClaim claim).wireChecks = true) :
    (RawSettlementClaim.ofClaim claim).decode = some claim := by
  have halloc' : (RawSettlementClaim.ofClaim claim).header.allocationChecks
      (RawSettlementClaim.ofClaim claim).maxOrders = true := by
    simpa only [RawSettlementClaim.ofClaim] using halloc
  unfold RawSettlementClaim.decode
  rw [dif_pos halloc', dif_pos hwire]
  simp only [RawSettlementClaim.ofClaim, RawSettlementClaim.batchSpec,
    Finset.toList_toFinset]
  cases claim with
  | mk spec commitment output baseInputs quoteInputs orderNullifiers =>
    cases spec
    rfl

/-! ## Private existential validity and opaque verifier boundaries -/

/-- Stable identity of a private order.  Its public nullifier is a total,
batch-independent injective projection, so changing a batch id or source root
cannot give the same private order another semantic nullifier.  A deployment
may represent `value` as a domain-separated nullifier digest rather than a raw
identifier; this model needs stability and injectivity, not preimage visibility. -/
structure PrivateOrderId where
  value : Digest32
deriving DecidableEq

def PrivateOrderId.nullifier (id : PrivateOrderId) : OrderNullifier :=
  ⟨id.value⟩

theorem PrivateOrderId.nullifier_injective :
    Function.Injective PrivateOrderId.nullifier := by
  intro left right h
  cases left
  cases right
  cases h
  rfl

structure PrivateOrder where
  id : PrivateOrderId
  order : Market.LimitOrder

/-- The private book has stable, unique order identities and explicit size,
quantity, and bucket bounds.  It is a proof witness only; it never crosses the
public transition boundary. -/
structure PrivateBatch (spec : BatchSpec) where
  orders : List PrivateOrder
  orderIdsNodup : (orders.map PrivateOrder.id).Nodup
  ordersValid : Market.OrdersValid (orders.map PrivateOrder.order)
  orderCountBound : (orders.map PrivateOrder.order).length ≤ spec.maxOrders
  quantityBound : ∀ order ∈ orders.map PrivateOrder.order,
    order.qty ≤ (spec.maxOrderQuantity : Int)
  priceBound : ∀ order ∈ orders.map PrivateOrder.order,
    order.limit < spec.pricing.buckets

def PrivateBatch.book {spec : BatchSpec} (batch : PrivateBatch spec) :
    Market.OrderBook :=
  batch.orders.map PrivateOrder.order

def PrivateBatch.orderNullifierImage {spec : BatchSpec}
    (batch : PrivateBatch spec) : Finset OrderNullifier :=
  (batch.orders.map PrivateOrder.id).toFinset.image PrivateOrderId.nullifier

/-- The public order-nullifier set is exactly the stable image of private order
identities, with no collapse in cardinality. -/
def ExactPublicOrderNullifiers {spec : BatchSpec} (batch : PrivateBatch spec)
    (publicNullifiers : Finset OrderNullifier) : Prop :=
  publicNullifiers = batch.orderNullifierImage ∧
    publicNullifiers.card = batch.orders.length

/-- The public pair is exactly the fhEgg lowest-bucket volume argmax. -/
def ExactClearingOutput {spec : BatchSpec} (batch : PrivateBatch spec)
    (output : ClearingOutput) : Prop :=
  output.bucket = Market.crossing batch.book spec.pricing.buckets ∧
    (output.volume : Int) = Market.clearedVolume batch.book spec.pricing.buckets

/-- External whole-claim opening relation.  The exact `SettlementClaim` index
includes identity, policy, batch/source coordinates, commitment, declared
output, escrow inputs, and public nullifiers. -/
opaque WholeClaimOpensTo (claim : SettlementClaim)
  (batch : PrivateBatch claim.spec) : Prop

/-- What the external verifier must establish existentially.  The witness lives
in `Prop` and is erased; `SettlementClaim` remains plaintext-book free. -/
def ClaimHasValidPrivateOpening (claim : SettlementClaim) : Prop :=
  ∃ batch : PrivateBatch claim.spec,
    WholeClaimOpensTo claim batch ∧
    ExactClearingOutput batch claim.output ∧
    ExactPublicOrderNullifiers batch claim.orderNullifiers

/-- A single combined external capability indexed by the exact whole public
claim.  Its producer must verify authenticated ingress, commitment opening,
stable order-nullifier image, and threshold-clearing output as one statement.
This avoids asserting that two unrelated proof-indexed capabilities share an
existential witness through proof irrelevance. -/
opaque CombinedPrivateSettlementAuthorization (claim : SettlementClaim) : Type

/-- Kernel-visible package accepted from the combined verifier boundary.  Its
constructor is private: downstream code can consume an authorization and its
whole-claim validity certificate but cannot assemble unrelated pieces.  The
single opaque authorization is indexed by the exact claim, not by a proof in
`Prop`; `valid` is an ordinary field and therefore introduces no soundness axiom. -/
structure VerifiedSettlementEvidence (claim : SettlementClaim) : Type where
  private mk ::
  authorization : CombinedPrivateSettlementAuthorization claim
  valid : ClaimHasValidPrivateOpening claim

theorem VerifiedSettlementEvidence.has_valid_private_opening
    {claim : SettlementClaim} (evidence : VerifiedSettlementEvidence claim) :
    ClaimHasValidPrivateOpening claim :=
  evidence.valid

theorem VerifiedSettlementEvidence.orderNullifiers_exact
    {claim : SettlementClaim} (evidence : VerifiedSettlementEvidence claim) :
    ∃ batch : PrivateBatch claim.spec,
      claim.orderNullifiers = batch.orderNullifierImage ∧
      claim.orderNullifiers.card = batch.orders.length := by
  rcases evidence.valid with ⟨batch, _opening, _output, exactNullifiers⟩
  exact ⟨batch, exactNullifiers⟩

theorem VerifiedSettlementEvidence.privateOrderNullifier_injective
    {claim : SettlementClaim} (_evidence : VerifiedSettlementEvidence claim) :
    Function.Injective PrivateOrderId.nullifier :=
  PrivateOrderId.nullifier_injective

theorem VerifiedSettlementEvidence.orderNullifiers_card_le_maxOrders
    {claim : SettlementClaim} (evidence : VerifiedSettlementEvidence claim) :
    claim.orderNullifiers.card ≤ claim.spec.maxOrders := by
  rcases evidence.valid with ⟨batch, _opening, _output, exactNullifiers⟩
  rw [exactNullifiers.2]
  simpa only [List.length_map] using batch.orderCountBound

theorem VerifiedSettlementEvidence.bucket_lt
    {claim : SettlementClaim} (evidence : VerifiedSettlementEvidence claim) :
    claim.output.bucket < claim.spec.pricing.buckets := by
  rcases evidence.valid with ⟨batch, _opening, exactOutput, _nullifiers⟩
  rw [exactOutput.1]
  exact Market.crossing_lt batch.book claim.spec.pricing.buckets_pos

theorem VerifiedSettlementEvidence.volume_optimal
    {claim : SettlementClaim} (evidence : VerifiedSettlementEvidence claim)
    {bucket : Nat} (hbucket : bucket < claim.spec.pricing.buckets) :
    Market.execVol
      (Classical.choose evidence.valid).book bucket ≤ (claim.output.volume : Int) := by
  let batch := Classical.choose evidence.valid
  have hvalid := Classical.choose_spec evidence.valid
  rw [hvalid.2.1.2]
  exact Market.clearedVolume_optimal batch.book claim.spec.pricing.buckets hbucket

/-- A fixed private opening has one exact public output. -/
theorem clearingOutput_unique_for_opening {spec : BatchSpec} (batch : PrivateBatch spec)
    {left right : ClearingOutput}
    (hl : ExactClearingOutput batch left) (hr : ExactClearingOutput batch right) :
    left = right := by
  cases left with
  | mk leftBucket leftVolume =>
    cases right with
    | mk rightBucket rightVolume =>
      have hbucket : leftBucket = rightBucket := hl.1.trans hr.1.symm
      have hvolumeInt : (leftVolume : Int) = (rightVolume : Int) :=
        hl.2.trans hr.2.symm
      have hvolume : leftVolume = rightVolume := by exact_mod_cast hvolumeInt
      cases hbucket
      cases hvolume
      rfl

/-! ## Public escrow/custody state -/

/-- An intrinsically well-formed escrow ledger.  Every note is positive, owned
by the indexed participant, denominated in the indexed asset, and has a unique
nullifier within the ledger.  Scalar capacity is derived by summing these notes;
there is no separately mutable escrow balance to drift out of sync. -/
structure EscrowLedger (owner : ParticipantId) (asset : AssetRef) where
  notes : Finset AssetInput
  notesWellFormed : ∀ input ∈ notes,
    input.owner = owner ∧ input.asset = asset ∧ 0 < input.amount
  nullifiersInjective : Set.InjOn AssetInput.nullifier notes

def EscrowLedger.balance {owner : ParticipantId} {asset : AssetRef}
    (ledger : EscrowLedger owner asset) : Nat :=
  ledger.notes.sum AssetInput.amount

def EscrowLedger.remove {owner : ParticipantId} {asset : AssetRef}
    (ledger : EscrowLedger owner asset) (spent : Finset AssetInput) :
    EscrowLedger owner asset where
  notes := ledger.notes \ spent
  notesWellFormed := by
    intro input hinput
    exact ledger.notesWellFormed input (Finset.mem_sdiff.mp hinput).1
  nullifiersInjective := by
    intro left hleft right hright heq
    exact ledger.nullifiersInjective
      (Finset.mem_sdiff.mp hleft).1 (Finset.mem_sdiff.mp hright).1 heq

theorem EscrowLedger.balance_remove {owner : ParticipantId} {asset : AssetRef}
    (ledger : EscrowLedger owner asset) (spent : Finset AssetInput)
    (hsubset : spent ⊆ ledger.notes) :
    (ledger.remove spent).balance =
      ledger.balance - spent.sum AssetInput.amount := by
  have hsum := Finset.sum_sdiff (f := AssetInput.amount) hsubset
  simp only [EscrowLedger.balance, EscrowLedger.remove]
  exact Nat.eq_sub_of_add_eq hsum

/-- One market's public ledger projection.  `identity` and `policy` are the
state-authored authority.  The two escrow ledgers are intrinsically well formed;
the two custody fields are the counterparties' received scalar balances. -/
structure BazaarState where
  identity : StableMarketIdentity
  policy : MarketPolicy
  baseEscrow : EscrowLedger identity.seller identity.baseAsset
  quoteEscrow : EscrowLedger identity.buyer identity.quoteAsset
  escrowNullifiersDisjoint :
    Disjoint (baseEscrow.notes.image AssetInput.nullifier)
      (quoteEscrow.notes.image AssetInput.nullifier)
  buyerBaseCustody : Nat
  sellerQuoteCustody : Nat
  /-- These replay registries are scoped to this state value.  A deployment that
  permits multiple market states must lift them into a shared world ledger (or
  route every settlement through one `BazaarState`) before reading the replay
  theorems below as global guarantees. -/
  consumedAssetNullifiers : Finset AssetNullifier
  consumedOrderNullifiers : Finset OrderNullifier
  consumedBatches : Finset BatchKey

/-- Initialize a public market from authored identity/policy and already
well-formed escrow ledgers.  Capacity is their derived sum, never a caller-supplied
scalar. -/
def BazaarState.funded (spec : BatchSpec)
    (baseEscrow : EscrowLedger spec.seller spec.baseAsset)
    (quoteEscrow : EscrowLedger spec.buyer spec.quoteAsset)
    (nullifiersDisjoint :
      Disjoint (baseEscrow.notes.image AssetInput.nullifier)
        (quoteEscrow.notes.image AssetInput.nullifier)) : BazaarState where
  identity := spec.stableIdentity
  policy := spec.marketPolicy
  baseEscrow := baseEscrow
  quoteEscrow := quoteEscrow
  escrowNullifiersDisjoint := nullifiersDisjoint
  buyerBaseCustody := 0
  sellerQuoteCustody := 0
  consumedAssetNullifiers := ∅
  consumedOrderNullifiers := ∅
  consumedBatches := ∅

def BatchKey.WireBounded (key : BatchKey) : Prop :=
  key.contentEpoch.WireBounded ∧ key.batchId.value ≤ Wire.maxBatchId

instance BatchKey.instDecidableWireBounded (key : BatchKey) :
    Decidable key.WireBounded := by
  unfold BatchKey.WireBounded
  infer_instance

/-- All Nat-valued state which can cross the u64 wire is in range.  Escrow
balances are checked as derived note sums, not as independent scalars. -/
def BazaarState.WireBounded (state : BazaarState) : Prop :=
  state.identity.WireBounded ∧
    state.policy.WireBounded ∧
    state.baseEscrow.notes.filter AssetInput.WireBounded =
      state.baseEscrow.notes ∧
    state.quoteEscrow.notes.filter AssetInput.WireBounded =
      state.quoteEscrow.notes ∧
    state.baseEscrow.balance ≤ Wire.u64Max ∧
    state.quoteEscrow.balance ≤ Wire.u64Max ∧
    state.buyerBaseCustody ≤ Wire.maxCustodyBalance ∧
    state.sellerQuoteCustody ≤ Wire.maxCustodyBalance ∧
    state.consumedBatches.filter BatchKey.WireBounded = state.consumedBatches

instance BazaarState.instDecidableWireBounded (state : BazaarState) :
    Decidable state.WireBounded := by
  unfold BazaarState.WireBounded
  infer_instance

/-! ## Fail-closed public admission -/

/-- Every proposition checked before balances or nullifier sets move. -/
structure AdmissionWitness (claim : SettlementClaim) (state : BazaarState) : Prop where
  claimWireBounded : claim.WireBounded
  stateWireBounded : state.WireBounded
  buyerCustodyCreditFits :
    state.buyerBaseCustody + claim.baseAmount ≤ Wire.maxCustodyBalance
  sellerCustodyCreditFits :
    state.sellerQuoteCustody + claim.quoteAmount ≤ Wire.maxCustodyBalance
  batchFresh : claim.spec.key ∉ state.consumedBatches
  assetNullifiersFresh :
    ∀ nullifier ∈ claim.assetNullifiers,
      nullifier ∉ state.consumedAssetNullifiers
  orderNullifiersFresh :
    ∀ nullifier ∈ claim.orderNullifiers,
      nullifier ∉ state.consumedOrderNullifiers
  identityMatches : state.identity = claim.spec.stableIdentity
  policyMatches : state.policy = claim.spec.marketPolicy
  /-- Authorization is read from the state-held policy, not trusted from the
  claim until exact policy equality has also been checked. -/
  outputPredeclared : claim.output ∈ state.policy.allowedOutputs
  bucketInRange : claim.output.bucket < state.policy.pricing.buckets
  positiveVolume : 0 < claim.output.volume
  orderInputsNonempty : claim.orderNullifiers.Nonempty
  /-- Executable wire/DoS refinements.  The authored policy bounds all
  attacker-controlled public input collections before settlement. -/
  publicAssetInputsBounded :
    claim.allAssetInputs.card ≤ state.policy.maxPublicAssetInputs
  publicOrderNullifiersBounded :
    claim.orderNullifiers.card ≤ state.policy.maxOrders
  assetNullifiersExact :
    claim.allAssetInputs.card = claim.assetNullifiers.card
  baseInputsEscrowed : claim.baseInputs ⊆ state.baseEscrow.notes
  quoteInputsEscrowed : claim.quoteInputs ⊆ state.quoteEscrow.notes
  baseInputAmountExact :
    claim.baseInputs.sum AssetInput.amount = claim.baseAmount
  quoteInputAmountExact :
    claim.quoteInputs.sum AssetInput.amount = claim.quoteAmount
  baseBalanceCovers : claim.baseAmount ≤ state.baseEscrow.balance
  quoteBalanceCovers : claim.quoteAmount ≤ state.quoteEscrow.balance

/-- Fully executable Boolean mirror of `AdmissionWitness`.  Bounded universal
checks run over each finite input/nullifier list; no `Classical.dec` is used. -/
def admissionChecks (claim : SettlementClaim) (state : BazaarState) : Bool :=
  decide claim.WireBounded &&
  (decide state.WireBounded &&
  (decide (state.buyerBaseCustody + claim.baseAmount ≤ Wire.maxCustodyBalance) &&
  (decide (state.sellerQuoteCustody + claim.quoteAmount ≤ Wire.maxCustodyBalance) &&
  (decide (claim.spec.key ∉ state.consumedBatches) &&
  (decide (claim.assetNullifiers.filter
    (fun nullifier => nullifier ∉ state.consumedAssetNullifiers) =
      claim.assetNullifiers) &&
  (decide (claim.orderNullifiers.filter
    (fun nullifier => nullifier ∉ state.consumedOrderNullifiers) =
      claim.orderNullifiers) &&
  (decide (state.identity = claim.spec.stableIdentity) &&
  (decide (state.policy = claim.spec.marketPolicy) &&
  (decide (claim.output ∈ state.policy.allowedOutputs) &&
  (decide (claim.output.bucket < state.policy.pricing.buckets) &&
  (decide (0 < claim.output.volume) &&
  (decide claim.orderNullifiers.Nonempty &&
  (decide (claim.allAssetInputs.card ≤ state.policy.maxPublicAssetInputs) &&
  (decide (claim.orderNullifiers.card ≤ state.policy.maxOrders) &&
  (decide (claim.allAssetInputs.card = claim.assetNullifiers.card) &&
  (decide (claim.baseInputs ⊆ state.baseEscrow.notes) &&
  (decide (claim.quoteInputs ⊆ state.quoteEscrow.notes) &&
  (decide (claim.baseInputs.sum AssetInput.amount = claim.baseAmount) &&
  (decide (claim.quoteInputs.sum AssetInput.amount = claim.quoteAmount) &&
  (decide (claim.baseAmount ≤ state.baseEscrow.balance) &&
   decide (claim.quoteAmount ≤ state.quoteEscrow.balance)))))))))))))))))))))

theorem admissionChecks_eq_true_iff (claim : SettlementClaim) (state : BazaarState) :
    admissionChecks claim state = true ↔ AdmissionWitness claim state := by
  constructor
  · intro h
    simp only [admissionChecks, Bool.and_eq_true, decide_eq_true_eq,
      Finset.filter_eq_self] at h
    rcases h with
      ⟨hClaimWire, hStateWire, hBuyerCredit, hSellerCredit,
        hBatch, hAssets, hOrders, hIdentity, hPolicy,
        hOutput, hBucket, hVolume, hOrderNonempty, hAssetBound, hOrderBound,
        hNullifiers, hBaseEscrowed, hQuoteEscrowed,
        hBaseAmount, hQuoteAmount, hBaseCover, hQuoteCover⟩
    exact {
      claimWireBounded := hClaimWire
      stateWireBounded := hStateWire
      buyerCustodyCreditFits := hBuyerCredit
      sellerCustodyCreditFits := hSellerCredit
      batchFresh := hBatch
      assetNullifiersFresh := hAssets
      orderNullifiersFresh := hOrders
      identityMatches := hIdentity
      policyMatches := hPolicy
      outputPredeclared := hOutput
      bucketInRange := hBucket
      positiveVolume := hVolume
      orderInputsNonempty := hOrderNonempty
      publicAssetInputsBounded := hAssetBound
      publicOrderNullifiersBounded := hOrderBound
      assetNullifiersExact := hNullifiers
      baseInputsEscrowed := hBaseEscrowed
      quoteInputsEscrowed := hQuoteEscrowed
      baseInputAmountExact := hBaseAmount
      quoteInputAmountExact := hQuoteAmount
      baseBalanceCovers := hBaseCover
      quoteBalanceCovers := hQuoteCover
    }
  · intro h
    simp only [admissionChecks, Bool.and_eq_true, decide_eq_true_eq,
      Finset.filter_eq_self]
    exact ⟨h.claimWireBounded, h.stateWireBounded,
      h.buyerCustodyCreditFits, h.sellerCustodyCreditFits,
      h.batchFresh, h.assetNullifiersFresh, h.orderNullifiersFresh,
      h.identityMatches, h.policyMatches, h.outputPredeclared,
      h.bucketInRange, h.positiveVolume, h.orderInputsNonempty,
      h.publicAssetInputsBounded, h.publicOrderNullifiersBounded,
      h.assetNullifiersExact, h.baseInputsEscrowed, h.quoteInputsEscrowed,
      h.baseInputAmountExact,
      h.quoteInputAmountExact, h.baseBalanceCovers, h.quoteBalanceCovers⟩

theorem admissionWitness_of_checks {claim : SettlementClaim} {state : BazaarState}
    (h : admissionChecks claim state = true) : AdmissionWitness claim state :=
  (admissionChecks_eq_true_iff claim state).mp h

/-! ## Actual settlement -/

/-- The sole public transition.  Its claim and state have no private book.  The
evidence parameter is proof-only and the function never projects its existential
witness. -/
def applySettlement (claim : SettlementClaim)
    (_evidence : VerifiedSettlementEvidence claim)
    (state : BazaarState) : Option BazaarState :=
  if admissionChecks claim state = true then
    some {
      identity := state.identity
      policy := state.policy
      baseEscrow := state.baseEscrow.remove claim.baseInputs
      quoteEscrow := state.quoteEscrow.remove claim.quoteInputs
      escrowNullifiersDisjoint := by
        rw [Finset.disjoint_left]
        intro nullifier hbase hquote
        rcases Finset.mem_image.mp hbase with ⟨baseInput, hbaseRemaining, hbaseEq⟩
        rcases Finset.mem_image.mp hquote with
          ⟨quoteInput, hquoteRemaining, hquoteEq⟩
        have hbaseOld : nullifier ∈
            state.baseEscrow.notes.image AssetInput.nullifier :=
          Finset.mem_image.mpr
            ⟨baseInput, (Finset.mem_sdiff.mp hbaseRemaining).1, hbaseEq⟩
        have hquoteOld : nullifier ∈
            state.quoteEscrow.notes.image AssetInput.nullifier :=
          Finset.mem_image.mpr
            ⟨quoteInput, (Finset.mem_sdiff.mp hquoteRemaining).1, hquoteEq⟩
        exact (Finset.disjoint_left.mp state.escrowNullifiersDisjoint)
          hbaseOld hquoteOld
      buyerBaseCustody := state.buyerBaseCustody + claim.baseAmount
      sellerQuoteCustody := state.sellerQuoteCustody + claim.quoteAmount
      consumedAssetNullifiers :=
        state.consumedAssetNullifiers ∪ claim.assetNullifiers
      consumedOrderNullifiers :=
        state.consumedOrderNullifiers ∪ claim.orderNullifiers
      consumedBatches := insert claim.spec.key state.consumedBatches
    }
  else none

theorem applySettlement_not_admissible {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) (state : BazaarState)
    (h : ¬ AdmissionWitness claim state) :
    applySettlement claim evidence state = none := by
  unfold applySettlement
  split
  · rename_i hchecks
    exact False.elim (h ((admissionChecks_eq_true_iff claim state).mp hchecks))
  · rfl

theorem admissionWitness_of_success {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) {before after : BazaarState}
    (h : applySettlement claim evidence before = some after) :
    AdmissionWitness claim before := by
  unfold applySettlement at h
  split at h
  · rename_i hchecks
    exact admissionWitness_of_checks hchecks
  · contradiction

/-- Successful admission binds every stable identity field and the complete
pricing/order/output/wire policy to the state-authored values. -/
theorem applySettlement_binds_state_authored_market {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) {before after : BazaarState}
    (h : applySettlement claim evidence before = some after) :
    before.identity = claim.spec.stableIdentity ∧
      before.policy = claim.spec.marketPolicy := by
  have witness := admissionWitness_of_success evidence h
  exact ⟨witness.identityMatches, witness.policyMatches⟩

/-- The explicit state-level view of the intrinsic escrow invariant. -/
def EscrowWellFormed (state : BazaarState) : Prop :=
  (∀ input ∈ state.baseEscrow.notes,
    input.owner = state.identity.seller ∧
      input.asset = state.identity.baseAsset ∧ 0 < input.amount) ∧
  Set.InjOn AssetInput.nullifier state.baseEscrow.notes ∧
  (∀ input ∈ state.quoteEscrow.notes,
    input.owner = state.identity.buyer ∧
      input.asset = state.identity.quoteAsset ∧ 0 < input.amount) ∧
  Set.InjOn AssetInput.nullifier state.quoteEscrow.notes ∧
  Disjoint (state.baseEscrow.notes.image AssetInput.nullifier)
    (state.quoteEscrow.notes.image AssetInput.nullifier)

theorem BazaarState.escrowWellFormed (state : BazaarState) :
    EscrowWellFormed state := by
  exact ⟨state.baseEscrow.notesWellFormed,
    state.baseEscrow.nullifiersInjective,
    state.quoteEscrow.notesWellFormed,
    state.quoteEscrow.nullifiersInjective,
    state.escrowNullifiersDisjoint⟩

/-- Removing exact notes preserves ownership, asset typing, positivity, and
nullifier injectivity.  Scalar escrow balances remain derived from those notes. -/
theorem applySettlement_preserves_escrow_wellformed {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) {before after : BazaarState}
    (_h : applySettlement claim evidence before = some after) :
    EscrowWellFormed after :=
  after.escrowWellFormed

theorem applySettlement_deterministic {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) (before after₁ after₂ : BazaarState)
    (h₁ : applySettlement claim evidence before = some after₁)
    (h₂ : applySettlement claim evidence before = some after₂) : after₁ = after₂ := by
  rw [h₁] at h₂
  exact Option.some.inj h₂

theorem applySettlement_balances_exact {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) {before after : BazaarState}
    (h : applySettlement claim evidence before = some after) :
    after.baseEscrow.balance = before.baseEscrow.balance - claim.baseAmount ∧
    after.quoteEscrow.balance = before.quoteEscrow.balance - claim.quoteAmount ∧
    after.buyerBaseCustody = before.buyerBaseCustody + claim.baseAmount ∧
    after.sellerQuoteCustody = before.sellerQuoteCustody + claim.quoteAmount := by
  have witness := admissionWitness_of_success evidence h
  unfold applySettlement at h
  split at h
  · simp only [Option.some.injEq] at h
    subst after
    exact ⟨
      (before.baseEscrow.balance_remove claim.baseInputs
        witness.baseInputsEscrowed).trans
          (congrArg (before.baseEscrow.balance - ·)
            witness.baseInputAmountExact),
      (before.quoteEscrow.balance_remove claim.quoteInputs
        witness.quoteInputsEscrowed).trans
          (congrArg (before.quoteEscrow.balance - ·)
            witness.quoteInputAmountExact),
      rfl, rfl⟩
  · contradiction

/-- The checked positive quote and its multiplication fit the selected u64 wire
integer on every successful settlement. -/
theorem applySettlement_quote_product_fits_u64 {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) {before after : BazaarState}
    (h : applySettlement claim evidence before = some after) :
    claim.quotePrice ≤ Wire.u64Max ∧ claim.quoteAmount ≤ Wire.u64Max := by
  have witness := admissionWitness_of_success evidence h
  exact ⟨claim.quotePrice_fits_u64 witness.claimWireBounded,
    claim.quoteAmount_fits_u64 witness.claimWireBounded⟩

/-- Range safety is inductive: removing bounded notes cannot enlarge a derived
escrow sum; checked custody credits fit; and the inserted batch key was already
u64-bounded in the checked claim. -/
theorem applySettlement_preserves_wire_bounded {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) {before after : BazaarState}
    (h : applySettlement claim evidence before = some after) :
    after.WireBounded := by
  have witness := admissionWitness_of_success evidence h
  rcases witness.stateWireBounded with
    ⟨hIdentity, hPolicy, hBaseNotes, hQuoteNotes, hBaseBalance, hQuoteBalance,
      _hBuyerBefore, _hSellerBefore, hBatches⟩
  unfold applySettlement at h
  split at h
  · simp only [Option.some.injEq] at h
    subst after
    refine ⟨hIdentity, hPolicy, ?_, ?_, ?_, ?_, witness.buyerCustodyCreditFits,
      witness.sellerCustodyCreditFits, ?_⟩
    · apply Finset.filter_eq_self.mpr
      intro input hinput
      exact Finset.filter_eq_self.mp hBaseNotes input
        (Finset.mem_sdiff.mp hinput).1
    · apply Finset.filter_eq_self.mpr
      intro input hinput
      exact Finset.filter_eq_self.mp hQuoteNotes input
        (Finset.mem_sdiff.mp hinput).1
    · have hremove := before.baseEscrow.balance_remove claim.baseInputs
        witness.baseInputsEscrowed
      have hnonincrease :
          (before.baseEscrow.remove claim.baseInputs).balance ≤
            before.baseEscrow.balance := by
        rw [hremove]
        exact Nat.sub_le _ _
      exact hnonincrease.trans hBaseBalance
    · have hremove := before.quoteEscrow.balance_remove claim.quoteInputs
        witness.quoteInputsEscrowed
      have hnonincrease :
          (before.quoteEscrow.remove claim.quoteInputs).balance ≤
            before.quoteEscrow.balance := by
        rw [hremove]
        exact Nat.sub_le _ _
      exact hnonincrease.trans hQuoteBalance
    · apply Finset.filter_eq_self.mpr
      intro key hkey
      rcases Finset.mem_insert.mp hkey with hnew | hold
      · subst key
        exact ⟨witness.claimWireBounded.1.1.1,
          witness.claimWireBounded.1.2.1⟩
      · exact Finset.filter_eq_self.mp hBatches key hold
  · contradiction

theorem applySettlement_successor_identity_wire_bounded
    {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) {before after : BazaarState}
    (h : applySettlement claim evidence before = some after) :
    after.identity.WireBounded :=
  (applySettlement_preserves_wire_bounded evidence h).1

/-- Conservation follows from the actual debit/credit updates and sufficient
held balances; it is not true by the definition of a separate flow object. -/
theorem applySettlement_conserves_held_assets {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) {before after : BazaarState}
    (h : applySettlement claim evidence before = some after) :
    after.baseEscrow.balance + after.buyerBaseCustody =
        before.baseEscrow.balance + before.buyerBaseCustody ∧
    after.quoteEscrow.balance + after.sellerQuoteCustody =
        before.quoteEscrow.balance + before.sellerQuoteCustody := by
  have witness := admissionWitness_of_success evidence h
  have hBaseCover := witness.baseBalanceCovers
  have hQuoteCover := witness.quoteBalanceCovers
  rcases applySettlement_balances_exact evidence h with
    ⟨hBaseEscrow, hQuoteEscrow, hBaseCustody, hQuoteCustody⟩
  constructor
  · omega
  · omega

/-- Successful capacity is derived only from balances actually held in escrow. -/
theorem applySettlement_capacity_from_held_balances {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) {before after : BazaarState}
    (h : applySettlement claim evidence before = some after) :
    claim.baseAmount ≤ before.baseEscrow.balance ∧
      claim.quoteAmount ≤ before.quoteEscrow.balance := by
  have witness := admissionWitness_of_success evidence h
  exact ⟨witness.baseBalanceCovers, witness.quoteBalanceCovers⟩

/-- Every debited input was already in escrow and names the authored owner and
asset.  The market cannot debit a merely claimed or differently owned note. -/
theorem applySettlement_only_owned_escrowed_inputs {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) {before after : BazaarState}
    (h : applySettlement claim evidence before = some after) :
    claim.baseInputs ⊆ before.baseEscrow.notes ∧
    claim.quoteInputs ⊆ before.quoteEscrow.notes ∧
    (∀ input ∈ claim.baseInputs,
      input.owner = claim.spec.seller ∧
      input.asset = claim.spec.baseAsset ∧ 0 < input.amount) ∧
    (∀ input ∈ claim.quoteInputs,
      input.owner = claim.spec.buyer ∧
      input.asset = claim.spec.quoteAsset ∧ 0 < input.amount) := by
  have witness := admissionWitness_of_success evidence h
  have baseOwned : ∀ input ∈ claim.baseInputs,
      input.owner = claim.spec.seller ∧
      input.asset = claim.spec.baseAsset ∧ 0 < input.amount := by
    intro input hinput
    have hwell := before.baseEscrow.notesWellFormed input
      (witness.baseInputsEscrowed hinput)
    rw [witness.identityMatches] at hwell
    exact hwell
  have quoteOwned : ∀ input ∈ claim.quoteInputs,
      input.owner = claim.spec.buyer ∧
      input.asset = claim.spec.quoteAsset ∧ 0 < input.amount := by
    intro input hinput
    have hwell := before.quoteEscrow.notesWellFormed input
      (witness.quoteInputsEscrowed hinput)
    rw [witness.identityMatches] at hwell
    exact hwell
  exact ⟨witness.baseInputsEscrowed, witness.quoteInputsEscrowed,
    baseOwned, quoteOwned⟩

/-- The exact owned input sums equal the exact balance debits. -/
theorem applySettlement_debits_exact_input_amounts {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) {before after : BazaarState}
    (h : applySettlement claim evidence before = some after) :
    claim.baseInputs.sum AssetInput.amount = claim.output.volume ∧
    claim.quoteInputs.sum AssetInput.amount =
      claim.spec.pricing.quoteAt claim.output.bucket * claim.output.volume := by
  have witness := admissionWitness_of_success evidence h
  exact ⟨witness.baseInputAmountExact, witness.quoteInputAmountExact⟩

theorem applySettlement_removes_exact_asset_inputs {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) {before after : BazaarState}
    (h : applySettlement claim evidence before = some after) :
    (∀ input ∈ claim.baseInputs, input ∉ after.baseEscrow.notes) ∧
    (∀ input ∈ claim.quoteInputs, input ∉ after.quoteEscrow.notes) := by
  unfold applySettlement at h
  split at h
  · simp only [Option.some.injEq] at h
    subst after
    constructor
    · intro input hinput hremaining
      exact (Finset.mem_sdiff.mp hremaining).2 hinput
    · intro input hinput hremaining
      exact (Finset.mem_sdiff.mp hremaining).2 hinput
  · contradiction

theorem applySettlement_consumes_asset_nullifiers {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) {before after : BazaarState}
    (h : applySettlement claim evidence before = some after) :
    claim.assetNullifiers ⊆ after.consumedAssetNullifiers := by
  unfold applySettlement at h
  split at h
  · simp only [Option.some.injEq] at h
    subst after
    simp
  · contradiction

theorem applySettlement_consumes_order_nullifiers {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) {before after : BazaarState}
    (h : applySettlement claim evidence before = some after) :
    claim.orderNullifiers ⊆ after.consumedOrderNullifiers := by
  unfold applySettlement at h
  split at h
  · simp only [Option.some.injEq] at h
    subst after
    simp
  · contradiction

theorem applySettlement_marks_batch_consumed {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) {before after : BazaarState}
    (h : applySettlement claim evidence before = some after) :
    claim.spec.key ∈ after.consumedBatches := by
  unfold applySettlement at h
  split at h
  · simp only [Option.some.injEq] at h
    subst after
    simp
  · contradiction

theorem applySettlement_replay_refused {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) (state : BazaarState)
    (h : claim.spec.key ∈ state.consumedBatches) :
    applySettlement claim evidence state = none := by
  apply applySettlement_not_admissible
  intro witness
  exact witness.batchFresh h

/-- Within one threaded/shared `BazaarState`, changing batch id or source root
does not revive an asset input.  This is not a theorem about two independent
state values; deployments needing global replay protection must share the
nullifier registry at world-state scope. -/
theorem applySettlement_rebatched_asset_in_shared_state_refused
    {first second : SettlementClaim}
    (firstEvidence : VerifiedSettlementEvidence first)
    (secondEvidence : VerifiedSettlementEvidence second)
    {before after : BazaarState}
    (hfirst : applySettlement first firstEvidence before = some after)
    (hreuse : ∃ nullifier,
      nullifier ∈ first.assetNullifiers ∧
      nullifier ∈ second.assetNullifiers) :
    applySettlement second secondEvidence after = none := by
  rcases hreuse with ⟨nullifier, hfirstNullifier, hsecondNullifier⟩
  have hconsumed : nullifier ∈ after.consumedAssetNullifiers :=
    applySettlement_consumes_asset_nullifiers firstEvidence hfirst hfirstNullifier
  apply applySettlement_not_admissible
  intro witness
  exact witness.assetNullifiersFresh nullifier hsecondNullifier hconsumed

/-- The corresponding shared-state result for a stable private-order
nullifier.  Its scope is deliberately explicit in the theorem name. -/
theorem applySettlement_rebatched_order_in_shared_state_refused
    {first second : SettlementClaim}
    (firstEvidence : VerifiedSettlementEvidence first)
    (secondEvidence : VerifiedSettlementEvidence second)
    {before after : BazaarState}
    (hfirst : applySettlement first firstEvidence before = some after)
    (hreuse : ∃ nullifier,
      nullifier ∈ first.orderNullifiers ∧
      nullifier ∈ second.orderNullifiers) :
    applySettlement second secondEvidence after = none := by
  rcases hreuse with ⟨nullifier, hfirstNullifier, hsecondNullifier⟩
  have hconsumed : nullifier ∈ after.consumedOrderNullifiers :=
    applySettlement_consumes_order_nullifiers firstEvidence hfirst hfirstNullifier
  apply applySettlement_not_admissible
  intro witness
  exact witness.orderNullifiersFresh nullifier hsecondNullifier hconsumed

theorem applySettlement_wrong_federation_refused {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) (state : BazaarState)
    (h : state.identity.federationId ≠ claim.spec.federationId) :
    applySettlement claim evidence state = none := by
  apply applySettlement_not_admissible
  intro witness
  apply h
  exact congrArg StableMarketIdentity.federationId witness.identityMatches

theorem applySettlement_wrong_activation_refused {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) (state : BazaarState)
    (h : state.identity.activationDigest ≠ claim.spec.activationDigest) :
    applySettlement claim evidence state = none := by
  apply applySettlement_not_admissible
  intro witness
  apply h
  exact congrArg StableMarketIdentity.activationDigest witness.identityMatches

theorem applySettlement_wrong_asset_refused {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) (state : BazaarState)
    (h : state.identity.baseAsset ≠ claim.spec.baseAsset) :
    applySettlement claim evidence state = none := by
  apply applySettlement_not_admissible
  intro witness
  apply h
  exact congrArg StableMarketIdentity.baseAsset witness.identityMatches

theorem applySettlement_wrong_policy_refused {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) (state : BazaarState)
    (h : state.policy ≠ claim.spec.marketPolicy) :
    applySettlement claim evidence state = none := by
  apply applySettlement_not_admissible
  intro witness
  exact h witness.policyMatches

theorem applySettlement_unbounded_claim_wire_refused {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) (state : BazaarState)
    (h : ¬ claim.WireBounded) :
    applySettlement claim evidence state = none := by
  apply applySettlement_not_admissible
  intro witness
  exact h witness.claimWireBounded

theorem applySettlement_unbounded_state_wire_refused {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) (state : BazaarState)
    (h : ¬ state.WireBounded) :
    applySettlement claim evidence state = none := by
  apply applySettlement_not_admissible
  intro witness
  exact h witness.stateWireBounded

theorem applySettlement_buyer_custody_overflow_refused {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) (state : BazaarState)
    (h : Wire.maxCustodyBalance <
      state.buyerBaseCustody + claim.baseAmount) :
    applySettlement claim evidence state = none := by
  apply applySettlement_not_admissible
  intro witness
  exact (Nat.not_le.mpr h) witness.buyerCustodyCreditFits

theorem applySettlement_seller_custody_overflow_refused {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) (state : BazaarState)
    (h : Wire.maxCustodyBalance <
      state.sellerQuoteCustody + claim.quoteAmount) :
    applySettlement claim evidence state = none := by
  apply applySettlement_not_admissible
  intro witness
  exact (Nat.not_le.mpr h) witness.sellerCustodyCreditFits

theorem applySettlement_unpredeclared_output_refused {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) (state : BazaarState)
    (h : claim.output ∉ state.policy.allowedOutputs) :
    applySettlement claim evidence state = none := by
  apply applySettlement_not_admissible
  intro witness
  exact h witness.outputPredeclared

theorem applySettlement_zero_volume_refused {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) (state : BazaarState)
    (h : claim.output.volume = 0) :
    applySettlement claim evidence state = none := by
  apply applySettlement_not_admissible
  intro witness
  exact (Nat.ne_of_gt witness.positiveVolume) h

theorem applySettlement_underfunded_base_refused {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) (state : BazaarState)
    (h : state.baseEscrow.balance < claim.baseAmount) :
    applySettlement claim evidence state = none := by
  apply applySettlement_not_admissible
  intro witness
  exact (Nat.not_le.mpr h) witness.baseBalanceCovers

theorem applySettlement_underfunded_quote_refused {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) (state : BazaarState)
    (h : state.quoteEscrow.balance < claim.quoteAmount) :
    applySettlement claim evidence state = none := by
  apply applySettlement_not_admissible
  intro witness
  exact (Nat.not_le.mpr h) witness.quoteBalanceCovers

theorem applySettlement_oversize_asset_wire_refused {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) (state : BazaarState)
    (h : state.policy.maxPublicAssetInputs < claim.allAssetInputs.card) :
    applySettlement claim evidence state = none := by
  apply applySettlement_not_admissible
  intro witness
  exact (Nat.not_le.mpr h) witness.publicAssetInputsBounded

theorem applySettlement_oversize_order_wire_refused {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) (state : BazaarState)
    (h : state.policy.maxOrders < claim.orderNullifiers.card) :
    applySettlement claim evidence state = none := by
  apply applySettlement_not_admissible
  intro witness
  exact (Nat.not_le.mpr h) witness.publicOrderNullifiersBounded

/-! ## Honest public observation -/

/-- Everything the public transition reveals.  The complete proposed spec is
included, including content/activation digests and every policy bound; admission
separately proves that it exactly matches state-authored identity and policy.
Exact escrow inputs and nullifiers are public because admission consumes them;
private orders, fills, shares, proof witnesses, and transcripts are absent. -/
structure PublicView where
  spec : BatchSpec
  privateBookCommitment : Digest32
  output : ClearingOutput
  baseInputs : Finset AssetInput
  quoteInputs : Finset AssetInput
  orderNullifiers : Finset OrderNullifier

def publicView (claim : SettlementClaim) : PublicView where
  spec := claim.spec
  privateBookCommitment := claim.privateBookCommitment
  output := claim.output
  baseInputs := claim.baseInputs
  quoteInputs := claim.quoteInputs
  orderNullifiers := claim.orderNullifiers

/-- Witness-free simulation from the public claim alone. -/
def publicSim (claim : SettlementClaim) : PublicView where
  spec := claim.spec
  privateBookCommitment := claim.privateBookCommitment
  output := claim.output
  baseInputs := claim.baseInputs
  quoteInputs := claim.quoteInputs
  orderNullifiers := claim.orderNullifiers

/-- Conditional evidence-erasure only: this theorem does not establish that the
cryptographic transcript leaks no more than the public claim. -/
theorem public_view_simulated_from_claim (claim : SettlementClaim) :
    publicView claim = publicSim claim := rfl

structure ObservableState where
  identity : StableMarketIdentity
  policy : MarketPolicy
  baseEscrow : Nat
  quoteEscrow : Nat
  buyerBaseCustody : Nat
  sellerQuoteCustody : Nat
  baseEscrowNotes : Finset AssetInput
  quoteEscrowNotes : Finset AssetInput
  consumedAssetNullifiers : Finset AssetNullifier
  consumedOrderNullifiers : Finset OrderNullifier
  consumedBatches : Finset BatchKey
deriving DecidableEq

def observeState (state : BazaarState) : ObservableState where
  identity := state.identity
  policy := state.policy
  baseEscrow := state.baseEscrow.balance
  quoteEscrow := state.quoteEscrow.balance
  buyerBaseCustody := state.buyerBaseCustody
  sellerQuoteCustody := state.sellerQuoteCustody
  baseEscrowNotes := state.baseEscrow.notes
  quoteEscrowNotes := state.quoteEscrow.notes
  consumedAssetNullifiers := state.consumedAssetNullifiers
  consumedOrderNullifiers := state.consumedOrderNullifiers
  consumedBatches := state.consumedBatches

def simulateObservableAfter (claim : SettlementClaim)
    (before : BazaarState) : ObservableState where
  identity := before.identity
  policy := before.policy
  baseEscrow := before.baseEscrow.balance - claim.baseAmount
  quoteEscrow := before.quoteEscrow.balance - claim.quoteAmount
  buyerBaseCustody := before.buyerBaseCustody + claim.baseAmount
  sellerQuoteCustody := before.sellerQuoteCustody + claim.quoteAmount
  baseEscrowNotes := before.baseEscrow.notes \ claim.baseInputs
  quoteEscrowNotes := before.quoteEscrow.notes \ claim.quoteInputs
  consumedAssetNullifiers :=
    before.consumedAssetNullifiers ∪ claim.assetNullifiers
  consumedOrderNullifiers :=
    before.consumedOrderNullifiers ∪ claim.orderNullifiers
  consumedBatches := insert claim.spec.key before.consumedBatches

/-- Conditional transition privacy: once external verification succeeds, the
public successor is determined from the public claim and prior public state, not
from the existential book or either opaque capability. -/
theorem successful_transition_evidence_erased {claim : SettlementClaim}
    (evidence : VerifiedSettlementEvidence claim) {before after : BazaarState}
    (h : applySettlement claim evidence before = some after) :
    observeState after = simulateObservableAfter claim before := by
  unfold applySettlement at h
  split at h
  · simp only [Option.some.injEq] at h
    subst after
    have witness := admissionWitness_of_checks ‹admissionChecks claim before = true›
    have hbase := (before.baseEscrow.balance_remove claim.baseInputs
      witness.baseInputsEscrowed).trans
        (congrArg (before.baseEscrow.balance - ·)
          witness.baseInputAmountExact)
    have hquote := (before.quoteEscrow.balance_remove claim.quoteInputs
      witness.quoteInputsEscrowed).trans
        (congrArg (before.quoteEscrow.balance - ·)
          witness.quoteInputAmountExact)
    rw [observeState, simulateObservableAfter, hbase, hquote]
    simp only [EscrowLedger.remove]
  · contradiction

/-- Two verifier evidence values for the same public claim cannot change the
public transition.  This is conditional noninterference, not a claim that either
verifier protocol securely constructs those values. -/
theorem same_claim_evidence_observationally_equivalent
    {claim : SettlementClaim}
    (leftEvidence rightEvidence : VerifiedSettlementEvidence claim)
    {before afterLeft afterRight : BazaarState}
    (hleft : applySettlement claim leftEvidence before = some afterLeft)
    (hright : applySettlement claim rightEvidence before = some afterRight) :
    observeState afterLeft = observeState afterRight := by
  rw [successful_transition_evidence_erased leftEvidence hleft,
    successful_transition_evidence_erased rightEvidence hright]

/-! ## Axiom visibility for every semantic/security theorem -/

#assert_axioms PriceSchedule.quoteAt_pos
#assert_axioms SettlementClaim.quotePrice_pos
#assert_axioms SettlementClaim.quoteAmount_eq_authored_tick
#assert_axioms SettlementClaim.quotePrice_fits_u64
#assert_axioms SettlementClaim.quoteAmount_fits_u64
#assert_axioms RawSettlementClaim.wireChecks_positive
#assert_axioms RawSettlementClaim.decode_allocation_refused
#assert_axioms RawSettlementClaim.decode_wire_refused
#assert_axioms RawSettlementClaim.decode_identity_wire_refused
#assert_axioms RawSettlementClaim.decode_success_implies_guards
#assert_axioms RawSettlementClaim.decode_ofClaim
#assert_axioms PrivateOrderId.nullifier_injective
#assert_axioms VerifiedSettlementEvidence.has_valid_private_opening
#assert_axioms VerifiedSettlementEvidence.orderNullifiers_exact
#assert_axioms VerifiedSettlementEvidence.privateOrderNullifier_injective
#assert_axioms VerifiedSettlementEvidence.orderNullifiers_card_le_maxOrders
#assert_axioms VerifiedSettlementEvidence.bucket_lt
#assert_axioms VerifiedSettlementEvidence.volume_optimal
#assert_axioms clearingOutput_unique_for_opening
#assert_axioms EscrowLedger.balance_remove
#assert_axioms admissionChecks_eq_true_iff
#assert_axioms admissionWitness_of_checks
#assert_axioms applySettlement_not_admissible
#assert_axioms admissionWitness_of_success
#assert_axioms applySettlement_binds_state_authored_market
#assert_axioms BazaarState.escrowWellFormed
#assert_axioms applySettlement_preserves_escrow_wellformed
#assert_axioms applySettlement_deterministic
#assert_axioms applySettlement_balances_exact
#assert_axioms applySettlement_quote_product_fits_u64
#assert_axioms applySettlement_preserves_wire_bounded
#assert_axioms applySettlement_successor_identity_wire_bounded
#assert_axioms applySettlement_conserves_held_assets
#assert_axioms applySettlement_capacity_from_held_balances
#assert_axioms applySettlement_only_owned_escrowed_inputs
#assert_axioms applySettlement_debits_exact_input_amounts
#assert_axioms applySettlement_removes_exact_asset_inputs
#assert_axioms applySettlement_consumes_asset_nullifiers
#assert_axioms applySettlement_consumes_order_nullifiers
#assert_axioms applySettlement_marks_batch_consumed
#assert_axioms applySettlement_replay_refused
#assert_axioms applySettlement_rebatched_asset_in_shared_state_refused
#assert_axioms applySettlement_rebatched_order_in_shared_state_refused
#assert_axioms applySettlement_wrong_federation_refused
#assert_axioms applySettlement_wrong_activation_refused
#assert_axioms applySettlement_wrong_asset_refused
#assert_axioms applySettlement_wrong_policy_refused
#assert_axioms applySettlement_unbounded_claim_wire_refused
#assert_axioms applySettlement_unbounded_state_wire_refused
#assert_axioms applySettlement_buyer_custody_overflow_refused
#assert_axioms applySettlement_seller_custody_overflow_refused
#assert_axioms applySettlement_unpredeclared_output_refused
#assert_axioms applySettlement_zero_volume_refused
#assert_axioms applySettlement_underfunded_base_refused
#assert_axioms applySettlement_underfunded_quote_refused
#assert_axioms applySettlement_oversize_asset_wire_refused
#assert_axioms applySettlement_oversize_order_wire_refused
#assert_axioms public_view_simulated_from_claim
#assert_axioms successful_transition_evidence_erased
#assert_axioms same_claim_evidence_observationally_equivalent

end Dregg2.Games.PathOfAngels.DarkBazaar
