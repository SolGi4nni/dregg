/-
# Path of Angels — strict Dark Bazaar v1 network wire

This is a canonical, proof-erased JSON boundary for one bounded private market
family.  Accepted input bytes reproduce Lean's compact encoder exactly: unknown
fields, whitespace, key reordering, alternate numbers, uppercase digests,
trailing bytes, noncanonical collection order, and every over-bound shape
refuse.  Semantic reconstruction then rebuilds the proof-carrying PoA claim and
escrow state; the Rust host never constructs either.

V1 is deliberately frozen at four private orders/four price buckets.  A larger
family is a new format, not a widened interpretation of these bytes.

This first wire carries the opening to the Lean judge.  It proves that the
public transition is exactly the one induced by those orders, but it does not
hide them from the judge process or the transport.  A house-blind DrEX wire
must carry a proof of the same statement in a separately versioned format.
-/
import Lean.Data.Json
import Mathlib.Data.List.Sort
import Dregg2.Games.PathOfAngels.DarkBazaar
import Dregg2.Games.PathOfAngels.Emit
import Dregg2.Circuit.CommitmentTreeWide
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.DarkBazaarJudgeWire

open Lean
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.DarkBazaar

set_option autoImplicit false

abbrev INPUT_FORMAT : String := "POA-DARK-BAZAAR-IN-1"
abbrev OUTPUT_FORMAT : String := "POA-DARK-BAZAAR-OUT-1"
abbrev AUTHORIZATION_FORMAT : String := "DREGG-DARK-BAZAAR-N4-K4-POSEIDON2-V1"

abbrev WIRE_BYTE_LIMIT : Nat := 4 * 1024 * 1024
abbrev MAX_ALLOWED_OUTPUTS : Nat := 64
abbrev MAX_ESCROW_NOTES : Nat := 4096
abbrev MAX_CONSUMED_NULLIFIERS : Nat := 16384
abbrev MAX_CONSUMED_BATCHES : Nat := 4096
abbrev MAX_CLAIM_INPUTS : Nat := 8

private def jsonString (s : String) : String := String.quote s
private def jsonArray (xs : List String) : String :=
  "[" ++ String.intercalate "," xs ++ "]"

private def exactKeys (j : Json) (allowed : List String) : Except String Unit := do
  let object ← j.getObj?
  if object.size == allowed.length && allowed.all object.contains then pure ()
  else throw "missing or unknown field"

private def boundedNat (limit value : Nat) : Except String Nat :=
  if value ≤ limit then pure value else throw "integer exceeds wire bound"

private def objectNat (j : Json) (key : String)
    (limit : Nat := DarkBazaar.Wire.u64Max) : Except String Nat := do
  boundedNat limit (← j.getObjValAs? Nat key)

private def objectDigest (j : Json) (key : String) : Except String Digest32 := do
  let spelling ← j.getObjValAs? String key
  match Emit.parseBytes32Hex? spelling with
  | some digest => pure digest
  | none => throw "digest must be exactly 64 lowercase hexadecimal digits"

private def canonicalB {T : Type} (encode : T → String) (limit : Nat)
    (values : List T) : Bool :=
  decide (values.length ≤ limit) &&
    decide (values.Pairwise fun left right => encode left < encode right)

private def parseCanonicalArray {T : Type} (j : Json) (limit : Nat)
    (parse : Json → Except String T) (encode : T → String) : Except String (List T) := do
  let values := (← j.getArr?).toList
  if values.length > limit then throw "list exceeds wire bound"
  let parsed ← values.mapM parse
  if canonicalB encode limit parsed then pure parsed else throw "list is not canonical"

/-! ## Proof-erased wire values -/

structure AssetRefWire where
  kind : String
  relicId : Nat
deriving DecidableEq, Repr

structure IdentityWire where
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : Nat
  seller : Digest32
  buyer : Digest32
  baseAsset : AssetRefWire
  quoteAsset : AssetRefWire
deriving DecidableEq

structure ClearingOutputWire where
  bucket : Nat
  volume : Nat
deriving DecidableEq, Repr

structure PolicyWire where
  buckets : Nat
  quoteTick : Nat
  maxOrders : Nat
  maxOrderQuantity : Nat
  maxPublicAssetInputs : Nat
  allowedOutputs : List ClearingOutputWire
deriving DecidableEq

structure BatchKeyWire where
  federationId : Digest32
  contentSession : Digest32
  contentEpoch : Nat
  batchId : Nat
  sourceRoot : Digest32
deriving DecidableEq

structure AssetInputWire where
  nullifier : Digest32
  owner : Digest32
  asset : AssetRefWire
  amount : Nat
deriving DecidableEq

structure BatchSpecWire where
  identity : IdentityWire
  batchId : Nat
  sourceRoot : Digest32
  policy : PolicyWire
deriving DecidableEq

structure ClaimWire where
  spec : BatchSpecWire
  privateBookCommitment : Digest32
  output : ClearingOutputWire
  baseInputs : List AssetInputWire
  quoteInputs : List AssetInputWire
  orderNullifiers : List Digest32
deriving DecidableEq

structure StateWire where
  identity : IdentityWire
  policy : PolicyWire
  baseNotes : List AssetInputWire
  quoteNotes : List AssetInputWire
  buyerBaseCustody : Nat
  sellerQuoteCustody : Nat
  consumedAssetNullifiers : List Digest32
  consumedOrderNullifiers : List Digest32
  consumedBatches : List BatchKeyWire
deriving DecidableEq

structure PrivateOrderWire where
  kind : Nat
  qty : Nat
deriving DecidableEq, Repr

structure OpeningWire where
  format : String
  orders : List PrivateOrderWire
  blinding : List Nat
deriving DecidableEq, Repr

structure InputWire where
  state : StateWire
  claim : ClaimWire
  opening : OpeningWire
deriving DecidableEq

structure PublicReceiptWire where
  authorization : String
  batchId : Nat
  sourceRoot : Digest32
  commitment : Digest32
  clearing : ClearingOutputWire
  assetNullifiers : List Digest32
  orderNullifiers : List Digest32
  buyerBaseCustody : Nat
  sellerQuoteCustody : Nat
deriving DecidableEq

structure OutputWire where
  inputDigest : Digest32
  successorDigest : Digest32
  publicViewDigest : Digest32
  receiptDigest : Digest32
  successor : StateWire
  publicView : ClaimWire
  receipt : PublicReceiptWire
deriving DecidableEq

/-! ## One canonical encoder -/

def AssetRefWire.toJson (asset : AssetRefWire) : String :=
  "{\"kind\":" ++ jsonString asset.kind ++
    ",\"relic_id\":" ++ toString asset.relicId ++ "}"

def IdentityWire.toJson (identity : IdentityWire) : String :=
  "{\"federation_id\":" ++ jsonString (Emit.bytes32Hex identity.federationId) ++
    ",\"content_root\":" ++ jsonString (Emit.bytes32Hex identity.contentRoot) ++
    ",\"activation_digest\":" ++ jsonString (Emit.bytes32Hex identity.activationDigest) ++
    ",\"content_session\":" ++ jsonString (Emit.bytes32Hex identity.contentSession) ++
    ",\"content_epoch\":" ++ toString identity.contentEpoch ++
    ",\"seller\":" ++ jsonString (Emit.bytes32Hex identity.seller) ++
    ",\"buyer\":" ++ jsonString (Emit.bytes32Hex identity.buyer) ++
    ",\"base_asset\":" ++ identity.baseAsset.toJson ++
    ",\"quote_asset\":" ++ identity.quoteAsset.toJson ++ "}"

def ClearingOutputWire.toJson (output : ClearingOutputWire) : String :=
  "{\"bucket\":" ++ toString output.bucket ++
    ",\"volume\":" ++ toString output.volume ++ "}"

def PolicyWire.toJson (policy : PolicyWire) : String :=
  "{\"buckets\":" ++ toString policy.buckets ++
    ",\"quote_tick\":" ++ toString policy.quoteTick ++
    ",\"max_orders\":" ++ toString policy.maxOrders ++
    ",\"max_order_quantity\":" ++ toString policy.maxOrderQuantity ++
    ",\"max_public_asset_inputs\":" ++ toString policy.maxPublicAssetInputs ++
    ",\"allowed_outputs\":" ++
      jsonArray (policy.allowedOutputs.map ClearingOutputWire.toJson) ++ "}"

def BatchKeyWire.toJson (key : BatchKeyWire) : String :=
  "{\"federation_id\":" ++ jsonString (Emit.bytes32Hex key.federationId) ++
    ",\"content_session\":" ++ jsonString (Emit.bytes32Hex key.contentSession) ++
    ",\"content_epoch\":" ++ toString key.contentEpoch ++
    ",\"batch_id\":" ++ toString key.batchId ++
    ",\"source_root\":" ++ jsonString (Emit.bytes32Hex key.sourceRoot) ++ "}"

def AssetInputWire.toJson (input : AssetInputWire) : String :=
  "{\"nullifier\":" ++ jsonString (Emit.bytes32Hex input.nullifier) ++
    ",\"owner\":" ++ jsonString (Emit.bytes32Hex input.owner) ++
    ",\"asset\":" ++ input.asset.toJson ++
    ",\"amount\":" ++ toString input.amount ++ "}"

def BatchSpecWire.toJson (spec : BatchSpecWire) : String :=
  "{\"identity\":" ++ spec.identity.toJson ++
    ",\"batch_id\":" ++ toString spec.batchId ++
    ",\"source_root\":" ++ jsonString (Emit.bytes32Hex spec.sourceRoot) ++
    ",\"policy\":" ++ spec.policy.toJson ++ "}"

def ClaimWire.toJson (claim : ClaimWire) : String :=
  "{\"spec\":" ++ claim.spec.toJson ++
    ",\"private_book_commitment\":" ++
      jsonString (Emit.bytes32Hex claim.privateBookCommitment) ++
    ",\"output\":" ++ claim.output.toJson ++
    ",\"base_inputs\":" ++ jsonArray (claim.baseInputs.map AssetInputWire.toJson) ++
    ",\"quote_inputs\":" ++ jsonArray (claim.quoteInputs.map AssetInputWire.toJson) ++
    ",\"order_nullifiers\":" ++
      jsonArray (claim.orderNullifiers.map (jsonString ∘ Emit.bytes32Hex)) ++ "}"

def StateWire.toJson (state : StateWire) : String :=
  "{\"identity\":" ++ state.identity.toJson ++
    ",\"policy\":" ++ state.policy.toJson ++
    ",\"base_notes\":" ++ jsonArray (state.baseNotes.map AssetInputWire.toJson) ++
    ",\"quote_notes\":" ++ jsonArray (state.quoteNotes.map AssetInputWire.toJson) ++
    ",\"buyer_base_custody\":" ++ toString state.buyerBaseCustody ++
    ",\"seller_quote_custody\":" ++ toString state.sellerQuoteCustody ++
    ",\"consumed_asset_nullifiers\":" ++
      jsonArray (state.consumedAssetNullifiers.map (jsonString ∘ Emit.bytes32Hex)) ++
    ",\"consumed_order_nullifiers\":" ++
      jsonArray (state.consumedOrderNullifiers.map (jsonString ∘ Emit.bytes32Hex)) ++
    ",\"consumed_batches\":" ++
      jsonArray (state.consumedBatches.map BatchKeyWire.toJson) ++ "}"

def PrivateOrderWire.toJson (order : PrivateOrderWire) : String :=
  "{\"kind\":" ++ toString order.kind ++ ",\"qty\":" ++ toString order.qty ++ "}"

def OpeningWire.toJson (opening : OpeningWire) : String :=
  "{\"format\":" ++ jsonString opening.format ++
    ",\"orders\":" ++ jsonArray (opening.orders.map PrivateOrderWire.toJson) ++
    ",\"blinding\":" ++ jsonArray (opening.blinding.map toString) ++ "}"

def InputWire.toJson (input : InputWire) : String :=
  "{\"format\":" ++ jsonString INPUT_FORMAT ++
    ",\"state\":" ++ input.state.toJson ++
    ",\"claim\":" ++ input.claim.toJson ++
    ",\"opening\":" ++ input.opening.toJson ++ "}"

def PublicReceiptWire.toJson (receipt : PublicReceiptWire) : String :=
  "{\"authorization\":" ++ jsonString receipt.authorization ++
    ",\"batch_id\":" ++ toString receipt.batchId ++
    ",\"source_root\":" ++ jsonString (Emit.bytes32Hex receipt.sourceRoot) ++
    ",\"commitment\":" ++ jsonString (Emit.bytes32Hex receipt.commitment) ++
    ",\"clearing\":" ++ receipt.clearing.toJson ++
    ",\"asset_nullifiers\":" ++
      jsonArray (receipt.assetNullifiers.map (jsonString ∘ Emit.bytes32Hex)) ++
    ",\"order_nullifiers\":" ++
      jsonArray (receipt.orderNullifiers.map (jsonString ∘ Emit.bytes32Hex)) ++
    ",\"buyer_base_custody\":" ++ toString receipt.buyerBaseCustody ++
    ",\"seller_quote_custody\":" ++ toString receipt.sellerQuoteCustody ++ "}"

def OutputWire.toJson (output : OutputWire) : String :=
  "{\"format\":" ++ jsonString OUTPUT_FORMAT ++
    ",\"input_digest\":" ++ jsonString (Emit.bytes32Hex output.inputDigest) ++
    ",\"successor_digest\":" ++ jsonString (Emit.bytes32Hex output.successorDigest) ++
    ",\"public_view_digest\":" ++ jsonString (Emit.bytes32Hex output.publicViewDigest) ++
    ",\"receipt_digest\":" ++ jsonString (Emit.bytes32Hex output.receiptDigest) ++
    ",\"successor\":" ++ output.successor.toJson ++
    ",\"public_view\":" ++ output.publicView.toJson ++
    ",\"receipt\":" ++ output.receipt.toJson ++ "}"

/-! ## Strict parsers and canonicality seal -/

private def parseDigestJson (j : Json) : Except String Digest32 := do
  let spelling ← j.getStr?
  match Emit.parseBytes32Hex? spelling with
  | some digest => pure digest
  | none => throw "digest must be exactly 64 lowercase hexadecimal digits"

private def parseAssetRef (j : Json) : Except String AssetRefWire := do
  exactKeys j ["kind", "relic_id"]
  let kind ← j.getObjValAs? String "kind"
  let relicId ← objectNat j "relic_id" DarkBazaar.Wire.u64Max
  if kind = "relic" then pure { kind, relicId }
  else if ["supplies", "intel", "munitions", "propellant"].contains kind && relicId = 0 then
    pure { kind, relicId }
  else throw "unknown or noncanonical asset"

private def parseIdentity (j : Json) : Except String IdentityWire := do
  exactKeys j ["federation_id", "content_root", "activation_digest", "content_session",
    "content_epoch", "seller", "buyer", "base_asset", "quote_asset"]
  pure {
    federationId := ← objectDigest j "federation_id"
    contentRoot := ← objectDigest j "content_root"
    activationDigest := ← objectDigest j "activation_digest"
    contentSession := ← objectDigest j "content_session"
    contentEpoch := ← objectNat j "content_epoch"
    seller := ← objectDigest j "seller"
    buyer := ← objectDigest j "buyer"
    baseAsset := ← parseAssetRef (← j.getObjVal? "base_asset")
    quoteAsset := ← parseAssetRef (← j.getObjVal? "quote_asset")
  }

private def parseOutput (j : Json) : Except String ClearingOutputWire := do
  exactKeys j ["bucket", "volume"]
  pure {
    bucket := ← objectNat j "bucket" DarkBazaar.Wire.u64Max
    volume := ← objectNat j "volume" DarkBazaar.Wire.maxOutputVolume
  }

private def parsePolicy (j : Json) : Except String PolicyWire := do
  exactKeys j ["buckets", "quote_tick", "max_orders", "max_order_quantity",
    "max_public_asset_inputs", "allowed_outputs"]
  pure {
    buckets := ← objectNat j "buckets" DarkBazaar.Wire.maxBuckets
    quoteTick := ← objectNat j "quote_tick" DarkBazaar.Wire.maxQuoteTick
    maxOrders := ← objectNat j "max_orders" DarkBazaar.Wire.maxOrders
    maxOrderQuantity := ← objectNat j "max_order_quantity" DarkBazaar.Wire.maxOrderQuantity
    maxPublicAssetInputs := ← objectNat j "max_public_asset_inputs"
    allowedOutputs := ← parseCanonicalArray (← j.getObjVal? "allowed_outputs")
      MAX_ALLOWED_OUTPUTS parseOutput ClearingOutputWire.toJson
  }

private def parseBatchKey (j : Json) : Except String BatchKeyWire := do
  exactKeys j ["federation_id", "content_session", "content_epoch", "batch_id", "source_root"]
  pure {
    federationId := ← objectDigest j "federation_id"
    contentSession := ← objectDigest j "content_session"
    contentEpoch := ← objectNat j "content_epoch"
    batchId := ← objectNat j "batch_id"
    sourceRoot := ← objectDigest j "source_root"
  }

private def parseAssetInput (j : Json) : Except String AssetInputWire := do
  exactKeys j ["nullifier", "owner", "asset", "amount"]
  pure {
    nullifier := ← objectDigest j "nullifier"
    owner := ← objectDigest j "owner"
    asset := ← parseAssetRef (← j.getObjVal? "asset")
    amount := ← objectNat j "amount" DarkBazaar.Wire.maxNoteAmount
  }

private def parseBatchSpec (j : Json) : Except String BatchSpecWire := do
  exactKeys j ["identity", "batch_id", "source_root", "policy"]
  pure {
    identity := ← parseIdentity (← j.getObjVal? "identity")
    batchId := ← objectNat j "batch_id"
    sourceRoot := ← objectDigest j "source_root"
    policy := ← parsePolicy (← j.getObjVal? "policy")
  }

private def parseClaim (j : Json) : Except String ClaimWire := do
  exactKeys j ["spec", "private_book_commitment", "output", "base_inputs",
    "quote_inputs", "order_nullifiers"]
  pure {
    spec := ← parseBatchSpec (← j.getObjVal? "spec")
    privateBookCommitment := ← objectDigest j "private_book_commitment"
    output := ← parseOutput (← j.getObjVal? "output")
    baseInputs := ← parseCanonicalArray (← j.getObjVal? "base_inputs")
      MAX_CLAIM_INPUTS parseAssetInput AssetInputWire.toJson
    quoteInputs := ← parseCanonicalArray (← j.getObjVal? "quote_inputs")
      MAX_CLAIM_INPUTS parseAssetInput AssetInputWire.toJson
    orderNullifiers := ← parseCanonicalArray (← j.getObjVal? "order_nullifiers")
      Market.DarkBazaarPrivateDescriptor.ORDER_COUNT parseDigestJson
      (jsonString ∘ Emit.bytes32Hex)
  }

private def parseState (j : Json) : Except String StateWire := do
  exactKeys j ["identity", "policy", "base_notes", "quote_notes", "buyer_base_custody",
    "seller_quote_custody", "consumed_asset_nullifiers", "consumed_order_nullifiers",
    "consumed_batches"]
  pure {
    identity := ← parseIdentity (← j.getObjVal? "identity")
    policy := ← parsePolicy (← j.getObjVal? "policy")
    baseNotes := ← parseCanonicalArray (← j.getObjVal? "base_notes")
      MAX_ESCROW_NOTES parseAssetInput AssetInputWire.toJson
    quoteNotes := ← parseCanonicalArray (← j.getObjVal? "quote_notes")
      MAX_ESCROW_NOTES parseAssetInput AssetInputWire.toJson
    buyerBaseCustody := ← objectNat j "buyer_base_custody"
    sellerQuoteCustody := ← objectNat j "seller_quote_custody"
    consumedAssetNullifiers := ← parseCanonicalArray
      (← j.getObjVal? "consumed_asset_nullifiers") MAX_CONSUMED_NULLIFIERS
      parseDigestJson (jsonString ∘ Emit.bytes32Hex)
    consumedOrderNullifiers := ← parseCanonicalArray
      (← j.getObjVal? "consumed_order_nullifiers") MAX_CONSUMED_NULLIFIERS
      parseDigestJson (jsonString ∘ Emit.bytes32Hex)
    consumedBatches := ← parseCanonicalArray (← j.getObjVal? "consumed_batches")
      MAX_CONSUMED_BATCHES parseBatchKey BatchKeyWire.toJson
  }

private def parsePrivateOrder (j : Json) : Except String PrivateOrderWire := do
  exactKeys j ["kind", "qty"]
  pure {
    kind := ← objectNat j "kind" 7
    qty := ← objectNat j "qty" 15
  }

private def parseOpening (j : Json) : Except String OpeningWire := do
  exactKeys j ["format", "orders", "blinding"]
  let format ← j.getObjValAs? String "format"
  if format != AUTHORIZATION_FORMAT then throw "wrong Dark Bazaar authorization format"
  let orders := (← (← j.getObjVal? "orders").getArr?).toList
  if orders.length != Market.DarkBazaarPrivateDescriptor.ORDER_COUNT then
    throw "v1 requires exactly four private orders"
  let blindingJson := (← (← j.getObjVal? "blinding").getArr?).toList
  if blindingJson.length != Market.DarkBazaarPrivateDescriptor.DIGEST_WIDTH then
    throw "v1 requires exactly eight blinding lanes"
  let blinding ← blindingJson.mapM fun value => do
    boundedNat (Market.DarkBazaarPrivateDescriptor.BABYBEAR_MODULUS.toNat - 1)
      (← value.getNat?)
  let parsedOrders ← orders.mapM parsePrivateOrder
  pure { format, orders := parsedOrders, blinding }

private def parseInputJson (j : Json) : Except String InputWire := do
  exactKeys j ["format", "state", "claim", "opening"]
  let format ← j.getObjValAs? String "format"
  if format != INPUT_FORMAT then throw "wrong Dark Bazaar input format"
  pure {
    state := ← parseState (← j.getObjVal? "state")
    claim := ← parseClaim (← j.getObjVal? "claim")
    opening := ← parseOpening (← j.getObjVal? "opening")
  }

def canonicalDecode {T : Type} (parse : Json → Except String T) (encode : T → String)
    (bytes : String) : Option T :=
  match Json.parse bytes with
  | .error _ => none
  | .ok json =>
      match parse json with
      | .error _ => none
      | .ok value => if encode value = bytes then some value else none

def decodeInputWithLimit (byteLimit : Nat) (bytes : String) : Option InputWire :=
  if bytes.length ≤ byteLimit then canonicalDecode parseInputJson InputWire.toJson bytes else none

def decodeInput (bytes : String) : Option InputWire :=
  decodeInputWithLimit WIRE_BYTE_LIMIT bytes

theorem canonicalDecode_reencodes {T : Type} (parse : Json → Except String T)
    (encode : T → String) {bytes : String} {value : T}
    (accepted : canonicalDecode parse encode bytes = some value) : encode value = bytes := by
  simp only [canonicalDecode] at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  rename_i equal
  cases accepted
  exact equal

theorem decodeInput_reencodes {bytes : String} {input : InputWire}
    (accepted : decodeInput bytes = some input) : input.toJson = bytes := by
  simp only [decodeInput, decodeInputWithLimit] at accepted
  split at accepted
  · exact canonicalDecode_reencodes parseInputJson InputWire.toJson accepted
  · contradiction

theorem decodeInput_refuses_oversized (bytes : String)
    (oversized : WIRE_BYTE_LIMIT < bytes.length) : decodeInput bytes = none := by
  simp [decodeInput, decodeInputWithLimit, Nat.not_le.mpr oversized]

/-! ## Semantic reconstruction -/

def AssetRefWire.toSemantic? (asset : AssetRefWire) : Option AssetRef :=
  match asset.kind with
  | "relic" => some (.relic ⟨asset.relicId⟩)
  | "supplies" => if asset.relicId = 0 then some .supplies else none
  | "intel" => if asset.relicId = 0 then some .intel else none
  | "munitions" => if asset.relicId = 0 then some .munitions else none
  | "propellant" => if asset.relicId = 0 then some .propellant else none
  | _ => none

def IdentityWire.toSemantic? (identity : IdentityWire) : Option StableMarketIdentity := do
  let baseAsset ← identity.baseAsset.toSemantic?
  let quoteAsset ← identity.quoteAsset.toSemantic?
  if hs : identity.seller ≠ identity.buyer then
    if ha : baseAsset ≠ quoteAsset then
      some {
        federationId := identity.federationId
        contentRoot := identity.contentRoot
        activationDigest := identity.activationDigest
        contentSession := identity.contentSession
        contentEpoch := ⟨identity.contentEpoch⟩
        seller := ⟨identity.seller⟩
        buyer := ⟨identity.buyer⟩
        parties_distinct := by exact fun h => hs (congrArg ParticipantId.value h)
        baseAsset
        quoteAsset
        assets_distinct := ha
      }
    else none
  else none

def ClearingOutputWire.toSemantic (output : ClearingOutputWire) : ClearingOutput :=
  ⟨output.bucket, output.volume⟩

def PolicyWire.toSemantic? (policy : PolicyWire) : Option MarketPolicy :=
  if hb : 0 < policy.buckets then
    if ht : 0 < policy.quoteTick then
      let result : MarketPolicy := {
        pricing := {
          buckets := policy.buckets
          buckets_pos := hb
          quoteTick := policy.quoteTick
          quoteTick_pos := ht
        }
        maxOrders := policy.maxOrders
        maxOrderQuantity := policy.maxOrderQuantity
        maxPublicAssetInputs := policy.maxPublicAssetInputs
        allowedOutputs := (policy.allowedOutputs.map ClearingOutputWire.toSemantic).toFinset
      }
      if result.WireBounded then some result else none
    else none
  else none

def BatchKeyWire.toSemantic (key : BatchKeyWire) : BatchKey where
  federationId := key.federationId
  contentSession := key.contentSession
  contentEpoch := ⟨key.contentEpoch⟩
  batchId := ⟨key.batchId⟩
  sourceRoot := key.sourceRoot

def AssetInputWire.toSemantic? (input : AssetInputWire) : Option AssetInput := do
  let asset ← input.asset.toSemantic?
  let result : AssetInput := {
    nullifier := ⟨input.nullifier⟩
    owner := ⟨input.owner⟩
    asset
    amount := input.amount
  }
  if result.WireBounded then some result else none

def BatchSpecWire.toSemantic? (spec : BatchSpecWire) : Option BatchSpec := do
  let identity ← spec.identity.toSemantic?
  let policy ← spec.policy.toSemantic?
  some {
    federationId := identity.federationId
    contentRoot := identity.contentRoot
    activationDigest := identity.activationDigest
    contentSession := identity.contentSession
    contentEpoch := identity.contentEpoch
    batchId := ⟨spec.batchId⟩
    sourceRoot := spec.sourceRoot
    seller := identity.seller
    buyer := identity.buyer
    parties_distinct := identity.parties_distinct
    baseAsset := identity.baseAsset
    quoteAsset := identity.quoteAsset
    assets_distinct := identity.assets_distinct
    pricing := policy.pricing
    maxOrders := policy.maxOrders
    maxOrderQuantity := policy.maxOrderQuantity
    allowedOutputs := policy.allowedOutputs
  }

def ClaimWire.toSemantic? (wire : ClaimWire) : Option SettlementClaim := do
  let spec ← wire.spec.toSemantic?
  let baseInputs ← wire.baseInputs.mapM AssetInputWire.toSemantic?
  let quoteInputs ← wire.quoteInputs.mapM AssetInputWire.toSemantic?
  let claim : SettlementClaim := {
    spec
    privateBookCommitment := wire.privateBookCommitment
    output := wire.output.toSemantic
    baseInputs := baseInputs.toFinset
    quoteInputs := quoteInputs.toFinset
    orderNullifiers := (wire.orderNullifiers.map (OrderNullifier.mk)).toFinset
  }
  if claim.WireBounded then some claim else none

def StateWire.toSemantic? (wire : StateWire) : Option BazaarState := do
  let identity ← wire.identity.toSemantic?
  let policy ← wire.policy.toSemantic?
  let baseList ← wire.baseNotes.mapM AssetInputWire.toSemantic?
  let quoteList ← wire.quoteNotes.mapM AssetInputWire.toSemantic?
  let baseNotes := baseList.toFinset
  let quoteNotes := quoteList.toFinset
  if hbase : ∀ input ∈ baseNotes,
      input.owner = identity.seller ∧ input.asset = identity.baseAsset ∧ 0 < input.amount then
    if hquote : ∀ input ∈ quoteNotes,
        input.owner = identity.buyer ∧ input.asset = identity.quoteAsset ∧ 0 < input.amount then
      if hbaseInj : Set.InjOn AssetInput.nullifier baseNotes then
        if hquoteInj : Set.InjOn AssetInput.nullifier quoteNotes then
          if hdisjoint : Disjoint (baseNotes.image AssetInput.nullifier)
              (quoteNotes.image AssetInput.nullifier) then
            let state : BazaarState := {
              identity
              policy
              baseEscrow := {
                notes := baseNotes
                notesWellFormed := hbase
                nullifiersInjective := hbaseInj
              }
              quoteEscrow := {
                notes := quoteNotes
                notesWellFormed := hquote
                nullifiersInjective := hquoteInj
              }
              escrowNullifiersDisjoint := hdisjoint
              buyerBaseCustody := wire.buyerBaseCustody
              sellerQuoteCustody := wire.sellerQuoteCustody
              consumedAssetNullifiers :=
                (wire.consumedAssetNullifiers.map AssetNullifier.mk).toFinset
              consumedOrderNullifiers :=
                (wire.consumedOrderNullifiers.map OrderNullifier.mk).toFinset
              consumedBatches := (wire.consumedBatches.map BatchKeyWire.toSemantic).toFinset
            }
            if state.WireBounded then some state else none
          else none
        else none
      else none
    else none
  else none

def PrivateOrderWire.toSemantic? (order : PrivateOrderWire) :
    Option Market.DarkBazaarPrivateDescriptor.PrivateOrder :=
  if hk : order.kind < 8 then
    if hq : order.qty < 16 then some ⟨⟨order.kind, hk⟩, ⟨order.qty, hq⟩⟩ else none
  else none

private def defaultPrivateOrder : Market.DarkBazaarPrivateDescriptor.PrivateOrder :=
  ⟨0, 0⟩

def OpeningWire.toSemantic? (opening : OpeningWire) :
    Option Market.DarkBazaarPrivateDescriptor.PrivateWitness := do
  if opening.format != AUTHORIZATION_FORMAT then none else
  if opening.orders.length != Market.DarkBazaarPrivateDescriptor.ORDER_COUNT then none else
  if opening.blinding.length != Market.DarkBazaarPrivateDescriptor.DIGEST_WIDTH then none else
  let orders ← opening.orders.mapM PrivateOrderWire.toSemantic?
  if opening.blinding.all
      (fun value => decide (value < Market.DarkBazaarPrivateDescriptor.BABYBEAR_MODULUS.toNat)) then
    some {
      orders := fun slot => orders.getD slot.val defaultPrivateOrder
      blinding := fun lane => opening.blinding.getD lane.val 0
    }
  else none

structure SemanticInput where
  wire : InputWire
  state : BazaarState
  claim : SettlementClaim
  root : Fin 8 → Int
  witness : Market.DarkBazaarPrivateDescriptor.PrivateWitness

def InputWire.toSemantic? (wire : InputWire) : Option SemanticInput := do
  let state ← wire.state.toSemantic?
  let claim ← wire.claim.toSemantic?
  let root ← V1.rootOfDigest? claim.privateBookCommitment
  let witness ← wire.opening.toSemantic?
  some { wire, state, claim, root, witness }

/-! ## Deterministic public successor and labelled digests -/

private def canonicalize {T : Type} [DecidableEq T]
    (encode : T → String) (values : List T) : List T :=
  (values.eraseDups).insertionSort (fun left right => encode left < encode right)

def ClaimWire.batchKey (claim : ClaimWire) : BatchKeyWire where
  federationId := claim.spec.identity.federationId
  contentSession := claim.spec.identity.contentSession
  contentEpoch := claim.spec.identity.contentEpoch
  batchId := claim.spec.batchId
  sourceRoot := claim.spec.sourceRoot

def ClaimWire.assetNullifiers (claim : ClaimWire) : List Digest32 :=
  canonicalize (jsonString ∘ Emit.bytes32Hex)
    ((claim.baseInputs ++ claim.quoteInputs).map AssetInputWire.nullifier)

/-- Wire-level candidate for the semantic transition.  The judge accepts this
candidate only after reconstructing it back into `BazaarState` and comparing
its complete `ObservableState` with Lean's actual `applySettlement` result. -/
def StateWire.successorCandidate (before : StateWire) (claim : ClaimWire) : StateWire := {
  identity := before.identity
  policy := before.policy
  baseNotes := before.baseNotes.filter (fun note => !claim.baseInputs.contains note)
  quoteNotes := before.quoteNotes.filter (fun note => !claim.quoteInputs.contains note)
  buyerBaseCustody := before.buyerBaseCustody + claim.output.volume
  sellerQuoteCustody := before.sellerQuoteCustody +
    ((claim.output.bucket + 1) * claim.spec.policy.quoteTick) * claim.output.volume
  consumedAssetNullifiers := canonicalize (jsonString ∘ Emit.bytes32Hex)
    (before.consumedAssetNullifiers ++ claim.assetNullifiers)
  consumedOrderNullifiers := canonicalize (jsonString ∘ Emit.bytes32Hex)
    (before.consumedOrderNullifiers ++ claim.orderNullifiers)
  consumedBatches := canonicalize BatchKeyWire.toJson
    (claim.batchKey :: before.consumedBatches)
}

def PublicReceiptWire.ofTransition (input : InputWire) (successor : StateWire) :
    PublicReceiptWire where
  authorization := AUTHORIZATION_FORMAT
  batchId := input.claim.spec.batchId
  sourceRoot := input.claim.spec.sourceRoot
  commitment := input.claim.privateBookCommitment
  clearing := input.claim.output
  assetNullifiers := input.claim.assetNullifiers
  orderNullifiers := input.claim.orderNullifiers
  buyerBaseCustody := successor.buyerBaseCustody
  sellerQuoteCustody := successor.sellerQuoteCustody

abbrev INPUT_DIGEST_DOMAIN : Nat := 0x50444249
abbrev SUCCESSOR_DIGEST_DOMAIN : Nat := 0x50444253
abbrev PUBLIC_VIEW_DIGEST_DOMAIN : Nat := 0x50444256
abbrev RECEIPT_DIGEST_DOMAIN : Nat := 0x50444252

private def stringBytes (value : String) : List Nat :=
  value.toUTF8.toList.map UInt8.toNat

def digestString (domain : Nat) (value : String) : Digest32 :=
  let lanes := Dregg2.Circuit.CommitmentTreeWide.hashTo8 domain (stringBytes value)
  V1.digestOfRoot fun lane => lanes.getD lane.val 0

private def receiptDigestPreimage (inputDigest successorDigest publicViewDigest : Digest32)
    (receipt : PublicReceiptWire) : String :=
  "{\"format\":\"POA-DARK-BAZAAR-RECEIPT-DIGEST-1\"" ++
    ",\"input_digest\":" ++ jsonString (Emit.bytes32Hex inputDigest) ++
    ",\"successor_digest\":" ++ jsonString (Emit.bytes32Hex successorDigest) ++
    ",\"public_view_digest\":" ++ jsonString (Emit.bytes32Hex publicViewDigest) ++
    ",\"receipt\":" ++ receipt.toJson ++ "}"

def OutputWire.ofTransition (inputBytes : String) (input : InputWire)
    (successor : StateWire) : OutputWire :=
  let receipt := PublicReceiptWire.ofTransition input successor
  let inputDigest := digestString INPUT_DIGEST_DOMAIN inputBytes
  let successorDigest := digestString SUCCESSOR_DIGEST_DOMAIN successor.toJson
  let publicViewDigest := digestString PUBLIC_VIEW_DIGEST_DOMAIN input.claim.toJson
  let receiptDigest := digestString RECEIPT_DIGEST_DOMAIN
    (receiptDigestPreimage inputDigest successorDigest publicViewDigest receipt)
  { inputDigest, successorDigest, publicViewDigest, receiptDigest,
    successor, publicView := input.claim, receipt }

private def parseReceipt (j : Json) : Except String PublicReceiptWire := do
  exactKeys j ["authorization", "batch_id", "source_root", "commitment", "clearing",
    "asset_nullifiers", "order_nullifiers", "buyer_base_custody", "seller_quote_custody"]
  let authorization ← j.getObjValAs? String "authorization"
  if authorization != AUTHORIZATION_FORMAT then throw "wrong receipt authorization"
  pure {
    authorization
    batchId := ← objectNat j "batch_id"
    sourceRoot := ← objectDigest j "source_root"
    commitment := ← objectDigest j "commitment"
    clearing := ← parseOutput (← j.getObjVal? "clearing")
    assetNullifiers := ← parseCanonicalArray (← j.getObjVal? "asset_nullifiers")
      MAX_CLAIM_INPUTS parseDigestJson (jsonString ∘ Emit.bytes32Hex)
    orderNullifiers := ← parseCanonicalArray (← j.getObjVal? "order_nullifiers")
      Market.DarkBazaarPrivateDescriptor.ORDER_COUNT parseDigestJson
      (jsonString ∘ Emit.bytes32Hex)
    buyerBaseCustody := ← objectNat j "buyer_base_custody"
    sellerQuoteCustody := ← objectNat j "seller_quote_custody"
  }

private def parseOutputJson (j : Json) : Except String OutputWire := do
  exactKeys j ["format", "input_digest", "successor_digest", "public_view_digest",
    "receipt_digest", "successor", "public_view", "receipt"]
  let format ← j.getObjValAs? String "format"
  if format != OUTPUT_FORMAT then throw "wrong Dark Bazaar output format"
  pure {
    inputDigest := ← objectDigest j "input_digest"
    successorDigest := ← objectDigest j "successor_digest"
    publicViewDigest := ← objectDigest j "public_view_digest"
    receiptDigest := ← objectDigest j "receipt_digest"
    successor := ← parseState (← j.getObjVal? "successor")
    publicView := ← parseClaim (← j.getObjVal? "public_view")
    receipt := ← parseReceipt (← j.getObjVal? "receipt")
  }

def decodeOutput (bytes : String) : Option OutputWire :=
  if bytes.length ≤ WIRE_BYTE_LIMIT then
    canonicalDecode parseOutputJson OutputWire.toJson bytes
  else none

theorem decodeOutput_reencodes {bytes : String} {output : OutputWire}
    (accepted : decodeOutput bytes = some output) : output.toJson = bytes := by
  simp only [decodeOutput] at accepted
  split at accepted
  · exact canonicalDecode_reencodes parseOutputJson OutputWire.toJson accepted
  · contradiction

#assert_axioms canonicalDecode_reencodes
#assert_axioms decodeInput_reencodes
#assert_axioms decodeInput_refuses_oversized
#assert_axioms decodeOutput_reencodes

end Dregg2.Games.PathOfAngels.DarkBazaarJudgeWire
