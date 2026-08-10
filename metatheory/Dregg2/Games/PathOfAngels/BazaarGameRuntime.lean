/-
# Path of Angels Bazaar — canonical restart wire and native CAS boundary

`BazaarGame` deliberately keeps its live registry, state, persistence receipt,
and every authority admission constructor private.  This module does not relax
that boundary.  It gives the trusted native runtime one much narrower job:

* Lean encodes the complete `StateKey` and `RuntimeCasRequest` from their typed
  values into one canonical, bounded JSON image;
* a strict Lean decoder recognizes exactly that image language and rejects
  whitespace, reordered keys, alternate tags, noncanonical sets, unknown
  fields, oversized values, and trailing bytes;
* the `performCas` native extern receives the typed request, asks Lean for the
  exact expected/replacement images, and may return its private admission only
  after a crash-durable byte CAS succeeds; and
* the durable-load extern may return its private admission only when the caller
  supplied the exact canonical bytes for `state.key`, the registry equations
  hold, and the native durable head is byte-identical.

The native store is intentionally ignorant of every Bazaar constructor and
game rule.  Conversely, JSON is not authority: decoding produces only the
proof-erased `WireValue` syntax below, never `StateKey`, `BazaarGameState`, a
registry, or an admission.  A caller-authored string therefore cannot become a
continuation even when it is canonical.
-/
import Lean.Data.Json
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Sort
import Dregg2.Games.PathOfAngels.BazaarGame
import Dregg2.Games.PathOfAngels.EmitDigestHex
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.BazaarGameRuntime

open Lean
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.DarkBazaar
open Dregg2.Games.PathOfAngels.BazaarGame

set_option autoImplicit false
set_option maxRecDepth 100000

abbrev STATE_FORMAT : String := "POA-BAZAAR-STATE-KEY-1"
abbrev CAS_FORMAT : String := "POA-BAZAAR-CAS-REQUEST-1"
abbrev WIRE_BYTE_LIMIT : Nat := 16 * 1024 * 1024
abbrev WIRE_U64_MAX : Nat := 2 ^ 64 - 1
abbrev MAX_COLLECTION : Nat := 65536
abbrev MAX_HISTORY : Nat := 65536
abbrev MAX_ESCROW_NOTES : Nat := 4096
abbrev MAX_ALLOWED_OUTPUTS : Nat := 64
abbrev MAX_ROUND_ENVELOPES : Nat := MAX_ROUND_ORDERS

private def jsonString (value : String) : String := String.quote value
private def jsonArray (values : List String) : String :=
  "[" ++ String.intercalate "," values ++ "]"

private def exactKeys (json : Json) (allowed : List String) : Except String Unit := do
  let object ← json.getObj?
  if object.size == allowed.length && allowed.all object.contains then pure ()
  else throw "missing or unknown field"

/-! ## A small canonical algebraic wire

This generic tree keeps the parser small without making the state opaque.  The
schema checker below names every constructor, field, collection bound, and set
ordering rule in the exact `StateKey` image. -/

inductive WireValue where
  | nat (value : Nat)
  | digest (value : Digest32)
  | text (value : String)
  | node (tag : String) (fields : List WireValue)

def WireValue.toJson : WireValue → String
  | .nat value => "{\"n\":" ++ toString value ++ "}"
  | .digest value => "{\"d\":" ++ jsonString (Emit.bytes32Hex value) ++ "}"
  | .text value => "{\"s\":" ++ jsonString value ++ "}"
  | .node tag fields =>
      "{\"tag\":" ++ jsonString tag ++
        ",\"fields\":" ++ jsonArray (fields.map WireValue.toJson) ++ "}"

private def parseWireValue : Nat → Json → Except String WireValue
  | 0, _ => throw "wire nesting exceeds bound"
  | fuel + 1, json => do
      let object ← json.getObj?
      if object.size = 1 && object.contains "n" then
        exactKeys json ["n"]
        let value ← json.getObjValAs? Nat "n"
        if value ≤ WIRE_U64_MAX then pure (.nat value)
        else throw "integer exceeds u64 wire bound"
      else if object.size = 1 && object.contains "d" then
        exactKeys json ["d"]
        let spelling ← json.getObjValAs? String "d"
        match Emit.parseBytes32Hex? spelling with
        | some digest => pure (.digest digest)
        | none => throw "digest must be exactly 64 lowercase hexadecimal digits"
      else if object.size = 1 && object.contains "s" then
        exactKeys json ["s"]
        let value ← json.getObjValAs? String "s"
        if value.toUTF8.size ≤ WIRE_BYTE_LIMIT then pure (.text value)
        else throw "embedded canonical value exceeds bound"
      else
        exactKeys json ["tag", "fields"]
        let tag ← json.getObjValAs? String "tag"
        if tag.isEmpty || tag.length > 96 then throw "invalid wire tag" else
        let values := (← (← json.getObjVal? "fields").getArr?).toList
        if values.length > MAX_COLLECTION then throw "wire collection exceeds bound" else
        pure (.node tag (← values.mapM (parseWireValue fuel)))

def canonicalDecode (bytes : String) : Option WireValue :=
  if bytes.toUTF8.size > WIRE_BYTE_LIMIT then none else
  match Json.parse bytes with
  | .error _ => none
  | .ok json =>
      match parseWireValue 256 json with
      | .error _ => none
      | .ok value => if value.toJson = bytes then some value else none

theorem canonicalDecode_reencodes {bytes : String} {value : WireValue}
    (accepted : canonicalDecode bytes = some value) : value.toJson = bytes := by
  simp only [canonicalDecode] at accepted
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  split at accepted <;> try contradiction
  rename_i equal
  cases accepted
  exact equal

private def wireLess (left right : WireValue) : Bool := left.toJson < right.toJson
private def wireLessP (left right : WireValue) : Prop := wireLess left right = true

private instance wireLessPDecidable (left right : WireValue) :
    Decidable (wireLessP left right) := by
  unfold wireLessP wireLess
  infer_instance

private def canonicalize (values : List WireValue) : List WireValue :=
  values.insertionSort wireLessP

private def setValue {T : Type} [DecidableEq T]
    (encode : T → WireValue) (values : Finset T) : WireValue :=
  let encoded : Finset String := values.image (fun value => (encode value).toJson)
  .node "set" (.nat values.card ::
    (encoded.sort (fun left right => left ≤ right)).map WireValue.text)

private def listValue {T : Type} (encode : T → WireValue)
    (values : List T) : WireValue := .node "list" (values.map encode)

private def optionValue {T : Type} (encode : T → WireValue) : Option T → WireValue
  | none => .node "none" []
  | some value => .node "some" [encode value]

/-! ## Complete typed image -/

private def participantValue (participant : ParticipantId) : WireValue :=
  .node "participant" [.digest participant.value]

private def assetRefValue : AssetRef → WireValue
  | .relic relic => .node "asset.relic" [.nat relic.value]
  | .supplies => .node "asset.supplies" []
  | .intel => .node "asset.intel" []
  | .munitions => .node "asset.munitions" []
  | .propellant => .node "asset.propellant" []

private def receiptKeyValue (key : ReceiptKey) : WireValue :=
  .node "receipt-key" [.digest key.federationId, .digest key.contentSession,
    .nat key.contentEpoch.value, .digest key.playerKey, .nat key.playerCounter]

private def originKeyValue (key : OriginKey) : WireValue :=
  .node "origin-key" [receiptKeyValue key.receipt, .digest key.contentRoot,
    .digest key.activationDigest, .nat key.relic.value]

private def assetInputValue (input : AssetInput) : WireValue :=
  .node "asset-input" [.digest input.nullifier.value,
    participantValue input.owner, assetRefValue input.asset, .nat input.amount]

private def lotKeyValue (key : LotKey) : WireValue :=
  .node "lot-key" [.digest key.authority, .digest key.sourceRoot,
    originKeyValue key.origin, participantValue key.seller,
    assetInputValue key.note]

private def priceScheduleValue (schedule : PriceSchedule) : WireValue :=
  .node "price-schedule" [.nat schedule.buckets, .nat schedule.quoteTick]

private def clearingOutputValue (output : ClearingOutput) : WireValue :=
  .node "clearing-output" [.nat output.bucket, .nat output.volume]

private def batchKeyValue (key : BatchKey) : WireValue :=
  .node "batch-key" [.digest key.federationId, .digest key.contentSession,
    .nat key.contentEpoch.value, .nat key.batchId.value, .digest key.sourceRoot]

private def identityValue (identity : StableMarketIdentity) : WireValue :=
  .node "market-identity" [.digest identity.federationId,
    .digest identity.contentRoot, .digest identity.activationDigest,
    .digest identity.contentSession, .nat identity.contentEpoch.value,
    participantValue identity.seller, participantValue identity.buyer,
    assetRefValue identity.baseAsset, assetRefValue identity.quoteAsset]

private def policyValue (policy : MarketPolicy) : WireValue :=
  .node "market-policy" [priceScheduleValue policy.pricing,
    .nat policy.maxOrders, .nat policy.maxOrderQuantity,
    .nat policy.maxPublicAssetInputs,
    setValue clearingOutputValue policy.allowedOutputs]

private def observableStateValue (state : ObservableState) : WireValue :=
  .node "observable-state" [identityValue state.identity,
    policyValue state.policy, .nat state.baseEscrow, .nat state.quoteEscrow,
    .nat state.buyerBaseCustody, .nat state.sellerQuoteCustody,
    setValue assetInputValue state.baseEscrowNotes,
    setValue assetInputValue state.quoteEscrowNotes,
    setValue (fun nullifier => .digest nullifier.value)
      state.consumedAssetNullifiers,
    setValue (fun nullifier => .digest nullifier.value)
      state.consumedOrderNullifiers,
    setValue batchKeyValue state.consumedBatches]

private def inventoryValue (inventory : Inventory) : WireValue :=
  .node "inventory" [setValue lotKeyValue inventory.maker,
    setValue lotKeyValue inventory.taker,
    setValue lotKeyValue inventory.escrow]

private def roundIdValue (id : RoundId) : WireValue :=
  .node "round-id" [.nat id.value.val]

private def scheduleValue (schedule : RoundSchedule) : WireValue :=
  .node "round-schedule" [.nat schedule.opensAt, .nat schedule.cancelBefore,
    .nat schedule.closesAt, .nat schedule.expiresAt]

private def feePolicyValue (fees : FeePolicy) : WireValue :=
  .node "fee-policy" [.nat fees.listingFee, .nat fees.settlementFee]

private def requestedPrivacyValue : RequestedPrivacy → WireValue
  | .openingAwareJudge => .node "privacy.opening-aware-judge" []
  | .houseBlind => .node "privacy.house-blind" []

private def preferenceIngressValue : PreferenceIngress → WireValue
  | .authenticatedCiphertextPendingOpening =>
      .node "ingress.authenticated-ciphertext-pending-opening" []
  | .v1SameOpeningBound => .node "ingress.v1-same-opening-bound" []
  | .commitReveal => .node "ingress.commit-reveal" []

private def privacyGradeValue : BazaarGame.PrivacyGrade → WireValue
  | .authenticatedCiphertextOnlyNoOpeningClaim =>
      .node "grade.authenticated-ciphertext-only" []
  | .commitmentsPublicOpeningVisibleToJudge =>
      .node "grade.opening-visible-to-judge" []
  | .houseBlindUnavailable => .node "grade.house-blind-unavailable" []

private def envelopeStatementValue (statement : EnvelopeStatement) : WireValue :=
  .node "envelope-statement" [participantValue statement.actor,
    roundIdValue statement.round, batchKeyValue statement.batchKey,
    .digest statement.nullifier.value, .digest statement.ciphertextCommitment,
    .digest statement.signatureCommitment]

private def sealedEnvelopeValue (envelope : SealedEnvelope) : WireValue :=
  -- The authorization field is a proposition-like private receipt.  Proof
  -- irrelevance means the exact semantic data is the indexed statement.
  envelopeStatementValue envelope.statement

private def bookBindingValue (binding : BookBindingKey) : WireValue :=
  .node "book-binding" [roundIdValue binding.round,
    batchKeyValue binding.batchKey, batchKeyValue binding.claimKey,
    .digest binding.privateBookCommitment,
    setValue envelopeStatementValue binding.transcript]

private def roundPhaseValue : RoundPhase → WireValue
  | .collecting => .node "round-phase.collecting" []
  | .awaitingSettlement binding =>
      .node "round-phase.awaiting-settlement" [bookBindingValue binding]

private def roundKeyValue (round : RoundKey) : WireValue :=
  .node "round-key" [roundIdValue round.id, lotKeyValue round.lot,
    participantValue round.buyer, batchKeyValue round.batchKey,
    assetRefValue round.quoteAsset, priceScheduleValue round.pricing,
    scheduleValue round.schedule, .nat round.maxOrders,
    .nat round.maxOrderQuantity,
    setValue clearingOutputValue round.allowedOutputs,
    feePolicyValue round.fees, requestedPrivacyValue round.requestedPrivacy,
    preferenceIngressValue round.preferenceIngress,
    roundPhaseValue round.phase,
    setValue sealedEnvelopeValue round.envelopes]

private def completionKindValue : CompletionKind → WireValue
  | .cancelled => .node "completion.cancelled" []
  | .expired => .node "completion.expired" []
  | .settled batch output =>
      .node "completion.settled" [batchKeyValue batch,
        clearingOutputValue output]

private def roundSummaryValue (summary : RoundSummary) : WireValue :=
  .node "round-summary" [roundIdValue summary.id, lotKeyValue summary.lot,
    assetRefValue summary.quoteAsset, priceScheduleValue summary.pricing,
    .nat summary.orderCount, privacyGradeValue summary.privacyGrade,
    preferenceIngressValue summary.preferenceIngress,
    completionKindValue summary.kind]

def stateKeyToWireValue (key : StateKey) : WireValue :=
  .node STATE_FORMAT [.digest key.authority, .nat key.registryRevision.val,
    inventoryValue key.inventory, observableStateValue key.market,
    optionValue roundKeyValue key.current,
    listValue roundSummaryValue key.history, .nat key.tick.val,
    .nat key.nextRound.val, setValue originKeyValue key.consumedOrigins,
    setValue batchKeyValue key.consumedSettlements]

def stateKeyToCanonicalJson (key : StateKey) : String :=
  (stateKeyToWireValue key).toJson

def runtimeCasRequestToWireValue (request : RuntimeCasRequest) : WireValue :=
  .node CAS_FORMAT [optionValue stateKeyToWireValue request.expected,
    stateKeyToWireValue request.replacement]

def runtimeCasRequestToCanonicalJson (request : RuntimeCasRequest) : String :=
  (runtimeCasRequestToWireValue request).toJson

/-! ## Canonical command-event payloads

These payloads retain computational command inputs, never opaque authority,
crown, envelope, opening, or settlement proof constructors.  Unlike the
`StateKey` recognizer below, this decoder returns a typed command: command
replay, rather than decoding a caller-authored state snapshot, reconstructs the
private machine state.
-/

abbrev REPLAY_EVENT_FORMAT : String := "POA-BAZAAR-COMMAND-EVENT-1"

private def replayContextValue (context : ReplayContext) : WireValue :=
  .node "replay-context" [.digest context.deploymentId,
    .digest context.storeIdentity]

private def replayGenesisValue (genesis : ReplayGenesisEvent) : WireValue :=
  .node "replay-genesis" [.digest genesis.authority,
    lotKeyValue genesis.lot, observableStateValue genesis.market,
    .nat genesis.originCounter]

def replayCommandEventToWireValue (context : ReplayContext)
    (event : ReplayCommandEvent) : WireValue :=
  match event with
  | .initialize genesis => .node REPLAY_EVENT_FORMAT
      [replayContextValue context, .node "command.initialize"
        [replayGenesisValue genesis]]
  | .advanceClock => .node REPLAY_EVENT_FORMAT
      [replayContextValue context, .node "command.advance-clock" []]

def replayCommandEventToCanonicalJson (context : ReplayContext)
    (event : ReplayCommandEvent) : String :=
  (replayCommandEventToWireValue context event).toJson

private def decodeNat : WireValue → Option Nat
  | .nat value => if value ≤ WIRE_U64_MAX then some value else none
  | _ => none

private def decodeDigest : WireValue → Option Digest32
  | .digest value => some value
  | _ => none

private def decodeParticipant : WireValue → Option ParticipantId
  | .node "participant" [value] => return ⟨← decodeDigest value⟩
  | _ => none

private def decodeAssetRef : WireValue → Option AssetRef
  | .node "asset.relic" [value] => return .relic ⟨← decodeNat value⟩
  | .node "asset.supplies" [] => some .supplies
  | .node "asset.intel" [] => some .intel
  | .node "asset.munitions" [] => some .munitions
  | .node "asset.propellant" [] => some .propellant
  | _ => none

private def decodeReceiptKey : WireValue → Option ReceiptKey
  | .node "receipt-key" [federation, session, epoch, player, counter] =>
      return {
        federationId := ← decodeDigest federation
        contentSession := ← decodeDigest session
        contentEpoch := ⟨← decodeNat epoch⟩
        playerKey := ← decodeDigest player
        playerCounter := ← decodeNat counter
      }
  | _ => none

private def decodeOriginKey : WireValue → Option OriginKey
  | .node "origin-key" [receipt, content, activation, relic] =>
      return {
        receipt := ← decodeReceiptKey receipt
        contentRoot := ← decodeDigest content
        activationDigest := ← decodeDigest activation
        relic := ⟨← decodeNat relic⟩
      }
  | _ => none

private def decodeAssetInput : WireValue → Option AssetInput
  | .node "asset-input" [nullifier, owner, asset, amount] =>
      return {
        nullifier := ⟨← decodeDigest nullifier⟩
        owner := ← decodeParticipant owner
        asset := ← decodeAssetRef asset
        amount := ← decodeNat amount
      }
  | _ => none

private def decodeLotKey : WireValue → Option LotKey
  | .node "lot-key" [authority, source, origin, seller, note] =>
      return {
        authority := ← decodeDigest authority
        sourceRoot := ← decodeDigest source
        origin := ← decodeOriginKey origin
        seller := ← decodeParticipant seller
        note := ← decodeAssetInput note
      }
  | _ => none

private def decodePriceSchedule : WireValue → Option PriceSchedule
  | .node "price-schedule" [bucketsWire, quoteTickWire] => do
      let buckets ← decodeNat bucketsWire
      let quoteTick ← decodeNat quoteTickWire
      if hbuckets : 0 < buckets then
        if hquote : 0 < quoteTick then
          some ⟨buckets, hbuckets, quoteTick, hquote⟩
        else none
      else none
  | _ => none

private def decodeClearingOutput : WireValue → Option ClearingOutput
  | .node "clearing-output" [bucket, volume] =>
      return ⟨← decodeNat bucket, ← decodeNat volume⟩
  | _ => none

private def decodeBatchKey : WireValue → Option BatchKey
  | .node "batch-key" [federation, session, epoch, batch, source] =>
      return {
        federationId := ← decodeDigest federation
        contentSession := ← decodeDigest session
        contentEpoch := ⟨← decodeNat epoch⟩
        batchId := ⟨← decodeNat batch⟩
        sourceRoot := ← decodeDigest source
      }
  | _ => none

private def decodeCanonicalSet {T : Type} [DecidableEq T]
    (limit : Nat) (decode : WireValue → Option T) : WireValue → Option (Finset T)
  | .node "set" (.nat declared :: fields) => do
      if declared != fields.length ∨ fields.length > limit then none else
      let values ← fields.mapM fun field => do
        let .text bytes := field | none
        decode (← canonicalDecode bytes)
      let result := values.toFinset
      if result.card = values.length then some result else none
  | _ => none

private def decodeIdentity : WireValue → Option StableMarketIdentity
  | .node "market-identity" [federation, content, activation, session, epoch,
      sellerWire, buyerWire, baseWire, quoteWire] => do
      let seller ← decodeParticipant sellerWire
      let buyer ← decodeParticipant buyerWire
      let baseAsset ← decodeAssetRef baseWire
      let quoteAsset ← decodeAssetRef quoteWire
      if hparties : seller ≠ buyer then
        if hassets : baseAsset ≠ quoteAsset then
          some {
            federationId := ← decodeDigest federation
            contentRoot := ← decodeDigest content
            activationDigest := ← decodeDigest activation
            contentSession := ← decodeDigest session
            contentEpoch := ⟨← decodeNat epoch⟩
            seller
            buyer
            parties_distinct := hparties
            baseAsset
            quoteAsset
            assets_distinct := hassets
          }
        else none
      else none
  | _ => none

private def decodePolicy : WireValue → Option MarketPolicy
  | .node "market-policy" [pricing, orders, quantity, publicInputs, outputs] =>
      return {
        pricing := ← decodePriceSchedule pricing
        maxOrders := ← decodeNat orders
        maxOrderQuantity := ← decodeNat quantity
        maxPublicAssetInputs := ← decodeNat publicInputs
        allowedOutputs := ← decodeCanonicalSet MAX_ALLOWED_OUTPUTS
          decodeClearingOutput outputs
      }
  | _ => none

private def decodeObservableState : WireValue → Option ObservableState
  | .node "observable-state" [identity, policy, baseEscrow, quoteEscrow,
      buyerBase, sellerQuote, baseNotes, quoteNotes, assetNullifiers,
      orderNullifiers, batches] =>
      return {
        identity := ← decodeIdentity identity
        policy := ← decodePolicy policy
        baseEscrow := ← decodeNat baseEscrow
        quoteEscrow := ← decodeNat quoteEscrow
        buyerBaseCustody := ← decodeNat buyerBase
        sellerQuoteCustody := ← decodeNat sellerQuote
        baseEscrowNotes := ← decodeCanonicalSet MAX_ESCROW_NOTES decodeAssetInput baseNotes
        quoteEscrowNotes := ← decodeCanonicalSet MAX_ESCROW_NOTES decodeAssetInput quoteNotes
        consumedAssetNullifiers := ← decodeCanonicalSet MAX_COLLECTION
          (fun wire => return ⟨← decodeDigest wire⟩) assetNullifiers
        consumedOrderNullifiers := ← decodeCanonicalSet MAX_COLLECTION
          (fun wire => return ⟨← decodeDigest wire⟩) orderNullifiers
        consumedBatches := ← decodeCanonicalSet MAX_COLLECTION decodeBatchKey batches
      }
  | _ => none

private def decodeReplayContext : WireValue → Option ReplayContext
  | .node "replay-context" [deployment, store] =>
      return ⟨← decodeDigest deployment, ← decodeDigest store⟩
  | _ => none

private def decodeReplayGenesis : WireValue → Option ReplayGenesisEvent
  | .node "replay-genesis" [authority, lot, market, counter] =>
      return {
        authority := ← decodeDigest authority
        lot := ← decodeLotKey lot
        market := ← decodeObservableState market
        originCounter := ← decodeNat counter
      }
  | _ => none

private def decodeReplayCommandValue : WireValue → Option (ReplayContext × ReplayCommandEvent)
  | .node format [contextWire, .node "command.initialize" [genesisWire]] => do
      if format != REPLAY_EVENT_FORMAT then none else
      return (← decodeReplayContext contextWire, .initialize (← decodeReplayGenesis genesisWire))
  | .node format [contextWire, .node "command.advance-clock" []] => do
      if format != REPLAY_EVENT_FORMAT then none else
      return (← decodeReplayContext contextWire, .advanceClock)
  | _ => none

def decodeReplayCommandEvent (bytes : String) :
    Option (ReplayContext × ReplayCommandEvent) := do
  let decoded ← canonicalDecode bytes
  let result ← decodeReplayCommandValue decoded
  if replayCommandEventToCanonicalJson result.1 result.2 = bytes then
    some result
  else none

theorem decodeReplayCommandEvent_reencodes {bytes : String}
    {result : ReplayContext × ReplayCommandEvent}
    (accepted : decodeReplayCommandEvent bytes = some result) :
    replayCommandEventToCanonicalJson result.1 result.2 = bytes := by
  cases decoded : canonicalDecode bytes with
  | none => simp [decodeReplayCommandEvent, decoded] at accepted
  | some wire =>
      cases parsed : decodeReplayCommandValue wire with
      | none => simp [decodeReplayCommandEvent, decoded, parsed] at accepted
      | some candidate =>
          by_cases exact :
              replayCommandEventToCanonicalJson candidate.1 candidate.2 = bytes
          · simp [decodeReplayCommandEvent, decoded, parsed, exact] at accepted
            subst result
            exact exact
          · simp [decodeReplayCommandEvent, decoded, parsed, exact] at accepted

/-! ## Exact schema recognizer -/

private def natB : WireValue → Bool
  | .nat value => decide (value ≤ WIRE_U64_MAX)
  | _ => false

private def positiveNatB : WireValue → Bool
  | .nat value => decide (0 < value ∧ value ≤ WIRE_U64_MAX)
  | _ => false

private def digestB : WireValue → Bool
  | .digest _ => true
  | _ => false

private def nullaryB (tag : String) : WireValue → Bool
  | .node actual [] => actual == tag
  | _ => false

private def canonicalFieldsB (limit : Nat) (element : WireValue → Bool)
    (fields : List WireValue) : Bool :=
  decide (fields.length ≤ limit) && fields.all element &&
    decide (fields.Pairwise wireLessP)

private def setB (limit : Nat) (element : WireValue → Bool) : WireValue → Bool
  | .node "set" (.nat declared :: fields) =>
      decide (declared = fields.length) && decide (fields.length ≤ limit) &&
        decide (fields.Pairwise wireLessP) && fields.all (fun field =>
          match field with
          | .text bytes => match canonicalDecode bytes with
            | some value => element value
            | none => false
          | _ => false)
  | _ => false

private def listB (limit : Nat) (element : WireValue → Bool) : WireValue → Bool
  | .node "list" fields => decide (fields.length ≤ limit) && fields.all element
  | _ => false

private def optionB (element : WireValue → Bool) : WireValue → Bool
  | .node "none" [] => true
  | .node "some" [value] => element value
  | _ => false

private def participantB : WireValue → Bool
  | .node "participant" [value] => digestB value
  | _ => false

private def assetRefB : WireValue → Bool
  | .node "asset.relic" [value] => natB value
  | value => ["asset.supplies", "asset.intel", "asset.munitions",
      "asset.propellant"].any (fun tag => nullaryB tag value)

private def receiptKeyB : WireValue → Bool
  | .node "receipt-key" [federation, session, epoch, player, counter] =>
      digestB federation && digestB session && natB epoch &&
        digestB player && natB counter
  | _ => false

private def originKeyB : WireValue → Bool
  | .node "origin-key" [receipt, content, activation, relic] =>
      receiptKeyB receipt && digestB content && digestB activation && natB relic
  | _ => false

private def assetInputB : WireValue → Bool
  | .node "asset-input" [nullifier, owner, asset, amount] =>
      digestB nullifier && participantB owner && assetRefB asset && natB amount
  | _ => false

private def lotKeyB : WireValue → Bool
  | .node "lot-key" [authority, source, origin, seller, note] =>
      digestB authority && digestB source && originKeyB origin &&
        participantB seller && assetInputB note
  | _ => false

private def priceScheduleB : WireValue → Bool
  | .node "price-schedule" [buckets, tick] =>
      positiveNatB buckets && positiveNatB tick
  | _ => false

private def clearingOutputB : WireValue → Bool
  | .node "clearing-output" [bucket, volume] => natB bucket && natB volume
  | _ => false

private def batchKeyB : WireValue → Bool
  | .node "batch-key" [federation, session, epoch, batch, source] =>
      digestB federation && digestB session && natB epoch && natB batch &&
        digestB source
  | _ => false

private def identityB : WireValue → Bool
  | .node "market-identity" [federation, content, activation, session, epoch,
      seller, buyer, baseAsset, quoteAsset] =>
      digestB federation && digestB content && digestB activation &&
        digestB session && natB epoch && participantB seller &&
        participantB buyer && (seller.toJson != buyer.toJson) && assetRefB baseAsset &&
        assetRefB quoteAsset && (baseAsset.toJson != quoteAsset.toJson)
  | _ => false

private def policyB : WireValue → Bool
  | .node "market-policy" [pricing, orders, quantity, publicInputs, outputs] =>
      priceScheduleB pricing && natB orders && natB quantity &&
        natB publicInputs && setB MAX_ALLOWED_OUTPUTS clearingOutputB outputs
  | _ => false

private def observableStateB : WireValue → Bool
  | .node "observable-state" [identity, policy, baseEscrow, quoteEscrow,
      buyerBase, sellerQuote, baseNotes, quoteNotes, assetNullifiers,
      orderNullifiers, batches] =>
      identityB identity && policyB policy && natB baseEscrow &&
        natB quoteEscrow && natB buyerBase && natB sellerQuote &&
        setB MAX_ESCROW_NOTES assetInputB baseNotes &&
        setB MAX_ESCROW_NOTES assetInputB quoteNotes &&
        setB MAX_COLLECTION digestB assetNullifiers &&
        setB MAX_COLLECTION digestB orderNullifiers &&
        setB MAX_COLLECTION batchKeyB batches
  | _ => false

private def inventoryB : WireValue → Bool
  | .node "inventory" [maker, taker, escrow] =>
      setB MAX_COLLECTION lotKeyB maker && setB MAX_COLLECTION lotKeyB taker &&
        setB MAX_COLLECTION lotKeyB escrow
  | _ => false

private def roundIdB : WireValue → Bool
  | .node "round-id" [value] => natB value
  | _ => false

private def scheduleB : WireValue → Bool
  | .node "round-schedule" [opens, cancel, closes, expires] =>
      natB opens && natB cancel && natB closes && natB expires
  | _ => false

private def feePolicyB : WireValue → Bool
  | .node "fee-policy" [listing, settlement] => natB listing && natB settlement
  | _ => false

private def requestedPrivacyB (value : WireValue) : Bool :=
  nullaryB "privacy.opening-aware-judge" value ||
    nullaryB "privacy.house-blind" value

private def preferenceIngressB (value : WireValue) : Bool :=
  nullaryB "ingress.authenticated-ciphertext-pending-opening" value ||
    nullaryB "ingress.v1-same-opening-bound" value ||
    nullaryB "ingress.commit-reveal" value

private def privacyGradeB (value : WireValue) : Bool :=
  nullaryB "grade.authenticated-ciphertext-only" value ||
    nullaryB "grade.opening-visible-to-judge" value ||
    nullaryB "grade.house-blind-unavailable" value

private def envelopeStatementB : WireValue → Bool
  | .node "envelope-statement" [actor, round, batch, nullifier,
      ciphertext, signature] =>
      participantB actor && roundIdB round && batchKeyB batch &&
        digestB nullifier && digestB ciphertext && digestB signature
  | _ => false

private def bookBindingB : WireValue → Bool
  | .node "book-binding" [round, batch, claim, commitment, transcript] =>
      roundIdB round && batchKeyB batch && batchKeyB claim &&
        digestB commitment && setB MAX_ROUND_ENVELOPES envelopeStatementB transcript
  | _ => false

private def roundPhaseB : WireValue → Bool
  | value@(.node "round-phase.collecting" []) =>
      nullaryB "round-phase.collecting" value
  | .node "round-phase.awaiting-settlement" [binding] => bookBindingB binding
  | _ => false

private def roundKeyB : WireValue → Bool
  | .node "round-key" [id, lot, buyer, batch, quote, pricing, schedule,
      orders, quantity, outputs, fees, privacy, ingress, phase, envelopes] =>
      roundIdB id && lotKeyB lot && participantB buyer && batchKeyB batch &&
        assetRefB quote && priceScheduleB pricing && scheduleB schedule &&
        natB orders && natB quantity &&
        setB MAX_ALLOWED_OUTPUTS clearingOutputB outputs && feePolicyB fees &&
        requestedPrivacyB privacy && preferenceIngressB ingress &&
        roundPhaseB phase &&
        setB MAX_ROUND_ENVELOPES envelopeStatementB envelopes
  | _ => false

private def completionKindB : WireValue → Bool
  | value@(.node "completion.cancelled" []) => nullaryB "completion.cancelled" value
  | value@(.node "completion.expired" []) => nullaryB "completion.expired" value
  | .node "completion.settled" [batch, output] =>
      batchKeyB batch && clearingOutputB output
  | _ => false

private def roundSummaryB : WireValue → Bool
  | .node "round-summary" [id, lot, quote, pricing, orders, grade, ingress, kind] =>
      roundIdB id && lotKeyB lot && assetRefB quote && priceScheduleB pricing &&
        natB orders && privacyGradeB grade && preferenceIngressB ingress &&
        completionKindB kind
  | _ => false

def stateKeyWireValueB : WireValue → Bool
  | .node format [authority, revision, inventory, market, current, history,
      tick, nextRound, origins, settlements] =>
      format == STATE_FORMAT && digestB authority && natB revision &&
        inventoryB inventory && observableStateB market &&
        optionB roundKeyB current && listB MAX_HISTORY roundSummaryB history &&
        natB tick && natB nextRound && setB MAX_COLLECTION originKeyB origins &&
        setB MAX_COLLECTION batchKeyB settlements
  | _ => false

def runtimeCasRequestWireValueB : WireValue → Bool
  | .node format [expected, replacement] =>
      format == CAS_FORMAT && optionB stateKeyWireValueB expected &&
        stateKeyWireValueB replacement
  | _ => false

def decodeStateKey (bytes : String) : Option WireValue := do
  let value ← canonicalDecode bytes
  if stateKeyWireValueB value then some value else none

def decodeRuntimeCasRequest (bytes : String) : Option WireValue := do
  let value ← canonicalDecode bytes
  if runtimeCasRequestWireValueB value then some value else none

theorem decodeStateKey_reencodes {bytes : String} {value : WireValue}
    (accepted : decodeStateKey bytes = some value) : value.toJson = bytes := by
  cases decoded : canonicalDecode bytes with
  | none => simp [decodeStateKey, decoded] at accepted
  | some candidate =>
      by_cases valid : stateKeyWireValueB candidate = true
      · simp [decodeStateKey, decoded, valid] at accepted
        subst value
        exact canonicalDecode_reencodes decoded
      · simp [decodeStateKey, decoded, valid] at accepted

theorem decodeRuntimeCasRequest_reencodes {bytes : String} {value : WireValue}
    (accepted : decodeRuntimeCasRequest bytes = some value) :
    value.toJson = bytes := by
  cases decoded : canonicalDecode bytes with
  | none => simp [decodeRuntimeCasRequest, decoded] at accepted
  | some candidate =>
      by_cases valid : runtimeCasRequestWireValueB candidate = true
      · simp [decodeRuntimeCasRequest, decoded, valid] at accepted
        subst value
        exact canonicalDecode_reencodes decoded
      · simp [decodeRuntimeCasRequest, decoded, valid] at accepted

def stateKeyCodecValidB (key : StateKey) : Bool :=
  match decodeStateKey (stateKeyToCanonicalJson key) with
  | some decoded => decoded.toJson == stateKeyToCanonicalJson key
  | none => false

def runtimeCasRequestCodecValidB (request : RuntimeCasRequest) : Bool :=
  match decodeRuntimeCasRequest (runtimeCasRequestToCanonicalJson request) with
  | some decoded => decoded.toJson == runtimeCasRequestToCanonicalJson request
  | none => false

def stateKeyMatchesCanonicalJsonB (key : StateKey) (wire : String) : Bool :=
  match decodeStateKey wire with
  | some decoded => decoded.toJson == stateKeyToCanonicalJson key
  | none => false

def durableLoadWireValidB (registry : DeploymentRegistry)
    (state : BazaarGameState) (wire : ByteArray) : Bool :=
  match String.fromUTF8? wire with
  | none => false
  | some text =>
      decide (registry.head = some state.key) &&
        decide (registry.revision = state.registryRevision) &&
        decide (registry.authority = state.authority) &&
        stateKeyMatchesCanonicalJsonB state.key text

def journaledRuntimeCasRequestCodecValidB
    (request : JournaledRuntimeCasRequest) : Bool :=
  runtimeCasRequestCodecValidB request.cas &&
    match decodeReplayCommandEvent
      (replayCommandEventToCanonicalJson request.context request.event) with
    | some decoded => decide (decoded = (request.context, request.event))
    | none => false

/-! ## Native ABI helpers

These exports never construct an admission.  The C implementation of the two
private checked-Bool externs calls them on the exact typed arguments, then
performs only journal-backed byte CAS or replay-tail equality.  The public Lean
wrappers in `BazaarGame` materialize the dependent private admissions only
after those checked primitives return true.
-/

@[export dregg_poa_bazaar_runtime_request_codec_valid]
def requestCodecValidExport (request : RuntimeCasRequest) : Bool :=
  runtimeCasRequestCodecValidB request

@[export dregg_poa_bazaar_runtime_request_expected_present]
def requestExpectedPresentExport (request : RuntimeCasRequest) : Bool :=
  request.expected.isSome

@[export dregg_poa_bazaar_runtime_request_expected_encode]
def requestExpectedEncodeExport (request : RuntimeCasRequest) : String :=
  request.expected.map stateKeyToCanonicalJson |>.getD ""

@[export dregg_poa_bazaar_runtime_request_replacement_encode]
def requestReplacementEncodeExport (request : RuntimeCasRequest) : String :=
  stateKeyToCanonicalJson request.replacement

-- ⚑ DELETED 2026-08-05: `@[export dregg_poa_bazaar_runtime_request_encode]` /
-- `requestEncodeExport`, a whole-`RuntimeCasRequest` canonical-JSON render. It shipped in
-- `libdregg_lean.a` and NOTHING called it — not `lean_init.c` (which declared it at :511 and
-- never used it), not any `.rs`, in either the working tree or HEAD. It is not a v2 leftover of
-- a v3 shape either: `dregg_poa_bazaar_perform_cas_checked` passes `expected` and `replacement`
-- as two independently-emitted byte strings BY DESIGN, so that C retains no game structure, and a
-- one-blob request render has no place on that path. Deleted rather than ratcheted because the
-- ratchet's own rule is that a row must say what would WIRE it, and there is no such consumer to
-- name. `runtimeCasRequestToCanonicalJson` itself STAYS — it is the codec-validity check at :805
-- and the fixture-distinctness theorem at :1086. Only the `@[export]` seam is gone.
-- Re-emits: none (Lean-side only). Also removed: the `extern` at `dregg-lean-ffi/src/lean_init.c`
-- and the row in `dregg-lean-ffi/build.rs`'s 16-symbol coherence list, now 15.

@[export dregg_poa_bazaar_runtime_journaled_request_codec_valid]
def journaledRequestCodecValidExport
    (request : JournaledRuntimeCasRequest) : Bool :=
  journaledRuntimeCasRequestCodecValidB request

@[export dregg_poa_bazaar_runtime_journaled_expected_present]
def journaledExpectedPresentExport
    (request : JournaledRuntimeCasRequest) : Bool :=
  request.cas.expected.isSome

@[export dregg_poa_bazaar_runtime_journaled_expected_encode]
def journaledExpectedEncodeExport
    (request : JournaledRuntimeCasRequest) : String :=
  request.cas.expected.map stateKeyToCanonicalJson |>.getD ""

@[export dregg_poa_bazaar_runtime_journaled_replacement_encode]
def journaledReplacementEncodeExport
    (request : JournaledRuntimeCasRequest) : String :=
  stateKeyToCanonicalJson request.cas.replacement

@[export dregg_poa_bazaar_runtime_journaled_event_encode]
def journaledEventEncodeExport
    (request : JournaledRuntimeCasRequest) : String :=
  replayCommandEventToCanonicalJson request.context request.event

@[export dregg_poa_bazaar_runtime_journaled_deployment_encode]
def journaledDeploymentEncodeExport
    (request : JournaledRuntimeCasRequest) : String :=
  Emit.bytes32Hex request.context.deploymentId

@[export dregg_poa_bazaar_runtime_journaled_store_encode]
def journaledStoreEncodeExport
    (request : JournaledRuntimeCasRequest) : String :=
  Emit.bytes32Hex request.context.storeIdentity

@[export dregg_poa_bazaar_runtime_state_from_game_encode]
def stateFromGameEncodeExport (state : BazaarGameState) : String :=
  stateKeyToCanonicalJson state.key

@[export dregg_poa_bazaar_runtime_durable_load_valid]
def durableLoadValidExport (registry : DeploymentRegistry)
    (state : BazaarGameState) (wire : ByteArray) : Bool :=
  durableLoadWireValidB registry state wire

@[export dregg_poa_bazaar_runtime_state_key_validate]
def stateKeyValidateExport (wire : String) : Bool :=
  (decodeStateKey wire).isSome

/-! ## Closed typed CAS fixture for the linked boundary

The fixture constructs `StateKey` directly; it does not fabricate a registry,
authority, crown, envelope, or durable-load admission.  It exists so native
tests can enter the actual dependent `performCas` extern and prove that only a
successful exact CAS produces `some`.

⚑ **SIX OF THE NINE PINS NO LONGER EVALUATE IN THIS MODULE (2026-08-08).** This module is in
the `Dregg2.FFI` closure — the crypto archive's build root — and its `native_decide` pins ran at
elaboration, so any fixture regression here was a hard failure of every Rust proving target in
the workspace (the compilation-unit coupling the stale-fixture outage measured). Six pins'
STATEMENTS stay here as evaluation-free `check_* : Bool` definitions (a `def` body elaborates
without running); the EVALUATION — each `check_* = true`, pinned by `native_decide` +
`#assert_compiled` — lives in `BazaarGameRuntimeFixtures.lean`, rooted in the
`PathOfAngelsGuards` library: a plain `lake build` still runs every pin, and a stale fixture
reds the guard library instead of the archive.

⚠ **Named residue, THREE construction proofs — they CANNOT move**, because each is required as
DATA at construction:

  * `fixtureIdentity.parties_distinct` — `StableMarketIdentity` carries the seller≠buyer proof
    as a field, so the fixture identity cannot be built without it;
  * `fixture_replay_genesis_accepts` → `fixtureReplayGenesisApplied`, and
  * `fixture_replay_advance_accepts` → `fixtureReplayAdvanceApplied`, both through
    `replayValueOfAccepted`.  `ReplayMachine.mk` is `private` with three proof fields, so there
    is NO `ReplayApplied` this module can build as a fail-closed fallback — and both values feed
    the `@[export] dregg_poa_bazaar_runtime_fixture` entry point, which stays exactly as it is.

Breaking the replay path therefore still reds this module (and the archive).  Everything the
codec pins cover moved.
-/

private def repeatedDigest (value : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨value % 256, Nat.mod_lt _ (by decide)⟩
  length_eq := by simp

private def fixtureSeller : ParticipantId := ⟨repeatedDigest 17⟩
private def fixtureBuyer : ParticipantId := ⟨repeatedDigest 34⟩
private def fixtureRelic : RelicId := ⟨9001⟩

private def fixtureReceiptKey : ReceiptKey where
  federationId := repeatedDigest 1
  contentSession := repeatedDigest 4
  contentEpoch := ⟨1⟩
  playerKey := repeatedDigest 7
  playerCounter := 1

private def fixtureOrigin : OriginKey where
  receipt := fixtureReceiptKey
  contentRoot := repeatedDigest 2
  activationDigest := repeatedDigest 3
  relic := fixtureRelic

private def fixtureNote : AssetInput where
  nullifier := ⟨repeatedDigest 113⟩
  owner := fixtureSeller
  asset := .relic fixtureRelic
  amount := 1

private def fixtureLot : LotKey where
  authority := repeatedDigest 88
  sourceRoot := repeatedDigest 51
  origin := fixtureOrigin
  seller := fixtureSeller
  note := fixtureNote

private def fixturePricing : PriceSchedule where
  buckets := 4
  buckets_pos := by decide
  quoteTick := 10
  quoteTick_pos := by decide

private def fixtureIdentity : StableMarketIdentity where
  federationId := repeatedDigest 1
  contentRoot := repeatedDigest 2
  activationDigest := repeatedDigest 3
  contentSession := repeatedDigest 4
  contentEpoch := ⟨1⟩
  seller := fixtureSeller
  buyer := fixtureBuyer
  -- ⚠ NAMED RESIDUE: a construction proof, demanded as a FIELD of `StableMarketIdentity`.
  -- It cannot move to `BazaarGameRuntimeFixtures` — the fixture identity does not exist
  -- without it.
  parties_distinct := by native_decide
  baseAsset := .relic fixtureRelic
  quoteAsset := .intel
  assets_distinct := by decide

private def fixturePolicy : MarketPolicy where
  pricing := fixturePricing
  maxOrders := 4
  maxOrderQuantity := 15
  maxPublicAssetInputs := 8
  allowedOutputs := {⟨0, 1⟩}

private def fixtureMarket : ObservableState where
  identity := fixtureIdentity
  policy := fixturePolicy
  baseEscrow := 1
  quoteEscrow := 10
  buyerBaseCustody := 0
  sellerQuoteCustody := 0
  baseEscrowNotes := {fixtureNote}
  quoteEscrowNotes := ∅
  consumedAssetNullifiers := ∅
  consumedOrderNullifiers := ∅
  consumedBatches := ∅

private def fixtureCounter (value : Nat) (small : value < PLAYER_COUNTER_MODULUS) :
    PlayerCounter := ⟨value, small⟩

def fixtureStateKey (revision tick : PlayerCounter) : StateKey where
  authority := repeatedDigest 88
  registryRevision := revision
  inventory := Inventory.singletonMaker fixtureLot
  market := fixtureMarket
  current := none
  history := []
  tick := tick
  nextRound := fixtureCounter 0 (by decide)
  consumedOrigins := ∅
  consumedSettlements := ∅

def fixtureState1 : StateKey :=
  fixtureStateKey (fixtureCounter 1 (by decide)) (fixtureCounter 0 (by decide))
def fixtureState2 : StateKey :=
  fixtureStateKey (fixtureCounter 2 (by decide)) (fixtureCounter 1 (by decide))
def fixtureState3 : StateKey :=
  fixtureStateKey (fixtureCounter 3 (by decide)) (fixtureCounter 2 (by decide))

def fixtureGenesisRequest : RuntimeCasRequest := ⟨none, fixtureState1⟩
def fixtureSuccessorRequest : RuntimeCasRequest := ⟨some fixtureState1, fixtureState2⟩
def fixtureStaleRequest : RuntimeCasRequest := ⟨some fixtureState1, fixtureState3⟩

def fixtureReplayContext : ReplayContext :=
  ⟨repeatedDigest 88, repeatedDigest 23⟩

def fixtureReplayGenesis : ReplayGenesisEvent where
  authority := repeatedDigest 88
  lot := fixtureLot
  market := fixtureMarket
  originCounter := 1

private def replayAcceptedB : Except ReplayRefusal ReplayApplied → Bool
  | .ok _ => true
  | .error _ => false

private def replayValueOfAccepted
    (result : Except ReplayRefusal ReplayApplied)
    (accepted : replayAcceptedB result = true) : ReplayApplied :=
  match h : result with
  | .ok value => value
  | .error _ => False.elim (by simp [replayAcceptedB] at accepted)

private def replayRefusalB (expected : ReplayRefusal) :
    Except ReplayRefusal ReplayApplied → Bool
  | .error actual => decide (actual = expected)
  | .ok _ => false

def fixtureReplayGenesisResult := replayCommand fixtureReplayContext none
  (.initialize fixtureReplayGenesis)

/-- ⚠ NAMED RESIDUE — this one CANNOT move to `BazaarGameRuntimeFixtures`:
`fixtureReplayGenesisApplied` below takes it as DATA through `replayValueOfAccepted`, and
`ReplayMachine.mk` is `private` with three proof fields, so there is no `ReplayApplied` this
module could use as a fail-closed fallback instead. -/
theorem fixture_replay_genesis_accepts :
    replayAcceptedB fixtureReplayGenesisResult = true := by
  native_decide

def fixtureReplayGenesisApplied : ReplayApplied :=
  replayValueOfAccepted fixtureReplayGenesisResult fixture_replay_genesis_accepts

def fixtureReplayAdvanceResult := replayCommand fixtureReplayContext
  (some fixtureReplayGenesisApplied.machine) .advanceClock

/-- ⚠ NAMED RESIDUE — same reason as the genesis witness: `fixtureReplayAdvanceApplied` takes
it as DATA and no fail-closed `ReplayApplied` exists. -/
theorem fixture_replay_advance_accepts :
    replayAcceptedB fixtureReplayAdvanceResult = true := by
  native_decide

def fixtureReplayAdvanceApplied : ReplayApplied :=
  replayValueOfAccepted fixtureReplayAdvanceResult fixture_replay_advance_accepts

/-- (Pinned `= true` in `BazaarGameRuntimeFixtures`.) -/
def check_fixture_replay_event_codec_is_canonical : Bool :=
  decide (decodeReplayCommandEvent
    (replayCommandEventToCanonicalJson fixtureReplayContext
      (.initialize fixtureReplayGenesis)) =
    some (fixtureReplayContext, .initialize fixtureReplayGenesis))

/-- (Pinned `= true` in `BazaarGameRuntimeFixtures`.) -/
def check_fixture_cross_deployment_event_refuses : Bool :=
  replayRefusalB .deploymentMismatch
    (replayCommand ⟨repeatedDigest 99, repeatedDigest 23⟩ none
      (.initialize fixtureReplayGenesis))

/-- (Pinned `= true` in `BazaarGameRuntimeFixtures`.) -/
def check_fixture_state_codec_is_canonical : Bool := stateKeyCodecValidB fixtureState2

/-- (Pinned `= true` in `BazaarGameRuntimeFixtures`.) -/
def check_fixture_request_codec_is_canonical : Bool :=
  runtimeCasRequestCodecValidB fixtureSuccessorRequest

/-- (Pinned `= true` in `BazaarGameRuntimeFixtures`.) -/
def check_fixture_state_trailing_byte_refuses : Bool :=
  (decodeStateKey (stateKeyToCanonicalJson fixtureState2 ++ " ")).isNone

/-- (Pinned `= true` in `BazaarGameRuntimeFixtures`.) -/
def check_fixture_request_substitution_changes_wire : Bool :=
  runtimeCasRequestToCanonicalJson fixtureSuccessorRequest !=
    runtimeCasRequestToCanonicalJson fixtureStaleRequest

-- The two named-residue construction proofs; the six codec pins moved to
-- `BazaarGameRuntimeFixtures.lean`, rooted in `PathOfAngelsGuards` — see the fixture header.
#assert_compiled fixture_replay_genesis_accepts
#assert_compiled fixture_replay_advance_accepts

@[export dregg_poa_bazaar_runtime_fixture]
def fixtureFFI (command : String) : IO String := do
  match command with
  | "genesis" =>
      let result ← TrustedRuntimePortal.performJournaledCas
        fixtureReplayGenesisApplied.journaledRequest
      pure (if result.isSome then "applied" else "refused")
  | "successor" =>
      let result ← TrustedRuntimePortal.performJournaledCas
        fixtureReplayAdvanceApplied.journaledRequest
      pure (if result.isSome then "applied" else "refused")
  | "stale" =>
      let result ← TrustedRuntimePortal.performJournaledCas
        fixtureReplayAdvanceApplied.journaledRequest
      pure (if result.isSome then "applied" else "refused")
  | "admit-replayed" =>
      let wire := (stateKeyToCanonicalJson fixtureReplayAdvanceApplied.machine.key).toUTF8
      let deployment ← fixtureReplayAdvanceApplied.machine.admitDurable wire
      pure (if deployment.isSome then "admitted" else "refused")
  | _ => pure "refused"

#assert_axioms canonicalDecode_reencodes
#assert_axioms decodeStateKey_reencodes
#assert_axioms decodeRuntimeCasRequest_reencodes
#assert_axioms decodeReplayCommandEvent_reencodes

end Dregg2.Games.PathOfAngels.BazaarGameRuntime
