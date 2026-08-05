/-
# Path of Angels — player-facing sealed-salvage Bazaar

This module is the game/economy layer around the existing Dark Bazaar semantic
judge.  A round has a real custody object, a bounded collection window, opaque
order envelopes, an exact close, and one settlement receipt.  Settlement moves
the listed lot only when the receipt contains an actually successful
`DarkBazaar.applySettlement`; a UI observation or a pending proof never mutates
custody.

The privacy claim is intentionally exact.  The only accepted receipt family is
`openingAwareV1`: Lean checks the private opening, but the judge process sees it.
Requesting a house-blind round produces a typed blocker and cannot be relabelled
as settlement.  Likewise, non-zero fees are blocked because the current Bazaar
successor has no treasury debit/credit leg.  A later DrEX proof family must add
those transitions rather than decorating the current receipt.

`SalvageOrigin` begins at an abstract, executable `JudgedRun`, keeps its exact
Field Archive membership, and proves the offered relic occurred in that run's
checked contribution.  `CrownedSalvage` additionally names the already-existing
escrow note.  There is deliberately no `SalvageOrigin -> CrownedSalvage`
producer in this module: the currently missing runtime crown/provenance proof is
represented by `CrownDecision.observationOnly`, not by minting a note here.
-/
import Dregg2.Games.PathOfAngels.DarkBazaar
import Dregg2.Games.PathOfAngels.FieldArchive
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.BazaarGame

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.DarkBazaar
open Dregg2.Games.PathOfAngels.FieldArchive

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

abbrev MAX_ROUND_ORDERS : Nat := DarkBazaar.Wire.maxOrders

/-! ## Exact salvage identity and the crown boundary -/

/-- The same judged object is retained through archive membership and relic
eligibility.  Neither the receipt key nor the relic is reconstructed from UI
metadata. -/
structure SalvageOrigin where
  run : JudgedRun
  archive : ArchiveState
  relic : RelicId
  archived : ArchiveEntry.ofJudged run ∈ archive.entries
  yielded : relic ∈ run.receipt.contribution.relics

/-- Identity of the deployment authority which is allowed to admit crown
certificates and advance the serialized Bazaar state.  The constructor is
private: a digest-shaped browser claim is not an authority capability. -/
structure DeploymentAuthority (id : Digest32) where
  private mk ::
  private authenticated : True

structure OriginKey where
  receipt : ReceiptKey
  contentRoot : Digest32
  activationDigest : Digest32
  relic : RelicId
deriving DecidableEq

def SalvageOrigin.key (origin : SalvageOrigin) : OriginKey where
  receipt := origin.run.receipt.key
  contentRoot := origin.run.receipt.contentRoot
  activationDigest := origin.run.receipt.activationDigest
  relic := origin.relic

/-- Equality of Bazaar origin keys implies equality of every receipt-domain
field subsequently read by batch derivation or settlement.  `ReceiptKey` alone
is intentionally only a replay key and omits the activated content pair; this
stronger game key closes that semantic alias. -/
theorem SalvageOrigin.key_extensional_downstream {left right : SalvageOrigin}
    (equal : left.key = right.key) :
    left.run.receipt.federationId = right.run.receipt.federationId ∧
      left.run.receipt.contentRoot = right.run.receipt.contentRoot ∧
      left.run.receipt.activationDigest = right.run.receipt.activationDigest ∧
      left.run.receipt.contentSession = right.run.receipt.contentSession ∧
      left.run.receipt.contentEpoch = right.run.receipt.contentEpoch ∧
      left.run.receipt.playerKey = right.run.receipt.playerKey ∧
      left.run.receipt.playerCounter = right.run.receipt.playerCounter ∧
      left.relic = right.relic := by
  exact ⟨congrArg (fun key => key.receipt.federationId) equal,
    congrArg OriginKey.contentRoot equal,
    congrArg OriginKey.activationDigest equal,
    congrArg (fun key => key.receipt.contentSession) equal,
    congrArg (fun key => key.receipt.contentEpoch) equal,
    congrArg (fun key => key.receipt.playerKey) equal,
    congrArg (fun key => key.receipt.playerCounter) equal,
    congrArg OriginKey.relic equal⟩

/-- Custody keys the complete offered object, not merely its story provenance.
This prevents a caller from substituting another seller or another note sharing
the same judged run and relic. -/
structure LotKey where
  authority : Digest32
  sourceRoot : Digest32
  origin : OriginKey
  seller : ParticipantId
  note : AssetInput
deriving DecidableEq

/-- The exact missing runtime evidence at the game -> custody boundary. -/
inductive CrownBlocker where
  | runtimeCrownProofMissing
  | exactNoteProvenanceMissing
deriving DecidableEq

inductive CrownDecision where
  | observationOnly (origin : SalvageOrigin) (blocker : CrownBlocker)
  | alreadyCrowned (lot : LotKey)

/-- Inspecting an eligible discovery never mints.  The only result currently
available from this module is the exact typed blocker. -/
def inspectEligible (origin : SalvageOrigin) : CrownDecision :=
  .observationOnly origin .runtimeCrownProofMissing

theorem inspectEligible_never_crowns (origin : SalvageOrigin) :
    inspectEligible origin = .observationOnly origin .runtimeCrownProofMissing := rfl

/-- Abstract exact output of the missing upstream crown verifier.  Its private
constructor is the load-bearing boundary: this module exposes no function from
a judged relic, seller, or note to a certificate.  The claim is deliberately
narrow: it binds the exact `SalvageOrigin` value (including its archive
membership proof), seller, complete note (including nullifier), and source
root, and proves only the note's static shape.  It does *not* claim the supplied
archive is the deployment's canonical archive head or that the note is still in
live custody.  `DeploymentRegistry.initialize` separately joins the certificate
to the serialized deployment and checks exact current escrow membership. -/
structure UpstreamCrownCertificate {authorityId : Digest32}
    (authority : DeploymentAuthority authorityId)
    (origin : SalvageOrigin) (seller : ParticipantId) (note : AssetInput)
    (sourceRoot : Digest32) where
  private mk ::
  note_owner : note.owner = seller
  note_asset : note.asset = .relic origin.relic
  note_indivisible : note.amount = 1

/-- A semantic certificate for a note which an upstream crown verifier already
placed in custody.  Both its own constructor and the upstream certificate's
constructor are private. -/
structure CrownedSalvage where
  private mk ::
  authority : Digest32
  origin : SalvageOrigin
  seller : ParticipantId
  note : AssetInput
  sourceRoot : Digest32
  note_owner : note.owner = seller
  note_asset : note.asset = .relic origin.relic
  note_indivisible : note.amount = 1

/-- Sole admission seam.  It consumes a certificate indexed by the exact
authority, origin, seller and note; none of those values can be substituted. -/
def CrownedSalvage.ofUpstream {authorityId : Digest32}
    {authority : DeploymentAuthority authorityId}
    {origin : SalvageOrigin} {seller : ParticipantId} {note : AssetInput}
    {sourceRoot : Digest32}
    (certificate : UpstreamCrownCertificate authority origin seller note sourceRoot) :
    CrownedSalvage where
  authority := authorityId
  origin
  seller
  note
  sourceRoot
  note_owner := certificate.note_owner
  note_asset := certificate.note_asset
  note_indivisible := certificate.note_indivisible

inductive CrownAdmissionRefusal where
  | sellerDoesNotMatchCertificate
  | noteDoesNotMatchCertificate
  | noteOwnerMismatch
  | noteAssetMismatch
  | noteNotIndivisible
deriving DecidableEq, Repr

/-- Decoder-facing admission check for a request which repeats seller and note.
Even possession of one exact certificate cannot be reused with substituted
custody material. -/
def CrownedSalvage.admitRequested {authorityId : Digest32}
    {authority : DeploymentAuthority authorityId}
    {origin : SalvageOrigin} {seller : ParticipantId} {note : AssetInput}
    {sourceRoot : Digest32}
    (certificate : UpstreamCrownCertificate authority origin seller note sourceRoot)
    (requestedSeller : ParticipantId) (requestedNote : AssetInput) :
    Except CrownAdmissionRefusal CrownedSalvage :=
  if requestedSeller ≠ seller then .error .sellerDoesNotMatchCertificate
  else if requestedNote ≠ note then .error .noteDoesNotMatchCertificate
  else .ok (CrownedSalvage.ofUpstream certificate)

def CrownedSalvage.key (lot : CrownedSalvage) : LotKey where
  authority := lot.authority
  sourceRoot := lot.sourceRoot
  origin := lot.origin.key
  seller := lot.seller
  note := lot.note

theorem CrownedSalvage.exact_receipt_key (lot : CrownedSalvage) :
    lot.key.origin.receipt = lot.origin.run.receipt.key := rfl

theorem CrownedSalvage.exact_relic (lot : CrownedSalvage) :
    lot.key.origin.relic = lot.origin.relic := rfl

theorem CrownedSalvage.exact_seller (lot : CrownedSalvage) :
    lot.key.seller = lot.seller := rfl

theorem CrownedSalvage.exact_note (lot : CrownedSalvage) :
    lot.key.note = lot.note := rfl

theorem CrownedSalvage.exact_note_nullifier (lot : CrownedSalvage) :
    lot.key.note.nullifier = lot.note.nullifier := rfl

theorem CrownedSalvage.exact_authority (lot : CrownedSalvage) :
    lot.key.authority = lot.authority := rfl

theorem CrownedSalvage.exact_sourceRoot (lot : CrownedSalvage) :
    lot.key.sourceRoot = lot.sourceRoot := rfl

theorem CrownedSalvage.relic_was_yielded (lot : CrownedSalvage) :
    lot.key.origin.relic ∈ lot.origin.run.receipt.contribution.relics := lot.origin.yielded

theorem CrownedSalvage.origin_was_in_supplied_archive (lot : CrownedSalvage) :
    ArchiveEntry.ofJudged lot.origin.run ∈ lot.origin.archive.entries :=
  lot.origin.archived

/-- Batch identity is not caller-authored.  It is derived from the judged
content domain, the upstream crown source root, and a checked deployment
counter. -/
def CrownedSalvage.batchKey (lot : CrownedSalvage)
    (counter : PlayerCounter) : BatchKey where
  federationId := lot.origin.run.receipt.federationId
  contentSession := lot.origin.run.receipt.contentSession
  contentEpoch := lot.origin.run.receipt.contentEpoch
  batchId := ⟨counter.val⟩
  sourceRoot := lot.sourceRoot

/-! ## Inventory and authored round policy -/

/-- The player-facing custody projection.  Pairwise disjointness is stated as a
predicate so every transition can expose and preserve it. -/
structure Inventory where
  private mk ::
  maker : Finset LotKey
  taker : Finset LotKey
  escrow : Finset LotKey
deriving DecidableEq

def Inventory.WellFormed (inventory : Inventory) : Prop :=
  Disjoint inventory.maker inventory.taker ∧
    Disjoint inventory.maker inventory.escrow ∧
    Disjoint inventory.taker inventory.escrow

instance (inventory : Inventory) : Decidable inventory.WellFormed := by
  unfold Inventory.WellFormed
  infer_instance

def Inventory.singletonMaker (lot : LotKey) : Inventory where
  maker := {lot}
  taker := ∅
  escrow := ∅

theorem Inventory.singletonMaker_wellFormed (lot : LotKey) :
    (Inventory.singletonMaker lot).WellFormed := by
  simp [Inventory.singletonMaker, Inventory.WellFormed]

def Inventory.escrowLot (inventory : Inventory) (lot : LotKey) : Inventory where
  maker := inventory.maker.erase lot
  taker := inventory.taker
  escrow := insert lot inventory.escrow

def Inventory.returnLot (inventory : Inventory) (lot : LotKey) : Inventory where
  maker := insert lot inventory.maker
  taker := inventory.taker
  escrow := inventory.escrow.erase lot

def Inventory.settleLot (inventory : Inventory) (lot : LotKey) : Inventory where
  maker := inventory.maker
  taker := insert lot inventory.taker
  escrow := inventory.escrow.erase lot

theorem Inventory.escrowLot_wellFormed (inventory : Inventory) (lot : LotKey)
    (wellFormed : inventory.WellFormed) (owned : lot ∈ inventory.maker) :
    (inventory.escrowLot lot).WellFormed := by
  rcases wellFormed with ⟨makerTaker, makerEscrow, takerEscrow⟩
  rw [Inventory.WellFormed]
  constructor
  · rw [Finset.disjoint_left]
    intro item hmaker htaker
    exact (Finset.disjoint_left.mp makerTaker) (Finset.mem_erase.mp hmaker).2 htaker
  constructor
  · rw [Finset.disjoint_left]
    intro item hmaker hescrow
    rcases Finset.mem_insert.mp hescrow with equal | old
    · subst item
      exact (Finset.mem_erase.mp hmaker).1 rfl
    · exact (Finset.disjoint_left.mp makerEscrow)
        (Finset.mem_erase.mp hmaker).2 old
  · rw [Finset.disjoint_left]
    intro item htaker hescrow
    rcases Finset.mem_insert.mp hescrow with equal | old
    · subst item
      exact (Finset.disjoint_left.mp makerTaker) owned htaker
    · exact (Finset.disjoint_left.mp takerEscrow) htaker old

theorem Inventory.returnLot_wellFormed (inventory : Inventory) (lot : LotKey)
    (wellFormed : inventory.WellFormed) (escrowed : lot ∈ inventory.escrow) :
    (inventory.returnLot lot).WellFormed := by
  rcases wellFormed with ⟨makerTaker, makerEscrow, takerEscrow⟩
  rw [Inventory.WellFormed]
  constructor
  · rw [Finset.disjoint_left]
    intro item hmaker htaker
    rcases Finset.mem_insert.mp hmaker with equal | old
    · subst item
      exact (Finset.disjoint_left.mp takerEscrow) htaker escrowed
    · exact (Finset.disjoint_left.mp makerTaker) old htaker
  constructor
  · rw [Finset.disjoint_left]
    intro item hmaker hescrow
    rcases Finset.mem_insert.mp hmaker with equal | old
    · subst item
      exact (Finset.mem_erase.mp hescrow).1 rfl
    · exact (Finset.disjoint_left.mp makerEscrow) old
        (Finset.mem_erase.mp hescrow).2
  · rw [Finset.disjoint_left]
    intro item htaker hescrow
    exact (Finset.disjoint_left.mp takerEscrow) htaker
      (Finset.mem_erase.mp hescrow).2

theorem Inventory.settleLot_wellFormed (inventory : Inventory) (lot : LotKey)
    (wellFormed : inventory.WellFormed)
    (escrowed : lot ∈ inventory.escrow) :
    (inventory.settleLot lot).WellFormed := by
  rcases wellFormed with ⟨makerTaker, makerEscrow, takerEscrow⟩
  rw [Inventory.WellFormed]
  constructor
  · rw [Finset.disjoint_left]
    intro item hmaker htaker
    rcases Finset.mem_insert.mp htaker with equal | old
    · subst item
      exact (Finset.disjoint_left.mp makerEscrow) hmaker escrowed
    · exact (Finset.disjoint_left.mp makerTaker) hmaker old
  constructor
  · rw [Finset.disjoint_left]
    intro item hmaker hescrow
    exact (Finset.disjoint_left.mp makerEscrow) hmaker
      (Finset.mem_erase.mp hescrow).2
  · rw [Finset.disjoint_left]
    intro item htaker hescrow
    rcases Finset.mem_insert.mp htaker with equal | old
    · subst item
      exact (Finset.mem_erase.mp hescrow).1 rfl
    · exact (Finset.disjoint_left.mp takerEscrow) old
        (Finset.mem_erase.mp hescrow).2

structure RoundId where
  value : PlayerCounter
deriving DecidableEq, Repr

structure RoundSchedule where
  opensAt : Nat
  cancelBefore : Nat
  closesAt : Nat
  expiresAt : Nat
deriving DecidableEq, Repr

def RoundSchedule.validB (schedule : RoundSchedule) : Bool :=
  decide (schedule.opensAt < schedule.cancelBefore) &&
    decide (schedule.cancelBefore ≤ schedule.closesAt) &&
    decide (schedule.closesAt < schedule.expiresAt)

theorem RoundSchedule.validB_iff (schedule : RoundSchedule) :
    schedule.validB = true ↔
      schedule.opensAt < schedule.cancelBefore ∧
      schedule.cancelBefore ≤ schedule.closesAt ∧
      schedule.closesAt < schedule.expiresAt := by
  simp only [RoundSchedule.validB, Bool.and_eq_true, decide_eq_true_eq]
  tauto

/-- A playable schedule reserves time for the full authored envelope capacity,
then a close and settlement, and still leaves one checked counter successor at
expiry so the lot can always be returned. -/
def RoundSchedule.wireSafeB (schedule : RoundSchedule)
    (maxOrders : Nat) : Bool :=
  schedule.validB &&
    decide (schedule.opensAt + maxOrders + 1 ≤ schedule.closesAt) &&
    decide (schedule.closesAt + 2 ≤ schedule.expiresAt) &&
    decide (schedule.expiresAt < Wire.u64Max)

theorem RoundSchedule.wireSafeB_iff (schedule : RoundSchedule)
    (maxOrders : Nat) :
    schedule.wireSafeB maxOrders = true ↔
      schedule.opensAt < schedule.cancelBefore ∧
      schedule.cancelBefore ≤ schedule.closesAt ∧
      schedule.closesAt < schedule.expiresAt ∧
      schedule.opensAt + maxOrders + 1 ≤ schedule.closesAt ∧
      schedule.closesAt + 2 ≤ schedule.expiresAt ∧
      schedule.expiresAt < Wire.u64Max := by
  simp only [RoundSchedule.wireSafeB, Bool.and_eq_true,
    decide_eq_true_eq, RoundSchedule.validB_iff]
  tauto

theorem RoundSchedule.max_expiry_is_never_wire_safe
    (schedule : RoundSchedule) (maxOrders : Nat)
    (maxExpiry : schedule.expiresAt = Wire.u64Max) :
    schedule.wireSafeB maxOrders = false := by
  simp [RoundSchedule.wireSafeB, maxExpiry]

structure FeePolicy where
  listingFee : Nat
  settlementFee : Nat
deriving DecidableEq, Repr

def FeePolicy.zero : FeePolicy := ⟨0, 0⟩

def FeePolicy.supportedB (fees : FeePolicy) : Bool :=
  decide (fees.listingFee = 0 ∧ fees.settlementFee = 0)

inductive RequestedPrivacy where
  | openingAwareJudge
  | houseBlind
deriving DecidableEq, Repr

/-- Player-facing order ingress.  This kernel implements encrypted sealed
preferences.  Commit/reveal is named so clients cannot silently simulate it
with a sealed-envelope path, but remains a typed unavailable action until its
reveal/censorship semantics are authored. -/
inductive PreferenceIngress where
  | authenticatedCiphertextPendingOpening
  | v1SameOpeningBound
  | commitReveal
deriving DecidableEq, Repr

/-- Exact privacy statement the current verifier family can honestly make. -/
inductive PrivacyGrade where
  | authenticatedCiphertextOnlyNoOpeningClaim
  | commitmentsPublicOpeningVisibleToJudge
  | houseBlindUnavailable
deriving DecidableEq, Repr

def RequestedPrivacy.grade : RequestedPrivacy → PrivacyGrade
  | .openingAwareJudge => .authenticatedCiphertextOnlyNoOpeningClaim
  | .houseBlind => .houseBlindUnavailable

/-- Complete statement authenticated by the order-intake verifier.  The
signature commitment is bound to the actor, exact round/batch, nullifier, and
ciphertext commitment by the indexed authorization below. -/
structure EnvelopeStatement where
  actor : ParticipantId
  round : RoundId
  batchKey : BatchKey
  nullifier : OrderNullifier
  ciphertextCommitment : Digest32
  signatureCommitment : Digest32
deriving DecidableEq

/-- Output of the missing runtime signature verifier.  There is no producer in
this module; digest-shaped browser input cannot authenticate itself. -/
structure UpstreamEnvelopeAuthorization (statement : EnvelopeStatement) where
  private mk ::
  private authenticated : True

/-- Opaque authenticated intake metadata.  It still does not claim the
ciphertext opens to a valid order; only the later Dark Bazaar receipt can
establish a committed book and clearing. -/
structure SealedEnvelope where
  private mk ::
  statement : EnvelopeStatement
  authorization : UpstreamEnvelopeAuthorization statement
deriving DecidableEq

def SealedEnvelope.ofUpstream (statement : EnvelopeStatement)
    (authorization : UpstreamEnvelopeAuthorization statement) : SealedEnvelope :=
  ⟨statement, authorization⟩

def SealedEnvelope.actor (envelope : SealedEnvelope) : ParticipantId :=
  envelope.statement.actor

def SealedEnvelope.round (envelope : SealedEnvelope) : RoundId :=
  envelope.statement.round

def SealedEnvelope.batchKey (envelope : SealedEnvelope) : BatchKey :=
  envelope.statement.batchKey

def SealedEnvelope.nullifier (envelope : SealedEnvelope) : OrderNullifier :=
  envelope.statement.nullifier

def SealedEnvelope.ciphertextCommitment (envelope : SealedEnvelope) : Digest32 :=
  envelope.statement.ciphertextCommitment

def SealedEnvelope.signatureCommitment (envelope : SealedEnvelope) : Digest32 :=
  envelope.statement.signatureCommitment

/-- Exact V1 private order at one descriptor slot. -/
def v1OrderAt {claim : SettlementClaim} (authorization : V1.Authorization claim)
    (slot : Fin 4) : PrivateOrder where
  id := V1.orderId authorization.root slot
  order := (authorization.witness.orders slot).toLimitOrder

/-- Output of the combined authenticated-ciphertext opening verifier.  Its
indices bind the exact signed statement (therefore exact ciphertext
commitment) to one exact V1 private order.  There is no producer here. -/
structure UpstreamSameOpeningAuthorization (statement : EnvelopeStatement)
    (order : PrivateOrder) where
  private mk ::
  private authenticated : True

/-- Canonical public book identity.  The transcript is a set because duplicate
signed statements are rejected at intake; the receipt additionally proves the
four V1 slots map injectively onto it. -/
structure BookBindingKey where
  round : RoundId
  batchKey : BatchKey
  claimKey : BatchKey
  privateBookCommitment : Digest32
  transcript : Finset EnvelopeStatement
deriving DecidableEq

/-- One combined receipt: the exact V1 opening and every authenticated
ciphertext-to-order opening share the same `V1.Authorization`. -/
structure OpeningAwareBookReceipt where
  private mk ::
  claim : SettlementClaim
  authorization : V1.Authorization claim
  round : RoundId
  batchKey : BatchKey
  envelopeAt : Fin 4 → SealedEnvelope
  statementsInjective : Function.Injective
    (fun slot => (envelopeAt slot).statement)
  statementRoundExact : ∀ slot, (envelopeAt slot).round = round
  statementBatchExact : ∀ slot, (envelopeAt slot).batchKey = batchKey
  nullifierExact : ∀ slot,
    (envelopeAt slot).nullifier = (v1OrderAt authorization slot).id.nullifier
  sameOpening : ∀ slot, UpstreamSameOpeningAuthorization
    (envelopeAt slot).statement (v1OrderAt authorization slot)

def OpeningAwareBookReceipt.ofUpstream (claim : SettlementClaim)
    (authorization : V1.Authorization claim) (round : RoundId)
    (batchKey : BatchKey) (envelopeAt : Fin 4 → SealedEnvelope)
    (statementsInjective : Function.Injective
      (fun slot => (envelopeAt slot).statement))
    (statementRoundExact : ∀ slot, (envelopeAt slot).round = round)
    (statementBatchExact : ∀ slot, (envelopeAt slot).batchKey = batchKey)
    (nullifierExact : ∀ slot,
      (envelopeAt slot).nullifier = (v1OrderAt authorization slot).id.nullifier)
    (sameOpening : ∀ slot, UpstreamSameOpeningAuthorization
      (envelopeAt slot).statement (v1OrderAt authorization slot)) :
    OpeningAwareBookReceipt :=
  ⟨claim, authorization, round, batchKey, envelopeAt, statementsInjective,
    statementRoundExact, statementBatchExact, nullifierExact, sameOpening⟩

def OpeningAwareBookReceipt.transcript (receipt : OpeningAwareBookReceipt) :
    Finset EnvelopeStatement :=
  Finset.univ.image (fun slot => (receipt.envelopeAt slot).statement)

theorem OpeningAwareBookReceipt.transcript_card
    (receipt : OpeningAwareBookReceipt) : receipt.transcript.card = 4 := by
  rw [OpeningAwareBookReceipt.transcript,
    Finset.card_image_of_injective _ receipt.statementsInjective,
    Finset.card_univ, Fintype.card_fin]

def OpeningAwareBookReceipt.bindingKey (receipt : OpeningAwareBookReceipt) :
    BookBindingKey where
  round := receipt.round
  batchKey := receipt.batchKey
  claimKey := receipt.claim.spec.key
  privateBookCommitment := receipt.claim.privateBookCommitment
  transcript := receipt.transcript

inductive RoundPhase where
  | collecting
  | awaitingSettlement (binding : BookBindingKey)
deriving DecidableEq

structure Round where
  private mk ::
  id : RoundId
  lot : CrownedSalvage
  buyer : ParticipantId
  batchKey : BatchKey
  quoteAsset : AssetRef
  pricing : PriceSchedule
  schedule : RoundSchedule
  maxOrders : Nat
  maxOrderQuantity : Nat
  allowedOutputs : Finset ClearingOutput
  fees : FeePolicy
  requestedPrivacy : RequestedPrivacy
  preferenceIngress : PreferenceIngress
  phase : RoundPhase
  envelopes : Finset SealedEnvelope

def Round.orderNullifiers (round : Round) : Finset OrderNullifier :=
  round.envelopes.image SealedEnvelope.nullifier

def Round.transcript (round : Round) : Finset EnvelopeStatement :=
  round.envelopes.image SealedEnvelope.statement

def Round.privacyGrade (round : Round) : PrivacyGrade :=
  match round.requestedPrivacy, round.phase with
  | .houseBlind, _ => .houseBlindUnavailable
  | .openingAwareJudge, .collecting =>
      .authenticatedCiphertextOnlyNoOpeningClaim
  | .openingAwareJudge, .awaitingSettlement _ =>
      .commitmentsPublicOpeningVisibleToJudge

inductive CompletionKind where
  | cancelled
  | expired
  | settled (batch : BatchKey) (output : ClearingOutput)
deriving DecidableEq

structure RoundSummary where
  id : RoundId
  lot : LotKey
  quoteAsset : AssetRef
  pricing : PriceSchedule
  orderCount : Nat
  privacyGrade : PrivacyGrade
  preferenceIngress : PreferenceIngress
  kind : CompletionKind
deriving DecidableEq

/-- The complete public result of a finished clearing.  It exposes the authored
currency and uniform clearing price/volume, but has no field for preferences,
orders, openings, shares, or fills. -/
structure ClearingObservation where
  round : RoundId
  lot : LotKey
  quoteAsset : AssetRef
  bucket : Nat
  unitQuote : Nat
  volume : Nat
  totalQuote : Nat
  orderCount : Nat
  privacyGrade : PrivacyGrade
  preferenceIngress : PreferenceIngress
deriving DecidableEq

def RoundSummary.clearing? (summary : RoundSummary) : Option ClearingObservation :=
  match summary.kind with
  | .cancelled => none
  | .expired => none
  | .settled _ output => some {
      round := summary.id
      lot := summary.lot
      quoteAsset := summary.quoteAsset
      bucket := output.bucket
      unitQuote := summary.pricing.quoteAt output.bucket
      volume := output.volume
      totalQuote := summary.pricing.quoteAt output.bucket * output.volume
      orderCount := summary.orderCount
      privacyGrade := summary.privacyGrade
      preferenceIngress := summary.preferenceIngress
    }

structure BazaarGameState where
  private mk ::
  authority : Digest32
  registryRevision : PlayerCounter
  inventory : Inventory
  market : ObservableState
  current : Option Round
  history : List RoundSummary
  tick : PlayerCounter
  nextRound : PlayerCounter
  consumedOrigins : Finset OriginKey
  consumedSettlements : Finset BatchKey

structure RoundKey where
  id : RoundId
  lot : LotKey
  buyer : ParticipantId
  batchKey : BatchKey
  quoteAsset : AssetRef
  pricing : PriceSchedule
  schedule : RoundSchedule
  maxOrders : Nat
  maxOrderQuantity : Nat
  allowedOutputs : Finset ClearingOutput
  fees : FeePolicy
  requestedPrivacy : RequestedPrivacy
  preferenceIngress : PreferenceIngress
  phase : RoundPhase
  envelopes : Finset SealedEnvelope
deriving DecidableEq

def Round.key (round : Round) : RoundKey where
  id := round.id
  lot := round.lot.key
  buyer := round.buyer
  batchKey := round.batchKey
  quoteAsset := round.quoteAsset
  pricing := round.pricing
  schedule := round.schedule
  maxOrders := round.maxOrders
  maxOrderQuantity := round.maxOrderQuantity
  allowedOutputs := round.allowedOutputs
  fees := round.fees
  requestedPrivacy := round.requestedPrivacy
  preferenceIngress := round.preferenceIngress
  phase := round.phase
  envelopes := round.envelopes

/-- Exact semantic prestate carrier used by the node's canonical-head CAS.  It
contains every field any Bazaar authorization below reads or writes; it is not
a lossy digest. -/
structure StateKey where
  authority : Digest32
  registryRevision : PlayerCounter
  inventory : Inventory
  market : ObservableState
  current : Option RoundKey
  history : List RoundSummary
  tick : PlayerCounter
  nextRound : PlayerCounter
  consumedOrigins : Finset OriginKey
  consumedSettlements : Finset BatchKey
deriving DecidableEq

def BazaarGameState.key (state : BazaarGameState) : StateKey where
  authority := state.authority
  registryRevision := state.registryRevision
  inventory := state.inventory
  market := state.market
  current := state.current.map Round.key
  history := state.history
  tick := state.tick
  nextRound := state.nextRound
  consumedOrigins := state.consumedOrigins
  consumedSettlements := state.consumedSettlements

private def observeLatestClearingState (state : BazaarGameState) :
    Option ClearingObservation :=
  state.history.head?.bind RoundSummary.clearing?

structure RegistryGenesis {authorityId : Digest32}
    (_authority : DeploymentAuthority authorityId) where
  private mk ::
  private authenticated : True

structure DeploymentRegistry where
  private mk ::
  authority : Digest32
  revision : PlayerCounter
  head : Option StateKey
  consumedOrigins : Finset OriginKey

/-- Exact request the node persistence adapter must execute atomically.  The
Lean registry transition prepares these values; only the external serialized
compare-and-swap supplies cross-process exclusion. -/
structure RuntimeCasRequest where
  expected : Option StateKey
  replacement : StateKey
deriving DecidableEq

/-- An exact successor waiting for durable persistence.  It is not a live game
state: no player verb accepts this type.  Genesis is represented by
`predecessor = none`; every continuation uses `some before.key`. -/
structure PersistenceCandidate where
  private mk ::
  private predecessor : Option StateKey
  private registry : DeploymentRegistry
  private state : BazaarGameState
  private head_exact : registry.head = some state.key
  private revision_exact : registry.revision = state.registryRevision
  private authority_exact : registry.authority = state.authority

def PersistenceCandidate.request (candidate : PersistenceCandidate) :
    RuntimeCasRequest :=
  ⟨candidate.predecessor, candidate.state.key⟩

/-- Restart/load capability from the durable adapter.  Both the complete state
key and the independently threaded registry revision must agree. -/
structure UpstreamDurableLoad (registry : DeploymentRegistry)
    (state : BazaarGameState) where
  private mk ::
  head_exact : registry.head = some state.key
  revision_exact : registry.revision = state.registryRevision
  authority_exact : registry.authority = state.authority

/-- The only state accepted by canonical player commands.  Its private
constructor prevents an in-memory candidate from being used as continuation. -/
structure DurableDeployment where
  private mk ::
  private registry : DeploymentRegistry
  private state : BazaarGameState
  private head_exact : registry.head = some state.key
  private revision_exact : registry.revision = state.registryRevision
  private authority_exact : registry.authority = state.authority

def DurableDeployment.ofUpstream {registry : DeploymentRegistry}
    {state : BazaarGameState} (load : UpstreamDurableLoad registry state) :
    DurableDeployment :=
  ⟨registry, state, load.head_exact, load.revision_exact,
    load.authority_exact⟩


/-! ## Refusals and pending observation -/

inductive Refusal where
  | registryAuthorityMismatch
  | registryAlreadyInitialized
  | registryNotInitialized
  | registryRevisionExhausted
  | staleCanonicalHead
  | proposalPrestateMismatch
  | proposalRevisionMismatch
  | wrongAuthority
  | initialMarketMismatch
  | unboundedOriginCounter
  | clockExhausted
  | activeRoundRequiresExpiry
  | roundCounterExhausted
  | openTickMismatch
  | invalidSchedule
  | scheduleNotWireSafe
  | unsupportedOrderBound
  | unsupportedV1MarketShape
  | roundAlreadyOpen
  | malformedInventory
  | originNotAdmitted
  | lotNotMakerOwned
  | lotNotEscrowed
  | authoredMarketMismatch
  | nonzeroListingFeeNeedsConservingReceipt
  | nonzeroSettlementFeeNeedsConservingReceipt
  | noOpenRound
  | wrongPhase
  | outsideCollectionWindow
  | envelopeActorMismatch
  | envelopeRoundMismatch
  | envelopeBatchMismatch
  | duplicateOrderNullifier
  | orderNullifierAlreadyConsumed
  | orderCapacityReached
  | cancellationClosed
  | ordersAlreadySubmitted
  | closeTooEarly
  | emptyBook
  | bookOpeningReceiptMismatch
  | notExpired
  | settlementWindowClosed
  | houseBlindProofUnavailable
  | commitRevealUnavailable
  | receiptDoesNotMatchRound
  | settlementAlreadyConsumed
deriving DecidableEq, Repr

/-- Pure specification of the required persistence adapter.  Production code
must implement this as one atomic compare-and-swap over the serialized head,
not as a read followed by a write. -/
def runtimeCas (persisted : Option StateKey) (request : RuntimeCasRequest) :
    Except Refusal (Option StateKey) :=
  if persisted ≠ request.expected then .error .staleCanonicalHead
  else .ok (some request.replacement)

/-- Opaque, proof-carrying output of the durable store.  Its index is the exact
full-state CAS request (including the registry revision embedded in `StateKey`).
There is deliberately no producer in this module: only the serialized runtime
adapter may return one after its atomic write succeeds. -/
structure SuccessfulPersistence (request : RuntimeCasRequest) where
  private mk ::
  observedBefore : Option StateKey
  observedAfter : Option StateKey
  expected_exact : observedBefore = request.expected
  applied_exact : runtimeCas observedBefore request = .ok observedAfter
  replacement_exact : observedAfter = some request.replacement

/-- A candidate becomes usable only after a successful persistence receipt
indexed by its exact optional predecessor and exact full replacement key. -/
def PersistenceCandidate.continue (candidate : PersistenceCandidate)
    (_receipt : SuccessfulPersistence candidate.request) : DurableDeployment :=
  ⟨candidate.registry, candidate.state, candidate.head_exact,
    candidate.revision_exact, candidate.authority_exact⟩

theorem SuccessfulPersistence.exact_cas {request : RuntimeCasRequest}
    (receipt : SuccessfulPersistence request) :
    runtimeCas request.expected request =
      .ok (some request.replacement) := by
  calc
    runtimeCas request.expected request =
        runtimeCas receipt.observedBefore request := by
          rw [receipt.expected_exact]
    _ = .ok receipt.observedAfter := receipt.applied_exact
    _ = .ok (some request.replacement) := by
      rw [receipt.replacement_exact]

def RuntimeCasRequest.ofRegistries (before after : DeploymentRegistry) :
    Except Refusal RuntimeCasRequest :=
  match after.head with
  | some replacement => .ok ⟨before.head, replacement⟩
  | none => .error .registryNotInitialized

/-- Two locally valid forks can name the same old head, but after one request
wins the serialized CAS the other request is rejected.  This theorem is the
runtime half intentionally absent from immutable registry values themselves. -/
theorem runtimeCas_same_old_fork_has_one_winner
    (old firstNext secondNext : StateKey) (changed : firstNext ≠ old) :
    let first : RuntimeCasRequest := ⟨some old, firstNext⟩
    let second : RuntimeCasRequest := ⟨some old, secondNext⟩
    runtimeCas (some old) first = .ok (some firstNext) ∧
      runtimeCas (some firstNext) second = .error .staleCanonicalHead := by
  simp [runtimeCas, changed]

theorem runtimeCas_genesis_is_explicit (replacement : StateKey) :
    runtimeCas none ⟨none, replacement⟩ = .ok (some replacement) := by
  simp [runtimeCas]

/-! ## Sealed trusted-runtime provisioning portal -/

/-- These admissions are concrete opaque runtime results, not caller-selected
typeclass families.  Every constructor and payload is private.  The only
producers are the `@[extern] opaque` operations in `TrustedRuntimePortal`, whose
runtime implementations must perform the named verification or atomic effect
before returning `some`. -/
structure AuthorityAdmission (id : Digest32) where
  private mk ::
  private token : Unit

structure GenesisAdmission {id : Digest32}
    (authority : DeploymentAuthority id) where
  private mk ::
  private token : Unit

structure DurableLoadAdmission (registry : DeploymentRegistry)
    (state : BazaarGameState) where
  private mk ::
  private token : Unit

structure PersistenceAdmission (request : RuntimeCasRequest) where
  private mk ::
  private token : Unit

structure EnvelopeAdmission (statement : EnvelopeStatement) where
  private mk ::
  private token : Unit

structure SameOpeningAdmission (statement : EnvelopeStatement)
    (order : PrivateOrder) where
  private mk ::
  private token : Unit

structure CrownAdmission {id : Digest32}
    (authority : DeploymentAuthority id) (origin : SalvageOrigin)
    (seller : ParticipantId) (note : AssetInput) (sourceRoot : Digest32) where
  private mk ::
  private token : Unit

structure TrustedInitialization (id : Digest32) where
  private mk ::
  authority : DeploymentAuthority id
  genesis : RegistryGenesis authority

namespace TrustedRuntimePortal

/-- Authenticate the deployment-control credential carried by `wire`. -/
@[extern "dregg_poa_bazaar_admit_authority"]
opaque admitAuthority (id : Digest32) (wire : ByteArray) :
  IO (Option (AuthorityAdmission id))

/-- Authenticate/provision the empty durable registry for this exact authority. -/
@[extern "dregg_poa_bazaar_admit_genesis"]
opaque admitGenesis {id : Digest32} (authority : DeploymentAuthority id)
    (wire : ByteArray) : IO (Option (GenesisAdmission authority))

/-- Admit one exact decoded durable image after the store has authenticated it. -/
@[extern "dregg_poa_bazaar_admit_durable_load"]
opaque admitDurableLoad (registry : DeploymentRegistry) (state : BazaarGameState)
    (wire : ByteArray) : IO (Option (DurableLoadAdmission registry state))

/-- Execute the exact request as one atomic durable compare-and-swap. -/
@[extern "dregg_poa_bazaar_perform_cas"]
opaque performCas (request : RuntimeCasRequest) :
  IO (Option (PersistenceAdmission request))

/-- Verify the exact signed envelope statement against its wire evidence. -/
@[extern "dregg_poa_bazaar_admit_envelope"]
opaque admitEnvelope (statement : EnvelopeStatement) (wire : ByteArray) :
  IO (Option (EnvelopeAdmission statement))

/-- Verify that this exact ciphertext statement opens to this exact V1 order. -/
@[extern "dregg_poa_bazaar_admit_same_opening"]
opaque admitSameOpening (statement : EnvelopeStatement) (order : PrivateOrder)
    (wire : ByteArray) : IO (Option (SameOpeningAdmission statement order))

/-- Verify crown/provenance evidence for the exact custody tuple. -/
@[extern "dregg_poa_bazaar_admit_crown"]
opaque admitCrown {id : Digest32} (authority : DeploymentAuthority id)
    (origin : SalvageOrigin) (seller : ParticipantId) (note : AssetInput)
    (sourceRoot : Digest32) (wire : ByteArray) :
    IO (Option (CrownAdmission authority origin seller note sourceRoot))

def provisionAuthority (id : Digest32)
    (_receipt : AuthorityAdmission id) : DeploymentAuthority id :=
  ⟨True.intro⟩

def provisionGenesis {id : Digest32}
    (authority : DeploymentAuthority id)
    (_receipt : GenesisAdmission authority) : RegistryGenesis authority :=
  ⟨True.intro⟩

/-- One source-level initializer portal: the runtime presents its two opaque
receipts and receives the dependent authority/genesis pair without either
private constructor becoming public. -/
def provisionInitialization (id : Digest32)
    (authorityReceipt : AuthorityAdmission id)
    (genesisReceipt : GenesisAdmission
      (provisionAuthority id authorityReceipt)) : TrustedInitialization id :=
  let authority := provisionAuthority id authorityReceipt
  ⟨authority, provisionGenesis authority genesisReceipt⟩

def authorizeEnvelope
    (statement : EnvelopeStatement)
    (_receipt : EnvelopeAdmission statement) :
    UpstreamEnvelopeAuthorization statement :=
  ⟨True.intro⟩

def authorizeSameOpening
    (statement : EnvelopeStatement) (order : PrivateOrder)
    (_receipt : SameOpeningAdmission statement order) :
    UpstreamSameOpeningAuthorization statement order :=
  ⟨True.intro⟩

def confirmDurableLoad
    (registry : DeploymentRegistry) (state : BazaarGameState)
    (_receipt : DurableLoadAdmission registry state)
    (headExact : registry.head = some state.key)
    (revisionExact : registry.revision = state.registryRevision)
    (authorityExact : registry.authority = state.authority) :
    UpstreamDurableLoad registry state :=
  ⟨headExact, revisionExact, authorityExact⟩

def confirmPersistence
    (request : RuntimeCasRequest)
    (_receipt : PersistenceAdmission request) :
    SuccessfulPersistence request where
  observedBefore := request.expected
  observedAfter := some request.replacement
  expected_exact := rfl
  applied_exact := by simp [runtimeCas]
  replacement_exact := rfl

theorem confirmPersistence_exact
    (request : RuntimeCasRequest)
    (receipt : PersistenceAdmission request) :
    runtimeCas request.expected request = .ok (some request.replacement) :=
  (confirmPersistence request receipt).exact_cas

theorem authorizeSameOpening_exact
    (statement : EnvelopeStatement) (order : PrivateOrder)
    (receipt : SameOpeningAdmission statement order) :
    Nonempty (UpstreamSameOpeningAuthorization statement order) :=
⟨authorizeSameOpening statement order receipt⟩

/-- Complete crown provisioning after the opaque runtime verified the exact
tuple.  Static note shape is still rechecked in Lean before the private crown
certificate and `CrownedSalvage` are constructed. -/
def provisionCrownedSalvage {id : Digest32}
    (authority : DeploymentAuthority id) (origin : SalvageOrigin)
    (seller : ParticipantId) (note : AssetInput) (sourceRoot : Digest32)
    (_receipt : CrownAdmission authority origin seller note sourceRoot) :
    Except CrownAdmissionRefusal CrownedSalvage :=
  if howner : note.owner = seller then
    if hasset : note.asset = .relic origin.relic then
      if hamount : note.amount = 1 then
        let certificate : UpstreamCrownCertificate authority origin seller note sourceRoot :=
          ⟨howner, hasset, hamount⟩
        .ok (CrownedSalvage.ofUpstream certificate)
      else .error .noteNotIndivisible
    else .error .noteAssetMismatch
  else .error .noteOwnerMismatch

theorem provisionCrownedSalvage_success_exact {id : Digest32}
    (authority : DeploymentAuthority id) (origin : SalvageOrigin)
    (seller : ParticipantId) (note : AssetInput) (sourceRoot : Digest32)
    (receipt : CrownAdmission authority origin seller note sourceRoot)
    (lot : CrownedSalvage)
    (success : provisionCrownedSalvage authority origin seller note sourceRoot receipt =
      .ok lot) :
    lot.authority = id ∧ lot.origin = origin ∧ lot.seller = seller ∧
      lot.note = note ∧ lot.sourceRoot = sourceRoot := by
  unfold provisionCrownedSalvage at success
  split at success <;> try contradiction
  split at success <;> try contradiction
  split at success <;> try contradiction
  simp only [Except.ok.injEq] at success
  subst lot
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end TrustedRuntimePortal

/-- The only market policy the currently implemented Dark Bazaar V1 checker
can authorize.  This gate is repeated at initialization and round opening so a
future loaded state cannot silently widen the proof family. -/
def v1MarketPolicyB (policy : MarketPolicy) : Bool :=
  decide policy.WireBounded &&
    decide (policy.pricing.buckets =
      Market.DarkBazaarPrivateDescriptor.PRICE_COUNT) &&
    decide (policy.maxOrders =
      Market.DarkBazaarPrivateDescriptor.ORDER_COUNT) &&
    decide (policy.maxOrderQuantity = 15)

theorem v1MarketPolicyB_iff (policy : MarketPolicy) :
    v1MarketPolicyB policy = true ↔
      policy.WireBounded ∧
      policy.pricing.buckets =
        Market.DarkBazaarPrivateDescriptor.PRICE_COUNT ∧
      policy.maxOrders = Market.DarkBazaarPrivateDescriptor.ORDER_COUNT ∧
      policy.maxOrderQuantity = 15 := by
  simp only [v1MarketPolicyB, Bool.and_eq_true, decide_eq_true_eq]
  tauto

def observableV1MarketShapeB (market : ObservableState) : Bool :=
  decide market.identity.WireBounded &&
    v1MarketPolicyB market.policy &&
    decide (market.baseEscrowNotes.filter AssetInput.WireBounded =
      market.baseEscrowNotes) &&
    decide (market.quoteEscrowNotes.filter AssetInput.WireBounded =
      market.quoteEscrowNotes) &&
    decide (market.baseEscrow ≤ Wire.u64Max) &&
    decide (market.quoteEscrow ≤ Wire.u64Max) &&
    decide (market.buyerBaseCustody ≤ Wire.maxCustodyBalance) &&
    decide (market.sellerQuoteCustody ≤ Wire.maxCustodyBalance) &&
    decide (market.consumedBatches.filter BatchKey.WireBounded =
      market.consumedBatches)

theorem observableV1MarketShapeB_requires_v1_policy
    (market : ObservableState)
    (accepted : observableV1MarketShapeB market = true) :
    v1MarketPolicyB market.policy = true := by
  simp only [observableV1MarketShapeB, Bool.and_eq_true,
    decide_eq_true_eq] at accepted
  tauto

def initializationMatchesB (authorityId : Digest32)
    (lot : CrownedSalvage) (market : BazaarState) : Bool :=
  decide market.WireBounded &&
    v1MarketPolicyB market.policy &&
    decide (lot.authority = authorityId) &&
    decide (market.identity.federationId = lot.origin.run.receipt.federationId) &&
    decide (market.identity.contentRoot = lot.origin.run.receipt.contentRoot) &&
    decide (market.identity.activationDigest = lot.origin.run.receipt.activationDigest) &&
    decide (market.identity.contentSession = lot.origin.run.receipt.contentSession) &&
    decide (market.identity.contentEpoch = lot.origin.run.receipt.contentEpoch) &&
    decide (market.identity.seller = lot.seller) &&
    decide (market.identity.baseAsset = .relic lot.origin.relic) &&
    decide (lot.note ∈ market.baseEscrow.notes) &&
    decide (lot.note.nullifier ∉ market.consumedAssetNullifiers)

theorem initializationMatchesB_requires_current_v1
    (authorityId : Digest32) (lot : CrownedSalvage) (market : BazaarState)
    (accepted : initializationMatchesB authorityId lot market = true) :
    market.WireBounded ∧ v1MarketPolicyB market.policy = true := by
  simp only [initializationMatchesB, Bool.and_eq_true,
    decide_eq_true_eq] at accepted
  tauto

private def zeroPlayerCounter : PlayerCounter := ⟨0, by decide⟩

/-- Open the deployment registry from an externally provisioned genesis
capability.  The value is a semantic model of the serialized node record, not a
linear token: the node must persist each accepted successor with compare-and-
swap on `head`. -/
def DeploymentRegistry.open {authorityId : Digest32}
    {authority : DeploymentAuthority authorityId}
    (_genesis : RegistryGenesis authority) : DeploymentRegistry where
  authority := authorityId
  revision := zeroPlayerCounter
  head := none
  consumedOrigins := ∅

/-- The only state initializer.  It emits a genesis persistence candidate with
an explicit `none` predecessor.  The returned state cannot drive a command
until `PersistenceCandidate.continue` consumes a successful genesis CAS
receipt. -/
def DeploymentRegistry.initialize {authorityId : Digest32}
    (_authority : DeploymentAuthority authorityId)
    (registry : DeploymentRegistry)
    (lot : CrownedSalvage) (market : BazaarState) :
    Except Refusal PersistenceCandidate :=
  if registry.authority ≠ authorityId then .error .registryAuthorityMismatch
  else if registry.head.isSome then .error .registryAlreadyInitialized
  else if lot.origin.key ∈ registry.consumedOrigins then .error .originNotAdmitted
  else if lot.authority ≠ authorityId then .error .wrongAuthority
  else if decide market.WireBounded ≠ true ∨
      v1MarketPolicyB market.policy ≠ true then
    .error .unsupportedV1MarketShape
  else if initializationMatchesB authorityId lot market ≠ true then
    .error .initialMarketMismatch
  else match checkedPlayerCounter lot.origin.run.receipt.playerCounter with
    | none => .error .unboundedOriginCounter
    | some counter => match registry.revision.next with
      | none => .error .registryRevisionExhausted
      | some nextRevision =>
        let state : BazaarGameState := {
          authority := authorityId
          registryRevision := nextRevision
          inventory := Inventory.singletonMaker lot.key
          market := observeState market
          current := none
          history := []
          tick := zeroPlayerCounter
          nextRound := counter
          consumedOrigins := {lot.origin.key}
          consumedSettlements := ∅
        }
        let nextRegistry : DeploymentRegistry := {
          authority := authorityId
          revision := nextRevision
          head := some state.key
          consumedOrigins := insert lot.origin.key registry.consumedOrigins
        }
        .ok {
          predecessor := none
          registry := nextRegistry
          state
          head_exact := rfl
          revision_exact := rfl
          authority_exact := rfl
        }

/-- Turn a pure semantic successor into an exact persistence candidate.  This
function advances the registry revision in the candidate but returns no live
state; only a later indexed `SuccessfulPersistence` can continue it. -/
private def preparePersistence (live : DurableDeployment)
    (result : Except Refusal BazaarGameState) :
    Except Refusal PersistenceCandidate :=
  match result with
  | .error refusal => .error refusal
  | .ok candidate =>
      if hAuthority : candidate.authority ≠ live.registry.authority then
        .error .registryAuthorityMismatch
      else if candidate.registryRevision ≠ live.state.registryRevision then
        .error .proposalRevisionMismatch
      else match live.registry.revision.next with
        | none => .error .registryRevisionExhausted
        | some nextRevision =>
          let accepted : BazaarGameState := {
            candidate with registryRevision := nextRevision
          }
          let nextRegistry : DeploymentRegistry := {
            live.registry with
            revision := nextRevision
            head := some accepted.key
            consumedOrigins := accepted.consumedOrigins
          }
          .ok {
            predecessor := some live.state.key
            registry := nextRegistry
            state := accepted
            head_exact := rfl
            revision_exact := rfl
            authority_exact := by
              simp only [nextRegistry, accepted]
              exact (of_not_not hAuthority).symm
          }

/-- Every command candidate is indexed by the exact durable state from which
it was proposed.  A receipt for any other predecessor cannot inhabit the
dependent continuation argument. -/
private theorem preparePersistence_success_expected_exact
    (live : DurableDeployment) (result : Except Refusal BazaarGameState)
    (candidate : PersistenceCandidate)
    (success : preparePersistence live result = .ok candidate) :
    candidate.request.expected = some live.state.key := by
  unfold preparePersistence at success
  cases result with
  | error refusal => simp at success
  | ok proposed =>
      dsimp only at success
      split at success
      · contradiction
      split at success
      · contradiction
      split at success
      · contradiction
      · simp only [Except.ok.injEq] at success
        subst candidate
        rfl

theorem PersistenceCandidate.continuation_replacement_exact
    (candidate : PersistenceCandidate)
    (receipt : SuccessfulPersistence candidate.request) :
    (candidate.continue receipt).state.key = candidate.request.replacement := by
  rfl

theorem PersistenceCandidate.continuation_revision_exact
    (candidate : PersistenceCandidate)
    (receipt : SuccessfulPersistence candidate.request) :
    (candidate.continue receipt).registry.revision =
      (candidate.continue receipt).state.registryRevision :=
  candidate.revision_exact

private def authorizedNextTick {authorityId : Digest32}
    (_authority : DeploymentAuthority authorityId)
    (state : BazaarGameState) : Except Refusal PlayerCounter :=
  if authorityId ≠ state.authority then .error .wrongAuthority
  else match state.tick.next with
    | none => .error .clockExhausted
    | some next => .ok next

/-- An authority can advance only the private state's canonical clock by one
checked u64 step.  There is no caller-supplied `Nat` timestamp. -/
private def proposeAdvanceClock {authorityId : Digest32}
    (_authority : DeploymentAuthority authorityId)
    (state : BazaarGameState) : Except Refusal BazaarGameState :=
  if authorityId ≠ state.authority then .error .wrongAuthority
  else match state.current with
    | some round =>
        if round.schedule.expiresAt ≤ state.tick.val then
          .error .activeRoundRequiresExpiry
        else match state.tick.next with
          | none => .error .clockExhausted
          | some next => .ok { state with tick := next }
    | none => match state.tick.next with
      | none => .error .clockExhausted
      | some next => .ok { state with tick := next }

/-- Once an active round reaches its expiry, the general clock verb cannot
consume the successor reserved for custody return.  This check precedes the
counter-successor lookup, so it also refuses a hostile loaded max-u64 state by
the recovery-specific reason rather than silently reporting ordinary clock
exhaustion. -/
private theorem advanceClock_active_at_or_after_expiry_refused
    {authorityId : Digest32} (authority : DeploymentAuthority authorityId)
    (state : BazaarGameState) (round : Round)
    (authorityExact : authorityId = state.authority)
    (current : state.current = some round)
    (expired : round.schedule.expiresAt ≤ state.tick.val) :
    proposeAdvanceClock authority state = .error .activeRoundRequiresExpiry := by
  simp [proposeAdvanceClock, authorityExact, current, expired]

private theorem wireSafe_expiry_has_tick_successor
    (state : BazaarGameState) (round : Round)
    (wireSafe : round.schedule.wireSafeB round.maxOrders = true)
    (atExpiry : state.tick.val = round.schedule.expiresAt) :
    ∃ next : PlayerCounter, state.tick.next = some next := by
  have expiryLt : round.schedule.expiresAt < Wire.u64Max :=
    (RoundSchedule.wireSafeB_iff round.schedule round.maxOrders).mp wireSafe |>.2.2.2.2.2
  have maxSucc : Wire.u64Max + 1 = PLAYER_COUNTER_MODULUS := by
    norm_num [Wire.u64Max, PLAYER_COUNTER_MODULUS]
  have successorLt : state.tick.val + 1 < PLAYER_COUNTER_MODULUS := by
    omega
  exact ⟨⟨state.tick.val + 1, successorLt⟩, by
    simp [PlayerCounter.next, checkedPlayerCounter, successorLt]⟩

inductive PendingStatus where
  | collecting
  | awaitingOpeningAwareJudge
deriving DecidableEq, Repr

inductive EnvelopeBindingStatus where
  | signatureVerifiedSameOpeningEncryptionProofMissing
  | v1CiphertextsBoundToExactPrivateOrders
deriving DecidableEq, Repr

structure PendingObservation where
  round : RoundId
  lot : LotKey
  orderCount : Nat
  closesAt : Nat
  expiresAt : Nat
  status : PendingStatus
  privacyGrade : PrivacyGrade
  preferenceIngress : PreferenceIngress
  envelopeBinding : EnvelopeBindingStatus
deriving DecidableEq

private def observePendingState (state : BazaarGameState) :
    Option PendingObservation := do
  let round ← state.current
  let status := match round.phase, round.requestedPrivacy with
    | .collecting, _ => PendingStatus.collecting
    | .awaitingSettlement _, .openingAwareJudge => .awaitingOpeningAwareJudge
    | .awaitingSettlement _, .houseBlind => .collecting
  let envelopeBinding := match round.phase with
    | .collecting =>
        EnvelopeBindingStatus.signatureVerifiedSameOpeningEncryptionProofMissing
    | .awaitingSettlement _ => .v1CiphertextsBoundToExactPrivateOrders
  some {
    round := round.id
    lot := round.lot.key
    orderCount := round.envelopes.card
    closesAt := round.schedule.closesAt
    expiresAt := round.schedule.expiresAt
    status
    privacyGrade := round.privacyGrade
    preferenceIngress := round.preferenceIngress
    envelopeBinding
  }

/-- Public observation is deliberately rooted in a receipt-backed durable
deployment; no raw candidate-state observer is exported. -/
def DurableDeployment.observePending (live : DurableDeployment) :
    Option PendingObservation :=
  observePendingState live.state

def DurableDeployment.observeLatestClearing (live : DurableDeployment) :
    Option ClearingObservation :=
  observeLatestClearingState live.state

def DurableDeployment.key (live : DurableDeployment) : StateKey :=
  live.state.key

def DurableDeployment.clock (live : DurableDeployment) : Nat :=
  live.state.tick.val

/-! ## Player verbs before settlement -/

/-- The authored market already fixes the counterparty, currencies, pricing,
quantity bound, order bound, and allowed public clearing outcomes.  Opening a
round may repeat the compact player-facing coordinates, but cannot alter them. -/
def authoredRoundMatchesB (lot : CrownedSalvage) (buyer : ParticipantId)
    (quoteAsset : AssetRef) (maxOrders : Nat) (state : BazaarGameState) : Bool :=
  decide (state.market.identity.seller = lot.seller) &&
    decide (state.market.identity.buyer = buyer) &&
    decide (state.market.identity.baseAsset = .relic lot.origin.relic) &&
    decide (state.market.identity.quoteAsset = quoteAsset) &&
    decide (state.market.policy.maxOrders = maxOrders)

theorem authoredRoundMatchesB_iff (lot : CrownedSalvage) (buyer : ParticipantId)
    (quoteAsset : AssetRef) (maxOrders : Nat) (state : BazaarGameState) :
    authoredRoundMatchesB lot buyer quoteAsset maxOrders state = true ↔
      state.market.identity.seller = lot.seller ∧
      state.market.identity.buyer = buyer ∧
      state.market.identity.baseAsset = .relic lot.origin.relic ∧
      state.market.identity.quoteAsset = quoteAsset ∧
      state.market.policy.maxOrders = maxOrders := by
  simp only [authoredRoundMatchesB, Bool.and_eq_true, decide_eq_true_eq]
  tauto

private def proposeOpenRound {authorityId : Digest32}
    (authority : DeploymentAuthority authorityId) (lot : CrownedSalvage)
    (buyer : ParticipantId) (quoteAsset : AssetRef) (schedule : RoundSchedule)
    (maxOrders : Nat) (fees : FeePolicy) (privacy : RequestedPrivacy)
    (state : BazaarGameState) : Except Refusal BazaarGameState :=
  match authorizedNextTick authority state with
  | .error refusal => .error refusal
  | .ok nextTick => match state.nextRound.next with
    | none => .error .roundCounterExhausted
    | some nextRound =>
      if privacy = .houseBlind then .error .houseBlindProofUnavailable
      else if maxOrders = 0 ∨ MAX_ROUND_ORDERS < maxOrders then .error .unsupportedOrderBound
      else if schedule.validB ≠ true then .error .invalidSchedule
      else if schedule.wireSafeB maxOrders ≠ true then .error .scheduleNotWireSafe
      else if observableV1MarketShapeB state.market ≠ true then
        .error .unsupportedV1MarketShape
      else if state.current.isSome then .error .roundAlreadyOpen
      else if state.tick.val ≠ schedule.opensAt then .error .openTickMismatch
      else if ¬ state.inventory.WellFormed then .error .malformedInventory
      else if lot.authority ≠ authorityId ∨ lot.origin.key ∉ state.consumedOrigins then
        .error .originNotAdmitted
      else if lot.key ∉ state.inventory.maker then .error .lotNotMakerOwned
      else if authoredRoundMatchesB lot buyer quoteAsset maxOrders state ≠ true then
        .error .authoredMarketMismatch
      else if fees.listingFee ≠ 0 then .error .nonzeroListingFeeNeedsConservingReceipt
      else if fees.settlementFee ≠ 0 then .error .nonzeroSettlementFeeNeedsConservingReceipt
      else .ok {
        state with
        inventory := state.inventory.escrowLot lot.key
        current := some {
          id := ⟨state.nextRound⟩
          lot
          buyer
          batchKey := lot.batchKey state.nextRound
          quoteAsset
          pricing := state.market.policy.pricing
          schedule
          maxOrders
          maxOrderQuantity := state.market.policy.maxOrderQuantity
          allowedOutputs := state.market.policy.allowedOutputs
          fees
          requestedPrivacy := privacy
          preferenceIngress := .authenticatedCiphertextPendingOpening
          phase := .collecting
          envelopes := ∅
        }
        tick := nextTick
        nextRound
      }

/-- Preferred playable opening: derive every economic coordinate from the
authored market instead of accepting caller-selected buyer/currency/bounds. -/
private def proposeOpenAuthoredRound {authorityId : Digest32}
    (authority : DeploymentAuthority authorityId) (lot : CrownedSalvage)
    (schedule : RoundSchedule) (fees : FeePolicy) (privacy : RequestedPrivacy)
    (state : BazaarGameState) : Except Refusal BazaarGameState :=
  proposeOpenRound authority lot state.market.identity.buyer
    state.market.identity.quoteAsset schedule state.market.policy.maxOrders fees privacy state

/-- Commit/reveal is a distinct future protocol, not a UI alias for sealed
preferences.  Refusal occurs before any custody or clock transition. -/
private def proposeOpenCommitRevealRound {authorityId : Digest32}
    (_authority : DeploymentAuthority authorityId) (state : BazaarGameState) :
    Except Refusal BazaarGameState :=
  if authorityId ≠ state.authority then .error .wrongAuthority
  else .error .commitRevealUnavailable

/-- Hostile near-counter-exhaustion schedule: even with otherwise executable
authority/counter inputs, `expiresAt = u64Max` refuses before inventory is
inspected or moved, so it cannot create permanent escrow. -/
private theorem max_expiry_refused_before_custody_lock
    {authorityId : Digest32} (authority : DeploymentAuthority authorityId)
    (lot : CrownedSalvage) (buyer : ParticipantId) (quoteAsset : AssetRef)
    (schedule : RoundSchedule) (maxOrders : Nat) (fees : FeePolicy)
    (privacy : RequestedPrivacy) (state : BazaarGameState)
    (nextTick nextRound : PlayerCounter)
    (authorityExact : authorityId = state.authority)
    (nextTickExact : state.tick.next = some nextTick)
    (nextRoundExact : state.nextRound.next = some nextRound)
    (privacySupported : privacy ≠ .houseBlind)
    (orderBound : ¬ (maxOrders = 0 ∨ MAX_ROUND_ORDERS < maxOrders))
    (scheduleValid : schedule.validB = true)
    (maxExpiry : schedule.expiresAt = Wire.u64Max) :
    proposeOpenRound authority lot buyer quoteAsset schedule maxOrders fees privacy state =
      .error .scheduleNotWireSafe := by
  have hUnsafe := schedule.max_expiry_is_never_wire_safe maxOrders maxExpiry
  simp [proposeOpenRound, authorizedNextTick, authorityExact, nextTickExact,
    nextRoundExact, privacySupported, orderBound, scheduleValid, hUnsafe]

private theorem openRound_success_moves_lot_to_escrow
    {authorityId : Digest32} {authority : DeploymentAuthority authorityId}
    {lot : CrownedSalvage} {buyer : ParticipantId}
    {quoteAsset : AssetRef} {schedule : RoundSchedule} {maxOrders : Nat}
    {fees : FeePolicy} {privacy : RequestedPrivacy}
    {before after : BazaarGameState}
    (h : proposeOpenRound authority lot buyer quoteAsset schedule maxOrders fees privacy before = .ok after) :
    lot.key ∉ after.inventory.maker ∧ lot.key ∈ after.inventory.escrow := by
  unfold proposeOpenRound at h
  cases htick : authorizedNextTick authority before with
  | error refusal => simp [htick] at h
  | ok nextTick =>
    rw [htick] at h
    dsimp only at h
    cases hcounter : before.nextRound.next with
    | none => simp [hcounter] at h
    | some nextRound =>
      rw [hcounter] at h
      dsimp only at h
      by_cases c1 : privacy = .houseBlind
      · simp [c1] at h
      simp only [c1, if_false] at h
      by_cases c2 : maxOrders = 0 ∨ MAX_ROUND_ORDERS < maxOrders
      · simp [c2] at h
      simp only [c2, if_false] at h
      by_cases c3 : schedule.validB ≠ true
      · simp [c3] at h
      simp only [c3, if_false] at h
      by_cases c4 : schedule.wireSafeB maxOrders ≠ true
      · simp [c4] at h
      simp only [c4, if_false] at h
      by_cases c5 : observableV1MarketShapeB before.market ≠ true
      · simp [c5] at h
      simp only [c5, if_false] at h
      by_cases c6 : before.current.isSome = true
      · simp [c6] at h
      have c6' : before.current.isSome = false := Bool.eq_false_of_not_eq_true c6
      simp only [c6', Bool.false_eq_true, if_false] at h
      by_cases c7 : before.tick.val ≠ schedule.opensAt
      · simp [c7] at h
      simp only [c7, if_false] at h
      by_cases c8 : ¬ before.inventory.WellFormed
      · simp [c8] at h
      simp only [c8, if_false] at h
      by_cases c9 : lot.authority ≠ authorityId ∨
          lot.origin.key ∉ before.consumedOrigins
      · simp [c9] at h
      simp only [c9, if_false] at h
      by_cases c10 : lot.key ∉ before.inventory.maker
      · simp [c10] at h
      simp only [c10, if_false] at h
      by_cases c11 : authoredRoundMatchesB lot buyer quoteAsset maxOrders before ≠ true
      · simp [c11] at h
      simp only [c11, if_false] at h
      by_cases c12 : fees.listingFee ≠ 0
      · simp [c12] at h
      simp only [c12, if_false] at h
      by_cases c13 : fees.settlementFee ≠ 0
      · simp [c13] at h
      simp only [c13, if_false, Except.ok.injEq] at h
      subst after
      exact ⟨fun member => (Finset.mem_erase.mp member).1 rfl,
        Finset.mem_insert_self lot.key before.inventory.escrow⟩

private theorem openRound_success_requires_maker
    {authorityId : Digest32} {authority : DeploymentAuthority authorityId}
    {lot : CrownedSalvage} {buyer : ParticipantId}
    {quoteAsset : AssetRef} {schedule : RoundSchedule} {maxOrders : Nat}
    {fees : FeePolicy} {privacy : RequestedPrivacy}
    {before after : BazaarGameState}
    (h : proposeOpenRound authority lot buyer quoteAsset schedule maxOrders fees privacy before = .ok after) :
    lot.key ∈ before.inventory.maker := by
  unfold proposeOpenRound at h
  cases htick : authorizedNextTick authority before with
  | error refusal => simp [htick] at h
  | ok nextTick =>
    rw [htick] at h
    dsimp only at h
    cases hcounter : before.nextRound.next with
    | none => simp [hcounter] at h
    | some nextRound =>
      rw [hcounter] at h
      dsimp only at h
      by_cases c1 : privacy = .houseBlind
      · simp [c1] at h
      simp only [c1, if_false] at h
      by_cases c2 : maxOrders = 0 ∨ MAX_ROUND_ORDERS < maxOrders
      · simp [c2] at h
      simp only [c2, if_false] at h
      by_cases c3 : schedule.validB ≠ true
      · simp [c3] at h
      simp only [c3, if_false] at h
      by_cases c4 : schedule.wireSafeB maxOrders ≠ true
      · simp [c4] at h
      simp only [c4, if_false] at h
      by_cases c5 : observableV1MarketShapeB before.market ≠ true
      · simp [c5] at h
      simp only [c5, if_false] at h
      by_cases c6 : before.current.isSome = true
      · simp [c6] at h
      have c6' : before.current.isSome = false := Bool.eq_false_of_not_eq_true c6
      simp only [c6', Bool.false_eq_true, if_false] at h
      by_cases c7 : before.tick.val ≠ schedule.opensAt
      · simp [c7] at h
      simp only [c7, if_false] at h
      by_cases c8 : ¬ before.inventory.WellFormed
      · simp [c8] at h
      simp only [c8, if_false] at h
      by_cases c9 : lot.authority ≠ authorityId ∨
          lot.origin.key ∉ before.consumedOrigins
      · simp [c9] at h
      simp only [c9, if_false] at h
      by_cases c10 : lot.key ∉ before.inventory.maker
      · simp [c10] at h
      exact of_not_not c10

private def proposeSubmitEnvelope {authorityId : Digest32}
    (authority : DeploymentAuthority authorityId) (envelope : SealedEnvelope)
    (state : BazaarGameState) : Except Refusal BazaarGameState :=
  match authorizedNextTick authority state with
  | .error refusal => .error refusal
  | .ok nextTick => match state.current with
  | none => .error .noOpenRound
  | some round => match round.phase with
    | .awaitingSettlement _ => .error .wrongPhase
    | .collecting =>
        if state.tick.val < round.schedule.opensAt ∨
            round.schedule.closesAt ≤ state.tick.val then
          .error .outsideCollectionWindow
        else if envelope.actor ≠ round.buyer then .error .envelopeActorMismatch
        else if envelope.round ≠ round.id then .error .envelopeRoundMismatch
        else if envelope.batchKey ≠ round.batchKey then .error .envelopeBatchMismatch
        else if envelope.nullifier ∈ round.orderNullifiers then
          .error .duplicateOrderNullifier
        else if envelope.nullifier ∈ state.market.consumedOrderNullifiers then
          .error .orderNullifierAlreadyConsumed
        else if round.envelopes.card ≥ round.maxOrders then .error .orderCapacityReached
        else .ok {
          state with
          tick := nextTick
          current := some { round with envelopes := insert envelope round.envelopes }
        }

/-- A fresh ciphertext and signature cannot recycle a nullifier which any
previously settled book already consumed in the threaded Dark Bazaar state. -/
private theorem consumed_order_nullifier_refused {authorityId : Digest32}
    (authority : DeploymentAuthority authorityId) (envelope : SealedEnvelope)
    (state : BazaarGameState) (round : Round) (nextTick : PlayerCounter)
    (authority_exact : authorityId = state.authority)
    (next_tick : state.tick.next = some nextTick)
    (current : state.current = some round)
    (phase : round.phase = .collecting)
    (windowOpen : ¬ (state.tick.val < round.schedule.opensAt ∨
      round.schedule.closesAt ≤ state.tick.val))
    (actor : envelope.actor = round.buyer)
    (roundId : envelope.round = round.id)
    (batch : envelope.batchKey = round.batchKey)
    (freshInRound : envelope.nullifier ∉ round.orderNullifiers)
    (consumed : envelope.nullifier ∈ state.market.consumedOrderNullifiers) :
    proposeSubmitEnvelope authority envelope state =
      .error .orderNullifierAlreadyConsumed := by
  simp [proposeSubmitEnvelope, authorizedNextTick, authority_exact, next_tick,
    current, phase, windowOpen, actor, roundId, batch, freshInRound, consumed]

def bookReceiptMatchesB (round : Round)
    (receipt : OpeningAwareBookReceipt) : Bool :=
  decide (receipt.round = round.id) &&
    decide (receipt.batchKey = round.batchKey) &&
    decide (receipt.claim.spec.key = round.batchKey) &&
    decide (receipt.transcript = round.transcript) &&
    decide (receipt.claim.orderNullifiers = round.orderNullifiers)

theorem bookReceiptMatchesB_iff (round : Round)
    (receipt : OpeningAwareBookReceipt) :
    bookReceiptMatchesB round receipt = true ↔
      receipt.round = round.id ∧
      receipt.batchKey = round.batchKey ∧
      receipt.claim.spec.key = round.batchKey ∧
      receipt.transcript = round.transcript ∧
      receipt.claim.orderNullifiers = round.orderNullifiers := by
  simp only [bookReceiptMatchesB, Bool.and_eq_true, decide_eq_true_eq]
  tauto

private def proposeCloseRound {authorityId : Digest32}
    (authority : DeploymentAuthority authorityId)
    (receipt : OpeningAwareBookReceipt)
    (state : BazaarGameState) : Except Refusal BazaarGameState :=
  match authorizedNextTick authority state with
  | .error refusal => .error refusal
  | .ok nextTick => match state.current with
  | none => .error .noOpenRound
  | some round => match round.phase with
    | .awaitingSettlement _ => .error .wrongPhase
    | .collecting =>
        if state.tick.val < round.schedule.closesAt then .error .closeTooEarly
        else if round.schedule.expiresAt ≤ state.tick.val then
          .error .settlementWindowClosed
        else if round.envelopes = ∅ then .error .emptyBook
        else if bookReceiptMatchesB round receipt ≠ true then
          .error .bookOpeningReceiptMismatch
        else .ok {
          state with
          tick := nextTick
          current := some {
            round with
            phase := .awaitingSettlement receipt.bindingKey
            preferenceIngress := .v1SameOpeningBound
          }
        }

private def summaryOf (kind : CompletionKind) (round : Round) : RoundSummary where
  id := round.id
  lot := round.lot.key
  quoteAsset := round.quoteAsset
  pricing := round.pricing
  orderCount := round.envelopes.card
  privacyGrade := round.privacyGrade
  preferenceIngress := round.preferenceIngress
  kind := kind

private def returnToMaker (kind : CompletionKind) (round : Round)
    (nextTick : PlayerCounter) (state : BazaarGameState) : BazaarGameState := {
  state with
  inventory := state.inventory.returnLot round.lot.key
  current := none
  history := summaryOf kind round :: state.history
  tick := nextTick
}

private def proposeCancelRound {authorityId : Digest32}
    (authority : DeploymentAuthority authorityId)
    (state : BazaarGameState) : Except Refusal BazaarGameState :=
  match authorizedNextTick authority state with
  | .error refusal => .error refusal
  | .ok nextTick => match state.current with
  | none => .error .noOpenRound
  | some round => match round.phase with
    | .awaitingSettlement _ => .error .wrongPhase
    | .collecting =>
        if ¬ state.inventory.WellFormed then .error .malformedInventory
        else if round.lot.key ∉ state.inventory.escrow then .error .lotNotEscrowed
        else if round.schedule.cancelBefore ≤ state.tick.val then
          .error .cancellationClosed
        else if round.envelopes ≠ ∅ then .error .ordersAlreadySubmitted
        else .ok (returnToMaker .cancelled round nextTick state)

private def proposeExpireRound {authorityId : Digest32}
    (authority : DeploymentAuthority authorityId)
    (state : BazaarGameState) : Except Refusal BazaarGameState :=
  match authorizedNextTick authority state with
  | .error refusal => .error refusal
  | .ok nextTick => match state.current with
  | none => .error .noOpenRound
  | some round =>
      if ¬ state.inventory.WellFormed then .error .malformedInventory
      else if round.lot.key ∉ state.inventory.escrow then .error .lotNotEscrowed
      else if state.tick.val < round.schedule.expiresAt then .error .notExpired
      else .ok (returnToMaker .expired round nextTick state)

/-- At the exact deadline of every admitted schedule, expiry has a checked
counter successor and returns the escrowed lot.  Together with
`advanceClock_active_at_or_after_expiry_refused`, this closes the hostile path
which formerly advanced to u64 max and stranded custody. -/
private theorem expire_at_wire_safe_deadline_returns_lot
    {authorityId : Digest32} (authority : DeploymentAuthority authorityId)
    (state : BazaarGameState) (round : Round)
    (authorityExact : authorityId = state.authority)
    (current : state.current = some round)
    (wireSafe : round.schedule.wireSafeB round.maxOrders = true)
    (atExpiry : state.tick.val = round.schedule.expiresAt)
    (wellFormed : state.inventory.WellFormed)
    (escrowed : round.lot.key ∈ state.inventory.escrow) :
    ∃ after : BazaarGameState,
      proposeExpireRound authority state = .ok after ∧
      round.lot.key ∈ after.inventory.maker ∧
      round.lot.key ∉ after.inventory.escrow := by
  obtain ⟨nextTick, nextTickExact⟩ :=
    wireSafe_expiry_has_tick_successor state round wireSafe atExpiry
  let after := returnToMaker .expired round nextTick state
  refine ⟨after, ?_, ?_, ?_⟩
  · simp [proposeExpireRound, authorizedNextTick, authorityExact,
      nextTickExact, current, wellFormed, escrowed, atExpiry, after]
  · simp [after, returnToMaker, Inventory.returnLot]
  · simp [after, returnToMaker, Inventory.returnLot]

private theorem expireRound_success_returns_exact_lot
    {authorityId : Digest32} {authority : DeploymentAuthority authorityId}
    {before after : BazaarGameState}
    (h : proposeExpireRound authority before = .ok after) :
    ∃ round : Round,
      before.current = some round ∧
      round.lot.key ∈ after.inventory.maker ∧
      round.lot.key ∉ after.inventory.escrow ∧
      after.inventory.WellFormed ∧
      after.current = none := by
  unfold proposeExpireRound at h
  cases htick : authorizedNextTick authority before with
  | error refusal => simp [htick] at h
  | ok nextTick =>
    rw [htick] at h
    dsimp only at h
    cases hcurrent : before.current with
    | none => rw [hcurrent] at h; contradiction
    | some round =>
      rw [hcurrent] at h
      dsimp only at h
      by_cases hwellFormed : ¬ before.inventory.WellFormed
      · simp [hwellFormed] at h
      by_cases hescrow : round.lot.key ∉ before.inventory.escrow
      · simp [hwellFormed, hescrow] at h
      by_cases hnotExpired : before.tick.val < round.schedule.expiresAt
      · simp [hwellFormed, hescrow, hnotExpired] at h
      simp only [hwellFormed, hescrow, hnotExpired, if_false,
        Except.ok.injEq] at h
      subst after
      exact ⟨round, rfl, by simp [returnToMaker, Inventory.returnLot],
        by simp [returnToMaker, Inventory.returnLot],
        Inventory.returnLot_wellFormed before.inventory round.lot.key
          (of_not_not hwellFormed) (of_not_not hescrow),
        rfl⟩

/-! ## Exact DrEX receipt consumption -/

/-- The only accepted privacy family today.  Its evidence is the existing Lean
V1 authorization, whose opening was visible to the judge. -/
structure OpeningAwareV1Receipt where
  private mk ::
  book : OpeningAwareBookReceipt
  evidence : VerifiedSettlementEvidence book.claim
  before : BazaarState
  after : BazaarState
  applied : applySettlement book.claim evidence before = some after

def OpeningAwareV1Receipt.claim (receipt : OpeningAwareV1Receipt) :
    SettlementClaim := receipt.book.claim

def OpeningAwareV1Receipt.ofApplied (book : OpeningAwareBookReceipt)
    (evidence : VerifiedSettlementEvidence book.claim)
    (before after : BazaarState)
    (applied : applySettlement book.claim evidence before = some after) :
    OpeningAwareV1Receipt := ⟨book, evidence, before, after, applied⟩

/-- Even the opening-aware path cannot widen its public currency arithmetic:
the existing verified Dark Bazaar receipt proves both unit price and total quote
fit the selected u64 wire domain. -/
theorem OpeningAwareV1Receipt.quote_currency_bounded
    (receipt : OpeningAwareV1Receipt) :
    receipt.claim.quotePrice ≤ Wire.u64Max ∧
      receipt.claim.quoteAmount ≤ Wire.u64Max :=
  applySettlement_quote_product_fits_u64 receipt.evidence receipt.applied

def settlementMatchesB (round : Round) (state : BazaarGameState)
    (receipt : OpeningAwareV1Receipt) : Bool :=
  match round.phase with
  | .collecting => false
  | .awaitingSettlement binding =>
      decide (binding = receipt.book.bindingKey) &&
      decide (round.preferenceIngress = .v1SameOpeningBound) &&
      decide (round.requestedPrivacy = .openingAwareJudge) &&
      decide (observeState receipt.before = state.market) &&
      decide (round.batchKey = round.lot.batchKey round.id.value) &&
      decide (receipt.claim.spec.key = round.batchKey) &&
      decide (receipt.claim.spec.federationId =
        round.lot.origin.run.receipt.federationId) &&
      decide (receipt.claim.spec.contentRoot =
        round.lot.origin.run.receipt.contentRoot) &&
      decide (receipt.claim.spec.activationDigest =
        round.lot.origin.run.receipt.activationDigest) &&
      decide (receipt.claim.spec.contentSession =
        round.lot.origin.run.receipt.contentSession) &&
      decide (receipt.claim.spec.contentEpoch =
        round.lot.origin.run.receipt.contentEpoch) &&
      decide (receipt.claim.spec.sourceRoot = round.lot.sourceRoot) &&
      decide (receipt.claim.spec.seller = round.lot.seller) &&
      decide (receipt.claim.spec.buyer = round.buyer) &&
      decide (receipt.claim.spec.baseAsset = .relic round.lot.origin.relic) &&
      decide (receipt.claim.spec.quoteAsset = round.quoteAsset) &&
      decide (receipt.claim.spec.pricing = round.pricing) &&
      decide (receipt.claim.spec.maxOrders = round.maxOrders) &&
      decide (receipt.claim.spec.maxOrderQuantity = round.maxOrderQuantity) &&
      decide (receipt.claim.spec.allowedOutputs = round.allowedOutputs) &&
      decide (receipt.claim.output ∈ round.allowedOutputs) &&
      decide (receipt.claim.privateBookCommitment =
        binding.privateBookCommitment) &&
      decide (receipt.claim.baseInputs = {round.lot.note}) &&
      decide (receipt.claim.output.volume = 1) &&
      decide (receipt.claim.orderNullifiers = round.orderNullifiers) &&
      decide state.inventory.WellFormed &&
      decide (round.lot.key ∈ state.inventory.escrow) &&
      decide (round.lot.key ∉ state.inventory.maker) &&
      decide (round.lot.key ∉ state.inventory.taker) &&
      decide (receipt.claim.spec.key ∉ state.consumedSettlements)

theorem settlementMatchesB_inventory (round : Round) (state : BazaarGameState)
    (receipt : OpeningAwareV1Receipt)
    (accepted : settlementMatchesB round state receipt = true) :
    state.inventory.WellFormed ∧
      round.lot.key ∈ state.inventory.escrow ∧
      round.lot.key ∉ state.inventory.maker ∧
      round.lot.key ∉ state.inventory.taker := by
  cases hphase : round.phase with
  | collecting => simp [settlementMatchesB, hphase] at accepted
  | awaitingSettlement commitment =>
      simp only [settlementMatchesB, hphase, Bool.and_eq_true,
        decide_eq_true_eq] at accepted
      tauto

private def proposeSettleRound {authorityId : Digest32}
    (authority : DeploymentAuthority authorityId)
    (receipt : OpeningAwareV1Receipt)
    (state : BazaarGameState) : Except Refusal BazaarGameState :=
  match authorizedNextTick authority state with
  | .error refusal => .error refusal
  | .ok nextTick => match state.current with
  | none => .error .noOpenRound
  | some round => match round.phase with
    | .collecting => .error .wrongPhase
    | .awaitingSettlement _ =>
        if round.schedule.expiresAt ≤ state.tick.val then
          .error .settlementWindowClosed
        else if round.requestedPrivacy = .houseBlind then .error .houseBlindProofUnavailable
        else if receipt.claim.spec.key ∈ state.consumedSettlements then
          .error .settlementAlreadyConsumed
        else if settlementMatchesB round state receipt ≠ true then
          .error .receiptDoesNotMatchRound
        else .ok {
          state with
          inventory := state.inventory.settleLot round.lot.key
          market := observeState receipt.after
          current := none
          history := summaryOf
            (.settled receipt.claim.spec.key receipt.claim.output) round :: state.history
          tick := nextTick
          consumedSettlements := insert receipt.claim.spec.key state.consumedSettlements
        }

/-! ## Canonical command surface

The private reducers above are implementation details, including for clients
and speculative execution: exposing them would let a holder extract a state
projection and manufacture an unpersisted branch.  These commands are the only
player transition surface.  Each accepts a proof-carrying durable deployment
and returns only a persistence candidate. -/

def advanceClock (live : DurableDeployment)
    {authorityId : Digest32} (authority : DeploymentAuthority authorityId)
    : Except Refusal PersistenceCandidate :=
  preparePersistence live (proposeAdvanceClock authority live.state)

/-- Public hostile-state statement over the persisted API: once the persisted
pending observation says its deadline has arrived, the canonical clock command
returns no candidate at all. -/
theorem advanceClock_persisted_at_or_after_expiry_refused
    (live : DurableDeployment) {authorityId : Digest32}
    (authority : DeploymentAuthority authorityId)
    (pending : PendingObservation)
    (authorityExact : authorityId = live.key.authority)
    (observed : live.observePending = some pending)
    (expired : pending.expiresAt ≤ live.clock) :
    advanceClock live authority = .error .activeRoundRequiresExpiry := by
  cases hcurrent : live.state.current with
  | none => simp [DurableDeployment.observePending, observePendingState,
      hcurrent] at observed
  | some round =>
      have deadlineExact : round.schedule.expiresAt = pending.expiresAt := by
        have mapped := congrArg (Option.map PendingObservation.expiresAt) observed
        simpa [DurableDeployment.observePending, observePendingState,
          hcurrent] using mapped
      have authorityExact' : authorityId = live.state.authority := by
        simpa [DurableDeployment.key, BazaarGameState.key] using authorityExact
      have expired' : round.schedule.expiresAt ≤ live.state.tick.val := by
        simpa [DurableDeployment.clock, deadlineExact] using expired
      unfold advanceClock
      rw [advanceClock_active_at_or_after_expiry_refused authority live.state
        round authorityExact' hcurrent expired']
      rfl

def openRound (live : DurableDeployment)
    {authorityId : Digest32} (authority : DeploymentAuthority authorityId)
    (lot : CrownedSalvage) (buyer : ParticipantId) (quoteAsset : AssetRef)
    (schedule : RoundSchedule) (maxOrders : Nat) (fees : FeePolicy)
    (privacy : RequestedPrivacy) : Except Refusal PersistenceCandidate :=
  preparePersistence live
    (proposeOpenRound authority lot buyer quoteAsset schedule maxOrders fees privacy
      live.state)

def openAuthoredRound (live : DurableDeployment)
    {authorityId : Digest32} (authority : DeploymentAuthority authorityId)
    (lot : CrownedSalvage) (schedule : RoundSchedule) (fees : FeePolicy)
    (privacy : RequestedPrivacy) : Except Refusal PersistenceCandidate :=
  preparePersistence live
    (proposeOpenAuthoredRound authority lot schedule fees privacy live.state)

def submitEnvelope (live : DurableDeployment)
    {authorityId : Digest32} (authority : DeploymentAuthority authorityId)
    (envelope : SealedEnvelope) : Except Refusal PersistenceCandidate :=
  preparePersistence live (proposeSubmitEnvelope authority envelope live.state)

def closeRound (live : DurableDeployment)
    {authorityId : Digest32} (authority : DeploymentAuthority authorityId)
    (receipt : OpeningAwareBookReceipt) : Except Refusal PersistenceCandidate :=
  preparePersistence live (proposeCloseRound authority receipt live.state)

def cancelRound (live : DurableDeployment)
    {authorityId : Digest32} (authority : DeploymentAuthority authorityId)
    : Except Refusal PersistenceCandidate :=
  preparePersistence live (proposeCancelRound authority live.state)

def expireRound (live : DurableDeployment)
    {authorityId : Digest32} (authority : DeploymentAuthority authorityId)
    : Except Refusal PersistenceCandidate :=
  preparePersistence live (proposeExpireRound authority live.state)

def settleRound (live : DurableDeployment)
    {authorityId : Digest32} (authority : DeploymentAuthority authorityId)
    (receipt : OpeningAwareV1Receipt) : Except Refusal PersistenceCandidate :=
  preparePersistence live (proposeSettleRound authority receipt live.state)

private theorem settleRound_success_moves_exact_lot_and_consumes_receipt
    {authorityId : Digest32} {authority : DeploymentAuthority authorityId}
    {receipt : OpeningAwareV1Receipt}
    {before after : BazaarGameState}
    (h : proposeSettleRound authority receipt before = .ok after) :
    ∃ round : Round,
      before.current = some round ∧
      round.lot.key ∈ after.inventory.taker ∧
      round.lot.key ∉ after.inventory.escrow ∧
      round.lot.key ∉ after.inventory.maker ∧
      after.inventory.WellFormed ∧
      receipt.claim.spec.key ∈ after.consumedSettlements ∧
      after.current = none := by
  unfold proposeSettleRound at h
  cases htick : authorizedNextTick authority before with
  | error refusal => simp [htick] at h
  | ok nextTick =>
    rw [htick] at h
    dsimp only at h
    cases hcurrent : before.current with
    | none => rw [hcurrent] at h; contradiction
    | some round =>
      rw [hcurrent] at h
      dsimp only at h
      cases hphase : round.phase with
      | collecting => rw [hphase] at h; contradiction
      | awaitingSettlement commitment =>
        rw [hphase] at h
        dsimp only at h
        by_cases hexpired : round.schedule.expiresAt ≤ before.tick.val
        · simp [hexpired] at h
        by_cases hprivate : round.requestedPrivacy = .houseBlind
        · simp [hexpired, hprivate] at h
        by_cases hconsumed : receipt.claim.spec.key ∈ before.consumedSettlements
        · simp [hexpired, hprivate, hconsumed] at h
        by_cases hmismatch : settlementMatchesB round before receipt ≠ true
        · simp [hexpired, hprivate, hconsumed, hmismatch] at h
        have hmatched : settlementMatchesB round before receipt = true :=
          of_not_not hmismatch
        have hinventory := settlementMatchesB_inventory round before receipt hmatched
        simp only [hexpired, hprivate, hconsumed, hmismatch, if_false,
          Except.ok.injEq] at h
        subst after
        exact ⟨round, rfl, by simp [Inventory.settleLot],
          by simp [Inventory.settleLot], hinventory.2.2.1,
          Inventory.settleLot_wellFormed before.inventory round.lot.key
            hinventory.1 hinventory.2.1,
          by simp, rfl⟩

/-- A consumed settlement cannot fill a second round in the same threaded game
state, independently of how its opening is represented. -/
private theorem consumed_settlement_refused {authorityId : Digest32}
    (authority : DeploymentAuthority authorityId)
    (receipt : OpeningAwareV1Receipt) (state : BazaarGameState) (round : Round)
    (nextTick : PlayerCounter)
    (authority_exact : authorityId = state.authority)
    (next_tick : state.tick.next = some nextTick)
    (current : state.current = some round)
    (phase : ∃ commitment, round.phase = .awaitingSettlement commitment)
    (window : ¬ round.schedule.expiresAt ≤ state.tick.val)
    (privacy : round.requestedPrivacy = .openingAwareJudge)
    (consumed : receipt.claim.spec.key ∈ state.consumedSettlements) :
    proposeSettleRound authority receipt state = .error .settlementAlreadyConsumed := by
  obtain ⟨commitment, phase⟩ := phase
  simp [proposeSettleRound, authorizedNextTick, authority_exact, next_tick, current,
    phase, window, privacy, consumed]

/-! ## Structural anti-duplication consequences -/

private theorem settled_lot_cannot_be_relisted_from_success
    {authorityId : Digest32} {authority : DeploymentAuthority authorityId}
    {receipt : OpeningAwareV1Receipt}
    {before after : BazaarGameState}
    (settled : proposeSettleRound authority receipt before = .ok after) :
    ∀ (buyer : ParticipantId) (quoteAsset : AssetRef)
      (schedule : RoundSchedule) (maxOrders : Nat) (fees : FeePolicy)
      (privacy : RequestedPrivacy) (round : Round) (candidate : BazaarGameState),
      before.current = some round →
      proposeOpenRound authority round.lot buyer quoteAsset schedule maxOrders fees privacy after ≠
        .ok candidate := by
  intro buyer quoteAsset schedule maxOrders fees privacy round candidate hround opened
  obtain ⟨settledRound, hcurrent, htaker, _hescrow, hnotmaker,
    hwellFormed, _hconsumed, hnone⟩ :=
    settleRound_success_moves_exact_lot_and_consumes_receipt settled
  have heq : settledRound = round := by
    rw [hround] at hcurrent
    exact (Option.some.inj hcurrent).symm
  subst settledRound
  exact hnotmaker (openRound_success_requires_maker opened)

#assert_axioms inspectEligible_never_crowns
#assert_axioms SalvageOrigin.key_extensional_downstream
#assert_axioms CrownedSalvage.exact_receipt_key
#assert_axioms CrownedSalvage.exact_relic
#assert_axioms CrownedSalvage.exact_seller
#assert_axioms CrownedSalvage.exact_note
#assert_axioms CrownedSalvage.exact_note_nullifier
#assert_axioms CrownedSalvage.exact_authority
#assert_axioms CrownedSalvage.exact_sourceRoot
#assert_axioms CrownedSalvage.relic_was_yielded
#assert_axioms CrownedSalvage.origin_was_in_supplied_archive
#assert_axioms Inventory.singletonMaker_wellFormed
#assert_axioms Inventory.escrowLot_wellFormed
#assert_axioms Inventory.returnLot_wellFormed
#assert_axioms Inventory.settleLot_wellFormed
#assert_axioms RoundSchedule.validB_iff
#assert_axioms RoundSchedule.wireSafeB_iff
#assert_axioms RoundSchedule.max_expiry_is_never_wire_safe
#assert_axioms v1MarketPolicyB_iff
#assert_axioms observableV1MarketShapeB_requires_v1_policy
#assert_axioms initializationMatchesB_requires_current_v1
#assert_axioms authoredRoundMatchesB_iff
#assert_axioms runtimeCas_same_old_fork_has_one_winner
#assert_axioms runtimeCas_genesis_is_explicit
#assert_axioms SuccessfulPersistence.exact_cas
#assert_axioms TrustedRuntimePortal.confirmPersistence_exact
#assert_axioms TrustedRuntimePortal.authorizeSameOpening_exact
#assert_axioms TrustedRuntimePortal.provisionCrownedSalvage_success_exact
#assert_axioms preparePersistence_success_expected_exact
#assert_axioms PersistenceCandidate.continuation_replacement_exact
#assert_axioms PersistenceCandidate.continuation_revision_exact
#assert_axioms OpeningAwareBookReceipt.transcript_card
#assert_axioms bookReceiptMatchesB_iff
#assert_axioms advanceClock_active_at_or_after_expiry_refused
#assert_axioms advanceClock_persisted_at_or_after_expiry_refused
#assert_axioms wireSafe_expiry_has_tick_successor
#assert_axioms max_expiry_refused_before_custody_lock
#assert_axioms openRound_success_moves_lot_to_escrow
#assert_axioms openRound_success_requires_maker
#assert_axioms consumed_order_nullifier_refused
#assert_axioms expire_at_wire_safe_deadline_returns_lot
#assert_axioms expireRound_success_returns_exact_lot
#assert_axioms OpeningAwareV1Receipt.quote_currency_bounded
#assert_axioms settlementMatchesB_inventory
#assert_axioms settleRound_success_moves_exact_lot_and_consumes_receipt
#assert_axioms consumed_settlement_refused
#assert_axioms settled_lot_cannot_be_relisted_from_success

end Dregg2.Games.PathOfAngels.BazaarGame
