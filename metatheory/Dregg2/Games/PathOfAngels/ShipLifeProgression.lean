/-
# ShipLifeProgression — a receipt-only projection of life aboard the Khovokhi

This is deliberately not a second game authority.  Expedition outcomes,
attendant transitions, crafting, gallery registration, ordinary-part exchange,
crew health, holder eligibility, and finalized daily claims are accepted only as
typed receipts from their named authorities.  This coordinator owns no balance,
inventory, custody, companion, health, or canon successor.  It owns only replayed
receipt indexes and disposable beta-facing views: career pages, cadence, loadout
previews, collections, recovery displays, cosmetic flair, and suggested unlocks.

That separation is the platform architecture.  Many small games may enrich one
ship-life page without acquiring the ability to mint a resource, kill an
attendant, move a relic, promote canon, or turn a holder badge into power.

The present direct authorities are `Shipworks.Settlement`,
`CrewFieldMissionRuntime`, and `AttendantContinuityAggregate`.  Expedition intake
is the opaque runtime + EventBatch receipt exposed by `ShipExpeditionSeason`; it
never proves acceptance by inspecting a season projection.  Craft/gear,
GalleryGated, crew-health, and ordinary-parts
Bazaar adapters are intentionally sealed seams until those authorities expose
canonical receipt codecs.  In particular, current `BazaarGame` relic salvage is
not silently reclassified as an ordinary market part.
-/
import Dregg2.Games.PathOfAngels.AttendantContinuityAggregate
import Dregg2.Games.PathOfAngels.BazaarGame
import Dregg2.Games.PathOfAngels.EventBatch
import Dregg2.Games.PathOfAngels.EventSourcing
import Dregg2.Games.PathOfAngels.ShipExpeditionSeason
import Dregg2.Games.PathOfAngels.Shipworks
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.ShipLifeProgression

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.EventSourcing

set_option autoImplicit false

abbrev SHIP_LIFE_STREAM_KIND : Nat := 13
abbrev MAX_FANOUT_EVENTS : Nat := 16
abbrev MAX_GALLERY_ITEMS : Nat := 512
abbrev MAX_LOADOUT_SLOTS : Nat := 8
abbrev MAX_DURABILITY : Nat := 100
abbrev MAX_RESOURCE_AUDIT : Nat := 1000000

/-! ## Authored, spoiler-free vocabulary -/

structure GalleryItemId where value : Nat
deriving Repr, DecidableEq

structure CosmeticId where value : Nat
deriving Repr, DecidableEq

structure SocialMarkId where value : Nat
deriving Repr, DecidableEq

structure GearId where value : Nat
deriving Repr, DecidableEq

structure BlueprintId where value : Nat
deriving Repr, DecidableEq

abbrev OrdinaryPartId := CrewFieldMissionRuntime.PartId

structure UnlockHintId where value : Nat
deriving Repr, DecidableEq

structure ReceiptId where digest : Digest32
deriving DecidableEq

structure UnlockRule where
  hint : UnlockHintId
  expeditionsRequired : Nat
  maintenanceRequired : Nat
  trainingRequired : Nat
deriving DecidableEq

structure AuthoredCatalog where
  galleryItems : Finset GalleryItemId
  cosmetics : Finset CosmeticId
  socialMarks : Finset SocialMarkId
  gear : Finset GearId
  blueprints : Finset BlueprintId
  ordinaryParts : Finset OrdinaryPartId
  unlockRules : List UnlockRule
  unlockIdsUnique : (unlockRules.map UnlockRule.hint).Nodup
  galleryBounded : galleryItems.card <= MAX_GALLERY_ITEMS
deriving DecidableEq

structure ProgressionIdentity where
  federationId : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  season : ShipExpeditionSeason.SeasonId
  activationDigest : Digest32
  owner : Digest32
deriving DecidableEq

def ProgressionIdentity.seasonIdentity (identity : ProgressionIdentity) :
    ShipExpeditionSeason.SeasonIdentity where
  federationId := identity.federationId
  contentSession := identity.contentSession
  contentEpoch := identity.contentEpoch
  season := identity.season
  activationDigest := identity.activationDigest

structure RawConfig where
  schemaVersion : Nat
  identity : ProgressionIdentity
  catalog : AuthoredCatalog
  graceEvery : Nat
  graceEveryPositive : 0 < graceEvery
deriving DecidableEq

/-- The constructor is sealed so deployed configuration must cross `activate`. -/
structure Config where
  private mk ::
  raw : RawConfig

def activate (raw : RawConfig) : Option Config :=
  if raw.schemaVersion = 0 then none
  else if raw.graceEvery > 64 then none
  else some ⟨raw⟩

/-! ## Derived views, never successor authority -/

structure DerivedCareerView where
  expeditions : Nat
  safeReturns : Nat
  deepReturns : Nat
  maintenanceSuccesses : Nat
  meaningfulFailures : Nat
  trainingObserved : Nat
  recoveryObserved : Nat
  meritObserved : Nat
deriving Repr, DecidableEq

def DerivedCareerView.empty : DerivedCareerView :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

structure DerivedCompanionView where
  key : Attendant.AttendantKey
  status : Attendant.OperationalStatus
  charge : Nat
  condition : Nat
  rapport : Nat
  training : Nat
  equipped : Option Attendant.EquipmentId
  deployments : Nat
deriving DecidableEq

def companionViewOf (wire : AttendantContinuityAggregate.AttendantReceiptWire) :
    DerivedCompanionView where
  key := wire.attendantKey
  status := wire.result.after.mutable.status
  charge := wire.result.after.mutable.charge.val
  condition := wire.result.after.mutable.condition.val
  rapport := wire.result.after.mutable.rapport.val
  training := wire.result.after.mutable.training.val
  equipped := wire.result.after.mutable.equipped
  deployments := wire.result.after.mutable.deployments.val

/-- There is no dead state.  `none` means no accepted continuity receipt has
been observed; maintenance remains recoverable in the attendant authority. -/
abbrev DerivedCompanionCache := Option DerivedCompanionView

structure DurabilityRow where
  gear : GearId
  durability : Nat
  bounded : durability <= MAX_DURABILITY
deriving DecidableEq

structure DerivedGearView where
  loadout : List GearId
  durability : List DurabilityRow
  loadoutBounded : loadout.length <= MAX_LOADOUT_SLOTS
  loadoutUnique : loadout.Nodup
deriving DecidableEq

def DerivedGearView.empty : DerivedGearView :=
  ⟨[], [], by simp, by simp⟩

abbrev DerivedHealthView := ShipExpeditionSeason.DerivedCrewHealthView

def DerivedHealthView.empty : DerivedHealthView :=
  ShipExpeditionSeason.DerivedCrewHealthView.empty

structure DailyCadence where
  lastEpoch : Option EpochId
  current : Nat
  longest : Nat
  grace : Nat
deriving Repr, DecidableEq

def DailyCadence.empty : DailyCadence := ⟨none, 0, 0, 0⟩

/-- Cadence is a social rhythm only.  A one-epoch miss may spend one earned
grace; any larger gap starts a new rhythm.  Nothing else decays. -/
def advanceCadence (graceEvery : Nat) (before : DailyCadence)
    (epoch : EpochId) : DailyCadence :=
  match before.lastEpoch with
  | none =>
      { lastEpoch := some epoch, current := 1, longest := max before.longest 1,
        grace := before.grace }
  | some prior =>
      if epoch.value = prior.value + 1 then
        let current := before.current + 1
        let earned := if graceEvery > 0 && current % graceEvery = 0 then 1 else 0
        { lastEpoch := some epoch, current, longest := max before.longest current,
          grace := before.grace + earned }
      else if epoch.value = prior.value + 2 && 0 < before.grace then
        let current := before.current + 1
        { lastEpoch := some epoch, current, longest := max before.longest current,
          grace := before.grace - 1 }
      else
        { lastEpoch := some epoch, current := 1, longest := max before.longest 1,
          grace := before.grace }

structure ResourceAudit where
  loose : Nat
  installed : Nat
  sunk : Nat
deriving Repr, DecidableEq

def ResourceAudit.valid (audit : ResourceAudit) : Bool :=
  decide (audit.loose <= MAX_RESOURCE_AUDIT ∧
    audit.installed <= MAX_RESOURCE_AUDIT ∧
    audit.sunk <= MAX_RESOURCE_AUDIT)

def ResourceAudit.total (audit : ResourceAudit) : Nat :=
  audit.loose + audit.installed + audit.sunk

structure PowerView where
  career : DerivedCareerView
  companion : DerivedCompanionCache
  gear : DerivedGearView
  health : DerivedHealthView
  gallery : Finset GalleryItemId
  unlockHints : Finset UnlockHintId
deriving DecidableEq

/-! ## Receipts from the real authorities and explicit missing adapters -/

/-- Atomic inclusion in the attendant continuity stream is a runtime seam.
The constructor is private: raw `AttendantReceiptWire` is not enough. -/
structure AttendantContinuityReceiptInterface where
  private mk ::
  receiptId : ReceiptId
  sourceBatchDigest : Digest32
  owner : Digest32
  wire : AttendantContinuityAggregate.AttendantReceiptWire
  ownerExact : owner = wire.attendantKey.owner

/-- Finalized Shipworks settlement plus authenticated owner binding. -/
structure ShipworksSettlementReceiptInterface where
  private mk ::
  receiptId : ReceiptId
  sourceBatchDigest : Digest32
  owner : Digest32
  settlement : Shipworks.Settlement

/-- An actual failed replay is retained as nonterminal participation; it has no
reward or negative resource field. -/
structure ShipworksFailureReceiptInterface where
  private mk ::
  receiptId : ReceiptId
  sourceBatchDigest : Digest32
  owner : Digest32
  dispatch : Shipworks.Dispatch
  loadout : Shipworks.Loadout
  actions : List Shipworks.Action
  finalState : Shipworks.State
  replayExact : Shipworks.replay dispatch loadout actions = some finalState
  failedExact : finalState.status = .failed

inductive CraftGearOperation where
  | craft (blueprint : BlueprintId) (gear : GearId)
  | repair (gear : GearId)
  | equip (gear : GearId)
  | unequip (gear : GearId)
deriving Repr, DecidableEq

/-- This interface is intentionally unproducible outside this module until
dreggnet-craft/gear exports a canonical Lean receipt.  The audit includes sinks,
so crafting may consume loose material without erasing it from conservation. -/
structure DreggnetCraftGearReceiptInterface where
  private mk ::
  receiptId : ReceiptId
  sourceBatchDigest : Digest32
  owner : Digest32
  operation : CraftGearOperation
  before : ResourceAudit
  after : ResourceAudit
  beforeValid : before.valid = true
  afterValid : after.valid = true
  conserved : before.total = after.total
  afterView : DerivedGearView

/-- GalleryGated remains the asset authority; this sealed adapter carries only
its finite, authored collection projection and an explicit zero balance delta. -/
structure GalleryGatedReceiptInterface where
  private mk ::
  receiptId : ReceiptId
  sourceBatchDigest : Digest32
  owner : Digest32
  afterItems : Finset GalleryItemId
  balanceDelta : Int
  balanceNeutral : balanceDelta = 0

inductive HolderAffordance where
  | cosmetic (id : CosmeticId)
  | socialMark (id : SocialMarkId)
deriving Repr, DecidableEq

/-- Holder eligibility yields exactly one bounded presentational affordance.
There is no quantity, score, loot, survival, canon, market, or unlock field. -/
structure HolderCosmeticReceiptInterface where
  private mk ::
  receiptId : ReceiptId
  sourceBatchDigest : Digest32
  owner : Digest32
  eligibilityNullifier : Digest32
  affordance : HolderAffordance

/-- Content-contract relics have no ingress into the ordinary-part market interface. -/
def canonRelicMarketIngress (_ : ContentContract.RelicId) :
    Option ShipExpeditionSeason.BazaarPartReceiptInterface := none

theorem canon_relics_are_non_market (relic : ContentContract.RelicId) :
    canonRelicMarketIngress relic = none := rfl

/-! ## Receipt-only state and fan-out -/

inductive DerivedFanoutEvent where
  | expeditionObserved (receipt : ReceiptId) (shift : ShipExpeditionSeason.ShiftId)
  | attendantObserved (receipt : ReceiptId) (key : Attendant.AttendantKey)
  | shipworksObserved (receipt : ReceiptId) (epoch : EpochId)
  | failedAttemptObserved (receipt : ReceiptId) (epoch : EpochId)
  | gearProjectionObserved (receipt : ReceiptId)
  | galleryProjectionObserved (receipt : ReceiptId)
  | healthProjectionObserved (receipt : ReceiptId)
  | ordinaryPartExchangeObserved (receipt : ReceiptId)
  | holderFlairObserved (receipt : ReceiptId)
deriving DecidableEq

structure DerivedFanoutBatch where
  sourceEvent : Nat
  sourceBatchDigest : Digest32
  ordered : List DerivedFanoutEvent
deriving DecidableEq

structure MigrationAnchor where
  priorIdentity : ProgressionIdentity
  priorEventCount : Nat
  priorHead : Digest32
deriving DecidableEq

/-- Every field is either an exact receipt index or a disposable view. -/
structure State where
  private mk ::
  identity : ProgressionIdentity
  eventCount : Nat
  career : DerivedCareerView
  companion : DerivedCompanionCache
  gear : DerivedGearView
  health : DerivedHealthView
  gallery : Finset GalleryItemId
  cadence : DailyCadence
  cosmetics : Finset CosmeticId
  socialMarks : Finset SocialMarkId
  unlockHints : Finset UnlockHintId
  seenExpeditions : Finset ReceiptId
  seenAttendants : Finset ReceiptId
  seenShipworks : Finset ReceiptId
  seenShipworksEpochs : Finset Nat
  seenFailures : Finset ReceiptId
  seenGear : Finset ReceiptId
  seenGallery : Finset ReceiptId
  seenHealth : Finset ReceiptId
  seenMarket : Finset ReceiptId
  seenHolder : Finset ReceiptId
  fanoutBatches : List DerivedFanoutBatch
  migrations : List MigrationAnchor
deriving DecidableEq

def initialState (config : Config) : State where
  identity := config.raw.identity
  eventCount := 0
  career := .empty
  companion := none
  gear := .empty
  health := .empty
  gallery := ∅
  cadence := .empty
  cosmetics := ∅
  socialMarks := ∅
  unlockHints := ∅
  seenExpeditions := ∅
  seenAttendants := ∅
  seenShipworks := ∅
  seenShipworksEpochs := ∅
  seenFailures := ∅
  seenGear := ∅
  seenGallery := ∅
  seenHealth := ∅
  seenMarket := ∅
  seenHolder := ∅
  fanoutBatches := []
  migrations := []

def State.powerView (state : State) : PowerView where
  career := state.career
  companion := state.companion
  gear := state.gear
  health := state.health
  gallery := state.gallery
  unlockHints := state.unlockHints

def deriveUnlockHints (catalog : AuthoredCatalog) (career : DerivedCareerView) :
    Finset UnlockHintId :=
  (catalog.unlockRules.filter fun rule =>
    rule.expeditionsRequired <= career.expeditions ∧
    rule.maintenanceRequired <= career.maintenanceSuccesses ∧
    rule.trainingRequired <= career.trainingObserved).map UnlockRule.hint |>.toFinset

def AuthoredCatalog.allowsGearView (catalog : AuthoredCatalog)
    (view : DerivedGearView) : Bool :=
  view.loadout.all (fun id => id ∈ catalog.gear) &&
    view.durability.all (fun row => row.gear ∈ catalog.gear)

def AuthoredCatalog.allowsOperation (catalog : AuthoredCatalog) :
    CraftGearOperation → Bool
  | .craft blueprint gear => blueprint ∈ catalog.blueprints && gear ∈ catalog.gear
  | .repair gear => gear ∈ catalog.gear
  | .equip gear => gear ∈ catalog.gear
  | .unequip gear => gear ∈ catalog.gear

def AuthoredCatalog.allowsAffordance (catalog : AuthoredCatalog) :
    HolderAffordance → Bool
  | .cosmetic id => id ∈ catalog.cosmetics
  | .socialMark id => id ∈ catalog.socialMarks

def expeditionCareer (before : DerivedCareerView)
    (summary : ShipExpeditionSeason.ShiftSummary) : DerivedCareerView :=
  { before with
    expeditions := before.expeditions + 1
    safeReturns := before.safeReturns +
      if summary.extraction = "return-now" then 1 else 0
    deepReturns := before.deepReturns +
      if summary.extraction = "descend-further" then 1 else 0
    meritObserved := before.meritObserved + summary.contribution.score }

def attendantCareer (before : DerivedCareerView)
    (view : DerivedCompanionView) : DerivedCareerView :=
  { before with trainingObserved := max before.trainingObserved view.training }

def shipworksCareer (before : DerivedCareerView) : DerivedCareerView :=
  { before with maintenanceSuccesses := before.maintenanceSuccesses + 1 }

def failedCareer (before : DerivedCareerView) : DerivedCareerView :=
  { before with meaningfulFailures := before.meaningfulFailures + 1 }

def healthCareer (before : DerivedCareerView)
    (receipt : ShipExpeditionSeason.CanonicalHealthReceiptInterface) : DerivedCareerView :=
  { before with recoveryObserved := before.recoveryObserved +
      if receipt.recovery then 1 else 0 }

inductive ObservedReceipt where
  | expedition (receipt : ShipExpeditionSeason.RuntimeEventBatchReceipt)
  | attendant (receipt : AttendantContinuityReceiptInterface)
  | shipworks (receipt : ShipworksSettlementReceiptInterface)
  | shipworksFailure (receipt : ShipworksFailureReceiptInterface)
  | craftGear (receipt : DreggnetCraftGearReceiptInterface)
  | gallery (receipt : GalleryGatedReceiptInterface)
  | health (receipt : ShipExpeditionSeason.CanonicalHealthReceiptInterface)
  | ordinaryPartExchange (receipt : ShipExpeditionSeason.BazaarPartReceiptInterface)
  | holderFlair (receipt : HolderCosmeticReceiptInterface)

def ObservedReceipt.sourceBatchDigest : ObservedReceipt → Digest32
  | .expedition receipt => receipt.sourceBatchDigest
  | .attendant receipt => receipt.sourceBatchDigest
  | .shipworks receipt => receipt.sourceBatchDigest
  | .shipworksFailure receipt => receipt.sourceBatchDigest
  | .craftGear receipt => receipt.sourceBatchDigest
  | .gallery receipt => receipt.sourceBatchDigest
  | .health receipt => receipt.sourceBatchDigest
  | .ordinaryPartExchange receipt => receipt.sourceBatchDigest
  | .holderFlair receipt => receipt.sourceBatchDigest

private def appendFanout (before : State) (sourceDigest : Digest32)
    (events : List DerivedFanoutEvent) : State :=
  { before with
    eventCount := before.eventCount + 1
    fanoutBatches := before.fanoutBatches ++
      [{ sourceEvent := before.eventCount + 1,
         sourceBatchDigest := sourceDigest, ordered := events }] }

private def acceptExpedition (config : Config) (before : State)
    (receipt : ShipExpeditionSeason.RuntimeEventBatchReceipt) : Option State := do
  let receiptId : ReceiptId := ⟨receipt.receiptId⟩
  let summary := ShipExpeditionSeason.summaryOf receipt
  if receipt.owner != before.identity.owner then none
  else if receipt.activationId != before.identity.activationDigest then none
  else if receipt.batch.coordinate.world.federationId != before.identity.federationId then none
  else if receipt.batch.coordinate.world.contentSession != before.identity.contentSession then none
  else if receipt.batch.coordinate.world.contentEpoch != before.identity.contentEpoch then none
  else if receiptId ∈ before.seenExpeditions then none
  else
    let career := expeditionCareer before.career summary
    let next := { before with
      career
      unlockHints := deriveUnlockHints config.raw.catalog career
      seenExpeditions := insert receiptId before.seenExpeditions }
    some (appendFanout next receipt.sourceBatchDigest
      [.expeditionObserved receiptId summary.plan.shift])

private def acceptAttendant (config : Config) (before : State)
    (receipt : AttendantContinuityReceiptInterface) : Option State := do
  if receipt.owner != before.identity.owner then none
  else if receipt.wire.result.after.federationId != before.identity.federationId then none
  else if receipt.wire.result.after.contentSession != before.identity.contentSession then none
  else if receipt.receiptId ∈ before.seenAttendants then none
  else
    let companion := companionViewOf receipt.wire
    let career := attendantCareer before.career companion
    let next := { before with
      career
      companion := some companion
      unlockHints := deriveUnlockHints config.raw.catalog career
      seenAttendants := insert receipt.receiptId before.seenAttendants }
    some (appendFanout next receipt.sourceBatchDigest
      [.attendantObserved receipt.receiptId receipt.wire.attendantKey])

private def acceptShipworks (config : Config) (before : State)
    (receipt : ShipworksSettlementReceiptInterface) : Option State := do
  if receipt.owner != before.identity.owner then none
  else if receipt.receiptId ∈ before.seenShipworks then none
  else if receipt.settlement.missionEpoch.value ∈ before.seenShipworksEpochs then none
  else
    let career := shipworksCareer before.career
    let next := { before with
      career
      cadence := advanceCadence config.raw.graceEvery before.cadence
        receipt.settlement.missionEpoch
      unlockHints := deriveUnlockHints config.raw.catalog career
      seenShipworks := insert receipt.receiptId before.seenShipworks
      seenShipworksEpochs := insert receipt.settlement.missionEpoch.value
        before.seenShipworksEpochs }
    some (appendFanout next receipt.sourceBatchDigest
      [.shipworksObserved receipt.receiptId receipt.settlement.missionEpoch])

private def acceptFailure (before : State)
    (receipt : ShipworksFailureReceiptInterface) : Option State := do
  if receipt.owner != before.identity.owner then none
  else if receipt.receiptId ∈ before.seenFailures then none
  else
    let next := { before with
      career := failedCareer before.career
      seenFailures := insert receipt.receiptId before.seenFailures }
    some (appendFanout next receipt.sourceBatchDigest
      [.failedAttemptObserved receipt.receiptId receipt.dispatch.epoch])

private def acceptCraftGear (config : Config) (before : State)
    (receipt : DreggnetCraftGearReceiptInterface) : Option State := do
  if receipt.owner != before.identity.owner then none
  else if receipt.receiptId ∈ before.seenGear then none
  else if !config.raw.catalog.allowsOperation receipt.operation then none
  else if !config.raw.catalog.allowsGearView receipt.afterView then none
  else
    let next := { before with
      gear := receipt.afterView
      seenGear := insert receipt.receiptId before.seenGear }
    some (appendFanout next receipt.sourceBatchDigest
      [.gearProjectionObserved receipt.receiptId])

private def acceptGallery (config : Config) (before : State)
    (receipt : GalleryGatedReceiptInterface) : Option State := do
  if receipt.owner != before.identity.owner then none
  else if receipt.receiptId ∈ before.seenGallery then none
  else if !(receipt.afterItems ⊆ config.raw.catalog.galleryItems) then none
  else
    let next := { before with
      gallery := receipt.afterItems
      seenGallery := insert receipt.receiptId before.seenGallery }
    some (appendFanout next receipt.sourceBatchDigest
      [.galleryProjectionObserved receipt.receiptId])

private def acceptHealth (before : State)
    (receipt : ShipExpeditionSeason.CanonicalHealthReceiptInterface) : Option State := do
  let receiptId : ReceiptId := ⟨receipt.receiptId⟩
  if receipt.owner != before.identity.owner then none
  else if receiptId ∈ before.seenHealth then none
  else if receipt.before != before.health then none
  else
    let next := { before with
      career := healthCareer before.career receipt
      health := receipt.after
      seenHealth := insert receiptId before.seenHealth }
    some (appendFanout next receipt.sourceBatchDigest
      [.healthProjectionObserved receiptId])

private def acceptOrdinaryPartExchange (config : Config) (before : State)
    (receipt : ShipExpeditionSeason.BazaarPartReceiptInterface) : Option State := do
  let receiptId : ReceiptId := ⟨receipt.receiptId⟩
  if receipt.seller != before.identity.owner && receipt.buyer != before.identity.owner then none
  else if receiptId ∈ before.seenMarket then none
  else if receipt.offered.part ∉ config.raw.catalog.ordinaryParts then none
  else if receipt.requested.part ∉ config.raw.catalog.ordinaryParts then none
  else
    let next := { before with seenMarket := insert receiptId before.seenMarket }
    some (appendFanout next receipt.sourceBatchDigest
      [.ordinaryPartExchangeObserved receiptId])

private def acceptHolderFlair (config : Config) (before : State)
    (receipt : HolderCosmeticReceiptInterface) : Option State := do
  if receipt.owner != before.identity.owner then none
  else if receipt.receiptId ∈ before.seenHolder then none
  else if !config.raw.catalog.allowsAffordance receipt.affordance then none
  else
    let styled := match receipt.affordance with
      | .cosmetic id => { before with cosmetics := insert id before.cosmetics }
      | .socialMark id => { before with socialMarks := insert id before.socialMarks }
    let next := { styled with seenHolder := insert receipt.receiptId before.seenHolder }
    some (appendFanout next receipt.sourceBatchDigest
      [.holderFlairObserved receipt.receiptId])

/-- The coordinator is intentionally a dispatcher into receipt-specific
admission.  It contains no branch that computes an authoritative successor. -/
def reduce (config : Config) (before : State) : ObservedReceipt → Option State
  | .expedition receipt => acceptExpedition config before receipt
  | .attendant receipt => acceptAttendant config before receipt
  | .shipworks receipt => acceptShipworks config before receipt
  | .shipworksFailure receipt => acceptFailure before receipt
  | .craftGear receipt => acceptCraftGear config before receipt
  | .gallery receipt => acceptGallery config before receipt
  | .health receipt => acceptHealth before receipt
  | .ordinaryPartExchange receipt => acceptOrdinaryPartExchange config before receipt
  | .holderFlair receipt => acceptHolderFlair config before receipt

theorem reduce_deterministic (config : Config) (before : State)
    (receipt : ObservedReceipt) {left right : State}
    (hl : reduce config before receipt = some left)
    (hr : reduce config before receipt = some right) : left = right := by
  rw [hl] at hr
  exact Option.some.inj hr

/-! ## Laws: projections cannot launder authority -/

theorem craft_receipt_conserves_resources
    (receipt : DreggnetCraftGearReceiptInterface) :
    receipt.before.total = receipt.after.total :=
  receipt.conserved

theorem gallery_receipt_is_balance_neutral
    (receipt : GalleryGatedReceiptInterface) : receipt.balanceDelta = 0 :=
  receipt.balanceNeutral

theorem companion_status_has_no_death_case (view : DerivedCompanionView) :
    view.status = .ready ∨ view.status = .needsCare ∨ view.status = .maintenance := by
  cases view.status <;> simp

theorem expedition_runtime_receipt_only_moves_derived_career
    (config : Config) (before after : State)
    (receipt : ShipExpeditionSeason.RuntimeEventBatchReceipt)
    (h : reduce config before (.expedition receipt) = some after) :
    after.companion = before.companion ∧
      after.gear = before.gear ∧
      after.health = before.health ∧
      after.gallery = before.gallery ∧
      after.cadence = before.cadence ∧
      after.cosmetics = before.cosmetics ∧
      after.socialMarks = before.socialMarks ∧
      after.seenAttendants = before.seenAttendants ∧
      after.seenGear = before.seenGear ∧
      after.seenHealth = before.seenHealth ∧
      after.seenMarket = before.seenMarket := by
  simp only [reduce, acceptExpedition] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem holder_flair_preserves_power (config : Config) (before after : State)
    (receipt : HolderCosmeticReceiptInterface)
    (h : reduce config before (.holderFlair receipt) = some after) :
    after.powerView = before.powerView := by
  simp only [reduce, acceptHolderFlair] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> cases h <;> rfl

theorem ordinary_part_exchange_preserves_power
    (config : Config) (before after : State)
    (receipt : ShipExpeditionSeason.BazaarPartReceiptInterface)
    (h : reduce config before (.ordinaryPartExchange receipt) = some after) :
    after.powerView = before.powerView := by
  simp only [reduce, acceptOrdinaryPartExchange] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h
  rfl

theorem meaningful_failure_is_nonterminal (config : Config) (before after : State)
    (receipt : ShipworksFailureReceiptInterface)
    (h : reduce config before (.shipworksFailure receipt) = some after) :
    after.companion = before.companion ∧
      after.gear = before.gear ∧
      after.health = before.health ∧
      after.gallery = before.gallery ∧
      after.cadence = before.cadence ∧
      after.cosmetics = before.cosmetics ∧
      after.socialMarks = before.socialMarks := by
  simp only [reduce, acceptFailure] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem holder_flair_cannot_unlock (config : Config) (before after : State)
    (receipt : HolderCosmeticReceiptInterface)
    (h : reduce config before (.holderFlair receipt) = some after) :
    after.unlockHints = before.unlockHints :=
  congrArg PowerView.unlockHints (holder_flair_preserves_power config before after receipt h)

/-! ## Canonical replay stream -/

structure Boundary where
  aggregateKey : ProgressionIdentity → Digest32
  genesisHead : State → Digest32
  payloadDigest : ObservedReceipt → Digest32
  eventDigest : EventStatement → Digest32

def streamSpec (boundary : Boundary) (config : Config) : StreamSpec where
  aggregate := {
    namespaceId := config.raw.identity.federationId
    kind := SHIP_LIFE_STREAM_KIND
    key := boundary.aggregateKey config.raw.identity }
  version := ⟨config.raw.schemaVersion⟩
  genesisHead := boundary.genesisHead (initialState config)

def digestBoundary (boundary : Boundary) :
    EventSourcing.DigestBoundary ObservedReceipt where
  payloadDigest := boundary.payloadDigest
  eventDigest := boundary.eventDigest

abbrev Envelope := EventSourcing.EventEnvelope ObservedReceipt

def rebuild (boundary : Boundary) (config : Config) (events : List Envelope) :
    Except EventSourcing.Error (EventSourcing.ReplayState State) :=
  EventSourcing.rebuild (streamSpec boundary config) (digestBoundary boundary)
    (reduce config) (initialState config) events

theorem rebuild_deterministic (boundary : Boundary) (config : Config)
    (events : List Envelope) (left right : EventSourcing.ReplayState State)
    (hl : rebuild boundary config events = .ok left)
    (hr : rebuild boundary config events = .ok right) : left = right := by
  exact EventSourcing.replay_deterministic (streamSpec boundary config)
    (digestBoundary boundary) (reduce config)
    { cursor := (streamSpec boundary config).genesisCursor,
      projection := initialState config } events left right hl hr

/-! ## Ordered EventBatch bridge -/

structure IntendedBatchStatement where
  aggregate : AggregateId
  identity : ProgressionIdentity
  sourceEvent : Nat
  sourceBatchDigest : Digest32
  ordered : List DerivedFanoutEvent
deriving DecidableEq

def intendedBatch? (boundary : Boundary) (config : Config) (state : State)
    (sourceEvent : Nat) : Option IntendedBatchStatement := do
  let batch ← state.fanoutBatches.find? fun item => item.sourceEvent = sourceEvent
  some {
    aggregate := (streamSpec boundary config).aggregate
    identity := state.identity
    sourceEvent := batch.sourceEvent
    sourceBatchDigest := batch.sourceBatchDigest
    ordered := batch.ordered }

structure FanoutBoundary where
  stream : DerivedFanoutEvent → EventBatch.StreamId
  payloadDigest : DerivedFanoutEvent → Digest32
  digests : EventBatch.DigestBoundary

private def planIndexedEvents (boundary : FanoutBoundary) :
    Nat → List EventBatch.StreamHead → List DerivedFanoutEvent →
      Option (List EventBatch.IndexedEvent × List EventBatch.StreamHead)
  | _, heads, [] => some ([], heads)
  | index, heads, event :: events => do
      let stream := boundary.stream event
      let head ← EventBatch.headFor? heads stream
      let statement : EventStatement := {
        aggregate := stream.aggregate
        version := stream.version
        sequence := head.sequence + 1
        predecessor := head.head
        payloadDigest := boundary.payloadDigest event }
      let indexed : EventBatch.IndexedEvent :=
        ⟨index, statement, boundary.digests.eventDigest statement⟩
      let successor : EventBatch.StreamHead :=
        ⟨stream, statement.sequence, indexed.eventDigest⟩
      let (rest, finalHeads) ← planIndexedEvents boundary (index + 1)
        (EventBatch.replaceHead heads successor) events
      some (indexed :: rest, finalHeads)

/-- Planning returns one all-or-none envelope.  Empty projection fanout and
unknown specialist heads refuse rather than synthesizing a stream successor. -/
def eventBatchEnvelope? (boundary : FanoutBoundary)
    (coordinate : EventBatch.FinalizedTurnCoordinate)
    (initialHeads : List EventBatch.StreamHead) (batch : IntendedBatchStatement) :
    Option EventBatch.Envelope := do
  if batch.identity.federationId != coordinate.world.federationId then none
  else if batch.ordered.isEmpty then none
  else if MAX_FANOUT_EVENTS < batch.ordered.length then none
  else
    let (events, _) ← planIndexedEvents boundary 0 initialHeads batch.ordered
    let statement : EventBatch.Statement := ⟨coordinate, events⟩
    some ⟨statement, boundary.digests.batchDigest statement⟩

/-! ## Season migration preserves everything that can affect play -/

structure SeasonMigrationReceiptInterface where
  private mk ::
  sourceBatchDigest : Digest32
  priorHead : Digest32
  priorIdentity : ProgressionIdentity
  priorEventCount : Nat
  targetIdentity : ProgressionIdentity
  sameFederation : targetIdentity.federationId = priorIdentity.federationId
  sameOwner : targetIdentity.owner = priorIdentity.owner
  seasonAdvances : priorIdentity.season.value < targetIdentity.season.value

def AuthoredCatalog.unlockIds (catalog : AuthoredCatalog) : Finset UnlockHintId :=
  (catalog.unlockRules.map UnlockRule.hint).toFinset

def migrationCatalogAccepts (catalog : AuthoredCatalog) (state : State) : Bool :=
  catalog.allowsGearView state.gear &&
    decide (state.gallery ⊆ catalog.galleryItems) &&
    decide (state.cosmetics ⊆ catalog.cosmetics) &&
    decide (state.socialMarks ⊆ catalog.socialMarks) &&
    decide (state.unlockHints ⊆ catalog.unlockIds)

structure MigrationResult (before : State) where
  state : State
  powerPreserved : state.powerView = before.powerView
  expeditionHistoryPreserved : state.seenExpeditions = before.seenExpeditions
  attendantHistoryPreserved : state.seenAttendants = before.seenAttendants
  shipworksHistoryPreserved : state.seenShipworks = before.seenShipworks
  gearHistoryPreserved : state.seenGear = before.seenGear
  marketHistoryPreserved : state.seenMarket = before.seenMarket

private def migrationCore (before : State)
    (receipt : SeasonMigrationReceiptInterface) : State :=
  { before with
    identity := receipt.targetIdentity
    eventCount := 0
    fanoutBatches := []
    migrations := before.migrations ++
      [⟨before.identity, before.eventCount, receipt.priorHead⟩] }

def migrate (target : Config) (before : State)
    (receipt : SeasonMigrationReceiptInterface) : Option (MigrationResult before) := do
  if receipt.priorIdentity != before.identity then none
  else if receipt.priorEventCount != before.eventCount then none
  else if receipt.targetIdentity != target.raw.identity then none
  else if !migrationCatalogAccepts target.raw.catalog before then none
  else
    let state := migrationCore before receipt
    some {
      state
      powerPreserved := rfl
      expeditionHistoryPreserved := rfl
      attendantHistoryPreserved := rfl
      shipworksHistoryPreserved := rfl
      gearHistoryPreserved := rfl
      marketHistoryPreserved := rfl }

theorem migration_preserves_power (target : Config) (before : State)
    (receipt : SeasonMigrationReceiptInterface) (result : MigrationResult before)
    (_h : migrate target before receipt = some result) :
    result.state.powerView = before.powerView :=
  result.powerPreserved

/-! ## Executable hostile checks

⚑ **THE FIXTURES NO LONGER EVALUATE IN THIS MODULE (2026-08-08).**  This module is in the
`Dregg2.FFI` closure — the crypto archive's build — and a `native_decide` here made every
game-fixture regression a hard failure of every Rust proving target.  The fixture facts
below are now evaluation-free `check_* : Bool` definitions (a `def` body elaborates without
running), kept here because they must see the private sealed-receipt fixtures; the
EVALUATION — each `check_* = true`, pinned by `native_decide` + `#assert_compiled` — lives
in `ShipLifeProgressionFixtures.lean`, rooted in the `PathOfAngelsGuards` library.  A plain
`lake build` still runs every pin; `lake build Dregg2.FFI` never does.

Fail-closed convention: `Shipworks.Settlement` has a private constructor and
`MigrationResult`/`ReplayState` carry accepted-transition data, so the old
`.get (by native_decide)` prerequisites are now `Option`-valued (`fixtureSettlement?`,
`fixtureAfterShipworks?`, …).  A check that needs one matches on it and answers `false` on
`none`; the reachable-state defs (`fixtureAfterShipworks`, `fixtureAfterGear`,
`fixtureAfterHolder`) fall back to `initialState fixtureConfig`, which every consuming
check reads as `false` — a broken prerequisite reds the guard library, never this module.

⚠ Named residue, one construction cluster (three `native_decide`): `fixtureFailureState`
and the `replayExact`/`failedExact` proof fields of `fixtureFailureReceipt` stay
`native_decide` HERE because `ShipworksFailureReceiptInterface` carries an actual failed
replay as PROOF DATA — constructing the receipt at all requires those proofs at
elaboration.  Breaking the Shipworks replay on that plan therefore still reds this module
(and the archive).  Everything else moved. -/

private def digestFilled (value : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨value % 256, Nat.mod_lt _ (by omega)⟩
  length_eq := by simp

private def fixtureOwner : Digest32 := digestFilled 7

private def fixtureCatalog : AuthoredCatalog where
  galleryItems := [GalleryItemId.mk 1, GalleryItemId.mk 2].toFinset
  cosmetics := [CosmeticId.mk 1, CosmeticId.mk 2].toFinset
  socialMarks := [SocialMarkId.mk 1].toFinset
  gear := [GearId.mk 1, GearId.mk 2].toFinset
  blueprints := [BlueprintId.mk 1].toFinset
  ordinaryParts := [CrewFieldMissionRuntime.PartId.mk 1,
    CrewFieldMissionRuntime.PartId.mk 2].toFinset
  unlockRules := [⟨UnlockHintId.mk 1, 0, 1, 0⟩,
    ⟨UnlockHintId.mk 2, 2, 0, 0⟩]
  unlockIdsUnique := by decide
  galleryBounded := by decide

private def fixtureIdentity : ProgressionIdentity where
  federationId := digestFilled 1
  contentSession := digestFilled 2
  contentEpoch := ⟨1⟩
  season := ⟨1⟩
  activationDigest := digestFilled 3
  owner := fixtureOwner

private def fixtureRaw : RawConfig where
  schemaVersion := 1
  identity := fixtureIdentity
  catalog := fixtureCatalog
  graceEvery := 2
  graceEveryPositive := by decide

private def fixtureConfig : Config := ⟨fixtureRaw⟩

/-- `Shipworks.Settlement` has a private constructor, so there is no fallback value to
serve from a `match` — the dependent fixtures below are `Option`-valued instead, and every
check that consumes them answers `false` on `none` (fail-closed). -/
private def fixtureSettlement? : Option Shipworks.Settlement :=
  Shipworks.settle Shipworks.CareRecord.empty (Shipworks.powerSubmission 20000)

private def fixtureShipworksReceipt? : Option ShipworksSettlementReceiptInterface :=
  fixtureSettlement?.map fun settlement =>
    { receiptId := ⟨digestFilled 20⟩
      sourceBatchDigest := digestFilled 21
      owner := fixtureOwner
      settlement }

/-- ⚠ Named residue: this `.get (by native_decide)` and the two proof fields of
`fixtureFailureReceipt` below stay in this module — the receipt interface carries the
failed replay as proof data, so they must elaborate where the receipt is built. -/
private def fixtureFailureState : Shipworks.State :=
  (Shipworks.replay Shipworks.powerDispatch Shipworks.carefulPowerLoadout
    [.advance, .advance, .advance, .advance, .advance]).get (by native_decide)

private def fixtureFailureReceipt : ShipworksFailureReceiptInterface where
  receiptId := ⟨digestFilled 22⟩
  sourceBatchDigest := digestFilled 23
  owner := fixtureOwner
  dispatch := Shipworks.powerDispatch
  loadout := Shipworks.carefulPowerLoadout
  actions := [.advance, .advance, .advance, .advance, .advance]
  finalState := fixtureFailureState
  replayExact := by native_decide
  failedExact := by native_decide

private def fixtureGearView : DerivedGearView where
  loadout := [⟨1⟩]
  durability := [⟨⟨1⟩, 70, by decide⟩]
  loadoutBounded := by decide
  loadoutUnique := by decide

private def fixtureGearReceipt : DreggnetCraftGearReceiptInterface where
  receiptId := ⟨digestFilled 24⟩
  sourceBatchDigest := digestFilled 25
  owner := fixtureOwner
  operation := .craft ⟨1⟩ ⟨1⟩
  before := ⟨5, 0, 0⟩
  after := ⟨2, 2, 1⟩
  beforeValid := by decide
  afterValid := by decide
  conserved := by decide
  afterView := fixtureGearView

private def fixtureGalleryReceipt : GalleryGatedReceiptInterface where
  receiptId := ⟨digestFilled 26⟩
  sourceBatchDigest := digestFilled 27
  owner := fixtureOwner
  afterItems := [GalleryItemId.mk 1].toFinset
  balanceDelta := 0
  balanceNeutral := rfl

private def fixtureHolderReceipt : HolderCosmeticReceiptInterface where
  receiptId := ⟨digestFilled 30⟩
  sourceBatchDigest := digestFilled 31
  owner := fixtureOwner
  eligibilityNullifier := digestFilled 32
  affordance := .cosmetic ⟨1⟩

private def fixtureAfterShipworks? : Option State := do
  let receipt ← fixtureShipworksReceipt?
  reduce fixtureConfig (initialState fixtureConfig) (.shipworks receipt)

/-- Fallback unreachable while `actual_shipworks_settlement_drives_daily_projection` pins
true in `ShipLifeProgressionFixtures` — and if the settle or the fold ever refused, every
check reading this state would see the installed ship and answer `false`. -/
private def fixtureAfterShipworks : State :=
  match fixtureAfterShipworks? with
  | some state => state
  | none => initialState fixtureConfig

private def fixtureAfterGear? : Option State :=
  reduce fixtureConfig fixtureAfterShipworks (.craftGear fixtureGearReceipt)

private def fixtureAfterGear : State :=
  match fixtureAfterGear? with
  | some state => state
  | none => initialState fixtureConfig

private def fixtureAfterHolder? : Option State :=
  reduce fixtureConfig fixtureAfterGear (.holderFlair fixtureHolderReceipt)

private def fixtureAfterHolder : State :=
  match fixtureAfterHolder? with
  | some state => state
  | none => initialState fixtureConfig

private def cadenceOne : DailyCadence := advanceCadence 2 .empty ⟨10⟩
private def cadenceTwo : DailyCadence := advanceCadence 2 cadenceOne ⟨11⟩
private def cadenceForgiven : DailyCadence := advanceCadence 2 cadenceTwo ⟨13⟩
private def cadenceReset : DailyCadence := advanceCadence 2 cadenceForgiven ⟨17⟩

/-- (Pinned `= true` in `ShipLifeProgressionFixtures`.) -/
def check_cadence_earns_and_spends_one_forgiveness : Bool :=
  decide ((cadenceOne.current, cadenceTwo.current, cadenceTwo.grace,
    cadenceForgiven.current, cadenceForgiven.grace, cadenceReset.current) =
    (1, 2, 1, 3, 0, 1))

/-- (Pinned `= true` in `ShipLifeProgressionFixtures`.) -/
def check_actual_shipworks_settlement_drives_daily_projection : Bool :=
  decide (fixtureAfterShipworks.career.maintenanceSuccesses = 1 ∧
    fixtureAfterShipworks.cadence.current = 1 ∧
    UnlockHintId.mk 1 ∈ fixtureAfterShipworks.unlockHints)

/-- Matches on the ACCEPTED first settlement fold; `none` answers `false` (fail-closed),
so this can never be satisfied by the first fold refusing.
(Pinned `= true` in `ShipLifeProgressionFixtures`.) -/
def check_hostile_same_shipworks_receipt_is_idempotently_refused : Bool :=
  match fixtureShipworksReceipt?, fixtureAfterShipworks? with
  | some receipt, some after =>
      (reduce fixtureConfig after (.shipworks receipt)).isNone
  | _, _ => false

private def fixtureAfterFailure? : Option State :=
  reduce fixtureConfig (initialState fixtureConfig)
    (.shipworksFailure fixtureFailureReceipt)

/-- Matches on the accepted failure fold; `none` answers `false` (fail-closed).
(Pinned `= true` in `ShipLifeProgressionFixtures`.) -/
def check_actual_failed_replay_is_meaningful_but_nonterminal : Bool :=
  match fixtureAfterFailure? with
  | some after =>
      decide (after.career.meaningfulFailures = 1 ∧
        after.companion = none ∧
        after.gear = DerivedGearView.empty ∧
        after.health = DerivedHealthView.empty ∧
        after.gallery = (∅ : Finset GalleryItemId) ∧
        after.cadence = DailyCadence.empty)
  | none => false

/-- (Pinned `= true` in `ShipLifeProgressionFixtures`.) -/
def check_craft_projection_conserves_and_never_mints : Bool :=
  decide (fixtureGearReceipt.before.total = fixtureGearReceipt.after.total ∧
    fixtureAfterGear.gear = fixtureGearView)

private def unknownGearView : DerivedGearView :=
  ⟨[⟨999⟩], [⟨⟨999⟩, 100, by decide⟩], by decide, by decide⟩

private def unknownGearReceipt : DreggnetCraftGearReceiptInterface :=
  ⟨⟨digestFilled 101⟩, digestFilled 102, fixtureOwner, .equip ⟨999⟩,
    ⟨1, 0, 0⟩, ⟨0, 1, 0⟩, by decide, by decide, by decide, unknownGearView⟩

/-- (Pinned `= true` in `ShipLifeProgressionFixtures`.) -/
def check_hostile_unknown_gear_is_refused : Bool :=
  (reduce fixtureConfig (initialState fixtureConfig) (.craftGear unknownGearReceipt)).isNone

/-- (Pinned `= true` in `ShipLifeProgressionFixtures`.) -/
def check_holder_cosmetic_changes_style_and_exactly_no_power : Bool :=
  decide (fixtureAfterHolder.cosmetics = [CosmeticId.mk 1].toFinset ∧
    fixtureAfterHolder.powerView = fixtureAfterGear.powerView)

/-- (Pinned `= true` in `ShipLifeProgressionFixtures`.) -/
def check_gallery_projection_is_balance_neutral_and_authored : Bool :=
  decide ((reduce fixtureConfig (initialState fixtureConfig)
      (.gallery fixtureGalleryReceipt)).map State.gallery =
    some [GalleryItemId.mk 1].toFinset) &&
  decide (fixtureGalleryReceipt.balanceDelta = 0)

private def fixtureTargetIdentity : ProgressionIdentity :=
  { federationId := fixtureIdentity.federationId
    contentSession := fixtureIdentity.contentSession
    contentEpoch := ⟨2⟩
    season := ⟨2⟩
    activationDigest := digestFilled 4
    owner := fixtureIdentity.owner }

private def fixtureTargetRaw : RawConfig :=
  { fixtureRaw with identity := fixtureTargetIdentity }

private def fixtureTargetConfig : Config := ⟨fixtureTargetRaw⟩

private def fixtureMigrationReceipt : SeasonMigrationReceiptInterface where
  sourceBatchDigest := digestFilled 40
  priorHead := digestFilled 41
  priorIdentity := fixtureAfterHolder.identity
  priorEventCount := fixtureAfterHolder.eventCount
  targetIdentity := fixtureTargetIdentity
  sameFederation := rfl
  sameOwner := rfl
  seasonAdvances := by decide

private def fixtureMigrationResult? : Option (MigrationResult fixtureAfterHolder) :=
  migrate fixtureTargetConfig fixtureAfterHolder fixtureMigrationReceipt

/-- Matches on the accepted migration; `none` answers `false` (fail-closed).
(Pinned `= true` in `ShipLifeProgressionFixtures`.) -/
def check_season_migration_preserves_power_and_replay_nullifiers : Bool :=
  match fixtureMigrationResult? with
  | some result =>
      decide (result.state.powerView = fixtureAfterHolder.powerView ∧
        result.state.seenShipworks = fixtureAfterHolder.seenShipworks ∧
        result.state.seenGear = fixtureAfterHolder.seenGear ∧
        result.state.seenHolder = fixtureAfterHolder.seenHolder ∧
        result.state.identity = fixtureTargetIdentity ∧
        result.state.eventCount = 0)
  | none => false

/-! The following fixture exercises exact event replay and the real EventBatch
planner.  It hashes small integers only to make the compiled semantic tooth
observable; deployment cryptography remains the named boundary above. -/

private def fixtureBoundary : Boundary where
  aggregateKey identity := identity.activationDigest
  genesisHead _ := digestFilled 50
  payloadDigest receipt := receipt.sourceBatchDigest
  eventDigest statement := digestFilled (60 + statement.sequence)

private def fixtureShipworksEnvelope? : Option Envelope :=
  fixtureShipworksReceipt?.map fun receipt =>
    let spec := streamSpec fixtureBoundary fixtureConfig
    let statement : EventStatement := {
      aggregate := spec.aggregate
      version := spec.version
      sequence := 1
      predecessor := spec.genesisHead
      payloadDigest := fixtureBoundary.payloadDigest (.shipworks receipt) }
    ⟨statement, .shipworks receipt, fixtureBoundary.eventDigest statement⟩

private def fixtureReplayed? : Option (EventSourcing.ReplayState State) := do
  let envelope ← fixtureShipworksEnvelope?
  (rebuild fixtureBoundary fixtureConfig [envelope]).toOption

/-- Matches on the accepted replay; `none` answers `false` (fail-closed).
(Pinned `= true` in `ShipLifeProgressionFixtures`.) -/
def check_event_stream_replays_exactly_one_daily_receipt : Bool :=
  match fixtureReplayed? with
  | some replayed =>
      decide (replayed.cursor.sequence = 1 ∧
        replayed.projection = fixtureAfterShipworks)
  | none => false

private def fixtureSpecialistStream : EventBatch.StreamId where
  world := {
    federationId := fixtureIdentity.federationId
    contentRoot := digestFilled 95
    activationDigest := fixtureIdentity.activationDigest
    contentSession := fixtureIdentity.contentSession
    contentEpoch := fixtureIdentity.contentEpoch }
  aggregate := ⟨fixtureIdentity.federationId, 90, digestFilled 91⟩
  version := ⟨1⟩

private def fixtureFanoutBoundary : FanoutBoundary where
  stream _ := fixtureSpecialistStream
  payloadDigest _ := digestFilled 92
  digests := {
    eventDigest := fun statement => digestFilled (93 + statement.sequence)
    batchDigest := fun statement => digestFilled (94 + statement.events.length) }

private def fixtureCoordinate : EventBatch.FinalizedTurnCoordinate where
  world := fixtureSpecialistStream.world
  commitOrdinal := 1
  blockId := digestFilled 96
  turnHash := digestFilled 97
  receiptHash := digestFilled 98
  actorRoot := fixtureOwner
  signer := fixtureOwner

private def fixtureSpecialistHead : EventBatch.StreamHead :=
  ⟨fixtureSpecialistStream, 0, digestFilled 103⟩

private def fixtureBatchApplied? : Option EventBatch.AppliedBatch := do
  let intended ← intendedBatch? fixtureBoundary fixtureConfig fixtureAfterShipworks 1
  let envelope ← eventBatchEnvelope? fixtureFanoutBoundary fixtureCoordinate
    [fixtureSpecialistHead] intended
  (EventBatch.applyBatch fixtureFanoutBoundary.digests
    [fixtureSpecialistHead] envelope).toOption

/-- (Pinned `= true` in `ShipLifeProgressionFixtures`.) -/
def check_event_batch_accepts_complete_derived_fanout : Bool :=
  fixtureBatchApplied?.isSome

#assert_axioms reduce_deterministic
#assert_axioms craft_receipt_conserves_resources
#assert_axioms gallery_receipt_is_balance_neutral
#assert_axioms companion_status_has_no_death_case
#assert_axioms expedition_runtime_receipt_only_moves_derived_career
#assert_axioms holder_flair_preserves_power
#assert_axioms ordinary_part_exchange_preserves_power
#assert_axioms meaningful_failure_is_nonterminal
#assert_axioms holder_flair_cannot_unlock
#assert_axioms rebuild_deterministic
#assert_axioms migration_preserves_power
#assert_axioms canon_relics_are_non_market

-- The eleven fixture pins (`#assert_compiled` + `native_decide`) live in
-- `ShipLifeProgressionFixtures.lean`, rooted in `PathOfAngelsGuards` — see the header above.

end Dregg2.Games.PathOfAngels.ShipLifeProgression
