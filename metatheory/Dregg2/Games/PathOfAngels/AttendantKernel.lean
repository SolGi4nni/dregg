/-
# AttendantKernel — a finite companion-shaped game kernel without Aspect canon

This module prepares one technical seam for a persistent expedition attendant:
stable identity, care, training, equipment-gated field work, bounded progression,
and exact consumption of receipted Path of Angels contributions.  It deliberately
does **not** define an Aspect, species, personality, dialogue model, market object,
or canon fact.  A later signed content epoch may interpret the continuity anchor;
this module cannot do so.

The four layers are separate on purpose:

* `Template` is immutable authored rules and equipment vocabulary;
* `OwnedInstance` is an immutable, procedurally derived identity bound to one owner;
* `Projection` is the finite mutable game state;
* `evaluateAuthenticatedStepCandidate` is the only local semantic transition and
  consumes exact counters/credits in its proposed post-state.

There is no transfer action and no death constructor.  Exhausted condition enters
maintenance and can be repaired.  Field deployment always requires an equipped,
owned, template-declared tool with the requested capability.
-/
import Dregg2.Games.PathOfAngels.Canon
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.Attendant

open Dregg2.Games.PathOfAngels

set_option autoImplicit false

/-! ## Immutable authored vocabulary -/

structure TemplateId where
  value : Nat
deriving DecidableEq, Repr

structure EquipmentId where
  value : Nat
deriving DecidableEq, Repr

inductive Capability where
  | survey
  | repair
  | ward
  | traverse
deriving DecidableEq, Repr

structure EquipmentSpec where
  id : EquipmentId
  capability : Capability
  energyCost : Fin 21
  energy_positive : 0 < energyCost.val
  wearCost : Fin 11
  wear_positive : 0 < wearCost.val
  minimumTraining : Fin 21
deriving DecidableEq

abbrev MAX_CREDITS : Nat := 128
abbrev MAX_INVENTORY : Nat := 16

/-- The authored, immutable rules for one generic attendant chassis.  It contains
no fiction-facing name or personality. -/
structure Template where
  schemaVersion : Nat
  templateId : TemplateId
  revision : Nat
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  identityOracleId : Digest32
  issuedEpoch : EpochId
  equipment : List EquipmentSpec
  equipment_ids_unique : (equipment.map EquipmentSpec.id).Nodup
  allowedMissions : Finset MissionId
  allowedCreditMissions : Finset MissionId
  creditLimit : Fin (MAX_CREDITS + 1)
deriving DecidableEq

def Template.equipmentIds (template : Template) : Finset EquipmentId :=
  (template.equipment.map EquipmentSpec.id).toFinset

private def findEquipmentIn : List EquipmentSpec → EquipmentId → Option EquipmentSpec
  | [], _ => none
  | spec :: rest, id => if spec.id = id then some spec else findEquipmentIn rest id

private theorem findEquipmentIn_id {id : EquipmentId} {spec : EquipmentSpec} :
    ∀ items : List EquipmentSpec,
      findEquipmentIn items id = some spec → spec.id = id
  | [], h => by simp [findEquipmentIn] at h
  | head :: tail, h => by
      simp only [findEquipmentIn] at h
      split at h
      · rename_i heq
        cases h
        exact heq
      · exact findEquipmentIn_id tail h

def Template.findEquipment (template : Template) (id : EquipmentId) : Option EquipmentSpec :=
  findEquipmentIn template.equipment id

theorem Template.findEquipment_id {template : Template} {id : EquipmentId}
    {spec : EquipmentSpec} (h : template.findEquipment id = some spec) : spec.id = id := by
  exact findEquipmentIn_id template.equipment h

/-! ## Procedural immutable identity -/

structure AttendantId where
  digest : Digest32
deriving DecidableEq

/-- Globally qualified attendant identity.  `AttendantId` is a derived local
identifier; every custody, ledger, command, and allocation surface below uses
this owner-qualified key so an oracle collision cannot become a global identity
collision. -/
structure AttendantKey where
  owner : Digest32
  id : AttendantId
deriving DecidableEq

/-- Numeric visual/behavioral biases.  They are finite rendering/game inputs, not
an authored intelligence or lore claim. -/
structure DerivedProfile where
  surveyBias : Fin 8
  repairBias : Fin 8
  mobilityBias : Fin 8
  renderVariant : Fin 32
deriving DecidableEq, Repr

def seedScalar (seed : Digest32) : Nat :=
  seed.bytes.foldl (fun acc byte => (acc * 257 + byte.val) % 65536) 0

def deriveProfile (seed : Digest32) : DerivedProfile :=
  let n := seedScalar seed
  { surveyBias := ⟨n % 8, Nat.mod_lt _ (by omega)⟩
    repairBias := ⟨(n / 8) % 8, Nat.mod_lt _ (by omega)⟩
    mobilityBias := ⟨(n / 64) % 8, Nat.mod_lt _ (by omega)⟩
    renderVariant := ⟨(n / 512) % 32, Nat.mod_lt _ (by omega)⟩ }

/-- Globally identified identity derivation.  The constructor is intentionally
opaque: callers cannot substitute an arbitrary colliding function while reusing
the identifier of the deployed derivation. -/
structure IdentityOracle where
  private mk ::
  oracleId : Digest32
  hash : List Nat → Digest32

instance : CoeFun IdentityOracle (fun _ => List Nat → Digest32) := ⟨IdentityOracle.hash⟩

def identityTranscript (template : Template) (owner seed : Digest32) (serial : Nat) : List Nat :=
  [1, template.schemaVersion, template.templateId.value, template.revision,
    template.issuedEpoch.value, serial] ++
  template.federationId.bytes.map Fin.val ++
  template.contentRoot.bytes.map Fin.val ++
  template.activationDigest.bytes.map Fin.val ++
  template.contentSession.bytes.map Fin.val ++
  template.identityOracleId.bytes.map Fin.val ++
  owner.bytes.map Fin.val ++ seed.bytes.map Fin.val

def deriveId (oracle : IdentityOracle) (template : Template)
    (owner seed : Digest32) (serial : Nat) : AttendantId :=
  ⟨oracle (identityTranscript template owner seed serial)⟩

/-- Stable identity and default custody.  Inventory is bound to the same owner and
cannot change through this module.  A market/custody policy is intentionally absent. -/
structure OwnedInstance (oracle : IdentityOracle) (template : Template) where
  id : AttendantId
  owner : Digest32
  seed : Digest32
  serial : Nat
  profile : DerivedProfile
  inventory : Finset EquipmentId
  inventory_bounded : inventory.card ≤ MAX_INVENTORY
  inventory_declared : inventory ⊆ template.equipmentIds
  oracle_matches : oracle.oracleId = template.identityOracleId
  id_matches : id = deriveId oracle template owner seed serial
  profile_matches : profile = deriveProfile seed
deriving DecidableEq

/-- Proof-erased but semantically complete authored policy. -/
structure TemplatePolicy where
  schemaVersion : Nat
  templateId : TemplateId
  revision : Nat
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  identityOracleId : Digest32
  issuedEpoch : EpochId
  equipment : List EquipmentSpec
  allowedMissions : Finset MissionId
  allowedCreditMissions : Finset MissionId
  creditLimit : Fin (MAX_CREDITS + 1)
deriving DecidableEq

def Template.policy (template : Template) : TemplatePolicy where
  schemaVersion := template.schemaVersion
  templateId := template.templateId
  revision := template.revision
  federationId := template.federationId
  contentRoot := template.contentRoot
  activationDigest := template.activationDigest
  contentSession := template.contentSession
  identityOracleId := template.identityOracleId
  issuedEpoch := template.issuedEpoch
  equipment := template.equipment
  allowedMissions := template.allowedMissions
  allowedCreditMissions := template.allowedCreditMissions
  creditLimit := template.creditLimit

/-- Complete immutable instance identity and custody policy, including the
deployed identity-oracle basis and all inventory authority. -/
structure InstancePolicy where
  id : AttendantId
  owner : Digest32
  seed : Digest32
  serial : Nat
  profile : DerivedProfile
  inventory : Finset EquipmentId
  identityOracleId : Digest32
deriving DecidableEq

def OwnedInstance.policy {oracle : IdentityOracle} {template : Template}
    (owned : OwnedInstance oracle template) : InstancePolicy where
  id := owned.id
  owner := owned.owner
  seed := owned.seed
  serial := owned.serial
  profile := owned.profile
  inventory := owned.inventory
  identityOracleId := oracle.oracleId

def OwnedInstance.key {oracle : IdentityOracle} {template : Template}
    (owned : OwnedInstance oracle template) : AttendantKey where
  owner := owned.owner
  id := owned.id

/-! ## Exact contribution-credit consumption -/

/- One settled activity contribution is named by Core's replay-resistant receipt
key. -/
/-! A judged run is not yet spendable: canon settlement may still refuse its
world, replay key, content domain, or counter.  The private evidence below retains
the actual successful `settleActiveRun` equation. -/
structure SettlementEvidence where
  private mk ::
  active : ActiveRunState
  carrier : FinalizedCarrier
  claim : RunClaim
  submitted : SubmittedRun
  beforeCanon : CanonState
  settled : SettledRun
  exact : settleActiveRun active carrier claim submitted beforeCanon = some settled

structure ReceiptIdentity where
  mission : MissionSpec
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  actorRoot : Digest32
  playerKey : Digest32
  previousPlayerCounter : Nat
  playerCounter : Nat
  runSeed : Digest32
  preWorld : WorldState
  postWorld : WorldState
  contribution : Contribution
  transcriptDigest : Digest32
deriving DecidableEq

def receiptIdentity (receipt : RunReceipt) : ReceiptIdentity where
  mission := receipt.mission
  federationId := receipt.federationId
  contentRoot := receipt.contentRoot
  activationDigest := receipt.activationDigest
  contentSession := receipt.contentSession
  contentEpoch := receipt.contentEpoch
  actorRoot := receipt.actorRoot
  playerKey := receipt.playerKey
  previousPlayerCounter := receipt.previousPlayerCounter
  playerCounter := receipt.playerCounter
  runSeed := receipt.runSeed
  preWorld := receipt.preWorld
  postWorld := receipt.postWorld
  contribution := receipt.contribution
  transcriptDigest := receipt.transcriptDigest

structure CanonIdentity where
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  curatorKey : Digest32
  world : WorldState
  known : Finset ArtifactRef
  alpha : Finset ArtifactRef
  superseded : Finset ArtifactRef
  consumedRuns : Finset ReceiptKey
  playerCounterRows : List (PlayerCounterKey × PlayerCounter)
  revision : Nat
  curatorCounter : Nat
deriving DecidableEq

def canonIdentity (state : CanonState) : CanonIdentity where
  federationId := state.federationId
  contentRoot := state.contentRoot
  activationDigest := state.activationDigest
  contentSession := state.contentSession
  contentEpoch := state.contentEpoch
  curatorKey := state.curatorKey
  world := state.world
  known := state.known
  alpha := state.alpha
  superseded := state.superseded
  consumedRuns := state.consumedRuns
  playerCounterRows := state.playerCounters.rows
  revision := state.revision
  curatorCounter := state.curatorCounter

structure SettlementIdentity where
  receipt : ReceiptIdentity
  beforeCanon : CanonIdentity
  postCanon : CanonIdentity
deriving DecidableEq

structure CreditCandidate where
  private mk ::
  settlement : SettlementEvidence

def CreditCandidate.identity (candidate : CreditCandidate) : SettlementIdentity where
  receipt := receiptIdentity candidate.settlement.settled.judged.receipt
  beforeCanon := canonIdentity candidate.settlement.beforeCanon
  postCanon := canonIdentity candidate.settlement.settled.postCanon

/-- Everything the authenticated operation must commit about its proposed
canonical transition.  The nullifier names this attempt independently of the
semantic action counter. -/
structure CasTransitionIdentity where
  expectedHead : Digest32
  nextHead : Digest32
  expectedRevision : Nat
  nextRevision : Nat
  finalizedRoot : Digest32
  nullifier : Digest32
deriving DecidableEq

/-- Opaque Tier-0 compare-and-swap witness.  This is deliberately *not* called a
one-shot capability: Lean values are duplicable.  It proves only that the
adapter attested one fresh successor-shaped proposal.  Atomic comparison and
storage against the node's canonical CAS/nullifier state remains an explicit
external transition contract, modelled below. -/
structure Tier0CasTooth where
  private mk ::
  expectedHead : Digest32
  nextHead : Digest32
  expectedRevision : Nat
  nextRevision : Nat
  operationDigest : Digest32
  finalizedRoot : Digest32
  nullifier : Digest32

def Tier0CasTooth.identity (tooth : Tier0CasTooth) : CasTransitionIdentity where
  expectedHead := tooth.expectedHead
  nextHead := tooth.nextHead
  expectedRevision := tooth.expectedRevision
  nextRevision := tooth.nextRevision
  finalizedRoot := tooth.finalizedRoot
  nullifier := tooth.nullifier

/-- Canonical CAS state owned by the node adapter.  `evaluateCasTransition` is a
pure transition predicate, not an atomic store operation: evaluating it twice
from the same value produces the same fork candidate.  Deployment must perform
the compare-and-swap and nullifier insertion atomically. -/
structure CanonicalCasState where
  head : Digest32
  revision : Nat
  consumedNullifiers : Finset Digest32
deriving DecidableEq

def evaluateCasTransition (before : CanonicalCasState) (tooth : Tier0CasTooth) :
    Option CanonicalCasState :=
  if tooth.expectedHead != before.head then none
  else if tooth.expectedRevision != before.revision then none
  else if tooth.nextRevision != tooth.expectedRevision + 1 then none
  else if tooth.nextHead = tooth.expectedHead then none
  else if tooth.nullifier ∈ before.consumedNullifiers then none
  else some {
    head := tooth.nextHead
    revision := tooth.nextRevision
    consumedNullifiers := insert tooth.nullifier before.consumedNullifiers
  }

theorem evaluateCasTransition_records_successor {before after : CanonicalCasState}
    {tooth : Tier0CasTooth}
    (h : evaluateCasTransition before tooth = some after) :
    after.head = tooth.nextHead ∧
      after.revision = tooth.nextRevision ∧
      tooth.nullifier ∈ after.consumedNullifiers ∧
      tooth.nextRevision = tooth.expectedRevision + 1 ∧
      tooth.nextHead ≠ tooth.expectedHead := by
  unfold evaluateCasTransition at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i successor
  split at h <;> try contradiction
  rename_i advances
  split at h <;> try contradiction
  rw [← Option.some.inj h]
  simp_all

theorem evaluateCasTransition_consumed_nullifier_refused
    (before : CanonicalCasState) (tooth : Tier0CasTooth)
    (spent : tooth.nullifier ∈ before.consumedNullifiers) :
    evaluateCasTransition before tooth = none := by
  unfold evaluateCasTransition
  split <;> simp_all

theorem evaluateCasTransition_same_head_refused
    (before : CanonicalCasState) (tooth : Tier0CasTooth)
    (same : tooth.nextHead = tooth.expectedHead) :
    evaluateCasTransition before tooth = none := by
  unfold evaluateCasTransition
  split <;> simp_all

structure CanonicalSettlementBinding where
  settlement : SettlementIdentity
  cas : CasTransitionIdentity
deriving DecidableEq

structure CanonicalSettlementCapability where
  private mk ::
  tooth : Tier0CasTooth
  binding : CanonicalSettlementBinding
  oracle : CanonicalSettlementBinding → Digest32
  settlementDigest : Digest32
  digest_exact : settlementDigest = oracle binding

/-- Spendable only after an opaque network-finality capability binds the complete
local settlement identity. -/
structure Credit where
  private mk ::
  candidate : CreditCandidate
  canonical : CanonicalSettlementCapability
  canonical_exact : canonical.binding.settlement = candidate.identity

def Credit.receipt (credit : Credit) : RunReceipt := credit.candidate.settlement.settled.judged.receipt
def Credit.key (credit : Credit) : ReceiptKey := credit.receipt.key
def Credit.contribution (credit : Credit) : Contribution := credit.receipt.contribution
def Credit.contentRoot (credit : Credit) : Digest32 := credit.receipt.contentRoot
def Credit.activationDigest (credit : Credit) : Digest32 := credit.receipt.activationDigest
def Credit.missionId (credit : Credit) : MissionId := credit.receipt.mission.missionId
def Credit.runSeed (credit : Credit) : Digest32 := credit.receipt.runSeed
def Credit.transcriptDigest (credit : Credit) : Digest32 := credit.receipt.transcriptDigest
def Credit.postCanon (credit : Credit) : CanonState := credit.candidate.settlement.settled.postCanon
def Credit.settlementIdentity (credit : Credit) : SettlementIdentity := credit.candidate.identity
def Credit.canonicalHead (credit : Credit) : Digest32 := credit.canonical.tooth.nextHead

/-- Local/fork evaluation only.  The result is deliberately not spendable. -/
def evaluateCreditCandidate (active : ActiveRunState) (carrier : FinalizedCarrier)
    (claim : RunClaim) (submitted : SubmittedRun) (beforeCanon : CanonState) : Option CreditCandidate :=
  match h : settleActiveRun active carrier claim submitted beforeCanon with
  | none => none
  | some settled => some ⟨⟨active, carrier, claim, submitted, beforeCanon, settled, h⟩⟩

def admitCanonicalCredit (candidate : CreditCandidate)
    (capability : CanonicalSettlementCapability) : Option Credit :=
  if capability.settlementDigest != capability.oracle capability.binding then none
  else if capability.tooth.operationDigest != capability.settlementDigest then none
  else if capability.binding.cas != capability.tooth.identity then none
  else if capability.tooth.nextRevision != capability.tooth.expectedRevision + 1 then none
  else if capability.tooth.nextHead = capability.tooth.expectedHead then none
  else if h : capability.binding.settlement = candidate.identity then
    some ⟨candidate, capability, h⟩
  else none

theorem Credit.is_locally_settled (credit : Credit) :
    settleActiveRun credit.candidate.settlement.active credit.candidate.settlement.carrier
      credit.candidate.settlement.claim credit.candidate.settlement.submitted
      credit.candidate.settlement.beforeCanon = some credit.candidate.settlement.settled :=
  credit.candidate.settlement.exact

theorem Credit.is_canonical_identity_bound (credit : Credit) :
    credit.canonical.binding.settlement = credit.settlementIdentity := credit.canonical_exact

abbrev CREDIT_TOTAL_LIMIT : Nat := MAX_CREDITS * METRIC_LIMIT
abbrev CreditTotal := Fin (CREDIT_TOTAL_LIMIT + 1)

structure Consumed where
  intel : CreditTotal
  supplies : CreditTotal
  cohesion : CreditTotal
  influence : CreditTotal
  score : CreditTotal
  keys : Finset ReceiptKey
  keys_bounded : keys.card ≤ MAX_CREDITS
deriving DecidableEq

def Consumed.empty : Consumed where
  intel := 0
  supplies := 0
  cohesion := 0
  influence := 0
  score := 0
  keys := ∅
  keys_bounded := by simp [MAX_CREDITS]

/-- Atomically record the exact five metric values of one credit.  No saturation,
rounding, partial allocation, or silent duplicate-key deduplication is possible. -/
def Consumed.add (limit : Fin (MAX_CREDITS + 1)) (before : Consumed)
    (credit : Credit) : Option Consumed :=
  if _hfresh : credit.key ∉ before.keys then
    let keys := insert credit.key before.keys
    if hk : keys.card ≤ limit.val then
      if hi : before.intel.val + credit.contribution.intel.val ≤ CREDIT_TOTAL_LIMIT then
        if hs : before.supplies.val + credit.contribution.supplies.val ≤ CREDIT_TOTAL_LIMIT then
          if hc : before.cohesion.val + credit.contribution.cohesion.val ≤ CREDIT_TOTAL_LIMIT then
            if hinf : before.influence.val + credit.contribution.influence.val ≤ CREDIT_TOTAL_LIMIT then
              if hscore : before.score.val + credit.contribution.score.val ≤ CREDIT_TOTAL_LIMIT then
                some {
                  intel := ⟨before.intel.val + credit.contribution.intel.val,
                    Nat.lt_succ_of_le hi⟩
                  supplies := ⟨before.supplies.val + credit.contribution.supplies.val,
                    Nat.lt_succ_of_le hs⟩
                  cohesion := ⟨before.cohesion.val + credit.contribution.cohesion.val,
                    Nat.lt_succ_of_le hc⟩
                  influence := ⟨before.influence.val + credit.contribution.influence.val,
                    Nat.lt_succ_of_le hinf⟩
                  score := ⟨before.score.val + credit.contribution.score.val,
                    Nat.lt_succ_of_le hscore⟩
                  keys
                  keys_bounded := le_trans hk (Nat.lt_succ_iff.mp limit.isLt)
                }
              else none
            else none
          else none
        else none
      else none
    else none
  else none

theorem Consumed.add_intel_exact {limit : Fin (MAX_CREDITS + 1)}
    {before after : Consumed} {credit : Credit}
    (h : before.add limit credit = some after) :
    after.intel.val = before.intel.val + credit.contribution.intel.val := by
  unfold Consumed.add at h
  split at h <;> try contradiction
  dsimp at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  injection h with heq
  rw [← heq]

theorem Consumed.add_supplies_exact {limit : Fin (MAX_CREDITS + 1)}
    {before after : Consumed} {credit : Credit}
    (h : before.add limit credit = some after) :
    after.supplies.val = before.supplies.val + credit.contribution.supplies.val := by
  unfold Consumed.add at h
  split at h <;> try contradiction
  dsimp at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  injection h with heq
  rw [← heq]

theorem Consumed.add_records_key {limit : Fin (MAX_CREDITS + 1)}
    {before after : Consumed} {credit : Credit}
    (h : before.add limit credit = some after) : credit.key ∈ after.keys := by
  unfold Consumed.add at h
  split at h <;> try contradiction
  dsimp at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  injection h with heq
  rw [← heq]
  simp

/-- All five values and the replay key move exactly together.  This is the
atomic consumption law used by every care/training verb. -/
theorem Consumed.add_exact {limit : Fin (MAX_CREDITS + 1)}
    {before after : Consumed} {credit : Credit}
    (h : before.add limit credit = some after) :
    after.intel.val = before.intel.val + credit.contribution.intel.val ∧
    after.supplies.val = before.supplies.val + credit.contribution.supplies.val ∧
    after.cohesion.val = before.cohesion.val + credit.contribution.cohesion.val ∧
    after.influence.val = before.influence.val + credit.contribution.influence.val ∧
    after.score.val = before.score.val + credit.contribution.score.val ∧
    credit.key ∈ after.keys := by
  unfold Consumed.add at h
  split at h <;> try contradiction
  dsimp at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  injection h with heq
  rw [← heq]
  simp

theorem Consumed.add_replay_refused (limit : Fin (MAX_CREDITS + 1))
    (before : Consumed) (credit : Credit) (spent : credit.key ∈ before.keys) :
    before.add limit credit = none := by
  simp [Consumed.add, spent]

/-! ## Finite mutable projection -/

abbrev MAX_NEED : Nat := 100
abbrev MAX_TRAINING : Nat := 100
abbrev MAX_DEPLOYMENTS : Nat := 64
abbrev MAX_OWNER_ATTENDANTS : Nat := 64
abbrev MAX_OWNER_SPENT_CREDITS : Nat := 4096

abbrev Need := Fin (MAX_NEED + 1)
abbrev Training := Fin (MAX_TRAINING + 1)
abbrev DeploymentCount := Fin (MAX_DEPLOYMENTS + 1)

structure DeploymentRecord where
  mission : MissionId
  startEpoch : EpochId
  capability : Capability
  equipment : EquipmentId
deriving DecidableEq, Repr

inductive Location where
  | home
  | field (deployment : DeploymentRecord)
deriving DecidableEq, Repr

inductive OperationalStatus where
  | ready
  | needsCare
  | maintenance
deriving DecidableEq, Repr

structure Mutable where
  private mk ::
  epoch : EpochId
  location : Location
  charge : Need
  condition : Need
  rapport : Need
  training : Training
  deployments : DeploymentCount
  equipped : Option EquipmentId
  consumed : Consumed
deriving DecidableEq

/-- The mutable state plus the one exact owner-authorized action counter. -/
structure Projection where
  private mk ::
  templatePolicy : TemplatePolicy
  instancePolicy : InstancePolicy
  attendantKey : AttendantKey
  templateId : TemplateId
  templateRevision : Nat
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  issuanceRoot : Digest32
  canonicalHead : Digest32
  canonicalRevision : Nat
  mutable : Mutable
  sequence : PlayerCounter
  nextCounter : PlayerCounter
deriving DecidableEq

/-- Owner-global authority state.  Credits are spent here, not only in one
attendant projection, so a settled run cannot be fed once to each attendant. -/
structure OwnerLedger where
  private mk ::
  registryId : Digest32
  canonicalHead : Digest32
  canonicalRevision : Nat
  owner : Digest32
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  issued : Finset AttendantKey
  spentCredits : Finset ReceiptKey
  issued_bounded : issued.card ≤ MAX_OWNER_ATTENDANTS
  spent_bounded : spentCredits.card ≤ MAX_OWNER_SPENT_CREDITS
deriving DecidableEq

/-! ## Opaque ledger genesis and authenticated command capabilities -/

inductive CareMode where
  | recharge
  | repair
  | attend
deriving DecidableEq, Repr

inductive Action where
  | care (mode : CareMode) (credit : Credit)
  | train (credit : Credit)
  | equip (equipment : EquipmentId)
  | unequip
  | deploy (mission : MissionId) (capability : Capability)
  | returnHome
  | advanceEpoch (next : EpochId)

/-- Canonical owner-registry state.  Its constructor and genesis producer are
intentionally absent from the public module API until the node has an audited,
finality-backed registry adapter. -/
structure OwnerRegistry where
  private mk ::
  registryId : Digest32
  canonicalHead : Digest32
  canonicalRevision : Nat
  sequence : PlayerCounter
  openedOwners : Finset Digest32
  opened_bounded : openedOwners.card ≤ MAX_OWNER_ATTENDANTS
deriving DecidableEq

structure LedgerOpenBinding where
  beforeRegistry : OwnerRegistry
  cas : CasTransitionIdentity
  owner : Digest32
  signer : Digest32
  finalizedTurnRoot : Digest32
  templateId : TemplateId
  templateRevision : Nat
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
deriving DecidableEq

abbrev LedgerOpenOracle := LedgerOpenBinding → Digest32

/-- Opaque proof that the node authenticated and finalized this exact ledger-open
preimage.  There is deliberately no public producer in this module. -/
structure AuthenticatedLedgerOpen where
  private mk ::
  signer : Digest32
  finalizedTurnRoot : Digest32
  binding : LedgerOpenBinding
  oracle : LedgerOpenOracle
  commandDigest : Digest32
  digest_exact : commandDigest = oracle binding
  tooth : Tier0CasTooth

theorem AuthenticatedLedgerOpen.digest_bound (command : AuthenticatedLedgerOpen) :
    command.commandDigest = command.oracle command.binding := command.digest_exact

/-- One canonical owner may open once in one registry.  Reusing an old command
against the advanced registry or issuing a fresh command for the same owner both
refuse. -/
def openOwnerLedger (template : Template) (registry : OwnerRegistry)
    (command : AuthenticatedLedgerOpen) : Option (OwnerLedger × OwnerRegistry) :=
  if command.commandDigest != command.oracle command.binding then none
  else if command.binding.cas != command.tooth.identity then none
  else if command.tooth.expectedHead != registry.canonicalHead then none
  else if command.tooth.expectedRevision != registry.canonicalRevision then none
  else if command.tooth.nextRevision != command.tooth.expectedRevision + 1 then none
  else if command.tooth.operationDigest != command.commandDigest then none
  else if command.tooth.nextHead = command.tooth.expectedHead then none
  else if command.tooth.finalizedRoot != command.finalizedTurnRoot then none
  else if command.signer != command.binding.signer then none
  else if command.finalizedTurnRoot != command.binding.finalizedTurnRoot then none
  else if command.signer != command.binding.owner then none
  else if command.binding.beforeRegistry != registry then none
  else if command.binding.templateId != template.templateId then none
  else if command.binding.templateRevision != template.revision then none
  else if command.binding.federationId != template.federationId then none
  else if command.binding.contentRoot != template.contentRoot then none
  else if command.binding.activationDigest != template.activationDigest then none
  else if command.binding.contentSession != template.contentSession then none
  else if command.binding.owner ∈ registry.openedOwners then none
  else do
    let nextSequence ← registry.sequence.next
    let openedOwners := insert command.binding.owner registry.openedOwners
    if hb : openedOwners.card ≤ MAX_OWNER_ATTENDANTS then
      some ({
        registryId := registry.registryId
        canonicalHead := command.tooth.nextHead
        canonicalRevision := command.tooth.nextRevision
        owner := command.binding.owner
        federationId := template.federationId
        contentRoot := template.contentRoot
        activationDigest := template.activationDigest
        contentSession := template.contentSession
        issued := ∅
        spentCredits := ∅
        issued_bounded := by simp [MAX_OWNER_ATTENDANTS]
        spent_bounded := by simp [MAX_OWNER_SPENT_CREDITS]
      }, {
        registryId := registry.registryId
        canonicalHead := command.tooth.nextHead
        canonicalRevision := command.tooth.nextRevision
        sequence := nextSequence
        openedOwners
        opened_bounded := hb
      })
    else none

theorem openOwnerLedger_opened_owner_refused (template : Template)
    (registry : OwnerRegistry) (command : AuthenticatedLedgerOpen)
    (opened : command.binding.owner ∈ registry.openedOwners) :
    openOwnerLedger template registry command = none := by
  simp [openOwnerLedger, opened]

structure IssuanceBinding where
  beforeLedger : OwnerLedger
  cas : CasTransitionIdentity
  templatePolicy : TemplatePolicy
  instancePolicy : InstancePolicy
  signer : Digest32
  finalizedTurnRoot : Digest32
  attendantKey : AttendantKey
  templateId : TemplateId
  templateRevision : Nat
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
deriving DecidableEq

abbrev IssuanceOracle := IssuanceBinding → Digest32

/-- Opaque finalized issuance for one exact ledger pre-state and instance.  As
with action authority below, the future node adapter is the only intended
producer; this kernel intentionally exposes none. -/
structure IssuanceCommand where
  private mk ::
  signer : Digest32
  finalizedTurnRoot : Digest32
  binding : IssuanceBinding
  oracle : IssuanceOracle
  commandDigest : Digest32
  digest_exact : commandDigest = oracle binding
  tooth : Tier0CasTooth

theorem IssuanceCommand.digest_bound (command : IssuanceCommand) :
    command.commandDigest = command.oracle command.binding := command.digest_exact

def initialMutable (template : Template) : Mutable where
  epoch := template.issuedEpoch
  location := .home
  charge := 70
  condition := 70
  rapport := 40
  training := 0
  deployments := 0
  equipped := none
  consumed := .empty

/-- The only projection constructor.  It accepts no caller-supplied progression
fields and records the exact instance/template/content/finalized-turn binding. -/
def issuanceChecks {oracle : IdentityOracle} (template : Template)
    (owned : OwnedInstance oracle template) (ledger : OwnerLedger)
    (command : IssuanceCommand) : Bool :=
  decide (
    command.commandDigest = command.oracle command.binding ∧
    command.binding.cas = command.tooth.identity ∧
    command.tooth.expectedHead = ledger.canonicalHead ∧
    command.tooth.expectedRevision = ledger.canonicalRevision ∧
    command.tooth.nextRevision = command.tooth.expectedRevision + 1 ∧
    command.tooth.operationDigest = command.commandDigest ∧
    command.tooth.nextHead ≠ command.tooth.expectedHead ∧
    command.tooth.finalizedRoot = command.finalizedTurnRoot ∧
    command.signer = command.binding.signer ∧
    command.finalizedTurnRoot = command.binding.finalizedTurnRoot ∧
    command.signer = owned.owner ∧
    command.binding.beforeLedger = ledger ∧
    command.binding.templatePolicy = template.policy ∧
    command.binding.instancePolicy = owned.policy ∧
    command.binding.attendantKey = owned.key ∧
    command.binding.templateId = template.templateId ∧
    command.binding.templateRevision = template.revision ∧
    command.binding.federationId = template.federationId ∧
    command.binding.contentRoot = template.contentRoot ∧
    command.binding.activationDigest = template.activationDigest ∧
    command.binding.contentSession = template.contentSession ∧
    ledger.owner = owned.owner ∧
    ledger.registryId = command.binding.beforeLedger.registryId ∧
    ledger.federationId = template.federationId ∧
    ledger.contentRoot = template.contentRoot ∧
    ledger.activationDigest = template.activationDigest ∧
    ledger.contentSession = template.contentSession ∧
    owned.key ∉ ledger.issued)

def issue {oracle : IdentityOracle} (template : Template) (owned : OwnedInstance oracle template)
    (beforeLedger : OwnerLedger) (command : IssuanceCommand) :
    Option (Projection × OwnerLedger) :=
  if issuanceChecks template owned beforeLedger command != true then none
  else
    let issued := insert owned.key beforeLedger.issued
    if hb : issued.card ≤ MAX_OWNER_ATTENDANTS then
      some ({
        templatePolicy := template.policy
        instancePolicy := owned.policy
        attendantKey := owned.key
        templateId := template.templateId
        templateRevision := template.revision
        federationId := template.federationId
        contentRoot := template.contentRoot
        activationDigest := template.activationDigest
        contentSession := template.contentSession
        issuanceRoot := command.finalizedTurnRoot
        canonicalHead := command.tooth.nextHead
        canonicalRevision := command.tooth.nextRevision
        mutable := initialMutable template
        sequence := 0
        nextCounter := 0
      }, {
        registryId := beforeLedger.registryId
        canonicalHead := command.tooth.nextHead
        canonicalRevision := command.tooth.nextRevision
        owner := beforeLedger.owner
        federationId := beforeLedger.federationId
        contentRoot := beforeLedger.contentRoot
        activationDigest := beforeLedger.activationDigest
        contentSession := beforeLedger.contentSession
        issued := issued
        spentCredits := beforeLedger.spentCredits
        issued_bounded := hb
        spent_bounded := beforeLedger.spent_bounded
      })
    else none

theorem issue_binds_identity {oracle : IdentityOracle} {template : Template}
    {owned : OwnedInstance oracle template}
    {beforeLedger : OwnerLedger} {command : IssuanceCommand}
    {projection : Projection} {afterLedger : OwnerLedger}
    (h : issue template owned beforeLedger command = some (projection, afterLedger)) :
    projection.templatePolicy = template.policy ∧
      projection.instancePolicy = owned.policy ∧
      projection.attendantKey = owned.key ∧
      projection.templateId = template.templateId ∧
      projection.templateRevision = template.revision ∧
      projection.federationId = template.federationId ∧
      projection.contentRoot = template.contentRoot ∧
      projection.activationDigest = template.activationDigest ∧
      projection.contentSession = template.contentSession ∧
      projection.mutable = initialMutable template := by
  unfold issue at h
  split at h <;> try contradiction
  dsimp at h
  split at h <;> try contradiction
  have hp := congrArg Prod.fst (Option.some.inj h)
  simp only at hp
  rw [← hp]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def Mutable.status (state : Mutable) : OperationalStatus :=
  if state.condition.val = 0 then .maintenance
  else if state.charge.val < 10 then .needsCare
  else .ready

theorem Mutable.condition_bounded (state : Mutable) : state.condition.val ≤ MAX_NEED :=
  Nat.lt_succ_iff.mp state.condition.isLt

theorem Mutable.training_bounded (state : Mutable) : state.training.val ≤ MAX_TRAINING :=
  Nat.lt_succ_iff.mp state.training.isLt

theorem Mutable.deployments_bounded (state : Mutable) :
    state.deployments.val ≤ MAX_DEPLOYMENTS :=
  Nat.lt_succ_iff.mp state.deployments.isLt

theorem Mutable.zero_condition_is_maintenance (state : Mutable)
    (h : state.condition.val = 0) : state.status = .maintenance := by
  simp [Mutable.status, h]

/-! ## Player verbs and deterministic updates -/

/-- Exact finite identity of a settled credit when embedded in a command. -/
structure CreditPreimage where
  settlement : SettlementIdentity
  canonicalHead : Digest32
  key : ReceiptKey
  contribution : Contribution
  contentRoot : Digest32
  activationDigest : Digest32
  missionId : MissionId
  runSeed : Digest32
  transcriptDigest : Digest32
deriving DecidableEq

def Credit.preimage (credit : Credit) : CreditPreimage where
  settlement := credit.settlementIdentity
  canonicalHead := credit.canonicalHead
  key := credit.key
  contribution := credit.contribution
  contentRoot := credit.contentRoot
  activationDigest := credit.activationDigest
  missionId := credit.missionId
  runSeed := credit.runSeed
  transcriptDigest := credit.transcriptDigest

/-- Exact action preimage.  Credit-bearing actions commit to every value consumed
by care/training, not merely a lossy tag or caller-selected action hash. -/
inductive ActionPreimage where
  | care (mode : CareMode) (credit : CreditPreimage)
  | train (credit : CreditPreimage)
  | equip (equipment : EquipmentId)
  | unequip
  | deploy (mission : MissionId) (capability : Capability)
  | returnHome
  | advanceEpoch (next : EpochId)
deriving DecidableEq

def Action.preimage : Action → ActionPreimage
  | .care mode credit => .care mode credit.preimage
  | .train credit => .train credit.preimage
  | .equip equipment => .equip equipment
  | .unequip => .unequip
  | .deploy mission capability => .deploy mission capability
  | .returnHome => .returnHome
  | .advanceEpoch next => .advanceEpoch next

/-- The exact authenticated preimage.  Whole projection and owner-ledger values
are included, rather than a caller-asserted "state hash" with no invariant. -/
structure CommandBinding where
  before : Projection
  beforeLedger : OwnerLedger
  cas : CasTransitionIdentity
  templatePolicy : TemplatePolicy
  instancePolicy : InstancePolicy
  signer : Digest32
  finalizedTurnRoot : Digest32
  attendantKey : AttendantKey
  templateId : TemplateId
  templateRevision : Nat
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  expectedSequence : PlayerCounter
  counter : PlayerCounter
  action : ActionPreimage
deriving DecidableEq

abbrev CommandOracle := CommandBinding → Digest32

/-- Opaque capability produced only after an external adapter verifies a signed,
finalized Dregg command.  This module has no public producer.  Its digest commits
to the exact `CommandBinding`; the proposed action is checked against its exact
finite Lean preimage at execution. -/
structure AuthenticatedCommand where
  private mk ::
  signer : Digest32
  finalizedTurnRoot : Digest32
  binding : CommandBinding
  commandOracle : CommandOracle
  commandDigest : Digest32
  digest_exact : commandDigest = commandOracle binding
  tooth : Tier0CasTooth

theorem AuthenticatedCommand.digest_bound (command : AuthenticatedCommand) :
    command.commandDigest = command.commandOracle command.binding := command.digest_exact

structure Envelope where
  authority : AuthenticatedCommand
  action : Action

structure FieldAuthorization where
  mission : MissionId
  capability : Capability
  equipment : EquipmentId
  strength : Nat
deriving DecidableEq, Repr

inductive Event where
  | cared (mode : CareMode) (key : ReceiptKey) (amount : Nat)
  | trained (key : ReceiptKey) (amount : Nat)
  | equipped (equipment : EquipmentId)
  | unequipped
  | deployed (authorization : FieldAuthorization)
  | returned (mission : MissionId)
  | epochAdvanced (epoch : EpochId)
deriving DecidableEq

structure CreditAllocation where
  attendant : AttendantKey
  receiptKey : ReceiptKey
  missionId : MissionId
  runSeed : Digest32
  transcriptDigest : Digest32
deriving DecidableEq

def Action.credit? : Action → Option Credit
  | .care _ credit => some credit
  | .train credit => some credit
  | _ => none

def OwnerLedger.allocate (ledger : OwnerLedger) (attendant : AttendantKey)
    (action : Action) : Option (OwnerLedger × Option CreditAllocation) :=
  match action.credit? with
  | none => some (ledger, none)
  | some credit =>
      if credit.key ∈ ledger.spentCredits then none
      else
        let spentCredits := insert credit.key ledger.spentCredits
        if hb : spentCredits.card ≤ MAX_OWNER_SPENT_CREDITS then
          some ({ ledger with spentCredits, spent_bounded := hb }, some {
            attendant
            receiptKey := credit.key
            missionId := credit.missionId
            runSeed := credit.runSeed
            transcriptDigest := credit.transcriptDigest
          })
        else none

theorem OwnerLedger.allocate_global_replay_refused (ledger : OwnerLedger)
    (attendant : AttendantKey) (action : Action) (credit : Credit)
    (haction : action.credit? = some credit) (spent : credit.key ∈ ledger.spentCredits) :
    ledger.allocate attendant action = none := by
  simp [OwnerLedger.allocate, haction, spent]

theorem OwnerLedger.allocate_preserves_binding {ledger after : OwnerLedger}
    {attendant : AttendantKey} {action : Action}
    {allocation : Option CreditAllocation}
    (h : ledger.allocate attendant action = some (after, allocation)) :
    after.registryId = ledger.registryId ∧
      after.owner = ledger.owner ∧
      after.federationId = ledger.federationId ∧
      after.contentRoot = ledger.contentRoot ∧
      after.activationDigest = ledger.activationDigest ∧
      after.contentSession = ledger.contentSession := by
  unfold OwnerLedger.allocate at h
  split at h
  · simp_all
  · split at h <;> try contradiction
    dsimp at h
    split at h <;> try contradiction
    have hp := congrArg Prod.fst (Option.some.inj h)
    simp only at hp
    rw [← hp]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def creditDomainValid {oracle : IdentityOracle} (template : Template)
    (owned : OwnedInstance oracle template) (state : Mutable) (credit : Credit) : Bool :=
  decide (
    credit.receipt.federationId = template.federationId ∧
    credit.contentRoot = template.contentRoot ∧
    credit.activationDigest = template.activationDigest ∧
    credit.receipt.contentSession = template.contentSession ∧
    credit.receipt.playerKey = owned.owner ∧
    credit.missionId ∈ template.allowedCreditMissions ∧
    credit.runSeed = credit.receipt.mission.runSeed ∧
    template.issuedEpoch.value ≤ credit.receipt.contentEpoch.value ∧
    credit.receipt.contentEpoch.value ≤ state.epoch.value)

def careAmount (mode : CareMode) (credit : Credit) : Option Nat :=
  match mode with
  | .recharge | .repair =>
      if credit.contribution.supplies.val = 0 then none
      else some credit.contribution.supplies.val
  | .attend =>
      if credit.contribution.cohesion.val = 0 then none
      else some credit.contribution.cohesion.val

def trainingAmount (credit : Credit) : Option Nat :=
  if credit.contribution.intel.val = 0 then none
  else some credit.contribution.intel.val

def fieldStrength (profile : DerivedProfile) (capability : Capability)
    (training rapport : Nat) : Nat :=
  let bias := match capability with
    | .survey => profile.surveyBias.val
    | .repair => profile.repairBias.val
    | .ward => (profile.surveyBias.val + profile.repairBias.val) / 2
    | .traverse => profile.mobilityBias.val
  bias + training + rapport / 10

private def isHome : Location → Bool
  | .home => true
  | .field _ => false

private def homeEpochUpdate (state : Mutable) (next : EpochId) : Mutable :=
  { state with
    epoch := next
    charge := ⟨max 20 (state.charge.val - 2), (max_lt_iff).2 ⟨by decide,
      lt_of_le_of_lt (Nat.sub_le _ _) state.charge.isLt⟩⟩
    condition := ⟨min MAX_NEED (state.condition.val + 1), by omega⟩ }

private def fieldEpochUpdate (state : Mutable) (next : EpochId) : Mutable :=
  { state with
    epoch := next
    charge := ⟨state.charge.val - 5,
      lt_of_le_of_lt (Nat.sub_le _ _) state.charge.isLt⟩
    condition := ⟨state.condition.val - 1,
      lt_of_le_of_lt (Nat.sub_le _ _) state.condition.isLt⟩ }

/-- An epoch step is exact-next, deterministic, and nonlethal.  At home, charge
has a floor and condition recovers; in the field, fatigue can reach maintenance
but never deletes the instance. -/
def advanceOneEpoch (state : Mutable) (next : EpochId) : Option Mutable :=
  if next.value != state.epoch.value + 1 then none
  else match state.location with
    | .home => some (homeEpochUpdate state next)
    | .field _ => some (fieldEpochUpdate state next)

theorem advanceOneEpoch_exact_next {before after : Mutable} {next : EpochId}
    (h : advanceOneEpoch before next = some after) :
    next.value = before.epoch.value + 1 := by
  unfold advanceOneEpoch at h
  split at h <;> simp_all

/-- Home catch-up is ambient maintenance, not a login streak.  Processing any
exact-next home epoch preserves attachment exactly; repeated absence therefore
cannot grind rapport away. -/
theorem advanceOneEpoch_home_preserves_rapport {before after : Mutable} {next : EpochId}
    (home : before.location = .home)
    (h : advanceOneEpoch before next = some after) : after.rapport = before.rapport := by
  unfold advanceOneEpoch at h
  split at h <;> try contradiction
  simp only [home] at h
  injection h with heq
  rw [← heq]
  rfl

/-- The pure semantic transition.  Actor and replay-counter authorization wrap
this function in `evaluateAuthenticatedStepCandidate` below. -/
def coreStep {oracle : IdentityOracle} (template : Template) (owned : OwnedInstance oracle template)
    (state : Mutable) (action : Action) : Option (Mutable × Event) :=
  match action with
  | .care mode credit => do
      if !isHome state.location then none else
      if creditDomainValid template owned state credit != true then none else
      let amount ← careAmount mode credit
      let consumed ← state.consumed.add template.creditLimit credit
      match mode with
      | .recharge =>
          if h : state.charge.val + amount ≤ MAX_NEED then
            some ({ state with
              charge := ⟨state.charge.val + amount, Nat.lt_succ_of_le h⟩
              consumed }, .cared mode credit.key amount)
          else none
      | .repair =>
          if h : state.condition.val + amount ≤ MAX_NEED then
            some ({ state with
              condition := ⟨state.condition.val + amount, Nat.lt_succ_of_le h⟩
              consumed }, .cared mode credit.key amount)
          else none
      | .attend =>
          if h : state.rapport.val + amount ≤ MAX_NEED then
            some ({ state with
              rapport := ⟨state.rapport.val + amount, Nat.lt_succ_of_le h⟩
              consumed }, .cared mode credit.key amount)
          else none
  | .train credit => do
      if !isHome state.location then none else
      if creditDomainValid template owned state credit != true then none else
      if state.charge.val < 2 then none else
      let amount ← trainingAmount credit
      if h : state.training.val + amount ≤ MAX_TRAINING then
        let consumed ← state.consumed.add template.creditLimit credit
        some ({ state with
          charge := ⟨state.charge.val - 2, by omega⟩
          training := ⟨state.training.val + amount, Nat.lt_succ_of_le h⟩
          consumed }, .trained credit.key amount)
      else none
  | .equip equipment => do
      if !isHome state.location then none else
      if equipment ∉ owned.inventory then none else
      let spec ← template.findEquipment equipment
      if state.training.val < spec.minimumTraining.val then none else
      some ({ state with equipped := some equipment }, .equipped equipment)
  | .unequip =>
      if !isHome state.location then none
      else match state.equipped with
        | none => none
        | some _ => some ({ state with equipped := none }, .unequipped)
  | .deploy mission capability => do
      if !isHome state.location then none else
      if mission ∉ template.allowedMissions then none else
      let equipment ← state.equipped
      if equipment ∉ owned.inventory then none else
      let spec ← template.findEquipment equipment
      if spec.capability != capability then none else
      if state.training.val < spec.minimumTraining.val then none else
      if state.charge.val < spec.energyCost.val then none else
      if state.condition.val < spec.wearCost.val then none else
      if hdeploy : state.deployments.val < MAX_DEPLOYMENTS then
        let authorization : FieldAuthorization := {
          mission
          capability
          equipment
          strength := fieldStrength owned.profile capability
            state.training.val state.rapport.val
        }
        some ({ state with
          location := .field {
            mission
            startEpoch := state.epoch
            capability
            equipment
          }
          charge := ⟨state.charge.val - spec.energyCost.val, by omega⟩
          condition := ⟨state.condition.val - spec.wearCost.val, by omega⟩
          deployments := ⟨state.deployments.val + 1, by omega⟩
        }, .deployed authorization)
      else none
  | .returnHome =>
      match state.location with
      | .home => none
      | .field deployment =>
          if deployment.startEpoch.value < state.epoch.value then
            some ({ state with location := .home }, .returned deployment.mission)
          else none
  | .advanceEpoch next => do
      let after ← advanceOneEpoch state next
      some (after, .epochAdvanced next)

structure StepResult where
  after : Projection
  afterLedger : OwnerLedger
  event : Event
  allocation : Option CreditAllocation
deriving DecidableEq

/-- Every value that must agree before an opaque authenticated command may cross
the authority boundary, including its exact full pre-state and proposed action. -/
def authorityChecks {oracle : IdentityOracle} (template : Template)
    (owned : OwnedInstance oracle template) (ledger : OwnerLedger)
    (before : Projection) (envelope : Envelope) : Bool :=
  decide (
    before.attendantKey = owned.key ∧
    before.templateId = template.templateId ∧
    before.templateRevision = template.revision ∧
    before.federationId = template.federationId ∧
    before.contentRoot = template.contentRoot ∧
    before.activationDigest = template.activationDigest ∧
    before.contentSession = template.contentSession ∧
    before.templatePolicy = template.policy ∧
    before.instancePolicy = owned.policy ∧
    ledger.owner = owned.owner ∧
    ledger.federationId = template.federationId ∧
    ledger.contentRoot = template.contentRoot ∧
    ledger.activationDigest = template.activationDigest ∧
    ledger.contentSession = template.contentSession ∧
    owned.key ∈ ledger.issued ∧
    envelope.authority.commandDigest =
      envelope.authority.commandOracle envelope.authority.binding ∧
    envelope.authority.binding.cas = envelope.authority.tooth.identity ∧
    envelope.authority.tooth.expectedHead = ledger.canonicalHead ∧
    envelope.authority.tooth.expectedRevision = ledger.canonicalRevision ∧
    envelope.authority.tooth.nextRevision =
      envelope.authority.tooth.expectedRevision + 1 ∧
    envelope.authority.tooth.operationDigest = envelope.authority.commandDigest ∧
    envelope.authority.tooth.nextHead ≠ envelope.authority.tooth.expectedHead ∧
    envelope.authority.tooth.finalizedRoot = envelope.authority.finalizedTurnRoot ∧
    envelope.authority.signer = envelope.authority.binding.signer ∧
    envelope.authority.finalizedTurnRoot =
      envelope.authority.binding.finalizedTurnRoot ∧
    envelope.authority.signer = owned.owner ∧
    envelope.authority.binding.before = before ∧
    envelope.authority.binding.beforeLedger = ledger ∧
    envelope.authority.binding.templatePolicy = template.policy ∧
    envelope.authority.binding.instancePolicy = owned.policy ∧
    envelope.authority.binding.attendantKey = owned.key ∧
    envelope.authority.binding.templateId = template.templateId ∧
    envelope.authority.binding.templateRevision = template.revision ∧
    envelope.authority.binding.federationId = template.federationId ∧
    envelope.authority.binding.contentRoot = template.contentRoot ∧
    envelope.authority.binding.activationDigest = template.activationDigest ∧
    envelope.authority.binding.contentSession = template.contentSession ∧
    envelope.authority.binding.beforeLedger.registryId = ledger.registryId ∧
    envelope.authority.binding.expectedSequence = before.sequence ∧
    envelope.authority.binding.counter = before.nextCounter ∧
    envelope.authority.binding.action = envelope.action.preimage)

private def advanceProjection (before : Projection) (mutable : Mutable)
    (canonicalHead : Digest32) (canonicalRevision : Nat)
    (sequence nextCounter : PlayerCounter) : Projection :=
  { before with mutable, canonicalHead, canonicalRevision, sequence, nextCounter }

/-- Pure evaluation of an authenticated step *candidate*: exact issued identity,
owner-ledger, content domain, pre-state sequence, and next counter, followed by
the Lean semantic transition.  Rejected candidates consume neither counter nor
credit.  A successful result is not by itself canonically committed; the node
must atomically apply `evaluateCasTransition` against its stored head/nullifiers. -/
def evaluateAuthenticatedStepCandidate {oracle : IdentityOracle} (template : Template)
    (owned : OwnedInstance oracle template)
    (beforeLedger : OwnerLedger) (before : Projection)
    (envelope : Envelope) : Option StepResult :=
  if authorityChecks template owned beforeLedger before envelope != true then none
  else do
    /- Both finite orderings refuse at exhaustion; neither wraps. -/
    let nextSequence ← before.sequence.next
    let nextCounter ← before.nextCounter.next
    let (afterLedger, allocation) ← beforeLedger.allocate owned.key envelope.action
    let (mutable, event) ← coreStep template owned before.mutable envelope.action
    some {
      after := advanceProjection before mutable envelope.authority.tooth.nextHead
        envelope.authority.tooth.nextRevision nextSequence nextCounter
      afterLedger := { afterLedger with
        canonicalHead := envelope.authority.tooth.nextHead
        canonicalRevision := envelope.authority.tooth.nextRevision }
      event
      allocation
    }

theorem authoritativeStep_counter_advances {template : Template}
    {oracle : IdentityOracle} {owned : OwnedInstance oracle template} {before : Projection}
    {beforeLedger : OwnerLedger}
    {envelope : Envelope} {result : StepResult}
    (h : evaluateAuthenticatedStepCandidate template owned beforeLedger before envelope = some result) :
    result.after.nextCounter.val = before.nextCounter.val + 1 := by
  unfold evaluateAuthenticatedStepCandidate at h
  split at h <;> try contradiction
  cases hs : before.sequence.next with
  | none => simp [hs] at h
  | some nextSequence =>
    cases hn : before.nextCounter.next with
    | none => simp [hs, hn] at h
    | some nextCounter =>
      cases ha : beforeLedger.allocate owned.key envelope.action with
      | none => simp [hs, hn, ha] at h
      | some allocated =>
        rcases allocated with ⟨afterLedger, allocation⟩
        cases hc : coreStep template owned before.mutable envelope.action with
        | none => simp [hs, hn, ha, hc] at h
        | some pair =>
          rcases pair with ⟨mutable, event⟩
          simp [hs, hn, ha, hc] at h
          rw [← h]
          exact PlayerCounter.next_value hn

theorem authoritativeStep_sequence_advances {template : Template}
    {oracle : IdentityOracle} {owned : OwnedInstance oracle template} {before : Projection}
    {beforeLedger : OwnerLedger} {envelope : Envelope} {result : StepResult}
    (h : evaluateAuthenticatedStepCandidate template owned beforeLedger before envelope = some result) :
    result.after.sequence.val = before.sequence.val + 1 := by
  unfold evaluateAuthenticatedStepCandidate at h
  split at h <;> try contradiction
  cases hs : before.sequence.next with
  | none => simp [hs] at h
  | some nextSequence =>
    cases hn : before.nextCounter.next with
    | none => simp [hs, hn] at h
    | some nextCounter =>
      cases ha : beforeLedger.allocate owned.key envelope.action with
      | none => simp [hs, hn, ha] at h
      | some allocated =>
        rcases allocated with ⟨afterLedger, allocation⟩
        cases hc : coreStep template owned before.mutable envelope.action with
        | none => simp [hs, hn, ha, hc] at h
        | some pair =>
          rcases pair with ⟨mutable, event⟩
          simp [hs, hn, ha, hc] at h
          rw [← h]
          exact PlayerCounter.next_value hs

theorem authoritativeStep_deterministic {template : Template}
    {oracle : IdentityOracle} {owned : OwnedInstance oracle template}
    {beforeLedger : OwnerLedger} {before : Projection} {envelope : Envelope}
    {left right : StepResult}
    (hl : evaluateAuthenticatedStepCandidate template owned beforeLedger before envelope = some left)
    (hr : evaluateAuthenticatedStepCandidate template owned beforeLedger before envelope = some right) :
    left = right := by
  rw [hl] at hr
  exact Option.some.inj hr

theorem authoritativeStep_wrong_signer_refused {oracle : IdentityOracle} (template : Template)
    (owned : OwnedInstance oracle template) (ledger : OwnerLedger) (before : Projection)
    (envelope : Envelope) (h : envelope.authority.signer ≠ owned.owner) :
    evaluateAuthenticatedStepCandidate template owned ledger before envelope = none := by
  simp [evaluateAuthenticatedStepCandidate, authorityChecks, h]

theorem authoritativeStep_counter_replay_refused {oracle : IdentityOracle} (template : Template)
    (owned : OwnedInstance oracle template) (ledger : OwnerLedger) (before : Projection)
    (envelope : Envelope) (h : envelope.authority.binding.counter ≠ before.nextCounter) :
    evaluateAuthenticatedStepCandidate template owned ledger before envelope = none := by
  simp [evaluateAuthenticatedStepCandidate, authorityChecks, h]

theorem authoritativeStep_action_substitution_refused {oracle : IdentityOracle}
    (template : Template) (owned : OwnedInstance oracle template)
    (ledger : OwnerLedger) (before : Projection) (envelope : Envelope)
    (h : envelope.authority.binding.action ≠ envelope.action.preimage) :
    evaluateAuthenticatedStepCandidate template owned ledger before envelope = none := by
  simp [evaluateAuthenticatedStepCandidate, authorityChecks, h]

theorem authoritativeStep_prestate_substitution_refused {oracle : IdentityOracle}
    (template : Template) (owned : OwnedInstance oracle template)
    (ledger : OwnerLedger) (before : Projection) (envelope : Envelope)
    (h : envelope.authority.binding.before ≠ before) :
    evaluateAuthenticatedStepCandidate template owned ledger before envelope = none := by
  simp [evaluateAuthenticatedStepCandidate, authorityChecks, h]

/-- Exhaustion is checked at the authority wrapper, before `coreStep`; a valid
game action cannot wrap the persistent counter. -/
theorem authoritativeStep_max_counter_refused {oracle : IdentityOracle} (template : Template)
    (owned : OwnedInstance oracle template) (ledger : OwnerLedger)
    (before : Projection) (envelope : Envelope)
    (hmax : before.nextCounter.val + 1 = PLAYER_COUNTER_MODULUS) :
    evaluateAuthenticatedStepCandidate template owned ledger before envelope = none := by
  unfold evaluateAuthenticatedStepCandidate
  split <;> try rfl
  cases before.sequence.next <;> simp [PlayerCounter.next, checkedPlayerCounter, hmax]

theorem authoritativeStep_preserves_binding {template : Template}
    {oracle : IdentityOracle} {owned : OwnedInstance oracle template}
    {ledger : OwnerLedger} {before : Projection} {envelope : Envelope}
    {result : StepResult}
    (h : evaluateAuthenticatedStepCandidate template owned ledger before envelope = some result) :
    result.after.templatePolicy = before.templatePolicy ∧
      result.after.instancePolicy = before.instancePolicy ∧
      result.after.attendantKey = before.attendantKey ∧
      result.after.templateId = before.templateId ∧
      result.after.templateRevision = before.templateRevision ∧
      result.after.federationId = before.federationId ∧
      result.after.contentRoot = before.contentRoot ∧
      result.after.activationDigest = before.activationDigest ∧
      result.after.contentSession = before.contentSession ∧
      result.after.issuanceRoot = before.issuanceRoot := by
  unfold evaluateAuthenticatedStepCandidate at h
  split at h <;> try contradiction
  cases hs : before.sequence.next <;> simp [hs] at h
  rename_i nextSequence
  cases hn : before.nextCounter.next <;> simp [hn] at h
  rename_i nextCounter
  cases ha : ledger.allocate owned.key envelope.action <;> simp [ha] at h
  rename_i allocated
  rcases allocated with ⟨afterLedger, allocation⟩
  cases hc : coreStep template owned before.mutable envelope.action <;> simp [hc] at h
  rename_i pair
  rcases pair with ⟨mutable, event⟩
  simp at h
  rw [← h]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem authoritativeStep_success_checks {template : Template}
    {oracle : IdentityOracle} {owned : OwnedInstance oracle template}
    {ledger : OwnerLedger} {before : Projection} {envelope : Envelope}
    {result : StepResult}
    (h : evaluateAuthenticatedStepCandidate template owned ledger before envelope = some result) :
    authorityChecks template owned ledger before envelope = true := by
  cases hc : authorityChecks template owned ledger before envelope with
  | false => simp [evaluateAuthenticatedStepCandidate, hc] at h
  | true => rfl

theorem authoritativeStep_preserves_ledger_binding {template : Template}
    {oracle : IdentityOracle} {owned : OwnedInstance oracle template}
    {ledger : OwnerLedger} {before : Projection} {envelope : Envelope}
    {result : StepResult}
    (h : evaluateAuthenticatedStepCandidate template owned ledger before envelope = some result) :
    result.afterLedger.registryId = ledger.registryId ∧
      result.afterLedger.owner = ledger.owner ∧
      result.afterLedger.federationId = ledger.federationId ∧
      result.afterLedger.contentRoot = ledger.contentRoot ∧
      result.afterLedger.activationDigest = ledger.activationDigest ∧
      result.afterLedger.contentSession = ledger.contentSession := by
  unfold evaluateAuthenticatedStepCandidate at h
  split at h <;> try contradiction
  cases hs : before.sequence.next <;> simp [hs] at h
  rename_i nextSequence
  cases hn : before.nextCounter.next <;> simp [hn] at h
  rename_i nextCounter
  cases ha : ledger.allocate owned.key envelope.action <;> simp [ha] at h
  rename_i allocated
  rcases allocated with ⟨afterLedger, allocation⟩
  have binding := OwnerLedger.allocate_preserves_binding ha
  cases hc : coreStep template owned before.mutable envelope.action <;> simp [hc] at h
  rename_i pair
  rcases pair with ⟨mutable, event⟩
  rw [← h]
  exact binding

theorem authorityChecks_owner {oracle : IdentityOracle} (template : Template)
    (owned : OwnedInstance oracle template) (ledger : OwnerLedger)
    (before : Projection) (envelope : Envelope)
    (h : authorityChecks template owned ledger before envelope = true) :
    ledger.owner = owned.owner := by
  simp only [authorityChecks, decide_eq_true_eq] at h
  exact h.2.2.2.2.2.2.2.2.2.1

/-- A receipt is indexed by the immutable instance.  It cannot substitute identity,
owner, template, or inventory while carrying a successful state transition. -/
structure TransitionReceipt (template : Template)
    {oracle : IdentityOracle} (owned : OwnedInstance oracle template) where
  beforeLedger : OwnerLedger
  before : Projection
  envelope : Envelope
  result : StepResult
  applied : evaluateAuthenticatedStepCandidate template owned beforeLedger before envelope = some result

def execute {oracle : IdentityOracle} (template : Template) (owned : OwnedInstance oracle template)
    (beforeLedger : OwnerLedger) (before : Projection) (envelope : Envelope) :
    Option (TransitionReceipt template owned) :=
  match h : evaluateAuthenticatedStepCandidate template owned beforeLedger before envelope with
  | none => none
  | some result => some ⟨beforeLedger, before, envelope, result, h⟩

theorem TransitionReceipt.identity_domain_preserved {template : Template}
    {oracle : IdentityOracle} {owned : OwnedInstance oracle template}
    (receipt : TransitionReceipt template owned) :
    receipt.result.after.attendantKey = receipt.before.attendantKey ∧
      receipt.result.after.templateId = receipt.before.templateId ∧
      receipt.result.after.templateRevision = receipt.before.templateRevision ∧
      receipt.result.after.federationId = receipt.before.federationId ∧
      receipt.result.after.contentRoot = receipt.before.contentRoot ∧
      receipt.result.after.activationDigest = receipt.before.activationDigest ∧
      receipt.result.after.contentSession = receipt.before.contentSession := by
  have binding := authoritativeStep_preserves_binding receipt.applied
  rcases binding with ⟨_, _, key, templateId, revision, federation,
    contentRoot, activation, session, _⟩
  exact ⟨key, templateId, revision, federation, contentRoot, activation, session⟩

theorem TransitionReceipt.owner_ledger_preserved {template : Template}
    {oracle : IdentityOracle} {owned : OwnedInstance oracle template}
    (receipt : TransitionReceipt template owned) :
    receipt.beforeLedger.owner = owned.owner ∧
      receipt.result.afterLedger.owner = owned.owner := by
  have checks := authoritativeStep_success_checks receipt.applied
  have beforeOwner := authorityChecks_owner template owned receipt.beforeLedger
    receipt.before receipt.envelope checks
  have preserved := authoritativeStep_preserves_ledger_binding receipt.applied
  exact ⟨beforeOwner, preserved.2.1.trans beforeOwner⟩

/-! ## Upgrade continuity seam, with no interpretation authority -/

/-- A later, separately activated content type can refer to this continuity data.
Nothing here assigns it an Aspect kind, lore, personality, copying rule, or market policy. -/
structure ContinuityAnchor where
  private mk ::
  templatePolicy : TemplatePolicy
  instancePolicy : InstancePolicy
  /-- Exact mutable state, not merely a counter-shaped label.  A later upgrader
  can therefore preserve or deliberately transform every need, progression,
  equipment, consumed-credit, epoch, and replay field. -/
  projection : Projection
deriving DecidableEq

def TransitionReceipt.continuityAnchor {oracle : IdentityOracle} {template : Template}
    {owned : OwnedInstance oracle template}
    (receipt : TransitionReceipt template owned) : ContinuityAnchor where
  templatePolicy := receipt.result.after.templatePolicy
  instancePolicy := receipt.result.after.instancePolicy
  projection := receipt.result.after

theorem continuity_identity_survives_transition {template : Template}
    {oracle : IdentityOracle} {owned : OwnedInstance oracle template}
    (receipt : TransitionReceipt template owned) :
    receipt.continuityAnchor.instancePolicy = receipt.before.instancePolicy := by
  exact (authoritativeStep_preserves_binding receipt.applied).2.1

theorem TransitionReceipt.continuity_exact {template : Template}
    {oracle : IdentityOracle} {owned : OwnedInstance oracle template}
    (receipt : TransitionReceipt template owned) :
    receipt.continuityAnchor.projection = receipt.result.after ∧
      receipt.continuityAnchor.templatePolicy = receipt.result.after.templatePolicy ∧
      receipt.continuityAnchor.instancePolicy = receipt.result.after.instancePolicy :=
  ⟨rfl, rfl, rfl⟩

/-! ## Executable settled-credit care/training/field loop and hostile cases -/

def digestByte (byte : Fin 256) : Digest32 where
  bytes := List.replicate 32 byte
  length_eq := by simp

private def fixtureOracle : IdentityOracle where
  oracleId := digestByte 29
  hash := fun transcript =>
    digestByte ⟨transcript.foldl (fun acc n => (acc + n) % 256) 0 % 256,
      Nat.mod_lt _ (by omega)⟩

def fixtureFederation : Digest32 := digestByte 17
def fixtureContentRoot : Digest32 := digestByte 19
def fixtureActivation : Digest32 := digestByte 21
def fixtureSession : Digest32 := digestByte 23
def fixtureOwner : Digest32 := digestByte 41
def hostileOwner : Digest32 := digestByte 99
def fixtureSeed : Digest32 := digestByte 7
def fixtureActorRoot : Digest32 := digestByte 61
def fixtureIssuanceRoot : Digest32 := digestByte 63
def fixtureCommandDigest : Digest32 := digestByte 65
def fixtureSupplyMission : MissionId := ⟨600⟩
def fixtureIntelMission : MissionId := ⟨601⟩
def fixtureFieldMission : MissionId := ⟨700⟩
def fixtureTool : EquipmentId := ⟨3⟩
def fixtureBorrowedTool : EquipmentId := ⟨4⟩

def metric (value : Nat) (bound : value ≤ METRIC_LIMIT) : Metric :=
  ⟨value, Nat.lt_succ_of_le bound⟩

def supplyContribution : Contribution where
  intel := 0
  supplies := metric 10 (by decide)
  cohesion := 0
  influence := 0
  score := 0
  relics := ∅
  relics_bounded := by simp

def intelContribution : Contribution where
  intel := metric 3 (by decide)
  supplies := 0
  cohesion := 0
  influence := 0
  score := 0
  relics := ∅
  relics_bounded := by simp

def fixtureMissionSpec (missionId : MissionId) (artifactId : ArtifactId)
    (runSeed : Digest32) (reward : Contribution) : MissionSpec where
  missionId
  artifact := {
    missionId
    artifactId
    sourceDigest := digestByte 71
    contentDigest := digestByte 73
  }
  epoch := ⟨1⟩
  federationId := fixtureFederation
  contentRoot := fixtureContentRoot
  activationDigest := fixtureActivation
  contentSession := fixtureSession
  runSeed
  budget := {
    intel := reward.intel
    supplies := reward.supplies
    cohesion := reward.cohesion
    influence := reward.influence
    score := reward.score
    relics := ⟨reward.relics.card, Nat.lt_succ_of_le reward.relics_bounded⟩
  }
  allowedRelics := reward.relics
  privacy := .public
  ballot := .none
  artifact_matches := rfl
  allowed_relics_bounded := le_trans reward.relics_bounded (by decide)

def fixtureSupplySpec : MissionSpec :=
  fixtureMissionSpec fixtureSupplyMission ⟨80⟩ (digestByte 81) supplyContribution

def fixtureIntelSpec : MissionSpec :=
  fixtureMissionSpec fixtureIntelMission ⟨82⟩ (digestByte 83) intelContribution

def fixtureSignalConfig (mission : MissionSpec) (reward : Contribution)
    (accepted : mission.acceptsContribution reward = true) : SignalTriangulation.Config where
  target := SignalTriangulation.targetFromSeed mission.runSeed
  mission
  reward
  reward_accepted := accepted
  target_eq := rfl

def fixtureSupplyConfig : SignalTriangulation.Config :=
  fixtureSignalConfig fixtureSupplySpec supplyContribution (by decide)

def fixtureIntelConfig : SignalTriangulation.Config :=
  fixtureSignalConfig fixtureIntelSpec intelContribution (by decide)

def fixtureToolSpec : EquipmentSpec where
  id := fixtureTool
  capability := .survey
  energyCost := 5
  energy_positive := by decide
  wearCost := 2
  wear_positive := by decide
  minimumTraining := 3

def fixtureBorrowedToolSpec : EquipmentSpec where
  id := fixtureBorrowedTool
  capability := .repair
  energyCost := 4
  energy_positive := by decide
  wearCost := 1
  wear_positive := by decide
  minimumTraining := 0

private def fixtureTemplate : Template where
  schemaVersion := 1
  templateId := ⟨1⟩
  revision := 1
  federationId := fixtureFederation
  contentRoot := fixtureContentRoot
  activationDigest := fixtureActivation
  contentSession := fixtureSession
  identityOracleId := fixtureOracle.oracleId
  issuedEpoch := ⟨1⟩
  equipment := [fixtureToolSpec, fixtureBorrowedToolSpec]
  equipment_ids_unique := by decide
  allowedMissions := {fixtureFieldMission}
  allowedCreditMissions := {fixtureSupplyMission, fixtureIntelMission}
  creditLimit := 16

private def fixtureInstance : OwnedInstance fixtureOracle fixtureTemplate where
  id := deriveId fixtureOracle fixtureTemplate fixtureOwner fixtureSeed 1
  owner := fixtureOwner
  seed := fixtureSeed
  serial := 1
  profile := deriveProfile fixtureSeed
  inventory := {fixtureTool}
  inventory_bounded := by decide
  inventory_declared := by decide
  oracle_matches := rfl
  id_matches := rfl
  profile_matches := rfl

private def fixtureInstanceTwo : OwnedInstance fixtureOracle fixtureTemplate where
  id := deriveId fixtureOracle fixtureTemplate fixtureOwner fixtureSeed 2
  owner := fixtureOwner
  seed := fixtureSeed
  serial := 2
  profile := deriveProfile fixtureSeed
  inventory := {fixtureTool}
  inventory_bounded := by decide
  inventory_declared := by decide
  oracle_matches := rfl
  id_matches := rfl
  profile_matches := rfl

private def fixtureTemplateAltered : Template where
  schemaVersion := fixtureTemplate.schemaVersion
  templateId := fixtureTemplate.templateId
  revision := fixtureTemplate.revision
  federationId := fixtureTemplate.federationId
  contentRoot := fixtureTemplate.contentRoot
  activationDigest := fixtureTemplate.activationDigest
  contentSession := fixtureTemplate.contentSession
  identityOracleId := fixtureTemplate.identityOracleId
  issuedEpoch := fixtureTemplate.issuedEpoch
  equipment := fixtureTemplate.equipment
  equipment_ids_unique := fixtureTemplate.equipment_ids_unique
  allowedMissions := ∅
  allowedCreditMissions := fixtureTemplate.allowedCreditMissions
  creditLimit := fixtureTemplate.creditLimit

private def fixtureAlteredInstance : OwnedInstance fixtureOracle fixtureTemplateAltered where
  id := deriveId fixtureOracle fixtureTemplateAltered fixtureOwner fixtureSeed 1
  owner := fixtureOwner
  seed := fixtureSeed
  serial := 1
  profile := deriveProfile fixtureSeed
  inventory := {fixtureTool}
  inventory_bounded := by decide
  inventory_declared := by decide
  oracle_matches := rfl
  id_matches := rfl
  profile_matches := rfl

private def fixtureNoToolInstance : OwnedInstance fixtureOracle fixtureTemplate where
  id := fixtureInstance.id
  owner := fixtureOwner
  seed := fixtureSeed
  serial := 1
  profile := deriveProfile fixtureSeed
  inventory := ∅
  inventory_bounded := by decide
  inventory_declared := by decide
  oracle_matches := rfl
  id_matches := by simp [fixtureInstance]
  profile_matches := rfl

private def hostileCollidingOracle : IdentityOracle where
  oracleId := fixtureOracle.oracleId
  hash := fun _ => fixtureInstance.id.digest

set_option maxRecDepth 4096 in
private def hostileCollidingInstance :
    OwnedInstance hostileCollidingOracle fixtureTemplate where
  id := fixtureInstance.id
  owner := hostileOwner
  seed := digestByte 201
  serial := 77
  profile := deriveProfile (digestByte 201)
  inventory := ∅
  inventory_bounded := by decide
  inventory_declared := by decide
  oracle_matches := rfl
  id_matches := rfl
  profile_matches := rfl

def fixtureCanon : CanonState :=
  CanonState.empty fixtureFederation fixtureContentRoot fixtureActivation fixtureSession
    ⟨1⟩ (digestByte 91)

def fixtureCounterKey : PlayerCounterKey where
  federationId := fixtureFederation
  contentSession := fixtureSession
  contentEpoch := ⟨1⟩
  playerKey := fixtureOwner

def fixtureActive (config : SignalTriangulation.Config)
    (canon : CanonState) : ActiveRunState where
  game := .signal config
  federationId := fixtureFederation
  contentRoot := fixtureContentRoot
  activationDigest := fixtureActivation
  contentSession := fixtureSession
  contentEpoch := ⟨1⟩
  runSeed := config.mission.runSeed
  world := canon.world
  playerCounters := canon.playerCounters

def fixtureCarrier (canon : CanonState) : FinalizedCarrier where
  federationId := fixtureFederation
  contentRoot := fixtureContentRoot
  activationDigest := fixtureActivation
  contentSession := fixtureSession
  contentEpoch := ⟨1⟩
  actorRoot := fixtureActorRoot
  playerKey := fixtureOwner
  currentPlayerCounter := canon.playerCounters.lookup fixtureCounterKey

def fixtureClaim (config : SignalTriangulation.Config)
    (canon : CanonState) : RunClaim where
  config := (ActiveGame.signal config).configClaim
  federationId := fixtureFederation
  contentRoot := fixtureContentRoot
  activationDigest := fixtureActivation
  contentSession := fixtureSession
  contentEpoch := ⟨1⟩
  runSeed := config.mission.runSeed
  actorRoot := fixtureActorRoot
  playerKey := fixtureOwner
  claimedPreviousPlayerCounter := (fixtureCarrier canon).currentPlayerCounter.val

def fixtureSubmitted (config : SignalTriangulation.Config) : SubmittedRun :=
  .signal [.submit config.target]

private def fixtureSettlementOracle : CanonicalSettlementBinding → Digest32 := fun binding =>
  digestByte ⟨(binding.settlement.receipt.playerCounter +
    binding.settlement.postCanon.revision + seedScalar binding.cas.nullifier + 131) % 256,
    Nat.mod_lt _ (by omega)⟩

private def fixtureCanonicalSettlement (candidate : CreditCandidate) :
    CanonicalSettlementCapability :=
  let cas : CasTransitionIdentity := {
    expectedHead := digestByte 131
    nextHead := digestByte ⟨(132 + candidate.identity.receipt.playerCounter) % 256,
      Nat.mod_lt _ (by omega)⟩
    expectedRevision := candidate.identity.beforeCanon.revision
    nextRevision := candidate.identity.postCanon.revision
    finalizedRoot := digestByte 133
    nullifier := digestByte ⟨(170 + candidate.identity.receipt.playerCounter) % 256,
      Nat.mod_lt _ (by omega)⟩
  }
  let binding : CanonicalSettlementBinding := { settlement := candidate.identity, cas }
  {
    tooth := {
      expectedHead := cas.expectedHead
      nextHead := cas.nextHead
      expectedRevision := cas.expectedRevision
      nextRevision := cas.nextRevision
      operationDigest := fixtureSettlementOracle binding
      finalizedRoot := cas.finalizedRoot
      nullifier := cas.nullifier
    }
    binding
    oracle := fixtureSettlementOracle
    settlementDigest := fixtureSettlementOracle binding
    digest_exact := rfl
  }

private def fixtureSettle (config : SignalTriangulation.Config)
    (canon : CanonState) : Option Credit := do
  let candidate ← evaluateCreditCandidate (fixtureActive config canon) (fixtureCarrier canon)
    (fixtureClaim config canon) (fixtureSubmitted config) canon
  admitCanonicalCredit candidate (fixtureCanonicalSettlement candidate)

private def fixtureCredits : Option (Credit × Credit) := do
  let supply ← fixtureSettle fixtureSupplyConfig fixtureCanon
  let intel ← fixtureSettle fixtureIntelConfig supply.postCanon
  some (supply, intel)

private structure Runtime where
  projection : Projection
  ledger : OwnerLedger
deriving DecidableEq

private def fixtureRegistry : OwnerRegistry where
  registryId := digestByte 111
  canonicalHead := digestByte 110
  canonicalRevision := 0
  sequence := 0
  openedOwners := ∅
  opened_bounded := by simp [MAX_OWNER_ATTENDANTS]

private def fixtureLedgerOpenOracle : LedgerOpenOracle := fun binding =>
  digestByte ⟨(binding.beforeRegistry.sequence.val + seedScalar binding.owner + 11) % 256,
    Nat.mod_lt _ (by omega)⟩

private def fixtureLedgerOpenCommand (registry : OwnerRegistry)
    (owner : Digest32) : AuthenticatedLedgerOpen :=
  let cas : CasTransitionIdentity := {
    expectedHead := registry.canonicalHead
    nextHead := digestByte 112
    expectedRevision := registry.canonicalRevision
    nextRevision := registry.canonicalRevision + 1
    finalizedRoot := fixtureIssuanceRoot
    nullifier := digestByte ⟨(seedScalar owner + registry.sequence.val + 113) % 256,
      Nat.mod_lt _ (by omega)⟩
  }
  let binding : LedgerOpenBinding := {
    beforeRegistry := registry
    cas
    owner
    signer := owner
    finalizedTurnRoot := fixtureIssuanceRoot
    templateId := fixtureTemplate.templateId
    templateRevision := fixtureTemplate.revision
    federationId := fixtureTemplate.federationId
    contentRoot := fixtureTemplate.contentRoot
    activationDigest := fixtureTemplate.activationDigest
    contentSession := fixtureTemplate.contentSession
  }
  {
    signer := owner
    finalizedTurnRoot := fixtureIssuanceRoot
    binding
    oracle := fixtureLedgerOpenOracle
    commandDigest := fixtureLedgerOpenOracle binding
    digest_exact := rfl
    tooth := {
      expectedHead := cas.expectedHead
      nextHead := cas.nextHead
      expectedRevision := cas.expectedRevision
      nextRevision := cas.nextRevision
      operationDigest := fixtureLedgerOpenOracle binding
      finalizedRoot := cas.finalizedRoot
      nullifier := cas.nullifier
    }
  }

private def fixtureIssuanceOracle : IssuanceOracle := fun binding =>
  digestByte ⟨(binding.beforeLedger.issued.card + seedScalar binding.attendantKey.id.digest + 17) % 256,
    Nat.mod_lt _ (by omega)⟩

private def fixtureIssuanceCommand {oracle : IdentityOracle} {template : Template}
    (owned : OwnedInstance oracle template) (ledger : OwnerLedger) : IssuanceCommand :=
  let cas : CasTransitionIdentity := {
    expectedHead := ledger.canonicalHead
    nextHead := digestByte ⟨(120 + ledger.issued.card) % 256, Nat.mod_lt _ (by omega)⟩
    expectedRevision := ledger.canonicalRevision
    nextRevision := ledger.canonicalRevision + 1
    finalizedRoot := fixtureIssuanceRoot
    nullifier := digestByte ⟨(180 + ledger.issued.card) % 256, Nat.mod_lt _ (by omega)⟩
  }
  let binding : IssuanceBinding := {
    beforeLedger := ledger
    cas
    templatePolicy := template.policy
    instancePolicy := owned.policy
    signer := owned.owner
    finalizedTurnRoot := fixtureIssuanceRoot
    attendantKey := owned.key
    templateId := template.templateId
    templateRevision := template.revision
    federationId := template.federationId
    contentRoot := template.contentRoot
    activationDigest := template.activationDigest
    contentSession := template.contentSession
  }
  {
    signer := owned.owner
    finalizedTurnRoot := fixtureIssuanceRoot
    binding
    oracle := fixtureIssuanceOracle
    commandDigest := fixtureIssuanceOracle binding
    digest_exact := rfl
    tooth := {
      expectedHead := cas.expectedHead
      nextHead := cas.nextHead
      expectedRevision := cas.expectedRevision
      nextRevision := cas.nextRevision
      operationDigest := fixtureIssuanceOracle binding
      finalizedRoot := cas.finalizedRoot
      nullifier := cas.nullifier
    }
  }

private def fixtureOpenedOwner : Option (OwnerLedger × OwnerRegistry) :=
  openOwnerLedger fixtureTemplate fixtureRegistry
    (fixtureLedgerOpenCommand fixtureRegistry fixtureOwner)

private def fixtureRuntime : Option Runtime := do
  let (opened, _) ← fixtureOpenedOwner
  let (projection, ledger) ← issue fixtureTemplate fixtureInstance
    opened (fixtureIssuanceCommand fixtureInstance opened)
  some { projection, ledger }

private def fixtureTwoRuntimes : Option (Projection × Projection × OwnerLedger) := do
  let (opened, _) ← fixtureOpenedOwner
  let (first, ledgerOne) ← issue fixtureTemplate fixtureInstance
    opened (fixtureIssuanceCommand fixtureInstance opened)
  let (second, ledgerTwo) ← issue fixtureTemplate fixtureInstanceTwo ledgerOne
    (fixtureIssuanceCommand fixtureInstanceTwo ledgerOne)
  some (first, second, ledgerTwo)

private def fixtureActionCode : ActionPreimage → Nat
  | .care .recharge credit => 10 + credit.key.playerCounter
  | .care .repair credit => 20 + credit.key.playerCounter
  | .care .attend credit => 30 + credit.key.playerCounter
  | .train credit => 40 + credit.key.playerCounter
  | .equip equipment => 50 + equipment.value
  | .unequip => 60
  | .deploy mission capability =>
      let capabilityTag := match capability with
        | .survey => 1 | .repair => 2 | .ward => 3 | .traverse => 4
      70 + mission.value + capabilityTag
  | .returnHome => 80
  | .advanceEpoch epoch => 90 + epoch.value

private def fixtureCommandOracle : CommandOracle := fun binding =>
  digestByte ⟨(binding.before.sequence.val + binding.counter.val +
    fixtureActionCode binding.action + seedScalar binding.attendantKey.id.digest) % 256,
    Nat.mod_lt _ (by omega)⟩

private def fixtureAuthenticatedCommand {oracle : IdentityOracle} {template : Template}
    (owned : OwnedInstance oracle template) (ledger : OwnerLedger) (projection : Projection)
    (action : Action) : AuthenticatedCommand :=
  let cas : CasTransitionIdentity := {
    expectedHead := ledger.canonicalHead
    nextHead := digestByte ⟨(140 + projection.sequence.val) % 256, Nat.mod_lt _ (by omega)⟩
    expectedRevision := ledger.canonicalRevision
    nextRevision := ledger.canonicalRevision + 1
    finalizedRoot := digestByte 101
    nullifier := digestByte ⟨(210 + projection.sequence.val + projection.nextCounter.val) % 256,
      Nat.mod_lt _ (by omega)⟩
  }
  let binding : CommandBinding := {
    before := projection
    beforeLedger := ledger
    cas
    templatePolicy := template.policy
    instancePolicy := owned.policy
    signer := owned.owner
    finalizedTurnRoot := digestByte 101
    attendantKey := owned.key
    templateId := template.templateId
    templateRevision := template.revision
    federationId := template.federationId
    contentRoot := template.contentRoot
    activationDigest := template.activationDigest
    contentSession := template.contentSession
    expectedSequence := projection.sequence
    counter := projection.nextCounter
    action := action.preimage
  }
  {
    signer := owned.owner
    finalizedTurnRoot := digestByte 101
    binding := binding
    commandOracle := fixtureCommandOracle
    commandDigest := fixtureCommandOracle binding
    digest_exact := rfl
    tooth := {
      expectedHead := cas.expectedHead
      nextHead := cas.nextHead
      expectedRevision := cas.expectedRevision
      nextRevision := cas.nextRevision
      operationDigest := fixtureCommandOracle binding
      finalizedRoot := cas.finalizedRoot
      nullifier := cas.nullifier
    }
  }

private def envelopeFor {oracle : IdentityOracle} {template : Template}
    (owned : OwnedInstance oracle template) (ledger : OwnerLedger) (projection : Projection)
    (action : Action) : Envelope where
  authority := fixtureAuthenticatedCommand owned ledger projection action
  action := action

private def act {oracle : IdentityOracle} (template : Template)
    (owned : OwnedInstance oracle template) (runtime : Runtime)
    (action : Action) : Option Runtime := do
  let result ← evaluateAuthenticatedStepCandidate template owned runtime.ledger runtime.projection
    (envelopeFor owned runtime.ledger runtime.projection action)
  some { projection := result.after, ledger := result.afterLedger }

private def play {oracle : IdentityOracle} (template : Template)
    (owned : OwnedInstance oracle template) : Runtime → List Action → Option Runtime
  | runtime, [] => some runtime
  | runtime, action :: rest => do
      let next ← act template owned runtime action
      play template owned next rest

private def playableLoop : Option Runtime := do
  let runtime ← fixtureRuntime
  let (supply, intel) ← fixtureCredits
  play fixtureTemplate fixtureInstance runtime [
    .care .recharge supply,
    .train intel,
    .equip fixtureTool,
    .deploy fixtureFieldMission .survey,
    .advanceEpoch ⟨2⟩,
    .returnHome
  ]

structure LoopSnapshot where
  epoch : Nat
  location : Location
  charge : Nat
  condition : Nat
  training : Nat
  deployments : Nat
  sequence : Nat
  counter : Nat
  consumedIntel : Nat
  consumedSupplies : Nat
  globallySpent : Nat
deriving DecidableEq

private def runtimeSnapshot (runtime : Runtime) : LoopSnapshot where
  epoch := runtime.projection.mutable.epoch.value
  location := runtime.projection.mutable.location
  charge := runtime.projection.mutable.charge.val
  condition := runtime.projection.mutable.condition.val
  training := runtime.projection.mutable.training.val
  deployments := runtime.projection.mutable.deployments.val
  sequence := runtime.projection.sequence.val
  counter := runtime.projection.nextCounter.val
  consumedIntel := runtime.projection.mutable.consumed.intel.val
  consumedSupplies := runtime.projection.mutable.consumed.supplies.val
  globallySpent := runtime.ledger.spentCredits.card

theorem playable_care_training_field_loop :
    playableLoop.map runtimeSnapshot = some {
      epoch := 2
      location := .home
      charge := 68
      condition := 67
      training := 3
      deployments := 1
      sequence := 6
      counter := 6
      consumedIntel := 3
      consumedSupplies := 10
      globallySpent := 2
    } := by native_decide

/-- A wire/UI projection can be checked, but never substituted for opaque state. -/
structure ProgressionClaim where
  attendant : AttendantKey
  epoch : Nat
  charge : Nat
  condition : Nat
  rapport : Nat
  training : Nat
  deployments : Nat
  sequence : Nat
deriving DecidableEq

def Projection.progressionClaim (projection : Projection) : ProgressionClaim where
  attendant := projection.attendantKey
  epoch := projection.mutable.epoch.value
  charge := projection.mutable.charge.val
  condition := projection.mutable.condition.val
  rapport := projection.mutable.rapport.val
  training := projection.mutable.training.val
  deployments := projection.mutable.deployments.val
  sequence := projection.sequence.val

def validateProgressionClaim (projection : Projection) (claim : ProgressionClaim) : Bool :=
  decide (claim = projection.progressionClaim)

theorem hostile_forged_progression_claim_is_refused :
    (fixtureRuntime.map fun runtime =>
      let honest := runtime.projection.progressionClaim
      validateProgressionClaim runtime.projection { honest with training := honest.training + 1 }) =
      some false := by native_decide

theorem hostile_judged_but_unsettled_credit_is_unavailable :
    let active := fixtureActive fixtureSupplyConfig fixtureCanon
    let carrier := fixtureCarrier fixtureCanon
    let claim := fixtureClaim fixtureSupplyConfig fixtureCanon
    let submitted := fixtureSubmitted fixtureSupplyConfig
    let wrongCanon := CanonState.empty fixtureFederation (digestByte 222)
      fixtureActivation fixtureSession ⟨1⟩ (digestByte 91)
    (judgeActive active carrier claim submitted).isSome = true ∧
      (evaluateCreditCandidate active carrier claim submitted wrongCanon).isNone = true := by native_decide

theorem hostile_ledger_reopen_credit_reset_is_refused :
    (do
      let (_, afterRegistry) ← fixtureOpenedOwner
      /- This is a newly authenticated command for the advanced registry, not
      merely a replay of the stale open command.  The one-owner registry still
      refuses to manufacture a fresh empty spend set. -/
      let reopened := openOwnerLedger fixtureTemplate afterRegistry
        (fixtureLedgerOpenCommand afterRegistry fixtureOwner)
      some reopened.isNone) = some true := by native_decide

theorem hostile_owner_global_credit_replay_is_refused :
    (do
      let runtime ← fixtureRuntime
      let (supply, _) ← fixtureCredits
      let once ← act fixtureTemplate fixtureInstance runtime (.care .recharge supply)
      some (act fixtureTemplate fixtureInstance once (.care .recharge supply) |>.isNone)) =
      some true := by native_decide

theorem hostile_cross_attendant_credit_double_spend_is_refused :
    (do
      let (first, second, ledger) ← fixtureTwoRuntimes
      let (supply, _) ← fixtureCredits
      let spent ← evaluateAuthenticatedStepCandidate fixtureTemplate fixtureInstance ledger first
        (envelopeFor fixtureInstance ledger first (.care .recharge supply))
      some ((evaluateAuthenticatedStepCandidate fixtureTemplate fixtureInstanceTwo spent.afterLedger second
        (envelopeFor fixtureInstanceTwo spent.afterLedger second (.care .recharge supply))).isNone)) =
      some true := by native_decide

theorem hostile_cross_instance_envelope_is_refused :
    (fixtureTwoRuntimes.map fun triple =>
      let (first, second, ledger) := triple
      (evaluateAuthenticatedStepCandidate fixtureTemplate fixtureInstanceTwo ledger second
        (envelopeFor fixtureInstance ledger first .unequip)).isNone) = some true := by native_decide

theorem hostile_projection_transplant_is_refused :
    (fixtureTwoRuntimes.map fun triple =>
      let (first, _, ledger) := triple
      (evaluateAuthenticatedStepCandidate fixtureTemplate fixtureInstanceTwo ledger first
        (envelopeFor fixtureInstanceTwo ledger first .unequip)).isNone) = some true := by native_decide

theorem hostile_same_header_different_template_policy_is_refused :
    (fixtureRuntime.map fun runtime =>
      let substituted := envelopeFor fixtureAlteredInstance runtime.ledger runtime.projection
        (.advanceEpoch ⟨2⟩)
      let honest := envelopeFor fixtureInstance runtime.ledger runtime.projection
        (.advanceEpoch ⟨2⟩)
      (evaluateAuthenticatedStepCandidate fixtureTemplateAltered fixtureAlteredInstance runtime.ledger
        runtime.projection substituted).isNone &&
      (evaluateAuthenticatedStepCandidate fixtureTemplate fixtureInstance runtime.ledger
        runtime.projection honest).isSome) = some true := by native_decide

theorem hostile_inventory_policy_substitution_is_refused :
    (fixtureRuntime.map fun runtime =>
      let substituted := envelopeFor fixtureNoToolInstance runtime.ledger runtime.projection
        (.advanceEpoch ⟨2⟩)
      (evaluateAuthenticatedStepCandidate fixtureTemplate fixtureNoToolInstance runtime.ledger
        runtime.projection substituted).isNone) = some true := by native_decide

theorem hostile_cross_owner_colliding_identity_oracle_is_refused :
    fixtureInstance.id = hostileCollidingInstance.id ∧
    (fixtureRuntime.map fun runtime =>
      let substituted := envelopeFor hostileCollidingInstance runtime.ledger runtime.projection
        (.advanceEpoch ⟨2⟩)
      (evaluateAuthenticatedStepCandidate fixtureTemplate hostileCollidingInstance runtime.ledger
        runtime.projection substituted).isNone) = some true := by native_decide

theorem hostile_same_epoch_return_is_refused :
    (do
      let runtime ← fixtureRuntime
      let (_, intel) ← fixtureCredits
      let deployed ← play fixtureTemplate fixtureInstance runtime [
        .train intel, .equip fixtureTool, .deploy fixtureFieldMission .survey]
      some (act fixtureTemplate fixtureInstance deployed .returnHome |>.isNone)) = some true := by
  native_decide

theorem hostile_wrong_signer_is_refused :
    (fixtureRuntime.map fun runtime =>
      let envelope := envelopeFor fixtureInstance runtime.ledger runtime.projection .unequip
      (evaluateAuthenticatedStepCandidate fixtureTemplate fixtureInstance runtime.ledger runtime.projection
        { envelope with authority := { envelope.authority with signer := hostileOwner } }).isNone) =
      some true := by native_decide

theorem hostile_counter_replay_is_refused :
    (do
      let runtime ← fixtureRuntime
      let replay := envelopeFor fixtureInstance runtime.ledger runtime.projection
        (.advanceEpoch ⟨2⟩)
      let result ← evaluateAuthenticatedStepCandidate fixtureTemplate fixtureInstance runtime.ledger runtime.projection
        replay
      some (evaluateAuthenticatedStepCandidate fixtureTemplate fixtureInstance result.afterLedger result.after replay |>.isNone)) =
      some true := by native_decide

theorem hostile_stale_cas_tooth_refuses_advanced_head :
    (do
      let runtime ← fixtureRuntime
      let stale := envelopeFor fixtureInstance runtime.ledger runtime.projection
        (.advanceEpoch ⟨2⟩)
      let first ← evaluateAuthenticatedStepCandidate fixtureTemplate fixtureInstance runtime.ledger
        runtime.projection stale
      let fresh := envelopeFor fixtureInstance first.afterLedger first.after
        (.advanceEpoch ⟨3⟩)
      some ((evaluateAuthenticatedStepCandidate fixtureTemplate fixtureInstance first.afterLedger first.after stale).isNone &&
        (evaluateAuthenticatedStepCandidate fixtureTemplate fixtureInstance first.afterLedger first.after fresh).isSome)) =
      some true := by native_decide

/-- Pure Lean evaluation is intentionally replayable from an identical snapshot:
both calls produce the same fork candidate.  Canonical replay resistance lives
in the explicit CAS/nullifier transition: after the first proposed CAS state,
the identical tooth is rejected.  The node must make that state update atomic. -/
theorem hostile_same_snapshot_fork_is_explicit_and_nullifier_closes_replay :
    (do
      let runtime ← fixtureRuntime
      let envelope := envelopeFor fixtureInstance runtime.ledger runtime.projection
        (.advanceEpoch ⟨2⟩)
      let left := evaluateAuthenticatedStepCandidate fixtureTemplate fixtureInstance
        runtime.ledger runtime.projection envelope
      let right := evaluateAuthenticatedStepCandidate fixtureTemplate fixtureInstance
        runtime.ledger runtime.projection envelope
      let beforeCas : CanonicalCasState := {
        head := runtime.ledger.canonicalHead
        revision := runtime.ledger.canonicalRevision
        consumedNullifiers := ∅
      }
      let afterCas ← evaluateCasTransition beforeCas envelope.authority.tooth
      some (left.isSome && right.isSome &&
        (evaluateCasTransition beforeCas envelope.authority.tooth).isSome &&
        (evaluateCasTransition afterCas envelope.authority.tooth).isNone)) =
      some true := by native_decide

theorem hostile_wrong_canonical_settlement_identity_is_refused :
    (do
      let supply ← evaluateCreditCandidate (fixtureActive fixtureSupplyConfig fixtureCanon)
        (fixtureCarrier fixtureCanon) (fixtureClaim fixtureSupplyConfig fixtureCanon)
        (fixtureSubmitted fixtureSupplyConfig) fixtureCanon
      let intel ← evaluateCreditCandidate (fixtureActive fixtureIntelConfig supply.settlement.settled.postCanon)
        (fixtureCarrier supply.settlement.settled.postCanon)
        (fixtureClaim fixtureIntelConfig supply.settlement.settled.postCanon)
        (fixtureSubmitted fixtureIntelConfig) supply.settlement.settled.postCanon
      some (admitCanonicalCredit intel (fixtureCanonicalSettlement supply) |>.isNone)) =
      some true := by native_decide

theorem hostile_settlement_successor_and_root_substitution_are_refused :
    (do
      let candidate ← evaluateCreditCandidate (fixtureActive fixtureSupplyConfig fixtureCanon)
        (fixtureCarrier fixtureCanon) (fixtureClaim fixtureSupplyConfig fixtureCanon)
        (fixtureSubmitted fixtureSupplyConfig) fixtureCanon
      let capability := fixtureCanonicalSettlement candidate
      let changedHead := { capability with tooth := {
        capability.tooth with nextHead := digestByte 250 } }
      let changedRoot := { capability with tooth := {
        capability.tooth with finalizedRoot := digestByte 251 } }
      some ((admitCanonicalCredit candidate changedHead).isNone &&
        (admitCanonicalCredit candidate changedRoot).isNone)) = some true := by native_decide

theorem hostile_command_successor_and_root_substitution_are_refused :
    (do
      let runtime ← fixtureRuntime
      let envelope := envelopeFor fixtureInstance runtime.ledger runtime.projection
        (.advanceEpoch ⟨2⟩)
      let changedHead : Envelope := { envelope with authority := {
        envelope.authority with tooth := {
          envelope.authority.tooth with nextHead := digestByte 250 } } }
      let changedRoot : Envelope := { envelope with authority := {
        envelope.authority with tooth := {
          envelope.authority.tooth with finalizedRoot := digestByte 251 } } }
      some ((evaluateAuthenticatedStepCandidate fixtureTemplate fixtureInstance
          runtime.ledger runtime.projection changedHead).isNone &&
        (evaluateAuthenticatedStepCandidate fixtureTemplate fixtureInstance
          runtime.ledger runtime.projection changedRoot).isNone)) = some true := by native_decide

theorem hostile_action_substitution_breaks_authenticated_preimage :
    (do
      let runtime ← fixtureRuntime
      let (supply, intel) ← fixtureCredits
      let authenticated := envelopeFor fixtureInstance runtime.ledger runtime.projection
        (.care .recharge supply)
      let substituted := { authenticated with action := Action.train intel }
      let honestTrain := envelopeFor fixtureInstance runtime.ledger runtime.projection
        (.train intel)
      some ((evaluateAuthenticatedStepCandidate fixtureTemplate fixtureInstance runtime.ledger runtime.projection
        substituted).isNone &&
        (evaluateAuthenticatedStepCandidate fixtureTemplate fixtureInstance runtime.ledger runtime.projection
          honestTrain).isSome)) = some true := by native_decide

theorem hostile_prestate_substitution_breaks_authenticated_preimage :
    (do
      let runtime ← fixtureRuntime
      let (supply, _) ← fixtureCredits
      let authenticated := envelopeFor fixtureInstance runtime.ledger runtime.projection
        (.care .recharge supply)
      let changed : Projection := { runtime.projection with
        mutable := { runtime.projection.mutable with rapport := 41 } }
      let honestChanged := envelopeFor fixtureInstance runtime.ledger changed
        (.care .recharge supply)
      some ((evaluateAuthenticatedStepCandidate fixtureTemplate fixtureInstance runtime.ledger changed
        authenticated).isNone &&
        (evaluateAuthenticatedStepCandidate fixtureTemplate fixtureInstance runtime.ledger changed
          honestChanged).isSome)) = some true := by native_decide

def maxPlayerCounter : PlayerCounter :=
  ⟨PLAYER_COUNTER_MODULUS - 1, by
    have positive : 0 < PLAYER_COUNTER_MODULUS := by simp [PLAYER_COUNTER_MODULUS]
    omega⟩

theorem max_counter_refuses_before_valid_epoch :
    (fixtureRuntime.map fun runtime =>
      let exhausted := { runtime.projection with nextCounter := maxPlayerCounter }
      (evaluateAuthenticatedStepCandidate fixtureTemplate fixtureInstance runtime.ledger exhausted
        (envelopeFor fixtureInstance runtime.ledger exhausted (.advanceEpoch ⟨2⟩))).isNone) = some true := by
  native_decide

theorem field_work_without_equipment_is_refused :
    (fixtureRuntime.map fun runtime =>
      (act fixtureTemplate fixtureInstance runtime
        (.deploy fixtureFieldMission .survey)).isNone) = some true := by native_decide

theorem equipment_before_training_is_refused :
    (fixtureRuntime.map fun runtime =>
      (act fixtureTemplate fixtureInstance runtime (.equip fixtureTool)).isNone) = some true := by
  native_decide

theorem declared_but_unowned_equipment_is_refused :
    (fixtureRuntime.map fun runtime =>
      (act fixtureTemplate fixtureInstance runtime (.equip fixtureBorrowedTool)).isNone) =
      some true := by native_decide

theorem skipped_epoch_is_refused :
    (fixtureRuntime.map fun runtime =>
      (act fixtureTemplate fixtureInstance runtime (.advanceEpoch ⟨3⟩)).isNone) = some true := by
  native_decide

theorem home_absence_cannot_erase_attachment :
    (do
      let runtime ← fixtureRuntime
      let after ← play fixtureTemplate fixtureInstance runtime [
        .advanceEpoch ⟨2⟩, .advanceEpoch ⟨3⟩, .advanceEpoch ⟨4⟩]
      some (after.projection.mutable.charge.val, after.projection.mutable.condition.val,
        after.projection.mutable.rapport.val, after.projection.sequence.val)) =
      some (64, 73, 40, 3) := by native_decide

theorem fixture_identity_rejects_serial_substitution :
    fixtureInstance.id ≠ fixtureInstanceTwo.id := by native_decide

#assert_axioms Template.findEquipment_id
#assert_axioms Credit.is_locally_settled
#assert_axioms Credit.is_canonical_identity_bound
#assert_axioms evaluateCasTransition_records_successor
#assert_axioms evaluateCasTransition_consumed_nullifier_refused
#assert_axioms evaluateCasTransition_same_head_refused
#assert_axioms Consumed.add_intel_exact
#assert_axioms Consumed.add_supplies_exact
#assert_axioms Consumed.add_records_key
#assert_axioms Consumed.add_exact
#assert_axioms Consumed.add_replay_refused
#assert_axioms issue_binds_identity
#assert_axioms AuthenticatedLedgerOpen.digest_bound
#assert_axioms openOwnerLedger_opened_owner_refused
#assert_axioms IssuanceCommand.digest_bound
#assert_axioms AuthenticatedCommand.digest_bound
#assert_axioms OwnerLedger.allocate_global_replay_refused
#assert_axioms OwnerLedger.allocate_preserves_binding
#assert_axioms Mutable.condition_bounded
#assert_axioms Mutable.training_bounded
#assert_axioms Mutable.deployments_bounded
#assert_axioms Mutable.zero_condition_is_maintenance
#assert_axioms advanceOneEpoch_exact_next
#assert_axioms advanceOneEpoch_home_preserves_rapport
#assert_axioms authoritativeStep_counter_advances
#assert_axioms authoritativeStep_sequence_advances
#assert_axioms authoritativeStep_deterministic
#assert_axioms authoritativeStep_wrong_signer_refused
#assert_axioms authoritativeStep_counter_replay_refused
#assert_axioms authoritativeStep_action_substitution_refused
#assert_axioms authoritativeStep_prestate_substitution_refused
#assert_axioms authoritativeStep_max_counter_refused
#assert_axioms authoritativeStep_preserves_binding
#assert_axioms authoritativeStep_success_checks
#assert_axioms authoritativeStep_preserves_ledger_binding
#assert_axioms TransitionReceipt.identity_domain_preserved
#assert_axioms TransitionReceipt.owner_ledger_preserved
#assert_axioms continuity_identity_survives_transition
#assert_axioms TransitionReceipt.continuity_exact

#assert_compiled playable_care_training_field_loop
#assert_compiled hostile_forged_progression_claim_is_refused
#assert_compiled hostile_judged_but_unsettled_credit_is_unavailable
#assert_compiled hostile_ledger_reopen_credit_reset_is_refused
#assert_compiled hostile_owner_global_credit_replay_is_refused
#assert_compiled hostile_cross_attendant_credit_double_spend_is_refused
#assert_compiled hostile_cross_instance_envelope_is_refused
#assert_compiled hostile_projection_transplant_is_refused
#assert_compiled hostile_same_header_different_template_policy_is_refused
#assert_compiled hostile_inventory_policy_substitution_is_refused
#assert_compiled hostile_cross_owner_colliding_identity_oracle_is_refused
#assert_compiled hostile_same_epoch_return_is_refused
#assert_compiled hostile_wrong_signer_is_refused
#assert_compiled hostile_counter_replay_is_refused
#assert_compiled hostile_stale_cas_tooth_refuses_advanced_head
#assert_compiled hostile_same_snapshot_fork_is_explicit_and_nullifier_closes_replay
#assert_compiled hostile_wrong_canonical_settlement_identity_is_refused
#assert_compiled hostile_settlement_successor_and_root_substitution_are_refused
#assert_compiled hostile_command_successor_and_root_substitution_are_refused
#assert_compiled hostile_action_substitution_breaks_authenticated_preimage
#assert_compiled hostile_prestate_substitution_breaks_authenticated_preimage
#assert_compiled max_counter_refuses_before_valid_epoch
#assert_compiled field_work_without_equipment_is_refused
#assert_compiled equipment_before_training_is_refused
#assert_compiled declared_but_unowned_equipment_is_refused
#assert_compiled skipped_epoch_is_refused
#assert_compiled home_absence_cannot_erase_attachment
#assert_compiled fixture_identity_rejects_serial_substitution

end Dregg2.Games.PathOfAngels.Attendant
