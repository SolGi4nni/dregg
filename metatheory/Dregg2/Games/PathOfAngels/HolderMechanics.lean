/-
# HolderMechanics — bounded DREGG-holder privileges for Path of Angels

This module starts *after* the bridge has admitted a proof of holdings.  It does
not model Solana RPC, finality, account decoding, or signature verification.
`AdmittedHoldingGrant` is the sealed adapter boundary: it retains the exact
consensus-proven holding and binds its use to one federation, mint, snapshot,
content epoch, holder/player identity, PoA event, sequence/expiry window, and
consume-once nullifier.

The executable menu is intentionally modest in authority but broad in play:
holder-only side-deck access, a capped choir ballot bonus, capped salvage
insurance, sponsorship of a public player, and a two-chamber holder/public
result.  The apparent sixth item—buying uncapped narrative weight—is present in
the wire vocabulary solely so the reducer can refuse it.  Receipts contain only
bounded `Core.Contribution`s and game-local entitlements; this dependency cone
does not import `Canon` and exposes no canon mutation.

Event replay is integrated through `EventSourcing`.  Its digest implementation
and atomic cursor persistence remain the explicitly named deployment boundary;
the wrapper below additionally pins payload sequence to event sequence and
projection sequence to replay cursor.
-/
import Dregg2.Bridge.ProofOfHoldings
import Dregg2.Games.PathOfAngels.EventSourcing
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.HolderMechanics

open Dregg2.Games.PathOfAngels
open Dregg2.Bridge.ProofOfHoldings

set_option autoImplicit false

/-! ## Policy, identities, and the sealed admitted grant -/

structure HolderPlayerId where
  digest : Digest32
deriving DecidableEq

structure PublicPlayerId where
  digest : Digest32
deriving DecidableEq

inductive VoteChoice
  | yes
  | no
deriving DecidableEq, Repr

/-- Exact event-local rules.  Keeping the complete policy in `State` prevents a
caller from replaying an old state under a same-identity/different-rules value. -/
structure Policy where
  federationId : Digest32
  dreggMint : Nat
  snapshotSlot : Slot
  contentEpoch : EpochId
  eventId : Digest32
  rulesDigest : Digest32
  eventGenesisHead : Digest32
  sideExpeditionKey : Digest32
  choirBonusCap : Nat
  insuranceCap : Metric
  sponsorCredit : Metric
  holderQuorum : Nat
  publicQuorum : Nat
deriving DecidableEq

/-- Every field needed to prevent a holding proof from drifting across a game,
snapshot, player, or replay position. -/
structure GrantBinding where
  federationId : Digest32
  mint : Nat
  snapshotSlot : Slot
  contentEpoch : EpochId
  player : HolderPlayerId
  holdingOwner : Account
  eventId : Digest32
  rulesDigest : Digest32
  eventSequence : Nat
  expiresAfterSequence : Nat
  nullifier : Digest32
deriving DecidableEq

/-- Already-admitted proof-of-holding authority.  The constructor is private:
production obtains this value only from the bridge verifier/identity-binding
adapter.  The retained equations ensure that the sealed grant really describes
the attached `ProofOfHoldings.ProvenHolding`; reducer checks then bind that grant
to the exact PoA policy and event position. -/
structure AdmittedHoldingGrant where
  private mk ::
  issuerId : Digest32
  verificationReceipt : Digest32
  identityBindingReceipt : Digest32
  /-- Exact rules value authenticated by the issuer, not merely a caller-chosen
  digest label.  This closes same-id/different-semantics policy substitution. -/
  boundPolicy : Policy
  binding : GrantBinding
  holding : ProvenHolding
  grantedWeight : Weight
  consensus_exact : holding.trust = TrustTier.consensusProven
  owner_exact : holding.owner = binding.holdingOwner
  mint_exact : holding.mint = binding.mint
  slot_exact : holding.slot = binding.snapshotSlot
  positive_weight : 0 < grantedWeight
  weight_backed : grantedWeight ≤ holding.amount

theorem AdmittedHoldingGrant.backed (grant : AdmittedHoldingGrant) :
    grant.holding.trust = TrustTier.consensusProven ∧
      grant.holding.owner = grant.binding.holdingOwner ∧
      grant.holding.mint = grant.binding.mint ∧
      grant.holding.slot = grant.binding.snapshotSlot ∧
      0 < grant.grantedWeight ∧ grant.grantedWeight ≤ grant.holding.amount :=
  ⟨grant.consensus_exact, grant.owner_exact, grant.mint_exact, grant.slot_exact,
    grant.positive_weight, grant.weight_backed⟩

/-! ## The executable menu and closed, non-canon effect vocabulary -/

/-- Opaque result of the expedition settlement verifier.  A holder never states
their own loss: the sealed receipt fixes ownership, run, settled amount, claim
sequence/expiry, and its own consume-once nullifier. -/
structure SettledLossEvidence where
  private mk ::
  verifierId : Digest32
  settlementReceipt : Digest32
  settlementRoot : Digest32
  federationId : Digest32
  contentEpoch : EpochId
  eventId : Digest32
  rulesDigest : Digest32
  player : HolderPlayerId
  runId : Digest32
  settledLoss : Nat
  claimSequence : Nat
  expiresAfterSequence : Nat
  receiptNullifier : Digest32

/-- Raw user assertions have no path to an insurance payout. -/
structure UntrustedLossClaim where
  player : HolderPlayerId
  runId : Digest32
  claimedLoss : Nat
deriving DecidableEq

inductive HolderAction
  | claimSideExpedition
  | choirVote (choice : VoteChoice)
  | claimSalvageInsurance (evidence : SettledLossEvidence)
  | sponsorPublicPlayer (beneficiary : PublicPlayerId)
  /-- Deliberate hostile wire case.  It is always refused. -/
  | buyUncappedWeight (payment requestedWeight : Nat) (choice : VoteChoice)

structure HolderEvent where
  player : HolderPlayerId
  grant : AdmittedHoldingGrant
  action : HolderAction

structure PublicVote where
  federationId : Digest32
  contentEpoch : EpochId
  eventId : Digest32
  rulesDigest : Digest32
  sequence : Nat
  player : PublicPlayerId
  choice : VoteChoice
deriving DecidableEq

inductive Payload
  | holder (event : HolderEvent)
  | publicVote (vote : PublicVote)

def Payload.sequence : Payload → Nat
  | .holder event => event.grant.binding.eventSequence
  | .publicVote vote => vote.sequence

structure ChamberTally where
  yes : Nat
  no : Nat
deriving DecidableEq, Repr

def ChamberTally.turnout (tally : ChamberTally) : Nat := tally.yes + tally.no

def ChamberTally.add (tally : ChamberTally) (choice : VoteChoice) (weight : Nat) :
    ChamberTally :=
  match choice with
  | .yes => { tally with yes := tally.yes + weight }
  | .no => { tally with no := tally.no + weight }

structure Sponsorship where
  sponsor : HolderPlayerId
  beneficiary : PublicPlayerId
  credit : Metric
deriving DecidableEq

structure InsuranceClaim where
  holder : HolderPlayerId
  runId : Digest32
  reimbursed : Metric
deriving DecidableEq

/-- Private construction prevents callers from inventing a projection with an
unspent nullifier or a different policy.  `initialState` and checked reducers are
the public producers. -/
structure State where
  private mk ::
  policy : Policy
  sequence : Nat
  spentGrantNullifiers : Finset Digest32
  spentLossEvidenceNullifiers : Finset Digest32
  sideExpeditionHolders : Finset HolderPlayerId
  choirVoters : Finset HolderPlayerId
  publicVoters : Finset PublicPlayerId
  holderChamber : ChamberTally
  publicChamber : ChamberTally
  sponsorships : List Sponsorship
  insuranceClaims : List InsuranceClaim
deriving DecidableEq

def initialState (policy : Policy) : State :=
  ⟨policy, 0, ∅, ∅, ∅, ∅, ∅, ⟨0, 0⟩, ⟨0, 0⟩, [], []⟩

inductive Effect
  | sideExpeditionKey (holder : HolderPlayerId) (key : Digest32)
  | choirBallot (holder : HolderPlayerId) (choice : VoteChoice) (weight : Nat)
  | salvageInsurance (claim : InsuranceClaim)
  | publicSponsorship (sponsorship : Sponsorship)
  | publicBallot (player : PublicPlayerId) (choice : VoteChoice)
deriving DecidableEq

/-- A receipt has no artifact/canon field.  The only world-facing output is the
already-bounded `Contribution`; all other effects are local entitlements/tallies. -/
structure Receipt where
  sequence : Nat
  consumedGrantNullifier : Option Digest32
  contribution : Contribution
  effect : Effect
deriving DecidableEq

def contributionWithSupplies (amount : Metric) : Contribution :=
  { Contribution.zero with supplies := amount }

def cappedMetric (requested : Nat) (cap : Metric) : Metric :=
  ⟨min requested cap.val, lt_of_le_of_lt (Nat.min_le_right _ _) cap.isLt⟩

theorem cappedMetric_le_settled (requested : Nat) (cap : Metric) :
    (cappedMetric requested cap).val ≤ requested :=
  Nat.min_le_left _ _

theorem cappedMetric_le_policy (requested : Nat) (cap : Metric) :
    (cappedMetric requested cap).val ≤ cap.val :=
  Nat.min_le_right _ _

def cappedChoirBonus (policy : Policy) (grant : AdmittedHoldingGrant) : Nat :=
  min grant.grantedWeight policy.choirBonusCap

/-- One ordinary voice plus a balance-derived bonus that cannot exceed the
authored cap. -/
def holderChoirWeight (policy : Policy) (grant : AdmittedHoldingGrant) : Nat :=
  1 + cappedChoirBonus policy grant

theorem capped_choir_bonus_le_policy (policy : Policy) (grant : AdmittedHoldingGrant) :
    cappedChoirBonus policy grant ≤ policy.choirBonusCap :=
  Nat.min_le_right _ _

theorem holder_choir_weight_le_cap_plus_one (policy : Policy)
    (grant : AdmittedHoldingGrant) :
    holderChoirWeight policy grant ≤ policy.choirBonusCap + 1 := by
  unfold holderChoirWeight
  simpa [Nat.add_comm] using
    Nat.add_le_add_left (capped_choir_bonus_le_policy policy grant) 1

theorem receipt_contribution_is_platform_bounded (receipt : Receipt) :
    receipt.contribution.intel.val ≤ METRIC_LIMIT ∧
      receipt.contribution.supplies.val ≤ METRIC_LIMIT ∧
      receipt.contribution.cohesion.val ≤ METRIC_LIMIT ∧
      receipt.contribution.influence.val ≤ METRIC_LIMIT ∧
      receipt.contribution.score.val ≤ METRIC_LIMIT ∧
      receipt.contribution.relics.card ≤ RELIC_LIMIT := by
  exact ⟨Nat.lt_succ_iff.mp receipt.contribution.intel.isLt,
    Nat.lt_succ_iff.mp receipt.contribution.supplies.isLt,
    Nat.lt_succ_iff.mp receipt.contribution.cohesion.isLt,
    Nat.lt_succ_iff.mp receipt.contribution.influence.isLt,
    Nat.lt_succ_iff.mp receipt.contribution.score.isLt,
    receipt.contribution.relics_bounded⟩

/-! ## Fail-closed grant consumption and mechanics -/

def stateMatchesPolicyB (policy : Policy) (state : State) : Bool :=
  decide (state.policy = policy)

def grantEligibleB (policy : Policy) (state : State) (event : HolderEvent) : Bool :=
  decide (
    state.policy = policy ∧
    event.grant.boundPolicy = policy ∧
    event.player = event.grant.binding.player ∧
    event.grant.binding.federationId = policy.federationId ∧
    event.grant.binding.mint = policy.dreggMint ∧
    event.grant.binding.snapshotSlot = policy.snapshotSlot ∧
    event.grant.binding.contentEpoch = policy.contentEpoch ∧
    event.grant.binding.eventId = policy.eventId ∧
    event.grant.binding.rulesDigest = policy.rulesDigest ∧
    event.grant.binding.eventSequence = state.sequence + 1 ∧
    event.grant.binding.eventSequence ≤ event.grant.binding.expiresAfterSequence ∧
    event.grant.binding.nullifier ∉ state.spentGrantNullifiers ∧
    event.grant.holding.trust = TrustTier.consensusProven ∧
    event.grant.holding.owner = event.grant.binding.holdingOwner ∧
    event.grant.holding.mint = event.grant.binding.mint ∧
    event.grant.holding.slot = event.grant.binding.snapshotSlot ∧
    0 < event.grant.grantedWeight ∧
    event.grant.grantedWeight ≤ event.grant.holding.amount)

def lossEvidenceEligibleB (policy : Policy) (state : State) (event : HolderEvent)
    (evidence : SettledLossEvidence) : Bool :=
  decide (
    evidence.federationId = policy.federationId ∧
    evidence.contentEpoch = policy.contentEpoch ∧
    evidence.eventId = policy.eventId ∧
    evidence.rulesDigest = policy.rulesDigest ∧
    evidence.player = event.player ∧
    evidence.claimSequence = event.grant.binding.eventSequence ∧
    evidence.claimSequence ≤ evidence.expiresAfterSequence ∧
    evidence.receiptNullifier ∉ state.spentLossEvidenceNullifiers)

/-- There is deliberately no decoder from an arbitrary claimed run/loss into
sealed settlement evidence. -/
def submitUntrustedLossClaim (_policy : Policy) (_state : State)
    (_claim : UntrustedLossClaim) : Option (State × Receipt) := none

private def consumeGrant (state : State) (grant : AdmittedHoldingGrant) : State :=
  { state with
    sequence := state.sequence + 1
    spentGrantNullifiers := insert grant.binding.nullifier state.spentGrantNullifiers }

private def holderReceipt (state : State) (grant : AdmittedHoldingGrant)
    (contribution : Contribution) (effect : Effect) : Receipt where
  sequence := state.sequence + 1
  consumedGrantNullifier := some grant.binding.nullifier
  contribution
  effect

/-- Execute one holder mechanic.  `buyUncappedWeight` is matched before every
other gate and has no accepting branch: payment is never narrative authority. -/
def applyHolder (policy : Policy) (state : State) (event : HolderEvent) :
    Option (State × Receipt) :=
  match event.action with
  | .buyUncappedWeight _ _ _ => none
  | .claimSideExpedition =>
      if grantEligibleB policy state event then
        if event.player ∈ state.sideExpeditionHolders then none
        else
          let next := consumeGrant state event.grant
          let next := { next with
            sideExpeditionHolders := insert event.player next.sideExpeditionHolders }
          some (next, holderReceipt state event.grant Contribution.zero
            (.sideExpeditionKey event.player policy.sideExpeditionKey))
      else none
  | .choirVote choice =>
      if grantEligibleB policy state event then
        if event.player ∈ state.choirVoters then none
        else
          let weight := holderChoirWeight policy event.grant
          let next := consumeGrant state event.grant
          let next := { next with
            choirVoters := insert event.player next.choirVoters
            holderChamber := next.holderChamber.add choice weight }
          some (next, holderReceipt state event.grant Contribution.zero
            (.choirBallot event.player choice weight))
      else none
  | .claimSalvageInsurance evidence =>
      if grantEligibleB policy state event then
        if lossEvidenceEligibleB policy state event evidence then
          if state.insuranceClaims.any (fun claim => claim.runId = evidence.runId) then none
          else
            let reimbursement := cappedMetric evidence.settledLoss policy.insuranceCap
            let claim : InsuranceClaim :=
              { holder := event.player, runId := evidence.runId, reimbursed := reimbursement }
            let next := consumeGrant state event.grant
            let next := { next with
              spentLossEvidenceNullifiers :=
                insert evidence.receiptNullifier next.spentLossEvidenceNullifiers
              insuranceClaims := claim :: next.insuranceClaims }
            some (next, holderReceipt state event.grant
              (contributionWithSupplies reimbursement) (.salvageInsurance claim))
        else
          none
      else none
  | .sponsorPublicPlayer beneficiary =>
      if grantEligibleB policy state event then
        if state.sponsorships.any (fun sponsorship => sponsorship.sponsor = event.player) then none
        else
          let sponsorship : Sponsorship :=
            { sponsor := event.player, beneficiary, credit := policy.sponsorCredit }
          let next := consumeGrant state event.grant
          let next := { next with sponsorships := sponsorship :: next.sponsorships }
          some (next, holderReceipt state event.grant Contribution.zero
            (.publicSponsorship sponsorship))
      else none

theorem pay_to_win_is_always_refused (policy : Policy) (state : State)
    (player : HolderPlayerId) (grant : AdmittedHoldingGrant)
    (payment requestedWeight : Nat) (choice : VoteChoice) :
    applyHolder policy state
      { player, grant, action := .buyUncappedWeight payment requestedWeight choice } = none := rfl

def applyPublicVote (policy : Policy) (state : State) (vote : PublicVote) :
    Option (State × Receipt) :=
  if state.policy != policy then none
  else if vote.federationId != policy.federationId then none
  else if vote.contentEpoch != policy.contentEpoch then none
  else if vote.eventId != policy.eventId then none
  else if vote.rulesDigest != policy.rulesDigest then none
  else if vote.sequence != state.sequence + 1 then none
  else if vote.player ∈ state.publicVoters then none
  else
    let next := { state with
      sequence := state.sequence + 1
      publicVoters := insert vote.player state.publicVoters
      publicChamber := state.publicChamber.add vote.choice 1 }
    some (next, {
      sequence := state.sequence + 1
      consumedGrantNullifier := none
      contribution := Contribution.zero
      effect := .publicBallot vote.player vote.choice
    })

def applyPayload (policy : Policy) (state : State) (payload : Payload) :
    Option (State × Receipt) :=
  match payload with
  | .holder event => applyHolder policy state event
  | .publicVote vote => applyPublicVote policy state vote

def reducePayload (policy : Policy) : EventSourcing.Reducer State Payload :=
  fun state payload => (applyPayload policy state payload).map Prod.fst

inductive TwoChamberResult
  | pending
  | passed
  | failed
deriving DecidableEq, Repr

/-- A decision passes only after both quorums are present and both independently
recorded chambers have a strict yes majority. -/
def twoChamberResult (policy : Policy) (state : State) : TwoChamberResult :=
  if state.holderChamber.turnout < policy.holderQuorum ∨
      state.publicChamber.turnout < policy.publicQuorum then .pending
  else if state.holderChamber.no < state.holderChamber.yes ∧
      state.publicChamber.no < state.publicChamber.yes then .passed
  else .failed

theorem two_chamber_pass_requires_both_majorities (policy : Policy) (state : State)
    (h : twoChamberResult policy state = .passed) :
    policy.holderQuorum ≤ state.holderChamber.turnout ∧
      policy.publicQuorum ≤ state.publicChamber.turnout ∧
      state.holderChamber.no < state.holderChamber.yes ∧
      state.publicChamber.no < state.publicChamber.yes := by
  unfold twoChamberResult at h
  split at h
  · contradiction
  · rename_i hquorum
    split at h
    · rename_i hmajorities
      exact ⟨Nat.le_of_not_gt (not_or.mp hquorum).1,
        Nat.le_of_not_gt (not_or.mp hquorum).2, hmajorities.1, hmajorities.2⟩
    · contradiction

/-! ## Event-sourcing adapter -/

def streamSpec (policy : Policy) : EventSourcing.StreamSpec where
  aggregate := { namespaceId := policy.federationId, kind := 8, key := policy.eventId }
  version := ⟨1⟩
  genesisHead := policy.eventGenesisHead

inductive SourcedError
  | projectionCursorSequence
  | payloadStatementSequence
  | eventSource (error : EventSourcing.Error)
deriving DecidableEq, Repr

/-- Replay wrapper: both the payload and private projection must advance at the
same sequence as the generic event-stream cursor. -/
def applySourcedEvent (policy : Policy) (digests : EventSourcing.DigestBoundary Payload)
    (before : EventSourcing.ReplayState State)
    (event : EventSourcing.EventEnvelope Payload) :
    Except SourcedError (EventSourcing.ReplayState State) := do
  if before.projection.sequence != before.cursor.sequence then
    throw .projectionCursorSequence
  if event.payload.sequence != event.statement.sequence then
    throw .payloadStatementSequence
  match EventSourcing.applyEvent (streamSpec policy) digests (reducePayload policy)
      before event with
  | .ok next => .ok next.state
  | .error error => .error (.eventSource error)

/-! ## Executable positive and hostile fixtures -/

private def digestByte (n : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨n % 256, Nat.mod_lt _ (by omega)⟩
  length_eq := by simp

private def holderA : HolderPlayerId := ⟨digestByte 20⟩
private def holderB : HolderPlayerId := ⟨digestByte 21⟩
private def holderC : HolderPlayerId := ⟨digestByte 22⟩
private def holderD : HolderPlayerId := ⟨digestByte 23⟩
private def publicA : PublicPlayerId := ⟨digestByte 30⟩

private def fixturePolicy : Policy where
  federationId := digestByte 1
  dreggMint := 42
  snapshotSlot := 100
  contentEpoch := ⟨3⟩
  eventId := digestByte 4
  rulesDigest := digestByte 5
  eventGenesisHead := digestByte 6
  sideExpeditionKey := digestByte 7
  choirBonusCap := 3
  insuranceCap := ⟨20, by native_decide⟩
  sponsorCredit := ⟨2, by native_decide⟩
  holderQuorum := 1
  publicQuorum := 1

private def fixtureGrantForPolicy (policy : Policy) (player : HolderPlayerId)
    (owner sequence expiry : Nat) (nullifier : Digest32) : AdmittedHoldingGrant :=
  let binding : GrantBinding := {
    federationId := policy.federationId
    mint := policy.dreggMint
    snapshotSlot := policy.snapshotSlot
    contentEpoch := policy.contentEpoch
    player
    holdingOwner := owner
    eventId := policy.eventId
    rulesDigest := policy.rulesDigest
    eventSequence := sequence
    expiresAfterSequence := expiry
    nullifier
  }
  let holding : ProvenHolding := {
    owner
    mint := policy.dreggMint
    amount := 100
    slot := policy.snapshotSlot
    trust := .consensusProven
  }
  {
    issuerId := digestByte 40
    verificationReceipt := digestByte 41
    identityBindingReceipt := digestByte 42
    boundPolicy := policy
    binding
    holding
    grantedWeight := 100
    consensus_exact := rfl
    owner_exact := rfl
    mint_exact := rfl
    slot_exact := rfl
    positive_weight := by decide
    weight_backed := by simp [holding]
  }

private def grantA1 : AdmittedHoldingGrant :=
  fixtureGrantForPolicy fixturePolicy holderA 70 1 10 (digestByte 51)
private def grantB2 : AdmittedHoldingGrant :=
  fixtureGrantForPolicy fixturePolicy holderB 71 2 10 (digestByte 52)
private def grantC3 : AdmittedHoldingGrant :=
  fixtureGrantForPolicy fixturePolicy holderC 72 3 10 (digestByte 53)
private def grantD4 : AdmittedHoldingGrant :=
  fixtureGrantForPolicy fixturePolicy holderD 73 4 10 (digestByte 54)

private def fixtureLossEvidenceForPolicy (policy : Policy) (player : HolderPlayerId)
    (sequence expiry : Nat) (receiptNullifier runId : Digest32)
    (settledLoss : Nat) : SettledLossEvidence := {
  verifierId := digestByte 55
  settlementReceipt := digestByte 56
  settlementRoot := digestByte 57
  federationId := policy.federationId
  contentEpoch := policy.contentEpoch
  eventId := policy.eventId
  rulesDigest := policy.rulesDigest
  player
  runId
  settledLoss
  claimSequence := sequence
  expiresAfterSequence := expiry
  receiptNullifier
}

private def sideEvent : HolderEvent :=
  { player := holderA, grant := grantA1, action := .claimSideExpedition }

private def sideStep? := applyHolder fixturePolicy (initialState fixturePolicy) sideEvent

theorem holder_side_expedition_fires :
    sideStep?.map (fun result =>
      decide (holderA ∈ result.1.sideExpeditionHolders) &&
      decide (result.2.effect = .sideExpeditionKey holderA fixturePolicy.sideExpeditionKey) &&
      decide (grantA1.binding.nullifier ∈ result.1.spentGrantNullifiers)) = some true := by
  native_decide

private def afterSide : State := sideStep?.get (by native_decide)
  |>.1

private def choirEvent : HolderEvent :=
  { player := holderB, grant := grantB2, action := .choirVote .yes }
private def choirStep? := applyHolder fixturePolicy afterSide choirEvent

theorem capped_choir_fires_at_cap_not_balance :
    choirStep?.map (fun result =>
      decide (result.1.holderChamber.yes = 4) &&
      decide (result.2.effect = .choirBallot holderB .yes 4)) = some true := by
  native_decide

private def afterChoir : State := choirStep?.get (by native_decide) |>.1

private def sponsorEvent : HolderEvent :=
  { player := holderC, grant := grantC3, action := .sponsorPublicPlayer publicA }
private def sponsorStep? := applyHolder fixturePolicy afterChoir sponsorEvent

theorem sponsor_public_player_fires :
    sponsorStep?.map (fun result =>
      let expected : Sponsorship := {
        sponsor := holderC
        beneficiary := publicA
        credit := fixturePolicy.sponsorCredit
      }
      decide (expected ∈ result.1.sponsorships)) = some true := by
  native_decide

private def afterSponsor : State := sponsorStep?.get (by native_decide) |>.1

private def insuranceRun : Digest32 := digestByte 60
private def lossReceiptNullifier : Digest32 := digestByte 61
private def insuranceEvidence : SettledLossEvidence :=
  fixtureLossEvidenceForPolicy fixturePolicy holderD 4 10 lossReceiptNullifier insuranceRun 99
private def insuranceEvent : HolderEvent :=
  { player := holderD, grant := grantD4,
    action := .claimSalvageInsurance insuranceEvidence }
private def insuranceStep? := applyHolder fixturePolicy afterSponsor insuranceEvent

theorem salvage_insurance_is_capped :
    insuranceStep?.map (fun result =>
      decide (result.2.contribution.supplies.val = 20) &&
      decide (result.1.insuranceClaims.head?.map InsuranceClaim.reimbursed =
        some fixturePolicy.insuranceCap) &&
      decide (lossReceiptNullifier ∈ result.1.spentLossEvidenceNullifiers)) = some true := by
  native_decide

private def afterInsurance : State := insuranceStep?.get (by native_decide) |>.1

private def publicVoteA : PublicVote where
  federationId := fixturePolicy.federationId
  contentEpoch := fixturePolicy.contentEpoch
  eventId := fixturePolicy.eventId
  rulesDigest := fixturePolicy.rulesDigest
  sequence := 5
  player := publicA
  choice := .yes

private def publicStep? := applyPublicVote fixturePolicy afterInsurance publicVoteA

theorem holder_and_public_chambers_pass_together :
    publicStep?.map (fun result => twoChamberResult fixturePolicy result.1) =
      some .passed := by
  native_decide

private def afterPublic : State := publicStep?.get (by native_decide) |>.1

theorem public_vote_replay_is_refused :
    applyPublicVote fixturePolicy afterPublic { publicVoteA with sequence := 6 } = none := by
  native_decide

theorem spent_grant_nullifier_is_refused_even_at_fresh_sequence :
    let replayGrant := fixtureGrantForPolicy fixturePolicy holderB 71 2 10 grantA1.binding.nullifier
    applyHolder fixturePolicy afterSide
      { player := holderB, grant := replayGrant, action := .choirVote .yes } = none := by
  native_decide

theorem untrusted_self_reported_loss_is_refused :
    submitUntrustedLossClaim fixturePolicy afterSponsor
      { player := holderD, runId := insuranceRun, claimedLoss := 1_000_000 } = none := rfl

theorem loss_evidence_for_another_player_is_refused :
    let wrongOwnerEvidence := fixtureLossEvidenceForPolicy fixturePolicy holderA 4 10
      (digestByte 62) insuranceRun 99
    applyHolder fixturePolicy afterSponsor
      { player := holderD, grant := grantD4,
        action := .claimSalvageInsurance wrongOwnerEvidence } = none := by
  native_decide

theorem spent_loss_receipt_is_refused_even_with_fresh_grant_and_sequence :
    let freshGrant := fixtureGrantForPolicy fixturePolicy holderA 74 5 10 (digestByte 63)
    let replayedReceipt := fixtureLossEvidenceForPolicy fixturePolicy holderA 5 10
      lossReceiptNullifier (digestByte 64) 50
    applyHolder fixturePolicy afterInsurance
      { player := holderA, grant := freshGrant,
        action := .claimSalvageInsurance replayedReceipt } = none := by
  native_decide

theorem grant_context_and_lifetime_are_fail_closed :
    let initial := initialState fixturePolicy
    let wrongFederation := fixtureGrantForPolicy
      { fixturePolicy with federationId := digestByte 80 } holderA 70 1 10 (digestByte 81)
    let wrongMint := fixtureGrantForPolicy
      { fixturePolicy with dreggMint := 43 } holderA 70 1 10 (digestByte 82)
    let wrongSlot := fixtureGrantForPolicy
      { fixturePolicy with snapshotSlot := 101 } holderA 70 1 10 (digestByte 83)
    let wrongEpoch := fixtureGrantForPolicy
      { fixturePolicy with contentEpoch := ⟨4⟩ } holderA 70 1 10 (digestByte 84)
    let wrongEvent := fixtureGrantForPolicy
      { fixturePolicy with eventId := digestByte 85 } holderA 70 1 10 (digestByte 86)
    let wrongRules := fixtureGrantForPolicy
      { fixturePolicy with rulesDigest := digestByte 87 } holderA 70 1 10 (digestByte 88)
    let wrongSequence := fixtureGrantForPolicy fixturePolicy holderA 70 2 10 (digestByte 89)
    let expired := fixtureGrantForPolicy fixturePolicy holderA 70 1 0 (digestByte 90)
    (applyHolder fixturePolicy initial
      { player := holderA, grant := wrongFederation, action := .claimSideExpedition }).isNone &&
    (applyHolder fixturePolicy initial
      { player := holderA, grant := wrongMint, action := .claimSideExpedition }).isNone &&
    (applyHolder fixturePolicy initial
      { player := holderA, grant := wrongSlot, action := .claimSideExpedition }).isNone &&
    (applyHolder fixturePolicy initial
      { player := holderA, grant := wrongEpoch, action := .claimSideExpedition }).isNone &&
    (applyHolder fixturePolicy initial
      { player := holderA, grant := wrongEvent, action := .claimSideExpedition }).isNone &&
    (applyHolder fixturePolicy initial
      { player := holderA, grant := wrongRules, action := .claimSideExpedition }).isNone &&
    (applyHolder fixturePolicy initial
      { player := holderA, grant := wrongSequence, action := .claimSideExpedition }).isNone &&
    (applyHolder fixturePolicy initial
      { player := holderA, grant := expired, action := .claimSideExpedition }).isNone &&
    (applyHolder fixturePolicy initial
      { player := holderB, grant := grantA1, action := .claimSideExpedition }).isNone = true := by
  native_decide

theorem same_ids_cannot_substitute_widened_policy_semantics :
    let widened := { fixturePolicy with choirBonusCap := 1_000_000 }
    applyHolder widened (initialState widened)
      { player := holderA, grant := grantA1, action := .choirVote .yes } = none := by
  native_decide

theorem uncapped_pay_to_win_hostile_fixture_is_refused :
    applyHolder fixturePolicy (initialState fixturePolicy)
      { player := holderA, grant := grantA1,
        action := .buyUncappedWeight 1_000_000 1_000_000 .yes } = none := rfl

private def fixtureDigests : EventSourcing.DigestBoundary Payload where
  payloadDigest payload := digestByte (100 + payload.sequence)
  eventDigest statement := digestByte (120 + statement.sequence)

private def sourcedSidePayload : Payload := .holder sideEvent
private def sourcedSideStatement : EventSourcing.EventStatement where
  aggregate := (streamSpec fixturePolicy).aggregate
  version := (streamSpec fixturePolicy).version
  sequence := 1
  predecessor := (streamSpec fixturePolicy).genesisHead
  payloadDigest := fixtureDigests.payloadDigest sourcedSidePayload

private def sourcedSideEvent : EventSourcing.EventEnvelope Payload where
  statement := sourcedSideStatement
  payload := sourcedSidePayload
  eventDigest := fixtureDigests.eventDigest sourcedSideStatement

private def sourcedInitial : EventSourcing.ReplayState State where
  cursor := (streamSpec fixturePolicy).genesisCursor
  projection := initialState fixturePolicy

theorem sourced_holder_event_replays :
    (applySourcedEvent fixturePolicy fixtureDigests sourcedInitial sourcedSideEvent).toOption.map
      (fun replayed =>
        decide (replayed.cursor.sequence = 1) &&
        decide (replayed.projection.sequence = 1) &&
        decide (grantA1.binding.nullifier ∈ replayed.projection.spentGrantNullifiers)) =
      some true := by
  native_decide

theorem sourced_payload_statement_sequence_mismatch_is_refused :
    applySourcedEvent fixturePolicy fixtureDigests sourcedInitial
      { sourcedSideEvent with statement := { sourcedSideStatement with sequence := 2 } } =
      .error .payloadStatementSequence := by
  native_decide

#assert_axioms AdmittedHoldingGrant.backed
#assert_axioms cappedMetric_le_settled
#assert_axioms cappedMetric_le_policy
#assert_axioms capped_choir_bonus_le_policy
#assert_axioms holder_choir_weight_le_cap_plus_one
#assert_axioms receipt_contribution_is_platform_bounded
#assert_axioms pay_to_win_is_always_refused
#assert_axioms two_chamber_pass_requires_both_majorities

#assert_compiled holder_side_expedition_fires
#assert_compiled capped_choir_fires_at_cap_not_balance
#assert_compiled sponsor_public_player_fires
#assert_compiled salvage_insurance_is_capped
#assert_compiled holder_and_public_chambers_pass_together
#assert_compiled public_vote_replay_is_refused
#assert_compiled spent_grant_nullifier_is_refused_even_at_fresh_sequence
#assert_compiled untrusted_self_reported_loss_is_refused
#assert_compiled loss_evidence_for_another_player_is_refused
#assert_compiled spent_loss_receipt_is_refused_even_with_fresh_grant_and_sequence
#assert_compiled grant_context_and_lifetime_are_fail_closed
#assert_compiled same_ids_cannot_substitute_widened_policy_semantics
#assert_compiled uncapped_pay_to_win_hostile_fixture_is_refused
#assert_compiled sourced_holder_event_replays
#assert_compiled sourced_payload_statement_sequence_mismatch_is_refused

end Dregg2.Games.PathOfAngels.HolderMechanics
