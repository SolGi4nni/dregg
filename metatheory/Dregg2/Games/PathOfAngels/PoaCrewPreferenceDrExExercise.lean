/-
# Path of Angels — operator-visible crew allocation semantic exercise

Four expedition officers privately score four authored uses for one recovered
object.  The Lean-authored N=4/K=4 preference relation chooses the lowest-index
aggregate winner.  This file supplies the game boundary around that relation:
an exact activated domain, ordered and authenticated roster rows, custody,
finite replay counters and nullifiers, authored option effects, quorum, result
interpretation, and opaque state/receipt authority.

## Exact privacy and authentication boundary

`judge` receives the complete `PrivateWitness`.  Its process sees every score and
all blinding material.  The receipt omits them.  This is operator-visible
plaintext input, not FHE, MPC, HidingFRI, threshold decryption, or
independent-operator privacy.  Despite the historical filename, this semantic
opening path is not advertised as DrEX or as an FHE deployment.

`RowSignature` is an opaque semantic capability: its Lean constructor is private
and its signed body is exact.  A strict host may create one only after a real
signature verifier accepts the same `RowSigningBody`.  This file proves no
Ed25519/PQ unforgeability and exports no signature-minting function.  The
executable fixture has an internal issuer solely to test protocol semantics.

The preference hash implementation is different: it is selected by a closed
Lean enum and cannot be replaced by a host function carrying the same id.  The
live implementation is the KAT-calibrated deployed BabyBear Poseidon2-w16
permutation used by the descriptor.  Collision resistance remains the named
cryptographic assumption; it is not a theorem about a compressing finite hash.

`State` and `Receipt` have private constructors.  The only non-fixture receipt
producer is `judge`; the transition constructor is private.  A serialized
receipt is merely a candidate and readmits only by rerunning the judge.  This
exercise deliberately exposes only initial-state readmission.  Persistence and
global compare-and-swap of a live continuation remain host obligations; a host
must never deserialize an arbitrary structure as `State`.
-/
import Dregg2.Games.PathOfAngels.Core
import Dregg2.Games.PrivatePreferenceDescriptor
import Dregg2.Circuit.Poseidon2BabyBearW16
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.PoaCrewPreferenceDrExExercise

open Dregg2.Games.PathOfAngels

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

namespace Preference

abbrev PrivateWitness := Dregg2.Games.PrivatePreferenceDescriptor.PrivateWitness
abbrev PublicStatement := Dregg2.Games.PrivatePreferenceDescriptor.PublicStatement

def ruleId : Int := Dregg2.Games.PrivatePreferenceDescriptor.RULE_ID
def participantCount : Nat := Dregg2.Games.PrivatePreferenceDescriptor.PARTICIPANT_COUNT
def optionCount : Nat := Dregg2.Games.PrivatePreferenceDescriptor.OPTION_COUNT
def digestWidth : Nat := Dregg2.Games.PrivatePreferenceDescriptor.DIGEST_WIDTH
def winner := Dregg2.Games.PrivatePreferenceDescriptor.winner
def ballotRoot := Dregg2.Games.PrivatePreferenceDescriptor.ballotRoot
def ballotPack := Dregg2.Games.PrivatePreferenceDescriptor.ballotPack
def aggregateScore := Dregg2.Games.PrivatePreferenceDescriptor.aggregateScore
def check := Dregg2.Games.PrivatePreferenceDescriptor.check

end Preference

abbrev CREW_COUNT : Nat := 4
abbrev ALLOCATION_COUNT : Nat := 4
abbrev WIRE_COUNTER_MODULUS : Nat := 65536
abbrev CIRCUIT_SESSION_MODULUS : Nat := 2013265921
abbrev WIRE_ID_MODULUS : Nat := 4294967296
abbrev EFFECT_LIMIT : Nat := 1000
abbrev RISK_LIMIT : Nat := 100

abbrev SeatIndex := Fin CREW_COUNT
abbrev WireCounter := Fin WIRE_COUNTER_MODULUS
abbrev CircuitSession := Fin CIRCUIT_SESSION_MODULUS
abbrev WireId := Fin WIRE_ID_MODULUS
abbrev EffectMetric := Fin (EFFECT_LIMIT + 1)
abbrev RiskMetric := Fin (RISK_LIMIT + 1)

/-- Strict signature wire width. -/
structure Digest64 where
  bytes : List (Fin 256)
  length_eq : bytes.length = 64
deriving DecidableEq

/-! ## Closed wire vocabulary -/

inductive AllocationUse where
  | containment
  | research
  | repair
  | reserve
deriving DecidableEq, Repr

def AllocationUse.tag : AllocationUse → Nat
  | .containment => 0
  | .research => 1
  | .repair => 2
  | .reserve => 3

def AllocationUse.ofWinner? : Nat → Option AllocationUse
  | 0 => some .containment
  | 1 => some .research
  | 2 => some .repair
  | 3 => some .reserve
  | _ => none

theorem AllocationUse.ofWinner?_tag (allocation : AllocationUse) :
    AllocationUse.ofWinner? allocation.tag = some allocation := by
  cases allocation <;> rfl

inductive DecisionPrivacyGrade where
  | operatorVisiblePlaintextInput
  | independentOperatorThreshold
deriving DecidableEq, Repr

inductive TiePolicy where
  | lowestIndex
deriving DecidableEq, Repr

/-- There is no function-valued hash-suite input.  Equal ids definitionally select
the same Lean-owned implementation. -/
inductive HashSuiteId where
  | poseidon2BabyBearW16V1
deriving DecidableEq, Repr

/-- Exact Lean implementation of the deployed width-16 BabyBear Poseidon2
permutation.  The preference descriptor absorbs exactly sixteen canonical field
elements and publishes the first eight permutation lanes. -/
def poseidon2Hash8 (input : List Int) (lane : Fin 8) : Int :=
  (Dregg2.Circuit.Poseidon2BabyBearW16.perm (input.map Int.toNat)).getD lane.val 0

def HashSuiteId.hash8 : HashSuiteId → List Int → Fin 8 → Int
  | .poseidon2BabyBearW16V1 => poseidon2Hash8

theorem same_hash_suite_id_selects_same_implementation
    (left right : HashSuiteId) (h : left = right) : left.hash8 = right.hash8 := by
  cases h
  rfl

inductive CheckStage where
  | stateAuthority
  | domain
  | orderedRoster
  | catalogue
  | privacyLabel
  | replay
  | sequence
  | custody
  | rowContext
  | rowAuthentication
  | rowBallotCommitment
  | privateDecision
  | quorum
  | interpretedResult
deriving DecidableEq, Repr

structure Descriptor where
  relation : String
  participantCount : Fin 5
  optionCount : Fin 5
  scoreUpperExclusive : Fin 5
  rule : Int
  rootWidth : Fin 9
  hashSuite : HashSuiteId
  privacy : DecisionPrivacyGrade
  tiePolicy : TiePolicy
  checkOrder : List CheckStage
deriving DecidableEq, Repr

def descriptor : Descriptor where
  relation := "poa-crew-preference-semantic/operator-visible-poseidon2/v3"
  participantCount := 4
  optionCount := 4
  scoreUpperExclusive := 4
  rule := Preference.ruleId
  rootWidth := 8
  hashSuite := .poseidon2BabyBearW16V1
  privacy := .operatorVisiblePlaintextInput
  tiePolicy := .lowestIndex
  checkOrder :=
    [ .stateAuthority, .domain, .orderedRoster, .catalogue,
      .privacyLabel, .replay, .sequence, .custody, .rowContext,
      .rowAuthentication, .rowBallotCommitment, .privateDecision, .quorum,
      .interpretedResult ]

theorem descriptor_is_exactly_n4k4_operator_visible :
    descriptor.participantCount.val = 4 ∧
    descriptor.optionCount.val = 4 ∧
    descriptor.scoreUpperExclusive.val = 4 ∧
    descriptor.rule = Preference.ruleId ∧
    descriptor.rootWidth.val = 8 ∧
    descriptor.hashSuite = .poseidon2BabyBearW16V1 ∧
    descriptor.privacy = .operatorVisiblePlaintextInput ∧
    descriptor.tiePolicy = .lowestIndex := by
  decide

/-! ## Full activated decision domain, roster, custody, and authored effects -/

structure DecisionDomain where
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : WireId
  missionId : WireId
  decisionId : Digest32
  circuitSession : CircuitSession
  hashSuite : HashSuiteId
deriving DecidableEq

structure RosterRow where
  seat : SeatIndex
  playerKey : Digest32
  credential : Digest32
  initialCounter : WireCounter
deriving DecidableEq

/-- Collision-free semantic nullifier.  The wire interpreter may commit this
fixed structure to a digest, but state semantics consume the exact preimage. -/
structure RowNullifier where
  domain : DecisionDomain
  seat : SeatIndex
  playerKey : Digest32
  credential : Digest32
  counter : WireCounter
deriving DecidableEq

def derivedRowNullifier (domain : DecisionDomain) (row : RosterRow)
    (counter : WireCounter) : RowNullifier :=
  ⟨domain, row.seat, row.playerKey, row.credential, counter⟩

structure CustodyObject where
  relic : WireId
  sourceReceipt : Digest32
  currentHolder : Digest32
  custodySequence : WireCounter
deriving DecidableEq

/-- Finite wire form of `ArtifactRef`; conversion to the shared world type is
exact and occurs only at the application seam. -/
structure WireArtifactRef where
  missionId : WireId
  artifactId : WireId
  sourceDigest : Digest32
  contentDigest : Digest32
deriving DecidableEq

def WireArtifactRef.toArtifactRef (artifact : WireArtifactRef) : ArtifactRef where
  missionId := ⟨artifact.missionId.val⟩
  artifactId := ⟨artifact.artifactId.val⟩
  sourceDigest := artifact.sourceDigest
  contentDigest := artifact.contentDigest

/-- Authored consequences make the winning allocation more than a display label.
All numeric outputs are finite on the wire. -/
structure OptionEffect where
  allocation : AllocationUse
  intel : EffectMetric
  supplies : EffectMetric
  cohesion : EffectMetric
  influence : EffectMetric
  risk : RiskMetric
  betaArtifact : WireArtifactRef
deriving DecidableEq

def OptionEffect.gameplayVector (effect : OptionEffect) :
    Nat × Nat × Nat × Nat × Nat :=
  (effect.intel.val, effect.supplies.val, effect.cohesion.val,
    effect.influence.val, effect.risk.val)

/-- The constructor is private because its proof fields are activation authority.
The host should expose a validated activation envelope, not deserialize this
structure directly. -/
structure Deployment where
  private mk ::
  domain : DecisionDomain
  roster : SeatIndex → RosterRow
  custody : CustodyObject
  catalogue : Fin ALLOCATION_COUNT → OptionEffect
  quorum : Fin (CREW_COUNT + 1)
  rosterSeatsExact : ∀ seat, (roster seat).seat = seat
  rosterPlayersInjective : Function.Injective (fun seat => (roster seat).playerKey)
  rosterCredentialsInjective : Function.Injective (fun seat => (roster seat).credential)
  catalogueOrderExact : ∀ option, (catalogue option).allocation.tag = option.val
  effectVectorsInjective : Function.Injective
    (fun option => (catalogue option).gameplayVector)
  quorumNontrivial : 2 ≤ quorum.val
  rosterCounterSuccessorAvailable :
    ∀ seat, (roster seat).initialCounter.val + 1 < WIRE_COUNTER_MODULUS
  custodySuccessorAvailable :
    custody.custodySequence.val + 1 < WIRE_COUNTER_MODULUS

/-! ## Public statement and exact row authentication -/

structure PublicRowContext where
  seat : SeatIndex
  playerKey : Digest32
  credential : Digest32
  counter : WireCounter
  nullifier : RowNullifier
  ballotCommitment : Fin 8 → Int
deriving DecidableEq

/-- This is the public input a future proof verifier must bind in full.  The
existing inner preference AIR consumes only `preferenceStatement`; the outer
operator-visible judge checks every other field exactly. -/
structure DecisionStatement where
  domain : DecisionDomain
  orderedRoster : SeatIndex → RosterRow
  custody : CustodyObject
  catalogue : Fin ALLOCATION_COUNT → OptionEffect
  quorum : Fin (CREW_COUNT + 1)
  tiePolicy : TiePolicy
  privacy : DecisionPrivacyGrade
  previousSequence : WireCounter
  nextSequence : WireCounter
  rows : SeatIndex → PublicRowContext
  ballotRoot : Fin 8 → Int
  /-- Exact activity count derived from the opened ballots.  Every roster row
  signs it.  A proof-mode successor must add this value to its public inputs;
  it may not trust an unbound host-side count. -/
  activeParticipantCount : Fin (CREW_COUNT + 1)
  winner : Fin ALLOCATION_COUNT
  tieCount : Fin (ALLOCATION_COUNT + 1)
  allocation : AllocationUse
  effect : OptionEffect
deriving DecidableEq

def DecisionStatement.preferenceStatement (statement : DecisionStatement) :
    Preference.PublicStatement where
  session := statement.domain.circuitSession.val
  rule := Preference.ruleId
  ballotRoot := statement.ballotRoot
  winner := statement.winner.val

/-- Each row signs its own ballot commitment and replay context under the full
activated decision binding.  The aggregate result is deliberately absent: a
seat authorizes its private input, not a winner chosen later by the operator. -/
structure RowSigningBody where
  domain : DecisionDomain
  orderedRoster : SeatIndex → RosterRow
  custody : CustodyObject
  catalogue : Fin ALLOCATION_COUNT → OptionEffect
  quorum : Fin (CREW_COUNT + 1)
  tiePolicy : TiePolicy
  privacy : DecisionPrivacyGrade
  previousSequence : WireCounter
  nextSequence : WireCounter
  activeParticipantCount : Fin (CREW_COUNT + 1)
  seat : SeatIndex
  row : PublicRowContext
deriving DecidableEq

def ROW_SIGNATURE_DOMAIN : WireId := 1347569224

/-- Canonical typed signing preimage.  Every component has fixed cardinality or
fixed byte width; the domain and version prevent cross-protocol reuse.  A host
codec must be a faithful encoding of this exact structure. -/
structure RowSigningPreimage where
  domain : WireId
  version : Fin 256
  body : RowSigningBody
deriving DecidableEq

def RowSigningBody.preimage (body : RowSigningBody) : RowSigningPreimage :=
  ⟨ROW_SIGNATURE_DOMAIN, 1, body⟩

def DecisionStatement.rowSigningBody (statement : DecisionStatement)
    (seat : SeatIndex) : RowSigningBody where
  domain := statement.domain
  orderedRoster := statement.orderedRoster
  custody := statement.custody
  catalogue := statement.catalogue
  quorum := statement.quorum
  tiePolicy := statement.tiePolicy
  privacy := statement.privacy
  previousSequence := statement.previousSequence
  nextSequence := statement.nextSequence
  activeParticipantCount := statement.activeParticipantCount
  seat
  row := statement.rows seat

/-- Opaque semantic signature capability.  No public constructor and no public
issuer exist in this module.  A host refinement may construct it only after its
real signature portal accepts the exact body. -/
structure RowSignature where
  private mk ::
  signer : Digest32
  preimage : RowSigningPreimage
  signatureBytes : Digest64
deriving DecidableEq

structure RowAuthorization where
  seat : SeatIndex
  signature : RowSignature
deriving DecidableEq

structure Claim where
  statement : DecisionStatement
  authorizations : SeatIndex → RowAuthorization
deriving DecidableEq

/-! ## Opaque live state and receipt authority -/

inductive CustodyState where
  | held (object : CustodyObject)
  | allocated (object : CustodyObject) (use : AllocationUse)
deriving DecidableEq

structure AllocationRecord where
  private mk ::
  statement : DecisionStatement
  custodyAfter : CustodyObject
deriving DecidableEq

structure State where
  private mk ::
  activeDomain : DecisionDomain
  orderedRoster : SeatIndex → RosterRow
  catalogue : Fin ALLOCATION_COUNT → OptionEffect
  sequence : WireCounter
  rowCounters : SeatIndex → WireCounter
  custody : CustodyState
  consumedDecisions : Finset Digest32
  consumedNullifiers : Finset RowNullifier
  records : List AllocationRecord
deriving DecidableEq

structure Receipt where
  private mk ::
  statement : DecisionStatement
  custodyAfter : CustodyObject
deriving DecidableEq

/-- Wire receipts have no authority. -/
structure ReceiptWire where
  statement : DecisionStatement
  custodyAfter : CustodyObject
deriving DecidableEq

def Receipt.toWire (receipt : Receipt) : ReceiptWire :=
  ⟨receipt.statement, receipt.custodyAfter⟩

def effectMetricToWorldMetric (metric : EffectMetric) : Metric :=
  ⟨metric.val, by
    have h := metric.isLt
    exact lt_of_lt_of_le h (by decide)⟩

/-- Exact seam into the shared PoA world-meter vocabulary.  Risk remains game
metadata; it is not silently converted into a positive world contribution. -/
def OptionEffect.toContribution (effect : OptionEffect) : Contribution where
  intel := effectMetricToWorldMetric effect.intel
  supplies := effectMetricToWorldMetric effect.supplies
  cohesion := effectMetricToWorldMetric effect.cohesion
  influence := effectMetricToWorldMetric effect.influence
  score := 0
  relics := ∅
  relics_bounded := by simp

def Receipt.worldContribution (receipt : Receipt) : Contribution :=
  receipt.statement.effect.toContribution

def Receipt.betaArtifact (receipt : Receipt) : ArtifactRef :=
  receipt.statement.effect.betaArtifact.toArtifactRef

/-- A snapshot is observability, not a state constructor. -/
structure StateSnapshot where
  activeDomain : DecisionDomain
  orderedRoster : SeatIndex → RosterRow
  catalogue : Fin ALLOCATION_COUNT → OptionEffect
  sequence : WireCounter
  rowCounters : SeatIndex → WireCounter
  custody : CustodyState
  consumedDecisions : Finset Digest32
  consumedNullifiers : Finset RowNullifier
  recordStatements : List DecisionStatement
deriving DecidableEq

def State.toSnapshot (state : State) : StateSnapshot where
  activeDomain := state.activeDomain
  orderedRoster := state.orderedRoster
  catalogue := state.catalogue
  sequence := state.sequence
  rowCounters := state.rowCounters
  custody := state.custody
  consumedDecisions := state.consumedDecisions
  consumedNullifiers := state.consumedNullifiers
  recordStatements := state.records.map AllocationRecord.statement

private def freshState (deployment : Deployment) : State :=
  ⟨deployment.domain, deployment.roster, deployment.catalogue, 0,
    fun seat => (deployment.roster seat).initialCounter,
    .held deployment.custody, ∅, ∅, []⟩

/-- Produces the sole valid initial live capability.  Global uniqueness of its
activation remains the host CAS obligation stated at the top of the file. -/
def start (deployment : Deployment) : State := freshState deployment

/-- Serialization may reconstitute only the exact initial capability here.  A
continuation must be retained live or reconstructed by exact judge replay. -/
def readmitInitialState? (deployment : Deployment) (snapshot : StateSnapshot) : Option State :=
  if snapshot = (freshState deployment).toSnapshot then some (freshState deployment) else none

def allFour (predicate : SeatIndex → Bool) : Bool :=
  predicate 0 && predicate 1 && predicate 2 && predicate 3

def statementDeploymentExactB (deployment : Deployment)
    (statement : DecisionStatement) : Bool :=
  decide (statement.domain = deployment.domain) &&
  decide (statement.orderedRoster = deployment.roster) &&
  decide (statement.custody = deployment.custody) &&
  decide (statement.catalogue = deployment.catalogue) &&
  decide (statement.quorum = deployment.quorum) &&
  decide (statement.tiePolicy = descriptor.tiePolicy) &&
  decide (statement.privacy = descriptor.privacy) &&
  decide (statement.allocation = (deployment.catalogue statement.winner).allocation) &&
  decide (statement.effect = deployment.catalogue statement.winner)

def nullifierSet (statement : DecisionStatement) : Finset RowNullifier :=
  (List.ofFn fun seat => (statement.rows seat).nullifier).toFinset

/-- Exact host compare-and-swap coordinate.  Emitting this event does not perform
the CAS; it gives the host both expected and successor coordinates without an
ambiguous reconstruction. -/
structure CasCoordinate where
  decisionId : Digest32
  sequence : WireCounter
  custodySequence : WireCounter
deriving DecidableEq

structure AllocationEvent where
  expected : CasCoordinate
  successor : CasCoordinate
  consumedNullifiers : Finset RowNullifier
  receipt : ReceiptWire
  contribution : Contribution
  betaArtifact : ArtifactRef
deriving DecidableEq

def Receipt.toEvent (receipt : Receipt) : AllocationEvent where
  expected :=
    ⟨receipt.statement.domain.decisionId, receipt.statement.previousSequence,
      receipt.statement.custody.custodySequence⟩
  successor :=
    ⟨receipt.statement.domain.decisionId, receipt.statement.nextSequence,
      receipt.custodyAfter.custodySequence⟩
  consumedNullifiers := nullifierSet receipt.statement
  receipt := receipt.toWire
  contribution := receipt.worldContribution
  betaArtifact := receipt.betaArtifact

def rowBlindLow (seat : SeatIndex) : Fin 8 :=
  ⟨2 * seat.val, by
    have h : seat.val < 4 := seat.isLt
    omega⟩

def rowBlindHigh (seat : SeatIndex) : Fin 8 :=
  ⟨2 * seat.val + 1, by
    have h : seat.val < 4 := seat.isLt
    omega⟩

def ROW_BALLOT_DOMAIN_TAG : Int := 1347569218

/-- Six meaningful values plus canonical zero framing form one exact width-16
per-seat Poseidon2 seed.  Two private blind lanes belong to each seat. -/
def rowBallotPreimage (domain : DecisionDomain) (seat : SeatIndex)
    (opening : Preference.PrivateWitness) : List Int :=
  [ ROW_BALLOT_DOMAIN_TAG
  , domain.circuitSession.val
  , Preference.ruleId
  , seat.val
  , Preference.ballotPack opening seat
  , opening.blinding (rowBlindLow seat)
  , opening.blinding (rowBlindHigh seat)
  , 0, 0, 0, 0, 0, 0, 0, 0, 0 ]

def rowBallotCommitment (domain : DecisionDomain) (seat : SeatIndex)
    (opening : Preference.PrivateWitness) : Fin 8 → Int :=
  domain.hashSuite.hash8 (rowBallotPreimage domain seat opening)

def rowsContextExactB (deployment : Deployment) (state : State)
    (statement : DecisionStatement) : Bool :=
  allFour fun seat =>
    let row := deployment.roster seat
    let context := statement.rows seat
    decide (context.seat = seat) &&
    decide (context.playerKey = row.playerKey) &&
    decide (context.credential = row.credential) &&
    decide (context.counter.val = (state.rowCounters seat).val + 1) &&
    decide (context.nullifier = derivedRowNullifier statement.domain row context.counter) &&
    decide (context.nullifier ∉ state.consumedNullifiers) &&
    decide ((List.ofFn fun i => (statement.rows i).nullifier).Nodup)

def rowsAuthenticatedB (deployment : Deployment) (claim : Claim) : Bool :=
  allFour fun seat =>
    let expectedBody := claim.statement.rowSigningBody seat
    let authorization := claim.authorizations seat
    decide (authorization.seat = seat) &&
    decide (authorization.signature.signer = (deployment.roster seat).playerKey) &&
    decide (authorization.signature.preimage = expectedBody.preimage)

def rowBallotCommitmentsExactB (statement : DecisionStatement)
    (opening : Preference.PrivateWitness) : Bool :=
  allFour fun seat =>
    decide ((statement.rows seat).ballotCommitment =
      rowBallotCommitment statement.domain seat opening)

/-- Quorum semantics are explicit: an all-zero ballot is an abstention and does
not count; any non-zero score makes the row active.  A participant who wants to
support no option while attending needs a later explicit attendance bit in the
AIR rather than silently overloading the all-zero vector. -/
def participantActiveB (opening : Preference.PrivateWitness) (participant : SeatIndex) : Bool :=
  (List.ofFn fun option : Fin 4 => opening.scores participant option).any
    (fun score => decide (score.val ≠ 0))

def activeParticipantCount (opening : Preference.PrivateWitness) : Nat :=
  ((List.ofFn fun participant : SeatIndex => participant).filter
    (fun participant => participantActiveB opening participant)).length

def winnerTieCount (opening : Preference.PrivateWitness) : Nat :=
  let score := Preference.aggregateScore opening (Preference.winner opening)
  ((List.ofFn fun option : Fin 4 => option).filter
    (fun option => decide (Preference.aggregateScore opening option.val = score))).length

def advanceCustody? (custody : CustodyObject) : Option CustodyObject :=
  if h : custody.custodySequence.val + 1 < WIRE_COUNTER_MODULUS then
    some { custody with custodySequence :=
      ⟨custody.custodySequence.val + 1, h⟩ }
  else none

def State.validB (deployment : Deployment) (state : State) : Bool :=
  decide (state.activeDomain = deployment.domain) &&
  decide (state.orderedRoster = deployment.roster) &&
  decide (state.catalogue = deployment.catalogue) &&
  match state.records with
  | [] =>
      decide (state.sequence.val = 0) &&
      decide (state.rowCounters = fun seat => (deployment.roster seat).initialCounter) &&
      decide (state.custody = .held deployment.custody) &&
      decide (state.consumedDecisions = ∅) &&
      decide (state.consumedNullifiers = ∅)
  | [record] =>
      statementDeploymentExactB deployment record.statement &&
      decide (state.sequence = record.statement.nextSequence) &&
      decide (record.statement.previousSequence.val = 0) &&
      decide (record.statement.nextSequence.val = 1) &&
      decide (state.rowCounters = fun seat => (record.statement.rows seat).counter) &&
      decide (state.custody = .allocated record.custodyAfter record.statement.allocation) &&
      decide (advanceCustody? deployment.custody = some record.custodyAfter) &&
      decide (state.consumedDecisions = {deployment.domain.decisionId}) &&
      decide (state.consumedNullifiers = nullifierSet record.statement)
  | _ => false

/-- Successful execution carries the invariant; callers cannot obtain a judged
continuation whose exact state/custody/replay shape was not rechecked. -/
structure StepResult (deployment : Deployment) where
  private mk ::
  state : State
  receipt : Receipt
  stateValid : state.validB deployment = true
deriving DecidableEq

inductive Refusal where
  | invalidStateAuthority
  | wrongFederation
  | wrongContentRoot
  | wrongActivation
  | wrongContentSession
  | wrongEpoch
  | wrongMission
  | wrongDecision
  | wrongCircuitSession
  | wrongHashSuite
  | wrongRosterOrder
  | wrongCatalogue
  | wrongQuorumPolicy
  | wrongTiePolicy
  | wrongPrivacyLabel
  | replayedDecision
  | staleSequence
  | nonSuccessorSequence
  | wrongCustody
  | custodySequenceExhausted
  | rowContextMismatch
  | rowSignatureRefused
  | rowBallotCommitmentMismatch
  | activeCountMismatch
  | quorumNotMet
  | privateDecisionRefused
  | resultMismatch
  | invalidSuccessor
deriving DecidableEq, Repr

/-! ## Sole value-deciding transition -/

private def commitDecision (state : State) (claim : Claim)
    (custodyAfter : CustodyObject) : State × Receipt :=
  let record : AllocationRecord := ⟨claim.statement, custodyAfter⟩
  let after : State :=
    ⟨state.activeDomain, state.orderedRoster, state.catalogue,
      claim.statement.nextSequence,
      (fun seat => (claim.statement.rows seat).counter),
      .allocated custodyAfter claim.statement.allocation,
      insert claim.statement.domain.decisionId state.consumedDecisions,
      state.consumedNullifiers ∪ nullifierSet claim.statement,
      [record]⟩
  let receipt : Receipt := ⟨claim.statement, custodyAfter⟩
  (after, receipt)

def judge (deployment : Deployment) (state : State) (claim : Claim)
    (opening : Preference.PrivateWitness) : Except Refusal (StepResult deployment) :=
  if state.validB deployment ≠ true then .error .invalidStateAuthority
  else if claim.statement.domain.federationId ≠ deployment.domain.federationId then
    .error .wrongFederation
  else if claim.statement.domain.contentRoot ≠ deployment.domain.contentRoot then
    .error .wrongContentRoot
  else if claim.statement.domain.activationDigest ≠ deployment.domain.activationDigest then
    .error .wrongActivation
  else if claim.statement.domain.contentSession ≠ deployment.domain.contentSession then
    .error .wrongContentSession
  else if claim.statement.domain.contentEpoch ≠ deployment.domain.contentEpoch then
    .error .wrongEpoch
  else if claim.statement.domain.missionId ≠ deployment.domain.missionId then
    .error .wrongMission
  else if claim.statement.domain.decisionId ≠ deployment.domain.decisionId then
    .error .wrongDecision
  else if claim.statement.domain.circuitSession ≠ deployment.domain.circuitSession then
    .error .wrongCircuitSession
  else if claim.statement.domain.hashSuite ≠ deployment.domain.hashSuite then
    .error .wrongHashSuite
  else if claim.statement.orderedRoster ≠ deployment.roster then
    .error .wrongRosterOrder
  else if claim.statement.catalogue ≠ deployment.catalogue then
    .error .wrongCatalogue
  else if claim.statement.quorum ≠ deployment.quorum then
    .error .wrongQuorumPolicy
  else if claim.statement.tiePolicy ≠ descriptor.tiePolicy then
    .error .wrongTiePolicy
  else if claim.statement.privacy ≠ descriptor.privacy then
    .error .wrongPrivacyLabel
  else if claim.statement.domain.decisionId ∈ state.consumedDecisions then
    .error .replayedDecision
  else if claim.statement.previousSequence ≠ state.sequence then
    .error .staleSequence
  else if claim.statement.nextSequence.val ≠ state.sequence.val + 1 then
    .error .nonSuccessorSequence
  else if claim.statement.custody ≠ deployment.custody ∨
      state.custody ≠ .held deployment.custody then
    .error .wrongCustody
  else match advanceCustody? deployment.custody with
    | none => .error .custodySequenceExhausted
    | some custodyAfter =>
      if rowsContextExactB deployment state claim.statement ≠ true then
        .error .rowContextMismatch
      else if rowsAuthenticatedB deployment claim ≠ true then
        .error .rowSignatureRefused
      else if rowBallotCommitmentsExactB claim.statement opening ≠ true then
        .error .rowBallotCommitmentMismatch
      else if Preference.check deployment.domain.hashSuite.hash8
          claim.statement.preferenceStatement opening ≠ true then
        .error .privateDecisionRefused
      else if claim.statement.activeParticipantCount.val ≠ activeParticipantCount opening then
        .error .activeCountMismatch
      else if claim.statement.activeParticipantCount.val < deployment.quorum.val then
        .error .quorumNotMet
      else if claim.statement.tieCount.val ≠ winnerTieCount opening then
        .error .resultMismatch
      else if claim.statement.allocation ≠
          (deployment.catalogue claim.statement.winner).allocation ∨
          claim.statement.effect ≠ deployment.catalogue claim.statement.winner then
        .error .resultMismatch
      else
        let committed := commitDecision state claim custodyAfter
        if hvalid : committed.1.validB deployment = true then
          .ok ⟨committed.1, committed.2, hvalid⟩
        else .error .invalidSuccessor

theorem judge_deterministic (deployment : Deployment) (state : State)
    (claim : Claim) (opening : Preference.PrivateWitness)
    {left right : StepResult deployment}
    (hl : judge deployment state claim opening = .ok left)
    (hr : judge deployment state claim opening = .ok right) : left = right := by
  rw [hl] at hr
  exact Except.ok.inj hr

theorem judge_success_state_invariant (deployment : Deployment) (state : State)
    (claim : Claim) (opening : Preference.PrivateWitness)
    (result : StepResult deployment)
    (_h : judge deployment state claim opening = .ok result) :
    result.state.validB deployment = true :=
  result.stateValid

theorem receipt_event_binds_world_output (receipt : Receipt) :
    receipt.toEvent.contribution = receipt.statement.effect.toContribution ∧
    receipt.toEvent.betaArtifact = receipt.statement.effect.betaArtifact.toArtifactRef ∧
    receipt.toEvent.expected.sequence = receipt.statement.previousSequence ∧
    receipt.toEvent.successor.sequence = receipt.statement.nextSequence := by
  simp [Receipt.toEvent, Receipt.worldContribution, Receipt.betaArtifact]

/-- A raw receipt readmits only by reproducing the exact successful transition;
there is no constructor-shaped shortcut. -/
def admitReceiptCandidate? (deployment : Deployment) (before : State) (claim : Claim)
    (opening : Preference.PrivateWitness) (candidate : ReceiptWire) : Option Receipt :=
  match judge deployment before claim opening with
  | .error _ => none
  | .ok result =>
      if result.receipt.toWire = candidate then some result.receipt else none

/-! ## Executable strict-interpreter vectors -/

private def repeatedDigest (value : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨value % 256, Nat.mod_lt _ (by decide)⟩
  length_eq := by simp

private def repeatedDigest64 (value : Nat) : Digest64 where
  bytes := List.replicate 64 ⟨value % 256, Nat.mod_lt _ (by decide)⟩
  length_eq := by simp

def fixtureRoster : SeatIndex → RosterRow
  | ⟨0, _⟩ => ⟨0, repeatedDigest 10, repeatedDigest 20, 40⟩
  | ⟨1, _⟩ => ⟨1, repeatedDigest 11, repeatedDigest 21, 41⟩
  | ⟨2, _⟩ => ⟨2, repeatedDigest 12, repeatedDigest 22, 42⟩
  | ⟨3, _⟩ => ⟨3, repeatedDigest 13, repeatedDigest 23, 43⟩

def fixtureDomain : DecisionDomain where
  federationId := repeatedDigest 1
  contentRoot := repeatedDigest 2
  activationDigest := repeatedDigest 3
  contentSession := repeatedDigest 4
  contentEpoch := 17
  missionId := 701
  decisionId := repeatedDigest 5
  circuitSession := 77
  hashSuite := .poseidon2BabyBearW16V1

def fixtureCustody : CustodyObject where
  relic := 31
  sourceReceipt := repeatedDigest 7
  currentHolder := repeatedDigest 8
  custodySequence := 9

def fixtureArtifact (tag : Fin 4) : WireArtifactRef where
  missionId := 701
  artifactId := ⟨tag.val, lt_trans tag.isLt (by decide)⟩
  sourceDigest := repeatedDigest (60 + tag.val)
  contentDigest := repeatedDigest (70 + tag.val)

def fixtureCatalogue : Fin ALLOCATION_COUNT → OptionEffect
  | ⟨0, _⟩ => ⟨.containment, 3, 0, 3, 0, 8, fixtureArtifact 0⟩
  | ⟨1, _⟩ => ⟨.research, 8, 0, 1, 2, 25, fixtureArtifact 1⟩
  | ⟨2, _⟩ => ⟨.repair, 0, 7, 2, 0, 4, fixtureArtifact 2⟩
  | ⟨3, _⟩ => ⟨.reserve, 0, 4, 4, 1, 1, fixtureArtifact 3⟩

def fixtureDeployment : Deployment where
  domain := fixtureDomain
  roster := fixtureRoster
  custody := fixtureCustody
  catalogue := fixtureCatalogue
  quorum := 3
  rosterSeatsExact := by native_decide
  rosterPlayersInjective := by native_decide
  rosterCredentialsInjective := by native_decide
  catalogueOrderExact := by native_decide
  effectVectorsInjective := by native_decide
  quorumNontrivial := by decide
  rosterCounterSuccessorAvailable := by native_decide
  custodySuccessorAvailable := by decide

def fixtureOpening : Preference.PrivateWitness :=
  Dregg2.Games.PrivatePreferenceDescriptor.fixtureWitness

def rowsForOpening (opening : Preference.PrivateWitness) : SeatIndex → PublicRowContext := fun seat =>
  let row := fixtureRoster seat
  let counter : WireCounter :=
    ⟨row.initialCounter.val + 1, by fin_cases seat <;> decide⟩
  ⟨seat, row.playerKey, row.credential, counter,
    derivedRowNullifier fixtureDomain row counter,
    rowBallotCommitment fixtureDomain seat opening⟩

def fixtureRows : SeatIndex → PublicRowContext := rowsForOpening fixtureOpening

def fixtureStatement : DecisionStatement where
  domain := fixtureDomain
  orderedRoster := fixtureRoster
  custody := fixtureCustody
  catalogue := fixtureCatalogue
  quorum := 3
  tiePolicy := .lowestIndex
  privacy := .operatorVisiblePlaintextInput
  previousSequence := 0
  nextSequence := 1
  rows := fixtureRows
  ballotRoot := Preference.ballotRoot fixtureDomain.hashSuite.hash8
    fixtureDomain.circuitSession.val fixtureOpening
  activeParticipantCount := ⟨activeParticipantCount fixtureOpening, by native_decide⟩
  winner := ⟨Preference.winner fixtureOpening,
    Dregg2.Games.PrivatePreferenceDescriptor.winner_lt fixtureOpening⟩
  tieCount := ⟨winnerTieCount fixtureOpening, by native_decide⟩
  allocation := .research
  effect := fixtureCatalogue 1

/-- Fixture-only capability issuer.  It is private and makes no cryptographic
claim; production must refine the opaque constructor through a real verifier. -/
private def issueFixtureRowSignature (statement : DecisionStatement)
    (seat : SeatIndex) : RowSignature :=
  ⟨(fixtureRoster seat).playerKey, (statement.rowSigningBody seat).preimage,
    repeatedDigest64 (100 + seat.val)⟩

private def authorizationsFor (statement : DecisionStatement) : SeatIndex → RowAuthorization :=
  fun seat => ⟨seat, issueFixtureRowSignature statement seat⟩

def fixtureClaim : Claim := ⟨fixtureStatement, authorizationsFor fixtureStatement⟩
def fixtureBefore : State := start fixtureDeployment

def rootCanonicalB (root : Fin 8 → Int) : Bool :=
  (List.ofFn root).all fun lane =>
    decide (0 ≤ lane ∧ lane < CIRCUIT_SESSION_MODULUS)

theorem fixture_poseidon_roots_are_canonical_babybear_elements :
    rootCanonicalB fixtureStatement.ballotRoot = true ∧
    allFour (fun seat => rootCanonicalB (fixtureStatement.rows seat).ballotCommitment) = true := by
  native_decide

def fixtureAcceptedB : Bool :=
  match judge fixtureDeployment fixtureBefore fixtureClaim fixtureOpening with
  | .error _ => false
  | .ok result =>
      result.state.validB fixtureDeployment &&
      decide (result.receipt.statement = fixtureStatement) &&
      decide (result.receipt.custodyAfter = advanceCustody? fixtureCustody)

theorem fixture_value_decision_accepts_with_valid_opaque_authority :
    fixtureAcceptedB = true := by native_decide

def missionSubstitution : Claim :=
  let statement := { fixtureStatement with domain :=
    { fixtureStatement.domain with missionId := 702 } }
  ⟨statement, authorizationsFor statement⟩

theorem mission_substitution_refuses :
    judge fixtureDeployment fixtureBefore missionSubstitution fixtureOpening =
      .error .wrongMission := by native_decide

def contentRootSubstitution : Claim :=
  let statement := { fixtureStatement with domain :=
    { fixtureStatement.domain with contentRoot := repeatedDigest 99 } }
  ⟨statement, authorizationsFor statement⟩

theorem content_root_substitution_refuses :
    judge fixtureDeployment fixtureBefore contentRootSubstitution fixtureOpening =
      .error .wrongContentRoot := by native_decide

def reorderedRoster : SeatIndex → RosterRow
  | ⟨0, _⟩ => fixtureRoster 1
  | ⟨1, _⟩ => fixtureRoster 0
  | ⟨2, _⟩ => fixtureRoster 2
  | ⟨3, _⟩ => fixtureRoster 3

def rosterOrderSubstitution : Claim :=
  let statement := { fixtureStatement with orderedRoster := reorderedRoster }
  ⟨statement, authorizationsFor statement⟩

theorem roster_order_substitution_refuses :
    judge fixtureDeployment fixtureBefore rosterOrderSubstitution fixtureOpening =
      .error .wrongRosterOrder := by native_decide

def custodySubstitution : Claim :=
  let statement := { fixtureStatement with custody :=
    { fixtureCustody with currentHolder := repeatedDigest 97 } }
  ⟨statement, authorizationsFor statement⟩

theorem custody_substitution_refuses :
    judge fixtureDeployment fixtureBefore custodySubstitution fixtureOpening =
      .error .wrongCustody := by native_decide

def resultSubstitution : Claim :=
  let statement := { fixtureStatement with allocation := .repair }
  ⟨statement, authorizationsFor statement⟩

theorem result_substitution_refuses :
    judge fixtureDeployment fixtureBefore resultSubstitution fixtureOpening =
      .error .resultMismatch := by native_decide

def privacyRelabelling : Claim :=
  let statement := { fixtureStatement with privacy := .independentOperatorThreshold }
  ⟨statement, authorizationsFor statement⟩

theorem privacy_relabelling_refuses :
    judge fixtureDeployment fixtureBefore privacyRelabelling fixtureOpening =
      .error .wrongPrivacyLabel := by native_decide

/-- The host supplies a different routine but claims the same id.  There is no
hash-function parameter to inject: even with fresh exact row signatures the
Lean-owned routine rejects its alternate root. -/
def alternateHash8 (input : List Int) (lane : Fin 8) : Int :=
  fixtureDomain.hashSuite.hash8 input lane + 1

def sameIdHashSubstitution : Claim :=
  let statement := { fixtureStatement with ballotRoot :=
    (Preference.ballotRoot alternateHash8 fixtureDomain.circuitSession.val fixtureOpening) }
  ⟨statement, authorizationsFor statement⟩

theorem hostile_same_id_hash_implementation_substitution_refused :
    judge fixtureDeployment fixtureBefore sameIdHashSubstitution fixtureOpening =
      .error .privateDecisionRefused := by native_decide

/-! The concrete additive-hash collision which motivated the Poseidon2 cutover.
One active ballot scores research at three.  The forged opening activates two
more rows by adding one option-zero point to each (`packedLow + 256`,
`packedHigh + 1`) and subtracts 257 from one blind.  Winner and tie count stay
fixed.  The obsolete additive hash collides; the live Poseidon2 relation does
not, so the forged quorum opening is refused. -/

def collisionBaseOpening : Preference.PrivateWitness where
  scores := fun participant option =>
    if participant = 0 ∧ option = 1 then 3 else 0
  blinding := fixtureOpening.blinding

def collisionForgedOpening : Preference.PrivateWitness where
  scores := fun participant option =>
    if (participant = 1 ∨ participant = 2) ∧ option = 0 then 1
    else collisionBaseOpening.scores participant option
  blinding := fun lane =>
    if lane = 0 then collisionBaseOpening.blinding lane - 257
    else collisionBaseOpening.blinding lane

theorem obsolete_additive_hash_has_concrete_quorum_collision :
    Preference.ballotRoot Dregg2.Games.PrivatePreferenceDescriptor.toyHash8
        fixtureDomain.circuitSession.val collisionBaseOpening =
      Preference.ballotRoot Dregg2.Games.PrivatePreferenceDescriptor.toyHash8
        fixtureDomain.circuitSession.val collisionForgedOpening ∧
    activeParticipantCount collisionBaseOpening = 1 ∧
    activeParticipantCount collisionForgedOpening = 3 ∧
    Preference.winner collisionBaseOpening = Preference.winner collisionForgedOpening ∧
    winnerTieCount collisionBaseOpening = winnerTieCount collisionForgedOpening := by
  native_decide

def collisionForgeryStatement : DecisionStatement :=
  { fixtureStatement with
    rows := rowsForOpening collisionForgedOpening
    ballotRoot := Preference.ballotRoot fixtureDomain.hashSuite.hash8
      fixtureDomain.circuitSession.val collisionBaseOpening
    activeParticipantCount := ⟨3, by decide⟩
    winner := ⟨Preference.winner collisionBaseOpening,
      Dregg2.Games.PrivatePreferenceDescriptor.winner_lt collisionBaseOpening⟩
    tieCount := ⟨winnerTieCount collisionBaseOpening, by native_decide⟩
    allocation := .research
    effect := fixtureCatalogue 1 }

def collisionForgeryClaim : Claim :=
  ⟨collisionForgeryStatement, authorizationsFor collisionForgeryStatement⟩

theorem concrete_additive_collision_forgery_refused_by_live_poseidon2 :
    judge fixtureDeployment fixtureBefore collisionForgeryClaim collisionForgedOpening =
      .error .privateDecisionRefused := by native_decide

def swappedAuthorizations : SeatIndex → RowAuthorization
  | ⟨0, _⟩ => fixtureClaim.authorizations 1
  | ⟨1, _⟩ => fixtureClaim.authorizations 0
  | ⟨2, _⟩ => fixtureClaim.authorizations 2
  | ⟨3, _⟩ => fixtureClaim.authorizations 3

def rowSubstitutionClaim : Claim := ⟨fixtureStatement, swappedAuthorizations⟩

theorem hostile_signed_roster_row_substitution_refused :
    judge fixtureDeployment fixtureBefore rowSubstitutionClaim fixtureOpening =
      .error .rowSignatureRefused := by native_decide

def replayedRowContexts : SeatIndex → PublicRowContext
  | ⟨0, _⟩ => { fixtureRows 0 with ballotCommitment :=
      fun lane => (fixtureRows 0).ballotCommitment lane + 1 }
  | ⟨1, _⟩ => fixtureRows 1
  | ⟨2, _⟩ => fixtureRows 2
  | ⟨3, _⟩ => fixtureRows 3

/-- Reusing a row signature after changing its exact signed ballot commitment
fails before the private relation is checked. -/
def replayedRowSignaturesClaim : Claim :=
  let statement := { fixtureStatement with rows := replayedRowContexts }
  ⟨statement, fixtureClaim.authorizations⟩

theorem hostile_row_signature_replay_on_changed_statement_refused :
    judge fixtureDeployment fixtureBefore replayedRowSignaturesClaim fixtureOpening =
      .error .rowSignatureRefused := by native_decide

def forgedRowCommitmentStatement : DecisionStatement :=
  { fixtureStatement with rows := replayedRowContexts }

def forgedRowCommitmentClaim : Claim :=
  ⟨forgedRowCommitmentStatement, authorizationsFor forgedRowCommitmentStatement⟩

theorem hostile_freshly_signed_wrong_per_seat_commitment_refused :
    judge fixtureDeployment fixtureBefore forgedRowCommitmentClaim fixtureOpening =
      .error .rowBallotCommitmentMismatch := by native_decide

def wrongNullifierRows : SeatIndex → PublicRowContext
  | ⟨0, _⟩ => { fixtureRows 0 with nullifier :=
      { (fixtureRows 0).nullifier with counter := 99 } }
  | ⟨1, _⟩ => fixtureRows 1
  | ⟨2, _⟩ => fixtureRows 2
  | ⟨3, _⟩ => fixtureRows 3

def wrongDerivedNullifierStatement : DecisionStatement :=
  { fixtureStatement with rows := wrongNullifierRows }

def wrongDerivedNullifierClaim : Claim :=
  ⟨wrongDerivedNullifierStatement, authorizationsFor wrongDerivedNullifierStatement⟩

theorem hostile_signed_but_nonderived_nullifier_refused :
    judge fixtureDeployment fixtureBefore wrongDerivedNullifierClaim fixtureOpening =
      .error .rowContextMismatch := by native_decide

def overstatedActivityStatement : DecisionStatement :=
  { fixtureStatement with activeParticipantCount := 3 }

def overstatedActivityClaim : Claim :=
  ⟨overstatedActivityStatement, authorizationsFor overstatedActivityStatement⟩

def oneActiveOpening : Preference.PrivateWitness where
  scores := collisionBaseOpening.scores
  blinding := collisionBaseOpening.blinding

def overstatedActivityOnExactRootStatement : DecisionStatement :=
  { overstatedActivityStatement with
    rows := rowsForOpening oneActiveOpening
    ballotRoot := Preference.ballotRoot fixtureDomain.hashSuite.hash8
      fixtureDomain.circuitSession.val oneActiveOpening
    winner := ⟨Preference.winner oneActiveOpening,
      Dregg2.Games.PrivatePreferenceDescriptor.winner_lt oneActiveOpening⟩
    tieCount := ⟨winnerTieCount oneActiveOpening, by native_decide⟩
    allocation := .research
    effect := fixtureCatalogue 1 }

def overstatedActivityOnExactRootClaim : Claim :=
  ⟨overstatedActivityOnExactRootStatement,
    authorizationsFor overstatedActivityOnExactRootStatement⟩

theorem hostile_signed_active_count_not_derived_from_opening_refused :
    judge fixtureDeployment fixtureBefore overstatedActivityOnExactRootClaim oneActiveOpening =
      .error .activeCountMismatch := by native_decide

def forgedStateSnapshot : StateSnapshot :=
  { fixtureBefore.toSnapshot with sequence := 1 }

theorem hostile_forged_state_snapshot_has_no_live_authority :
    readmitInitialState? fixtureDeployment forgedStateSnapshot = none := by native_decide

def forgedReceiptCandidate : ReceiptWire where
  statement := { fixtureStatement with effect := fixtureCatalogue 2 }
  custodyAfter := (advanceCustody? fixtureCustody).getD fixtureCustody

theorem hostile_direct_receipt_candidate_mint_refused :
    admitReceiptCandidate? fixtureDeployment fixtureBefore fixtureClaim fixtureOpening
      forgedReceiptCandidate = none := by native_decide

def acceptedAfter? : Option State :=
  match judge fixtureDeployment fixtureBefore fixtureClaim fixtureOpening with
  | .error _ => none
  | .ok result => some result.state

def replayResult : Option Refusal := do
  let after ← acceptedAfter?
  match judge fixtureDeployment after fixtureClaim fixtureOpening with
  | .error refusal => some refusal
  | .ok _ => none

theorem exact_decision_replay_refuses :
    replayResult = some .replayedDecision := by native_decide

def belowQuorumOpening : Preference.PrivateWitness where
  scores := fun participant option =>
    if participant = 0 then fixtureOpening.scores participant option else 0
  blinding := fixtureOpening.blinding

def belowQuorumStatement : DecisionStatement :=
  { fixtureStatement with
    rows := rowsForOpening belowQuorumOpening
    ballotRoot := Preference.ballotRoot fixtureDomain.hashSuite.hash8
      fixtureDomain.circuitSession.val belowQuorumOpening
    activeParticipantCount := ⟨activeParticipantCount belowQuorumOpening, by native_decide⟩
    winner := ⟨Preference.winner belowQuorumOpening,
      Dregg2.Games.PrivatePreferenceDescriptor.winner_lt belowQuorumOpening⟩
    tieCount := ⟨winnerTieCount belowQuorumOpening, by native_decide⟩
    allocation := (fixtureCatalogue ⟨Preference.winner belowQuorumOpening,
      Dregg2.Games.PrivatePreferenceDescriptor.winner_lt belowQuorumOpening⟩).allocation
    effect := fixtureCatalogue ⟨Preference.winner belowQuorumOpening,
      Dregg2.Games.PrivatePreferenceDescriptor.winner_lt belowQuorumOpening⟩ }

def belowQuorumClaim : Claim :=
  ⟨belowQuorumStatement, authorizationsFor belowQuorumStatement⟩

theorem authored_quorum_has_teeth :
    judge fixtureDeployment fixtureBefore belowQuorumClaim belowQuorumOpening =
      .error .quorumNotMet := by native_decide

theorem all_zero_ballot_is_explicit_abstention :
    participantActiveB belowQuorumOpening 1 = false ∧
    participantActiveB belowQuorumOpening 2 = false ∧
    participantActiveB belowQuorumOpening 3 = false := by native_decide

theorem authored_options_have_distinct_effects :
    fixtureCatalogue 0 ≠ fixtureCatalogue 1 ∧
    fixtureCatalogue 1 ≠ fixtureCatalogue 2 ∧
    fixtureCatalogue 2 ≠ fixtureCatalogue 3 := by native_decide

#assert_axioms descriptor_is_exactly_n4k4_operator_visible
#assert_axioms same_hash_suite_id_selects_same_implementation
#assert_axioms judge_deterministic
#assert_axioms judge_success_state_invariant
#assert_axioms receipt_event_binds_world_output

#assert_compiled fixture_value_decision_accepts_with_valid_opaque_authority
#assert_compiled fixture_poseidon_roots_are_canonical_babybear_elements
#assert_compiled mission_substitution_refuses
#assert_compiled content_root_substitution_refuses
#assert_compiled roster_order_substitution_refuses
#assert_compiled custody_substitution_refuses
#assert_compiled result_substitution_refuses
#assert_compiled privacy_relabelling_refuses
#assert_compiled hostile_same_id_hash_implementation_substitution_refused
#assert_compiled obsolete_additive_hash_has_concrete_quorum_collision
#assert_compiled concrete_additive_collision_forgery_refused_by_live_poseidon2
#assert_compiled hostile_signed_roster_row_substitution_refused
#assert_compiled hostile_row_signature_replay_on_changed_statement_refused
#assert_compiled hostile_freshly_signed_wrong_per_seat_commitment_refused
#assert_compiled hostile_signed_but_nonderived_nullifier_refused
#assert_compiled hostile_signed_active_count_not_derived_from_opening_refused
#assert_compiled hostile_forged_state_snapshot_has_no_live_authority
#assert_compiled hostile_direct_receipt_candidate_mint_refused
#assert_compiled exact_decision_replay_refuses
#assert_compiled authored_quorum_has_teeth
#assert_compiled all_zero_ballot_is_explicit_abstention
#assert_compiled authored_options_have_distinct_effects

end Dregg2.Games.PathOfAngels.PoaCrewPreferenceDrExExercise
