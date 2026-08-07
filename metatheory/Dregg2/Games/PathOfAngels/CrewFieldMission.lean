/-
# CrewFieldMission — semantic kernel for private briefings and deck extraction

This is the game-facing layer above the lower-level Crew Relay vocabulary.  Four
officers receive different role-exact observations.  They do not act in one
shared browser session: every disclosure and choice is an independently signed
handoff over the exact predecessor root and personal counter.

Privacy is deliberately limited and temporal.  The trusted mission dealer and
the operator executing Lean see the complete ordered briefing deck.  Before a
seat acts, other players receive no observation through this state-machine API;
the observation is deliberately disclosed into the public signed handoff and
combined field record after that seat acts.  This is not MPC, FHE, threshold
privacy, or secrecy from the operator.  The public deck commitment binds the
activated ordering but makes no hiding claim.

The first three specialists disclose evidence and recommend a route.  The
quartermaster receives the accumulated field record and chooses both the route
and whether to return safely or descend for a deeper recovery.  Safe extraction
needs two matching signed route recommendations; those recommendations are not
misdescribed as independent sensor corroboration.  Deep recovery needs unanimity,
three matching observations, a stable extraction window, and a coordinated
salvage strategy.

Completion yields one exactly replayable combined field record and one predeclared beta
candidate through `ActivityOutcome.Checked`.  It does not mint a `JudgedRun`, an
Archive entry, or curator authority; those remain later canonical-settlement
boundaries.  This file is not a durable aggregate or a byte-wire specification.
`CanonicalRunAdmission` is an explicit one-shot *deployment boundary*, not a
claim that immutable Lean values are globally linear: a runtime must issue it
once, consume the session key by atomic CAS, and wrap accepted transitions in
the generic finalized event stream.
-/
import Mathlib.Data.Finset.Sort
import Dregg2.Crypto.Keccak
import Dregg2.Crypto.MlDsaVerifyReal
import Dregg2.Games.PathOfAngels.CrewRelayExpedition
import Dregg2.Games.PathOfAngels.ActivityOutcome
import Dregg2.Games.PathOfAngels.PlayerCounters
import Dregg2.Games.PathOfAngels.CrewSigningVectors
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.CrewFieldMission

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.CrewRelayExpedition

set_option autoImplicit false

abbrev CREW_SIZE : Nat := 4

/-! ## Authored mission and hidden role briefings -/

inductive Route where
  | maintenanceSpine
  | signalGallery
  | sealedNave
deriving Repr, DecidableEq

def Route.code : Route → Nat
  | .maintenanceSpine => 0
  | .signalGallery => 1
  | .sealedNave => 2

inductive ExtractionChoice where
  | returnNow
  | descendFurther
deriving Repr, DecidableEq

def ExtractionChoice.strategy : ExtractionChoice → Strategy
  | .returnNow => .survey
  | .descendFurther => .salvage

/-- Every specialist action spends according to the crew-wide strategy. -/
def specialistOperationalCost : Strategy → Nat
  | .survey => 1
  | .salvage => 2

def mandatorySpecialistSpend (extraction : ExtractionChoice) : Nat :=
  (CREW_SIZE - 1) * specialistOperationalCost extraction.strategy

inductive ExtractionWindow where
  | closing
  | stable
deriving Repr, DecidableEq

inductive BriefingPrivacyBoundary where
  | trustedDealerOperatorVisibleThenPublicHandoff
deriving Repr, DecidableEq

/-- These observations are private until their owner signs a handoff which
discloses them.  The constructor itself carries the role: a pathfinder briefing
cannot be relabelled as containment evidence. -/
inductive PrivateObservation where
  | pathfinder (mapped : Route)
  | engineer (structurallySound : Route)
  | containment (hazardClear : Route)
  | quartermaster (window : ExtractionWindow)
deriving Repr, DecidableEq

def PrivateObservation.role : PrivateObservation → CrewRole
  | .pathfinder _ => .pathfinder
  | .engineer _ => .engineer
  | .containment _ => .containment
  | .quartermaster _ => .quartermaster

def PrivateObservation.supportedRoute? : PrivateObservation → Option Route
  | .pathfinder route | .engineer route | .containment route => some route
  | .quartermaster _ => none

def PrivateObservation.code : PrivateObservation → Nat
  | .pathfinder route => 10 + route.code
  | .engineer route => 20 + route.code
  | .containment route => 30 + route.code
  | .quartermaster .closing => 40
  | .quartermaster .stable => 41

structure BriefingAssignment where
  seat : SeatId
  observation : PrivateObservation
deriving DecidableEq

structure RouteOutcomeSpec where
  route : Route
  extraction : ExtractionChoice
  operationalCost : Nat
  featuredArtifact : ArtifactRef
  outcome : ActivityOutcome.Raw
deriving DecidableEq

def RouteOutcomeSpec.key (spec : RouteOutcomeSpec) : Route × ExtractionChoice :=
  (spec.route, spec.extraction)

def routeOutcomeBy? : List RouteOutcomeSpec → Route → ExtractionChoice →
    Option RouteOutcomeSpec
  | [], _, _ => none
  | spec :: specs, route, extraction =>
      if spec.route = route ∧ spec.extraction = extraction then some spec
      else routeOutcomeBy? specs route extraction

def briefingBySeat? : List BriefingAssignment → SeatId → Option BriefingAssignment
  | [], _ => none
  | briefing :: briefings, id =>
      if briefing.seat = id then some briefing else briefingBySeat? briefings id

structure RawConfig where
  federationId : Digest32
  contentSession : Digest32
  missionEpoch : EpochId
  missionId : MissionId
  relayId : Digest32
  briefingPrivacy : BriefingPrivacyBoundary
  briefingHashSuiteId : Digest32
  briefingCommitment : Digest32
  messageDigestSuiteId : Digest32
  signingSuiteId : Digest32
  roster : List Seat
  policy : ActivityOutcome.Policy
  operationalBudget : Nat
  routeOutcomes : List RouteOutcomeSpec
deriving DecidableEq

/-- Public identity of the exact activated mission.  The hidden briefing deck is
bound by `briefingCommitment`; collision resistance of its deployment hash is a
named boundary rather than a theorem about `Digest32`. -/
structure SessionDigest where
  federationId : Digest32
  contentSession : Digest32
  missionEpoch : EpochId
  missionId : MissionId
  relayId : Digest32
  briefingPrivacy : BriefingPrivacyBoundary
  briefingHashSuiteId : Digest32
  briefingCommitment : Digest32
  messageDigestSuiteId : Digest32
  signingSuiteId : Digest32
  roster : List Seat
  policy : ActivityOutcome.Policy
  operationalBudget : Nat
  routeOutcomes : List RouteOutcomeSpec
deriving DecidableEq

def RawConfig.sessionDigest (raw : RawConfig) : SessionDigest where
  federationId := raw.federationId
  contentSession := raw.contentSession
  missionEpoch := raw.missionEpoch
  missionId := raw.missionId
  relayId := raw.relayId
  briefingPrivacy := raw.briefingPrivacy
  briefingHashSuiteId := raw.briefingHashSuiteId
  briefingCommitment := raw.briefingCommitment
  messageDigestSuiteId := raw.messageDigestSuiteId
  signingSuiteId := raw.signingSuiteId
  roster := raw.roster
  policy := raw.policy
  operationalBudget := raw.operationalBudget
  routeOutcomes := raw.routeOutcomes

/-- Exact ordered deck preimage.  The digest boundary receives deployment
identity, roster order, the temporal privacy label, and every role briefing. -/
structure BriefingDeckPreimage where
  federationId : Digest32
  contentSession : Digest32
  missionEpoch : EpochId
  missionId : MissionId
  relayId : Digest32
  privacy : BriefingPrivacyBoundary
  roster : List Seat
  orderedBriefings : List BriefingAssignment
deriving DecidableEq

def briefingDeckPreimage (raw : RawConfig)
    (briefings : List BriefingAssignment) : BriefingDeckPreimage where
  federationId := raw.federationId
  contentSession := raw.contentSession
  missionEpoch := raw.missionEpoch
  missionId := raw.missionId
  relayId := raw.relayId
  privacy := raw.briefingPrivacy
  roster := raw.roster
  orderedBriefings := briefings

/-- Activated digest trust boundary.  Collision resistance and faithful byte
encoding remain deployment obligations; `Config` prevents substitution of this
function under the same suite id after activation. -/
structure BriefingDigestBoundary where
  id : Digest32
  digest : BriefingDeckPreimage → Digest32

def expectedRoles : List CrewRole :=
  [.pathfinder, .engineer, .containment, .quartermaster]

def briefingsValidB (roster : List Seat) (briefings : List BriefingAssignment) : Bool :=
  decide (briefings.map BriefingAssignment.seat = roster.map Seat.id) &&
  briefings.all fun briefing =>
    match seatById? roster briefing.seat with
    | none => false
    | some seat => decide (briefing.observation.role = seat.role)

def expectedRouteOutcomeKeys : List (Route × ExtractionChoice) :=
  [ (.maintenanceSpine, .returnNow), (.maintenanceSpine, .descendFurther)
  , (.signalGallery, .returnNow), (.signalGallery, .descendFurther)
  , (.sealedNave, .returnNow), (.sealedNave, .descendFurther) ]

def routeSpecsFor (extraction : ExtractionChoice)
    (specs : List RouteOutcomeSpec) : List RouteOutcomeSpec :=
  specs.filter fun spec => decide (spec.extraction = extraction)

def routeCostsFor (extraction : ExtractionChoice)
    (specs : List RouteOutcomeSpec) : List Nat :=
  (routeSpecsFor extraction specs).map RouteOutcomeSpec.operationalCost

def routeArtifactsFor (extraction : ExtractionChoice)
    (specs : List RouteOutcomeSpec) : List ArtifactRef :=
  (routeSpecsFor extraction specs).map RouteOutcomeSpec.featuredArtifact

def routeRewardsFor (extraction : ExtractionChoice)
    (specs : List RouteOutcomeSpec) : List ActivityOutcome.Raw :=
  (routeSpecsFor extraction specs).map RouteOutcomeSpec.outcome

/-- Because safe return depends on matching recommendations rather than hidden
sensor agreement, any authored return route can be recommended by two specialists.
Activation therefore requires at least one such route to remain affordable after
all three mandatory survey handoffs. -/
def authoredSafeTerminalReachabilityFloorB (raw : RawConfig) : Bool :=
  (routeSpecsFor .returnNow raw.routeOutcomes).any fun spec =>
    decide (mandatorySpecialistSpend .returnNow + spec.operationalCost ≤
      raw.operationalBudget)

def rawConfigValidB (raw : RawConfig) (briefings : List BriefingAssignment)
    (briefingDigest : BriefingDigestBoundary) : Bool :=
  decide (raw.roster.length = CREW_SIZE) &&
  decide (raw.roster.map Seat.id = [⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨3⟩]) &&
  decide (raw.roster.map Seat.role = expectedRoles) &&
  decide (raw.roster.map Seat.playerKey).Nodup &&
  decide (raw.roster.map Seat.credential).Nodup &&
  raw.roster.all (fun seat => decide (seat.initialCounter + 1 < PLAYER_COUNTER_MODULUS)) &&
  briefingsValidB raw.roster briefings &&
  decide (raw.briefingPrivacy =
    .trustedDealerOperatorVisibleThenPublicHandoff) &&
  decide (raw.briefingHashSuiteId = briefingDigest.id) &&
  decide (raw.briefingCommitment =
    briefingDigest.digest (briefingDeckPreimage raw briefings)) &&
  decide (raw.federationId = raw.policy.mission.federationId) &&
  decide (raw.contentSession = raw.policy.mission.contentSession) &&
  decide (raw.missionEpoch = raw.policy.mission.epoch) &&
  decide (raw.missionId = raw.policy.mission.missionId) &&
  decide (raw.policy.allowedBeta.filter (fun artifact =>
    artifact.missionId = raw.missionId) = raw.policy.allowedBeta) &&
  decide (0 < raw.operationalBudget ∧ raw.operationalBudget ≤ 32) &&
  decide (raw.routeOutcomes.map RouteOutcomeSpec.key = expectedRouteOutcomeKeys) &&
  raw.routeOutcomes.all (fun spec =>
    decide (0 < spec.operationalCost ∧ spec.operationalCost ≤ raw.operationalBudget) &&
    (ActivityOutcome.validate raw.policy spec.outcome).isSome &&
    decide (spec.featuredArtifact ∈ spec.outcome.betaCandidates) &&
    decide (spec.featuredArtifact.missionId = raw.missionId) &&
    spec.outcome.betaCandidates.all fun artifact =>
      decide (artifact.missionId = raw.missionId)) &&
  authoredSafeTerminalReachabilityFloorB raw &&
  decide (routeCostsFor .returnNow raw.routeOutcomes).Nodup &&
  decide (routeCostsFor .descendFurther raw.routeOutcomes).Nodup &&
  decide (routeArtifactsFor .returnNow raw.routeOutcomes).Nodup &&
  decide (routeArtifactsFor .descendFurther raw.routeOutcomes).Nodup &&
  decide (routeRewardsFor .returnNow raw.routeOutcomes).Nodup &&
  decide (routeRewardsFor .descendFurther raw.routeOutcomes).Nodup

structure SeatAdmissionBody where
  session : SessionDigest
  seat : Seat
deriving DecidableEq

/-! ### ⚑ SIGNATURE ENVELOPE FLAG DAY — 2026-08-07

`SIGNATURE_BYTE_LENGTH` was 64 (an ed25519-shaped placeholder no verifier ever
interpreted cryptographically).  It is now the ML-DSA-65 envelope
`publicKey ‖ signature` (1952 + 3309 = 5261 bytes), because the production
signing suite below verifies through the REAL executable FIPS 204 verify
(`Dregg2.Crypto.MlDsaVerifyReal.verifyCore`) and the verifier receives only
`playerKey : Digest32` — the full public key must travel in the envelope, and
`SHAKE256(publicKey, 32) = playerKey` is the two-source pin (roster vs envelope).

What breaks and re-emits: every previously constructed `SignatureBytes` value
(there were none outside this file's fixtures and `CrewFieldMissionRuntime`'s
wire fixtures, both re-derived here), and any wire bytes carrying the old
64-byte arrays refuse at `parseSignature`.  Nothing else in the tree names this
length. -/

abbrev MLDSA65_PUBLIC_KEY_BYTE_LENGTH : Nat := 1952
abbrev MLDSA65_SIGNATURE_BYTE_LENGTH : Nat := 3309
abbrev SIGNATURE_BYTE_LENGTH : Nat :=
  MLDSA65_PUBLIC_KEY_BYTE_LENGTH + MLDSA65_SIGNATURE_BYTE_LENGTH

/-- Finite representation of an external signature envelope
`publicKey ‖ signature`.  These bytes are opaque to the semantic kernel; only
the activated verifier interprets them (the fixture suite as a whole opaque
pattern, the production suite as the ML-DSA-65 envelope). -/
structure SignatureBytes where
  bytes : List (Fin 256)
  length_eq : bytes.length = SIGNATURE_BYTE_LENGTH
deriving DecidableEq

structure SeatSignature where
  bytes : SignatureBytes
deriving DecidableEq

structure HandoffSignature where
  bytes : SignatureBytes
deriving DecidableEq

/-! ## Signed asynchronous handoffs -/

inductive Decision where
  | specialist (recommended : Route) (command : Command)
  | finalize (chosen : Route) (extraction : ExtractionChoice) (command : Command)
deriving Repr, DecidableEq

def Decision.command : Decision → Command
  | .specialist _ command | .finalize _ _ command => command

def Decision.route : Decision → Route
  | .specialist route _ | .finalize route _ _ => route

def Decision.code : Decision → Nat
  | .specialist route command => 100 + route.code * 10 + command.code
  | .finalize route .returnNow command => 200 + route.code * 10 + command.code
  | .finalize route .descendFurther command => 300 + route.code * 10 + command.code

inductive MissionPhase where
  | active
  | extracted
deriving Repr, DecidableEq

structure SeatCounter where
  seat : SeatId
  counter : Nat
deriving Repr, DecidableEq

structure HandoffTrace where
  sequence : Nat
  seat : Seat
  previousCounter : Nat
  counter : Nat
  observation : PrivateObservation
  decision : Decision
  seatSignature : SeatSignature
  signature : HandoffSignature
deriving DecidableEq

structure StateSnapshot where
  phase : MissionPhase
  sequence : Nat
  nextSeat : Nat
  counters : List SeatCounter
  strategy : Option Strategy
  operationalBudgetRemaining : Nat
  transcript : List HandoffTrace
deriving DecidableEq

structure StateRoot where
  session : SessionDigest
  snapshot : StateSnapshot
deriving DecidableEq

structure HandoffBody where
  session : SessionDigest
  sequence : Nat
  preRoot : StateRoot
  seat : Seat
  previousCounter : Nat
  counter : Nat
  observation : PrivateObservation
  decision : Decision
deriving DecidableEq

abbrev SIGNING_FORMAT_VERSION : Nat := 1

/-- Canonical signing preimages retain the complete semantic body instead of an
ad-hoc arithmetic selection of fields.  A strict wire adapter must encode these
structures prefix-free and byte-exact before applying its signature hash. -/
structure SeatSigningPreimage where
  formatVersion : Nat
  messageDigestSuiteId : Digest32
  signatureSuiteId : Digest32
  body : SeatAdmissionBody
deriving DecidableEq

structure HandoffSigningPreimage where
  formatVersion : Nat
  messageDigestSuiteId : Digest32
  signatureSuiteId : Digest32
  body : HandoffBody
deriving DecidableEq

def SeatAdmissionBody.signingPreimage (messageDigestSuiteId signatureSuiteId : Digest32)
    (body : SeatAdmissionBody) : SeatSigningPreimage :=
  ⟨SIGNING_FORMAT_VERSION, messageDigestSuiteId, signatureSuiteId, body⟩

def HandoffBody.signingPreimage (messageDigestSuiteId signatureSuiteId : Digest32)
    (body : HandoffBody) : HandoffSigningPreimage :=
  ⟨SIGNING_FORMAT_VERSION, messageDigestSuiteId, signatureSuiteId, body⟩

/-! The message digest and signature verifier are separate activated boundaries.
A publicly computable digest commits to a message; it is never proof that the
seat's private key signed that message. -/
structure SigningMessageDigestBoundary where
  id : Digest32
  seatMessageDigest : SeatSigningPreimage → Digest32
  handoffMessageDigest : HandoffSigningPreimage → Digest32

/-- Deployment-supplied verification of an exact finite signature byte string
against the credential, player key, and full canonical semantic preimage. -/
structure ActivatedSignatureVerifier where
  id : Digest32
  verifySeat : Digest32 → CredentialId → SeatSigningPreimage → SignatureBytes → Bool
  verifyHandoff :
    Digest32 → CredentialId → HandoffSigningPreimage → SignatureBytes → Bool

/-- Digest selection, signature verification, and the clear briefing deck are
activated deployment authority.  The private constructor prevents an accept-all
verifier or same-id function substitution after activation.  It does not prove
the production verifier's cryptographic security. -/
structure Config where
  private mk ::
  raw : RawConfig
  private briefings : List BriefingAssignment
  private briefingDigest : BriefingDigestBoundary
  private messageDigest : SigningMessageDigestBoundary
  private signatureVerifier : ActivatedSignatureVerifier
  valid : rawConfigValidB raw briefings briefingDigest = true
  messageDigestSuiteExact : raw.messageDigestSuiteId = messageDigest.id
  signingSuiteExact : raw.signingSuiteId = signatureVerifier.id

/-- Public message commitment for display, logging, and detached transport.  It
does not authenticate the seat and cannot be submitted as a signature. -/
def SeatAdmissionBody.messageDigest (config : Config)
    (body : SeatAdmissionBody) : Digest32 :=
  config.messageDigest.seatMessageDigest
    (body.signingPreimage config.raw.messageDigestSuiteId config.raw.signingSuiteId)

/-- Public message commitment, not proof of key possession. -/
def HandoffBody.messageDigest (config : Config) (body : HandoffBody) : Digest32 :=
  config.messageDigest.handoffMessageDigest
    (body.signingPreimage config.raw.messageDigestSuiteId config.raw.signingSuiteId)

def seatSignatureValidB (config : Config) (seat : Seat)
    (body : SeatAdmissionBody) (signature : SeatSignature) : Bool :=
  config.signatureVerifier.verifySeat seat.playerKey seat.credential
    (body.signingPreimage config.raw.messageDigestSuiteId config.raw.signingSuiteId)
    signature.bytes

def handoffSignatureValidB (config : Config) (seat : Seat)
    (body : HandoffBody) (signature : HandoffSignature) : Bool :=
  config.signatureVerifier.verifyHandoff seat.playerKey seat.credential
    (body.signingPreimage config.raw.messageDigestSuiteId config.raw.signingSuiteId)
    signature.bytes

structure SeatCapability (config : Config) where
  private mk ::
  seat : Seat
  admission : SeatAdmissionBody
  signature : SeatSignature
  authenticated : seatSignatureValidB config seat admission signature = true
deriving DecidableEq

/-- A private observation may be opened only through the exact authenticated
seat capability.  The observation becomes public only when copied into a signed
handoff body. -/
structure Briefing (config : Config) where
  private mk ::
  seat : Seat
  observation : PrivateObservation
deriving DecidableEq

structure SignedHandoff (config : Config) where
  capability : SeatCapability config
  briefing : Briefing config
  body : HandoffBody
  signature : HandoffSignature
deriving DecidableEq

structure State where
  private mk ::
  snapshot : StateSnapshot
  root : StateRoot
deriving DecidableEq

structure CanonicalRunAdmission (config : Config) where
  private mk ::
  session : SessionDigest
  exactSession : session = config.raw.sessionDigest

def initialCounters (roster : List Seat) : List SeatCounter :=
  roster.map fun seat => ⟨seat.id, seat.initialCounter⟩

def rootFor (config : Config) (snapshot : StateSnapshot) : StateRoot :=
  ⟨config.raw.sessionDigest, snapshot⟩

private def initialState (config : Config) : State :=
  let snapshot : StateSnapshot := {
    phase := .active
    sequence := 0
    nextSeat := 0
    counters := initialCounters config.raw.roster
    strategy := none
    operationalBudgetRemaining := config.raw.operationalBudget
    transcript := []
  }
  ⟨snapshot, rootFor config snapshot⟩

def start {config : Config} (_admission : CanonicalRunAdmission config) : State :=
  initialState config

def counterFor? : List SeatCounter → SeatId → Option Nat
  | [], _ => none
  | counter :: counters, id =>
      if counter.seat = id then some counter.counter else counterFor? counters id

def setCounter (counters : List SeatCounter) (id : SeatId) (value : Nat) : List SeatCounter :=
  counters.map fun counter =>
    if counter.seat = id then { counter with counter := value } else counter

def expectedAdmission (config : Config) (seat : Seat) : SeatAdmissionBody :=
  ⟨config.raw.sessionDigest, seat⟩

def authenticateSeat? (config : Config) (id : SeatId)
    (signature : SeatSignature) : Option (SeatCapability config) := do
  let seat ← seatById? config.raw.roster id
  let admission := expectedAdmission config seat
  if h : seatSignatureValidB config seat admission signature = true then
    some ⟨seat, admission, signature, h⟩
  else none

def briefingFor? (config : Config) (capability : SeatCapability config) :
    Option (Briefing config) := do
  let assignment ← briefingBySeat? config.briefings capability.seat.id
  if assignment.observation.role = capability.seat.role then
    some ⟨capability.seat, assignment.observation⟩
  else none

def expectedBody? (config : Config) (state : State)
    (capability : SeatCapability config) (briefing : Briefing config)
    (decision : Decision) : Option HandoffBody := do
  let previousCounter ← counterFor? state.snapshot.counters capability.seat.id
  some {
    session := config.raw.sessionDigest
    sequence := state.snapshot.sequence
    preRoot := state.root
    seat := capability.seat
    previousCounter
    counter := previousCounter + 1
    observation := briefing.observation
    decision
  }

def traceOf {config : Config} (handoff : SignedHandoff config) : HandoffTrace where
  sequence := handoff.body.sequence
  seat := handoff.body.seat
  previousCounter := handoff.body.previousCounter
  counter := handoff.body.counter
  observation := handoff.body.observation
  decision := handoff.body.decision
  seatSignature := handoff.capability.signature
  signature := handoff.signature

def strategyCompatibleB (current : Option Strategy) (decision : Decision) : Bool :=
  match current with
  | none => true
  | some before => decide (before = decision.command.strategy)

def decisionRoleExactB (role : CrewRole) (decision : Decision) : Bool :=
  decide (decision.command.role = role) &&
  match role, decision with
  | .quartermaster, .finalize _ _ _ => true
  | .pathfinder, .specialist _ _ => true
  | .engineer, .specialist _ _ => true
  | .containment, .specialist _ _ => true
  | _, _ => false

def recommendationCount (transcript : List HandoffTrace) (route : Route) : Nat :=
  (transcript.filter fun trace => match trace.decision with
    | .specialist recommendation _ => decide (recommendation = route)
    | .finalize _ _ _ => false).length

def evidenceCount (transcript : List HandoffTrace) (route : Route) : Nat :=
  (transcript.filter fun trace =>
    decide (trace.observation.supportedRoute? = some route)).length

def finalChoiceValidB (state : State) (observation : PrivateObservation)
    (decision : Decision) : Bool :=
  match observation, decision with
  | .quartermaster window, .finalize route extraction command =>
      decide (state.snapshot.transcript.length = 3) &&
      decide (command.strategy = extraction.strategy) &&
      match extraction with
      | .returnNow =>
          decide (2 ≤ recommendationCount state.snapshot.transcript route)
      | .descendFurther =>
          decide (recommendationCount state.snapshot.transcript route = 3) &&
          decide (evidenceCount state.snapshot.transcript route = 3) &&
          decide (window = .stable)
  | _, _ => false

def decisionOperationalCost? (config : Config) (decision : Decision) : Option Nat :=
  match decision with
  | .specialist _ command => some (specialistOperationalCost command.strategy)
  | .finalize route extraction _ =>
      (routeOutcomeBy? config.raw.routeOutcomes route extraction).map
        RouteOutcomeSpec.operationalCost

def transcriptOperationalCost (config : Config)
    (transcript : List HandoffTrace) : Nat :=
  (transcript.map fun trace =>
    (decisionOperationalCost? config trace.decision).getD 0).sum

def operationalCostAvailableB (config : Config) (state : State)
    (decision : Decision) : Bool :=
  match decisionOperationalCost? config decision with
  | none => false
  | some cost => decide (cost ≤ state.snapshot.operationalBudgetRemaining)

def stateValidB (config : Config) (state : State) : Bool :=
  decide (state.root = rootFor config state.snapshot) &&
  decide (state.snapshot.sequence = state.snapshot.transcript.length) &&
  decide (state.snapshot.sequence = state.snapshot.nextSeat) &&
  decide (state.snapshot.nextSeat ≤ config.raw.roster.length) &&
  decide (state.snapshot.operationalBudgetRemaining ≤ config.raw.operationalBudget) &&
  decide (state.snapshot.operationalBudgetRemaining +
    transcriptOperationalCost config state.snapshot.transcript =
      config.raw.operationalBudget) &&
  decide (state.snapshot.counters.map SeatCounter.seat = config.raw.roster.map Seat.id) &&
  state.snapshot.counters.all (fun counter =>
    decide (counter.counter < PLAYER_COUNTER_MODULUS)) &&
  match state.snapshot.phase with
  | .active => decide (state.snapshot.nextSeat < config.raw.roster.length)
  | .extracted => decide (state.snapshot.nextSeat = config.raw.roster.length)

/-! ## Combined record and exact replay -/

structure CombinedFieldRecord (config : Config) where
  private mk ::
  session : SessionDigest
  route : Route
  extraction : ExtractionChoice
  strategy : Strategy
  routeOperationalCost : Nat
  totalOperationalCost : Nat
  transcript : List HandoffTrace
  finalCounters : List SeatCounter
  finalRoot : StateRoot
  outcomeRaw : ActivityOutcome.Raw
  outcome : ActivityOutcome.Checked config.raw.policy
  outcomeExact : ActivityOutcome.validate config.raw.policy outcomeRaw = some outcome
  featuredBeta : ArtifactRef
  featuredDeclared : featuredBeta ∈ outcome.betaCandidates
deriving DecidableEq

/-- Unchecked semantic projection used for replay tests.  This is not a canonical
wire value: it has no byte codec, allocation bounds, or durable event/CAS
envelope, and must not be persisted, hashed, or signed directly. -/
structure RawCombinedFieldRecord where
  session : SessionDigest
  route : Route
  extraction : ExtractionChoice
  strategy : Strategy
  routeOperationalCost : Nat
  totalOperationalCost : Nat
  transcript : List HandoffTrace
  finalCounters : List SeatCounter
  finalRoot : StateRoot
  outcome : ActivityOutcome.Raw
  featuredBeta : ArtifactRef
deriving DecidableEq

def CombinedFieldRecord.toRaw {config : Config}
    (record : CombinedFieldRecord config) : RawCombinedFieldRecord where
  session := record.session
  route := record.route
  extraction := record.extraction
  strategy := record.strategy
  routeOperationalCost := record.routeOperationalCost
  totalOperationalCost := record.totalOperationalCost
  transcript := record.transcript
  finalCounters := record.finalCounters
  finalRoot := record.finalRoot
  outcome := record.outcomeRaw
  featuredBeta := record.featuredBeta

private def completedRecord? (config : Config) (state : State) :
    Option (CombinedFieldRecord config) := do
  if state.snapshot.phase ≠ .extracted then none
  let finalTrace ← state.snapshot.transcript.getLast?
  let (route, extraction) ← match finalTrace.decision with
    | .finalize route extraction _ => some (route, extraction)
    | .specialist _ _ => none
  let spec ← routeOutcomeBy? config.raw.routeOutcomes route extraction
  let raw := spec.outcome
  match houtcome : ActivityOutcome.validate config.raw.policy raw with
  | none => none
  | some outcome =>
      if hfeatured : spec.featuredArtifact ∈ outcome.betaCandidates then
        some ⟨config.raw.sessionDigest, route, extraction, extraction.strategy,
          spec.operationalCost,
          transcriptOperationalCost config state.snapshot.transcript,
          state.snapshot.transcript, state.snapshot.counters, state.root, raw,
          outcome, houtcome, spec.featuredArtifact, hfeatured⟩
      else none

structure StepResult (config : Config) where
  private mk ::
  state : State
  completion : Option (CombinedFieldRecord config)
deriving DecidableEq

inductive Refusal where
  | invalidState
  | terminal
  | wrongSeat
  | capabilityMismatch
  | briefingMismatch
  | wrongSession
  | staleSequence
  | staleRoot
  | bodySeatMismatch
  | observationMismatch
  | counterMismatch
  | counterOutOfRange
  | signatureRefused
  | roleWidening
  | strategyConflict
  | routeEvidenceRefused
  | insufficientOperationalBudget
  | invalidSuccessor
  | outcomeRefused
deriving Repr, DecidableEq

private def transition (config : Config) (state : State)
    (handoff : SignedHandoff config) : State :=
  let nextSeat := state.snapshot.nextSeat + 1
  let operationalCost :=
    (decisionOperationalCost? config handoff.body.decision).getD 0
  let snapshot : StateSnapshot := {
    phase := if nextSeat = config.raw.roster.length then .extracted else .active
    sequence := state.snapshot.sequence + 1
    nextSeat
    counters := setCounter state.snapshot.counters handoff.body.seat.id handoff.body.counter
    strategy := some handoff.body.decision.command.strategy
    operationalBudgetRemaining :=
      state.snapshot.operationalBudgetRemaining - operationalCost
    transcript := state.snapshot.transcript ++ [traceOf handoff]
  }
  ⟨snapshot, rootFor config snapshot⟩

def execute (config : Config) (state : State) (handoff : SignedHandoff config) :
    Except Refusal (StepResult config) :=
  if stateValidB config state ≠ true then .error .invalidState
  else if state.snapshot.phase = .extracted then .error .terminal
  else match config.raw.roster[state.snapshot.nextSeat]? with
    | none => .error .terminal
    | some expected =>
      if handoff.capability.seat ≠ expected then .error .wrongSeat
      else if seatById? config.raw.roster handoff.capability.seat.id ≠
          some handoff.capability.seat then .error .capabilityMismatch
      else if handoff.briefing.seat ≠ handoff.capability.seat then .error .briefingMismatch
      else if handoff.body.session ≠ config.raw.sessionDigest then .error .wrongSession
      else if handoff.body.sequence ≠ state.snapshot.sequence then .error .staleSequence
      else if handoff.body.preRoot ≠ state.root then .error .staleRoot
      else if handoff.body.seat ≠ handoff.capability.seat then .error .bodySeatMismatch
      else match briefingBySeat? config.briefings handoff.capability.seat.id with
        | none => .error .briefingMismatch
        | some assignment =>
          if handoff.briefing.observation ≠ assignment.observation then
            .error .briefingMismatch
          else if handoff.body.observation ≠ handoff.briefing.observation then
            .error .observationMismatch
          else match counterFor? state.snapshot.counters handoff.capability.seat.id with
            | none => .error .invalidState
            | some previous =>
              if handoff.body.previousCounter ≠ previous ∨
                  handoff.body.counter ≠ previous + 1 then .error .counterMismatch
              else if PLAYER_COUNTER_MODULUS ≤ handoff.body.counter then
                .error .counterOutOfRange
              else if handoffSignatureValidB config handoff.capability.seat
                  handoff.body handoff.signature ≠ true then .error .signatureRefused
              else if decisionRoleExactB handoff.capability.seat.role
                  handoff.body.decision ≠ true then .error .roleWidening
              else if strategyCompatibleB state.snapshot.strategy
                  handoff.body.decision ≠ true then .error .strategyConflict
              else if handoff.capability.seat.role = .quartermaster &&
                  finalChoiceValidB state handoff.body.observation
                    handoff.body.decision ≠ true then .error .routeEvidenceRefused
              else if operationalCostAvailableB config state
                  handoff.body.decision ≠ true then .error .insufficientOperationalBudget
              else
                let successor := transition config state handoff
                if stateValidB config successor ≠ true then .error .invalidSuccessor
                else
                  let completion := completedRecord? config successor
                  if successor.snapshot.phase = .extracted && completion.isNone then
                    .error .outcomeRefused
                  else .ok ⟨successor, completion⟩

def signedHandoffFromTrace? (config : Config) (state : State)
    (trace : HandoffTrace) : Option (SignedHandoff config) := do
  let capability ← authenticateSeat? config trace.seat.id trace.seatSignature
  let briefing ← briefingFor? config capability
  let body ← expectedBody? config state capability briefing trace.decision
  let handoff : SignedHandoff config := ⟨capability, briefing, body, trace.signature⟩
  if traceOf handoff = trace then some handoff else none

def replayTrace (config : Config) : State → List HandoffTrace →
    Except Refusal (StepResult config)
  | state, [] => .ok ⟨state, completedRecord? config state⟩
  | state, trace :: traces => do
      let handoff ← match signedHandoffFromTrace? config state trace with
        | none => .error .signatureRefused
        | some handoff => .ok handoff
      let result ← execute config state handoff
      match traces with
      | [] => .ok result
      | _ => replayTrace config result.state traces

def CombinedFieldRecord.validB {config : Config}
    (record : CombinedFieldRecord config) : Bool :=
  match replayTrace config (initialState config) record.transcript with
  | .error _ => false
  | .ok result => match result.completion with
    | none => false
    | some replayed => decide (record.toRaw = replayed.toRaw)

/-- Opaque readmission witness.  A raw record is not upgraded to this type until
the entire signed transcript has rebuilt the byte-for-byte semantic record. -/
structure ReplayedFieldRecord (config : Config) where
  private mk ::
  record : CombinedFieldRecord config
  exactReplay : record.validB = true

/-- Unchecked field-record projections have no authority by themselves.
Readmission requires the original one-shot run admission and exact signed replay.
The deployment adapter must atomically consume the admission/session key. -/
def admitCombinedFieldRecord? {config : Config}
    (admission : CanonicalRunAdmission config) (raw : RawCombinedFieldRecord) :
    Option (ReplayedFieldRecord config) := do
  if raw.session ≠ admission.session then none
  match houtcome : ActivityOutcome.validate config.raw.policy raw.outcome with
  | none => none
  | some outcome =>
      if hfeatured : raw.featuredBeta ∈ outcome.betaCandidates then
        let record : CombinedFieldRecord config := ⟨raw.session, raw.route, raw.extraction,
          raw.strategy, raw.routeOperationalCost, raw.totalOperationalCost,
          raw.transcript, raw.finalCounters, raw.finalRoot, raw.outcome, outcome,
          houtcome, raw.featuredBeta, hfeatured⟩
        if hvalid : record.validB = true then some ⟨record, hvalid⟩ else none
      else none

/-! ## The run seal — the kernel's own replay, handed out as a value

A host does not hold a `Config`: its constructor is private and this module
publishes no producer, because a caller that could choose `signatureVerifier`
could choose `fun _ _ _ _ => true`.  That privacy is why the runtime above this
kernel could not call it, and why it reconstructed a terminal state by asserting
`phase := .extracted` instead.

`RunSeal` closes that without opening the constructor.  It packages an activated
`Config` with the one-shot admission issued against it, keeps both fields
private, and exposes exactly one operation: `admits`, which is
`admitCombinedFieldRecord?` and therefore drives `execute` over every handoff
from the private `initialState`.  A caller can pass a seal along and ask it about
a record.  It cannot read the verifier back out, substitute one, or fabricate a
seal for a session it was not issued for — `session` is derived from the sealed
`Config`, so a consumer can pin `runSeal.session` against its own activation and get
two independent sources for the same identity. -/
structure RunSeal where
  private mk ::
  private config : Config
  private admission : CanonicalRunAdmission config

/-- The sealed session.  Pin your own activation against this: a seal issued for
one mission then cannot judge another. -/
def RunSeal.session (runSeal : RunSeal) : SessionDigest := runSeal.config.raw.sessionDigest

/-- The sole replay predicate.  Not a caller-supplied function: it replays every
signed handoff through `execute` from the kernel's initial root and demands the
whole record back byte-for-byte. -/
def RunSeal.admits (runSeal : RunSeal) (raw : RawCombinedFieldRecord) : Bool :=
  (admitCombinedFieldRecord? runSeal.admission raw).isSome

/-- An accepted record carries the sealed session.  This is what lets a consumer
turn one seal into two independent sources for the same identity: it pins
`runSeal.session` against the session its own activation was authenticated for, and
a seal issued elsewhere then cannot judge this mission's records. -/
theorem RunSeal.admitted_record_carries_the_sealed_session (runSeal : RunSeal)
    (raw : RawCombinedFieldRecord) (accepted : runSeal.admits raw = true) :
    raw.session = runSeal.session := by
  by_contra different
  have mismatch : raw.session ≠ runSeal.admission.session := by
    rw [runSeal.admission.exactSession]
    exact different
  simp [RunSeal.admits, admitCombinedFieldRecord?, mismatch] at accepted

/-- The record the kernel **reached**, for a transcript of signed handoffs.

This is the difference between checking a claim and deriving a value.  `admits`
takes a record a caller wrote down and says yes or no; `replay?` is handed only
the signed transcript and returns what `execute` actually arrived at.  A consumer
built on this cannot fabricate a terminal state, because it never writes one
down: `replayTrace` drives `execute` from the private `initialState` over every
handoff, `completedRecord?` returns `none` unless the run genuinely reached
`.extracted`, and every field of the result — phase, sequence, counters,
remaining budget, route, extraction, outcome, featured artifact — is read off the
state the kernel computed.

A seal still holds no signing capability: a forged handoff fails
`signedHandoffFromTrace?` and the whole replay refuses. -/
def RunSeal.replay? (runSeal : RunSeal) (transcript : List HandoffTrace) :
    Option RawCombinedFieldRecord :=
  match replayTrace runSeal.config (initialState runSeal.config) transcript with
  | .error _ => none
  | .ok result => result.completion.map CombinedFieldRecord.toRaw

/-! ⚑ AN UNDISCHARGED LEMMA, NAMED RATHER THAN FAKED.

`RunSeal.replayed_record_carries_the_sealed_session` — "a record returned by
`replay?` carries the sealed session" — is TRUE by construction
(`completedRecord?` stamps `config.raw.sessionDigest`) and is NOT PROVED here.
Two attempts at the supporting lemmas
(`completedRecord?` stamps the session; every `StepResult` carries the
completion of its own state) left unsolved goals against the `Option.bind`
chain, and it is not worth a proof written faster than it can be checked.

It is stated here and nowhere claimed, rather than replaced by a `native_decide`
on the fixture — one instance standing in for a general fact is the sin this
tree keeps finding.

⚠ Nothing depends on it.  The weld's pin is
`CrewFieldMissionRuntime.Activation.sealSessionExact`, a decidable equality
checked at activation time between the seal's session and the authored field
session; and the analogous fact for `admits` IS proved, immediately above, as
`RunSeal.admitted_record_carries_the_sealed_session`.
-/

/-! ## The per-handoff step surface — what the NEXT seat has to sign

`replay?` answers only about a COMPLETE run: `completedRecord?` returns `none`
until the mission reaches `.extracted`, so a seat asked to produce the SECOND
handoff can learn nothing from it.  And what that seat needs is not a record.
It is `preRoot` — the exact `StateRoot` `execute` compares its body against, on
pain of `.staleRoot` — inside the exact canonical preimage bytes its key signs.
Neither was reachable, so a signing client could only obtain them by
REIMPLEMENTING the kernel's transition beside it.

This cone has paid for that once already: the runtime above this kernel
reconstructed a terminal state by ASSERTING `phase := .extracted`, and the weld
of 2026-08-06 deleted it.  A signing client that computes its own `preRoot` is
the same twin one layer further out — and it would be the worse one, because it
would be written by whoever holds the keys.

`step?` is that same replay, stopped wherever the transcript stops.  Nothing
here is asserted: `replayTrace` drives `execute` from the private `initialState`
over the prefix and every field below is READ OFF the state the kernel computed.
The view carries no authority — it verifies nothing, signs nothing, settles
nothing, and a caller who could fabricate one would gain nothing, because
`execute` recomputes the root it compares against and the signature is over the
body.  What makes it more than a convenience is
`step_view_next_body_is_the_kernel_expected_body` below: at a seat's turn, the
body this surface hands out **is** `expectedBody?`, the one
`signedHandoffFromTrace?` reconstructs and `execute` demands. -/

/-- The state a prefix of signed handoffs REACHED, plus what the next signer
needs to address its handoff at it.  The constructor is private: only
`RunSeal.step?` produces one, so a view is always something the kernel replayed
rather than something a caller wrote down. -/
structure StepView where
  private mk ::
  /-- The sealed session, same value `RunSeal.session` exposes. -/
  session : SessionDigest
  sequence : Nat
  phase : MissionPhase
  /-- ⚑ The point of the surface: the root the next `HandoffBody.preRoot` must
  equal exactly, or `execute` answers `.staleRoot`. -/
  reachedRoot : StateRoot
  counters : List SeatCounter
  strategy : Option Strategy
  operationalBudgetRemaining : Nat
  /-- The seat whose turn it is; `none` once the roster is exhausted. -/
  nextSeat : Option Seat
  /-- That seat's counter as the kernel holds it now.  Its handoff must carry
  `previousCounter` equal to this and `counter` one higher. -/
  nextPreviousCounter : Option Nat
  /-- The completed record, present exactly when the run genuinely reached
  `.extracted` — the same value `replay?` returns, proved below. -/
  completion : Option RawCombinedFieldRecord
deriving DecidableEq

private def stepViewAt (config : Config) (state : State)
    (completion : Option (CombinedFieldRecord config)) : StepView :=
  let seat? := config.raw.roster[state.snapshot.nextSeat]?
  { session := config.raw.sessionDigest
    sequence := state.snapshot.sequence
    phase := state.snapshot.phase
    reachedRoot := state.root
    counters := state.snapshot.counters
    strategy := state.snapshot.strategy
    operationalBudgetRemaining := state.snapshot.operationalBudgetRemaining
    nextSeat := seat?
    nextPreviousCounter := seat?.bind fun seat => counterFor? state.snapshot.counters seat.id
    completion := completion.map CombinedFieldRecord.toRaw }

/-- The kernel's own answer for a PREFIX of signed handoffs.  Identical
machinery to `replay?` — `replayTrace` from the private `initialState` — read at
the point the transcript ends instead of only at the end of a completed run. -/
def RunSeal.step? (runSeal : RunSeal) (transcript : List HandoffTrace) : Option StepView :=
  match replayTrace runSeal.config (initialState runSeal.config) transcript with
  | .error _ => none
  | .ok result => some (stepViewAt runSeal.config result.state result.completion)

/-- The new surface is not a second answer.  Where `replay?` speaks at all, the
step view says the same thing; where it is silent, so is the view's completion.
Without this the two could drift and a host could settle on one while showing
the other. -/
theorem RunSeal.step_completion_is_the_replayed_record (runSeal : RunSeal)
    (transcript : List HandoffTrace) :
    (runSeal.step? transcript).bind StepView.completion = runSeal.replay? transcript := by
  unfold RunSeal.step? RunSeal.replay?
  cases replayed : replayTrace runSeal.config (initialState runSeal.config) transcript with
  | error _ => simp
  | ok result => simp [stepViewAt]

/-- The handoff body the next seat must address at this view.  A client fills in
only its decision; session, sequence, `preRoot`, seat and both counters come
from the state the kernel reached. -/
def StepView.nextBody? (view : StepView) (observation : PrivateObservation)
    (decision : Decision) : Option HandoffBody := do
  let seat ← view.nextSeat
  let previousCounter ← view.nextPreviousCounter
  some {
    session := view.session
    sequence := view.sequence
    preRoot := view.reachedRoot
    seat
    previousCounter
    counter := previousCounter + 1
    observation
    decision
  }

/-- ⚑ THE REASON THIS IS A SURFACE AND NOT A MIRROR.  At the seat whose turn it
is — `turn` is exactly the condition `execute` enforces as `.wrongSeat` — the
body the step view hands out is *definitionally* `expectedBody?`, the body
`signedHandoffFromTrace?` reconstructs and `execute` compares against.  A client
that signs what this surface returns cannot be signing something the kernel will
not recognise, and the two cannot drift apart later without this going red. -/
theorem step_view_next_body_is_the_kernel_expected_body (config : Config) (state : State)
    (completion : Option (CombinedFieldRecord config))
    (capability : SeatCapability config) (briefing : Briefing config) (decision : Decision)
    (turn : config.raw.roster[state.snapshot.nextSeat]? = some capability.seat) :
    (stepViewAt config state completion).nextBody? briefing.observation decision
      = expectedBody? config state capability briefing decision := by
  simp [stepViewAt, StepView.nextBody?, expectedBody?, turn]

/-- ⚑ THE AUTHENTICATED HALF.  A briefing observation reaches the wire only when
its seat copies it into a signed body, so a surface that handed the NEXT seat's
body to anyone who asked would publish it early.  This one opens nothing until
the caller presents that seat's admission signature and `authenticateSeat?`
accepts it — the same ML-DSA-65 envelope, verified by the same activated
verifier, that mints a `SeatCapability`.

⚠ The honest limit: a seat-admission signature is a bearer value, not a
challenge-response, so this gate is "first use".  It holds where it matters —
a seat that has not yet played has never published its admission envelope, since
a trace carries it only once the seat has acted — and after that seat has acted
its observation is already public in its own trace, so there is nothing left to
leak.  It is not a defence against a party that has already seen the seat's
handoff, and nothing here claims one.

The result is the exact `HandoffSigningPreimage`: hand it to
`ProductionSigning.handoffPreimageMessage` for the byte string, sign THOSE bytes
under `HANDOFF_SIGNING_CONTEXT`, and the trace built from this body and that
signature is one `execute` accepts. -/
def RunSeal.nextSigningPreimage? (runSeal : RunSeal) (transcript : List HandoffTrace)
    (seatSignature : SeatSignature) (decision : Decision) :
    Option HandoffSigningPreimage :=
  match replayTrace runSeal.config (initialState runSeal.config) transcript with
  | .error _ => none
  | .ok result => do
      let expected ← runSeal.config.raw.roster[result.state.snapshot.nextSeat]?
      let capability ← authenticateSeat? runSeal.config expected.id seatSignature
      let briefing ← briefingFor? runSeal.config capability
      let body ← expectedBody? runSeal.config result.state capability briefing decision
      some (body.signingPreimage runSeal.config.raw.messageDigestSuiteId
        runSeal.config.raw.signingSuiteId)

theorem execute_deterministic (config : Config) (state : State)
    (handoff : SignedHandoff config) {left right : StepResult config}
    (hl : execute config state handoff = .ok left)
    (hr : execute config state handoff = .ok right) : left = right := by
  rw [hl] at hr
  exact Except.ok.inj hr

/-- The canonical semantic preimage itself loses no handoff field.  Only the
deployment digest from that preimage remains a cryptographic trust boundary. -/
theorem handoff_signing_preimage_injective
    (messageDigestSuiteId signatureSuiteId : Digest32) :
    Function.Injective
      (HandoffBody.signingPreimage messageDigestSuiteId signatureSuiteId) := by
  intro left right h
  exact congrArg HandoffSigningPreimage.body h

theorem seat_signing_preimage_injective
    (messageDigestSuiteId signatureSuiteId : Digest32) :
    Function.Injective
      (SeatAdmissionBody.signingPreimage messageDigestSuiteId signatureSuiteId) := by
  intro left right h
  exact congrArg SeatSigningPreimage.body h

theorem completed_featured_artifact_is_beta_candidate {config : Config}
    (record : CombinedFieldRecord config) :
    record.featuredBeta ∈ record.outcome.betaCandidates :=
  record.featuredDeclared

/-! ## Executable cooperative fixture -/

def digestFilled (value : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨value % 256, Nat.mod_lt _ (by omega)⟩
  length_eq := by simp

private def signatureBytesPattern (value : Nat) : SignatureBytes where
  bytes :=
    List.replicate (SIGNATURE_BYTE_LENGTH - 32) ⟨value % 256, Nat.mod_lt _ (by omega)⟩ ++
    List.replicate 32 ⟨(value + 1) % 256, Nat.mod_lt _ (by omega)⟩
  length_eq := by
    simp only [List.length_append, List.length_replicate]
    decide

def fixtureBriefings : List BriefingAssignment :=
  [ ⟨⟨0⟩, .pathfinder .signalGallery⟩
  , ⟨⟨1⟩, .engineer .signalGallery⟩
  , ⟨⟨2⟩, .containment .signalGallery⟩
  , ⟨⟨3⟩, .quartermaster .stable⟩ ]

private def digestCode (digest : Digest32) : Nat :=
  (digest.bytes.map Fin.val).sum

private def listCode {α : Type} (code : α → Nat) : List α → Nat
  | [] => 0
  | value :: values => code value + 257 * listCode code values

private def artifactCode (artifact : ArtifactRef) : Nat :=
  artifact.missionId.value + 17 * artifact.artifactId.value +
    31 * digestCode artifact.sourceDigest + 43 * digestCode artifact.contentDigest

private def rawContributionCode (raw : RawContribution) : Nat :=
  raw.intel + 17 * raw.supplies + 31 * raw.cohesion + 43 * raw.influence +
    59 * raw.score + 71 * listCode RelicId.value raw.relics

private def outcomeCode (raw : ActivityOutcome.Raw) : Nat :=
  rawContributionCode raw.contribution +
    97 * listCode artifactCode raw.betaCandidates

private def seatCode (seat : Seat) : Nat :=
  seat.id.value + 11 * digestCode seat.playerKey + 17 * seat.credential.value +
    23 * (match seat.role with
      | .pathfinder => 0 | .engineer => 1 | .containment => 2 | .quartermaster => 3) +
    29 * seat.initialCounter

private def routeOutcomeCode (spec : RouteOutcomeSpec) : Nat :=
  spec.route.code + 7 * (match spec.extraction with
    | .returnNow => 0 | .descendFurther => 1) +
    13 * spec.operationalCost + 19 * artifactCode spec.featuredArtifact +
    31 * outcomeCode spec.outcome

private def sessionCode (session : SessionDigest) : Nat :=
  digestCode session.federationId + 3 * digestCode session.contentSession +
    5 * session.missionEpoch.value + 7 * session.missionId.value +
    11 * digestCode session.relayId + 13 * digestCode session.briefingHashSuiteId +
    17 * digestCode session.briefingCommitment +
    19 * digestCode session.messageDigestSuiteId +
    23 * digestCode session.signingSuiteId + 29 * listCode seatCode session.roster +
    31 * session.operationalBudget + 37 * listCode routeOutcomeCode session.routeOutcomes

private def seatCounterCode (counter : SeatCounter) : Nat :=
  counter.seat.value + 17 * counter.counter

private def signatureBytesCode (signature : SignatureBytes) : Nat :=
  (signature.bytes.map Fin.val).sum

private def traceCode (trace : HandoffTrace) : Nat :=
  trace.sequence + 3 * seatCode trace.seat + 5 * trace.previousCounter +
    7 * trace.counter + 11 * trace.observation.code + 13 * trace.decision.code +
    17 * signatureBytesCode trace.seatSignature.bytes +
    19 * signatureBytesCode trace.signature.bytes

private def snapshotCode (snapshot : StateSnapshot) : Nat :=
  (match snapshot.phase with | .active => 0 | .extracted => 1) +
    3 * snapshot.sequence + 5 * snapshot.nextSeat +
    7 * listCode seatCounterCode snapshot.counters +
    11 * (match snapshot.strategy with
      | none => 0 | some .survey => 1 | some .salvage => 2) +
    13 * snapshot.operationalBudgetRemaining +
    17 * listCode traceCode snapshot.transcript

private def stateRootCode (root : StateRoot) : Nat :=
  sessionCode root.session + 101 * snapshotCode root.snapshot

private def briefingPreimageCode (preimage : BriefingDeckPreimage) : Nat :=
  digestCode preimage.federationId + 3 * digestCode preimage.contentSession +
    5 * preimage.missionEpoch.value + 7 * preimage.missionId.value +
    11 * digestCode preimage.relayId + 13 * listCode seatCode preimage.roster +
    17 * listCode (fun briefing =>
      briefing.seat.value + 19 * briefing.observation.code) preimage.orderedBriefings

private def seatPreimageCode (preimage : SeatSigningPreimage) : Nat :=
  preimage.formatVersion + 3 * digestCode preimage.messageDigestSuiteId +
    5 * digestCode preimage.signatureSuiteId +
    7 * sessionCode preimage.body.session + 11 * seatCode preimage.body.seat

private def handoffPreimageCode (preimage : HandoffSigningPreimage) : Nat :=
  preimage.formatVersion + 3 * digestCode preimage.messageDigestSuiteId +
    5 * digestCode preimage.signatureSuiteId +
    7 * sessionCode preimage.body.session + 11 * preimage.body.sequence +
    13 * stateRootCode preimage.body.preRoot + 17 * seatCode preimage.body.seat +
    19 * preimage.body.previousCounter + 23 * preimage.body.counter +
    29 * preimage.body.observation.code + 31 * preimage.body.decision.code

private def fixtureBriefingDigest : BriefingDigestBoundary where
  id := digestFilled 190
  digest preimage := digestFilled (briefingPreimageCode preimage)

private def fixtureMessageDigestSuiteId : Digest32 := digestFilled 191

private def fixtureSignatureSuiteId : Digest32 := digestFilled 192

private def fixtureMessageDigest : SigningMessageDigestBoundary where
  id := fixtureMessageDigestSuiteId
  seatMessageDigest preimage := digestFilled (seatPreimageCode preimage)
  handoffMessageDigest preimage := digestFilled (handoffPreimageCode preimage)

/-! This deterministic verifier is fixture-only.  Production activation
(`ProductionSigning.activate?` below) replaces it with the ML-DSA-65 verifier
over the canonical signing-preimage bytes; the kernel supplies the full
semantic preimage and exact fixed-length signature envelope in both suites. -/
private def fixtureExpectedSignature (domain : Nat) (playerKey : Digest32)
    (credential : CredentialId) (messageDigest : Digest32) : SignatureBytes :=
  signatureBytesPattern
    (domain + 3 * (digestCode playerKey / 32) + 5 * credential.value +
      7 * (digestCode messageDigest / 32) + 104729)

private def fixtureSignatureVerifier : ActivatedSignatureVerifier where
  id := fixtureSignatureSuiteId
  verifySeat playerKey credential preimage signature :=
    decide (preimage.formatVersion = SIGNING_FORMAT_VERSION) &&
    decide (preimage.messageDigestSuiteId = fixtureMessageDigestSuiteId) &&
    decide (preimage.signatureSuiteId = fixtureSignatureSuiteId) &&
    decide (signature = fixtureExpectedSignature 1 playerKey credential
      (fixtureMessageDigest.seatMessageDigest preimage))
  verifyHandoff playerKey credential preimage signature :=
    decide (preimage.formatVersion = SIGNING_FORMAT_VERSION) &&
    decide (preimage.messageDigestSuiteId = fixtureMessageDigestSuiteId) &&
    decide (preimage.signatureSuiteId = fixtureSignatureSuiteId) &&
    decide (signature = fixtureExpectedSignature 2 playerKey credential
      (fixtureMessageDigest.handoffMessageDigest preimage))

def fixtureMaintenanceArtifact : ArtifactRef := {
  DeckExpedition.fixtureArtifact with
  artifactId := ⟨813⟩
  contentDigest := digestFilled 201 }

def fixtureSignalArtifact : ArtifactRef := DeckExpedition.fixtureArtifact

def fixtureNaveArtifact : ArtifactRef := {
  DeckExpedition.fixtureArtifact with
  artifactId := ⟨814⟩
  contentDigest := digestFilled 202 }

def fixturePolicy : ActivityOutcome.Policy where
  mission := DeckExpedition.fixtureMission
  allowedBeta := {fixtureMaintenanceArtifact, fixtureSignalArtifact, fixtureNaveArtifact}
  resultLimit := ⟨1, by decide⟩
  catalogue_bounded := by native_decide

def wrongMissionArtifact : ArtifactRef := {
  fixtureMaintenanceArtifact with missionId := ⟨7002⟩ }

def wrongArtifactPolicy : ActivityOutcome.Policy where
  mission := DeckExpedition.fixtureMission
  allowedBeta := {fixtureMaintenanceArtifact, fixtureSignalArtifact,
    fixtureNaveArtifact, wrongMissionArtifact}
  resultLimit := ⟨1, by decide⟩
  catalogue_bounded := by native_decide

def fixtureOutcome (route : Route) (extraction : ExtractionChoice) :
    ActivityOutcome.Raw where
  contribution := match route, extraction with
    | .maintenanceSpine, .returnNow => ⟨2, 4, 4, 0, 18, []⟩
    | .maintenanceSpine, .descendFurther =>
        ⟨3, 2, 3, 0, 48, [DeckExpedition.fixtureRelic]⟩
    | .signalGallery, .returnNow => ⟨6, 2, 3, 0, 25, []⟩
    | .signalGallery, .descendFurther =>
        ⟨8, 0, 2, 0, 62, [DeckExpedition.fixtureRelic]⟩
    | .sealedNave, .returnNow => ⟨4, 1, 6, 0, 31, []⟩
    | .sealedNave, .descendFurther =>
        ⟨5, 0, 5, 0, 79, [DeckExpedition.fixtureRelic]⟩
  betaCandidates := [match route with
    | .maintenanceSpine => fixtureMaintenanceArtifact
    | .signalGallery => fixtureSignalArtifact
    | .sealedNave => fixtureNaveArtifact]

def wrongMissionOutcome : ActivityOutcome.Raw := {
  fixtureOutcome .maintenanceSpine .returnNow with
  betaCandidates := [wrongMissionArtifact] }

def fixtureRouteOutcomes : List RouteOutcomeSpec :=
  [ ⟨.maintenanceSpine, .returnNow, 2, fixtureMaintenanceArtifact,
      fixtureOutcome .maintenanceSpine .returnNow⟩
  , ⟨.maintenanceSpine, .descendFurther, 5, fixtureMaintenanceArtifact,
      fixtureOutcome .maintenanceSpine .descendFurther⟩
  , ⟨.signalGallery, .returnNow, 3, fixtureSignalArtifact,
      fixtureOutcome .signalGallery .returnNow⟩
  , ⟨.signalGallery, .descendFurther, 7, fixtureSignalArtifact,
      fixtureOutcome .signalGallery .descendFurther⟩
  , ⟨.sealedNave, .returnNow, 11, fixtureNaveArtifact,
      fixtureOutcome .sealedNave .returnNow⟩
  , ⟨.sealedNave, .descendFurther, 12, fixtureNaveArtifact,
      fixtureOutcome .sealedNave .descendFurther⟩ ]

/-- Every terminal cost is individually within budget three, but mandatory
specialist play spends all three units before the quartermaster can act. -/
def globallyUnwinnableRouteOutcomes : List RouteOutcomeSpec :=
  [ ⟨.maintenanceSpine, .returnNow, 1, fixtureMaintenanceArtifact,
      fixtureOutcome .maintenanceSpine .returnNow⟩
  , ⟨.maintenanceSpine, .descendFurther, 1, fixtureMaintenanceArtifact,
      fixtureOutcome .maintenanceSpine .descendFurther⟩
  , ⟨.signalGallery, .returnNow, 2, fixtureSignalArtifact,
      fixtureOutcome .signalGallery .returnNow⟩
  , ⟨.signalGallery, .descendFurther, 2, fixtureSignalArtifact,
      fixtureOutcome .signalGallery .descendFurther⟩
  , ⟨.sealedNave, .returnNow, 3, fixtureNaveArtifact,
      fixtureOutcome .sealedNave .returnNow⟩
  , ⟨.sealedNave, .descendFurther, 3, fixtureNaveArtifact,
      fixtureOutcome .sealedNave .descendFurther⟩ ]

def wrongArtifactRouteOutcomes : List RouteOutcomeSpec :=
  [ ⟨.maintenanceSpine, .returnNow, 2, wrongMissionArtifact,
      wrongMissionOutcome⟩
  , ⟨.maintenanceSpine, .descendFurther, 5, fixtureMaintenanceArtifact,
      fixtureOutcome .maintenanceSpine .descendFurther⟩
  , ⟨.signalGallery, .returnNow, 3, fixtureSignalArtifact,
      fixtureOutcome .signalGallery .returnNow⟩
  , ⟨.signalGallery, .descendFurther, 7, fixtureSignalArtifact,
      fixtureOutcome .signalGallery .descendFurther⟩
  , ⟨.sealedNave, .returnNow, 11, fixtureNaveArtifact,
      fixtureOutcome .sealedNave .returnNow⟩
  , ⟨.sealedNave, .descendFurther, 12, fixtureNaveArtifact,
      fixtureOutcome .sealedNave .descendFurther⟩ ]

private def fixtureRawConfigBase : RawConfig where
  federationId := DeckExpedition.fixtureMission.federationId
  contentSession := DeckExpedition.fixtureMission.contentSession
  missionEpoch := DeckExpedition.fixtureMission.epoch
  missionId := DeckExpedition.fixtureMission.missionId
  relayId := digestFilled 182
  briefingPrivacy := .trustedDealerOperatorVisibleThenPublicHandoff
  briefingHashSuiteId := fixtureBriefingDigest.id
  briefingCommitment := digestFilled 0
  messageDigestSuiteId := fixtureMessageDigest.id
  signingSuiteId := fixtureSignatureVerifier.id
  roster := fixtureRoster
  policy := fixturePolicy
  operationalBudget := 13
  routeOutcomes := fixtureRouteOutcomes

private def withFixtureBriefingCommitment (raw : RawConfig) : RawConfig := {
  raw with
  briefingCommitment := fixtureBriefingDigest.digest
    (briefingDeckPreimage raw fixtureBriefings) }

def fixtureRawConfig : RawConfig :=
  withFixtureBriefingCommitment fixtureRawConfigBase

def globallyUnwinnableRawConfig : RawConfig :=
  withFixtureBriefingCommitment {
    fixtureRawConfigBase with
    operationalBudget := 3
    routeOutcomes := globallyUnwinnableRouteOutcomes }

theorem fixture_config_valid :
    rawConfigValidB fixtureRawConfig fixtureBriefings fixtureBriefingDigest = true := by
  native_decide

theorem fixture_ordered_briefing_deck_is_commitment_bound :
    fixtureRawConfig.briefingCommitment = fixtureBriefingDigest.digest
      (briefingDeckPreimage fixtureRawConfig fixtureBriefings) := by
  native_decide

theorem hostile_unwinnable_terminal_costs_are_individually_within_budget :
    globallyUnwinnableRouteOutcomes.all (fun spec =>
      decide (0 < spec.operationalCost ∧
        spec.operationalCost ≤ globallyUnwinnableRawConfig.operationalBudget)) = true := by
  native_decide

theorem hostile_unwinnable_config_has_no_affordable_safe_terminal :
    authoredSafeTerminalReachabilityFloorB globallyUnwinnableRawConfig = false := by
  native_decide

theorem hostile_globally_unwinnable_config_refused_at_activation :
    rawConfigValidB globallyUnwinnableRawConfig fixtureBriefings
      fixtureBriefingDigest = false := by
  native_decide

def missionIdentityMutationsRefusedB : Bool :=
  let mutations : List RawConfig :=
    [ { fixtureRawConfigBase with federationId := digestFilled 241 }
    , { fixtureRawConfigBase with contentSession := digestFilled 242 }
    , { fixtureRawConfigBase with missionEpoch := ⟨243⟩ }
    , { fixtureRawConfigBase with missionId := ⟨244⟩ } ]
  mutations.all fun raw =>
    !(rawConfigValidB (withFixtureBriefingCommitment raw) fixtureBriefings
      fixtureBriefingDigest)

theorem raw_identity_fields_must_exactly_match_policy_mission :
    missionIdentityMutationsRefusedB = true := by
  native_decide

def wrongMissionArtifactRawConfig : RawConfig :=
  withFixtureBriefingCommitment {
    fixtureRawConfigBase with
    policy := wrongArtifactPolicy
    routeOutcomes := wrongArtifactRouteOutcomes }

theorem wrong_mission_artifact_is_otherwise_declared_and_outcome_valid :
    (ActivityOutcome.validate wrongArtifactPolicy wrongMissionOutcome).isSome = true ∧
      wrongMissionArtifact ∈ wrongMissionOutcome.betaCandidates := by
  native_decide

theorem artifact_mission_must_exactly_match_activated_mission :
    rawConfigValidB wrongMissionArtifactRawConfig fixtureBriefings
      fixtureBriefingDigest = false := by
  native_decide

def substitutedFixtureBriefings : List BriefingAssignment :=
  [ ⟨⟨0⟩, .pathfinder .sealedNave⟩
  , ⟨⟨1⟩, .engineer .signalGallery⟩
  , ⟨⟨2⟩, .containment .signalGallery⟩
  , ⟨⟨3⟩, .quartermaster .stable⟩ ]

theorem hostile_same_role_briefing_substitution_breaks_activation_commitment :
    rawConfigValidB fixtureRawConfig substitutedFixtureBriefings
      fixtureBriefingDigest = false := by
  native_decide

private def fixtureConfig : Config where
  raw := fixtureRawConfig
  briefings := fixtureBriefings
  briefingDigest := fixtureBriefingDigest
  messageDigest := fixtureMessageDigest
  signatureVerifier := fixtureSignatureVerifier
  valid := fixture_config_valid
  messageDigestSuiteExact := rfl
  signingSuiteExact := rfl

private def fixtureAdmission : CanonicalRunAdmission fixtureConfig :=
  ⟨fixtureConfig.raw.sessionDigest, rfl⟩

private def testCapability? (id : SeatId) : Option (SeatCapability fixtureConfig) := do
  let seat ← seatById? fixtureConfig.raw.roster id
  let body := expectedAdmission fixtureConfig seat
  let signature : SeatSignature := {
    bytes := fixtureExpectedSignature 1 seat.playerKey seat.credential
      (fixtureMessageDigest.seatMessageDigest
        (body.signingPreimage fixtureConfig.raw.messageDigestSuiteId
          fixtureConfig.raw.signingSuiteId)) }
  authenticateSeat? fixtureConfig id signature

private def testHandoff? (state : State) (id : SeatId) (decision : Decision) :
    Option (SignedHandoff fixtureConfig) := do
  let capability ← testCapability? id
  let briefing ← briefingFor? fixtureConfig capability
  let body ← expectedBody? fixtureConfig state capability briefing decision
  let signature : HandoffSignature := {
    bytes := fixtureExpectedSignature 2 capability.seat.playerKey
      capability.seat.credential (fixtureMessageDigest.handoffMessageDigest
        (body.signingPreimage fixtureConfig.raw.messageDigestSuiteId
          fixtureConfig.raw.signingSuiteId)) }
  some ⟨capability, briefing, body, signature⟩

private def drive : State → List (SeatId × Decision) →
    Option (StepResult fixtureConfig)
  | state, [] => some ⟨state, completedRecord? fixtureConfig state⟩
  | state, (id, decision) :: decisions => do
      let handoff ← testHandoff? state id decision
      match execute fixtureConfig state handoff with
      | .error _ => none
      | .ok result =>
          match decisions with
          | [] => some result
          | _ => drive result.state decisions

def safePlan : List (SeatId × Decision) :=
  [ (⟨0⟩, .specialist .signalGallery .chartPressureRoute)
  , (⟨1⟩, .specialist .signalGallery .braceTransit)
  , (⟨2⟩, .specialist .sealedNave .quietAnomaly)
  , (⟨3⟩, .finalize .signalGallery .returnNow .bankSupplies) ]

def safeMaintenancePlan : List (SeatId × Decision) :=
  [ (⟨0⟩, .specialist .maintenanceSpine .chartPressureRoute)
  , (⟨1⟩, .specialist .maintenanceSpine .braceTransit)
  , (⟨2⟩, .specialist .signalGallery .quietAnomaly)
  , (⟨3⟩, .finalize .maintenanceSpine .returnNow .bankSupplies) ]

def deepPlan : List (SeatId × Decision) :=
  [ (⟨0⟩, .specialist .signalGallery .markSalvageRoute)
  , (⟨1⟩, .specialist .signalGallery .overdriveCargoLift)
  , (⟨2⟩, .specialist .signalGallery .screenRecovery)
  , (⟨3⟩, .finalize .signalGallery .descendFurther .secureCache) ]

private def completionFor? (plan : List (SeatId × Decision)) :
    Option (CombinedFieldRecord fixtureConfig) := do
  let result ← drive (start fixtureAdmission) plan
  result.completion

/-! ### The sealed fixture run

⚠ Fixture-only, and deliberately public: `CrewFieldMissionRuntime` is welded to
this kernel and its activation fixture must hold a real seal to exercise the
weld.  A seal can only *verify*; it holds no signing capability, and its
`session` is the fixture session, so an activation for any other mission refuses
it (`Activation.sealSessionExact`).  Production activation issues its own seal
over a cryptographic verifier; this one is the non-cryptographic fixture suite
and must never reach a deployment. -/
def fixtureRunSeal : RunSeal := ⟨fixtureConfig, fixtureAdmission⟩

/-! ### A second sealed world — the rekeyed crew

`CrewFieldMissionRuntime` demonstrates that its durable key separates two crews
that share one authored `activation_id`, and it needs an activation for the
substituted crew to do it.  Since the weld, that activation needs a SEAL, and a
seal can be minted only here.

⚑ Note WHY it needs a whole second world rather than the fixture seal pointed at
a different roster: a `RunSeal` carries a `Config`, a `Config` determines the
session, and the session CONTAINS the roster.  There is no way to move a seal
onto another crew, which is the property the runtime relies on.

⚠ And note what does NOT do this work.  `briefingDeckPreimage` includes
`raw.roster`, so it is tempting to say the briefing commitment binds the crew.
It does not bind it HERE: the fixture digest is
`digestFilled (briefingPreimageCode preimage % 256)` — eight bits — and the two
rosters collide under it, so the substituted roster carrying the AUTHORED
commitment still passes `rawConfigValidB`.  A first draft of this comment
asserted the opposite as a theorem and `native_decide` refuted it.  The refusal
downstream comes from the seal, not from the commitment. -/
def fixtureRekeyedRoster : List Seat :=
  fixtureRoster.map fun seat =>
    { seat with playerKey := digestFilled (200 + seat.id.value) }

def fixtureRekeyedRawConfig : RawConfig :=
  withFixtureBriefingCommitment { fixtureRawConfigBase with roster := fixtureRekeyedRoster }

theorem fixture_rekeyed_config_valid :
    rawConfigValidB fixtureRekeyedRawConfig fixtureBriefings fixtureBriefingDigest = true := by
  native_decide

/-- The substitution moved the wallet keys and nothing else about who the crew
is.  Asserted here, next to the world it describes, so the world cannot quietly
become a copy of the authored one. -/
theorem fixture_rekeyed_roster_substitutes_only_the_player_keys :
    fixtureRekeyedRoster.map Seat.playerKey ≠ fixtureRoster.map Seat.playerKey ∧
    fixtureRekeyedRoster.map Seat.id = fixtureRoster.map Seat.id ∧
    fixtureRekeyedRoster.map Seat.role = fixtureRoster.map Seat.role ∧
    fixtureRekeyedRoster.map Seat.credential = fixtureRoster.map Seat.credential ∧
    fixtureRekeyedRoster.map Seat.initialCounter = fixtureRoster.map Seat.initialCounter := by
  native_decide

/-- ⚑ The fixture briefing commitment does NOT separate these two crews: the
substituted roster carrying the authored commitment is still a valid config.
Recorded as a theorem because it is the reason the seal has to be what refuses,
and because the opposite was asserted here first and was false.  This is a fact
about the eight-bit fixture digest, not about the design: a deployment digest
would separate them. -/
theorem the_fixture_briefing_commitment_does_not_separate_the_two_crews :
    rawConfigValidB { fixtureRawConfig with roster := fixtureRekeyedRoster }
      fixtureBriefings fixtureBriefingDigest = true := by
  native_decide

private def fixtureRekeyedConfig : Config where
  raw := fixtureRekeyedRawConfig
  briefings := fixtureBriefings
  briefingDigest := fixtureBriefingDigest
  messageDigest := fixtureMessageDigest
  signatureVerifier := fixtureSignatureVerifier
  valid := fixture_rekeyed_config_valid
  messageDigestSuiteExact := rfl
  signingSuiteExact := rfl

private def fixtureRekeyedAdmission : CanonicalRunAdmission fixtureRekeyedConfig :=
  ⟨fixtureRekeyedConfig.raw.sessionDigest, rfl⟩

def fixtureRekeyedRunSeal : RunSeal := ⟨fixtureRekeyedConfig, fixtureRekeyedAdmission⟩

/-- The two seals are for different sessions.  Without this the runtime's
cross-crew refusals could be comparing a world with itself. -/
theorem the_two_fixture_seals_carry_different_sessions :
    fixtureRekeyedRunSeal.session ≠ fixtureRunSeal.session := by native_decide

/-- The traces the kernel actually signed, exported as data rather than as a
signing oracle.  `CrewFieldMissionRuntime` builds its wire transcripts from
these, so a change to the kernel's signing preimage moves the runtime fixtures
with it instead of leaving them asserting against a stale constant. -/
def fixtureSafeMaintenanceTranscript : List HandoffTrace :=
  ((completionFor? safeMaintenancePlan).map CombinedFieldRecord.transcript).getD []

def fixtureDeepTranscript : List HandoffTrace :=
  ((completionFor? deepPlan).map CombinedFieldRecord.transcript).getD []

theorem exported_fixture_transcripts_are_four_signed_handoffs_each :
    fixtureSafeMaintenanceTranscript.length = CREW_SIZE ∧
      fixtureDeepTranscript.length = CREW_SIZE := by native_decide

/-! ### The step surface, over a real signed transcript

Three claims, each with its own failure mode:

1. the gap this closes is REAL — `replay?` is silent at every proper prefix
   while `step?` answers at all five of them, with a sequence and a root that
   MOVE (a surface that reported one constant root would satisfy every "is it
   `some`" test and be useless);
2. a client holding only the public surface can play a whole run one signed
   handoff at a time, and what it produces is byte-identical to the transcript
   the kernel itself signed;
3. the surface refuses to open a seat's briefing to anyone but that seat. -/

private def fixtureSeatSignature (seat : Seat) : SeatSignature :=
  { bytes := fixtureExpectedSignature 1 seat.playerKey seat.credential
      (fixtureMessageDigest.seatMessageDigest
        ((expectedAdmission fixtureConfig seat).signingPreimage
          fixtureConfig.raw.messageDigestSuiteId fixtureConfig.raw.signingSuiteId)) }

private def fixtureHandoffSignatureFor (seat : Seat) (preimage : HandoffSigningPreimage) :
    HandoffSignature :=
  { bytes := fixtureExpectedSignature 2 seat.playerKey seat.credential
      (fixtureMessageDigest.handoffMessageDigest preimage) }

def stepAnswersEveryPrefixWhileReplayIsSilentB : Bool :=
  let transcript := fixtureDeepTranscript
  let views := (List.range (CREW_SIZE + 1)).map fun k =>
    fixtureRunSeal.step? (transcript.take k)
  let roots := views.filterMap fun view? => view?.map StepView.reachedRoot
  decide (roots.length = CREW_SIZE + 1) &&
  decide (roots.Nodup) &&
  ((List.range (CREW_SIZE + 1)).all fun k =>
    match fixtureRunSeal.step? (transcript.take k) with
    | none => false
    | some view =>
        decide (view.sequence = k) &&
        decide (view.session = fixtureRunSeal.session) &&
        decide (view.nextSeat.isSome = decide (k < CREW_SIZE)) &&
        decide (view.phase = if k = CREW_SIZE then MissionPhase.extracted else .active) &&
        decide ((fixtureRunSeal.replay? (transcript.take k)).isSome =
          decide (k = CREW_SIZE)))

/-- The prefix gap, stated: four proper prefixes at which the kernel has a state
and `replay?` has nothing to say, and one completed run where they agree. -/
theorem the_step_surface_answers_at_every_prefix_replay_refuses :
    stepAnswersEveryPrefixWhileReplayIsSilentB = true := by native_decide

/-- One handoff, produced through nothing but the public surface: ask the seal
what this seat must sign, sign exactly those bytes, and emit the trace.  No
caller-side transition, no caller-authored `preRoot`. -/
private def stepDrive : List HandoffTrace → List Decision → Option (List HandoffTrace)
  | transcript, [] => some transcript
  | transcript, decision :: rest => do
      let view ← fixtureRunSeal.step? transcript
      let seat ← view.nextSeat
      let seatSignature := fixtureSeatSignature seat
      let preimage ← fixtureRunSeal.nextSigningPreimage? transcript seatSignature decision
      let trace : HandoffTrace := {
        sequence := preimage.body.sequence
        seat := preimage.body.seat
        previousCounter := preimage.body.previousCounter
        counter := preimage.body.counter
        observation := preimage.body.observation
        decision := preimage.body.decision
        seatSignature
        signature := fixtureHandoffSignatureFor seat preimage }
      stepDrive (transcript ++ [trace]) rest

def stepSurfaceDrivesAWholeSignedRunB : Bool :=
  match stepDrive [] (deepPlan.map Prod.snd) with
  | none => false
  | some transcript =>
      decide (transcript = fixtureDeepTranscript) &&
      (fixtureRunSeal.replay? transcript).isSome &&
      match fixtureRunSeal.step? transcript with
      | none => false
      | some view => decide (view.completion = fixtureRunSeal.replay? transcript)

/-- ⚑ ONE SEAT'S SIGNED HANDOFF IS COMPLETABLE — four times over.  Driven from
the empty transcript through `step?` and `nextSigningPreimage?` alone, a client
that never reimplements the transition reconstructs the kernel's own signed
transcript byte for byte, and the seal admits the run it built. -/
theorem a_crew_plays_a_whole_run_one_signed_handoff_at_a_time :
    stepSurfaceDrivesAWholeSignedRunB = true := by native_decide

def stepSurfaceRefusesAnotherSeatsAdmissionB : Bool :=
  let decision : Decision := .specialist .signalGallery .markSalvageRoute
  match fixtureRunSeal.step? [] with
  | none => false
  | some view =>
    match view.nextSeat, seatById? fixtureRawConfig.roster ⟨1⟩ with
    | some turn, some other =>
        decide (other ≠ turn) &&
        (fixtureRunSeal.nextSigningPreimage? [] (fixtureSeatSignature other) decision).isNone &&
        (fixtureRunSeal.nextSigningPreimage? [] (fixtureSeatSignature turn) decision).isSome
    | _, _ => false

/-- The mutation is asserted present (`other ≠ turn`) and the honest control is
in the same statement: seat 0's own admission envelope opens seat 0's briefing,
seat 1's does not.  Without the second conjunct's control this would pass for a
surface that refused everyone. -/
theorem the_step_surface_opens_a_briefing_only_to_its_own_seat :
    stepSurfaceRefusesAnotherSeatsAdmissionB = true := by native_decide

/-! The seal must be satisfiable *and* refutable.  A predicate that accepted
everything would weld the runtime to nothing at all, so each acceptance below is
paired with a refusal built by mutating the record the kernel just produced. -/

def sealAdmitsKernelProducedRecordB : Bool :=
  match completionFor? deepPlan with
  | none => false
  | some record => fixtureRunSeal.admits record.toRaw

theorem run_seal_admits_the_record_the_kernel_produced :
    sealAdmitsKernelProducedRecordB = true := by native_decide

/-- ⚑ The fabrication check, and the reason `RunSeal` exists.  A caller that
asserts a terminal state — the exact defect `CrewFieldMissionRuntime.deriveRecord?`
had — is refused, because `admits` reaches that state by running `execute` rather
than by reading the claim.  The mutated root is built from the live record and
asserted different before the verdict is read. -/
def sealRefusesAssertedTerminalRootB : Bool :=
  match completionFor? deepPlan with
  | none => false
  | some record =>
      let raw := record.toRaw
      let asserted : StateRoot := { raw.finalRoot with snapshot :=
        { raw.finalRoot.snapshot with
          operationalBudgetRemaining :=
            raw.finalRoot.snapshot.operationalBudgetRemaining + 1 } }
      decide (asserted ≠ raw.finalRoot) &&
      !fixtureRunSeal.admits { raw with finalRoot := asserted }

theorem run_seal_refuses_a_terminal_state_the_kernel_did_not_reach :
    sealRefusesAssertedTerminalRootB = true := by native_decide

/-- The signature leg: one forged handoff signature and the seal refuses.  The
forgery is constructed from the live trace and asserted to differ from it, so
this cannot quietly become a comparison of a value with itself. -/
def sealRefusesForgedHandoffSignatureB : Bool :=
  match completionFor? deepPlan with
  | none => false
  | some record =>
      match record.toRaw.transcript with
      | [] => false
      | trace :: rest =>
          let forged : HandoffTrace :=
            { trace with signature := ⟨signatureBytesPattern 251⟩ }
          decide (forged.signature ≠ trace.signature) &&
          !fixtureRunSeal.admits { record.toRaw with transcript := forged :: rest }

theorem run_seal_refuses_a_forged_handoff_signature :
    sealRefusesForgedHandoffSignatureB = true := by native_decide

/-- A seal issued for this session says so.  The runtime pins this against the
session its activation was authenticated for. -/
theorem fixture_run_seal_carries_the_fixture_session :
    fixtureRunSeal.session = fixtureRawConfig.sessionDigest := rfl

theorem safe_extraction_accepts_two_matching_signed_recommendations :
    (completionFor? safePlan).isSome = true := by native_decide

theorem alternative_safe_route_is_reachable :
    (completionFor? safeMaintenancePlan).isSome = true := by native_decide

theorem deep_recovery_requires_and_accepts_full_crew_consensus :
    (completionFor? deepPlan).isSome = true := by native_decide

def completedPlansDifferB : Bool :=
  match completionFor? safePlan, completionFor? deepPlan with
  | some safe, some deep =>
      decide (safe.extraction = .returnNow) &&
      decide (deep.extraction = .descendFurther) &&
      decide (safe.outcome.contribution ≠ deep.outcome.contribution) &&
      decide (safe.featuredBeta ∈ safe.outcome.betaCandidates) &&
      decide (deep.featuredBeta ∈ deep.outcome.betaCandidates)
  | _, _ => false

theorem route_and_extraction_choices_produce_materially_distinct_records :
    completedPlansDifferB = true := by native_decide

def completedBudgetAccountingB : Bool :=
  match completionFor? safePlan, completionFor? deepPlan with
  | some safe, some deep =>
      decide (safe.routeOperationalCost = 3) &&
      decide (safe.totalOperationalCost = 6) &&
      decide (safe.finalRoot.snapshot.operationalBudgetRemaining = 7) &&
      decide (safe.totalOperationalCost +
        safe.finalRoot.snapshot.operationalBudgetRemaining =
          fixtureRawConfig.operationalBudget) &&
      decide (deep.routeOperationalCost = 7) &&
      decide (deep.totalOperationalCost = 13) &&
      decide (deep.finalRoot.snapshot.operationalBudgetRemaining = 0) &&
      decide (deep.totalOperationalCost +
        deep.finalRoot.snapshot.operationalBudgetRemaining =
          fixtureRawConfig.operationalBudget)
  | _, _ => false

theorem specialist_steps_and_final_route_are_both_charged_exactly :
    completedBudgetAccountingB = true := by
  native_decide

def fixedExtractionRouteVariationB : Bool :=
  match completionFor? safePlan, completionFor? safeMaintenancePlan with
  | some signal, some maintenance =>
      decide (signal.extraction = .returnNow) &&
      decide (maintenance.extraction = .returnNow) &&
      decide (signal.route ≠ maintenance.route) &&
      decide (signal.routeOperationalCost ≠ maintenance.routeOperationalCost) &&
      decide (signal.totalOperationalCost ≠ maintenance.totalOperationalCost) &&
      decide (signal.finalRoot.snapshot.operationalBudgetRemaining ≠
        maintenance.finalRoot.snapshot.operationalBudgetRemaining) &&
      decide (signal.outcome.contribution ≠ maintenance.outcome.contribution) &&
      decide (signal.featuredBeta ≠ maintenance.featuredBeta)
  | _, _ => false

/-- Route is a material choice even with extraction held fixed: it changes
cost, bounded reward, and the exact beta candidate. -/
theorem route_changes_cost_reward_and_artifact_at_fixed_extraction :
    fixedExtractionRouteVariationB = true := by native_decide

/-! Outcome-table well-formedness is not a claim that every authored branch is
reachable from this particular briefing deck and cooperation policy. -/
def allAuthoredOutcomesWellFormedB : Bool :=
  fixtureRouteOutcomes.all fun spec =>
    (ActivityOutcome.validate fixturePolicy spec.outcome).isSome &&
    decide (spec.featuredArtifact ∈ spec.outcome.betaCandidates) &&
    decide (0 < spec.operationalCost)

theorem all_six_authored_route_extraction_outcomes_are_bounded_and_declared :
    allAuthoredOutcomesWellFormedB = true := by native_decide

def exactReplayB (plan : List (SeatId × Decision)) : Bool :=
  match completionFor? plan with
  | none => false
  | some record =>
      match replayTrace fixtureConfig (initialState fixtureConfig) record.transcript with
      | .error _ => false
      | .ok result => match result.completion with
        | none => false
        | some replayed => decide (replayed.toRaw = record.toRaw)

theorem combined_field_record_replays_every_signed_handoff_exactly :
    exactReplayB deepPlan = true := by native_decide

def readmitB (plan : List (SeatId × Decision)) : Bool :=
  match completionFor? plan with
  | none => false
  | some record => (admitCombinedFieldRecord? fixtureAdmission record.toRaw).isSome

theorem unchecked_record_projection_readmits_after_exact_replay :
    readmitB deepPlan = true := by native_decide

def overBudgetSafePrefix : List (SeatId × Decision) :=
  [ (⟨0⟩, .specialist .sealedNave .chartPressureRoute)
  , (⟨1⟩, .specialist .sealedNave .braceTransit)
  , (⟨2⟩, .specialist .signalGallery .quietAnomaly) ]

/-- This branch satisfies the safe-return recommendation rule but its three
survey steps leave only ten units, less than the sealed-nave return cost eleven. -/
def overBudgetSafeFinalResult : Option Refusal := do
  let prefixResult ← drive (start fixtureAdmission) overBudgetSafePrefix
  let handoff ← testHandoff? prefixResult.state ⟨3⟩
    (.finalize .sealedNave .returnNow .bankSupplies)
  match execute fixtureConfig prefixResult.state handoff with
  | .error refusal => some refusal
  | .ok _ => none

theorem recommendation_valid_but_over_budget_route_is_refused_at_live_budget_boundary :
    overBudgetSafeFinalResult = some .insufficientOperationalBudget := by
  native_decide

def mixedStrategyPlan : List (SeatId × Decision) :=
  [ (⟨0⟩, .specialist .signalGallery .markSalvageRoute)
  , (⟨1⟩, .specialist .signalGallery .braceTransit)
  , (⟨2⟩, .specialist .signalGallery .quietAnomaly)
  , (⟨3⟩, .finalize .signalGallery .returnNow .bankSupplies) ]

theorem hostile_mixed_crew_strategy_refused :
    drive (start fixtureAdmission) mixedStrategyPlan = none := by native_decide

def splitDeepPlan : List (SeatId × Decision) :=
  [ (⟨0⟩, .specialist .signalGallery .markSalvageRoute)
  , (⟨1⟩, .specialist .maintenanceSpine .overdriveCargoLift)
  , (⟨2⟩, .specialist .signalGallery .screenRecovery)
  , (⟨3⟩, .finalize .signalGallery .descendFurther .secureCache) ]

theorem hostile_deep_recovery_without_unanimity_refused :
    drive (start fixtureAdmission) splitDeepPlan = none := by native_decide

private def firstState : State := start fixtureAdmission

private def firstHandoff? : Option (SignedHandoff fixtureConfig) :=
  testHandoff? firstState ⟨0⟩ (.specialist .signalGallery .chartPressureRoute)

def substitutedObservationResult : Option Refusal := do
  let handoff ← firstHandoff?
  let forgedBody := { handoff.body with observation := .pathfinder .sealedNave }
  match execute fixtureConfig firstState { handoff with body := forgedBody } with
  | .error refusal => some refusal
  | .ok _ => none

theorem hostile_private_observation_substitution_refused :
    substitutedObservationResult = some .observationMismatch := by native_decide

def staleRootResult : Option Refusal := do
  let handoff ← firstHandoff?
  let forgedRoot : StateRoot := {
    handoff.body.preRoot with snapshot := {
      handoff.body.preRoot.snapshot with sequence := 1 } }
  let forgedBody := { handoff.body with preRoot := forgedRoot }
  match execute fixtureConfig firstState { handoff with body := forgedBody } with
  | .error refusal => some refusal
  | .ok _ => none

theorem hostile_stale_predecessor_root_refused :
    staleRootResult = some .staleRoot := by native_decide

def substitutedSignatureResult : Option Refusal := do
  let handoff ← firstHandoff?
  let forged := { handoff with signature := {
    bytes := signatureBytesPattern 250 } }
  match execute fixtureConfig firstState forged with
  | .error refusal => some refusal
  | .ok _ => none

theorem hostile_handoff_signature_substitution_refused :
    substitutedSignatureResult = some .signatureRefused := by native_decide

def unsignedDecisionSubstitutionResult : Option Refusal := do
  let handoff ← firstHandoff?
  let forgedBody := { handoff.body with decision :=
    (Decision.specialist Route.maintenanceSpine Command.chartPressureRoute) }
  match execute fixtureConfig firstState { handoff with body := forgedBody } with
  | .error refusal => some refusal
  | .ok _ => none

theorem hostile_full_field_decision_substitution_refused_by_signature :
    unsignedDecisionSubstitutionResult = some .signatureRefused := by native_decide

def otherSeatSignatureResult : Option Refusal := do
  let handoff ← firstHandoff?
  let messageDigest := fixtureMessageDigest.handoffMessageDigest
    (handoff.body.signingPreimage fixtureConfig.raw.messageDigestSuiteId
      fixtureConfig.raw.signingSuiteId)
  let forgedSignature : HandoffSignature := {
    bytes := fixtureExpectedSignature 2 fixtureSeat1.playerKey
      fixtureSeat1.credential messageDigest }
  match execute fixtureConfig firstState { handoff with signature := forgedSignature } with
  | .error refusal => some refusal
  | .ok _ => none

theorem hostile_signature_issued_for_other_seat_refused :
    otherSeatSignatureResult = some .signatureRefused := by native_decide

def wrongSigningSuiteResult : Option Refusal := do
  let handoff ← firstHandoff?
  let wrongPreimage := handoff.body.signingPreimage
    fixtureConfig.raw.messageDigestSuiteId (digestFilled 249)
  let forgedSignature : HandoffSignature := {
    bytes := fixtureExpectedSignature 2 handoff.capability.seat.playerKey
      handoff.capability.seat.credential
      (fixtureMessageDigest.handoffMessageDigest wrongPreimage) }
  match execute fixtureConfig firstState { handoff with signature := forgedSignature } with
  | .error refusal => some refusal
  | .ok _ => none

theorem hostile_signing_suite_substitution_refused :
    wrongSigningSuiteResult = some .signatureRefused := by native_decide

private def digestDoubledAsSignatureBytes (digest : Digest32) : SignatureBytes where
  bytes := digest.bytes ++ digest.bytes ++
    List.replicate (SIGNATURE_BYTE_LENGTH - 64) 0
  length_eq := by
    simp only [List.length_append, List.length_replicate, digest.length_eq]
    decide

/-- A message digest is public and easy to compute.  Repeating its 32 bytes
(zero-padded to the envelope length) still provides no proof of key
possession. -/
def forgedMessageDigestAsSignatureResult : Option Refusal := do
  let handoff ← firstHandoff?
  let forgedSignature : HandoffSignature := {
    bytes := digestDoubledAsSignatureBytes
      (handoff.body.messageDigest fixtureConfig) }
  match execute fixtureConfig firstState { handoff with signature := forgedSignature } with
  | .error refusal => some refusal
  | .ok _ => none

theorem hostile_public_message_digest_submitted_as_signature_refused :
    forgedMessageDigestAsSignatureResult = some .signatureRefused := by
  native_decide

def tamperedRecordReadmitsB : Bool :=
  match completionFor? deepPlan with
  | none => false
  | some record =>
      let raw := { record.toRaw with route := .sealedNave }
      (admitCombinedFieldRecord? fixtureAdmission raw).isSome

theorem hostile_combined_record_route_substitution_refused :
    tamperedRecordReadmitsB = false := by native_decide

private def tamperFirstTrace : List HandoffTrace → List HandoffTrace
  | [] => []
  | trace :: traces =>
      { trace with decision := .specialist .maintenanceSpine .markSalvageRoute } :: traces

def expandedRecordMutationsRefusedB : Bool :=
  match completionFor? deepPlan with
  | none => false
  | some record =>
      let raw := record.toRaw
      let rootMutation := { raw.finalRoot with snapshot := {
        raw.finalRoot.snapshot with sequence := raw.finalRoot.snapshot.sequence + 1 } }
      let mutations : List RawCombinedFieldRecord :=
        [ { raw with route := .sealedNave }
        , { raw with extraction := .returnNow }
        , { raw with strategy := .survey }
        , { raw with routeOperationalCost := raw.routeOperationalCost + 1 }
        , { raw with totalOperationalCost := raw.totalOperationalCost + 1 }
        , { raw with
              outcome := fixtureOutcome .maintenanceSpine .descendFurther
              featuredBeta := fixtureMaintenanceArtifact }
        , { raw with featuredBeta := fixtureMaintenanceArtifact }
        , { raw with finalRoot := rootMutation }
        , { raw with transcript := tamperFirstTrace raw.transcript }
        , { raw with transcript := raw.transcript.reverse }
        , { raw with session := {
              raw.session with briefingCommitment := digestFilled 244 } } ]
      mutations.all fun mutated =>
        !(admitCombinedFieldRecord? fixtureAdmission mutated).isSome

theorem hostile_expanded_record_mutation_matrix_refused :
    expandedRecordMutationsRefusedB = true := by native_decide

#assert_axioms execute_deterministic
#assert_axioms handoff_signing_preimage_injective
#assert_axioms seat_signing_preimage_injective
#assert_axioms completed_featured_artifact_is_beta_candidate
#assert_axioms RunSeal.admitted_record_carries_the_sealed_session
#assert_axioms RunSeal.step_completion_is_the_replayed_record
#assert_axioms step_view_next_body_is_the_kernel_expected_body
#assert_compiled fixture_rekeyed_config_valid
#assert_compiled fixture_rekeyed_roster_substitutes_only_the_player_keys
#assert_compiled the_fixture_briefing_commitment_does_not_separate_the_two_crews
#assert_compiled the_two_fixture_seals_carry_different_sessions
#assert_compiled exported_fixture_transcripts_are_four_signed_handoffs_each
#assert_compiled the_step_surface_answers_at_every_prefix_replay_refuses
#assert_compiled a_crew_plays_a_whole_run_one_signed_handoff_at_a_time
#assert_compiled the_step_surface_opens_a_briefing_only_to_its_own_seat
#assert_compiled run_seal_admits_the_record_the_kernel_produced
#assert_compiled run_seal_refuses_a_terminal_state_the_kernel_did_not_reach
#assert_compiled run_seal_refuses_a_forged_handoff_signature
#assert_compiled fixture_run_seal_carries_the_fixture_session
#assert_compiled fixture_config_valid
#assert_compiled fixture_ordered_briefing_deck_is_commitment_bound
#assert_compiled hostile_unwinnable_terminal_costs_are_individually_within_budget
#assert_compiled hostile_unwinnable_config_has_no_affordable_safe_terminal
#assert_compiled hostile_globally_unwinnable_config_refused_at_activation
#assert_compiled raw_identity_fields_must_exactly_match_policy_mission
#assert_compiled wrong_mission_artifact_is_otherwise_declared_and_outcome_valid
#assert_compiled artifact_mission_must_exactly_match_activated_mission
#assert_compiled hostile_same_role_briefing_substitution_breaks_activation_commitment
#assert_compiled safe_extraction_accepts_two_matching_signed_recommendations
#assert_compiled alternative_safe_route_is_reachable
#assert_compiled deep_recovery_requires_and_accepts_full_crew_consensus
#assert_compiled route_and_extraction_choices_produce_materially_distinct_records
#assert_compiled specialist_steps_and_final_route_are_both_charged_exactly
#assert_compiled route_changes_cost_reward_and_artifact_at_fixed_extraction
#assert_compiled all_six_authored_route_extraction_outcomes_are_bounded_and_declared
#assert_compiled combined_field_record_replays_every_signed_handoff_exactly
#assert_compiled unchecked_record_projection_readmits_after_exact_replay
#assert_compiled recommendation_valid_but_over_budget_route_is_refused_at_live_budget_boundary
#assert_compiled hostile_mixed_crew_strategy_refused
#assert_compiled hostile_deep_recovery_without_unanimity_refused
#assert_compiled hostile_private_observation_substitution_refused
#assert_compiled hostile_stale_predecessor_root_refused
#assert_compiled hostile_handoff_signature_substitution_refused
#assert_compiled hostile_full_field_decision_substitution_refused_by_signature
#assert_compiled hostile_signature_issued_for_other_seat_refused
#assert_compiled hostile_signing_suite_substitution_refused
#assert_compiled hostile_public_message_digest_submitted_as_signature_refused
#assert_compiled hostile_combined_record_route_substitution_refused
#assert_compiled hostile_expanded_record_mutation_matrix_refused

/-! ## ⚑ The production ML-DSA-65 signing suite — 2026-08-07

Until today every seal in the universe was a FIXTURE seal, and the fixture
verifier checks a publicly computable pattern with no secret anywhere — the
kernel's own docblock bars it from deployment.  This section is the deployable
suite: the canonical signing-preimage byte encoding, the SHAKE-256 message
digest, the ML-DSA-65 envelope verifier through the REAL executable FIPS 204
verify (`Dregg2.Crypto.MlDsaVerifyReal.verifyCore` — NIST-ACVP- and
crate-anchored in its own module), and the one public seal producer
`ProductionSigning.activate?`, structurally pinned to these three boundaries so
no caller ever supplies a verifier function.

**The signing message is canonical JSON with a FIXED key order**, containing
only decimal naturals, fixed labels, and lowercase hex — no escapable content
anywhere, so byte-faithful reproduction by a client signer is string
concatenation, not a JSON library.  The exact shapes are the `*Json` functions
below; they are the client-signing spec.  Faithfulness of this encoding
(injectivity into bytes) rests on the fixed key order plus the injective
`.code` projections, whose injectivity over their full finite spaces is proved
below as `observation_codes_are_injective` / `decision_codes_are_injective`.

**The two-source key pin.**  The verifier receives `playerKey : Digest32` from
the activated roster and an envelope `publicKey ‖ signature` from the signer;
it demands `SHAKE256(publicKey, 32) = playerKey` and then runs `verifyCore`
with the suite's signature context.  Roster and envelope are independent
sources; a genuine signature under a key that is not the seat's key is refused
by the pin (proved below with a REAL second keypair, not a corrupted blob).

**Signature-level domain separation.**  Seat admission and handoff signing use
distinct FIPS 204 `ctx` strings (`SEAT_SIGNING_CONTEXT` /
`HANDOFF_SIGNING_CONTEXT`) in addition to the distinct preimage formats, so a
seat-admission signature can never be replayed as a handoff signature even if
the message bytes were ever to collide.

The cross-language KAT at the bottom is the reason to believe the encoding is
not a mirror: the Lean encoder emitted the exact message bytes, the Rust
`fips204` v0.4.6 crate (an independent implementation) signed them, the crate's
own verify accepted them first, and `verifyCore` accepts them here —
satisfiable and refutable, with every refutation's mutation asserted present
before the verdict. -/

namespace ProductionSigning

open scoped Prod.Lex

/-! ### Canonical order for the two `Finset`s inside a session

`SessionDigest` reaches the signing preimage, and it contains
`policy.allowedBeta : Finset ArtifactRef` and
`policy.mission.allowedRelics : Finset RelicId`.  A `Finset`'s runtime
representative is insertion-ordered, so encoding the representative would make
the encoder non-functional (equal sessions, different bytes) — they must be
sorted.  These instances mirror `NetworkJudgeWire`'s (same order keys); they
are duplicated rather than imported because that module belongs to the signal
organ and drags its whole wire cone. -/

instance : LinearOrder RelicId :=
  LinearOrder.lift' RelicId.value (by
    intro left right equal
    cases left
    cases right
    simp_all)

private abbrev ArtifactSigningKey := Nat ×ₗ (Nat ×ₗ (Digest32 ×ₗ Digest32))

private def artifactSigningKey (a : ArtifactRef) : ArtifactSigningKey :=
  toLex (a.missionId.value,
    toLex (a.artifactId.value, toLex (a.sourceDigest, a.contentDigest)))

instance : LinearOrder ArtifactRef :=
  LinearOrder.lift' artifactSigningKey (by
    intro left right equal
    cases left
    cases right
    case mk.mk missionId₁ artifactId₁ source₁ content₁ missionId₂ artifactId₂ source₂ content₂ =>
      cases missionId₁
      cases artifactId₁
      cases missionId₂
      cases artifactId₂
      simp_all [artifactSigningKey])

/-! ### Canonical JSON emission (the client-signing spec) -/

private def hexDigitChar (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

private def byteHex (b : Fin 256) : String :=
  String.ofList [hexDigitChar (b.val / 16), hexDigitChar (b.val % 16)]

/-- 64 lowercase hex digits. -/
def digestHex (digest : Digest32) : String :=
  String.join (digest.bytes.map byteHex)

private def natArray (values : List Nat) : String :=
  "[" ++ String.intercalate "," (values.map toString) ++ "]"

private def jsonArray (values : List String) : String :=
  "[" ++ String.intercalate "," values ++ "]"

private def crewRoleCode : CrewRole → Nat
  | .pathfinder => 0
  | .engineer => 1
  | .containment => 2
  | .quartermaster => 3

private def privacyGradeCode : PrivacyGrade → Nat
  | .public => 0
  | .operatorVisibleHidingFri => 1
  | .processSeparatedThreshold => 2
  | .independentOperatorThreshold => 3

private def ballotRegimeCode : BallotRegime → Nat
  | .none => 0
  | .onePlayerOneVoice => 1
  | .oneWalletOneVoice => 2
  | .cappedChoir => 3
  | .predictionOracle => 4

private def briefingPrivacyCode : BriefingPrivacyBoundary → Nat
  | .trustedDealerOperatorVisibleThenPublicHandoff => 0

private def extractionCode : ExtractionChoice → Nat
  | .returnNow => 0
  | .descendFurther => 1

private def phaseCode : MissionPhase → Nat
  | .active => 0
  | .extracted => 1

private def strategyCode : Option Strategy → Nat
  | none => 0
  | some .survey => 1
  | some .salvage => 2

def seatJson (seat : Seat) : String :=
  "{\"seat\":" ++ toString seat.id.value ++
    ",\"player_key\":\"" ++ digestHex seat.playerKey ++ "\"" ++
    ",\"credential\":" ++ toString seat.credential.value ++
    ",\"role\":" ++ toString (crewRoleCode seat.role) ++
    ",\"initial_counter\":" ++ toString seat.initialCounter ++ "}"

def artifactJson (artifact : ArtifactRef) : String :=
  "{\"mission\":" ++ toString artifact.missionId.value ++
    ",\"artifact\":" ++ toString artifact.artifactId.value ++
    ",\"source\":\"" ++ digestHex artifact.sourceDigest ++ "\"" ++
    ",\"content\":\"" ++ digestHex artifact.contentDigest ++ "\"}"

private def budgetJson (budget : ContributionBudget) : String :=
  "{\"intel\":" ++ toString budget.intel.val ++
    ",\"supplies\":" ++ toString budget.supplies.val ++
    ",\"cohesion\":" ++ toString budget.cohesion.val ++
    ",\"influence\":" ++ toString budget.influence.val ++
    ",\"score\":" ++ toString budget.score.val ++
    ",\"relics\":" ++ toString budget.relics.val ++ "}"

private def missionSpecJson (mission : MissionSpec) : String :=
  "{\"mission\":" ++ toString mission.missionId.value ++
    ",\"artifact\":" ++ artifactJson mission.artifact ++
    ",\"epoch\":" ++ toString mission.epoch.value ++
    ",\"federation\":\"" ++ digestHex mission.federationId ++ "\"" ++
    ",\"content_root\":\"" ++ digestHex mission.contentRoot ++ "\"" ++
    ",\"activation\":\"" ++ digestHex mission.activationDigest ++ "\"" ++
    ",\"content_session\":\"" ++ digestHex mission.contentSession ++ "\"" ++
    ",\"run_seed\":\"" ++ digestHex mission.runSeed ++ "\"" ++
    ",\"budget\":" ++ budgetJson mission.budget ++
    ",\"allowed_relics\":" ++
      natArray ((mission.allowedRelics.sort (· ≤ ·)).map RelicId.value) ++
    ",\"privacy\":" ++ toString (privacyGradeCode mission.privacy) ++
    ",\"ballot\":" ++ toString (ballotRegimeCode mission.ballot) ++ "}"

private def policyJson (policy : ActivityOutcome.Policy) : String :=
  "{\"mission\":" ++ missionSpecJson policy.mission ++
    ",\"allowed_beta\":" ++
      jsonArray ((policy.allowedBeta.sort (· ≤ ·)).map artifactJson) ++
    ",\"result_limit\":" ++ toString policy.resultLimit.val ++ "}"

private def rawContributionJson (raw : RawContribution) : String :=
  "{\"intel\":" ++ toString raw.intel ++
    ",\"supplies\":" ++ toString raw.supplies ++
    ",\"cohesion\":" ++ toString raw.cohesion ++
    ",\"influence\":" ++ toString raw.influence ++
    ",\"score\":" ++ toString raw.score ++
    ",\"relics\":" ++ natArray (raw.relics.map RelicId.value) ++ "}"

private def rawOutcomeJson (raw : ActivityOutcome.Raw) : String :=
  "{\"contribution\":" ++ rawContributionJson raw.contribution ++
    ",\"beta_candidates\":" ++ jsonArray (raw.betaCandidates.map artifactJson) ++ "}"

private def routeOutcomeJson (spec : RouteOutcomeSpec) : String :=
  "{\"route\":" ++ toString spec.route.code ++
    ",\"extraction\":" ++ toString (extractionCode spec.extraction) ++
    ",\"cost\":" ++ toString spec.operationalCost ++
    ",\"featured\":" ++ artifactJson spec.featuredArtifact ++
    ",\"outcome\":" ++ rawOutcomeJson spec.outcome ++ "}"

def sessionJson (session : SessionDigest) : String :=
  "{\"federation\":\"" ++ digestHex session.federationId ++ "\"" ++
    ",\"content_session\":\"" ++ digestHex session.contentSession ++ "\"" ++
    ",\"epoch\":" ++ toString session.missionEpoch.value ++
    ",\"mission\":" ++ toString session.missionId.value ++
    ",\"relay\":\"" ++ digestHex session.relayId ++ "\"" ++
    ",\"privacy\":" ++ toString (briefingPrivacyCode session.briefingPrivacy) ++
    ",\"briefing_suite\":\"" ++ digestHex session.briefingHashSuiteId ++ "\"" ++
    ",\"briefing_commitment\":\"" ++ digestHex session.briefingCommitment ++ "\"" ++
    ",\"message_suite\":\"" ++ digestHex session.messageDigestSuiteId ++ "\"" ++
    ",\"signing_suite\":\"" ++ digestHex session.signingSuiteId ++ "\"" ++
    ",\"roster\":" ++ jsonArray (session.roster.map seatJson) ++
    ",\"policy\":" ++ policyJson session.policy ++
    ",\"budget\":" ++ toString session.operationalBudget ++
    ",\"route_outcomes\":" ++ jsonArray (session.routeOutcomes.map routeOutcomeJson) ++ "}"

private def seatCounterJson (counter : SeatCounter) : String :=
  "{\"seat\":" ++ toString counter.seat.value ++
    ",\"counter\":" ++ toString counter.counter ++ "}"

private def signatureNats (signature : SignatureBytes) : List Nat :=
  signature.bytes.map Fin.val

private def traceJson (trace : HandoffTrace) : String :=
  "{\"sequence\":" ++ toString trace.sequence ++
    ",\"seat\":" ++ seatJson trace.seat ++
    ",\"previous_counter\":" ++ toString trace.previousCounter ++
    ",\"counter\":" ++ toString trace.counter ++
    ",\"observation\":" ++ toString trace.observation.code ++
    ",\"decision\":" ++ toString trace.decision.code ++
    ",\"seat_signature\":" ++ natArray (signatureNats trace.seatSignature.bytes) ++
    ",\"handoff_signature\":" ++ natArray (signatureNats trace.signature.bytes) ++ "}"

private def snapshotJson (snapshot : StateSnapshot) : String :=
  "{\"phase\":" ++ toString (phaseCode snapshot.phase) ++
    ",\"sequence\":" ++ toString snapshot.sequence ++
    ",\"next_seat\":" ++ toString snapshot.nextSeat ++
    ",\"counters\":" ++ jsonArray (snapshot.counters.map seatCounterJson) ++
    ",\"strategy\":" ++ toString (strategyCode snapshot.strategy) ++
    ",\"budget_remaining\":" ++ toString snapshot.operationalBudgetRemaining ++
    ",\"transcript\":" ++ jsonArray (snapshot.transcript.map traceJson) ++ "}"

private def stateRootJson (root : StateRoot) : String :=
  "{\"session\":" ++ sessionJson root.session ++
    ",\"snapshot\":" ++ snapshotJson root.snapshot ++ "}"

def seatAdmissionBodyJson (body : SeatAdmissionBody) : String :=
  "{\"session\":" ++ sessionJson body.session ++
    ",\"seat\":" ++ seatJson body.seat ++ "}"

def handoffBodyJson (body : HandoffBody) : String :=
  "{\"session\":" ++ sessionJson body.session ++
    ",\"sequence\":" ++ toString body.sequence ++
    ",\"pre_root\":" ++ stateRootJson body.preRoot ++
    ",\"seat\":" ++ seatJson body.seat ++
    ",\"previous_counter\":" ++ toString body.previousCounter ++
    ",\"counter\":" ++ toString body.counter ++
    ",\"observation\":" ++ toString body.observation.code ++
    ",\"decision\":" ++ toString body.decision.code ++ "}"

def seatPreimageJson (preimage : SeatSigningPreimage) : String :=
  "{\"format\":\"POA-CREW-SEAT-SIGNING-1\"" ++
    ",\"version\":" ++ toString preimage.formatVersion ++
    ",\"message_suite\":\"" ++ digestHex preimage.messageDigestSuiteId ++ "\"" ++
    ",\"signing_suite\":\"" ++ digestHex preimage.signatureSuiteId ++ "\"" ++
    ",\"body\":" ++ seatAdmissionBodyJson preimage.body ++ "}"

def handoffPreimageJson (preimage : HandoffSigningPreimage) : String :=
  "{\"format\":\"POA-CREW-HANDOFF-SIGNING-1\"" ++
    ",\"version\":" ++ toString preimage.formatVersion ++
    ",\"message_suite\":\"" ++ digestHex preimage.messageDigestSuiteId ++ "\"" ++
    ",\"signing_suite\":\"" ++ digestHex preimage.signatureSuiteId ++ "\"" ++
    ",\"body\":" ++ handoffBodyJson preimage.body ++ "}"

/-- The exact bytes a seat's signer signs to open its seat. -/
def seatPreimageMessage (preimage : SeatSigningPreimage) : List UInt8 :=
  (seatPreimageJson preimage).toUTF8.toList

/-- The exact bytes a seat's signer signs for one handoff. -/
def handoffPreimageMessage (preimage : HandoffSigningPreimage) : List UInt8 :=
  (handoffPreimageJson preimage).toUTF8.toList

/-! The encoder leans on the `.code` projections; their injectivity over the
COMPLETE finite decision and observation spaces is asserted here as named
theorems, not left to the constructor comment. -/

private def allRoutes : List Route := [.maintenanceSpine, .signalGallery, .sealedNave]

private def allObservations : List PrivateObservation :=
  (allRoutes.map .pathfinder) ++ (allRoutes.map .engineer) ++
    (allRoutes.map .containment) ++ [.quartermaster .closing, .quartermaster .stable]

private def allCommands : List Command :=
  [.chartPressureRoute, .markSalvageRoute, .braceTransit, .overdriveCargoLift,
    .quietAnomaly, .screenRecovery, .bankSupplies, .secureCache]

private def allDecisions : List Decision :=
  (allRoutes.flatMap fun route => allCommands.map (Decision.specialist route)) ++
    (allRoutes.flatMap fun route => allCommands.flatMap fun command =>
      [Decision.finalize route .returnNow command,
       Decision.finalize route .descendFurther command])

private def codesInjectiveOnB {α : Type} [DecidableEq α]
    (code : α → Nat) (values : List α) : Bool :=
  values.all fun left => values.all fun right =>
    decide (code left = code right → left = right)

theorem observation_codes_are_injective :
    codesInjectiveOnB PrivateObservation.code allObservations = true ∧
      allObservations.length = 11 := by native_decide

theorem decision_codes_are_injective :
    codesInjectiveOnB Decision.code allDecisions = true ∧
      allDecisions.length = 72 := by native_decide

/-! ### SHAKE-256 digest and the suite identities -/

/-- SHAKE-256 → 32 bytes, refusal-shaped.  `none` is structurally dead —
`Keccak.squeeze` emits `⌈32/136⌉·136 = 136` bytes and takes 32, a length that
depends only on the requested output length, never on the input — but the type
does not know that, and a silent pad here would be a degrade, so the mismatch
arm refuses instead. -/
def shakeDigest32? (input : List UInt8) : Option Digest32 :=
  let out := (Dregg2.Crypto.Keccak.shake256 input 32).map
    fun b => (⟨b.toNat % 256, Nat.mod_lt _ (by omega)⟩ : Fin 256)
  if h : out.length = 32 then some ⟨out, h⟩ else none

/-- Total form for the activated boundaries, which must return a digest.  The
fallback arm is the structurally dead branch above; the concrete teeth below
pin the live arm on every value this file relies on. -/
def shakeDigest32 (input : List UInt8) : Digest32 :=
  (shakeDigest32? input).getD (digestFilled 0)

/-- Two labeled INSTANCES (not a general proof) that the shake output length is
exactly 32 — one empty input, one multi-block input. -/
theorem shake_digest_lengths_hold_on_instances :
    (shakeDigest32? []).isSome = true ∧
      (shakeDigest32? (List.replicate 500 7)).isSome = true := by native_decide

private def labelDigest (label : String) : Digest32 :=
  shakeDigest32 label.toUTF8.toList

def briefingSuiteId : Digest32 := labelDigest "POA-CREW-BRIEFING-SHAKE256-1"
def messageSuiteId : Digest32 := labelDigest "POA-CREW-MSGDIGEST-SHAKE256-1"
def signingSuiteId : Digest32 := labelDigest "POA-CREW-SIGNING-MLDSA65-1"

/-- Distinct from each other AND from the fixture suite ids.  This is also the
tooth that proves the `labelDigest` fallback arm never fired (a fired fallback
would collapse two of these to the same constant). -/
theorem production_suite_ids_are_distinct_and_not_the_fixture_ids :
    briefingSuiteId ≠ messageSuiteId ∧ briefingSuiteId ≠ signingSuiteId ∧
    messageSuiteId ≠ signingSuiteId ∧
    briefingSuiteId ≠ fixtureBriefingDigest.id ∧
    messageSuiteId ≠ fixtureMessageDigestSuiteId ∧
    signingSuiteId ≠ fixtureSignatureSuiteId := by native_decide

def briefingDeckJson (preimage : BriefingDeckPreimage) : String :=
  "{\"format\":\"POA-CREW-BRIEFING-DECK-1\"" ++
    ",\"federation\":\"" ++ digestHex preimage.federationId ++ "\"" ++
    ",\"content_session\":\"" ++ digestHex preimage.contentSession ++ "\"" ++
    ",\"epoch\":" ++ toString preimage.missionEpoch.value ++
    ",\"mission\":" ++ toString preimage.missionId.value ++
    ",\"relay\":\"" ++ digestHex preimage.relayId ++ "\"" ++
    ",\"privacy\":" ++ toString (briefingPrivacyCode preimage.privacy) ++
    ",\"roster\":" ++ jsonArray (preimage.roster.map seatJson) ++
    ",\"briefings\":" ++ jsonArray (preimage.orderedBriefings.map fun briefing =>
      "{\"seat\":" ++ toString briefing.seat.value ++
        ",\"observation\":" ++ toString briefing.observation.code ++ "}") ++ "}"

def productionBriefingDigest : BriefingDigestBoundary where
  id := briefingSuiteId
  digest preimage := shakeDigest32 (briefingDeckJson preimage).toUTF8.toList

def productionMessageDigest : SigningMessageDigestBoundary where
  id := messageSuiteId
  seatMessageDigest preimage := shakeDigest32 (seatPreimageMessage preimage)
  handoffMessageDigest preimage := shakeDigest32 (handoffPreimageMessage preimage)

/-! ### The ML-DSA-65 envelope verifier -/

abbrev SEAT_SIGNING_CONTEXT : String := "POA-CREW-SEAT-MLDSA65-1"
abbrev HANDOFF_SIGNING_CONTEXT : String := "POA-CREW-HANDOFF-MLDSA65-1"

private def envelopeParts (signature : SignatureBytes) : List UInt8 × List UInt8 :=
  let bytes := signature.bytes.map fun b => UInt8.ofNat b.val
  (bytes.take MLDSA65_PUBLIC_KEY_BYTE_LENGTH, bytes.drop MLDSA65_PUBLIC_KEY_BYTE_LENGTH)

/-- The two-source pin plus the real verify: the envelope's public key must
digest to the roster's `playerKey`, and the ML-DSA-65 signature must verify
over the exact message under the suite's signature context. -/
def verifyEnvelope (playerKey : Digest32) (context : String) (message : List UInt8)
    (signature : SignatureBytes) : Bool :=
  let (publicKey, mldsaSignature) := envelopeParts signature
  decide (shakeDigest32? publicKey = some playerKey) &&
  Dregg2.Crypto.MlDsaVerifyReal.verifyCore publicKey message
    context.toUTF8.toList mldsaSignature

def productionSignatureVerifier : ActivatedSignatureVerifier where
  id := signingSuiteId
  verifySeat playerKey _credential preimage signature :=
    decide (preimage.formatVersion = SIGNING_FORMAT_VERSION) &&
    decide (preimage.messageDigestSuiteId = messageSuiteId) &&
    decide (preimage.signatureSuiteId = signingSuiteId) &&
    verifyEnvelope playerKey SEAT_SIGNING_CONTEXT
      (seatPreimageMessage preimage) signature
  verifyHandoff playerKey _credential preimage signature :=
    decide (preimage.formatVersion = SIGNING_FORMAT_VERSION) &&
    decide (preimage.messageDigestSuiteId = messageSuiteId) &&
    decide (preimage.signatureSuiteId = signingSuiteId) &&
    verifyEnvelope playerKey HANDOFF_SIGNING_CONTEXT
      (handoffPreimageMessage preimage) signature

/-! ### The one public seal producer

A caller chooses only DATA (`RawConfig` + briefings); every function — briefing
digest, message digest, signature verifier — is pinned structurally to the
production suite.  This does not reopen the caller-supplied-verifier hole the
2026-08-06 weld closed: there is no argument through which a verifier could
arrive.  A caller can mint a seal for a mission of its own authorship, but a
seal only ever judges its own session
(`RunSeal.admitted_record_carries_the_sealed_session`), and the runtime pins
`runSeal.session` against the authored activation's field session. -/

def activate? (raw : RawConfig) (briefings : List BriefingAssignment) : Option RunSeal :=
  if hvalid : rawConfigValidB raw briefings productionBriefingDigest = true then
    if hmessage : raw.messageDigestSuiteId = productionMessageDigest.id then
      if hsigning : raw.signingSuiteId = productionSignatureVerifier.id then
        let config : Config := ⟨raw, briefings, productionBriefingDigest,
          productionMessageDigest, productionSignatureVerifier, hvalid, hmessage, hsigning⟩
        some ⟨config, ⟨config.raw.sessionDigest, rfl⟩⟩
      else none
    else none
  else none

/-! ### The KAT world — a production-suited mission with one REAL keypair

Seat 0's `playerKey` is the SHAKE-256 digest of a genuine ML-DSA-65 public key
(`CrewSigningVectors.katSeat0PublicKey`, deterministic `keygen_from_seed` from
a pinned xi — the secret is derivable by anyone; this world is for the KAT and
must never be deployed, same status as the fixture crew).  Seats 1–3 keep
fixture placeholder keys: only seat 0's signatures are judged here. -/

private def katSeat0PublicKeyBytes : List UInt8 :=
  CrewSigningVectors.katSeat0PublicKey.toList

private def katWrongPublicKeyBytes : List UInt8 :=
  CrewSigningVectors.katWrongPublicKey.toList

def katPlayerKey : Digest32 :=
  (shakeDigest32? katSeat0PublicKeyBytes).getD (digestFilled 7)

theorem kat_player_key_is_the_seat0_public_key_digest :
    shakeDigest32? katSeat0PublicKeyBytes = some katPlayerKey := by native_decide

/-- The wrong keypair's digest is NOT seat 0's player key — the premise of the
wrong-key refutation below. -/
theorem kat_wrong_public_key_digest_is_not_the_seat_key :
    shakeDigest32? katWrongPublicKeyBytes ≠ some katPlayerKey := by native_decide

private def katSeat0 : Seat := { fixtureSeat0 with playerKey := katPlayerKey }

private def katRoster : List Seat := [katSeat0, fixtureSeat1, fixtureSeat2, fixtureSeat3]

private def katRawConfigBase : RawConfig := {
  fixtureRawConfigBase with
  roster := katRoster
  briefingHashSuiteId := briefingSuiteId
  messageDigestSuiteId := productionMessageDigest.id
  signingSuiteId := productionSignatureVerifier.id }

def katRawConfig : RawConfig := {
  katRawConfigBase with
  briefingCommitment := productionBriefingDigest.digest
    (briefingDeckPreimage katRawConfigBase fixtureBriefings) }

theorem kat_config_valid :
    rawConfigValidB katRawConfig fixtureBriefings productionBriefingDigest = true := by
  native_decide

private def katConfig : Config :=
  ⟨katRawConfig, fixtureBriefings, productionBriefingDigest, productionMessageDigest,
    productionSignatureVerifier, kat_config_valid, rfl, rfl⟩

private def katState : State := initialState katConfig

private def katSeatBody : SeatAdmissionBody := expectedAdmission katConfig katSeat0

/-- Seat 0's first handoff body at the initial root — the exact thing a player
signs to act. -/
def katHandoffBody : HandoffBody := {
  session := katRawConfig.sessionDigest
  sequence := 0
  preRoot := katState.root
  seat := katSeat0
  previousCounter := katSeat0.initialCounter
  counter := katSeat0.initialCounter + 1
  observation := .pathfinder .signalGallery
  decision := .specialist .signalGallery .chartPressureRoute }

/-- The exact seat-admission message bytes (emitted for the cross-language
generator, and pinned back below once signed). -/
def katSeatMessage : List UInt8 :=
  seatPreimageMessage (katSeatBody.signingPreimage
    katRawConfig.messageDigestSuiteId katRawConfig.signingSuiteId)

/-- The exact handoff message bytes. -/
def katHandoffMessage : List UInt8 :=
  handoffPreimageMessage (katHandoffBody.signingPreimage
    katRawConfig.messageDigestSuiteId katRawConfig.signingSuiteId)

/-! ### Producer teeth (signature-independent) -/

theorem production_activation_seals_the_kat_mission :
    (activate? katRawConfig fixtureBriefings).map RunSeal.session =
      some katRawConfig.sessionDigest := by native_decide

/-- The producer cannot mint a seal over the fixture suite: the authored
fixture config names the fixture briefing/message/signing suite ids and the
production validator refuses it. -/
theorem production_activation_refuses_the_fixture_suite_config :
    activate? fixtureRawConfig fixtureBriefings = none := by native_decide

/-! ### The cross-language KAT — Rust `fips204` signs, Lean `verifyCore` accepts

Chronology, so the two-source claim is checkable: (1) the Lean encoder above
emitted `katSeatMessage` / `katHandoffMessage`; (2) the `fips204` crate signed
those exact bytes under the suite contexts and its OWN verify accepted the
honest pairings and refused the wrong-key/wrong-ctx/wrong-message pairings —
asserted inside the generator, before Lean ever judged anything; (3) the
signatures were pinned verbatim into `CrewSigningVectors`; (4) the theorems
below run the production verifier — the SHAKE-256 key pin plus the executable
FIPS 204 verify — over them.  Every refutation's mutation is asserted present
in the same statement as its refusal. -/

private def envelope? (publicKey signature : Array UInt8) : Option SignatureBytes :=
  let bytes := (publicKey.toList ++ signature.toList).map
    fun b => (⟨b.toNat % 256, Nat.mod_lt _ (by omega)⟩ : Fin 256)
  if h : bytes.length = SIGNATURE_BYTE_LENGTH then some ⟨bytes, h⟩ else none

private def katSeatEnvelope : SignatureBytes :=
  (envelope? CrewSigningVectors.katSeat0PublicKey
    CrewSigningVectors.katSeatSignature).getD (signatureBytesPattern 0)

private def katHandoffEnvelope : SignatureBytes :=
  (envelope? CrewSigningVectors.katSeat0PublicKey
    CrewSigningVectors.katHandoffSignature).getD (signatureBytesPattern 0)

private def katWrongKeyEnvelope : SignatureBytes :=
  (envelope? CrewSigningVectors.katWrongPublicKey
    CrewSigningVectors.katWrongKeyHandoffSignature).getD (signatureBytesPattern 0)

/-- The pinned vectors really are envelope-sized — and therefore none of the
`getD` fallbacks above fired. -/
theorem kat_envelopes_are_exact :
    envelope? CrewSigningVectors.katSeat0PublicKey CrewSigningVectors.katSeatSignature =
      some katSeatEnvelope ∧
    envelope? CrewSigningVectors.katSeat0PublicKey CrewSigningVectors.katHandoffSignature =
      some katHandoffEnvelope ∧
    envelope? CrewSigningVectors.katWrongPublicKey
      CrewSigningVectors.katWrongKeyHandoffSignature = some katWrongKeyEnvelope := by
  native_decide

/-- The messages the Rust side signed are byte-identical to what the Lean
encoder emits TODAY.  If the encoder ever drifts, this goes red separately
from the verify theorems, so encoder drift and verifier drift are
distinguishable at a glance. -/
theorem kat_messages_are_the_pinned_bytes :
    katSeatMessage = CrewSigningVectors.katSeatMessagePinned.toList ∧
    katHandoffMessage = CrewSigningVectors.katHandoffMessagePinned.toList := by
  native_decide

/-- ⚑ THE KEYSTONE, seat half: the honest seat-admission signature verifies
through the REAL executable FIPS 204 verify, over the production preimage
bytes, under the production suite — cross-language. -/
theorem kat_seat_admission_signature_verifies_cross_language :
    seatSignatureValidB katConfig katSeat0 katSeatBody ⟨katSeatEnvelope⟩ = true := by
  native_decide

/-- ⚑ THE KEYSTONE, handoff half: the honest handoff signature verifies. -/
theorem kat_handoff_signature_verifies_cross_language :
    handoffSignatureValidB katConfig katSeat0 katHandoffBody ⟨katHandoffEnvelope⟩ = true := by
  native_decide

/-- One seat's signed handoff, end to end through the kernel: the ML-DSA-65
seat admission mints the capability (`authenticateSeat?`), the briefing opens,
and `execute` ACCEPTS the ML-DSA-65-signed handoff and advances the mission to
sequence 1 (not yet complete — three seats remain).  This is the smallest real
crew action, judged by the kernel under real cryptography. -/
def katFirstHandoffExecutesB : Bool :=
  match authenticateSeat? katConfig ⟨0⟩ ⟨katSeatEnvelope⟩ with
  | none => false
  | some capability =>
    match briefingFor? katConfig capability with
    | none => false
    | some briefing =>
      match execute katConfig katState ⟨capability, briefing, katHandoffBody,
          ⟨katHandoffEnvelope⟩⟩ with
      | .error _ => false
      | .ok result =>
          decide (result.state.snapshot.sequence = 1) &&
          decide (result.completion = none)

theorem kat_one_seats_signed_handoff_is_executed_by_the_kernel :
    katFirstHandoffExecutesB = true := by native_decide

/-- Refutation: one flipped byte in the ML-DSA signature half of the envelope,
asserted a real mutation, refused by `verifyCore`. -/
private def katTamperedEnvelope : SignatureBytes :=
  { katHandoffEnvelope with
    bytes := katHandoffEnvelope.bytes.set (MLDSA65_PUBLIC_KEY_BYTE_LENGTH + 100)
      ((katHandoffEnvelope.bytes.getD (MLDSA65_PUBLIC_KEY_BYTE_LENGTH + 100) 0) + 1)
    length_eq := by rw [List.length_set]; exact katHandoffEnvelope.length_eq }

theorem kat_tampered_signature_byte_is_refused :
    katTamperedEnvelope.bytes ≠ katHandoffEnvelope.bytes ∧
    handoffSignatureValidB katConfig katSeat0 katHandoffBody ⟨katTamperedEnvelope⟩ = false := by
  native_decide

/-- ⚑ Refutation with a GENUINE signature: the wrong-key envelope carries a
signature that `verifyCore` itself ACCEPTS under its own public key (first
conjunct — the signature is not broken), and the crew verifier still refuses
it for seat 0 (second conjunct).  Together with
`kat_wrong_public_key_digest_is_not_the_seat_key`, the refusal is the
two-source `SHAKE256(pk) = playerKey` pin doing its work — the case a
self-pinned verifier could never catch. -/
theorem kat_wrong_key_signature_is_genuine_but_refused_by_the_key_pin :
    Dregg2.Crypto.MlDsaVerifyReal.verifyCore katWrongPublicKeyBytes katHandoffMessage
      HANDOFF_SIGNING_CONTEXT.toUTF8.toList
      CrewSigningVectors.katWrongKeyHandoffSignature.toList = true ∧
    handoffSignatureValidB katConfig katSeat0 katHandoffBody ⟨katWrongKeyEnvelope⟩ = false := by
  native_decide

/-- Refutation: the honest signature does not transfer to a different body —
one counter increment, asserted different, refused. -/
private def katTamperedBody : HandoffBody :=
  { katHandoffBody with counter := katHandoffBody.counter + 1 }

theorem kat_signature_does_not_transfer_to_a_different_body :
    katTamperedBody ≠ katHandoffBody ∧
    handoffSignatureValidB katConfig katSeat0 katTamperedBody ⟨katHandoffEnvelope⟩ = false := by
  native_decide

/-- Refutation: signature-level domain separation — the genuine SEAT-admission
envelope is refused as a HANDOFF signature (distinct FIPS 204 `ctx`, distinct
preimage format). -/
theorem kat_seat_admission_envelope_is_refused_as_a_handoff :
    handoffSignatureValidB katConfig katSeat0 katHandoffBody ⟨katSeatEnvelope⟩ = false := by
  native_decide

/-! ### The step surface under real cryptography

Everything above about `nextSigningPreimage?` was checked in the fixture world,
whose verifier is a publicly computable pattern.  Here the same surface is
driven by a seal `activate?` produced — so it cannot be a fixture seal, by
`production_activation_refuses_the_fixture_suite_config` — with seat 0's REAL
ML-DSA-65 admission envelope as the authenticator. -/

private def katRunSeal? : Option RunSeal := activate? katRawConfig fixtureBriefings

/-- ⚑ THE COMPLETABLE HANDOFF, END TO END.  Seat 0 presents the ML-DSA-65
admission envelope the `fips204` crate produced; the surface returns the
preimage; its message bytes are EXACTLY the bytes that crate signed
(`katHandoffMessagePinned`, independently pinned as
`kat_messages_are_the_pinned_bytes`); the signature over those bytes verifies
through the real FIPS 204 verify; and the kernel executes the resulting handoff
to sequence 1.

That is the whole loop a live seat performs, with nothing computed twice: the
client never derives `preRoot`, never assembles a body, and never re-encodes a
preimage — it signs the bytes it was handed.  A drift in the encoder, the
transition, or the surface breaks it here. -/
def katStepSurfaceHandsBackTheSignedBytesB : Bool :=
  match katRunSeal? with
  | none => false
  | some katSeal =>
    match katSeal.nextSigningPreimage? [] ⟨katSeatEnvelope⟩
        (.specialist .signalGallery .chartPressureRoute) with
    | none => false
    | some preimage =>
        decide (handoffPreimageMessage preimage =
          CrewSigningVectors.katHandoffMessagePinned.toList) &&
        decide (preimage.body = katHandoffBody) &&
        handoffSignatureValidB katConfig katSeat0 preimage.body ⟨katHandoffEnvelope⟩ &&
        (match authenticateSeat? katConfig ⟨0⟩ ⟨katSeatEnvelope⟩ with
         | none => false
         | some capability =>
           match briefingFor? katConfig capability with
           | none => false
           | some briefing =>
             match execute katConfig katState
                 ⟨capability, briefing, preimage.body, ⟨katHandoffEnvelope⟩⟩ with
             | .error _ => false
             | .ok result => decide (result.state.snapshot.sequence = 1))

theorem kat_step_surface_hands_back_exactly_the_bytes_the_crate_signed :
    katStepSurfaceHandsBackTheSignedBytesB = true := by native_decide

/-- The production surface refuses a caller who is not the seat: the wrong
keypair's envelope is a GENUINE ML-DSA-65 seat signature (it verifies under its
own key) and it still opens nothing, because `authenticateSeat?` runs the same
`SHAKE256(pk) = playerKey` pin.  Control in the same statement: seat 0's own
envelope does open it. -/
def katStepSurfaceRefusesAWrongKeyEnvelopeB : Bool :=
  match katRunSeal? with
  | none => false
  | some katSeal =>
    let decision : Decision := .specialist .signalGallery .chartPressureRoute
    (katSeal.nextSigningPreimage? [] ⟨katWrongKeyEnvelope⟩ decision).isNone &&
    (katSeal.nextSigningPreimage? [] ⟨katSeatEnvelope⟩ decision).isSome

theorem kat_step_surface_refuses_a_genuine_signature_under_the_wrong_key :
    katStepSurfaceRefusesAWrongKeyEnvelopeB = true := by native_decide

#assert_compiled observation_codes_are_injective
#assert_compiled decision_codes_are_injective
#assert_compiled shake_digest_lengths_hold_on_instances
#assert_compiled production_suite_ids_are_distinct_and_not_the_fixture_ids
#assert_compiled kat_player_key_is_the_seat0_public_key_digest
#assert_compiled kat_wrong_public_key_digest_is_not_the_seat_key
#assert_compiled kat_config_valid
#assert_compiled production_activation_seals_the_kat_mission
#assert_compiled production_activation_refuses_the_fixture_suite_config
#assert_compiled kat_envelopes_are_exact
#assert_compiled kat_messages_are_the_pinned_bytes
#assert_compiled kat_seat_admission_signature_verifies_cross_language
#assert_compiled kat_handoff_signature_verifies_cross_language
#assert_compiled kat_one_seats_signed_handoff_is_executed_by_the_kernel
#assert_compiled kat_tampered_signature_byte_is_refused
#assert_compiled kat_wrong_key_signature_is_genuine_but_refused_by_the_key_pin
#assert_compiled kat_signature_does_not_transfer_to_a_different_body
#assert_compiled kat_seat_admission_envelope_is_refused_as_a_handoff
#assert_compiled kat_step_surface_hands_back_exactly_the_bytes_the_crate_signed
#assert_compiled kat_step_surface_refuses_a_genuine_signature_under_the_wrong_key

end ProductionSigning

end Dregg2.Games.PathOfAngels.CrewFieldMission
