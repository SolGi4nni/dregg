/-
# CrewRelayExpedition — asynchronous signed expedition handoffs

This is a 2–4 seat cooperative deck-expedition protocol.  It is deliberately a
cross-cell authority stress test rather than a local puzzle with multiplayer
labels painted over it:

* the exact validated deck configuration and expedition key are retained in the
  session digest;
* every roster seat has a unique player key and credential and receives an
  authenticated, role-exact capability;
* every handoff is signed separately over the exact session, generation,
  sequence, semantic pre-state root, seat, command, and per-seat counter;
* a seat acts at most once per generation and cannot widen its authored role;
* abort is terminal until seat zero signs a bounded restart, which advances the
  generation without rewinding any seat counter or the global transcript;
* extraction deterministically combines the complete signed trace into one
  record; and
* the world contribution can reach a canonical settlement candidate only through
  the private completed-relay capability emitted at that terminal transition and
  an exact compare-and-swap settlement head.

The signature verifiers are an authenticated deployment boundary, not public
configuration fields.  `Config` has no public constructor or verifier-injection
producer: wiring a production signature suite remains an explicit tier-zero
integration obligation.  The fixtures use an internal, explicitly
non-cryptographic deterministic verifier; it tests the protocol semantics, not a
shadow signature scheme.
-/
import Dregg2.Games.PathOfAngels.DeckExpedition
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.CrewRelayExpedition

open Dregg2.Games.PathOfAngels

set_option autoImplicit false

abbrev MIN_SEATS : Nat := 2
abbrev MAX_SEATS : Nat := 4
abbrev MAX_RESTARTS : Nat := 2
abbrev MAX_RELAY_OPERATIONS : Nat := 24
abbrev MAX_RELAY_SUPPLIES : Nat := 32

structure SeatId where
  value : Nat
deriving Repr, DecidableEq

structure CredentialId where
  value : Nat
deriving Repr, DecidableEq

inductive CrewRole where
  | pathfinder
  | engineer
  | containment
  | quartermaster
deriving Repr, DecidableEq

/-- A singleton role grant.  There is no role-set field that a client can widen. -/
structure Seat where
  id : SeatId
  playerKey : Digest32
  credential : CredentialId
  role : CrewRole
  initialCounter : Nat
deriving DecidableEq

def seatIds (roster : List Seat) : List SeatId := roster.map Seat.id
def seatPlayers (roster : List Seat) : List Digest32 := roster.map Seat.playerKey
def seatCredentials (roster : List Seat) : List CredentialId := roster.map Seat.credential

def seatById? : List Seat → SeatId → Option Seat
  | [], _ => none
  | seat :: seats, id => if seat.id = id then some seat else seatById? seats id

/-! ## Exact activated-deck and session identity -/

/-- Proof-free exact image of the validated expedition configuration.  Its
constructor is private: callers can retain and compare this image, but only a
validated `DeckExpedition.Config` can produce one. -/
structure DeckBinding where
  private mk ::
  pack : DeckGraph.Pack
  policy : ActivityOutcome.Policy
  day : EpochId
  officers : List DeckExpedition.OfficerProfile
  hazards : List DeckExpedition.HazardSpec
  salvage : List DeckExpedition.SalvageSpec
  discoveries : List DeckExpedition.DiscoverySpec
  dailyRunBudget : Nat
  turnBudget : Nat
  operationalSupplyBudget : Nat
  baseContribution : Contribution
deriving DecidableEq

def DeckBinding.ofExpedition (config : DeckExpedition.Config) : DeckBinding where
  pack := config.raw.graph.pack
  policy := config.raw.policy
  day := config.raw.day
  officers := config.raw.officers
  hazards := config.raw.hazards
  salvage := config.raw.salvage
  discoveries := config.raw.discoveries
  dailyRunBudget := config.raw.dailyRunBudget
  turnBudget := config.raw.turnBudget
  operationalSupplyBudget := config.raw.operationalSupplyBudget
  baseContribution := config.raw.baseContribution

def DeckBinding.packKey (deck : DeckBinding) : DeckExpedition.PackKey where
  packId := deck.pack.packId
  activation := deck.pack.activation

inductive Strategy where
  | survey
  | salvage
deriving Repr, DecidableEq

/-- Each role has one move in either strategy.  Constructors, rather than a
caller-owned role field, make the role surface finite and auditable. -/
inductive Command where
  | chartPressureRoute
  | markSalvageRoute
  | braceTransit
  | overdriveCargoLift
  | quietAnomaly
  | screenRecovery
  | bankSupplies
  | secureCache
  | abort
  | restart
deriving Repr, DecidableEq

def Command.role? : Command → Option CrewRole
  | .chartPressureRoute | .markSalvageRoute => some .pathfinder
  | .braceTransit | .overdriveCargoLift => some .engineer
  | .quietAnomaly | .screenRecovery => some .containment
  | .bankSupplies | .secureCache => some .quartermaster
  | .abort | .restart => none

def Command.strategy? : Command → Option Strategy
  | .chartPressureRoute | .braceTransit | .quietAnomaly | .bankSupplies => some .survey
  | .markSalvageRoute | .overdriveCargoLift | .screenRecovery | .secureCache => some .salvage
  | .abort | .restart => none

def Command.code : Command → Nat
  | .chartPressureRoute => 0
  | .markSalvageRoute => 1
  | .braceTransit => 2
  | .overdriveCargoLift => 3
  | .quietAnomaly => 4
  | .screenRecovery => 5
  | .bankSupplies => 6
  | .secureCache => 7
  | .abort => 8
  | .restart => 9

structure RawConfig where
  deck : DeckBinding
  expeditionKey : DeckExpedition.ExpeditionKey
  actorRoot : Digest32
  relayId : Digest32
  roster : List Seat
  operationBudget : Nat
  restartBudget : Nat
  initialSupplies : Nat
  surveyOutcome : ActivityOutcome.Raw
  salvageOutcome : ActivityOutcome.Raw
deriving DecidableEq

/-- Full-width semantic session digest.  A wire hash may commit to this object,
but equality here never replaces it with a lossy arithmetic fold. -/
structure SessionDigest where
  deck : DeckBinding
  expeditionKey : DeckExpedition.ExpeditionKey
  actorRoot : Digest32
  relayId : Digest32
  roster : List Seat
  operationBudget : Nat
  restartBudget : Nat
  initialSupplies : Nat
  surveyOutcome : ActivityOutcome.Raw
  salvageOutcome : ActivityOutcome.Raw
deriving DecidableEq

def RawConfig.sessionDigest (raw : RawConfig) : SessionDigest where
  deck := raw.deck
  expeditionKey := raw.expeditionKey
  actorRoot := raw.actorRoot
  relayId := raw.relayId
  roster := raw.roster
  operationBudget := raw.operationBudget
  restartBudget := raw.restartBudget
  initialSupplies := raw.initialSupplies
  surveyOutcome := raw.surveyOutcome
  salvageOutcome := raw.salvageOutcome

def rosterNumberedB (roster : List Seat) : Bool :=
  decide (roster.map (fun seat => seat.id.value) = List.range roster.length)

def rawConfigValidB (raw : RawConfig) : Bool :=
  decide (MIN_SEATS ≤ raw.roster.length) &&
  decide (raw.roster.length ≤ MAX_SEATS) &&
  rosterNumberedB raw.roster &&
  decide (seatIds raw.roster).Nodup &&
  decide (seatPlayers raw.roster).Nodup &&
  decide (seatCredentials raw.roster).Nodup &&
  raw.roster.all (fun seat =>
    decide (seat.initialCounter + (2 * raw.restartBudget + 1) < PLAYER_COUNTER_MODULUS)) &&
  decide (raw.expeditionKey.pack = raw.deck.packKey) &&
  decide (raw.expeditionKey.day = raw.deck.day) &&
  decide (0 < raw.expeditionKey.counter) &&
  decide (raw.expeditionKey.counter < PLAYER_COUNTER_MODULUS) &&
  decide (raw.roster.length ≤ raw.operationBudget) &&
  decide (raw.roster.length * (raw.restartBudget + 1) + raw.restartBudget ≤
    raw.operationBudget) &&
  decide (raw.operationBudget ≤ MAX_RELAY_OPERATIONS) &&
  decide (raw.restartBudget ≤ MAX_RESTARTS) &&
  decide (raw.roster.length ≤ raw.initialSupplies) &&
  decide (raw.initialSupplies ≤ MAX_RELAY_SUPPLIES) &&
  (ActivityOutcome.validate raw.deck.policy raw.surveyOutcome).isSome &&
  (ActivityOutcome.validate raw.deck.policy raw.salvageOutcome).isSome &&
  decide (raw.surveyOutcome ≠ raw.salvageOutcome)

/-! ## Authenticated seats and separately signed handoffs -/

structure SeatAdmissionBody where
  session : SessionDigest
  seat : Seat
deriving DecidableEq

structure SeatSignature where
  value : Nat
deriving Repr, DecidableEq

structure TurnSignature where
  value : Nat
deriving Repr, DecidableEq

inductive RelayPhase where
  | active
  | aborted
  | extracted
deriving Repr, DecidableEq

structure SeatCounter where
  seat : SeatId
  counter : Nat
deriving Repr, DecidableEq

structure TurnTrace where
  generation : Nat
  sequence : Nat
  seat : Seat
  previousCounter : Nat
  counter : Nat
  command : Command
  seatSignature : SeatSignature
  signature : TurnSignature
deriving DecidableEq

/-- The complete replayable semantic state, excluding only its redundant root. -/
structure StateSnapshot where
  phase : RelayPhase
  generation : Nat
  sequence : Nat
  nextSeat : Nat
  seatCounters : List SeatCounter
  usedSeats : Finset SeatId
  strategy : Option Strategy
  surveyProgress : Nat
  salvageProgress : Nat
  supplies : Nat
  restartsUsed : Nat
  transcript : List TurnTrace
deriving DecidableEq

/-- Exact semantic root.  This is intentionally a full object, not a digest with
an assumed collision theorem. -/
structure StateRoot where
  session : SessionDigest
  snapshot : StateSnapshot
deriving DecidableEq

structure TurnBody where
  session : SessionDigest
  generation : Nat
  sequence : Nat
  preRoot : StateRoot
  seat : Seat
  previousCounter : Nat
  counter : Nat
  command : Command
deriving DecidableEq

/-- Activated verifier selection is an authority boundary.  In particular,
callers cannot rebuild the same `RawConfig` with `fun _ _ _ => true`: the
constructor is private and this module deliberately exposes no raw verifier
injection function.  A deployment adapter must authenticate its verifier suite
before producing this opaque value. -/
structure Config where
  private mk ::
  raw : RawConfig
  verifySeat : CredentialId → SeatAdmissionBody → SeatSignature → Bool
  verifyTurn : CredentialId → TurnBody → TurnSignature → Bool
  valid : rawConfigValidB raw = true

/-- Exact authority to start this configured relay.  Its constructor is private
and there is intentionally no public minting function yet: a production node
must obtain one from the future canonical run-admission/CAS adapter.  This is a
typed tier-zero blocker, not a claim that pure Lean values are linear. -/
structure CanonicalRunAdmission (config : Config) where
  private mk ::
  session : SessionDigest
  exactSession : session = config.raw.sessionDigest

def expectedAdmission (config : Config) (seat : Seat) : SeatAdmissionBody where
  session := config.raw.sessionDigest
  seat

/-- Opaque authenticated roster authority.  It carries exactly one authored
seat, and hence exactly one role. -/
structure SeatCapability (config : Config) where
  private mk ::
  seat : Seat
  admission : SeatAdmissionBody
  signature : SeatSignature
  authenticated : config.verifySeat seat.credential admission signature = true
deriving DecidableEq

def authenticateSeat? (config : Config) (id : SeatId)
    (signature : SeatSignature) : Option (SeatCapability config) := do
  let seat ← seatById? config.raw.roster id
  let admission := expectedAdmission config seat
  if h : config.verifySeat seat.credential admission signature = true then
    some ⟨seat, admission, signature, h⟩
  else none

structure SignedTurn (config : Config) where
  capability : SeatCapability config
  body : TurnBody
  signature : TurnSignature
deriving DecidableEq

structure State where
  private mk ::
  snapshot : StateSnapshot
  root : StateRoot
deriving DecidableEq

def rootFor (config : Config) (snapshot : StateSnapshot) : StateRoot where
  session := config.raw.sessionDigest
  snapshot

def initialCounters (roster : List Seat) : List SeatCounter :=
  roster.map fun seat => ⟨seat.id, seat.initialCounter⟩

def initialSnapshot (config : Config) : StateSnapshot where
  phase := .active
  generation := 0
  sequence := 0
  nextSeat := 0
  seatCounters := initialCounters config.raw.roster
  usedSeats := ∅
  strategy := none
  surveyProgress := 0
  salvageProgress := 0
  supplies := config.raw.initialSupplies
  restartsUsed := 0
  transcript := []

private def initialState (config : Config) : State :=
  let snapshot := initialSnapshot config
  ⟨snapshot, rootFor config snapshot⟩

/-- Sole public run initializer.  The opaque admission is expected to be issued
against a serialized canonical run registry; this module does not pretend that
copying an immutable Lean value performs global consumption. -/
def start {config : Config} (_admission : CanonicalRunAdmission config) : State :=
  initialState config

def counterFor? : List SeatCounter → SeatId → Option Nat
  | [], _ => none
  | counter :: counters, id =>
      if counter.seat = id then some counter.counter else counterFor? counters id

def setCounter (counters : List SeatCounter) (id : SeatId) (value : Nat) : List SeatCounter :=
  counters.map fun counter => if counter.seat = id then { counter with counter := value } else counter

def expectedSeat? (config : Config) (state : State) : Option Seat :=
  match state.snapshot.phase with
  | .active => config.raw.roster[state.snapshot.nextSeat]?
  | .aborted => config.raw.roster[0]?
  | .extracted => none

def usedPrefix (config : Config) (nextSeat : Nat) : Finset SeatId :=
  ((config.raw.roster.take nextSeat).map Seat.id).toFinset

def countersShapeB (config : Config) (snapshot : StateSnapshot) : Bool :=
  decide (snapshot.seatCounters.map SeatCounter.seat = seatIds config.raw.roster) &&
  snapshot.seatCounters.all (fun counter => decide (counter.counter < PLAYER_COUNTER_MODULUS))

def progressValidB (config : Config) (snapshot : StateSnapshot) : Bool :=
  decide (snapshot.surveyProgress + snapshot.salvageProgress ≤ snapshot.nextSeat) &&
  decide (snapshot.supplies + snapshot.salvageProgress = config.raw.initialSupplies) &&
  match snapshot.phase with
  | .aborted => true
  | .active | .extracted =>
      decide (snapshot.surveyProgress + snapshot.salvageProgress = snapshot.nextSeat) &&
      match snapshot.strategy with
      | none => decide (snapshot.nextSeat = 0)
      | some .survey => decide (snapshot.surveyProgress = snapshot.nextSeat)
      | some .salvage => decide (snapshot.salvageProgress = snapshot.nextSeat)

def phaseValidB (config : Config) (snapshot : StateSnapshot) : Bool :=
  match snapshot.phase with
  | .active => decide (snapshot.nextSeat < config.raw.roster.length)
  | .aborted => decide (snapshot.nextSeat ≤ config.raw.roster.length)
  | .extracted => decide (snapshot.nextSeat = config.raw.roster.length)

def stateValidB (config : Config) (state : State) : Bool :=
  decide (state.root = rootFor config state.snapshot) &&
  decide (state.snapshot.sequence = state.snapshot.transcript.length) &&
  decide (state.snapshot.sequence ≤ config.raw.operationBudget) &&
  decide (state.snapshot.generation = state.snapshot.restartsUsed) &&
  decide (state.snapshot.restartsUsed ≤ config.raw.restartBudget) &&
  decide (state.snapshot.nextSeat ≤ config.raw.roster.length) &&
  decide (state.snapshot.usedSeats = usedPrefix config state.snapshot.nextSeat) &&
  countersShapeB config state.snapshot &&
  progressValidB config state.snapshot &&
  phaseValidB config state.snapshot

def expectedTurnBody (config : Config) (state : State)
    (capability : SeatCapability config) (command : Command) : Option TurnBody := do
  let previousCounter ← counterFor? state.snapshot.seatCounters capability.seat.id
  some {
    session := config.raw.sessionDigest
    generation := state.snapshot.generation
    sequence := state.snapshot.sequence
    preRoot := state.root
    seat := capability.seat
    previousCounter
    counter := previousCounter + 1
    command
  }

inductive Refusal where
  | invalidState
  | invalidSuccessor
  | operationBudgetExhausted
  | terminal
  | restartRequired
  | restartOnlyAfterAbort
  | restartAuthority
  | restartBudgetExhausted
  | capabilityMismatch
  | wrongSeat
  | seatAlreadyUsed
  | wrongSession
  | staleGeneration
  | staleSequence
  | staleRoot
  | bodySeatMismatch
  | seatCounterMismatch
  | seatCounterOutOfRange
  | signatureRefused
  | roleWidening
  | strategyConflict
  | insufficientSupplies
  | outcomeRefused
deriving Repr, DecidableEq

def capabilityMatchesB (config : Config) (capability : SeatCapability config) : Bool :=
  decide (seatById? config.raw.roster capability.seat.id = some capability.seat) &&
  decide (capability.admission = expectedAdmission config capability.seat)

def strategyCompatibleB (current : Option Strategy) (command : Command) : Bool :=
  match current, command.strategy? with
  | _, none => true
  | none, some _ => true
  | some left, some right => decide (left = right)

def roleExactB (seat : Seat) (command : Command) : Bool :=
  match command.role? with
  | none => true
  | some role => decide (seat.role = role)

def traceOf {config : Config} (turn : SignedTurn config) : TurnTrace where
  generation := turn.body.generation
  sequence := turn.body.sequence
  seat := turn.body.seat
  previousCounter := turn.body.previousCounter
  counter := turn.body.counter
  command := turn.body.command
  seatSignature := turn.capability.signature
  signature := turn.signature

private def committedBase {config : Config} (state : State)
    (turn : SignedTurn config) : StateSnapshot :=
  { state.snapshot with
    sequence := state.snapshot.sequence + 1
    seatCounters := setCounter state.snapshot.seatCounters turn.body.seat.id turn.body.counter
    transcript := state.snapshot.transcript ++ [traceOf turn] }

private def transition (config : Config) (state : State)
    (turn : SignedTurn config) : State :=
  let base := committedBase state turn
  match turn.body.command with
  | .restart =>
      let snapshot : StateSnapshot := {
        base with
        phase := .active
        generation := state.snapshot.generation + 1
        nextSeat := 0
        usedSeats := ∅
        strategy := none
        surveyProgress := 0
        salvageProgress := 0
        supplies := config.raw.initialSupplies
        restartsUsed := state.snapshot.restartsUsed + 1
      }
      ⟨snapshot, rootFor config snapshot⟩
  | .abort =>
      let snapshot : StateSnapshot := {
        base with
        phase := .aborted
        nextSeat := state.snapshot.nextSeat + 1
        usedSeats := insert turn.body.seat.id state.snapshot.usedSeats
      }
      ⟨snapshot, rootFor config snapshot⟩
  | command =>
      let strategy := command.strategy?.getD .survey
      let nextSeat := state.snapshot.nextSeat + 1
      let terminal := nextSeat = config.raw.roster.length
      let snapshot : StateSnapshot := {
        base with
        phase := if terminal then .extracted else .active
        nextSeat
        usedSeats := insert turn.body.seat.id state.snapshot.usedSeats
        strategy := some strategy
        surveyProgress := state.snapshot.surveyProgress + if strategy = .survey then 1 else 0
        salvageProgress := state.snapshot.salvageProgress + if strategy = .salvage then 1 else 0
        supplies := state.snapshot.supplies - if strategy = .salvage then 1 else 0
      }
      ⟨snapshot, rootFor config snapshot⟩

/-! ## Opaque completion and contribution boundary -/

structure CombinedExtractionRecord (config : Config) where
  private mk ::
  session : SessionDigest
  generation : Nat
  strategy : Strategy
  roster : List Seat
  turns : List TurnTrace
  completedSeats : Finset SeatId
  finalSeatCounters : List SeatCounter
  finalRoot : StateRoot
  outcome : ActivityOutcome.Checked config.raw.deck.policy
deriving DecidableEq

/-- Wire-shaped terminal record.  Unlike `CombinedExtractionRecord`, every
field here is caller-controlled.  It confers no authority until the strict
decoder below replays all admission and turn signatures from the exact initial
root and checks every claimed terminal field. -/
structure RawCombinedExtractionRecord where
  session : SessionDigest
  generation : Nat
  strategy : Strategy
  roster : List Seat
  turns : List TurnTrace
  completedSeats : Finset SeatId
  finalSeatCounters : List SeatCounter
  finalRoot : StateRoot
  outcome : ActivityOutcome.Raw
deriving DecidableEq

structure CompletedRelayCapability (config : Config) where
  private mk ::
  record : CombinedExtractionRecord config
deriving DecidableEq

private def completedCapability? (config : Config) (state : State) :
    Option (CompletedRelayCapability config) := do
  if state.snapshot.phase = .extracted then
    let strategy ← state.snapshot.strategy
    let raw := match strategy with
      | .survey => config.raw.surveyOutcome
      | .salvage => config.raw.salvageOutcome
    let outcome ← ActivityOutcome.validate config.raw.deck.policy raw
    some ⟨{
      session := config.raw.sessionDigest
      generation := state.snapshot.generation
      strategy
      roster := config.raw.roster
      turns := state.snapshot.transcript
      completedSeats := state.snapshot.usedSeats
      finalSeatCounters := state.snapshot.seatCounters
      finalRoot := state.root
      outcome
    }⟩
  else none

structure StepResult (config : Config) where
  private mk ::
  state : State
  completion : Option (CompletedRelayCapability config)
deriving DecidableEq

/-- Sole turn transition.  Every accepted row authenticates one exact seat and
one exact pre-state, consumes one global sequence and one per-seat counter, then
checks the complete successor invariant before exposing any completion. -/
def execute (config : Config) (state : State)
    (turn : SignedTurn config) : Except Refusal (StepResult config) :=
  if stateValidB config state ≠ true then .error .invalidState
  else if config.raw.operationBudget ≤ state.snapshot.sequence then
    .error .operationBudgetExhausted
  else if state.snapshot.phase = .extracted then .error .terminal
  else if turn.body.command = .restart && state.snapshot.phase ≠ .aborted then
    .error .restartOnlyAfterAbort
  else if state.snapshot.phase = .aborted && turn.body.command ≠ .restart then
    .error .restartRequired
  else if turn.body.command = .restart && turn.capability.seat.id ≠ ⟨0⟩ then
    .error .restartAuthority
  else if turn.body.command = .restart &&
      config.raw.restartBudget ≤ state.snapshot.restartsUsed then
    .error .restartBudgetExhausted
  else if capabilityMatchesB config turn.capability ≠ true then .error .capabilityMismatch
  else match expectedSeat? config state with
    | none => .error .terminal
    | some expected =>
      if state.snapshot.phase = .active &&
          turn.capability.seat.id ∈ state.snapshot.usedSeats then .error .seatAlreadyUsed
      else if turn.capability.seat ≠ expected then .error .wrongSeat
      else if turn.body.session ≠ config.raw.sessionDigest then .error .wrongSession
      else if turn.body.generation ≠ state.snapshot.generation then .error .staleGeneration
      else if turn.body.sequence ≠ state.snapshot.sequence then .error .staleSequence
      else if turn.body.preRoot ≠ state.root then .error .staleRoot
      else if turn.body.seat ≠ turn.capability.seat then .error .bodySeatMismatch
      else match counterFor? state.snapshot.seatCounters turn.capability.seat.id with
        | none => .error .invalidState
        | some previous =>
          if turn.body.previousCounter ≠ previous ∨
              turn.body.counter ≠ turn.body.previousCounter + 1 then
            .error .seatCounterMismatch
          else if PLAYER_COUNTER_MODULUS ≤ turn.body.counter then
            .error .seatCounterOutOfRange
          else if config.verifyTurn turn.capability.seat.credential
              turn.body turn.signature ≠ true then .error .signatureRefused
          else if roleExactB turn.capability.seat turn.body.command ≠ true then
            .error .roleWidening
          else if strategyCompatibleB state.snapshot.strategy turn.body.command ≠ true then
            .error .strategyConflict
          else if turn.body.command.strategy? = some .salvage &&
              state.snapshot.supplies = 0 then .error .insufficientSupplies
          else
            let successor := transition config state turn
            if stateValidB config successor ≠ true then .error .invalidSuccessor
            else
              let completion := completedCapability? config successor
              if successor.snapshot.phase = .extracted && completion.isNone then
                .error .outcomeRefused
              else .ok ⟨successor, completion⟩

def replay (config : Config) : State → List (SignedTurn config) →
    Except Refusal (StepResult config)
  | state, [] => .ok ⟨state, completedCapability? config state⟩
  | state, turn :: turns => do
      let result ← execute config state turn
      match turns with
      | [] => .ok result
      | _ => replay config result.state turns

/-- Reconstruct one exact signed turn from its compact trace and the unique
pre-state.  Both signatures are retained: the admission signature remints the
same singleton seat capability, and `execute` verifies the turn signature over
the reconstructed body/root. -/
def signedTurnFromTrace? (config : Config) (state : State)
    (trace : TurnTrace) : Option (SignedTurn config) := do
  let capability ← authenticateSeat? config trace.seat.id trace.seatSignature
  let body ← expectedTurnBody config state capability trace.command
  let turn : SignedTurn config := ⟨capability, body, trace.signature⟩
  if traceOf turn = trace then some turn else none

/-- Independent transcript verifier for serialized combined records. -/
def replayTrace? (config : Config) : State → List TurnTrace → Option State
  | state, [] => some state
  | state, trace :: traces => do
      let turn ← signedTurnFromTrace? config state trace
      match execute config state turn with
      | .error _ => none
      | .ok result => replayTrace? config result.state traces

def expectedOutcome? (config : Config) (strategy : Strategy) :
    Option (ActivityOutcome.Checked config.raw.deck.policy) :=
  ActivityOutcome.validate config.raw.deck.policy <| match strategy with
    | .survey => config.raw.surveyOutcome
    | .salvage => config.raw.salvageOutcome

/-- A wire-decoded record is accepted only if all separately signed turns replay
from the exact initial root to every terminal field it claims. -/
def CombinedExtractionRecord.validB {config : Config}
    (record : CombinedExtractionRecord config) : Bool :=
  match replayTrace? config (initialState config) record.turns,
      expectedOutcome? config record.strategy with
  | some final, some outcome =>
      decide (final.snapshot.phase = .extracted) &&
      decide (final.snapshot.strategy = some record.strategy) &&
      decide (record.session = config.raw.sessionDigest) &&
      decide (record.generation = final.snapshot.generation) &&
      decide (record.roster = config.raw.roster) &&
      decide (record.completedSeats = final.snapshot.usedSeats) &&
      decide (record.finalSeatCounters = final.snapshot.seatCounters) &&
      decide (record.finalRoot = final.root) &&
      decide (record.outcome = outcome)
  | _, _ => false

def CombinedExtractionRecord.toRaw {config : Config}
    (record : CombinedExtractionRecord config) : RawCombinedExtractionRecord where
  session := record.session
  generation := record.generation
  strategy := record.strategy
  roster := record.roster
  turns := record.turns
  completedSeats := record.completedSeats
  finalSeatCounters := record.finalSeatCounters
  finalRoot := record.finalRoot
  outcome := match record.strategy with
    | .survey => config.raw.surveyOutcome
    | .salvage => config.raw.salvageOutcome

/-- Strict wire admission.  Exact replay alone is only an offline candidate:
recovering an authoritative record additionally requires the opaque canonical
run admission that authorized this session. -/
def admitCombinedExtractionRecord? {config : Config}
    (admission : CanonicalRunAdmission config)
    (raw : RawCombinedExtractionRecord) : Option (CombinedExtractionRecord config) :=
  if raw.session ≠ admission.session then none
  else do
    let outcome ← ActivityOutcome.validate config.raw.deck.policy raw.outcome
    let record : CombinedExtractionRecord config := ⟨
      raw.session, raw.generation, raw.strategy, raw.roster, raw.turns,
      raw.completedSeats, raw.finalSeatCounters, raw.finalRoot, outcome⟩
    if record.validB then some record else none

/-- A valid serialized relay plus its canonical run admission can recover the
same opaque completion authority.  A fully signed offline transcript without
that admission cannot invoke this producer. -/
def admitCompletedRelay? {config : Config}
    (admission : CanonicalRunAdmission config)
    (raw : RawCombinedExtractionRecord) : Option (CompletedRelayCapability config) := do
  let record ← admitCombinedExtractionRecord? admission raw
  some ⟨record⟩

def CompletedRelayCapability.contribution {config : Config}
    (capability : CompletedRelayCapability config) : Contribution :=
  capability.record.outcome.contribution

/-! ## Canonical one-run settlement tooth -/

/-- Exact admitted-run identity consumed by canonical settlement.  The terminal
root remains bound in the record, but is deliberately *not* part of this key:
survey and salvage are competing outcomes of one admitted session, not two runs
that may both settle.  `SessionDigest` includes the exact relay id, expedition
key, roster, policy/deck image, budgets, and outcomes. -/
structure RelayRunKey where
  session : SessionDigest
deriving DecidableEq

def CombinedExtractionRecord.runKey {config : Config}
    (record : CombinedExtractionRecord config) : RelayRunKey :=
  ⟨record.session⟩

/-- Complete semantic CAS key for the relay settlement registry. -/
structure SettlementHead where
  world : WorldState
  consumedRuns : List RelayRunKey
  revision : Nat
deriving DecidableEq

structure SettlementState (config : Config) where
  private mk ::
  world : WorldState
  consumedRuns : List RelayRunKey
  revision : Nat
  noDuplicateRuns : consumedRuns.Nodup

def SettlementState.head {config : Config}
    (state : SettlementState config) : SettlementHead :=
  ⟨state.world, state.consumedRuns, state.revision⟩

/-- Externally provisioned genesis authority.  There is no public producer in
this module.  Deployment must serialize its first head and all successors. -/
structure CanonicalSettlementGenesis (config : Config) where
  private mk ::
  private authenticated : True

structure SettlementRegistry (config : Config) where
  private mk ::
  head : SettlementHead

/-- Open the semantic registry from tier-zero authority.  Reusing a copied
genesis in pure Lean can fork; the deployment obligation is an atomic creation
of this exact head, followed by CAS for every successor. -/
def SettlementRegistry.open {config : Config}
    (_genesis : CanonicalSettlementGenesis config)
    (world : WorldState) : SettlementRegistry config × SettlementState config :=
  let state : SettlementState config := ⟨world, [], 0, by simp⟩
  (⟨state.head⟩, state)

inductive SettlementRefusal where
  | staleCanonicalHead
  | runAlreadyConsumed
  | contributionRefused
deriving DecidableEq, Repr

/-- Exact settlement candidate authorized by the current canonical head.  The
node must atomically CAS `before.head` to `after.head`; this value alone does not
claim global finality. -/
structure SettlementTransition (config : Config) where
  private mk ::
  record : CombinedExtractionRecord config
  before : SettlementState config
  after : SettlementState config
  applied : applyContribution config.raw.deck.policy.mission
    record.outcome.contribution before.world = some after.world
  consumed : record.runKey ∈ after.consumedRuns

/-- The sole world-update path.  It consumes the exact run key in the returned
head and rejects both a stale observed head and a key already consumed by the
threaded canonical state.  The runtime supplies global exclusion by CASing the
registry head from `canonicalHead` to the returned head. -/
def SettlementRegistry.admitCompleted {config : Config}
    (registry : SettlementRegistry config) (canonicalHead : SettlementHead)
    (before : SettlementState config)
    (capability : CompletedRelayCapability config) :
    Except SettlementRefusal (SettlementRegistry config × SettlementTransition config) :=
  if registry.head ≠ canonicalHead then .error .staleCanonicalHead
  else if before.head ≠ canonicalHead then .error .staleCanonicalHead
  else if hconsumed : capability.record.runKey ∈ before.consumedRuns then
    .error .runAlreadyConsumed
  else match happlied : applyContribution config.raw.deck.policy.mission
      capability.record.outcome.contribution before.world with
    | none => .error .contributionRefused
    | some world =>
      let after : SettlementState config := {
        world
        consumedRuns := capability.record.runKey :: before.consumedRuns
        revision := before.revision + 1
        noDuplicateRuns := List.nodup_cons.mpr ⟨hconsumed, before.noDuplicateRuns⟩
      }
      .ok (⟨after.head⟩,
        ⟨capability.record, before, after, happlied, List.mem_cons_self⟩)

/-! ## General laws -/

theorem execute_deterministic (config : Config) (state : State)
    (turn : SignedTurn config) {first second : StepResult config}
    (hfirst : execute config state turn = .ok first)
    (hsecond : execute config state turn = .ok second) : first = second := by
  rw [hfirst] at hsecond
  exact Except.ok.inj hsecond

theorem replay_deterministic (config : Config) (state : State)
    (turns : List (SignedTurn config)) {first second : StepResult config}
    (hfirst : replay config state turns = .ok first)
    (hsecond : replay config state turns = .ok second) : first = second := by
  rw [hfirst] at hsecond
  exact Except.ok.inj hsecond

theorem completed_contribution_is_mission_admitted
    {config : Config} (capability : CompletedRelayCapability config) :
    config.raw.deck.policy.mission.acceptsContribution
      capability.contribution = true :=
  capability.record.outcome.contribution_accepted

theorem admitted_settlement_advances_world_sequence {config : Config}
    (transition : SettlementTransition config) :
    transition.after.world.sequence = transition.before.world.sequence + 1 :=
  applyContribution_sequence transition.applied

theorem admitted_settlement_consumes_exact_run {config : Config}
    (transition : SettlementTransition config) :
    transition.record.runKey ∈ transition.after.consumedRuns := by
  exact transition.consumed

theorem Config.roster_has_two_to_four_seats (config : Config) :
    MIN_SEATS ≤ config.raw.roster.length ∧ config.raw.roster.length ≤ MAX_SEATS := by
  have valid := config.valid
  simp only [rawConfigValidB, Bool.and_eq_true, decide_eq_true_eq] at valid
  aesop

/-! ## Strategic and hostile executable fixtures -/

def digestFilled (value : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨value % 256, Nat.mod_lt _ (by omega)⟩
  length_eq := by simp

def fixtureSeat0 : Seat := ⟨⟨0⟩, digestFilled 10, ⟨10⟩, .pathfinder, 10⟩
def fixtureSeat1 : Seat := ⟨⟨1⟩, digestFilled 11, ⟨11⟩, .engineer, 20⟩
def fixtureSeat2 : Seat := ⟨⟨2⟩, digestFilled 12, ⟨12⟩, .containment, 30⟩
def fixtureSeat3 : Seat := ⟨⟨3⟩, digestFilled 13, ⟨13⟩, .quartermaster, 40⟩

def fixtureRoster : List Seat := [fixtureSeat0, fixtureSeat1, fixtureSeat2, fixtureSeat3]

def fixtureSurveyOutcome : ActivityOutcome.Raw where
  contribution := {
    intel := 4
    supplies := 2
    cohesion := 4
    influence := 0
    score := 20
    relics := []
  }
  betaCandidates := [DeckExpedition.fixtureArtifact]

def fixtureSalvageOutcome : ActivityOutcome.Raw where
  contribution := {
    intel := 1
    supplies := 0
    cohesion := 2
    influence := 0
    score := 50
    relics := [DeckExpedition.fixtureRelic]
  }
  betaCandidates := [DeckExpedition.fixtureArtifact]

def fixtureRawConfig : RawConfig where
  deck := DeckBinding.ofExpedition DeckExpedition.fixtureConfig
  expeditionKey := DeckExpedition.fixtureKey
  actorRoot := digestFilled 70
  relayId := digestFilled 71
  roster := fixtureRoster
  operationBudget := 12
  restartBudget := 1
  initialSupplies := 4
  surveyOutcome := fixtureSurveyOutcome
  salvageOutcome := fixtureSalvageOutcome

private def seatSignatureValue (credential : CredentialId) (body : SeatAdmissionBody) : Nat :=
  credential.value * 100 + body.seat.id.value * 10 + body.session.roster.length

private def turnSignatureValue (credential : CredentialId) (body : TurnBody) : Nat :=
  credential.value * 100000 + body.generation * 10000 + body.sequence * 100 +
    body.command.code * 2 + body.counter % 2

private def fixtureVerifySeat (credential : CredentialId) (body : SeatAdmissionBody)
    (signature : SeatSignature) : Bool :=
  decide (body.seat.credential = credential) &&
  decide (signature.value = seatSignatureValue credential body)

private def fixtureVerifyTurn (credential : CredentialId) (body : TurnBody)
    (signature : TurnSignature) : Bool :=
  decide (body.seat.credential = credential) &&
  decide (signature.value = turnSignatureValue credential body)

theorem fixture_raw_config_valid : rawConfigValidB fixtureRawConfig = true := by
  native_decide

private def fixtureConfig : Config where
  raw := fixtureRawConfig
  verifySeat := fixtureVerifySeat
  verifyTurn := fixtureVerifyTurn
  valid := fixture_raw_config_valid

private def testRunAdmission (config : Config) : CanonicalRunAdmission config :=
  ⟨config.raw.sessionDigest, rfl⟩

private def testCapability? (config : Config) (id : SeatId) : Option (SeatCapability config) := do
  let seat ← seatById? config.raw.roster id
  let body := expectedAdmission config seat
  authenticateSeat? config id ⟨seatSignatureValue seat.credential body⟩

private def testTurn? (config : Config) (state : State) (id : SeatId)
    (command : Command) : Option (SignedTurn config) := do
  let capability ← testCapability? config id
  let body ← expectedTurnBody config state capability command
  some ⟨capability, body, ⟨turnSignatureValue capability.seat.credential body⟩⟩

private def driveTest (config : Config) : State → List (SeatId × Command) →
    Option (StepResult config)
  | state, [] => match replay config state [] with
      | .ok result => some result
      | .error _ => none
  | state, (id, command) :: commands => do
      let turn ← testTurn? config state id command
      match execute config state turn with
      | .error _ => none
      | .ok result =>
          match commands with
          | [] => some result
          | _ => driveTest config result.state commands

def surveyPlan : List (SeatId × Command) :=
  [ (⟨0⟩, .chartPressureRoute)
  , (⟨1⟩, .braceTransit)
  , (⟨2⟩, .quietAnomaly)
  , (⟨3⟩, .bankSupplies) ]

def salvagePlan : List (SeatId × Command) :=
  [ (⟨0⟩, .markSalvageRoute)
  , (⟨1⟩, .overdriveCargoLift)
  , (⟨2⟩, .screenRecovery)
  , (⟨3⟩, .secureCache) ]

private def completionFor? (config : Config) (plan : List (SeatId × Command)) :
    Option (CompletedRelayCapability config) := do
  let result ← driveTest config (start (testRunAdmission config)) plan
  result.completion

theorem survey_plan_completes : (completionFor? fixtureConfig surveyPlan).isSome = true := by
  native_decide

theorem salvage_plan_completes : (completionFor? fixtureConfig salvagePlan).isSome = true := by
  native_decide

def completedPlansAreMateriallyDistinctB : Bool :=
  match completionFor? fixtureConfig surveyPlan, completionFor? fixtureConfig salvagePlan with
  | some survey, some salvage =>
      decide (survey.record.strategy = .survey) &&
      decide (salvage.record.strategy = .salvage) &&
      decide (survey.contribution ≠ salvage.contribution) &&
      decide (DeckExpedition.fixtureRelic ∉ survey.contribution.relics) &&
      decide (DeckExpedition.fixtureRelic ∈ salvage.contribution.relics) &&
      decide (survey.record.turns.length = 4) &&
      decide (salvage.record.turns.length = 4)
  | _, _ => false

theorem strategic_plans_have_distinct_admitted_outputs :
    completedPlansAreMateriallyDistinctB = true := by native_decide

def combinedRecordsReverifyB : Bool :=
  match completionFor? fixtureConfig surveyPlan, completionFor? fixtureConfig salvagePlan with
  | some survey, some salvage => survey.record.validB && salvage.record.validB
  | _, _ => false

theorem combined_records_reverify_every_signed_handoff :
    combinedRecordsReverifyB = true := by native_decide

def wireRecordsReadmitB : Bool :=
  match completionFor? fixtureConfig surveyPlan, completionFor? fixtureConfig salvagePlan with
  | some survey, some salvage =>
      (admitCompletedRelay? (testRunAdmission fixtureConfig) survey.record.toRaw).isSome &&
      (admitCompletedRelay? (testRunAdmission fixtureConfig) salvage.record.toRaw).isSome
  | _, _ => false

theorem strict_wire_decoder_readmits_both_complete_plans :
    wireRecordsReadmitB = true := by native_decide

def tamperedCombinedRecordRefusesB : Bool :=
  match completionFor? fixtureConfig surveyPlan with
  | none => false
  | some capability => match capability.record.turns with
    | [] => false
    | turn :: turns =>
        let forgedTurn := { turn with signature := ⟨0⟩ }
        let forgedRecord := { capability.record with turns := forgedTurn :: turns }
        decide (forgedRecord.validB = false)

theorem tampered_combined_record_refuses :
    tamperedCombinedRecordRefusesB = true := by native_decide

def tamperedWireRecordRefusesB : Bool :=
  match completionFor? fixtureConfig surveyPlan with
  | none => false
  | some capability => match capability.record.toRaw.turns with
    | [] => false
    | turn :: turns =>
        let forgedTurn := { turn with signature := ⟨0⟩ }
        let forgedRaw := { capability.record.toRaw with turns := forgedTurn :: turns }
        (admitCompletedRelay? (testRunAdmission fixtureConfig) forgedRaw).isNone

theorem strict_wire_decoder_refuses_tampered_signature :
    tamperedWireRecordRefusesB = true := by native_decide

def relabelledStrategyRecordRefusesB : Bool :=
  match completionFor? fixtureConfig surveyPlan,
      expectedOutcome? fixtureConfig .salvage with
  | some capability, some salvageOutcome =>
      let relabelled := {
        capability.record with
        strategy := .salvage
        outcome := salvageOutcome
      }
      decide (relabelled.validB = false)
  | _, _ => false

theorem relabelled_strategy_and_output_refuse :
    relabelledStrategyRecordRefusesB = true := by native_decide

def twoSeatRawConfig : RawConfig :=
  { fixtureRawConfig with
    roster := fixtureRoster.take 2
    operationBudget := 6
    initialSupplies := 2 }

theorem two_seat_raw_config_valid : rawConfigValidB twoSeatRawConfig = true := by
  native_decide

private def twoSeatConfig : Config where
  raw := twoSeatRawConfig
  verifySeat := fixtureVerifySeat
  verifyTurn := fixtureVerifyTurn
  valid := two_seat_raw_config_valid

def twoSeatSurveyPlan : List (SeatId × Command) :=
  [(⟨0⟩, .chartPressureRoute), (⟨1⟩, .braceTransit)]

theorem two_seat_relay_is_playable :
    (completionFor? twoSeatConfig twoSeatSurveyPlan).isSome = true := by native_decide

def threeSeatRawConfig : RawConfig :=
  { fixtureRawConfig with
    roster := fixtureRoster.take 3
    operationBudget := 7
    initialSupplies := 3 }

theorem three_seat_raw_config_valid : rawConfigValidB threeSeatRawConfig = true := by
  native_decide

private def threeSeatConfig : Config where
  raw := threeSeatRawConfig
  verifySeat := fixtureVerifySeat
  verifyTurn := fixtureVerifyTurn
  valid := three_seat_raw_config_valid

def threeSeatSalvagePlan : List (SeatId × Command) :=
  [ ( ⟨0⟩, .markSalvageRoute)
  , ( ⟨1⟩, .overdriveCargoLift)
  , ( ⟨2⟩, .screenRecovery) ]

theorem three_seat_relay_is_playable :
    (completionFor? threeSeatConfig threeSeatSalvagePlan).isSome = true := by native_decide

def duplicatePlayerRaw : RawConfig :=
  { fixtureRawConfig with roster :=
      [fixtureSeat0, { fixtureSeat1 with playerKey := fixtureSeat0.playerKey },
        fixtureSeat2, fixtureSeat3] }

theorem duplicate_player_roster_refuses : rawConfigValidB duplicatePlayerRaw = false := by
  native_decide

def duplicateCredentialRaw : RawConfig :=
  { fixtureRawConfig with roster :=
      [fixtureSeat0, { fixtureSeat1 with credential := fixtureSeat0.credential },
        fixtureSeat2, fixtureSeat3] }

theorem duplicate_credential_roster_refuses :
    rawConfigValidB duplicateCredentialRaw = false := by native_decide

def replayedSeatRefusesB : Bool :=
  let initial := initialState fixtureConfig
  match testTurn? fixtureConfig initial ⟨0⟩ .chartPressureRoute with
  | none => false
  | some first => match execute fixtureConfig initial first with
    | .error _ => false
    | .ok after => match testTurn? fixtureConfig after.state ⟨0⟩ .chartPressureRoute with
      | none => false
      | some replay => decide (execute fixtureConfig after.state replay = .error .seatAlreadyUsed)

theorem replayed_seat_in_generation_refuses : replayedSeatRefusesB = true := by native_decide

def widenedRoleRefusesB : Bool :=
  let initial := initialState fixtureConfig
  match testTurn? fixtureConfig initial ⟨0⟩ .braceTransit with
  | none => false
  | some widened => decide (execute fixtureConfig initial widened = .error .roleWidening)

theorem widened_role_refuses : widenedRoleRefusesB = true := by native_decide

def mixedStrategyRefusesB : Bool :=
  let initial := initialState fixtureConfig
  match testTurn? fixtureConfig initial ⟨0⟩ .chartPressureRoute with
  | none => false
  | some first => match execute fixtureConfig initial first with
    | .error _ => false
    | .ok after => match testTurn? fixtureConfig after.state ⟨1⟩ .overdriveCargoLift with
      | none => false
      | some mixed => decide (execute fixtureConfig after.state mixed = .error .strategyConflict)

theorem mixed_strategy_handoff_refuses : mixedStrategyRefusesB = true := by native_decide

def staleRootRefusesB : Bool :=
  let initial := initialState fixtureConfig
  match testTurn? fixtureConfig initial ⟨0⟩ .chartPressureRoute with
  | none => false
  | some first => match execute fixtureConfig initial first with
    | .error _ => false
    | .ok after => match testTurn? fixtureConfig after.state ⟨1⟩ .braceTransit with
      | none => false
      | some next =>
          let staleBody := { next.body with preRoot := initial.root }
          let resigned : SignedTurn fixtureConfig := {
            capability := next.capability
            body := staleBody
            signature := ⟨turnSignatureValue next.capability.seat.credential staleBody⟩ }
          decide (execute fixtureConfig after.state resigned = .error .staleRoot)

theorem stale_root_even_when_resigned_refuses : staleRootRefusesB = true := by native_decide

def forgedSignatureRefusesB : Bool :=
  let initial := initialState fixtureConfig
  match testTurn? fixtureConfig initial ⟨0⟩ .chartPressureRoute with
  | none => false
  | some turn =>
      let forged : SignedTurn fixtureConfig := { turn with signature := ⟨0⟩ }
      decide (execute fixtureConfig initial forged = .error .signatureRefused)

theorem forged_turn_signature_refuses : forgedSignatureRefusesB = true := by native_decide

def wrongSessionEvenWhenResignedRefusesB : Bool :=
  let initial := initialState fixtureConfig
  match testTurn? fixtureConfig initial ⟨0⟩ .chartPressureRoute with
  | none => false
  | some turn =>
      let foreignSession := { turn.body.session with relayId := digestFilled 199 }
      let foreignBody := { turn.body with session := foreignSession }
      let resigned : SignedTurn fixtureConfig := {
        capability := turn.capability
        body := foreignBody
        signature := ⟨turnSignatureValue turn.capability.seat.credential foreignBody⟩ }
      decide (execute fixtureConfig initial resigned = .error .wrongSession)

theorem cross_session_turn_even_when_resigned_refuses :
    wrongSessionEvenWhenResignedRefusesB = true := by native_decide

def replayedCounterEvenWhenResignedRefusesB : Bool :=
  let initial := initialState fixtureConfig
  match testTurn? fixtureConfig initial ⟨0⟩ .chartPressureRoute with
  | none => false
  | some turn =>
      let replayBody := { turn.body with counter := turn.body.previousCounter }
      let resigned : SignedTurn fixtureConfig := {
        capability := turn.capability
        body := replayBody
        signature := ⟨turnSignatureValue turn.capability.seat.credential replayBody⟩ }
      decide (execute fixtureConfig initial resigned = .error .seatCounterMismatch)

theorem replayed_counter_even_when_resigned_refuses :
    replayedCounterEvenWhenResignedRefusesB = true := by native_decide

def abortRestartReplayRefusesB : Bool :=
  let initial := initialState fixtureConfig
  match testTurn? fixtureConfig initial ⟨0⟩ .abort with
  | none => false
  | some abortTurn => match execute fixtureConfig initial abortTurn with
    | .error _ => false
    | .ok aborted => match testTurn? fixtureConfig aborted.state ⟨0⟩ .restart with
      | none => false
      | some restartTurn => match execute fixtureConfig aborted.state restartTurn with
        | .error _ => false
        | .ok restarted =>
            decide (restarted.state.snapshot.generation = 1) &&
            decide (restarted.state.snapshot.seatCounters ≠ initial.snapshot.seatCounters) &&
            decide (execute fixtureConfig restarted.state abortTurn = .error .staleGeneration)

theorem restart_advances_generation_and_old_turn_refuses :
    abortRestartReplayRefusesB = true := by native_decide

def abortedRunHasNoCompletionB : Bool :=
  let initial := initialState fixtureConfig
  match testTurn? fixtureConfig initial ⟨0⟩ .abort with
  | none => false
  | some abortTurn => match execute fixtureConfig initial abortTurn with
    | .error _ => false
    | .ok aborted => aborted.completion.isNone

theorem aborted_run_has_no_contribution_capability :
    abortedRunHasNoCompletionB = true := by native_decide

private def fixtureSettlementGenesis : CanonicalSettlementGenesis fixtureConfig :=
  ⟨trivial⟩

def canonicalSettlementAdmitsOnceB : Bool :=
  match completionFor? fixtureConfig salvagePlan with
  | none => false
  | some capability =>
      let opened := SettlementRegistry.open fixtureSettlementGenesis WorldState.empty
      match opened.1.admitCompleted opened.2.head opened.2 capability with
      | .error _ => false
      | .ok (_, transition) =>
          decide (transition.after.world.sequence = 1) &&
          decide (capability.record.runKey ∈ transition.after.consumedRuns)

theorem completed_relay_proposes_exact_canonical_settlement_once :
    canonicalSettlementAdmitsOnceB = true := by native_decide

/-- Completing the same admitted session twice—equivalent to copying a fresh
initial state in a pure model—produces the same exact run key.  Once the first
completion advances the threaded canonical state, the second is refused. -/
def duplicateFreshRunSettlementRefusesB : Bool :=
  match completionFor? fixtureConfig salvagePlan,
      completionFor? fixtureConfig salvagePlan with
  | some first, some replayed =>
      let opened := SettlementRegistry.open fixtureSettlementGenesis WorldState.empty
      match opened.1.admitCompleted opened.2.head opened.2 first with
      | .error _ => false
      | .ok (advanced, transition) =>
          decide (first.record.runKey = replayed.record.runKey) &&
          match advanced.admitCompleted transition.after.head transition.after replayed with
          | .error .runAlreadyConsumed => true
          | _ => false
  | _, _ => false

theorem fresh_initial_replay_cannot_settle_same_run_twice :
    duplicateFreshRunSettlementRefusesB = true := by native_decide

/-- Survey and salvage produce different terminal roots, but they are competing
outcomes of one canonically admitted session.  Settling survey consumes the
session key, so a later salvage branch cannot exploit its different root to
settle again. -/
def competingOutcomeSettlementRefusesB : Bool :=
  match completionFor? fixtureConfig surveyPlan,
      completionFor? fixtureConfig salvagePlan with
  | some survey, some salvage =>
      let opened := SettlementRegistry.open fixtureSettlementGenesis WorldState.empty
      match opened.1.admitCompleted opened.2.head opened.2 survey with
      | .error _ => false
      | .ok (advanced, transition) =>
          decide (survey.record.finalRoot ≠ salvage.record.finalRoot) &&
          decide (survey.record.runKey = salvage.record.runKey) &&
          match advanced.admitCompleted transition.after.head transition.after salvage with
          | .error .runAlreadyConsumed => true
          | _ => false
  | _, _ => false

theorem survey_then_salvage_cannot_settle_one_admitted_session_twice :
    competingOutcomeSettlementRefusesB = true := by native_decide

def staleSettlementHeadRefusesB : Bool :=
  match completionFor? fixtureConfig salvagePlan with
  | none => false
  | some capability =>
      let opened := SettlementRegistry.open fixtureSettlementGenesis WorldState.empty
      match opened.1.admitCompleted opened.2.head opened.2 capability with
      | .error _ => false
      | .ok (advanced, _) =>
          match advanced.admitCompleted opened.2.head opened.2 capability with
          | .error .staleCanonicalHead => true
          | _ => false

theorem stale_prestate_cannot_reapply_completed_relay :
    staleSettlementHeadRefusesB = true := by native_decide

#assert_axioms execute_deterministic
#assert_axioms replay_deterministic
#assert_axioms completed_contribution_is_mission_admitted
#assert_axioms admitted_settlement_advances_world_sequence
#assert_axioms admitted_settlement_consumes_exact_run
#assert_axioms Config.roster_has_two_to_four_seats

#assert_compiled fixture_raw_config_valid
#assert_compiled survey_plan_completes
#assert_compiled salvage_plan_completes
#assert_compiled strategic_plans_have_distinct_admitted_outputs
#assert_compiled combined_records_reverify_every_signed_handoff
#assert_compiled strict_wire_decoder_readmits_both_complete_plans
#assert_compiled tampered_combined_record_refuses
#assert_compiled strict_wire_decoder_refuses_tampered_signature
#assert_compiled relabelled_strategy_and_output_refuse
#assert_compiled two_seat_raw_config_valid
#assert_compiled two_seat_relay_is_playable
#assert_compiled three_seat_raw_config_valid
#assert_compiled three_seat_relay_is_playable
#assert_compiled duplicate_player_roster_refuses
#assert_compiled duplicate_credential_roster_refuses
#assert_compiled replayed_seat_in_generation_refuses
#assert_compiled widened_role_refuses
#assert_compiled mixed_strategy_handoff_refuses
#assert_compiled stale_root_even_when_resigned_refuses
#assert_compiled forged_turn_signature_refuses
#assert_compiled cross_session_turn_even_when_resigned_refuses
#assert_compiled replayed_counter_even_when_resigned_refuses
#assert_compiled restart_advances_generation_and_old_turn_refuses
#assert_compiled aborted_run_has_no_contribution_capability
#assert_compiled completed_relay_proposes_exact_canonical_settlement_once
#assert_compiled fresh_initial_replay_cannot_settle_same_run_twice
#assert_compiled survey_then_salvage_cannot_settle_one_admitted_session_twice
#assert_compiled stale_prestate_cannot_reapply_completed_relay

end Dregg2.Games.PathOfAngels.CrewRelayExpedition
