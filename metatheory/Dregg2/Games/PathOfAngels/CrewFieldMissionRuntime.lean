/-
# CrewFieldMissionRuntime — canonical expedition admission and salvage authority

This is the callable authority between an activated authored content pack, the
complete `CrewFieldMission` transcript, and a durable expedition event stream.
The caller supplies no outcome, contribution, beta candidate, or salvage list:
all of them are derived from the activated field session and content bindings.

There are deliberately two salvage namespaces.  Ordinary parts are authored
mechanical inventory and may produce bounded market-mint authorizations.  A
`ContentContract.RelicId` is beta/canon provenance: it produces custody data,
never a market mint or trade authority.  The two constructors cannot be
relabelled by a caller.

⚑ 2026-08-06 — THE RUNTIME NOW RUNS THE KERNEL.  This paragraph used to read
"`ReplayAuthority.verify` is the cryptographic trust boundary.  A production
activation MUST pin it to the exact `CrewFieldMission.Config` … it must not be
an accept-all predicate."  That was an obligation written in prose and enforced
nowhere: `verify` was a caller-supplied `RawCombinedFieldRecord → Bool`, so a
host could pass `fun _ => true`, and the fixture activation in this very file
passed a session-equality plus a transcript-length check — no signature, no
replay.  Underneath it, `deriveRecord?` **asserted** the terminal state
(`phase := .extracted`, `sequence := CREW_SIZE`) instead of reaching it.

`Activation` now carries a `CrewFieldMission.RunSeal`, and `deriveRecord?`
returns `seal.replay? traces` — the record `CrewFieldMission.execute` actually
arrived at, driven from the kernel's private `initialState` over every signed
handoff.  Nothing here writes a terminal state down, so nothing here can
fabricate one, and a forged handoff signature refuses the whole run.

The seal is pinned by `sealSessionExact : runSeal.session = raw.fieldSession`.
That is a gate and not decoration: the seal's session comes from the private
`Config` its issuer sealed, `raw.fieldSession` is the authored activation's own
field session, and `SessionDigest` carries the roster, budget, policy and route
outcomes — so a seal issued for another mission cannot judge this one.

⚠ `replayVerifierId` (on `RawActivation` and on the emitted receipt) is an
authored AUDIT LABEL naming the expected verifier.  `activationValidB` does not
pin it and neither does anything else; it carries no authority.  The authority
is the seal.

The durable host owns the predecessor state and must CAS the emitted successor
atomically.  That is now the only host seam.

⚑ The durable key is the **pair** `(activation_id, roster_binding)`, not
`activation_id` alone.  `activation_id` is the digest of the authored activation
envelope and `MissionSpec` has no roster field, so two crews with disjoint
wallet keys share one `activation_id` — see
`hostile_rekeyed_roster_shares_the_authored_activation_id`, which is a fact
about the authored identity and is expected to stay true.  `roster_binding` is
computed by `rosterBindingOf` over every seat field and is pinned in
`activationValidB`, so it cannot be chosen by a caller.  A host that keys its
store on `activation_id` alone does not corrupt state — `StateWire.validB`
refuses the mismatch — but it does deny service to every crew after the first,
so key on the pair.
-/
import Lean.Data.Json
import Mathlib.Data.List.Sort
import Dregg2.Circuit.CommitmentTreeWide
import Dregg2.Games.PathOfAngels.ContentContract
import Dregg2.Games.PathOfAngels.CrewFieldMission
import Dregg2.Games.PathOfAngels.Emit
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.CrewFieldMissionRuntime

open Lean
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.CrewRelayExpedition

set_option autoImplicit false

abbrev INPUT_FORMAT : String := "POA-CREW-FIELD-RUN-IN-1"
abbrev STATE_FORMAT : String := "POA-CREW-FIELD-STATE-1"
abbrev OUTPUT_FORMAT : String := "POA-CREW-FIELD-RUN-OUT-1"
abbrev WIRE_BYTE_LIMIT : Nat := 1024 * 1024
abbrev MAX_RUNS : Nat := 4096
abbrev MAX_PART_RULES : Nat := 64
abbrev MAX_PART_QUANTITY : Nat := 64

/-! ## Digest primitive

Defined before the activation predicate because the crew identity that predicate
pins is a *computed* digest of the roster, not a caller-supplied claim. -/

private def byte (n : Nat) : Fin 256 := ⟨n % 256, Nat.mod_lt _ (by decide)⟩
private def u32le (n : Nat) : List (Fin 256) :=
  [byte n, byte (n / 256), byte (n / 65536), byte (n / 16777216)]
private def stringBytes (value : String) : List Nat :=
  value.toUTF8.toList.map UInt8.toNat

/-- Faithful eight-lane result of the Lean-authored wide commitment primitive. -/
def digestString (domain : Nat) (value : String) : Digest32 :=
  let lanes := Dregg2.Circuit.CommitmentTreeWide.hashTo8 domain (stringBytes value)
  { bytes := (List.ofFn (fun lane : Fin 8 => u32le (lanes.getD lane.val 0))).flatten
    length_eq := by simp [u32le] }

abbrev RUN_DIGEST_DOMAIN : Nat := 0x504f4158
abbrev SUCCESSOR_DIGEST_DOMAIN : Nat := 0x504f4159
abbrev ROSTER_BINDING_DOMAIN : Nat := 0x504f415a

/-! ## Crew identity

`MissionSpec.activationDigest` is the digest of the authored, detached activation
envelope; the roster is **not** part of it — `MissionSpec` (`Core.lean`) has no
roster field, and the roster lives one level out, in `SessionDigest.roster`.
`judge` authorizes a command by comparing `command.actor` against
`Seat.playerKey`, so the player keys are load-bearing for authorization and were
constrained by nothing: two activations differing only in their four
`playerKey`s were both valid under `activationValidB` and carried the *same*
`activationId`.  A durable host keyed by `activation_id` would therefore serve
one state stream — one admission cursor — to two distinct crews.

`rosterBindingOf` closes that by deriving a second, *computed* identity over
every field of every seat.  It is pinned in `activationValidB` and carried in
`StateWire`, so the durable key is the pair and a state minted for one crew is
refused under another's activation.  See
`hostile_rekeyed_roster_shares_the_authored_activation_id` for the collision
that motivates it and `hostile_rekeyed_crew_cannot_use_the_authored_crews_state`
for the refusal that closes it. -/

private def crewRoleCode : CrewRole → Nat
  | .pathfinder => 0
  | .engineer => 1
  | .containment => 2
  | .quartermaster => 3

/-- Canonical preimage of one seat.  Every field is included: the seat id and
role fix the seating, `credential` the authored officer, `playerKey` the wallet
`judge` authorizes against, and `initialCounter` the replay origin. -/
def seatBindingJson (seat : Seat) : String :=
  "{\"seat\":" ++ toString seat.id.value ++
    ",\"player_key\":\"" ++ Emit.bytes32Hex seat.playerKey ++ "\"" ++
    ",\"credential\":" ++ toString seat.credential.value ++
    ",\"role\":" ++ toString (crewRoleCode seat.role) ++
    ",\"initial_counter\":" ++ toString seat.initialCounter ++ "}"

/-- Computed crew identity.  Never a caller claim: `activationValidB` pins the
activation's declared `rosterBinding` against this function of the roster. -/
def rosterBindingOf (roster : List Seat) : Digest32 :=
  digestString ROSTER_BINDING_DOMAIN
    ("[" ++ String.intercalate "," (roster.map seatBindingJson) ++ "]")

/-! ## Activated content bridge -/

structure PartId where
  value : Nat
deriving Repr, DecidableEq

structure RouteBinding where
  field : CrewFieldMission.Route
  content : ContentContract.RouteId
deriving DecidableEq

structure ArtifactBinding where
  field : ArtifactRef
  content : ContentContract.ArtifactId
deriving DecidableEq

structure RelicBinding where
  field : RelicId
  content : ContentContract.RelicId
deriving DecidableEq

structure OrdinarySalvageRule where
  route : CrewFieldMission.Route
  extraction : CrewFieldMission.ExtractionChoice
  part : PartId
  quantity : Nat
deriving DecidableEq

def OrdinarySalvageRule.key (rule : OrdinarySalvageRule) :
    CrewFieldMission.Route × CrewFieldMission.ExtractionChoice × PartId :=
  (rule.route, rule.extraction, rule.part)

structure RawActivation where
  activationId : Digest32
  /-- Computed crew identity; `activationValidB` pins it to `rosterBindingOf
  fieldSession.roster`, so it cannot be chosen by the caller.  It is the second
  half of the durable key — `activationId` alone does not separate two crews. -/
  rosterBinding : Digest32
  contentDigest : Digest32
  fieldSession : CrewFieldMission.SessionDigest
  briefings : List CrewFieldMission.BriefingAssignment
  content : ContentContract.RawContent
  routeBindings : List RouteBinding
  artifactBindings : List ArtifactBinding
  relicBindings : List RelicBinding
  ordinarySalvage : List OrdinarySalvageRule
  replayVerifierId : Digest32
deriving DecidableEq

/-- ⚑ `ReplayAuthority` was deleted on 2026-08-06.  It carried
`verify : RawCombinedFieldRecord → Bool` — a function the caller chose — and was
described as "the cryptographic trust boundary".  A caller that supplies the
predicate that judges it is not a boundary.  `CrewFieldMission.RunSeal` replaces
it: the verification is the kernel's own `execute`, and the seal cannot be
opened, substituted, or asked to accept a record it did not reach.
`ReplayAuthority.id` went with it, because a pin between two fields the same
caller supplied (`replay.id = raw.replayVerifierId`) is decoration. -/

def routeBindingByField? : List RouteBinding → CrewFieldMission.Route →
    Option RouteBinding
  | [], _ => none
  | binding :: bindings, route =>
      if binding.field = route then some binding else routeBindingByField? bindings route

def artifactBindingByField? : List ArtifactBinding → ArtifactRef →
    Option ArtifactBinding
  | [], _ => none
  | binding :: bindings, artifact =>
      if binding.field = artifact then some binding
      else artifactBindingByField? bindings artifact

def relicBindingByField? : List RelicBinding → RelicId → Option RelicBinding
  | [], _ => none
  | binding :: bindings, relic =>
      if binding.field = relic then some binding else relicBindingByField? bindings relic

def contentOutcomeBy? : List ContentContract.RouteOutcome → ContentContract.RouteId →
    ContentContract.ExtractionChoice → Option ContentContract.RouteOutcome
  | [], _, _ => none
  | outcome :: outcomes, route, extraction =>
      if outcome.route = route ∧ outcome.extraction = extraction then some outcome
      else contentOutcomeBy? outcomes route extraction

def toContentExtraction : CrewFieldMission.ExtractionChoice →
    ContentContract.ExtractionChoice
  | .returnNow => .returnNow
  | .descendFurther => .descendFurther

def fieldRelicsToContent? (bindings : List RelicBinding) : List RelicId →
    Option (List ContentContract.RelicId)
  | [] => some []
  | relic :: relics => do
      let binding ← relicBindingByField? bindings relic
      let rest ← fieldRelicsToContent? bindings relics
      some (binding.content :: rest)

def contributionAlignedB (bindings : List RelicBinding) (field : RawContribution)
    (content : ContentContract.Contribution) : Bool :=
  match fieldRelicsToContent? bindings field.relics with
  | none => false
  | some relics =>
      decide (field.intel = content.intel) &&
      decide (field.supplies = content.supplies) &&
      decide (field.cohesion = content.cohesion) &&
      decide (field.influence = content.influence) &&
      decide (field.score = content.score) &&
      decide (relics = content.relics)

def fieldOutcomeAlignedB (raw : RawActivation)
    (field : CrewFieldMission.RouteOutcomeSpec) : Bool :=
  match routeBindingByField? raw.routeBindings field.route with
  | none => false
  | some routeBinding =>
    match contentOutcomeBy? raw.content.outcomes routeBinding.content
        (toContentExtraction field.extraction) with
    | none => false
    | some contentOutcome =>
      match artifactBindingByField? raw.artifactBindings field.featuredArtifact with
      | none => false
      | some artifactBinding =>
          decide (field.operationalCost = contentOutcome.operationalCost) &&
          decide (artifactBinding.content = contentOutcome.featuredArtifact) &&
          contributionAlignedB raw.relicBindings field.outcome.contribution
            contentOutcome.contribution

def briefingAlignedB (raw : RawActivation) : Bool :=
  decide (raw.briefings.length = CrewFieldMission.CREW_SIZE) &&
  decide (raw.briefings.map CrewFieldMission.BriefingAssignment.seat =
    raw.fieldSession.roster.map Seat.id) &&
  decide (raw.content.briefings.length = CrewFieldMission.CREW_SIZE) &&
  (raw.briefings.zip raw.content.briefings).all fun pair =>
    let field := pair.1
    let content := pair.2
    decide (field.observation.role = content.role) &&
    match field.observation.supportedRoute?, content.recommendedRoute with
    | none, none => true
    | some route, some routeId =>
        match routeBindingByField? raw.routeBindings route with
        | none => false
        | some binding => decide (binding.content = routeId)
    | _, _ => false

def ordinaryRulesValidB (raw : RawActivation) : Bool :=
  decide (raw.ordinarySalvage.length ≤ MAX_PART_RULES) &&
  decide (raw.ordinarySalvage.map OrdinarySalvageRule.key).Nodup &&
  decide (raw.ordinarySalvage.map (fun rule => rule.part)).Nodup &&
  raw.ordinarySalvage.all fun rule =>
    decide (0 < rule.quantity ∧ rule.quantity ≤ MAX_PART_QUANTITY) &&
    decide ((routeBindingByField? raw.routeBindings rule.route).isSome) &&
    decide (rule.part.value ∉ raw.content.relics.map (fun relic => relic.id.value))

def activationValidB (raw : RawActivation) : Bool :=
  ContentContract.contentValidB raw.content &&
  decide (raw.activationId = raw.fieldSession.policy.mission.activationDigest) &&
  decide (raw.rosterBinding = rosterBindingOf raw.fieldSession.roster) &&
  decide (raw.contentDigest = raw.fieldSession.policy.mission.contentRoot) &&
  decide (raw.fieldSession.federationId = raw.fieldSession.policy.mission.federationId) &&
  decide (raw.fieldSession.contentSession = raw.fieldSession.policy.mission.contentSession) &&
  decide (raw.fieldSession.missionEpoch = raw.fieldSession.policy.mission.epoch) &&
  decide (raw.fieldSession.missionId = raw.fieldSession.policy.mission.missionId) &&
  decide (raw.fieldSession.roster.length = CrewFieldMission.CREW_SIZE) &&
  decide (raw.fieldSession.roster.map Seat.role = ContentContract.exactRoles) &&
  decide (raw.fieldSession.roster.map (fun seat => seat.credential.value) =
    raw.content.officers.map (fun officer => officer.credential.value)) &&
  decide (raw.routeBindings.map RouteBinding.field =
    [.maintenanceSpine, .signalGallery, .sealedNave]) &&
  decide (raw.routeBindings.map RouteBinding.content = ContentContract.routeIds raw.content) &&
  decide (raw.artifactBindings.map ArtifactBinding.field).Nodup &&
  decide ((raw.artifactBindings.map ArtifactBinding.field).toFinset =
    raw.fieldSession.policy.allowedBeta) &&
  decide (raw.artifactBindings.map ArtifactBinding.content =
    ContentContract.artifactIds raw.content) &&
  decide (raw.relicBindings.map RelicBinding.field).Nodup &&
  decide ((raw.relicBindings.map RelicBinding.field).toFinset =
    raw.fieldSession.policy.mission.allowedRelics) &&
  decide (raw.relicBindings.map RelicBinding.content = ContentContract.relicIds raw.content) &&
  briefingAlignedB raw &&
  raw.fieldSession.routeOutcomes.all (fieldOutcomeAlignedB raw) &&
  ordinaryRulesValidB raw

/-- Private construction pins the run seal to this activation.  The seal is the
only thing in this structure that can judge a run, and `sealSessionExact` is what
stops one issued for another mission from doing so. -/
structure Activation where
  private mk ::
  raw : RawActivation
  private runSeal : CrewFieldMission.RunSeal
  valid : activationValidB raw = true
  sealSessionExact : runSeal.session = raw.fieldSession

/-- Two independent sources for one identity: `runSeal.session` is projected from
the private `CrewFieldMission.Config` the seal was issued over, `raw.fieldSession`
is the authored activation's field session, and they must be equal. -/
def activate? (raw : RawActivation) (runSeal : CrewFieldMission.RunSeal) :
    Option Activation :=
  if hvalid : activationValidB raw = true then
    if hseal : runSeal.session = raw.fieldSession then
      some ⟨raw, runSeal, hvalid, hseal⟩
    else none
  else none

/-! ## Strict proof-erased command and durable state -/

structure TraceWire where
  sequence : Nat
  seat : Nat
  previousCounter : Nat
  counter : Nat
  observation : String
  observedRoute : String
  decision : String
  decidedRoute : String
  extraction : String
  command : String
  seatSignature : CrewFieldMission.SignatureBytes
  handoffSignature : CrewFieldMission.SignatureBytes
deriving DecidableEq

structure ContributionWire where
  intel : Nat
  supplies : Nat
  cohesion : Nat
  influence : Nat
  score : Nat
  relics : List Nat
deriving DecidableEq

def ContributionWire.ofRaw (raw : RawContribution) : ContributionWire where
  intel := raw.intel
  supplies := raw.supplies
  cohesion := raw.cohesion
  influence := raw.influence
  score := raw.score
  relics := raw.relics.map RelicId.value

structure CommandWire where
  activationId : Digest32
  sequence : Nat
  predecessor : Digest32
  admission : Nat
  actor : Digest32
  officerSeat : Nat
  claimedRoute : String
  claimedExtraction : String
  claimedContribution : ContributionWire
  claimedFeaturedArtifact : Nat
  transcript : List TraceWire
deriving DecidableEq

structure StateWire where
  activationId : Digest32
  /-- The crew half of the durable key.  Present so a host that keys its store
  by `activation_id` alone cannot silently hand one crew another crew's stream:
  `validB` refuses the mismatch. -/
  rosterBinding : Digest32
  sequence : Nat
  head : Digest32
  nextAdmission : Nat
deriving DecidableEq

/-! ### ⚑ `consumedRuns` was deleted on 2026-08-06, and here is the argument

`StateWire` carried `consumedRuns : List Digest32`, `validB` required it to be
`Nodup` with `length = sequence`, the wire carried every entry up to
`MAX_RUNS = 4096`, and `judge` tested `if run ∈ state.consumedRuns then throw
.admissionReplay`.

THAT TEST COULD NOT FIRE.  `run = digestString RUN_DIGEST_DOMAIN command.toJson`
and `CommandWire.toJson` emits `"sequence":n`.  `judge` refuses unless
`command.sequence = state.sequence` (`.staleCursor`), and the successor sets
`sequence := state.sequence + 1`.  So every command that is ever admitted has a
sequence no admitted command has had before, hence a distinct `toJson`, hence a
distinct digest — and membership can only hold on a hash collision.  A ledger
that grows to 4,096 entries on the wire to hold a check whose only reachable
outcome is "absent".

NO COVERAGE WAS LOST.  `hostile_same_admission_and_run_cannot_replay` replays the
identical command against the successor state and already asserted
`.error .staleCursor`, not `.admissionReplay` — the tooth that was supposed to be
about this ledger was, and remains, about the cursor.

The cursor is what makes a run one-shot.  `.admissionReplay` survives on the
`command.admission ≠ state.nextAdmission` leg, which is reachable. -/

def StateWire.validB (activation : Activation) (state : StateWire) : Bool :=
  decide (state.activationId = activation.raw.activationId) &&
  decide (state.rosterBinding = activation.raw.rosterBinding) &&
  decide (state.sequence ≤ MAX_RUNS) &&
  decide (state.nextAdmission = state.sequence + 1)

def initialState (activation : Activation) (genesisHead : Digest32) : StateWire where
  activationId := activation.raw.activationId
  rosterBinding := activation.raw.rosterBinding
  sequence := 0
  head := genesisHead
  nextAdmission := 1

private def routeFromString? : String → Option CrewFieldMission.Route
  | "maintenance-spine" => some .maintenanceSpine
  | "signal-gallery" => some .signalGallery
  | "sealed-nave" => some .sealedNave
  | _ => none

private def routeString : CrewFieldMission.Route → String
  | .maintenanceSpine => "maintenance-spine"
  | .signalGallery => "signal-gallery"
  | .sealedNave => "sealed-nave"

private def extractionFromString? : String → Option CrewFieldMission.ExtractionChoice
  | "return-now" => some .returnNow
  | "descend-further" => some .descendFurther
  | _ => none

private def extractionString : CrewFieldMission.ExtractionChoice → String
  | .returnNow => "return-now"
  | .descendFurther => "descend-further"

private def commandFromString? : String → Option CrewRelayExpedition.Command
  | "chart-pressure-route" => some .chartPressureRoute
  | "mark-salvage-route" => some .markSalvageRoute
  | "brace-transit" => some .braceTransit
  | "overdrive-cargo-lift" => some .overdriveCargoLift
  | "quiet-anomaly" => some .quietAnomaly
  | "screen-recovery" => some .screenRecovery
  | "bank-supplies" => some .bankSupplies
  | "secure-cache" => some .secureCache
  | _ => none

private def commandString : CrewRelayExpedition.Command → String
  | .chartPressureRoute => "chart-pressure-route"
  | .markSalvageRoute => "mark-salvage-route"
  | .braceTransit => "brace-transit"
  | .overdriveCargoLift => "overdrive-cargo-lift"
  | .quietAnomaly => "quiet-anomaly"
  | .screenRecovery => "screen-recovery"
  | .bankSupplies => "bank-supplies"
  | .secureCache => "secure-cache"

private def observationFromWire? (wire : TraceWire) :
    Option CrewFieldMission.PrivateObservation := do
  match wire.observation with
  | "pathfinder" => return .pathfinder (← routeFromString? wire.observedRoute)
  | "engineer" => return .engineer (← routeFromString? wire.observedRoute)
  | "containment" => return .containment (← routeFromString? wire.observedRoute)
  | "quartermaster-closing" =>
      if wire.observedRoute = "none" then return .quartermaster .closing else none
  | "quartermaster-stable" =>
      if wire.observedRoute = "none" then return .quartermaster .stable else none
  | _ => none

private def decisionFromWire? (wire : TraceWire) : Option CrewFieldMission.Decision := do
  let route ← routeFromString? wire.decidedRoute
  let command ← commandFromString? wire.command
  match wire.decision with
  | "specialist" =>
      if wire.extraction = "none" then return .specialist route command else none
  | "finalize" =>
      return .finalize route (← extractionFromString? wire.extraction) command
  | _ => none

def TraceWire.toSemantic? (activation : Activation) : TraceWire →
    Option CrewFieldMission.HandoffTrace
  | wire => do
      let seat ← seatById? activation.raw.fieldSession.roster ⟨wire.seat⟩
      let observation ← observationFromWire? wire
      let decision ← decisionFromWire? wire
      some {
        sequence := wire.sequence
        seat
        previousCounter := wire.previousCounter
        counter := wire.counter
        observation
        decision
        seatSignature := ⟨wire.seatSignature⟩
        signature := ⟨wire.handoffSignature⟩
      }

/-! ### The wire encoder

`toSemantic?`'s inverse.  It exists so the fixtures below can be built FROM the
transcripts `CrewFieldMission` actually signed rather than from hand-written
constant signature bytes: a change to the kernel's signing preimage then moves
these fixtures with it instead of leaving them asserting against a stale
constant.  It is not part of the host ABI — the host sends `TraceWire`. -/

private def observationToWire : CrewFieldMission.PrivateObservation → String × String
  | .pathfinder route => ("pathfinder", routeString route)
  | .engineer route => ("engineer", routeString route)
  | .containment route => ("containment", routeString route)
  | .quartermaster .closing => ("quartermaster-closing", "none")
  | .quartermaster .stable => ("quartermaster-stable", "none")

private def decisionToWire : CrewFieldMission.Decision → String × String × String × String
  | .specialist route command =>
      ("specialist", routeString route, "none", commandString command)
  | .finalize route extraction command =>
      ("finalize", routeString route, extractionString extraction, commandString command)

private def TraceWire.ofSemantic (trace : CrewFieldMission.HandoffTrace) : TraceWire :=
  let (observation, observedRoute) := observationToWire trace.observation
  let (decision, decidedRoute, extraction, command) := decisionToWire trace.decision
  { sequence := trace.sequence
    seat := trace.seat.id.value
    previousCounter := trace.previousCounter
    counter := trace.counter
    observation
    observedRoute
    decision
    decidedRoute
    extraction
    command
    seatSignature := trace.seatSignature.bytes
    handoffSignature := trace.signature.bytes }

/-! ## Refusals

Declared here rather than beside `judge` because `deriveRecord?` now returns an
`Except Refusal _`: since the weld it can fail for two distinguishable reasons —
the wire transcript does not decode, or the kernel refuses the run. -/

inductive Refusal where
  | invalidState
  | wrongActivation
  | staleCursor
  | admissionReplay
  | unauthorizedOfficer
  | invalidTranscript
  | replayRefused
  | custodyRefused
deriving Repr, DecidableEq

/-- ⚑ THE WELD.  This function used to assemble a terminal
`CrewFieldMission.StateSnapshot` by ASSERTING `phase := .extracted`,
`sequence := CREW_SIZE`, `nextSeat := CREW_SIZE` and a budget it subtracted
itself, then hand the result to a caller-supplied verifier.  The kernel's
`execute` was never called; `CrewFieldMission` shipped a state machine that this
runtime reimplemented badly beside it.

It now asks the kernel and returns what the kernel answered.
`RunSeal.replay?` drives `execute` from the private `initialState` over every
signed handoff and yields the record the run actually REACHED — phase, sequence,
counters, remaining budget, route, extraction, outcome and featured artifact all
read off the kernel's own state.  Nothing here writes a terminal state down, so
nothing here can fabricate one, and a forged handoff signature refuses the run.

What survives from the old body is only the part the kernel cannot know: the
caller's CLAIMS and the activation's authored content tables.  Those are pinned
against the kernel's record, so they are a second source rather than the source.
The structural transcript checks are gone with the fabrication — every one of
them (length, sequence, seat order, briefed observation, counters, role
exactness, strategy agreement, recommendation and evidence counts, the
quartermaster window) is enforced inside `execute`, and a second copy here is
two shapes that agree today and disagree later. -/
private def deriveRecord? (activation : Activation) (command : CommandWire) :
    Except Refusal CrewFieldMission.RawCombinedFieldRecord := do
  let traces ← match command.transcript.mapM (TraceWire.toSemantic? activation) with
    | none => throw .invalidTranscript
    | some traces => pure traces
  let record ← match activation.runSeal.replay? traces with
    | none => throw .replayRefused
    | some record => pure record
  if command.claimedRoute ≠ routeString record.route then throw .invalidTranscript
  if command.claimedExtraction ≠ extractionString record.extraction then
    throw .invalidTranscript
  if command.claimedContribution ≠ ContributionWire.ofRaw record.outcome.contribution then
    throw .invalidTranscript
  let artifactBinding ← match artifactBindingByField? activation.raw.artifactBindings
      record.featuredBeta with
    | none => throw .invalidTranscript
    | some binding => pure binding
  if command.claimedFeaturedArtifact ≠ artifactBinding.content.value then
    throw .invalidTranscript
  pure record

/-! ## Derived settlement output -/

structure OrdinaryMintAuthorization where
  part : PartId
  quantity : Nat
  recipient : Digest32
  marketEligible : Bool
deriving DecidableEq

structure RelicCustodyAuthorization where
  relic : ContentContract.RelicId
  destination : ContentContract.CustodyLocation
  marketEligible : Bool
  directTradeAllowed : Bool
deriving DecidableEq

structure ReceiptWire where
  activationId : Digest32
  replayVerifierId : Digest32
  admission : Nat
  actor : Digest32
  route : String
  extraction : String
  runDigest : Digest32
  predecessor : Digest32
  successor : Digest32
  contribution : ContributionWire
  featuredArtifact : Nat
  ordinaryMints : List OrdinaryMintAuthorization
  relicCustody : List RelicCustodyAuthorization
deriving DecidableEq

structure OutputWire where
  state : StateWire
  receipt : ReceiptWire
deriving DecidableEq

private def ordinaryMints (activation : Activation) (record :
    CrewFieldMission.RawCombinedFieldRecord) (actor : Digest32) :
    List OrdinaryMintAuthorization :=
  (activation.raw.ordinarySalvage.filter fun rule =>
    decide (rule.route = record.route ∧ rule.extraction = record.extraction)).map fun rule =>
      ⟨rule.part, rule.quantity, actor, true⟩

private def relicCustody? (activation : Activation) (record :
    CrewFieldMission.RawCombinedFieldRecord) : Option (List RelicCustodyAuthorization) :=
  record.outcome.contribution.relics.mapM fun relic => do
    let binding ← relicBindingByField? activation.raw.relicBindings relic
    let contentRelic ← ContentContract.relicById? activation.raw.content.relics binding.content
    let plan ← ContentContract.custodyByRelic? activation.raw.content.custodyPlans binding.content
    if contentRelic.marketEligible ≠ false then none
    if plan.directTradeAllowed ≠ false then none
    if plan.destination = .market then none
    some ⟨binding.content, plan.destination, false, false⟩

private def signatureNatList (signature : CrewFieldMission.SignatureBytes) : List Nat :=
  signature.bytes.map Fin.val

private def jsonString (value : String) : String := String.quote value
private def jsonArray (values : List String) : String :=
  "[" ++ String.intercalate "," values ++ "]"
private def natArray (values : List Nat) : String :=
  jsonArray (values.map toString)

def ContributionWire.toJson (wire : ContributionWire) : String :=
  "{\"intel\":" ++ toString wire.intel ++
    ",\"supplies\":" ++ toString wire.supplies ++
    ",\"cohesion\":" ++ toString wire.cohesion ++
    ",\"influence\":" ++ toString wire.influence ++
    ",\"score\":" ++ toString wire.score ++
    ",\"relics\":" ++ natArray wire.relics ++ "}"

def TraceWire.toJson (wire : TraceWire) : String :=
  "{\"sequence\":" ++ toString wire.sequence ++
    ",\"seat\":" ++ toString wire.seat ++
    ",\"previous_counter\":" ++ toString wire.previousCounter ++
    ",\"counter\":" ++ toString wire.counter ++
    ",\"observation\":" ++ jsonString wire.observation ++
    ",\"observed_route\":" ++ jsonString wire.observedRoute ++
    ",\"decision\":" ++ jsonString wire.decision ++
    ",\"decided_route\":" ++ jsonString wire.decidedRoute ++
    ",\"extraction\":" ++ jsonString wire.extraction ++
    ",\"command\":" ++ jsonString wire.command ++
    ",\"seat_signature\":" ++ natArray (signatureNatList wire.seatSignature) ++
    ",\"handoff_signature\":" ++ natArray (signatureNatList wire.handoffSignature) ++ "}"

def CommandWire.toJson (wire : CommandWire) : String :=
  "{\"format\":" ++ jsonString INPUT_FORMAT ++
    ",\"activation_id\":" ++ jsonString (Emit.bytes32Hex wire.activationId) ++
    ",\"sequence\":" ++ toString wire.sequence ++
    ",\"predecessor\":" ++ jsonString (Emit.bytes32Hex wire.predecessor) ++
    ",\"admission\":" ++ toString wire.admission ++
    ",\"actor\":" ++ jsonString (Emit.bytes32Hex wire.actor) ++
    ",\"officer_seat\":" ++ toString wire.officerSeat ++
    ",\"claimed_route\":" ++ jsonString wire.claimedRoute ++
    ",\"claimed_extraction\":" ++ jsonString wire.claimedExtraction ++
    ",\"claimed_contribution\":" ++ wire.claimedContribution.toJson ++
    ",\"claimed_featured_artifact\":" ++ toString wire.claimedFeaturedArtifact ++
    ",\"transcript\":" ++ jsonArray (wire.transcript.map TraceWire.toJson) ++ "}"

def StateWire.toJson (wire : StateWire) : String :=
  "{\"format\":" ++ jsonString STATE_FORMAT ++
    ",\"activation_id\":" ++ jsonString (Emit.bytes32Hex wire.activationId) ++
    ",\"roster_binding\":" ++ jsonString (Emit.bytes32Hex wire.rosterBinding) ++
    ",\"sequence\":" ++ toString wire.sequence ++
    ",\"head\":" ++ jsonString (Emit.bytes32Hex wire.head) ++
    ",\"next_admission\":" ++ toString wire.nextAdmission ++ "}"

private def runDigest (command : CommandWire) : Digest32 :=
  digestString RUN_DIGEST_DOMAIN command.toJson

private def successorDigest (state : StateWire) (command : CommandWire)
    (run : Digest32) : Digest32 :=
  digestString SUCCESSOR_DIGEST_DOMAIN
    (state.toJson ++ command.toJson ++ Emit.bytes32Hex run)

/-- Pure Lean admission.  The host must atomically CAS `state.head` to the
emitted successor and persist the complete receipt before exposing a mint. -/
def judge (activation : Activation) (state : StateWire) (command : CommandWire) :
    Except Refusal OutputWire := do
  if state.validB activation ≠ true then throw .invalidState
  if command.activationId ≠ activation.raw.activationId then throw .wrongActivation
  if command.sequence ≠ state.sequence ∨ command.predecessor ≠ state.head then
    throw .staleCursor
  if command.admission ≠ state.nextAdmission then throw .admissionReplay
  let officer ← match seatById? activation.raw.fieldSession.roster ⟨command.officerSeat⟩ with
    | none => throw .unauthorizedOfficer
    | some seat => pure seat
  if command.actor ≠ officer.playerKey then throw .unauthorizedOfficer
  let record ← deriveRecord? activation command
  let run := runDigest command
  let custody ← match relicCustody? activation record with
    | none => throw .custodyRefused
    | some custody => pure custody
  let successor := successorDigest state command run
  let after : StateWire := {
    activationId := state.activationId
    rosterBinding := state.rosterBinding
    sequence := state.sequence + 1
    head := successor
    nextAdmission := state.nextAdmission + 1
  }
  if after.validB activation ≠ true then throw .invalidState
  let artifactBinding ← match artifactBindingByField? activation.raw.artifactBindings
      record.featuredBeta with
    | none => throw .invalidTranscript
    | some binding => pure binding
  let receipt : ReceiptWire := {
    activationId := activation.raw.activationId
    replayVerifierId := activation.raw.replayVerifierId
    admission := command.admission
    actor := command.actor
    route := routeString record.route
    extraction := extractionString record.extraction
    runDigest := run
    predecessor := state.head
    successor
    contribution := ContributionWire.ofRaw record.outcome.contribution
    featuredArtifact := artifactBinding.content.value
    ordinaryMints := ordinaryMints activation record command.actor
    relicCustody := custody
  }
  pure ⟨after, receipt⟩

/-! ## Canonical bounded JSON ABI

The runtime is deliberately parameterized by an already-pinned `Activation`.
Neither verifier functions nor authored tables travel over the public wire.
The host passes canonical predecessor-state bytes and canonical command bytes;
Lean returns canonical successor/receipt bytes only after `judge` accepts.
-/

private def exactKeys (j : Json) (allowed : List String) : Except String Unit := do
  let object ← j.getObj?
  if object.size == allowed.length && allowed.all object.contains then pure ()
  else throw "missing or unknown field"

private def objectNat (j : Json) (key : String) (limit : Nat := 2 ^ 64 - 1) :
    Except String Nat := do
  let value ← j.getObjValAs? Nat key
  if value ≤ limit then pure value else throw "integer exceeds wire bound"

private def objectDigest (j : Json) (key : String) : Except String Digest32 := do
  let spelling ← j.getObjValAs? String key
  match Emit.parseBytes32Hex? spelling with
  | some digest => pure digest
  | none => throw "digest must be exactly 64 lowercase hexadecimal digits"

private def parseNatList (j : Json) (lengthLimit valueLimit : Nat) :
    Except String (List Nat) := do
  let values := (← j.getArr?).toList
  if values.length > lengthLimit then throw "list exceeds wire bound"
  values.mapM fun value => do
    let n ← value.getNat?
    if n ≤ valueLimit then pure n else throw "list integer exceeds wire bound"

private def signatureBytes? (values : List Nat) :
    Option CrewFieldMission.SignatureBytes := do
  let bytes ← values.mapM fun value => if h : value < 256 then some ⟨value, h⟩ else none
  if h : bytes.length = CrewFieldMission.SIGNATURE_BYTE_LENGTH then some ⟨bytes, h⟩
  else none

private def parseSignature (j : Json) : Except String CrewFieldMission.SignatureBytes := do
  let values ← parseNatList j CrewFieldMission.SIGNATURE_BYTE_LENGTH 255
  match signatureBytes? values with
  | some signature => pure signature
  | none => throw "signature must contain exactly 64 bytes"

private def parseContribution (j : Json) : Except String ContributionWire := do
  exactKeys j ["intel", "supplies", "cohesion", "influence", "score", "relics"]
  pure {
    intel := ← objectNat j "intel" METRIC_LIMIT
    supplies := ← objectNat j "supplies" METRIC_LIMIT
    cohesion := ← objectNat j "cohesion" METRIC_LIMIT
    influence := ← objectNat j "influence" METRIC_LIMIT
    score := ← objectNat j "score" METRIC_LIMIT
    relics := ← parseNatList (← j.getObjVal? "relics") RELIC_LIMIT (2 ^ 64 - 1)
  }

private def parseTrace (j : Json) : Except String TraceWire := do
  exactKeys j ["sequence", "seat", "previous_counter", "counter", "observation",
    "observed_route", "decision", "decided_route", "extraction", "command",
    "seat_signature", "handoff_signature"]
  pure {
    sequence := ← objectNat j "sequence" CrewFieldMission.CREW_SIZE
    seat := ← objectNat j "seat" (CrewFieldMission.CREW_SIZE - 1)
    previousCounter := ← objectNat j "previous_counter" PLAYER_COUNTER_MODULUS
    counter := ← objectNat j "counter" PLAYER_COUNTER_MODULUS
    observation := ← j.getObjValAs? String "observation"
    observedRoute := ← j.getObjValAs? String "observed_route"
    decision := ← j.getObjValAs? String "decision"
    decidedRoute := ← j.getObjValAs? String "decided_route"
    extraction := ← j.getObjValAs? String "extraction"
    command := ← j.getObjValAs? String "command"
    seatSignature := ← parseSignature (← j.getObjVal? "seat_signature")
    handoffSignature := ← parseSignature (← j.getObjVal? "handoff_signature")
  }

private def parseTranscript (j : Json) : Except String (List TraceWire) := do
  let values := (← j.getArr?).toList
  if values.length != CrewFieldMission.CREW_SIZE then
    throw "field transcript must contain exactly four handoffs"
  values.mapM parseTrace

private def parseCommandJson (j : Json) : Except String CommandWire := do
  exactKeys j ["format", "activation_id", "sequence", "predecessor", "admission",
    "actor", "officer_seat", "claimed_route", "claimed_extraction",
    "claimed_contribution", "claimed_featured_artifact", "transcript"]
  if (← j.getObjValAs? String "format") != INPUT_FORMAT then throw "wrong input format"
  pure {
    activationId := ← objectDigest j "activation_id"
    sequence := ← objectNat j "sequence" MAX_RUNS
    predecessor := ← objectDigest j "predecessor"
    admission := ← objectNat j "admission" (MAX_RUNS + 1)
    actor := ← objectDigest j "actor"
    officerSeat := ← objectNat j "officer_seat" (CrewFieldMission.CREW_SIZE - 1)
    claimedRoute := ← j.getObjValAs? String "claimed_route"
    claimedExtraction := ← j.getObjValAs? String "claimed_extraction"
    claimedContribution := ← parseContribution (← j.getObjVal? "claimed_contribution")
    claimedFeaturedArtifact := ← objectNat j "claimed_featured_artifact"
    transcript := ← parseTranscript (← j.getObjVal? "transcript")
  }

private def parseStateJson (j : Json) : Except String StateWire := do
  exactKeys j ["format", "activation_id", "roster_binding", "sequence", "head",
    "next_admission"]
  if (← j.getObjValAs? String "format") != STATE_FORMAT then throw "wrong state format"
  pure {
    activationId := ← objectDigest j "activation_id"
    rosterBinding := ← objectDigest j "roster_binding"
    sequence := ← objectNat j "sequence" MAX_RUNS
    head := ← objectDigest j "head"
    nextAdmission := ← objectNat j "next_admission" (MAX_RUNS + 1)
  }

def canonicalDecode {T : Type} (parse : Json → Except String T) (encode : T → String)
    (bytes : String) : Option T :=
  match Json.parse bytes with
  | .error _ => none
  | .ok json =>
      match parse json with
      | .error _ => none
      | .ok value => if encode value = bytes then some value else none

def decodeCommandWithLimit (limit : Nat) (bytes : String) : Option CommandWire :=
  if bytes.length ≤ limit then canonicalDecode parseCommandJson CommandWire.toJson bytes
  else none

def decodeCommand (bytes : String) : Option CommandWire :=
  decodeCommandWithLimit WIRE_BYTE_LIMIT bytes

def decodeStateWithLimit (limit : Nat) (bytes : String) : Option StateWire :=
  if bytes.length ≤ limit then canonicalDecode parseStateJson StateWire.toJson bytes else none

def decodeState (bytes : String) : Option StateWire :=
  decodeStateWithLimit WIRE_BYTE_LIMIT bytes

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

theorem decodeCommand_reencodes {bytes : String} {command : CommandWire}
    (accepted : decodeCommand bytes = some command) : command.toJson = bytes := by
  simp only [decodeCommand, decodeCommandWithLimit] at accepted
  split at accepted
  · exact canonicalDecode_reencodes parseCommandJson CommandWire.toJson accepted
  · contradiction

theorem decodeState_reencodes {bytes : String} {state : StateWire}
    (accepted : decodeState bytes = some state) : state.toJson = bytes := by
  simp only [decodeState, decodeStateWithLimit] at accepted
  split at accepted
  · exact canonicalDecode_reencodes parseStateJson StateWire.toJson accepted
  · contradiction

private def custodyLocationJson : ContentContract.CustodyLocation → String
  | .atEncounter encounter =>
      "{\"kind\":\"at-encounter\",\"encounter\":" ++ toString encounter.value ++ "}"
  | .crewCarried => "{\"kind\":\"crew-carried\",\"encounter\":0}"
  | .quarantine => "{\"kind\":\"quarantine\",\"encounter\":0}"
  | .archive => "{\"kind\":\"archive\",\"encounter\":0}"
  | .market => "{\"kind\":\"market\",\"encounter\":0}"

private def OrdinaryMintAuthorization.toJson (mint : OrdinaryMintAuthorization) : String :=
  "{\"kind\":\"ordinary-part\",\"part\":" ++ toString mint.part.value ++
    ",\"quantity\":" ++ toString mint.quantity ++
    ",\"recipient\":" ++ jsonString (Emit.bytes32Hex mint.recipient) ++
    ",\"market_eligible\":" ++ toString mint.marketEligible ++ "}"

private def RelicCustodyAuthorization.toJson (custody : RelicCustodyAuthorization) : String :=
  "{\"kind\":\"provenance-relic\",\"relic\":" ++ toString custody.relic.value ++
    ",\"destination\":" ++ custodyLocationJson custody.destination ++
    ",\"market_eligible\":" ++ toString custody.marketEligible ++
    ",\"direct_trade_allowed\":" ++ toString custody.directTradeAllowed ++ "}"

def ReceiptWire.toJson (receipt : ReceiptWire) : String :=
  "{\"activation_id\":" ++ jsonString (Emit.bytes32Hex receipt.activationId) ++
    ",\"replay_verifier_id\":" ++ jsonString (Emit.bytes32Hex receipt.replayVerifierId) ++
    ",\"admission\":" ++ toString receipt.admission ++
    ",\"actor\":" ++ jsonString (Emit.bytes32Hex receipt.actor) ++
    ",\"route\":" ++ jsonString receipt.route ++
    ",\"extraction\":" ++ jsonString receipt.extraction ++
    ",\"run_digest\":" ++ jsonString (Emit.bytes32Hex receipt.runDigest) ++
    ",\"predecessor\":" ++ jsonString (Emit.bytes32Hex receipt.predecessor) ++
    ",\"successor\":" ++ jsonString (Emit.bytes32Hex receipt.successor) ++
    ",\"contribution\":" ++ receipt.contribution.toJson ++
    ",\"featured_artifact\":" ++ toString receipt.featuredArtifact ++
    ",\"ordinary_mints\":" ++ jsonArray (receipt.ordinaryMints.map
      OrdinaryMintAuthorization.toJson) ++
    ",\"relic_custody\":" ++ jsonArray (receipt.relicCustody.map
      RelicCustodyAuthorization.toJson) ++ "}"

def OutputWire.toJson (output : OutputWire) : String :=
  "{\"format\":" ++ jsonString OUTPUT_FORMAT ++
    ",\"state\":" ++ output.state.toJson ++
    ",\"receipt\":" ++ output.receipt.toJson ++ "}"

/-- Exact host ABI: pinned activation + canonical durable state bytes +
canonical command bytes -> canonical successor/receipt bytes. -/
def process (activation : Activation) (stateBytes commandBytes : String) : Option String := do
  let state ← decodeState stateBytes
  let command ← decodeCommand commandBytes
  match judge activation state command with
  | .error _ => none
  | .ok output => some output.toJson

/-! ## Executable activation and hostile cases -/

private def fixtureDigest (value : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨value % 256, Nat.mod_lt _ (by omega)⟩
  length_eq := by simp

private def fixtureContentOfficers : List ContentContract.OfficerSeat :=
  [ ⟨⟨0⟩, ⟨10⟩, .pathfinder⟩
  , ⟨⟨1⟩, ⟨11⟩, .engineer⟩
  , ⟨⟨2⟩, ⟨12⟩, .containment⟩
  , ⟨⟨3⟩, ⟨13⟩, .quartermaster⟩ ]

private def fixtureContentBriefings : List ContentContract.BriefingShape :=
  [ ⟨.pathfinder, .mappedRoute, some ⟨1⟩, .privateUntilSignedHandoff⟩
  , ⟨.engineer, .structurallySoundRoute, some ⟨1⟩, .privateUntilSignedHandoff⟩
  , ⟨.containment, .hazardClearRoute, some ⟨1⟩, .privateUntilSignedHandoff⟩
  , ⟨.quartermaster, .extractionWindow, none, .privateUntilSignedHandoff⟩ ]

private def fixtureContentArtifacts : List ContentContract.ArtifactSpec :=
  [ ⟨⟨20⟩, none⟩, ⟨⟨21⟩, none⟩, ⟨⟨22⟩, none⟩ ]

private def fixtureContentEncounters : List ContentContract.EncounterSpec :=
  [ { id := ⟨10⟩, room := DeckGraph.fixtureRoomB.id,
      routes := [⟨0⟩, ⟨1⟩, ⟨2⟩], betaArtifacts := [⟨20⟩] }
  , { id := ⟨11⟩, room := DeckGraph.fixtureRoomC.id,
      routes := [⟨0⟩], betaArtifacts := [⟨20⟩] }
  , { id := ⟨12⟩, room := DeckGraph.fixtureRoomD.id,
      routes := [⟨1⟩], betaArtifacts := [⟨21⟩] }
  , { id := ⟨13⟩, room := DeckGraph.fixtureExtraction.id,
      routes := [⟨2⟩], betaArtifacts := [⟨22⟩] } ]

private def contentRoute : CrewFieldMission.Route → ContentContract.RouteId
  | .maintenanceSpine => ⟨0⟩
  | .signalGallery => ⟨1⟩
  | .sealedNave => ⟨2⟩

private def contentArtifact : CrewFieldMission.Route → ContentContract.ArtifactId
  | .maintenanceSpine => ⟨20⟩
  | .signalGallery => ⟨21⟩
  | .sealedNave => ⟨22⟩

private def contentRelics (relics : List RelicId) : List ContentContract.RelicId :=
  relics.map fun relic => ⟨relic.value⟩

private def fixtureContentOutcomes : List ContentContract.RouteOutcome :=
  CrewFieldMission.fixtureRouteOutcomes.map fun spec => {
    route := contentRoute spec.route
    extraction := toContentExtraction spec.extraction
    operationalCost := spec.operationalCost
    agreement := ContentContract.requiredAgreement (toContentExtraction spec.extraction)
    featuredArtifact := contentArtifact spec.route
    contribution := {
      intel := spec.outcome.contribution.intel
      supplies := spec.outcome.contribution.supplies
      cohesion := spec.outcome.contribution.cohesion
      influence := spec.outcome.contribution.influence
      score := spec.outcome.contribution.score
      relics := contentRelics spec.outcome.contribution.relics
    }
    recovery := if spec.extraction = .returnNow then ⟨40⟩ else ⟨41⟩
  }

private def fixtureRuntimeContent : ContentContract.RawContent := {
  ContentContract.fixtureContent with
  officers := fixtureContentOfficers
  briefings := fixtureContentBriefings
  encounters := fixtureContentEncounters
  artifacts := fixtureContentArtifacts
  outcomes := fixtureContentOutcomes
  relics := [⟨⟨447⟩, ⟨12⟩, true, false, none⟩]
  custodyPlans := [⟨⟨447⟩, .atEncounter ⟨12⟩, .quarantine,
    .fullCrewUnanimity, false⟩]
  promotionHooks :=
    [ ⟨.place ⟨50⟩, none⟩
    , ⟨.artifact ⟨20⟩, none⟩
    , ⟨.relic ⟨447⟩, none⟩ ]
  contributionBudget := {
    intel := 8, supplies := 4, cohesion := 6, influence := 0, score := 79,
    relicAllowlist := [⟨447⟩]
  }
}

private theorem fixture_runtime_content_valid :
    ContentContract.contentValidB fixtureRuntimeContent = true := by
  native_decide

private def fixtureRawActivation : RawActivation where
  activationId := CrewFieldMission.fixtureRawConfig.policy.mission.activationDigest
  rosterBinding := rosterBindingOf CrewFieldMission.fixtureRawConfig.roster
  contentDigest := CrewFieldMission.fixtureRawConfig.policy.mission.contentRoot
  fieldSession := CrewFieldMission.fixtureRawConfig.sessionDigest
  briefings := CrewFieldMission.fixtureBriefings
  content := fixtureRuntimeContent
  routeBindings :=
    [ ⟨.maintenanceSpine, ⟨0⟩⟩
    , ⟨.signalGallery, ⟨1⟩⟩
    , ⟨.sealedNave, ⟨2⟩⟩ ]
  artifactBindings :=
    [ ⟨CrewFieldMission.fixtureMaintenanceArtifact, ⟨20⟩⟩
    , ⟨CrewFieldMission.fixtureSignalArtifact, ⟨21⟩⟩
    , ⟨CrewFieldMission.fixtureNaveArtifact, ⟨22⟩⟩ ]
  relicBindings := [⟨DeckExpedition.fixtureRelic, ⟨447⟩⟩]
  ordinarySalvage :=
    [ ⟨.maintenanceSpine, .returnNow, ⟨900⟩, 2⟩
    , ⟨.signalGallery, .descendFurther, ⟨901⟩, 1⟩ ]
  replayVerifierId := fixtureDigest 222

private theorem fixture_activation_valid : activationValidB fixtureRawActivation = true := by
  native_decide

/-! ### The sealed fixture activation

⚑ 2026-08-06.  What stood here was a `ReplayAuthority` whose `verify` was

    decide (record.session = fixtureRawActivation.fieldSession) &&
    decide (record.transcript.length = CrewFieldMission.CREW_SIZE)

— a session comparison and a length check, standing in for the module's
"cryptographic trust boundary".  It verified no signature and replayed nothing,
and every `native_decide` result below was evidence about THAT.  The transcripts
it judged carried `fixtureSignature` in both signature fields: one constant byte
pattern, identical for all four seats.

The activation now holds `CrewFieldMission.fixtureRunSeal`, and the transcripts
are the ones the kernel itself signed, re-encoded to the wire.  `sealSessionExact`
holds by `rfl` because the seal's config and this activation's `fieldSession` are
both `CrewFieldMission.fixtureRawConfig.sessionDigest` — two spellings the
elaborator has to agree on, not a value copied from one to the other. -/
private def fixtureActivation : Activation :=
  ⟨fixtureRawActivation, CrewFieldMission.fixtureRunSeal, fixture_activation_valid, rfl⟩

private def fixtureSafeTranscript : List TraceWire :=
  CrewFieldMission.fixtureSafeMaintenanceTranscript.map TraceWire.ofSemantic

private def fixtureDeepTranscript : List TraceWire :=
  CrewFieldMission.fixtureDeepTranscript.map TraceWire.ofSemantic

/-- The wire encoder is a genuine inverse on the transcripts the kernel signed:
decoding the encoding returns the kernel's own traces.  Without this the
fixtures below could be exercising a transcript the runtime silently reinterprets. -/
theorem fixture_wire_transcripts_decode_back_to_the_kernel_traces :
    fixtureSafeTranscript.mapM (TraceWire.toSemantic? fixtureActivation) =
      some CrewFieldMission.fixtureSafeMaintenanceTranscript ∧
    fixtureDeepTranscript.mapM (TraceWire.toSemantic? fixtureActivation) =
      some CrewFieldMission.fixtureDeepTranscript := by
  native_decide

private def fixtureGenesis : StateWire := initialState fixtureActivation (fixtureDigest 223)

private def fixtureSafeCommand : CommandWire where
  activationId := fixtureRawActivation.activationId
  sequence := 0
  predecessor := fixtureGenesis.head
  admission := 1
  actor := CrewRelayExpedition.fixtureSeat0.playerKey
  officerSeat := 0
  claimedRoute := "maintenance-spine"
  claimedExtraction := "return-now"
  claimedContribution := ContributionWire.ofRaw
    (CrewFieldMission.fixtureOutcome .maintenanceSpine .returnNow).contribution
  claimedFeaturedArtifact := 20
  transcript := fixtureSafeTranscript

private def fixtureDeepCommand : CommandWire := {
  fixtureSafeCommand with
  claimedRoute := "signal-gallery"
  claimedExtraction := "descend-further"
  claimedContribution := ContributionWire.ofRaw
    (CrewFieldMission.fixtureOutcome .signalGallery .descendFurther).contribution
  claimedFeaturedArtifact := 21
  transcript := fixtureDeepTranscript
}

private def fixtureSafeResult : Except Refusal OutputWire :=
  judge fixtureActivation fixtureGenesis fixtureSafeCommand

private def fixtureDeepResult : Except Refusal OutputWire :=
  judge fixtureActivation fixtureGenesis fixtureDeepCommand

def honestOrdinarySalvageB : Bool :=
  match fixtureSafeResult with
  | .error _ => false
  | .ok output => decide (
      output.receipt.ordinaryMints =
        [⟨⟨900⟩, 2, CrewRelayExpedition.fixtureSeat0.playerKey, true⟩] ∧
      output.receipt.relicCustody = [])

theorem honest_complete_run_emits_one_ordinary_salvage_authorization :
    honestOrdinarySalvageB = true := by
  native_decide

def deepTaxonomyB : Bool :=
  match fixtureDeepResult with
  | .error _ => false
  | .ok output => decide (
      output.receipt.ordinaryMints =
        [⟨⟨901⟩, 1, CrewRelayExpedition.fixtureSeat0.playerKey, true⟩] ∧
      output.receipt.relicCustody =
        [⟨⟨447⟩, .quarantine, false, false⟩])

theorem deep_run_separates_exchangeable_parts_from_nonmarket_relic_custody :
    deepTaxonomyB = true := by
  native_decide

def replayRefusedB : Bool :=
  match fixtureSafeResult with
  | .error _ => false
  | .ok first => decide (judge fixtureActivation first.state fixtureSafeCommand =
      .error .staleCursor)

theorem hostile_same_admission_and_run_cannot_replay : replayRefusedB = true := by
  native_decide

theorem hostile_cross_activation_command_refused :
    judge fixtureActivation fixtureGenesis
      { fixtureSafeCommand with activationId := fixtureDigest 250 } =
        .error .wrongActivation := by
  native_decide

theorem hostile_forged_route_refused :
    judge fixtureActivation fixtureGenesis
      { fixtureSafeCommand with claimedRoute := "sealed-nave" } =
        .error .invalidTranscript := by
  native_decide

theorem hostile_forged_outcome_refused :
    judge fixtureActivation fixtureGenesis
      { fixtureSafeCommand with claimedContribution :=
          { fixtureSafeCommand.claimedContribution with score := 999 } } =
        .error .invalidTranscript := by
  native_decide

theorem hostile_actor_who_is_not_the_selected_officer_refused :
    judge fixtureActivation fixtureGenesis
      { fixtureSafeCommand with actor := CrewRelayExpedition.fixtureSeat1.playerKey } =
        .error .unauthorizedOfficer := by
  native_decide

/-- ⚑ The refusal MOVED, and that is the weld showing.  This used to be
`.invalidTranscript` — this module's own `traces.length = CREW_SIZE` check.  It
is now `.replayRefused`: three signed handoffs replay fine, the run simply never
reaches `.extracted`, so the kernel has no completed record to give back.  The
truncation is refused by the state machine rather than by a length comparison. -/
theorem hostile_truncated_crew_transcript_refused :
    judge fixtureActivation fixtureGenesis
      { fixtureSafeCommand with transcript := fixtureSafeTranscript.take 3 } =
        .error .replayRefused := by
  native_decide

private def forgedSignatureBytes : CrewFieldMission.SignatureBytes where
  bytes := List.replicate CrewFieldMission.SIGNATURE_BYTE_LENGTH 7
  length_eq := by simp [CrewFieldMission.SIGNATURE_BYTE_LENGTH]

/-- ⚑ THE WELD, SHOWN.  This is the case the old code got wrong: substituting a
handoff signature changes neither the session nor the transcript length, so the
`ReplayAuthority` that stood here — `session = … && length = CREW_SIZE` — ACCEPTED
it, and `deriveRecord?` had already asserted the terminal state it was asked
about.  A forged run was admitted and would have minted salvage.

The kernel refuses it, because `replay?` rebuilds each `SignedHandoff` from the
trace and the signature has to verify.

The forgery is constructed from the live fixture trace and asserted DIFFERENT
before the verdict is read: if a fixture re-emit ever makes the mutation a
no-op, this goes red instead of quietly comparing a value with itself. -/
def forgedHandoffSignatureRefusedB : Bool :=
  match fixtureSafeTranscript with
  | [] => false
  | wire :: rest =>
      let forged : TraceWire := { wire with handoffSignature := forgedSignatureBytes }
      decide (forged.handoffSignature ≠ wire.handoffSignature) &&
      decide (judge fixtureActivation fixtureGenesis
        { fixtureSafeCommand with transcript := forged :: rest } = .error .replayRefused)

theorem hostile_forged_handoff_signature_refused_by_the_kernel :
    forgedHandoffSignatureRefusedB = true := by native_decide

/-- ⚑ Replaces `hostile_wrong_replay_authority_id_refused`, which checked that
`activate?` refused a `ReplayAuthority` whose `id` disagreed with the
activation's own `replayVerifierId` — two fields the same caller supplied.  This
is the check that has teeth: a seal minted for a DIFFERENT session cannot be
attached to this activation, and the two sessions are proved distinct in the
kernel (`the_two_fixture_seals_carry_different_sessions`). -/
theorem hostile_seal_for_another_session_cannot_activate :
    activate? fixtureRawActivation CrewFieldMission.fixtureRekeyedRunSeal = none := by
  native_decide

private def hostileMarketContent : ContentContract.RawContent := {
  fixtureRuntimeContent with
  relics := [{ (fixtureRuntimeContent.relics.getD 0
    ⟨⟨447⟩, ⟨12⟩, true, false, none⟩) with marketEligible := true }]
}

private def hostileTradeContent : ContentContract.RawContent := {
  fixtureRuntimeContent with
  custodyPlans := [{ (fixtureRuntimeContent.custodyPlans.getD 0
    ⟨⟨447⟩, .atEncounter ⟨12⟩, .quarantine, .fullCrewUnanimity, false⟩) with
      directTradeAllowed := true }]
}

theorem hostile_canon_relic_market_activation_refused :
    activate? { fixtureRawActivation with content := hostileMarketContent }
      CrewFieldMission.fixtureRunSeal = none := by
  native_decide

theorem hostile_canon_relic_direct_trade_activation_refused :
    activate? { fixtureRawActivation with content := hostileTradeContent }
      CrewFieldMission.fixtureRunSeal = none := by
  native_decide

private def callerAuthoredMintBytes : String :=
  (fixtureSafeCommand.toJson.dropEnd 1).toString ++
    ",\"ordinary_mints\":[{\"part\":999,\"quantity\":64}]}"

theorem hostile_caller_authored_salvage_field_refused_by_strict_codec :
    decodeCommand callerAuthoredMintBytes = none := by
  native_decide

theorem strict_command_roundtrip :
    decodeCommand fixtureSafeCommand.toJson = some fixtureSafeCommand := by
  native_decide

theorem strict_state_roundtrip :
    decodeState fixtureGenesis.toJson = some fixtureGenesis := by
  native_decide

/-! ### The two-crews-one-key collision, and the binding that closes it

`activationId` is pinned only against `fieldSession.policy.mission.activationDigest`
— a field of the same caller-supplied record — and `MissionSpec` carries no
roster.  The seating that `judge` authorizes against therefore sat outside the
activation's identity entirely.  The fixtures below substitute the four wallet
keys and change nothing else.

⚑ 2026-08-06.  The substituted crew now comes from `CrewFieldMission`'s second
SEALED world rather than from a roster swapped in here.  It has to: since the
weld an `Activation` carries a `RunSeal`, and a seal can be minted only by the
kernel, because it holds a `Config` whose constructor is private.  The roster
substitution itself is unchanged — `CrewFieldMission.fixtureRekeyedRoster` is
the same four keys this file used to build inline, and
`fixture_rekeyed_roster_substitutes_only_the_player_keys` says so next to the
world it describes. -/

private def rekeyedRoster : List Seat := CrewFieldMission.fixtureRekeyedRoster

private def rekeyedSession : CrewFieldMission.SessionDigest :=
  CrewFieldMission.fixtureRekeyedRawConfig.sessionDigest

private def rekeyedRawActivation : RawActivation :=
  { fixtureRawActivation with
    fieldSession := rekeyedSession
    rosterBinding := rosterBindingOf rekeyedRoster }

/-- Guard against a falsifier that has stopped falsifying: the substitution must
really have happened, and must have moved *only* the player keys. -/
def rekeySubstitutionRealB : Bool :=
  decide (rekeyedRoster ≠ CrewFieldMission.fixtureRawConfig.roster) &&
  decide (rekeyedRoster.map Seat.playerKey ≠
    CrewFieldMission.fixtureRawConfig.roster.map Seat.playerKey) &&
  decide (rekeyedRoster.map Seat.id =
    CrewFieldMission.fixtureRawConfig.roster.map Seat.id) &&
  decide (rekeyedRoster.map Seat.role =
    CrewFieldMission.fixtureRawConfig.roster.map Seat.role) &&
  decide (rekeyedRoster.map Seat.credential =
    CrewFieldMission.fixtureRawConfig.roster.map Seat.credential) &&
  decide (rekeyedRoster.map Seat.initialCounter =
    CrewFieldMission.fixtureRawConfig.roster.map Seat.initialCounter)

theorem rekeyed_crew_is_a_real_substitution_of_the_player_keys_alone :
    rekeySubstitutionRealB = true := by native_decide

/-- The substituted crew is *admitted*, not rejected.  Without this the
collision below would be about an activation nothing accepts. -/
theorem rekeyed_crew_activation_is_valid :
    activationValidB rekeyedRawActivation = true := by native_decide

/-- ⚑ The collision.  Two crews with disjoint wallet keys, both valid, carry the
same authored activation identity.  A durable host keyed by `activation_id`
alone would serve one state stream — one admission cursor — to both.  This
statement is expected to stay true: `activationDigest` is the digest of the
authored envelope and the roster is not in it.  It is the reason
`rosterBinding` exists. -/
theorem hostile_rekeyed_roster_shares_the_authored_activation_id :
    rekeyedRawActivation.activationId = fixtureRawActivation.activationId := rfl

/-- The computed binding is what separates them. -/
theorem rekeyed_roster_changes_the_computed_crew_binding :
    rekeyedRawActivation.rosterBinding ≠ fixtureRawActivation.rosterBinding := by
  native_decide

/-- …and the pin refuses in the other direction too, so it is a statement about
the pin and not about one unlucky pairing. -/
theorem hostile_authored_seal_cannot_activate_the_substituted_crew :
    activate? rekeyedRawActivation CrewFieldMission.fixtureRunSeal = none := by
  native_decide

private def rekeyedActivation : Activation :=
  ⟨rekeyedRawActivation, CrewFieldMission.fixtureRekeyedRunSeal,
    rekeyed_crew_activation_is_valid, rfl⟩

/-- The refusal, decomposed so the *cause* is named: the authored crew's genesis
state still matches on `activation_id` — the old key really does still collide —
and is refused solely because the roster binding disagrees. -/
def crossCrewStateRefusedOnRosterB : Bool :=
  decide (fixtureGenesis.activationId = rekeyedActivation.raw.activationId) &&
  decide (fixtureGenesis.rosterBinding ≠ rekeyedActivation.raw.rosterBinding) &&
  decide (StateWire.validB rekeyedActivation fixtureGenesis = false)

theorem cross_crew_state_refused_only_by_the_roster_binding :
    crossCrewStateRefusedOnRosterB = true := by native_decide

/-- End to end: a substituted officer, presenting the authored crew's durable
state, cannot consume that crew's admission. -/
private def rekeyedActorCommand : CommandWire :=
  { fixtureSafeCommand with
    actor := (rekeyedRoster.getD 0 CrewRelayExpedition.fixtureSeat0).playerKey }

def crossCrewRunRefusedB : Bool :=
  decide (judge rekeyedActivation fixtureGenesis rekeyedActorCommand = .error .invalidState)

theorem hostile_substituted_crew_cannot_consume_the_authored_crews_admission :
    crossCrewRunRefusedB = true := by native_decide

theorem callable_entrypoint_emits_the_exact_successful_receipt :
    process fixtureActivation fixtureGenesis.toJson fixtureSafeCommand.toJson =
      fixtureSafeResult.toOption.map OutputWire.toJson := by
  native_decide

#assert_axioms canonicalDecode_reencodes
#assert_axioms decodeCommand_reencodes
#assert_axioms decodeState_reencodes
-- `rfl` closes this one, but `CrewFieldMission.fixturePolicy` was itself built with
-- `native_decide`, so the statement inherits that axiom and pins in the compiled tier.
#assert_compiled hostile_rekeyed_roster_shares_the_authored_activation_id
#assert_compiled rekeyed_crew_is_a_real_substitution_of_the_player_keys_alone
#assert_compiled rekeyed_crew_activation_is_valid
#assert_compiled rekeyed_roster_changes_the_computed_crew_binding
#assert_compiled cross_crew_state_refused_only_by_the_roster_binding
#assert_compiled hostile_substituted_crew_cannot_consume_the_authored_crews_admission
#assert_compiled fixture_runtime_content_valid
#assert_compiled fixture_activation_valid
#assert_compiled honest_complete_run_emits_one_ordinary_salvage_authorization
#assert_compiled deep_run_separates_exchangeable_parts_from_nonmarket_relic_custody
#assert_compiled hostile_same_admission_and_run_cannot_replay
#assert_compiled hostile_cross_activation_command_refused
#assert_compiled hostile_forged_route_refused
#assert_compiled hostile_forged_outcome_refused
#assert_compiled hostile_actor_who_is_not_the_selected_officer_refused
#assert_compiled hostile_truncated_crew_transcript_refused
#assert_compiled hostile_forged_handoff_signature_refused_by_the_kernel
#assert_compiled hostile_seal_for_another_session_cannot_activate
#assert_compiled hostile_authored_seal_cannot_activate_the_substituted_crew
#assert_compiled fixture_wire_transcripts_decode_back_to_the_kernel_traces
#assert_compiled hostile_canon_relic_market_activation_refused
#assert_compiled hostile_canon_relic_direct_trade_activation_refused
#assert_compiled hostile_caller_authored_salvage_field_refused_by_strict_codec
#assert_compiled strict_command_roundtrip
#assert_compiled strict_state_roundtrip
#assert_compiled callable_entrypoint_emits_the_exact_successful_receipt

end Dregg2.Games.PathOfAngels.CrewFieldMissionRuntime
