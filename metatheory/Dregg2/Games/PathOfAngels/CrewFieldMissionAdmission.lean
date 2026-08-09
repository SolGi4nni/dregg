/-
# CrewFieldMissionAdmission — where a crew activation STOPS being the caller's, and
where the RUN SEAL stops being an argument

`CrewFieldMissionRuntime.activate?` takes a `CrewFieldMission.RunSeal` **as a
parameter**.  It checks that the seal's session equals the authored field session and
nothing else, because there is nothing else it *can* check: a seal is opaque.  So the
question "which seals exist, publicly?" is the whole security of the organ, and until
this module the answer was:

* `CrewFieldMission.fixtureRunSeal` and `CrewFieldMission.fixtureRekeyedRunSeal` —
  both **public**, both carrying the fixture signature suite whose `verifySeat` /
  `verifyHandoff` accept a constant byte pattern derived from the seat's own public
  fields, i.e. a signature anyone can compute; and
* `CrewFieldMission.ProductionSigning.activate?`, which is real but consumes a
  `RawConfig` that **had no codec**, so nothing on a wire could reach it.

An `@[export]` shaped `(activation, requestBytes) → String` therefore could not exist:
the only activations a host could build were built from a fixture seal, and
`fixtureRunSeal` completing a seat is "anyone completes any seat" — which is exactly
what the kernel's own docblock says a seal must prevent.  That is why this organ, with
a landed ML-DSA-65 suite and a landed per-handoff step surface, still had **zero
`@[export]`**.

## What this module does

`authorizeCrewActivationForWorld?` is
`ActivatedContent.authorizeEmbeddedGalleyPolicyForWorld?` /
`NightWatchCampaignAdmission.authorizeCampaignConfigForWorld?` for this organ, with one
addition that is the point of the file:

1. it locates `poa.crew-field-mission.activation.v1` by exact name inside an activated
   manifest whose SHA-256 root IS the audited world's `contentRoot`;
2. it decodes those bytes **canonically** — parse, re-encode, demand byte equality, so
   one activation has exactly one spelling — into `CrewFieldMissionRuntime.RawActivation`;
3. it **MINTS** the seal, inside the witness, by calling
   `CrewFieldMission.ProductionSigning.activate?` on a `RawConfig` reconstructed from
   the admitted `fieldSession`.  The seal is a **function of the admitted bytes**.  It
   is not an argument, it is not a field of the request, and there is no constructor
   of this witness that takes one.

Because `ProductionSigning.activate?` pins `messageDigestSuiteId` and `signingSuiteId`
to the production suite ids structurally, an admitted document whose session names the
FIXTURE suite mints **no seal at all**, and therefore reaches no activation and no step
surface.  The fixture-seal ban is a refusal of the minting function, not a convention:
see `a_fixture_suited_activation_in_an_exactly_matching_world_mints_no_seal`.

## Why a `RawConfig` can be reconstructed from a `SessionDigest`

`CrewFieldMission.RawConfig` and `CrewFieldMission.SessionDigest` carry the same
fourteen fields, and `RawConfig.sessionDigest` is the field-for-field projection.
`configOfSession` is its inverse, and `configOfSession_sessionDigest` /
`sessionDigest_configOfSession` prove the round trip in both directions by `rfl` after
`cases`.  So "the session the activation authored" and "the config the seal is issued
over" are one document, not two that agree today.  Nothing is invented at the seam:
`ProductionSigning.activate?` still runs the full `rawConfigValidB` — roster shape,
briefing-deck commitment under the production SHAKE-256 boundary, mission-identity
agreement, budget floor, route-outcome table — over exactly those bytes.

## What this does NOT buy

**Signature verification of the WORLD is `WorldActivation`'s, at the persistence
seam**, exactly as it is for Galley and Night Watch.  This module proves membership in
a world it is HANDED; a caller that hands it a world nobody audited gets a witness
about nothing.  That is the same boundary `ActivatedContent`'s docblock draws, not a
new one — and it is why the export below is safe only when mounted behind the same
audited-world seam Galley's is.

⚠ The seal-minting closure is INDEPENDENT of that boundary and is the part that is
new: even a caller that fabricates a world and a manifest cannot obtain a
fixture-suited seal, because minting refuses the fixture suite before the world is
ever consulted.

⚠ Nothing yet EMITS a `poa.crew-field-mission.activation.v1` component — `Emit` has no
renderer for one — so today the only manifests carrying one are the fixtures below.

⚠ `raw.contentDigest` and `content.deck.activation.contentRoot` are deliberately NOT
pinned to `world.contentRoot`.  The world's content root is the SHA-256 of the manifest
that embeds this very activation, so pinning either would be a cycle.  What IS pinned
to the world is the federation, the content session, and the deck's own signed
activation identity (`contentEpoch`, `activationDigest`) — the fields
`DeckGraph.ActivationIdentity` documents as "carried by the externally signed
activation statement", which `DeckGraph.validateB` explicitly does not authenticate and
which were therefore free for a caller to choose.

## Flag day

`poa.crew-field-mission.activation.v1` is a NEW component name and
`POA-CREW-FIELD-ACTIVATION-1` a new document format; nothing emitted one before, so
nothing re-emits.  The `@[export dregg_poa_crew_field_step]` below is new and its
`REQUIRED_DECISION_EXPORTS` row lands with it.
-/
import Lean.Data.Json
import Dregg2.Games.PathOfAngels.ActivatedContent
import Dregg2.Games.PathOfAngels.CrewFieldMissionRuntime
import Dregg2.Games.PathOfAngels.NightWatchCampaignAdmission
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.CrewFieldMissionAdmission

open Lean
open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.CrewRelayExpedition
open Dregg2.Games.PathOfAngels.CrewFieldMissionRuntime
open Dregg2.Games.PathOfAngels.NightWatchCampaignAdmission
  (canonicalDecode canonicalDecode_reencodes exactKeys objectNat objectDigest
   parseBoundedList parseNat parseOption jsonString jsonArray optionJson boolJson
   roleCode roleOfCode?)

set_option autoImplicit false
set_option maxRecDepth 20000

/-! ## Wire constants -/

abbrev ACTIVATION_FORMAT : String := "POA-CREW-FIELD-ACTIVATION-1"

/-- The canonical public name of the crew activation component inside an activated
manifest.  Exact: `componentByName?` does not prefix-match. -/
abbrev ACTIVATION_COMPONENT : String := "poa.crew-field-mission.activation.v1"

abbrev STEP_ENVELOPE_FORMAT : String := "POA-CREW-FIELD-STEP-ENVELOPE-1"

/-- ⚑ 2026-08-09 — the ENTRY POINT's wire.  `stepWire` hands a client the HANDOFF
preimage and tells it to sign THOSE BYTES; the SEAT-ADMISSION preimage, which a seat
must sign FIRST to be admitted at all, had no export and no route, so the organ's own
first move was the one thing a client could not make without re-encoding a body this
module forbids clients to build.  `seatPreimageWire` closes that. -/
abbrev SEAT_ENVELOPE_FORMAT : String := "POA-CREW-FIELD-SEAT-ENVELOPE-1"

abbrev SEAT_OUTPUT_FORMAT : String := "POA-CREW-FIELD-SEAT-OUT-1"

/-- An admitted activation is a manifest component, so it can never exceed a
component's own bound.  Using that bound rather than a second, larger one keeps the
decoder from accepting a document the manifest validator would have refused. -/
abbrev ACTIVATION_BYTE_LIMIT : Nat := ActivatedContent.COMPONENT_BYTE_LIMIT

abbrev ENVELOPE_BYTE_LIMIT : Nat := 4 * 1024 * 1024

/-- Plain unquoted integer array — the spelling `ProductionSigning.natArray` emits
inside `sessionJson`, which this module must parse back byte-exactly. -/
def natArray (values : List Nat) : String :=
  "[" ++ String.intercalate "," (values.map toString) ++ "]"

/-! ## The two hex spellings are one spelling

`Emit.bytes32Hex` (this module, and every manifest) and
`CrewFieldMission.ProductionSigning.digestHex` (the signing preimages, and therefore
`sessionJson`) are separate functions in separate modules with separate private
`byteHex` helpers.  Both are a `String.join` over a per-byte map, so agreement on all
256 byte values is agreement on every digest — this is the whole domain of the
function they differ in, not a sample of digests. -/

private def uniformDigest (value : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨value % 256, Nat.mod_lt _ (by omega)⟩
  length_eq := by simp

/-- Agreement on all 256 byte values — the whole domain of the per-byte function the two
spellings differ in, not a sample of digests. (Pinned `= true` in
`CrewFieldMissionAdmissionFixtures`; see the campaign note at the Teeth header below.) -/
def check_the_manifest_hex_and_the_signing_hex_agree_on_every_byte_value : Bool :=
  (List.range 256).all (fun value =>
    Emit.bytes32Hex (uniformDigest value) ==
      CrewFieldMission.ProductionSigning.digestHex (uniformDigest value))

/-! ## Stable finite codes

Every code below is either the organ's OWN published numbering (`Route.code`,
`PrivateObservation.code`, both of which already reach a signed preimage) or a fresh
numbering with a named round-trip theorem.  A code with no inverse is a field a
document can carry and a reader cannot check. -/

def routeOfCode? : Nat → Option CrewFieldMission.Route
  | 0 => some .maintenanceSpine
  | 1 => some .signalGallery
  | 2 => some .sealedNave
  | _ => none

theorem routeOfCode_code (route : CrewFieldMission.Route) :
    routeOfCode? route.code = some route := by
  cases route <;> rfl

def extractionCode : CrewFieldMission.ExtractionChoice → Nat
  | .returnNow => 0
  | .descendFurther => 1

def extractionOfCode? : Nat → Option CrewFieldMission.ExtractionChoice
  | 0 => some .returnNow
  | 1 => some .descendFurther
  | _ => none

theorem extractionOfCode_code (extraction : CrewFieldMission.ExtractionChoice) :
    extractionOfCode? (extractionCode extraction) = some extraction := by
  cases extraction <;> rfl

/-- The inverse of `PrivateObservation.code`, which is the numbering the signed
briefing deck already publishes (`ProductionSigning.briefingDeckJson`). -/
def observationOfCode? : Nat → Option CrewFieldMission.PrivateObservation
  | 10 => some (.pathfinder .maintenanceSpine)
  | 11 => some (.pathfinder .signalGallery)
  | 12 => some (.pathfinder .sealedNave)
  | 20 => some (.engineer .maintenanceSpine)
  | 21 => some (.engineer .signalGallery)
  | 22 => some (.engineer .sealedNave)
  | 30 => some (.containment .maintenanceSpine)
  | 31 => some (.containment .signalGallery)
  | 32 => some (.containment .sealedNave)
  | 40 => some (.quartermaster .closing)
  | 41 => some (.quartermaster .stable)
  | _ => none

theorem observationOfCode_code (observation : CrewFieldMission.PrivateObservation) :
    observationOfCode? observation.code = some observation := by
  cases observation with
  | pathfinder route => cases route <;> rfl
  | engineer route => cases route <;> rfl
  | containment route => cases route <;> rfl
  | quartermaster window => cases window <;> rfl

def privacyGradeCode : PrivacyGrade → Nat
  | .public => 0
  | .operatorVisibleHidingFri => 1
  | .processSeparatedThreshold => 2
  | .independentOperatorThreshold => 3

def privacyGradeOfCode? : Nat → Option PrivacyGrade
  | 0 => some .public
  | 1 => some .operatorVisibleHidingFri
  | 2 => some .processSeparatedThreshold
  | 3 => some .independentOperatorThreshold
  | _ => none

theorem privacyGradeOfCode_code (grade : PrivacyGrade) :
    privacyGradeOfCode? (privacyGradeCode grade) = some grade := by
  cases grade <;> rfl

def ballotRegimeCode : BallotRegime → Nat
  | .none => 0
  | .onePlayerOneVoice => 1
  | .oneWalletOneVoice => 2
  | .cappedChoir => 3
  | .predictionOracle => 4

def ballotRegimeOfCode? : Nat → Option BallotRegime
  | 0 => some .none
  | 1 => some .onePlayerOneVoice
  | 2 => some .oneWalletOneVoice
  | 3 => some .cappedChoir
  | 4 => some .predictionOracle
  | _ => none

theorem ballotRegimeOfCode_code (ballot : BallotRegime) :
    ballotRegimeOfCode? (ballotRegimeCode ballot) = some ballot := by
  cases ballot <;> rfl

def contentExtractionCode : ContentContract.ExtractionChoice → Nat
  | .returnNow => 0
  | .descendFurther => 1

def contentExtractionOfCode? : Nat → Option ContentContract.ExtractionChoice
  | 0 => some .returnNow
  | 1 => some .descendFurther
  | _ => none

theorem contentExtractionOfCode_code (extraction : ContentContract.ExtractionChoice) :
    contentExtractionOfCode? (contentExtractionCode extraction) = some extraction := by
  cases extraction <;> rfl

def observationKindCode : ContentContract.ObservationKind → Nat
  | .mappedRoute => 0
  | .structurallySoundRoute => 1
  | .hazardClearRoute => 2
  | .extractionWindow => 3

def observationKindOfCode? : Nat → Option ContentContract.ObservationKind
  | 0 => some .mappedRoute
  | 1 => some .structurallySoundRoute
  | 2 => some .hazardClearRoute
  | 3 => some .extractionWindow
  | _ => none

theorem observationKindOfCode_code (kind : ContentContract.ObservationKind) :
    observationKindOfCode? (observationKindCode kind) = some kind := by
  cases kind <;> rfl

def agreementCode : ContentContract.AgreementRule → Nat
  | .twoSpecialistSupport => 0
  | .fullCrewUnanimity => 1

def agreementOfCode? : Nat → Option ContentContract.AgreementRule
  | 0 => some .twoSpecialistSupport
  | 1 => some .fullCrewUnanimity
  | _ => none

theorem agreementOfCode_code (rule : ContentContract.AgreementRule) :
    agreementOfCode? (agreementCode rule) = some rule := by
  cases rule <;> rfl

def recoveryGradeCode : ContentContract.RecoveryGrade → Nat
  | .clean => 0
  | .equipmentUnavailable => 1
  | .marked => 2
  | .lostOpportunity => 3
  | .containmentDebt => 4

def recoveryGradeOfCode? : Nat → Option ContentContract.RecoveryGrade
  | 0 => some .clean
  | 1 => some .equipmentUnavailable
  | 2 => some .marked
  | 3 => some .lostOpportunity
  | 4 => some .containmentDebt
  | _ => none

theorem recoveryGradeOfCode_code (grade : ContentContract.RecoveryGrade) :
    recoveryGradeOfCode? (recoveryGradeCode grade) = some grade := by
  cases grade <;> rfl

def recoveryDurationCode : ContentContract.RecoveryDuration → Nat
  | .none => 0
  | .oneStudyCycle => 1
  | .contentEpoch => 2
  | .untilCuratorSuccessor => 3

def recoveryDurationOfCode? : Nat → Option ContentContract.RecoveryDuration
  | 0 => some .none
  | 1 => some .oneStudyCycle
  | 2 => some .contentEpoch
  | 3 => some .untilCuratorSuccessor
  | _ => none

theorem recoveryDurationOfCode_code (duration : ContentContract.RecoveryDuration) :
    recoveryDurationOfCode? (recoveryDurationCode duration) = some duration := by
  cases duration <;> rfl

def recoveryImplementationCode : ContentContract.RecoveryImplementation → Nat
  | .betaRecordOnly => 0
  | .automaticWorldMutation => 1

def recoveryImplementationOfCode? : Nat → Option ContentContract.RecoveryImplementation
  | 0 => some .betaRecordOnly
  | 1 => some .automaticWorldMutation
  | _ => none

theorem recoveryImplementationOfCode_code
    (implementation : ContentContract.RecoveryImplementation) :
    recoveryImplementationOfCode? (recoveryImplementationCode implementation)
      = some implementation := by
  cases implementation <;> rfl

def custodyAuthorityCode : ContentContract.CustodyAuthority → Nat
  | .fullCrewUnanimity => 0
  | .explicitCuratorSuccessor => 1
  | .unilateralHolder => 2

def custodyAuthorityOfCode? : Nat → Option ContentContract.CustodyAuthority
  | 0 => some .fullCrewUnanimity
  | 1 => some .explicitCuratorSuccessor
  | 2 => some .unilateralHolder
  | _ => none

theorem custodyAuthorityOfCode_code (authority : ContentContract.CustodyAuthority) :
    custodyAuthorityOfCode? (custodyAuthorityCode authority) = some authority := by
  cases authority <;> rfl

def contentTierCode : ContentContract.ContentTier → Nat
  | .betaDraft => 0
  | .alphaCanon => 1

def contentTierOfCode? : Nat → Option ContentContract.ContentTier
  | 0 => some .betaDraft
  | 1 => some .alphaCanon
  | _ => none

theorem contentTierOfCode_code (tier : ContentContract.ContentTier) :
    contentTierOfCode? (contentTierCode tier) = some tier := by
  cases tier <;> rfl

def storyAuthorityCode : ContentContract.StoryAuthority → Nat
  | .explicitCuratorAction => 0
  | .automaticGameOutcome => 1
  | .holderVote => 2

def storyAuthorityOfCode? : Nat → Option ContentContract.StoryAuthority
  | 0 => some .explicitCuratorAction
  | 1 => some .automaticGameOutcome
  | 2 => some .holderVote
  | _ => none

theorem storyAuthorityOfCode_code (authority : ContentContract.StoryAuthority) :
    storyAuthorityOfCode? (storyAuthorityCode authority) = some authority := by
  cases authority <;> rfl

def axisCode : DeckGraph.Axis → Nat
  | .horizontal => 0
  | .vertical => 1

def axisOfCode? : Nat → Option DeckGraph.Axis
  | 0 => some .horizontal
  | 1 => some .vertical
  | _ => none

theorem axisOfCode_code (axis : DeckGraph.Axis) : axisOfCode? (axisCode axis) = some axis := by
  cases axis <;> rfl

#assert_axioms routeOfCode_code
#assert_axioms extractionOfCode_code
#assert_axioms observationOfCode_code
#assert_axioms privacyGradeOfCode_code
#assert_axioms ballotRegimeOfCode_code
#assert_axioms contentExtractionOfCode_code
#assert_axioms observationKindOfCode_code
#assert_axioms agreementOfCode_code
#assert_axioms recoveryGradeOfCode_code
#assert_axioms recoveryDurationOfCode_code
#assert_axioms recoveryImplementationOfCode_code
#assert_axioms custodyAuthorityOfCode_code
#assert_axioms contentTierOfCode_code
#assert_axioms storyAuthorityOfCode_code
#assert_axioms axisOfCode_code

/-! ## The deck graph -/

def activationIdentityJson (identity : DeckGraph.ActivationIdentity) : String :=
  "{\"federation_id\":" ++ jsonString (Emit.bytes32Hex identity.federationId) ++
  ",\"content_root\":" ++ jsonString (Emit.bytes32Hex identity.contentRoot) ++
  ",\"activation_digest\":" ++ jsonString (Emit.bytes32Hex identity.activationDigest) ++
  ",\"content_session\":" ++ jsonString (Emit.bytes32Hex identity.contentSession) ++
  ",\"content_epoch\":" ++ toString identity.contentEpoch.value ++
  ",\"signer_key_id\":" ++ jsonString (Emit.bytes32Hex identity.signerKeyId) ++
  ",\"activation_counter\":" ++ toString identity.activationCounter ++ "}"

/-- One uniform shape for all four modifiers, with the fields a constructor does not
use written as `0`.  A document that fills them anyway decodes to the same modifier and
then FAILS the canonical re-encode, so the filler is refused rather than ignored. -/
def modifierJson (modifier : DeckGraph.Modifier) : String :=
  match modifier with
  | .oneWay => "{\"kind\":0,\"axis\":0,\"required\":0,\"next\":0}"
  | .wrap axis =>
      "{\"kind\":1,\"axis\":" ++ toString (axisCode axis) ++ ",\"required\":0,\"next\":0}"
  | .mirror axis =>
      "{\"kind\":2,\"axis\":" ++ toString (axisCode axis) ++ ",\"required\":0,\"next\":0}"
  | .phase required next =>
      "{\"kind\":3,\"axis\":0,\"required\":" ++ toString required.val ++
        ",\"next\":" ++ toString next.val ++ "}"

def hotspotJson (hotspot : DeckGraph.Hotspot) : String :=
  "{\"id\":" ++ toString hotspot.id.value ++
  ",\"source\":" ++ toString hotspot.source.value ++
  ",\"destination\":" ++ toString hotspot.destination.value ++
  ",\"modifier\":" ++ modifierJson hotspot.modifier ++ "}"

def deckJson (pack : DeckGraph.Pack) : String :=
  "{\"schema_version\":" ++ toString pack.schemaVersion ++
  ",\"pack_id\":" ++ toString pack.packId.value ++
  ",\"activation\":" ++ activationIdentityJson pack.activation ++
  ",\"rooms\":" ++ natArray (pack.rooms.map (fun room => room.id.value)) ++
  ",\"hotspots\":" ++ jsonArray (pack.hotspots.map hotspotJson) ++
  ",\"entry\":" ++ toString pack.entry.value ++
  ",\"extraction\":" ++ toString pack.extraction.value ++
  ",\"initial_phase\":" ++ toString pack.initialPhase.val ++
  ",\"navigation_fuel\":" ++ toString pack.navigationFuel ++
  ",\"validation_fuel\":" ++ toString pack.validationFuel ++ "}"

private def parseActivationIdentity (j : Json) :
    Except String DeckGraph.ActivationIdentity := do
  exactKeys j ["federation_id", "content_root", "activation_digest", "content_session",
    "content_epoch", "signer_key_id", "activation_counter"]
  pure {
    federationId := ← objectDigest j "federation_id"
    contentRoot := ← objectDigest j "content_root"
    activationDigest := ← objectDigest j "activation_digest"
    contentSession := ← objectDigest j "content_session"
    contentEpoch := ⟨← objectNat j "content_epoch"⟩
    signerKeyId := ← objectDigest j "signer_key_id"
    activationCounter := ← objectNat j "activation_counter"
  }

private def parseModifier (j : Json) : Except String DeckGraph.Modifier := do
  exactKeys j ["kind", "axis", "required", "next"]
  let kind ← objectNat j "kind" 3
  let axisValue ← objectNat j "axis" 1
  let required ← objectNat j "required" 3
  let next ← objectNat j "next" 3
  let axis ← match axisOfCode? axisValue with
    | some value => pure value
    | none => throw "unknown deck axis code"
  if hrequired : required < 4 then
    if hnext : next < 4 then
      match kind with
      | 0 => pure .oneWay
      | 1 => pure (.wrap axis)
      | 2 => pure (.mirror axis)
      | _ => pure (.phase ⟨required, hrequired⟩ ⟨next, hnext⟩)
    else throw "phase index exceeds the finite phase count"
  else throw "phase index exceeds the finite phase count"

private def parseHotspot (j : Json) : Except String DeckGraph.Hotspot := do
  exactKeys j ["id", "source", "destination", "modifier"]
  pure {
    id := ⟨← objectNat j "id"⟩
    source := ⟨← objectNat j "source"⟩
    destination := ⟨← objectNat j "destination"⟩
    modifier := ← parseModifier (← j.getObjVal? "modifier")
  }

private def parseDeck (j : Json) : Except String DeckGraph.Pack := do
  exactKeys j ["schema_version", "pack_id", "activation", "rooms", "hotspots", "entry",
    "extraction", "initial_phase", "navigation_fuel", "validation_fuel"]
  let roomValues ← parseBoundedList (← j.getObjVal? "rooms") DeckGraph.MAX_ROOMS
    (fun value => parseNat value)
  let phase ← objectNat j "initial_phase" 3
  if hphase : phase < 4 then
    pure {
      schemaVersion := ← objectNat j "schema_version"
      packId := ⟨← objectNat j "pack_id"⟩
      activation := ← parseActivationIdentity (← j.getObjVal? "activation")
      rooms := roomValues.map (fun value => { id := ⟨value⟩ })
      hotspots := ← parseBoundedList (← j.getObjVal? "hotspots") DeckGraph.MAX_HOTSPOTS
        parseHotspot
      entry := ⟨← objectNat j "entry"⟩
      extraction := ⟨← objectNat j "extraction"⟩
      initialPhase := ⟨phase, hphase⟩
      navigationFuel := ← objectNat j "navigation_fuel" DeckGraph.MAX_NAVIGATION_FUEL
      validationFuel := ← objectNat j "validation_fuel" DeckGraph.MAX_VALIDATION_FUEL
    }
  else throw "initial phase exceeds the finite phase count"

/-! ## The authored content pack -/

def officerJson (officer : ContentContract.OfficerSeat) : String :=
  "{\"officer\":" ++ toString officer.officer.value ++
  ",\"credential\":" ++ toString officer.credential.value ++
  ",\"role\":" ++ toString (roleCode officer.role) ++ "}"

def briefingShapeJson (shape : ContentContract.BriefingShape) : String :=
  "{\"role\":" ++ toString (roleCode shape.role) ++
  ",\"observation\":" ++ toString (observationKindCode shape.observation) ++
  ",\"recommended_route\":" ++
    optionJson (fun (route : ContentContract.RouteId) => toString route.value)
      shape.recommendedRoute ++
  ",\"disclosure\":0}"

def routeSpecJson (spec : ContentContract.RouteSpec) : String :=
  "{\"id\":" ++ toString spec.id.value ++
  ",\"encounters\":" ++ natArray (spec.encounters.map (fun id => id.value)) ++
  ",\"path\":" ++ natArray (spec.path.map (fun id => id.value)) ++ "}"

def encounterJson (spec : ContentContract.EncounterSpec) : String :=
  "{\"id\":" ++ toString spec.id.value ++
  ",\"room\":" ++ toString spec.room.value ++
  ",\"routes\":" ++ natArray (spec.routes.map (fun id => id.value)) ++
  ",\"beta_artifacts\":" ++ natArray (spec.betaArtifacts.map (fun id => id.value)) ++ "}"

def artifactSpecJson (spec : ContentContract.ArtifactSpec) : String :=
  "{\"id\":" ++ toString spec.id.value ++
  ",\"alpha_interpretation\":" ++
    optionJson (fun (fact : ContentContract.AlphaFactId) => toString fact.value)
      spec.alphaInterpretation ++ "}"

def contentContributionJson (contribution : ContentContract.Contribution) : String :=
  "{\"intel\":" ++ toString contribution.intel ++
  ",\"supplies\":" ++ toString contribution.supplies ++
  ",\"cohesion\":" ++ toString contribution.cohesion ++
  ",\"influence\":" ++ toString contribution.influence ++
  ",\"score\":" ++ toString contribution.score ++
  ",\"relics\":" ++ natArray (contribution.relics.map (fun relic => relic.value)) ++ "}"

def contentRouteOutcomeJson (outcome : ContentContract.RouteOutcome) : String :=
  "{\"route\":" ++ toString outcome.route.value ++
  ",\"extraction\":" ++ toString (contentExtractionCode outcome.extraction) ++
  ",\"operational_cost\":" ++ toString outcome.operationalCost ++
  ",\"agreement\":" ++ toString (agreementCode outcome.agreement) ++
  ",\"featured_artifact\":" ++ toString outcome.featuredArtifact.value ++
  ",\"contribution\":" ++ contentContributionJson outcome.contribution ++
  ",\"recovery\":" ++ toString outcome.recovery.value ++ "}"

def recoveryJson (recovery : ContentContract.RecoveryConsequence) : String :=
  "{\"id\":" ++ toString recovery.id.value ++
  ",\"grade\":" ++ toString (recoveryGradeCode recovery.grade) ++
  ",\"duration\":" ++ toString (recoveryDurationCode recovery.duration) ++
  ",\"implementation\":" ++ toString (recoveryImplementationCode recovery.implementation) ++
  ",\"global_meter_debit\":" ++ toString recovery.globalMeterDebit ++ "}"

def relicSpecJson (spec : ContentContract.RelicSpec) : String :=
  "{\"id\":" ++ toString spec.id.value ++
  ",\"source_encounter\":" ++ toString spec.sourceEncounter.value ++
  ",\"portable\":" ++ boolJson spec.portable ++
  ",\"market_eligible\":" ++ boolJson spec.marketEligible ++
  ",\"alpha_interpretation\":" ++
    optionJson (fun (fact : ContentContract.AlphaFactId) => toString fact.value)
      spec.alphaInterpretation ++ "}"

/-- `atEncounter` is the only location carrying a payload; the other four write `0`
and a document that writes anything else fails the canonical re-encode. -/
def custodyLocationJson (location : ContentContract.CustodyLocation) : String :=
  match location with
  | .atEncounter encounter =>
      "{\"kind\":0,\"encounter\":" ++ toString encounter.value ++ "}"
  | .crewCarried => "{\"kind\":1,\"encounter\":0}"
  | .quarantine => "{\"kind\":2,\"encounter\":0}"
  | .archive => "{\"kind\":3,\"encounter\":0}"
  | .market => "{\"kind\":4,\"encounter\":0}"

def custodyPlanJson (plan : ContentContract.CustodyPlan) : String :=
  "{\"relic\":" ++ toString plan.relic.value ++
  ",\"source\":" ++ custodyLocationJson plan.source ++
  ",\"destination\":" ++ custodyLocationJson plan.destination ++
  ",\"authority\":" ++ toString (custodyAuthorityCode plan.authority) ++
  ",\"direct_trade_allowed\":" ++ boolJson plan.directTradeAllowed ++ "}"

def candidateJson (candidate : ContentContract.CandidateRef) : String :=
  match candidate with
  | .place id => "{\"kind\":0,\"id\":" ++ toString id.value ++ "}"
  | .artifact id => "{\"kind\":1,\"id\":" ++ toString id.value ++ "}"
  | .relic id => "{\"kind\":2,\"id\":" ++ toString id.value ++ "}"

def promotionHookJson (hook : ContentContract.PromotionHook) : String :=
  "{\"candidate\":" ++ candidateJson hook.candidate ++
  ",\"alpha_value\":" ++
    optionJson (fun (fact : ContentContract.AlphaFactId) => toString fact.value)
      hook.alphaValue ++ "}"

def contentBudgetJson (budget : ContentContract.ContributionBudget) : String :=
  "{\"intel\":" ++ toString budget.intel ++
  ",\"supplies\":" ++ toString budget.supplies ++
  ",\"cohesion\":" ++ toString budget.cohesion ++
  ",\"influence\":" ++ toString budget.influence ++
  ",\"score\":" ++ toString budget.score ++
  ",\"relic_allowlist\":" ++
    natArray (budget.relicAllowlist.map (fun relic => relic.value)) ++ "}"

def canonJson (canon : ContentContract.CanonBoundary) : String :=
  "{\"tier\":" ++ toString (contentTierCode canon.tier) ++
  ",\"authoritative\":" ++ boolJson canon.authoritative ++
  ",\"claims_activated\":" ++ boolJson canon.claimsActivated ++
  ",\"automatic_promotion\":" ++ boolJson canon.automaticPromotion ++
  ",\"authority\":" ++ toString (storyAuthorityCode canon.authority) ++
  ",\"direct_alpha_facts\":" ++
    natArray (canon.directAlphaFacts.map (fun fact => fact.value)) ++ "}"

def contentJson (pack : ContentContract.RawContent) : String :=
  "{\"schema_version\":" ++ toString pack.schemaVersion ++
  ",\"place\":" ++ toString pack.place.value ++
  ",\"deck\":" ++ deckJson pack.deck ++
  ",\"officers\":" ++ jsonArray (pack.officers.map officerJson) ++
  ",\"briefings\":" ++ jsonArray (pack.briefings.map briefingShapeJson) ++
  ",\"routes\":" ++ jsonArray (pack.routes.map routeSpecJson) ++
  ",\"encounters\":" ++ jsonArray (pack.encounters.map encounterJson) ++
  ",\"artifacts\":" ++ jsonArray (pack.artifacts.map artifactSpecJson) ++
  ",\"outcomes\":" ++ jsonArray (pack.outcomes.map contentRouteOutcomeJson) ++
  ",\"recoveries\":" ++ jsonArray (pack.recoveries.map recoveryJson) ++
  ",\"relics\":" ++ jsonArray (pack.relics.map relicSpecJson) ++
  ",\"custody_plans\":" ++ jsonArray (pack.custodyPlans.map custodyPlanJson) ++
  ",\"promotion_hooks\":" ++ jsonArray (pack.promotionHooks.map promotionHookJson) ++
  ",\"turn_budget\":" ++ toString pack.turnBudget ++
  ",\"operational_budget\":" ++ toString pack.operationalBudget ++
  ",\"contribution_budget\":" ++ contentBudgetJson pack.contributionBudget ++
  ",\"canon\":" ++ canonJson pack.canon ++ "}"

private def parseRole (j : Json) (key : String) : Except String CrewRole := do
  match roleOfCode? (← objectNat j key 3) with
  | some role => pure role
  | none => throw "unknown crew role code"

private def parseOfficer (j : Json) : Except String ContentContract.OfficerSeat := do
  exactKeys j ["officer", "credential", "role"]
  pure {
    officer := ⟨← objectNat j "officer"⟩
    credential := ⟨← objectNat j "credential"⟩
    role := ← parseRole j "role"
  }

private def parseBriefingShape (j : Json) : Except String ContentContract.BriefingShape := do
  exactKeys j ["role", "observation", "recommended_route", "disclosure"]
  if (← objectNat j "disclosure" 0) != 0 then throw "unknown disclosure boundary code"
  let observation ← match observationKindOfCode? (← objectNat j "observation" 3) with
    | some kind => pure kind
    | none => throw "unknown observation kind code"
  pure {
    role := ← parseRole j "role"
    observation
    recommendedRoute := ← parseOption (← j.getObjVal? "recommended_route")
      (fun value => do pure ⟨← parseNat value⟩)
    disclosure := .privateUntilSignedHandoff
  }

private def parseRouteSpec (j : Json) : Except String ContentContract.RouteSpec := do
  exactKeys j ["id", "encounters", "path"]
  let encounters ← parseBoundedList (← j.getObjVal? "encounters")
    ContentContract.MAX_ENCOUNTERS (fun value => parseNat value)
  let path ← parseBoundedList (← j.getObjVal? "path") DeckGraph.MAX_HOTSPOTS
    (fun value => parseNat value)
  pure {
    id := ⟨← objectNat j "id"⟩
    encounters := encounters.map (fun value => ⟨value⟩)
    path := path.map (fun value => ⟨value⟩)
  }

private def parseEncounter (j : Json) : Except String ContentContract.EncounterSpec := do
  exactKeys j ["id", "room", "routes", "beta_artifacts"]
  let routes ← parseBoundedList (← j.getObjVal? "routes") ContentContract.MAX_ROUTES
    (fun value => parseNat value)
  let artifacts ← parseBoundedList (← j.getObjVal? "beta_artifacts")
    ContentContract.MAX_ARTIFACTS (fun value => parseNat value)
  pure {
    id := ⟨← objectNat j "id"⟩
    room := ⟨← objectNat j "room"⟩
    routes := routes.map (fun value => ⟨value⟩)
    betaArtifacts := artifacts.map (fun value => ⟨value⟩)
  }

private def parseArtifactSpec (j : Json) : Except String ContentContract.ArtifactSpec := do
  exactKeys j ["id", "alpha_interpretation"]
  pure {
    id := ⟨← objectNat j "id"⟩
    alphaInterpretation := ← parseOption (← j.getObjVal? "alpha_interpretation")
      (fun value => do pure ⟨← parseNat value⟩)
  }

private def parseContentContribution (j : Json) :
    Except String ContentContract.Contribution := do
  exactKeys j ["intel", "supplies", "cohesion", "influence", "score", "relics"]
  let relics ← parseBoundedList (← j.getObjVal? "relics") RELIC_LIMIT
    (fun value => parseNat value)
  pure {
    intel := ← objectNat j "intel" METRIC_LIMIT
    supplies := ← objectNat j "supplies" METRIC_LIMIT
    cohesion := ← objectNat j "cohesion" METRIC_LIMIT
    influence := ← objectNat j "influence" METRIC_LIMIT
    score := ← objectNat j "score" METRIC_LIMIT
    relics := relics.map (fun value => ⟨value⟩)
  }

private def parseContentRouteOutcome (j : Json) :
    Except String ContentContract.RouteOutcome := do
  exactKeys j ["route", "extraction", "operational_cost", "agreement",
    "featured_artifact", "contribution", "recovery"]
  let extraction ← match contentExtractionOfCode? (← objectNat j "extraction" 1) with
    | some value => pure value
    | none => throw "unknown extraction code"
  let agreement ← match agreementOfCode? (← objectNat j "agreement" 1) with
    | some value => pure value
    | none => throw "unknown agreement rule code"
  pure {
    route := ⟨← objectNat j "route"⟩
    extraction
    operationalCost := ← objectNat j "operational_cost"
      ContentContract.MAX_OPERATIONAL_BUDGET
    agreement
    featuredArtifact := ⟨← objectNat j "featured_artifact"⟩
    contribution := ← parseContentContribution (← j.getObjVal? "contribution")
    recovery := ⟨← objectNat j "recovery"⟩
  }

private def parseRecovery (j : Json) :
    Except String ContentContract.RecoveryConsequence := do
  exactKeys j ["id", "grade", "duration", "implementation", "global_meter_debit"]
  let grade ← match recoveryGradeOfCode? (← objectNat j "grade" 4) with
    | some value => pure value
    | none => throw "unknown recovery grade code"
  let duration ← match recoveryDurationOfCode? (← objectNat j "duration" 3) with
    | some value => pure value
    | none => throw "unknown recovery duration code"
  let implementation ← match recoveryImplementationOfCode?
      (← objectNat j "implementation" 1) with
    | some value => pure value
    | none => throw "unknown recovery implementation code"
  pure {
    id := ⟨← objectNat j "id"⟩
    grade
    duration
    implementation
    globalMeterDebit := ← objectNat j "global_meter_debit" METRIC_LIMIT
  }

private def parseRelicSpec (j : Json) : Except String ContentContract.RelicSpec := do
  exactKeys j ["id", "source_encounter", "portable", "market_eligible",
    "alpha_interpretation"]
  pure {
    id := ⟨← objectNat j "id"⟩
    sourceEncounter := ⟨← objectNat j "source_encounter"⟩
    portable := ← j.getObjValAs? Bool "portable"
    marketEligible := ← j.getObjValAs? Bool "market_eligible"
    alphaInterpretation := ← parseOption (← j.getObjVal? "alpha_interpretation")
      (fun value => do pure ⟨← parseNat value⟩)
  }

private def parseCustodyLocation (j : Json) :
    Except String ContentContract.CustodyLocation := do
  exactKeys j ["kind", "encounter"]
  let kind ← objectNat j "kind" 4
  let encounter ← objectNat j "encounter"
  match kind with
  | 0 => pure (.atEncounter ⟨encounter⟩)
  | 1 => pure .crewCarried
  | 2 => pure .quarantine
  | 3 => pure .archive
  | _ => pure .market

private def parseCustodyPlan (j : Json) : Except String ContentContract.CustodyPlan := do
  exactKeys j ["relic", "source", "destination", "authority", "direct_trade_allowed"]
  let authority ← match custodyAuthorityOfCode? (← objectNat j "authority" 2) with
    | some value => pure value
    | none => throw "unknown custody authority code"
  pure {
    relic := ⟨← objectNat j "relic"⟩
    source := ← parseCustodyLocation (← j.getObjVal? "source")
    destination := ← parseCustodyLocation (← j.getObjVal? "destination")
    authority
    directTradeAllowed := ← j.getObjValAs? Bool "direct_trade_allowed"
  }

private def parseCandidate (j : Json) : Except String ContentContract.CandidateRef := do
  exactKeys j ["kind", "id"]
  let kind ← objectNat j "kind" 2
  let id ← objectNat j "id"
  match kind with
  | 0 => pure (.place ⟨id⟩)
  | 1 => pure (.artifact ⟨id⟩)
  | _ => pure (.relic ⟨id⟩)

private def parsePromotionHook (j : Json) :
    Except String ContentContract.PromotionHook := do
  exactKeys j ["candidate", "alpha_value"]
  pure {
    candidate := ← parseCandidate (← j.getObjVal? "candidate")
    alphaValue := ← parseOption (← j.getObjVal? "alpha_value")
      (fun value => do pure ⟨← parseNat value⟩)
  }

private def parseContentBudget (j : Json) :
    Except String ContentContract.ContributionBudget := do
  exactKeys j ["intel", "supplies", "cohesion", "influence", "score", "relic_allowlist"]
  let allowlist ← parseBoundedList (← j.getObjVal? "relic_allowlist")
    ContentContract.MAX_RELICS (fun value => parseNat value)
  pure {
    intel := ← objectNat j "intel" METRIC_LIMIT
    supplies := ← objectNat j "supplies" METRIC_LIMIT
    cohesion := ← objectNat j "cohesion" METRIC_LIMIT
    influence := ← objectNat j "influence" METRIC_LIMIT
    score := ← objectNat j "score" METRIC_LIMIT
    relicAllowlist := allowlist.map (fun value => ⟨value⟩)
  }

private def parseCanon (j : Json) : Except String ContentContract.CanonBoundary := do
  exactKeys j ["tier", "authoritative", "claims_activated", "automatic_promotion",
    "authority", "direct_alpha_facts"]
  let tier ← match contentTierOfCode? (← objectNat j "tier" 1) with
    | some value => pure value
    | none => throw "unknown content tier code"
  let authority ← match storyAuthorityOfCode? (← objectNat j "authority" 2) with
    | some value => pure value
    | none => throw "unknown story authority code"
  let facts ← parseBoundedList (← j.getObjVal? "direct_alpha_facts")
    ContentContract.MAX_ARTIFACTS (fun value => parseNat value)
  pure {
    tier
    authoritative := ← j.getObjValAs? Bool "authoritative"
    claimsActivated := ← j.getObjValAs? Bool "claims_activated"
    automaticPromotion := ← j.getObjValAs? Bool "automatic_promotion"
    authority
    directAlphaFacts := facts.map (fun value => ⟨value⟩)
  }

private def parseContent (j : Json) : Except String ContentContract.RawContent := do
  exactKeys j ["schema_version", "place", "deck", "officers", "briefings", "routes",
    "encounters", "artifacts", "outcomes", "recoveries", "relics", "custody_plans",
    "promotion_hooks", "turn_budget", "operational_budget", "contribution_budget",
    "canon"]
  pure {
    schemaVersion := ← objectNat j "schema_version"
    place := ⟨← objectNat j "place"⟩
    deck := ← parseDeck (← j.getObjVal? "deck")
    officers := ← parseBoundedList (← j.getObjVal? "officers")
      CrewFieldMission.CREW_SIZE parseOfficer
    briefings := ← parseBoundedList (← j.getObjVal? "briefings")
      CrewFieldMission.CREW_SIZE parseBriefingShape
    routes := ← parseBoundedList (← j.getObjVal? "routes")
      ContentContract.MAX_ROUTES parseRouteSpec
    encounters := ← parseBoundedList (← j.getObjVal? "encounters")
      ContentContract.MAX_ENCOUNTERS parseEncounter
    artifacts := ← parseBoundedList (← j.getObjVal? "artifacts")
      ContentContract.MAX_ARTIFACTS parseArtifactSpec
    outcomes := ← parseBoundedList (← j.getObjVal? "outcomes")
      (2 * ContentContract.MAX_ROUTES) parseContentRouteOutcome
    recoveries := ← parseBoundedList (← j.getObjVal? "recoveries")
      ContentContract.MAX_ENCOUNTERS parseRecovery
    relics := ← parseBoundedList (← j.getObjVal? "relics")
      ContentContract.MAX_RELICS parseRelicSpec
    custodyPlans := ← parseBoundedList (← j.getObjVal? "custody_plans")
      ContentContract.MAX_RELICS parseCustodyPlan
    promotionHooks := ← parseBoundedList (← j.getObjVal? "promotion_hooks")
      ContentContract.MAX_ARTIFACTS parsePromotionHook
    turnBudget := ← objectNat j "turn_budget" ContentContract.MAX_TURN_BUDGET
    operationalBudget := ← objectNat j "operational_budget"
      ContentContract.MAX_OPERATIONAL_BUDGET
    contributionBudget := ← parseContentBudget (← j.getObjVal? "contribution_budget")
    canon := ← parseCanon (← j.getObjVal? "canon")
  }

/-! ## The field session — parsed back into `ProductionSigning.sessionJson`

⚑ The ENCODER here is `CrewFieldMission.ProductionSigning.sessionJson` itself, not a
copy of it.  The session reaches the seat and handoff signing preimages, so the bytes a
curator publishes in the manifest and the bytes a player's key signs over are produced
by ONE function.  Only the parser is new. -/

private def parseArtifactRef (j : Json) : Except String ArtifactRef := do
  exactKeys j ["mission", "artifact", "source", "content"]
  pure {
    missionId := ⟨← objectNat j "mission"⟩
    artifactId := ⟨← objectNat j "artifact"⟩
    sourceDigest := ← objectDigest j "source"
    contentDigest := ← objectDigest j "content"
  }

private def parseMetric (j : Json) (key : String) : Except String Metric := do
  let value ← objectNat j key METRIC_LIMIT
  if h : value < METRIC_LIMIT + 1 then pure ⟨value, h⟩
  else throw "meter exceeds the platform ceiling"

private def parseCoreBudget (j : Json) : Except String ContributionBudget := do
  exactKeys j ["intel", "supplies", "cohesion", "influence", "score", "relics"]
  let relics ← objectNat j "relics" RELIC_LIMIT
  if h : relics < RELIC_LIMIT + 1 then
    pure {
      intel := ← parseMetric j "intel"
      supplies := ← parseMetric j "supplies"
      cohesion := ← parseMetric j "cohesion"
      influence := ← parseMetric j "influence"
      score := ← parseMetric j "score"
      relics := ⟨relics, h⟩
    }
  else throw "relic budget exceeds the platform ceiling"

private def parseMissionSpec (j : Json) : Except String MissionSpec := do
  exactKeys j ["mission", "artifact", "epoch", "federation", "content_root",
    "activation", "content_session", "run_seed", "budget", "allowed_relics", "privacy",
    "ballot"]
  let missionId : MissionId := ⟨← objectNat j "mission"⟩
  let artifact ← parseArtifactRef (← j.getObjVal? "artifact")
  let epoch : EpochId := ⟨← objectNat j "epoch"⟩
  let federationId ← objectDigest j "federation"
  let contentRoot ← objectDigest j "content_root"
  let activationDigest ← objectDigest j "activation"
  let contentSession ← objectDigest j "content_session"
  let runSeed ← objectDigest j "run_seed"
  let budget ← parseCoreBudget (← j.getObjVal? "budget")
  let relicValues ← parseBoundedList (← j.getObjVal? "allowed_relics")
    MISSION_RELIC_LIMIT (fun value => parseNat value)
  let allowedRelics : Finset RelicId :=
    (relicValues.map (fun value => (⟨value⟩ : RelicId))).toFinset
  let privacy ← match privacyGradeOfCode? (← objectNat j "privacy" 3) with
    | some value => pure value
    | none => throw "unknown privacy grade code"
  let ballot ← match ballotRegimeOfCode? (← objectNat j "ballot" 4) with
    | some value => pure value
    | none => throw "unknown ballot regime code"
  if hmatch : artifact.missionId = missionId then
    if hbound : allowedRelics.card ≤ MISSION_RELIC_LIMIT then
      pure {
        missionId, artifact, epoch, federationId, contentRoot, activationDigest,
        contentSession, runSeed, budget, allowedRelics, privacy, ballot
        artifact_matches := hmatch
        allowed_relics_bounded := hbound
      }
    else throw "mission relic catalogue exceeds the platform ceiling"
  else throw "the mission artifact names another mission"

private def parsePolicy (j : Json) : Except String ActivityOutcome.Policy := do
  exactKeys j ["mission", "allowed_beta", "result_limit"]
  let mission ← parseMissionSpec (← j.getObjVal? "mission")
  let betas ← parseBoundedList (← j.getObjVal? "allowed_beta")
    ActivityOutcome.BETA_CATALOGUE_LIMIT parseArtifactRef
  let allowedBeta : Finset ArtifactRef := betas.toFinset
  let limit ← objectNat j "result_limit" ActivityOutcome.BETA_CANDIDATE_LIMIT
  if hlimit : limit < ActivityOutcome.BETA_CANDIDATE_LIMIT + 1 then
    if hcard : allowedBeta.card ≤ ActivityOutcome.BETA_CATALOGUE_LIMIT then
      pure { mission, allowedBeta, resultLimit := ⟨limit, hlimit⟩,
             catalogue_bounded := hcard }
    else throw "beta catalogue exceeds the platform ceiling"
  else throw "result limit exceeds the platform ceiling"

private def parseSeat (j : Json) : Except String Seat := do
  exactKeys j ["seat", "player_key", "credential", "role", "initial_counter"]
  pure {
    id := ⟨← objectNat j "seat"⟩
    playerKey := ← objectDigest j "player_key"
    credential := ⟨← objectNat j "credential"⟩
    role := ← parseRole j "role"
    initialCounter := ← objectNat j "initial_counter"
  }

private def parseRawContribution (j : Json) : Except String RawContribution := do
  exactKeys j ["intel", "supplies", "cohesion", "influence", "score", "relics"]
  let relics ← parseBoundedList (← j.getObjVal? "relics") RELIC_LIMIT
    (fun value => parseNat value)
  pure {
    intel := ← objectNat j "intel" METRIC_LIMIT
    supplies := ← objectNat j "supplies" METRIC_LIMIT
    cohesion := ← objectNat j "cohesion" METRIC_LIMIT
    influence := ← objectNat j "influence" METRIC_LIMIT
    score := ← objectNat j "score" METRIC_LIMIT
    relics := relics.map (fun value => ⟨value⟩)
  }

private def parseRawOutcome (j : Json) : Except String ActivityOutcome.Raw := do
  exactKeys j ["contribution", "beta_candidates"]
  pure {
    contribution := ← parseRawContribution (← j.getObjVal? "contribution")
    betaCandidates := ← parseBoundedList (← j.getObjVal? "beta_candidates")
      ActivityOutcome.BETA_CANDIDATE_LIMIT parseArtifactRef
  }

private def parseRouteOutcomeSpec (j : Json) :
    Except String CrewFieldMission.RouteOutcomeSpec := do
  exactKeys j ["route", "extraction", "cost", "featured", "outcome"]
  let route ← match routeOfCode? (← objectNat j "route" 2) with
    | some value => pure value
    | none => throw "unknown field route code"
  let extraction ← match extractionOfCode? (← objectNat j "extraction" 1) with
    | some value => pure value
    | none => throw "unknown extraction code"
  pure {
    route
    extraction
    operationalCost := ← objectNat j "cost" ContentContract.MAX_OPERATIONAL_BUDGET
    featuredArtifact := ← parseArtifactRef (← j.getObjVal? "featured")
    outcome := ← parseRawOutcome (← j.getObjVal? "outcome")
  }

private def parseSession (j : Json) : Except String CrewFieldMission.SessionDigest := do
  exactKeys j ["federation", "content_session", "epoch", "mission", "relay", "privacy",
    "briefing_suite", "briefing_commitment", "message_suite", "signing_suite", "roster",
    "policy", "budget", "route_outcomes"]
  if (← objectNat j "privacy" 0) != 0 then throw "unknown briefing privacy code"
  pure {
    federationId := ← objectDigest j "federation"
    contentSession := ← objectDigest j "content_session"
    missionEpoch := ⟨← objectNat j "epoch"⟩
    missionId := ⟨← objectNat j "mission"⟩
    relayId := ← objectDigest j "relay"
    briefingPrivacy := .trustedDealerOperatorVisibleThenPublicHandoff
    briefingHashSuiteId := ← objectDigest j "briefing_suite"
    briefingCommitment := ← objectDigest j "briefing_commitment"
    messageDigestSuiteId := ← objectDigest j "message_suite"
    signingSuiteId := ← objectDigest j "signing_suite"
    roster := ← parseBoundedList (← j.getObjVal? "roster")
      CrewFieldMission.CREW_SIZE parseSeat
    policy := ← parsePolicy (← j.getObjVal? "policy")
    operationalBudget := ← objectNat j "budget" ContentContract.MAX_OPERATIONAL_BUDGET
    routeOutcomes := ← parseBoundedList (← j.getObjVal? "route_outcomes")
      (2 * ContentContract.MAX_ROUTES) parseRouteOutcomeSpec
  }

/-! ## The authored activation document -/

def briefingAssignmentJson (briefing : CrewFieldMission.BriefingAssignment) : String :=
  "{\"seat\":" ++ toString briefing.seat.value ++
  ",\"observation\":" ++ toString briefing.observation.code ++ "}"

def routeBindingJson (binding : RouteBinding) : String :=
  "{\"field\":" ++ toString binding.field.code ++
  ",\"content\":" ++ toString binding.content.value ++ "}"

def artifactBindingJson (binding : ArtifactBinding) : String :=
  "{\"field\":" ++ CrewFieldMission.ProductionSigning.artifactJson binding.field ++
  ",\"content\":" ++ toString binding.content.value ++ "}"

def relicBindingJson (binding : RelicBinding) : String :=
  "{\"field\":" ++ toString binding.field.value ++
  ",\"content\":" ++ toString binding.content.value ++ "}"

def salvageRuleJson (rule : OrdinarySalvageRule) : String :=
  "{\"route\":" ++ toString rule.route.code ++
  ",\"extraction\":" ++ toString (extractionCode rule.extraction) ++
  ",\"part\":" ++ toString rule.part.value ++
  ",\"quantity\":" ++ toString rule.quantity ++ "}"

/-- The canonical activation document.  `field_session` is
`ProductionSigning.sessionJson` — the signing spelling — so the bytes the world commits
to and the bytes a seat's key signs over cannot drift apart. -/
def activationJson (raw : RawActivation) : String :=
  "{\"format\":" ++ jsonString ACTIVATION_FORMAT ++
  ",\"activation_id\":" ++ jsonString (Emit.bytes32Hex raw.activationId) ++
  ",\"roster_binding\":" ++ jsonString (Emit.bytes32Hex raw.rosterBinding) ++
  ",\"content_digest\":" ++ jsonString (Emit.bytes32Hex raw.contentDigest) ++
  ",\"field_session\":" ++
    CrewFieldMission.ProductionSigning.sessionJson raw.fieldSession ++
  ",\"briefings\":" ++ jsonArray (raw.briefings.map briefingAssignmentJson) ++
  ",\"content\":" ++ contentJson raw.content ++
  ",\"route_bindings\":" ++ jsonArray (raw.routeBindings.map routeBindingJson) ++
  ",\"artifact_bindings\":" ++ jsonArray (raw.artifactBindings.map artifactBindingJson) ++
  ",\"relic_bindings\":" ++ jsonArray (raw.relicBindings.map relicBindingJson) ++
  ",\"ordinary_salvage\":" ++ jsonArray (raw.ordinarySalvage.map salvageRuleJson) ++
  ",\"replay_verifier_id\":" ++ jsonString (Emit.bytes32Hex raw.replayVerifierId) ++ "}"

private def parseBriefingAssignment (j : Json) :
    Except String CrewFieldMission.BriefingAssignment := do
  exactKeys j ["seat", "observation"]
  let observation ← match observationOfCode? (← objectNat j "observation" 41) with
    | some value => pure value
    | none => throw "unknown private observation code"
  pure { seat := ⟨← objectNat j "seat"⟩, observation }

private def parseRouteBinding (j : Json) : Except String RouteBinding := do
  exactKeys j ["field", "content"]
  let field ← match routeOfCode? (← objectNat j "field" 2) with
    | some value => pure value
    | none => throw "unknown field route code"
  pure { field, content := ⟨← objectNat j "content"⟩ }

private def parseArtifactBinding (j : Json) : Except String ArtifactBinding := do
  exactKeys j ["field", "content"]
  pure {
    field := ← parseArtifactRef (← j.getObjVal? "field")
    content := ⟨← objectNat j "content"⟩
  }

private def parseRelicBinding (j : Json) : Except String RelicBinding := do
  exactKeys j ["field", "content"]
  pure { field := ⟨← objectNat j "field"⟩, content := ⟨← objectNat j "content"⟩ }

private def parseSalvageRule (j : Json) : Except String OrdinarySalvageRule := do
  exactKeys j ["route", "extraction", "part", "quantity"]
  let route ← match routeOfCode? (← objectNat j "route" 2) with
    | some value => pure value
    | none => throw "unknown field route code"
  let extraction ← match extractionOfCode? (← objectNat j "extraction" 1) with
    | some value => pure value
    | none => throw "unknown extraction code"
  pure {
    route
    extraction
    part := ⟨← objectNat j "part"⟩
    quantity := ← objectNat j "quantity" MAX_PART_QUANTITY
  }

private def parseActivation (j : Json) : Except String RawActivation := do
  exactKeys j ["format", "activation_id", "roster_binding", "content_digest",
    "field_session", "briefings", "content", "route_bindings", "artifact_bindings",
    "relic_bindings", "ordinary_salvage", "replay_verifier_id"]
  if (← j.getObjValAs? String "format") != ACTIVATION_FORMAT then
    throw "wrong activation format"
  pure {
    activationId := ← objectDigest j "activation_id"
    rosterBinding := ← objectDigest j "roster_binding"
    contentDigest := ← objectDigest j "content_digest"
    fieldSession := ← parseSession (← j.getObjVal? "field_session")
    briefings := ← parseBoundedList (← j.getObjVal? "briefings")
      CrewFieldMission.CREW_SIZE parseBriefingAssignment
    content := ← parseContent (← j.getObjVal? "content")
    routeBindings := ← parseBoundedList (← j.getObjVal? "route_bindings")
      ContentContract.MAX_ROUTES parseRouteBinding
    artifactBindings := ← parseBoundedList (← j.getObjVal? "artifact_bindings")
      ContentContract.MAX_ARTIFACTS parseArtifactBinding
    relicBindings := ← parseBoundedList (← j.getObjVal? "relic_bindings")
      ContentContract.MAX_RELICS parseRelicBinding
    ordinarySalvage := ← parseBoundedList (← j.getObjVal? "ordinary_salvage")
      MAX_PART_RULES parseSalvageRule
    replayVerifierId := ← objectDigest j "replay_verifier_id"
  }

def decodeActivationWithLimit (limit : Nat) (bytes : String) : Option RawActivation :=
  canonicalDecode parseActivation activationJson limit bytes

def decodeActivation (bytes : String) : Option RawActivation :=
  decodeActivationWithLimit ACTIVATION_BYTE_LIMIT bytes

theorem decodeActivationWithLimit_reencodes {limit : Nat} {bytes : String}
    {value : RawActivation} (accepted : decodeActivationWithLimit limit bytes = some value) :
    activationJson value = bytes :=
  canonicalDecode_reencodes parseActivation activationJson limit bytes value accepted

theorem decodeActivation_reencodes {bytes : String} {value : RawActivation}
    (accepted : decodeActivation bytes = some value) : activationJson value = bytes :=
  decodeActivationWithLimit_reencodes accepted

-- `the_empty_document_is_not_an_activation` (the refusal sentinel is total: `""` is not
-- a decodable input) is pinned verbatim in `CrewFieldMissionAdmissionFixtures`.

#assert_axioms decodeActivationWithLimit_reencodes
#assert_axioms decodeActivation_reencodes

/-! ## The seal is MINTED, never accepted

`RawConfig` and `SessionDigest` are the same fourteen fields; `RawConfig.sessionDigest`
is the projection and `configOfSession` is its inverse.  That is what lets the seal be
a FUNCTION of the admitted bytes: there is no argument, anywhere in this module, of
type `CrewFieldMission.RunSeal`. -/

def configOfSession (session : CrewFieldMission.SessionDigest) :
    CrewFieldMission.RawConfig where
  federationId := session.federationId
  contentSession := session.contentSession
  missionEpoch := session.missionEpoch
  missionId := session.missionId
  relayId := session.relayId
  briefingPrivacy := session.briefingPrivacy
  briefingHashSuiteId := session.briefingHashSuiteId
  briefingCommitment := session.briefingCommitment
  messageDigestSuiteId := session.messageDigestSuiteId
  signingSuiteId := session.signingSuiteId
  roster := session.roster
  policy := session.policy
  operationalBudget := session.operationalBudget
  routeOutcomes := session.routeOutcomes

theorem configOfSession_sessionDigest (session : CrewFieldMission.SessionDigest) :
    (configOfSession session).sessionDigest = session := by
  cases session
  rfl

theorem sessionDigest_configOfSession (raw : CrewFieldMission.RawConfig) :
    configOfSession raw.sessionDigest = raw := by
  cases raw
  rfl

/-- The only seal producer this module has.  Every function inside it — briefing
digest, message digest, signature verifier — is pinned structurally to the production
suite by `ProductionSigning.activate?`; a caller supplies DATA and never a verifier,
and cannot supply a seal at all. -/
def mintSeal? (raw : RawActivation) : Option CrewFieldMission.RunSeal :=
  CrewFieldMission.ProductionSigning.activate? (configOfSession raw.fieldSession)
    raw.briefings

/-- A minted seal always carries the admitted field session, so
`CrewFieldMissionRuntime.activate?`'s `sealSessionExact` gate cannot refuse for a
reason the admitted document did not cause.  Proved from the round trip, not observed
on a fixture. -/
theorem mintSeal_session_is_the_admitted_field_session {raw : RawActivation}
    {runSeal : CrewFieldMission.RunSeal} (minted : mintSeal? raw = some runSeal) :
    runSeal.session = raw.fieldSession := by
  unfold mintSeal? CrewFieldMission.ProductionSigning.activate? at minted
  split at minted
  · split at minted
    · split at minted
      · have same := Option.some.inj minted
        rw [← same]
        exact configOfSession_sessionDigest raw.fieldSession
      · simp at minted
    · simp at minted
  · simp at minted

#assert_axioms configOfSession_sessionDigest
#assert_axioms sessionDigest_configOfSession
#assert_axioms mintSeal_session_is_the_admitted_field_session

/-! ## The world-scoped authenticated activation -/

/-- An activation that is a member of an activated world, with every step of that claim
as a proof field.  `mk` is private and `authorizeCrewActivationForWorld?` is the only
producer — and that producer MINTS the seal rather than receiving one, which is what
makes `fixtureRunSeal` unreachable from here rather than merely unused. -/
structure WorldScopedCrewActivation where
  private mk ::
  world : WorldActivation.WorldIdentity
  manifest : ActivatedContent.ValidatedManifest
  component : ActivatedContent.Component
  raw : RawActivation
  activation : Activation
  root_and_scope_exact : manifest.raw.matchesWorldB world = true
  located : ActivatedContent.componentByName? manifest.raw.components ACTIVATION_COMPONENT
    = some component
  activation_bytes_exact : component.bytesUtf8 = activationJson raw
  /-- ⚑ THE CLOSURE.  The seal the activation was pinned to is the one this module
  minted from `raw` — there is no other value it could be. -/
  seal_minted_from_the_admitted_bytes :
    (mintSeal? raw).bind (fun runSeal => CrewFieldMissionRuntime.activate? raw runSeal)
      = some activation
  federation_exact : raw.fieldSession.federationId = world.federationId
  session_exact : raw.fieldSession.contentSession = world.contentSession
  deck_federation_exact : raw.content.deck.activation.federationId = world.federationId
  deck_session_exact : raw.content.deck.activation.contentSession = world.contentSession
  deck_epoch_exact : raw.content.deck.activation.contentEpoch = world.contentEpoch
  deck_activation_exact :
    raw.content.deck.activation.activationDigest = world.activationDigest

def authorizeCrewActivationForWorld? (world : WorldActivation.WorldIdentity)
    (manifest : ActivatedContent.ValidatedManifest) : Option WorldScopedCrewActivation :=
  if worldExact : manifest.raw.matchesWorldB world = true then
    match located : ActivatedContent.componentByName? manifest.raw.components
        ACTIVATION_COMPONENT with
    | none => none
    | some component =>
        match decoded : decodeActivation component.bytesUtf8 with
        | none => none
        | some raw =>
            match sealed : (mintSeal? raw).bind
                (fun runSeal => CrewFieldMissionRuntime.activate? raw runSeal) with
            | none => none
            | some activation =>
                if federation : raw.fieldSession.federationId = world.federationId then
                  if session : raw.fieldSession.contentSession = world.contentSession then
                    if deckFederation :
                        raw.content.deck.activation.federationId = world.federationId then
                      if deckSession :
                          raw.content.deck.activation.contentSession
                            = world.contentSession then
                        if deckEpoch :
                            raw.content.deck.activation.contentEpoch
                              = world.contentEpoch then
                          if deckActivation :
                              raw.content.deck.activation.activationDigest
                                = world.activationDigest then
                            some ⟨world, manifest, component, raw, activation, worldExact,
                              located, (decodeActivation_reencodes decoded).symm, sealed,
                              federation, session, deckFederation, deckSession, deckEpoch,
                              deckActivation⟩
                          else none
                        else none
                      else none
                    else none
                  else none
                else none
  else none

/-- The bytes the manifest carries ARE this activation's canonical encoding, so the
digest the world's content root commits to is a digest of exactly this roster, this
policy and this content pack. -/
theorem WorldScopedCrewActivation.exact_activation_bytes
    (member : WorldScopedCrewActivation) :
    member.component.bytesUtf8 = activationJson member.activation.raw := by
  have same : member.activation.raw = member.raw := by
    have sealed := member.seal_minted_from_the_admitted_bytes
    cases minted : mintSeal? member.raw with
    | none => rw [minted] at sealed; simp at sealed
    | some runSeal =>
        rw [minted] at sealed
        simp only [Option.bind] at sealed
        unfold CrewFieldMissionRuntime.activate? at sealed
        split at sealed
        · split at sealed
          · have inj := Option.some.inj sealed
            rw [← inj]
          · simp at sealed
        · simp at sealed
  rw [same]
  exact member.activation_bytes_exact

/-- The manifest this activation came out of is the world's own content root, not
merely a manifest that happens to name the same federation. -/
theorem WorldScopedCrewActivation.exact_content_root
    (member : WorldScopedCrewActivation) :
    ActivatedContent.manifestRoot? member.manifest.raw = some member.world.contentRoot := by
  have exact := member.root_and_scope_exact
  unfold ActivatedContent.Manifest.matchesWorldB at exact
  obtain ⟨exact, _⟩ := Eq.mp (Bool.and_eq_true _ _) exact
  obtain ⟨exact, _⟩ := Eq.mp (Bool.and_eq_true _ _) exact
  obtain ⟨exact, _⟩ := Eq.mp (Bool.and_eq_true _ _) exact
  obtain ⟨_, root⟩ := Eq.mp (Bool.and_eq_true _ _) exact
  exact of_decide_eq_true root

/-- ⚑ THE STRUCTURAL STATEMENT, and the reason an `@[export]` may exist.  Whatever
seal the admitted activation was pinned to, it is one `mintSeal?` produced from the
admitted bytes.  A caller-supplied seal — the public `fixtureRunSeal` included —
appears nowhere in the chain, because `WorldScopedCrewActivation.mk` is private and the
sole producer takes no seal argument. -/
theorem WorldScopedCrewActivation.the_seal_was_minted_here
    (member : WorldScopedCrewActivation) :
    ∃ runSeal, mintSeal? member.raw = some runSeal ∧
      CrewFieldMissionRuntime.activate? member.raw runSeal = some member.activation := by
  have sealed := member.seal_minted_from_the_admitted_bytes
  cases minted : mintSeal? member.raw with
  | none => rw [minted] at sealed; simp at sealed
  | some runSeal =>
      refine ⟨runSeal, rfl, ?_⟩
      rw [minted] at sealed
      simpa using sealed

/-! ⚑ The constructor-privacy half of this claim is NOT ratcheted here.  A `private`
name is visible inside its own module, so `fail_if_success (have _ :=
WorldScopedCrewActivation.mk)` would SUCCEED in this file while guarding nothing — a
falsifier that cannot falsify.  It lives in `CrewFieldMissionRuntimeBoundary`, which
imports this module and is therefore a real importer. -/

#assert_axioms WorldScopedCrewActivation.exact_activation_bytes
#assert_axioms WorldScopedCrewActivation.exact_content_root
#assert_axioms WorldScopedCrewActivation.the_seal_was_minted_here

/-! ## The admitted step surface, and the export

`stepProcess` is the read-only per-handoff surface: canonical
`POA-CREW-FIELD-STEP-IN-1` bytes in, canonical `POA-CREW-FIELD-STEP-OUT-1` bytes out,
carrying the exact preimage the next seat's key must sign.  It takes a pinned
`Activation`, and the ONLY `Activation` this module can produce comes out of the
witness above. -/

structure StepEnvelopeWire where
  world : WorldActivation.WorldIdentity
  manifestJson : String
  stepRequestJson : String
deriving DecidableEq

def StepEnvelopeWire.toJson (envelope : StepEnvelopeWire) : String :=
  "{\"format\":" ++ jsonString STEP_ENVELOPE_FORMAT ++
  ",\"world\":" ++ envelope.world.toJson ++
  ",\"manifest_json\":" ++ jsonString envelope.manifestJson ++
  ",\"step_request_json\":" ++ jsonString envelope.stepRequestJson ++ "}"

private def parseWorldIdentity (j : Json) :
    Except String WorldActivation.WorldIdentity := do
  exactKeys j ["federation_id", "content_root", "activation_digest", "content_session",
    "content_epoch"]
  pure {
    federationId := ← objectDigest j "federation_id"
    contentRoot := ← objectDigest j "content_root"
    activationDigest := ← objectDigest j "activation_digest"
    contentSession := ← objectDigest j "content_session"
    contentEpoch := ⟨← objectNat j "content_epoch"⟩
  }

private def parseStepEnvelope (j : Json) : Except String StepEnvelopeWire := do
  exactKeys j ["format", "world", "manifest_json", "step_request_json"]
  if (← j.getObjValAs? String "format") != STEP_ENVELOPE_FORMAT then
    throw "wrong step envelope format"
  let manifestJson ← j.getObjValAs? String "manifest_json"
  if manifestJson.utf8ByteSize > ActivatedContent.MANIFEST_BYTE_LIMIT then
    throw "manifest exceeds bound"
  let stepRequestJson ← j.getObjValAs? String "step_request_json"
  if stepRequestJson.utf8ByteSize > CrewFieldMissionRuntime.WIRE_BYTE_LIMIT then
    throw "step request exceeds bound"
  pure {
    world := ← parseWorldIdentity (← j.getObjVal? "world")
    manifestJson
    stepRequestJson
  }

def decodeStepEnvelope (bytes : String) : Option StepEnvelopeWire :=
  canonicalDecode parseStepEnvelope StepEnvelopeWire.toJson ENVELOPE_BYTE_LIMIT bytes

theorem decodeStepEnvelope_reencodes {bytes : String} {envelope : StepEnvelopeWire}
    (accepted : decodeStepEnvelope bytes = some envelope) :
    envelope.toJson = bytes :=
  canonicalDecode_reencodes parseStepEnvelope StepEnvelopeWire.toJson
    ENVELOPE_BYTE_LIMIT bytes envelope accepted

/-- ⚑ There is no `Activation` argument and no `RunSeal` argument.  The activation is
built here, from an admitted manifest component, over a seal this module minted. -/
def stepForAdmittedWorld? (envelope : StepEnvelopeWire) : Option String := do
  let manifest ← ActivatedContent.decodeManifest envelope.manifestJson
  let member ← authorizeCrewActivationForWorld? envelope.world manifest
  CrewFieldMissionRuntime.stepProcess member.activation envelope.stepRequestJson

/-- **`@[export dregg_poa_crew_field_step]`** — the crew field-mission per-handoff read
boundary.  `""` is the single refusal, for every reason: envelope not canonical, world
not matched by the manifest, no `poa.crew-field-mission.activation.v1` component, the
component not canonical, the activation invalid, the SEAL UNMINTABLE (fixture suite, or
a briefing deck whose production commitment does not check), or the step itself
refused.

⚠ The world argument is audited by PERSISTENCE, exactly as it is for
`dregg_poa_activated_content_authorize` and `dregg_poa_galley_daily_judge`.  A host
that passes a world nobody signed gets an answer about nothing.  What this export does
NOT depend on that audit for is the seal: a fabricated world cannot produce a
fixture-suited seal, because minting refuses the fixture suite before the world is
consulted. -/
@[export dregg_poa_crew_field_step]
def stepWire (bytes : String) : String :=
  match decodeStepEnvelope bytes with
  | none => ""
  | some envelope => (stepForAdmittedWorld? envelope).getD ""

#assert_axioms decodeStepEnvelope_reencodes

/-! ## The ENTRY POINT — the seat-admission preimage, and its export

⚑ 2026-08-09.  `stepWire` above answers "what does the next seat sign?", and it answers
it only for a caller that can already present that seat's ML-DSA-65 SEAT-ADMISSION
envelope.  Producing that envelope requires knowing the seat-admission preimage bytes,
and until this section nothing emitted them: they were reachable only by evaluating
`CrewFieldMission.ProductionSigning.seatPreimageJson` inside Lean.  A browser that
re-derived them would be building the exact body the step surface's own docblock
forbids a client to build — "a client signs THESE BYTES; it does not build a body,
does not derive a `preRoot`, and does not re-encode anything."  So the organ had a
handoff surface and no way to take the first seat.

The read below is the same admission path as `stepWire` — the manifest is located by
exact component name inside a manifest whose SHA-256 root IS the audited world's
`contentRoot`, decoded canonically, and the seal is MINTED from those bytes — and it
takes no `RunSeal` and no `Activation` argument, for the same structural reason. -/

structure SeatEnvelopeWire where
  world : WorldActivation.WorldIdentity
  manifestJson : String
  seat : Nat
deriving DecidableEq

def SeatEnvelopeWire.toJson (envelope : SeatEnvelopeWire) : String :=
  "{\"format\":" ++ jsonString SEAT_ENVELOPE_FORMAT ++
  ",\"world\":" ++ envelope.world.toJson ++
  ",\"manifest_json\":" ++ jsonString envelope.manifestJson ++
  ",\"seat\":" ++ toString envelope.seat ++ "}"

private def parseSeatEnvelope (j : Json) : Except String SeatEnvelopeWire := do
  exactKeys j ["format", "world", "manifest_json", "seat"]
  if (← j.getObjValAs? String "format") != SEAT_ENVELOPE_FORMAT then
    throw "wrong seat envelope format"
  let manifestJson ← j.getObjValAs? String "manifest_json"
  if manifestJson.utf8ByteSize > ActivatedContent.MANIFEST_BYTE_LIMIT then
    throw "manifest exceeds bound"
  let seat ← objectNat j "seat"
  if seat ≥ CrewFieldMission.CREW_SIZE then throw "seat is off the roster"
  pure {
    world := ← parseWorldIdentity (← j.getObjVal? "world")
    manifestJson
    seat
  }

def decodeSeatEnvelope (bytes : String) : Option SeatEnvelopeWire :=
  canonicalDecode parseSeatEnvelope SeatEnvelopeWire.toJson ENVELOPE_BYTE_LIMIT bytes

theorem decodeSeatEnvelope_reencodes {bytes : String} {envelope : SeatEnvelopeWire}
    (accepted : decodeSeatEnvelope bytes = some envelope) :
    envelope.toJson = bytes :=
  canonicalDecode_reencodes parseSeatEnvelope SeatEnvelopeWire.toJson
    ENVELOPE_BYTE_LIMIT bytes envelope accepted

structure SeatPreimageResponseWire where
  activationId : Digest32
  rosterBinding : Digest32
  seat : Nat
  /-- ⚑ The payload: the exact canonical `POA-CREW-SEAT-SIGNING-1` preimage bytes this
  seat's key must sign, under `CrewFieldMission.ProductionSigning.SEAT_SIGNING_CONTEXT`.
  A client signs THESE BYTES — the same discipline as `StepResponseWire.signingMessage`,
  one move earlier in the run. -/
  signingMessage : String
deriving DecidableEq

def SeatPreimageResponseWire.toJson (wire : SeatPreimageResponseWire) : String :=
  "{\"format\":" ++ jsonString SEAT_OUTPUT_FORMAT ++
    ",\"activation_id\":" ++ jsonString (Emit.bytes32Hex wire.activationId) ++
    ",\"roster_binding\":" ++ jsonString (Emit.bytes32Hex wire.rosterBinding) ++
    ",\"seat\":" ++ toString wire.seat ++
    ",\"signing_message\":" ++ jsonString wire.signingMessage ++ "}"

/-- The seat-admission preimage over an admitted activation's own field session.

⚠ It is read off `raw.fieldSession`, not off a `CrewFieldMission.Config`, and that is
sound rather than convenient: `CrewFieldMissionRuntime.Activation` carries
`sealSessionExact : runSeal.session = raw.fieldSession` as a PROOF FIELD, and
`RunSeal.session` is the seal's own `config.raw.sessionDigest`.  So the session this
reads and the session `authenticateSeat?` checks against are the same document by the
activation's construction, not by agreement. -/
def seatPreimageOf (raw : RawActivation) (seat : Seat) : String :=
  CrewFieldMission.ProductionSigning.seatPreimageJson
    ((CrewFieldMission.SeatAdmissionBody.mk raw.fieldSession seat).signingPreimage
      raw.fieldSession.messageDigestSuiteId raw.fieldSession.signingSuiteId)

/-- ⚑ WHY THIS SURFACE MAY BE PUBLIC, AND WHY THE HANDOFF ONE MAY NOT.

`RunSeal.nextSigningPreimage?` is gated behind seat authentication because a
`HandoffBody` carries an `observation` — the seat's private briefing — so an ungated
handoff surface would publish the next seat's briefing to anyone who asked.  A
`SeatAdmissionBody` carries a session and a seat and NOTHING ELSE.  This theorem is
that difference, stated: the emitted preimage is a function of the field session alone,
and the field session is verbatim inside `activationJson raw`, which IS the manifest
component the caller handed in.  It therefore confers nothing on a caller that the
bytes it already supplied do not. -/
theorem the_seat_preimage_reads_only_the_admitted_field_session
    (left right : RawActivation) (seat : Seat)
    (session : left.fieldSession = right.fieldSession) :
    seatPreimageOf left seat = seatPreimageOf right seat := by
  simp [seatPreimageOf, session]

/-- ⚠ There is no `Activation` argument and no `RunSeal` argument, exactly as at
`stepForAdmittedWorld?`.  The activation is built here, from an admitted manifest
component, over a seal this module minted — so a caller-supplied fixture seal
structurally cannot reach it. -/
def seatPreimageForAdmittedWorld? (envelope : SeatEnvelopeWire) : Option String := do
  let manifest ← ActivatedContent.decodeManifest envelope.manifestJson
  let member ← authorizeCrewActivationForWorld? envelope.world manifest
  let seat ← seatById? member.raw.fieldSession.roster ⟨envelope.seat⟩
  some (SeatPreimageResponseWire.toJson {
    activationId := member.raw.activationId
    rosterBinding := member.raw.rosterBinding
    seat := envelope.seat
    signingMessage := seatPreimageOf member.raw seat })

/-- **`@[export dregg_poa_crew_field_seat_preimage]`** — the crew field-mission SEAT
ADMISSION read boundary, and the organ's entry point.  `""` is the single refusal, for
every reason: envelope not canonical, world not matched by the manifest, no
`poa.crew-field-mission.activation.v1` component, the component not canonical, the
activation invalid, the SEAL UNMINTABLE (fixture suite, or a briefing deck whose
production commitment does not check), or the named seat not on the admitted roster.

⚠ The world argument is audited by PERSISTENCE, exactly as it is for `stepWire`.  A
host that passes a world nobody signed gets an answer about nothing — and, as there,
what this does NOT depend on that audit for is the seal.

⚠ This export ANSWERS A QUESTION; it does not admit anybody.  The reply is the bytes to
sign, never a capability: `SeatCapability.mk` is private and its only producer is
`authenticateSeat?`, which still demands a signature this surface cannot produce. -/
@[export dregg_poa_crew_field_seat_preimage]
def seatPreimageWire (bytes : String) : String :=
  match decodeSeatEnvelope bytes with
  | none => ""
  | some envelope => (seatPreimageForAdmittedWorld? envelope).getD ""

#assert_axioms decodeSeatEnvelope_reencodes
#assert_axioms the_seat_preimage_reads_only_the_admitted_field_session

/-! ## The admitted fixture — a production-suited crew in an activated world

Deployment-free test vectors, not canon.  ⚠ This crew is NOT
`CrewFieldMission.katRawConfig`: the KAT world inherits
`DeckGraph.fixtureActivation`'s ALL-ZERO federation and content session, and
`WorldActivation.validWorld` refuses a zero federation, so a KAT-sessioned activation
could never be a member of any valid world.  The identity fields below are therefore
authored nonzero — which re-bases the session, and therefore invalidates every
signature bound to the KAT session.

## ⚑ 2026-08-09 — this fixture used to pass the door and be unable to play

The paragraph above used to end "which costs the real ML-DSA-65 keypair ... and buys
an activation that an audited world can actually carry", and the roster below was
`CrewRelayExpedition.fixtureRoster` — player keys `digestFilled 10..13`, i.e.
`0a0a0a…`, `0b0b0b…`, `0c0c0c…`, `0d0d0d…`.  The config also names the PRODUCTION
signing suite, whose `verifySeat` is `verifyEnvelope`, which demands
`SHAKE256(publicKey, 32) = playerKey` before it will run FIPS 204 verify at all.

**No ML-DSA-65 public key digests to `0a0a0a…`.**  So `authenticateSeat?` could never
accept for any seat of this crew, and the organ's own demonstration material was an
activation that MINTED, was ADMITTED to its world, and then refused every single step
— measured: `admittedMember?.isSome = true`, `stepWire <honest envelope> = ""`.  Every
refusal tooth below was passing over a crew that had no accepting pole to contrast
with, which is the vacuity class in the module that exists to demonstrate the fix.

The roster is now four REAL ML-DSA-65 public keys.  Seats 0 and 1 reuse the two
keypairs already pinned in `CrewSigningVectors`; seats 2 and 3 are pinned here, from
the same deterministic `keygen_from_seed` harness, because a four-seat crew in which
two seats can never act still cannot complete a run.

⚠ **TEST MATERIAL — NEVER DEPLOY THIS CREW.**  All four secret keys are derivable by
anyone from the pinned xi seeds below, exactly as `CrewSigningVectors` says of the KAT
keypair.  A real crew's player keys are its players' own; these exist so that the
accepting pole of this organ is checkable, and for no other purpose.

Provenance, reproducible: `ml_dsa_65::KG::keygen_from_seed(xi)` with
`xi = b"POA-CREW-ADMITTED-SEAT2-XI-0003!"` and `b"POA-CREW-ADMITTED-SEAT3-XI-0004!"`,
through the `crew-kat-gen` harness whose complete source is reproduced at the bottom of
`CrewSigningVectors.lean`.  The end-to-end drive — seat preimages out of
`seatPreimageWire`, signatures in from `fips204` 0.4.6, the handoff out of `stepWire` —
is `metatheory/scripts/crew_playable_handoff.lean`. -/

/-- Genuine ML-DSA-65 public key (1952 bytes), seat 2 of the admitted crew. -/
def admittedSeat2PublicKey : Array UInt8 := #[135, 56, 73, 10, 219, 193, 56, 119, 85, 213, 130, 147, 72, 162, 44, 185, 148, 211, 18, 141, 24, 182, 34, 74, 180, 147, 140, 201, 224, 83, 4, 215, 120, 164, 10, 58, 19, 49, 235, 170, 170, 191, 30, 60, 211, 196, 2, 34, 67, 125, 113, 132, 96, 249, 144, 147, 133, 192, 160, 5, 109, 113, 66, 119, 250, 193, 168, 88, 58, 9, 98, 237, 135, 186, 70, 222, 94, 72, 31, 90, 112, 16, 128, 117, 11, 202, 76, 40, 31, 114, 254, 16, 141, 76, 24, 227, 233, 37, 241, 29, 211, 119, 53, 37, 26, 251, 51, 87, 160, 24, 135, 127, 140, 226, 219, 225, 229, 184, 45, 202, 137, 16, 4, 221, 206, 0, 48, 72, 217, 51, 16, 57, 196, 213, 105, 161, 25, 169, 132, 73, 213, 182, 163, 110, 137, 67, 36, 26, 102, 246, 175, 146, 203, 88, 45, 249, 97, 217, 106, 187, 186, 242, 54, 215, 148, 213, 25, 83, 185, 189, 198, 175, 74, 241, 128, 245, 95, 84, 26, 161, 240, 173, 16, 42, 121, 120, 91, 49, 250, 240, 197, 144, 169, 142, 168, 252, 109, 165, 242, 92, 7, 134, 64, 119, 183, 52, 233, 194, 25, 235, 5, 241, 208, 92, 34, 124, 214, 126, 247, 182, 150, 133, 238, 62, 111, 60, 156, 148, 21, 41, 101, 24, 163, 209, 6, 179, 249, 54, 104, 90, 138, 77, 110, 173, 4, 9, 194, 12, 45, 211, 125, 23, 40, 202, 111, 162, 123, 166, 47, 232, 77, 59, 150, 84, 65, 67, 120, 187, 124, 214, 114, 130, 24, 166, 60, 62, 231, 138, 214, 84, 145, 238, 99, 127, 175, 34, 150, 244, 56, 71, 26, 214, 114, 46, 236, 225, 229, 206, 202, 186, 241, 243, 73, 29, 88, 72, 240, 82, 164, 174, 160, 24, 136, 145, 225, 53, 186, 123, 236, 159, 215, 182, 89, 135, 14, 229, 20, 166, 118, 236, 69, 63, 30, 34, 184, 68, 110, 154, 211, 148, 169, 50, 178, 193, 31, 209, 178, 203, 144, 92, 168, 111, 149, 191, 74, 145, 166, 175, 111, 166, 57, 44, 7, 13, 30, 100, 224, 140, 253, 87, 2, 51, 118, 254, 225, 126, 63, 137, 124, 253, 119, 138, 175, 57, 56, 57, 210, 227, 46, 155, 118, 221, 204, 41, 254, 218, 252, 248, 0, 209, 132, 39, 159, 20, 239, 156, 210, 235, 159, 224, 176, 241, 81, 96, 31, 135, 68, 249, 46, 248, 212, 50, 158, 64, 235, 8, 205, 114, 37, 153, 39, 251, 223, 27, 178, 108, 34, 247, 158, 106, 199, 228, 149, 250, 0, 150, 183, 209, 131, 194, 99, 153, 244, 68, 119, 113, 231, 108, 235, 144, 211, 205, 27, 108, 219, 197, 252, 232, 241, 101, 73, 238, 178, 250, 192, 8, 115, 228, 246, 160, 129, 2, 156, 118, 207, 83, 221, 85, 155, 119, 85, 109, 132, 46, 81, 185, 209, 33, 139, 113, 169, 252, 199, 82, 213, 28, 224, 43, 129, 25, 107, 232, 147, 150, 14, 182, 192, 62, 39, 188, 218, 161, 57, 189, 95, 192, 1, 93, 20, 188, 62, 66, 3, 150, 185, 218, 50, 58, 66, 30, 50, 20, 66, 113, 244, 13, 63, 250, 161, 58, 87, 136, 232, 115, 126, 122, 173, 0, 234, 130, 107, 133, 59, 191, 68, 168, 20, 78, 51, 245, 125, 170, 2, 12, 17, 51, 149, 91, 31, 76, 224, 174, 185, 45, 248, 11, 46, 39, 249, 171, 219, 49, 184, 60, 36, 218, 117, 118, 19, 179, 252, 14, 138, 227, 65, 138, 97, 39, 157, 79, 175, 151, 113, 35, 196, 247, 1, 12, 63, 165, 14, 29, 156, 239, 28, 34, 30, 218, 202, 35, 70, 22, 26, 124, 124, 207, 219, 222, 2, 180, 114, 130, 206, 78, 135, 167, 89, 97, 94, 89, 126, 29, 141, 40, 36, 198, 159, 227, 223, 31, 81, 219, 75, 168, 154, 129, 64, 154, 48, 207, 247, 24, 93, 204, 77, 60, 89, 199, 58, 144, 227, 169, 240, 75, 56, 150, 98, 160, 151, 73, 167, 237, 130, 4, 252, 25, 137, 62, 72, 121, 168, 74, 250, 242, 160, 211, 110, 158, 34, 37, 147, 177, 19, 86, 145, 66, 168, 219, 58, 164, 56, 123, 55, 233, 46, 180, 171, 8, 74, 188, 127, 149, 196, 203, 156, 236, 35, 35, 21, 191, 214, 22, 185, 69, 241, 161, 13, 21, 109, 115, 136, 238, 171, 116, 175, 227, 75, 34, 79, 56, 190, 73, 164, 201, 190, 12, 209, 210, 1, 50, 64, 166, 158, 241, 9, 109, 205, 150, 25, 184, 81, 225, 150, 69, 58, 121, 59, 72, 188, 60, 138, 104, 72, 197, 209, 77, 9, 137, 207, 70, 97, 11, 98, 194, 35, 15, 16, 145, 255, 168, 231, 146, 80, 190, 60, 92, 232, 116, 211, 140, 236, 195, 197, 129, 18, 204, 76, 73, 37, 212, 150, 129, 27, 159, 141, 153, 184, 232, 51, 96, 10, 126, 157, 243, 146, 44, 99, 11, 52, 145, 147, 125, 104, 160, 131, 96, 224, 63, 200, 45, 20, 45, 148, 53, 46, 135, 22, 58, 28, 239, 100, 234, 26, 235, 35, 215, 134, 168, 188, 74, 251, 48, 57, 149, 125, 200, 173, 68, 192, 28, 11, 227, 165, 190, 183, 210, 119, 109, 98, 35, 6, 115, 21, 66, 43, 106, 87, 153, 104, 123, 143, 119, 82, 74, 102, 204, 120, 218, 149, 72, 131, 40, 69, 167, 135, 192, 106, 197, 75, 25, 91, 210, 245, 158, 0, 89, 186, 52, 236, 254, 64, 60, 133, 112, 202, 121, 70, 62, 111, 33, 166, 142, 68, 252, 233, 239, 10, 233, 198, 127, 30, 91, 117, 233, 164, 5, 228, 237, 183, 206, 35, 190, 108, 239, 84, 216, 53, 11, 154, 113, 153, 99, 78, 20, 42, 247, 37, 155, 4, 38, 68, 0, 80, 34, 147, 66, 74, 223, 106, 60, 144, 192, 202, 152, 15, 221, 173, 164, 101, 223, 130, 1, 194, 232, 41, 106, 233, 48, 46, 74, 119, 17, 111, 177, 213, 246, 186, 103, 56, 23, 197, 204, 205, 233, 102, 184, 188, 223, 81, 194, 173, 234, 210, 105, 153, 117, 80, 0, 237, 128, 36, 108, 70, 38, 165, 13, 191, 227, 206, 8, 231, 159, 92, 202, 187, 112, 23, 12, 46, 8, 177, 191, 98, 11, 93, 143, 213, 0, 171, 147, 203, 109, 179, 112, 33, 248, 67, 218, 84, 123, 213, 130, 5, 195, 102, 40, 248, 20, 103, 210, 235, 92, 23, 123, 36, 120, 38, 217, 3, 224, 5, 93, 167, 45, 116, 4, 24, 254, 250, 179, 234, 205, 250, 161, 176, 81, 86, 150, 221, 140, 240, 223, 82, 168, 106, 126, 176, 68, 147, 31, 83, 125, 92, 252, 148, 66, 208, 103, 102, 137, 41, 204, 172, 10, 194, 181, 145, 225, 41, 142, 237, 114, 46, 82, 110, 170, 184, 19, 41, 98, 196, 107, 202, 21, 18, 79, 106, 250, 56, 35, 48, 235, 158, 138, 161, 83, 138, 49, 78, 146, 247, 87, 19, 53, 23, 153, 71, 146, 185, 53, 208, 136, 20, 23, 70, 29, 236, 46, 152, 197, 44, 73, 231, 183, 99, 108, 194, 188, 56, 0, 43, 56, 104, 117, 208, 135, 253, 206, 228, 82, 196, 204, 152, 177, 209, 213, 153, 116, 98, 68, 150, 142, 210, 236, 114, 63, 234, 175, 155, 99, 161, 65, 46, 189, 222, 1, 223, 165, 234, 121, 165, 31, 204, 106, 200, 0, 200, 6, 202, 224, 251, 12, 58, 95, 55, 82, 234, 138, 91, 102, 72, 72, 199, 231, 243, 72, 174, 64, 106, 57, 75, 38, 12, 66, 250, 124, 113, 95, 33, 45, 89, 3, 111, 107, 191, 145, 84, 26, 25, 143, 21, 75, 183, 8, 105, 182, 136, 173, 242, 137, 1, 219, 167, 230, 64, 98, 35, 179, 191, 132, 56, 36, 213, 231, 227, 149, 118, 205, 62, 77, 82, 139, 55, 47, 59, 173, 247, 174, 196, 184, 163, 169, 243, 103, 57, 71, 39, 41, 97, 208, 180, 90, 151, 95, 55, 223, 93, 175, 53, 16, 107, 101, 231, 3, 58, 126, 146, 199, 127, 53, 234, 204, 220, 71, 2, 229, 158, 71, 85, 5, 3, 26, 190, 144, 220, 221, 64, 121, 109, 30, 98, 242, 120, 165, 209, 170, 3, 243, 28, 238, 95, 6, 119, 8, 57, 240, 88, 42, 79, 182, 250, 169, 159, 238, 113, 45, 229, 6, 221, 19, 53, 185, 231, 108, 185, 215, 141, 167, 144, 57, 227, 190, 193, 198, 50, 178, 14, 197, 29, 87, 233, 48, 205, 105, 189, 231, 47, 17, 205, 187, 157, 135, 163, 210, 85, 217, 82, 40, 21, 214, 224, 76, 164, 175, 175, 92, 86, 138, 184, 65, 47, 100, 155, 190, 229, 139, 26, 35, 69, 36, 160, 145, 92, 164, 135, 33, 81, 1, 90, 105, 6, 171, 45, 253, 98, 135, 126, 49, 74, 219, 154, 42, 144, 148, 147, 113, 242, 145, 102, 253, 84, 134, 150, 248, 92, 253, 87, 131, 154, 71, 166, 16, 252, 111, 18, 211, 137, 37, 222, 67, 29, 214, 95, 64, 199, 192, 43, 202, 222, 136, 250, 56, 117, 235, 51, 184, 0, 170, 1, 184, 205, 217, 147, 44, 151, 253, 255, 93, 159, 42, 165, 63, 54, 172, 101, 231, 171, 127, 131, 249, 15, 86, 209, 42, 135, 141, 31, 12, 206, 62, 131, 103, 46, 44, 19, 124, 232, 52, 157, 93, 174, 200, 21, 22, 229, 225, 167, 1, 188, 221, 35, 33, 51, 63, 220, 180, 41, 215, 254, 237, 250, 95, 61, 33, 245, 117, 220, 180, 98, 122, 138, 210, 194, 217, 252, 183, 14, 106, 110, 243, 133, 245, 223, 112, 64, 51, 51, 116, 146, 36, 168, 137, 76, 96, 178, 36, 6, 170, 103, 85, 231, 91, 158, 24, 207, 98, 86, 36, 250, 108, 168, 192, 244, 162, 202, 117, 58, 189, 8, 205, 220, 237, 113, 251, 238, 99, 189, 105, 122, 135, 191, 133, 16, 159, 229, 118, 202, 210, 158, 242, 87, 127, 91, 5, 205, 95, 144, 40, 82, 189, 171, 55, 254, 240, 157, 30, 186, 93, 27, 96, 130, 10, 74, 77, 170, 244, 17, 72, 147, 17, 148, 180, 216, 218, 72, 43, 58, 148, 203, 185, 72, 97, 255, 218, 51, 203, 215, 252, 45, 252, 132, 254, 83, 235, 197, 244, 98, 217, 144, 140, 113, 136, 108, 180, 177, 120, 109, 42, 45, 154, 213, 87, 91, 234, 14, 30, 229, 29, 88, 70, 192, 250, 108, 161, 47, 27, 142, 149, 95, 78, 111, 128, 148, 242, 171, 142, 106, 63, 144, 93, 67, 29, 118, 28, 122, 29, 208, 168, 163, 77, 39, 69, 29, 184, 160, 57, 238, 77, 179, 123, 108, 180, 44, 125, 157, 214, 156, 207, 248, 113, 81, 120, 69, 48, 67, 0, 120, 80, 178, 27, 17, 97, 211, 75, 74, 137, 246, 234, 149, 230, 175, 51, 3, 233, 88, 87, 115, 108, 164, 138, 133, 143, 10, 106, 26, 103, 200, 183, 16, 227, 124, 45, 103, 236, 106, 253, 116, 112, 144, 97, 193, 59, 223, 23, 182, 201, 175, 207, 183, 247, 226, 220, 26, 203, 138, 69, 161, 247, 0, 134, 135, 231, 147, 134, 9, 237, 37, 225, 162, 173, 63, 244, 166, 211, 223, 151, 117, 95, 157, 196, 148, 218, 238, 65, 223, 27, 52, 217, 159, 69, 71, 148, 147, 166, 151, 175, 148, 166, 164, 244, 26, 142, 223, 204, 106, 5, 47, 151, 224, 243, 244, 145]

/-- Genuine ML-DSA-65 public key (1952 bytes), seat 3 of the admitted crew. -/
def admittedSeat3PublicKey : Array UInt8 := #[33, 1, 3, 233, 90, 23, 253, 73, 13, 213, 125, 249, 73, 26, 192, 205, 183, 59, 119, 48, 34, 100, 204, 8, 125, 207, 234, 59, 166, 69, 185, 105, 165, 196, 60, 196, 48, 45, 176, 22, 11, 205, 212, 179, 118, 194, 56, 75, 111, 51, 32, 79, 136, 215, 20, 97, 40, 218, 110, 159, 95, 71, 66, 32, 175, 192, 35, 136, 253, 134, 150, 84, 205, 55, 233, 230, 2, 253, 209, 119, 106, 96, 9, 156, 187, 239, 48, 123, 239, 239, 181, 61, 32, 20, 84, 135, 166, 121, 145, 33, 56, 185, 196, 240, 16, 132, 50, 174, 98, 144, 193, 107, 208, 225, 66, 8, 237, 124, 82, 74, 205, 143, 45, 19, 144, 182, 47, 132, 79, 10, 2, 17, 180, 241, 12, 205, 199, 225, 58, 185, 124, 93, 73, 45, 60, 145, 54, 32, 95, 174, 218, 184, 72, 195, 147, 25, 15, 56, 18, 183, 59, 14, 171, 77, 47, 222, 169, 118, 154, 184, 83, 35, 16, 237, 11, 150, 106, 144, 59, 41, 178, 98, 3, 191, 201, 133, 72, 22, 50, 246, 181, 179, 124, 237, 159, 40, 200, 137, 211, 21, 122, 126, 230, 33, 160, 119, 148, 68, 194, 64, 249, 174, 230, 86, 41, 142, 213, 190, 157, 229, 195, 26, 91, 52, 29, 239, 153, 89, 233, 142, 28, 163, 55, 29, 233, 171, 20, 204, 139, 174, 232, 138, 183, 120, 58, 227, 128, 38, 74, 222, 135, 72, 32, 215, 162, 157, 215, 34, 123, 119, 31, 104, 126, 175, 67, 59, 51, 238, 186, 58, 110, 173, 124, 201, 58, 24, 206, 56, 27, 122, 43, 182, 167, 223, 5, 223, 35, 71, 179, 31, 58, 20, 139, 187, 112, 244, 173, 180, 204, 88, 218, 137, 232, 204, 165, 210, 72, 250, 157, 246, 196, 118, 222, 196, 233, 202, 114, 19, 119, 233, 159, 135, 31, 4, 6, 222, 108, 164, 136, 211, 80, 69, 141, 205, 14, 83, 27, 96, 233, 160, 127, 198, 124, 18, 80, 144, 176, 199, 27, 170, 97, 214, 99, 89, 230, 94, 212, 125, 121, 222, 115, 20, 153, 157, 235, 249, 122, 94, 103, 122, 5, 76, 180, 20, 176, 83, 215, 239, 239, 177, 227, 172, 45, 195, 231, 180, 170, 148, 127, 192, 172, 126, 185, 40, 105, 157, 198, 255, 104, 100, 134, 201, 144, 20, 237, 61, 56, 74, 68, 183, 38, 202, 40, 153, 62, 67, 14, 41, 130, 42, 255, 91, 129, 6, 180, 221, 18, 56, 118, 233, 248, 196, 238, 222, 12, 241, 220, 16, 128, 106, 26, 105, 27, 171, 189, 27, 69, 71, 219, 64, 74, 198, 10, 11, 186, 71, 93, 155, 212, 213, 210, 109, 142, 194, 93, 100, 81, 224, 77, 175, 33, 178, 131, 150, 252, 70, 50, 147, 144, 133, 177, 186, 6, 113, 112, 255, 207, 236, 136, 120, 122, 66, 116, 120, 106, 244, 25, 59, 62, 70, 185, 181, 79, 187, 19, 237, 17, 194, 101, 144, 117, 16, 13, 2, 40, 1, 64, 91, 174, 203, 11, 209, 36, 8, 141, 33, 107, 117, 65, 202, 36, 142, 141, 53, 11, 80, 15, 67, 249, 73, 94, 117, 86, 245, 141, 167, 245, 59, 84, 141, 9, 58, 222, 182, 204, 45, 204, 125, 25, 33, 141, 141, 171, 62, 137, 111, 130, 118, 121, 148, 222, 228, 143, 140, 195, 239, 203, 202, 9, 66, 230, 208, 80, 212, 10, 209, 99, 121, 105, 228, 121, 123, 98, 86, 204, 78, 191, 56, 125, 85, 254, 149, 131, 63, 232, 150, 210, 94, 66, 175, 152, 24, 217, 252, 166, 23, 160, 182, 14, 249, 41, 76, 47, 136, 53, 107, 209, 85, 176, 102, 241, 114, 151, 193, 81, 236, 103, 251, 144, 162, 106, 51, 4, 239, 229, 90, 130, 50, 83, 128, 184, 221, 83, 241, 208, 23, 234, 180, 82, 205, 131, 184, 252, 229, 172, 25, 165, 138, 171, 34, 24, 199, 41, 104, 188, 222, 195, 126, 155, 95, 27, 191, 170, 61, 53, 211, 224, 39, 22, 153, 124, 50, 112, 62, 192, 96, 158, 17, 247, 48, 87, 63, 147, 188, 216, 155, 148, 108, 43, 5, 132, 208, 44, 74, 98, 185, 231, 104, 203, 160, 254, 127, 23, 185, 51, 46, 192, 196, 42, 59, 156, 95, 42, 64, 135, 126, 227, 217, 84, 72, 16, 79, 117, 161, 100, 253, 117, 138, 193, 138, 99, 80, 182, 56, 100, 46, 232, 156, 144, 137, 0, 148, 18, 15, 131, 31, 44, 83, 160, 249, 201, 0, 125, 246, 153, 254, 247, 107, 170, 211, 219, 89, 58, 73, 63, 33, 207, 129, 146, 68, 205, 236, 41, 21, 209, 129, 102, 103, 56, 76, 252, 177, 82, 204, 165, 14, 3, 219, 189, 153, 230, 165, 164, 24, 187, 103, 12, 36, 47, 237, 0, 219, 178, 113, 159, 239, 137, 49, 177, 30, 73, 34, 127, 218, 88, 143, 55, 89, 73, 149, 125, 156, 212, 146, 179, 166, 82, 57, 49, 175, 81, 22, 29, 166, 219, 194, 8, 150, 45, 42, 189, 131, 236, 128, 168, 206, 29, 34, 86, 103, 230, 10, 159, 39, 129, 97, 242, 253, 246, 66, 226, 119, 229, 38, 15, 73, 109, 156, 210, 185, 252, 194, 194, 226, 115, 37, 18, 98, 226, 159, 125, 141, 112, 253, 87, 15, 165, 196, 112, 133, 128, 29, 111, 235, 50, 79, 145, 162, 115, 132, 109, 37, 253, 170, 176, 109, 69, 113, 123, 65, 250, 213, 54, 190, 171, 99, 30, 122, 121, 10, 154, 61, 19, 139, 32, 43, 253, 130, 150, 122, 57, 105, 82, 69, 29, 94, 167, 223, 117, 41, 153, 48, 145, 174, 238, 157, 31, 59, 236, 39, 93, 78, 136, 162, 108, 47, 242, 130, 62, 130, 139, 234, 244, 158, 68, 94, 164, 208, 51, 129, 138, 28, 7, 45, 236, 184, 105, 174, 220, 5, 211, 80, 111, 178, 166, 177, 28, 38, 73, 78, 84, 171, 92, 83, 95, 77, 1, 221, 209, 38, 209, 44, 157, 38, 241, 251, 107, 63, 229, 232, 31, 139, 156, 247, 210, 13, 66, 58, 170, 52, 203, 14, 97, 40, 101, 204, 218, 7, 172, 122, 0, 69, 227, 141, 206, 31, 193, 42, 182, 178, 233, 111, 187, 177, 55, 75, 37, 240, 98, 167, 11, 41, 172, 132, 186, 143, 24, 165, 78, 96, 114, 200, 77, 94, 249, 174, 214, 229, 99, 169, 50, 238, 137, 142, 253, 86, 88, 94, 200, 178, 237, 123, 88, 26, 76, 150, 43, 26, 194, 84, 181, 198, 74, 88, 229, 147, 29, 211, 171, 68, 239, 54, 139, 105, 241, 150, 230, 56, 219, 164, 81, 166, 90, 252, 215, 194, 237, 194, 110, 7, 168, 51, 174, 111, 189, 200, 2, 102, 218, 203, 33, 206, 105, 240, 210, 67, 129, 246, 215, 33, 9, 161, 179, 180, 112, 251, 213, 46, 147, 115, 178, 51, 152, 118, 152, 190, 169, 227, 99, 169, 211, 47, 15, 246, 88, 122, 229, 38, 184, 175, 223, 86, 110, 23, 111, 227, 177, 188, 134, 204, 130, 147, 65, 174, 84, 249, 10, 155, 183, 148, 221, 220, 201, 249, 88, 164, 168, 210, 187, 243, 204, 86, 246, 238, 233, 96, 99, 13, 103, 40, 87, 254, 159, 197, 99, 0, 56, 233, 106, 222, 237, 49, 94, 57, 13, 201, 233, 19, 75, 176, 78, 47, 47, 74, 161, 221, 177, 151, 197, 224, 3, 254, 25, 158, 233, 0, 176, 69, 249, 55, 107, 20, 139, 203, 89, 216, 185, 160, 156, 124, 148, 246, 227, 5, 199, 183, 133, 112, 168, 133, 241, 182, 145, 22, 199, 100, 178, 48, 193, 114, 36, 64, 40, 212, 225, 152, 80, 248, 11, 8, 239, 42, 79, 244, 20, 171, 199, 117, 80, 4, 119, 65, 30, 167, 77, 147, 102, 119, 244, 78, 68, 154, 44, 136, 240, 91, 98, 22, 192, 61, 134, 48, 170, 213, 219, 147, 227, 103, 104, 11, 120, 168, 3, 63, 195, 223, 55, 45, 69, 78, 115, 201, 219, 68, 112, 188, 8, 140, 68, 24, 148, 188, 3, 86, 255, 244, 66, 189, 169, 49, 253, 101, 242, 132, 251, 92, 23, 254, 214, 57, 16, 159, 200, 64, 132, 237, 33, 227, 201, 85, 249, 249, 35, 38, 227, 169, 175, 46, 165, 242, 86, 161, 48, 88, 168, 20, 151, 28, 0, 55, 206, 31, 233, 209, 140, 46, 220, 245, 250, 13, 172, 40, 39, 225, 224, 247, 220, 140, 4, 115, 224, 254, 212, 182, 254, 3, 229, 244, 169, 227, 208, 242, 174, 140, 178, 4, 169, 118, 134, 154, 194, 189, 212, 173, 145, 38, 198, 86, 104, 91, 117, 14, 122, 233, 231, 7, 183, 134, 137, 72, 71, 76, 4, 126, 76, 156, 151, 113, 249, 214, 245, 163, 72, 1, 26, 105, 171, 194, 172, 229, 131, 167, 85, 184, 72, 116, 127, 215, 192, 206, 52, 106, 248, 234, 124, 194, 39, 171, 17, 103, 203, 99, 180, 128, 83, 158, 26, 174, 113, 46, 167, 121, 117, 220, 178, 194, 39, 75, 135, 190, 236, 56, 26, 43, 211, 186, 174, 175, 141, 205, 3, 149, 99, 113, 53, 173, 247, 98, 43, 223, 6, 164, 168, 29, 137, 17, 41, 147, 92, 215, 202, 245, 177, 159, 132, 74, 242, 143, 62, 198, 77, 148, 252, 51, 46, 180, 147, 220, 37, 176, 20, 189, 91, 1, 122, 196, 36, 210, 137, 171, 47, 59, 184, 141, 7, 252, 64, 107, 0, 158, 86, 179, 214, 178, 46, 25, 39, 193, 210, 22, 97, 245, 124, 246, 214, 22, 126, 118, 197, 66, 45, 140, 152, 38, 154, 214, 4, 163, 198, 240, 186, 126, 110, 172, 33, 140, 25, 171, 253, 139, 210, 200, 81, 47, 119, 229, 1, 220, 205, 155, 202, 4, 155, 250, 138, 91, 92, 230, 154, 17, 187, 116, 95, 215, 248, 108, 132, 133, 21, 169, 125, 159, 100, 40, 241, 229, 217, 118, 169, 231, 15, 160, 129, 21, 28, 224, 25, 164, 245, 50, 35, 56, 167, 209, 104, 104, 72, 199, 41, 155, 210, 58, 78, 210, 115, 92, 19, 31, 36, 190, 142, 69, 205, 249, 137, 231, 63, 187, 32, 242, 40, 111, 88, 182, 177, 163, 229, 63, 16, 239, 183, 60, 252, 209, 181, 47, 71, 238, 36, 119, 146, 17, 2, 253, 206, 156, 129, 72, 246, 2, 219, 31, 72, 79, 138, 226, 165, 53, 206, 84, 56, 32, 86, 103, 83, 150, 238, 212, 129, 199, 76, 11, 33, 5, 43, 111, 214, 218, 89, 2, 129, 65, 65, 216, 234, 96, 4, 97, 92, 221, 204, 14, 70, 174, 124, 145, 95, 89, 85, 58, 132, 212, 108, 25, 18, 254, 175, 115, 169, 117, 109, 186, 61, 76, 176, 183, 162, 239, 123, 222, 41, 41, 84, 173, 151, 205, 144, 107, 228, 140, 209, 80, 137, 155, 80, 133, 52, 228, 233, 162, 76, 217, 233, 119, 16, 29, 30, 126, 156, 109, 0, 80, 75, 124, 90, 174, 86, 143, 91, 165, 202, 135, 111, 13, 138, 198, 230, 249, 236, 122, 182, 136, 248, 45, 220, 16, 81, 128, 143, 190, 149, 77, 30, 220, 196, 188, 18, 56, 185, 17, 187, 237, 91, 166, 59, 19, 3, 28, 58, 238, 239, 201, 253, 164, 147, 138, 145, 38, 87, 4, 69, 223, 224, 76, 247, 253, 30, 98, 238, 104, 77, 172, 216, 62, 147, 62, 165, 93, 44, 199, 97, 21, 142, 77, 92, 83, 136, 194, 64, 187, 117, 58]

/-- A roster player key is the SHAKE-256 digest of the seat's real ML-DSA-65 public
key — the two-source pin the production `verifyEnvelope` re-checks against the envelope
the seat presents.  ⚠ The `getD` fallback is pinned never to fire by
`every_admitted_seat_holds_a_real_ml_dsa_public_key`. -/
def playerKeyOfPublicKey (publicKey : Array UInt8) : Digest32 :=
  (CrewFieldMission.ProductionSigning.shakeDigest32? publicKey.toList).getD
    (CrewFieldMission.digestFilled 0)

/-- The four seats keep `fixtureRoster`'s ids, credentials, roles and counter origins —
only the player keys change, so every structural tooth below is about the same crew it
was about before. -/
def admittedRoster : List Seat :=
  [ { fixtureSeat0 with playerKey := CrewFieldMission.ProductionSigning.katPlayerKey }
  , { fixtureSeat1 with
      playerKey := playerKeyOfPublicKey CrewSigningVectors.katWrongPublicKey }
  , { fixtureSeat2 with playerKey := playerKeyOfPublicKey admittedSeat2PublicKey }
  , { fixtureSeat3 with playerKey := playerKeyOfPublicKey admittedSeat3PublicKey } ]

/-- ⚑ THE SATISFIABILITY POLE OF THE ROSTER.  Every seat's player key is the SHAKE-256
digest of a real ML-DSA-65 public key, the four are distinct, and none is the old
placeholder — so `playerKeyOfPublicKey`'s fallback never fired and this crew is one
whose seats a production `verifySeat` can actually admit.
(Pinned `= true` in `CrewFieldMissionAdmissionFixtures`.) -/
def check_every_admitted_seat_holds_a_real_ml_dsa_public_key : Bool :=
  let keys := [CrewSigningVectors.katSeat0PublicKey, CrewSigningVectors.katWrongPublicKey,
    admittedSeat2PublicKey, admittedSeat3PublicKey]
  decide (keys.all (fun k => k.size = 1952)) &&
  decide (admittedRoster.map Seat.playerKey
    = keys.map (fun k => (CrewFieldMission.ProductionSigning.shakeDigest32? k.toList).getD
        (CrewFieldMission.digestFilled 1))) &&
  decide ((admittedRoster.map Seat.playerKey).Nodup) &&
  decide (admittedRoster.map Seat.playerKey
    ≠ CrewRelayExpedition.fixtureRoster.map Seat.playerKey) &&
  decide (admittedRoster.map Seat.id = CrewRelayExpedition.fixtureRoster.map Seat.id) &&
  decide (admittedRoster.map Seat.credential
    = CrewRelayExpedition.fixtureRoster.map Seat.credential) &&
  decide (admittedRoster.map Seat.role = CrewRelayExpedition.fixtureRoster.map Seat.role)

def admittedFederation : Digest32 := CrewFieldMission.digestFilled 0x41
def admittedContentSession : Digest32 := CrewFieldMission.digestFilled 0x42
def admittedActivationDigest : Digest32 := CrewFieldMission.digestFilled 0x43
def admittedMissionContentRoot : Digest32 := CrewFieldMission.digestFilled 0x44
def admittedSignerKeyId : Digest32 := CrewFieldMission.digestFilled 0x45

def admittedMission : MissionSpec :=
  { DeckExpedition.fixtureMission with
    federationId := admittedFederation
    contentSession := admittedContentSession
    activationDigest := admittedActivationDigest
    contentRoot := admittedMissionContentRoot }

def admittedPolicy : ActivityOutcome.Policy :=
  { CrewFieldMission.fixturePolicy with mission := admittedMission }

def admittedRawConfigBase : CrewFieldMission.RawConfig where
  federationId := admittedFederation
  contentSession := admittedContentSession
  missionEpoch := admittedMission.epoch
  missionId := admittedMission.missionId
  relayId := CrewFieldMission.digestFilled 182
  briefingPrivacy := .trustedDealerOperatorVisibleThenPublicHandoff
  briefingHashSuiteId := CrewFieldMission.ProductionSigning.briefingSuiteId
  briefingCommitment := CrewFieldMission.digestFilled 0
  messageDigestSuiteId := CrewFieldMission.ProductionSigning.messageSuiteId
  signingSuiteId := CrewFieldMission.ProductionSigning.signingSuiteId
  roster := admittedRoster
  policy := admittedPolicy
  operationalBudget := 13
  routeOutcomes := CrewFieldMission.fixtureRouteOutcomes

/-- The briefing commitment under the PRODUCTION SHAKE-256 deck boundary.  A config
whose commitment was computed under the fixture boundary fails `rawConfigValidB` inside
`ProductionSigning.activate?` and mints nothing. -/
def admittedRawConfig : CrewFieldMission.RawConfig :=
  { admittedRawConfigBase with
    briefingCommitment := CrewFieldMission.ProductionSigning.productionBriefingDigest.digest
      (CrewFieldMission.briefingDeckPreimage admittedRawConfigBase
        CrewFieldMission.fixtureBriefings) }

def admittedDeckActivation : DeckGraph.ActivationIdentity where
  federationId := admittedFederation
  contentRoot := admittedMissionContentRoot
  activationDigest := admittedActivationDigest
  contentSession := admittedContentSession
  contentEpoch := ⟨1⟩
  signerKeyId := admittedSignerKeyId
  activationCounter := 1

def admittedContentOfficers : List ContentContract.OfficerSeat :=
  [ ⟨⟨0⟩, ⟨10⟩, .pathfinder⟩
  , ⟨⟨1⟩, ⟨11⟩, .engineer⟩
  , ⟨⟨2⟩, ⟨12⟩, .containment⟩
  , ⟨⟨3⟩, ⟨13⟩, .quartermaster⟩ ]

def admittedContentBriefings : List ContentContract.BriefingShape :=
  [ ⟨.pathfinder, .mappedRoute, some ⟨1⟩, .privateUntilSignedHandoff⟩
  , ⟨.engineer, .structurallySoundRoute, some ⟨1⟩, .privateUntilSignedHandoff⟩
  , ⟨.containment, .hazardClearRoute, some ⟨1⟩, .privateUntilSignedHandoff⟩
  , ⟨.quartermaster, .extractionWindow, none, .privateUntilSignedHandoff⟩ ]

def admittedContentArtifacts : List ContentContract.ArtifactSpec :=
  [ ⟨⟨20⟩, none⟩, ⟨⟨21⟩, none⟩, ⟨⟨22⟩, none⟩ ]

def admittedContentEncounters : List ContentContract.EncounterSpec :=
  [ { id := ⟨10⟩, room := DeckGraph.fixtureRoomB.id,
      routes := [⟨0⟩, ⟨1⟩, ⟨2⟩], betaArtifacts := [⟨20⟩] }
  , { id := ⟨11⟩, room := DeckGraph.fixtureRoomC.id,
      routes := [⟨0⟩], betaArtifacts := [⟨20⟩] }
  , { id := ⟨12⟩, room := DeckGraph.fixtureRoomD.id,
      routes := [⟨1⟩], betaArtifacts := [⟨21⟩] }
  , { id := ⟨13⟩, room := DeckGraph.fixtureExtraction.id,
      routes := [⟨2⟩], betaArtifacts := [⟨22⟩] } ]

private def admittedContentRoute : CrewFieldMission.Route → ContentContract.RouteId
  | .maintenanceSpine => ⟨0⟩
  | .signalGallery => ⟨1⟩
  | .sealedNave => ⟨2⟩

private def admittedContentArtifact : CrewFieldMission.Route → ContentContract.ArtifactId
  | .maintenanceSpine => ⟨20⟩
  | .signalGallery => ⟨21⟩
  | .sealedNave => ⟨22⟩

def admittedContentOutcomes : List ContentContract.RouteOutcome :=
  CrewFieldMission.fixtureRouteOutcomes.map fun spec => {
    route := admittedContentRoute spec.route
    extraction := toContentExtraction spec.extraction
    operationalCost := spec.operationalCost
    agreement := ContentContract.requiredAgreement (toContentExtraction spec.extraction)
    featuredArtifact := admittedContentArtifact spec.route
    contribution := {
      intel := spec.outcome.contribution.intel
      supplies := spec.outcome.contribution.supplies
      cohesion := spec.outcome.contribution.cohesion
      influence := spec.outcome.contribution.influence
      score := spec.outcome.contribution.score
      relics := spec.outcome.contribution.relics.map fun relic => ⟨relic.value⟩
    }
    recovery := if spec.extraction = .returnNow then ⟨40⟩ else ⟨41⟩
  }

def admittedContent : ContentContract.RawContent := {
  ContentContract.fixtureContent with
  deck := { DeckGraph.fixturePack with activation := admittedDeckActivation }
  officers := admittedContentOfficers
  briefings := admittedContentBriefings
  encounters := admittedContentEncounters
  artifacts := admittedContentArtifacts
  outcomes := admittedContentOutcomes
  relics := [⟨⟨447⟩, ⟨12⟩, true, false, none⟩]
  custodyPlans := [⟨⟨447⟩, .atEncounter ⟨12⟩, .quarantine, .fullCrewUnanimity, false⟩]
  promotionHooks :=
    [ ⟨.place ⟨50⟩, none⟩
    , ⟨.artifact ⟨20⟩, none⟩
    , ⟨.relic ⟨447⟩, none⟩ ]
  contributionBudget := {
    intel := 8, supplies := 4, cohesion := 6, influence := 0, score := 79,
    relicAllowlist := [⟨447⟩]
  }
}

def admittedRaw : RawActivation where
  activationId := admittedRawConfig.policy.mission.activationDigest
  rosterBinding := rosterBindingOf admittedRawConfig.roster
  contentDigest := admittedRawConfig.policy.mission.contentRoot
  fieldSession := admittedRawConfig.sessionDigest
  briefings := CrewFieldMission.fixtureBriefings
  content := admittedContent
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
  replayVerifierId := CrewFieldMission.digestFilled 222

def admittedComponent : ActivatedContent.Component where
  name := ACTIVATION_COMPONENT
  sha256 := (ActivatedContent.sha256Utf8? (activationJson admittedRaw)).getD
    (CrewFieldMission.digestFilled 0)
  bytesUtf8 := activationJson admittedRaw

def admittedManifest : ActivatedContent.Manifest where
  scope := {
    federationId := admittedFederation
    contentSession := admittedContentSession
    contentEpoch := 1
  }
  legacyWholePackRoot := none
  components := [admittedComponent]

def admittedManifestRoot : Digest32 :=
  (ActivatedContent.manifestRoot? admittedManifest).getD (CrewFieldMission.digestFilled 0)

def admittedWorld : WorldActivation.WorldIdentity where
  federationId := admittedFederation
  contentRoot := admittedManifestRoot
  activationDigest := admittedActivationDigest
  contentSession := admittedContentSession
  contentEpoch := ⟨1⟩

def admittedValidatedManifest? : Option ActivatedContent.ValidatedManifest :=
  ActivatedContent.decodeManifest admittedManifest.toJson

def admittedMember? : Option WorldScopedCrewActivation := do
  let manifest ← admittedValidatedManifest?
  authorizeCrewActivationForWorld? admittedWorld manifest

/-! ### The ENTRY POINT's own poles, over the admitted crew -/

def admittedSeatEnvelope (seat : Nat) : SeatEnvelopeWire where
  world := admittedWorld
  manifestJson := admittedManifest.toJson
  seat := seat

/-- ⚑ THE ACCEPTING POLE OF THE ENTRY POINT.  Conjunct 1: every one of the four
admitted seats gets an answer, so the export is not a surface that only ever refuses —
which is exactly what it WOULD have been over the placeholder roster this fixture
carried until 2026-08-09.  Conjunct 2: the four answers are pairwise distinct, so it is
not emitting one constant blob under four names.  Conjunct 3: each answer re-encodes
canonically, i.e. it is a document a decoder accepts rather than a string.  Conjunct 4:
a seat off the roster is the `""` refusal, with the seat index as the asserted mutation.
(Pinned `= true` in `CrewFieldMissionAdmissionFixtures`.) -/
def check_the_entry_point_answers_for_every_admitted_seat : Bool :=
  let answers := (List.range CrewFieldMission.CREW_SIZE).map
    (fun i => seatPreimageWire (admittedSeatEnvelope i).toJson)
  decide (answers.all (fun a => a ≠ "")) &&
  decide answers.Nodup &&
  decide ((List.range CrewFieldMission.CREW_SIZE).all
    (fun i => (decodeSeatEnvelope (admittedSeatEnvelope i).toJson).isSome)) &&
  decide (CrewFieldMission.CREW_SIZE < 8) &&
  decide (seatPreimageWire (admittedSeatEnvelope CrewFieldMission.CREW_SIZE).toJson = "")

/-- The entry point is scoped to the world exactly as the step surface is: the same
seat, asked for through a world this manifest does not root, is refused — and the
mutation is asserted present (the two worlds differ, and the honest one answers).
(Pinned `= true` in `CrewFieldMissionAdmissionFixtures`.) -/
def check_the_entry_point_refuses_a_world_this_manifest_does_not_root : Bool :=
  let honest := admittedSeatEnvelope 0
  let foreign : SeatEnvelopeWire := { honest with
    world := { admittedWorld with
      contentSession := CrewFieldMission.digestFilled 0x77 } }
  decide (foreign.world ≠ honest.world) &&
  decide (seatPreimageWire honest.toJson ≠ "") &&
  decide (seatPreimageWire foreign.toJson = "")

/-! ## Teeth

⚑ **THE TEETH NO LONGER EVALUATE IN THIS MODULE (2026-08-08).** This module is in the
`Dregg2.FFI` closure — the crypto archive's build — and a `native_decide` here made every
game-fixture regression a hard failure of every Rust proving target (the compilation-unit
coupling the stale-fixture outage measured). The witnesses (`admittedRaw`, the hostile
mutations, their manifests and worlds) stay here as evaluation-free `def`s; the sixteen
pins — every statement below names only public values and moves VERBATIM, except the
hex-agreement pin, which is stated over the private `uniformDigest` and therefore stays
as `check_the_manifest_hex_and_the_signing_hex_agree_on_every_byte_value` above — live in
`CrewFieldMissionAdmissionFixtures.lean`, rooted in the `PathOfAngelsGuards` library: a
plain `lake build` still runs every pin, and a stale fixture reds the guard library
instead of the archive.

⚠ Named residue: none.  Nothing in this module needs a fixture proof as data. -/

/-! ### The refusal pole — the fixture seal, structurally

`CrewFieldMission.fixtureRunSeal` is public and its verifier accepts a byte pattern any
reader can compute.  `CrewFieldMissionRuntime.activate?` pins
`runSeal.session = raw.fieldSession`, so the document a holder of that seal MUST
publish is one whose field session carries the fixture suite ids — and the suite ids
below are read off `fixtureRunSeal.session` itself rather than re-authored, so this is
that document and not a lookalike.

⚠ Everything else is the admitted crew: same roster, content, policy, route table and
mission identity, and the world is re-rooted at the re-hashed manifest.  So
`activationValidB` still holds and `matchesWorldB` still passes — both asserted below —
and the ONLY thing that refuses is the mint.  (The fixture seal's own session cannot be
used verbatim: it inherits `DeckGraph.fixtureActivation`'s zero federation, which
`validWorld` refuses, and the refusal would then be over-determined and prove nothing
about the suite.) -/

def fixtureSuitedSession : CrewFieldMission.SessionDigest :=
  { admittedRawConfig.sessionDigest with
    briefingHashSuiteId := CrewFieldMission.fixtureRunSeal.session.briefingHashSuiteId
    briefingCommitment := CrewFieldMission.fixtureRunSeal.session.briefingCommitment
    messageDigestSuiteId := CrewFieldMission.fixtureRunSeal.session.messageDigestSuiteId
    signingSuiteId := CrewFieldMission.fixtureRunSeal.session.signingSuiteId }

def fixtureSuitedRaw : RawActivation :=
  { admittedRaw with fieldSession := fixtureSuitedSession }

def fixtureSuitedComponent : ActivatedContent.Component where
  name := ACTIVATION_COMPONENT
  sha256 := (ActivatedContent.sha256Utf8? (activationJson fixtureSuitedRaw)).getD
    (CrewFieldMission.digestFilled 0)
  bytesUtf8 := activationJson fixtureSuitedRaw

def fixtureSuitedManifest : ActivatedContent.Manifest :=
  { admittedManifest with components := [fixtureSuitedComponent] }

def fixtureSuitedWorld : WorldActivation.WorldIdentity :=
  { admittedWorld with
    contentRoot := (ActivatedContent.manifestRoot? fixtureSuitedManifest).getD
      (CrewFieldMission.digestFilled 0) }

def fixtureSuitedMember? : Option WorldScopedCrewActivation := do
  let manifest ← ActivatedContent.decodeManifest fixtureSuitedManifest.toJson
  authorizeCrewActivationForWorld? fixtureSuitedWorld manifest

/-- The same document under the PRODUCTION suite ids but carrying the FIXTURE seal's
briefing commitment: the mint refuses on the deck commitment alone, so "name the
production suite" is not enough either — the commitment must check under the production
SHAKE-256 deck boundary over this crew's own deck. -/
def wrongCommitmentRaw : RawActivation :=
  { admittedRaw with
    fieldSession := { admittedRawConfig.sessionDigest with
      briefingCommitment := CrewFieldMission.fixtureRunSeal.session.briefingCommitment } }

/-- A different route table re-hashes the manifest and therefore no longer matches the
activated world's content root: a player cannot swap the salvage rules and keep the
world.  (The substituted activation still MINTS — first conjunct — so the refusal is the
ROOT, not a malformed document.) -/
def forgedSalvageRaw : RawActivation :=
  { admittedRaw with
    ordinarySalvage :=
      [ ⟨.maintenanceSpine, .returnNow, ⟨900⟩, MAX_PART_QUANTITY⟩
      , ⟨.signalGallery, .descendFurther, ⟨901⟩, MAX_PART_QUANTITY⟩ ] }

def forgedSalvageComponent : ActivatedContent.Component where
  name := ACTIVATION_COMPONENT
  sha256 := (ActivatedContent.sha256Utf8? (activationJson forgedSalvageRaw)).getD
    (CrewFieldMission.digestFilled 0)
  bytesUtf8 := activationJson forgedSalvageRaw

def forgedSalvageManifest : ActivatedContent.Manifest :=
  { admittedManifest with components := [forgedSalvageComponent] }

def forgedSalvageMember? : Option WorldScopedCrewActivation := do
  let manifest ← ActivatedContent.decodeManifest forgedSalvageManifest.toJson
  authorizeCrewActivationForWorld? admittedWorld manifest

/-- The component name is exact.  ⚠ The world here is the one whose `contentRoot` IS
the misnamed manifest's root, so `matchesWorldB` PASSES — first conjunct — and the
refusal is isolated to the name lookup. -/
def misnamedManifest : ActivatedContent.Manifest :=
  { admittedManifest with
    components := [{ admittedComponent with
      name := "poa.crew-field-mission.activation.v2" }] }

def misnamedWorld : WorldActivation.WorldIdentity :=
  { admittedWorld with
    contentRoot := (ActivatedContent.manifestRoot? misnamedManifest).getD
      (CrewFieldMission.digestFilled 0) }

def misnamedMember? : Option WorldScopedCrewActivation := do
  let manifest ← ActivatedContent.decodeManifest misnamedManifest.toJson
  authorizeCrewActivationForWorld? misnamedWorld manifest

/-- A world that is structurally fine and names a different content session cannot
consume this manifest, even though the manifest root is unchanged. -/
def crossSessionWorld : WorldActivation.WorldIdentity :=
  { admittedWorld with contentSession := CrewFieldMission.digestFilled 0x77 }

def crossSessionMember? : Option WorldScopedCrewActivation := do
  let manifest ← admittedValidatedManifest?
  authorizeCrewActivationForWorld? crossSessionWorld manifest

/-- The deck's own signed activation identity is pinned to the world.  ⚠ The world here
is the one whose `contentRoot` IS the re-hashed manifest's root, so `matchesWorldB`
PASSES and the mint still SUCCEEDS — both asserted — leaving the deck-lineage pin as the
only thing that can refuse. -/
def foreignDeckLineageRaw : RawActivation :=
  { admittedRaw with
    content := { admittedContent with
      deck := { DeckGraph.fixturePack with
        activation := { admittedDeckActivation with
          activationDigest := CrewFieldMission.digestFilled 0x66 } } } }

def foreignDeckLineageComponent : ActivatedContent.Component where
  name := ACTIVATION_COMPONENT
  sha256 := (ActivatedContent.sha256Utf8? (activationJson foreignDeckLineageRaw)).getD
    (CrewFieldMission.digestFilled 0)
  bytesUtf8 := activationJson foreignDeckLineageRaw

def foreignDeckLineageManifest : ActivatedContent.Manifest :=
  { admittedManifest with components := [foreignDeckLineageComponent] }

def foreignDeckLineageWorld : WorldActivation.WorldIdentity :=
  { admittedWorld with
    contentRoot := (ActivatedContent.manifestRoot? foreignDeckLineageManifest).getD
      (CrewFieldMission.digestFilled 0) }

def foreignDeckLineageMember? : Option WorldScopedCrewActivation := do
  let manifest ← ActivatedContent.decodeManifest foreignDeckLineageManifest.toJson
  authorizeCrewActivationForWorld? foreignDeckLineageWorld manifest

/-! ### Codec-shape refusals, on the real decoder -/

def truncatedActivationBytes : String :=
  ((activationJson admittedRaw).dropEnd 1).toString

def spliceAppendedActivationBytes : String :=
  ((activationJson admittedRaw).dropEnd 1).toString ++ ",\"replay_authority\":{}}"

def oversizedSalvageBytes : String :=
  activationJson { admittedRaw with
    ordinarySalvage :=
      List.replicate (MAX_PART_RULES + 1)
        ⟨.maintenanceSpine, .returnNow, ⟨900⟩, 2⟩ }

-- The sixteen pins (`#assert_compiled` + `native_decide`) live in
-- `CrewFieldMissionAdmissionFixtures.lean`, rooted in `PathOfAngelsGuards` — see the
-- Teeth header above.

end Dregg2.Games.PathOfAngels.CrewFieldMissionAdmission
