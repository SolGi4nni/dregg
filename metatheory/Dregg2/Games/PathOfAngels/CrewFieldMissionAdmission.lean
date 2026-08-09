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

/-! ## The admitted fixture — a production-suited crew in an activated world

Deployment-free test vectors, not canon.  ⚠ This crew is NOT
`CrewFieldMission.katRawConfig`: the KAT world inherits
`DeckGraph.fixtureActivation`'s ALL-ZERO federation and content session, and
`WorldActivation.validWorld` refuses a zero federation, so a KAT-sessioned activation
could never be a member of any valid world.  The identity fields below are therefore
authored nonzero, which costs the real ML-DSA-65 keypair (its signatures are bound to
the KAT session) and buys the thing this module is about: an activation that an audited
world can actually carry. -/

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
  roster := CrewRelayExpedition.fixtureRoster
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
