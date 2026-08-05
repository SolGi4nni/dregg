/-
# ContentContract — spoiler-free activation rules for authored PoA missions

This module is the typed boundary between a private authoring pack and the
public game engine.  Content identifiers are opaque natural-number carriers;
no prose, room names, encounter explanations, or proposed canon is copied into
this file.  The contract decides only finite mechanical facts:

* the four officer roles and their role-exact briefing shapes;
* a directed, phase-aware deck graph with a bounded extraction witness;
* bidirectional route/encounter membership and resolved artifact references;
* exact route × extraction coverage, finite budgets, and winnable outcomes;
* bounded beta-only recovery consequences;
* an explicit curator-only alpha-canon successor boundary; and
* provenance-linked relic custody which cannot become a market transfer.

`validateWire` returns stable numeric refusal codes.  Its `accepted` bit is not
an independent implementation: `validateWire_accepts_iff` connects it to the
proposition-carrying `ValidatedContent` constructor.  Authentication of the
private pack's canonical bytes remains the signed activation layer's job.
-/
import Dregg2.Games.PathOfAngels.CrewFieldMission
import Dregg2.Games.PathOfAngels.DeckGraph
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.ContentContract

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.CrewRelayExpedition

set_option autoImplicit false

abbrev CURRENT_SCHEMA_VERSION : Nat := 1
abbrev MAX_ROUTES : Nat := 16
abbrev MAX_ENCOUNTERS : Nat := 64
abbrev MAX_ARTIFACTS : Nat := 128
abbrev MAX_RELICS : Nat := 32
abbrev MAX_TURN_BUDGET : Nat := 64
abbrev MAX_OPERATIONAL_BUDGET : Nat := 256

/-! ## Opaque public identifiers and exact officer schema -/

structure OfficerId where value : Nat
deriving Repr, DecidableEq

structure CredentialId where value : Nat
deriving Repr, DecidableEq

structure RouteId where value : Nat
deriving Repr, DecidableEq

structure EncounterId where value : Nat
deriving Repr, DecidableEq

structure ArtifactId where value : Nat
deriving Repr, DecidableEq

structure RelicId where value : Nat
deriving Repr, DecidableEq

structure RecoveryId where value : Nat
deriving Repr, DecidableEq

structure PlaceId where value : Nat
deriving Repr, DecidableEq

structure AlphaFactId where value : Nat
deriving Repr, DecidableEq

structure OfficerSeat where
  officer : OfficerId
  credential : CredentialId
  role : CrewRole
deriving Repr, DecidableEq

inductive ObservationKind where
  | mappedRoute
  | structurallySoundRoute
  | hazardClearRoute
  | extractionWindow
deriving Repr, DecidableEq

def ObservationKind.role : ObservationKind → CrewRole
  | .mappedRoute => .pathfinder
  | .structurallySoundRoute => .engineer
  | .hazardClearRoute => .containment
  | .extractionWindow => .quartermaster

inductive DisclosureBoundary where
  | privateUntilSignedHandoff
deriving Repr, DecidableEq

structure BriefingShape where
  role : CrewRole
  observation : ObservationKind
  recommendedRoute : Option RouteId
  disclosure : DisclosureBoundary
deriving Repr, DecidableEq

def exactRoles : List CrewRole :=
  [.pathfinder, .engineer, .containment, .quartermaster]

def officerIds (pack : List OfficerSeat) : List OfficerId :=
  pack.map OfficerSeat.officer

def officerCredentials (pack : List OfficerSeat) : List CredentialId :=
  pack.map OfficerSeat.credential

/-! ## Routes, encounters, budgets, and recovery -/

structure RouteSpec where
  id : RouteId
  encounters : List EncounterId
  /-- Exact directed hotspot sequence; phase changes are interpreted by DeckGraph. -/
  path : List DeckGraph.HotspotId
deriving Repr, DecidableEq

structure EncounterSpec where
  id : EncounterId
  room : DeckGraph.RoomId
  routes : List RouteId
  betaArtifacts : List ArtifactId
deriving Repr, DecidableEq

structure ArtifactSpec where
  id : ArtifactId
  /-- `none` means the beta pack records an observation without inventing why. -/
  alphaInterpretation : Option AlphaFactId
deriving Repr, DecidableEq

inductive ExtractionChoice where
  | returnNow
  | descendFurther
deriving Repr, DecidableEq

inductive AgreementRule where
  | twoSpecialistSupport
  | fullCrewUnanimity
deriving Repr, DecidableEq

def requiredAgreement : ExtractionChoice → AgreementRule
  | .returnNow => .twoSpecialistSupport
  | .descendFurther => .fullCrewUnanimity

/-- Three specialist handoffs cost one unit each on safe return and two on a
deep recovery.  The route's authored operational cost is charged in addition. -/
def mandatorySpecialistSpend : ExtractionChoice → Nat
  | .returnNow => 3
  | .descendFurther => 6

structure Contribution where
  intel : Nat
  supplies : Nat
  cohesion : Nat
  influence : Nat
  score : Nat
  relics : List RelicId
deriving Repr, DecidableEq

structure ContributionBudget where
  intel : Nat
  supplies : Nat
  cohesion : Nat
  influence : Nat
  score : Nat
  relicAllowlist : List RelicId
deriving Repr, DecidableEq

inductive RecoveryGrade where
  | clean
  | equipmentUnavailable
  | marked
  | lostOpportunity
  | containmentDebt
deriving Repr, DecidableEq

inductive RecoveryDuration where
  | none
  | oneStudyCycle
  | contentEpoch
  | untilCuratorSuccessor
deriving Repr, DecidableEq

inductive RecoveryImplementation where
  | betaRecordOnly
  | automaticWorldMutation
deriving Repr, DecidableEq

structure RecoveryConsequence where
  id : RecoveryId
  grade : RecoveryGrade
  duration : RecoveryDuration
  implementation : RecoveryImplementation
  /-- Beta recovery may change local presentation, never silently debit world meters. -/
  globalMeterDebit : Nat
deriving Repr, DecidableEq

structure RouteOutcome where
  route : RouteId
  extraction : ExtractionChoice
  operationalCost : Nat
  agreement : AgreementRule
  featuredArtifact : ArtifactId
  contribution : Contribution
  recovery : RecoveryId
deriving Repr, DecidableEq

def RouteOutcome.key (outcome : RouteOutcome) : RouteId × ExtractionChoice :=
  (outcome.route, outcome.extraction)

/-! ## Relic custody is provenance, not a market flag -/

inductive CustodyLocation where
  | atEncounter (encounter : EncounterId)
  | crewCarried
  | quarantine
  | archive
  | market
deriving Repr, DecidableEq

inductive CustodyAuthority where
  | fullCrewUnanimity
  | explicitCuratorSuccessor
  | unilateralHolder
deriving Repr, DecidableEq

structure RelicSpec where
  id : RelicId
  sourceEncounter : EncounterId
  portable : Bool
  marketEligible : Bool
  alphaInterpretation : Option AlphaFactId
deriving Repr, DecidableEq

structure CustodyPlan where
  relic : RelicId
  source : CustodyLocation
  destination : CustodyLocation
  authority : CustodyAuthority
  directTradeAllowed : Bool
deriving Repr, DecidableEq

/-! ## Beta-to-alpha boundary -/

inductive ContentTier where
  | betaDraft
  | alphaCanon
deriving Repr, DecidableEq

inductive StoryAuthority where
  | explicitCuratorAction
  | automaticGameOutcome
  | holderVote
deriving Repr, DecidableEq

inductive CandidateRef where
  | place (id : PlaceId)
  | artifact (id : ArtifactId)
  | relic (id : RelicId)
deriving Repr, DecidableEq

structure PromotionHook where
  candidate : CandidateRef
  /-- A draft carries no alpha value.  The curator creates it in a successor. -/
  alphaValue : Option AlphaFactId
deriving Repr, DecidableEq

structure CanonBoundary where
  tier : ContentTier
  authoritative : Bool
  claimsActivated : Bool
  automaticPromotion : Bool
  authority : StoryAuthority
  directAlphaFacts : List AlphaFactId
deriving Repr, DecidableEq

/-! ## Whole mechanical pack -/

structure RawContent where
  schemaVersion : Nat
  place : PlaceId
  deck : DeckGraph.Pack
  officers : List OfficerSeat
  briefings : List BriefingShape
  routes : List RouteSpec
  encounters : List EncounterSpec
  artifacts : List ArtifactSpec
  outcomes : List RouteOutcome
  recoveries : List RecoveryConsequence
  relics : List RelicSpec
  custodyPlans : List CustodyPlan
  promotionHooks : List PromotionHook
  turnBudget : Nat
  operationalBudget : Nat
  contributionBudget : ContributionBudget
  canon : CanonBoundary
deriving DecidableEq

def routeIds (pack : RawContent) : List RouteId := pack.routes.map RouteSpec.id
def encounterIds (pack : RawContent) : List EncounterId := pack.encounters.map EncounterSpec.id
def artifactIds (pack : RawContent) : List ArtifactId := pack.artifacts.map ArtifactSpec.id
def relicIds (pack : RawContent) : List RelicId := pack.relics.map RelicSpec.id
def recoveryIds (pack : RawContent) : List RecoveryId := pack.recoveries.map RecoveryConsequence.id
def custodyRelicIds (pack : RawContent) : List RelicId := pack.custodyPlans.map CustodyPlan.relic

def routeById? : List RouteSpec → RouteId → Option RouteSpec
  | [], _ => none
  | route :: routes, id => if route.id = id then some route else routeById? routes id

def encounterById? : List EncounterSpec → EncounterId → Option EncounterSpec
  | [], _ => none
  | encounter :: encounters, id =>
      if encounter.id = id then some encounter else encounterById? encounters id

def relicById? : List RelicSpec → RelicId → Option RelicSpec
  | [], _ => none
  | relic :: relics, id => if relic.id = id then some relic else relicById? relics id

def recoveryById? : List RecoveryConsequence → RecoveryId →
    Option RecoveryConsequence
  | [], _ => none
  | recovery :: recoveries, id =>
      if recovery.id = id then some recovery else recoveryById? recoveries id

def custodyByRelic? : List CustodyPlan → RelicId → Option CustodyPlan
  | [], _ => none
  | plan :: plans, id => if plan.relic = id then some plan else custodyByRelic? plans id

def officerSchemaValidB (pack : RawContent) : Bool :=
  decide (pack.officers.map OfficerSeat.role = exactRoles) &&
  decide (officerIds pack.officers).Nodup &&
  decide (officerCredentials pack.officers).Nodup &&
  decide (pack.briefings.map BriefingShape.role = exactRoles) &&
  pack.briefings.all fun briefing =>
    decide (briefing.observation.role = briefing.role) &&
    decide (briefing.disclosure = .privateUntilSignedHandoff) &&
    match briefing.role, briefing.recommendedRoute with
    | .quartermaster, none => true
    | .quartermaster, some _ => false
    | _, some route => decide (route ∈ routeIds pack)
    | _, none => false

def deckValidB (pack : RawContent) : Bool :=
  DeckGraph.validateB pack.deck

def routeExtractsB (pack : RawContent) (route : RouteSpec) : Bool :=
  match DeckGraph.replay pack.deck pack.deck.navigationFuel
      (DeckGraph.initialPosition pack.deck) route.path with
  | none => false
  | some final => decide (final.room = pack.deck.extraction)

def routeEncounterSymmetricB (pack : RawContent) : Bool :=
  decide (0 < pack.routes.length ∧ pack.routes.length ≤ MAX_ROUTES) &&
  decide (0 < pack.encounters.length ∧ pack.encounters.length ≤ MAX_ENCOUNTERS) &&
  decide (routeIds pack).Nodup &&
  decide (encounterIds pack).Nodup &&
  decide (artifactIds pack).Nodup &&
  decide (pack.artifacts.length ≤ MAX_ARTIFACTS) &&
  pack.routes.all (fun route =>
    decide (route.encounters ≠ [] ∧ route.encounters.Nodup) &&
    decide (route.path ≠ []) &&
    routeExtractsB pack route &&
    route.encounters.all fun encounterId =>
      match encounterById? pack.encounters encounterId with
      | none => false
      | some encounter => decide (route.id ∈ encounter.routes)) &&
  pack.encounters.all (fun encounter =>
    decide (encounter.routes ≠ [] ∧ encounter.routes.Nodup) &&
    decide (encounter.room ∈ DeckGraph.roomIds pack.deck) &&
    decide encounter.betaArtifacts.Nodup &&
    encounter.betaArtifacts.all (fun artifact => decide (artifact ∈ artifactIds pack)) &&
    encounter.routes.all fun routeId =>
      match routeById? pack.routes routeId with
      | none => false
      | some route => decide (encounter.id ∈ route.encounters))

def expectedOutcomeKeys (pack : RawContent) : List (RouteId × ExtractionChoice) :=
  (routeIds pack).flatMap fun route =>
    [(route, .returnNow), (route, .descendFurther)]

def contributionWithinB (budget : ContributionBudget)
    (contribution : Contribution) : Bool :=
  decide (contribution.intel ≤ budget.intel) &&
  decide (contribution.supplies ≤ budget.supplies) &&
  decide (contribution.cohesion ≤ budget.cohesion) &&
  decide (contribution.influence ≤ budget.influence) &&
  decide (contribution.score ≤ budget.score) &&
  decide contribution.relics.Nodup &&
  contribution.relics.all fun relic => decide (relic ∈ budget.relicAllowlist)

def outcomeWinnableB (pack : RawContent) (outcome : RouteOutcome) : Bool :=
  match routeById? pack.routes outcome.route with
  | none => false
  | some route =>
      decide (mandatorySpecialistSpend outcome.extraction + outcome.operationalCost ≤
        pack.operationalBudget) &&
      decide (route.encounters.length +
        (match outcome.extraction with | .returnNow => 1 | .descendFurther => 2) ≤
        pack.turnBudget)

def budgetsValidB (pack : RawContent) : Bool :=
  decide (0 < pack.turnBudget ∧ pack.turnBudget ≤ MAX_TURN_BUDGET) &&
  decide (0 < pack.operationalBudget ∧
    pack.operationalBudget ≤ MAX_OPERATIONAL_BUDGET) &&
  decide (pack.outcomes.map RouteOutcome.key = expectedOutcomeKeys pack) &&
  pack.outcomes.all fun outcome =>
    decide (outcome.agreement = requiredAgreement outcome.extraction) &&
    decide (outcome.featuredArtifact ∈ artifactIds pack) &&
    contributionWithinB pack.contributionBudget outcome.contribution &&
    outcomeWinnableB pack outcome

def recoveryConsequenceValidB (recovery : RecoveryConsequence) : Bool :=
  decide ((recovery.grade = .clean) ↔ (recovery.duration = .none)) &&
  decide (recovery.implementation = .betaRecordOnly) &&
  decide (recovery.globalMeterDebit = 0)

def recoveryValidB (pack : RawContent) : Bool :=
  decide (recoveryIds pack).Nodup &&
  pack.recoveries.all recoveryConsequenceValidB &&
  pack.outcomes.all fun outcome =>
    match recoveryById? pack.recoveries outcome.recovery with
    | none => false
    | some _ => true

def custodyDestinationAllowedB (relic : RelicSpec)
    (destination : CustodyLocation) : Bool :=
  match destination with
  | .market => false
  | .atEncounter _ => false
  | .crewCarried => relic.portable
  | .quarantine | .archive => true

def relicCustodyValidB (pack : RawContent) : Bool :=
  decide (pack.relics.length ≤ MAX_RELICS) &&
  decide (relicIds pack).Nodup &&
  decide (custodyRelicIds pack = relicIds pack) &&
  decide (pack.contributionBudget.relicAllowlist = relicIds pack) &&
  pack.relics.all (fun relic =>
    decide (relic.sourceEncounter ∈ encounterIds pack) &&
    decide (relic.marketEligible = false) &&
    decide (relic.alphaInterpretation = none) &&
    match custodyByRelic? pack.custodyPlans relic.id with
    | none => false
    | some plan =>
        decide (plan.source = .atEncounter relic.sourceEncounter) &&
        custodyDestinationAllowedB relic plan.destination &&
        decide (plan.authority = .fullCrewUnanimity) &&
        decide (plan.directTradeAllowed = false)) &&
  pack.outcomes.all (fun outcome =>
    (match outcome.extraction with
      | .returnNow => decide (outcome.contribution.relics = [])
      | .descendFurther => true) &&
    outcome.contribution.relics.all fun relic =>
      decide (relic ∈ relicIds pack) &&
      match custodyByRelic? pack.custodyPlans relic with
      | none => false
      | some plan => decide (plan.authority = .fullCrewUnanimity))

def candidateResolvedB (pack : RawContent) : CandidateRef → Bool
  | .place id => decide (id = pack.place)
  | .artifact id => decide (id ∈ artifactIds pack)
  | .relic id => decide (id ∈ relicIds pack)

def canonBoundaryValidB (pack : RawContent) : Bool :=
  decide (pack.canon.tier = .betaDraft) &&
  decide (pack.canon.authoritative = false) &&
  decide (pack.canon.claimsActivated = false) &&
  decide (pack.canon.automaticPromotion = false) &&
  decide (pack.canon.authority = .explicitCuratorAction) &&
  decide (pack.canon.directAlphaFacts = []) &&
  pack.artifacts.all (fun artifact => decide (artifact.alphaInterpretation = none)) &&
  pack.promotionHooks.all fun hook =>
    candidateResolvedB pack hook.candidate && decide (hook.alphaValue = none)

/-! ## Runtime-facing validator and proof surface -/

structure ContentValid (pack : RawContent) : Prop where
  schema : pack.schemaVersion = CURRENT_SCHEMA_VERSION
  officers : officerSchemaValidB pack = true
  deck : deckValidB pack = true
  routeEncounter : routeEncounterSymmetricB pack = true
  budgets : budgetsValidB pack = true
  recovery : recoveryValidB pack = true
  relicCustody : relicCustodyValidB pack = true
  canonBoundary : canonBoundaryValidB pack = true

def contentValidB (pack : RawContent) : Bool :=
  decide (pack.schemaVersion = CURRENT_SCHEMA_VERSION) &&
  officerSchemaValidB pack &&
  deckValidB pack &&
  routeEncounterSymmetricB pack &&
  budgetsValidB pack &&
  recoveryValidB pack &&
  relicCustodyValidB pack &&
  canonBoundaryValidB pack

theorem contentValidB_sound (pack : RawContent)
    (h : contentValidB pack = true) : ContentValid pack := by
  unfold contentValidB at h
  obtain ⟨h, hcanon⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h, hrelic⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h, hrecovery⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h, hbudgets⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h, hroute⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h, hdeck⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨hschema, hofficer⟩ := Eq.mp (Bool.and_eq_true _ _) h
  exact {
    schema := of_decide_eq_true hschema
    officers := hofficer
    deck := hdeck
    routeEncounter := hroute
    budgets := hbudgets
    recovery := hrecovery
    relicCustody := hrelic
    canonBoundary := hcanon
  }

theorem contentValidB_complete (pack : RawContent)
    (h : ContentValid pack) : contentValidB pack = true := by
  simp [contentValidB, h.schema, h.officers, h.deck, h.routeEncounter,
    h.budgets, h.recovery, h.relicCustody, h.canonBoundary]

theorem contentValidB_iff (pack : RawContent) :
    contentValidB pack = true ↔ ContentValid pack :=
  ⟨contentValidB_sound pack, contentValidB_complete pack⟩

inductive ValidationError where
  | wrongSchema
  | officerSchema
  | deck
  | routeEncounter
  | budget
  | recovery
  | relicCustody
  | canonBoundary
deriving Repr, DecidableEq

def ValidationError.code : ValidationError → Nat
  | .wrongSchema => 1
  | .officerSchema => 2
  | .deck => 3
  | .routeEncounter => 4
  | .budget => 5
  | .recovery => 6
  | .relicCustody => 7
  | .canonBoundary => 8

def flag (valid : Bool) (error : ValidationError) : List ValidationError :=
  if valid then [] else [error]

def validationErrors (pack : RawContent) : List ValidationError :=
  flag (decide (pack.schemaVersion = CURRENT_SCHEMA_VERSION)) .wrongSchema ++
  flag (officerSchemaValidB pack) .officerSchema ++
  flag (deckValidB pack) .deck ++
  flag (routeEncounterSymmetricB pack) .routeEncounter ++
  flag (budgetsValidB pack) .budget ++
  flag (recoveryValidB pack) .recovery ++
  flag (relicCustodyValidB pack) .relicCustody ++
  flag (canonBoundaryValidB pack) .canonBoundary

structure WireValidation where
  schemaVersion : Nat
  accepted : Bool
  errorCodes : List Nat
deriving Repr, DecidableEq

def validateWire (pack : RawContent) : WireValidation where
  schemaVersion := CURRENT_SCHEMA_VERSION
  accepted := contentValidB pack
  errorCodes := (validationErrors pack).map ValidationError.code

theorem validationErrors_empty_iff (pack : RawContent) :
    validationErrors pack = [] ↔ contentValidB pack = true := by
  simp [validationErrors, flag, contentValidB, and_assoc]

theorem validateWire_accepts_iff (pack : RawContent) :
    (validateWire pack).accepted = true ↔ ContentValid pack := by
  exact contentValidB_iff pack

theorem validateWire_empty_errors_iff (pack : RawContent) :
    (validateWire pack).errorCodes = [] ↔ ContentValid pack := by
  rw [show (validateWire pack).errorCodes =
    (validationErrors pack).map ValidationError.code by rfl]
  simp only [List.map_eq_nil_iff]
  rw [validationErrors_empty_iff, contentValidB_iff]

structure ValidatedContent where
  pack : RawContent
  valid : ContentValid pack

def validate? (pack : RawContent) : Option ValidatedContent :=
  if h : contentValidB pack = true then
    some { pack := pack, valid := contentValidB_sound pack h }
  else none

theorem validate_isSome_iff (pack : RawContent) :
    (validate? pack).isSome = true ↔ ContentValid pack := by
  by_cases h : contentValidB pack = true
  · simp [validate?, h, (contentValidB_iff pack).mp h]
  · have hn : ¬ ContentValid pack := by
      intro valid
      exact h ((contentValidB_iff pack).mpr valid)
    simp [validate?, h, hn]

/-- Successful activation carries the phase-aware directed extraction theorem
from the existing graph kernel, rather than reimplementing graph semantics. -/
theorem validation_implies_phase_aware_extraction (pack : RawContent)
    (valid : ContentValid pack) : DeckGraph.ReachableExtraction pack.deck :=
  DeckGraph.validation_implies_reachable_extraction pack.deck valid.deck

theorem validation_implies_exact_officer_roles (pack : RawContent)
    (valid : ContentValid pack) : pack.officers.map OfficerSeat.role = exactRoles := by
  have h := valid.officers
  unfold officerSchemaValidB at h
  obtain ⟨h, _⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h, _⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h, _⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨hroles, _⟩ := Eq.mp (Bool.and_eq_true _ _) h
  exact of_decide_eq_true hroles

theorem validation_implies_no_direct_alpha_facts (pack : RawContent)
    (valid : ContentValid pack) :
    pack.canon.directAlphaFacts = [] ∧ pack.canon.automaticPromotion = false := by
  have h := valid.canonBoundary
  unfold canonBoundaryValidB at h
  obtain ⟨h, _⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h, _⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h, hfacts⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨h, _⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨_, hautomatic⟩ := Eq.mp (Bool.and_eq_true _ _) h
  exact ⟨of_decide_eq_true hfacts, of_decide_eq_true hautomatic⟩

theorem validation_implies_no_market_relics (pack : RawContent)
    (valid : ContentValid pack) :
    ∀ relic ∈ pack.relics, relic.marketEligible = false := by
  have h := valid.relicCustody
  unfold relicCustodyValidB at h
  obtain ⟨h, _⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨_, hall⟩ := Eq.mp (Bool.and_eq_true _ _) h
  intro relic hmember
  have hrelic := (List.all_eq_true.mp hall) relic hmember
  obtain ⟨hrelic, _⟩ := Eq.mp (Bool.and_eq_true _ _) hrelic
  obtain ⟨hrelic, _⟩ := Eq.mp (Bool.and_eq_true _ _) hrelic
  obtain ⟨_, hmarket⟩ := Eq.mp (Bool.and_eq_true _ _) hrelic
  exact of_decide_eq_true hmarket

theorem validation_implies_all_outcomes_winnable (pack : RawContent)
    (valid : ContentValid pack) :
    ∀ outcome ∈ pack.outcomes, outcomeWinnableB pack outcome = true := by
  have h := valid.budgets
  unfold budgetsValidB at h
  obtain ⟨_, hall⟩ := Eq.mp (Bool.and_eq_true _ _) h
  intro outcome hmember
  have houtcome := (List.all_eq_true.mp hall) outcome hmember
  exact (Eq.mp (Bool.and_eq_true _ _) houtcome).2

theorem validation_implies_route_encounter_forward (pack : RawContent)
    (valid : ContentValid pack) :
    ∀ route ∈ pack.routes, ∀ encounterId ∈ route.encounters,
      ∃ encounter,
        encounterById? pack.encounters encounterId = some encounter ∧
        route.id ∈ encounter.routes := by
  have h := valid.routeEncounter
  unfold routeEncounterSymmetricB at h
  obtain ⟨h, _⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨_, hallRoutes⟩ := Eq.mp (Bool.and_eq_true _ _) h
  intro route hroute encounterId hencounter
  have hrouteValid := (List.all_eq_true.mp hallRoutes) route hroute
  have hallEncounters := (Eq.mp (Bool.and_eq_true _ _) hrouteValid).2
  have hresolved := (List.all_eq_true.mp hallEncounters) encounterId hencounter
  cases heq : encounterById? pack.encounters encounterId with
  | none => simp [heq] at hresolved
  | some encounter =>
      have hmembership : decide (route.id ∈ encounter.routes) = true := by
        simpa [heq] using hresolved
      exact ⟨encounter, rfl, of_decide_eq_true hmembership⟩

theorem validation_implies_every_route_extracts (pack : RawContent)
    (valid : ContentValid pack) :
    ∀ route ∈ pack.routes, routeExtractsB pack route = true := by
  have h := valid.routeEncounter
  unfold routeEncounterSymmetricB at h
  obtain ⟨h, _⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨_, hallRoutes⟩ := Eq.mp (Bool.and_eq_true _ _) h
  intro route hroute
  have hrouteValid := (List.all_eq_true.mp hallRoutes) route hroute
  obtain ⟨hrouteValid, _⟩ := Eq.mp (Bool.and_eq_true _ _) hrouteValid
  exact (Eq.mp (Bool.and_eq_true _ _) hrouteValid).2

theorem validation_implies_encounter_route_reverse (pack : RawContent)
    (valid : ContentValid pack) :
    ∀ encounter ∈ pack.encounters, ∀ routeId ∈ encounter.routes,
      ∃ route,
        routeById? pack.routes routeId = some route ∧
        encounter.id ∈ route.encounters := by
  have h := valid.routeEncounter
  unfold routeEncounterSymmetricB at h
  have hallEncounters := (Eq.mp (Bool.and_eq_true _ _) h).2
  intro encounter hencounter routeId hroute
  have hencounterValid := (List.all_eq_true.mp hallEncounters) encounter hencounter
  have hallRoutes := (Eq.mp (Bool.and_eq_true _ _) hencounterValid).2
  have hresolved := (List.all_eq_true.mp hallRoutes) routeId hroute
  cases heq : routeById? pack.routes routeId with
  | none => simp [heq] at hresolved
  | some route =>
      have hmembership : decide (encounter.id ∈ route.encounters) = true := by
        simpa [heq] using hresolved
      exact ⟨route, rfl, of_decide_eq_true hmembership⟩

theorem validation_implies_recovery_is_beta_local (pack : RawContent)
    (valid : ContentValid pack) :
    ∀ recovery ∈ pack.recoveries,
      recovery.implementation = .betaRecordOnly ∧ recovery.globalMeterDebit = 0 := by
  have h := valid.recovery
  unfold recoveryValidB at h
  obtain ⟨h, _⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨_, hall⟩ := Eq.mp (Bool.and_eq_true _ _) h
  intro recovery hmember
  have hrecovery := (List.all_eq_true.mp hall) recovery hmember
  unfold recoveryConsequenceValidB at hrecovery
  obtain ⟨h, hdebit⟩ := Eq.mp (Bool.and_eq_true _ _) hrecovery
  obtain ⟨_, himplementation⟩ := Eq.mp (Bool.and_eq_true _ _) h
  exact ⟨of_decide_eq_true himplementation, of_decide_eq_true hdebit⟩

theorem allowed_custody_destination_is_not_market (relic : RelicSpec)
    (destination : CustodyLocation)
    (h : custodyDestinationAllowedB relic destination = true) :
    destination ≠ .market := by
  cases destination <;> simp_all [custodyDestinationAllowedB]

/-! ## Spoiler-free executable specimen and named hostile examples -/

def fixtureRoutes : List RouteSpec :=
  [ { id := ⟨0⟩, encounters := [⟨10⟩, ⟨11⟩], path := DeckGraph.fixturePath }
  , { id := ⟨1⟩, encounters := [⟨10⟩, ⟨12⟩], path := DeckGraph.fixturePath }
  , { id := ⟨2⟩, encounters := [⟨10⟩, ⟨13⟩], path := DeckGraph.fixturePath } ]

def fixtureEncounters : List EncounterSpec :=
  [ { id := ⟨10⟩, room := DeckGraph.fixtureRoomB.id,
      routes := [⟨0⟩, ⟨1⟩, ⟨2⟩], betaArtifacts := [⟨20⟩] }
  , { id := ⟨11⟩, room := DeckGraph.fixtureRoomC.id,
      routes := [⟨0⟩], betaArtifacts := [⟨21⟩] }
  , { id := ⟨12⟩, room := DeckGraph.fixtureRoomD.id,
      routes := [⟨1⟩], betaArtifacts := [⟨22⟩] }
  , { id := ⟨13⟩, room := DeckGraph.fixtureExtraction.id,
      routes := [⟨2⟩], betaArtifacts := [⟨23⟩] } ]

def fixtureArtifacts : List ArtifactSpec :=
  [ { id := ⟨20⟩, alphaInterpretation := none }
  , { id := ⟨21⟩, alphaInterpretation := none }
  , { id := ⟨22⟩, alphaInterpretation := none }
  , { id := ⟨23⟩, alphaInterpretation := none } ]

def fixtureOfficers : List OfficerSeat :=
  [ { officer := ⟨0⟩, credential := ⟨100⟩, role := .pathfinder }
  , { officer := ⟨1⟩, credential := ⟨101⟩, role := .engineer }
  , { officer := ⟨2⟩, credential := ⟨102⟩, role := .containment }
  , { officer := ⟨3⟩, credential := ⟨103⟩, role := .quartermaster } ]

def fixtureBriefings : List BriefingShape :=
  [ { role := .pathfinder, observation := .mappedRoute,
      recommendedRoute := some ⟨0⟩, disclosure := .privateUntilSignedHandoff }
  , { role := .engineer, observation := .structurallySoundRoute,
      recommendedRoute := some ⟨1⟩, disclosure := .privateUntilSignedHandoff }
  , { role := .containment, observation := .hazardClearRoute,
      recommendedRoute := some ⟨2⟩, disclosure := .privateUntilSignedHandoff }
  , { role := .quartermaster, observation := .extractionWindow,
      recommendedRoute := none, disclosure := .privateUntilSignedHandoff } ]

def fixtureBudget : ContributionBudget :=
  { intel := 12, supplies := 8, cohesion := 8, influence := 0, score := 100,
    relicAllowlist := [⟨30⟩, ⟨31⟩, ⟨32⟩] }

def fixtureContribution (score : Nat) (relics : List RelicId) : Contribution :=
  { intel := 2, supplies := 1, cohesion := 2, influence := 0,
    score := score, relics := relics }

def fixtureOutcomes : List RouteOutcome :=
  [ { route := ⟨0⟩, extraction := .returnNow, operationalCost := 2,
      agreement := .twoSpecialistSupport, featuredArtifact := ⟨20⟩,
      contribution := fixtureContribution 10 [], recovery := ⟨40⟩ }
  , { route := ⟨0⟩, extraction := .descendFurther, operationalCost := 5,
      agreement := .fullCrewUnanimity, featuredArtifact := ⟨21⟩,
      contribution := fixtureContribution 20 [⟨30⟩], recovery := ⟨41⟩ }
  , { route := ⟨1⟩, extraction := .returnNow, operationalCost := 3,
      agreement := .twoSpecialistSupport, featuredArtifact := ⟨22⟩,
      contribution := fixtureContribution 12 [], recovery := ⟨40⟩ }
  , { route := ⟨1⟩, extraction := .descendFurther, operationalCost := 7,
      agreement := .fullCrewUnanimity, featuredArtifact := ⟨22⟩,
      contribution := fixtureContribution 30 [⟨31⟩], recovery := ⟨41⟩ }
  , { route := ⟨2⟩, extraction := .returnNow, operationalCost := 4,
      agreement := .twoSpecialistSupport, featuredArtifact := ⟨23⟩,
      contribution := fixtureContribution 14 [], recovery := ⟨40⟩ }
  , { route := ⟨2⟩, extraction := .descendFurther, operationalCost := 8,
      agreement := .fullCrewUnanimity, featuredArtifact := ⟨23⟩,
      contribution := fixtureContribution 40 [⟨32⟩], recovery := ⟨41⟩ } ]

def fixtureRecoveries : List RecoveryConsequence :=
  [ { id := ⟨40⟩, grade := .clean, duration := .none,
      implementation := .betaRecordOnly, globalMeterDebit := 0 }
  , { id := ⟨41⟩, grade := .containmentDebt,
      duration := .untilCuratorSuccessor,
      implementation := .betaRecordOnly, globalMeterDebit := 0 } ]

def fixtureRelics : List RelicSpec :=
  [ { id := ⟨30⟩, sourceEncounter := ⟨11⟩, portable := true,
      marketEligible := false, alphaInterpretation := none }
  , { id := ⟨31⟩, sourceEncounter := ⟨12⟩, portable := true,
      marketEligible := false, alphaInterpretation := none }
  , { id := ⟨32⟩, sourceEncounter := ⟨13⟩, portable := false,
      marketEligible := false, alphaInterpretation := none } ]

def fixtureCustody : List CustodyPlan :=
  [ { relic := ⟨30⟩, source := .atEncounter ⟨11⟩,
      destination := .quarantine, authority := .fullCrewUnanimity,
      directTradeAllowed := false }
  , { relic := ⟨31⟩, source := .atEncounter ⟨12⟩,
      destination := .crewCarried, authority := .fullCrewUnanimity,
      directTradeAllowed := false }
  , { relic := ⟨32⟩, source := .atEncounter ⟨13⟩,
      destination := .archive, authority := .fullCrewUnanimity,
      directTradeAllowed := false } ]

def fixtureCanon : CanonBoundary :=
  { tier := .betaDraft, authoritative := false, claimsActivated := false,
    automaticPromotion := false, authority := .explicitCuratorAction,
    directAlphaFacts := [] }

def fixtureContent : RawContent :=
  { schemaVersion := CURRENT_SCHEMA_VERSION
    place := ⟨50⟩
    deck := DeckGraph.fixturePack
    officers := fixtureOfficers
    briefings := fixtureBriefings
    routes := fixtureRoutes
    encounters := fixtureEncounters
    artifacts := fixtureArtifacts
    outcomes := fixtureOutcomes
    recoveries := fixtureRecoveries
    relics := fixtureRelics
    custodyPlans := fixtureCustody
    promotionHooks :=
      [ { candidate := .place ⟨50⟩, alphaValue := none }
      , { candidate := .artifact ⟨20⟩, alphaValue := none }
      , { candidate := .relic ⟨30⟩, alphaValue := none } ]
    turnBudget := 18
    operationalBudget := 20
    contributionBudget := fixtureBudget
    canon := fixtureCanon }

theorem fixture_content_is_valid : contentValidB fixtureContent = true := by
  native_decide

def hostileRoleRelabel : RawContent :=
  { fixtureContent with officers :=
      [ { officer := ⟨0⟩, credential := ⟨100⟩, role := .quartermaster }
      , { officer := ⟨1⟩, credential := ⟨101⟩, role := .engineer }
      , { officer := ⟨2⟩, credential := ⟨102⟩, role := .containment }
      , { officer := ⟨3⟩, credential := ⟨103⟩, role := .quartermaster } ] }

theorem hostile_role_relabel_refused :
    (validateWire hostileRoleRelabel).errorCodes = [2] := by native_decide

def hostileUnreachableExtraction : RawContent :=
  { fixtureContent with deck := DeckGraph.boundedSearchFailurePack }

theorem hostile_unreachable_extraction_refused :
    (validateWire hostileUnreachableExtraction).errorCodes = [3, 4] := by native_decide

def hostileAsymmetricEncounter : RawContent :=
  { fixtureContent with routes :=
      [ { id := ⟨0⟩, encounters := [⟨11⟩], path := DeckGraph.fixturePath }
      , { id := ⟨1⟩, encounters := [⟨10⟩, ⟨12⟩], path := DeckGraph.fixturePath }
      , { id := ⟨2⟩, encounters := [⟨10⟩, ⟨13⟩], path := DeckGraph.fixturePath } ] }

theorem hostile_route_encounter_asymmetry_refused :
    (validateWire hostileAsymmetricEncounter).errorCodes = [4] := by native_decide

def hostileUnwinnableOutcome : RawContent :=
  { fixtureContent with outcomes :=
      { route := ⟨0⟩, extraction := .returnNow, operationalCost := 99,
        agreement := .twoSpecialistSupport, featuredArtifact := ⟨20⟩,
        contribution := fixtureContribution 10 [], recovery := ⟨40⟩ } ::
      fixtureOutcomes.drop 1 }

theorem hostile_unwinnable_budget_refused :
    (validateWire hostileUnwinnableOutcome).errorCodes = [5] := by native_decide

def hostileAutomaticRecovery : RawContent :=
  { fixtureContent with recoveries :=
      [ { id := ⟨40⟩, grade := .clean, duration := .none,
          implementation := .betaRecordOnly, globalMeterDebit := 0 }
      , { id := ⟨41⟩, grade := .containmentDebt,
          duration := .untilCuratorSuccessor,
          implementation := .automaticWorldMutation, globalMeterDebit := 1 } ] }

theorem hostile_automatic_recovery_refused :
    (validateWire hostileAutomaticRecovery).errorCodes = [6] := by native_decide

def hostileMarketRelic : RawContent :=
  { fixtureContent with relics :=
      [ { id := ⟨30⟩, sourceEncounter := ⟨11⟩, portable := true,
          marketEligible := true, alphaInterpretation := none }
      , { id := ⟨31⟩, sourceEncounter := ⟨12⟩, portable := true,
          marketEligible := false, alphaInterpretation := none }
      , { id := ⟨32⟩, sourceEncounter := ⟨13⟩, portable := false,
          marketEligible := false, alphaInterpretation := none } ] }

theorem hostile_market_relic_refused :
    (validateWire hostileMarketRelic).errorCodes = [7] := by native_decide

def hostileSelfPromotion : RawContent :=
  { fixtureContent with promotionHooks :=
      [{ candidate := .place ⟨50⟩, alphaValue := some ⟨99⟩ }] }

theorem hostile_direct_alpha_promotion_refused :
    (validateWire hostileSelfPromotion).errorCodes = [8] := by native_decide

#assert_axioms contentValidB_sound
#assert_axioms contentValidB_complete
#assert_axioms contentValidB_iff
#assert_axioms validationErrors_empty_iff
#assert_axioms validateWire_accepts_iff
#assert_axioms validateWire_empty_errors_iff
#assert_axioms validate_isSome_iff
#assert_axioms validation_implies_phase_aware_extraction
#assert_axioms validation_implies_exact_officer_roles
#assert_axioms validation_implies_no_direct_alpha_facts
#assert_axioms validation_implies_no_market_relics
#assert_axioms validation_implies_all_outcomes_winnable
#assert_axioms validation_implies_route_encounter_forward
#assert_axioms validation_implies_every_route_extracts
#assert_axioms validation_implies_encounter_route_reverse
#assert_axioms validation_implies_recovery_is_beta_local
#assert_axioms allowed_custody_destination_is_not_market
#assert_compiled fixture_content_is_valid
#assert_compiled hostile_role_relabel_refused
#assert_compiled hostile_unreachable_extraction_refused
#assert_compiled hostile_route_encounter_asymmetry_refused
#assert_compiled hostile_unwinnable_budget_refused
#assert_compiled hostile_automatic_recovery_refused
#assert_compiled hostile_market_relic_refused
#assert_compiled hostile_direct_alpha_promotion_refused

end Dregg2.Games.PathOfAngels.ContentContract
