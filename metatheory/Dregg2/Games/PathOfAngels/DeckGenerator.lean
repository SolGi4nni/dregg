/-
# DeckGenerator — finalized-seed procedural expedition packs

This is a bounded content *generator*, not a prose generator.  Its output is a
finite navigation graph plus abstract encounter, salvage, and discovery slots.
It has no constructor for room names, dialogue, or canon claims.  A curator may
skin these mechanics later without changing the generated semantic pack.

The randomness boundary is explicit.  A `FinalizedMissionSeed` can be obtained
only after `DailyMission.select` has selected a mission at a finalized epoch and
the selection has been checked against the activated mission policy.  Every
choice is an indexed draw from the mission's committed `runSeed` and the exact
selection identity.  The present mixer is deterministic scheduling semantics,
not a cryptographic beacon: unpredictability belongs to the finalized value
committed into `runSeed`.

Validation replays the authored extraction path, runs `DeckGraph.validateB`,
and then asks the existing `DeckExpedition.configValidB` to enforce officer,
encounter, resource, reward, and custody-shape constraints.  Finally it demands
byte-for-byte semantic equality with regeneration from the finalized seed.
-/
import Dregg2.Games.PathOfAngels.DailyMission
import Dregg2.Games.PathOfAngels.DeckExpedition

namespace Dregg2.Games.PathOfAngels.DeckGenerator

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.DailyMission
open Dregg2.Games.PathOfAngels.DeckGraph
open Dregg2.Games.PathOfAngels.DeckExpedition

set_option autoImplicit false

/-! ## Finalized mission seed and indexed draws -/

abbrev DRAW_COUNT : Nat := 16
abbrev DrawIndex := Fin DRAW_COUNT

/-- Raw inputs at the semantic finality boundary.  `selection` is not a browser
epoch: its private constructor is produced by `DailyMission.select`. -/
structure MechanicSlots where
  rewardRelic : Option RelicId
  discovery : Option ArtifactRef
deriving DecidableEq

structure SeedRequest where
  selection : DailyMission.Selection
  activation : ActivationIdentity
  policy : ActivityOutcome.Policy
  slots : MechanicSlots
deriving DecidableEq

/-- All identity fields that make a run seed belong to one finalized mission. -/
def seedRequestValidB (request : SeedRequest) : Bool :=
  decide (request.selection.mission = request.policy.mission.missionId) &&
  decide (request.selection.federationId = request.policy.mission.federationId) &&
  decide (request.selection.contentEpoch = request.policy.mission.epoch) &&
  decide (request.selection.contentRoot = request.policy.mission.contentRoot) &&
  decide (request.selection.activationDigest = request.policy.mission.activationDigest) &&
  decide (request.selection.contentSession = request.policy.mission.contentSession) &&
  decide (request.activation.federationId = request.policy.mission.federationId) &&
  decide (request.activation.contentEpoch = request.policy.mission.epoch) &&
  decide (request.activation.contentRoot = request.policy.mission.contentRoot) &&
  decide (request.activation.activationDigest = request.policy.mission.activationDigest) &&
  decide (request.activation.contentSession = request.policy.mission.contentSession) &&
  (match request.slots.rewardRelic with
    | none => true
    | some relic =>
        decide (0 < request.policy.mission.budget.relics.val) &&
        decide (relic ∈ request.policy.mission.allowedRelics)) &&
  (match request.slots.discovery with
    | none => true
    | some artifact =>
        decide (0 < request.policy.resultLimit.val) &&
        decide (artifact ∈ request.policy.allowedBeta))

/-- Checked finalized seed.  The seed bytes themselves come only from the exact
mission policy selected above; there is no second caller-supplied seed field. -/
structure FinalizedMissionSeed where
  request : SeedRequest
  valid : seedRequestValidB request = true

def finalizeSeed? (request : SeedRequest) : Option FinalizedMissionSeed :=
  if h : seedRequestValidB request = true then some { request, valid := h }
  else none

theorem FinalizedMissionSeed.binds_selected_mission
    (seed : FinalizedMissionSeed) :
    seed.request.selection.mission = seed.request.policy.mission.missionId := by
  have h := seed.valid
  simp only [seedRequestValidB, Bool.and_eq_true, decide_eq_true_eq] at h
  aesop

theorem FinalizedMissionSeed.binds_finalized_activation
    (seed : FinalizedMissionSeed) :
    seed.request.selection.contentEpoch = seed.request.policy.mission.epoch ∧
    seed.request.selection.activationDigest = seed.request.activation.activationDigest ∧
    seed.request.selection.contentSession = seed.request.activation.contentSession := by
  have h := seed.valid
  simp only [seedRequestValidB, Bool.and_eq_true, decide_eq_true_eq] at h
  aesop

/-- The only convenience entry point: selection happens before seed validation. -/
def finalizeFromDaily? (catalog : DailyMission.Catalog)
    (request : DailyMission.Request) (activation : ActivationIdentity)
    (policy : ActivityOutcome.Policy) (slots : MechanicSlots) :
    Option FinalizedMissionSeed := do
  let selection ← DailyMission.select catalog request
  finalizeSeed? { selection, activation, policy, slots }

def digestByteAt (digest : Digest32) (index : Nat) : Nat :=
  let position := index % 32
  have inBounds : position < digest.bytes.length := by
    rw [digest.length_eq]
    exact Nat.mod_lt _ (by decide)
  (digest.bytes.get ⟨position, inBounds⟩).val

/-- One stable draw word.  Domain separation is by the fixed index and by every
finalized selection component that can choose a different mission activation. -/
def drawWord (seed : FinalizedMissionSeed) (index : DrawIndex) : Nat :=
  digestByteAt seed.request.policy.mission.runSeed index.val +
  3 * digestByteAt seed.request.selection.catalogDigest (index.val + 7) +
  5 * digestByteAt seed.request.selection.activationDigest (index.val + 13) +
  17 * index.val +
  19 * seed.request.selection.finalizedEpoch.value +
  23 * seed.request.selection.mission.value

/-- Reject-free bounded mapping for a caller-supplied positive bound. -/
def drawBounded (seed : FinalizedMissionSeed) (index : DrawIndex)
    (bound : Nat) (positive : 0 < bound) : Fin bound :=
  ⟨drawWord seed index % bound, Nat.mod_lt _ positive⟩

theorem drawBounded_lt (seed : FinalizedMissionSeed) (index : DrawIndex)
    (bound : Nat) (positive : 0 < bound) :
    (drawBounded seed index bound positive).val < bound :=
  (drawBounded seed index bound positive).isLt

theorem drawBounded_deterministic (seed : FinalizedMissionSeed)
    (index : DrawIndex) (bound : Nat) (positive : 0 < bound) :
    drawBounded seed index bound positive = drawBounded seed index bound positive :=
  rfl

/-! ## Abstract generated mechanics -/

inductive Layout where
  | splitMerge
  | braidedReturn
  | offsetShaft
deriving Repr, DecidableEq

inductive EncounterClass where
  | pressure
  | unstableMachinery
  | containment
deriving Repr, DecidableEq

structure Encounter where
  id : HazardId
  room : RoomId
  kind : EncounterClass
  damage : Fin 4
  supplyCost : Nat
deriving Repr, DecidableEq

def Encounter.toHazard (encounter : Encounter) : HazardSpec where
  id := encounter.id
  room := encounter.room
  damage := encounter.damage
  supplyCost := encounter.supplyCost

/-- The generated semantic object.  It deliberately contains no strings. -/
structure Candidate where
  layout : Layout
  pack : DeckGraph.Pack
  extractionPath : List HotspotId
  encounters : List Encounter
  salvage : List SalvageSpec
  discoveries : List DiscoverySpec
  dailyRunBudget : Nat
  turnBudget : Nat
  operationalSupplyBudget : Nat
deriving DecidableEq

def Candidate.hazards (candidate : Candidate) : List HazardSpec :=
  candidate.encounters.map Encounter.toHazard

def standardPathfinder : OfficerProfile := { id := ⟨101⟩, role := .pathfinder }
def standardEngineer : OfficerProfile := { id := ⟨102⟩, role := .engineer }
def standardContainment : OfficerProfile := { id := ⟨103⟩, role := .containment }
def standardMedic : OfficerProfile := { id := ⟨104⟩, role := .medic }

def standardOfficers : List OfficerProfile :=
  [standardPathfinder, standardEngineer, standardContainment, standardMedic]

def standardParty : List OfficerId := standardOfficers.map OfficerProfile.id

private def room (base offset : Nat) : Room := { id := ⟨base + offset⟩ }

private def hotspot (base offset : Nat) (source destination : Room)
    (modifier : Modifier := .oneWay) : Hotspot :=
  { id := ⟨base + offset⟩, source := source.id, destination := destination.id, modifier }

def layoutOf (seed : FinalizedMissionSeed) : Layout :=
  match (drawBounded seed 0 3 (by decide)).val with
  | 0 => .splitMerge
  | 1 => .braidedReturn
  | _ => .offsetShaft

def packNumber (seed : FinalizedMissionSeed) : Nat :=
  seed.request.policy.mission.missionId.value * 1_000_000 +
    seed.request.selection.finalizedEpoch.value * 100 +
    (drawBounded seed 1 97 (by decide)).val

private def generatedRooms (seed : FinalizedMissionSeed) : List Room :=
  let base := packNumber seed * 10
  (List.range 7).map (room base)

private def roomAt (seed : FinalizedMissionSeed) (index : Fin 7) : Room :=
  (generatedRooms seed).get ⟨index.val, by simp [generatedRooms]⟩

private def generatedHotspots (seed : FinalizedMissionSeed) : List Hotspot :=
  let r0 := roomAt seed 0
  let r1 := roomAt seed 1
  let r2 := roomAt seed 2
  let r3 := roomAt seed 3
  let r4 := roomAt seed 4
  let r5 := roomAt seed 5
  let r6 := roomAt seed 6
  let base := packNumber seed * 10
  match layoutOf seed with
  | .splitMerge =>
      [ hotspot base 0 r0 r1
      , hotspot base 1 r1 r2 (.wrap .horizontal)
      , hotspot base 2 r2 r5 (.mirror .vertical)
      , hotspot base 3 r1 r3
      , hotspot base 4 r3 r4
      , hotspot base 5 r4 r5
      , hotspot base 6 r5 r6 (.phase 0 1) ]
  | .braidedReturn =>
      [ hotspot base 0 r0 r1
      , hotspot base 1 r1 r2 (.mirror .horizontal)
      , hotspot base 2 r2 r3
      , hotspot base 3 r3 r6 (.phase 0 1)
      , hotspot base 4 r1 r4
      , hotspot base 5 r4 r5 (.wrap .vertical)
      , hotspot base 6 r5 r6 (.phase 0 1) ]
  | .offsetShaft =>
      [ hotspot base 0 r0 r1
      , hotspot base 1 r1 r2 (.wrap .vertical)
      , hotspot base 2 r2 r3
      , hotspot base 3 r3 r6 (.phase 0 1)
      , hotspot base 4 r1 r4 (.mirror .horizontal)
      , hotspot base 5 r4 r5
      , hotspot base 6 r5 r2 ]

private def safeHotspotOffsets (seed : FinalizedMissionSeed) : List Nat :=
  match layoutOf seed with
  | .splitMerge => [0, 1, 2, 6]
  | .braidedReturn => [0, 1, 2, 3]
  | .offsetShaft => [0, 1, 2, 3]

private def extractionPath (seed : FinalizedMissionSeed) : List HotspotId :=
  let base := packNumber seed * 10
  (safeHotspotOffsets seed).map fun offset => ⟨base + offset⟩

private def branchRooms (seed : FinalizedMissionSeed) : Room × Room :=
  (roomAt seed 4, roomAt seed 5)

private def encounterClass (seed : FinalizedMissionSeed) : EncounterClass :=
  match (drawBounded seed 2 3 (by decide)).val with
  | 0 => .pressure
  | 1 => .unstableMachinery
  | _ => .containment

private def generatedEncounter (seed : FinalizedMissionSeed) : Encounter :=
  let branch := branchRooms seed
  { id := ⟨packNumber seed * 10 + 50⟩
    room := branch.1.id
    kind := encounterClass seed
    damage := ⟨1 + (drawBounded seed 3 2 (by decide)).val, by omega⟩
    supplyCost := 1 + (drawBounded seed 4 3 (by decide)).val }

private def generatedSalvage (seed : FinalizedMissionSeed) : List SalvageSpec :=
  match seed.request.slots.rewardRelic with
  | none => []
  | some relic =>
      [{ id := ⟨packNumber seed * 10 + 60⟩
         room := (branchRooms seed).2.id
         relic }]

private def generatedDiscoveries (seed : FinalizedMissionSeed) : List DiscoverySpec :=
  match seed.request.slots.discovery with
  | none => []
  | some artifact => [{ room := (roomAt seed 2).id, artifact }]

/-- Pure regeneration from the finalized seed.  Every structural choice is an
indexed draw; unused indices remain reserved by `DRAW_COUNT` for compatible
future enrichment. -/
def regenerate (seed : FinalizedMissionSeed) : Candidate :=
  let rooms := generatedRooms seed
  { layout := layoutOf seed
    pack := {
      schemaVersion := DeckGraph.CURRENT_SCHEMA_VERSION
      packId := ⟨packNumber seed⟩
      activation := seed.request.activation
      rooms
      hotspots := generatedHotspots seed
      entry := (roomAt seed 0).id
      extraction := (roomAt seed 6).id
      initialPhase := 0
      navigationFuel := 10
      validationFuel := 64
    }
    extractionPath := extractionPath seed
    encounters := [generatedEncounter seed]
    salvage := generatedSalvage seed
    discoveries := generatedDiscoveries seed
    dailyRunBudget := 3
    turnBudget := 10
    operationalSupplyBudget := 3 }

theorem regenerate_deterministic (seed : FinalizedMissionSeed)
    {first second : Candidate}
    (hfirst : regenerate seed = first) (hsecond : regenerate seed = second) :
    first = second := by
  rw [← hfirst, ← hsecond]

/-- Proof objects in `FinalizedMissionSeed` are irrelevant to generation; exact
request equality is sufficient for exact semantic regeneration. -/
theorem regeneration_depends_only_on_request
    {first second : FinalizedMissionSeed}
    (h : first.request = second.request) : regenerate first = regenerate second := by
  cases first with
  | mk firstRequest firstValid =>
      cases second with
      | mk secondRequest secondValid =>
          simp only at h
          subst secondRequest
          rfl

theorem regenerated_room_count (seed : FinalizedMissionSeed) :
    (regenerate seed).pack.rooms.length = 7 := by
  simp [regenerate, generatedRooms]

theorem regenerated_hotspot_count (seed : FinalizedMissionSeed) :
    (regenerate seed).pack.hotspots.length = 7 := by
  cases h : layoutOf seed <;> simp [regenerate, generatedHotspots, h]

theorem regenerated_extraction_path_count (seed : FinalizedMissionSeed) :
    (regenerate seed).extractionPath.length = 4 := by
  cases h : layoutOf seed <;>
    simp [regenerate, extractionPath, safeHotspotOffsets, h]

theorem regenerated_encounter_count (seed : FinalizedMissionSeed) :
    (regenerate seed).encounters.length = 1 := by
  rfl

theorem regenerated_encounters_fit_supply_budget (seed : FinalizedMissionSeed) :
    ∀ encounter ∈ (regenerate seed).encounters,
      encounter.supplyCost ≤ (regenerate seed).operationalSupplyBudget := by
  intro encounter hmember
  change encounter ∈ [generatedEncounter seed] at hmember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
  subst encounter
  change (generatedEncounter seed).supplyCost ≤ 3
  simp only [generatedEncounter]
  have hdraw := (drawBounded seed 4 3 (by decide)).isLt
  omega

theorem regenerated_encounters_have_positive_damage (seed : FinalizedMissionSeed) :
    ∀ encounter ∈ (regenerate seed).encounters, 0 < encounter.damage.val := by
  intro encounter hmember
  change encounter ∈ [generatedEncounter seed] at hmember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
  subst encounter
  simp [generatedEncounter]

theorem regenerated_salvage_ids_unique (seed : FinalizedMissionSeed) :
    ((regenerate seed).salvage.map SalvageSpec.id).Nodup := by
  change ((generatedSalvage seed).map SalvageSpec.id).Nodup
  unfold generatedSalvage
  cases seed.request.slots.rewardRelic <;> simp

/-! ## Validation by the existing graph and expedition semantics -/

def expeditionRaw (seed : FinalizedMissionSeed) (candidate : Candidate)
    (graphValid : DeckGraph.validateB candidate.pack = true) : RawConfig where
  graph := { pack := candidate.pack, validation := graphValid }
  policy := seed.request.policy
  day := seed.request.policy.mission.epoch
  officers := standardOfficers
  hazards := candidate.hazards
  salvage := candidate.salvage
  discoveries := candidate.discoveries
  dailyRunBudget := candidate.dailyRunBudget
  turnBudget := candidate.turnBudget
  operationalSupplyBudget := candidate.operationalSupplyBudget
  baseContribution := Contribution.zero

/-- A validated generation carries the existing expedition configuration itself;
there is no weaker parallel resource checker to drift from game semantics. -/
structure Generated (seed : FinalizedMissionSeed) where
  candidate : Candidate
  finalPosition : Position
  graphValid : DeckGraph.validateB candidate.pack = true
  configValid : DeckExpedition.configValidB
    (expeditionRaw seed candidate graphValid) = true
  extractionReplay : DeckGraph.replay candidate.pack candidate.pack.navigationFuel
    (DeckGraph.initialPosition candidate.pack) candidate.extractionPath = some finalPosition
  atExtraction : finalPosition.room = candidate.pack.extraction
  exactRegeneration : candidate = regenerate seed

def Generated.config {seed : FinalizedMissionSeed}
    (generated : Generated seed) : DeckExpedition.Config where
  raw := expeditionRaw seed generated.candidate generated.graphValid
  valid := generated.configValid

/-- Validate structure and resources before checking exact regeneration.  This
ordering means malformed graphs and impossible resource packs are refused by the
specific existing semantic checker, not merely because their bytes drift. -/
def validateCandidate? (seed : FinalizedMissionSeed)
    (candidate : Candidate) : Option (Generated seed) :=
  if hgraph : DeckGraph.validateB candidate.pack = true then
    let raw := expeditionRaw seed candidate hgraph
    if hconfig : DeckExpedition.configValidB raw = true then
      match hroute : DeckGraph.replay candidate.pack candidate.pack.navigationFuel
          (DeckGraph.initialPosition candidate.pack) candidate.extractionPath with
      | none => none
      | some finalPosition =>
          if hroom : finalPosition.room = candidate.pack.extraction then
            if hexact : candidate = regenerate seed then
              some {
                candidate
                finalPosition
                graphValid := hgraph
                configValid := hconfig
                extractionReplay := hroute
                atExtraction := hroom
                exactRegeneration := hexact
              }
            else none
          else none
    else none
  else none

def generate? (seed : FinalizedMissionSeed) : Option (Generated seed) :=
  validateCandidate? seed (regenerate seed)

structure DailyGeneration where
  seed : FinalizedMissionSeed
  generated : Generated seed

def generateFromDaily? (catalog : DailyMission.Catalog)
    (request : DailyMission.Request) (activation : ActivationIdentity)
    (policy : ActivityOutcome.Policy) (slots : MechanicSlots) :
    Option DailyGeneration := do
  let seed ← finalizeFromDaily? catalog request activation policy slots
  let generated ← generate? seed
  some { seed, generated }

theorem validateCandidate_deterministic (seed : FinalizedMissionSeed)
    (candidate : Candidate) {first second : Generated seed}
    (hfirst : validateCandidate? seed candidate = some first)
    (hsecond : validateCandidate? seed candidate = some second) : first = second := by
  rw [hfirst] at hsecond
  exact Option.some.inj hsecond

theorem validated_candidate_is_exact_regeneration {seed : FinalizedMissionSeed}
    (generated : Generated seed) : generated.candidate = regenerate seed :=
  generated.exactRegeneration

theorem validated_candidate_reaches_extraction {seed : FinalizedMissionSeed}
    (generated : Generated seed) :
    ∃ finalPosition,
      DeckGraph.replay generated.candidate.pack
        generated.candidate.pack.navigationFuel
        (DeckGraph.initialPosition generated.candidate.pack)
        generated.candidate.extractionPath = some finalPosition ∧
      finalPosition.room = generated.candidate.pack.extraction :=
  ⟨generated.finalPosition, generated.extractionReplay, generated.atExtraction⟩

theorem validated_candidate_has_bounded_turn_budget {seed : FinalizedMissionSeed}
    (generated : Generated seed) :
    generated.candidate.turnBudget ≤ DeckExpedition.MAX_TURNS :=
  (generated.config).turnBudget_bounded

theorem validated_candidate_has_seven_rooms {seed : FinalizedMissionSeed}
    (generated : Generated seed) : generated.candidate.pack.rooms.length = 7 := by
  rw [generated.exactRegeneration]
  exact regenerated_room_count seed

theorem validated_candidate_has_four_step_extraction {seed : FinalizedMissionSeed}
    (generated : Generated seed) : generated.candidate.extractionPath.length = 4 := by
  rw [generated.exactRegeneration]
  exact regenerated_extraction_path_count seed

theorem validated_candidate_encounters_fit_supply_budget
    {seed : FinalizedMissionSeed} (generated : Generated seed) :
    ∀ encounter ∈ generated.candidate.encounters,
      encounter.supplyCost ≤ generated.candidate.operationalSupplyBudget := by
  rw [generated.exactRegeneration]
  exact regenerated_encounters_fit_supply_budget seed

theorem validated_candidate_salvage_ids_unique {seed : FinalizedMissionSeed}
    (generated : Generated seed) :
    (generated.candidate.salvage.map SalvageSpec.id).Nodup := by
  rw [generated.exactRegeneration]
  exact regenerated_salvage_ids_unique seed

/-- Custody identity is inherited from the real expedition transition, not
restated by the generator. -/
theorem validated_candidate_preserves_custody {seed : FinalizedMissionSeed}
    (generated : Generated seed) (state : DeckExpedition.State)
    (action : DeckExpedition.Action)
    (result : DeckExpedition.StepResult generated.config)
    (h : DeckExpedition.step generated.config state action = some result) :
    result.state.salvage.map SalvageRecord.id = state.salvage.map SalvageRecord.id :=
  DeckExpedition.step_custody_conservation generated.config state action result h

/-! ## Executable portfolio and hostile packs -/

def digestFilled (value : Fin 256) : Digest32 where
  bytes := List.replicate 32 value
  length_eq := by simp

def fixtureActivation : ActivationIdentity := DeckGraph.fixtureActivation

def fixturePolicyWithSeed (value : Fin 256) : ActivityOutcome.Policy :=
  { DeckExpedition.fixturePolicy with
    mission := { DeckExpedition.fixtureMission with runSeed := digestFilled value } }

def fixtureCatalog : DailyMission.Catalog where
  federationId := fixtureActivation.federationId
  contentEpoch := fixtureActivation.contentEpoch
  contentRoot := fixtureActivation.contentRoot
  activationDigest := fixtureActivation.activationDigest
  contentSession := fixtureActivation.contentSession
  catalogDigest := DeckGraph.zeroDigest
  opensAt := ⟨1⟩
  closesAt := ⟨100⟩
  missions := [DeckExpedition.fixtureMissionId]
  window_ordered := by decide
  missions_nonempty := by decide
  missions_nodup := by decide

def fixtureRequest : DailyMission.Request where
  federationId := fixtureActivation.federationId
  contentEpoch := fixtureActivation.contentEpoch
  contentRoot := fixtureActivation.contentRoot
  activationDigest := fixtureActivation.activationDigest
  contentSession := fixtureActivation.contentSession
  catalogDigest := fixtureCatalog.catalogDigest
  finalizedEpoch := ⟨7⟩

def fixtureGeneration? (value : Fin 256) : Option DailyGeneration :=
  generateFromDaily? fixtureCatalog fixtureRequest fixtureActivation
    (fixturePolicyWithSeed value)
    { rewardRelic := DeckExpedition.fixtureRelic
      discovery := DeckExpedition.fixtureArtifact }

theorem fixture_generation_succeeds : (fixtureGeneration? 0).isSome = true := by
  native_decide

def generatedLayout? (value : Fin 256) : Option Layout :=
  (fixtureGeneration? value).map fun generation => generation.generated.candidate.layout

/-- Three committed seeds exercise all bounded topology templates. -/
theorem fixture_seed_portfolio_has_three_layouts :
    (generatedLayout? 0).isSome = true ∧
    (generatedLayout? 1).isSome = true ∧
    (generatedLayout? 2).isSome = true ∧
    generatedLayout? 0 ≠ generatedLayout? 1 ∧
    generatedLayout? 0 ≠ generatedLayout? 2 ∧
    generatedLayout? 1 ≠ generatedLayout? 2 := by
  native_decide

def fixtureRunAcceptsB : Bool :=
  match fixtureGeneration? 0 with
  | none => false
  | some daily =>
      let generated := daily.generated
      let cfg := generated.config
      let player := DeckGraph.zeroDigest
      let key : ExpeditionKey := {
        pack := cfg.packKey
        playerKey := player
        day := cfg.raw.day
        counter := 1
      }
      let actions : List Action :=
        [.begin key standardParty] ++
          generated.candidate.extractionPath.map Action.traverse ++ [.extract]
      match DeckExpedition.replay cfg actions.length
          (DeckExpedition.initialState cfg player) actions with
      | some (state, [receipt]) =>
          decide (receipt.finalPosition.room = generated.candidate.pack.extraction) &&
          decide (receipt.recovered = ∅) &&
          decide (state.salvage.map SalvageRecord.id =
            generated.candidate.salvage.map SalvageSpec.id) &&
          DeckExpedition.validStateB cfg state
      | _ => false

/-- The generator's output is immediately playable by the existing persistent
expedition machine; this is not a parallel toy executor. -/
theorem fixture_generated_expedition_extracts : fixtureRunAcceptsB = true := by
  native_decide

def withFinalHotspotRemoved (candidate : Candidate) : Candidate :=
  { candidate with
    pack := { candidate.pack with hotspots := candidate.pack.hotspots.dropLast } }

def withImpossibleSupplyBudget (candidate : Candidate) : Candidate :=
  { candidate with operationalSupplyBudget := 0 }

def withDuplicateSalvage (candidate : Candidate) : Candidate :=
  match candidate.salvage with
  | [] => candidate
  | item :: _ => { candidate with salvage := item :: candidate.salvage }

def withDifferentPackId (candidate : Candidate) : Candidate :=
  { candidate with pack := { candidate.pack with packId := ⟨candidate.pack.packId.value + 1⟩ } }

def hostileRefusalsB : Bool :=
  match finalizeFromDaily? fixtureCatalog fixtureRequest fixtureActivation
      (fixturePolicyWithSeed 0)
      { rewardRelic := DeckExpedition.fixtureRelic
        discovery := DeckExpedition.fixtureArtifact } with
  | none => false
  | some seed =>
      let candidate := regenerate seed
      (validateCandidate? seed (withFinalHotspotRemoved candidate)).isNone &&
      (validateCandidate? seed (withImpossibleSupplyBudget candidate)).isNone &&
      (validateCandidate? seed (withDuplicateSalvage candidate)).isNone &&
      (validateCandidate? seed (withDifferentPackId candidate)).isNone

/-- Unreachable topology, impossible encounter budget, duplicate custody objects,
and a structurally valid but non-regenerated pack all refuse. -/
theorem fixture_malformed_and_impossible_packs_refuse : hostileRefusalsB = true := by
  native_decide

def wrongMissionPolicy : ActivityOutcome.Policy :=
  { fixturePolicyWithSeed 0 with
    mission := {
      (fixturePolicyWithSeed 0).mission with
      missionId := ⟨99_999⟩
      artifact := { (fixturePolicyWithSeed 0).mission.artifact with missionId := ⟨99_999⟩ }
      artifact_matches := rfl
    } }

theorem fixture_wrong_selected_mission_refuses :
    (generateFromDaily? fixtureCatalog fixtureRequest fixtureActivation wrongMissionPolicy
      { rewardRelic := none, discovery := none }).isNone = true := by
  native_decide

#assert_axioms drawBounded_lt
#assert_axioms drawBounded_deterministic
#assert_axioms FinalizedMissionSeed.binds_selected_mission
#assert_axioms FinalizedMissionSeed.binds_finalized_activation
#assert_axioms regenerate_deterministic
#assert_axioms regeneration_depends_only_on_request
#assert_axioms regenerated_room_count
#assert_axioms regenerated_hotspot_count
#assert_axioms regenerated_extraction_path_count
#assert_axioms regenerated_encounter_count
#assert_axioms regenerated_encounters_fit_supply_budget
#assert_axioms regenerated_encounters_have_positive_damage
#assert_axioms regenerated_salvage_ids_unique
#assert_axioms validateCandidate_deterministic
#assert_axioms validated_candidate_is_exact_regeneration
#assert_axioms validated_candidate_reaches_extraction
#assert_axioms validated_candidate_has_bounded_turn_budget
#assert_axioms validated_candidate_has_seven_rooms
#assert_axioms validated_candidate_has_four_step_extraction
#assert_axioms validated_candidate_encounters_fit_supply_budget
#assert_axioms validated_candidate_salvage_ids_unique
#assert_axioms validated_candidate_preserves_custody

#assert_compiled fixture_generation_succeeds
#assert_compiled fixture_seed_portfolio_has_three_layouts
#assert_compiled fixture_generated_expedition_extracts
#assert_compiled fixture_malformed_and_impossible_packs_refuse
#assert_compiled fixture_wrong_selected_mission_refuses

end Dregg2.Games.PathOfAngels.DeckGenerator
