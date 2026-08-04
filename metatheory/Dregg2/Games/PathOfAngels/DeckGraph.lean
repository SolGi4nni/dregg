/-
# DeckGraph — finite signed-content-ready navigation for the Khovokhi

This module validates the semantic payload of a deck pack: finite rooms and
hotspots, unique identifiers, resolved directed exits, explicit non-Euclidean
modifiers, bounded content, and a fuel-bounded executable extraction search.

It deliberately does NOT verify signatures or infer authenticity from digest
fields.  `ActivationIdentity` is the identity an external verifier must bind to
canonical pack bytes.  `ExternalActivationEvidence` is opaque here and has no
constructor or inhabitant in this module.  It represents a trusted boundary
input only after the pinned signer, signature, rollback counter, canonical
encoding, and exact bytes of the whole pack have been checked.
-/
import Dregg2.Games.PathOfAngels.Core

namespace Dregg2.Games.PathOfAngels.DeckGraph

open Dregg2.Games.PathOfAngels

abbrev CURRENT_SCHEMA_VERSION : Nat := 1
abbrev MAX_ROOMS : Nat := 128
abbrev MAX_HOTSPOTS : Nat := 512
abbrev MAX_NAVIGATION_FUEL : Nat := 64
abbrev MAX_VALIDATION_FUEL : Nat := 4096

structure RoomId where
  value : Nat
deriving Repr, DecidableEq

structure HotspotId where
  value : Nat
deriving Repr, DecidableEq

structure PackId where
  value : Nat
deriving Repr, DecidableEq

inductive Axis where
  | horizontal
  | vertical
deriving Repr, DecidableEq

/-- Every hotspot is directed.  `oneWay` records an ordinary intentionally
one-way passage; a bidirectional door is authored as two distinct hotspots.
`wrap` and `mirror` are finite renderer metadata: this semantic validator stores
their intended axis but currently enforces only their directed source and
destination.  A renderer may consume those tags for spatial presentation.
`phase` is semantic here: it is traversable only in its required finite phase
before moving to the declared next phase. -/
inductive Modifier where
  | oneWay
  | wrap (axis : Axis)
  | mirror (axis : Axis)
  | phase (required next : Fin 4)
deriving Repr, DecidableEq

structure Room where
  id : RoomId
deriving Repr, DecidableEq

structure Hotspot where
  id : HotspotId
  source : RoomId
  destination : RoomId
  modifier : Modifier
deriving Repr, DecidableEq

/-- Identity fields carried by the externally signed activation statement.
Their mere presence or equality does not prove a signature. -/
structure ActivationIdentity where
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  signerKeyId : Digest32
  activationCounter : Nat
deriving DecidableEq

/-- Raw signed-content payload.  It contains no proof fields so malformed packs
can be decoded and refused by the executable validator. -/
structure Pack where
  schemaVersion : Nat
  packId : PackId
  activation : ActivationIdentity
  rooms : List Room
  hotspots : List Hotspot
  entry : RoomId
  extraction : RoomId
  initialPhase : Fin 4
  navigationFuel : Nat
  validationFuel : Nat
deriving DecidableEq

def roomIds (pack : Pack) : List RoomId :=
  pack.rooms.map Room.id

def hotspotIds (pack : Pack) : List HotspotId :=
  pack.hotspots.map Hotspot.id

def hasRoom (pack : Pack) (room : RoomId) : Bool :=
  decide (room ∈ roomIds pack)

/-- Navigation state contains only state consumed by this validator.  Wrap and
mirror presentation state deliberately does not appear here; phase does. -/
structure Position where
  room : RoomId
  phase : Fin 4
deriving Repr, DecidableEq

def initialPosition (pack : Pack) : Position :=
  {
    room := pack.entry
    phase := pack.initialPhase
  }

/-- Apply one exact directed hotspot.  Phase mismatch and wrong-origin use
refuse rather than becoming accepted no-ops. -/
def traverseHotspot (position : Position) (hotspot : Hotspot) : Option Position :=
  if hotspot.source != position.room then
    none
  else
    match hotspot.modifier with
    | .oneWay => some { position with room := hotspot.destination }
    -- Renderer metadata is retained in the pack but is not interpreted here.
    | .wrap _ => some { position with room := hotspot.destination }
    | .mirror _ => some { position with room := hotspot.destination }
    | .phase required next =>
        if position.phase = required then
          some { position with room := hotspot.destination, phase := next }
        else
          none

def hotspotById? : List Hotspot → HotspotId → Option Hotspot
  | [], _ => none
  | hotspot :: hotspots, id =>
      if hotspot.id = id then some hotspot else hotspotById? hotspots id

def navigateStep (pack : Pack) (position : Position)
    (hotspotId : HotspotId) : Option Position := do
  let hotspot ← hotspotById? pack.hotspots hotspotId
  traverseHotspot position hotspot

/-- Fuel bounds accepted moves independently of the content's structure. -/
def replay (pack : Pack) : Nat → Position → List HotspotId → Option Position
  | _, position, [] => some position
  | 0, _, _ :: _ => none
  | fuel + 1, position, hotspotId :: hotspotIds => do
      let next ← navigateStep pack position hotspotId
      replay pack fuel next hotspotIds

theorem navigateStep_deterministic (pack : Pack) (position : Position)
    (hotspotId : HotspotId) {first second : Position}
    (hfirst : navigateStep pack position hotspotId = some first)
    (hsecond : navigateStep pack position hotspotId = some second) :
    first = second := by
  rw [hfirst] at hsecond
  exact Option.some.inj hsecond

theorem replay_deterministic (pack : Pack) (fuel : Nat) (position : Position)
    (path : List HotspotId) {first second : Position}
    (hfirst : replay pack fuel position path = some first)
    (hsecond : replay pack fuel position path = some second) :
    first = second := by
  rw [hfirst] at hsecond
  exact Option.some.inj hsecond

theorem replay_some_length_le_fuel (pack : Pack) (fuel : Nat)
    (position : Position) (path : List HotspotId) {final : Position}
    (h : replay pack fuel position path = some final) :
    path.length ≤ fuel := by
  induction fuel generalizing position path final with
  | zero =>
      cases path with
      | nil => simp
      | cons hotspotId hotspots => simp [replay] at h
  | succ fuel ih =>
      cases path with
      | nil => simp
      | cons hotspotId hotspots =>
          cases hstep : navigateStep pack position hotspotId with
          | none => simp [replay, hstep] at h
          | some next =>
              have htail : replay pack fuel next hotspots = some final := by
                simpa [replay, hstep] using h
              simpa using Nat.succ_le_succ (ih next hotspots htail)

theorem overfuel_path_refused (pack : Pack) (fuel : Nat)
    (position : Position) (path : List HotspotId)
    (h : fuel < path.length) : replay pack fuel position path = none := by
  cases hresult : replay pack fuel position path with
  | none => rfl
  | some final =>
      have hbound := replay_some_length_le_fuel pack fuel position path hresult
      omega

/-! ## Fuel-bounded executable extraction search -/

structure SearchNode where
  position : Position
  reversedPath : List HotspotId
deriving DecidableEq

def expandNode (pack : Pack) (node : SearchNode) : List SearchNode :=
  if node.reversedPath.length < pack.navigationFuel then
    pack.hotspots.filterMap (fun hotspot =>
      match traverseHotspot node.position hotspot with
      | none => none
      | some position => some {
          position
          reversedPath := hotspot.id :: node.reversedPath
        })
  else
    []

def freshChildren (visited : Finset Position)
    (children : List SearchNode) : List SearchNode :=
  children.filter (fun child => decide (child.position ∉ visited))

def rememberChildren (visited : Finset Position)
    (children : List SearchNode) : Finset Position :=
  children.foldl (fun known child => insert child.position known) visited

structure SearchResult where
  path : List HotspotId
  /-- Exact number of queue nodes popped before this successful result. -/
  poppedNodes : Nat
deriving DecidableEq

/-- Breadth-first queue search.  Zero fuel pops no node.  Every nonempty-queue
successor clause pops exactly its head and consumes exactly one fuel unit; a
recursive success increments `poppedNodes` for that pop.  Thus validation fuel
bounds nodes examined, rather than recursion depth with a free zero-fuel check.
The returned candidate is re-run below; search output is never trusted directly. -/
def searchPath (pack : Pack) : Nat → List SearchNode →
    Finset Position → Option SearchResult
  | 0, _, _ => none
  | _ + 1, [], _ => none
  | fuel + 1, node :: queue, visited =>
      if node.position.room = pack.extraction then
        some { path := node.reversedPath.reverse, poppedNodes := 1 }
      else
        let children := freshChildren visited (expandNode pack node)
        let visited' := rememberChildren visited children
        match searchPath pack fuel (queue ++ children) visited' with
        | none => none
        | some result =>
            some { result with poppedNodes := result.poppedNodes + 1 }

/-- An exhausted budget examines no queue node. -/
theorem searchPath_zero_fuel (pack : Pack) (queue : List SearchNode)
    (visited : Finset Position) : searchPath pack 0 queue visited = none := by
  rfl

/-- `poppedNodes` is a real resource counter: a successful search cannot report
more popped queue nodes than the fuel supplied to it. -/
theorem searchPath_success_popped_le_fuel (pack : Pack) (fuel : Nat)
    (queue : List SearchNode) (visited : Finset Position)
    {result : SearchResult}
    (h : searchPath pack fuel queue visited = some result) :
    result.poppedNodes ≤ fuel := by
  induction fuel generalizing queue visited result with
  | zero => simp [searchPath] at h
  | succ fuel ih =>
      cases queue with
      | nil => simp [searchPath] at h
      | cons node queue =>
          by_cases hextraction : node.position.room = pack.extraction
          · simp [searchPath, hextraction] at h
            subst result
            simp
          · simp only [searchPath, hextraction, ↓reduceIte] at h
            cases hrecursive : searchPath pack fuel
                (queue ++ freshChildren visited (expandNode pack node))
                (rememberChildren visited
                  (freshChildren visited (expandNode pack node))) with
            | none => simp [hrecursive] at h
            | some recursiveResult =>
                simp [hrecursive] at h
                subst result
                have hbound := ih _ _ hrecursive
                change recursiveResult.poppedNodes + 1 ≤ fuel + 1
                omega

def candidateExtractionSearch? (pack : Pack) : Option SearchResult :=
  let initial := initialPosition pack
  searchPath pack pack.validationFuel
    [{ position := initial, reversedPath := [] }]
    {initial}

theorem candidateExtractionSearch_popped_le_validationFuel (pack : Pack)
    {result : SearchResult}
    (h : candidateExtractionSearch? pack = some result) :
    result.poppedNodes ≤ pack.validationFuel := by
  exact searchPath_success_popped_le_fuel pack pack.validationFuel
    [{ position := initialPosition pack, reversedPath := [] }]
    {initialPosition pack} h

/-- The executable search candidate is accepted only after exact replay under the
declared navigation fuel reaches the declared extraction room. -/
def reachableExtractionB (pack : Pack) : Bool :=
  match candidateExtractionSearch? pack with
  | none => false
  | some result =>
      match replay pack pack.navigationFuel (initialPosition pack) result.path with
      | none => false
      | some final => decide (final.room = pack.extraction)

def ReachableExtraction (pack : Pack) : Prop :=
  ∃ path final,
    path.length ≤ pack.navigationFuel ∧
    replay pack pack.navigationFuel (initialPosition pack) path = some final ∧
    final.room = pack.extraction

theorem reachableExtractionB_sound (pack : Pack)
    (h : reachableExtractionB pack = true) : ReachableExtraction pack := by
  unfold reachableExtractionB at h
  split at h
  · contradiction
  · rename_i path hpath
    split at h
    · contradiction
    · rename_i final hreplay
      have hextraction : final.room = pack.extraction := by simpa using h
      exact ⟨path.path, final,
        replay_some_length_le_fuel pack pack.navigationFuel
          (initialPosition pack) path.path hreplay,
        hreplay, hextraction⟩

theorem reachableExtractionB_implies_bounded_popped_nodes (pack : Pack)
    (h : reachableExtractionB pack = true) :
    ∃ result, candidateExtractionSearch? pack = some result ∧
      result.poppedNodes ≤ pack.validationFuel := by
  unfold reachableExtractionB at h
  split at h
  · contradiction
  · rename_i result hresult
    exact ⟨result, hresult,
      candidateExtractionSearch_popped_le_validationFuel pack hresult⟩

/-! ## Structural validation and external activation boundary -/

structure StructurallyValid (pack : Pack) : Prop where
  schema_current : pack.schemaVersion = CURRENT_SCHEMA_VERSION
  rooms_nonempty : pack.rooms ≠ []
  rooms_bounded : pack.rooms.length ≤ MAX_ROOMS
  hotspots_bounded : pack.hotspots.length ≤ MAX_HOTSPOTS
  navigation_fuel_positive : 0 < pack.navigationFuel
  navigation_fuel_bounded : pack.navigationFuel ≤ MAX_NAVIGATION_FUEL
  validation_fuel_positive : 0 < pack.validationFuel
  validation_fuel_bounded : pack.validationFuel ≤ MAX_VALIDATION_FUEL
  room_ids_unique : (roomIds pack).Nodup
  hotspot_ids_unique : (hotspotIds pack).Nodup
  entry_resolved : pack.entry ∈ roomIds pack
  extraction_resolved : pack.extraction ∈ roomIds pack
  exits_resolved : ∀ hotspot ∈ pack.hotspots,
    hotspot.source ∈ roomIds pack ∧ hotspot.destination ∈ roomIds pack

def hotspotResolvedB (pack : Pack) (hotspot : Hotspot) : Bool :=
  hasRoom pack hotspot.source && hasRoom pack hotspot.destination

/-- The structural checker is intentionally expressed as finite Boolean data.
Its soundness theorem below reconstructs the proposition-level contract. -/
def structuralValidB (pack : Pack) : Bool :=
  decide (pack.schemaVersion = CURRENT_SCHEMA_VERSION) && (
  decide (pack.rooms ≠ []) && (
  decide (pack.rooms.length ≤ MAX_ROOMS) && (
  decide (pack.hotspots.length ≤ MAX_HOTSPOTS) && (
  decide (0 < pack.navigationFuel) && (
  decide (pack.navigationFuel ≤ MAX_NAVIGATION_FUEL) && (
  decide (0 < pack.validationFuel) && (
  decide (pack.validationFuel ≤ MAX_VALIDATION_FUEL) && (
  decide ((roomIds pack).Nodup) && (
  decide ((hotspotIds pack).Nodup) && (
  decide (pack.entry ∈ roomIds pack) && (
  decide (pack.extraction ∈ roomIds pack) &&
  pack.hotspots.all (hotspotResolvedB pack))))))))))))

theorem structuralValidB_sound (pack : Pack)
    (h : structuralValidB pack = true) : StructurallyValid pack := by
  simp only [structuralValidB] at h
  obtain ⟨hschemaB, h⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨hnonemptyB, h⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨hroomsB, h⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨hhotspotsB, h⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨hnavposB, h⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨hnavB, h⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨hvalidationposB, h⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨hvalidationB, h⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨hroomidsB, h⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨hhotspotidsB, h⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨hentryB, h⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨hextractionB, hexits⟩ := Eq.mp (Bool.and_eq_true _ _) h
  have hschema := of_decide_eq_true hschemaB
  have hnonempty := of_decide_eq_true hnonemptyB
  have hrooms := of_decide_eq_true hroomsB
  have hhotspots := of_decide_eq_true hhotspotsB
  have hnavpos := of_decide_eq_true hnavposB
  have hnav := of_decide_eq_true hnavB
  have hvalidationpos := of_decide_eq_true hvalidationposB
  have hvalidation := of_decide_eq_true hvalidationB
  have hroomids := of_decide_eq_true hroomidsB
  have hhotspotids := of_decide_eq_true hhotspotidsB
  have hentry := of_decide_eq_true hentryB
  have hextraction := of_decide_eq_true hextractionB
  refine {
    schema_current := hschema
    rooms_nonempty := hnonempty
    rooms_bounded := hrooms
    hotspots_bounded := hhotspots
    navigation_fuel_positive := hnavpos
    navigation_fuel_bounded := hnav
    validation_fuel_positive := hvalidationpos
    validation_fuel_bounded := hvalidation
    room_ids_unique := hroomids
    hotspot_ids_unique := hhotspotids
    entry_resolved := hentry
    extraction_resolved := hextraction
    exits_resolved := ?_
  }
  intro hotspot hmember
  have hresolved := (List.all_eq_true.mp hexits) hotspot hmember
  have hpair := Eq.mp (Bool.and_eq_true _ _) hresolved
  exact ⟨(by simpa [hotspotResolvedB, hasRoom] using hpair.1),
    (by simpa [hotspotResolvedB, hasRoom] using hpair.2)⟩

/-- Complete executable pack validation.  It proves structure and one bounded
extraction witness; it does not authenticate `pack.activation`. -/
def validateB (pack : Pack) : Bool :=
  structuralValidB pack && reachableExtractionB pack

theorem validateB_eq_true_iff (pack : Pack) :
    validateB pack = true ↔
      structuralValidB pack = true ∧ reachableExtractionB pack = true := by
  simp [validateB]

theorem validation_implies_room_ids_unique (pack : Pack)
    (h : validateB pack = true) : (roomIds pack).Nodup :=
  (structuralValidB_sound pack ((validateB_eq_true_iff pack).mp h).1).room_ids_unique

theorem validation_implies_hotspot_ids_unique (pack : Pack)
    (h : validateB pack = true) : (hotspotIds pack).Nodup :=
  (structuralValidB_sound pack ((validateB_eq_true_iff pack).mp h).1).hotspot_ids_unique

theorem validation_implies_resolved_entry_and_extraction (pack : Pack)
    (h : validateB pack = true) :
    pack.entry ∈ roomIds pack ∧ pack.extraction ∈ roomIds pack := by
  have valid := structuralValidB_sound pack ((validateB_eq_true_iff pack).mp h).1
  exact ⟨valid.entry_resolved, valid.extraction_resolved⟩

theorem validation_implies_all_exits_resolved (pack : Pack)
    (h : validateB pack = true) :
    ∀ hotspot ∈ pack.hotspots,
      hotspot.source ∈ roomIds pack ∧ hotspot.destination ∈ roomIds pack :=
  (structuralValidB_sound pack ((validateB_eq_true_iff pack).mp h).1).exits_resolved

theorem validation_implies_content_bounds (pack : Pack)
    (h : validateB pack = true) :
    pack.rooms.length ≤ MAX_ROOMS ∧
    pack.hotspots.length ≤ MAX_HOTSPOTS ∧
    pack.navigationFuel ≤ MAX_NAVIGATION_FUEL ∧
    pack.validationFuel ≤ MAX_VALIDATION_FUEL := by
  have valid := structuralValidB_sound pack ((validateB_eq_true_iff pack).mp h).1
  exact ⟨valid.rooms_bounded, valid.hotspots_bounded,
    valid.navigation_fuel_bounded, valid.validation_fuel_bounded⟩

theorem validation_implies_reachable_extraction (pack : Pack)
    (h : validateB pack = true) : ReachableExtraction pack :=
  reachableExtractionB_sound pack ((validateB_eq_true_iff pack).mp h).2

/-- The result pure code can construct after running the complete executable
semantic validator.  This makes no activation or authentication claim. -/
structure ValidatedPack where
  pack : Pack
  validation : validateB pack = true

def validatePack? (pack : Pack) : Option ValidatedPack :=
  if h : validateB pack = true then
    some { pack, validation := h }
  else
    none

theorem validatePack_isSome_iff (pack : Pack) :
    (validatePack? pack).isSome = true ↔ validateB pack = true := by
  by_cases h : validateB pack = true <;> simp [validatePack?, h]

theorem validation_implies_bounded_popped_nodes (pack : Pack)
    (h : validateB pack = true) :
    ∃ result, candidateExtractionSearch? pack = some result ∧
      result.poppedNodes ≤ pack.validationFuel :=
  reachableExtractionB_implies_bounded_popped_nodes pack
    ((validateB_eq_true_iff pack).mp h).2

/-- Trusted activation evidence is indexed by the exact whole pack, not merely
its claimed identity fields.  This pure module supplies no constructor or
inhabitant; runtime activation must cross a separate signature-verifying trust
boundary that binds canonical bytes to this exact `Pack`. -/
opaque ExternalActivationEvidence (pack : Pack) : Type

structure ActivatedPack where
  validated : ValidatedPack
  externalActivation : ExternalActivationEvidence validated.pack

/-! ## Generic malformed-pack refusal theorems -/

theorem validateB_false_of_not_structural (pack : Pack)
    (h : ¬ StructurallyValid pack) : validateB pack = false := by
  cases hstructural : structuralValidB pack with
  | false => simp [validateB, hstructural]
  | true => exact False.elim (h (structuralValidB_sound pack hstructural))

theorem malformed_schema_refused (pack : Pack)
    (h : pack.schemaVersion ≠ CURRENT_SCHEMA_VERSION) :
    validateB pack = false := by
  apply validateB_false_of_not_structural
  intro valid
  exact h valid.schema_current

theorem empty_rooms_refused (pack : Pack) (h : pack.rooms = []) :
    validateB pack = false := by
  apply validateB_false_of_not_structural
  intro valid
  exact valid.rooms_nonempty h

theorem duplicate_room_ids_refused (pack : Pack)
    (h : ¬ (roomIds pack).Nodup) : validateB pack = false := by
  apply validateB_false_of_not_structural
  intro valid
  exact h valid.room_ids_unique

theorem duplicate_hotspot_ids_refused (pack : Pack)
    (h : ¬ (hotspotIds pack).Nodup) : validateB pack = false := by
  apply validateB_false_of_not_structural
  intro valid
  exact h valid.hotspot_ids_unique

theorem dangling_exit_refused (pack : Pack) (hotspot : Hotspot)
    (hmember : hotspot ∈ pack.hotspots)
    (hdangling : hotspot.source ∉ roomIds pack ∨
      hotspot.destination ∉ roomIds pack) :
    validateB pack = false := by
  apply validateB_false_of_not_structural
  intro valid
  have hresolved := valid.exits_resolved hotspot hmember
  exact hdangling.elim (fun h => h hresolved.1) (fun h => h hresolved.2)

theorem oversized_rooms_refused (pack : Pack)
    (h : MAX_ROOMS < pack.rooms.length) : validateB pack = false := by
  apply validateB_false_of_not_structural
  intro valid
  exact (Nat.not_lt_of_ge valid.rooms_bounded) h

theorem oversized_hotspots_refused (pack : Pack)
    (h : MAX_HOTSPOTS < pack.hotspots.length) : validateB pack = false := by
  apply validateB_false_of_not_structural
  intro valid
  exact (Nat.not_lt_of_ge valid.hotspots_bounded) h

theorem oversized_navigation_fuel_refused (pack : Pack)
    (h : MAX_NAVIGATION_FUEL < pack.navigationFuel) : validateB pack = false := by
  apply validateB_false_of_not_structural
  intro valid
  exact (Nat.not_lt_of_ge valid.navigation_fuel_bounded) h

theorem oversized_validation_fuel_refused (pack : Pack)
    (h : MAX_VALIDATION_FUEL < pack.validationFuel) : validateB pack = false := by
  apply validateB_false_of_not_structural
  intro valid
  exact (Nat.not_lt_of_ge valid.validation_fuel_bounded) h

theorem bounded_extraction_search_failure_refused (pack : Pack)
    (h : reachableExtractionB pack = false) : validateB pack = false := by
  simp [validateB, h]

/-! ## Named executable fixtures -/

def zeroDigest : Digest32 where
  bytes := List.replicate 32 0
  length_eq := by simp

def fixtureActivation : ActivationIdentity := {
  federationId := zeroDigest
  contentRoot := zeroDigest
  activationDigest := zeroDigest
  contentSession := zeroDigest
  contentEpoch := ⟨1⟩
  signerKeyId := zeroDigest
  activationCounter := 1
}

def fixtureRoomA : Room := { id := ⟨1⟩ }
def fixtureRoomB : Room := { id := ⟨2⟩ }
def fixtureRoomC : Room := { id := ⟨3⟩ }
def fixtureRoomD : Room := { id := ⟨4⟩ }
def fixtureExtraction : Room := { id := ⟨5⟩ }

def fixtureOneWay : Hotspot :=
  { id := ⟨10⟩, source := fixtureRoomA.id, destination := fixtureRoomB.id,
    modifier := .oneWay }

def fixtureWrap : Hotspot :=
  { id := ⟨11⟩, source := fixtureRoomB.id, destination := fixtureRoomC.id,
    modifier := .wrap .horizontal }

def fixtureMirror : Hotspot :=
  { id := ⟨12⟩, source := fixtureRoomC.id, destination := fixtureRoomD.id,
    modifier := .mirror .vertical }

def fixturePhase : Hotspot :=
  { id := ⟨13⟩, source := fixtureRoomD.id, destination := fixtureExtraction.id,
    modifier := .phase 0 1 }

def fixturePack : Pack := {
  schemaVersion := CURRENT_SCHEMA_VERSION
  packId := ⟨77⟩
  activation := fixtureActivation
  rooms := [fixtureRoomA, fixtureRoomB, fixtureRoomC, fixtureRoomD, fixtureExtraction]
  hotspots := [fixtureOneWay, fixtureWrap, fixtureMirror, fixturePhase]
  entry := fixtureRoomA.id
  extraction := fixtureExtraction.id
  initialPhase := 0
  navigationFuel := 4
  validationFuel := 16
}

def fixturePath : List HotspotId :=
  [fixtureOneWay.id, fixtureWrap.id, fixtureMirror.id, fixturePhase.id]

def fixtureFinalPosition : Position := {
  room := fixtureExtraction.id
  phase := 1
}

/-- The path traverses both renderer tags and the semantic phase edge.  This
theorem intentionally asserts no wrap/mirror rendering effect. -/
theorem fixture_path_traverses_all_modifier_tags :
    replay fixturePack fixturePack.navigationFuel
      (initialPosition fixturePack) fixturePath = some fixtureFinalPosition := by
  decide

theorem fixture_pack_validates : validateB fixturePack = true := by
  decide

def fixtureSearchResult : SearchResult := {
  path := fixturePath
  poppedNodes := 5
}

theorem fixture_search_reports_exact_popped_nodes :
    candidateExtractionSearch? fixturePack = some fixtureSearchResult := by
  decide

/-- Four edges require five queue pops: entry, B, C, D, then extraction. -/
def fixtureFourPopBudgetPack : Pack :=
  { fixturePack with validationFuel := 4 }

theorem fixture_four_pop_budget_cannot_check_fifth_node :
    candidateExtractionSearch? fixtureFourPopBudgetPack = none ∧
      validateB fixtureFourPopBudgetPack = false := by
  decide

def duplicateRoomPack : Pack :=
  { fixturePack with rooms := fixtureRoomA :: fixturePack.rooms }

theorem fixture_duplicate_room_pack_refused :
    validateB duplicateRoomPack = false := by
  decide

def danglingHotspot : Hotspot :=
  { fixturePhase with id := ⟨99⟩, destination := ⟨999⟩ }

def danglingPack : Pack :=
  { fixturePack with hotspots := fixturePack.hotspots ++ [danglingHotspot] }

theorem fixture_dangling_pack_refused : validateB danglingPack = false := by
  decide

def boundedSearchFailurePack : Pack :=
  { fixturePack with hotspots :=
      [fixtureOneWay, fixtureWrap, fixtureMirror] }

theorem fixture_bounded_search_failure_refused :
    validateB boundedSearchFailurePack = false := by
  decide

def oversizedPack : Pack :=
  { fixturePack with rooms := List.replicate (MAX_ROOMS + 1) fixtureRoomA }

theorem fixture_oversized_pack_refused : validateB oversizedPack = false := by
  apply oversized_rooms_refused
  simp [oversizedPack]

#assert_axioms navigateStep_deterministic
#assert_axioms replay_deterministic
#assert_axioms replay_some_length_le_fuel
#assert_axioms overfuel_path_refused
#assert_axioms searchPath_zero_fuel
#assert_axioms searchPath_success_popped_le_fuel
#assert_axioms candidateExtractionSearch_popped_le_validationFuel
#assert_axioms reachableExtractionB_sound
#assert_axioms reachableExtractionB_implies_bounded_popped_nodes
#assert_axioms structuralValidB_sound
#assert_axioms validateB_eq_true_iff
#assert_axioms validation_implies_room_ids_unique
#assert_axioms validation_implies_hotspot_ids_unique
#assert_axioms validation_implies_resolved_entry_and_extraction
#assert_axioms validation_implies_all_exits_resolved
#assert_axioms validation_implies_content_bounds
#assert_axioms validation_implies_reachable_extraction
#assert_axioms validatePack_isSome_iff
#assert_axioms validation_implies_bounded_popped_nodes
#assert_axioms validateB_false_of_not_structural
#assert_axioms malformed_schema_refused
#assert_axioms empty_rooms_refused
#assert_axioms duplicate_room_ids_refused
#assert_axioms duplicate_hotspot_ids_refused
#assert_axioms dangling_exit_refused
#assert_axioms oversized_rooms_refused
#assert_axioms oversized_hotspots_refused
#assert_axioms oversized_navigation_fuel_refused
#assert_axioms oversized_validation_fuel_refused
#assert_axioms bounded_extraction_search_failure_refused
#assert_axioms fixture_path_traverses_all_modifier_tags
#assert_axioms fixture_pack_validates
#assert_axioms fixture_search_reports_exact_popped_nodes
#assert_axioms fixture_four_pop_budget_cannot_check_fifth_node
#assert_axioms fixture_duplicate_room_pack_refused
#assert_axioms fixture_dangling_pack_refused
#assert_axioms fixture_bounded_search_failure_refused
#assert_axioms fixture_oversized_pack_refused

end Dregg2.Games.PathOfAngels.DeckGraph
