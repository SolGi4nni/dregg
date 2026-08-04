/-
# Salvage Crate — a mundane daily ritual on a protocol-serious foundation

Once per finalized period, an eligible crew account may open the crate beside the
Khovokhi reclamation desk.  Most contents are deliberately ordinary: packing
foam, maintenance stickers, account-bound cosmetics, or a small communal salvage
credit.  There is no streak, missed-day debt, token payout, tradeable prize, or
client clock in this state machine.

The curator authors a finite weighted table and a finite, strictly ordered beacon
schedule.  The exact table, content seed, finalized beacon, player, period, and
global player counter are retained in the result identity.  Selection uses
canonical byte rejection rather than `% tableSize` over a biased range.  A browser
cannot provide a seed, beacon, date, ticket index, entry, contribution, or result.

`CurrentStateCapability` is intentionally opaque.  A node may mint it only for the
current globally agreed state after authenticating its root.  This is what makes
replay protection global rather than "whatever fresh object the browser sent".
Likewise, only a finality adapter may mint `FinalityCapability`; the pure helper it
authorizes consumes an exact authored period, never wall-clock time.  The private
state and result constructors are representation boundaries, not signature
verification claims.
-/
import Dregg2.Games.PathOfAngels.PlayerCounters
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.SalvageCrate

open Dregg2.Games.PathOfAngels

set_option autoImplicit false

abbrev MAX_ENTRIES : Nat := 64
abbrev MAX_TICKETS : Nat := 256
abbrev MAX_PLAYERS : Nat := 256
abbrev MAX_PERIODS : Nat := 128
abbrev MAX_OPEN_RECORDS : Nat := MAX_PLAYERS * MAX_PERIODS

structure LootId where
  value : Nat
deriving Repr, DecidableEq

structure CosmeticId where
  value : Nat
deriving Repr, DecidableEq

structure RecordId where
  value : Nat
deriving Repr, DecidableEq

inductive CommonOutcome where
  | packingFoam
  | maintenanceSticker
  | warmAir
  | galleyCoupon
deriving Repr, DecidableEq

/-- These are account records or communal effects, never fungible inventory. -/
inductive Prize where
  | common (kind : CommonOutcome)
  | cosmetic (id : CosmeticId)
  | record (id : RecordId)
  | communalSalvage (id : RelicId)
deriving Repr, DecidableEq

inductive Custody where
  | nonEconomic
  | transferable
deriving Repr, DecidableEq

structure LootEntry where
  id : LootId
  prize : Prize
  custody : Custody
  weight : Nat
  contribution : Contribution
deriving DecidableEq

def Prize.declaredB (cosmetics : Finset CosmeticId) (records : Finset RecordId)
    (relics : Finset RelicId) : Prize → Bool
  | .common _ => true
  | .cosmetic id => decide (id ∈ cosmetics)
  | .record id => decide (id ∈ records)
  | .communalSalvage id => decide (id ∈ relics)

def Prize.isCommonB : Prize → Bool
  | .common _ => true
  | _ => false

def LootEntry.shapeValidB (mission : MissionSpec)
    (cosmetics : Finset CosmeticId) (records : Finset RecordId)
    (relics : Finset RelicId) (entry : LootEntry) : Bool :=
  decide (0 < entry.weight) &&
  decide (entry.custody = .nonEconomic) &&
  entry.prize.declaredB cosmetics records relics &&
  mission.acceptsContribution entry.contribution &&
  match entry.prize with
  | .common _ => decide (entry.contribution = Contribution.zero)
  | .communalSalvage relic => decide (entry.contribution.relics = {relic})
  | _ => decide (entry.contribution.relics = ∅)

structure DailyBeacon where
  period : EpochId
  value : Digest32
deriving DecidableEq

/-- Every field is part of the semantic deployment identity.  Compact wire hashes
may commit to this value, but may not replace its equality inside this layer. -/
structure RawConfig where
  mission : MissionSpec
  contentSeed : Digest32
  curatorKey : Digest32
  opensAt : EpochId
  closesAt : EpochId
  eligiblePlayers : Finset Digest32
  allowedCosmetics : Finset CosmeticId
  allowedRecords : Finset RecordId
  allowedSalvage : Finset RelicId
  table : List LootEntry
  beacons : List DailyBeacon
deriving DecidableEq

def ticketEntries (raw : RawConfig) : List LootEntry :=
  raw.table.flatMap fun entry => List.replicate entry.weight entry

def periodsStrictlyIncreaseB (beacons : List DailyBeacon) : Bool :=
  (beacons.map fun beacon => beacon.period.value).Pairwise (· < ·)

def beaconInWindowB (raw : RawConfig) (beacon : DailyBeacon) : Bool :=
  decide (raw.opensAt.value ≤ beacon.period.value ∧
    beacon.period.value ≤ raw.closesAt.value)

def configValidB (raw : RawConfig) : Bool :=
  decide (raw.opensAt.value ≤ raw.closesAt.value) &&
  decide raw.eligiblePlayers.Nonempty &&
  decide (raw.eligiblePlayers.card ≤ MAX_PLAYERS) &&
  decide raw.table.Nodup &&
  decide (raw.table.map LootEntry.id).Nodup &&
  decide (0 < raw.table.length) &&
  decide (raw.table.length ≤ MAX_ENTRIES) &&
  decide (0 < (ticketEntries raw).length) &&
  decide ((ticketEntries raw).length ≤ MAX_TICKETS) &&
  raw.table.all (LootEntry.shapeValidB raw.mission raw.allowedCosmetics
    raw.allowedRecords raw.allowedSalvage) &&
  raw.table.any (fun entry => entry.prize.isCommonB) &&
  decide (0 < raw.beacons.length) &&
  decide (raw.beacons.length ≤ MAX_PERIODS) &&
  periodsStrictlyIncreaseB raw.beacons &&
  raw.beacons.all (beaconInWindowB raw)

structure Config where
  raw : RawConfig
  valid : configValidB raw = true

def beaconByPeriod? (config : Config) (period : EpochId) : Option DailyBeacon :=
  config.raw.beacons.find? fun beacon => beacon.period = period

def digestByte (digest : Digest32) (index : Nat) : Nat :=
  (digest.bytes.getD index 0).val

def byte (value : Nat) : Fin 256 :=
  ⟨value % 256, Nat.mod_lt _ (by omega)⟩

/-- Deterministic expansion of the exact committed draw domain.  This is not
presented as a cryptographic hash or as an unpredictability source: the authored
beacon schedule is visible and a player may precompute their rotation.  Its job
is reproducible selection without caller-controlled rerolls.  The result identity
below retains every preimage field, so mixer collisions never become identity
collisions. -/
def drawBytes (raw : RawConfig) (beacon : DailyBeacon) (player : Digest32) :
    List (Fin 256) :=
  List.ofFn fun index : Fin 32 => byte (
    digestByte beacon.value index.val +
    digestByte raw.contentSeed index.val +
    digestByte player index.val +
    beacon.period.value * (index.val + 1) + index.val * 17)

/-- Unbiased selection from bytes.  Values in the incomplete high tail are
discarded; if all 32 bytes land there, the period has no opening rather than a
biased `% count` fallback. -/
def unbiasedIndex? (count : Nat) (bytes : List (Fin 256)) : Option (Fin count) :=
  if positive : 0 < count then
    if _bounded : count ≤ 256 then
      let ceiling := 256 - (256 % count)
      match bytes.find? (fun candidate => candidate.val < ceiling) with
      | none => none
      | some candidate => some ⟨candidate.val % count, Nat.mod_lt _ positive⟩
    else none
  else none

def drawIndex? (config : Config) (beacon : DailyBeacon) (player : Digest32) :
    Option (Fin (ticketEntries config.raw).length) :=
  unbiasedIndex? (ticketEntries config.raw).length
    (drawBytes config.raw beacon player)

def previewEntry? (config : Config) (player : Digest32) (period : EpochId) :
    Option LootEntry := do
  let beacon ← beaconByPeriod? config period
  let index ← drawIndex? config beacon player
  some ((ticketEntries config.raw).get index)

structure RotationEntry where
  period : EpochId
  beacon : Digest32
  entry : Option LootEntry
deriving DecidableEq

/-- A generated informational rotation.  It grants no opening and consumes no
eligibility; the judge independently derives the same entry. -/
def generatedRotation (config : Config) (player : Digest32) : List RotationEntry :=
  config.raw.beacons.map fun beacon =>
    { period := beacon.period
      beacon := beacon.value
      entry := previewEntry? config player beacon.period }

structure OpenKey where
  federationId : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  period : EpochId
  player : Digest32
deriving DecidableEq

def openKey (config : Config) (period : EpochId) (player : Digest32) : OpenKey where
  federationId := config.raw.mission.federationId
  contentSession := config.raw.mission.contentSession
  contentEpoch := config.raw.mission.epoch
  period
  player

def counterKey (config : Config) (player : Digest32) : PlayerCounterKey where
  federationId := config.raw.mission.federationId
  contentSession := config.raw.mission.contentSession
  contentEpoch := config.raw.mission.epoch
  playerKey := player

/-- Runtime-owned persistent state.  There is deliberately no public empty-state
producer: genesis/restore belongs to the global state adapter. -/
structure State (config : Config) where
  private mk ::
  configIdentity : RawConfig
  currentPeriod : EpochId
  sequence : Nat
  consumed : Finset OpenKey
  playerCounters : PlayerCounterTable

structure GlobalSnapshot where
  configIdentity : RawConfig
  currentPeriod : EpochId
  sequence : Nat
  consumed : Finset OpenKey
  counterRows : List (PlayerCounterKey × PlayerCounter)
deriving DecidableEq

private def State.snapshot {config : Config} (state : State config) : GlobalSnapshot where
  configIdentity := state.configIdentity
  currentPeriod := state.currentPeriod
  sequence := state.sequence
  consumed := state.consumed
  counterRows := state.playerCounters.rows

/-- The action is signed over the entire exact deployment and global pre-state
position.  It contains no caller-selected date, beacon, ticket, entry, or prize. -/
structure OpenEnvelope where
  configIdentity : RawConfig
  expectedPeriod : EpochId
  expectedSequence : Nat
  actorRoot : Digest32
  player : Digest32
  previousPlayerCounter : Nat
  playerCounter : Nat
deriving DecidableEq

structure ResultIdentity where
  configIdentity : RawConfig
  beacon : DailyBeacon
  contentSeed : Digest32
  actorRoot : Digest32
  player : Digest32
  playerCounter : Nat
  ticketIndex : Nat
  entryId : LootId
deriving DecidableEq

/-- Successful opening is itself the non-forgeable result capability. -/
structure OpenResult (config : Config) (envelope : OpenEnvelope) where
  private mk ::
  identity : ResultIdentity
  entry : LootEntry
  contribution : Contribution
  after : State config
  config_exact : identity.configIdentity = config.raw
  content_seed_exact : identity.contentSeed = config.raw.contentSeed
  actor_root_exact : identity.actorRoot = envelope.actorRoot
  player_exact : identity.player = envelope.player
  player_counter_exact : identity.playerCounter = envelope.playerCounter
  entry_id_exact : identity.entryId = entry.id
  contribution_exact : contribution = entry.contribution
  consumes_exact_period :
    openKey config envelope.expectedPeriod envelope.player ∈ after.consumed
  counter_committed :
    (after.playerCounters.lookup (counterKey config envelope.player)).val =
      envelope.playerCounter

/-- Minted outside this module only after authenticating the current global root.
The index prevents a capability for one state from authorizing another. -/
opaque CurrentStateCapability {config : Config} (state : State config) : Type

def stateValidB (config : Config) (state : State config) : Bool :=
  decide (state.configIdentity = config.raw) &&
  decide ((beaconByPeriod? config state.currentPeriod).isSome) &&
  decide (state.consumed.card ≤ MAX_OPEN_RECORDS)

private def openCore (config : Config) (global : GlobalSnapshot)
    (state : State config) (envelope : OpenEnvelope) : Option (OpenResult config envelope) := do
  if stateValidB config state ≠ true then none else
  if global ≠ state.snapshot then none else
  if envelope.configIdentity ≠ config.raw then none else
  if periodMatches : envelope.expectedPeriod = state.currentPeriod then
  if envelope.expectedSequence ≠ state.sequence then none else
  if envelope.player ∉ config.raw.eligiblePlayers then none else
  let key := openKey config state.currentPeriod envelope.player
  if key ∈ state.consumed then none else
  let playerKey := counterKey config envelope.player
  if envelope.previousPlayerCounter ≠ state.playerCounters.lookup playerKey then none else
  if advances : envelope.playerCounter = envelope.previousPlayerCounter + 1 then
  if inRange : envelope.playerCounter < PLAYER_COUNTER_MODULUS then
    if state.consumed.card ≥ MAX_OPEN_RECORDS then none else
    let beacon ← beaconByPeriod? config state.currentPeriod
    let index ← drawIndex? config beacon envelope.player
    let entry := (ticketEntries config.raw).get index
    let nextCounter : PlayerCounter := ⟨envelope.playerCounter, inRange⟩
    let nextCounterNonzero : nextCounter ≠ 0 := by
      intro zero
      have valueZero := congrArg Fin.val zero
      simp only [nextCounter, Fin.val_zero] at valueZero
      omega
    let after : State config := {
      configIdentity := state.configIdentity
      currentPeriod := state.currentPeriod
      sequence := state.sequence + 1
      consumed := insert key state.consumed
      playerCounters := state.playerCounters.set playerKey nextCounter nextCounterNonzero
    }
    some {
      identity := {
        configIdentity := config.raw
        beacon
        contentSeed := config.raw.contentSeed
        actorRoot := envelope.actorRoot
        player := envelope.player
        playerCounter := envelope.playerCounter
        ticketIndex := index.val
        entryId := entry.id
      }
      entry
      contribution := entry.contribution
      after
      config_exact := rfl
      content_seed_exact := rfl
      actor_root_exact := rfl
      player_exact := rfl
      player_counter_exact := rfl
      entry_id_exact := rfl
      contribution_exact := rfl
      consumes_exact_period := by simp [after, key, periodMatches]
      counter_committed := by
        change ((state.playerCounters.set playerKey nextCounter nextCounterNonzero).lookup
          playerKey).val = envelope.playerCounter
        rw [PlayerCounterTable.lookup_set_same]
    }
  else none
  else none
  else none

/-- Public opening.  The caller must possess the capability for the exact current
global state; the browser cannot manufacture one for a stale or fresh state. -/
def openCrate (config : Config) (state : State config)
    (_current : CurrentStateCapability state) (envelope : OpenEnvelope) :
    Option (OpenResult config envelope) :=
  openCore config state.snapshot state envelope

structure FinalityUpdate where
  priorPeriod : EpochId
  finalizedPeriod : EpochId
deriving DecidableEq

opaque FinalityCapability {config : Config} (state : State config)
  (update : FinalityUpdate) : Type

private def advanceCore (config : Config) (global : GlobalSnapshot)
    (state : State config) (update : FinalityUpdate) : Option (State config) := do
  if stateValidB config state ≠ true then none else
  if global ≠ state.snapshot then none else
  if update.priorPeriod ≠ state.currentPeriod then none else
  if ¬state.currentPeriod.value < update.finalizedPeriod.value then none else
  let _ ← beaconByPeriod? config update.finalizedPeriod
  some {
    configIdentity := state.configIdentity
    currentPeriod := update.finalizedPeriod
    sequence := state.sequence + 1
    consumed := state.consumed
    playerCounters := state.playerCounters
  }

/-- Finality may skip quiet periods.  No streak state is created or updated. -/
def advancePeriod (config : Config) (state : State config)
    (update : FinalityUpdate) (_finalized : FinalityCapability state update) :
    Option (State config) :=
  advanceCore config state.snapshot state update

theorem open_result_retains_exact_entry {config : Config} {state : State config}
    {envelope : OpenEnvelope} {result : OpenResult config envelope}
    (_accepted : openCore config state.snapshot state envelope = some result) :
    result.identity.configIdentity = config.raw ∧
    result.identity.contentSeed = config.raw.contentSeed ∧
    result.identity.actorRoot = envelope.actorRoot ∧
    result.identity.player = envelope.player ∧
    result.identity.playerCounter = envelope.playerCounter ∧
    result.identity.entryId = result.entry.id ∧
    result.contribution = result.entry.contribution := by
  exact ⟨result.config_exact, result.content_seed_exact, result.actor_root_exact,
    result.player_exact, result.player_counter_exact, result.entry_id_exact,
    result.contribution_exact⟩

theorem accepted_open_consumes_exact_period {config : Config} {state : State config}
    {envelope : OpenEnvelope} {result : OpenResult config envelope}
    (_accepted : openCore config state.snapshot state envelope = some result) :
    openKey config envelope.expectedPeriod envelope.player ∈ result.after.consumed :=
  result.consumes_exact_period

theorem accepted_open_advances_global_counter {config : Config} {state : State config}
    {envelope : OpenEnvelope} {result : OpenResult config envelope}
    (_accepted : openCore config state.snapshot state envelope = some result) :
    (result.after.playerCounters.lookup (counterKey config envelope.player)).val =
      envelope.playerCounter :=
  result.counter_committed

/-! ## Private executable hostility laboratory

The runtime capabilities cannot be forged inside ordinary Lean clients.  These
fixtures deliberately exercise the private transition core so the refusal rules
remain executable without postulating a fake capability.
-/

private def fixtureDigest (tag : Nat) : Digest32 where
  bytes := List.replicate 32 (byte tag)
  length_eq := by simp

private def fixtureArtifact : ArtifactRef where
  missionId := ⟨700⟩
  artifactId := ⟨701⟩
  sourceDigest := fixtureDigest 1
  contentDigest := fixtureDigest 2

private def fixtureBudget : ContributionBudget where
  intel := 0
  supplies := 5
  cohesion := 0
  influence := 0
  score := 0
  relics := 1

private def fixtureRelic : RelicId := ⟨41⟩

private def fixtureMission : MissionSpec where
  missionId := ⟨700⟩
  artifact := fixtureArtifact
  epoch := ⟨9⟩
  federationId := fixtureDigest 3
  contentRoot := fixtureDigest 4
  activationDigest := fixtureDigest 5
  contentSession := fixtureDigest 6
  runSeed := fixtureDigest 7
  budget := fixtureBudget
  allowedRelics := {fixtureRelic}
  privacy := .public
  ballot := .none
  artifact_matches := rfl
  allowed_relics_bounded := by simp

private def salvageContribution : Contribution where
  intel := 0
  supplies := 2
  cohesion := 0
  influence := 0
  score := 0
  relics := {fixtureRelic}
  relics_bounded := by simp

private def fixtureTable : List LootEntry :=
  [ { id := ⟨1⟩, prize := .common .packingFoam, custody := .nonEconomic,
      weight := 3, contribution := .zero }
  , { id := ⟨2⟩, prize := .cosmetic ⟨11⟩, custody := .nonEconomic,
      weight := 2, contribution := .zero }
  , { id := ⟨3⟩, prize := .communalSalvage fixtureRelic, custody := .nonEconomic,
      weight := 1, contribution := salvageContribution }
  ]

private def fixtureRaw : RawConfig where
  mission := fixtureMission
  contentSeed := fixtureDigest 12
  curatorKey := fixtureDigest 13
  opensAt := ⟨12⟩
  closesAt := ⟨19⟩
  eligiblePlayers := {fixtureDigest 20, fixtureDigest 21}
  allowedCosmetics := {⟨11⟩}
  allowedRecords := ∅
  allowedSalvage := {fixtureRelic}
  table := fixtureTable
  beacons :=
    [⟨⟨12⟩, fixtureDigest 31⟩, ⟨⟨13⟩, fixtureDigest 47⟩, ⟨⟨19⟩, fixtureDigest 83⟩]

private theorem fixture_config_valid : configValidB fixtureRaw = true := by
  native_decide

private def fixtureConfig : Config := ⟨fixtureRaw, fixture_config_valid⟩
private def alice : Digest32 := fixtureDigest 20

private def initialAt (period : EpochId) : State fixtureConfig where
  configIdentity := fixtureRaw
  currentPeriod := period
  sequence := 0
  consumed := ∅
  playerCounters := PlayerCounterTable.empty

private def initial : State fixtureConfig := initialAt ⟨12⟩

private def envelopeFor (state : State fixtureConfig) (period : EpochId)
    (previous next : Nat) : OpenEnvelope where
  configIdentity := fixtureRaw
  expectedPeriod := period
  expectedSequence := state.sequence
  actorRoot := fixtureDigest 90
  player := alice
  previousPlayerCounter := previous
  playerCounter := next

private def firstEnvelope : OpenEnvelope := envelopeFor initial ⟨12⟩ 0 1
private def firstOpen? : Option (OpenResult fixtureConfig firstEnvelope) :=
  openCore fixtureConfig initial.snapshot initial firstEnvelope

theorem fixture_daily_open_succeeds : firstOpen?.isSome = true := by native_decide

private def afterFirst : State fixtureConfig :=
  (firstOpen?.get (by native_decide)).after

theorem identical_daily_open_reroll_refuses :
    openCore fixtureConfig afterFirst.snapshot afterFirst firstEnvelope = none := by
  native_decide

theorem tomorrow_and_old_epoch_claims_refuse :
    openCore fixtureConfig initial.snapshot initial
        (envelopeFor initial ⟨13⟩ 0 1) = none ∧
      let current := initialAt ⟨19⟩
      openCore fixtureConfig current.snapshot current
        (envelopeFor current ⟨12⟩ 0 1) = none := by
  native_decide

/-- Even a representation-level fresh state cannot be reopened against the latest
global snapshot.  Public callers cannot construct that fresh state in the first
place, and cannot mint its `CurrentStateCapability`. -/
theorem fresh_state_reopen_against_global_snapshot_refuses :
    openCore fixtureConfig afterFirst.snapshot initial firstEnvelope = none := by
  native_decide

private def rerolledRaw : RawConfig :=
  { fixtureRaw with beacons :=
      [⟨⟨12⟩, fixtureDigest 99⟩, ⟨⟨13⟩, fixtureDigest 47⟩,
       ⟨⟨19⟩, fixtureDigest 83⟩] }

private theorem rerolled_config_valid : configValidB rerolledRaw = true := by native_decide
private def rerolledConfig : Config := ⟨rerolledRaw, rerolled_config_valid⟩
private def rerolledState : State rerolledConfig where
  configIdentity := rerolledRaw
  currentPeriod := ⟨12⟩
  sequence := 0
  consumed := ∅
  playerCounters := PlayerCounterTable.empty

/-- Changing the committed beacon changes the complete config identity.  An
envelope authorized for the original deployment cannot ask the operator to try
the new beacon. -/
theorem operator_beacon_reroll_breaks_authorized_identity :
    openCore rerolledConfig rerolledState.snapshot rerolledState firstEnvelope = none := by
  native_decide

private def transferableTable : List LootEntry :=
  match fixtureTable with
  | [] => []
  | first :: rest => { first with custody := .transferable } :: rest

private def forgedTableRaw : RawConfig := { fixtureRaw with table := transferableTable }
private def emptyTableRaw : RawConfig := { fixtureRaw with table := [] }

theorem forged_transferable_table_refuses : configValidB forgedTableRaw = false := by
  native_decide

theorem empty_loot_table_refuses : configValidB emptyTableRaw = false := by
  native_decide

private def all255 : List (Fin 256) := List.replicate 32 (byte 255)

/-- Three does not divide 256.  Byte 255 belongs to the biased high tail and is
rejected rather than silently mapping to ticket zero. -/
theorem modulo_bias_tail_refuses_instead_of_favoring_zero :
    unbiasedIndex? 3 all255 = none := by native_decide

private def exhaustedCounters : PlayerCounterTable :=
  PlayerCounterTable.empty.set (counterKey fixtureConfig alice)
    ⟨PLAYER_COUNTER_MODULUS - 1, by simp [PLAYER_COUNTER_MODULUS]⟩
    (by intro h; have := congrArg Fin.val h; simp at this)

private def exhaustedState : State fixtureConfig where
  configIdentity := fixtureRaw
  currentPeriod := ⟨12⟩
  sequence := 0
  consumed := ∅
  playerCounters := exhaustedCounters

private def exhaustedEnvelope : OpenEnvelope :=
  envelopeFor exhaustedState ⟨12⟩ (PLAYER_COUNTER_MODULUS - 1) PLAYER_COUNTER_MODULUS

theorem counter_exhaustion_refuses_otherwise_eligible_open :
    openCore fixtureConfig exhaustedState.snapshot exhaustedState exhaustedEnvelope = none := by
  native_decide

private def periodNineteenFresh : State fixtureConfig := initialAt ⟨19⟩
private def periodNineteenEnvelope : OpenEnvelope :=
  envelopeFor periodNineteenFresh ⟨19⟩ 0 1

private def returningEnvelope (advanced : State fixtureConfig) : OpenEnvelope :=
  envelopeFor advanced ⟨19⟩ 1 2

private def periodNineteenReturning? : Option LootEntry := do
  let advanced ← advanceCore fixtureConfig afterFirst.snapshot afterFirst
    { priorPeriod := ⟨12⟩, finalizedPeriod := ⟨19⟩ }
  let result ← openCore fixtureConfig advanced.snapshot advanced (returningEnvelope advanced)
  some result.entry

private def periodNineteenFresh? : Option LootEntry := do
  let result ← openCore fixtureConfig periodNineteenFresh.snapshot periodNineteenFresh
    periodNineteenEnvelope
  some result.entry

/-- Counter history affects replay identity, never the draw.  Missing every period
between 12 and 19 therefore imposes no streak penalty. -/
theorem skipped_periods_do_not_change_the_daily_prize :
    periodNineteenReturning? = periodNineteenFresh? ∧
    periodNineteenReturning?.isSome = true := by
  native_decide

#assert_axioms open_result_retains_exact_entry
#assert_axioms accepted_open_consumes_exact_period
#assert_axioms accepted_open_advances_global_counter
#assert_compiled fixture_daily_open_succeeds
#assert_compiled identical_daily_open_reroll_refuses
#assert_compiled tomorrow_and_old_epoch_claims_refuse
#assert_compiled fresh_state_reopen_against_global_snapshot_refuses
#assert_compiled operator_beacon_reroll_breaks_authorized_identity
#assert_compiled forged_transferable_table_refuses
#assert_compiled empty_loot_table_refuses
#assert_compiled modulo_bias_tail_refuses_instead_of_favoring_zero
#assert_compiled counter_exhaustion_refuses_otherwise_eligible_open
#assert_compiled skipped_periods_do_not_change_the_daily_prize

end Dregg2.Games.PathOfAngels.SalvageCrate
