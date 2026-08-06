/-
# NightWatchCampaign — a Lean-authored shift aboard the Khovokhi

The player chooses an officer, station, and authored task.  The activated policy
and current state derive everything else: hazard roll, success, evidence,
resource movement, wounds/recovery, contribution, mastery, and beta discovery.
No action contains reward bytes.

The campaign emits exact logbook/event intents.  An intent deliberately lacks
an `EventBatch.FinalizedTurnCoordinate`, event digest, batch digest, and durable
append receipt.  The existing EventBatch authority must supply those later.
Holder presentation is accepted only as UI metadata and is erased before the
semantic command; it cannot affect score, resources, safety, mastery, or canon.

## ⚑ STATUS 2026-08-05 — this is the shipped night watch

Two Path-of-Angels state machines carry "Night Watch" in the name and share **no
type, no relation and no theorem**.  `NightWatchLoop` (4,400 lines: rotations, a
commons serving economy, encounters, routes, extraction terminals) is a different
game for the same fiction, and it is unreachable by construction — its `Policy`
needs a `ContentMembershipAdmission` that has no public producer.  See its docblock
for the disposition question.

**This module is the one connected to a player.**  Its boundary is
`NightWatchCampaignWire` (canonical JSON + `@[export
dregg_poa_night_watch_campaign_judge]`, ⚠ still MOUNTED NOWHERE), the authenticated
route to a `Config` is `NightWatchCampaignAdmission`, and its proof that the kernel
actually runs is `NightWatchCampaignExamples`.

## ⚑ 2026-08-05 — the two authority holes this kernel used to have, and the flag day

**1. The hazard was PUBLISHED.**  `hazardAt` read `hazardCycle.getD (shift % len) 0`
off the config, so anyone holding the config could compute every future roll, and
publishing the config as a curator-signed manifest component would have published
the whole solution.  That is exactly the wound `HiddenInstance.lean` exists to close,
and deleting the field alone would have closed NOTHING — the same trap that module
records for `signal-triangulation.json`.

So `hazardCycle` LEFT `RawConfig` and the roll is DRAWN, per run, off the hidden
instance: the config publishes the rules and a per-slot COMMITMENT, and the schedule
comes from `HiddenInstance.runSeedFor` through the sponge chain below.  Nobody
without the slot secret can predict a roll, and the schedule moves with the secret,
the slot and the player (`NightWatchCampaignExamples` exhibits all three).

**2. The config was whatever the caller handed over.**  `activate?` checks that a
config is STRUCTURALLY valid; it has never checked that it is AUTHENTIC, and it still
does not.  What changed is that there is now a producer which does:
`NightWatchCampaignAdmission.authorizeCampaignConfigForWorld?` locates
`poa.night-watch-campaign.config.v1` inside a curator-signed activated manifest whose
root IS the active world's `contentRoot`, and only that route yields a config bound
to a world.  `activate?` stays public — a config is not authority, a
`WorldScopedCampaignConfigMember` is.

**The `Activation` is the object every entry point now takes**, and it is the
`Judged.admissionChecks` discipline for this organ (`SlotDeriveRuntime.lean:14-24`):
the node derives the slot commitment and the run seed independently — through the
live `dregg_poa_signal_slot_derive` export — and `admitActivation?` RE-DERIVES both
and refuses on mismatch.  That is a check only because the node derived them itself;
a node that shipped a placeholder and let the kernel fill it in would be asking the
kernel to compute the answer rather than to verify the one the player was served.

**Flag day.**  `RawConfig` lost `hazardCycle` and gained `missionId`, `slot` and
`slotCommitment`; `riskThreshold` is now out of `HAZARD_FACES = 256`, not 100;
`MAX_HAZARD_CYCLE` is gone; `judge`, `replay`, `initialState` and `hazardAt` take an
`Activation`, not a `Config`.  Every `POA-NIGHT-WATCH-CAMPAIGN-CONFIG-1` document
re-emits, every manifest carrying one re-hashes, and the world whose `contentRoot`
is that manifest root is re-activated.  Old config bytes REFUSE to decode: the key
set is exact and `hazard_cycle` is no longer a key.

⚑ `HiddenInstance.commit` and `runSeedFor` are `@[irreducible]` because
`Poseidon2BabyBearW16.perm` reduces exponentially (measured: 47.6 GB, 68 minutes for
one file).  Nothing here unfolds them, nothing here proves a fact about a CONCRETE
seed by `decide`/`rfl`, and every theorem below about the derivation is general —
both sides are the same opaque application.  The concrete facts live in
`NightWatchCampaignExamples` under `native_decide` and are pinned `#assert_compiled`.
-/
import Dregg2.Games.PathOfAngels.HiddenInstance
import Dregg2.Games.PathOfAngels.ShipLifeProgression
import Dregg2.Games.PathOfAngels.OfficerLogbook
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.NightWatchCampaign

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.CrewRelayExpedition

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

abbrev MAX_RULES : Nat := 32
abbrev MAX_SHIFTS : Nat := 4096
abbrev MAX_HISTORY : Nat := 4096
abbrev MAX_RESOURCE : Nat := 1000000
abbrev MAX_EVIDENCE : Nat := 1000000
abbrev MAX_WOUNDS : Nat := 100
abbrev MAX_STRAIN : Nat := 100
abbrev MASTERY_LEVEL_SIZE : Nat := 10

/-! ## The hazard schedule, drawn from the hidden instance

⚑ **The stream-length problem, and why there is no cap here.**  A run seed is 32
bytes.  A rejection-sampled draw below 100 has ceiling `256 - 256 % 100 = 200`, so it
consumes about 1.28 bytes *in expectation* — roughly 24 draws out of one seed, and an
expectation is not a bound.  Against `MAX_SHIFTS = 4096` that seed exhausts mid
schedule and the draw returns `none`, which would refuse that player's run: a liveness
failure landing on some players and not others.  Capping `maxShifts` at whatever a
seed happens to serve would leave a number in the kernel that reads as design intent
and is really a byte budget.

Two things remove the problem instead, and each is a theorem below.

* **The stream is squeezed as long as the schedule needs.**  `hazardBlock` is the
  `HiddenInstance` sponge again — same `absorbAll`/`squeeze`/`digestBlocks`/
  `digestOfStream`/`laneBytes`/`SQUEEZE_BLOCKS`, a new domain tag, and the block index
  in the header — and `Digest32` carries its own `length_eq`, so `hazardBytes` is
  exactly `32 * blocks` bytes for ANY block count, with no reference to what the sponge
  computed.  `hazardBlocksFor` asks for exactly the blocks the shift count needs.
* **The draw is exact-width, so it never rejects.**  `HAZARD_FACES = 256` and
  `SeedDraw.ceilingFor 256 = 256`: every byte is below the ceiling, so
  `drawing_below_the_face_count_consumes_exactly_one_byte` — one byte in, one roll out,
  no rejection to be unlucky with.  That is why a roll is out of 256 rather than out of
  100: 100 does not divide any power of two, so a percentage roll cannot have a
  consumption bound at all, only an expectation.  The authored `riskThreshold` is
  therefore in 256ths (60% odds is `102`, not `40`).

`hazard_schedule_has_exactly_one_roll_per_shift` is the totality statement: for EVERY
seed and EVERY shift count — no bound, no side condition — the schedule has exactly one
roll per shift.  The rejection `SeedDraw` still performs is not dead code; it is what
makes the 256 case a theorem rather than a coincidence.

The one residual, named: `HiddenInstance.laneByte?` drops the single aliasing lane
value (`P - 1`, one lane in 2^31), and `digestOfStream` zero-fills if a block loses more
than sixteen of its forty-eight squeezed lanes.  That is a property of the sponge this
module reuses rather than one it introduces, and it costs at most a non-uniform byte in
an event of probability under 2^-500 — it can never shorten the schedule, because the
digest's length is a proof field, not a measurement. -/

/-- `"POAH"` — the hazard-schedule chain, kept apart from `HiddenInstance`'s `"POAC"`
commitment and `"POAD"` derivation domains. -/
abbrev HAZARD_DOMAIN : Nat := 0x504F4148

/-- The lane modulus of the deployed sponge; a header lane must be canonical. -/
abbrev HAZARD_LANE_MODULUS : Nat := Dregg2.Circuit.Poseidon2BabyBearW16.P

/-- A roll is a byte.  256 is the ONLY interesting property: it is the exact width of
the stream `SeedDraw` consumes, so a draw below it can never reject. -/
abbrev HAZARD_FACES : Nat := 256

theorem the_hazard_domain_is_distinct_from_the_commit_and_derive_domains :
    HAZARD_DOMAIN ≠ HiddenInstance.COMMIT_DOMAIN ∧
    HAZARD_DOMAIN ≠ HiddenInstance.DERIVE_DOMAIN ∧
    HAZARD_DOMAIN < HAZARD_LANE_MODULUS := by
  refine ⟨by decide, by decide, by decide⟩

/-- One 32-byte chain block off the run seed, indexed.  This is `HiddenInstance.commit`'s
shape with the hazard domain and a block index: absorb a header block and the seed's four
rate blocks, squeeze `SQUEEZE_BLOCKS`, project lanes to bytes, take 32. -/
def hazardBlock (seed : Digest32) (index : Nat) : Digest32 :=
  HiddenInstance.digestOfStream (HiddenInstance.laneBytes
    (HiddenInstance.squeeze
      (HiddenInstance.absorbAll HiddenInstance.initialState
        (HiddenInstance.pad HiddenInstance.RATE
            [HAZARD_DOMAIN, index % HAZARD_LANE_MODULUS, 0, 0, 0, 0, 0, 0]
          :: HiddenInstance.digestBlocks seed))
      HiddenInstance.SQUEEZE_BLOCKS))

/-- The chained byte stream: block 0, then block 1, and so on. -/
def hazardBytes (seed : Digest32) : Nat → List (Fin 256)
  | 0 => []
  | index + 1 => hazardBytes seed index ++ (hazardBlock seed index).bytes

/-- How many chain blocks a shift count needs — `⌈shifts / 32⌉`, where 32 is the width
of a `Digest32`.  Derived from the need, not chosen: this is the number that would have
been a cap. -/
def hazardBlocksFor (shifts : Nat) : Nat := (shifts + 31) / 32

def hazardStream (seed : Digest32) (shifts : Nat) : List (Fin 256) :=
  hazardBytes seed (hazardBlocksFor shifts)

/-- `count` consuming draws off the stream.  The `none` arm is what an exhausted stream
would take; `drawRolls_length` proves the caller below never reaches it. -/
def drawRolls : Nat → List (Fin 256) → List (Fin HAZARD_FACES)
  | 0, _ => []
  | count + 1, bytes =>
      match SeedDraw.drawBelow? HAZARD_FACES (by decide) bytes with
      | none => []
      | some (roll, rest) => roll :: drawRolls count rest

/-- **The schedule.**  One roll per shift, drawn off the seed's chained stream. -/
def hazardSchedule (seed : Digest32) (shifts : Nat) : List Nat :=
  (drawRolls shifts (hazardStream seed shifts)).map Fin.val

/-- At the exact stream width the draw accepts every byte: `ceilingFor 256 = 256`, so
the rejection branch is unreachable and one draw consumes exactly one byte.  This is
the fact that turns "about 1.28 bytes in expectation" into a length. -/
theorem drawing_below_the_face_count_consumes_exactly_one_byte
    (byte : Fin 256) (rest : List (Fin 256)) :
    SeedDraw.drawBelow? HAZARD_FACES (by decide) (byte :: rest) = some (byte, rest) := by
  have below : byte.val < SeedDraw.ceilingFor HAZARD_FACES := by
    show byte.val < 256 - 256 % 256
    rw [Nat.mod_self, Nat.sub_zero]
    exact byte.isLt
  simp only [SeedDraw.drawBelow?]
  rw [if_pos below]
  exact congrArg (fun value => some (value, rest))
    (Fin.ext (Nat.mod_eq_of_lt byte.isLt))

/-- The stream length is a count of digests, not a measurement of the sponge: every
block contributes exactly 32 bytes because `Digest32` carries that as a proof field. -/
theorem hazard_stream_is_thirty_two_bytes_per_block (seed : Digest32) (blocks : Nat) :
    (hazardBytes seed blocks).length = 32 * blocks := by
  induction blocks with
  | zero => rfl
  | succ blocks ih =>
      have width : (hazardBlock seed blocks).bytes.length = 32 :=
        (hazardBlock seed blocks).length_eq
      have split : (hazardBytes seed (blocks + 1)).length
          = (hazardBytes seed blocks).length + (hazardBlock seed blocks).bytes.length := by
        simp [hazardBytes]
      rw [split, ih, width]
      omega

theorem hazard_stream_supplies_at_least_one_byte_per_shift (seed : Digest32)
    (shifts : Nat) : shifts ≤ (hazardStream seed shifts).length := by
  rw [hazardStream, hazard_stream_is_thirty_two_bytes_per_block]
  unfold hazardBlocksFor
  omega

theorem drawRolls_length (count : Nat) (bytes : List (Fin 256))
    (enough : count ≤ bytes.length) : (drawRolls count bytes).length = count := by
  induction count generalizing bytes with
  | zero => rfl
  | succ count ih =>
      cases bytes with
      | nil => exact absurd enough (by simp only [List.length_nil]; omega)
      | cons byte rest =>
          have shorter : count ≤ rest.length := by
            simp only [List.length_cons] at enough
            omega
          have step : drawRolls (count + 1) (byte :: rest) = byte :: drawRolls count rest := by
            rw [drawRolls, drawing_below_the_face_count_consumes_exactly_one_byte]
          rw [step, List.length_cons, ih rest shorter]

/-- **Totality, for every seed and every shift count.**  No bound, no side condition,
no `none`: the schedule always has exactly one roll per shift, so no run can be refused
for running out of stream. -/
theorem hazard_schedule_has_exactly_one_roll_per_shift (seed : Digest32) (shifts : Nat) :
    (hazardSchedule seed shifts).length = shifts := by
  rw [hazardSchedule, List.length_map]
  exact drawRolls_length shifts (hazardStream seed shifts)
    (hazard_stream_supplies_at_least_one_byte_per_shift seed shifts)

/-- Every roll is a face, by the type the draw returns. -/
theorem every_hazard_roll_is_below_the_face_count (seed : Digest32) (shifts : Nat) :
    ∀ roll ∈ hazardSchedule seed shifts, roll < HAZARD_FACES := by
  intro roll member
  simp only [hazardSchedule, List.mem_map] at member
  obtain ⟨drawn, _, value⟩ := member
  exact value ▸ drawn.isLt

/-! ## Authored campaign vocabulary -/

inductive Station where
  | bridge
  | engineSpine
  | signalGallery
  | containment
  | galley
  | infirmary
deriving DecidableEq, Repr

inductive Task where
  | plotDrift
  | coolantBalance
  | traceSignal
  | inspectSeal
  | rationAudit
  | recoveryRound
deriving DecidableEq, Repr

def Station.tag : Station → Nat
  | .bridge => 1
  | .engineSpine => 2
  | .signalGallery => 3
  | .containment => 4
  | .galley => 5
  | .infirmary => 6

def Task.tag : Task → Nat
  | .plotDrift => 1
  | .coolantBalance => 2
  | .traceSignal => 3
  | .inspectSeal => 4
  | .rationAudit => 5
  | .recoveryRound => 6

structure ContributionDelta where
  intel : Nat
  supplies : Nat
  cohesion : Nat
  influence : Nat
  score : Nat
deriving DecidableEq, Repr

def ContributionDelta.zero : ContributionDelta := ⟨0, 0, 0, 0, 0⟩

structure ShipResources where
  propellant : Nat
  munitions : Nat
  supplies : Nat
  morale : Nat
deriving DecidableEq, Repr

def ShipResources.boundedB (resources : ShipResources) : Bool :=
  decide (resources.propellant ≤ MAX_RESOURCE) &&
    decide (resources.munitions ≤ MAX_RESOURCE) &&
    decide (resources.supplies ≤ MAX_RESOURCE) &&
    decide (resources.morale ≤ MAX_RESOURCE)

/-- Explicit spends and gains make conservation/audit visible. -/
structure WorldEffects where
  spendPropellant : Nat := 0
  spendMunitions : Nat := 0
  spendSupplies : Nat := 0
  spendMorale : Nat := 0
  gainPropellant : Nat := 0
  gainMunitions : Nat := 0
  gainSupplies : Nat := 0
  gainMorale : Nat := 0
deriving DecidableEq, Repr

def WorldEffects.boundedB (effect : WorldEffects) : Bool :=
  [effect.spendPropellant, effect.spendMunitions, effect.spendSupplies,
    effect.spendMorale, effect.gainPropellant, effect.gainMunitions,
    effect.gainSupplies, effect.gainMorale].all fun value =>
      decide (value ≤ MAX_RESOURCE)

def WorldEffects.apply? (effect : WorldEffects)
    (before : ShipResources) : Option ShipResources := do
  if before.propellant < effect.spendPropellant then none
  if before.munitions < effect.spendMunitions then none
  if before.supplies < effect.spendSupplies then none
  if before.morale < effect.spendMorale then none
  let after : ShipResources := {
    propellant := before.propellant - effect.spendPropellant + effect.gainPropellant
    munitions := before.munitions - effect.spendMunitions + effect.gainMunitions
    supplies := before.supplies - effect.spendSupplies + effect.gainSupplies
    morale := before.morale - effect.spendMorale + effect.gainMorale
  }
  if !after.boundedB then none else some after

structure HealthEffect where
  woundsAdded : Nat := 0
  strainAdded : Nat := 0
  woundsRecovered : Nat := 0
  strainRecovered : Nat := 0
deriving DecidableEq, Repr

def HealthEffect.boundedB (effect : HealthEffect) : Bool :=
  decide (effect.woundsAdded ≤ MAX_WOUNDS) &&
    decide (effect.strainAdded ≤ MAX_STRAIN) &&
    decide (effect.woundsRecovered ≤ MAX_WOUNDS) &&
    decide (effect.strainRecovered ≤ MAX_STRAIN)

structure OfficerHealth where
  seat : SeatId
  wounds : Nat
  strain : Nat
  recoveryObserved : Nat
deriving DecidableEq, Repr

/-- `recoveryObserved` counts the recovery that HAPPENED, not the one that was asked
for.  Wounds and strain are Nat, so a recovery offered to an officer with nothing to
recover truncates away and moves no health; the condition below is exactly the one
`progressionOf` reports per watch, and `the_two_recovery_counters_agree` proves the
running row counter and the per-watch figure cannot disagree. -/
def OfficerHealth.apply (before : OfficerHealth) (effect : HealthEffect) :
    OfficerHealth :=
  let wounds := min MAX_WOUNDS
    (before.wounds + effect.woundsAdded - effect.woundsRecovered)
  let strain := min MAX_STRAIN
    (before.strain + effect.strainAdded - effect.strainRecovered)
  { before with
    wounds
    strain
    recoveryObserved := before.recoveryObserved +
      if wounds < before.wounds || strain < before.strain then 1 else 0 }

theorem officer_health_counts_the_recovery_that_happened
    (before : OfficerHealth) (effect : HealthEffect) :
    (before.apply effect).recoveryObserved =
      before.recoveryObserved +
        (if (before.apply effect).wounds < before.wounds ||
            (before.apply effect).strain < before.strain then 1 else 0) := rfl

/-- A recovery that moves neither wounds nor strain leaves the counter alone. -/
theorem a_recovery_that_moves_no_health_does_not_move_the_recovery_counter
    (before : OfficerHealth) (effect : HealthEffect)
    (wounds : (before.apply effect).wounds = before.wounds)
    (strain : (before.apply effect).strain = before.strain) :
    (before.apply effect).recoveryObserved = before.recoveryObserved := by
  rw [officer_health_counts_the_recovery_that_happened, wounds, strain]
  simp

/-- The other direction, which is what stops the counter from being a constant zero: a
recovery that DOES move wounds or strain still increments by exactly one. -/
theorem a_recovery_that_moves_health_increments_the_recovery_counter
    (before : OfficerHealth) (effect : HealthEffect)
    (moved : (before.apply effect).wounds < before.wounds ∨
      (before.apply effect).strain < before.strain) :
    (before.apply effect).recoveryObserved = before.recoveryObserved + 1 := by
  have observed : ((before.apply effect).wounds < before.wounds ||
      (before.apply effect).strain < before.strain) = true := by
    rcases moved with h | h
    · simp [h]
    · simp [h]
  rw [officer_health_counts_the_recovery_that_happened, observed]
  simp

/-- The concrete divergence the condition above closes: an unhurt officer offered a
two-wound three-strain recovery keeps every field it had, counter included. -/
theorem an_unhurt_officer_offered_a_recovery_moves_nothing_at_all :
    OfficerHealth.apply ⟨⟨0⟩, 0, 0, 0⟩
        { woundsRecovered := 2, strainRecovered := 3 } = ⟨⟨0⟩, 0, 0, 0⟩ := by
  decide

/-- The same recovery offered to an officer who has something to recover heals and is
counted, so the two theorems above are demonstrated on the same effect. -/
theorem a_wounded_officer_offered_the_same_recovery_heals_and_is_counted :
    OfficerHealth.apply ⟨⟨0⟩, 2, 3, 0⟩
        { woundsRecovered := 2, strainRecovered := 3 } = ⟨⟨0⟩, 0, 0, 1⟩ := by
  decide

def OfficerHealth.progressionView (health : OfficerHealth) :
    ShipLifeProgression.DerivedHealthView where
  wounds := health.wounds
  strain := health.strain
  inRecovery := decide (0 < health.wounds + health.strain)
  training := 0

structure TaskRule where
  station : Station
  task : Task
  role : CrewRole
  riskThreshold : Nat
  successContribution : ContributionDelta
  failureContribution : ContributionDelta
  successEffects : WorldEffects
  failureEffects : WorldEffects
  successHealth : HealthEffect
  failureHealth : HealthEffect
  successEvidence : Nat
  failureEvidence : Nat
  localService : Fin (GalleyMaintenanceDailyRuntime.MAX_LOCAL_SERVICE + 1)
  betaDiscovery : Option ContentContract.ArtifactId
  discoveryEvidenceRequired : Nat
  taskContentId : Digest32
  successContentId : Digest32
  failureContentId : Digest32
deriving DecidableEq

def TaskRule.key (rule : TaskRule) : Station × Task := (rule.station, rule.task)

def contributionBoundedB (value : ContributionDelta) : Bool :=
  [value.intel, value.supplies, value.cohesion, value.influence,
    value.score].all fun amount => decide (amount ≤ METRIC_LIMIT)

/-- ⚠ `riskThreshold` is in 256ths, not percent: the roll it is compared against is a
byte, because that is the width at which the draw never rejects (see the hazard
section).  Sixty-percent odds are `102`, not `40`.  `HAZARD_FACES` itself is admitted
so that "cannot succeed" is authorable; `0` is "cannot fail". -/
def taskRuleValidB (rule : TaskRule) : Bool :=
  decide (rule.riskThreshold ≤ HAZARD_FACES) &&
    contributionBoundedB rule.successContribution &&
    contributionBoundedB rule.failureContribution &&
    rule.successEffects.boundedB && rule.failureEffects.boundedB &&
    rule.successHealth.boundedB && rule.failureHealth.boundedB &&
    decide (rule.successEvidence ≤ MAX_EVIDENCE) &&
    decide (rule.failureEvidence ≤ MAX_EVIDENCE) &&
    decide (rule.discoveryEvidenceRequired ≤ MAX_EVIDENCE)

/-- The curator's published campaign.  ⚠ There is no `hazardCycle`: what is published
is the per-slot COMMITMENT, and the rolls are drawn per run from the secret that opens
it.  `missionId`, `slot` and `slotCommitment` are what bind a run's derivation to this
document — `NightWatchCampaign.ActivationBinds` refuses an activation that names any
other slot, commitment or mission context. -/
structure RawConfig where
  schemaVersion : Nat
  missionId : MissionId
  progression : ShipLifeProgression.ProgressionIdentity
  logStream : EventBatch.StreamId
  slot : EpochId
  slotCommitment : Digest32
  roster : List Seat
  rules : List TaskRule
  initialResources : ShipResources
  maxShifts : Nat
deriving DecidableEq

def configValidB (raw : RawConfig) : Bool :=
  decide (raw.schemaVersion > 0) &&
    decide (raw.logStream.aggregate.namespaceId = raw.progression.federationId) &&
    decide (raw.roster.length = CrewFieldMission.CREW_SIZE) &&
    decide (raw.roster.map Seat.id = [⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨3⟩]) &&
    decide (raw.roster.map Seat.role = CrewFieldMission.expectedRoles) &&
    decide (raw.roster.map Seat.playerKey).Nodup &&
    decide (raw.rules ≠ []) && decide (raw.rules.length ≤ MAX_RULES) &&
    decide (raw.rules.map TaskRule.key).Nodup &&
    raw.rules.all taskRuleValidB &&
    raw.initialResources.boundedB &&
    decide (0 < raw.maxShifts ∧ raw.maxShifts ≤ MAX_SHIFTS)

/-- ⚠ Structural validity, and NOTHING about authenticity — `activate?` is happy to
activate a config a player wrote.  The authenticated producer is
`NightWatchCampaignAdmission.authorizeCampaignConfigForWorld?`, which locates these
exact bytes inside a curator-signed manifest whose root is the active world's
`contentRoot`.  This constructor stays public because a `Config` confers no authority
on its own: nothing can be judged without an `Activation`, and an `Activation` needs a
secret that opens the config's own published commitment. -/
structure Config where
  private mk ::
  raw : RawConfig
  valid : configValidB raw = true

def activate? (raw : RawConfig) : Option Config :=
  if valid : configValidB raw = true then some ⟨raw, valid⟩ else none

/-- Activation reports the config it was given, so a caller that authenticated the
BYTES has authenticated the `Config`.  Without this, the admission witness could bind
its proof fields to a config nobody checked. -/
theorem activate_preserves_the_raw_config {raw : RawConfig} {config : Config}
    (accepted : activate? raw = some config) : config.raw = raw := by
  by_cases valid : configValidB raw = true
  · unfold activate? at accepted
    rw [dif_pos valid] at accepted
    injection accepted with accepted
    exact (congrArg Config.raw accepted).symm
  · unfold activate? at accepted
    rw [dif_neg valid] at accepted
    simp at accepted

/-! ## The run activation — the hidden instance, re-derived rather than believed

`RawActivation` is what the NODE assembles from its own state: the slot secret it
drew off-line, the commitment it published, the player the run belongs to, the mission
context, and the run seed it derived through `dregg_poa_signal_slot_derive`.  None of
it is a player claim, and `ActivationBinds` re-derives the two values that matter.

The residual, stated: whoever holds the slot secret knows every schedule for the slot
in advance, and may choose which of the four seated officers owns a run — so a node can
pick among at most four schedules.  That is `HiddenInstance`'s operator-hiding residual
narrowed to this organ, not a new one, and it is UNDONE WORK: removing it needs a
beacon feeding the slot secret. -/

structure RawActivation where
  slot : EpochId
  slotSecret : HiddenInstance.SlotSecret
  slotCommitment : Digest32
  playerKey : Digest32
  mission : HiddenInstance.MissionContext
  runSeed : Digest32
deriving DecidableEq

/-- The mission context a config determines.  It is DERIVED, so an activation cannot
grind the run seed by naming a context of its own — `ActivationBinds` requires equality
with this. -/
def missionContextOf (config : Config) : HiddenInstance.MissionContext where
  missionId := config.raw.missionId
  epoch := config.raw.progression.contentEpoch
  federationId := config.raw.progression.federationId
  contentSession := config.raw.progression.contentSession

/-- Does the roster seat this player key? -/
def rosterHolds (raw : RawConfig) (playerKey : Digest32) : Bool :=
  raw.roster.any fun seat => decide (seat.playerKey = playerKey)

/-- Every equality admission checks.  The last two are the RE-DERIVATIONS: the node
supplied a commitment and a seed, and the kernel recomputes both from the secret.  The
first four pin the derivation's inputs to the signed config, so the only freedom left
is which seated officer owns the run. -/
def ActivationBinds (config : Config) (draw : RawActivation) : Prop :=
  draw.slot = config.raw.slot ∧
  draw.slotCommitment = config.raw.slotCommitment ∧
  draw.mission = missionContextOf config ∧
  rosterHolds config.raw draw.playerKey = true ∧
  draw.slotCommitment = HiddenInstance.commit draw.slotSecret draw.slot ∧
  draw.runSeed =
    HiddenInstance.runSeedFor
      { secret := draw.slotSecret, slot := draw.slot, playerKey := draw.playerKey }
      draw.mission

instance (config : Config) (draw : RawActivation) : Decidable (ActivationBinds config draw) := by
  unfold ActivationBinds
  infer_instance

/-- ⚑ The judged object.  `private mk ::`, so the only way to hold one is
`admitActivation?`, and therefore every judged watch has a schedule that came out of a
secret opening the config's published commitment. -/
structure Activation where
  private mk ::
  config : Config
  draw : RawActivation
  schedule : List Nat
  slot_exact : draw.slot = config.raw.slot
  commitment_exact : draw.slotCommitment = config.raw.slotCommitment
  mission_exact : draw.mission = missionContextOf config
  player_seated : rosterHolds config.raw draw.playerKey = true
  commitment_opens : draw.slotCommitment = HiddenInstance.commit draw.slotSecret draw.slot
  seed_derived : draw.runSeed =
    HiddenInstance.runSeedFor
      { secret := draw.slotSecret, slot := draw.slot, playerKey := draw.playerKey }
      draw.mission
  schedule_derived : schedule = hazardSchedule draw.runSeed config.raw.maxShifts

def admitActivation? (config : Config) (draw : RawActivation) : Option Activation :=
  if binds : ActivationBinds config draw then
    some ⟨config, draw, hazardSchedule draw.runSeed config.raw.maxShifts,
      binds.1, binds.2.1, binds.2.2.1, binds.2.2.2.1, binds.2.2.2.2.1, binds.2.2.2.2.2, rfl⟩
  else none

theorem admitted_activation_carries_the_config_it_was_admitted_against
    {config : Config} {draw : RawActivation} {activation : Activation}
    (accepted : admitActivation? config draw = some activation) :
    activation.config = config ∧ activation.draw = draw := by
  by_cases binds : ActivationBinds config draw
  · unfold admitActivation? at accepted
    rw [dif_pos binds] at accepted
    injection accepted with accepted
    exact ⟨(congrArg Activation.config accepted).symm,
      (congrArg Activation.draw accepted).symm⟩
  · unfold admitActivation? at accepted
    rw [dif_neg binds] at accepted
    simp at accepted

/-- The schedule an activation carries is exactly one roll per shift of its own
config, so the ceiling and the schedule cannot disagree. -/
theorem an_activation_has_one_roll_per_authored_shift (activation : Activation) :
    activation.schedule.length = activation.config.raw.maxShifts := by
  rw [activation.schedule_derived]
  exact hazard_schedule_has_exactly_one_roll_per_shift _ _

/-! ## Derived shift state -/

structure MasteryRow where
  seat : SeatId
  station : Station
  xp : Nat
  level : Nat
deriving DecidableEq, Repr

def healthFor? : List OfficerHealth → SeatId → Option OfficerHealth
  | [], _ => none
  | row :: rows, seat => if row.seat = seat then some row else healthFor? rows seat

def setHealth : List OfficerHealth → OfficerHealth → List OfficerHealth
  | [], replacement => [replacement]
  | row :: rows, replacement =>
      if row.seat = replacement.seat then replacement :: rows
      else row :: setHealth rows replacement

def masteryFor : List MasteryRow → SeatId → Station → MasteryRow
  | [], seat, station => ⟨seat, station, 0, 0⟩
  | row :: rows, seat, station =>
      if row.seat = seat ∧ row.station = station then row
      else masteryFor rows seat station

def setMastery : List MasteryRow → MasteryRow → List MasteryRow
  | [], replacement => [replacement]
  | row :: rows, replacement =>
      if row.seat = replacement.seat ∧ row.station = replacement.station then
        replacement :: rows
      else row :: setMastery rows replacement

def findSeat? : List Seat → SeatId → Option Seat
  | [], _ => none
  | seat :: seats, id => if seat.id = id then some seat else findSeat? seats id

def findRule? : List TaskRule → Station → Task → Option TaskRule
  | [], _, _ => none
  | rule :: rules, station, task =>
      if rule.station = station ∧ rule.task = task then some rule
      else findRule? rules station task

structure BetaCanonProposal where
  sourceShift : Nat
  officer : Digest32
  artifact : ContentContract.ArtifactId
  evidence : Nat
  taskContentId : Digest32
deriving DecidableEq

structure ProgressionEffect where
  maintenanceSuccess : Nat
  meaningfulFailure : Nat
  trainingObserved : Nat
  recoveryObserved : Nat
deriving DecidableEq, Repr

structure ResolvedShift where
  shift : Nat
  officer : Seat
  rule : TaskRule
  hazardRoll : Nat
  success : Bool
  contribution : ContributionDelta
  worldEffects : WorldEffects
  resourcesBefore : ShipResources
  resourcesAfter : ShipResources
  healthBefore : OfficerHealth
  healthAfter : OfficerHealth
  evidenceBefore : Nat
  evidenceAfter : Nat
  betaProposal : Option BetaCanonProposal
  progression : ProgressionEffect
deriving DecidableEq

structure LogbookEntry where
  shift : Nat
  officer : Digest32
  seat : SeatId
  role : CrewRole
  participation : OfficerLogbook.Participation
  station : Station
  task : Task
  success : Bool
  hazardRoll : Nat
  riskThreshold : Nat
  contribution : ContributionDelta
  worldEffects : WorldEffects
  resourcesBefore : ShipResources
  resourcesAfter : ShipResources
  healthBefore : ShipLifeProgression.DerivedHealthView
  healthAfter : ShipLifeProgression.DerivedHealthView
  evidenceBefore : Nat
  evidenceAfter : Nat
  masteryBefore : MasteryRow
  masteryAfter : MasteryRow
  galleyLocalService : Option
    (Fin (GalleyMaintenanceDailyRuntime.MAX_LOCAL_SERVICE + 1))
  betaProposal : Option BetaCanonProposal
  progression : ProgressionEffect
  terminalContentId : Digest32
deriving DecidableEq

/-- Enough material to create an EventStatement after the host supplies the
current stream head and canonical payload digest.  It is not finality. -/
structure EventIntent where
  stream : EventBatch.StreamId
  expectedSequence : Nat
  entry : LogbookEntry
deriving DecidableEq

structure IntentDigestBoundary where
  payloadDigest : LogbookEntry → Digest32

def EventIntent.statement? (boundary : IntentDigestBoundary)
    (head : EventBatch.StreamHead) (intent : EventIntent) :
    Option EventSourcing.EventStatement := do
  if head.stream ≠ intent.stream then none
  if intent.expectedSequence ≠ head.sequence + 1 then none
  some {
    aggregate := intent.stream.aggregate
    version := intent.stream.version
    sequence := intent.expectedSequence
    predecessor := head.head
    payloadDigest := boundary.payloadDigest intent.entry
  }

/-- Explicit non-authority: an intent cannot manufacture an applied/finalized
batch. -/
def fabricateFinality (_intent : EventIntent) : Option EventBatch.AppliedBatch := none

theorem event_intent_has_no_finality (intent : EventIntent) :
    fabricateFinality intent = none := rfl

inductive Phase where
  | idle
  | claimed (officer : Seat)
  | assigned (officer : Seat) (rule : TaskRule)
  | awaitingDebrief (resolved : ResolvedShift)
deriving DecidableEq

structure State where
  private mk ::
  sequence : Nat
  shift : Nat
  resources : ShipResources
  evidence : Nat
  health : List OfficerHealth
  mastery : List MasteryRow
  phase : Phase
  history : List LogbookEntry
  intents : List EventIntent
  consumedActions : Finset Digest32
deriving DecidableEq

def initialState (activation : Activation) : State where
  sequence := 0
  shift := 0
  resources := activation.config.raw.initialResources
  evidence := 0
  health := activation.config.raw.roster.map fun seat => ⟨seat.id, 0, 0, 0⟩
  mastery := []
  phase := .idle
  history := []
  intents := []
  consumedActions := ∅

/-- The roll of a shift.  It reads the drawn schedule; the `0` is the out-of-range
default and `every_shift_below_the_ceiling_reads_a_drawn_roll` says it is never the
answer for a shift the campaign can be at. -/
def hazardAt (activation : Activation) (shift : Nat) : Nat :=
  (activation.schedule[shift]?).getD 0

theorem every_shift_below_the_ceiling_reads_a_drawn_roll (activation : Activation)
    (shift : Nat) (below : shift < activation.config.raw.maxShifts) :
    activation.schedule[shift]? = some (hazardAt activation shift) := by
  have index : shift < activation.schedule.length := by
    rw [an_activation_has_one_roll_per_authored_shift]
    exact below
  rw [List.getElem?_eq_getElem index]
  simp only [hazardAt, List.getElem?_eq_getElem index, Option.getD_some]

/-- And the roll is a face, so a `riskThreshold` of `HAZARD_FACES` cannot be met. -/
theorem every_roll_a_watch_can_read_is_below_the_face_count (activation : Activation)
    (shift : Nat) (below : shift < activation.config.raw.maxShifts) :
    hazardAt activation shift < HAZARD_FACES := by
  have index : shift < activation.schedule.length := by
    rw [an_activation_has_one_roll_per_authored_shift]
    exact below
  have member : hazardAt activation shift ∈ activation.schedule := by
    have read := every_shift_below_the_ceiling_reads_a_drawn_roll activation shift below
    rw [List.getElem?_eq_getElem index] at read
    have value : activation.schedule[shift] = hazardAt activation shift :=
      Option.some.inj read
    exact value ▸ List.getElem_mem index
  rw [activation.schedule_derived] at member
  exact every_hazard_roll_is_below_the_face_count _ _ _ member

inductive Action where
  | claimOfficer (actor : Digest32) (seat : SeatId)
  | chooseTask (station : Station) (task : Task)
  | resolve
  | debrief
deriving DecidableEq

structure Command where
  sequence : Nat
  nullifier : Digest32
  action : Action
deriving DecidableEq

/-- UI-only holder metadata.  It has no power field. -/
structure HolderPresentation where
  eligible : Bool
  affordance : Option ShipLifeProgression.HolderAffordance
deriving DecidableEq

/-- Raw client submission.  Any claimed semantic output causes admission to
fail; holder presentation is erased. -/
structure SubmittedCommand where
  command : Command
  claimedContribution : Option ContributionDelta := none
  claimedWorldEffects : Option WorldEffects := none
  claimedSafe : Option Bool := none
  claimedCanonArtifact : Option ContentContract.ArtifactId := none
  holder : Option HolderPresentation := none
deriving DecidableEq

def SubmittedCommand.admit? (submitted : SubmittedCommand) : Option Command := do
  if submitted.claimedContribution.isSome then none
  if submitted.claimedWorldEffects.isSome then none
  if submitted.claimedSafe.isSome then none
  if submitted.claimedCanonArtifact.isSome then none
  some submitted.command

theorem holder_presentation_erased (command : Command)
    (left right : Option HolderPresentation) :
    ({ command, holder := left : SubmittedCommand }).admit? =
      ({ command, holder := right : SubmittedCommand }).admit? := rfl

inductive Error where
  | wrongSequence
  | replayedAction
  | shiftLimit
  | wrongPhase
  | unknownOfficer
  | officerActorMismatch
  | unknownTask
  | roleMismatch
  | insufficientResources
  | evidenceBound
  | missingHealth
  | historyLimit
  | callerAuthoredOutcome
deriving DecidableEq, Repr

private def progressionOf (rule : TaskRule) (success : Bool)
    (before after : OfficerHealth) : ProgressionEffect where
  maintenanceSuccess :=
    if success && (rule.station = .engineSpine || rule.station = .galley) then 1 else 0
  meaningfulFailure := if success then 0 else 1
  trainingObserved := 1
  recoveryObserved :=
    if after.wounds < before.wounds || after.strain < before.strain then 1 else 0

/-- Two recovery counters exist — the running one on the officer row, maintained by
`OfficerHealth.apply`, and the per-watch one `progressionOf` derives by comparing before
against after — and this says they read the same fact, so the row advances by exactly
what the watch reports.  While `OfficerHealth.apply` counted the ATTEMPT rather than the
EFFECT, the two disagreed on every recovery that recovered nothing. -/
theorem the_two_recovery_counters_agree (rule : TaskRule) (success : Bool)
    (before : OfficerHealth) (effect : HealthEffect) :
    (before.apply effect).recoveryObserved =
      before.recoveryObserved +
        (progressionOf rule success before (before.apply effect)).recoveryObserved := rfl

private def resolveAssigned (activation : Activation) (state : State)
    (officer : Seat) (rule : TaskRule) : Except Error State := do
  let healthBefore ← match healthFor? state.health officer.id with
    | none => throw .missingHealth
    | some health => pure health
  let roll := hazardAt activation state.shift
  let success := decide (rule.riskThreshold ≤ roll)
  let contribution := if success then rule.successContribution else rule.failureContribution
  let effects := if success then rule.successEffects else rule.failureEffects
  let healthEffect := if success then rule.successHealth else rule.failureHealth
  let evidenceGain := if success then rule.successEvidence else rule.failureEvidence
  -- No bound re-check follows this: `apply?` ends `if !after.boundedB then none else
  -- some after`, so `resourcesAfter` is bounded by construction and the `none` arm is the
  -- only reachable refusal.  That is
  -- `NightWatchCampaignExamples.worldEffects_apply_returns_only_bounded_resources`.
  let resourcesAfter ← match effects.apply? state.resources with
    | none => throw .insufficientResources
    | some resources => pure resources
  if MAX_EVIDENCE < state.evidence + evidenceGain then throw .evidenceBound
  let evidenceAfter := state.evidence + evidenceGain
  let healthAfter := healthBefore.apply healthEffect
  let betaProposal :=
    if success && rule.discoveryEvidenceRequired ≤ evidenceAfter then
      rule.betaDiscovery.map fun artifact => {
        sourceShift := state.shift
        officer := officer.playerKey
        artifact
        evidence := evidenceAfter
        taskContentId := rule.taskContentId
      }
    else none
  let resolved : ResolvedShift := {
    shift := state.shift
    officer
    rule
    hazardRoll := roll
    success
    contribution
    worldEffects := effects
    resourcesBefore := state.resources
    resourcesAfter
    healthBefore
    healthAfter
    evidenceBefore := state.evidence
    evidenceAfter
    betaProposal
    progression := progressionOf rule success healthBefore healthAfter
  }
  pure { state with
    resources := resourcesAfter
    evidence := evidenceAfter
    health := setHealth state.health healthAfter
    phase := .awaitingDebrief resolved }

private def debriefResolved (activation : Activation) (state : State)
    (resolved : ResolvedShift) : Except Error State := do
  if state.history.length ≥ MAX_HISTORY then throw .historyLimit
  let masteryBefore := masteryFor state.mastery resolved.officer.id resolved.rule.station
  let xp := masteryBefore.xp + resolved.contribution.score + 1
  let masteryAfter : MasteryRow := {
    masteryBefore with xp, level := xp / MASTERY_LEVEL_SIZE }
  let localService := if resolved.rule.station = .galley then
    some resolved.rule.localService else none
  let terminalContentId := if resolved.success then
    resolved.rule.successContentId else resolved.rule.failureContentId
  let entry : LogbookEntry := {
    shift := resolved.shift
    officer := resolved.officer.playerKey
    seat := resolved.officer.id
    role := resolved.officer.role
    participation := .principal
    station := resolved.rule.station
    task := resolved.rule.task
    success := resolved.success
    hazardRoll := resolved.hazardRoll
    riskThreshold := resolved.rule.riskThreshold
    contribution := resolved.contribution
    worldEffects := resolved.worldEffects
    resourcesBefore := resolved.resourcesBefore
    resourcesAfter := resolved.resourcesAfter
    healthBefore := resolved.healthBefore.progressionView
    healthAfter := resolved.healthAfter.progressionView
    evidenceBefore := resolved.evidenceBefore
    evidenceAfter := resolved.evidenceAfter
    masteryBefore
    masteryAfter
    galleyLocalService := localService
    betaProposal := resolved.betaProposal
    progression := resolved.progression
    terminalContentId
  }
  let intent : EventIntent := {
    stream := activation.config.raw.logStream
    expectedSequence := state.history.length + 1
    entry
  }
  pure { state with
    shift := state.shift + 1
    mastery := setMastery state.mastery masteryAfter
    phase := .idle
    history := state.history ++ [entry]
    intents := state.intents ++ [intent] }

private def applyAction (activation : Activation) (state : State)
    (action : Action) : Except Error State :=
  match action, state.phase with
  | .claimOfficer actor seatId, .idle => do
      if state.shift ≥ activation.config.raw.maxShifts then throw .shiftLimit
      let officer ← match findSeat? activation.config.raw.roster seatId with
        | none => throw .unknownOfficer
        | some officer => pure officer
      if actor ≠ officer.playerKey then throw .officerActorMismatch
      pure { state with phase := .claimed officer }
  | .chooseTask station task, .claimed officer => do
      let rule ← match findRule? activation.config.raw.rules station task with
        | none => throw .unknownTask
        | some rule => pure rule
      if officer.role ≠ rule.role then throw .roleMismatch
      pure { state with phase := .assigned officer rule }
  | .resolve, .assigned officer rule => resolveAssigned activation state officer rule
  | .debrief, .awaitingDebrief resolved => debriefResolved activation state resolved
  | _, _ => .error .wrongPhase

/-- The canonical semantic judge.  Sequence and nullifier advance even for a
meaningful risk failure, but never for a refused command.

⚠ It takes an `Activation`, not a `Config`: there is no way to judge a watch whose
hazard schedule did not come out of a secret opening the config's own commitment. -/
def judge (activation : Activation) (state : State) (command : Command) :
    Except Error State := do
  if command.sequence ≠ state.sequence then throw .wrongSequence
  if command.nullifier ∈ state.consumedActions then throw .replayedAction
  let next ← applyAction activation state command.action
  pure { next with
    sequence := state.sequence + 1
    consumedActions := insert command.nullifier state.consumedActions }

def judgeSubmitted (activation : Activation) (state : State)
    (submitted : SubmittedCommand) : Except Error State :=
  match submitted.admit? with
  | none => .error .callerAuthoredOutcome
  | some command => judge activation state command

theorem holder_status_cannot_change_transition (activation : Activation) (state : State)
    (command : Command) (left right : Option HolderPresentation) :
    judgeSubmitted activation state { command, holder := left } =
      judgeSubmitted activation state { command, holder := right } := rfl

def replay (activation : Activation) : State → List Command → Except Error State
  | state, [] => .ok state
  | state, command :: commands => do
      let next ← judge activation state command
      replay activation next commands

theorem replay_append (activation : Activation) (state : State)
    (left right : List Command) :
    replay activation state (left ++ right) = (do
      let middle ← replay activation state left
      replay activation middle right) := by
  induction left generalizing state with
  | nil => rfl
  | cons command commands ih =>
      simp only [List.cons_append, replay]
      cases judge activation state command <;> simp [ih]

theorem replay_deterministic (activation : Activation) (state : State)
    (commands : List Command) {left right : State}
    (hl : replay activation state commands = .ok left)
    (hr : replay activation state commands = .ok right) : left = right := by
  rw [hl] at hr
  exact Except.ok.inj hr

theorem caller_claimed_outcome_is_refused (activation : Activation) (state : State)
    (command : Command) (claimed : ContributionDelta) :
    judgeSubmitted activation state {
      command
      claimedContribution := some claimed
    } = .error .callerAuthoredOutcome := by
  rfl

#assert_axioms the_hazard_domain_is_distinct_from_the_commit_and_derive_domains
#assert_axioms drawing_below_the_face_count_consumes_exactly_one_byte
#assert_axioms hazard_stream_is_thirty_two_bytes_per_block
#assert_axioms hazard_stream_supplies_at_least_one_byte_per_shift
#assert_axioms drawRolls_length
#assert_axioms hazard_schedule_has_exactly_one_roll_per_shift
#assert_axioms every_hazard_roll_is_below_the_face_count
#assert_axioms activate_preserves_the_raw_config
#assert_axioms admitted_activation_carries_the_config_it_was_admitted_against
#assert_axioms an_activation_has_one_roll_per_authored_shift
#assert_axioms every_shift_below_the_ceiling_reads_a_drawn_roll
#assert_axioms every_roll_a_watch_can_read_is_below_the_face_count
#assert_axioms officer_health_counts_the_recovery_that_happened
#assert_axioms a_recovery_that_moves_no_health_does_not_move_the_recovery_counter
#assert_axioms a_recovery_that_moves_health_increments_the_recovery_counter
#assert_axioms an_unhurt_officer_offered_a_recovery_moves_nothing_at_all
#assert_axioms a_wounded_officer_offered_the_same_recovery_heals_and_is_counted
#assert_axioms the_two_recovery_counters_agree
#assert_axioms event_intent_has_no_finality
#assert_axioms holder_presentation_erased
#assert_axioms holder_status_cannot_change_transition
#assert_axioms replay_append
#assert_axioms replay_deterministic
#assert_axioms caller_claimed_outcome_is_refused

end Dregg2.Games.PathOfAngels.NightWatchCampaign
