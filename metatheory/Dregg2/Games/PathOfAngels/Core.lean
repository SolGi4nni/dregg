/-
# Dregg2.Games.PathOfAngels.Core — the shared semantic envelope for PoA games.

The games are deliberately smaller than the world they feed.  A game may return a
bounded contribution and an exact beta artifact; it cannot manufacture unbounded
world state, choose a different mission after play, or silently clip an overflow.
Every conversion from wire-shaped naturals is checked and returns `none` on the
first violated bound.

Canon authority is kept out of this module.  It lives in `Canon.lean`, so a game
module importing only `Core` has no promotion operation in scope.
-/
import Mathlib.Data.Finset.Card
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels

/-! ## Stable identifiers and exact artifacts -/

structure MissionId where
  value : Nat
deriving DecidableEq, Repr

structure RelicId where
  value : Nat
deriving DecidableEq, Repr

structure ArtifactId where
  value : Nat
deriving DecidableEq, Repr

structure EpochId where
  value : Nat
deriving DecidableEq, Repr

/-- A digest has exactly 32 bytes by construction.  The list is the wire
projection; the equality proof is erased by emitters. -/
structure Digest32 where
  bytes : List (Fin 256)
  length_eq : bytes.length = 32
deriving DecidableEq

/-- The identity promoted into canon.  Both the authored source and the emitted
content are named, so promotion cannot drift from the reviewed object to a later
artifact carrying the same display id. -/
structure ArtifactRef where
  missionId    : MissionId
  artifactId   : ArtifactId
  sourceDigest : Digest32
  contentDigest : Digest32
deriving DecidableEq

inductive PrivacyGrade where
  | «public»
  | operatorVisibleHidingFri
  | processSeparatedThreshold
  | independentOperatorThreshold
deriving DecidableEq, Repr

inductive BallotRegime where
  | none
  | onePlayerOneVoice
  | oneWalletOneVoice
  | cappedChoir
  | predictionOracle
deriving DecidableEq, Repr

/-! ## Contributions -/

/-- One game cannot move a world meter by more than this in one receipted result. -/
abbrev METRIC_LIMIT : Nat := 1_000_000

/-- A single result may name at most this many newly encountered relics. -/
abbrev RELIC_LIMIT : Nat := 64

/-- A mission may predeclare a larger catalogue than one run can return. -/
abbrev MISSION_RELIC_LIMIT : Nat := 4096

/-- A meter is bounded in its type, rather than by a comment on a `Nat`. -/
abbrev Metric := Fin (METRIC_LIMIT + 1)

/-- Wire-shaped contribution.  This is never applied directly. -/
structure RawContribution where
  intel     : Nat
  supplies  : Nat
  cohesion  : Nat
  influence : Nat
  score     : Nat
  relics    : List RelicId
deriving DecidableEq, Repr

/-- Checked game output.  The five meters and the relic population are bounded. -/
structure Contribution where
  intel     : Metric
  supplies  : Metric
  cohesion  : Metric
  influence : Metric
  score     : Metric
  relics    : Finset RelicId
  relics_bounded : relics.card ≤ RELIC_LIMIT
deriving DecidableEq

/-- The empty contribution, used by games whose legal terminal state changes no
shared meter. -/
def Contribution.zero : Contribution where
  intel := 0
  supplies := 0
  cohesion := 0
  influence := 0
  score := 0
  relics := ∅
  relics_bounded := by simp

/-- Fail-closed conversion from wire values to the bounded semantic type.
Duplicate relic ids are rejected rather than silently deduplicated. -/
def validateContribution (raw : RawContribution) : Option Contribution :=
  if hi : raw.intel ≤ METRIC_LIMIT then
    if hs : raw.supplies ≤ METRIC_LIMIT then
      if hc : raw.cohesion ≤ METRIC_LIMIT then
        if hf : raw.influence ≤ METRIC_LIMIT then
          if hsc : raw.score ≤ METRIC_LIMIT then
            if _hn : raw.relics.Nodup then
              let rs := raw.relics.toFinset
              if hr : rs.card ≤ RELIC_LIMIT then
                some {
                  intel := ⟨raw.intel, Nat.lt_succ_of_le hi⟩
                  supplies := ⟨raw.supplies, Nat.lt_succ_of_le hs⟩
                  cohesion := ⟨raw.cohesion, Nat.lt_succ_of_le hc⟩
                  influence := ⟨raw.influence, Nat.lt_succ_of_le hf⟩
                  score := ⟨raw.score, Nat.lt_succ_of_le hsc⟩
                  relics := rs
                  relics_bounded := hr
                }
              else none
            else none
          else none
        else none
      else none
    else none
  else none

theorem validateContribution_intel_bound {raw : RawContribution} {c : Contribution}
    (h : validateContribution raw = some c) : raw.intel ≤ METRIC_LIMIT := by
  simp only [validateContribution] at h
  split at h <;> simp_all

theorem validateContribution_supplies_bound {raw : RawContribution} {c : Contribution}
    (h : validateContribution raw = some c) : raw.supplies ≤ METRIC_LIMIT := by
  by_contra hn
  have hz : validateContribution raw = none := by
    simp [validateContribution, hn]
  rw [hz] at h
  simp at h

theorem validateContribution_rejects_intel_overflow (raw : RawContribution)
    (h : METRIC_LIMIT < raw.intel) : validateContribution raw = none := by
  simp [validateContribution, Nat.not_le.mpr h]

theorem validateContribution_rejects_duplicate_relics (raw : RawContribution)
    (h : ¬ raw.relics.Nodup) : validateContribution raw = none := by
  simp [validateContribution, h]

/-- Exact addition of two bounded meters.  Overflow refuses; it never saturates. -/
def checkedAddMetric (a b : Metric) : Option Metric :=
  if h : a.val + b.val ≤ METRIC_LIMIT then
    some ⟨a.val + b.val, Nat.lt_succ_of_le h⟩
  else none

theorem checkedAddMetric_comm (a b : Metric) :
    checkedAddMetric a b = checkedAddMetric b a := by
  simp only [checkedAddMetric, add_comm]

theorem checkedAddMetric_eq_some_iff (a b c : Metric) :
    checkedAddMetric a b = some c ↔ a.val + b.val = c.val := by
  simp only [checkedAddMetric]
  split <;> rename_i h
  · constructor
    · intro heq
      injection heq with hv
      exact congrArg Fin.val hv
    · intro hv
      congr 1
      exact Fin.ext hv
  · constructor
    · simp
    · intro hv
      exfalso
      apply h
      rw [hv]
      exact Nat.lt_succ_iff.mp c.isLt

/-- Merge two game results.  Every numeric component adds exactly and the relic set
unions exactly; any meter or relic-population overflow refuses the whole merge. -/
def Contribution.merge (a b : Contribution) : Option Contribution := do
  let intel ← checkedAddMetric a.intel b.intel
  let supplies ← checkedAddMetric a.supplies b.supplies
  let cohesion ← checkedAddMetric a.cohesion b.cohesion
  let influence ← checkedAddMetric a.influence b.influence
  let score ← checkedAddMetric a.score b.score
  let relics := a.relics ∪ b.relics
  if h : relics.card ≤ RELIC_LIMIT then
    some { intel, supplies, cohesion, influence, score, relics, relics_bounded := h }
  else none

theorem Contribution.merge_comm (a b : Contribution) :
    a.merge b = b.merge a := by
  simp only [Contribution.merge, checkedAddMetric_comm, Finset.union_comm]

theorem Contribution.merge_intel_exact {a b c : Contribution}
    (h : a.merge b = some c) : c.intel.val = a.intel.val + b.intel.val := by
  simp only [Contribution.merge, checkedAddMetric] at h
  split_ifs at h <;> try contradiction
  cases h
  rfl

/-! ## Mission declarations and bounded world state -/

/-- Per-mission ceiling.  A mission may choose any cap no larger than the platform
ceiling; it cannot widen the platform type. -/
structure ContributionBudget where
  intel     : Metric
  supplies  : Metric
  cohesion  : Metric
  influence : Metric
  score     : Metric
  relics    : Fin (RELIC_LIMIT + 1)
deriving DecidableEq

/-- A mission commits to the exact artifact whose state machine produced its result. -/
structure MissionSpec where
  missionId : MissionId
  artifact  : ArtifactRef
  epoch     : EpochId
  federationId : Digest32
  /-- Root of emitted game programs/assets only.  Its preimage excludes the catalog
  and manifest envelopes, so this field is not a self-referential manifest hash. -/
  contentRoot : Digest32
  /-- Digest of the detached signed activation envelope.  This is filled only when
  the mission template is activated; it is excluded from emitted contentRoot input. -/
  activationDigest : Digest32
  contentSession : Digest32
  runSeed : Digest32
  budget    : ContributionBudget
  allowedRelics : Finset RelicId
  privacy   : PrivacyGrade
  ballot    : BallotRegime
  artifact_matches : artifact.missionId = missionId
  allowed_relics_bounded : allowedRelics.card ≤ MISSION_RELIC_LIMIT
deriving DecidableEq

/-- The contribution lies under the mission's predeclared ceiling. -/
def Contribution.within (c : Contribution) (b : ContributionBudget) : Bool :=
  decide (
    c.intel.val ≤ b.intel.val ∧
    c.supplies.val ≤ b.supplies.val ∧
    c.cohesion.val ≤ b.cohesion.val ∧
    c.influence.val ≤ b.influence.val ∧
    c.score.val ≤ b.score.val ∧
    c.relics.card ≤ b.relics.val)

theorem Contribution.within_eq_true_iff (c : Contribution) (b : ContributionBudget) :
    c.within b = true ↔
      c.intel.val ≤ b.intel.val ∧
      c.supplies.val ≤ b.supplies.val ∧
      c.cohesion.val ≤ b.cohesion.val ∧
      c.influence.val ≤ b.influence.val ∧
      c.score.val ≤ b.score.val ∧
      c.relics.card ≤ b.relics.val := by
  simp [Contribution.within]

/-- A result is accepted only when both its quantities and the identities it names
were declared before play.  The allowlist clause prevents a game from inventing a
new `RelicId` while remaining under the numeric count ceiling. -/
def MissionSpec.acceptsContribution (mission : MissionSpec) (c : Contribution) : Bool :=
  c.within mission.budget && decide (c.relics ⊆ mission.allowedRelics)

theorem MissionSpec.acceptsContribution_eq_true_iff
    (mission : MissionSpec) (c : Contribution) :
    mission.acceptsContribution c = true ↔
      c.within mission.budget = true ∧ c.relics ⊆ mission.allowedRelics := by
  simp [MissionSpec.acceptsContribution]

abbrev WORLD_RELIC_LIMIT : Nat := 4096
abbrev BETA_ARTIFACT_LIMIT : Nat := 4096

/-- The small shared state games are allowed to move.  Narrative branches and alpha
canon are intentionally absent. -/
structure WorldState where
  intel     : Metric
  supplies  : Metric
  cohesion  : Metric
  influence : Metric
  score     : Metric
  discoveredRelics : Finset RelicId
  betaArtifacts : Finset ArtifactRef
  sequence : Nat
  relics_bounded : discoveredRelics.card ≤ WORLD_RELIC_LIMIT
  beta_bounded : betaArtifacts.card ≤ BETA_ARTIFACT_LIMIT
deriving DecidableEq

def WorldState.empty : WorldState where
  intel := 0
  supplies := 0
  cohesion := 0
  influence := 0
  score := 0
  discoveredRelics := ∅
  betaArtifacts := ∅
  sequence := 0
  relics_bounded := by simp
  beta_bounded := by simp

/-- The complete decidable admission predicate for a world update.  It is named
separately so every refusal arm is visible without expanding an `Option` program. -/
def ApplyChecks (mission : MissionSpec) (c : Contribution) (world : WorldState) : Bool :=
  mission.acceptsContribution c &&
  decide (world.intel.val + c.intel.val ≤ METRIC_LIMIT) &&
  decide (world.supplies.val + c.supplies.val ≤ METRIC_LIMIT) &&
  decide (world.cohesion.val + c.cohesion.val ≤ METRIC_LIMIT) &&
  decide (world.influence.val + c.influence.val ≤ METRIC_LIMIT) &&
  decide (world.score.val + c.score.val ≤ METRIC_LIMIT) &&
  decide ((world.discoveredRelics ∪ c.relics).card ≤ WORLD_RELIC_LIMIT) &&
  decide ((insert mission.artifact world.betaArtifacts).card ≤ BETA_ARTIFACT_LIMIT)

theorem ApplyChecks_eq_true_iff (mission : MissionSpec) (c : Contribution)
    (world : WorldState) : ApplyChecks mission c world = true ↔
      mission.acceptsContribution c = true ∧
      world.intel.val + c.intel.val ≤ METRIC_LIMIT ∧
      world.supplies.val + c.supplies.val ≤ METRIC_LIMIT ∧
      world.cohesion.val + c.cohesion.val ≤ METRIC_LIMIT ∧
      world.influence.val + c.influence.val ≤ METRIC_LIMIT ∧
      world.score.val + c.score.val ≤ METRIC_LIMIT ∧
      (world.discoveredRelics ∪ c.relics).card ≤ WORLD_RELIC_LIMIT ∧
      (insert mission.artifact world.betaArtifacts).card ≤ BETA_ARTIFACT_LIMIT := by
  simp only [ApplyChecks, Bool.and_eq_true, decide_eq_true_eq]
  tauto

/-- Apply one contribution atomically.  Mission-budget failure, an undeclared relic,
meter overflow, world relic overflow, or beta-artifact overflow all return `none`. -/
def applyContribution (mission : MissionSpec) (c : Contribution)
    (world : WorldState) : Option WorldState :=
  if h : ApplyChecks mission c world = true then
    let hw := (ApplyChecks_eq_true_iff mission c world).mp h
    some {
      intel := ⟨world.intel.val + c.intel.val, Nat.lt_succ_of_le hw.2.1⟩
      supplies := ⟨world.supplies.val + c.supplies.val, Nat.lt_succ_of_le hw.2.2.1⟩
      cohesion := ⟨world.cohesion.val + c.cohesion.val, Nat.lt_succ_of_le hw.2.2.2.1⟩
      influence := ⟨world.influence.val + c.influence.val,
        Nat.lt_succ_of_le hw.2.2.2.2.1⟩
      score := ⟨world.score.val + c.score.val, Nat.lt_succ_of_le hw.2.2.2.2.2.1⟩
      discoveredRelics := world.discoveredRelics ∪ c.relics
      betaArtifacts := insert mission.artifact world.betaArtifacts
      sequence := world.sequence + 1
      relics_bounded := hw.2.2.2.2.2.2.1
      beta_bounded := hw.2.2.2.2.2.2.2
    }
  else none

theorem applyContribution_sequence {mission : MissionSpec} {c : Contribution}
    {before after : WorldState} (h : applyContribution mission c before = some after) :
    after.sequence = before.sequence + 1 := by
  unfold applyContribution at h
  split at h
  · injection h with heq
    rw [← heq]
  · contradiction

theorem applyContribution_records_exact_artifact {mission : MissionSpec} {c : Contribution}
    {before after : WorldState} (h : applyContribution mission c before = some after) :
    mission.artifact ∈ after.betaArtifacts := by
  unfold applyContribution at h
  split at h
  · injection h with heq
    rw [← heq]
    simp
  · contradiction

theorem applyContribution_respects_budget {mission : MissionSpec} {c : Contribution}
    {before after : WorldState} (h : applyContribution mission c before = some after) :
    c.within mission.budget = true := by
  unfold applyContribution at h
  split at h
  · rename_i hc
    have hw := (ApplyChecks_eq_true_iff mission c before).mp hc
    exact (MissionSpec.acceptsContribution_eq_true_iff mission c).mp hw.1 |>.1
  · contradiction

theorem applyContribution_relics_predeclared {mission : MissionSpec} {c : Contribution}
    {before after : WorldState} (h : applyContribution mission c before = some after) :
    c.relics ⊆ mission.allowedRelics := by
  have ha : mission.acceptsContribution c = true := by
    unfold applyContribution at h
    split at h
    · rename_i hc
      exact (ApplyChecks_eq_true_iff mission c before).mp hc |>.1
    · contradiction
  exact (MissionSpec.acceptsContribution_eq_true_iff mission c).mp ha |>.2

/-- The receipt envelope returned by a game executor.  Its constructor carries the
actual checked transition: there is no receipt-shaped value whose pre/post worlds are
unrelated to `applyContribution`. -/
structure RunReceipt where
  mission : MissionSpec
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  actorRoot : Digest32
  playerKey : Digest32
  previousPlayerCounter : Nat
  playerCounter : Nat
  runSeed : Digest32
  preWorld : WorldState
  postWorld : WorldState
  contribution : Contribution
  transcriptDigest : Digest32
  federation_matches : federationId = mission.federationId
  content_root_matches : contentRoot = mission.contentRoot
  activation_matches : activationDigest = mission.activationDigest
  content_session_matches : contentSession = mission.contentSession
  content_epoch_matches : contentEpoch = mission.epoch
  run_seed_matches : runSeed = mission.runSeed
  player_counter_advances : playerCounter = previousPlayerCounter + 1
  applied : applyContribution mission contribution preWorld = some postWorld

theorem RunReceipt.sequence_advances (receipt : RunReceipt) :
    receipt.postWorld.sequence = receipt.preWorld.sequence + 1 :=
  applyContribution_sequence receipt.applied

theorem RunReceipt.records_exact_artifact (receipt : RunReceipt) :
    receipt.mission.artifact ∈ receipt.postWorld.betaArtifacts :=
  applyContribution_records_exact_artifact receipt.applied

theorem RunReceipt.player_counter_positive (receipt : RunReceipt) :
    0 < receipt.playerCounter := by
  rw [receipt.player_counter_advances]
  omega

/-- Replay identity for a judged run.  Mutable transcript material is intentionally
absent: counter consumption is domain-, session-, epoch-, player-, and counter-specific. -/
structure ReceiptKey where
  federationId : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  playerKey : Digest32
  playerCounter : Nat
deriving DecidableEq

/-- The per-player namespace whose last accepted counter canon remembers. -/
structure PlayerCounterKey where
  federationId : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  playerKey : Digest32
deriving DecidableEq

def RunReceipt.key (receipt : RunReceipt) : ReceiptKey where
  federationId := receipt.federationId
  contentSession := receipt.contentSession
  contentEpoch := receipt.contentEpoch
  playerKey := receipt.playerKey
  playerCounter := receipt.playerCounter

def RunReceipt.counterKey (receipt : RunReceipt) : PlayerCounterKey where
  federationId := receipt.federationId
  contentSession := receipt.contentSession
  contentEpoch := receipt.contentEpoch
  playerKey := receipt.playerKey

#assert_axioms validateContribution_intel_bound
#assert_axioms validateContribution_supplies_bound
#assert_axioms validateContribution_rejects_intel_overflow
#assert_axioms validateContribution_rejects_duplicate_relics
#assert_axioms checkedAddMetric_comm
#assert_axioms checkedAddMetric_eq_some_iff
#assert_axioms Contribution.merge_comm
#assert_axioms Contribution.merge_intel_exact
#assert_axioms Contribution.within_eq_true_iff
#assert_axioms MissionSpec.acceptsContribution_eq_true_iff
#assert_axioms ApplyChecks_eq_true_iff
#assert_axioms applyContribution_sequence
#assert_axioms applyContribution_records_exact_artifact
#assert_axioms applyContribution_respects_budget
#assert_axioms applyContribution_relics_predeclared
#assert_axioms RunReceipt.sequence_advances
#assert_axioms RunReceipt.records_exact_artifact
#assert_axioms RunReceipt.player_counter_positive

end Dregg2.Games.PathOfAngels
