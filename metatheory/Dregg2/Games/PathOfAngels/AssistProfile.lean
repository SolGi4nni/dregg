/-
# Assist profiles — presentation freedom, semantic commitment, fair comparison

Presentation assists never enter a game's semantic configuration or judge input.
Anything that changes available actions, information, undo semantics, or problem
shape is a `SemanticAssistProfile`, is committed beside the exact `MissionSpec`
before activation, and is fixed by the type index of an active run.

League policy is explicit: eligible runs retain their raw score unchanged and are
comparable only inside the same mission, semantic profile, profile digest, and
effective-config digest.  Practice-only profiles are excluded rather than silently
penalized.
-/
import Dregg2.Games.PathOfAngels.Judged
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.AssistProfile

open Dregg2.Games.PathOfAngels

/-! ## Presentation-only preferences -/

structure PresentationAssists where
  highContrast : Bool := false
  reducedMotion : Bool := false
  largeTargets : Bool := false
  screenReaderLabels : Bool := false
  redundantAudioCues : Bool := false
deriving DecidableEq, Repr

/-! ## Explicit semantic assists -/

abbrev MAX_ACTION_BUDGET : Nat := 64

inductive HintPolicy where
  | none
  | singleClue
  | guided
deriving DecidableEq, Repr

inductive UndoPolicy where
  | disabled
  | singleAction
deriving DecidableEq, Repr

inductive SimplificationPolicy where
  | standard
  | reducedChoices
  | reducedObjective
deriving DecidableEq, Repr

structure SemanticAssistProfile where
  actionBudget : Fin (MAX_ACTION_BUDGET + 1)
  action_budget_positive : 0 < actionBudget.val
  hint : HintPolicy
  undo : UndoPolicy
  simplification : SimplificationPolicy
deriving DecidableEq

def SemanticAssistProfile.standard (actionBudget : Fin (MAX_ACTION_BUDGET + 1))
    (positive : 0 < actionBudget.val) : SemanticAssistProfile :=
  { actionBudget
    action_budget_positive := positive
    hint := .none
    undo := .disabled
    simplification := .standard }

/-! ## Fail-closed wire validation -/

structure RawSemanticAssistProfile where
  schemaVersion : Nat
  actionBudget : Nat
  hintTag : Nat
  undoTag : Nat
  simplificationTag : Nat
deriving DecidableEq, Repr

private def validateHint : Nat → Option HintPolicy
  | 0 => some .none
  | 1 => some .singleClue
  | 2 => some .guided
  | _ => none

private def validateUndo : Nat → Option UndoPolicy
  | 0 => some .disabled
  | 1 => some .singleAction
  | _ => none

private def validateSimplification : Nat → Option SimplificationPolicy
  | 0 => some .standard
  | 1 => some .reducedChoices
  | 2 => some .reducedObjective
  | _ => none

/-- Unknown versions/tags, zero budgets, and oversized budgets all refuse. -/
def validateSemanticAssistProfile (raw : RawSemanticAssistProfile) :
    Option SemanticAssistProfile := do
  if raw.schemaVersion != 1 then none else
  if hpositive : 0 < raw.actionBudget then
    if hbound : raw.actionBudget ≤ MAX_ACTION_BUDGET then
      let hint ← validateHint raw.hintTag
      let undo ← validateUndo raw.undoTag
      let simplification ← validateSimplification raw.simplificationTag
      some {
        actionBudget := ⟨raw.actionBudget, Nat.lt_succ_of_le hbound⟩
        action_budget_positive := hpositive
        hint
        undo
        simplification
      }
    else none
  else none

private def validateByte (value : Nat) : Option (Fin 256) :=
  if h : value < 256 then some ⟨value, h⟩ else none

/-- Digest bytes arrive as naturals at the wire boundary; length and every byte
are checked before constructing Core's proof-carrying `Digest32`. -/
def validateDigest32 (raw : List Nat) : Option Digest32 := do
  let bytes ← raw.mapM validateByte
  if h : bytes.length = 32 then some { bytes, length_eq := h } else none

/-! ## Pre-activation semantic commitment -/

abbrev DigestOracle := List Nat → Digest32

def hintTag : HintPolicy → Nat
  | .none => 0
  | .singleClue => 1
  | .guided => 2

def undoTag : UndoPolicy → Nat
  | .disabled => 0
  | .singleAction => 1

def simplificationTag : SimplificationPolicy → Nat
  | .standard => 0
  | .reducedChoices => 1
  | .reducedObjective => 2

/-- Canonical semantic transcript under the assist-profile domain. -/
def profileTranscript (profile : SemanticAssistProfile) : List Nat :=
  [1, profile.actionBudget.val, hintTag profile.hint, undoTag profile.undo,
    simplificationTag profile.simplification]

/-- Fixed-field transcript for the effective mission/config.  Activation digest
is intentionally excluded: the assist config is committed before activation. -/
def effectiveConfigTranscript (mission : MissionSpec) (profile : SemanticAssistProfile) :
    List Nat :=
  [1, mission.missionId.value, mission.artifact.artifactId.value, mission.epoch.value] ++
  mission.federationId.bytes.map Fin.val ++
  mission.contentRoot.bytes.map Fin.val ++
  mission.contentSession.bytes.map Fin.val ++
  mission.runSeed.bytes.map Fin.val ++
  mission.artifact.sourceDigest.bytes.map Fin.val ++
  mission.artifact.contentDigest.bytes.map Fin.val ++
  profileTranscript profile

/-- Proof-carrying pre-activation config.  The two digest equalities prevent a
wire caller from labelling one profile/config with another profile's digests. -/
structure MissionAssistConfig (digest : DigestOracle) where
  mission : MissionSpec
  profile : SemanticAssistProfile
  profileDigest : Digest32
  effectiveConfigDigest : Digest32
  profile_digest_matches : profileDigest = digest (profileTranscript profile)
  config_digest_matches :
    effectiveConfigDigest = digest (effectiveConfigTranscript mission profile)

structure RawAssistCommitment where
  semantic : RawSemanticAssistProfile
  profileDigest : List Nat
  effectiveConfigDigest : List Nat
deriving DecidableEq, Repr

/-- The complete wire boundary refuses malformed semantics, malformed digests,
and well-shaped but wrongly labelled commitments. -/
def validateMissionAssistConfig (digest : DigestOracle) (mission : MissionSpec)
    (raw : RawAssistCommitment) : Option (MissionAssistConfig digest) := do
  let profile ← validateSemanticAssistProfile raw.semantic
  let profileDigest ← validateDigest32 raw.profileDigest
  let effectiveConfigDigest ← validateDigest32 raw.effectiveConfigDigest
  if hp : profileDigest = digest (profileTranscript profile) then
    if hc : effectiveConfigDigest = digest (effectiveConfigTranscript mission profile) then
      some {
        mission
        profile
        profileDigest
        effectiveConfigDigest
        profile_digest_matches := hp
        config_digest_matches := hc
      }
    else none
  else none

theorem validateMissionAssistConfig_success_mission {digest : DigestOracle}
    {mission : MissionSpec} {raw : RawAssistCommitment}
    {config : MissionAssistConfig digest}
    (h : validateMissionAssistConfig digest mission raw = some config) :
    config.mission = mission := by
  unfold validateMissionAssistConfig at h
  rcases Option.bind_eq_some_iff.mp h with ⟨profile, _hprofile, h⟩
  rcases Option.bind_eq_some_iff.mp h with ⟨profileDigest, _hprofileDigest, h⟩
  rcases Option.bind_eq_some_iff.mp h with
    ⟨effectiveConfigDigest, _heffectiveConfigDigest, h⟩
  split at h <;> rename_i hprofileMatch
  · split at h <;> rename_i hconfigMatch
    · exact (congrArg MissionAssistConfig.mission (Option.some.inj h)).symm
    · simp at h
  · simp at h

/-- A well-shaped digest with the wrong semantic preimage still refuses. -/
theorem validateMissionAssistConfig_rejects_profile_digest_mismatch
    (digest : DigestOracle) (mission : MissionSpec) (raw : RawAssistCommitment)
    (profile : SemanticAssistProfile) (profileDigest : Digest32)
    (hprofile : validateSemanticAssistProfile raw.semantic = some profile)
    (hdigest : validateDigest32 raw.profileDigest = some profileDigest)
    (hmismatch : profileDigest ≠ digest (profileTranscript profile)) :
    validateMissionAssistConfig digest mission raw = none := by
  simp [validateMissionAssistConfig, hprofile, hdigest, hmismatch]

/-- Matching the profile commitment cannot launder a wrong effective-config
commitment: the second check independently refuses. -/
theorem validateMissionAssistConfig_rejects_effective_digest_mismatch
    (digest : DigestOracle) (mission : MissionSpec) (raw : RawAssistCommitment)
    (profile : SemanticAssistProfile) (profileDigest effectiveConfigDigest : Digest32)
    (hprofile : validateSemanticAssistProfile raw.semantic = some profile)
    (hprofileDigest : validateDigest32 raw.profileDigest = some profileDigest)
    (hprofileMatch : profileDigest = digest (profileTranscript profile))
    (heffectiveDigest :
      validateDigest32 raw.effectiveConfigDigest = some effectiveConfigDigest)
    (hmismatch :
      effectiveConfigDigest ≠ digest (effectiveConfigTranscript mission profile)) :
    validateMissionAssistConfig digest mission raw = none := by
  simp [validateMissionAssistConfig, hprofile, hprofileDigest, heffectiveDigest,
    hprofileMatch, hmismatch]

/-! ## Activation and active-run immutability -/

/-- Executable activation evidence.  Its constructor is private: the public
issuer below must establish both that the assist commitment names the active
game's exact mission and that Judged's full carrying-turn admission passed. -/
structure AssistActivation {digest : DigestOracle}
    (config : MissionAssistConfig digest) where
  private mk ::
  active : ActiveRunState
  carrier : FinalizedCarrier
  claim : RunClaim
  mission_matches : active.game.mission = config.mission
  admitted : admissionChecks active carrier claim = true

/-- The only activation constructor surface.  This reuses the live judged-run
admission predicate rather than introducing a second, weaker authority check. -/
def validateAssistActivation {digest : DigestOracle}
    (config : MissionAssistConfig digest) (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) : Option (AssistActivation config) :=
  if hmission : active.game.mission = config.mission then
    if hadmitted : admissionChecks active carrier claim = true then
      some ⟨active, carrier, claim, hmission, hadmitted⟩
    else none
  else none

theorem validateAssistActivation_success_admitted {digest : DigestOracle}
    {config : MissionAssistConfig digest} {active : ActiveRunState}
    {carrier : FinalizedCarrier} {claim : RunClaim} {activation : AssistActivation config}
    (h : validateAssistActivation config active carrier claim = some activation) :
    admissionChecks active carrier claim = true := by
  simp only [validateAssistActivation] at h
  split at h <;> rename_i hmission
  · split at h <;> simp_all
  · simp at h

theorem validateAssistActivation_success_mission_matches {digest : DigestOracle}
    {config : MissionAssistConfig digest} {active : ActiveRunState}
    {carrier : FinalizedCarrier} {claim : RunClaim} {activation : AssistActivation config}
    (h : validateAssistActivation config active carrier claim = some activation) :
    active.game.mission = config.mission := by
  simp only [validateAssistActivation] at h
  split at h <;> rename_i hmission
  · exact hmission
  · simp at h

theorem validateAssistActivation_rejects_mission_mismatch {digest : DigestOracle}
    (config : MissionAssistConfig digest) (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim)
    (h : active.game.mission ≠ config.mission) :
    validateAssistActivation config active carrier claim = none := by
  simp [validateAssistActivation, h]

theorem validateAssistActivation_rejects_failed_admission {digest : DigestOracle}
    (config : MissionAssistConfig digest) (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim)
    (h : admissionChecks active carrier claim ≠ true) :
    validateAssistActivation config active carrier claim = none := by
  simp [validateAssistActivation, h]

structure SemanticJudgeInputs where
  mission : MissionSpec
  profile : SemanticAssistProfile
  profileDigest : Digest32
  effectiveConfigDigest : Digest32
deriving DecidableEq

structure PresentedConfig (digest : DigestOracle) where
  semantic : MissionAssistConfig digest
  presentation : PresentationAssists

def PresentedConfig.judgeInputs (config : PresentedConfig digest) : SemanticJudgeInputs :=
  { mission := config.semantic.mission
    profile := config.semantic.profile
    profileDigest := config.semantic.profileDigest
    effectiveConfigDigest := config.semantic.effectiveConfigDigest }

def PresentedConfig.withPresentation (config : PresentedConfig digest)
    (presentation : PresentationAssists) : PresentedConfig digest :=
  { semantic := config.semantic, presentation }

/-- Presentation changes erase before semantic config/judge projection. -/
theorem presentation_irrelevant_to_judge_inputs (config : PresentedConfig digest)
    (presentation : PresentationAssists) :
    (config.withPresentation presentation).judgeInputs = config.judgeInputs := rfl

structure ActiveRun {digest : DigestOracle} (config : MissionAssistConfig digest) where
  private mk ::
  activation : AssistActivation config
  presentation : PresentationAssists
  actionsUsed : Nat
  actions_within_budget : actionsUsed ≤ config.profile.actionBudget.val

inductive ActiveInput where
  | recordAction
  | setPresentation (presentation : PresentationAssists)
deriving DecidableEq, Repr

/-- A real initial state from checked activation evidence.  Because both
constructors are private, callers cannot manufacture an active run at a later
action count or without passing `validateAssistActivation`. -/
def startActiveRun {config : MissionAssistConfig digest}
    (activation : AssistActivation config) (presentation : PresentationAssists) :
    ActiveRun config :=
  ⟨activation, presentation, 0, Nat.zero_le _⟩

/-- There is deliberately no `setSemanticAssist` input.  The semantic config is
the type index; only presentation preferences can change mid-run. -/
def activeStep {config : MissionAssistConfig digest} (run : ActiveRun config) :
    ActiveInput → Option (ActiveRun config)
  | .setPresentation presentation => some { run with presentation }
  | .recordAction =>
      if h : run.actionsUsed < config.profile.actionBudget.val then
        some {
          run with
          actionsUsed := run.actionsUsed + 1
          actions_within_budget := Nat.succ_le_of_lt h
        }
      else none

def activeJudgeInputs {config : MissionAssistConfig digest} (_run : ActiveRun config) :
    SemanticJudgeInputs :=
  { mission := config.mission
    profile := config.profile
    profileDigest := config.profileDigest
    effectiveConfigDigest := config.effectiveConfigDigest }

/-- Existential package returned by the end-to-end wire/runtime boundary. -/
structure AdmittedAssistRun (digest : DigestOracle) where
  private mk ::
  config : MissionAssistConfig digest
  run : ActiveRun config

/-- Validate the untrusted assist commitment against the active mission, reuse
Judged's complete runtime admission, and only then construct the zero-action run. -/
def admitAssistRun (digest : DigestOracle) (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) (raw : RawAssistCommitment)
    (presentation : PresentationAssists) : Option (AdmittedAssistRun digest) := do
  let config ← validateMissionAssistConfig digest active.game.mission raw
  let activation ← validateAssistActivation config active carrier claim
  some ⟨config, startActiveRun activation presentation⟩

/-- Constructive inhabitation bridge: exact successful commitment validation and
runtime admission produce an actual active run, not an uninhabited token. -/
theorem admitAssistRun_of_exact {digest : DigestOracle} {active : ActiveRunState}
    {carrier : FinalizedCarrier} {claim : RunClaim} {raw : RawAssistCommitment}
    {presentation : PresentationAssists} {config : MissionAssistConfig digest}
    (hconfig :
      validateMissionAssistConfig digest active.game.mission raw = some config)
    (hadmitted : admissionChecks active carrier claim = true) :
    ∃ admitted : AdmittedAssistRun digest,
      admitAssistRun digest active carrier claim raw presentation = some admitted ∧
      admitted.config = config ∧ admitted.run.actionsUsed = 0 := by
  have hmission : active.game.mission = config.mission := by
    exact (validateMissionAssistConfig_success_mission hconfig).symm
  unfold admitAssistRun
  rw [hconfig]
  simp [validateAssistActivation, hmission, hadmitted, startActiveRun]

/-- Every admitted active transition retains the exact pre-activation semantic
config, profile digest, and effective-config digest by construction. -/
theorem activeStep_preserves_judge_inputs {config : MissionAssistConfig digest}
    (before after : ActiveRun config) (input : ActiveInput)
    (_h : activeStep before input = some after) :
    activeJudgeInputs after = activeJudgeInputs before := rfl

theorem presentation_step_preserves_action_count {config : MissionAssistConfig digest}
    (run next : ActiveRun config) (presentation : PresentationAssists)
    (h : activeStep run (.setPresentation presentation) = some next) :
    next.actionsUsed = run.actionsUsed := by
  simp [activeStep] at h
  subst next
  rfl

theorem action_refuses_at_budget {config : MissionAssistConfig digest}
    (run : ActiveRun config)
    (h : run.actionsUsed = config.profile.actionBudget.val) :
    activeStep run .recordAction = none := by
  simp [activeStep, h]

/-! ## Explicit league eligibility and comparison -/

inductive LeagueDivision where
  | standard
  | assisted
deriving DecidableEq, Repr

inductive PracticeReason where
  | guidedSolution
  | reducedObjective
deriving DecidableEq, Repr

inductive Eligibility where
  | eligible (division : LeagueDivision)
  | practiceOnly (reason : PracticeReason)
deriving DecidableEq, Repr

/-- Explicit fixed policy: guided solutions and reduced objectives are practice
only; other nonstandard profiles enter an assisted division without score loss. -/
def eligibility (profile : SemanticAssistProfile) : Eligibility :=
  if profile.hint = .guided then .practiceOnly .guidedSolution
  else if profile.simplification = .reducedObjective then .practiceOnly .reducedObjective
  else if profile.hint = .none ∧ profile.undo = .disabled ∧
      profile.simplification = .standard then
    .eligible .standard
  else
    .eligible .assisted

def eligibleB (profile : SemanticAssistProfile) : Bool :=
  match eligibility profile with
  | .eligible _ => true
  | .practiceOnly _ => false

structure LeagueRun (digest : DigestOracle) where
  config : MissionAssistConfig digest
  rawScore : Nat

/-- No multiplier or hidden penalty exists: eligible score is the raw score;
practice-only runs return no league score. -/
def LeagueRun.leagueScore (run : LeagueRun digest) : Option Nat :=
  match eligibility run.config.profile with
  | .eligible _ => some run.rawScore
  | .practiceOnly _ => none

theorem LeagueRun.eligible_score_unchanged (run : LeagueRun digest)
    (division : LeagueDivision)
    (h : eligibility run.config.profile = .eligible division) :
    run.leagueScore = some run.rawScore := by
  simp [LeagueRun.leagueScore, h]

/-- Exact comparison policy.  Presentation is absent; semantics, both digests,
the complete mission, and eligibility must agree.  Direct semantic equality is
required in addition to digest equality, so this theorem does not assume an
injective hash oracle. -/
def LeagueRun.comparableB (left right : LeagueRun digest) : Bool :=
  eligibleB left.config.profile &&
  eligibleB right.config.profile &&
  decide (left.config.mission = right.config.mission) &&
  decide (left.config.profile = right.config.profile) &&
  decide (left.config.profileDigest = right.config.profileDigest) &&
  decide (left.config.effectiveConfigDigest = right.config.effectiveConfigDigest)

theorem LeagueRun.comparable_eq_true_iff (left right : LeagueRun digest) :
    left.comparableB right = true ↔
      eligibleB left.config.profile = true ∧
      eligibleB right.config.profile = true ∧
      left.config.mission = right.config.mission ∧
      left.config.profile = right.config.profile ∧
      left.config.profileDigest = right.config.profileDigest ∧
      left.config.effectiveConfigDigest = right.config.effectiveConfigDigest := by
  simp [LeagueRun.comparableB, and_assoc]

theorem LeagueRun.comparable_requires_profile_digest_equality
    {left right : LeagueRun digest} (h : left.comparableB right = true) :
    left.config.profileDigest = right.config.profileDigest :=
  (LeagueRun.comparable_eq_true_iff left right).mp h |>.2.2.2.2.1

theorem LeagueRun.comparable_requires_config_digest_equality
    {left right : LeagueRun digest} (h : left.comparableB right = true) :
    left.config.effectiveConfigDigest = right.config.effectiveConfigDigest :=
  (LeagueRun.comparable_eq_true_iff left right).mp h |>.2.2.2.2.2

/-! ## Hostile executable vectors -/

def standardRaw : RawSemanticAssistProfile :=
  { schemaVersion := 1, actionBudget := 12, hintTag := 0, undoTag := 0,
    simplificationTag := 0 }

theorem valid_standard_wire_accepts : (validateSemanticAssistProfile standardRaw).isSome = true := by
  native_decide

theorem unknown_schema_refuses :
    validateSemanticAssistProfile { standardRaw with schemaVersion := 2 } = none := by
  native_decide

theorem zero_budget_refuses :
    validateSemanticAssistProfile { standardRaw with actionBudget := 0 } = none := by
  native_decide

theorem oversized_budget_refuses :
    validateSemanticAssistProfile { standardRaw with actionBudget := 65 } = none := by
  native_decide

theorem unknown_hint_refuses :
    validateSemanticAssistProfile { standardRaw with hintTag := 3 } = none := by
  native_decide

theorem unknown_undo_refuses :
    validateSemanticAssistProfile { standardRaw with undoTag := 2 } = none := by
  native_decide

theorem unknown_simplification_refuses :
    validateSemanticAssistProfile { standardRaw with simplificationTag := 3 } = none := by
  native_decide

theorem short_digest_refuses : validateDigest32 (List.replicate 31 0) = none := by
  native_decide

theorem oversized_digest_byte_refuses :
    validateDigest32 (256 :: List.replicate 31 0) = none := by
  native_decide

theorem exact_digest_wire_accepts :
    (validateDigest32 (List.replicate 32 0)).isSome = true := by
  native_decide

theorem guided_profile_is_explicitly_practice_only (budget : Fin (MAX_ACTION_BUDGET + 1))
    (positive : 0 < budget.val) :
    eligibility {
      actionBudget := budget
      action_budget_positive := positive
      hint := .guided
      undo := .disabled
      simplification := .standard
    } = .practiceOnly .guidedSolution := by
  simp [eligibility]

/-! ## Axiom audit -/

#assert_axioms presentation_irrelevant_to_judge_inputs
#assert_axioms validateMissionAssistConfig_success_mission
#assert_axioms validateMissionAssistConfig_rejects_profile_digest_mismatch
#assert_axioms validateMissionAssistConfig_rejects_effective_digest_mismatch
#assert_axioms validateAssistActivation_success_admitted
#assert_axioms validateAssistActivation_success_mission_matches
#assert_axioms validateAssistActivation_rejects_mission_mismatch
#assert_axioms validateAssistActivation_rejects_failed_admission
#assert_axioms admitAssistRun_of_exact
#assert_axioms activeStep_preserves_judge_inputs
#assert_axioms presentation_step_preserves_action_count
#assert_axioms action_refuses_at_budget
#assert_axioms LeagueRun.eligible_score_unchanged
#assert_axioms LeagueRun.comparable_eq_true_iff
#assert_axioms LeagueRun.comparable_requires_profile_digest_equality
#assert_axioms LeagueRun.comparable_requires_config_digest_equality
#assert_axioms guided_profile_is_explicitly_practice_only

#assert_compiled valid_standard_wire_accepts
#assert_compiled unknown_schema_refuses
#assert_compiled zero_budget_refuses
#assert_compiled oversized_budget_refuses
#assert_compiled unknown_hint_refuses
#assert_compiled unknown_undo_refuses
#assert_compiled unknown_simplification_refuses
#assert_compiled short_digest_refuses
#assert_compiled oversized_digest_byte_refuses
#assert_compiled exact_digest_wire_accepts

end Dregg2.Games.PathOfAngels.AssistProfile
