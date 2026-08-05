/-
# Dregg2.Games.PathOfAngels.Judged — executable runtime admission

`JudgedRun` is abstract outside this module.  It is produced only by
`judgeActive`, which checks an exact active game/config projection, all content
and activation domains, the authenticated carrying-turn context, and the current
canonical player counter before invoking one concrete game judge.

The semantic judge remains publicly replayable.  Network authority is not source
secrecy and is not an unconstructible token: the adapter must derive
`FinalizedCarrier` from the already-finalized Dregg turn/receipt, then this module
checks every value it consumes.  A caller can model those inputs, but cannot forge
a `JudgedRun` constructor or bypass the executable equality retained below.
-/
import Dregg2.Games.PathOfAngels.SignalTriangulation
import Dregg2.Games.PathOfAngels.RelayRepair
import Dregg2.Games.PathOfAngels.SalvageLock
import Dregg2.Games.PathOfAngels.BlackBoxReconstruction
import Dregg2.Games.PathOfAngels.PlayerCounters

namespace Dregg2.Games.PathOfAngels

set_option autoImplicit false

/-! ## Active configuration and authenticated carrying context -/

inductive ActiveGame where
  | signal (config : SignalTriangulation.Config)
  | relay (config : RelayRepair.Config)
  | salvage (config : SalvageLock.Config)
  | blackBox (config : BlackBoxReconstruction.Config)

def ActiveGame.mission : ActiveGame → MissionSpec
  | .signal config => config.mission
  | .relay config => config.mission
  | .salvage config => config.mission
  | .blackBox config => config.mission

/-- Proof fields are omitted, but every semantic config field is retained.  This
is the exact claim compared at the dispatch boundary. -/
inductive GameConfigClaim where
  | signal (target : SignalTriangulation.Code) (mission : MissionSpec)
      (reward : Contribution)
  | relay (mission : MissionSpec) (reward : Contribution)
  | salvage (seed : Fin SalvageLock.SEED_SPACE) (mission : MissionSpec) (reward : Contribution)
  | blackBox (mission : MissionSpec) (reward : Contribution)
deriving DecidableEq

def ActiveGame.configClaim : ActiveGame → GameConfigClaim
  | .signal config => .signal config.target config.mission config.reward
  | .relay config => .relay config.mission config.reward
  | .salvage config => .salvage config.seed config.mission config.reward
  | .blackBox config => .blackBox config.mission config.reward

/-- Runtime state selected from the authenticated active catalog.  Domain fields
are repeated intentionally and checked against the mission: malformed decoded
state refuses rather than being silently repaired from `game`. -/
structure ActiveRunState where
  game : ActiveGame
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  runSeed : Digest32
  world : WorldState
  playerCounters : PlayerCounterTable

/-- Values derived from the finalized carrying Dregg turn.  `playerKey` is its
signer and `actorRoot` is its AIR-bound pre-state commitment. -/
structure FinalizedCarrier where
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  actorRoot : Digest32
  playerKey : Digest32
  currentPlayerCounter : PlayerCounter

/-- Untrusted receipt-shaped claims supplied by the game request.  They are all
compared with active state or the finalized carrier before replay. -/
structure RunClaim where
  config : GameConfigClaim
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  runSeed : Digest32
  actorRoot : Digest32
  playerKey : Digest32
  claimedPreviousPlayerCounter : Nat

inductive SubmittedRun where
  | signal (actions : List SignalTriangulation.Action)
  | relay (actions : List RelayRepair.Action)
  | salvage (actions : List SalvageLock.Action)
  | blackBox (actions : List BlackBoxReconstruction.Action)

def FinalizedCarrier.counterKey (carrier : FinalizedCarrier) : PlayerCounterKey where
  federationId := carrier.federationId
  contentSession := carrier.contentSession
  contentEpoch := carrier.contentEpoch
  playerKey := carrier.playerKey

/-- Every authority/configuration equality checked before the game judge runs. -/
def admissionChecks (active : ActiveRunState) (carrier : FinalizedCarrier)
    (claim : RunClaim) : Bool :=
  decide (
    claim.config = active.game.configClaim ∧
    active.federationId = active.game.mission.federationId ∧
    active.contentRoot = active.game.mission.contentRoot ∧
    active.activationDigest = active.game.mission.activationDigest ∧
    active.contentSession = active.game.mission.contentSession ∧
    active.contentEpoch = active.game.mission.epoch ∧
    active.runSeed = active.game.mission.runSeed ∧
    carrier.federationId = active.federationId ∧
    carrier.contentRoot = active.contentRoot ∧
    carrier.activationDigest = active.activationDigest ∧
    carrier.contentSession = active.contentSession ∧
    carrier.contentEpoch = active.contentEpoch ∧
    claim.federationId = carrier.federationId ∧
    claim.contentRoot = carrier.contentRoot ∧
    claim.activationDigest = carrier.activationDigest ∧
    claim.contentSession = carrier.contentSession ∧
    claim.contentEpoch = carrier.contentEpoch ∧
    claim.runSeed = active.runSeed ∧
    claim.actorRoot = carrier.actorRoot ∧
    claim.playerKey = carrier.playerKey ∧
    claim.claimedPreviousPlayerCounter = carrier.currentPlayerCounter.val ∧
    active.playerCounters.lookup carrier.counterKey = carrier.currentPlayerCounter ∧
    carrier.currentPlayerCounter.val + 1 < PLAYER_COUNTER_MODULUS)

theorem admissionChecks_eq_true_iff (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) :
    admissionChecks active carrier claim = true ↔
      claim.config = active.game.configClaim ∧
      active.federationId = active.game.mission.federationId ∧
      active.contentRoot = active.game.mission.contentRoot ∧
      active.activationDigest = active.game.mission.activationDigest ∧
      active.contentSession = active.game.mission.contentSession ∧
      active.contentEpoch = active.game.mission.epoch ∧
      active.runSeed = active.game.mission.runSeed ∧
      carrier.federationId = active.federationId ∧
      carrier.contentRoot = active.contentRoot ∧
      carrier.activationDigest = active.activationDigest ∧
      carrier.contentSession = active.contentSession ∧
      carrier.contentEpoch = active.contentEpoch ∧
      claim.federationId = carrier.federationId ∧
      claim.contentRoot = carrier.contentRoot ∧
      claim.activationDigest = carrier.activationDigest ∧
      claim.contentSession = carrier.contentSession ∧
      claim.contentEpoch = carrier.contentEpoch ∧
      claim.runSeed = active.runSeed ∧
      claim.actorRoot = carrier.actorRoot ∧
      claim.playerKey = carrier.playerKey ∧
      claim.claimedPreviousPlayerCounter = carrier.currentPlayerCounter.val ∧
      active.playerCounters.lookup carrier.counterKey = carrier.currentPlayerCounter ∧
      carrier.currentPlayerCounter.val + 1 < PLAYER_COUNTER_MODULUS := by
  simp only [admissionChecks, decide_eq_true_eq]

private def signalContext (carrier : FinalizedCarrier) : SignalTriangulation.JudgeContext where
  actorRoot := carrier.actorRoot
  playerKey := carrier.playerKey
  previousPlayerCounter := carrier.currentPlayerCounter.val

private def relayContext (carrier : FinalizedCarrier) : RelayRepair.JudgeContext where
  actorRoot := carrier.actorRoot
  playerKey := carrier.playerKey
  previousPlayerCounter := carrier.currentPlayerCounter.val

private def salvageContext (carrier : FinalizedCarrier) : SalvageLock.JudgeContext where
  actorRoot := carrier.actorRoot
  playerKey := carrier.playerKey
  previousPlayerCounter := carrier.currentPlayerCounter.val

private def blackBoxContext (carrier : FinalizedCarrier) : BlackBoxReconstruction.JudgeContext where
  actorRoot := carrier.actorRoot
  playerKey := carrier.playerKey
  previousPlayerCounter := carrier.currentPlayerCounter.val

/-! ## Abstract judged value with game-specific executable evidence -/

private inductive JudgedEvidence where
  | signal
      (active : ActiveRunState) (carrier : FinalizedCarrier) (claim : RunClaim)
      (config : SignalTriangulation.Config)
      (admitted : admissionChecks active carrier claim = true)
      (actions : List SignalTriangulation.Action)
      (run : SignalTriangulation.JudgedRun)
      (judged : SignalTriangulation.judge config active.world (signalContext carrier) actions = some run)
  | relay
      (active : ActiveRunState) (carrier : FinalizedCarrier) (claim : RunClaim)
      (config : RelayRepair.Config)
      (admitted : admissionChecks active carrier claim = true)
      (actions : List RelayRepair.Action)
      (run : RelayRepair.JudgedRun)
      (judged : RelayRepair.judge config active.world (relayContext carrier) actions = some run)
  | salvage
      (active : ActiveRunState) (carrier : FinalizedCarrier) (claim : RunClaim)
      (config : SalvageLock.Config)
      (admitted : admissionChecks active carrier claim = true)
      (actions : List SalvageLock.Action)
      (run : SalvageLock.JudgedRun)
      (judged : SalvageLock.judge config active.world (salvageContext carrier) actions = some run)
  | blackBox
      (active : ActiveRunState) (carrier : FinalizedCarrier) (claim : RunClaim)
      (config : BlackBoxReconstruction.Config)
      (admitted : admissionChecks active carrier claim = true)
      (actions : List BlackBoxReconstruction.Action)
      (run : BlackBoxReconstruction.JudgedRun)
      (judged : BlackBoxReconstruction.judge config active.world (blackBoxContext carrier) actions = some run)

/-- Public type, private constructor and payload. -/
structure JudgedRun where
  private mk ::
  private evidence : JudgedEvidence

def JudgedRun.receipt (judgedRun : JudgedRun) : RunReceipt :=
  match judgedRun.evidence with
  | .signal _ _ _ _ _ _ run _ => run.receipt
  | .relay _ _ _ _ _ _ run _ => run.receipt
  | .salvage _ _ _ _ _ _ run _ => run.receipt
  | .blackBox _ _ _ _ _ _ run _ => run.receipt

/-- The only constructor surface: checks first, exact game tag second, executable
judge third.  Every failure returns `none`. -/
def judgeActive (active : ActiveRunState) (carrier : FinalizedCarrier)
    (claim : RunClaim) (submitted : SubmittedRun) : Option JudgedRun :=
  if hadmitted : admissionChecks active carrier claim = true then
    match active.game, submitted with
    | .signal config, .signal actions =>
        match hjudged : SignalTriangulation.judge config active.world
            (signalContext carrier) actions with
        | some run => some ⟨.signal active carrier claim config hadmitted actions run hjudged⟩
        | none => none
    | .relay config, .relay actions =>
        match hjudged : RelayRepair.judge config active.world (relayContext carrier) actions with
        | some run => some ⟨.relay active carrier claim config hadmitted actions run hjudged⟩
        | none => none
    | .salvage config, .salvage actions =>
        match hjudged : SalvageLock.judge config active.world (salvageContext carrier) actions with
        | some run => some ⟨.salvage active carrier claim config hadmitted actions run hjudged⟩
        | none => none
    | .blackBox config, .blackBox actions =>
        match hjudged : BlackBoxReconstruction.judge config active.world
            (blackBoxContext carrier) actions with
        | some run => some ⟨.blackBox active carrier claim config hadmitted actions run hjudged⟩
        | none => none
    | _, _ => none
  else none

/-- Constructive inhabitation bridge for the first live game: any genuinely
successful Signal judge under admitted active inputs produces an abstract
`JudgedRun`; no token, axiom, or unsafe constructor is involved. -/
theorem judgeActive_signal_of_exact {active : ActiveRunState}
    {carrier : FinalizedCarrier} {claim : RunClaim}
    {config : SignalTriangulation.Config} {actions : List SignalTriangulation.Action}
    {raw : SignalTriangulation.JudgedRun}
    (hgame : active.game = .signal config)
    (hadmitted : admissionChecks active carrier claim = true)
    (hjudged : SignalTriangulation.judge config active.world
      (signalContext carrier) actions = some raw) :
    ∃ run : JudgedRun,
      judgeActive active carrier claim (.signal actions) = some run ∧
      run.receipt = raw.receipt := by
  simp only [judgeActive, hadmitted, ↓reduceDIte, hgame]
  split
  · rename_i found hfound
    rw [hfound] at hjudged
    injection hjudged with heq
    subst found
    exact ⟨_, rfl, rfl⟩
  · rename_i hnone
    rw [hnone] at hjudged
    contradiction

theorem judgeActive_success_admitted {active : ActiveRunState} {carrier : FinalizedCarrier}
    {claim : RunClaim} {submitted : SubmittedRun} {run : JudgedRun}
    (h : judgeActive active carrier claim submitted = some run) :
    admissionChecks active carrier claim = true := by
  unfold judgeActive at h
  split at h
  · assumption
  · contradiction

theorem judgeActive_wrong_activation_refused (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) (submitted : SubmittedRun)
    (h : claim.activationDigest ≠ carrier.activationDigest) :
    judgeActive active carrier claim submitted = none := by
  simp [judgeActive, admissionChecks, h]

theorem judgeActive_wrong_config_refused (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) (submitted : SubmittedRun)
    (h : claim.config ≠ active.game.configClaim) :
    judgeActive active carrier claim submitted = none := by
  simp [judgeActive, admissionChecks, h]

theorem judgeActive_inactive_activation_refused (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) (submitted : SubmittedRun)
    (h : active.activationDigest ≠ active.game.mission.activationDigest) :
    judgeActive active carrier claim submitted = none := by
  simp [judgeActive, admissionChecks, h]

theorem judgeActive_wrong_session_refused (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) (submitted : SubmittedRun)
    (h : claim.contentSession ≠ carrier.contentSession) :
    judgeActive active carrier claim submitted = none := by
  simp [judgeActive, admissionChecks, h]

theorem judgeActive_wrong_epoch_refused (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) (submitted : SubmittedRun)
    (h : claim.contentEpoch ≠ carrier.contentEpoch) :
    judgeActive active carrier claim submitted = none := by
  simp [judgeActive, admissionChecks, h]

theorem judgeActive_wrong_seed_refused (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) (submitted : SubmittedRun)
    (h : claim.runSeed ≠ active.runSeed) :
    judgeActive active carrier claim submitted = none := by
  simp [judgeActive, admissionChecks, h]

theorem judgeActive_wrong_player_refused (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) (submitted : SubmittedRun)
    (h : claim.playerKey ≠ carrier.playerKey) :
    judgeActive active carrier claim submitted = none := by
  simp [judgeActive, admissionChecks, h]

theorem judgeActive_wrong_actor_root_refused (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) (submitted : SubmittedRun)
    (h : claim.actorRoot ≠ carrier.actorRoot) :
    judgeActive active carrier claim submitted = none := by
  simp [judgeActive, admissionChecks, h]

theorem judgeActive_stale_counter_refused (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) (submitted : SubmittedRun)
    (h : claim.claimedPreviousPlayerCounter ≠ carrier.currentPlayerCounter.val) :
    judgeActive active carrier claim submitted = none := by
  simp [judgeActive, admissionChecks, h]

theorem judgeActive_wrong_current_counter_refused (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) (submitted : SubmittedRun)
    (h : active.playerCounters.lookup carrier.counterKey ≠ carrier.currentPlayerCounter) :
    judgeActive active carrier claim submitted = none := by
  simp [judgeActive, admissionChecks, h]

theorem judgeActive_counter_exhausted_refused (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim) (submitted : SubmittedRun)
    (h : PLAYER_COUNTER_MODULUS ≤ carrier.currentPlayerCounter.val + 1) :
    judgeActive active carrier claim submitted = none := by
  simp [judgeActive, admissionChecks, Nat.not_lt.mpr h]

theorem judgeActive_wrong_game_refused (active : ActiveRunState)
    (carrier : FinalizedCarrier) (claim : RunClaim)
    (config : SignalTriangulation.Config) (actions : List RelayRepair.Action)
    (hgame : active.game = .signal config) :
    judgeActive active carrier claim (.relay actions) = none := by
  simp [judgeActive, hgame]

/-- Every inhabitant retains an equality to one concrete executable judge. -/
theorem JudgedRun.has_executable_origin (run : JudgedRun) :
    (∃ (active : ActiveRunState) (carrier : FinalizedCarrier)
        (config : SignalTriangulation.Config) (actions : List SignalTriangulation.Action)
        (raw : SignalTriangulation.JudgedRun),
      SignalTriangulation.judge config active.world (signalContext carrier) actions = some raw ∧
      run.receipt = raw.receipt) ∨
    (∃ (active : ActiveRunState) (carrier : FinalizedCarrier)
        (config : RelayRepair.Config) (actions : List RelayRepair.Action)
        (raw : RelayRepair.JudgedRun),
      RelayRepair.judge config active.world (relayContext carrier) actions = some raw ∧
      run.receipt = raw.receipt) ∨
    (∃ (active : ActiveRunState) (carrier : FinalizedCarrier)
        (config : SalvageLock.Config) (actions : List SalvageLock.Action)
        (raw : SalvageLock.JudgedRun),
      SalvageLock.judge config active.world (salvageContext carrier) actions = some raw ∧
      run.receipt = raw.receipt) ∨
    (∃ (active : ActiveRunState) (carrier : FinalizedCarrier)
        (config : BlackBoxReconstruction.Config)
        (actions : List BlackBoxReconstruction.Action)
        (raw : BlackBoxReconstruction.JudgedRun),
      BlackBoxReconstruction.judge config active.world (blackBoxContext carrier) actions = some raw ∧
      run.receipt = raw.receipt) := by
  obtain ⟨evidence⟩ := run
  cases evidence with
  | signal active carrier claim config admitted actions raw judged =>
      exact Or.inl ⟨active, carrier, config, actions, raw, judged, rfl⟩
  | relay active carrier claim config admitted actions raw judged =>
      exact Or.inr (Or.inl ⟨active, carrier, config, actions, raw, judged, rfl⟩)
  | salvage active carrier claim config admitted actions raw judged =>
      exact Or.inr (Or.inr (Or.inl ⟨active, carrier, config, actions, raw, judged, rfl⟩))
  | blackBox active carrier claim config admitted actions raw judged =>
      exact Or.inr (Or.inr (Or.inr ⟨active, carrier, config, actions, raw, judged, rfl⟩))

theorem JudgedRun.applied (run : JudgedRun) :
    applyContribution run.receipt.mission run.receipt.contribution
      run.receipt.preWorld = some run.receipt.postWorld :=
  run.receipt.applied

theorem JudgedRun.player_counter_positive (run : JudgedRun) :
    0 < run.receipt.playerCounter :=
  run.receipt.player_counter_positive

#assert_axioms admissionChecks_eq_true_iff
#assert_axioms judgeActive_signal_of_exact
#assert_axioms judgeActive_success_admitted
#assert_axioms judgeActive_wrong_activation_refused
#assert_axioms judgeActive_wrong_config_refused
#assert_axioms judgeActive_inactive_activation_refused
#assert_axioms judgeActive_wrong_session_refused
#assert_axioms judgeActive_wrong_epoch_refused
#assert_axioms judgeActive_wrong_seed_refused
#assert_axioms judgeActive_wrong_player_refused
#assert_axioms judgeActive_wrong_actor_root_refused
#assert_axioms judgeActive_stale_counter_refused
#assert_axioms judgeActive_wrong_current_counter_refused
#assert_axioms judgeActive_counter_exhausted_refused
#assert_axioms judgeActive_wrong_game_refused
#assert_axioms JudgedRun.has_executable_origin
#assert_axioms JudgedRun.applied
#assert_axioms JudgedRun.player_counter_positive

end Dregg2.Games.PathOfAngels
