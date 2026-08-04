/-
# Black Box Reconstruction — order the five recovered telemetry fragments

The mission's precommitted run seed selects one cyclic ordering of five unique
fragments.  A run may place each fragment once, for at most five actions.  Every
permutation is a legal attempt; exactly one order reconstructs the recording and may
release the mission's checked contribution.  The host cannot supply a different seed,
artifact, reward, or transcript to the receipt: all four are reconstructed below.
-/
import Dregg2.Games.PathOfAngels.Core
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.BlackBoxReconstruction

open Dregg2.Games.PathOfAngels

abbrev FRAGMENT_COUNT : Nat := 5
abbrev MAX_TURNS : Nat := FRAGMENT_COUNT
abbrev Fragment := Fin FRAGMENT_COUNT

def byte (n : Nat) : Fin 256 := ⟨n % 256, Nat.mod_lt _ (by omega)⟩

def seedOffset (seed : Digest32) : Fin FRAGMENT_COUNT :=
  ⟨(seed.bytes.getD 0 0).val % FRAGMENT_COUNT, Nat.mod_lt _ (by decide)⟩

def allFragments : List Fragment := [0, 1, 2, 3, 4]

/-- The compact v1 generator: the seed chooses one of five cyclic telemetry orders. -/
def orderForOffset (offset : Fin FRAGMENT_COUNT) : List Fragment :=
  [ ⟨(0 + offset.val) % FRAGMENT_COUNT, Nat.mod_lt _ (by decide)⟩
  , ⟨(1 + offset.val) % FRAGMENT_COUNT, Nat.mod_lt _ (by decide)⟩
  , ⟨(2 + offset.val) % FRAGMENT_COUNT, Nat.mod_lt _ (by decide)⟩
  , ⟨(3 + offset.val) % FRAGMENT_COUNT, Nat.mod_lt _ (by decide)⟩
  , ⟨(4 + offset.val) % FRAGMENT_COUNT, Nat.mod_lt _ (by decide)⟩
  ]

def orderFromSeed (seed : Digest32) : List Fragment :=
  orderForOffset (seedOffset seed)

theorem orderForOffset_length : ∀ offset : Fin FRAGMENT_COUNT,
    (orderForOffset offset).length = FRAGMENT_COUNT := by
  decide

theorem orderForOffset_nodup : ∀ offset : Fin FRAGMENT_COUNT,
    (orderForOffset offset).Nodup := by
  decide

theorem orderForOffset_perm : ∀ offset : Fin FRAGMENT_COUNT,
    (orderForOffset offset).Perm allFragments := by
  decide

theorem orderFromSeed_length (seed : Digest32) :
    (orderFromSeed seed).length = FRAGMENT_COUNT :=
  orderForOffset_length (seedOffset seed)

theorem orderFromSeed_nodup (seed : Digest32) : (orderFromSeed seed).Nodup :=
  orderForOffset_nodup (seedOffset seed)

theorem orderFromSeed_perm (seed : Digest32) :
    (orderFromSeed seed).Perm allFragments :=
  orderForOffset_perm (seedOffset seed)

structure Config where
  mission : MissionSpec
  reward : Contribution
  reward_accepted : mission.acceptsContribution reward = true

structure State where
  placed : List Fragment
  turns : Nat
deriving Repr, DecidableEq

def initialState : State := { placed := [], turns := 0 }

inductive Action where
  | place (fragment : Fragment)
deriving Repr, DecidableEq

def openB (s : State) (fragment : Fragment) : Bool :=
  s.turns < MAX_TURNS &&
  s.placed.length < FRAGMENT_COUNT &&
  decide (fragment ∉ s.placed)

/-- The authoritative partial transition.  Duplicate and sixth placements refuse. -/
def step (s : State) : Action → Option State
  | .place fragment =>
      if openB s fragment then
        some { placed := s.placed ++ [fragment], turns := s.turns + 1 }
      else
        none

def replay : State → List Action → Option State
  | s, [] => some s
  | s, a :: as =>
      match step s a with
      | none => none
      | some s' => replay s' as

def winningOrder (cfg : Config) : List Fragment := orderFromSeed cfg.mission.runSeed

def solvedB (cfg : Config) (s : State) : Bool := s.placed == winningOrder cfg

private def terminalOutput (cfg : Config) (s : State) : Option (Contribution × ArtifactRef) :=
  if solvedB cfg s then some (cfg.reward, cfg.mission.artifact) else none

def fragmentOf : Action → Fragment
  | .place fragment => fragment

def actionAt (actions : List Action) (i : Nat) : Nat :=
  match actions[i]? with
  | some action => (fragmentOf action).val
  | none => 255

def transcriptDigest (actions : List Action) : Digest32 where
  bytes := List.ofFn (fun i : Fin 32 =>
    if i.val = 0 then byte actions.length else byte (actionAt actions (i.val - 1)))
  length_eq := by simp

structure JudgeContext where
  actorRoot : Digest32
  playerKey : Digest32
  previousPlayerCounter : Nat

structure JudgedRun where
  finalState : State
  afterWorld : WorldState
  receipt : RunReceipt

def judge (cfg : Config) (before : WorldState) (ctx : JudgeContext)
    (actions : List Action) : Option JudgedRun :=
  match replay initialState actions with
  | none => none
  | some finalState =>
      match terminalOutput cfg finalState with
      | none => none
      | some (contribution, _artifact) =>
          match happlied : applyContribution cfg.mission contribution before with
          | none => none
          | some afterWorld =>
              some {
                finalState
                afterWorld
                receipt := {
                  mission := cfg.mission
                  federationId := cfg.mission.federationId
                  contentRoot := cfg.mission.contentRoot
                  activationDigest := cfg.mission.activationDigest
                  contentSession := cfg.mission.contentSession
                  contentEpoch := cfg.mission.epoch
                  actorRoot := ctx.actorRoot
                  playerKey := ctx.playerKey
                  previousPlayerCounter := ctx.previousPlayerCounter
                  playerCounter := ctx.previousPlayerCounter + 1
                  runSeed := cfg.mission.runSeed
                  preWorld := before
                  postWorld := afterWorld
                  contribution
                  transcriptDigest := transcriptDigest actions
                  federation_matches := rfl
                  content_root_matches := rfl
                  activation_matches := rfl
                  content_session_matches := rfl
                  content_epoch_matches := rfl
                  run_seed_matches := rfl
                  player_counter_advances := rfl
                  applied := happlied
                }
              }

def remaining (s : State) : Nat := MAX_TURNS - s.turns

theorem step_deterministic (s : State) (a : Action) {s₁ s₂ : State}
    (h₁ : step s a = some s₁) (h₂ : step s a = some s₂) : s₁ = s₂ := by
  rw [h₁] at h₂
  exact Option.some.inj h₂

theorem step_some_turns (s : State) (a : Action) {s' : State}
    (h : step s a = some s') : s'.turns = s.turns + 1 := by
  cases a with
  | place fragment =>
      simp only [step] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst s'
        rfl
      · contradiction

theorem step_some_placed (s : State) (fragment : Fragment) {s' : State}
    (h : step s (.place fragment) = some s') : s'.placed = s.placed ++ [fragment] := by
  simp only [step] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst s'
    rfl
  · contradiction

theorem step_some_bound (s : State) (a : Action) {s' : State}
    (h : step s a = some s') : s'.turns ≤ MAX_TURNS := by
  have ht := step_some_turns s a h
  cases a with
  | place fragment =>
      simp only [step] at h
      split at h
      · rename_i hop
        have hlt : s.turns < MAX_TURNS := by
          simp only [openB, Bool.and_eq_true, decide_eq_true_eq] at hop
          exact hop.1.1
        omega
      · contradiction

theorem remaining_strictly_decreases (s : State) (a : Action) {s' : State}
    (h : step s a = some s') : remaining s' < remaining s := by
  have ht := step_some_turns s a h
  have hb := step_some_bound s a h
  simp only [remaining]
  omega

theorem duplicate_fragment_refused (s : State) (fragment : Fragment)
    (h : fragment ∈ s.placed) : step s (.place fragment) = none := by
  simp [step, openB, h]

theorem exhausted_refuses (s : State) (a : Action) (h : MAX_TURNS ≤ s.turns) :
    step s a = none := by
  cases a with
  | place fragment => simp [step, openB, Nat.not_lt.mpr h]

theorem full_sequence_refuses (s : State) (a : Action)
    (h : FRAGMENT_COUNT ≤ s.placed.length) : step s a = none := by
  cases a with
  | place fragment => simp [step, openB, Nat.not_lt.mpr h]

theorem step_preserves_nodup (s : State) (a : Action) {s' : State}
    (hn : s.placed.Nodup) (h : step s a = some s') : s'.placed.Nodup := by
  cases a with
  | place fragment =>
      simp only [step] at h
      split at h
      · rename_i hop
        simp only [openB, Bool.and_eq_true, decide_eq_true_eq] at hop
        simp only [Option.some.injEq] at h
        subst s'
        rw [List.nodup_append]
        simp only [hn, List.nodup_singleton, true_and, List.mem_singleton]
        intro prior hprior candidate hcand hsame
        apply hop.2
        simpa [hcand, hsame] using hprior
      · contradiction

theorem replay_preserves_nodup (s : State) (actions : List Action) {s' : State}
    (hn : s.placed.Nodup) (h : replay s actions = some s') : s'.placed.Nodup := by
  induction actions generalizing s with
  | nil =>
      simp only [replay, Option.some.injEq] at h
      subst s'
      exact hn
  | cons a as ih =>
      cases hs : step s a with
      | none => simp [replay, hs] at h
      | some next =>
          apply ih next (step_preserves_nodup s a hn hs)
          simpa [replay, hs] using h

theorem replay_append (s : State) (xs ys : List Action) :
    replay s (xs ++ ys) = (replay s xs).bind (fun s' => replay s' ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons a as ih =>
      simp only [List.cons_append, replay]
      split <;> simp_all

theorem refused_prefix_refuses_replay (s : State) (a : Action) (as : List Action)
    (h : step s a = none) : replay s (a :: as) = none := by
  simp [replay, h]

def winningActions (cfg : Config) : List Action := (winningOrder cfg).map .place

def winningState (cfg : Config) : State :=
  { placed := winningOrder cfg, turns := FRAGMENT_COUNT }

theorem replay_orderForOffset : ∀ offset : Fin FRAGMENT_COUNT,
    replay initialState ((orderForOffset offset).map .place) =
      some { placed := orderForOffset offset, turns := FRAGMENT_COUNT } := by
  decide

theorem winning_replay (cfg : Config) :
    replay initialState (winningActions cfg) = some (winningState cfg) := by
  exact replay_orderForOffset (seedOffset cfg.mission.runSeed)

theorem winning_state_solved (cfg : Config) : solvedB cfg (winningState cfg) = true := by
  simp [solvedB, winningState, winningOrder]

theorem terminalOutput_is_mission_accepted (cfg : Config) (s : State)
    {out : Contribution × ArtifactRef} (h : terminalOutput cfg s = some out) :
    cfg.mission.acceptsContribution out.1 = true := by
  simp only [terminalOutput] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst out
    exact cfg.reward_accepted
  · contradiction

theorem terminalOutput_names_exact_beta_artifact (cfg : Config) (s : State)
    {out : Contribution × ArtifactRef} (h : terminalOutput cfg s = some out) :
    out.2 = cfg.mission.artifact := by
  simp only [terminalOutput] at h
  split at h
  · simp only [Option.some.injEq] at h
    rw [← h]
  · contradiction

theorem terminalOutput_canonical (cfg : Config) (s : State)
    {contribution : Contribution} {artifact : ArtifactRef}
    (h : terminalOutput cfg s = some (contribution, artifact)) :
    terminalOutput cfg s = some (contribution, cfg.mission.artifact) := by
  have hart := terminalOutput_names_exact_beta_artifact cfg s h
  change artifact = cfg.mission.artifact at hart
  rw [hart] at h
  exact h

theorem terminalOutput_exact_order (cfg : Config) (s : State)
    {out : Contribution × ArtifactRef} (h : terminalOutput cfg s = some out) :
    s.placed = winningOrder cfg := by
  simp only [terminalOutput] at h
  split at h
  · rename_i hs
    exact beq_iff_eq.mp hs
  · contradiction

theorem judge_some_sound (cfg : Config) (before : WorldState) (ctx : JudgeContext)
    (actions : List Action) {run : JudgedRun} (h : judge cfg before ctx actions = some run) :
    replay initialState actions = some run.finalState ∧
    terminalOutput cfg run.finalState =
      some (run.receipt.contribution, cfg.mission.artifact) ∧
    applyContribution cfg.mission run.receipt.contribution before = some run.afterWorld ∧
    run.receipt.mission = cfg.mission ∧
    run.receipt.transcriptDigest = transcriptDigest actions := by
  unfold judge at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · contradiction
      · simp only [Option.some.injEq] at h
        subst run
        refine ⟨by assumption, ?_, by assumption, rfl, rfl⟩
        apply terminalOutput_canonical
        assumption

theorem judge_final_order_exact (cfg : Config) (before : WorldState) (ctx : JudgeContext)
    (actions : List Action) {run : JudgedRun} (h : judge cfg before ctx actions = some run) :
    run.finalState.placed = winningOrder cfg := by
  apply terminalOutput_exact_order cfg run.finalState
  exact (judge_some_sound cfg before ctx actions h).2.1

theorem judge_final_order_is_permutation (cfg : Config) (before : WorldState)
    (ctx : JudgeContext) (actions : List Action) {run : JudgedRun}
    (h : judge cfg before ctx actions = some run) :
    run.finalState.placed.Perm allFragments := by
  rw [judge_final_order_exact cfg before ctx actions h]
  exact orderFromSeed_perm cfg.mission.runSeed

theorem judge_receipt_binds_transcript (cfg : Config) (before : WorldState)
    (ctx : JudgeContext) (actions : List Action) {run : JudgedRun}
    (h : judge cfg before ctx actions = some run) :
    run.receipt.transcriptDigest = transcriptDigest actions :=
  (judge_some_sound cfg before ctx actions h).2.2.2.2

#assert_axioms orderForOffset_length
#assert_axioms orderForOffset_nodup
#assert_axioms orderForOffset_perm
#assert_axioms orderFromSeed_length
#assert_axioms orderFromSeed_nodup
#assert_axioms orderFromSeed_perm
#assert_axioms step_deterministic
#assert_axioms step_some_turns
#assert_axioms step_some_placed
#assert_axioms step_some_bound
#assert_axioms remaining_strictly_decreases
#assert_axioms duplicate_fragment_refused
#assert_axioms exhausted_refuses
#assert_axioms full_sequence_refuses
#assert_axioms step_preserves_nodup
#assert_axioms replay_preserves_nodup
#assert_axioms replay_append
#assert_axioms refused_prefix_refuses_replay
#assert_axioms replay_orderForOffset
#assert_axioms winning_replay
#assert_axioms winning_state_solved
#assert_axioms terminalOutput_is_mission_accepted
#assert_axioms terminalOutput_names_exact_beta_artifact
#assert_axioms terminalOutput_canonical
#assert_axioms terminalOutput_exact_order
#assert_axioms judge_some_sound
#assert_axioms judge_final_order_exact
#assert_axioms judge_final_order_is_permutation
#assert_axioms judge_receipt_binds_transcript

end Dregg2.Games.PathOfAngels.BlackBoxReconstruction
