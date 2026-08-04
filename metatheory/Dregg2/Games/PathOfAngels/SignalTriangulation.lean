/-
# Signal Triangulation — a five-burst intercepted-signal puzzle

This is a pure, executable Lean state machine.  The host supplies a checked PoA
`Contribution` and mission; the game may release exactly the mission's beta artifact
after a solved run, but it has no authority to manufacture or promote
canon.  `step` is the rules oracle: refusal is `none`, never an accepted no-op.
-/
import Dregg2.Games.PathOfAngels.Core
import Dregg2.Tactics
import Mathlib.Data.Multiset.UnionInter

namespace Dregg2.Games.PathOfAngels.SignalTriangulation

open Dregg2.Games.PathOfAngels

/-- A three-band intercepted signal.  Every band is in the public range `0..5`. -/
structure Code where
  low  : Fin 6
  mid  : Fin 6
  high : Fin 6
deriving Repr, DecidableEq

/-- Mastermind-style feedback. `exact` counts bands in the correct position;
`present` counts additional multiplicity-respecting matches in the wrong position. -/
structure Feedback where
  exact   : Nat
  present : Nat
deriving Repr, DecidableEq

def noFeedback : Feedback := { exact := 0, present := 0 }

def exactCount (target guess : Code) : Nat :=
  (if guess.low = target.low then 1 else 0) +
  (if guess.mid = target.mid then 1 else 0) +
  (if guess.high = target.high then 1 else 0)

/-- The three submitted bands as a bag: duplicates retain their multiplicity. -/
def bands (c : Code) : Multiset (Fin 6) :=
  c.low ::ₘ c.mid ::ₘ c.high ::ₘ 0

/-- Total symbol matches, including exact positions, with each target occurrence usable once. -/
def totalMatches (target guess : Code) : Nat :=
  (bands target ∩ bands guess).card

def presentCount (target guess : Code) : Nat :=
  totalMatches target guess - exactCount target guess

def feedback (target guess : Code) : Feedback :=
  { exact := exactCount target guess, present := presentCount target guess }

theorem exactCount_le_three (target guess : Code) : exactCount target guess ≤ 3 := by
  simp only [exactCount]
  split <;> split <;> split <;> omega

theorem totalMatches_le_three (target guess : Code) : totalMatches target guess ≤ 3 := by
  have h := Multiset.card_le_card (Multiset.inter_le_left (s := bands target) (t := bands guess))
  simpa [totalMatches, bands] using h

theorem feedback_match_bound (target guess : Code) :
    (feedback target guess).exact + (feedback target guess).present ≤ 3 := by
  have he := exactCount_le_three target guess
  have ht := totalMatches_le_three target guess
  simp only [feedback, presentCount]
  omega

theorem exactCount_eq_three_iff (target guess : Code) :
    exactCount target guess = 3 ↔ guess = target := by
  constructor
  · intro h
    by_cases hlo : guess.low = target.low
    · by_cases hmid : guess.mid = target.mid
      · by_cases hhigh : guess.high = target.high
        · cases guess
          cases target
          simp_all
        · simp [exactCount, hlo, hmid, hhigh] at h
      · by_cases hhigh : guess.high = target.high <;>
          simp [exactCount, hlo, hmid, hhigh] at h
    · by_cases hmid : guess.mid = target.mid <;>
        by_cases hhigh : guess.high = target.high <;>
        simp [exactCount, hlo, hmid, hhigh] at h
  · rintro rfl
    simp [exactCount]

theorem feedback_exact_target (target : Code) : (feedback target target).exact = 3 := by
  simp [feedback, exactCount]

theorem feedback_present_target (target : Code) : (feedback target target).present = 0 := by
  unfold feedback presentCount totalMatches
  have hi : (bands target ⊓ bands target) = bands target :=
    inf_idem (α := Multiset (Fin 6)) (bands target)
  change bands target ∩ bands target = bands target at hi
  rw [hi]
  simp [bands, exactCount]

/-- Duplicate bands consume duplicate target multiplicity only once each. -/
theorem duplicate_band_example :
    feedback { low := 1, mid := 1, high := 2 }
      { low := 1, mid := 2, high := 2 } = { exact := 2, present := 0 } := by
  decide

/-- Five intercepted bursts is the complete session budget. -/
abbrev MAX_TURNS : Nat := 5

def byte (n : Nat) : Fin 256 := ⟨n % 256, Nat.mod_lt _ (by omega)⟩

def digestByte (digest : Digest32) (i : Nat) : Nat :=
  (digest.bytes.getD i 0).val

/-- The run seed chooses the puzzle; it is recorded verbatim in the Core receipt.
The mission artifact pins this derivation and the full feedback table. -/
def targetFromSeed (seed : Digest32) : Code := {
  low := ⟨digestByte seed 0 % 6, Nat.mod_lt _ (by omega)⟩
  mid := ⟨digestByte seed 1 % 6, Nat.mod_lt _ (by omega)⟩
  high := ⟨digestByte seed 2 % 6, Nat.mod_lt _ (by omega)⟩
}

structure Config where
  target       : Code
  mission      : MissionSpec
  reward       : Contribution
  reward_accepted : mission.acceptsContribution reward = true
  target_eq : target = targetFromSeed mission.runSeed

structure State where
  turns        : Nat
  solved       : Bool
  lastFeedback : Feedback
deriving Repr, DecidableEq

def initialState : State :=
  { turns := 0, solved := false, lastFeedback := noFeedback }

inductive Action where
  | submit (guess : Code)
deriving Repr, DecidableEq

def openB (s : State) : Bool := !s.solved && s.turns < MAX_TURNS

/-- The authoritative partial transition.  Closed and exhausted receivers refuse. -/
def step (cfg : Config) (s : State) : Action → Option State
  | .submit guess =>
      if openB s then
        let f := feedback cfg.target guess
        some {
          turns := s.turns + 1
          solved := f.exact == 3
          lastFeedback := f
        }
      else
        none

def zeroCode : Code := { low := 0, mid := 0, high := 0 }

def guessAt (actions : List Action) (i : Nat) : Code :=
  match actions[i]? with
  | some (.submit guess) => guess
  | none => zeroCode

/-- The receipt commits to the whole accepted transcript, not a caller-supplied digest.
An accepted transcript has at most five actions, so bytes 1..15 carry every band. -/
def transcriptDigest (actions : List Action) : Digest32 where
  bytes := List.ofFn (fun i : Fin 32 =>
    if i.val = 0 then byte actions.length else
      let off := i.val - 1
      let guess := guessAt actions (off / 3)
      match off % 3 with
      | 0 => byte guess.low.val
      | 1 => byte guess.mid.val
      | _ => byte guess.high.val)
  length_eq := by simp

/-- Raw terminal projection.  It is private: authoritative callers use `judge`. -/
private def terminalOutput (cfg : Config) (s : State) : Option (Contribution × ArtifactRef) :=
  if s.solved then some (cfg.reward, cfg.mission.artifact) else none

/-- Replay is fail-stop: the first refused action refuses the complete script. -/
def replay (cfg : Config) : State → List Action → Option State
  | s, [] => some s
  | s, a :: as =>
      match step cfg s a with
      | none => none
      | some s' => replay cfg s' as

def remaining (s : State) : Nat := MAX_TURNS - s.turns

/-- The only authoritative run result: exact replay from genesis, mission-accepted
terminal output, atomic world application, and the Core receipt in one value. -/
structure JudgedRun where
  finalState : State
  afterWorld : WorldState
  receipt : RunReceipt

structure JudgeContext where
  actorRoot : Digest32
  playerKey : Digest32
  previousPlayerCounter : Nat

def judge (cfg : Config) (before : WorldState) (ctx : JudgeContext)
    (actions : List Action) : Option JudgedRun :=
  match replay cfg initialState actions with
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

theorem step_deterministic (cfg : Config) (s : State) (a : Action) {s₁ s₂ : State}
    (h₁ : step cfg s a = some s₁) (h₂ : step cfg s a = some s₂) : s₁ = s₂ := by
  rw [h₁] at h₂
  exact Option.some.inj h₂

theorem step_some_turns (cfg : Config) (s : State) (a : Action) {s' : State}
    (h : step cfg s a = some s') : s'.turns = s.turns + 1 := by
  cases a with
  | submit guess =>
      simp only [step] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst s'
        rfl
      · contradiction

theorem step_some_bound (cfg : Config) (s : State) (a : Action) {s' : State}
    (h : step cfg s a = some s') : s'.turns ≤ MAX_TURNS := by
  cases a with
  | submit guess =>
      simp only [step, openB, Bool.and_eq_true, decide_eq_true_eq] at h
      split at h
      · rename_i hop
        have hlt : s.turns < MAX_TURNS := hop.2
        simp only [Option.some.injEq] at h
        subst s'
        simp only
        omega
      · contradiction

theorem remaining_strictly_decreases (cfg : Config) (s : State) (a : Action) {s' : State}
    (h : step cfg s a = some s') : remaining s' < remaining s := by
  have ht := step_some_turns cfg s a h
  have hb := step_some_bound cfg s a h
  simp only [remaining]
  omega

theorem solved_refuses (cfg : Config) (s : State) (a : Action) (h : s.solved = true) :
    step cfg s a = none := by
  cases a <;> simp [step, openB, h]

theorem exhausted_refuses (cfg : Config) (s : State) (a : Action)
    (h : MAX_TURNS ≤ s.turns) : step cfg s a = none := by
  cases a <;> simp [step, openB, Nat.not_lt.mpr h]

theorem target_submission_solves (cfg : Config) :
    ∃ s', step cfg initialState (.submit cfg.target) = some s' ∧ s'.solved = true := by
  refine ⟨{
    turns := 1
    solved := true
    lastFeedback := feedback cfg.target cfg.target
  }, ?_, ?_⟩
  · simp [step, openB, initialState, feedback, exactCount]
  · rfl

theorem accepted_solved_iff_target (cfg : Config) (s : State) (guess : Code) {s' : State}
    (h : step cfg s (.submit guess) = some s') : s'.solved = true ↔ guess = cfg.target := by
  simp only [step] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst s'
    simp only [beq_iff_eq, feedback]
    exact exactCount_eq_three_iff _ _
  · contradiction

theorem terminalOutput_none_before_solution (cfg : Config) (s : State) (h : s.solved = false) :
    terminalOutput cfg s = none := by
  simp [terminalOutput, h]

theorem terminalOutput_after_solution (cfg : Config) (s : State) (h : s.solved = true) :
    terminalOutput cfg s = some (cfg.reward, cfg.mission.artifact) := by
  simp [terminalOutput, h]

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

theorem judge_some_sound (cfg : Config) (before : WorldState) (ctx : JudgeContext)
    (actions : List Action) {run : JudgedRun} (h : judge cfg before ctx actions = some run) :
    replay cfg initialState actions = some run.finalState ∧
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

theorem judge_receipt_binds_target (cfg : Config) (before : WorldState) (ctx : JudgeContext)
    (actions : List Action) {run : JudgedRun} (h : judge cfg before ctx actions = some run) :
    cfg.target = targetFromSeed run.receipt.runSeed := by
  have hs := judge_some_sound cfg before ctx actions h
  rw [run.receipt.run_seed_matches, hs.2.2.2.1]
  exact cfg.target_eq

theorem judge_receipt_binds_transcript (cfg : Config) (before : WorldState) (ctx : JudgeContext)
    (actions : List Action) {run : JudgedRun} (h : judge cfg before ctx actions = some run) :
    run.receipt.transcriptDigest = transcriptDigest actions := by
  exact (judge_some_sound cfg before ctx actions h).2.2.2.2

theorem replay_nil (cfg : Config) (s : State) : replay cfg s [] = some s := by rfl

theorem replay_cons (cfg : Config) (s : State) (a : Action) (as : List Action) :
    replay cfg s (a :: as) = (step cfg s a).bind (fun s' => replay cfg s' as) := by
  cases h : step cfg s a <;> simp [replay, h]

theorem replay_append (cfg : Config) (s : State) (xs ys : List Action) :
    replay cfg s (xs ++ ys) = (replay cfg s xs).bind (fun s' => replay cfg s' ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons a as ih =>
      simp only [List.cons_append, replay]
      split <;> simp_all

theorem refused_prefix_refuses_replay (cfg : Config) (s : State) (a : Action) (as : List Action)
    (h : step cfg s a = none) : replay cfg s (a :: as) = none := by
  simp [replay, h]

#assert_axioms exactCount_le_three
#assert_axioms totalMatches_le_three
#assert_axioms feedback_match_bound
#assert_axioms exactCount_eq_three_iff
#assert_axioms feedback_exact_target
#assert_axioms feedback_present_target
#assert_axioms duplicate_band_example
#assert_axioms step_deterministic
#assert_axioms step_some_turns
#assert_axioms step_some_bound
#assert_axioms remaining_strictly_decreases
#assert_axioms solved_refuses
#assert_axioms exhausted_refuses
#assert_axioms target_submission_solves
#assert_axioms accepted_solved_iff_target
#assert_axioms terminalOutput_none_before_solution
#assert_axioms terminalOutput_after_solution
#assert_axioms terminalOutput_is_mission_accepted
#assert_axioms terminalOutput_names_exact_beta_artifact
#assert_axioms terminalOutput_canonical
#assert_axioms judge_some_sound
#assert_axioms judge_receipt_binds_target
#assert_axioms judge_receipt_binds_transcript
#assert_axioms replay_nil
#assert_axioms replay_cons
#assert_axioms replay_append
#assert_axioms refused_prefix_refuses_replay

end Dregg2.Games.PathOfAngels.SignalTriangulation
