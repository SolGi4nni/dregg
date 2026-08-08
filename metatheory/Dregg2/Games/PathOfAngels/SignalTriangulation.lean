/-
# Signal Triangulation — a five-burst intercepted-signal puzzle

This is a pure, executable Lean state machine.  The host supplies a checked PoA
`Contribution` and mission; the game may release exactly the mission's beta artifact
after a solved run, but it has no authority to manufacture or promote
canon.  `step` is the rules oracle: refusal is `none`, never an accepted no-op.
-/
import Dregg2.Games.PathOfAngels.Core
import Dregg2.Games.PathOfAngels.SeedDraw
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

/-! ## What a feedback oracle reveals, and what it cannot

`SignalFeedbackRuntime` serves `feedback target guess` to a player mid-run, against the
target the JUDGE will score.  That leak is the mechanic — five rounds are meant to solve
216 codes — but it has to be exactly the leak and no more.  The two facts below are the
formal content of "a reader learns no more than by playing", stated about `feedback`
itself so that any surface serving it inherits them:

* `feedback_transcript_cannot_separate` — over a whole transcript, two targets that
  agree on every guess PLAYED produce identical answers.  A reader's posterior after
  `k` rounds is therefore exactly the feedback-consistency class of the transcript,
  which is the definition of having played it.
* `one_round_never_determines_the_target` — that class is never a singleton after one
  round, for ANY first guess.  The invariance above is consequently not vacuous: there
  is always something left to deduce.

⚠ Neither says the oracle is harmless.  It says the oracle is exactly the game. -/

/-- ⚑ Two targets that answer alike on the guesses PLAYED answer alike on the whole
transcript.  Nothing a session serves separates them, because the served value is a
function of `feedback` and the played guesses alone. -/
theorem feedback_transcript_cannot_separate (t₁ t₂ : Code) (guesses : List Code)
    (agree : ∀ g ∈ guesses, feedback t₁ g = feedback t₂ g) :
    guesses.map (feedback t₁) = guesses.map (feedback t₂) :=
  List.map_congr_left agree

/-- The three-band code whose every band is `a`. -/
def monoCode (a : Fin 6) : Code := { low := a, mid := a, high := a }

theorem monoCode_injective {a b : Fin 6} (h : a ≠ b) : monoCode a ≠ monoCode b := by
  intro hEq
  exact h (congrArg Code.low hEq)

/-- A target none of whose bands the guess submitted scores a flat zero: no exact
position, and no multiplicity left over to be present elsewhere. -/
theorem feedback_of_absent_mono (guess : Code) (a : Fin 6)
    (low : a ≠ guess.low) (mid : a ≠ guess.mid) (high : a ≠ guess.high) :
    feedback (monoCode a) guess = { exact := 0, present := 0 } := by
  have hexact : exactCount (monoCode a) guess = 0 := by
    simp [exactCount, monoCode, Ne.symm low, Ne.symm mid, Ne.symm high]
  have hinter : bands (monoCode a) ∩ bands guess = 0 := by
    refine Multiset.eq_zero_of_forall_notMem ?_
    intro x hx
    rw [Multiset.mem_inter] at hx
    obtain ⟨hleft, hright⟩ := hx
    simp only [bands, monoCode, Multiset.mem_cons,
      Multiset.notMem_zero, or_false] at hleft hright
    rcases hleft with rfl | rfl | rfl <;>
      rcases hright with h | h | h <;> simp_all
  simp [feedback, presentCount, totalMatches, hexact, hinter]

/-- A guess names at most three of the six band values, so at least two values are
absent from it — and this exhausts the 216 guesses in the kernel rather than asserting
the counting argument in prose. -/
theorem two_band_values_are_always_absent (a b c : Fin 6) :
    ∃ x y : Fin 6, x ≠ y ∧ (x ≠ a ∧ x ≠ b ∧ x ≠ c) ∧ (y ≠ a ∧ y ≠ b ∧ y ≠ c) := by
  revert a b c
  decide

/-- ⚑ **ONE ROUND NEVER DETERMINES THE TARGET.**  For EVERY guess there are two
distinct targets the oracle answers identically, so a single feedback leaves the
target genuinely undecided — for any opening a player or a reader picks.

The witnesses are constructed rather than searched: a guess names at most three of the
six band values, so at least three values are absent from it, and the all-same codes
built from any two of those are indistinguishable (both score a flat zero). -/
theorem one_round_never_determines_the_target (guess : Code) :
    ∃ t₁ t₂ : Code, t₁ ≠ t₂ ∧ feedback t₁ guess = feedback t₂ guess := by
  obtain ⟨x, y, hxy, ⟨xlow, xmid, xhigh⟩, ⟨ylow, ymid, yhigh⟩⟩ :=
    two_band_values_are_always_absent guess.low guess.mid guess.high
  refine ⟨monoCode x, monoCode y, monoCode_injective hxy, ?_⟩
  rw [feedback_of_absent_mono guess x xlow xmid xhigh,
    feedback_of_absent_mono guess y ylow ymid yhigh]

/-- Five intercepted bursts is the complete session budget. -/
abbrev MAX_TURNS : Nat := 5

def byte (n : Nat) : Fin 256 := ⟨n % 256, Nat.mod_lt _ (by omega)⟩

/-! ## The instance draw

The three bands are three CONSUMING rejection-sampled draws off one byte stream —
`SeedDraw.drawBelow? 6`, the same draw `HiddenInstance` goes to trouble to hand a
uniform stream to, and the one its docblock names.

⚑ **WHY THIS IS PARTIAL, AND WHY THERE IS NO FALLBACK.**  216 does not divide
`2^256`, so no TOTAL function from a 32-byte seed onto the 216 targets is exactly
uniform.  An honest uniform draw MUST be able to refuse.  A fallback would not
rescue totality, it would relocate the bias and CONCENTRATE it: `getD zeroCode`
piles the whole excess onto `[0,0,0]`, which is in `aaa` — the one opener class
the design gate reports as unable to win within the five-burst budget.  So the
draw returns `Option Code` and `Config.target_eq` carries the measurement, exactly
the shape `BlackBoxReconstruction.orderFromRunSeed?` / `Config.order_eq` has.

⚑ **WHAT THIS REPLACED, 2026-08-07.**  `targetFromSeed : Digest32 → Code` folded
each byte with `% 6`.  `256 = 42*6 + 4`, so band symbols `0..3` came back 43/256
against 42/256 — the most likely of the 216 targets was 1.0731x the least likely
and the distribution sat 0.0070 in total variation from uniform, in a judged game
whose target is hidden and committed to and which pays a mission reward.
`modulo_fold_is_not_uniform` below keeps that refuted rather than remembered.

Byte-stream partiality is not hypothetical: `all_high_block_seed_refuses` exhibits
a seed the draw declines outright. -/

/-- The draw, on a raw byte stream.  Three consuming draws below 6: each one
discards the incomplete high block (`SeedDraw.ceilingFor 6 = 252`) rather than
folding it, and hands the REMAINING bytes to the next, so the three bands read
disjoint prefixes (`SeedDraw.drawBelow?_consumes`) instead of one byte three
times. -/
def targetFromBytes? (bs : List (Fin 256)) : Option Code :=
  match SeedDraw.drawBelow? 6 (by decide) bs with
  | none => none
  | some (low, s1) =>
    match SeedDraw.drawBelow? 6 (by decide) s1 with
    | none => none
    | some (mid, s2) =>
      match SeedDraw.drawBelow? 6 (by decide) s2 with
      | none => none
      | some (high, _) => some { low, mid, high }

/-- The run seed chooses the puzzle; it is recorded verbatim in the Core receipt.
The mission artifact pins this derivation and the full feedback table.

`none` means this seed draws no instance.  A caller may not substitute one: every
`Config` carries `target_eq`, so a refused seed has no configuration at all. -/
def targetFromSeed? (seed : Digest32) : Option Code := targetFromBytes? seed.bytes

theorem targetFromSeed?_is_the_byte_draw (seed : Digest32) :
    targetFromSeed? seed = targetFromBytes? seed.bytes := rfl

/-! ### The uniformity, measured — and the fold it replaced, refuted

`SeedDraw.draw_is_uniform_on_every_bound` is the general fact: for EVERY bound in
`1..256` each residue has exactly `256 / bound` accepted preimages.  The two
measurements below are about the bound this game actually uses, and they are
stated so that a regression to the fold turns them RED rather than leaving them
true of a function nobody calls. -/

/-- MEASURED at the band bound: the six symbols have exactly 42 accepted preimages
each, and no symbol is favoured. -/
theorem band_draw_fibres_at_six : SeedDraw.fibreSizes 6 = List.replicate 6 42 := by decide

/-- The fibres of the map this module used to apply: `byte % 6` over the WHOLE byte
domain, nothing rejected. -/
def moduloFibres : List Nat :=
  (List.range 6).map fun r => ((List.range 256).filter fun b => b % 6 == r).length

/-- ⚑ **THE DEFECT, KEPT REFUTED.**  The fold is not uniform — four symbols have 43
preimages and two have 42 — and it is not the draw.  These are the two facts the
repair rests on; if `targetFromBytes?` ever folds again they are what goes red. -/
theorem modulo_fold_is_not_uniform : moduloFibres = [43, 43, 43, 43, 42, 42] := by decide

theorem modulo_fold_is_not_the_draw : moduloFibres ≠ SeedDraw.fibreSizes 6 := by decide

/-- ⚑ **PARTIALITY IS REAL, NOT DECORATIVE.**  Every byte of this seed is in the
incomplete high block, so every byte is discarded and the stream runs out: the draw
refuses rather than folding a biased byte.  This is the witness that no total
function could have been written here. -/
theorem all_high_block_seed_refuses :
    targetFromSeed? ⟨List.replicate 32 255, by simp⟩ = none := by decide

/-- The complement: an all-zero stream draws the all-low code.  Stated so the
refusal above cannot be read as the draw refusing everything. -/
theorem zero_seed_draws_the_all_low_code :
    targetFromSeed? ⟨List.replicate 32 0, by simp⟩ =
      some { low := 0, mid := 0, high := 0 } := by decide

/-- ⚑ The three bands are three DRAWS, not one byte read three times: a seed whose
first three bytes differ draws three different bands, in order.  This is the
`SeedDraw.consuming_draw_is_not_a_repeat` property at this call site. -/
theorem bands_are_three_consuming_draws :
    targetFromBytes? ([1, 2, 3] ++ List.replicate 29 0) =
      some { low := 1, mid := 2, high := 3 } := by decide

/-- ⚑ A rejected byte is CONSUMED, not re-read: byte 0 is in the high block, so the
low band comes from byte 1 and the bands shift down the stream.  A draw that
re-read on rejection would return `low = 2` here and the stream would be one byte
out for every band after it. -/
theorem a_rejected_byte_shifts_the_stream :
    targetFromBytes? ([255, 1, 2, 3] ++ List.replicate 28 0) =
      some { low := 1, mid := 2, high := 3 } := by decide

structure Config where
  target       : Code
  mission      : MissionSpec
  reward       : Contribution
  reward_accepted : mission.acceptsContribution reward = true
  /-- ⚠ `some target = …`, not `target = …`: a seed the draw refuses has no
  configuration.  There is no `Option.get`, no default, and no way to name a target
  the seed did not draw. -/
  target_eq : some target = targetFromSeed? mission.runSeed

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
    some cfg.target = targetFromSeed? run.receipt.runSeed := by
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

#assert_axioms targetFromSeed?_is_the_byte_draw
#assert_axioms band_draw_fibres_at_six
#assert_axioms modulo_fold_is_not_uniform
#assert_axioms modulo_fold_is_not_the_draw
#assert_axioms all_high_block_seed_refuses
#assert_axioms zero_seed_draws_the_all_low_code
#assert_axioms bands_are_three_consuming_draws
#assert_axioms a_rejected_byte_shifts_the_stream
#assert_axioms exactCount_le_three
#assert_axioms totalMatches_le_three
#assert_axioms feedback_match_bound
#assert_axioms exactCount_eq_three_iff
#assert_axioms feedback_exact_target
#assert_axioms feedback_present_target
#assert_axioms duplicate_band_example
#assert_axioms feedback_transcript_cannot_separate
#assert_axioms monoCode_injective
#assert_axioms feedback_of_absent_mono
#assert_axioms two_band_values_are_always_absent
#assert_axioms one_round_never_determines_the_target
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
