/-
# Salvage Lock — a seeded paired-glyph hatch

Six sealed plates carry exactly two copies of each of three glyphs.  One plate may
remain exposed between actions; the second exposure either clears a matching pair or
closes both.  The type therefore makes an impossible "three exposed plates" state
unrepresentable.  All shared-world effects go through `judge` and Core's receipt.

Substrate note: this is Lean-authored game semantics.  Nothing here is an AIR, a
constraint system or a gadget; Rust and TypeScript dispatch the finite table this
board generates, they do not carry a second copy of the rules.

## The board is the seed

The board used to be `glyphAt seed slot = (slot + seed) % 3` over a three-element
seed space.  Every seed produced the SAME pairing `[[0,3],[1,4],[2,5]]` — the seed
only renamed the glyphs — so `pair = slot mod 3` cleared the hatch on every seed
without remembering anything and without reading the instance.  The seed space was
nominally 3 and effectively 1.

The board is now drawn from the run seed by four CONSUMING draws
(`SeedDraw.drawBelow?`): the partner of plate 0 (5 ways), the partner of the lowest
remaining plate (3 ways), and which of the three glyph names labels each resulting
pair (3! ways).  5 * 3 * 3! = 90, which is exactly the number of six-plate rows
carrying two copies of each of three glyphs, and the induced pairing ranges over all
15 perfect matchings of six plates.  Both facts are proved below against
INDEPENDENTLY ENUMERATED domains — every one of the 6^6 candidate partner functions
and every one of the 3^6 candidate glyph rows — so the construction cannot satisfy
them by agreeing with itself.

⚠ What this does NOT do.  The emitted POAG1 finite table still publishes the board:
in the `glyph_id` of every action row, and — unavoidably in that wire — in the
transition table itself, whose successors say which exposures clear.  A player who
fetches the descriptor reads the instance off it either way, so removing `glyph_id`
would silence a gate without hiding anything.  Seeding the board makes the run seed
load-bearing, kills the memory-free universal routine, and gives the hidden game a
real instance underneath; ACTUALLY hiding it needs a different wire (a commitment to
the board plus per-exposure openings judged in Lean), which is not built here.
-/
import Dregg2.Games.PathOfAngels.Core
import Dregg2.Games.PathOfAngels.SeedDraw
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.SalvageLock

open Dregg2.Games.PathOfAngels

abbrev MAX_TURNS : Nat := 12

/-- How many distinct boards a seed can name: 6! / (2! * 2! * 2!) = 90 rows of six
plates carrying two copies of each of three glyphs. -/
abbrev SEED_SPACE : Nat := 90

def byte (n : Nat) : Fin 256 := ⟨n % 256, Nat.mod_lt _ (by omega)⟩

def allSlots : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-! ## The seeded board -/

/-- Which of the five candidate partners plate 0 takes. -/
def partnerIndex (seed : Fin SEED_SPACE) : Nat := seed.val / 18

/-- Which of the three remaining candidates the lowest unpaired plate takes. -/
def secondIndex (seed : Fin SEED_SPACE) : Nat := (seed.val % 18) / 6

/-- Which glyph name labels the pair containing plate 0. -/
def firstGlyphIndex (seed : Fin SEED_SPACE) : Nat := (seed.val % 6) / 2

/-- Which of the two remaining glyph names labels the second pair. -/
def secondGlyphIndex (seed : Fin SEED_SPACE) : Nat := seed.val % 2

/-- The perfect matching of the six plates a seed names.  Pair 0 contains plate 0,
pair 1 contains the lowest plate outside pair 0, pair 2 is what is left. -/
def pairsOf (seed : Fin SEED_SPACE) : List (Fin 6 × Fin 6) :=
  let rest0 : List (Fin 6) := [1, 2, 3, 4, 5]
  let p := rest0.getD (partnerIndex seed) 1
  let rest1 := rest0.filter (fun x => x != p)
  let m := rest1.getD 0 1
  let rest2 := rest1.filter (fun x => x != m)
  let q := rest2.getD (secondIndex seed) 2
  let rest3 := rest2.filter (fun x => x != q)
  [(0, p), (m, q), (rest3.getD 0 2, rest3.getD 1 3)]

/-- The glyph names, in the order the seed assigns them to `pairsOf`. -/
def glyphNamesOf (seed : Fin SEED_SPACE) : List (Fin 3) :=
  let names : List (Fin 3) := [0, 1, 2]
  let g0 := names.getD (firstGlyphIndex seed) 0
  let rest1 := names.filter (fun x => x != g0)
  let g1 := rest1.getD (secondGlyphIndex seed) 0
  let rest2 := rest1.filter (fun x => x != g1)
  [g0, g1, rest2.getD 0 0]

/-- The board as a six-glyph row, plate 0 first. -/
def boardRow (seed : Fin SEED_SPACE) : List (Fin 3) :=
  let tagged := (pairsOf seed).zip (glyphNamesOf seed)
  allSlots.map fun slot =>
    match tagged.find? (fun pg => pg.1.1 == slot || pg.1.2 == slot) with
    | some pg => pg.2
    | none => 0

/-- The partner of each plate, plate 0 first: the matching as a function. -/
def partnerRow (seed : Fin SEED_SPACE) : List (Fin 6) :=
  let ps := pairsOf seed
  allSlots.map fun slot =>
    match ps.find? (fun pr => pr.1 == slot || pr.2 == slot) with
    | some pr => if pr.1 == slot then pr.2 else pr.1
    | none => slot

/-- The glyph sealed under a plate. -/
def glyphAt (seed : Fin SEED_SPACE) (slot : Fin 6) : Fin 3 :=
  (boardRow seed).getD slot.val 0

/-- The run seed drawn into a board index by four CONSUMING draws.  A `none` is an
exhausted byte stream and nothing else: the index carries its bound out of the draws
themselves, so there is no range check that could silently fold an out-of-range
value back into the seed space. -/
def seedFromRunSeed? (runSeed : Digest32) : Option (Fin SEED_SPACE) :=
  match SeedDraw.drawBelow? 5 (by decide) runSeed.bytes with
  | none => none
  | some (a, s1) =>
    match SeedDraw.drawBelow? 3 (by decide) s1 with
    | none => none
    | some (b, s2) =>
      match SeedDraw.drawBelow? 3 (by decide) s2 with
      | none => none
      | some (c, s3) =>
        match SeedDraw.drawBelow? 2 (by decide) s3 with
        | none => none
        | some (d, _) =>
          some ⟨18 * a.val + 6 * b.val + 2 * c.val + d.val, by
            have ha := a.isLt
            have hb := b.isLt
            have hc := c.isLt
            have hd := d.isLt
            show _ < 90
            omega⟩

/-- The complete precommitted run seed for the beta Salvage mission: the tag spells
`SALVAGE-1`, and the remaining bytes are zero by construction, so a host cannot grind
them after seeing a transcript.  It lives here rather than in `Emit` because the
BOARD — and therefore the entire finite table — is derived from it.

⚠ The leading `2` byte this constant used to carry is GONE.  Its only function was
`(runSeed.bytes.getD 0 0) % 3 = 2` under the deleted board, i.e. it selected old seed
2; it named nothing and it would have read as a version or domain byte to the next
person.  Removing it also makes the shipped fixture DISTINGUISH the two draw shapes:
the consuming draws read bytes `S`, `A`, `L`, `V` and land on board 68, while a draw
with no cursor would read `S` four times and land on 71.  With the leading `2` in
place both shapes landed on 52 and the fixture was blind to the difference. -/
def PINNED_RUN_SEED : Digest32 where
  bytes := List.ofFn fun i : Fin 32 =>
    match ([83, 65, 76, 86, 65, 71, 69, 45, 49] : List Nat)[i.val]? with
    | some n => ⟨n % 256, Nat.mod_lt _ (by decide)⟩
    | none => 0
  length_eq := by simp

/-! ### What the seed space actually is

Checked against independently enumerated domains rather than against `pairsOf` /
`boardRow` restated: `allMatchings` filters all 6^6 candidate partner functions by
"fixed-point-free involution", which is what a perfect matching of six plates IS,
and `allBoards` filters all 3^6 candidate glyph rows by "two of each glyph". -/

/-- Every row of length `n` over an alphabet. -/
def rowsOver {α : Type} (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => (rowsOver alphabet n).flatMap fun row => alphabet.map fun x => x :: row

/-- A perfect matching of the six plates is exactly a fixed-point-free involution of
them: no plate is its own partner, and partnering twice returns. -/
def isPerfectMatchingB (row : List (Fin 6)) : Bool :=
  (List.finRange 6).all fun i =>
    let j := row.getD i.val i
    j != i && row.getD j.val j == i

/-- All perfect matchings of six plates, over all 6^6 candidate partner rows. -/
def allMatchings : List (List (Fin 6)) :=
  (rowsOver (List.finRange 6) 6).filter isPerfectMatchingB

/-- All six-plate boards carrying two copies of each glyph, over all 3^6 candidate
glyph rows. -/
def allBoards : List (List (Fin 3)) :=
  (rowsOver (List.finRange 3) 6).filter fun row =>
    (List.finRange 3).all fun g => (row.filter (fun x => x == g)).length == 2

/-- The matchings the seed space actually produces. -/
def realizedMatchings : List (List (Fin 6)) :=
  ((List.finRange SEED_SPACE).map partnerRow).eraseDups

/-- The boards the seed space actually produces. -/
def realizedBoards : List (List (Fin 3)) :=
  ((List.finRange SEED_SPACE).map boardRow).eraseDups

/-- Six plates admit exactly 15 perfect matchings; every seed names one of them, and
every one of them is named by some seed.  This is the statement the old board failed:
its 3 seeds named ONE matching. -/
theorem seed_space_realizes_every_perfect_matching :
    (allMatchings.length == 15 &&
      realizedMatchings.length == 15 &&
      realizedMatchings.all isPerfectMatchingB &&
      allMatchings.all (fun m => realizedMatchings.contains m)) = true := by
  native_decide

/-- The 90 seeds name 90 distinct boards, and those are exactly the boards carrying
two copies of each glyph: the seed-to-board map is a bijection onto them, so the
seed space is neither degenerate nor redundant. -/
theorem seed_space_is_exactly_the_two_of_each_boards :
    (allBoards.length == SEED_SPACE &&
      realizedBoards.length == SEED_SPACE &&
      allBoards.all (fun b => realizedBoards.contains b)) = true := by
  native_decide

/-- Six seeds share each matching — the 3! relabellings of its pairs — so a glyph
name carries no information about the pairing beyond agreement with a glyph already
seen.  A canonical labelling would leak: "this plate shows glyph 0" would mean "this
plate is plate 0's partner". -/
theorem every_matching_has_all_six_labellings :
    (realizedMatchings.all fun m =>
      ((List.finRange SEED_SPACE).filter (fun s => partnerRow s == m)).length == 6) = true := by
  native_decide

def glyphPopulation (seed : Fin SEED_SPACE) (glyph : Fin 3) : Nat :=
  (allSlots.filter (fun slot => glyphAt seed slot = glyph)).length

/-- Generated boards contain exactly two of each glyph, for every seed. -/
theorem glyph_population_two :
    ((List.finRange SEED_SPACE).all fun seed =>
      (List.finRange 3).all fun glyph => glyphPopulation seed glyph == 2) = true := by
  native_decide

structure Config where
  seed : Fin SEED_SPACE
  mission : MissionSpec
  reward : Contribution
  reward_accepted : mission.acceptsContribution reward = true
  seed_eq : some seed = seedFromRunSeed? mission.runSeed

structure State where
  cleared : Finset (Fin 6)
  exposed : Option (Fin 6)
  turns : Nat
deriving DecidableEq

def initialState : State := { cleared := ∅, exposed := none, turns := 0 }

inductive Action where
  | expose (slot : Fin 6)
deriving Repr, DecidableEq

def solvedB (s : State) : Bool := s.cleared.card == 6

def openB (s : State) (slot : Fin 6) : Bool :=
  !solvedB s &&
  s.turns < MAX_TURNS &&
  decide (slot ∉ s.cleared) &&
  decide (s.exposed ≠ some slot)

def step (cfg : Config) (s : State) : Action → Option State
  | .expose slot =>
      if openB s slot then
        match s.exposed with
        | none => some { s with exposed := some slot, turns := s.turns + 1 }
        | some first =>
            let cleared :=
              if glyphAt cfg.seed first = glyphAt cfg.seed slot then
                insert slot (insert first s.cleared)
              else
                s.cleared
            some { cleared, exposed := none, turns := s.turns + 1 }
      else
        none

def replay (cfg : Config) : State → List Action → Option State
  | s, [] => some s
  | s, a :: as =>
      match step cfg s a with
      | none => none
      | some s' => replay cfg s' as

private def terminalOutput (cfg : Config) (s : State) : Option (Contribution × ArtifactRef) :=
  if solvedB s then some (cfg.reward, cfg.mission.artifact) else none

def actionSlot : Action → Fin 6
  | .expose slot => slot

def actionAt (actions : List Action) (i : Nat) : Nat :=
  match actions[i]? with
  | some a => (actionSlot a).val
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

def remaining (s : State) : Nat := MAX_TURNS - s.turns

def exposedCount (s : State) : Nat :=
  match s.exposed with
  | none => 0
  | some _ => 1

theorem exposed_population_le_one (s : State) : exposedCount s ≤ 1 := by
  cases h : s.exposed <;> simp [exposedCount, h]

theorem step_deterministic (cfg : Config) (s : State) (a : Action) {s₁ s₂ : State}
    (h₁ : step cfg s a = some s₁) (h₂ : step cfg s a = some s₂) : s₁ = s₂ := by
  rw [h₁] at h₂
  exact Option.some.inj h₂

theorem step_some_turns (cfg : Config) (s : State) (a : Action) {s' : State}
    (h : step cfg s a = some s') : s'.turns = s.turns + 1 := by
  cases a with
  | expose slot =>
      simp only [step] at h
      split at h
      · split at h
        · simp only [Option.some.injEq] at h
          subst s'
          rfl
        · simp only [Option.some.injEq] at h
          subst s'
          rfl
      · contradiction

theorem step_some_bound (cfg : Config) (s : State) (a : Action) {s' : State}
    (h : step cfg s a = some s') : s'.turns ≤ MAX_TURNS := by
  have ht := step_some_turns cfg s a h
  cases a with
  | expose slot =>
    simp only [step] at h
    split at h
    · rename_i hop
      have hlt : s.turns < MAX_TURNS := by
        simp only [openB, Bool.and_eq_true, decide_eq_true_eq] at hop
        exact hop.1.1.2
      omega
    · contradiction

theorem remaining_strictly_decreases (cfg : Config) (s : State) (a : Action) {s' : State}
    (h : step cfg s a = some s') : remaining s' < remaining s := by
  have ht := step_some_turns cfg s a h
  have hb := step_some_bound cfg s a h
  simp only [remaining]
  omega

theorem cleared_never_shrinks (cfg : Config) (s : State) (a : Action) {s' : State}
    (h : step cfg s a = some s') : s.cleared ⊆ s'.cleared := by
  cases a with
  | expose slot =>
      simp only [step] at h
      split at h
      · split at h
        · simp only [Option.some.injEq] at h
          subst s'
          exact Finset.Subset.rfl
        · split at h
          · simp only [Option.some.injEq] at h
            subst s'
            exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
          · simp only [Option.some.injEq] at h
            subst s'
            exact Finset.Subset.rfl
      · contradiction

theorem matching_second_exposure_clears (cfg : Config) (s : State) (first slot : Fin 6)
    (hopen : openB s slot = true)
    (hexposed : s.exposed = some first)
    (hmatch : glyphAt cfg.seed first = glyphAt cfg.seed slot) :
    step cfg s (.expose slot) = some {
      cleared := insert slot (insert first s.cleared)
      exposed := none
      turns := s.turns + 1
    } := by
  simp [step, hopen, hexposed, hmatch]

theorem duplicate_exposure_refused (cfg : Config) (s : State) (slot : Fin 6)
    (h : s.exposed = some slot) : step cfg s (.expose slot) = none := by
  simp [step, openB, h]

theorem cleared_slot_refused (cfg : Config) (s : State) (slot : Fin 6)
    (h : slot ∈ s.cleared) : step cfg s (.expose slot) = none := by
  simp [step, openB, h]

theorem solved_refuses (cfg : Config) (s : State) (a : Action)
    (h : solvedB s = true) : step cfg s a = none := by
  cases a <;> simp [step, openB, h]

theorem exhausted_refuses (cfg : Config) (s : State) (a : Action)
    (h : MAX_TURNS ≤ s.turns) : step cfg s a = none := by
  cases a <;> simp [step, openB, Nat.not_lt.mpr h]

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

/-- The receipt binds the BOARD, not just a nonce: the run seed it carries is the
one the config's board was drawn from.  A host cannot show a transcript against a
board it picked after the fact. -/
theorem judge_receipt_binds_seed (cfg : Config) (before : WorldState) (ctx : JudgeContext)
    (actions : List Action) {run : JudgedRun} (h : judge cfg before ctx actions = some run) :
    some cfg.seed = seedFromRunSeed? run.receipt.runSeed := by
  have hs := judge_some_sound cfg before ctx actions h
  rw [run.receipt.run_seed_matches, hs.2.2.2.1]
  exact cfg.seed_eq

theorem judge_receipt_binds_transcript (cfg : Config) (before : WorldState) (ctx : JudgeContext)
    (actions : List Action) {run : JudgedRun} (h : judge cfg before ctx actions = some run) :
    run.receipt.transcriptDigest = transcriptDigest actions := by
  exact (judge_some_sound cfg before ctx actions h).2.2.2.2

#assert_compiled seed_space_realizes_every_perfect_matching
#assert_compiled seed_space_is_exactly_the_two_of_each_boards
#assert_compiled every_matching_has_all_six_labellings
#assert_compiled glyph_population_two
#assert_axioms exposed_population_le_one
#assert_axioms step_deterministic
#assert_axioms step_some_turns
#assert_axioms step_some_bound
#assert_axioms remaining_strictly_decreases
#assert_axioms cleared_never_shrinks
#assert_axioms matching_second_exposure_clears
#assert_axioms duplicate_exposure_refused
#assert_axioms cleared_slot_refused
#assert_axioms solved_refuses
#assert_axioms exhausted_refuses
#assert_axioms replay_append
#assert_axioms refused_prefix_refuses_replay
#assert_axioms terminalOutput_is_mission_accepted
#assert_axioms terminalOutput_names_exact_beta_artifact
#assert_axioms terminalOutput_canonical
#assert_axioms judge_some_sound
#assert_axioms judge_receipt_binds_seed
#assert_axioms judge_receipt_binds_transcript

end Dregg2.Games.PathOfAngels.SalvageLock
