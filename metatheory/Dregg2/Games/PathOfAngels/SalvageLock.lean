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

## The board is no longer in the wire

The paragraph that used to stand here said the emitted table still published the
board twice — in each action row's `glyph_id`, and in the successors, which say
which exposures clear — and that hiding it needed "a different wire (a commitment
to the board plus per-exposure openings)".  That wire is built.

`Emit` now renders `FiniteTables.salvageParametricTransitions`: a first exposure
is deterministic, and a second names BOTH successors, `on_match` and
`on_mismatch`.  One bit per second exposure comes from the judge, which holds the
live run seed; `FiniteTables.salvage_parametric_table_is_the_kernel` is the
refinement over all ninety boards.  `MissionSpec.runSeed` itself is now derived
per run from a committed slot secret (`HiddenInstance.runSeedFor`), so nothing a
client fetches determines the board.

This kernel did not change.  `Config.seed_eq` still binds the played board to
`mission.runSeed`; what changed is that the seed is no longer published.

## ⛑ The budget: 18, and it was 12 because nobody solved the hidden game

`MAX_TURNS` was 12 from before the board left the wire, and it stayed 12 after.  That
is the whole defect: 12 was sized against a game in which the plates showed their
glyphs, and the game that shipped hands the player ONE BIT per comparison — did these
two match — and no glyph at all.

Exhaustively solved (uniform over the 15 perfect matchings; a comparison is two
exposures; the player learns only match/mismatch and remembers everything):

| exposures | comparisons | perfect play | memoryless | skill band |
| --------- | ----------- | ------------ | ---------- | ---------- |
|  6 |  3 |   1/15 =  6.67% |  6.67% |  0.00 pts |
|  8 |  4 |   3/15 = 20.00% | 16.44% |  3.56 pts |
| 10 |  5 |   6/15 = 40.00% | 27.23% | 12.77 pts |
| **12** |  6 |   **9/15 = 60.00%** | 37.83% | 22.17 pts |
| 14 |  7 |  12/15 = 80.00% | 47.63% | 32.37 pts |
| 16 |  8 |  14/15 = 93.33% | 56.35% | 36.98 pts |
| **18** |  9 |  **15/15 = 100.0%** | **63.91%** | **36.09 pts** |
| 20 | 10 |          100.0% | 70.35% | 29.65 pts |

⚑ **At 12 a player who plays perfectly loses two runs in five.**  Not through a
mistake — the budget sat exactly at the mean of optimal play, so the game punished
correct play and had no way to say so.

**Why 18:**

1. **It is the exact adversarial worst case of the game that actually ships.**  An
   adversary answering any way still consistent with some board forces nine
   comparisons and no more.  So the budget is spent to its LAST EXPOSURE in the worst
   case and is never one short of it: tight, and never cheating.
2. **Correct play is never punished.**  15 of 15.  That was the whole complaint —
   "a player who plays perfectly and loses is right to feel cheated" — and only 18
   answers it.
3. **The skill band costs almost nothing to get there.**  36.09 points against the
   36.98 maximum at 16: 0.89 points, for the property that a perfect player never
   loses.  ⚠ 16 is the band's argmax and it is the WRONG number, because the band
   is a tiebreaker and not the criterion — `scripts/poa-design-gate.py` FAILS a budget
   that refuses more than one perfect run in twenty (`budget-refuses-optimal-play`,
   threshold 95%) and 16 sits at 93.3%, BELOW the repo's own bar.  A first draft of
   this section argued for 16 by quoting the band maximum and not the bar it failed.

**Why an EVEN number.**  A comparison is two exposures and nothing else buys
information, so an odd budget spends its last exposure on a plate whose pair can never
be turned — `a_lone_last_exposure_clears_nothing` is that, proved.  17 and 19 are 16
and 18 with a dead button on the end.

⚠ **The skill band above is a MEASUREMENT, not a theorem in this file.**  It is an
exhaustive backward induction over the belief state (sets of candidate matchings),
which memoizes to nothing in a scripting language and does not fit a Lean structural
recursion without an explicitly tabulated state enumeration — that table is undone
work and is named here rather than dressed up.  The perfect-play column IS
independently checked: `poa-design-gate.py`'s `skill-band-is-real` recomputes it from
the EMITTED rows and agrees (84/90 at 16 — and that agreement is what moved this
number, because the same pass FAILED 16).

⚠ **And one gate measure here is computed on the WRONG GAME.**
`hidden_pairing_worst_case` partitions candidate boards by WHICH previously-seen plate
an exposure matches, which hands the player a glyph identity the emitted rows never
give.  That is the pre-split face-up game; it returns 10 exposures where the one-bit
game's real worst case is 18, and it is why `hidden-board-floor` reports slack on a
budget that is exactly tight.  The gate flags the contradiction itself inside
`budget-refuses-optimal-play`; fixing it belongs to whoever owns the gate.

What this file pins is the SHAPE of the budget — `the_budget_is_nine_comparisons`
and `a_lone_last_exposure_clears_nothing`.
-/
import Dregg2.Games.PathOfAngels.Core
import Dregg2.Games.PathOfAngels.SeedDraw
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.SalvageLock

open Dregg2.Games.PathOfAngels

/-- Exposures a run may spend.  ⚑ 18, not 12 — see the budget section of the header
for the solve.  A comparison is two exposures, so this is nine comparisons. -/
abbrev MAX_TURNS : Nat := 18

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

/-! ⚠ `PINNED_RUN_SEED` is GONE.  It spelled `SALVAGE-1`, it was published in the
descriptor and the catalog, and it therefore named the board to anyone who read
either.  A precommitted constant stops a host grinding the seed after a
transcript; it does not stop a player computing the answer before the run, which
is the property a hidden board needs.  The live seed is now
`HiddenInstance.runSeedFor`, drawn per (slot, mission, player) from a slot secret
the descriptor commits to and does not contain.

### What the seed space actually is

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

/-! ⚑ **THE SEED-SPACE ENUMERATIONS NO LONGER EVALUATE IN THIS MODULE (2026-08-08).** This
module is in the `Dregg2.FFI` closure — the crypto archive's build root — and the four
`native_decide` pins below enumerate 6^6 partner rows, 3^6 glyph rows and all 90 seeds at
elaboration, so any change to the seed space was a hard failure of every Rust proving target in
the workspace (the compilation-unit coupling the stale-fixture outage measured). The pins'
STATEMENTS stay here as evaluation-free `check_* : Bool` definitions (a `def` body elaborates
without running), beside the domains they compare. The EVALUATION — each `check_* = true`,
pinned by `native_decide` + `#assert_compiled` — lives in `SalvageLockFixtures.lean`, rooted in
the `PathOfAngelsGuards` library: a plain `lake build` still runs every pin, and a degenerate
seed space reds the guard library instead of the archive.

Named residue: NONE — nothing here demands a proof as data, so all four pins moved. -/

/-- Six plates admit exactly 15 perfect matchings; every seed names one of them, and
every one of them is named by some seed.  This is the statement the old board failed:
its 3 seeds named ONE matching.
(Pinned `= true` in `SalvageLockFixtures`.) -/
def check_seed_space_realizes_every_perfect_matching : Bool :=
  allMatchings.length == 15 &&
  realizedMatchings.length == 15 &&
  realizedMatchings.all isPerfectMatchingB &&
  allMatchings.all (fun m => realizedMatchings.contains m)

/-- The 90 seeds name 90 distinct boards, and those are exactly the boards carrying
two copies of each glyph: the seed-to-board map is a bijection onto them, so the
seed space is neither degenerate nor redundant.
(Pinned `= true` in `SalvageLockFixtures`.) -/
def check_seed_space_is_exactly_the_two_of_each_boards : Bool :=
  allBoards.length == SEED_SPACE &&
  realizedBoards.length == SEED_SPACE &&
  allBoards.all (fun b => realizedBoards.contains b)

/-- Six seeds share each matching — the 3! relabellings of its pairs — so a glyph
name carries no information about the pairing beyond agreement with a glyph already
seen.  A canonical labelling would leak: "this plate shows glyph 0" would mean "this
plate is plate 0's partner".
(Pinned `= true` in `SalvageLockFixtures`.) -/
def check_every_matching_has_all_six_labellings : Bool :=
  realizedMatchings.all fun m =>
    ((List.finRange SEED_SPACE).filter (fun s => partnerRow s == m)).length == 6

def glyphPopulation (seed : Fin SEED_SPACE) (glyph : Fin 3) : Nat :=
  (allSlots.filter (fun slot => glyphAt seed slot = glyph)).length

/-- Generated boards contain exactly two of each glyph, for every seed.
(Pinned `= true` in `SalvageLockFixtures`.) -/
def check_glyph_population_two : Bool :=
  (List.finRange SEED_SPACE).all fun seed =>
    (List.finRange 3).all fun glyph => glyphPopulation seed glyph == 2

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

/-- ⚑ **The budget is nine COMPARISONS.**  Named so the unit is in the file and not
only in the header: a player never spends an exposure, they spend a pair of them. -/
theorem the_budget_is_nine_comparisons : MAX_TURNS = 2 * 9 := by decide

/-- ⚑ **AND THEREFORE AN ODD BUDGET WOULD BUY NOTHING.**  A first exposure clears no
plate and settles no question; it only turns a plate face up.  So a run that spends its
LAST exposure with nothing already face up ends holding one exposed plate, no new
cleared pair, and no legal move — the exposure is a button that cannot be answered.

This is why `MAX_TURNS` is even, and it is the whole argument: 15 and 17 are 14 and 16
with a dead press on the end. -/
theorem a_lone_last_exposure_clears_nothing (cfg : Config) (s : State) (slot : Fin 6)
    (hnone : s.exposed = none) (hlast : s.turns + 1 = MAX_TURNS) {s' : State}
    (h : step cfg s (.expose slot) = some s') :
    s'.cleared = s.cleared ∧ ∀ a : Action, step cfg s' a = none := by
  simp only [step, hnone] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst s'
    refine ⟨rfl, fun a => exhausted_refuses cfg _ a ?_⟩
    simp only []
    omega
  · exact absurd h (by simp)

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

-- The four seed-space pins (`native_decide` + `#assert_compiled`) live in
-- `SalvageLockFixtures.lean`, rooted in `PathOfAngelsGuards` — see the note above them.
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
#assert_axioms the_budget_is_nine_comparisons
#assert_axioms a_lone_last_exposure_clears_nothing
#assert_axioms replay_append
#assert_axioms refused_prefix_refuses_replay
#assert_axioms terminalOutput_is_mission_accepted
#assert_axioms terminalOutput_names_exact_beta_artifact
#assert_axioms terminalOutput_canonical
#assert_axioms judge_some_sound
#assert_axioms judge_receipt_binds_seed
#assert_axioms judge_receipt_binds_transcript

end Dregg2.Games.PathOfAngels.SalvageLock
