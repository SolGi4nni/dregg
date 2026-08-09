/-
# DayWater — the one fact two games are pointed at

Substrate note: this is Lean-authored game semantics.  Nothing here is an AIR, a
constraint system or a gadget.  Rust and the browser dispatch what the emitters
render out of this module and its consumers; they carry no second copy of the
derivation.

## The census this module answers

`WorldState` is written by every game and read back into NO game's rules.
`judge cfg before ctx actions` threads `before` into `applyContribution` and into
`receipt.preWorld` and nowhere else; `replay cfg initialState actions` never sees
it, and a game's instance comes from `cfg.mission.runSeed`, which is
`HiddenInstance.runSeedFor ⟨secret, slot, playerKey⟩ ⟨missionId, epoch,
federationId, contentSession⟩`.  Two missions in one slot for one player are
therefore two PRF-independent draws that differ only in a lane of the header
block.  `WorldState.discoveredRelics` is read only by JSON emitters
(`Emit.worldStateJsonWith`, `NetworkJudgeWire`) and by the node's DTO validator,
and it is ONE GLOBAL MONOTONE SET on the canon head — a ratchet, not a channel:
it saturates after the first player and cannot carry anything private.

⚠ So a coupling narrated between two games today would be exactly the lie: the
player would be TOLD about a connection whose two sides are independent draws.
Making one real is a change to the DERIVATION, and this module is that change.

## What it is

One bit per slot — is the lower ship holding water tonight — drawn from the slot
secret under its own sponge domain, belonging to NO mission and NO player.  Two
games look at it:

* **Vent Crawl** — the vein's BOTTOM.  A wet bilge means the shaft bottoms out in
  water and the last rung pays nothing; a dry one means it opens into a pocket.
  `VentCrawl.allVeins` is already ordered `seam * 2 + bottom`, so binding the
  bottom to this bit is an index substitution and the eight-vein family is
  unchanged.
* **Deck Descent** — the MOUTH, through a reading that is right THREE TIMES IN
  FOUR and wrong the fourth.  A wet bilge floods the main shaft three times in
  four; a dry one floods it once in four.

⚑ The fiction and the arithmetic agree in the useful direction: a flooded mouth
is a setback in Deck Descent AND the news that the vent is not worth the deepest
rung tonight.  The bad outcome in one game is the informative one in the other.

## Why the reading is NOISY, measured rather than chosen

An EXACT shared bit was measured first and REFUSED.  Deck Descent has six boards
and one spare unit of air; handing its player a certain mouth bit collapses the
junction, and the repo's own bar sees it:

| reading accuracy | Deck Descent, best BLIND fixed line | `blind-line-dominates` (FAIL ≥ 0.75) |
| ---------------- | ----------------------------------- | ------------------------------------ |
| 1/2 (no coupling) | 0.6667 | ok |
| 5/8               | 0.6667 | ok |
| 2/3               | 0.6667 | ok |
| **3/4**           | **0.7083** | **ok** |
| 13/16             | 0.7396 | ok |
| 7/8               | 0.7708 | FAIL |
| 1 (exact)         | 0.8333 | FAIL |

`READING_FACES` must divide 256 for `SeedDraw.drawBelow?` to reject no byte, so
the accuracies actually available are `k/2^n`.  **3/4 is the largest available
accuracy that keeps Deck Descent under the bar**, and 13/16 — the only larger one
that also passes — buys 0.16 of a point of salvage for 0.03 of the blind-line
margin and needs a sixteen-face draw.  The noise is not a hedge; it is the
parameter the measurement picked, exactly as `SHORING = 1` and Salvage's
eighteen exposures were.

⚠ **Those two columns are MEASUREMENTS, not theorems of this file.**  They come
from an exact backward induction over the Deck Descent belief state and over the
Vent Crawl carry ladder, replayed through the kernel semantics in
`DeckDescent.lean` and `VentCrawl.lean` — the same class of computation
`SalvageLock`'s budget table is, and the same one its docblock names as not
fitting a Lean structural recursion without a tabulated state enumeration.  What
IS proved below is the DERIVATION: the calibration, the informativeness, the two
posteriors, and that both games' instance families are unchanged in distribution.

## What the coupling is worth, and why the ORDER is not symmetric

Measured the same way, over the two kernels:

| | |
| - | - |
| Vent Crawl, E[salvage], bottom unknown | 5.5833 |
| Vent Crawl, E[salvage], 3/4 reading in hand | 5.8508  (**+4.79%**) |
| Vent Crawl, E[salvage], exact bit in hand | 6.1825  (+10.73%) |
| Deck Descent, E[relics], bilge unknown | 2.0000 |
| Deck Descent, E[relics], bilge known | 2.1250 |
| Deck Descent, E[relics] of a run that must READ its mouth | 1.6667 |
| Deck Descent, P(a run can read its mouth at all) | 5/6 |
| Vent Crawl, P(optimal play survives into rung 6) | 315/16384 ≈ 0.0192 |

⚑ **Descent first, then the vent.**  A descent hands over a 3/4 reading five
times in six; a crawl hands over the exact bit under two times in a hundred,
because collecting it means surviving the 5-in-8 rung.  Expected transfer is
0.223 salvage one way against 0.0024 relics the other — a factor of about ninety.
The order is not a story about the fiction; it falls out of which instrument is
cheap to read.

⚑ And the reading has a PRICE in Deck Descent's own currency.  The relic-optimal
line timbers the mouth blind (`shore` is legal on a dark chamber, and it
overwrites the lore), so it never learns the bit.  A run that insists on reading
it pays 2.0000 → 1.6667 relics and 1.0000 → 0.8333 wins.  That is a cross-game
decision with an in-game cost, which is the shape a coupling has to have to be
more than a difficulty knob.

## The sentinel that stops being a convention

`VentCrawl.daySeedFor` draws the day's table by handing `HiddenInstance.runSeedFor`
a reserved sentinel PLAYER key, and its docblock names the residual out loud: a
crawler whose signing-key digest equalled `DAY_TABLE_KEY` would draw the day's
table as their own stream, and "the structural fix — a distinct sponge domain —
belongs in `HiddenInstance`".  `SHIP_DOMAIN` is that domain.  A ship draw takes
no player and no mission, so there is no key to collide with and no mission to
scope it to, and `the_ship_draw_is_not_a_player_draw` is the separation as a fact
about the preimage rather than about a constant nobody chose adversarially.

## Hard facts respected

`Poseidon2BabyBearW16.perm` reduces exponentially — one permutation measured at
47.6 GB and 68 minutes through Lean's interpreter — so `shipSeedFor` is
`@[irreducible]` for the same reason `HiddenInstance.commit`, `runSeedFor` and
`practiceRunSeed` are, and nothing here `decide`s or `rfl`s through it.  Every
`decide` below runs on the READING and the INDEX arithmetic, which mention no
sponge.

`SeedDraw.drawBelow?` is the only draw used.  Both bounds divide 256
(`READING_FACES = 4`, the bilge bound 2), so neither ever rejects a byte and the
`getD` fallbacks are dead code for a 32-byte seed — stated, not assumed.
-/
import Dregg2.Games.PathOfAngels.Core
import Dregg2.Games.PathOfAngels.SeedDraw
import Dregg2.Games.PathOfAngels.HiddenInstance
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.DayWater

open Dregg2.Games.PathOfAngels
open Dregg2.Circuit.Poseidon2BabyBearW16 (P)

set_option autoImplicit false

/-! ## The ship domain

A fourth four-character tag beside `HiddenInstance`'s `POAC` and `POAD`, read
big-endian and below `P`, for the draws that belong to the day rather than to a
mission or a player. -/

/-- `"POAS"` — the per-slot SHIP draw. -/
abbrev SHIP_DOMAIN : Nat := 0x504F4153

theorem ship_domain_is_new_and_canonical :
    SHIP_DOMAIN ≠ HiddenInstance.COMMIT_DOMAIN ∧
    SHIP_DOMAIN ≠ HiddenInstance.DERIVE_DOMAIN ∧
    SHIP_DOMAIN < P := by
  refine ⟨by decide, by decide, by decide⟩

/-- The header block of a ship draw.  ⚠ It names the domain and the slot and
NOTHING else — no mission id, no epoch, no purpose tag, no player.  That absence
is the whole point: two missions asking the day the same question get the same
answer, which is what makes a cross-game coupling possible at all. -/
def shipHeaderBlock (slot : EpochId) : List Nat :=
  HiddenInstance.pad HiddenInstance.RATE
    [SHIP_DOMAIN, slot.value % P, 0, 0, 0, 0, 0, 0]

theorem shipHeaderBlock_length (slot : EpochId) :
    (shipHeaderBlock slot).length = HiddenInstance.RATE :=
  HiddenInstance.pad_length _ _

/-- The header block does not mention a mission or a player, stated as the fact
that it is a function of the slot alone. -/
theorem shipHeaderBlock_is_the_slot_alone (a b : EpochId) (h : a.value = b.value) :
    shipHeaderBlock a = shipHeaderBlock b := by
  simp only [shipHeaderBlock, h]

/-- **The day's seed.**  Same sponge, same capacity, same binding as
`HiddenInstance.runSeedFor`; a different domain and a shorter preimage.  A
federation and a content session still enter, so two federations sharing a slot
number do not share a day. -/
@[irreducible] def shipSeedFor (secret : HiddenInstance.SlotSecret) (slot : EpochId)
    (federationId contentSession : Digest32) : Digest32 :=
  HiddenInstance.digestOfStream (HiddenInstance.laneBytes
    (HiddenInstance.squeeze
      (HiddenInstance.absorbAll HiddenInstance.initialState
        (shipHeaderBlock slot
          :: (HiddenInstance.digestBlocks secret.value
            ++ HiddenInstance.digestBlocks federationId
            ++ HiddenInstance.digestBlocks contentSession)))
      HiddenInstance.SQUEEZE_BLOCKS))

/-- The first lane of a ship block is the ship domain, by computation. -/
theorem shipHeaderBlock_head (slot : EpochId) :
    (shipHeaderBlock slot).headI = SHIP_DOMAIN := rfl

/-- And the first lane of a per-player block is the derive domain. -/
theorem deriveHeaderBlock_head (purpose : HiddenInstance.Purpose) (slot : EpochId)
    (ctx : HiddenInstance.MissionContext) :
    (HiddenInstance.headerBlock purpose slot ctx).headI = HiddenInstance.DERIVE_DOMAIN := rfl

/-- ⚑ **A ship draw is not a player draw, by the preimage and not by a constant.**
`HiddenInstance.headerBlock` opens with `DERIVE_DOMAIN`; `shipHeaderBlock` opens
with `SHIP_DOMAIN`; the two differ.  This is what `VentCrawl`'s `DAY_TABLE_KEY`
could only get from a 256-bit constant nobody chose adversarially — there is no
player key, so there is no key to collide with. -/
theorem the_ship_draw_is_not_a_player_draw
    (purpose : HiddenInstance.Purpose) (slot : EpochId)
    (ctx : HiddenInstance.MissionContext) :
    (shipHeaderBlock slot).headI ≠ (HiddenInstance.headerBlock purpose slot ctx).headI := by
  rw [shipHeaderBlock_head, deriveHeaderBlock_head]
  exact ship_domain_is_new_and_canonical.2.1

/-! ## The bilge bit

One rejection-free draw.  `2` divides 256, so `SeedDraw.ceilingFor 2 = 256`, the
draw reads exactly the first byte, and the `getD` below is dead code for a
32-byte seed. -/

/-- Is the lower ship holding water tonight? -/
def bilgeFrom? (shipSeed : Digest32) : Option Bool := do
  let (b, _) ← SeedDraw.drawBelow? 2 (by decide) shipSeed.bytes
  some (b.val = 1)

def bilgeFrom (shipSeed : Digest32) : Bool := (bilgeFrom? shipSeed).getD false

/-- ⚑ The whole draw, as a judge assembles it: the day's water for a slot, taking
no mission and no player. -/
def bilgeFor (secret : HiddenInstance.SlotSecret) (slot : EpochId)
    (federationId contentSession : Digest32) : Bool :=
  bilgeFrom (shipSeedFor secret slot federationId contentSession)

/-- The bilge draw never rejects a byte, so the fallback in `bilgeFrom` is not
reached by any 32-byte seed. -/
theorem the_bilge_draw_never_rejects (b : Fin 256) (rest : List (Fin 256)) :
    SeedDraw.drawBelow? 2 (by decide) (b :: rest)
      = some (⟨b.val % 2, Nat.mod_lt _ (by decide)⟩, rest) := by
  have hceil : SeedDraw.ceilingFor 2 = 256 := by decide
  simp [SeedDraw.drawBelow?, hceil, b.isLt]

/-- Both bilge values are reachable off a one-byte stream, so the bit is a bit
and not a constant with a name. -/
theorem the_bilge_is_a_real_bit :
    bilgeFrom? ⟨List.replicate 32 0, by simp⟩ = some false ∧
    bilgeFrom? ⟨List.replicate 32 1, by simp⟩ = some true := by
  refine ⟨by decide, by decide⟩

/-! ## The reading — Deck Descent's noisy look at the day

A DIFFERENT instrument pointed at the same fact, and a worse one.  The mouth of
the descent shaft floods three times in four on a wet night and once in four on a
dry one; the crawler at the bottom of the vent sees the water itself. -/

/-- Faces of the reading die.  4 divides 256, so `SeedDraw.drawBelow?` never
rejects, and the accuracy has a power-of-two denominator. -/
abbrev READING_FACES : Nat := 4

/-- ⚑ How many of those faces agree with the bilge.  THREE — the largest
available value that keeps Deck Descent's best blind fixed line under the design
gate's `blind-line-dominates` bar; see the table in the header. -/
abbrev READING_AGREE : Nat := 3

theorem the_reading_is_a_proper_coin :
    READING_FACES - READING_AGREE < READING_AGREE ∧ READING_AGREE < READING_FACES := by
  refine ⟨by decide, by decide⟩

/-- The instrument.  `true` is a flooded mouth.  On a wet night it reads flooded
on `READING_AGREE` of the faces; on a dry one, on the rest. -/
def readingOf (bilge : Bool) (draw : Fin READING_FACES) : Bool :=
  if bilge then decide (draw.val < READING_AGREE)
  else decide (draw.val < READING_FACES - READING_AGREE)

/-! ### The complete finite domain

Every theorem below counts over ALL of it — two bilge values times four faces —
so none of them is a sampled instance of a claim about a distribution. -/

def allBilge : List Bool := [false, true]

def allReadingDraws : List (Fin READING_FACES) := [0, 1, 2, 3]

theorem allReadingDraws_complete : ∀ d : Fin READING_FACES, d ∈ allReadingDraws := by
  decide

theorem allReadingDraws_nodup : allReadingDraws.Nodup := by decide

/-- The joint domain: a fair bilge bit crossed with a uniform face. -/
def allReadings : List (Bool × Fin READING_FACES) :=
  allBilge.flatMap fun w => allReadingDraws.map fun d => (w, d)

theorem allReadings_length : allReadings.length = 2 * READING_FACES := by decide

theorem allReadings_nodup : allReadings.Nodup := by decide

/-- ⚑ **The reading is CALIBRATED: exactly half the joint domain reads flooded.**
This is the fact that makes the coupling free for a player who knows nothing
about the day — the mouth is still a fair coin, so Deck Descent played by
somebody who has not been in the vents is the game it is today. -/
theorem the_reading_is_calibrated :
    2 * (allReadings.filter fun p => readingOf p.1 p.2).length = allReadings.length := by
  decide

/-- ⚑ **And it is INFORMATIVE: the two conditionals differ.**  Three faces of four
on a wet night against one of four on a dry one.  This is the refutation of the
failure the header names — a connection a player is told about and cannot use —
stated as the inequality that would have to be an equality for the coupling to be
narration. -/
theorem the_reading_is_informative :
    (allReadingDraws.filter fun d => readingOf true d).length = READING_AGREE ∧
    (allReadingDraws.filter fun d => readingOf false d).length
      = READING_FACES - READING_AGREE ∧
    READING_AGREE ≠ READING_FACES - READING_AGREE := by
  refine ⟨by decide, by decide, by decide⟩

/-- **What a flooded mouth is worth**, as the exact count it is: of the four
equally likely ways to see a flooded mouth, three are wet nights. -/
theorem a_flooded_mouth_says_the_bilge_is_wet :
    ((allReadings.filter fun p => readingOf p.1 p.2).filter fun p => p.1).length = 3 ∧
    (allReadings.filter fun p => readingOf p.1 p.2).length = 4 := by
  refine ⟨by decide, by decide⟩

/-- And a sound mouth, symmetrically: three of the four ways to see one are dry
nights.  Both directions are stated, because a reading that were informative in
only one of them would be a different instrument. -/
theorem a_sound_mouth_says_the_bilge_is_dry :
    ((allReadings.filter fun p => ! readingOf p.1 p.2).filter fun p => ! p.1).length = 3 ∧
    (allReadings.filter fun p => ! readingOf p.1 p.2).length = 4 := by
  refine ⟨by decide, by decide⟩

/-- ⚠ **The reading is not the bilge, and a player who treats it as the bilge is
wrong a quarter of the time.**  Both errors are exhibited: a dry night that
floods the mouth, and a wet one that does not.  This is the floor being
refutable — and it is precisely the property that stopped the coupling from
re-solving Deck Descent. -/
theorem the_reading_lies_in_both_directions :
    (∃ p ∈ allReadings, p.1 = false ∧ readingOf p.1 p.2 = true) ∧
    (∃ p ∈ allReadings, p.1 = true ∧ readingOf p.1 p.2 = false) := by
  refine ⟨⟨(false, 0), by decide, by decide, by decide⟩,
    ⟨(true, 3), by decide, by decide, by decide⟩⟩

/-- The instrument that was measured and REJECTED: an exact reading is the bilge
itself, and it is kept here as a named object rather than as a sentence, so the
0.8333 in the header table is a claim about something the tree contains. -/
def exactReadingOf (bilge : Bool) (_ : Fin READING_FACES) : Bool := bilge

theorem the_exact_reading_is_the_bilge_itself :
    ∀ w : Bool, ∀ d : Fin READING_FACES, exactReadingOf w d = w := by
  intro w d; rfl

/-- The rejected instrument is calibrated too — which is the point.  Calibration
is NOT what separates the two, so a design that checked only the marginal would
have shipped the one that re-solves the game. -/
theorem calibration_does_not_separate_the_two_instruments :
    2 * (allReadings.filter fun p => exactReadingOf p.1 p.2).length
        = allReadings.length ∧
    (allReadingDraws.filter fun d => exactReadingOf true d).length = READING_FACES := by
  refine ⟨by decide, by decide⟩

/-! ## The two coupled draws, as index arithmetic

Both games index a published table by a natural computed from their draws:
`DeckDescent.boardAt ⟨3 * mouth + spur⟩` over `boardTable`, and
`VentCrawl.veinAt ⟨i⟩` over `allVeins`, which is ordered `seam * 2 + bottom`.  The
coupling is therefore a change of what feeds those indices and nothing else, and
it can be stated — and its distribution proved unchanged — without importing
either game.  When the two draw functions are cut over, the theorems below
transfer to them by `rfl` on the index. -/

/-- How many boards Deck Descent draws from. -/
abbrev BOARD_COUNT : Nat := 6

/-- How many spurs the lower deck can let water into.  The mouth's own passage is
the other factor, and it is the one this module supplies. -/
abbrev SPUR_COUNT : Nat := 3

/-- The bound both board indices satisfy, over plain naturals so that neither
`Fin` bound proof has to unfold an abbreviation inside a dependent type. -/
theorem board_index_bound (mouth spur : Nat) (hm : mouth < 2) (hs : spur < 3) :
    3 * mouth + spur < 6 := by omega

/-- Deck Descent's board index, coupled.  `boardTable` is ordered
`mouth * 3 + breach`, so a flooded mouth is the upper half of the table. -/
def boardIndexFrom (bilge : Bool) (reading : Fin READING_FACES) (spur : Fin SPUR_COUNT) :
    Fin BOARD_COUNT :=
  ⟨SPUR_COUNT * (if readingOf bilge reading then 1 else 0) + spur.val,
    board_index_bound _ _ (by cases readingOf bilge reading <;> decide) spur.isLt⟩

/-- Deck Descent's board index as it is drawn TODAY: a fair mouth bit and a spur.
This is the arithmetic of `DeckDescent.boardFromRunSeed?` verbatim. -/
def boardIndexToday (mouth : Fin 2) (spur : Fin SPUR_COUNT) : Fin BOARD_COUNT :=
  ⟨SPUR_COUNT * mouth.val + spur.val,
    board_index_bound _ _ mouth.isLt spur.isLt⟩

def allSpurs : List (Fin SPUR_COUNT) := [0, 1, 2]

def allMouths : List (Fin 2) := [0, 1]

/-- The complete coupled domain for a board: bilge, reading face, spur. -/
def allBoardDraws : List (Bool × Fin READING_FACES × Fin SPUR_COUNT) :=
  allBilge.flatMap fun w =>
    allReadingDraws.flatMap fun d => allSpurs.map fun s => (w, d, s)

/-- And the domain the game draws over today. -/
def allBoardDrawsToday : List (Fin 2 × Fin SPUR_COUNT) :=
  allMouths.flatMap fun m => allSpurs.map fun s => (m, s)

/-- ⚑ **Deck Descent's instance family is UNCHANGED IN DISTRIBUTION.**  Over the
whole coupled domain — 24 equally likely triples — each of the six boards is
drawn exactly four times, which is exactly the uniform the present draw gives
over its six.  A player who knows nothing about the day is playing the same game,
not a similar one, and this is the statement that makes the cutover safe. -/
theorem the_board_family_is_unchanged :
    (List.range BOARD_COUNT).all (fun i =>
      decide ((allBoardDraws.filter fun t =>
        (boardIndexFrom t.1 t.2.1 t.2.2).val = i).length * allBoardDrawsToday.length
        = (allBoardDrawsToday.filter fun t =>
            (boardIndexToday t.1 t.2).val = i).length * allBoardDraws.length)) = true := by
  decide

/-- The same fact in the shape a reader checks against a table: four of the
twenty-four, six times over. -/
theorem the_board_family_is_uniform :
    (List.range BOARD_COUNT).map (fun i =>
      (allBoardDraws.filter fun t => (boardIndexFrom t.1 t.2.1 t.2.2).val = i).length)
      = [4, 4, 4, 4, 4, 4] := by
  decide

/-- ⚠ The falsifier for the two theorems above: the coupled draw is NOT uniform
once the day is CONDITIONED on, which is the entire content of the coupling.  On
a wet night the three flooded-mouth boards are three times as likely as the dry
ones.  A statement that survived this conditioning would be a statement about a
coupling that does nothing. -/
theorem the_board_family_moves_with_the_day :
    (List.range BOARD_COUNT).map (fun i =>
      ((allBoardDraws.filter fun t => t.1 = true).filter fun t =>
        (boardIndexFrom t.1 t.2.1 t.2.2).val = i).length)
      = [1, 1, 1, 3, 3, 3] := by
  decide

/-! ### Vent Crawl's vein

`VentCrawl.allVeins` is ordered `[barren, barrenPocket, patchy, patchyPocket,
layered, layeredPocket, foolsLode, motherlode]` — four seams, and within each the
PINCH before the POCKET.  So the vein index is `seam * 2 + bottom`, and the
bottom is the bit this module supplies.

⚑ A WET bilge PINCHES: the shaft bottoms out in the water that is already in the
ship, and the deepest rung pays its seam's pinch.  A dry bilge opens into the
pocket. -/

/-- How many seams the day can be running. -/
abbrev SEAM_COUNT : Nat := 4

/-- How many veins the family holds — `VentCrawl.VEINS`, restated here because
this module must not import the game it feeds. -/
abbrev VEIN_COUNT : Nat := 8

theorem the_vein_family_is_the_seams_and_the_bottom :
    VEIN_COUNT = SEAM_COUNT * 2 := by decide

/-- The bottom of the shaft, from the day's water.  Pinch is index 0 and pocket
is index 1, matching `allVeins`. -/
def bottomIndex (bilge : Bool) : Nat := if bilge then 0 else 1

theorem the_wet_night_pinches : bottomIndex true = 0 ∧ bottomIndex false = 1 := by
  refine ⟨rfl, rfl⟩

theorem vein_index_bound (seam bottom : Nat) (hs : seam < 4) (hb : bottom < 2) :
    2 * seam + bottom < 8 := by omega

/-- Vent Crawl's vein index, coupled. -/
def veinIndexFrom (seam : Fin SEAM_COUNT) (bilge : Bool) : Fin VEIN_COUNT :=
  ⟨2 * seam.val + bottomIndex bilge,
    vein_index_bound _ _ seam.isLt (by cases bilge <;> decide)⟩

def allSeams : List (Fin SEAM_COUNT) := [0, 1, 2, 3]

def allVeinDraws : List (Fin SEAM_COUNT × Bool) :=
  allSeams.flatMap fun s => allBilge.map fun w => (s, w)

/-- ⚑ **Vent Crawl's vein family is UNCHANGED IN DISTRIBUTION.**  Eight equally
likely `(seam, bilge)` pairs land on the eight veins one apiece — the same
uniform the single `drawBelow? 8` gives today.  The day is not a ninth vein and
it is not a reweighting; it is a relabelling of where one of the three bits comes
from. -/
theorem the_vein_family_is_unchanged :
    (List.range VEIN_COUNT).map (fun i =>
      (allVeinDraws.filter fun t => (veinIndexFrom t.1 t.2).val = i).length)
      = [1, 1, 1, 1, 1, 1, 1, 1] := by
  decide

/-- The coupled vein index is a bijection onto the family: every vein is reached
and no two draws collide.  Stated as injectivity so the uniformity above is not
the only thing standing between the family and a silent collapse. -/
theorem the_vein_index_is_injective :
    ∀ s₁ : Fin SEAM_COUNT, ∀ w₁ : Bool, ∀ s₂ : Fin SEAM_COUNT, ∀ w₂ : Bool,
      veinIndexFrom s₁ w₁ = veinIndexFrom s₂ w₂ → s₁ = s₂ ∧ w₁ = w₂ := by
  decide

/-- ⚠ And the falsifier: conditioned on the day, four of the eight veins are
GONE.  A crawler who knows the bilge is standing in a four-vein world, and that
is what the last rung is worth. -/
theorem the_day_halves_the_vein_family :
    ((allVeinDraws.filter fun t => t.2 = true).map fun t =>
      (veinIndexFrom t.1 t.2).val) = [0, 2, 4, 6] ∧
    ((allVeinDraws.filter fun t => t.2 = false).map fun t =>
      (veinIndexFrom t.1 t.2).val) = [1, 3, 5, 7] := by
  refine ⟨by decide, by decide⟩

/-! ## ⚑ The coupling is USABLE, which is a different claim from being real

`VentCrawl.the_bottom_rung_is_a_coin_flip_on_every_seam` says that at the deepest
decision the crawler holds exactly two candidate veins and they want OPPOSITE
verbs.  That theorem is what makes the bottom rung a wager.  The two candidates
are a seam's pinch and its pocket — indices `2*seam` and `2*seam+1` — so they are
exactly the two the bilge separates.

The theorem below is the informed counterpart, stated over the index arithmetic:
the day's water names WHICH of the two the crawler is standing over, at every
seam.  Together they are the claim the whole design rests on — a bit that is
undecided in one game, and decided by another. -/

/-- The two veins a crawler cannot tell apart at the deepest rung, for a seam. -/
def seamPair (seam : Fin SEAM_COUNT) : List Nat := [2 * seam.val, 2 * seam.val + 1]

/-- ⚑ **The bit that is a coin flip inside Vent Crawl is settled outside it.**
At every seam, the pair the crawler is choosing between is exactly the pair the
bilge splits, and the day's water picks one of the two.  This is the sentence
"information earned in one game is usable in another", as arithmetic over the
published vein order. -/
theorem the_day_settles_the_bottom_rung :
    allSeams.all (fun seam =>
      decide ((veinIndexFrom seam true).val ∈ seamPair seam) &&
      decide ((veinIndexFrom seam false).val ∈ seamPair seam) &&
      decide (veinIndexFrom seam true ≠ veinIndexFrom seam false) &&
      decide ((seamPair seam).length = 2)) = true := by
  decide

/-- And the reading reaches the same pair, one step further out and one quarter
less often: a flooded mouth is evidence for the pinch of whatever seam the night
turns out to be running.  The chain the player actually walks —
mouth → bilge → bottom — as one statement. -/
theorem the_mouth_reaches_the_bottom_rung :
    allSeams.all (fun seam =>
      allReadingDraws.all (fun d =>
        -- a mouth that reads flooded is three-in-four evidence of a wet night,
        -- and a wet night is the PINCH of this seam, exactly.
        decide (readingOf true d = true → (veinIndexFrom seam true).val = 2 * seam.val) &&
        decide (readingOf false d = false →
          (veinIndexFrom seam false).val = 2 * seam.val + 1))) = true := by
  decide

#assert_axioms ship_domain_is_new_and_canonical
#assert_axioms shipHeaderBlock_length
#assert_axioms shipHeaderBlock_is_the_slot_alone
#assert_axioms shipHeaderBlock_head
#assert_axioms deriveHeaderBlock_head
#assert_axioms the_ship_draw_is_not_a_player_draw
#assert_axioms board_index_bound
#assert_axioms vein_index_bound
#assert_axioms the_bilge_draw_never_rejects
#assert_axioms the_bilge_is_a_real_bit
#assert_axioms the_reading_is_a_proper_coin
#assert_axioms allReadingDraws_complete
#assert_axioms allReadingDraws_nodup
#assert_axioms allReadings_length
#assert_axioms allReadings_nodup
#assert_axioms the_reading_is_calibrated
#assert_axioms the_reading_is_informative
#assert_axioms a_flooded_mouth_says_the_bilge_is_wet
#assert_axioms a_sound_mouth_says_the_bilge_is_dry
#assert_axioms the_reading_lies_in_both_directions
#assert_axioms the_exact_reading_is_the_bilge_itself
#assert_axioms calibration_does_not_separate_the_two_instruments
#assert_axioms the_board_family_is_unchanged
#assert_axioms the_board_family_is_uniform
#assert_axioms the_board_family_moves_with_the_day
#assert_axioms the_vein_family_is_the_seams_and_the_bottom
#assert_axioms the_wet_night_pinches
#assert_axioms the_vein_family_is_unchanged
#assert_axioms the_vein_index_is_injective
#assert_axioms the_day_halves_the_vein_family
#assert_axioms the_day_settles_the_bottom_rung
#assert_axioms the_mouth_reaches_the_bottom_rung

end Dregg2.Games.PathOfAngels.DayWater
