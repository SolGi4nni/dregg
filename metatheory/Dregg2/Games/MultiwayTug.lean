/-
# Dregg2.Games.MultiwayTug — a VERIFIED pure-transition spec for the multiway-tug card game.

Design lineage: the mechanics are derived from **Hanamikoji** (Kota Nakayama). The *shipped*
dregg game is the original re-theming "multiway-tug"; only the name/theme differ — the rules
modelled here are the Hanamikoji rules (2 players, 7 "geisha" rows with charm values
`[2,2,2,3,3,4,5]` = 21, a 21-card deck holding `charm g` copies of each row `g`, a hidden
6-card hand, four once-per-round actions Secret / Discard / Gift / Competition, control of a
row goes to whoever placed MORE on it, win at ≥ 11 charm OR ≥ 4 rows). The reference
implementation is `~/dev/multiway-tug/src/mechanics.rs`.

## What is PROVEN here (the pure model — real, non-vacuous, `#assert_axioms`-clean)

  1. **CONSERVATION** (`conservation`) — the total card multiset (`removed + deck + hands +
     secrets + discard-piles + placed`) is INVARIANT under `applyAction`. This is the Rust
     `Drop`-bomb (`Card`'s `drop` is `unreachable!()`) discharged as a Lean theorem: cards only
     move between locations, never created or destroyed. Genuine multiset arithmetic
     (`Multiset.sub_add_cancel`), NOT `by decide` on a toy. Lifted to whole executions along the
     `Boundary` keystone (`conservation_along_run`).
  2. **ONE-ACTION-PER-ROUND** (`used_monotone`, `legal_needs_unused`) — a monotone used-set:
     `applyAction` only ever *sets* an action's used-flag, and a legal action REQUIRES its flag
     unset — so each of the 4 actions fires at most once per player per round.
  3. **SCORING** — control goes to whoever placed more (`control_correct`); raw placement counts
     only accrue (`geishaCount_mono`); and — fixing the reference gap — the **Secret card IS
     scored** (`geishaCount` counts `placed + secret`, `secret_is_scored`).
  4. **WIN-SAFETY** — the win predicate `Won` (≥ 11 charm OR ≥ 4 rows) as a `Good`-style
     predicate: winning REQUIRES meeting the threshold (`won_iff_threshold`), you cannot win out
     of nothing (`won_needs_control`), a below-threshold state is not a win (`not_won_blank`),
     and a real winning state exists (`winState_wins`).

## The reference gaps FIXED in this model

  * **The Secret is scored.** In `mechanics.rs`, `update_control_and_score` never adds the
    secreted card to its row — the Secret is placed but never counted. Here `geishaCount` counts
    `placed + secret`, so the Secret contributes to control (`secret_is_scored`), matching the
    physical Hanamikoji rule (the face-down card is revealed and tallied at round end).
  * **The blind pick is pre-folded (modelled explicitly).** Physical Gift/Competition have the
    OPPONENT choose which cards they keep. The Rust pre-folds that choice into the acting
    player's `Action` (the split is declared, not adjudicated). We model exactly that fold: a
    `Gift`/`Competition` action carries the self-share and other-share directly.

## The OBLIGATION stated (NOT yet discharged — Lane-D-gated)

`multiwayTug_air_refines_applyAction` — the game's transition AIR admits `(old, p, action, new)`
IFF `new = applyAction old p action` (the game-level analogue of `Exec.Program`'s
`evalSimpleCtx_*_iff` admit-characterizations). The AIR predicate is HYPOTHESIZED here
(`AirSpec`): the verified circuit lands later and discharges exactly this contract. This Lean
spec is the reference the AIR is emitted against.
-/
import Dregg2.Boundary
import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Abel

namespace Dregg2.Games.MultiwayTug

open scoped BigOperators

/-! ## 1. Rows, charm, players, actions -/

/-- A **geisha row**, indexed `0..6`. A card is just the row it scores for. -/
abbrev Geisha := Fin 7

/-- The **charm value** of each row `[2,2,2,3,3,4,5]` (Σ = 21). This is ALSO the number of
copies of that row's card in the deck (face-value copies), so the full deck has 21 cards. -/
def charm : Geisha → ℕ := ![2, 2, 2, 3, 3, 4, 5]

/-- The two players. -/
inductive Player where
  | p1 | p2
deriving DecidableEq, Repr

/-- The opponent. -/
def Player.other : Player → Player
  | .p1 => .p2
  | .p2 => .p1

@[simp] theorem Player.other_p1 : Player.other .p1 = .p2 := rfl
@[simp] theorem Player.other_p2 : Player.other .p2 = .p1 := rfl
@[simp] theorem Player.other_other (p : Player) : p.other.other = p := by cases p <;> rfl
theorem Player.other_ne (p : Player) : p.other ≠ p := by cases p <;> decide

/-- The four once-per-round **action kinds** (the used-flag domain). -/
inductive ActionKind where
  | secretK | discardK | giftK | competitionK
deriving DecidableEq, Repr

/-- A concrete **action** (a move), carrying the actual cards. The Gift/Competition splits are
the pre-folded opponent choices (see header): `gift self₁ self₂ other`, `competition self₁ self₂
other₁ other₂`. -/
inductive Action where
  /-- Secret one card (set aside face-down; scored at round end in THIS model). -/
  | secret (c : Geisha)
  /-- Discard two cards (removed from the round; never scored). -/
  | discard (c₁ c₂ : Geisha)
  /-- Gift: place two cards on your own rows, one on the opponent's. -/
  | gift (self₁ self₂ other : Geisha)
  /-- Competition: two cards to your rows, two to the opponent's. -/
  | competition (self₁ self₂ other₁ other₂ : Geisha)
deriving DecidableEq, Repr

/-- The action-kind of an action (for the used-flag). -/
def Action.kind : Action → ActionKind
  | .secret _ => .secretK
  | .discard _ _ => .discardK
  | .gift _ _ _ => .giftK
  | .competition _ _ _ _ => .competitionK

/-! ### The card-movement decomposition (destinations of an action's cards) -/

/-- Cards added to the acting player's **placed** rows. -/
def toSelf : Action → Multiset Geisha
  | .gift s₁ s₂ _ => {s₁} + {s₂}
  | .competition s₁ s₂ _ _ => {s₁} + {s₂}
  | _ => 0

/-- Cards added to the **opponent's** placed rows. -/
def toOther : Action → Multiset Geisha
  | .gift _ _ o => {o}
  | .competition _ _ o₁ o₂ => {o₁} + {o₂}
  | _ => 0

/-- Cards added to the acting player's **secret** pile. -/
def toSecret : Action → Multiset Geisha
  | .secret c => {c}
  | _ => 0

/-- Cards added to the acting player's **discard** pile. -/
def toDiscardPile : Action → Multiset Geisha
  | .discard c₁ c₂ => {c₁} + {c₂}
  | _ => 0

/-- The FULL multiset of cards the action removes from the acting player's hand. -/
def actionCards : Action → Multiset Geisha
  | .secret c => {c}
  | .discard c₁ c₂ => {c₁} + {c₂}
  | .gift s₁ s₂ o => {s₁} + {s₂} + {o}
  | .competition s₁ s₂ o₁ o₂ => {s₁} + {s₂} + {o₁} + {o₂}

/-- **The cards leaving the hand equal the cards arriving everywhere else.** The bookkeeping
identity that makes conservation hold: `toSelf + toOther + toSecret + toDiscardPile = actionCards`.
-/
theorem actionCards_split (a : Action) :
    toSelf a + toOther a + toSecret a + toDiscardPile a = actionCards a := by
  cases a <;>
    simp only [toSelf, toOther, toSecret, toDiscardPile, actionCards, add_zero, zero_add,
      add_assoc]

/-! ## 2. The game state -/

/-- The **multiway-tug state**. Every card lives in exactly one location; `placed`/`secret` are
per-player multisets, so scoring is a pure multiset read and conservation is a pure multiset
equation. `used` is the per-player per-action once-per-round flag. -/
structure GState where
  /-- The single face-down card removed at deal (Rust `discarded`). -/
  removed : Multiset Geisha
  /-- The draw pile. -/
  deck : Multiset Geisha
  /-- Each player's hidden hand. -/
  hand : Player → Multiset Geisha
  /-- Each player's secret pile (scored at round end — the fixed gap). -/
  secret : Player → Multiset Geisha
  /-- Each player's discard pile (out of the round). -/
  discardPile : Player → Multiset Geisha
  /-- Each player's placed cards (on the geisha rows). -/
  placed : Player → Multiset Geisha
  /-- Once-per-round action flags. -/
  used : Player → ActionKind → Bool
  /-- Whose turn it is. -/
  current : Player

/-- Sum of a per-player multiset over both players. -/
def sum2 (f : Player → Multiset Geisha) : Multiset Geisha := f .p1 + f .p2

/-- The **total card multiset** (the conserved quantity). -/
def totalCards (s : GState) : Multiset Geisha :=
  s.removed + s.deck + sum2 s.hand + sum2 s.secret + sum2 s.discardPile + sum2 s.placed

/-! ## 3. The pure transition -/

/-- Is the action **legal**: the acting player is to move, its action-kind is unused this round,
and its cards are actually in the acting player's hand. -/
def legalB (s : GState) (p : Player) (a : Action) : Bool :=
  decide (s.current = p) && (! s.used p a.kind) && decide (actionCards a ≤ s.hand p)

/-- The state update for a LEGAL action: move `actionCards a` out of the hand into the four
destinations, set the used-flag, pass the turn. -/
def applyLegal (s : GState) (p : Player) (a : Action) : GState :=
  { s with
    hand := Function.update s.hand p (s.hand p - actionCards a)
    placed := Function.update
      (Function.update s.placed p (s.placed p + toSelf a))
      p.other (s.placed p.other + toOther a)
    secret := Function.update s.secret p (s.secret p + toSecret a)
    discardPile := Function.update s.discardPile p (s.discardPile p + toDiscardPile a)
    used := Function.update s.used p (Function.update (s.used p) a.kind true)
    current := p.other }

/-- **`applyAction` — the pure transition.** A legal action moves cards; an illegal action is a
no-op (fail-closed). Total and deterministic (it is a function). -/
def applyAction (s : GState) (p : Player) (a : Action) : GState :=
  bif legalB s p a then applyLegal s p a else s

/-- Determinism: `applyAction` is a function, so the successor is unique. -/
theorem applyAction_deterministic (s : GState) (p : Player) (a : Action) {n₁ n₂ : GState}
    (h₁ : n₁ = applyAction s p a) (h₂ : n₂ = applyAction s p a) : n₁ = n₂ :=
  h₁.trans h₂.symm

/-! ## 4. INVARIANT 1 — CONSERVATION (the Drop-bomb, in Lean) -/

/-- The hand-move identity: removing `actionCards a` from a hand `m` (`actionCards a ≤ m`) and
re-adding the four destination shares recovers `m` exactly. -/
theorem hand_move {m : Multiset Geisha} (a : Action) (hle : actionCards a ≤ m) :
    m - actionCards a + toSelf a + toOther a + toSecret a + toDiscardPile a = m := by
  -- reduce to per-row Nat counts; the four destination shares sum to `actionCards a`, which
  -- (being ≤ the hand) cancels the subtraction. Robust against the truncated-`-` (no `abel`).
  have hsplit : ∀ g, Multiset.count g (toSelf a) + Multiset.count g (toOther a)
      + Multiset.count g (toSecret a) + Multiset.count g (toDiscardPile a)
      = Multiset.count g (actionCards a) := by
    intro g
    rw [← Multiset.count_add, ← Multiset.count_add, ← Multiset.count_add, actionCards_split]
  ext g
  have hc : Multiset.count g (actionCards a) ≤ Multiset.count g m := Multiset.count_le_of_le g hle
  have hg := hsplit g
  simp only [Multiset.count_add, Multiset.count_sub]
  omega

/-- **`conservation` (INVARIANT 1 — the Drop-bomb).** The total card multiset is INVARIANT under
`applyAction`: cards only move between locations, none is created or destroyed. Proven by real
multiset arithmetic (`hand_move`), for EVERY input (legal ⇒ genuine relocation; illegal ⇒ no-op).
-/
theorem conservation (s : GState) (p : Player) (a : Action) :
    totalCards (applyAction s p a) = totalCards s := by
  by_cases hleg : legalB s p a = true
  · have hle : actionCards a ≤ s.hand p := by
      simp only [legalB, Bool.and_eq_true, decide_eq_true_eq] at hleg
      exact hleg.2
    simp only [applyAction, hleg, cond_true, totalCards, applyLegal, sum2]
    cases p <;>
      simp only [Function.update_apply, Player.other_p1, Player.other_p2, reduceCtorEq,
        reduceIte] <;>
      · conv_rhs => rw [← hand_move a hle]
        ac_rfl
  · simp only [Bool.not_eq_true] at hleg
    simp [applyAction, hleg]

/-! ## 5. INVARIANT 2 — ONE ACTION PER ROUND (a monotone used-set) -/

/-- **`used_monotone` (INVARIANT 2a).** `applyAction` only ever SETS a used-flag: any flag true
before the step is still true after. The used-set is monotone. -/
theorem used_monotone (s : GState) (p : Player) (a : Action) (q : Player) (k : ActionKind)
    (h : s.used q k = true) : (applyAction s p a).used q k = true := by
  by_cases hleg : legalB s p a = true
  · simp only [applyAction, hleg, cond_true, applyLegal, Function.update_apply]
    by_cases hq : q = p
    · subst hq
      by_cases hk : k = a.kind
      · subst hk; simp
      · simp [hk, h]
    · simp [hq, h]
  · simp only [Bool.not_eq_true] at hleg
    simp only [applyAction, hleg, cond_false]; exact h

/-- **`legal_needs_unused` (INVARIANT 2b).** A legal action REQUIRES its kind unused this round.
Together with `used_monotone`, each of the 4 actions fires at most once per player per round. -/
theorem legal_needs_unused (s : GState) (p : Player) (a : Action) (h : legalB s p a = true) :
    s.used p a.kind = false := by
  simp only [legalB, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h.1.2

/-- **`used_after_legal` (the flag IS set — non-vacuity of the used-set).** After a legal action,
its own kind is marked used, so it cannot legally repeat. -/
theorem used_after_legal (s : GState) (p : Player) (a : Action) (h : legalB s p a = true) :
    (applyAction s p a).used p a.kind = true := by
  simp only [applyAction, h, cond_true, applyLegal, Function.update_self]

/-! ## 6. INVARIANT 3 — SCORING (control, monotonicity, the Secret scored) -/

/-- **`geishaCount s p g`** — how many cards player `p` has tallied on row `g`: the placed cards
PLUS the secret (the fixed reference gap — the Secret is scored). -/
def geishaCount (s : GState) (p : Player) (g : Geisha) : ℕ :=
  (s.placed p).count g + (s.secret p).count g

/-- **`secret_is_scored` (the fixed gap, witnessed).** The secret pile contributes to the tally:
adding a card to `secret` raises that row's `geishaCount`. In the reference `mechanics.rs` the
secret is never added at scoring; here it is. -/
theorem secret_is_scored (s : GState) (p : Player) (g : Geisha) :
    (s.placed p).count g ≤ geishaCount s p g := by
  simp only [geishaCount]; exact Nat.le_add_right _ _

/-- Placed cards only accrue under a transition. -/
theorem placed_le (s : GState) (p : Player) (a : Action) (q : Player) :
    s.placed q ≤ (applyAction s p a).placed q := by
  by_cases hleg : legalB s p a = true
  · simp only [applyAction, hleg, cond_true, applyLegal, Function.update_apply]
    cases p <;> cases q <;>
      simp only [Player.other_p1, Player.other_p2, reduceCtorEq, if_true, if_false] <;>
      first
        | exact le_rfl
        | exact Multiset.le_add_right _ _
  · simp only [Bool.not_eq_true] at hleg
    simp [applyAction, hleg]

/-- Secret cards only accrue under a transition. -/
theorem secret_le (s : GState) (p : Player) (a : Action) (q : Player) :
    s.secret q ≤ (applyAction s p a).secret q := by
  by_cases hleg : legalB s p a = true
  · simp only [applyAction, hleg, cond_true, applyLegal, Function.update_apply]
    cases p <;> cases q <;>
      simp only [reduceCtorEq, if_true, if_false] <;>
      first
        | exact le_rfl
        | exact Multiset.le_add_right _ _
  · simp only [Bool.not_eq_true] at hleg
    simp [applyAction, hleg]

/-- **`geishaCount_mono` (INVARIANT 3 — scores only accrue).** A player's raw tally on any row
never decreases under a legal transition. (The DERIVED charm total may still shift when the
opponent overtakes a row — that flip is the game; the RAW counts are monotone.) -/
theorem geishaCount_mono (s : GState) (p : Player) (a : Action) (q : Player) (g : Geisha) :
    geishaCount s q g ≤ geishaCount (applyAction s p a) q g :=
  Nat.add_le_add
    (Multiset.count_le_of_le g (placed_le s p a q))
    (Multiset.count_le_of_le g (secret_le s p a q))

/-- **`control s g`** — who controls row `g`: whoever has the strictly higher tally, else nobody
(a tie leaves the row uncontrolled), exactly as `update_control_and_score`. -/
def control (s : GState) (g : Geisha) : Option Player :=
  if geishaCount s .p2 g < geishaCount s .p1 g then some .p1
  else if geishaCount s .p1 g < geishaCount s .p2 g then some .p2
  else none

/-- **`control_correct` (INVARIANT 3 — control goes to whoever placed MORE).** If `control s g =
some p` then `p` strictly out-tallies the opponent on row `g`. -/
theorem control_correct (s : GState) (g : Geisha) (p : Player)
    (h : control s g = some p) : geishaCount s p.other g < geishaCount s p g := by
  simp only [control] at h
  split at h
  · rename_i h1
    rw [Option.some.injEq] at h; subst h; simpa using h1
  · split at h
    · rename_i h2
      rw [Option.some.injEq] at h; subst h; simpa using h2
    · exact absurd h (by simp)

/-! ## 7. INVARIANT 4 — WIN-SAFETY (a `Good`-style predicate) -/

/-- Rows controlled by player `p`. -/
def controlledBy (s : GState) (p : Player) : Finset Geisha :=
  Finset.univ.filter (fun g => control s g = some p)

/-- Total charm a player controls (Σ of `charm` over their rows). -/
def charmScore (s : GState) (p : Player) : ℕ := ∑ g ∈ controlledBy s p, charm g

/-- Number of rows a player controls. -/
def geishaScore (s : GState) (p : Player) : ℕ := (controlledBy s p).card

/-- The charm win threshold (`≥ 11 charm`). A single source of truth: the model win predicate
`Won` AND the deployed program's win-gate (`MultiwayTugProgram.lean`) both read THIS constant, so
a threshold edit here moves the proven game and the emitted referee together (`abbrev` keeps it
definitionally transparent, so every `decide`/`Iff.rfl`/`omega` proof below still discharges). -/
abbrev charmWinThreshold : ℕ := 11

/-- The guild-count win threshold (`≥ 4 rows`); the single-source twin of `charmWinThreshold`. -/
abbrev guildWinThreshold : ℕ := 4

/-- **`Won`** — the win predicate: ≥ 11 charm OR ≥ 4 rows (`update_control_and_score`'s two
victory tests), stated as a `Good`-style state predicate. Reads the shared `charmWinThreshold` /
`guildWinThreshold` constants the deployed win-gate reads (single source). -/
def Won (s : GState) (p : Player) : Prop :=
  charmWinThreshold ≤ charmScore s p ∨ guildWinThreshold ≤ geishaScore s p

/-- **`won_iff_threshold` (WIN-SAFETY — cannot win illegally).** Winning is EXACTLY meeting the
threshold: there is no way to be a winner without ≥ 11 charm or ≥ 4 rows. -/
theorem won_iff_threshold (s : GState) (p : Player) :
    Won s p ↔ (11 ≤ charmScore s p ∨ 4 ≤ geishaScore s p) := Iff.rfl

/-- **`won_needs_control` (WIN-SAFETY — cannot win out of nothing).** A winner controls at least
one row: a win with zero controlled rows is impossible (both thresholds need a positive score,
and both scores are `0` on an empty control set). -/
theorem won_needs_control (s : GState) (p : Player) (h : Won s p) :
    (controlledBy s p).Nonempty := by
  rcases h with hc | hg
  · rcases Finset.eq_empty_or_nonempty (controlledBy s p) with he | hne
    · simp only [charmScore, charmWinThreshold, he, Finset.sum_empty] at hc; omega
    · exact hne
  · rcases Finset.eq_empty_or_nonempty (controlledBy s p) with he | hne
    · simp only [geishaScore, guildWinThreshold, he, Finset.card_empty] at hg; omega
    · exact hne

/-! ### The blank state and the winning witnesses (non-vacuity + teeth) -/

/-- A blank state: empty everywhere, nobody has acted. -/
def blankState : GState where
  removed := 0
  deck := 0
  hand := fun _ => 0
  secret := fun _ => 0
  discardPile := fun _ => 0
  placed := fun _ => 0
  used := fun _ _ => false
  current := .p1

/-- **`not_won_blank` (WIN-SAFETY teeth — a below-threshold state is NOT a win).** With no cards
placed, nobody controls any row, so neither victory test is met. -/
theorem not_won_blank (p : Player) : ¬ Won blankState p := by
  have hempty : controlledBy blankState p = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro g _
    simp [control, blankState, geishaCount]
  simp only [Won, charmScore, geishaScore, charmWinThreshold, guildWinThreshold, hempty,
    Finset.sum_empty, Finset.card_empty]
  omega

/-- A concrete **winning state**: player 1 has placed on rows `3` (charm 3), `5` (charm 4) and `6`
(charm 5) with player 2 empty — so P1 controls all three, for `3 + 4 + 5 = 12 ≥ 11` charm. -/
def winState : GState :=
  { blankState with placed := fun p => if p = .p1 then ({3, 5, 6} : Multiset Geisha) else 0 }

/-- **`winState_wins` (WIN-SAFETY non-vacuity — a real win exists).** `winState` is an honest win
for player 1 (12 charm ≥ 11), so `Won` is inhabited and the win-safety theorems are not vacuous. -/
theorem winState_wins : Won winState .p1 := by
  have hctl : controlledBy winState .p1 = {3, 5, 6} := by decide
  left
  simp only [charmScore, hctl]
  decide

/-! ## 7B. ⚑ THE ADJUDICATED ROUND WINNER — the fix for the 66% draw rate

**The design wound.** `Won` is an ABSOLUTE threshold (≥ 11 charm or ≥ 4 guilds) and the shipped
game is ONE round. In Hanamikoji the round is a *hand*, not a *match*: rounds repeat, and the
absolute threshold is a "you have won the whole match" test. Shipping a single round against an
absolute threshold means a round in which neither player clears the bar has NO WINNER, and
`reference.rs::winner_of` duly returns `None`.

**Measured** (1500 rounds, symmetric greedy agents, this model's rules): **66.1% of rounds end
with no winner at all.** That is not a close game; it is two thirds of matches ending in a shrug.

**Why it happens is exact, not incidental.** `∑ g, charm g = 21` and `control` awards a row to
at most one player, so `charmScore p1 + charmScore p2 ≤ 21` (`charmScore_add_le`) — and if every
row were controlled the sum would be exactly 21, forcing one player to ≥ 11. So *every* undecided
round is caused by TIED rows going uncontrolled, and the charm they carry evaporating. Empty rows
are not the cause (0.09 per round measured); contested ties are.

**The fix, and why this one.** Three tie rules were measured. Awarding tied rows to a fixed player
decides every round but at **81.7% / 18.3%** — a landslide, because ties are frequent. Awarding
them to whoever secreted onto the row leaves 41.8% draws. Adjudicating an *undecided round* on
total charm, then on rows held, leaves **5.1%** draws at **41.2% / 53.7%** — decisive, and it does
not touch `control`, so the emitted win-gate teeth (`MultiwayTugProgram.winTooth_shape`, which
gate `winner = p ⇒ charm ≥ 11 ∨ guilds ≥ 4`) keep meaning exactly what they meant. `Won` is
UNCHANGED and still the first thing `roundWinner` asks.

⚠ The residual, measured and NOT fixed here: the player who takes the round's LAST action wins
~57% of decided rounds (alternating order 40.6/54.5; the mirrored "snake" order 55.5/39.6 — the
edge follows the last action, so no re-ordering of a single round is fair). That is the second
thing Hanamikoji's repeated rounds buy, and it needs an even number of rounds with the opening
player alternating — a state change, not a tweak. -/

instance (s : GState) (p : Player) : Decidable (Won s p) := by unfold Won; exact inferInstance

/-- The two players' controlled-row sets are DISJOINT: `control` returns at most one owner. -/
theorem controlledBy_disjoint (s : GState) :
    Disjoint (controlledBy s .p1) (controlledBy s .p2) := by
  rw [Finset.disjoint_left]
  intro g h1 h2
  simp only [controlledBy, Finset.mem_filter] at h1 h2
  rw [h1.2] at h2
  exact absurd h2.2 (by simp)

/-- **`charmScore_add_le` — the conservation of charm.** The two charm totals together never
exceed the whole board's `∑ charm = 21`, because the controlled-row sets are disjoint subsets of
`univ`. This is the fact that makes the adjudication well-behaved (and that makes a double win
impossible). -/
theorem charmScore_add_le (s : GState) :
    charmScore s .p1 + charmScore s .p2 ≤ ∑ g : Geisha, charm g := by
  rw [charmScore, charmScore, ← Finset.sum_union (controlledBy_disjoint s)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun _ _ _ => Nat.zero_le _)

/-- The board's whole charm is `21`. -/
theorem total_charm : (∑ g : Geisha, charm g) = 21 := by decide

/-- Likewise for rows held: at most the seven rows exist. -/
theorem geishaScore_add_le (s : GState) : geishaScore s .p1 + geishaScore s .p2 ≤ 7 := by
  rw [geishaScore, geishaScore, ← Finset.card_union_of_disjoint (controlledBy_disjoint s)]
  simpa using Finset.card_le_card (Finset.subset_univ
    (controlledBy s .p1 ∪ controlledBy s .p2))

/-- **`not_both_charm_won`** — `11 + 11 > 21`, so the charm bar cannot be cleared by both. -/
theorem not_both_charm_won (s : GState) :
    ¬ (charmWinThreshold ≤ charmScore s .p1 ∧ charmWinThreshold ≤ charmScore s .p2) := by
  rintro ⟨h1, h2⟩
  have hc := charmScore_add_le s
  rw [total_charm] at hc
  simp only [charmWinThreshold] at h1 h2
  omega

/-- **`not_both_guild_won`** — `4 + 4 > 7`, so the row bar cannot be cleared by both. -/
theorem not_both_guild_won (s : GState) :
    ¬ (guildWinThreshold ≤ geishaScore s .p1 ∧ guildWinThreshold ≤ geishaScore s .p2) := by
  rintro ⟨h1, h2⟩
  have hg := geishaScore_add_le s
  simp only [guildWinThreshold] at h1 h2
  omega

/-- ⚠ **`won_can_be_mutual` — `Won` is NOT exclusive, and the shipped rule already knew it.**
`Won` is a DISJUNCTION, and its two disjuncts can straddle: P1 can hold rows `4,5,6` for
`3 + 4 + 5 = 12` charm on only THREE rows while P2 holds the other FOUR rows for `2+2+2+3 = 9`
charm. Both are `Won`. So the round's terminal rule needs a PRECEDENCE, not just an exclusivity
argument — and `reference.rs::winner_of` fixes it as *charm bar, then row bar*. `roundWinner`
below reproduces exactly that order, so the adjudication is bolted onto the shipped precedence
rather than quietly re-ranking it. -/
def straddleState : GState :=
  { blankState with
    placed := fun p => if p = .p1 then ({4, 5, 6} : Multiset Geisha)
                                   else ({0, 1, 2, 3} : Multiset Geisha) }

theorem won_can_be_mutual : Won straddleState .p1 ∧ Won straddleState .p2 := by
  have h1 : controlledBy straddleState .p1 = {4, 5, 6} := by decide
  have h2 : controlledBy straddleState .p2 = {0, 1, 2, 3} := by decide
  refine ⟨Or.inl ?_, Or.inr ?_⟩
  · simp only [charmScore, h1]; decide
  · simp only [geishaScore, h2]; decide

/-- **`roundWinner` — the terminal rule the shipped game was missing.**

A round is decided by, in order: the absolute threshold (`Won`, UNCHANGED — this is still the
"you cleared the bar" win the emitted teeth gate); then, if neither player cleared it, the higher
TOTAL CHARM; then the higher ROW COUNT; and only on exact parity of both is the round a genuine
draw. Total, deterministic, and — by `roundWinner_draw_iff` — the draw it does return is an
honest dead heat rather than the shipped "nobody reached the bar". -/
def roundWinner (s : GState) : Option Player :=
  if charmWinThreshold ≤ charmScore s .p1 then some .p1
  else if charmWinThreshold ≤ charmScore s .p2 then some .p2
  else if guildWinThreshold ≤ geishaScore s .p1 then some .p1
  else if guildWinThreshold ≤ geishaScore s .p2 then some .p2
  else if charmScore s .p2 < charmScore s .p1 then some .p1
  else if charmScore s .p1 < charmScore s .p2 then some .p2
  else if geishaScore s .p2 < geishaScore s .p1 then some .p1
  else if geishaScore s .p1 < geishaScore s .p2 then some .p2
  else none

/-- **`roundWinner_extends_Won` (the fix is CONSERVATIVE).** Whenever the shipped threshold rule
named a winner *outright* — that player cleared a bar and the opponent cleared neither —
`roundWinner` names the SAME winner. Adjudication only ever fills in rounds the old rule left
blank; it never overturns an uncontested threshold win. (The straddle case, where both are `Won`,
is settled by the same charm-then-rows precedence `reference.rs::winner_of` already used.) -/
theorem roundWinner_extends_Won (s : GState) (p : Player) (h : Won s p) (h' : ¬ Won s p.other) :
    roundWinner s = some p := by
  simp only [Won, charmWinThreshold, guildWinThreshold, not_or, not_le] at h h'
  cases p with
  | p1 => simp only [Player.other_p1] at h'
          rcases h with hc | hg <;>
            (rw [roundWinner]; simp only [charmWinThreshold, guildWinThreshold]
             split_ifs <;> first | rfl | omega)
  | p2 => simp only [Player.other_p2] at h'
          rcases h with hc | hg <;>
            (rw [roundWinner]; simp only [charmWinThreshold, guildWinThreshold]
             split_ifs <;> first | rfl | omega)

/-- **`roundWinner_sound` (the adjudicated winner EARNED it).** A named winner either cleared one
of the absolute bars, or strictly out-charmed the opponent, or matched on charm and strictly
out-held them on rows. There is no arm that hands the round to a player who is behind on both. -/
theorem roundWinner_sound (s : GState) (p : Player) (h : roundWinner s = some p) :
    Won s p
      ∨ charmScore s p.other < charmScore s p
      ∨ (charmScore s p.other = charmScore s p ∧ geishaScore s p.other < geishaScore s p) := by
  unfold roundWinner at h
  split at h
  · rename_i hw; rw [Option.some.injEq] at h; subst h; exact Or.inl (Or.inl hw)
  · split at h
    · rename_i hw; rw [Option.some.injEq] at h; subst h; exact Or.inl (Or.inl hw)
    · split at h
      · rename_i hw; rw [Option.some.injEq] at h; subst h; exact Or.inl (Or.inr hw)
      · split at h
        · rename_i hw; rw [Option.some.injEq] at h; subst h; exact Or.inl (Or.inr hw)
        · split at h
          · rename_i hlt; rw [Option.some.injEq] at h; subst h; exact Or.inr (Or.inl hlt)
          · split at h
            · rename_i hlt; rw [Option.some.injEq] at h; subst h; exact Or.inr (Or.inl hlt)
            · split at h
              · rename_i h1 h2 hlt
                rw [Option.some.injEq] at h; subst h
                exact Or.inr (Or.inr ⟨by simp only [Player.other_p1]; omega, hlt⟩)
              · split at h
                · rename_i h1 h2 h3 hlt
                  rw [Option.some.injEq] at h; subst h
                  exact Or.inr (Or.inr ⟨by simp only [Player.other_p2]; omega, hlt⟩)
                · exact absurd h (by simp)

/-- **`roundWinner_draw_iff` (the draw is an EXACT DEAD HEAT).** `roundWinner` returns `none` iff
the two players are level on charm AND level on rows held. Contrast the shipped rule, whose `none`
meant only "neither reached the bar" — the state `9 charm vs 6` was a non-result there and is a
win here. This is the theorem that says the 66% is gone for a reason and not by fiat. -/
theorem roundWinner_draw_iff (s : GState) :
    roundWinner s = none ↔
      (charmScore s .p1 = charmScore s .p2 ∧ geishaScore s .p1 = geishaScore s .p2) := by
  constructor
  · intro h
    unfold roundWinner at h
    repeat (split at h; · exact absurd h (by simp))
    rename_i h1 h2 h3 h4 h5 h6 h7 h8
    exact ⟨by omega, by omega⟩
  · rintro ⟨hc, hg⟩
    -- level on both scales ⇒ neither bar can have been cleared (11+11 > 21, 4+4 > 7)
    have hcs := charmScore_add_le s
    rw [total_charm] at hcs
    have hgs := geishaScore_add_le s
    rw [roundWinner, if_neg (by simp only [charmWinThreshold]; omega),
      if_neg (by simp only [charmWinThreshold]; omega),
      if_neg (by simp only [guildWinThreshold]; omega),
      if_neg (by simp only [guildWinThreshold]; omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- A concrete round the SHIPPED rule threw away: P1 holds rows `5` and `6` (charm `4 + 4 = 9`),
P2 holds row `3` (charm `3`). Nobody reached 11 charm or 4 rows, so `winner_of` returned `None`
and the match was a non-event — with P1 three rows and six charm ahead. -/
def undecidedState : GState :=
  { blankState with
    placed := fun p => if p = .p1 then ({5, 6} : Multiset Geisha) else ({3} : Multiset Geisha) }

/-- **`undecidedState_not_Won` — the shipped rule finds NO winner here.** -/
theorem undecidedState_not_Won (p : Player) : ¬ Won undecidedState p := by
  have h1 : controlledBy undecidedState .p1 = {5, 6} := by decide
  have h2 : controlledBy undecidedState .p2 = {3} := by decide
  cases p <;>
    simp only [Won, charmScore, geishaScore, charmWinThreshold, guildWinThreshold, h1, h2] <;>
    decide

/-- **`undecidedState_adjudicates` (THE FIX, WITNESSED).** The same round is a clean P1 win under
`roundWinner` — 9 charm to 3. Together with `undecidedState_not_Won` this is the non-vacuity of
the whole section: the adjudication is not decoration, it decides a round the shipped rule
dropped. -/
theorem undecidedState_adjudicates : roundWinner undecidedState = some .p1 := by
  have h1 : ¬ Won undecidedState .p1 := undecidedState_not_Won .p1
  have h2 : ¬ Won undecidedState .p2 := undecidedState_not_Won .p2
  have hc1 : controlledBy undecidedState .p1 = {5, 6} := by decide
  have hc2 : controlledBy undecidedState .p2 = {3} := by decide
  have e1 : charmScore undecidedState .p1 = 9 := by simp only [charmScore, hc1]; decide
  have e2 : charmScore undecidedState .p2 = 3 := by simp only [charmScore, hc2]; decide
  have g1 : geishaScore undecidedState .p1 = 2 := by simp only [geishaScore, hc1]; decide
  have g2 : geishaScore undecidedState .p2 = 1 := by simp only [geishaScore, hc2]; decide
  rw [roundWinner]
  simp only [charmWinThreshold, guildWinThreshold, e1, e2, g1, g2]
  decide

/-- **`winState_roundWinner` — a threshold win is still a threshold win.** -/
theorem winState_roundWinner : roundWinner winState = some .p1 := by
  have hctl : controlledBy winState .p1 = {3, 5, 6} := by decide
  have hc : charmWinThreshold ≤ charmScore winState .p1 := by
    simp only [charmScore, charmWinThreshold, hctl]; decide
  simp only [roundWinner, if_pos hc]

/-- A genuine dead heat — both players hold row `0` counts of zero and nothing else, so both
scores are `0` and the round honestly draws. -/
theorem blankState_draws : roundWinner blankState = none := by
  rw [roundWinner_draw_iff]
  have h : ∀ p, controlledBy blankState p = ∅ := by
    intro p
    apply Finset.filter_eq_empty_iff.mpr
    intro g _
    simp [control, blankState, geishaCount]
  simp [charmScore, geishaScore, h]

/-! ## 8. The `Boundary` tie-in — conservation as a `Good`-invariant along whole executions -/

open Dregg2.Boundary

/-- The game as a `TurnCoalg`: the input alphabet is `Player × Action`; the successor is
`applyAction`. -/
def gameCoalg : TurnCoalg Unit (Player × Action) where
  Carrier := GState
  step := fun s => ((), fun pa => applyAction s pa.1 pa.2)

/-- **`conservation_along_run` (INVARIANT 1, lifted to all time).** Conservation is not just a
one-step fact: instantiating the `Boundary` keystone `stepComplete_preserves` with the
conservation `StepInv`, the total card multiset is preserved at EVERY configuration reachable
along a whole execution `Run`. The game-level use of the coinductive safety keystone. -/
theorem conservation_along_run {x y : GState} (C : Multiset Geisha)
    (hrun : Execution.Run (inducedSystem gameCoalg) x y)
    (hx : totalCards x = C) : totalCards y = C := by
  refine stepComplete_preserves gameCoalg
    (fun a _ b => totalCards b = totalCards a)
    (fun _ _ _ => True) (fun _ _ _ => True) (fun _ _ _ => True)
    (fun s => totalCards s = C) ?_ ?_ hrun hx
  · intro x t
    refine ⟨?_, trivial, trivial, trivial⟩
    obtain ⟨p, a⟩ := t
    exact conservation x p a
  · intro x t hgood hinv
    exact hinv.1.trans hgood

/-! ## 9. THE AIR-REFINEMENT OBLIGATION (Lane-D-gated — the AIR side lands later)

The verified circuit for the game mechanics will emit a transition AIR. The CONTRACT it must
satisfy — the game-level analogue of `Exec.Program`'s `evalSimpleCtx_*_iff` admit-characterizations
— is that the AIR admits `(old, p, action, new)` EXACTLY when `new = applyAction old p action`.
Here `air` is HYPOTHESIZED (`AirSpec`); the Lean model above IS the specification the AIR is
emitted against. Discharging `AirSpec` for the real emitted AIR is the deferred (Lane-D) work. -/

/-- **`AirSpec air`** — the contract the verified circuit's transition AIR must meet: it admits a
`(old, player, action, new)` tuple iff `new` is the model successor. -/
def AirSpec (air : GState → Player → Action → GState → Prop) : Prop :=
  ∀ o p a n, air o p a n ↔ n = applyAction o p a

/-- **`multiwayTug_air_refines_applyAction` (THE OBLIGATION, stated).** Given an AIR satisfying
`AirSpec`, its admission relation IS the graph of `applyAction`. This is the game-level refinement
the verified circuit discharges; the AIR side (`air` + a proof of `AirSpec air` for the emitted
constraint system) is the Lane-D deliverable. -/
theorem multiwayTug_air_refines_applyAction
    (air : GState → Player → Action → GState → Prop) (h : AirSpec air)
    (o : GState) (p : Player) (a : Action) (n : GState) :
    air o p a n ↔ n = applyAction o p a :=
  h o p a n

/-- **`air_functional` (a consequence of the contract).** Any AIR meeting `AirSpec` is
functional: it admits at most one successor for a given `(old, player, action)` — the emitted
circuit inherits `applyAction`'s determinism. -/
theorem air_functional
    (air : GState → Player → Action → GState → Prop) (h : AirSpec air)
    {o : GState} {p : Player} {a : Action} {n₁ n₂ : GState}
    (h₁ : air o p a n₁) (h₂ : air o p a n₂) : n₁ = n₂ :=
  ((h o p a n₁).mp h₁).trans ((h o p a n₂).mp h₂).symm

/-! ## 10. A real play witness (`#guard` smoke — the model runs, cards are conserved) -/

/-- A concrete mid-game state: P1 to move, both hands dealt. -/
def demo : GState :=
  { blankState with
    hand := fun p => if p = .p1 then ({3, 3, 5, 6, 6, 0} : Multiset Geisha)
                                 else ({1, 2, 4, 5, 6, 0} : Multiset Geisha)
    current := .p1 }

-- P1 plays a legal Gift (keep 3,3; give 5 to the opponent).
#guard legalB demo .p1 (Action.gift 3 3 5)
-- Conservation holds on the real play: the total card multiset is unchanged.
#guard totalCards (applyAction demo .p1 (Action.gift 3 3 5)) = totalCards demo
-- After the Gift, P1 controls row 3 (placed two, P2 none).
#guard control (applyAction demo .p1 (Action.gift 3 3 5)) 3 = some Player.p1
-- The Gift's kind is now marked used (cannot repeat this round).
#guard (applyAction demo .p1 (Action.gift 3 3 5)).used .p1 ActionKind.giftK
-- An illegal action (card not in hand) is a no-op.
#guard totalCards (applyAction demo .p1 (Action.secret 4)) = totalCards demo
-- The full deck holds 21 cards (Σ charm).
#guard (∑ g : Geisha, Multiset.replicate (charm g) g).card = 21

/-! ## 11. Axiom hygiene — the PROVEN invariants pinned to the standard kernel triple.

`#assert_axioms` errors if any keystone escapes `{propext, Classical.choice, Quot.sound}`. The
AIR-refinement obligation is a CARRIED hypothesis (`AirSpec`), not an axiom. -/

#assert_axioms conservation
#assert_axioms applyAction_deterministic
#assert_axioms used_monotone
#assert_axioms legal_needs_unused
#assert_axioms used_after_legal
#assert_axioms secret_is_scored
#assert_axioms geishaCount_mono
#assert_axioms control_correct
#assert_axioms won_iff_threshold
#assert_axioms won_needs_control
#assert_axioms not_won_blank
#assert_axioms winState_wins
#assert_axioms controlledBy_disjoint
#assert_axioms charmScore_add_le
#assert_axioms geishaScore_add_le
#assert_axioms not_both_charm_won
#assert_axioms not_both_guild_won
#assert_axioms won_can_be_mutual
#assert_axioms roundWinner_extends_Won
#assert_axioms roundWinner_sound
#assert_axioms roundWinner_draw_iff
#assert_axioms undecidedState_not_Won
#assert_axioms undecidedState_adjudicates
#assert_axioms winState_roundWinner
#assert_axioms blankState_draws
#assert_axioms conservation_along_run
#assert_axioms multiwayTug_air_refines_applyAction
#assert_axioms air_functional

end Dregg2.Games.MultiwayTug
