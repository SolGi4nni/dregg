/-
# Artificer Logic — name the rule, not the instance

Substrate note: this is Lean-authored game semantics.  Nothing here is an AIR, a
constraint system or a gadget.  Rust and the browser only dispatch the table the
Lean emitter writes.

## The verb is different

Every Path of Angels game shipped so far is an INSTANCE-GUESSER: Signal hunts a
code, Salvage hunts a pairing, Deck Descent hunts three passage bits.  The player
is told the rule and asked for the hidden value.

Here the value is not hidden — every charge the mechanism will ever be fed is
public, and so is what it does with each one.  What is hidden is the RULE.  You
feed the mechanism a train of cogs, it turns or it jams, and you win by NAMING
the law it obeys.  That is Zendo/Eleusis, and it is a genuinely different verb.

## Zendo's failure, and the fix this codebase already owns

Classic Zendo loses players because the rule space is unbounded: a guess feels
arbitrary and a loss feels unfair.  The fix is the discipline this repository
lives by anyway — the manual is an INDUCTIVE TYPE.  `Rule` below has seven
families and sixteen inhabitants, all of them rendered into the descriptor, so a
player narrows a KNOWN lattice.  Twenty questions over a visible space is fair;
twenty questions over an unstated one is not.

⚑ TOY SIZE, DELIBERATELY.  Three cogs, two metals, eight charges, sixteen rules.
The grammar is small so that every property below is a theorem over the ACTUAL
transition rather than a sample of it, and so that the whole reachable state
space is emitted.  `docs`-level sizing and the families to add first are in the
lane report; the shape of this file does not change when the manual grows.

## The four properties this design is accountable for

1. **The manual has no synonyms.**  `manual_has_no_synonyms` — two rules that
   agree on all eight charges ARE the same rule.  This is the design gate for an
   induction game: an indistinguishable pair means a player can play perfectly
   and still lose to a coin flip.  It is stated as a ∀ over `Rule`, not as a
   check over a list, and `the_cut_family_would_have_been_a_synonym` exhibits the
   family this grammar was cut back from to keep it true.
2. **The budget binds exactly.**  `certainWithin` is a minimax over the remaining
   charges.  `four_charges_are_enough` and `three_charges_are_not` are the two
   halves of "worst-case identification = 4 = `PROBE_BUDGET`, slack ZERO".
3. **Which charge, not whether.**  A charge that cannot split the surviving
   candidates is REFUSED — the mechanism has already answered it.  So every
   accepted probe is a real cut, and `every_open_probe_resolves` says every one
   of them consults the instance.  The decision the game asks for is *which*.
4. **Certainty is not a gamble, and a gamble is not certainty.**  With one
   candidate left, declaring it is an `advance` row — one successor, no oracle
   consulted (`certain_declaration_is_an_advance`).  With two left it is a
   `resolve` row and the run can end either way.  The table says which, in the
   bytes, before the player commits.

## What the budget is sized for

`PROBE_BUDGET = 4` is not slack.  Sixteen rules over eight binary charges is a
perfect four-bit code — `three_charges_are_not` — so four cuts identify and three
never can.  MEASURED: of the eight opening charges only three keep a run on a
four-cut line, and `bbb` is the trap, an even 8/8 split that still costs five.
An even split is not the same as a good one, and that is the whole lesson of the
opening.
-/
import Dregg2.Games.PathOfAngels.Core
import Dregg2.Games.PathOfAngels.SeedDraw
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.ArtificerLogic

open Dregg2.Games.PathOfAngels

set_option autoImplicit false

/-- How many charges a run may feed the mechanism.  Every accepted action spends
one unit, including the declaration, so `ACTION_LIMIT` is this plus the naming. -/
abbrev PROBE_BUDGET : Nat := 4

/-- The transcript ceiling: four charges and the one declaration that ends the
run.  This is the emitted `action_limit`. -/
abbrev ACTION_LIMIT : Nat := PROBE_BUDGET + 1

/-! ## Cogs and charges

A charge is a train of three cogs.  Iron is listed first everywhere so that the
canonical charge order runs `iii, iib, ibi, ibb, bii, bib, bbi, bbb` — the plain
binary counting order with brass as the one bit. -/

inductive Metal where
  | iron
  | brass
deriving Repr, DecidableEq

def allMetals : List Metal := [.iron, .brass]

theorem allMetals_complete (m : Metal) : m ∈ allMetals := by
  cases m <;> simp [allMetals]

/-- The three positions in a train.  A seat is a place a rule can talk about. -/
inductive Seat where
  | first
  | second
  | third
deriving Repr, DecidableEq

def allSeats : List Seat := [.first, .second, .third]

theorem allSeats_complete (p : Seat) : p ∈ allSeats := by
  cases p <;> simp [allSeats]

/-- One experiment's input: three cogs in a row. -/
structure Charge where
  first : Metal
  second : Metal
  third : Metal
deriving Repr, DecidableEq

def Charge.seat (ch : Charge) : Seat → Metal
  | .first => ch.first
  | .second => ch.second
  | .third => ch.third

def Charge.count (ch : Charge) (m : Metal) : Nat :=
  (if ch.first = m then 1 else 0) + (if ch.second = m then 1 else 0) +
  (if ch.third = m then 1 else 0)

theorem Charge.count_le_three (ch : Charge) (m : Metal) : ch.count m ≤ 3 := by
  obtain ⟨a, b, c⟩ := ch
  cases a <;> cases b <;> cases c <;> cases m <;> decide

/-- The two metals partition the three seats, so the counts always sum to three.
This is what makes `atLeast iron` and `atLeast brass` genuinely different
families rather than one family written twice. -/
theorem Charge.counts_sum (ch : Charge) :
    ch.count Metal.iron + ch.count Metal.brass = 3 := by
  obtain ⟨a, b, c⟩ := ch
  cases a <;> cases b <;> cases c <;> decide

def allCharges : List Charge :=
  allMetals.flatMap fun a =>
    allMetals.flatMap fun b =>
      allMetals.map fun c => { first := a, second := b, third := c }

theorem allCharges_complete (ch : Charge) : ch ∈ allCharges := by
  obtain ⟨a, b, c⟩ := ch
  cases a <;> cases b <;> cases c <;> decide

theorem allCharges_length : allCharges.length = 8 := by decide

theorem allCharges_nodup : allCharges.Nodup := by decide

/-! ## The field manual

Seven families.  The parameters are what make this a GRAMMAR rather than a list
of sixteen unrelated predicates, and they are what the descriptor renders: a
player reads `seat`, `uniform`, `atLeast`, and four singletons, not sixteen
arbitrary names. -/

/-- How many cogs a counting rule demands.  ⚠ There is no `three`.  At three,
`atLeast m three` IS `uniform m` — the collision this grammar was cut back from,
exhibited as a theorem in `the_cut_family_would_have_been_a_synonym`. -/
inductive Threshold where
  | one
  | two
deriving Repr, DecidableEq

def Threshold.val : Threshold → Nat
  | .one => 1
  | .two => 2

def allThresholds : List Threshold := [.one, .two]

theorem allThresholds_complete (k : Threshold) : k ∈ allThresholds := by
  cases k <;> simp [allThresholds]

/-- The published manual.  Sixteen inhabitants over seven families, and the
player can see every one of them before the first charge is fed. -/
inductive Rule where
  /-- The cog in seat `p` is `m`.  Six of these. -/
  | seat (p : Seat) (m : Metal)
  /-- Every cog is `m`.  Two. -/
  | uniform (m : Metal)
  /-- At least `k` cogs are `m`.  Four. -/
  | atLeast (m : Metal) (k : Threshold)
  /-- No two neighbouring cogs share a metal. -/
  | alternating
  /-- Some two neighbouring cogs share a metal.  The complement of the above,
  and a distinct entry because a player narrowing the lattice needs both. -/
  | hasRun
  /-- The outer cogs agree. -/
  | mirrored
  /-- An even number of brass cogs — zero counts. -/
  | evenBrass
deriving Repr, DecidableEq

/-- Does the mechanism turn on this charge, under this rule?  This is the ONLY
place a rule means anything; everything below reads it. -/
def Rule.accepts : Rule → Charge → Bool
  | .seat p m, ch => decide (ch.seat p = m)
  | .uniform m, ch => decide (ch.count m = 3)
  | .atLeast m k, ch => decide (k.val ≤ ch.count m)
  | .alternating, ch => decide (ch.first ≠ ch.second ∧ ch.second ≠ ch.third)
  | .hasRun, ch => decide (ch.first = ch.second ∨ ch.second = ch.third)
  | .mirrored, ch => decide (ch.first = ch.third)
  | .evenBrass, ch => decide (ch.count Metal.brass % 2 = 0)

/-- `alternating` and `hasRun` are exact complements.  Stated because two entries
that are each other's negation is a DESIGN choice — it doubles a family's reach
without doubling its cost — and a reader should see it asserted rather than
discover it. -/
theorem alternating_is_the_complement_of_hasRun (ch : Charge) :
    Rule.accepts .alternating ch = !Rule.accepts .hasRun ch := by
  obtain ⟨a, b, c⟩ := ch
  cases a <;> cases b <;> cases c <;> decide

def manual : List Rule :=
  (allSeats.flatMap fun p => allMetals.map fun m => Rule.seat p m) ++
  (allMetals.map Rule.uniform) ++
  (allMetals.flatMap fun m => allThresholds.map fun k => Rule.atLeast m k) ++
  [.alternating, .hasRun, .mirrored, .evenBrass]

theorem manual_complete (r : Rule) : r ∈ manual := by
  cases r with
  | seat p m => cases p <;> cases m <;> decide
  | uniform m => cases m <;> decide
  | atLeast m k => cases m <;> cases k <;> decide
  | alternating => decide
  | hasRun => decide
  | mirrored => decide
  | evenBrass => decide

theorem manual_length : manual.length = 16 := by decide

theorem manual_nodup : manual.Nodup := by decide

/-! ### ⚑ The distinguishability theorem

This is the design gate for an induction game, and it is a HARD one: if two rules
in the manual agreed on every charge, a player could run every legal experiment,
narrow correctly, and still lose to a coin flip.  That is the induction-game form
of "the budget never binds". -/

/-- What the mechanism does, charge by charge, under one rule.  Eight bits. -/
def signature (r : Rule) : List Bool := allCharges.map r.accepts

/-- ⚑ **Every pair of distinct rules is separated by a legal experiment.**  The
decidable form, over the published manual — this is what the gate reproduces
independently from the emitted table. -/
theorem every_pair_is_separated :
    manual.all (fun r => manual.all (fun r' =>
      decide (r = r') || allCharges.any (fun c => r.accepts c != r'.accepts c)))
      = true := by
  decide

/-- The same fact as a count: sixteen rules, sixteen distinct signatures. -/
theorem manual_signatures_are_distinct :
    (manual.map signature).eraseDups.length = manual.length := by
  native_decide

/-- Separation, read back out of the decidable check for two rules of the manual. -/
theorem separated_of_mem (r r' : Rule) (hr : r ∈ manual) (hr' : r' ∈ manual)
    (h : ∀ c : Charge, r.accepts c = r'.accepts c) : r = r' := by
  have hall := every_pair_is_separated
  rw [List.all_eq_true] at hall
  have h1 := hall r hr
  rw [List.all_eq_true] at h1
  have h2 := h1 r' hr'
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, bne_iff_ne] at h2
  rcases h2 with hd | ⟨c, _, hne⟩
  · exact hd
  · exact absurd (h c) hne

/-- ⚑ **THE DISTINGUISHABILITY THEOREM.**  Two rules that the mechanism cannot be
made to tell apart are the same rule.  Every rule is in the manual
(`manual_complete`), so this is unconditional: there is no inhabitant of `Rule`
hiding outside the published lattice, and no pair of them a player can be handed
without a way to separate them. -/
theorem manual_has_no_synonyms (r r' : Rule)
    (h : ∀ c : Charge, r.accepts c = r'.accepts c) : r = r' :=
  separated_of_mem r r' (manual_complete r) (manual_complete r') h

/-! ### ⚠ The property is refutable, and here is what it cost

`Threshold` has no `three`.  It had one while this grammar was being drawn, and
the family collided with `uniform` — the check above would have been FALSE.  The
cut family is modelled here by its signature so that the collision is a theorem
and not a design note, and so a later hand that adds `three` back finds this. -/

/-- The signature `atLeast m three` would have had. -/
def atLeastThreeSignature (m : Metal) : List Bool :=
  allCharges.map (fun ch => decide (3 ≤ ch.count m))

/-- ⚠ **The cut family WAS a synonym.**  At threshold three the counting family is
exactly `uniform`, so a manual carrying both would have had an indistinguishable
pair and a player could have lost a perfectly-played run to a coin flip. -/
theorem the_cut_family_would_have_been_a_synonym (m : Metal) :
    atLeastThreeSignature m = signature (Rule.uniform m) := by
  cases m <;> decide

/-- ⚠ **And the check goes red.**  A manual that repeats an entry fails
`manual_signatures_are_distinct`'s test, so the pin above is a gate and not a
decoration.  The first conjunct asserts the mutation HAPPENED — a falsifier whose
mutation silently became a no-op has stopped falsifying twice in this
repository. -/
def repeatedManual : List Rule := Rule.uniform Metal.brass :: manual

theorem repeated_manual_is_caught :
    repeatedManual ≠ manual ∧
    (repeatedManual.map signature).eraseDups.length ≠ repeatedManual.length := by
  refine ⟨?_, ?_⟩
  · native_decide
  · native_decide

/-! ## The instance — which rule the mechanism obeys

Drawn per (slot, mission, player) from the precommitted run seed via
`SeedDraw.drawBelow?`, exactly as `DeckDescent` draws its board.  The manual is
public; the DRAW is the secret. -/

def ruleAt (i : Fin 16) : Rule :=
  manual.get (Fin.cast manual_length.symm i)

theorem ruleAt_mem : ∀ i : Fin 16, ruleAt i ∈ manual := by decide

/-- Sixteen indices, sixteen distinct rules: the family is as large as it says. -/
theorem ruleAt_injective : ∀ i j : Fin 16, ruleAt i = ruleAt j → i = j := by decide

/-- `none` only if the 32-byte seed runs out of acceptable bytes.  A bound of 16
divides 256, so `ceilingFor 16 = 256` and no byte is ever rejected —
`draw_below_sixteen_never_rejects` says the `getD` below is dead code rather
than leaving a reader to assume it. -/
def ruleFromRunSeed? (runSeed : Digest32) : Option Rule := do
  let (i, _) ← SeedDraw.drawBelow? 16 (by decide) runSeed.bytes
  some (ruleAt i)

def ruleFromRunSeed (runSeed : Digest32) : Rule :=
  (ruleFromRunSeed? runSeed).getD (Rule.seat .first .iron)

theorem draw_below_sixteen_never_rejects (b : Fin 256) (rest : List (Fin 256)) :
    SeedDraw.drawBelow? 16 (by decide) (b :: rest)
      = some (⟨b.val % 16, Nat.mod_lt _ (by decide)⟩, rest) := by
  have hceil : SeedDraw.ceilingFor 16 = 256 := by decide
  simp [SeedDraw.drawBelow?, hceil, b.isLt]

/-! ## What a run knows

⚑ The whole state is the SURVIVING CANDIDATE SET plus the clock.  There is no
separate record of which charges have been fed, and there does not need to be: a
charge already fed can no longer split the survivors (they were filtered by its
answer), and a charge that cannot split is REFUSED.  `a_fed_charge_never_splits_
again` is that fact, and it is why the state space is the lattice of candidate
sets rather than the far larger space of evidence transcripts. -/

inductive Verdict where
  /-- The run is live. -/
  | probing
  /-- The run named the rule and was right. -/
  | identified
  /-- The run named a rule and was wrong. -/
  | mistaken
deriving Repr, DecidableEq

def Verdict.tag : Verdict → String
  | .probing => "probing"
  | .identified => "identified"
  | .mistaken => "mistaken"

/-- `candidates` is always a `List.filter` of `manual`, so it is in manual order
and a state has ONE representation.  `state_ids_are_distinct` is the check. -/
structure State where
  candidates : List Rule
  spent : Nat
  verdict : Verdict
deriving Repr, DecidableEq

def initialState : State where
  candidates := manual
  spent := 0
  verdict := .probing

/-- The charges still left to feed. -/
def chargesLeft (s : State) : Nat := PROBE_BUDGET - s.spent

/-- Does this charge cut the surviving candidates in two?  Public: it reads the
candidate set, which the player can see, and never the instance. -/
def splitsB (cands : List Rule) (c : Charge) : Bool :=
  cands.any (fun r => r.accepts c) && cands.any (fun r => !r.accepts c)

/-- One candidate left is certainty.  Two or more is a wager. -/
def certainB (s : State) : Bool := decide (s.candidates.length = 1)

/-! ## Actions -/

inductive Action where
  /-- Feed the mechanism this charge and watch.  Spends one unit of the budget. -/
  | probe (c : Charge)
  /-- Name the rule.  Terminal either way, and it spends a unit too, so the
  emitted `action_limit` is the whole transcript and not just its probes. -/
  | declare (r : Rule)
deriving Repr, DecidableEq

def allActions : List Action :=
  allCharges.map Action.probe ++ manual.map Action.declare

theorem allActions_complete (a : Action) : a ∈ allActions := by
  cases a with
  | probe c =>
      have hm : Action.probe c ∈ allCharges.map Action.probe :=
        List.mem_map.mpr ⟨c, allCharges_complete c, rfl⟩
      simp only [allActions, List.mem_append]
      exact Or.inl hm
  | declare r =>
      have hm : Action.declare r ∈ manual.map Action.declare :=
        List.mem_map.mpr ⟨r, manual_complete r, rfl⟩
      simp only [allActions, List.mem_append]
      exact Or.inr hm

theorem allActions_length : allActions.length = 24 := by decide

theorem allActions_nodup : allActions.Nodup := by decide

/-- ⚑ The single bit the instance contributes to any action.  For a probe it is
"does the mechanism turn"; for a declaration it is "is that the rule".  BOTH are
one bit, which is why every row of the emitted table names at most two
successors. -/
def oracleAnswer (hidden : Rule) : Action → Bool
  | .probe c => hidden.accepts c
  | .declare r => decide (hidden = r)

/-- Openness, in conjuncts that never move and that read PUBLIC state only.  The
instance is nowhere in this function, which is what makes a greyed-out action a
fact the player could have worked out. -/
def openB (s : State) (a : Action) : Bool :=
  decide (s.verdict = Verdict.probing) &&
  match a with
  | .probe c => decide (s.spent < PROBE_BUDGET) && splitsB s.candidates c
  | .declare r => s.candidates.contains r

/-- The effect of an action once the oracle has answered.  Total: openness is
decided separately, so every branch here is a state and not an `Option`. -/
def stepAns (ans : Bool) (s : State) (a : Action) : State :=
  match a with
  | .probe c =>
      { candidates := s.candidates.filter (fun r => r.accepts c == ans)
        spent := s.spent + 1
        verdict := .probing }
  | .declare r =>
      if ans then
        { candidates := [r], spent := s.spent + 1, verdict := .identified }
      else
        { candidates := s.candidates.filter (fun r' => r' != r)
          spent := s.spent + 1
          verdict := .mistaken }

def stepR (hidden : Rule) (s : State) (a : Action) : Option State :=
  match openB s a with
  | true => some (stepAns (oracleAnswer hidden a) s a)
  | false => none

def replayR (hidden : Rule) : State → List Action → Option State
  | s, [] => some s
  | s, a :: as =>
      match stepR hidden s a with
      | none => none
      | some s' => replayR hidden s' as

/-! ## Soundness — the truth is never eliminated

This is the theorem an induction game lives or dies by.  If an accepted action
could remove the hidden rule from the candidate set, the game could reach a state
in which NO declaration wins, and the player would be narrowing towards a lie. -/

/-- ⚑ **No accepted action ever eliminates the truth.**  Holds for probes and for
BOTH branches of a declaration — a wrong naming removes the rule that was named,
which the hidden rule is not. -/
theorem truth_survives (hidden : Rule) (s s' : State) (a : Action)
    (hmem : hidden ∈ s.candidates) (h : stepR hidden s a = some s') :
    hidden ∈ s'.candidates := by
  simp only [stepR] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    cases a with
    | probe c =>
        simp only [stepAns, oracleAnswer, List.mem_filter]
        exact ⟨hmem, by simp⟩
    | declare r =>
        simp only [stepAns, oracleAnswer]
        by_cases hr : hidden = r
        · subst hr
          simp
        · simp only [decide_eq_true_eq, hr, ↓reduceIte, List.mem_filter]
          exact ⟨hmem, by simp [hr]⟩
  · exact absurd h (by simp)

/-- The invariant, carried the length of a transcript. -/
theorem replay_keeps_the_truth (hidden : Rule) (acts : List Action) :
    ∀ (s s' : State), hidden ∈ s.candidates → replayR hidden s acts = some s' →
      hidden ∈ s'.candidates := by
  induction acts with
  | nil =>
      intro s s' hmem h
      simp only [replayR, Option.some.injEq] at h
      subst h
      exact hmem
  | cons a as ih =>
      intro s s' hmem h
      simp only [replayR] at h
      split at h
      · contradiction
      · rename_i s₁ hstep
        exact ih s₁ s' (truth_survives hidden s s₁ a hmem hstep) h

/-- The run starts holding every rule, so the invariant is available from the
opening position for any instance whatsoever. -/
theorem the_truth_starts_in_the_manual (hidden : Rule) :
    hidden ∈ initialState.candidates :=
  manual_complete hidden

/-- ⚑ **Certainty cannot be mistaken.**  One candidate left, and naming it
identifies the rule — for EVERY hidden rule the evidence still permits.  This is
what makes the last cut worth making rather than guessing one earlier. -/
theorem certainty_cannot_be_mistaken (hidden : Rule) (s : State) (r : Rule)
    (hmem : hidden ∈ s.candidates) (hsingle : s.candidates = [r])
    (hopen : openB s (.declare r) = true) :
    stepR hidden s (.declare r) =
      some { candidates := [r], spent := s.spent + 1, verdict := .identified } := by
  rw [hsingle] at hmem
  have hr : hidden = r := by simpa using hmem
  subst hr
  simp [stepR, hopen, stepAns, oracleAnswer]

/-- A naming is right exactly when it names the rule.  There is no branch in
which a wrong name is scored. -/
theorem a_declaration_is_scored_on_the_truth (hidden : Rule) (s s' : State)
    (r : Rule) (h : stepR hidden s (.declare r) = some s') :
    (s'.verdict = Verdict.identified ↔ hidden = r) := by
  simp only [stepR] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    simp only [stepAns, oracleAnswer]
    by_cases hr : hidden = r
    · subst hr; simp
    · simp [hr]
  · exact absurd h (by simp)

/-! ## Reading openness back out of an accepted action -/

theorem step_some_open (hidden : Rule) (s s' : State) (a : Action)
    (h : stepR hidden s a = some s') : openB s a = true := by
  simp only [stepR] at h
  split at h
  · assumption
  · exact absurd h (by simp)

theorem step_some_probing (hidden : Rule) (s s' : State) (a : Action)
    (h : stepR hidden s a = some s') : s.verdict = Verdict.probing := by
  have hopen := step_some_open hidden s s' a h
  simp only [openB, Bool.and_eq_true, decide_eq_true_eq] at hopen
  exact hopen.1

/-- ⚑ **Every accepted action spends exactly one unit**, the declaration
included.  So the emitted `action_limit` is the whole transcript length and the
machine is a DAG layered by the clock — which is what lets the gate's minimax be
one sweep and not a fixpoint. -/
theorem step_spends_exactly_one (hidden : Rule) (s s' : State) (a : Action)
    (h : stepR hidden s a = some s') : s'.spent = s.spent + 1 := by
  simp only [stepR] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    cases a with
    | probe c => rfl
    | declare r =>
        simp only [stepAns]
        split <;> rfl
  · exact absurd h (by simp)

/-- A probe leaves the run live; only a declaration ends it. -/
theorem a_probe_leaves_the_run_live (hidden : Rule) (s s' : State) (c : Charge)
    (h : stepR hidden s (.probe c) = some s') : s'.verdict = Verdict.probing := by
  simp only [stepR] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rfl
  · exact absurd h (by simp)

/-- A declaration always ends it. -/
theorem a_declaration_ends_the_run (hidden : Rule) (s s' : State) (r : Rule)
    (h : stepR hidden s (.declare r) = some s') :
    s'.verdict ≠ Verdict.probing := by
  simp only [stepR] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    simp only [stepAns]
    split <;> simp
  · exact absurd h (by simp)

/-- Candidates only ever shrink.  There is no action that revives a refuted
rule, which is what makes the narrowing monotone and the lattice a lattice. -/
theorem candidates_never_grow (hidden : Rule) (s s' : State) (a : Action)
    (h : stepR hidden s a = some s') (r : Rule)
    (hmem : r ∈ s'.candidates) (hne : s'.verdict = Verdict.probing) :
    r ∈ s.candidates := by
  simp only [stepR] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    cases a with
    | probe c =>
        simp only [stepAns, List.mem_filter] at hmem
        exact hmem.1
    | declare r' =>
        exfalso
        simp only [stepAns] at hne
        revert hne
        split <;> simp
  · exact absurd h (by simp)

/-! ## Refusals — each emitted reason is a theorem -/

theorem not_open_refuses (hidden : Rule) (s : State) (a : Action)
    (h : openB s a = false) : stepR hidden s a = none := by
  simp [stepR, h]

/-- A finished run refuses everything.  A player cannot keep feeding a mechanism
that has already been named. -/
theorem a_finished_run_refuses_everything (hidden : Rule) (s : State) (a : Action)
    (h : s.verdict ≠ Verdict.probing) : stepR hidden s a = none := by
  exact not_open_refuses hidden s a (by simp [openB, h])

/-- Out of charges, the mechanism takes no more.  Only a declaration is left,
which is what makes the last cut a real decision instead of a formality. -/
theorem an_empty_budget_refuses_a_probe (hidden : Rule) (s : State) (c : Charge)
    (h : PROBE_BUDGET ≤ s.spent) : stepR hidden s (.probe c) = none := by
  exact not_open_refuses hidden s (.probe c)
    (by simp [openB, Nat.not_lt.mpr h])

/-- ⚑ **A charge that cannot split is refused.**  This is the rule that makes the
interesting decision *which* charge rather than *whether* to spend one: there is
no way to burn the budget on a question the evidence has already answered. -/
theorem an_answered_charge_is_refused (hidden : Rule) (s : State) (c : Charge)
    (h : splitsB s.candidates c = false) : stepR hidden s (.probe c) = none := by
  exact not_open_refuses hidden s (.probe c) (by simp [openB, h])

/-- ⚑ **A charge already fed can never split again.**  Its answer filtered the
survivors, so they all agree on it forever.  Together with the theorem above this
is why the state need not record which charges were fed: "already fed" and
"cannot split" are the same refusal. -/
theorem a_fed_charge_never_splits_again (ans : Bool) (s : State) (c : Charge) :
    splitsB (stepAns ans s (.probe c)).candidates c = false := by
  simp only [stepAns, splitsB, Bool.and_eq_false_iff]
  cases ans with
  | true =>
      right
      simp only [Bool.not_eq_true, List.any_eq_false, List.mem_filter]
      intro r hr
      simpa using hr.2
  | false =>
      left
      simp only [List.any_eq_false, List.mem_filter]
      intro r hr
      simpa using hr.2

/-- A rule the evidence has refuted cannot be named.  A player is never offered a
declaration they can already see is wrong. -/
theorem a_refuted_rule_cannot_be_named (hidden : Rule) (s : State) (r : Rule)
    (h : s.candidates.contains r = false) : stepR hidden s (.declare r) = none := by
  refine not_open_refuses hidden s (.declare r) ?_
  simp only [openB, Bool.and_eq_false_iff]
  exact Or.inr h

/-! ## Replay and the budget -/

theorem replayR_append (hidden : Rule) (s : State) (xs ys : List Action) :
    replayR hidden s (xs ++ ys) =
      (replayR hidden s xs).bind (fun s' => replayR hidden s' ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons a as ih =>
      simp only [List.cons_append, replayR]
      split <;> simp_all

theorem refused_prefix_refuses_replay (hidden : Rule) (s : State) (a : Action)
    (as : List Action) (h : stepR hidden s a = none) :
    replayR hidden s (a :: as) = none := by
  simp [replayR, h]

/-- One unit per accepted action all the way along. -/
theorem replayR_spends (hidden : Rule) (acts : List Action) :
    ∀ (s s' : State), replayR hidden s acts = some s' →
      s'.spent = s.spent + acts.length := by
  induction acts with
  | nil =>
      intro s s' h
      simp only [replayR, Option.some.injEq] at h
      subst h
      simp
  | cons a as ih =>
      intro s s' h
      simp only [replayR] at h
      split at h
      · contradiction
      · rename_i s₁ hstep
        have h1 := step_spends_exactly_one hidden s s₁ a hstep
        have h2 := ih s₁ s' h
        simp only [List.length_cons]
        omega

/-- A run that has been named replays nothing further: every action is refused,
so the only transcript a finished state accepts is the empty one. -/
theorem a_finished_run_replays_nothing (hidden : Rule) (s s' : State)
    (acts : List Action) (h : s.verdict ≠ Verdict.probing)
    (hr : replayR hidden s acts = some s') : s' = s := by
  cases acts with
  | nil =>
      simp only [replayR, Option.some.injEq] at hr
      exact hr.symm
  | cons a as =>
      rw [refused_prefix_refuses_replay hidden s a as
        (a_finished_run_refuses_everything hidden s a h)] at hr
      exact absurd hr (by simp)

/-- The clock never passes the transcript ceiling.  A probe needs
`spent < PROBE_BUDGET`, so at most four are accepted; a declaration spends the
fifth and then refuses everything. -/
theorem step_clock_bound (hidden : Rule) (s s' : State) (a : Action)
    (h : stepR hidden s a = some s') (hle : s.spent ≤ PROBE_BUDGET) :
    s'.spent ≤ ACTION_LIMIT ∧
      (s'.verdict = Verdict.probing → s'.spent ≤ PROBE_BUDGET) := by
  have hone := step_spends_exactly_one hidden s s' a h
  have hopen := step_some_open hidden s s' a h
  cases a with
  | probe c =>
      simp only [openB, Bool.and_eq_true, decide_eq_true_eq] at hopen
      have hlt : s.spent < PROBE_BUDGET := hopen.2.1
      refine ⟨?_, fun _ => by omega⟩
      simp only [ACTION_LIMIT]
      omega
  | declare r =>
      refine ⟨?_, fun hp => absurd hp (a_declaration_ends_the_run hidden s s' r h)⟩
      simp only [ACTION_LIMIT]
      omega

theorem replay_clock_bounded (hidden : Rule) (acts : List Action) :
    ∀ (s s' : State), s.spent ≤ PROBE_BUDGET →
      replayR hidden s acts = some s' → s'.spent ≤ ACTION_LIMIT := by
  induction acts with
  | nil =>
      intro s s' hle hr
      simp only [replayR, Option.some.injEq] at hr
      subst hr
      simp only [ACTION_LIMIT]
      omega
  | cons a as ih =>
      intro s s' hle hr
      simp only [replayR] at hr
      split at hr
      · contradiction
      · rename_i s₁ hstep
        have hb := step_clock_bound hidden s s₁ a hstep hle
        cases hv : s₁.verdict with
        | probing => exact ih s₁ s' (hb.2 hv) hr
        | identified =>
            have heq := a_finished_run_replays_nothing hidden s₁ s' as
              (by rw [hv]; decide) hr
            subst heq
            exact hb.1
        | mistaken =>
            have heq := a_finished_run_replays_nothing hidden s₁ s' as
              (by rw [hv]; decide) hr
            subst heq
            exact hb.1

/-- ⚑ **The emitted `action_limit` is a cap the kernel cannot exceed.**  Not a cap
the client enforces: an accepted transcript is at most four charges and one
naming, because the fifth probe is refused and the naming is terminal. -/
theorem accepted_transcript_within_budget (hidden : Rule) (acts : List Action)
    (s' : State) (h : replayR hidden initialState acts = some s') :
    acts.length ≤ ACTION_LIMIT := by
  have hspent := replayR_spends hidden acts initialState s' h
  have hbound := replay_clock_bounded hidden acts initialState s'
    (by simp only [initialState]; omega) h
  simp only [initialState] at hspent
  omega

/-- ⚑ The only transition that reaches `identified` is a naming that was right,
and it leaves the hidden rule ALONE in the candidate set.  So an identified state
does not merely record "the run won" — it records WHICH rule the mechanism
obeyed, and it could not have recorded a different one. -/
theorem identified_state_is_the_singleton (hidden : Rule) (s s' : State)
    (a : Action) (h : stepR hidden s a = some s')
    (hid : s'.verdict = Verdict.identified) : s'.candidates = [hidden] := by
  simp only [stepR] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    cases a with
    | probe c =>
        simp only [stepAns] at hid
        exact absurd hid (by decide)
    | declare r =>
        simp only [stepAns, oracleAnswer] at hid ⊢
        by_cases hr : hidden = r
        · subst hr
          simp
        · simp only [decide_eq_true_eq, hr, ↓reduceIte] at hid
          exact absurd hid (by decide)
  · exact absurd h (by simp)

/-- The same fact carried the length of a transcript. -/
theorem replay_identified_is_the_singleton (hidden : Rule) (acts : List Action) :
    ∀ (s s' : State), s.verdict = Verdict.probing →
      replayR hidden s acts = some s' → s'.verdict = Verdict.identified →
      s'.candidates = [hidden] := by
  induction acts with
  | nil =>
      intro s s' hprob hr hid
      simp only [replayR, Option.some.injEq] at hr
      subst hr
      rw [hprob] at hid
      exact absurd hid (by decide)
  | cons a as ih =>
      intro s s' hprob hr hid
      simp only [replayR] at hr
      split at hr
      · contradiction
      · rename_i s₁ hstep
        cases hv : s₁.verdict with
        | probing => exact ih s₁ s' hv hr hid
        | identified =>
            have heq := a_finished_run_replays_nothing hidden s₁ s' as
              (by rw [hv]; decide) hr
            subst heq
            exact identified_state_is_the_singleton hidden s _ a hstep hid
        | mistaken =>
            have heq := a_finished_run_replays_nothing hidden s₁ s' as
              (by rw [hv]; decide) hr
            subst heq
            rw [hv] at hid
            exact absurd hid (by decide)

/-! ## The design properties, measured over the actual transition

Everything below is `native_decide` over `stepR`/`certainWithin` — the same
functions the emitter tabulates and the judge runs. -/

/-- ⚑ Can this candidate set still be cut down to ONE, within `fuel` charges, on
the WORST answer the mechanism could give?  A minimax: both branches of every cut
must succeed, so a `true` here is a guarantee and not a hope. -/
def certainWithin : Nat → List Rule → Bool
  | 0, cands => decide (cands.length ≤ 1)
  | fuel + 1, cands =>
      decide (cands.length ≤ 1) ||
      allCharges.any (fun c =>
        splitsB cands c &&
        certainWithin fuel (cands.filter (fun r => r.accepts c)) &&
        certainWithin fuel (cands.filter (fun r => !(r.accepts c))))

/-- Can this run still reach certainty on skill alone?  A run that cannot may
still WIN — it can name a survivor and be lucky — but it can no longer be sure,
and a client that does not say so is hiding the thing the budget is for. -/
def certifiableB (s : State) : Bool :=
  decide (s.verdict = Verdict.probing) && certainWithin (chargesLeft s) s.candidates

/-- ⚑ **Four charges are enough.**  From the full manual, on the worst answers the
mechanism can give, four cuts always reach a single rule. -/
theorem four_charges_are_enough : certainWithin PROBE_BUDGET manual = true := by
  native_decide

/-- ⚑ **And three are not.**  Sixteen rules over binary charges cannot be
separated in three cuts — the budget is the information floor and the slack is
ZERO.  These two theorems together are the whole sizing argument. -/
theorem three_charges_are_not : certainWithin (PROBE_BUDGET - 1) manual = false := by
  native_decide

/-! ### The opening, measured

The single most useful thing a player can be taught about this game is that an
EVEN CUT IS NOT THE SAME AS A GOOD ONE.  Here is that, as a theorem. -/

/-- How many rules of the manual the mechanism turns on, for this charge. -/
def turningCount (c : Charge) : Nat := (manual.filter (fun r => r.accepts c)).length

/-- Does opening with this charge leave a run able to finish inside the budget? -/
def keepsTheBudget (c : Charge) : Bool :=
  splitsB manual c &&
  certainWithin (PROBE_BUDGET - 1) (manual.filter (fun r => r.accepts c)) &&
  certainWithin (PROBE_BUDGET - 1) (manual.filter (fun r => !(r.accepts c)))

/-- ⚑ **An even split is not the same as a good one.**  FOUR of the eight opening
charges cut the sixteen rules exactly in half; only THREE of those four leave a
run able to reach certainty in the three charges that remain.  The fourth is the
trap, and a player who opens on it has already lost the guarantee without
spending anything they can see.

The third conjunct is what makes this a statement and not a coincidence: every
charge that keeps the budget IS an even cut, so evenness is necessary and not
sufficient — exactly the lesson the opening is for. -/
theorem an_even_split_is_not_a_good_one :
    (allCharges.filter (fun c => decide (turningCount c = 8))).length = 4 ∧
    (allCharges.filter keepsTheBudget).length = 3 ∧
    (allCharges.all (fun c => !keepsTheBudget c || decide (turningCount c = 8)))
      = true := by
  native_decide

/-! ## The parametric table — the rules without the instance

A descriptor cannot carry the hidden rule.  What it carries instead is a table in
which every row that CONSULTS the instance names BOTH of its successors, and
every other row names one.  `stepWith` is the transition under a fixed answer —
it is `stepR` itself with the oracle replaced by a constant, not a copy of it. -/

def stepWith (ans : Bool) (s : State) (a : Action) : Option State :=
  match openB s a with
  | true => some (stepAns ans s a)
  | false => none

theorem stepR_eq_stepWith (hidden : Rule) (s : State) (a : Action) :
    stepR hidden s a = stepWith (oracleAnswer hidden a) s a := rfl

/-- ⚑ **The row is complete.**  For every hidden rule, every state and every
action, the real transition equals one of the two branches the emitted row names.
A client that renders both branches has rendered every outcome that can occur,
and the descriptor has still not said which.

Where `DeckDescent` needed a nine-way case split for this, one suffices here: the
instance reaches the transition through `oracleAnswer` and nowhere else, and
`oracleAnswer` is a `Bool`. -/
theorem step_is_one_of_the_two_branches (hidden : Rule) (s : State) (a : Action) :
    stepR hidden s a = stepWith true s a ∨ stepR hidden s a = stepWith false s a := by
  rw [stepR_eq_stepWith]
  cases h : oracleAnswer hidden a with
  | true => exact Or.inl rfl
  | false => exact Or.inr rfl

/-- Whether an action is closed here does not depend on the instance: both
readings refuse together, so a greyed-out action is a fact the player could have
worked out and never a bit they cannot see. -/
theorem branches_agree_on_refusal (s : State) (a : Action) :
    (stepWith true s a).isNone = (stepWith false s a).isNone := by
  simp only [stepWith]
  split <;> rfl

/-- Do ALL surviving candidates answer this action the same way?  If they do, the
row does not need the oracle and the emitted row names one successor. -/
def allAnswerB (s : State) (a : Action) (b : Bool) : Bool :=
  s.candidates.all (fun r => oracleAnswer r a == b)

/-- ⚑ A forced answer is the TRUE answer.  If every survivor says `b`, then the
hidden rule says `b` — because the hidden rule is a survivor (`truth_survives`).
This is what makes a one-successor row honest rather than a guess. -/
theorem forced_answer_is_the_truth (s : State) (a : Action) (b : Bool)
    (h : allAnswerB s a b = true) (hidden : Rule) (hmem : hidden ∈ s.candidates) :
    oracleAnswer hidden a = b := by
  rw [allAnswerB, List.all_eq_true] at h
  simpa using h hidden hmem

/-- Why an action is refused here.  The conjuncts are tested in the SAME order
`openB` tests them, so the reason a client renders is the first thing that
actually failed and not a plausible one. -/
def refusalReason (s : State) (a : Action) : String :=
  if s.verdict = Verdict.identified then "solved"
  else if s.verdict = Verdict.mistaken then "run-lost"
  else
    match a with
    | .probe _ =>
        if PROBE_BUDGET ≤ s.spent then "no-charges-left" else "already-answered"
    | .declare _ => "refuted"

/-- The five reasons this kernel can give.  ⚑ Every one of them is reachable —
`every_declared_reason_is_reachable` — because a refusal a client can render and
the kernel can never produce is a lie in the UI.

⚠ `solved` and `run-lost` are SEPARATE, and the split is not cosmetic.  A run
that ended is not a run that was won, and this game is the one on the rack where
those come apart: a mistaken naming stops the machine exactly as a right one
does.  A single `run-over` covering both would tell a player who guessed wrong
the same thing it tells a player who was right.  (`solved` is also the name the
shared browser engine requires on a terminal state's rows, so the split is the
contract as well as the honest reading.) -/
def refusalVocabulary : List String :=
  ["solved", "run-lost", "no-charges-left", "already-answered", "refuted"]

/-- A row of the emitted table.  `refuse` carries a named reason and no
successor; `advance` is instance-independent and carries one; `resolve` consults
the instance and carries both. -/
inductive Row where
  | refuse (reason : String)
  | advance (next : State)
  | resolve (onTurn onJam : State)
deriving DecidableEq

/-- Factored out of `rowFor` so that the three booleans are ordinary arguments and
every proof below is a `cases` on a `Bool` rather than a fight with a nested
match under a hypothesis. -/
def rowOf (isOpen allTurn allJam : Bool) (reason : String) (onTurn onJam : State) : Row :=
  match isOpen, allTurn, allJam with
  | false, _, _ => .refuse reason
  | true, true, _ => .advance onTurn
  | true, false, true => .advance onJam
  | true, false, false => .resolve onTurn onJam

def rowFor (s : State) (a : Action) : Row :=
  rowOf (openB s a) (allAnswerB s a true) (allAnswerB s a false)
    (refusalReason s a) (stepAns true s a) (stepAns false s a)

/-- ⚑ **An `advance` row IS the real step**, for every instance the evidence still
permits.  A client that follows the single successor of a one-branch row has not
guessed: the row is one-branch exactly when every surviving candidate agrees, and
the hidden rule is a surviving candidate.

⚠ `DeckDescent` names this direction and does NOT land it — its
`rowFor` compares two successors, and the proof foundered on reducing a
two-scrutinee match under a hypothesis.  Deriving the row from `allAnswerB`
instead of from an equality between branches is what makes it go through. -/
theorem advance_row_is_the_real_step (s : State) (a : Action) (n : State)
    (hidden : Rule) (hmem : hidden ∈ s.candidates)
    (hrow : rowFor s a = Row.advance n) : stepR hidden s a = some n := by
  simp only [rowFor] at hrow
  cases hopen : openB s a with
  | false =>
      rw [hopen] at hrow
      simp only [rowOf] at hrow
      exact absurd hrow (by simp)
  | true =>
      cases htrue : allAnswerB s a true with
      | true =>
          rw [hopen, htrue] at hrow
          simp only [rowOf, Row.advance.injEq] at hrow
          rw [stepR_eq_stepWith, forced_answer_is_the_truth s a true htrue hidden hmem,
            stepWith, hopen, hrow]
      | false =>
          cases hfalse : allAnswerB s a false with
          | true =>
              rw [hopen, htrue, hfalse] at hrow
              simp only [rowOf, Row.advance.injEq] at hrow
              rw [stepR_eq_stepWith,
                forced_answer_is_the_truth s a false hfalse hidden hmem, stepWith,
                hopen, hrow]
          | false =>
              rw [hopen, htrue, hfalse] at hrow
              simp only [rowOf] at hrow
              exact absurd hrow (by simp)

/-- And a `refuse` row is a real refusal, for every instance: openness never
reads the oracle. -/
theorem refuse_row_is_a_real_refusal (s : State) (a : Action) (reason : String)
    (hidden : Rule) (hrow : rowFor s a = Row.refuse reason) :
    stepR hidden s a = none := by
  simp only [rowFor] at hrow
  cases hopen : openB s a with
  | false => exact not_open_refuses hidden s a hopen
  | true =>
      rw [hopen] at hrow
      cases htrue : allAnswerB s a true <;> cases hfalse : allAnswerB s a false <;>
        rw [htrue, hfalse] at hrow <;> simp only [rowOf] at hrow <;>
        exact absurd hrow (by simp)

/-- ⚑ **A declaration made on certainty is a one-branch row.**  With a single
candidate left, `allAnswerB` forces `true`, so the table names ONE successor and
the run is over without the oracle being consulted at all.  This is the
structural payoff of narrowing: the descriptor itself distinguishes a sure
naming from a wager, in bytes, before the player commits. -/
theorem certain_declaration_is_an_advance (s : State) (r : Rule)
    (hsingle : s.candidates = [r]) (hopen : openB s (.declare r) = true) :
    rowFor s (.declare r) =
      Row.advance { candidates := [r], spent := s.spent + 1, verdict := .identified } := by
  have hall : allAnswerB s (Action.declare r) true = true := by
    simp [allAnswerB, hsingle, oracleAnswer]
  simp only [rowFor, hopen, hall, rowOf, stepAns, oracleAnswer]
  simp

/-! ### The board-independent closure

Both branches of every resolve row are followed, so the closure is the set of
knowledge states reachable under SOME instance — exactly the state set a
descriptor that names both branches has to declare.

⚑ LAYERED BY THE CLOCK.  `step_spends_exactly_one` says every accepted action
advances `spent`, so a state reachable in `n` actions has `spent = n` and two
layers can never overlap.  Enumerating layer by layer means each level is only
ever deduplicated against itself — the difference between an `eraseDups` over
~57,000 entries and one over a few hundred. -/

def rowSuccessors (s : State) (a : Action) : List State :=
  match rowFor s a with
  | .refuse _ => []
  | .advance n => [n]
  | .resolve m f => [m, f]

def parametricSuccessors (s : State) : List State :=
  (allActions.flatMap (rowSuccessors s)).eraseDups

def parametricLayer : Nat → List State
  | 0 => [initialState]
  | n + 1 => ((parametricLayer n).flatMap parametricSuccessors).eraseDups

def parametricStates : List State :=
  (List.range (ACTION_LIMIT + 1)).flatMap parametricLayer

def parametricRowCount : Nat := parametricStates.length * allActions.length

/-- ⚑ **The layers are the clock.**  Every state in layer `n` has spent exactly
`n`, which is why the layered enumeration is complete and why the concatenation
above needs no cross-layer deduplication. -/
theorem parametric_layers_are_the_clock :
    (List.range (ACTION_LIMIT + 1)).all (fun n =>
      (parametricLayer n).all (fun s => decide (s.spent = n))) = true := by
  native_decide

/-- ⚑ **The table is closed.**  Every successor any row names is a state the
descriptor declares, so a client can never be handed an id it does not have. -/
theorem parametric_closure_is_closed :
    parametricStates.all (fun s =>
      allActions.all (fun a =>
        (rowSuccessors s a).all (fun n => parametricStates.contains n))) = true := by
  native_decide

theorem parametric_states_nodup : parametricStates.eraseDups = parametricStates := by
  native_decide

theorem initial_state_is_declared : parametricStates.contains initialState = true := by
  native_decide

/-- ⚑ **No declared state is empty.**  A candidate set can never be narrowed to
nothing, because the hidden rule always survives — so the state a mistaken
naming would produce from a SINGLE candidate is never named by any row.  This is
`truth_survives`, visible in the enumeration. -/
theorem no_declared_state_is_empty :
    parametricStates.all (fun s => decide (0 < s.candidates.length)) = true := by
  native_decide

/-- ⚑ **Resolve rows name two different states**, so the gate's "the oracle bit is
not consulted and the row should be an accept" refusal cannot fire. -/
theorem resolve_rows_name_two_states :
    parametricStates.all (fun s => allActions.all (fun a =>
      match rowFor s a with
      | .resolve m f => decide (m ≠ f)
      | _ => true)) = true := by
  native_decide

/-- ⚑ **The table really consults the instance.** -/
def resolveRowCount : Nat :=
  (parametricStates.flatMap (fun s =>
    allActions.filter (fun a =>
      match rowFor s a with | .resolve _ _ => true | _ => false))).length

theorem the_table_consults_the_instance : 0 < resolveRowCount := by
  native_decide

/-- ⚑ **Every open probe resolves.**  A charge that cannot split is refused, so
there is no accepted probe whose row names one successor: every experiment a
player is allowed to run is one whose answer they do not already hold.  This is
requirement "which charge, not whether", as a property of the emitted table. -/
theorem every_open_probe_resolves :
    parametricStates.all (fun s => allCharges.all (fun c =>
      match rowFor s (.probe c) with
      | .advance _ => false
      | _ => true)) = true := by
  native_decide

/-- The refusal reasons the emitted table actually carries. -/
def emittedReasons : List String :=
  (parametricStates.flatMap (fun s =>
    allActions.filterMap (fun a =>
      match rowFor s a with | .refuse reason => some reason | _ => none))).eraseDups

/-- ⚑ **Every declared refusal reason is reachable, and no other is emitted.**  A
reason a client can render but the kernel can never produce is a lie in the UI;
a reason the kernel produces but the vocabulary does not name is a string the
client cannot translate. -/
theorem every_declared_reason_is_reachable :
    (refusalVocabulary.all (fun r => emittedReasons.contains r) &&
     emittedReasons.all (fun r => refusalVocabulary.contains r)) = true := by
  native_decide

/-! ### Reachable design measurements -/

/-- The first charge that keeps certainty reachable on BOTH answers. -/
def bestProbe (s : State) : Option Charge :=
  allCharges.find? (fun c =>
    splitsB s.candidates c &&
    certainWithin (chargesLeft s - 1) (s.candidates.filter (fun r => r.accepts c)) &&
    certainWithin (chargesLeft s - 1) (s.candidates.filter (fun r => !(r.accepts c))))

/-- The line a player who never wastes a cut would walk against this instance. -/
def perfectLine (hidden : Rule) : Nat → State → List Action
  | 0, s => match s.candidates with | [r] => [Action.declare r] | _ => []
  | fuel + 1, s =>
      match s.candidates with
      | [r] => [Action.declare r]
      | _ =>
          match bestProbe s with
          | none => []
          | some c =>
              Action.probe c ::
                perfectLine hidden fuel (stepAns (hidden.accepts c) s (.probe c))

def identifies (hidden : Rule) : Bool :=
  match replayR hidden initialState (perfectLine hidden ACTION_LIMIT initialState) with
  | none => false
  | some s => decide (s.verdict = Verdict.identified)

/-- ⚑ **Every instance is identifiable, and the line is exactly the budget.**  No
draw is a dead mission — for all sixteen hidden rules the never-waste-a-cut line
names the rule, and it takes all five actions to do it.  Same shape as
`DeckDescent.every_board_can_be_banked`, and the same argument: a family with an
unwinnable member is a family with a coin flip in it. -/
theorem every_rule_is_identifiable :
    manual.all identifies = true ∧
    manual.all (fun r =>
      decide ((perfectLine r ACTION_LIMIT initialState).length = ACTION_LIMIT))
      = true := by
  refine ⟨?_, ?_⟩
  · native_decide
  · native_decide

/-- States from which the run must name a rule with more than one candidate still
standing: out of charges, and holding a wager. -/
def wagerStates : Nat :=
  (parametricStates.filter (fun s =>
    decide (s.verdict = Verdict.probing) &&
    decide (2 ≤ s.candidates.length) &&
    decide (PROBE_BUDGET ≤ s.spent))).length

/-- ⚑ **The run can be lost.**  A player who spends a cut badly reaches a state
with charges gone and more than one rule standing; from there naming is a wager
and the run can end mistaken.  A design in which this count is zero is one where
the budget never binds. -/
theorem the_run_can_be_lost : 0 < wagerStates := by native_decide

/-- Reachable states from which certainty is still available. -/
def certifiableCount : Nat := (parametricStates.filter certifiableB).length

/-- Reachable live states from which it is NOT. -/
def luckOnlyCount : Nat :=
  (parametricStates.filter (fun s =>
    decide (s.verdict = Verdict.probing) && !certifiableB s)).length

/-- ⚑ **Both sides of the skill/luck line are reachable.**  There are live states
that can still be brought to certainty and live states that cannot, so
`certifiable` is a field that says something — a flag that is constant is a flag
that is decoration. -/
theorem the_skill_line_is_real : 0 < certifiableCount ∧ 0 < luckOnlyCount := by
  refine ⟨?_, ?_⟩
  · native_decide
  · native_decide

/-! ## Rendering names

Ids are semantic, not enumeration indices, so a re-emission that visits states in
a different order produces the same wire. -/

def Metal.tag : Metal → String
  | .iron => "iron"
  | .brass => "brass"

def Metal.code : Metal → String
  | .iron => "i"
  | .brass => "b"

def Charge.tag (ch : Charge) : String :=
  ch.first.code ++ ch.second.code ++ ch.third.code

def Seat.tag : Seat → String
  | .first => "first"
  | .second => "second"
  | .third => "third"

def Threshold.tag : Threshold → String
  | .one => "one"
  | .two => "two"

def Rule.tag : Rule → String
  | .seat p m => "seat-" ++ p.tag ++ "-" ++ m.tag
  | .uniform m => "uniform-" ++ m.tag
  | .atLeast m k => "at-least-" ++ k.tag ++ "-" ++ m.tag
  | .alternating => "alternating"
  | .hasRun => "has-run"
  | .mirrored => "mirrored"
  | .evenBrass => "even-brass"

def Rule.family : Rule → String
  | .seat _ _ => "seat"
  | .uniform _ => "uniform"
  | .atLeast _ _ => "at-least"
  | .alternating => "alternating"
  | .hasRun => "has-run"
  | .mirrored => "mirrored"
  | .evenBrass => "even-brass"

def Rule.label : Rule → String
  | .seat .first m => "the leading cog is " ++ m.tag
  | .seat .second m => "the middle cog is " ++ m.tag
  | .seat .third m => "the trailing cog is " ++ m.tag
  | .uniform m => "every cog is " ++ m.tag
  | .atLeast m .one => "at least one cog is " ++ m.tag
  | .atLeast m .two => "at least two cogs are " ++ m.tag
  | .alternating => "no two neighbouring cogs share a metal"
  | .hasRun => "some two neighbouring cogs share a metal"
  | .mirrored => "the outer cogs are the same metal"
  | .evenBrass => "an even number of cogs are brass"

def Action.tag : Action → String
  | .probe c => "feed-" ++ c.tag
  | .declare r => "name-" ++ r.tag

def Action.label : Action → String
  | .probe c => "Feed the mechanism " ++ c.tag
  | .declare r => "Name it: " ++ r.label

theorem rule_tags_are_distinct :
    (manual.map Rule.tag).eraseDups.length = manual.length := by native_decide

theorem charge_tags_are_distinct :
    (allCharges.map Charge.tag).eraseDups.length = allCharges.length := by decide

theorem action_tags_are_distinct :
    (allActions.map Action.tag).eraseDups.length = allActions.length := by
  native_decide

/-- The surviving candidates as a sixteen-character mask in manual order.  A
state has ONE representation because `candidates` is always a `List.filter` of
`manual`, and `state_ids_are_distinct` is the check that it does. -/
def candidateMask (s : State) : String :=
  (manual.map (fun r => if s.candidates.contains r then "1" else "0")).foldl (· ++ ·) ""

def stateId (s : State) : String :=
  "al:" ++ candidateMask s ++ ":" ++ toString s.spent ++ ":" ++ s.verdict.tag

/-- ⚑ **Ids separate states.**  Two declared states never share an id, so the
transition table's string references are unambiguous. -/
theorem state_ids_are_distinct :
    (parametricStates.map stateId).eraseDups.length = parametricStates.length := by
  native_decide

/-- What a client may render as "the run is over and it was right". -/
def solvedB (s : State) : Bool := decide (s.verdict = Verdict.identified)

/-- And "the run is over and it was wrong".  Unlike a descent, a live run here is
never doomed — naming a survivor can always win — so this is terminal loss and
`certifiableB` is the predicate that carries the skill story. -/
def doomedB (s : State) : Bool := decide (s.verdict = Verdict.mistaken)

/-! ## The emitted shape

Stated so the descriptor's size is a number a reader has before they open the
file, and so a change to the manual or the budget shows up as a broken pin rather
than a quietly larger download. -/

theorem parametric_shape_is_measured :
    parametricStates.length = 1197 ∧ allActions.length = 24 ∧
      parametricRowCount = 28728 := by
  refine ⟨by native_decide, by decide, by native_decide⟩

/-! ## Config, judge and receipt

The judged surface is exactly `DeckDescent`'s: a `Config` whose instance field is
pinned to the precommitted run seed by a proof obligation, a `terminalOutput`
that fails closed against the mission's own acceptance predicate, and a `judge`
that binds the transcript into the receipt. -/

structure Config where
  hidden : Rule
  mission : MissionSpec
  reward : Contribution
  reward_accepted : mission.acceptsContribution reward = true
  /-- ⚑ The rule a run is judged against is the one the precommitted seed draws.
  A host cannot pick the law after reading the transcript. -/
  hidden_eq : hidden = ruleFromRunSeed mission.runSeed

/-- Fail closed: a terminal state pays only if the run NAMED THE RULE and the
mission itself accepts the contribution.  A mistaken naming is a completed run
and an unpaid one. -/
def terminalOutput (cfg : Config) (s : State) : Option (Contribution × ArtifactRef) :=
  if s.verdict = Verdict.identified then
    if cfg.mission.acceptsContribution cfg.reward then
      some (cfg.reward, cfg.mission.artifact)
    else none
  else none

theorem terminalOutput_none_unless_identified (cfg : Config) (s : State)
    (h : s.verdict ≠ Verdict.identified) : terminalOutput cfg s = none := by
  simp [terminalOutput, h]

/-- ⚑ A wrong naming is never paid.  Stated separately from the theorem above
because "the run ended" and "the run won" are the two things an induction game
must not conflate. -/
theorem a_mistaken_run_is_not_paid (cfg : Config) (s : State)
    (h : s.verdict = Verdict.mistaken) : terminalOutput cfg s = none := by
  refine terminalOutput_none_unless_identified cfg s ?_
  rw [h]
  simp

theorem terminalOutput_is_mission_accepted (cfg : Config) (s : State)
    {out : Contribution × ArtifactRef} (h : terminalOutput cfg s = some out) :
    cfg.mission.acceptsContribution out.1 = true := by
  simp only [terminalOutput] at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h
      subst out
      assumption
    · contradiction
  · contradiction

theorem terminalOutput_names_exact_artifact (cfg : Config) (s : State)
    {out : Contribution × ArtifactRef} (h : terminalOutput cfg s = some out) :
    out.2 = cfg.mission.artifact := by
  simp only [terminalOutput] at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h
      subst out
      rfl
    · contradiction
  · contradiction

theorem terminalOutput_canonical (cfg : Config) (s : State)
    {contribution : Contribution} {artifact : ArtifactRef}
    (h : terminalOutput cfg s = some (contribution, artifact)) :
    terminalOutput cfg s = some (contribution, cfg.mission.artifact) := by
  have hart := terminalOutput_names_exact_artifact cfg s h
  change artifact = cfg.mission.artifact at hart
  rw [hart] at h
  exact h

def step (cfg : Config) (s : State) (a : Action) : Option State := stepR cfg.hidden s a

def replay (cfg : Config) : State → List Action → Option State := replayR cfg.hidden

theorem step_eq_stepR (cfg : Config) (s : State) (a : Action) :
    step cfg s a = stepR cfg.hidden s a := rfl

theorem replay_eq_replayR (cfg : Config) (s : State) (acts : List Action) :
    replay cfg s acts = replayR cfg.hidden s acts := rfl

theorem judged_rule_is_the_drawn_rule (cfg : Config) :
    cfg.hidden = ruleFromRunSeed cfg.mission.runSeed := cfg.hidden_eq

def byte (n : Nat) : Fin 256 := ⟨n % 256, Nat.mod_lt _ (by omega)⟩

def chargeIndex (c : Charge) : Nat := allCharges.findIdx (fun x => x == c)

def ruleIndex (r : Rule) : Nat := manual.findIdx (fun x => x == r)

/-- The transcript alphabet.  Charges take 0–7 and namings 8–23, so a receipt
records WHICH rule a run committed to and not merely that it committed. -/
def actionCode : Action → Nat
  | .probe c => chargeIndex c
  | .declare r => 8 + ruleIndex r

theorem action_codes_are_distinct :
    (allActions.map actionCode).eraseDups.length = allActions.length := by
  native_decide

def actionAt (actions : List Action) (i : Nat) : Nat :=
  match actions[i]? with
  | some a => actionCode a
  | none => 255

def transcriptDigest (actions : List Action) : Digest32 where
  bytes := List.ofFn (fun i : Fin 32 =>
    if i.val = 0 then byte actions.length else byte (actionAt actions (i.val - 1)))
  length_eq := by simp

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

theorem judge_some_sound (cfg : Config) (before : WorldState) (ctx : JudgeContext)
    (actions : List Action) {run : JudgedRun}
    (h : judge cfg before ctx actions = some run) :
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

theorem judge_receipt_binds_transcript (cfg : Config) (before : WorldState)
    (ctx : JudgeContext) (actions : List Action) {run : JudgedRun}
    (h : judge cfg before ctx actions = some run) :
    run.receipt.transcriptDigest = transcriptDigest actions :=
  (judge_some_sound cfg before ctx actions h).2.2.2.2

/-- ⚑ **A judged run named the rule.**  There is no rewarded transcript whose
final state is still probing, and none whose naming was wrong. -/
theorem judged_run_identified (cfg : Config) (before : WorldState)
    (ctx : JudgeContext) (actions : List Action) {run : JudgedRun}
    (h : judge cfg before ctx actions = some run) :
    run.finalState.verdict = Verdict.identified := by
  have hsound := judge_some_sound cfg before ctx actions h
  by_cases hv : run.finalState.verdict = Verdict.identified
  · exact hv
  · have hterm := hsound.2.1
    rw [terminalOutput_none_unless_identified cfg _ hv] at hterm
    exact absurd hterm (by simp)

/-- ⚑ **And it named the rule the seed drew.**  Identification is scored against
`cfg.hidden`, which `hidden_eq` pins to the precommitted run seed, so a receipt
cannot be produced by naming a rule the mechanism did not obey. -/
theorem judged_run_named_the_drawn_rule (cfg : Config) (before : WorldState)
    (ctx : JudgeContext) (actions : List Action) {run : JudgedRun}
    (h : judge cfg before ctx actions = some run) :
    run.finalState.candidates = [ruleFromRunSeed cfg.mission.runSeed] := by
  have hid := judged_run_identified cfg before ctx actions h
  have hsound := judge_some_sound cfg before ctx actions h
  have hrep := hsound.1
  rw [replay_eq_replayR] at hrep
  have hsingle := replay_identified_is_the_singleton cfg.hidden actions initialState
    run.finalState rfl hrep hid
  rw [hsingle, cfg.hidden_eq]

theorem judged_run_within_budget (cfg : Config) (before : WorldState)
    (ctx : JudgeContext) (actions : List Action) {run : JudgedRun}
    (h : judge cfg before ctx actions = some run) : actions.length ≤ ACTION_LIMIT := by
  have hsound := judge_some_sound cfg before ctx actions h
  rw [replay_eq_replayR] at hsound
  exact accepted_transcript_within_budget cfg.hidden actions run.finalState hsound.1

/-! ## Pins -/

#assert_axioms allMetals_complete
#assert_axioms allSeats_complete
#assert_axioms allThresholds_complete
#assert_axioms allCharges_complete
#assert_axioms Charge.count_le_three
#assert_axioms Charge.counts_sum
#assert_axioms alternating_is_the_complement_of_hasRun
#assert_axioms manual_complete
#assert_axioms every_pair_is_separated
#assert_axioms separated_of_mem
#assert_axioms manual_has_no_synonyms
#assert_axioms the_cut_family_would_have_been_a_synonym
#assert_axioms draw_below_sixteen_never_rejects
#assert_axioms allActions_complete
#assert_axioms truth_survives
#assert_axioms replay_keeps_the_truth
#assert_axioms the_truth_starts_in_the_manual
#assert_axioms certainty_cannot_be_mistaken
#assert_axioms a_declaration_is_scored_on_the_truth
#assert_axioms step_some_open
#assert_axioms step_some_probing
#assert_axioms step_spends_exactly_one
#assert_axioms a_probe_leaves_the_run_live
#assert_axioms a_declaration_ends_the_run
#assert_axioms candidates_never_grow
#assert_axioms not_open_refuses
#assert_axioms a_finished_run_refuses_everything
#assert_axioms an_empty_budget_refuses_a_probe
#assert_axioms an_answered_charge_is_refused
#assert_axioms a_fed_charge_never_splits_again
#assert_axioms a_refuted_rule_cannot_be_named
#assert_axioms replayR_append
#assert_axioms refused_prefix_refuses_replay
#assert_axioms replayR_spends
#assert_axioms a_finished_run_replays_nothing
#assert_axioms step_clock_bound
#assert_axioms replay_clock_bounded
#assert_axioms accepted_transcript_within_budget
#assert_axioms stepR_eq_stepWith
#assert_axioms step_is_one_of_the_two_branches
#assert_axioms branches_agree_on_refusal
#assert_axioms forced_answer_is_the_truth
#assert_axioms advance_row_is_the_real_step
#assert_axioms refuse_row_is_a_real_refusal
#assert_axioms certain_declaration_is_an_advance
#assert_axioms charge_tags_are_distinct
#assert_axioms terminalOutput_none_unless_identified
#assert_axioms a_mistaken_run_is_not_paid
#assert_axioms terminalOutput_is_mission_accepted
#assert_axioms terminalOutput_names_exact_artifact
#assert_axioms terminalOutput_canonical
#assert_axioms step_eq_stepR
#assert_axioms replay_eq_replayR
#assert_axioms judged_rule_is_the_drawn_rule
#assert_axioms judge_some_sound
#assert_axioms judge_receipt_binds_transcript
#assert_axioms judged_run_identified
#assert_axioms identified_state_is_the_singleton
#assert_axioms replay_identified_is_the_singleton
#assert_axioms judged_run_named_the_drawn_rule
#assert_axioms judged_run_within_budget

#assert_compiled manual_signatures_are_distinct
#assert_compiled repeated_manual_is_caught
#assert_compiled four_charges_are_enough
#assert_compiled three_charges_are_not
#assert_compiled an_even_split_is_not_a_good_one
#assert_compiled parametric_layers_are_the_clock
#assert_compiled parametric_closure_is_closed
#assert_compiled parametric_states_nodup
#assert_compiled initial_state_is_declared
#assert_compiled no_declared_state_is_empty
#assert_compiled resolve_rows_name_two_states
#assert_compiled the_table_consults_the_instance
#assert_compiled every_open_probe_resolves
#assert_compiled every_declared_reason_is_reachable
#assert_compiled every_rule_is_identifiable
#assert_compiled the_run_can_be_lost
#assert_compiled the_skill_line_is_real
#assert_compiled rule_tags_are_distinct
#assert_compiled action_tags_are_distinct
#assert_compiled state_ids_are_distinct
#assert_compiled parametric_shape_is_measured
#assert_compiled action_codes_are_distinct

end Dregg2.Games.PathOfAngels.ArtificerLogic
