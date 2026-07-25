/-
# Dregg2.Games.Dungeon — THE DESCENT, reimagined natively in Lean.

This is NOT a port of the Rust dungeon. It is a fresh authoring of the descent as the
dreggic object it wants to be:

> **a turn = the exercise of an attenuable proof-carrying token over OWNED state,
> leaving a receipt.**

## The reimagined design, stated as law (each law is a THEOREM below, not prose)

1. **Relics are owned objects with provenance, not counters.** The state carries a
   CUSTODY code per relic (`deep at floor d` → `carried` → `banked`) and custody is a
   MONOTONE RATCHET (`custody_ratchet`): a relic moves down its provenance pipeline and
   never back. A banked relic's history is exactly the receipted turn chain back to the
   world's mint. The counters the deployed teeth read (`pack`, `bank`, `hoard_d`) are
   PROJECTIONS of custody (they are *definitions* here), not independent facts.

2. **Descent attenuates capability.** Carrying rights shrink with depth: every reachable
   state satisfies `pack + depth + harm ≤ CAP` (`capacity_attenuates`). Descending with a
   full pack is not "discouraged" — the deeper turn is *unprovable*. Attenuation as
   arithmetic, not flavor. Corollary `hoard_never_leaves_whole`: EVERY relic that leaves
   the dungeon was looted at `depth ≥ 1`, and every point of `harm` was bought there too,
   so `pack + bank + harm ≤ CAP − 1` on every reachable state — one carry slot is spoken
   for however the run is played, and each broken grip eats another. Hence
   `no_run_banks_everything`: no receipt chain whatsoever banks all `RELICS` relics.

   ⚑ This clause REPLACES the retired `crowned_bank_le_four` (`bank ≤ CAP − FLOORS − harm`
   for a crowned run). That bound was true, but true only BECAUSE THERE WAS NO WAY BACK
   UP: banking the prize forced `depth = FLOORS` in the terminal state. It was an artifact
   of the one-way descent, not a design intent, and `ascend` falsifies it. What replaces
   it never mentions one-way descent at all — which is why it survives.

3. **The light is the clock, and the climb is part of the bill.** Every verb has a posted
   price in `spent`; `spent` strictly increases and is capped at `BREATH`. `flee` demands
   the SURFACE (`depth = 0`) and `ascend` costs one breath per floor, so the clock a run
   really plays against is the TOLL, `spent + depth`: breath burned plus breath the climb
   home will cost. `toll_ratchets` — no verb rewinds it; the climb repays the descent at
   par, never at a discount. `doomed_never_banks` — from a living state with
   `BREATH ≤ toll`, NO continuation banks. That is permadeath as a reachable event
   (`doomed_every_day`, driven on all 16 maps), not merely `the_light_dies` at the end of
   an unlosable run.

3b. **The guardian does not kill you — it BREAKS YOUR GRIP.** There are no hit points to
   take, so the descent's HP-analogue is CAPACITY. `harm` is a run-long ratchet in
   `0..HARMCAP` and the capacity law is `pack + depth + harm ≤ CAP`: every harm taken is
   one relic that does not leave the dungeon. Two verbs strike the standing guardian:
   `smite` (the *press*) costs 2 breath and no harm, `lunge` costs 1 breath and +1 harm.
   Because capacity already attenuates with depth, the SAME posted price is cheap at
   depth 1 (7 slots) and ruinous at depth 4 (4 slots — exactly three keys plus the
   prize), so a `guardHp = 2` floor is a mixable decision rather than a quotient. Unlike
   `wounds`, `harm` is NOT reset by `delve` (`harm_ratchets`); and taking any harm at all
   forfeits carry slots that never come back — `banked_bank_pays_for_harm`:
   `bank + harm ≤ CAP − 1`, so each point of harm is EXACTLY one relic that did not leave
   the dungeon, whatever route the run took to the surface. (The old, stronger-sounding
   `crowned_full_bank_harmless` retired with `crowned_bank_le_four`: it was a corollary of
   the same one-way accident.)

4. **Keys are capabilities.** The way to floor `w` opens only by EXERCISING the carried
   key-relic for `w` (`keyless_unlock_impossible`): a key is an owned, un-dupable relic
   whose own provenance chain proves where it was won.

5. **Banking is terminal, and it happens at the mouth.** `flee` banks the pack and writes
   the run's fate exactly once; a banked run is a frozen tomb (`banked_run_frozen`)
   standing at the surface (`banked_at_the_surface`). You climb out; you do not teleport
   out. `ascend` is the climb: `depth ≥ 1`, one breath, `wounds` reset — and `harm`
   emphatically NOT reset, so the grip the guardians broke is not laundered by a walk
   upstairs (`harm_ratchets` still holds of it). A way you have passed stays open
   (`ways_behind_stay_open`), so nothing but the light can keep you down.

6. **The world is minted once**; every relic's provenance replays to the mint
   (`genesisState` is the only entry; `Reachable` quantifies over receipt chains).

The deployed teeth for this design are the `CellProgram` value in
`Dregg2.Games.DungeonProgram` (emitted to `dungeon-on-dregg/program/dungeon_program.json`
and loaded by `dungeon_on_dregg::descent`); the refinement/attack theorems live there.
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Count
import Dregg2.Tactics

namespace Dregg2.Games.Dungeon

/-! ## 1. The world constants (the balance is part of the design). -/

/-- Number of floors below the surface. Depth `0` is the surface. -/
abbrev FLOORS : Nat := 4

/-- Number of relics minted into the world; conservation is over this total. -/
abbrev RELICS : Nat := 8

/-- The light: total exertion a run may spend. A perfect crowned run costs 24–30 of it,
and — since `flee` now demands the surface and the climb home is priced one breath per
floor — the light running out while you are still below IS death (`doomed_never_banks`).
A full clear is impossible (see `no_run_banks_everything` — by capacity, not by breath). -/
abbrev BREATH : Nat := 30

/-- Carrying rights at the surface; the capacity law is `pack + depth + harm ≤ CAP`. -/
abbrev CAP : Nat := 8

/-- The most harm a run can take and still be running: `harm` is a `0..2` ratchet, and
each point of it is a permanently forfeited carry slot. Three broken grips and there is
nothing left to attenuate — the deployed `harm` register carries exactly this range. -/
abbrev HARMCAP : Nat := 2

/-! ### Custody codes — the provenance ratchet's ordered alphabet.

`1..FLOORS` = lying in that floor's hoard; `CARRIED = 8` = in the pack; `BANKED = 9`.
The order `floor < CARRIED < BANKED` IS the provenance direction; monotonicity of the
code is the no-return ratchet. -/

abbrev CARRIED : Nat := 8
abbrev BANKED : Nat := 9

/-- The key-relic that opens way `w` (ways 2..FLOORS ⇒ relics 1..3). -/
def keyFor (w : Nat) : Nat := w - 1

/-! ## 1b. THE DAY'S WORLD — the map is a PARAMETER, not a compile-time constant.

The descent is a DAILY: the committed drand day-seed must move the *map*, not only the
loot-note provenance. So the two facts that used to be hard-wired constants — where each
relic is minted and how tough each floor's guardian is — become a `World`, and every
rule, invariant and law below is stated over an ARBITRARY well-formed world (`WorldParam`).
The day's world is DRAWN from the committed seed (`drawWorld`, §9) and the deployed teeth
are emitted once per family member (`Dregg2.Games.DungeonProgram`). -/

/-- The day's map. `homes i` = relic `i`'s minted floor; `ghp d` = floor `d`'s guardian
vitality (index 0 is the surface, which has no guardian). -/
structure World where
  /-- Per-relic minted floor, length `RELICS`. -/
  homes : List Nat
  /-- Per-floor guardian vitality, length `FLOORS + 1` (index 0 = the surface). -/
  ghp   : List Nat
deriving Repr, DecidableEq

/-- **The structural law of a legal map.** Decidable, so every drawn world is CHECKED,
never hoped. The three clauses that keep the dungeon playable:

* `homes 0 = FLOORS` — relic 0 is THE PRIZE and it lies at the bottom (so the crowned
  run must stand on the deepest floor to take it — see
  `prize_leaves_home_only_at_the_bottom`, the local fact `crowned_bank_le_four` used to
  cash in globally);
* `homes (keyFor w) < w` for every keyed way — **no key behind the door it opens**. The
  key to way `w` is minted strictly above floor `w`, so by induction on `w` every way is
  openable from the surface;
* every guardian is real (`1 ≤ ghp d`) and slayable in at most two blows (`ghp d ≤ 2`),
  which is what keeps `wounds` inside its deployed register range.

Completability under BREATH and CAP is *not* structural — it is DRIVEN, per drawn world,
by replaying an actual winning line (`crownedWins`, §8). -/
def WorldWF (W : World) : Bool :=
  (W.homes.length == RELICS) &&
  (W.ghp.length == FLOORS + 1) &&
  (W.ghp.getD 0 1 == 0) &&
  W.homes.all (fun c => 1 ≤ c && c ≤ FLOORS) &&
  W.ghp.all (fun h => h ≤ 2) &&
  (W.homes.getD 0 0 == FLOORS) &&
  (List.range' 2 (FLOORS - 1)).all (fun w => W.homes.getD (keyFor w) 0 < w) &&
  (List.range' 1 FLOORS).all (fun d => 1 ≤ W.ghp.getD d 0)

/-- **The world under which a descent is played**, carried as a parameter of every rule
and every law below. It carries its own well-formedness proof, so no theorem downstream
has to re-plumb a hypothesis: possessing a `WorldParam` IS possessing a legal map. -/
class WorldParam where
  world : World
  wf    : WorldWF world = true

section
variable [WorldParam]

/-- The day's map. -/
abbrev theWorld : World := WorldParam.world

/-- Per-floor guardian vitality (wounds required to slay). The surface has no guardian. -/
def guardHp (d : Nat) : Nat := theWorld.ghp.getD d 0

/-- Where each relic is minted. Relic 0 is THE PRIZE (floor `FLOORS`); relics 1–3 are
the KEYS to ways 2–4, each minted strictly above the way it opens; relics 4–7 are
treasures. THE DAY'S DRAW decides the exact floors. -/
def homeFloors : List Nat := theWorld.homes

/-- Relic `i`'s minted floor. -/
def homeOf (i : Nat) : Nat := homeFloors.getD i 0

/-! ### Reading the world law back out (used by `inv_genesis` and the program weld). -/

theorem wf_homes_length : homeFloors.length = RELICS := by
  have h := WorldParam.wf (self := ‹WorldParam›)
  simp only [WorldWF, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.1.1.1

theorem wf_ghp_length : theWorld.ghp.length = FLOORS + 1 := by
  have h := WorldParam.wf (self := ‹WorldParam›)
  simp only [WorldWF, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.1.1.2

theorem wf_home_floor {c : Nat} (hc : c ∈ homeFloors) : 1 ≤ c ∧ c ≤ FLOORS := by
  have h := WorldParam.wf (self := ‹WorldParam›)
  simp only [WorldWF, Bool.and_eq_true, beq_iff_eq] at h
  have := (List.all_eq_true.mp h.1.1.1.1.2) c hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

theorem wf_guardHp_le (d : Nat) : guardHp d ≤ 2 := by
  have h := WorldParam.wf (self := ‹WorldParam›)
  simp only [WorldWF, Bool.and_eq_true, beq_iff_eq] at h
  show theWorld.ghp.getD d 0 ≤ 2
  by_cases hd : d < theWorld.ghp.length
  · rw [← List.getElem_eq_getD (l := theWorld.ghp) (i := d) (h := hd) 0]
    simpa using (List.all_eq_true.mp h.1.1.1.2) _ (List.getElem_mem hd)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    exact Nat.zero_le _

theorem wf_prize_home : homeOf 0 = FLOORS := by
  have h := WorldParam.wf (self := ‹WorldParam›)
  simp only [WorldWF, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.2

/-- **No key behind the door it opens**: the key to way `w` is minted strictly above
floor `w`. -/
theorem wf_key_above_its_way {w : Nat} (hlo : 2 ≤ w) (hhi : w ≤ FLOORS) :
    homeOf (keyFor w) < w := by
  have h := WorldParam.wf (self := ‹WorldParam›)
  simp only [WorldWF, Bool.and_eq_true, beq_iff_eq] at h
  have hmem : w ∈ List.range' 2 (FLOORS - 1) := by
    have : w = 2 ∨ w = 3 ∨ w = 4 := by
      have : w ≤ 4 := hhi; omega
    rcases this with rfl | rfl | rfl <;> decide
  have := (List.all_eq_true.mp h.1.2) w hmem
  simpa only [homeOf, homeFloors, decide_eq_true_eq] using this

theorem wf_guardian_stands {d : Nat} (hlo : 1 ≤ d) (hhi : d ≤ FLOORS) : 1 ≤ guardHp d := by
  have h := WorldParam.wf (self := ‹WorldParam›)
  simp only [WorldWF, Bool.and_eq_true, beq_iff_eq] at h
  have hmem : d ∈ List.range' 1 FLOORS := by
    have : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by
      have : d ≤ 4 := hhi; omega
    rcases this with rfl | rfl | rfl | rfl <;> decide
  have := (List.all_eq_true.mp h.2) d hmem
  simpa only [guardHp, decide_eq_true_eq] using this

/-! ## 2. The model state — relics first; counters are projections. -/

/-- The descent state. `ways = [way2, way3, way4]` (way 1 is always open);
`custody` is the per-relic custody code list. -/
structure DState where
  depth   : Nat
  spent   : Nat
  wounds  : Nat
  /-- The RUN-LONG grip damage the guardians have done, `0..HARMCAP`. Unlike `wounds`
  (which is the standing guardian's tally and resets on `delve`), `harm` never resets and
  never decreases: it is subtracted from carrying rights for the rest of the run. -/
  harm    : Nat
  fate    : Nat          -- 0 = alive, 1 = banked
  ways    : List Nat     -- 0/1 each
  custody : List Nat
deriving Repr, DecidableEq

/-- The minted world: surface, full light, unbroken grip, ways shut, every relic at its
home floor. -/
def genesisState : DState :=
  { depth := 0, spent := 0, wounds := 0, harm := 0, fate := 0
    ways := [0, 0, 0], custody := homeFloors }

/-- Pack size — a PROJECTION of custody (design law 1). -/
def pack (s : DState) : Nat := s.custody.countP (· == CARRIED)

/-- Banked count — a projection of custody. -/
def bank (s : DState) : Nat := s.custody.countP (· == BANKED)

/-- Hoard size at floor `d` — a projection of custody. -/
def hoardAt (s : DState) (d : Nat) : Nat := s.custody.countP (· == d)

/-- Is way `d` open? Way 1 (the first stair) is always open. -/
def wayOpen (s : DState) (d : Nat) : Bool :=
  if d ≤ 1 then true
  else match s.ways[d - 2]? with
       | some v => v == 1
       | none   => false

/-! ## 3. The verbs. Every verb's price is posted; every check IS the rule. -/

inductive Move where
  | delve                  -- descend one floor (the way must be open; wounds reset)
  | ascend                 -- climb one floor toward the surface (wounds reset; harm does NOT)
  | unlock (w : Nat)       -- exercise the carried key-relic to open way w
  | smite                  -- THE PRESS: wound the guardian (price 2 — it strikes back)
  | lunge                  -- wound the guardian for 1 breath and +1 HARM (a carry slot)
  | loot (r : Nat)         -- take relic r from the standing floor's hoard (guardian slain)
  | flee                   -- bank the pack AT THE SURFACE; the run ends
deriving Repr, DecidableEq

/-- The posted price of a verb in breath. `smite` alone costs two: `lunge` buys that
second breath back and pays for it in `harm` instead. -/
def price : Move → Nat
  | .smite => 2
  | _      => 1

/-- One receipted turn of the descent: `step s m = some s'` iff `m` is LEGAL at `s`.
This function IS the rulebook; everything else is proved about it. -/
def step (s : DState) : Move → Option DState
  | .delve =>
      if s.fate = 0 ∧ s.spent + 1 ≤ BREATH ∧ s.depth < FLOORS
          ∧ wayOpen s (s.depth + 1) = true
          ∧ pack s + (s.depth + 1) + s.harm ≤ CAP then  -- attenuated carrying rights
        -- `wounds` resets (a fresh guardian stands below); `harm` does NOT — it is a
        -- run-long ratchet, and `{s with …}` carries it forward by construction.
        some { s with depth := s.depth + 1, wounds := 0, spent := s.spent + 1 }
      else none
  | .ascend =>
      -- THE ONE-WAY DOOR, RUNNING THE OTHER WAY. The climb is unconditional except for
      -- the light: no way to re-open, no capacity to re-earn (going up only ever loosens
      -- `pack + depth + harm ≤ CAP`), no guardian to re-fell. What it costs is a breath
      -- PER FLOOR, and that is exactly why `spent + depth` is a ratchet no verb rewinds
      -- (`toll_ratchets`) — descending buys a debt the climb must repay at par.
      -- `wounds` resets (the guardian above stands again); `harm` does NOT.
      if s.fate = 0 ∧ s.spent + 1 ≤ BREATH ∧ 1 ≤ s.depth then
        some { s with depth := s.depth - 1, wounds := 0, spent := s.spent + 1 }
      else none
  | .unlock w =>
      if s.fate = 0 ∧ s.spent + 1 ≤ BREATH ∧ 2 ≤ w ∧ w ≤ FLOORS
          ∧ s.ways[w - 2]? = some 0
          ∧ s.custody[keyFor w]? = some CARRIED then
        some { s with ways := s.ways.set (w - 2) 1, spent := s.spent + 1 }
      else none
  | .smite =>
      if s.fate = 0 ∧ s.spent + 2 ≤ BREATH ∧ 1 ≤ s.depth
          ∧ s.wounds + 1 ≤ guardHp s.depth then
        some { s with wounds := s.wounds + 1, spent := s.spent + 2 }
      else none
  | .lunge =>
      -- The same blow for HALF the breath, paid in grip: `harm + 1`. The capacity
      -- clause is the whole decision — at depth 1 it costs a slot you were never going
      -- to fill, at depth 4 it costs the prize.
      if s.fate = 0 ∧ s.spent + 1 ≤ BREATH ∧ 1 ≤ s.depth
          ∧ s.wounds + 1 ≤ guardHp s.depth
          ∧ s.harm + 1 ≤ HARMCAP                       -- the ratchet's ceiling
          ∧ pack s + s.depth + (s.harm + 1) ≤ CAP then -- attenuated carrying rights
        some { s with wounds := s.wounds + 1, spent := s.spent + 1, harm := s.harm + 1 }
      else none
  | .loot r =>
      if s.fate = 0 ∧ s.spent + 1 ≤ BREATH ∧ 1 ≤ s.depth
          ∧ s.custody[r]? = some s.depth              -- the relic lies HERE
          ∧ s.wounds = guardHp s.depth                -- the guardian is slain
          ∧ pack s + 1 + s.depth + s.harm ≤ CAP then  -- attenuated carrying rights
        some { s with custody := s.custody.set r CARRIED, spent := s.spent + 1 }
      else none
  | .flee =>
      -- ⚑ YOU CLIMB OUT; YOU DO NOT TELEPORT OUT. Banking demands the surface. This one
      -- clause is what turns the whole descent into a wager: every floor you take is a
      -- breath you must still have when you want to leave.
      if s.fate = 0 ∧ s.spent + 1 ≤ BREATH ∧ s.depth = 0 then
        some { s with fate := 1, spent := s.spent + 1, custody := s.custody.map (fun c => if c = CARRIED then BANKED else c) }
      else none

/-! ## 4. Runs and reachability. A run IS its receipt chain. -/

/-- Replay a move script from the mint; `none` as soon as any move is illegal —
there is no partially-legal run. -/
def replay (ms : List Move) : Option DState :=
  ms.foldl (fun acc m => acc.bind (fun s => step s m)) (some genesisState)

/-- Reachable = some receipt chain replays to it from the mint. -/
def Reachable (s : DState) : Prop := ∃ ms, replay ms = some s

/-- A refused prefix refuses the whole run (folding from `none` stays `none`). -/
private theorem foldl_none (ms : List Move) :
    ms.foldl (fun acc m => acc.bind (fun t => step t m)) none = none := by
  induction ms with
  | nil => rfl
  | cons m rest ih => exact ih

/-! ## 5. Counting helpers (custody projections under `set` / the flee map). -/

private theorem countP_set_bump {l : List Nat} {i a v : Nat} (p : Nat → Bool)
    (hget : l[i]? = some a) (hpa : p a = false) (hpv : p v = true) :
    (l.set i v).countP p = l.countP p + 1 := by
  induction l generalizing i with
  | nil => simp at hget
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      simp [List.set, List.countP_cons, hpa, hpv]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hget
      simp only [List.set, List.countP_cons, ih hget]
      omega

private theorem countP_set_same {l : List Nat} {i a v : Nat} (p : Nat → Bool)
    (hget : l[i]? = some a) (heq : p a = p v) :
    (l.set i v).countP p = l.countP p := by
  induction l generalizing i with
  | nil => simp at hget
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget
      simp only [List.set, List.countP_cons, heq]
    | succ j =>
      simp only [List.getElem?_cons_succ] at hget
      simp only [List.set, List.countP_cons, ih hget]

private def fleeMap (c : Nat) : Nat := if c = CARRIED then BANKED else c

private theorem countP_fleeMap_carried (l : List Nat) :
    (l.map fleeMap).countP (· == CARRIED) = 0 := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.map_cons, List.countP_cons, ih]
    by_cases h : hd = CARRIED
    · have h1 : fleeMap hd = BANKED := by simp [fleeMap, h]
      rw [h1]; rfl
    · have h1 : fleeMap hd = hd := by simp [fleeMap, h]
      rw [h1]
      have h2 : (hd == CARRIED) = false := beq_eq_false_iff_ne.mpr h
      simp [h2]

private theorem countP_fleeMap_banked (l : List Nat) :
    (l.map fleeMap).countP (· == BANKED)
      = l.countP (· == CARRIED) + l.countP (· == BANKED) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.map_cons, List.countP_cons, List.countP_cons, List.countP_cons, ih]
    by_cases h : hd = CARRIED
    · have h1 : fleeMap hd = BANKED := by simp [fleeMap, h]
      have h2 : (hd == BANKED) = false := by
        subst h; decide
      rw [h1, h2]
      have h3 : (hd == CARRIED) = true := beq_iff_eq.mpr h
      rw [h3]
      simp
      omega
    · have h1 : fleeMap hd = hd := by simp [fleeMap, h]
      have h3 : (hd == CARRIED) = false := beq_eq_false_iff_ne.mpr h
      rw [h1, h3]
      by_cases h9 : hd = BANKED
      · have h4 : (hd == BANKED) = true := beq_iff_eq.mpr h9
        rw [h4]; simp; omega
      · have h4 : (hd == BANKED) = false := beq_eq_false_iff_ne.mpr h9
        rw [h4]; simp

private theorem mem_of_mem_set {l : List Nat} {i v c : Nat}
    (hc : c ∈ l.set i v) : c ∈ l ∨ c = v := by
  induction l generalizing i with
  | nil => simp [List.set] at hc
  | cons hd tl ih =>
    cases i with
    | zero => simp only [List.set, List.mem_cons] at hc ⊢; tauto
    | succ j =>
      simp only [List.set, List.mem_cons] at hc ⊢
      rcases hc with h | h
      · tauto
      · rcases ih h with h' | h' <;> tauto

private theorem countP_pos_of_mem {l : List Nat} {v : Nat} (hmem : v ∈ l) :
    1 ≤ l.countP (· == v) := by
  induction l with
  | nil => simp at hmem
  | cons hd tl ih =>
    rw [List.countP_cons]
    rcases List.mem_cons.mp hmem with h | h
    · have h1 : (hd == v) = true := beq_iff_eq.mpr h.symm
      rw [h1]; simp
    · have := ih h; omega

private theorem countP_pos_of_getElem {l : List Nat} {i v : Nat}
    (hget : l[i]? = some v) : 1 ≤ l.countP (· == v) :=
  countP_pos_of_mem (List.mem_of_getElem? hget)

/-- Opening a way never shuts one: `unlock` only ever writes a `1`. -/
private theorem wayOpen_set_true {s : DState} {w d : Nat} (h : wayOpen s d = true) :
    wayOpen { s with ways := s.ways.set (w - 2) 1 } d = true := by
  by_cases hd : d ≤ 1
  · simp only [wayOpen, if_pos hd]
  · simp only [wayOpen, if_neg hd] at h ⊢
    cases hg : s.ways[d - 2]? with
    | none => rw [hg] at h; exact absurd h (by simp)
    | some v =>
      rw [hg] at h
      have hv : v = 1 := by simpa using h
      have hlt : d - 2 < s.ways.length := by
        by_contra hge
        rw [List.getElem?_eq_none (by omega)] at hg
        exact absurd hg (by simp)
      by_cases hw : w - 2 = d - 2
      · rw [hw, List.getElem?_set_self hlt]; rfl
      · rw [List.getElem?_set_ne hw, hg, hv]; rfl

/-! ## 6. The inductive invariant — the design laws as one package. -/

/-- Custody well-formedness: exactly `RELICS` relics forever (no mint, no burn — the
no-dupe law is STRUCTURAL: a relic is one list entry), every code legal. -/
def CustodyWF (s : DState) : Prop :=
  s.custody.length = RELICS ∧
  ∀ c ∈ s.custody, (1 ≤ c ∧ c ≤ FLOORS) ∨ c = CARRIED ∨ c = BANKED

/-- **A way you have passed stays open.** No verb ever shuts a way, and you can only
have reached depth `d` by exercising the key to every way above it — so the climb home
never meets a locked door. This is the clause that makes `ascend` unconditional, and it
is what the deployed depth-rider's `wayTooth` cashes in on an ASCENDING turn (the
post-state depth is one you already stood on). -/
def WaysBehind (s : DState) : Prop := ∀ d, 2 ≤ d → d ≤ s.depth → wayOpen s d = true

def Inv (s : DState) : Prop :=
  CustodyWF s
    ∧ s.spent ≤ BREATH
    ∧ s.depth ≤ FLOORS
    ∧ s.fate ≤ 1
    ∧ s.ways.length = FLOORS - 1
    ∧ pack s + s.depth + s.harm ≤ CAP
    ∧ (s.fate = 0 → bank s = 0)
    -- ⚑ RESTATED FOR THE CLIMB: `flee` demands the surface, so a banked run is standing
    -- at the mouth. (It used to only need an emptied pack, because banking was a
    -- teleport.)
    ∧ (s.fate = 1 → pack s = 0 ∧ s.depth = 0)
    -- ⚑ THE REPLACEMENT FOR `crowned_bank_le_four`. Every relic that leaves the dungeon
    -- was looted at depth ≥ 1 under `pack + 1 + depth + harm ≤ CAP`, and every point of
    -- `harm` was bought at depth ≥ 1 too — so one carry slot is spoken for no matter how
    -- the run is played, and each broken grip eats another. Nothing about the ONE-WAY
    -- descent is needed to see it, which is exactly why this clause survives `ascend`
    -- and the old bound did not.
    ∧ pack s + bank s + s.harm ≤ CAP - 1
    -- ⚑ RESTATED FOR THE CLIMB: the surface has no guardian. (It used to say the surface
    -- held nothing at all — `pack = bank = 0` — which was true only because the only way
    -- to stand here was to have never left.)
    ∧ (s.depth = 0 → s.wounds = 0)
    ∧ WaysBehind s
    -- ⚑ RESTATED FOR THE CLIMB: THE PRIZE lies at the bottom or it is in your hands.
    -- (It used to say `custody 0 = FLOORS ∨ depth = FLOORS` — that you could not be
    -- holding the prize anywhere but standing on it. You can now: you carry it up.)
    ∧ (s.custody[0]? = some FLOORS ∨ s.custody[0]? = some CARRIED
        ∨ s.custody[0]? = some BANKED)
    ∧ s.harm ≤ HARMCAP

/-- No relic is minted already-carried or already-banked (every home is a real floor). -/
private theorem genesis_pack_zero : pack genesisState = 0 := by
  simp only [pack, genesisState, List.countP_eq_zero]
  intro c hc
  have hc' := wf_home_floor hc
  have hF : (FLOORS : Nat) = 4 := rfl
  have hC : (CARRIED : Nat) = 8 := rfl
  simp only [beq_iff_eq]
  omega

private theorem genesis_bank_zero : bank genesisState = 0 := by
  simp only [bank, genesisState, List.countP_eq_zero]
  intro c hc
  have hc' := wf_home_floor hc
  have hF : (FLOORS : Nat) = 4 := rfl
  have hB : (BANKED : Nat) = 9 := rfl
  simp only [beq_iff_eq]
  omega

private theorem genesis_prize : genesisState.custody[0]? = some FLOORS := by
  have h0 : (0 : Nat) < homeFloors.length := by rw [wf_homes_length]; decide
  show homeFloors[0]? = some FLOORS
  rw [List.getElem?_eq_getElem h0, List.getElem_eq_getD (0 : Nat)]
  exact congrArg some wf_prize_home

theorem inv_genesis : Inv genesisState := by
  refine ⟨⟨wf_homes_length, ?_⟩,
    (Nat.zero_le _), (Nat.zero_le _), (Nat.zero_le _), rfl, ?_, ?_, ?_, ?_, ?_, ?_,
    Or.inl genesis_prize, Nat.zero_le _⟩
  · intro c hc
    exact Or.inl (wf_home_floor hc)
  · show pack genesisState + 0 + 0 ≤ CAP
    rw [genesis_pack_zero]; decide
  · intro _; exact genesis_bank_zero
  · intro hf; exact absurd (show (0 : Nat) = 1 from hf) (by decide)
  · show pack genesisState + bank genesisState + 0 ≤ CAP - 1
    rw [genesis_pack_zero, genesis_bank_zero]; decide
  · intro _; rfl
  · intro d hlo hhi
    exact absurd (show d ≤ 0 from hhi) (by omega)

/-- **Invariant preservation** — every legal turn preserves the design laws. -/
theorem inv_step {s s' : DState} {m : Move} (hInv : Inv s) (h : step s m = some s') :
    Inv s' := by
  obtain ⟨⟨hlen, hcodes⟩, hspent, hdepth, hfate, hways, hcap, hb0, hb1, hcap1, hd0, hwb,
    hprize, hharm⟩ := hInv
  cases m with
  | delve =>
    simp only [step] at h
    split at h
    case isTrue hcond =>
      obtain ⟨h0, h1, h2, h3, h4⟩ := hcond
      cases h
      refine ⟨⟨hlen, hcodes⟩, ?_, ?_, ?_, hways, ?_, ?_, ?_, hcap1, ?_, ?_, ?_, hharm⟩
      · show s.spent + 1 ≤ BREATH; omega
      · show s.depth + 1 ≤ FLOORS; omega
      · exact hfate
      · exact h4
      · intro hf; exact hb0 hf
      · intro hf; exact absurd (show s.fate = 1 from hf) (by omega)
      · intro hd; exact absurd (show s.depth + 1 = 0 from hd) (by omega)
      · -- ⚑ THE WAY BEHIND YOU: every way at or above the new depth is open — the ones
        -- above by hypothesis, the one just taken by this delve's own guard.
        intro d hlo hhi
        have hhi' : d ≤ s.depth + 1 := hhi
        by_cases hd : d ≤ s.depth
        · exact hwb d hlo hd
        · have hdd : d = s.depth + 1 := by omega
          subst hdd
          exact h3
      · exact hprize
    case isFalse => exact absurd h (by simp)
  | ascend =>
    simp only [step] at h
    split at h
    case isTrue hcond =>
      obtain ⟨h0, h1, h2⟩ := hcond
      cases h
      refine ⟨⟨hlen, hcodes⟩, ?_, ?_, hfate, hways, ?_, ?_, ?_, hcap1, ?_, ?_, hprize,
        hharm⟩
      · show s.spent + 1 ≤ BREATH; omega
      · show s.depth - 1 ≤ FLOORS; omega
      · -- Climbing only ever LOOSENS the capacity law; that is why `ascend` needs no
        -- capacity guard of its own.
        show pack s + (s.depth - 1) + s.harm ≤ CAP; omega
      · intro hf; exact hb0 hf
      · intro hf; exact absurd (show s.fate = 1 from hf) (by omega)
      · intro _; rfl
      · intro d hlo hhi
        have hhi' : d ≤ s.depth - 1 := hhi
        exact hwb d hlo (by omega)
    case isFalse => exact absurd h (by simp)
  | unlock w =>
    simp only [step] at h
    split at h
    case isTrue hcond =>
      obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hcond
      cases h
      refine ⟨⟨hlen, hcodes⟩, ?_, hdepth, hfate, ?_, hcap, ?_, ?_, hcap1, hd0, ?_,
        hprize, hharm⟩
      · show s.spent + 1 ≤ BREATH; omega
      · show (s.ways.set (w - 2) 1).length = FLOORS - 1
        simpa using hways
      · intro hf; exact hb0 hf
      · intro hf; exact absurd (show s.fate = 1 from hf) (by omega)
      · intro d hlo hhi; exact wayOpen_set_true (hwb d hlo hhi)
    case isFalse => exact absurd h (by simp)
  | smite =>
    simp only [step] at h
    split at h
    case isTrue hcond =>
      obtain ⟨h0, h1, h2, h3⟩ := hcond
      cases h
      refine ⟨⟨hlen, hcodes⟩, ?_, hdepth, hfate, hways, hcap, ?_, ?_, hcap1, ?_, hwb,
        hprize, hharm⟩
      · show s.spent + 2 ≤ BREATH; omega
      · intro hf; exact hb0 hf
      · intro hf; exact absurd (show s.fate = 1 from hf) (by omega)
      · intro hdz; exact absurd (show s.depth = 0 from hdz) (by omega)
    case isFalse => exact absurd h (by simp)
  | lunge =>
    simp only [step] at h
    split at h
    case isTrue hcond =>
      obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hcond
      cases h
      refine ⟨⟨hlen, hcodes⟩, ?_, hdepth, hfate, hways, ?_, ?_, ?_, ?_, ?_, hwb, hprize,
        ?_⟩
      · show s.spent + 1 ≤ BREATH; omega
      · show pack s + s.depth + (s.harm + 1) ≤ CAP; exact h5
      · intro hf; exact hb0 hf
      · intro hf; exact absurd (show s.fate = 1 from hf) (by omega)
      · -- ⚑ THE GRIP IS BOUGHT AT DEPTH, so it is bought against a slot that was already
        -- spoken for: `1 ≤ depth` turns the capacity guard into `pack + harm' ≤ CAP - 1`.
        show pack s + bank s + (s.harm + 1) ≤ CAP - 1
        have hbz : bank s = 0 := hb0 h0
        have hCAP : (CAP : Nat) = 8 := rfl
        omega
      · intro hdz; exact absurd (show s.depth = 0 from hdz) (by omega)
      · show s.harm + 1 ≤ HARMCAP; exact h4
    case isFalse => exact absurd h (by simp)
  | loot r =>
    simp only [step] at h
    split at h
    case isTrue hcond =>
      obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hcond
      cases h
      have hd4 : s.depth ≤ 4 := hdepth
      have hdC : (s.depth == CARRIED) = false :=
        beq_eq_false_iff_ne.mpr (show s.depth ≠ 8 by omega)
      have hdB : (s.depth == BANKED) = false :=
        beq_eq_false_iff_ne.mpr (show s.depth ≠ 9 by omega)
      have hpackBump :
          (s.custody.set r CARRIED).countP (· == CARRIED)
            = s.custody.countP (· == CARRIED) + 1 :=
        countP_set_bump _ h3 hdC (by simp)
      have hbankSame :
          (s.custody.set r CARRIED).countP (· == BANKED)
            = s.custody.countP (· == BANKED) :=
        countP_set_same _ h3 (by simp [hdB])
      refine ⟨⟨?_, ?_⟩, ?_, hdepth, hfate, hways, ?_, ?_, ?_, ?_, ?_, hwb, ?_, hharm⟩
      · show (s.custody.set r CARRIED).length = RELICS
        simpa using hlen
      · intro c hc
        rcases mem_of_mem_set hc with hcl | hcv
        · exact hcodes c hcl
        · right; left; exact hcv
      · show s.spent + 1 ≤ BREATH; omega
      · show (s.custody.set r CARRIED).countP (· == CARRIED) + s.depth + s.harm ≤ CAP
        rw [hpackBump]
        exact h5
      · intro _
        show (s.custody.set r CARRIED).countP (· == BANKED) = 0
        rw [hbankSame]; exact hb0 h0
      · intro hf; exact absurd (show s.fate = 1 from hf) (by omega)
      · -- ⚑ EVERY RELIC IS TAKEN AT DEPTH, so the loot guard `pack + 1 + depth + harm ≤
        -- CAP` with `1 ≤ depth` is already `pack' + harm ≤ CAP - 1`. THIS is what used to
        -- be `crowned_bank_le_four`, stated without a word about one-way descent.
        show (s.custody.set r CARRIED).countP (· == CARRIED)
              + (s.custody.set r CARRIED).countP (· == BANKED) + s.harm ≤ CAP - 1
        rw [hpackBump, hbankSame]
        have hbz : bank s = 0 := hb0 h0
        simp only [pack, bank] at h5 hbz ⊢
        have hCAP : (CAP : Nat) = 8 := rfl
        omega
      · intro hdz; exact absurd (show s.depth = 0 from hdz) (by omega)
      · -- ⚑ THE PRIZE stays at the bottom, or THIS loot is the one that lifts it.
        by_cases hr0 : r = 0
        · right; left
          have hlt : (0 : Nat) < s.custody.length := by rw [hlen]; decide
          have hgot : (s.custody.set r CARRIED)[0]? = some CARRIED := by
            rw [hr0, List.getElem?_set_self (by simpa using hlt)]
          exact hgot
        · have hset : ∀ v : Nat, s.custody[0]? = some v →
              (s.custody.set r CARRIED)[0]? = some v := by
            intro v hv
            rw [List.getElem?_set_ne (by omega)]; exact hv
          rcases hprize with hp | hp | hp
          · exact Or.inl (hset _ hp)
          · exact Or.inr (Or.inl (hset _ hp))
          · exact Or.inr (Or.inr (hset _ hp))
    case isFalse => exact absurd h (by simp)
  | flee =>
    simp only [step] at h
    split at h
    case isTrue hcond =>
      obtain ⟨h0, h1, h2⟩ := hcond
      cases h
      have hpack0 : (s.custody.map fleeMap).countP (· == CARRIED) = 0 :=
        countP_fleeMap_carried _
      have hbank : (s.custody.map fleeMap).countP (· == BANKED)
          = s.custody.countP (· == CARRIED) + s.custody.countP (· == BANKED) :=
        countP_fleeMap_banked _
      refine ⟨⟨?_, ?_⟩, ?_, hdepth, ?_, hways, ?_, ?_, ?_, ?_, ?_, hwb, ?_, hharm⟩
      · show (s.custody.map fleeMap).length = RELICS
        simpa using hlen
      · intro c hc
        simp only [List.mem_map] at hc
        obtain ⟨a, ha, hEq⟩ := hc
        by_cases hA : a = CARRIED
        · right; right
          rw [← hEq]
          simp [fleeMap, hA]
        · have hca : c = a := by rw [← hEq]; simp [fleeMap, hA]
          subst hca; exact hcodes c ha
      · show s.spent + 1 ≤ BREATH; omega
      · show (1 : Nat) ≤ 1; exact Nat.le_refl 1
      · show (s.custody.map fleeMap).countP (· == CARRIED) + s.depth + s.harm ≤ CAP
        rw [hpack0]
        have hcap' : pack s + s.depth + s.harm ≤ CAP := hcap
        simp only [pack] at hcap'
        omega
      · intro hf; exact absurd (show (1 : Nat) = 0 from hf) (by omega)
      · -- ⚑ THE BANKED RUN STANDS AT THE MOUTH. `flee` demands `depth = 0`, so this is
        -- no longer "the pack emptied somewhere" — it is a receipt that the climb was
        -- paid for.
        intro _
        exact ⟨hpack0, h2⟩
      · show (s.custody.map fleeMap).countP (· == CARRIED)
              + (s.custody.map fleeMap).countP (· == BANKED) + s.harm ≤ CAP - 1
        rw [hpack0, hbank]
        have hcap1' : pack s + bank s + s.harm ≤ CAP - 1 := hcap1
        simp only [pack, bank] at hcap1'
        omega
      · intro _; exact hd0 h2
      · rcases hprize with hp | hp | hp
        · left
          show (s.custody.map fleeMap)[0]? = some FLOORS
          rw [List.getElem?_map, hp]
          rfl
        · right; right
          show (s.custody.map fleeMap)[0]? = some BANKED
          rw [List.getElem?_map, hp]
          rfl
        · right; right
          show (s.custody.map fleeMap)[0]? = some BANKED
          rw [List.getElem?_map, hp]
          rfl
    case isFalse => exact absurd h (by simp)

/-- Every reachable state satisfies the design laws. -/
theorem inv_reachable {s : DState} (h : Reachable s) : Inv s := by
  obtain ⟨ms, hms⟩ := h
  -- generalize over the seed state
  suffices H : ∀ (ms : List Move) (s0 s1 : DState), Inv s0 →
      (ms.foldl (fun acc m => acc.bind (fun t => step t m)) (some s0)) = some s1 →
      Inv s1 by
    exact H ms genesisState s inv_genesis hms
  intro ms
  induction ms with
  | nil => intro s0 s1 h0 h1; simp at h1; exact h1 ▸ h0
  | cons m rest ih =>
    intro s0 s1 h0 h1
    simp only [List.foldl_cons, Option.bind_some] at h1
    cases hstep : step s0 m with
    | none =>
      rw [hstep, foldl_none] at h1
      simp at h1
    | some smid =>
      rw [hstep] at h1
      exact ih smid s1 (inv_step h0 hstep) h1

/-! ## 7. The design laws as standalone theorems. -/

/-- **Law 2 — descent attenuates capability**: carried relics + depth + the grip the
guardians have broken never exceed CAP. -/
theorem capacity_attenuates {s : DState} (h : Reachable s) :
    pack s + s.depth + s.harm ≤ CAP :=
  (inv_reachable h).2.2.2.2.2.1

/-- **Law 3b — harm is a RATCHET, and `delve` does not wash it off.** `wounds` is the
standing guardian's tally and resets on descent; `harm` is the run's, and only ever
climbs — capped at `HARMCAP`. -/
theorem harm_ratchets {s s' : DState} {m : Move} (h : step s m = some s') :
    s.harm ≤ s'.harm := by
  cases m <;> simp only [step] at h <;> split at h <;>
    first
      | (cases h; exact Nat.le_refl _)
      | (cases h; exact Nat.le_succ _)
      | exact absurd h (by simp)

theorem harm_bounded {s : DState} (h : Reachable s) : s.harm ≤ HARMCAP :=
  (inv_reachable h).2.2.2.2.2.2.2.2.2.2.2.2

/-- Named accessor for the invariant's ways clause (positional projections into a
thirteen-clause conjunction are a footgun; downstream files use this). -/
theorem inv_waysBehind {s : DState} (h : Inv s) : WaysBehind s :=
  h.2.2.2.2.2.2.2.2.2.2.1

/-- **The climb is unconditional** — a way you have already passed is still open, so
`ascend` never meets a locked door. Only the light can keep you down. -/
theorem ways_behind_stay_open {s : DState} (h : Reachable s) :
    ∀ d, 2 ≤ d → d ≤ s.depth → wayOpen s d = true :=
  inv_waysBehind (inv_reachable h)

/-- **The surface has no guardian.** -/
theorem surface_is_unguarded {s : DState} (h : Reachable s) (hd : s.depth = 0) :
    s.wounds = 0 :=
  (inv_reachable h).2.2.2.2.2.2.2.2.2.1 hd

/-- **Law 3a — the light dies**: at `spent = BREATH` no verb is legal. Permadeath is a
theorem, not a timer. -/
theorem the_light_dies {s : DState} (hs : s.spent = BREATH) (m : Move) :
    step s m = none := by
  cases m <;> simp only [step] <;> split <;>
    first
      | rfl
      | (rename_i hc; exact absurd hc.2.1 (by omega))

/-- Every legal turn strictly spends breath. -/
theorem step_spends {s s' : DState} {m : Move} (h : step s m = some s') :
    s.spent < s'.spent := by
  cases m <;> simp only [step] at h <;> split at h <;>
    (cases h; try (show s.spent < s.spent + _; omega))

/-- **Law 3b — a run is at most `BREATH` turns long.** -/
theorem run_bounded {ms : List Move} {s : DState} (h : replay ms = some s) :
    ms.length ≤ BREATH := by
  suffices H : ∀ (ms : List Move) (s0 s1 : DState),
      (ms.foldl (fun acc m => acc.bind (fun t => step t m)) (some s0)) = some s1 →
      s0.spent + ms.length ≤ s1.spent by
    have hlen := H ms genesisState s h
    have hspent : s.spent ≤ BREATH := (inv_reachable ⟨ms, h⟩).2.1
    have hg : genesisState.spent = 0 := rfl
    omega
  intro ms
  induction ms with
  | nil => intro s0 s1 h1; simp at h1; subst h1; simp
  | cons m rest ih =>
    intro s0 s1 h1
    simp only [List.foldl_cons, Option.bind_some] at h1
    cases hstep : step s0 m with
    | none =>
      rw [hstep, foldl_none] at h1
      simp at h1
    | some smid =>
      rw [hstep] at h1
      have h2 := ih smid s1 h1
      have h3 := step_spends hstep
      simp only [List.length_cons]
      omega

/-- **Law 5 — banking is terminal**: a banked run is a frozen tomb. -/
theorem banked_run_frozen {s : DState} (hf : s.fate = 1) (m : Move) :
    step s m = none := by
  cases m <;> simp only [step] <;> split <;>
    first
      | rfl
      | (rename_i hc; exact absurd hc.1 (by omega))

/-- **Law 4 — keys are capabilities**: an admitted `unlock w` EXERCISED the carried
key-relic for `w`; there is no other way to open a way. -/
theorem keyless_unlock_impossible {s s' : DState} {w : Nat}
    (h : step s (.unlock w) = some s') :
    s.custody[keyFor w]? = some CARRIED := by
  simp only [step] at h
  split at h
  · rename_i hc; exact hc.2.2.2.2.2
  · exact absurd h (by simp)

/-- **Law 1 — the custody ratchet**: a relic's custody code never decreases; provenance
runs one way (floor → carried → banked), so a banked relic's history is a straight
receipt chain back to the mint. -/
theorem custody_ratchet {s s' : DState} {m : Move} (hInv : Inv s)
    (h : step s m = some s') :
    ∀ (i a b : Nat), s.custody[i]? = some a → s'.custody[i]? = some b → a ≤ b := by
  intro i a b hga hgb
  cases m with
  | delve =>
    simp only [step] at h; split at h
    · cases h; simp only at hgb; rw [hga] at hgb; cases hgb; omega
    · exact absurd h (by simp)
  | ascend =>
    simp only [step] at h; split at h
    · cases h; simp only at hgb; rw [hga] at hgb; cases hgb; omega
    · exact absurd h (by simp)
  | unlock w =>
    simp only [step] at h; split at h
    · cases h; simp only at hgb; rw [hga] at hgb; cases hgb; omega
    · exact absurd h (by simp)
  | smite =>
    simp only [step] at h; split at h
    · cases h; simp only at hgb; rw [hga] at hgb; cases hgb; omega
    · exact absurd h (by simp)
  | lunge =>
    simp only [step] at h; split at h
    · cases h; simp only at hgb; rw [hga] at hgb; cases hgb; omega
    · exact absurd h (by simp)
  | loot r =>
    simp only [step] at h; split at h
    · rename_i hc
      obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hc
      cases h
      simp only at hgb
      by_cases hir : i = r
      · subst hir
        rw [hga] at h3; cases h3
        have : b = CARRIED := by
          have hlt : i < s.custody.length := by
            by_contra hge
            rw [List.getElem?_eq_none (by omega)] at hga
            cases hga
          rw [List.getElem?_set_self (by simpa using hlt)] at hgb
          simpa using hgb.symm
        subst this
        obtain ⟨hlen, hcodes⟩ := hInv.1
        have hd4 : s.depth ≤ FLOORS := hInv.2.2.1
        simp only [CARRIED, FLOORS] at *
        omega
      · rw [List.getElem?_set_ne (by omega)] at hgb
        rw [hga] at hgb; cases hgb; omega
    · exact absurd h (by simp)
  | flee =>
    simp only [step] at h; split at h
    · cases h
      simp only [List.getElem?_map, hga, Option.map_some] at hgb
      cases hgb
      by_cases hA : a = CARRIED <;> simp [fleeMap, hA, CARRIED, BANKED] <;> omega
    · exact absurd h (by simp)

/-- **Law 2 corollary — no receipt chain banks everything**: the full hoard can never
be banked. It used to follow from "the surface holds nothing"; that clause died with the
one-way descent, and this one stands on `hoard_never_leaves_whole` instead — which is
where it always belonged. -/
theorem no_run_banks_everything {s : DState} (h : Reachable s) :
    bank s < RELICS := by
  have hcap1 : pack s + bank s + s.harm ≤ CAP - 1 :=
    (inv_reachable h).2.2.2.2.2.2.2.2.1
  have hCAP : (CAP : Nat) = 8 := rfl
  have hREL : (RELICS : Nat) = 8 := rfl
  omega

/-- ⚑ **THE REPLACEMENT FOR `crowned_bank_le_four`, and the law that made it retirable.**

`crowned_bank_le_four` (`bank ≤ CAP − FLOORS − harm` for a run that banked THE PRIZE) was
TRUE, and it was true BECAUSE THERE WAS NO WAY BACK UP: banking the prize forced
`depth = FLOORS` in the terminal state, so the capacity law could be read at the bottom.
That is an artifact of the one-way descent, not a design intent — and `ascend` falsifies
it (crown at depth 4, climb, re-fight a floor, take more, climb out: `maxbank(crowned)`
reaches 5–6 on ten of the sixteen daily maps).

What survives — and what was doing the real work all along — is this: EVERY relic that
leaves the dungeon was looted at `depth ≥ 1` under `pack + 1 + depth + harm ≤ CAP`, and
every point of `harm` was bought at `depth ≥ 1` too. One carry slot is therefore spoken
for no matter how the run is played, and each broken grip eats another. No clause about
one-way descent appears anywhere in it, which is exactly why it outlives `ascend`. -/
theorem hoard_never_leaves_whole {s : DState} (h : Reachable s) :
    pack s + bank s + s.harm ≤ CAP - 1 :=
  (inv_reachable h).2.2.2.2.2.2.2.2.1

/-- **The lunge keeps its price, stated on the only ledger that matters.** A banked run
took `harm` broken grips and banked at most `CAP − 1 − harm` relics: every point of harm
is EXACTLY one relic that did not leave the dungeon, whatever route the run took to the
surface. This is the `bank + harm ≤ CAP` the retirement owed, proven one tighter. -/
theorem banked_bank_pays_for_harm {s : DState} (h : Reachable s) (hf : s.fate = 1) :
    bank s + s.harm ≤ CAP - 1 := by
  have hcap1 := hoard_never_leaves_whole h
  have hp : pack s = 0 := ((inv_reachable h).2.2.2.2.2.2.2.1 hf).1
  omega

/-- **You climb out; you do not teleport out.** A banked run is standing at the mouth of
the dungeon — `flee` demands the surface, so `fate = 1` is a receipt that the climb was
paid for, one breath per floor. -/
theorem banked_at_the_surface {s : DState} (h : Reachable s) (hf : s.fate = 1) :
    s.depth = 0 :=
  ((inv_reachable h).2.2.2.2.2.2.2.1 hf).2

/-- **THE PRIZE lies at the bottom or it is in your hands.** The old form of this clause
(`custody 0 = FLOORS ∨ depth = FLOORS`) said you could not be holding the prize anywhere
but standing on it. You can now — you carry it up — and what remains true is that it
never lies on any other floor. -/
theorem prize_never_lies_elsewhere {s : DState} (h : Reachable s) :
    s.custody[0]? = some FLOORS ∨ s.custody[0]? = some CARRIED
      ∨ s.custody[0]? = some BANKED :=
  (inv_reachable h).2.2.2.2.2.2.2.2.2.2.2.1

/-- **And the prize is still won at the bottom** — the content `crowned_bank_le_four`
carried that is not an artifact of the one-way descent, restated as the local fact it
actually is: the only step that takes THE PRIZE out of its home is a `loot 0` standing on
floor `FLOORS`. A run holding the prize stood at the bottom; it simply need not still be
standing there. -/
theorem prize_leaves_home_only_at_the_bottom {s s' : DState} {m : Move}
    (hp : s.custody[0]? = some FLOORS) (h : step s m = some s')
    (hmoved : s'.custody[0]? ≠ some FLOORS) :
    m = .loot 0 ∧ s.depth = FLOORS := by
  cases m with
  | delve => simp only [step] at h; split at h
             · cases h; exact absurd hp hmoved
             · exact absurd h (by simp)
  | ascend => simp only [step] at h; split at h
              · cases h; exact absurd hp hmoved
              · exact absurd h (by simp)
  | unlock w => simp only [step] at h; split at h
                · cases h; exact absurd hp hmoved
                · exact absurd h (by simp)
  | smite => simp only [step] at h; split at h
             · cases h; exact absurd hp hmoved
             · exact absurd h (by simp)
  | lunge => simp only [step] at h; split at h
             · cases h; exact absurd hp hmoved
             · exact absurd h (by simp)
  | loot r =>
    simp only [step] at h; split at h
    · rename_i hc
      obtain ⟨_, _, _, h3, _, _⟩ := hc
      cases h
      by_cases hr0 : r = 0
      · subst hr0
        rw [hp] at h3
        exact ⟨rfl, (Option.some.injEq _ _ ▸ h3).symm⟩
      · exfalso
        apply hmoved
        show (s.custody.set r CARRIED)[0]? = some FLOORS
        rw [List.getElem?_set_ne (by omega)]
        exact hp
    · exact absurd h (by simp)
  | flee =>
    simp only [step] at h; split at h
    · cases h
      exfalso
      apply hmoved
      show (s.custody.map fleeMap)[0]? = some FLOORS
      rw [List.getElem?_map, hp]
      rfl
    · exact absurd h (by simp)

/-! ### ⚑ THE TOLL — why the descent can now kill you.

`flee` demands the surface and `ascend` costs one breath per floor, so the real clock a
run plays against is not `spent` but `spent + depth`: the breath already burned PLUS the
breath the climb home will cost. `toll_ratchets` says no verb ever rewinds it — `ascend`
is the only verb that lowers `depth`, and it pays exactly the floor it removes, so the
toll is preserved rather than refunded. `flee_needs_toll` says banking demands
`toll < BREATH`. Together: a reachable state with `BREATH ≤ toll` is DEAD — not stuck,
not disadvantaged, but incapable of ever banking, from any continuation whatsoever. -/

/-- The TOLL: breath already spent, plus the breath the climb home will cost. -/
def toll (s : DState) : Nat := s.spent + s.depth

/-- Every verb but `flee` leaves `fate` alone. -/
private theorem step_fate_frozen {s s' : DState} {m : Move} (hm : m ≠ Move.flee)
    (h : step s m = some s') : s'.fate = s.fate := by
  cases m with
  | flee => exact absurd rfl hm
  | delve => simp only [step] at h; split at h
             · cases h; rfl
             · exact absurd h (by simp)
  | ascend => simp only [step] at h; split at h
              · cases h; rfl
              · exact absurd h (by simp)
  | unlock w => simp only [step] at h; split at h
                · cases h; rfl
                · exact absurd h (by simp)
  | smite => simp only [step] at h; split at h
             · cases h; rfl
             · exact absurd h (by simp)
  | lunge => simp only [step] at h; split at h
             · cases h; rfl
             · exact absurd h (by simp)
  | loot r => simp only [step] at h; split at h
              · cases h; rfl
              · exact absurd h (by simp)

/-- **The toll is a RATCHET no verb rewinds.** Descending buys a debt at par; the climb
repays it at par (`ascend` spends exactly the floor it removes); everything else only
ever adds. This is the whole reason `ascend` makes the game lethal instead of merely
longer — you cannot walk a bad clock off. -/
theorem toll_ratchets {s s' : DState} {m : Move} (h : step s m = some s') :
    toll s ≤ toll s' := by
  cases m with
  | delve =>
    simp only [step] at h; split at h
    · cases h; show s.spent + s.depth ≤ s.spent + 1 + (s.depth + 1); omega
    · exact absurd h (by simp)
  | ascend =>
    simp only [step] at h; split at h
    · rename_i hc
      obtain ⟨_, _, hd1⟩ := hc
      cases h; show s.spent + s.depth ≤ s.spent + 1 + (s.depth - 1); omega
    · exact absurd h (by simp)
  | unlock w =>
    simp only [step] at h; split at h
    · cases h; show s.spent + s.depth ≤ s.spent + 1 + s.depth; omega
    · exact absurd h (by simp)
  | smite =>
    simp only [step] at h; split at h
    · cases h; show s.spent + s.depth ≤ s.spent + 2 + s.depth; omega
    · exact absurd h (by simp)
  | lunge =>
    simp only [step] at h; split at h
    · cases h; show s.spent + s.depth ≤ s.spent + 1 + s.depth; omega
    · exact absurd h (by simp)
  | loot r =>
    simp only [step] at h; split at h
    · cases h; show s.spent + s.depth ≤ s.spent + 1 + s.depth; omega
    · exact absurd h (by simp)
  | flee =>
    simp only [step] at h; split at h
    · cases h; show s.spent + s.depth ≤ s.spent + 1 + s.depth; omega
    · exact absurd h (by simp)

/-- **Banking demands an unspent toll**: `flee` is legal only from the surface with a
breath still in hand — which is exactly `toll s < BREATH`. -/
theorem flee_needs_toll {s s' : DState} (h : step s .flee = some s') : toll s < BREATH := by
  simp only [step] at h
  split at h
  · rename_i hc
    obtain ⟨_, h1, h2⟩ := hc
    show s.spent + s.depth < BREATH
    omega
  · exact absurd h (by simp)

/-- **⚑ LAW 3c — THE DESCENT CAN KILL YOU.** From a living state whose toll has reached
`BREATH`, NO continuation banks — not a shorter route, not a cheaper verb, not luck. The
run is over and the pack is lost where it lies.

This is the theorem the descent claimed in prose and did not have. Before `ascend`,
`flee` cost ONE breath from ANY depth, so `toll` was just `spent`, every reachable
position could still go home, and on fourteen of the sixteen daily maps there was no
losable position at all. -/
theorem doomed_never_banks {s : DState} (halive : s.fate = 0) (hdoom : BREATH ≤ toll s)
    (ms : List Move) (t : DState)
    (ht : ms.foldl (fun acc m => acc.bind (fun u => step u m)) (some s) = some t) :
    t.fate = 0 := by
  suffices H : ∀ (ms : List Move) (s0 s1 : DState), s0.fate = 0 → BREATH ≤ toll s0 →
      (ms.foldl (fun acc m => acc.bind (fun u => step u m)) (some s0)) = some s1 →
      s1.fate = 0 by
    exact H ms s t halive hdoom ht
  intro ms
  induction ms with
  | nil => intro s0 s1 h0 _ h1; simp at h1; exact h1 ▸ h0
  | cons m rest ih =>
    intro s0 s1 h0 hd h1
    simp only [List.foldl_cons, Option.bind_some] at h1
    cases hstep : step s0 m with
    | none => rw [hstep, foldl_none] at h1; simp at h1
    | some smid =>
      rw [hstep] at h1
      refine ih smid s1 ?_ (le_trans hd (toll_ratchets hstep)) h1
      by_cases hf : m = Move.flee
      · subst hf
        exact absurd (flee_needs_toll hstep) (by omega)
      · rw [step_fate_frozen hf hstep]; exact h0

/-- **Death is REACHABLE — driven, on every map, with breath still in hand.** The witness
below walks fourteen floors down-and-up (28 breath, back at the surface) and then takes
one more step down. It stands on floor 1 with 29 of 30 spent: the last breath buys the
climb, and there is nothing left to flee with. It dies at the mouth of the dungeon.

Only `delve`/`ascend` appear, and way 1 is always open, so this is legal on EVERY drawn
map regardless of where the keys lie (`doomed_every_day`). -/
def doomedRun : List Move :=
  (List.replicate 14 [Move.delve, Move.ascend]).flatten ++ [Move.delve]

def doomedOutcome : Option DState := replay doomedRun

/-- The doomed witness, as a decidable predicate over the day's world. -/
def doomExists : Bool :=
  match doomedOutcome with
  | some s => (s.fate == 0) && (s.spent + 1 ≤ BREATH) && decide (BREATH ≤ toll s)
  | none   => false

/-- **`doomExists` really is a doomed reachable state** — alive, with breath left, and
past the toll. Everything it can still do, `doomed_never_banks` says, ends unbanked. -/
theorem doomed_of_doomExists (h : doomExists = true) :
    ∃ s, Reachable s ∧ s.fate = 0 ∧ s.spent < BREATH ∧ BREATH ≤ toll s := by
  unfold doomExists at h
  split at h
  · rename_i s hc
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    have hrep : replay doomedRun = some s := hc
    exact ⟨s, ⟨doomedRun, hrep⟩, h.1.1, by omega, h.2⟩
  · exact absurd h (by simp)

/-! ## 8. THE CROWNED LINE — a winning receipt chain GENERATED from the day's world.

The old file hard-coded one 18-verb script for one hard-coded map. Now the winning line
is a FUNCTION of the world, and `crownedWins` REPLAYS it through the actual rulebook: a
world is completable because a real receipt chain banks THE PRIZE, not because we hoped. -/

/-- The relics a crowned line must win on floor `d`: the way-keys minted there, then
THE PRIZE at the bottom (a key is never minted at `FLOORS`, by `wf_key_above_its_way`). -/
def needAt (d : Nat) : List Nat :=
  (List.range' 2 (FLOORS - 1)).filterMap
      (fun w => if homeOf (keyFor w) == d then some (keyFor w) else none)
    ++ (if d == FLOORS then [0] else [])

/-- The ways whose key is won on floor `d` — exercised the moment it is in hand. -/
def unlocksAt (d : Nat) : List Nat :=
  (List.range' 2 (FLOORS - 1)).filter (fun w => homeOf (keyFor w) == d)

/-- One floor of the crowned line: descend; if anything needed lies here, fell the
guardian and take it; then exercise every key just won. A floor holding nothing the line
needs costs exactly one breath — the day's map decides where the fighting happens. -/
def floorLine (d : Nat) : List Move :=
  (Move.delve ::
      (if (needAt d).isEmpty then []
       else List.replicate (guardHp d) Move.smite ++ (needAt d).map Move.loot))
    ++ (unlocksAt d).map Move.unlock

/-- The perfect crowned descent for the DAY'S world: win each key where it lies, exercise
it, fell the deep guardian, take the prize — and then CLIMB OUT, one breath per floor,
before banking. The four trailing `ascend`s are not decoration: `flee` is illegal below
the surface, so the crowned line now pays `FLOORS` breath for the way home, which is
exactly why `BREATH` moved 26 → 30. -/
def crownedRun : List Move :=
  ((List.range' 1 FLOORS).flatMap floorLine)
    ++ List.replicate FLOORS Move.ascend ++ [Move.flee]

def crownedOutcome : Option DState := replay crownedRun

/-- **The completability check, DRIVEN**: the generated line is legal end to end under
the real `step`, ends banked, and banks THE PRIZE. -/
def crownedWins : Bool :=
  match crownedOutcome with
  | some s => (s.fate == 1) && (s.custody.getD 0 0 == BANKED)
  | none   => false

/-- The breath the crowned line costs on the day's world (`0` if it does not replay). -/
def crownedCost : Nat := (crownedOutcome.map (·.spent)).getD 0

/-- **The dungeon is completable**: some receipt chain from the mint banks THE PRIZE. -/
def Completable : Prop :=
  ∃ ms s, replay ms = some s ∧ s.fate = 1 ∧ s.custody[0]? = some BANKED

/-- Driving the generated line IS the completability proof — witness and all. -/
theorem completable_of_crownedWins (h : crownedWins = true) : Completable := by
  simp only [crownedWins] at h
  cases hc : crownedOutcome with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some s =>
    rw [hc] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have hrep : replay crownedRun = some s := hc
    have hlen := (inv_reachable ⟨crownedRun, hrep⟩).1.1
    have h0 : 0 < s.custody.length := by rw [hlen]; decide
    refine ⟨crownedRun, s, hrep, h.1, ?_⟩
    rw [List.getElem?_eq_getElem h0, List.getElem_eq_getD (0 : Nat)]
    exact congrArg some h.2

end

/-! ## 9. THE DAY'S DRAW — the map is a function of the committed day-seed.

`drawFamily` is the whole space of maps the descent can be played on. Every member is
CHECKED (`drawFamily_wf`, by `decide`) and every member is DRIVEN to a win
(`winsAt_true`, by `decide` over the family) — a drawn dungeon that cannot be finished is
not a hypothesis we carry, it is a proposition we refute.

Family shape (the axes the day moves):
* **where the keys lie** — the key to way 3 on floor 1 or 2; the key to way 4 on floor
  1, 2 or 3. All three keys on floor 1 is a *different puzzle*: you skip two guardians
  entirely but haul three keys the whole way down against `pack + depth ≤ CAP`.
* **which guardians are tough** — per-floor vitality 1 or 2, so the breath the line
  costs moves with the map.
* **where the treasures lie** — the greed decisions (never needed by the crowned line,
  always competing with it for capacity).

Capacity keeps the tension the fixed map had, on EVERY member: at the bottom you may
carry `CAP - FLOORS = 4`, which is exactly three keys plus the prize. One extra treasure
past floor 3 forfeits the crown. -/

/-- Day 0 — the map the descent shipped with, kept as the canonical/default world. -/
def canonWorld : World := ⟨[4, 1, 2, 3, 1, 1, 2, 3], [0, 1, 1, 2, 2]⟩

/-- The number of distinct maps in the draw. Growing the family is one line here plus a
re-emit; the artifact grows linearly (one emitted program per member). -/
def dayCount : Nat := 16

/-- **The family of maps the day-seed draws from.** Index 0 is the shipped map. -/
def drawFamily : List World :=
  [ ⟨[4, 1, 2, 3, 1, 1, 2, 3], [0, 1, 1, 2, 2]⟩,   -- 0  the shipped map        cost 24
    ⟨[4, 1, 2, 3, 2, 1, 3, 4], [0, 2, 1, 2, 2]⟩,   -- 1  every key one floor up  cost 26
    ⟨[4, 1, 2, 3, 1, 2, 2, 4], [0, 1, 1, 1, 2]⟩,   -- 2  a soft descent          cost 22
    ⟨[4, 1, 2, 3, 3, 1, 1, 2], [0, 2, 2, 1, 1]⟩,   -- 3  the teeth are up top    cost 24
    ⟨[4, 1, 1, 3, 1, 2, 3, 4], [0, 2, 1, 2, 2]⟩,   -- 4  floor 2 holds nothing   cost 24
    ⟨[4, 1, 1, 3, 2, 2, 3, 3], [0, 2, 2, 2, 1]⟩,   -- 5  a shallow bottom        cost 22
    ⟨[4, 1, 1, 3, 1, 1, 4, 4], [0, 2, 1, 1, 2]⟩,   -- 6  treasure in the deep    cost 22
    ⟨[4, 1, 1, 2, 1, 3, 3, 4], [0, 2, 2, 1, 2]⟩,   -- 7  floor 3 holds nothing   cost 24
    ⟨[4, 1, 1, 2, 2, 2, 4, 4], [0, 1, 2, 1, 2]⟩,   -- 8  an easy door            cost 22
    ⟨[4, 1, 1, 2, 1, 2, 3, 4], [0, 2, 2, 2, 2]⟩,   -- 9  every guardian tough    cost 24
    ⟨[4, 1, 2, 2, 1, 1, 3, 4], [0, 1, 2, 2, 2]⟩,   -- 10 two keys on floor 2     cost 22
    ⟨[4, 1, 2, 2, 3, 3, 4, 4], [0, 2, 2, 1, 2]⟩,   -- 11 the deep is crowded     cost 24
    ⟨[4, 1, 1, 1, 2, 2, 3, 3], [0, 2, 1, 1, 2]⟩,   -- 12 all keys on floor 1     cost 20
    ⟨[4, 1, 1, 1, 1, 3, 4, 4], [0, 2, 2, 2, 2]⟩,   -- 13 all keys, all tough     cost 20
    ⟨[4, 1, 2, 1, 1, 2, 2, 4], [0, 1, 2, 2, 2]⟩,   -- 14 the deep key lies high  cost 22
    ⟨[4, 1, 2, 1, 3, 4, 4, 4], [0, 2, 2, 1, 2]⟩ ]  -- 15 a hoard at the bottom   cost 24

theorem canonWorld_wf : WorldWF canonWorld = true := by decide

/-- **Every drawn map is a LEGAL map** — checked, not assumed. -/
theorem drawFamily_wf : drawFamily.all WorldWF = true := by decide

#guard drawFamily.length = dayCount
#guard drawFamily.getD 0 canonWorld = canonWorld

/-- The map at family index `k` (out-of-range folds to the canonical map). -/
def worldAt (k : Nat) : World := drawFamily.getD k canonWorld

theorem worldAt_wf (k : Nat) : WorldWF (worldAt k) = true := by
  simp only [worldAt]
  by_cases hk : k < drawFamily.length
  · rw [← List.getElem_eq_getD (l := drawFamily) (i := k) (h := hk) canonWorld]
    exact (List.all_eq_true.mp drawFamily_wf) _ (List.getElem_mem hk)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    exact canonWorld_wf

/-- The world parameter for family index `k`. -/
@[reducible] def instAt (k : Nat) : WorldParam := ⟨worldAt k, worldAt_wf k⟩

def winsAt (k : Nat) : Bool := @crownedWins (instAt k)
def costAt (k : Nat) : Nat := @crownedCost (instAt k)

private theorem lt_dayCount_cases {k : Nat} (hk : k < dayCount) :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨
    k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by
  simp only [dayCount] at hk; omega

/-- **EVERY map in the family is finishable**, driven through the real rulebook. -/
theorem winsAt_true (k : Nat) (hk : k < dayCount) : winsAt k = true := by
  rcases lt_dayCount_cases hk with
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

/-- **The tension survives the draw**: every day's perfect line costs at least 24 of the
30 breath, and (by `winsAt_true`) at most all of it. The slack band is UNCHANGED by the
climb — 0–6 spare breath, exactly as when the line cost 20–26 of 26 — because `ascend`
added `FLOORS` breath to every day's line and `BREATH` grew by the same `FLOORS`. -/
theorem costAt_tense (k : Nat) (hk : k < dayCount) : 24 ≤ costAt k ∧ costAt k ≤ BREATH := by
  rcases lt_dayCount_cases hk with
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    exact ⟨by decide, by decide⟩

/-- **The day's map, drawn from the committed day-seed.** The caller reduces the beacon
to a family index; the map is then a total function of it. -/
def drawWorld (n : Nat) : World := worldAt (n % dayCount)

@[reducible] def drawInst (n : Nat) : WorldParam := instAt (n % dayCount)

/-- **THE LAW OF THE DAILY**: whatever the beacon says, the dungeon it draws can be
finished — there is a legal receipt chain from the mint that banks THE PRIZE. -/
theorem draw_completable (n : Nat) : @Completable (drawInst n) :=
  @completable_of_crownedWins (drawInst n) (winsAt_true _ (Nat.mod_lt _ (by decide)))

/-- And the drawn map is a legal map. -/
theorem draw_wf (n : Nat) : WorldWF (drawWorld n) = true := worldAt_wf _

/-- **⚑ EVERY DRAWN MAP CAN KILL YOU.** `doomedRun` uses only `delve`/`ascend` and way 1
is always open, so the doomed witness exists on every member of the family — checked, not
argued. Together with `doomed_never_banks` this is the retirement of "the descent is
deathless": there is a reachable, living position on EVERY day from which no continuation
whatsoever banks. -/
theorem doomed_every_day (k : Nat) (hk : k < dayCount) : @doomExists (instAt k) = true := by
  rcases lt_dayCount_cases hk with
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

/-- The daily form: whatever the beacon says, the dungeon it draws has a losable position. -/
theorem draw_can_kill (n : Nat) :
    ∃ s, @Reachable (drawInst n) s ∧ s.fate = 0 ∧ s.spent < BREATH ∧ BREATH ≤ toll s :=
  @doomed_of_doomExists (drawInst n) (doomed_every_day _ (Nat.mod_lt _ (by decide)))

#guard (List.range dayCount).all (fun k => @doomExists (instAt k))

-- Every day of the family, driven end to end (the theorems above, as executable checks).
#guard (List.range dayCount).all winsAt
#guard (List.range dayCount).all (fun k => 24 ≤ costAt k && costAt k ≤ BREATH)
-- The old vector was [24,26,22,24,24,22,22,24,22,24,22,24,20,20,22,24]; every entry is
-- now exactly `+ FLOORS`, the price of the climb home.
#guard (List.range dayCount).map costAt
        = [28, 30, 26, 28, 28, 26, 26, 28, 26, 28, 26, 28, 24, 24, 26, 28]
-- The days are genuinely different dungeons (no two draws share a map).
#guard ((List.range dayCount).map worldAt).Nodup

/-! ## 10. Day 0 driven — the shipped map still plays exactly as it did. -/

section Canon
local instance : WorldParam := instAt 0

-- The crowned line for the shipped map is the old 18-verb script plus THE CLIMB: four
-- `ascend`s before the `flee`, because banking now demands the surface. It costs 28 of
-- 30 breath (was 24 of 26 — the same 2 spare) and banks the prize + three keys.
#guard crownedRun =
  [ .delve, .smite, .loot 1, .unlock 2,
    .delve, .smite, .loot 2, .unlock 3,
    .delve, .smite, .smite, .loot 3, .unlock 4,
    .delve, .smite, .smite, .loot 0,
    .ascend, .ascend, .ascend, .ascend,
    .flee ]
#guard (replay crownedRun).isSome
#guard (replay crownedRun).map (·.fate) = some 1
#guard (replay crownedRun).map bank = some 4
#guard (replay crownedRun).map (·.spent) = some 28
#guard (replay crownedRun).map (fun s => s.custody[0]?) = some (some BANKED)
-- The banked run stands at the mouth (`banked_at_the_surface`), driven.
#guard (replay crownedRun).map (·.depth) = some 0

-- ⚑ THE ONE-WAY DOOR CLOSED: the SAME crowned script without the climb is REFUSED. This
-- is the falsifier for the whole change — if `flee` were still a teleport this would
-- still bank, and nothing below would be lethal.
#guard replay
  [ .delve, .smite, .loot 1, .unlock 2,
    .delve, .smite, .loot 2, .unlock 3,
    .delve, .smite, .smite, .loot 3, .unlock 4,
    .delve, .smite, .smite, .loot 0,
    .flee ] = none

-- ⚑ THE CLIMB IS UNCONDITIONAL — no key, no guardian, no capacity, only breath. From the
-- bottom with a full pack, four ascends always get you home.
#guard (replay ([.delve, .smite, .loot 1, .unlock 2,
                 .delve, .smite, .loot 2, .unlock 3,
                 .delve, .smite, .smite, .loot 3, .unlock 4,
                 .delve, .smite, .smite, .loot 0] ++
                List.replicate 4 Move.ascend)).map (·.depth) = some 0

-- ⚑ AND THE DESCENT KILLS. Fourteen floors down-and-up (28 breath) then one step down:
-- alive at floor 1, 29 of 30 spent, one breath in hand — and no way to spend it that
-- ends banked. The last breath buys the climb; the flee is one breath too late.
#guard (replay doomedRun).map (·.spent) = some 29
#guard (replay doomedRun).map (·.depth) = some 1
#guard (replay doomedRun).map (·.fate)  = some 0
#guard (replay doomedRun).map toll      = some 30
#guard doomExists
#guard (replay (doomedRun ++ [.ascend])).map (·.spent) = some 30    -- the climb is paid
#guard replay (doomedRun ++ [.ascend, .flee]) = none                -- and there is nothing left
#guard replay (doomedRun ++ [.flee]) = none                         -- fleeing from below: illegal

-- Illegal moves are REFUSED by the rulebook (driven, not asserted):
-- keyless descent past floor 1 (way 2 shut):
#guard (replay [.delve, .delve]) = none
-- looting under a living guardian:
#guard (replay [.delve, .loot 1]) = none
-- a second unlock of the same way (the way is no longer 0):
#guard (replay [.delve, .smite, .loot 1, .unlock 2, .unlock 2]) = none
-- ⚑ FLEEING FROM BELOW is now itself illegal (`flee` demands `depth = 0`):
#guard (replay [.delve, .flee]) = none
-- climbing above the surface is not a verb you get:
#guard (replay [.ascend]) = none
-- moving after banking (the frozen tomb) — reached by the climb now:
#guard (replay [.delve, .ascend, .flee, .delve]) = none
-- fleeing twice:
#guard (replay [.delve, .ascend, .flee, .flee]) = none

/-! ### THE LUNGE, DRIVEN (day 0: `ghp = [0, 1, 1, 2, 2]`).

Everything below is `decide`-evaluated through the real `step`; nothing is asserted. -/

-- The same wound, one breath cheaper — and one carry slot poorer.
#guard (replay [.delve, .lunge, .loot 1]).map (·.spent)  = some 3
#guard (replay [.delve, .smite, .loot 1]).map (·.spent)  = some 4
#guard (replay [.delve, .lunge, .loot 1]).map (·.harm)   = some 1
#guard (replay [.delve, .smite, .loot 1]).map (·.harm)   = some 0

-- ⚑ `delve` RESETS `wounds` AND CARRIES `harm` — the ratchet is run-long.
#guard (replay [.delve, .lunge, .loot 1, .unlock 2, .delve]).map (·.wounds) = some 0
#guard (replay [.delve, .lunge, .loot 1, .unlock 2, .delve]).map (·.harm)   = some 1

-- The ratchet's ceiling BITES: two lunges are a run, a third is refused (harm ≤ 2).
-- (Capacity alone would still permit it here — 2 + 3 + 3 = 8 = CAP — so this refusal is
-- HARMCAP's, not the capacity clause's.)
#guard (replay [.delve, .lunge, .loot 1, .unlock 2,
                .delve, .lunge, .loot 2]).map (·.harm) = some 2
#guard (replay [.delve, .lunge, .loot 1, .unlock 2,
                .delve, .lunge, .loot 2, .unlock 3, .delve, .lunge]) = none

-- ⚑ THE DECISION AT THE BOTTOM SURVIVES THE CLIMB: the crowned line with ONE breath
-- saved by a lunge on floor 1 STILL cannot take the prize — at depth 4 the pack holds
-- three keys and capacity is `CAP - FLOORS - harm = 3`. The refusal lands on the `loot 0`,
-- before the climb is even reached. One saved breath, one forfeited crown.
#guard replay
  [ .delve, .lunge, .loot 1, .unlock 2,
    .delve, .smite, .loot 2, .unlock 3,
    .delve, .smite, .smite, .loot 3, .unlock 4,
    .delve, .smite, .smite, .loot 0,
    .ascend, .ascend, .ascend, .ascend,
    .flee ] = none
-- …and the same line with the press (today's smite) still crowns, for 28 of 30 breath.
#guard (replay crownedRun).map (·.harm) = some 0

-- ⚑ THE PRICE OF HARM, ON THE BANKED LEDGER (`banked_bank_pays_for_harm`): a run that
-- lunges once banks at most `CAP - 1 - harm = 6`. Driven at the edge — six relics out
-- with one broken grip, and the seventh refused by capacity, not by breath.
#guard (replay crownedRun).map (fun s => bank s + s.harm) = some 4

end Canon

/-! ## 11. Axiom hygiene. -/

#assert_axioms capacity_attenuates
#assert_axioms harm_ratchets
#assert_axioms harm_bounded
#assert_axioms the_light_dies
#assert_axioms run_bounded
#assert_axioms banked_run_frozen
#assert_axioms keyless_unlock_impossible
#assert_axioms custody_ratchet
#assert_axioms no_run_banks_everything
#assert_axioms hoard_never_leaves_whole
#assert_axioms banked_bank_pays_for_harm
#assert_axioms banked_at_the_surface
#assert_axioms prize_never_lies_elsewhere
#assert_axioms prize_leaves_home_only_at_the_bottom
#assert_axioms ways_behind_stay_open
#assert_axioms surface_is_unguarded
#assert_axioms toll_ratchets
#assert_axioms flee_needs_toll
#assert_axioms doomed_never_banks
#assert_axioms doomed_of_doomExists
#assert_axioms doomed_every_day
#assert_axioms draw_can_kill
#assert_axioms drawFamily_wf
#assert_axioms winsAt_true
#assert_axioms costAt_tense
#assert_axioms draw_completable
#assert_axioms draw_wf

end Dregg2.Games.Dungeon
