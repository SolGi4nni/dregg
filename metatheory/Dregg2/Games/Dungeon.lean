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
   state satisfies `pack + depth ≤ CAP` (`capacity_attenuates`). Descending with a full
   pack is not "discouraged" — the deeper turn is *unprovable*. Attenuation as
   arithmetic, not flavor. Corollary `crowned_bank_le_four`: a run that banks THE PRIZE
   (relic 0, floor 4) banks at most `CAP − FLOORS = 4` relics — reaching the bottom
   costs half your carrying rights. And `no_run_banks_everything`: no receipt chain
   whatsoever banks all `RELICS` relics.

3. **The light is the clock.** Every verb has a posted price in `spent`; `spent`
   strictly increases on every turn and is capped at `BREATH`. Permadeath is a theorem:
   a run is at most `BREATH` turns (`run_bounded`) and at `spent = BREATH` no verb is
   legal (`the_light_dies`).

4. **Keys are capabilities.** The way to floor `w` opens only by EXERCISING the carried
   key-relic for `w` (`keyless_unlock_impossible`): a key is an owned, un-dupable relic
   whose own provenance chain proves where it was won.

5. **Banking is terminal.** `flee` banks the pack and writes the run's fate exactly
   once; a banked run is a frozen tomb (`banked_run_frozen`).

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

/-- The light: total exertion a run may spend. A perfect crowned run costs 24; a full
clear is impossible (see `no_run_banks_everything` — by capacity, not by breath). -/
abbrev BREATH : Nat := 26

/-- Carrying rights at the surface; the capacity law is `pack + depth ≤ CAP`. -/
abbrev CAP : Nat := 8

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
  run must stand on the deepest floor, which is what `crowned_bank_le_four` cashes in);
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
  fate    : Nat          -- 0 = alive, 1 = banked
  ways    : List Nat     -- 0/1 each
  custody : List Nat
deriving Repr, DecidableEq

/-- The minted world: surface, full light, ways shut, every relic at its home floor. -/
def genesisState : DState :=
  { depth := 0, spent := 0, wounds := 0, fate := 0
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
  | unlock (w : Nat)       -- exercise the carried key-relic to open way w
  | smite                  -- wound the standing floor's guardian (price 2 — it strikes back)
  | loot (r : Nat)         -- take relic r from the standing floor's hoard (guardian slain)
  | flee                   -- surface and bank the pack; the run ends
deriving Repr, DecidableEq

/-- The posted price of a verb in breath. -/
def price : Move → Nat
  | .smite => 2
  | _      => 1

/-- One receipted turn of the descent: `step s m = some s'` iff `m` is LEGAL at `s`.
This function IS the rulebook; everything else is proved about it. -/
def step (s : DState) : Move → Option DState
  | .delve =>
      if s.fate = 0 ∧ s.spent + 1 ≤ BREATH ∧ s.depth < FLOORS
          ∧ wayOpen s (s.depth + 1) = true
          ∧ pack s + (s.depth + 1) ≤ CAP then       -- attenuated carrying rights
        some { s with depth := s.depth + 1, wounds := 0, spent := s.spent + 1 }
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
  | .loot r =>
      if s.fate = 0 ∧ s.spent + 1 ≤ BREATH ∧ 1 ≤ s.depth
          ∧ s.custody[r]? = some s.depth              -- the relic lies HERE
          ∧ s.wounds = guardHp s.depth                -- the guardian is slain
          ∧ pack s + 1 + s.depth ≤ CAP then           -- attenuated carrying rights
        some { s with custody := s.custody.set r CARRIED, spent := s.spent + 1 }
      else none
  | .flee =>
      if s.fate = 0 ∧ s.spent + 1 ≤ BREATH then
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

/-! ## 6. The inductive invariant — the design laws as one package. -/

/-- Custody well-formedness: exactly `RELICS` relics forever (no mint, no burn — the
no-dupe law is STRUCTURAL: a relic is one list entry), every code legal. -/
def CustodyWF (s : DState) : Prop :=
  s.custody.length = RELICS ∧
  ∀ c ∈ s.custody, (1 ≤ c ∧ c ≤ FLOORS) ∨ c = CARRIED ∨ c = BANKED

def Inv (s : DState) : Prop :=
  CustodyWF s
    ∧ s.spent ≤ BREATH
    ∧ s.depth ≤ FLOORS
    ∧ s.fate ≤ 1
    ∧ s.ways.length = FLOORS - 1
    ∧ pack s + s.depth ≤ CAP
    ∧ (s.fate = 0 → bank s = 0)
    ∧ (s.fate = 1 → pack s = 0 ∧ bank s + s.depth ≤ CAP)
    ∧ (s.depth = 0 → pack s = 0 ∧ bank s = 0)
    ∧ (s.custody[0]? = some FLOORS ∨ s.depth = FLOORS)

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
    (Nat.zero_le _), (Nat.zero_le _), (Nat.zero_le _), rfl, ?_, ?_, ?_, ?_,
    Or.inl genesis_prize⟩
  · intro c hc
    exact Or.inl (wf_home_floor hc)
  · show pack genesisState + 0 ≤ CAP
    rw [genesis_pack_zero]; decide
  · intro _; exact genesis_bank_zero
  · intro hf; exact absurd (show (0 : Nat) = 1 from hf) (by decide)
  · intro _; exact ⟨genesis_pack_zero, genesis_bank_zero⟩

/-- **Invariant preservation** — every legal turn preserves the design laws. -/
theorem inv_step {s s' : DState} {m : Move} (hInv : Inv s) (h : step s m = some s') :
    Inv s' := by
  obtain ⟨⟨hlen, hcodes⟩, hspent, hdepth, hfate, hways, hcap, hb0, hb1, hd0, hprize⟩ := hInv
  cases m with
  | delve =>
    simp only [step] at h
    split at h
    case isTrue hcond =>
      obtain ⟨h0, h1, h2, h3, h4⟩ := hcond
      cases h
      refine ⟨⟨hlen, hcodes⟩, ?_, ?_, ?_, hways, ?_, ?_, ?_, ?_, ?_⟩
      · show s.spent + 1 ≤ BREATH; omega
      · show s.depth + 1 ≤ FLOORS; omega
      · exact hfate
      · exact h4
      · intro hf; exact hb0 hf
      · intro hf; exact absurd (show s.fate = 1 from hf) (by omega)
      · intro hd; exact absurd (show s.depth + 1 = 0 from hd) (by omega)
      · rcases hprize with hp | hp
        · exact Or.inl hp
        · exact absurd hp (by omega)
    case isFalse => exact absurd h (by simp)
  | unlock w =>
    simp only [step] at h
    split at h
    case isTrue hcond =>
      obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hcond
      cases h
      refine ⟨⟨hlen, hcodes⟩, ?_, hdepth, hfate, ?_, hcap, ?_, ?_, hd0, ?_⟩
      · show s.spent + 1 ≤ BREATH; omega
      · show (s.ways.set (w - 2) 1).length = FLOORS - 1
        simpa using hways
      · intro hf; exact hb0 hf
      · intro hf; exact absurd (show s.fate = 1 from hf) (by omega)
      · rcases hprize with hp | hp
        · exact Or.inl hp
        · exact Or.inr hp
    case isFalse => exact absurd h (by simp)
  | smite =>
    simp only [step] at h
    split at h
    case isTrue hcond =>
      obtain ⟨h0, h1, h2, h3⟩ := hcond
      cases h
      refine ⟨⟨hlen, hcodes⟩, ?_, hdepth, hfate, hways, hcap, ?_, ?_, hd0, ?_⟩
      · show s.spent + 2 ≤ BREATH; omega
      · intro hf; exact hb0 hf
      · intro hf; exact absurd (show s.fate = 1 from hf) (by omega)
      · rcases hprize with hp | hp
        · exact Or.inl hp
        · exact Or.inr hp
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
      refine ⟨⟨?_, ?_⟩, ?_, hdepth, hfate, hways, ?_, ?_, ?_, ?_, ?_⟩
      · show (s.custody.set r CARRIED).length = RELICS
        simpa using hlen
      · intro c hc
        rcases mem_of_mem_set hc with hcl | hcv
        · exact hcodes c hcl
        · right; left; exact hcv
      · show s.spent + 1 ≤ BREATH; omega
      · show (s.custody.set r CARRIED).countP (· == CARRIED) + s.depth ≤ CAP
        rw [hpackBump]
        exact h5
      · intro _
        show (s.custody.set r CARRIED).countP (· == BANKED) = 0
        rw [hbankSame]; exact hb0 h0
      · intro hf; exact absurd (show s.fate = 1 from hf) (by omega)
      · intro hdz; exact absurd (show s.depth = 0 from hdz) (by omega)
      · rcases hprize with hp | hp
        · by_cases hr0 : r = 0
          · subst hr0
            rw [hp] at h3
            injection h3 with heq
            right
            show s.depth = FLOORS
            omega
          · left
            show (s.custody.set r CARRIED)[0]? = some FLOORS
            rw [List.getElem?_set_ne (by omega)]
            exact hp
        · exact Or.inr hp
    case isFalse => exact absurd h (by simp)
  | flee =>
    simp only [step] at h
    split at h
    case isTrue hcond =>
      obtain ⟨h0, h1⟩ := hcond
      cases h
      have hpack0 : (s.custody.map fleeMap).countP (· == CARRIED) = 0 :=
        countP_fleeMap_carried _
      have hbank : (s.custody.map fleeMap).countP (· == BANKED)
          = s.custody.countP (· == CARRIED) + s.custody.countP (· == BANKED) :=
        countP_fleeMap_banked _
      refine ⟨⟨?_, ?_⟩, ?_, hdepth, ?_, hways, ?_, ?_, ?_, ?_, ?_⟩
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
      · show (s.custody.map fleeMap).countP (· == CARRIED) + s.depth ≤ CAP
        rw [hpack0]; omega
      · intro hf; exact absurd (show (1 : Nat) = 0 from hf) (by omega)
      · intro _
        refine ⟨hpack0, ?_⟩
        show (s.custody.map fleeMap).countP (· == BANKED) + s.depth ≤ CAP
        rw [hbank]
        have hbz := hb0 h0
        simp only [bank] at hbz
        rw [hbz]
        simpa [pack] using hcap
      · intro hdz
        have hdz' : s.depth = 0 := hdz
        obtain ⟨hp, hb⟩ := hd0 hdz'
        refine ⟨hpack0, ?_⟩
        show (s.custody.map fleeMap).countP (· == BANKED) = 0
        rw [hbank]
        simp only [pack] at hp
        simp only [bank] at hb
        rw [hp, hb]
      · rcases hprize with hp | hp
        · left
          show (s.custody.map fleeMap)[0]? = some FLOORS
          rw [List.getElem?_map, hp]
          rfl
        · exact Or.inr hp
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

/-- **Law 2 — descent attenuates capability**: carried relics + depth never exceed CAP. -/
theorem capacity_attenuates {s : DState} (h : Reachable s) :
    pack s + s.depth ≤ CAP :=
  (inv_reachable h).2.2.2.2.2.1

/-- **Law 3a — the light dies**: at `spent = BREATH` no verb is legal. Permadeath is a
theorem, not a timer. -/
theorem the_light_dies {s : DState} (hs : s.spent = BREATH) (m : Move) :
    step s m = none := by
  cases m <;> simp only [step] <;> split <;>
    first
      | rfl
      | (rename_i hc; exact absurd hc.2.1 (by omega))
      | (rename_i hc; exact absurd hc.2 (by omega))

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
  | unlock w =>
    simp only [step] at h; split at h
    · cases h; simp only at hgb; rw [hga] at hgb; cases hgb; omega
    · exact absurd h (by simp)
  | smite =>
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
be banked; the capacity attenuation makes a full clear UNPROVABLE, not merely hard. -/
theorem no_run_banks_everything {s : DState} (h : Reachable s) :
    bank s < RELICS := by
  have hInv := inv_reachable h
  obtain ⟨⟨hlen, _⟩, _, hdepth, hfate, _, hcap, hb0, hb1, hd0, _⟩ := hInv
  by_cases hf : s.fate = 0
  · have := hb0 hf
    simp [RELICS] at *
    omega
  · have hf1 : s.fate = 1 := by omega
    obtain ⟨hp, hb⟩ := hb1 hf1
    by_cases hdz : s.depth = 0
    · have := (hd0 hdz).2
      simp [RELICS] at *
      omega
    · simp [CAP, RELICS] at *
      omega

/-- **The crowned run banks at most half the hoard**: banking THE PRIZE (relic 0)
means the run stood at the bottom, and capacity at the bottom is `CAP − FLOORS = 4`.
Glory costs carrying rights. -/
theorem crowned_bank_le_four {s : DState} (h : Reachable s)
    (hcrown : s.custody[0]? = some BANKED) :
    bank s ≤ CAP - FLOORS := by
  have hInv := inv_reachable h
  obtain ⟨⟨hlen, _⟩, _, hdepth, hfate, _, hcap, hb0, hb1, hd0, hprize⟩ := hInv
  have hdF : s.depth = FLOORS := by
    rcases hprize with hp | hp
    · rw [hcrown] at hp
      simp only [Option.some.injEq] at hp
      simp [BANKED, FLOORS] at hp
    · exact hp
  have hbank1 : 1 ≤ bank s := countP_pos_of_getElem hcrown
  by_cases hf : s.fate = 0
  · have := hb0 hf; omega
  · have hf1 : s.fate = 1 := by omega
    obtain ⟨_, hb⟩ := hb1 hf1
    simp [CAP, FLOORS] at *
    omega

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
it, fell the deep guardian, take the prize, flee. -/
def crownedRun : List Move :=
  ((List.range' 1 FLOORS).flatMap floorLine) ++ [Move.flee]

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

/-- **The tension survives the draw**: every day's perfect line costs at least 20 of the
26 breath, and (by `winsAt_true`) at most all of it. -/
theorem costAt_tense (k : Nat) (hk : k < dayCount) : 20 ≤ costAt k ∧ costAt k ≤ BREATH := by
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

-- Every day of the family, driven end to end (the theorems above, as executable checks).
#guard (List.range dayCount).all winsAt
#guard (List.range dayCount).all (fun k => 20 ≤ costAt k && costAt k ≤ BREATH)
#guard (List.range dayCount).map costAt
        = [24, 26, 22, 24, 24, 22, 22, 24, 22, 24, 22, 24, 20, 20, 22, 24]
-- The days are genuinely different dungeons (no two draws share a map).
#guard ((List.range dayCount).map worldAt).Nodup

/-! ## 10. Day 0 driven — the shipped map still plays exactly as it did. -/

section Canon
local instance : WorldParam := instAt 0

-- The crowned line for the shipped map is the same 18-verb script the file used to
-- hard-code, and it still costs 24 of 26 breath and banks the prize + three keys.
#guard crownedRun =
  [ .delve, .smite, .loot 1, .unlock 2,
    .delve, .smite, .loot 2, .unlock 3,
    .delve, .smite, .smite, .loot 3, .unlock 4,
    .delve, .smite, .smite, .loot 0,
    .flee ]
#guard (replay crownedRun).isSome
#guard (replay crownedRun).map (·.fate) = some 1
#guard (replay crownedRun).map bank = some 4
#guard (replay crownedRun).map (·.spent) = some 24
#guard (replay crownedRun).map (fun s => s.custody[0]?) = some (some BANKED)

-- Illegal moves are REFUSED by the rulebook (driven, not asserted):
-- keyless descent past floor 1 (way 2 shut):
#guard (replay [.delve, .delve]) = none
-- looting under a living guardian:
#guard (replay [.delve, .loot 1]) = none
-- a second unlock of the same way (the way is no longer 0):
#guard (replay [.delve, .smite, .loot 1, .unlock 2, .unlock 2]) = none
-- moving after banking (the frozen tomb):
#guard (replay [.delve, .flee, .delve]) = none
-- fleeing twice:
#guard (replay [.delve, .flee, .flee]) = none

end Canon

/-! ## 11. Axiom hygiene. -/

#assert_axioms capacity_attenuates
#assert_axioms the_light_dies
#assert_axioms run_bounded
#assert_axioms banked_run_frozen
#assert_axioms keyless_unlock_impossible
#assert_axioms custody_ratchet
#assert_axioms no_run_banks_everything
#assert_axioms crowned_bank_le_four
#assert_axioms drawFamily_wf
#assert_axioms winsAt_true
#assert_axioms costAt_tense
#assert_axioms draw_completable
#assert_axioms draw_wf

end Dregg2.Games.Dungeon
