/-
# Metatheory.PolisSandboxUnifiedAttack — the UNIFIED world withstands ALL adaptive attacks.

`PolisSandboxAdaptive` ran an adaptive searcher against ONE lever (foreclosure / reach-home) and
proved the viability governor withstands attacks of any depth. This module does the same against the
RICHEST world — `PolisSandboxUnified`'s three simultaneous levers (foreclosure ∧ laundering ∧
hoarding) under its ONE combined governor.

An adaptive attacker SEARCHES the unified move space (every actor × every action) for *any* ≤ `d`-round
governed sequence that breaks the combined floor on ANY axis:
  * `existsHarmAttack govStep d w` — true iff some governed sequence reaches a floor-broken state;
  * `existsHarmAttack stepMove d w` — the SAME search with the governor removed (raw step): the
    attacker walks straight to a break (`raw_search_finds_attack`).

The contrast is the point. With the governor in the step, the search returns `false` forever:
  * `unifiedGov_preserves` — the combined governor preserves the WHOLE combined floor (it is exactly
    `PolisSandboxUnified.govStep_preserves`, restated here for the searcher);
  * `unified_withstands_all_attacks` — by induction over depth (the `viability_withstands_all_attacks`
    shape), NO adaptive attack of ANY depth breaks ANY of the three leverage axes under the combined
    governor. Stronger than any bounded `decide`: it quantifies over every attack tree.

Honest scope: a small finite world (two `Bool` agents, `decide`-cheap); the adversary is a scripted /
bounded Lean searcher exhaustively enumerating the move space, not an LLM — but it genuinely explores
every actor×action at every step, and the governance is proven universal over those trees. No `sorry`,
no load-bearing `True`.
-/
import Metatheory.PolisSandboxUnified

namespace Metatheory.PolisSandboxUnifiedAttack

open Metatheory.PolisSandboxUnified

/-- Every action the attacker can try (the full `Act` vocabulary, including the three abuses). The
victim of a `trap` is enumerated over both agents. -/
def atkActs : List Act :=
  [.noop, .stepHome, .earnTier, .claim, .contribute, .trap false, .trap true, .launder, .hoard]

/-- Every move the attacker can propose: each actor × each action. The searcher explores ALL of them. -/
def atkMoves : List Move :=
  (atkActs.map (fun a => (⟨false, a⟩ : Move))) ++ (atkActs.map (fun a => (⟨true, a⟩ : Move)))

/-- The combined floor is broken (Bool view of `¬ worldFloor`). -/
def broken (w : World) : Bool := ! decide (worldFloor w)

/-- The adaptive attacker, parametric in the step rule `step` (so we can run it with the governed
`govStep` or the raw `stepMove`): does SOME sequence of ≤ `d` rounds reach a floor-broken state? It
explores every move at every step — an exhaustive search, not a script. -/
def existsHarmAttack (step : World → Move → World) : Nat → World → Bool
  | 0, w => broken w
  | d + 1, w => broken w || atkMoves.any (fun m => existsHarmAttack step d (step w m))

-- WITHOUT the governor (raw step), the search walks straight to a break:
#eval existsHarmAttack stepMove 1 w0    -- true
-- WITH the combined governor, the search finds NOTHING at this (or any) depth:
#eval existsHarmAttack govStep 4 w0     -- false

/-- **`raw_search_finds_attack`** — with the governor removed, the adaptive search discovers a
floor-breaking move in a single round (e.g. a `trap`, a `launder`, or a `hoard` breaks the combined
floor immediately). The baseline: harm is reachable when no envelope guards the step. -/
theorem raw_search_finds_attack : existsHarmAttack stepMove 1 w0 = true := by decide

/-- **`unified_search_finds_none`** — the same exhaustive search finds no attack on the combined
governor: no actor×action sequence breaks any of the three axes. (Stated at depth 1 so the `decide`
stays cheap; the all-depth result below is `unified_withstands_from_genesis`, which subsumes it for
every depth without a heartbeat budget.) -/
theorem unified_search_finds_none : existsHarmAttack govStep 1 w0 = false := by decide

/-! ## The strong result: the combined governor withstands attacks of ANY depth. -/

/-- The combined governor PRESERVES the whole combined floor: from any world where all three axes hold,
after any governed move every axis still holds. (This is `PolisSandboxUnified.govStep_preserves`, the
load-bearing fact the searcher needs.) -/
theorem unifiedGov_preserves (w : World) (m : Move) (h : worldFloor w) :
    worldFloor (govStep w m) := govStep_preserves w m h

/-- `broken` is exactly the Bool reflection of "the combined floor fails". So when the floor holds,
nothing is broken. -/
theorem broken_eq_false_of_floor (w : World) (h : worldFloor w) : broken w = false := by
  simp [broken, decide_eq_true (by exact h)]

/-- **`unified_withstands_all_attacks` — the combined governor is provably attack-proof.** From any
world where the combined floor holds, NO adaptive attack of ANY depth breaks ANY of the three leverage
axes (foreclosure, laundering, hoarding): the exhaustive search returns `false` forever. Stronger than
any bounded `decide` — it quantifies over every attack tree the searcher could ever explore, because
the combined governor preserves the whole floor at every governed step. -/
theorem unified_withstands_all_attacks (d : Nat) (w : World) (h : worldFloor w) :
    existsHarmAttack govStep d w = false := by
  induction d generalizing w with
  | zero => simp [existsHarmAttack, broken_eq_false_of_floor w h]
  | succ k ih =>
      have hb : broken w = false := broken_eq_false_of_floor w h
      show (broken w || atkMoves.any (fun m => existsHarmAttack govStep k (govStep w m))) = false
      rw [hb, Bool.false_or]
      -- every governed successor still satisfies the floor, so the IH kills every disjunct
      apply List.any_eq_false.mpr
      intro m _
      simp [ih (govStep w m) (unifiedGov_preserves w m h)]

/-- A corollary the searcher's `false` answers now MEAN something universal: depth-4 is not a lucky
bound. Whatever depth the parent picks, the governed search is `false` from genesis. -/
theorem unified_withstands_from_genesis (d : Nat) : existsHarmAttack govStep d w0 = false :=
  unified_withstands_all_attacks d w0 genesis_floor_holds

end Metatheory.PolisSandboxUnifiedAttack
