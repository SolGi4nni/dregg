/-
# Automatafl — the §8 non-vacuity-witness EVALUATION, out of the crypto archive's build

`Automatafl.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and until
2026-08-08 its §8 witnesses ran 18 `#guard` pins at elaboration — so any game-fixture
regression was a hard failure of every Rust proving target in the workspace. The witness boards
and moves remain in `Automatafl.lean`; THIS module is where the facts are RUN — each former
`#guard` as a NAMED theorem per GUARD-DISCIPLINE, proved by `native_decide` and pinned
`#assert_compiled`. Rooted in the central guard library and reachable from `Dregg2.FFI` by
NOTHING, so a plain `lake build` still evaluates every pin while `lake build Dregg2.FFI` never
does. Every pinned expression mentions only PUBLIC names, so the pins moved verbatim.

`Automatafl.lean` is deliberately prelude-only, so `Dregg2.Tactics` (for `#assert_compiled`)
is imported here, not there.
-/
import Dregg2.Games.Automatafl
import Dregg2.Tactics

namespace Dregg2.Games.Automatafl

/-! ### The Daemon's step on the demo board -/

/-- The attractor is seen two steps north (dist 2, room to move): the Daemon steps north. -/
theorem demo_step_moves_north : (automatonStep demoBoard).automaton = (⟨2, 3⟩ : Coord) := by
  native_decide

theorem demo_step_places_automaton :
    (automatonStep demoBoard).cellAt ⟨2, 3⟩ = Particle.automaton := by native_decide

theorem demo_step_vacates_old_square :
    (automatonStep demoBoard).cellAt ⟨2, 2⟩ = Particle.vacuum := by native_decide

/-- The attractor is untouched by the Daemon's step. -/
theorem demo_step_leaves_attractor :
    (automatonStep demoBoard).cellAt ⟨2, 4⟩ = Particle.attractor := by native_decide

/-- The Daemon flees the repulsor north (FromRepulsor). -/
theorem rep_step_flees_north : (automatonStep repBoard).automaton = (⟨2, 3⟩ : Coord) := by
  native_decide

/-! ### Move resolution and the full turn -/

theorem demo_move_is_valid : moveValidB moveBoard demoMove = true := by native_decide

theorem demo_move_places_attractor :
    (applyMoves moveBoard [demoMove]).cellAt ⟨0, 3⟩ = Particle.attractor := by native_decide

theorem demo_move_vacates_source :
    (applyMoves moveBoard [demoMove]).cellAt ⟨0, 0⟩ = Particle.vacuum := by native_decide

/-- A full turn: the piece moves, then the Daemon (no opposing pair / repulsor in range from
the corner) does not move. -/
theorem full_turn_keeps_the_moved_piece :
    (applyTurn moveBoard [demoMove]).cellAt ⟨0, 3⟩ = Particle.attractor := by native_decide

/-! ### Validity teeth (non-vacuous both polarities)

(Moves are written with the anonymous constructor `⟨who, frm, to⟩` — Mathlib's token table,
imported here via `Dregg2.Tactics`, makes `to := …` in structure-instance syntax unparseable;
the prelude-only parent could use the named form.) -/

/-- from = to. -/
theorem same_square_move_invalid :
    moveValidB moveBoard ⟨0, ⟨0, 0⟩, ⟨0, 0⟩⟩ = false := by native_decide

/-- Not rook-aligned. -/
theorem off_axis_move_invalid :
    moveValidB moveBoard ⟨0, ⟨0, 0⟩, ⟨1, 3⟩⟩ = false := by native_decide

/-- Source is the Automaton. -/
theorem automaton_source_move_invalid :
    moveValidB moveBoard ⟨0, ⟨4, 4⟩, ⟨4, 0⟩⟩ = false := by native_decide

/-- Destination out of bounds. -/
theorem out_of_bounds_move_invalid :
    moveValidB moveBoard ⟨0, ⟨0, 0⟩, ⟨0, 9⟩⟩ = false := by native_decide

/-! ### Conflict detection -/

/-- Two distinct destinations from one source = a fork conflict, so both moves are dropped … -/
theorem fork_conflict_drops_both_moves :
    conflictResolve moveBoard [forkA, forkB] = ([] : List Move) := by native_decide

/-- … and the piece stays. -/
theorem fork_conflict_leaves_piece_put :
    (applyMoves moveBoard (conflictResolve moveBoard [forkA, forkB])).cellAt ⟨0, 0⟩
      = Particle.attractor := by native_decide

/-! ### Win-check -/

/-- The Automaton on a goal wins … -/
theorem winner_on_goal_square : winner demoBoard [(⟨2, 2⟩, 7)] = some 7 := by native_decide

/-- … off a goal, no win. -/
theorem no_winner_off_goal : winner demoBoard [(⟨0, 0⟩, 7)] = none := by native_decide

/-- Steps onto the goal → win. -/
theorem step_onto_goal_wins : hasWon (automatonStep demoBoard) [(⟨2, 3⟩, 3)] = true := by
  native_decide

#assert_compiled demo_step_moves_north
#assert_compiled demo_step_places_automaton
#assert_compiled demo_step_vacates_old_square
#assert_compiled demo_step_leaves_attractor
#assert_compiled rep_step_flees_north
#assert_compiled demo_move_is_valid
#assert_compiled demo_move_places_attractor
#assert_compiled demo_move_vacates_source
#assert_compiled full_turn_keeps_the_moved_piece
#assert_compiled same_square_move_invalid
#assert_compiled off_axis_move_invalid
#assert_compiled automaton_source_move_invalid
#assert_compiled out_of_bounds_move_invalid
#assert_compiled fork_conflict_drops_both_moves
#assert_compiled fork_conflict_leaves_piece_put
#assert_compiled winner_on_goal_square
#assert_compiled no_winner_off_goal
#assert_compiled step_onto_goal_wins

end Dregg2.Games.Automatafl
