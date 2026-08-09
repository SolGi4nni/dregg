/-
# MultiwayTugFFI — the wire-oracle teeth EVALUATION, out of the crypto archive's build

`MultiwayTugFFI.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 its §7 teeth ran 60 `#guard` wire pins at elaboration — so any game-fixture
regression was a hard failure of every Rust proving target in the workspace. The witness states
(`rowTieState`, `demoCut`, and the model's own `demo`/`undecidedState`/`winState`/`blankState`/
`straddleState`) remain where they were; THIS module is where the pins are RUN — each former
`#guard` as a NAMED theorem per GUARD-DISCIPLINE, proved by `native_decide` and pinned
`#assert_compiled`. Rooted in the central guard library and reachable from `Dregg2.FFI` by
NOTHING, so a plain `lake build` still evaluates every pin while `lake build Dregg2.FFI` never
does. Every pinned expression mentions only PUBLIC names, so the expressions moved verbatim;
the section narratives moved with them.
-/
import Dregg2.Games.MultiwayTugFFI

namespace Dregg2.Games.MultiwayTugFFI

open Dregg2.Games.MultiwayTug

/-! ### The influence table and the round length -/

/-- The influence table is the model's … -/
theorem charm_verb_is_the_influence_table :
    (rulesFFI "charm" == "1 7 2 2 2 3 3 4 5") = true := by native_decide

/-- … and the round is twelve committed turns. -/
theorem turns_verb_is_twelve : (rulesFFI "turns" == "1 12") = true := by native_decide

/-! ### The state codec round-trips the model's own witnesses -/

/-- `act` with an ILLEGAL action (out of turn) is a fail-closed NO-OP, so its reply is the
encoding of the input state. -/
theorem act_refuses_out_of_turn_as_no_op :
    (rulesFFI ("act " ++ encodeState demo ++ " 1 0 4") == "1 " ++ encodeState demo) = true := by
  native_decide

theorem act_on_blank_state_is_a_no_op :
    (rulesFFI ("act " ++ encodeState blankState ++ " 0 0 4")
      == "1 " ++ encodeState blankState) = true := by native_decide

/-- … and `demo`'s own model pin: a card not in hand is a no-op. -/
theorem act_without_the_card_is_a_no_op :
    (rulesFFI ("act " ++ encodeState demo ++ " 0 0 4") == "1 " ++ encodeState demo) = true := by
  native_decide

/-- P1's Gift of `3 3 5` is LEGAL from `demo` (the model's `demo_gift_cut_is_legal`) … -/
theorem gift_cut_is_legal_on_wire :
    (rulesFFI ("legal " ++ encodeState demo ++ " 0 2 3 3 5") == "1 1") = true := by
  native_decide

/-- … and executing it puts the offer in escrow with the seat passed to P2. -/
theorem act_executes_the_gift_cut :
    (rulesFFI ("act " ++ encodeState demo ++ " 0 2 3 3 5")
      == "1 " ++ encodeState demoCut) = true := by native_decide

/-! ### The anti-self-deal tooth and the interlock -/

/-- ⚑ THE ANTI-SELF-DEAL TOOTH. The cutter cannot answer their own cut … -/
theorem anti_self_deal_cutter_refused :
    (rulesFFI ("legalresp " ++ encodeState demoCut ++ " 0 0 0") == "1 0") = true := by
  native_decide

/-- … the other seat can. -/
theorem anti_self_deal_responder_allowed :
    (rulesFFI ("legalresp " ++ encodeState demoCut ++ " 1 0 0") == "1 1") = true := by
  native_decide

/-- THE INTERLOCK: while the offer stands, no ACTION is legal for either seat. -/
theorem interlock_blocks_responder_actions :
    (rulesFFI ("legal " ++ encodeState demoCut ++ " 1 0 1") == "1 0") = true := by native_decide

theorem interlock_blocks_proposer_actions :
    (rulesFFI ("legal " ++ encodeState demoCut ++ " 0 0 3") == "1 0") = true := by native_decide

/-- A response with nothing on the table is refused. -/
theorem response_without_offer_refused :
    (rulesFFI ("legalresp " ++ encodeState demo ++ " 0 0 0") == "1 0") = true := by
  native_decide

/-- A SHAPE-MISMATCHED response (a comp answer to a gift offer) is refused. -/
theorem shape_mismatched_response_refused :
    (rulesFFI ("legalresp " ++ encodeState demoCut ++ " 1 1 0") == "1 0") = true := by
  native_decide

/-! ### `kinds` before and during the offer -/

/-- All four kinds open for the seat to move … -/
theorem kinds_all_open_for_seat_to_move :
    (rulesFFI ("kinds " ++ encodeState demo ++ " 0") == "1 1 1 1 1 0") = true := by
  native_decide

/-- … none for the other … -/
theorem kinds_none_open_for_waiting_seat :
    (rulesFFI ("kinds " ++ encodeState demo ++ " 1") == "1 0 0 0 0 0") = true := by
  native_decide

/-- … during the offer NO kind is open for the proposer … -/
theorem kinds_none_open_during_offer_for_proposer :
    (rulesFFI ("kinds " ++ encodeState demoCut ++ " 0") == "1 0 0 0 0 0") = true := by
  native_decide

/-- … and only the non-proposer's response is. -/
theorem kinds_response_open_for_non_proposer :
    (rulesFFI ("kinds " ++ encodeState demoCut ++ " 1") == "1 0 0 0 0 1") = true := by
  native_decide

/-! ### THE SPLIT TABLE (`takerShare` / `cutterShare`)

The taker takes ONE of a gift's three, the cutter keeps the other two; on a competition the
taker takes a PAIR. -/

theorem split_gift_pick_zero : (rulesFFI "split 1 0 6 0 2 0 0" == "1 6 02") = true := by
  native_decide

theorem split_gift_pick_one : (rulesFFI "split 1 0 6 0 2 0 1" == "1 0 26") = true := by
  native_decide

theorem split_gift_pick_two : (rulesFFI "split 1 0 6 0 2 0 2" == "1 2 06") = true := by
  native_decide

theorem split_comp_pick_zero : (rulesFFI "split 2 0 6 5 1 0 1 0" == "1 56 01") = true := by
  native_decide

theorem split_comp_pick_one : (rulesFFI "split 2 0 6 5 1 0 1 1" == "1 01 56") = true := by
  native_decide

/-- A pick that does not exist on the shape REFUSES (fail-closed, not "share nothing"). -/
theorem split_gift_out_of_range_pick_refused :
    (rulesFFI "split 1 0 6 0 2 0 3" == "0") = true := by native_decide

theorem split_comp_out_of_range_pick_refused :
    (rulesFFI "split 2 0 6 5 1 0 1 2" == "0") = true := by native_decide

/-! ### Conservation over the cut and the answer (`conservation_move`) -/

theorem total_conserved_over_the_cut :
    (rulesFFI ("total " ++ encodeState demo)
      == rulesFFI ("total " ++ encodeState demoCut)) = true := by native_decide

theorem total_conserved_over_cut_and_answer :
    (rulesFFI ("total " ++ encodeState (applyResponse demoCut .p2 (Response.gift 0)))
      == rulesFFI ("total " ++ encodeState demo)) = true := by native_decide

/-! ### The tallies -/

/-- THE SECRET IS SCORED (`secret_is_scored`): a card in the secret pile counts toward its
row. -/
theorem secret_pile_counts_toward_row :
    (rulesFFI ("count " ++ encodeState { blankState with
        secret := fun p => if p = .p1 then ({4} : Multiset Geisha) else 0 } ++ " 0 4")
      == "1 1") = true := by native_decide

theorem secret_pile_controls_row :
    (rulesFFI ("control " ++ encodeState { blankState with
        secret := fun p => if p = .p1 then ({4} : Multiset Geisha) else 0 })
      == "1 7 0 0 0 0 1 0 0") = true := by native_decide

/-- CONTROL goes to whoever placed MORE … -/
theorem control_verb_on_win_state :
    (rulesFFI ("control " ++ encodeState winState) == "1 7 0 0 0 1 0 1 1") = true := by
  native_decide

/-- … an exact tie leaves the row UNCONTROLLED. -/
theorem control_verb_on_blank_state :
    (rulesFFI ("control " ++ encodeState blankState) == "1 7 0 0 0 0 0 0 0") = true := by
  native_decide

/-! ### A THRESHOLD win, where the two objects AGREE -/

/-- `winState` is p1 at 12 charm on 3 rows. -/
theorem score_verb_on_win_state :
    (rulesFFI ("score " ++ encodeState winState) == "1 12 3 0 0") = true := by native_decide

theorem won_verb_on_win_state :
    (rulesFFI ("won " ++ encodeState winState ++ " 0") == "1 1") = true := by native_decide

theorem winner_verb_on_win_state :
    (rulesFFI ("winner " ++ encodeState winState) == "1 1") = true := by native_decide

/-- A GENUINE dead heat is a draw. -/
theorem winner_verb_dead_heat_draws :
    (rulesFFI ("winner " ++ encodeState blankState) == "1 0") = true := by native_decide

/-! ### ⚑ THE CLAUSE, which is what a deployed scoring turn must name

`winState` fires clause 0 (charm threshold, p1); `blankState` clause 8 (dead heat);
`undecidedState` clause 4 (charm LEAD, p1 — no threshold cleared); `rowTieState` clause 7
(charm tied, ROW lead, p2). Clauses 4 and 7 are precisely the ones the deleted Rust could not
reach. `straddleState` is the case where BOTH seats are `Won` — the precedence, not
exclusivity, decides it (clause 0, p1 on charm). -/

theorem branch_verb_win_state_clause_zero :
    (rulesFFI ("branch " ++ encodeState winState) == "1 0 1") = true := by native_decide

theorem branch_verb_blank_state_clause_eight :
    (rulesFFI ("branch " ++ encodeState blankState) == "1 8 0") = true := by native_decide

theorem branch_verb_undecided_state_clause_four :
    (rulesFFI ("branch " ++ encodeState undecidedState) == "1 4 1") = true := by native_decide

theorem branch_verb_row_tie_state_clause_seven :
    (rulesFFI ("branch " ++ encodeState rowTieState) == "1 7 2") = true := by native_decide

theorem branch_verb_straddle_state_clause_zero :
    (rulesFFI ("branch " ++ encodeState straddleState) == "1 0 1") = true := by native_decide

/-- A malformed `branch` wire REFUSES like every other verb. -/
theorem branch_bare_fails_closed : (rulesFFI "branch" == "0") = true := by native_decide

theorem branch_trailing_token_fails_closed :
    (rulesFFI ("branch " ++ encodeState blankState ++ " 0") == "0") = true := by native_decide

/-! ### ⚑⚑ THE PROVENANCE TOOTH — `undecidedState`, the round the Rust twin THREW AWAY

p1 holds rows 5,6 (charm 9, two rows); p2 holds row 3 (charm 3, one row). NEITHER seat clears a
threshold, so `won` is 0 for BOTH (`undecidedState_not_Won`) — and yet the round HAS a winner
(`undecidedState_adjudicates`: `roundWinner = some .p1`). `reference.rs::winner_of` is
`roundWinner` truncated to its four threshold branches, so it answers "no winner" here. The
`won` 0/0 beside the `winner` 1 is what makes a pass evidence about WHICH OBJECT ANSWERED. -/

theorem provenance_undecided_score :
    (rulesFFI ("score " ++ encodeState undecidedState) == "1 9 2 3 1") = true := by
  native_decide

theorem provenance_undecided_not_won_p1 :
    (rulesFFI ("won " ++ encodeState undecidedState ++ " 0") == "1 0") = true := by
  native_decide

theorem provenance_undecided_not_won_p2 :
    (rulesFFI ("won " ++ encodeState undecidedState ++ " 1") == "1 0") = true := by
  native_decide

theorem provenance_undecided_has_a_winner :
    (rulesFFI ("winner " ++ encodeState undecidedState) == "1 1") = true := by native_decide

/-! ### ⚑⚑ THE DEEPEST BRANCH — charm TIES 5-5 and the ROW COUNT decides, for p2

The truncated Rust cannot reach this answer by any input: it has no charm tie-break and no row
tie-break. -/

theorem deepest_branch_row_tie_score :
    (rulesFFI ("score " ++ encodeState rowTieState) == "1 5 1 5 2") = true := by native_decide

theorem deepest_branch_not_won_p1 :
    (rulesFFI ("won " ++ encodeState rowTieState ++ " 0") == "1 0") = true := by native_decide

theorem deepest_branch_not_won_p2 :
    (rulesFFI ("won " ++ encodeState rowTieState ++ " 1") == "1 0") = true := by native_decide

theorem deepest_branch_winner_is_p2 :
    (rulesFFI ("winner " ++ encodeState rowTieState) == "1 2") = true := by native_decide

/-! ### Fail-closed: no verb, an unknown verb, a truncated state, a bad card digit, a
non-digit card, a malformed used-flag field, a trailing token where the grammar ends -/

theorem empty_wire_fails_closed : (rulesFFI "" == "0") = true := by native_decide

theorem unknown_verb_fails_closed : (rulesFFI "bogus" == "0") = true := by native_decide

theorem winner_bare_fails_closed : (rulesFFI "winner" == "0") = true := by native_decide

theorem winner_truncated_state_fails_closed :
    (rulesFFI "winner - - - -" == "0") = true := by native_decide

theorem winner_trailing_token_fails_closed :
    (rulesFFI ("winner " ++ encodeState blankState ++ " 7") == "0") = true := by native_decide

theorem winner_bad_card_digit_fails_closed :
    (rulesFFI "winner - - 7 - - - - - - - 0000 0000 0 0 0" == "0") = true := by native_decide

theorem winner_non_digit_card_fails_closed :
    (rulesFFI "winner - - x - - - - - - - 0000 0000 0 0 0" == "0") = true := by native_decide

theorem winner_bad_used_flag_fails_closed :
    (rulesFFI "winner - - - - - - - - - - 0002 0000 0 0 0" == "0") = true := by native_decide

theorem winner_bad_seat_token_fails_closed :
    (rulesFFI "winner - - - - - - - - - - 0000 0000 0 2 0" == "0") = true := by native_decide

theorem legal_truncated_action_fails_closed :
    (rulesFFI ("legal " ++ encodeState demo ++ " 0 2 3 3") == "0") = true := by native_decide

theorem legal_bad_action_tag_fails_closed :
    (rulesFFI ("legal " ++ encodeState demo ++ " 0 9 3 3 5") == "0") = true := by native_decide

#assert_compiled charm_verb_is_the_influence_table
#assert_compiled turns_verb_is_twelve
#assert_compiled act_refuses_out_of_turn_as_no_op
#assert_compiled act_on_blank_state_is_a_no_op
#assert_compiled act_without_the_card_is_a_no_op
#assert_compiled gift_cut_is_legal_on_wire
#assert_compiled act_executes_the_gift_cut
#assert_compiled anti_self_deal_cutter_refused
#assert_compiled anti_self_deal_responder_allowed
#assert_compiled interlock_blocks_responder_actions
#assert_compiled interlock_blocks_proposer_actions
#assert_compiled response_without_offer_refused
#assert_compiled shape_mismatched_response_refused
#assert_compiled kinds_all_open_for_seat_to_move
#assert_compiled kinds_none_open_for_waiting_seat
#assert_compiled kinds_none_open_during_offer_for_proposer
#assert_compiled kinds_response_open_for_non_proposer
#assert_compiled split_gift_pick_zero
#assert_compiled split_gift_pick_one
#assert_compiled split_gift_pick_two
#assert_compiled split_comp_pick_zero
#assert_compiled split_comp_pick_one
#assert_compiled split_gift_out_of_range_pick_refused
#assert_compiled split_comp_out_of_range_pick_refused
#assert_compiled total_conserved_over_the_cut
#assert_compiled total_conserved_over_cut_and_answer
#assert_compiled secret_pile_counts_toward_row
#assert_compiled secret_pile_controls_row
#assert_compiled control_verb_on_win_state
#assert_compiled control_verb_on_blank_state
#assert_compiled score_verb_on_win_state
#assert_compiled won_verb_on_win_state
#assert_compiled winner_verb_on_win_state
#assert_compiled winner_verb_dead_heat_draws
#assert_compiled branch_verb_win_state_clause_zero
#assert_compiled branch_verb_blank_state_clause_eight
#assert_compiled branch_verb_undecided_state_clause_four
#assert_compiled branch_verb_row_tie_state_clause_seven
#assert_compiled branch_verb_straddle_state_clause_zero
#assert_compiled branch_bare_fails_closed
#assert_compiled branch_trailing_token_fails_closed
#assert_compiled provenance_undecided_score
#assert_compiled provenance_undecided_not_won_p1
#assert_compiled provenance_undecided_not_won_p2
#assert_compiled provenance_undecided_has_a_winner
#assert_compiled deepest_branch_row_tie_score
#assert_compiled deepest_branch_not_won_p1
#assert_compiled deepest_branch_not_won_p2
#assert_compiled deepest_branch_winner_is_p2
#assert_compiled empty_wire_fails_closed
#assert_compiled unknown_verb_fails_closed
#assert_compiled winner_bare_fails_closed
#assert_compiled winner_truncated_state_fails_closed
#assert_compiled winner_trailing_token_fails_closed
#assert_compiled winner_bad_card_digit_fails_closed
#assert_compiled winner_non_digit_card_fails_closed
#assert_compiled winner_bad_used_flag_fails_closed
#assert_compiled winner_bad_seat_token_fails_closed
#assert_compiled legal_truncated_action_fails_closed
#assert_compiled legal_bad_action_tag_fails_closed

end Dregg2.Games.MultiwayTugFFI
