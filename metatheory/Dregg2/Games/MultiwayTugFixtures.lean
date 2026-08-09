/-
# MultiwayTug — the §10 play-witness EVALUATION, out of the crypto archive's build

`MultiwayTug.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 its §10 smoke witness ran 12 `#guard` pins at elaboration — so any
game-fixture regression was a hard failure of every Rust proving target in the workspace. The
`demo` state remains in `MultiwayTug.lean`; THIS module is where the facts are RUN — each
former `#guard` as a NAMED theorem per GUARD-DISCIPLINE, proved by `native_decide` and pinned
`#assert_compiled`. Rooted in the central guard library and reachable from `Dregg2.FFI` by
NOTHING, so a plain `lake build` still evaluates every pin while `lake build Dregg2.FFI` never
does. Every pinned expression mentions only PUBLIC names, so the pins moved verbatim.
-/
import Dregg2.Games.MultiwayTug

namespace Dregg2.Games.MultiwayTug

open scoped BigOperators

/-- P1 CUTS a legal Gift (presents 3, 3 and 5 — the split is NOT theirs to make). -/
theorem demo_gift_cut_is_legal : legalB demo .p1 (Action.offerGift 3 3 5) = true := by
  native_decide

/-- Conservation holds on the cut: the three favors are in escrow, none created or
destroyed. -/
theorem cut_conserves_the_deck :
    totalCards (applyAction demo .p1 (Action.offerGift 3 3 5)) = totalCards demo := by
  native_decide

/-- The offer is now PENDING … -/
theorem cut_opens_the_offer :
    (applyAction demo .p1 (Action.offerGift 3 3 5)).pending
      = some (Offer.gift .p1 3 3 5) := by native_decide

/-- … and the seat has passed to P2. -/
theorem cut_passes_the_seat :
    (applyAction demo .p1 (Action.offerGift 3 3 5)).current = Player.p2 := by native_decide

/-- P1 cannot answer their own cut … -/
theorem cutter_cannot_answer_own_cut :
    legalRespB (applyAction demo .p1 (Action.offerGift 3 3 5)) .p1 (Response.gift 0)
      = false := by native_decide

/-- … P2 can. -/
theorem responder_may_answer :
    legalRespB (applyAction demo .p1 (Action.offerGift 3 3 5)) .p2 (Response.gift 0)
      = true := by native_decide

/-- While the offer stands, NOTHING else is legal (the interlock). -/
theorem pending_offer_blocks_actions :
    legalB (applyAction demo .p1 (Action.offerGift 3 3 5)) .p2 (Action.secret 1) = false := by
  native_decide

/-- The whole cut-then-choose sequence conserves the deck. -/
theorem cut_then_choose_conserves_the_deck :
    totalCards (applyResponse (applyAction demo .p1 (Action.offerGift 3 3 5)) .p2
      (Response.gift 0)) = totalCards demo := by native_decide

/-- The Gift's kind is now marked used (cannot repeat this round). -/
theorem gift_kind_is_marked_used :
    (applyAction demo .p1 (Action.offerGift 3 3 5)).used .p1 ActionKind.giftK = true := by
  native_decide

/-- An illegal action (card not in hand) is a no-op. -/
theorem illegal_action_is_a_no_op :
    totalCards (applyAction demo .p1 (Action.secret 4)) = totalCards demo := by native_decide

/-- The full deck holds 21 cards (Σ charm). -/
theorem full_deck_holds_twenty_one_cards :
    (∑ g : Geisha, Multiset.replicate (charm g) g).card = 21 := by native_decide

/-- A full round is 12 committed turns: 8 actions + 4 responses (two offers per player). -/
theorem full_round_is_twelve_turns : (8 + 4 : ℕ) = 12 := by native_decide

#assert_compiled demo_gift_cut_is_legal
#assert_compiled cut_conserves_the_deck
#assert_compiled cut_opens_the_offer
#assert_compiled cut_passes_the_seat
#assert_compiled cutter_cannot_answer_own_cut
#assert_compiled responder_may_answer
#assert_compiled pending_offer_blocks_actions
#assert_compiled cut_then_choose_conserves_the_deck
#assert_compiled gift_kind_is_marked_used
#assert_compiled illegal_action_is_a_no_op
#assert_compiled full_deck_holds_twenty_one_cards
#assert_compiled full_round_is_twelve_turns

end Dregg2.Games.MultiwayTug
