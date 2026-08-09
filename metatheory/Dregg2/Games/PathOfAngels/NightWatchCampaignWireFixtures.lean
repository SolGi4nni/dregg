/-
# NightWatch campaign wire — the teeth's EVALUATION, out of the crypto archive's build

`NightWatchCampaignWire.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build
root), and until 2026-08-08 its teeth ran twenty `native_decide` pins at elaboration — each end
to end over the exported judge, through a Poseidon2 slot commitment and a real SHA-256 of the
manifest — so any fixture regression was a hard failure of every Rust proving target in the
workspace (the compilation-unit coupling the stale-fixture outage measured). Seventeen of them
are HERE; their STATEMENTS stay in `NightWatchCampaignWire.lean` as evaluation-free
`check_* : Bool` definitions. This module is rooted in the `PathOfAngelsGuards` library and
reachable from `Dregg2.FFI` by NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.

⚠ **Named residue, THREE — they did NOT move.** `NightWatchCampaign.Activation.mk` and
`State.mk` are `private`, so `fixtureActivation`, `fixtureStateA` and `fixtureStateB` take their
witnesses as DATA through `Option.get` and no fail-closed fallback value exists;
`fixtureStateA` is additionally consumed outside the module (`CanonicalCodecHealthWire`), so it
cannot become an `Option`. `the_authenticated_path_reaches_an_activation`,
`fixture_claim_with_nullifier_A_reaches_a_state` and
`fixture_claim_with_nullifier_B_reaches_a_state` therefore stay `native_decide` in the parent,
where its lab header records them.

⚠ `state_view_erases_the_consumed_nullifier_ledger` and `no_state_view_decoder_can_be_sound`
are reproduced below VERBATIM — statements and proofs unchanged — because the corollary's only
proof is the fixture pin, and leaving it in the parent would have kept a `native_decide` in the
archive's build for no gain.

⚠ Budget: these pins run Poseidon2 sponges and SHA-256 over manifest bytes — minutes, not
seconds.
-/
import Dregg2.Games.PathOfAngels.NightWatchCampaignWire

namespace Dregg2.Games.PathOfAngels.NightWatchCampaignWire

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.NightWatchCampaignAdmission

set_option autoImplicit false

theorem error_names_are_pairwise_distinct :
    check_error_names_are_pairwise_distinct = true := by native_decide

theorem fixture_command_round_trips_through_the_wire :
    check_fixture_command_round_trips_through_the_wire = true := by native_decide

theorem fixture_input_round_trips_through_the_wire :
    check_fixture_input_round_trips_through_the_wire = true := by native_decide

theorem command_with_unknown_action_kind_refuses :
    check_command_with_unknown_action_kind_refuses = true := by native_decide

theorem command_with_unknown_field_refuses :
    check_command_with_unknown_field_refuses = true := by native_decide

theorem command_with_reordered_keys_refuses :
    check_command_with_reordered_keys_refuses = true := by native_decide

theorem command_with_uppercase_digest_refuses :
    check_command_with_uppercase_digest_refuses = true := by native_decide

theorem judge_publishes_the_accepted_state_view :
    check_judge_publishes_the_accepted_state_view = true := by native_decide

theorem judge_publishes_the_wrong_sequence_refusal :
    check_judge_publishes_the_wrong_sequence_refusal = true := by native_decide

theorem judge_replays_the_history_and_refuses_a_spent_nullifier :
    check_judge_replays_the_history_and_refuses_a_spent_nullifier = true := by native_decide

theorem judgeFFI_returns_empty_on_undecodable_bytes :
    check_judgeFFI_returns_empty_on_undecodable_bytes = true := by native_decide

theorem a_fraudulent_rulebook_is_no_longer_judged :
    check_a_fraudulent_rulebook_is_no_longer_judged = true := by native_decide

theorem a_forged_manifest_needs_a_forged_world :
    check_a_forged_manifest_needs_a_forged_world = true := by native_decide

theorem a_run_drawn_under_the_wrong_secret_is_not_judged :
    check_a_run_drawn_under_the_wrong_secret_is_not_judged = true := by native_decide

theorem a_run_claiming_another_slot_is_not_judged :
    check_a_run_claiming_another_slot_is_not_judged = true := by native_decide

theorem a_run_owned_by_an_unseated_key_is_not_judged :
    check_a_run_owned_by_an_unseated_key_is_not_judged = true := by native_decide

/-- Two states reached by the same command with different nullifiers are DISTINCT — their
`consumedActions` differ — and publish the SAME view. -/
theorem state_view_erases_the_consumed_nullifier_ledger :
    fixtureStateA ≠ fixtureStateB ∧
      StateViewWire.ofState fixtureStateA = StateViewWire.ofState fixtureStateB := by
  native_decide

/-- `ofState` is not injective, so the corollary is unconditional: no decoder from the
published view back to a `State` can be sound.  This is why there is no `parseStateView`, and
it is refutable — put the nullifier set in the view and the first conjunct of the pin above
stays true while the second goes red. -/
theorem no_state_view_decoder_can_be_sound
    (decode : StateViewWire → Option NightWatchCampaign.State)
    (sound : ∀ state : NightWatchCampaign.State,
      decode (StateViewWire.ofState state) = some state) : False := by
  obtain ⟨distinct, sameView⟩ := state_view_erases_the_consumed_nullifier_ledger
  refine distinct (Option.some.inj ?_)
  rw [← sound fixtureStateA, ← sound fixtureStateB, sameView]

#assert_compiled error_names_are_pairwise_distinct
#assert_compiled fixture_command_round_trips_through_the_wire
#assert_compiled fixture_input_round_trips_through_the_wire
#assert_compiled command_with_unknown_action_kind_refuses
#assert_compiled command_with_unknown_field_refuses
#assert_compiled command_with_reordered_keys_refuses
#assert_compiled command_with_uppercase_digest_refuses
#assert_compiled judge_publishes_the_accepted_state_view
#assert_compiled judge_publishes_the_wrong_sequence_refusal
#assert_compiled judge_replays_the_history_and_refuses_a_spent_nullifier
#assert_compiled judgeFFI_returns_empty_on_undecodable_bytes
#assert_compiled a_fraudulent_rulebook_is_no_longer_judged
#assert_compiled a_forged_manifest_needs_a_forged_world
#assert_compiled a_run_drawn_under_the_wrong_secret_is_not_judged
#assert_compiled a_run_claiming_another_slot_is_not_judged
#assert_compiled a_run_owned_by_an_unseated_key_is_not_judged
#assert_compiled state_view_erases_the_consumed_nullifier_ledger
#assert_compiled no_state_view_decoder_can_be_sound

end Dregg2.Games.PathOfAngels.NightWatchCampaignWire
