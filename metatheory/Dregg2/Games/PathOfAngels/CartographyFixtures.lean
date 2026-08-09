/-
# Cartography — the fixture EVALUATION, out of the crypto archive's build

`Cartography.lean` sits in the `Dregg2.FFI` closure (the crypto archive's build root), and
until 2026-08-08 it ran twenty-three `native_decide` evaluations at elaboration — two whole
expedition replays, six observation draws, two catalogue validations and eleven notebook
pins — so a game-fixture regression was a hard failure of every Rust proving target in the
workspace (the compilation-unit coupling the stale-fixture outage measured).  The
STATEMENTS remain in `Cartography.lean` as evaluation-free `check_* : Bool` definitions,
beside the receipts and catalogues they are stated over; THIS module is where they are RUN.
It is rooted in the `PathOfAngelsGuards` library and reachable from `Dregg2.FFI` by
NOTHING, so:

  * a plain `lake build` still evaluates every pin — no loss of checking;
  * `lake build Dregg2.FFI` (what `dregg-lean-ffi/build.rs` and the seed scripts run) never
    does — a red pin here can no longer take the archive down.

Each theorem keeps the name the in-module `#assert_compiled` census used, so the
fully-qualified names are unchanged.  The fail-closed convention transfers: a check whose
prerequisite judgement refuses answers `false`, so a broken prerequisite reds THIS module.

⚠ Four proofs did NOT move.  `playerA_receipt_exists` / `playerB_receipt_exists` are
required as DATA by `receiptA` / `receiptB` (`Option.get`), and
`DeckExpedition.ExtractionReceipt` has a private constructor, so no fallback is
constructible; `fixture_config_valid` / `reordered_catalogue_config_valid` are the
`Config` validity proofs the fixture configs carry as data.  They are the named residue;
the fixtures header in `Cartography.lean` records it.
-/
import Dregg2.Games.PathOfAngels.Cartography

namespace Dregg2.Games.PathOfAngels.Cartography

set_option autoImplicit false

theorem fixture_receipted_observations_exist :
    check_fixture_receipted_observations_exist = true := by native_decide

theorem fixture_cooperative_revision_publishes :
    check_fixture_cooperative_revision_publishes = true := by native_decide

theorem fixture_max_player_counter_refuses_publication :
    check_fixture_max_player_counter_refuses_publication = true := by native_decide

theorem fixture_reordered_play_has_same_community_map :
    check_fixture_reordered_play_has_same_community_map = true := by native_decide

theorem fixture_separate_revisions_normalize_cross_claim_dispute :
    check_fixture_separate_revisions_normalize_cross_claim_dispute = true := by native_decide

theorem fixture_catalogue_digest_moves_with_observation_order :
    check_fixture_catalogue_digest_moves_with_observation_order = true := by native_decide

theorem fixture_cross_catalogue_session_replay_refuses :
    check_fixture_cross_catalogue_session_replay_refuses = true := by native_decide

theorem fixture_phantom_objects_refuse :
    check_fixture_phantom_objects_refuse = true := by native_decide

theorem fixture_replays_weak_links_and_early_publish_refuse :
    check_fixture_replays_weak_links_and_early_publish_refuse = true := by native_decide

theorem fixture_duplicate_origin_fact_refuses :
    check_fixture_duplicate_origin_fact_refuses = true := by native_decide

theorem fixture_wrong_federation_provenance_refuses :
    check_fixture_wrong_federation_provenance_refuses = true := by native_decide

/-- The authored catalogue really holds all six receipt-derived observations, not a short
list `filterMap id` silently produced.  This is the pin that makes the fail-closed
`filterMap` in `fixtureObservations` observable HERE as well as through
`fixture_config_valid`. -/
theorem fixture_catalogue_holds_all_six_observations :
    fixtureObservations.length = 6 := by native_decide

#assert_compiled fixture_receipted_observations_exist
#assert_compiled fixture_cooperative_revision_publishes
#assert_compiled fixture_max_player_counter_refuses_publication
#assert_compiled fixture_reordered_play_has_same_community_map
#assert_compiled fixture_separate_revisions_normalize_cross_claim_dispute
#assert_compiled fixture_catalogue_digest_moves_with_observation_order
#assert_compiled fixture_cross_catalogue_session_replay_refuses
#assert_compiled fixture_phantom_objects_refuse
#assert_compiled fixture_replays_weak_links_and_early_publish_refuse
#assert_compiled fixture_duplicate_origin_fact_refuses
#assert_compiled fixture_wrong_federation_provenance_refuses
#assert_compiled fixture_catalogue_holds_all_six_observations

end Dregg2.Games.PathOfAngels.Cartography
