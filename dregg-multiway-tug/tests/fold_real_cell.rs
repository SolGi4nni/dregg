//! **THE FOLD FOLDS OVER THE REAL WORLDCELL CELL** — not a `pk[0]=7` fixture.
//!
//! The mannequin this closes: the Phase-3 fold minted every leg over a synthetic
//! `producer_cell` (pk[0]=7, balance 1000, identical for every match), so a game's published
//! win root was a genuine commitment but was NOT welded to the actual cell's heap state. Here
//! the terminal win folds over the game's OWN committed cell (`WorldCell::cell_snapshot`),
//! carrying its real pk / balance / heap — the winner it publishes is a register the cell's
//! v9 commitment (`old8`/`new8`, the deployed state-binding prefix) actually commits.
//!
//! The FAST battery drives the weld without a STARK: the real cell's commitment differs from
//! the fixture's, moves with the committed winner, and the win leaf's public-input commitment
//! moves when its `[old8 ‖ new8]` prefix is the real cell's vs the fixture's. The SLOW
//! `#[ignore]` fold mints the deployed recursion artifact and `verify_history` accepts it.
//!
//! The winner weld itself is DEPLOYED at the WorldCell executor: `tests/round.rs`'s
//! `false_win_claim_is_refused` shows a false winner (meeting neither threshold) is refused at
//! the `score` admission by the installed `winner==p ⇒ charm_p>=11 OR guilds_p>=4` implication
//! — so a fold never receives a cell whose committed winner did not win.
//!
//! `winning_game` now drives 12 committed turns, not 8: the round is 8 actions plus the 4
//! RESPONSES that place the escrow, each under the Lean-emitted `respond_gift`/`respond_comp`
//! case. Nothing about the fold itself changed.

use dregg_cell::program::field_from_u64;
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
use dregg_multiway_tug::fold::{cell_wire_commit8, fixture_wire_commit8, win_leaf_bound};
use dregg_multiway_tug::game::MultiwayTug;
use dregg_multiway_tug::reference::{Engine, greedy_policy, play_round};

/// Play a full round on the real executor to a winner whose CHARM crossed the threshold
/// (`>= 11`), returning the deployed game + `(charm, winner)`. The win was committed via the
/// real `score` turn, so the installed win implication already gated it.
fn winning_game() -> (MultiwayTug, u64, u64) {
    let seed = (0u8..=255)
        .find(|&s| {
            let (mut e, _) = play_round(s as u64);
            if e.score().expect("the Lean oracle adjudicates").is_some() {
                let p = e.projection();
                p.winner != 0 && p.charm[(p.winner - 1) as usize] >= 11
            } else {
                false
            }
        })
        .expect("a seed yields a winner over the charm threshold");

    let mut eng = Engine::new(seed as u64);
    let game = MultiwayTug::deploy(seed).expect("deploy");
    game.seed(&eng.projection()).expect("genesis seeds");
    while !eng.round_complete() {
        let p = eng.current_player();
        let d = greedy_policy(&eng);
        let mv = eng.apply(p, d).expect("the policy plays legally");
        let proj = eng.projection();
        game.commit_projection(mv.method(), &proj)
            .expect("legal play commits");
    }
    eng.score().expect("the Lean oracle adjudicates");
    let scored = eng.projection();
    game.commit_score(&scored).expect("scoring commits");
    let winner = scored.winner;
    let charm = scored.charm[(winner - 1) as usize];
    assert!(
        charm >= 11,
        "the folded winner really crossed the threshold"
    );
    (game, charm, winner)
}

/// The fold's cell is the REAL WorldCell cell — its balance and v9 commitment are NOT the
/// `pk[0]=7`, balance-1000 fixture's.
#[test]
fn folds_over_the_real_cell_not_the_fixture() {
    let (game, _charm, _winner) = winning_game();
    let real = game.world().cell_snapshot().expect("the world-cell exists");

    assert_ne!(
        real.state.balance(),
        1000,
        "the real world-cell balance is not the fixture's 1000"
    );
    let real_commit = cell_wire_commit8(&real);
    assert_ne!(
        real_commit,
        fixture_wire_commit8(),
        "the real cell's v9 commitment must differ from the pk[0]=7 fixture's — the fold no \
         longer folds over a synthetic cell"
    );
}

/// The real cell's commitment REFLECTS the committed winner: overwrite the `winner` register on
/// a clone and the v9 commitment moves. So `old8/new8` (welded to the leg by the deployed
/// state-binding node) genuinely carry the winner the game recorded.
#[test]
fn the_cell_commitment_reflects_the_committed_winner() {
    let (game, _charm, winner) = winning_game();
    let real = game.world().cell_snapshot().expect("cell");
    let base = cell_wire_commit8(&real);

    let mut tampered = real.clone();
    let winner_key = game.dep().reg("winner") as u64;
    let other = if winner == 1 { 2 } else { 1 };
    tampered
        .state
        .set_field_ext(winner_key, field_from_u64(other));
    let moved = cell_wire_commit8(&tampered);

    assert_ne!(
        base, moved,
        "changing the committed winner must move the cell's v9 commitment — the winner is IN \
         the state old8/new8 commit"
    );
}

/// ⚑ THE FIX, AT THE LEG LEVEL (medium: one wide-leg prove). The wide leg's exposed AFTER-block field
/// octet (leg PIs the app-root weld's `field_key` indexes) must carry the cell's REAL committed fields —
/// specifically `octet[reg("winner")] == winner`. Before the fix the octet was ALL ZEROS (the EffectVM
/// `CellState::new` zeroed `fields`, and `fill_block` OVERRODE the octet from that zero state block), so
/// no `field_key` could ever read the winner. `cell_custom_leg` now routes the cell's real lane-0 field
/// octet into the EffectVM `CellState.fields`, so the octet exposes the committed values.
#[test]
#[ignore = "MEDIUM: one wide-leg STARK prove (~1min)"]
fn the_leg_octet_exposes_the_committed_field_values() {
    let (game, _charm, winner) = winning_game();
    let real = game.world().cell_snapshot().expect("cell");
    let octet = dregg_multiway_tug::fold::probe_leg_field_octet(&real);
    let winner_slot = game.dep().reg("winner") as usize;

    // Every exposed octet lane equals the cell's committed lane-0 field at that slot.
    for k in 0..8 {
        let committed = dregg_circuit::effect_vm::field_limbs8(&real.state.fields[k])[0].as_u32();
        assert_eq!(
            octet[k], committed,
            "leg octet[{k}] ({}) must equal the committed fields[{k}] lane-0 ({committed})",
            octet[k]
        );
    }
    // The load-bearing one: the winner's field slot exposes the winner — the value the weld reads.
    assert_eq!(
        octet[winner_slot], winner as u32,
        "leg octet[reg(\"winner\")={winner_slot}] must expose the committed winner ({winner}) — the app-root \
         weld's field_key reads exactly this lane"
    );
}

/// ⚑ THE APP-ROOT OCTET INDEX (fast regression for the winner-weldable fix). The wide leg exposes the
/// AFTER-block `fields[0..8]` octet, and the producer (`compute_rotated_pre_limbs`, `fields[i] -> limb
/// 4+i`) puts `cell.state.fields[k]` at octet index `k` — so the octet index of a cell field slot IS
/// that slot itself. `winner` rides slot `reg("winner")`, so its committed value sits at octet index
/// `reg("winner")` — the `field_key` the app-root weld must aim at. The old `octet_index_of_register`
/// (which subtracts `FIELD_BASE` for the rotated-limb r3..r10 numbering) aimed at octet index `7-3=4`
/// = `a_secret`, the driven `0 vs 2` WitnessConflict — captured here so the mis-map cannot return.
#[test]
fn the_winner_rides_its_own_field_slot_in_the_exposed_octet() {
    use dregg_circuit::effect_vm::{field_limbs8, layout_generated::CUSTOM_APP_FIELD_OCTET_LEN};

    let (game, _charm, winner) = winning_game();
    let real = game.world().cell_snapshot().expect("cell");
    let winner_slot = game.dep().reg("winner") as usize;

    // The winner must ride the exposed octet (fields[0..8]) to be weldable at all.
    assert!(
        winner_slot < CUSTOM_APP_FIELD_OCTET_LEN,
        "winner slot {winner_slot} must be < {CUSTOM_APP_FIELD_OCTET_LEN} (only fields[0..8] have lane-0 limbs)"
    );

    // octet index = field slot: octet[k] lane-0 == field value at slot k.
    let octet_at = |k: usize| field_limbs8(&real.state.fields[k])[0];
    assert_eq!(
        octet_at(winner_slot),
        BabyBear::from_u64(winner),
        "octet index reg(\"winner\")={winner_slot} carries the committed winner ({winner}) — the correct field_key"
    );

    // The OLD buggy field_key: octet_index_of_register(winner_slot) = winner_slot - FIELD_BASE.
    let old_buggy_key =
        dregg_circuit::effect_vm::layout_generated::octet_index_of_register(winner_slot);
    assert_ne!(
        old_buggy_key, winner_slot,
        "the rotated-limb map differs from the cell field slot — that difference WAS the bug"
    );
    assert_ne!(
        octet_at(old_buggy_key),
        BabyBear::from_u64(winner),
        "the old field_key ({old_buggy_key}) reads a DIFFERENT field (a_secret), not the winner — the `0 vs N` conflict"
    );
}

/// The win leaf publishes `[old8 ‖ new8 ‖ charm ‖ winner]`, and its public-input commitment
/// (the value the fold binds) MOVES when the `[old8 ‖ new8]` prefix is the real cell's vs the
/// fixture's. This replaces the vacuous `win_output_binds_the_winner` (which only asserted
/// Poseidon2 is injective): the win output is welded to the CELL, not free.
#[test]
fn the_win_leaf_is_welded_to_the_cell_prefix() {
    let (game, charm, winner) = winning_game();
    let real = game.world().cell_snapshot().expect("cell");
    let real8 = cell_wire_commit8(&real);
    let new8: [BabyBear; 8] = core::array::from_fn(|i| BabyBear::new(1_000 + i as u32));

    let leaf = win_leaf_bound(real8, new8, charm, winner);
    assert_eq!(
        leaf.public_inputs.len(),
        18,
        "[old8 ‖ new8 ‖ charm ‖ winner]"
    );
    assert_eq!(
        &leaf.public_inputs[0..8],
        &real8,
        "PI[0..8] = the real cell old8"
    );
    assert_eq!(&leaf.public_inputs[8..16], &new8, "PI[8..16] = new8");
    assert_eq!(
        leaf.public_inputs[16],
        BabyBear::from_u64(charm),
        "PI[16] = the bound charm"
    );
    assert_eq!(
        leaf.public_inputs[17],
        BabyBear::from_u64(winner),
        "PI[17] = the bound winner"
    );

    // The SAME win, but with the fixture's roots as the prefix, commits differently — so a
    // sub-proof cannot claim the real cell's win while carrying a fixture transition.
    let fixture_leaf = win_leaf_bound(fixture_wire_commit8(), new8, charm, winner);
    assert_ne!(
        custom_proof_pi_commitment(&leaf.public_inputs),
        custom_proof_pi_commitment(&fixture_leaf.public_inputs),
        "the win leaf's bound commitment must move when its state prefix is the real cell's vs \
         the fixture's — the win is welded to the cell"
    );
}

/// SLOW: the terminal win folds over the REAL cell through the deployed recursion fold, and the
/// pure light client accepts it; a spliced final_root is rejected.
#[test]
#[ignore = "SLOW: deployed custom-binding recursion fold over the real WorldCell win transition (~minutes)"]
fn win_folds_over_the_real_cell_and_lightclient_accepts() {
    use dregg_lightclient::verify_history;

    let (game, charm, winner) = winning_game();
    let real = game.world().cell_snapshot().expect("cell");

    let mut whole = dregg_multiway_tug::fold::fold_win_over_cell(&real, charm, winner)
        .expect("the real-cell win folds to one proof");
    let vk = whole.root_vk_fingerprint();
    let attested = verify_history(&whole, &vk)
        .expect("the light client ACCEPTS the honest real-cell win fold");
    assert_eq!(attested.num_turns, 2, "the win turn + the linking tail");
    eprintln!(
        "MULTIWAY-TUG REAL-CELL WIN: folded over the WorldCell's own cell; verify_history OK, \
         num_turns={}, winner={winner}, charm={charm}.",
        attested.num_turns
    );

    let honest_final = whole.final_root;
    whole.final_root[0] = honest_final[0] + BabyBear::ONE;
    assert!(
        verify_history(&whole, &vk).is_err(),
        "a relabeled final_root must be REJECTED"
    );
    whole.final_root = honest_final;
    verify_history(&whole, &vk).expect("the restored real-cell win fold verifies again");
}

/// ⚑ THE HARD GATE — the app-root weld is a property of the ARTIFACT, light-client-visible. Three
/// legs over the SAME real WorldCell win transition:
///   (A) HONEST: the win sub-proof publishes the winner == the cell's committed winner field →
///       the app-root fold is SAT and `verify_history` ACCEPTS (R == field[K] forced IN-CIRCUIT by
///       `prove_custom_binding_node_app_root_segmented`).
///   (B) DISAGREEING: the sub-proof publishes a winner != the cell's committed winner field → the
///       app-root fold is UNSAT (no satisfying partner), so NO verifying artifact ever reaches
///       `verify_history` — the DEPLOYED fold refuses it, visible to a pure light client.
///   (C) CANARY (no code disabled): the SAME disagreeing winner folded through the STATE node
///       (`app_root_binding = None`, the pre-cutover behavior) folds GREEN and `verify_history`
///       ACCEPTS it — proving (B)'s refusal IS the app-root weld, not incidental.
#[test]
#[ignore = "SLOW: deployed app-root-welded recursion fold over the real WorldCell (~minutes ×3)"]
fn app_root_weld_refuses_disagreeing_winner_through_verify_history() {
    use dregg_lightclient::verify_history;
    use dregg_multiway_tug::fold::{fold_win_over_cell, fold_win_over_cell_state_node_canary};

    let (game, charm, winner) = winning_game();
    let real = game.world().cell_snapshot().expect("cell");
    let wrong = if winner == 1 { 2 } else { 1 };

    // (A) HONEST — the app-root fold welds the published winner to the cell's committed field[K].
    let whole = fold_win_over_cell(&real, charm, winner)
        .expect("the honest app-root win folds to one proof");
    let vk = whole.root_vk_fingerprint();
    let attested = verify_history(&whole, &vk)
        .expect("verify_history ACCEPTS the honest app-root win (R == committed winner field)");
    assert_eq!(attested.num_turns, 2, "the win turn + the linking tail");
    eprintln!(
        "HARD GATE (A) HONEST: app-root win folded, verify_history OK, winner={winner}, charm={charm}."
    );

    // (B) DISAGREEING — a winner not matching the cell's committed field has NO satisfying fold.
    let disagree = fold_win_over_cell(&real, charm, wrong);
    assert!(
        disagree.is_err(),
        "a winner ({wrong}) disagreeing with the cell's committed winner field ({winner}) must have \
         NO satisfying app-root fold — UNSAT, refused through verify_history (got Ok, the weld leaks!)"
    );
    eprintln!(
        "HARD GATE (B) REFUSE: disagreeing winner={wrong} is UNSAT — no artifact reaches verify_history."
    );

    // (C) CANARY — the SAME disagreeing winner through the STATE node folds GREEN + verifies.
    let canary = fold_win_over_cell_state_node_canary(&real, charm, wrong)
        .expect("the STATE-node fold accepts the disagreeing winner (no field-K weld)");
    let cvk = canary.root_vk_fingerprint();
    let cattested = verify_history(&canary, &cvk)
        .expect("verify_history ACCEPTS the disagreeing winner through the state node (canary)");
    assert_eq!(cattested.num_turns, 2);
    eprintln!(
        "HARD GATE (C) CANARY: disagreeing winner={wrong} folds GREEN through the STATE node — \
         so (B)'s refusal IS the app-root weld, not incidental."
    );
}
