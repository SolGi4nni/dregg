//! Phase 3 — the STARK fold, DRIVEN.
//!
//! The hidden-hand `Witnessed { MerkleMembership }` tooth lowers to a foldable leaf
//! ([`membership_leaf_for_play`]); a whole PRIVATE match (a sequence of membership-proven
//! plays) folds to ONE `verify_history`-accepted proof; a forged match is rejected. The
//! cheap tests always run (lowering is non-vacuous); the fold tests are `#[ignore]` SLOW.

use super::*;
use crate::hidden_hand::HandTree;
use dregg_cell::program::{StateConstraint, field_from_u64};
use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
use dregg_lightclient::verify_history;
use game_turn_slice::compiler::{GameProgramCompiler, SlotAssignment};

/// A deterministic six-card hand: distinct card ids across guilds, distinct nonces (the same
/// shape `hidden_hand::tests::sample_hand` uses).
fn sample_hand() -> Vec<(u64, u64)> {
    vec![
        (0, 1001),
        (1, 1002),
        (3, 1003),
        (7, 1004),
        (12, 1005),
        (18, 1006),
    ]
}

// The win/score turn's slot layout.
const WIN_CHARM: u8 = 0; // the winner's total influence — FieldGte >= 11 (range gadget)
const WIN_SCORE: u8 = 1; // running score — conserved this turn
const WIN_POINTS: u8 = 2; // influence gained this turn

/// The terminal win/score turn: a range-gadget leaf binding `[charm, winner]` as a public
/// output, proving the winner crossed the influence threshold (`FieldGte charm >= 11`) with a
/// conserved score (`new[score] == old[score] + new[points]`). The win is thus a BOUND public
/// output the light client attests via the leaf's commitment.
fn win_bundle(charm: u64, winner: u64) -> LeafBundle {
    let mut c = GameProgramCompiler::new("multiway-tug-win-v1", 16).with_public_inputs(2);
    c.lower_state_constraint(&StateConstraint::SumEqualsAcross {
        input_fields: vec![WIN_SCORE],
        output_fields: vec![WIN_POINTS],
    })
    .expect("score conservation lowers");
    c.lower_state_constraint(&StateConstraint::FieldGte {
        index: WIN_CHARM,
        value: field_from_u64(11),
    })
    .expect("the win threshold lowers via the range gadget");
    let program = c.finish();
    let assign = SlotAssignment::new()
        .set_new(WIN_CHARM, charm) // >= 11
        .set_new(WIN_SCORE, 20)
        .set_old(WIN_SCORE, 15)
        .set_new(WIN_POINTS, 5); // 20 - 15 - 5 == 0
    let witness_values = c.witness(&assign, 4).expect("honest win witness");
    LeafBundle {
        program,
        witness_values,
        num_rows: 4,
        public_inputs: vec![BabyBear::from_u64(charm), BabyBear::from_u64(winner)],
        descriptor_state_leaf: None,
    }
}

// ---------------------------------------------------------------------------
// Cheap, always-run: the lowering is total + non-vacuous (no proving).
// ---------------------------------------------------------------------------

/// Every dealt card's Phase-2 play lowers to a foldable membership leaf: PIs `[leaf, root]`
/// (the card id is NOT among them — the hand is private-in-fold), leaf `== card_leaf(card,
/// nonce)`, root `== the committed hand root`.
#[test]
fn every_play_lowers_to_a_membership_leaf() {
    let hand = sample_hand();
    let tree = HandTree::commit(hand.clone());
    let root = root_felt_from_commitment(&tree.root_bytes());
    for &(card, nonce) in &hand {
        let proof = tree.prove_play(card).expect("a dealt card can be proven");
        let leaf = membership_leaf_for_play(&proof).expect("an honest play lowers to a leaf");
        assert_eq!(
            leaf.public_inputs,
            vec![card_leaf(card, nonce), root],
            "PIs are [leaf, root] — the card id is NOT in the proof"
        );
        assert!(
            !leaf.public_inputs.contains(&BabyBear::from_u64(card)),
            "the raw card id never appears in the public inputs"
        );
        assert_eq!(
            leaf.num_rows, 2,
            "depth-2 hand tree ⇒ a 2-row membership trace"
        );
    }
}

/// A fabricated card / tampered path has NO membership leaf: a card never dealt cannot be
/// proven at all, and a play whose path is corrupted (so it no longer climbs to the committed
/// root) is refused at lowering.
#[test]
fn fabricated_card_has_no_membership_leaf() {
    let hand = sample_hand();
    let tree = HandTree::commit(hand.clone());

    // A card that was never dealt (20 ∉ the hand) cannot even be proven.
    assert!(
        tree.prove_play(20).is_none(),
        "a card not in the hand has no membership proof"
    );

    // A dealt card's proof with a corrupted sibling no longer climbs to the committed root.
    let mut proof = tree.prove_play(hand[0].0).expect("dealt card proves");
    proof.path[0].siblings[0] = proof.path[0].siblings[0] + BabyBear::ONE;
    assert!(
        membership_leaf_for_play(&proof).is_err(),
        "a tampered path that does not climb to the committed root is refused at lowering"
    );

    // A replay of a played card against the UPDATED remaining root fails membership.
    let remaining = tree.without(hand[0].0);
    assert!(
        remaining.prove_play(hand[0].0).is_none(),
        "a played card is no longer under the remaining-hand root (no double-play)"
    );
}

/// **THE WIN IS WELDED TO THE CELL'S STATE PREFIX.** The win leaf publishes
/// `[old8 ‖ new8 ‖ charm ‖ winner]`; its public-input commitment (the value the fold binds and
/// the deployed state-binding node connects to the leg's real rotated roots) MOVES when the
/// `[old8 ‖ new8]` prefix is one cell's vs another's — so a win cannot be claimed over a
/// different cell transition. The winner is still a bound output (a different winner moves the
/// commitment too).
///
/// This REPLACES the old `win_output_binds_the_winner`, which only asserted Poseidon2 is
/// injective over `[charm, winner]` (vacuous — it was true of any hash and said nothing about
/// the cell). The real-cell drive — the win folding over the WorldCell's own committed cell —
/// is `tests/fold_real_cell.rs`.
#[test]
fn win_output_is_welded_to_the_cell_prefix() {
    use super::{fixture_wire_commit8, win_leaf_bound};
    let new8: [BabyBear; 8] = core::array::from_fn(|i| BabyBear::new(500 + i as u32));
    let cell_a: [BabyBear; 8] = core::array::from_fn(|i| BabyBear::new(i as u32));

    let a = win_leaf_bound(cell_a, new8, 13, 1);
    let b = win_leaf_bound(fixture_wire_commit8(), new8, 13, 1);
    assert_ne!(
        custom_proof_pi_commitment(&a.public_inputs),
        custom_proof_pi_commitment(&b.public_inputs),
        "the SAME win over a DIFFERENT cell prefix must bind a different commitment — the win \
         is welded to the cell, not free"
    );

    let c = win_leaf_bound(cell_a, new8, 13, 2);
    assert_ne!(
        custom_proof_pi_commitment(&a.public_inputs),
        custom_proof_pi_commitment(&c.public_inputs),
        "a different winner still binds a different commitment"
    );
}

/// **THE PER-PLAY MEMBERSHIP RECEIPT IS WELDED TO THE CELL PREFIX.** The membership leaf now
/// publishes `[old8 ‖ new8 ‖ leaf ‖ root]` (18 PIs), the deployed state-binding shape — not the
/// old fixture-bound `[leaf, root]`. Its public-input commitment (the value the fold binds and the
/// state node connects to the leg's real rotated roots) MOVES when the `[old8 ‖ new8]` prefix is
/// one cell's vs another's, so a per-play move cannot be claimed over a different cell transition.
/// The membership fact is unchanged (the card id is still NOT in the PIs).
#[test]
fn membership_leaf_is_welded_to_the_cell_prefix() {
    use super::{fixture_wire_commit8, membership_leaf_bound};
    let hand = sample_hand();
    let tree = HandTree::commit(hand.clone());
    let root = root_felt_from_commitment(&tree.root_bytes());
    let (card, nonce) = hand[5]; // card 18 — a hidden play
    let proof = tree.prove_play(card).expect("a dealt card proves");

    let new8: [BabyBear; 8] = core::array::from_fn(|i| BabyBear::new(700 + i as u32));
    // A distinct non-fixture prefix standing in for a cell's rotated roots.
    let cell_a: [BabyBear; 8] = core::array::from_fn(|i| BabyBear::new(9_000 + i as u32));

    let a = membership_leaf_bound(cell_a, new8, &proof).expect("an honest play lowers to a leaf");
    // The state-binding ABI shape: [old8 ‖ new8 ‖ leaf ‖ root].
    assert_eq!(a.public_inputs.len(), 18, "[old8 ‖ new8 ‖ leaf ‖ root]");
    assert_eq!(&a.public_inputs[0..8], &cell_a, "PI[0..8] = old8");
    assert_eq!(&a.public_inputs[8..16], &new8, "PI[8..16] = new8");
    assert_eq!(
        a.public_inputs[16],
        card_leaf(card, nonce),
        "PI[16] = the blinded card leaf"
    );
    assert_eq!(
        a.public_inputs[17], root,
        "PI[17] = the committed hand root"
    );
    // The membership portion [leaf, root] hides the card: the raw card id is not among it (leaf
    // is the blinded Poseidon2 commitment card_leaf(card, nonce), root is the hand digest).
    assert!(
        !a.public_inputs[16..].contains(&BabyBear::from_u64(card)),
        "the raw card id never appears in the membership PIs — the hand stays private-in-fold"
    );

    // The SAME play over a DIFFERENT cell prefix binds a different commitment — the receipt is
    // welded to the cell, not free.
    let b = membership_leaf_bound(fixture_wire_commit8(), new8, &proof).expect("lowers");
    assert_ne!(
        custom_proof_pi_commitment(&a.public_inputs),
        custom_proof_pi_commitment(&b.public_inputs),
        "a membership play over a DIFFERENT cell prefix must bind a different commitment — the \
         per-play receipt is welded to the cell, not the fixture"
    );

    // A fabricated/tampered play still has no leaf (the refusal survives the prefixing).
    let mut bad = tree.prove_play(hand[0].0).expect("dealt card proves");
    bad.path[0].siblings[0] = bad.path[0].siblings[0] + BabyBear::ONE;
    assert!(
        membership_leaf_bound(cell_a, new8, &bad).is_err(),
        "a tampered path is refused at lowering even with the state prefix"
    );
}

// ---------------------------------------------------------------------------
// SLOW (#[ignore]): the whole private match folds to one verify_history-accepted proof.
// ---------------------------------------------------------------------------

/// THE HARD GATE: a private multiway-tug match — TWO membership-proven plays (card A from the
/// full hand, then card B from the updated remaining hand, each proven under its own committed
/// root, the cards never revealed in the proof) — FOLDS via `prove_turn_chain_recursive` into
/// ONE `WholeChainProof` the pure light client `verify_history` ACCEPTS. Then a relabeled
/// `final_root` is REJECTED (a non-vacuous light-client bite), and the restored proof accepts.
// NOTE (state-prefix residual): the two SLOW tests below fold 2-felt membership/win leaves
// (`[leaf, root]` / `[charm, winner]`) that PREDATE the deployed custom state-binding node,
// which now requires every custom sub-proof leaf to publish the 16-felt `[old8 ‖ new8]` prefix
// (see `circuit/src/effect_vm/custom_state_binding.rs`). They therefore no longer mint through
// `prove_custom_leaf_with_state_commitment` as-is. The WIN leaf's prefix closure is
// `win_leaf_bound` + the real-cell fold (`tests/fold_real_cell.rs`); the MEMBERSHIP-leaf prefix
// (prepend the leg's real roots to `[leaf, root]`, identically) is the named residual for the
// hidden-hand plays.
#[test]
#[ignore = "SUPERSEDED by tests/fold_real_cell.rs: 2-PI membership leaves predate the state-binding prefix; membership-leaf prefixing is the named residual"]
fn private_match_folds_and_lightclient_accepts() {
    let hand = sample_hand();
    let t0 = HandTree::commit(hand.clone());
    let p0 = t0.prove_play(hand[0].0).expect("play A proves membership");
    let t1 = t0.without(hand[0].0);
    let p1 = t1
        .prove_play(hand[1].0)
        .expect("play B proves membership vs the remaining root");

    let b0: LeafBundle = membership_leaf_for_play(&p0)
        .expect("play A lowers to a membership leaf")
        .into();
    let b1: LeafBundle = membership_leaf_for_play(&p1)
        .expect("play B lowers to a membership leaf")
        .into();

    let mut whole = fold_match(&[b0, b1]).expect("the private match folds to one proof");
    let vk = whole.root_vk_fingerprint();

    let attested =
        verify_history(&whole, &vk).expect("the light client ACCEPTS the honest private match");
    assert_eq!(
        attested.num_turns, 2,
        "the attestation covers both membership-proven plays"
    );
    eprintln!(
        "MULTIWAY-TUG PHASE 3 ACCEPT: a 2-play PRIVATE match folded to ONE proof; \
         verify_history OK, num_turns={} (the cards never appeared in the proof).",
        attested.num_turns
    );

    // NON-VACUOUS FORGERY: relabel the carried final_root; verify_history REFUSES.
    let honest_final = whole.final_root;
    whole.final_root[0] = honest_final[0] + BabyBear::ONE;
    assert!(
        verify_history(&whole, &vk).is_err(),
        "a relabeled final_root must be REJECTED by verify_history"
    );
    // Restore + re-accept — the refusal was the lie, not collateral damage.
    whole.final_root = honest_final;
    verify_history(&whole, &vk).expect("the restored honest match verifies again");
    eprintln!("MULTIWAY-TUG PHASE 3 REJECT: verify_history refused a spliced final_root.");
}

/// THE WIN AS A BOUND PUBLIC OUTPUT: a match of a membership-proven play followed by the
/// terminal win/score turn folds; the light client attests the whole chain, and the win turn's
/// leg publishes the honest `custom_proof_pi_commitment([charm, winner])` — the win is a bound
/// public output. A relabeled final_root is rejected.
#[test]
#[ignore = "SUPERSEDED by tests/fold_real_cell.rs::win_folds_over_the_real_cell_and_lightclient_accepts: the real-cell win fold carries the [old8 ‖ new8] prefix; this 2-PI form predates it"]
fn match_win_output_is_attested() {
    let hand = sample_hand();
    let tree = HandTree::commit(hand.clone());
    let p0 = tree
        .prove_play(hand[0].0)
        .expect("the play proves membership");
    let play: LeafBundle = membership_leaf_for_play(&p0)
        .expect("the play lowers to a membership leaf")
        .into();
    let win = win_bundle(13, 1); // winner = player 1, influence 13 (>= 11)

    let mut whole = fold_match(&[play, win]).expect("the play + win turn fold to one proof");
    let vk = whole.root_vk_fingerprint();

    let attested = verify_history(&whole, &vk)
        .expect("the light client ACCEPTS the membership-play + win-turn match");
    assert_eq!(attested.num_turns, 2, "one play + the win turn");
    eprintln!(
        "MULTIWAY-TUG PHASE 3 WIN: membership play + win turn folded; verify_history OK, \
         num_turns={}; the win [charm=13, winner=1] is a bound public output.",
        attested.num_turns
    );

    let honest_final = whole.final_root;
    whole.final_root[0] = honest_final[0] + BabyBear::ONE;
    assert!(
        verify_history(&whole, &vk).is_err(),
        "a relabeled final_root must be REJECTED"
    );
    whole.final_root = honest_final;
    verify_history(&whole, &vk).expect("the restored match verifies again");
}

/// Deploy + seed + play a few legal turns on the REAL executor, returning the game's OWN committed
/// cell snapshot — a real WorldCell cell (real pk / balance / heap), not the `pk[0]=7` fixture.
fn a_real_world_cell() -> dregg_cell::Cell {
    use crate::game::MultiwayTug;
    use crate::reference::Engine;
    let seed = 0u64;
    let mut eng = Engine::new(seed);
    let game = MultiwayTug::deploy(seed as u8).expect("deploy");
    game.seed(&eng.projection()).expect("genesis seeds");
    for _ in 0..3 {
        if eng.round_complete() {
            break;
        }
        let mv = eng.play_next();
        let proj = eng.projection();
        game.commit_projection(mv.action().method(), &proj)
            .expect("a legal play commits");
    }
    game.world().cell_snapshot().expect("the world-cell exists")
}

/// ⚑ THE PER-PLAY MOVE IS A REAL RECEIPT (SLOW). A hidden-hand membership play folds over the
/// game's OWN committed WorldCell cell through the deployed recursion fold, and the pure light
/// client `verify_history` ACCEPTS it — the per-play leg is welded to real state, no longer the
/// `pk[0]=7` fixture. Then the ANTI-GHOST bite: the SAME play whose leaf carries the FIXTURE's
/// state prefix (not the real cell's rotated roots) is UNSAT over the real leg — no satisfying
/// fold, refused. This closes the fixture residual for the per-play moves the way
/// `fold_real_cell.rs` closed it for the WIN move.
#[test]
#[ignore = "SLOW: deployed state-binding recursion fold over the real WorldCell per-play membership transition (~minutes)"]
fn membership_play_folds_over_the_real_cell_and_lightclient_accepts() {
    use super::{
        cell_rotated_roots, fixture_wire_commit8, fold_membership_play_over_cell,
        membership_leaf_bound, mint_membership_turn_over_cell, nonce_bumped, plain_turn_over_cell,
    };
    use dregg_circuit_prove::ivc_turn_chain::prove_turn_chain_recursive;

    let real = a_real_world_cell();
    assert_ne!(
        super::cell_wire_commit8(&real),
        fixture_wire_commit8(),
        "the real cell's v9 commitment differs from the pk[0]=7 fixture's"
    );

    let hand = sample_hand();
    let tree = HandTree::commit(hand.clone());
    let proof = tree.prove_play(hand[0].0).expect("a dealt card proves");

    // HONEST: the membership play welded to the real cell folds and verify_history accepts.
    let mut whole = fold_membership_play_over_cell(&real, &proof)
        .expect("the real-cell membership play folds to one proof");
    let vk = whole.root_vk_fingerprint();
    let attested = verify_history(&whole, &vk)
        .expect("the light client ACCEPTS the honest real-cell membership play");
    assert_eq!(attested.num_turns, 2, "the play turn + the linking tail");
    eprintln!(
        "MULTIWAY-TUG REAL-CELL PLAY: a membership play folded over the WorldCell's own cell; \
         verify_history OK, num_turns={} (the card never appeared in the proof).",
        attested.num_turns
    );

    // NON-VACUOUS light-client bite: a relabeled final_root is rejected.
    let honest_final = whole.final_root;
    whole.final_root[0] = honest_final[0] + BabyBear::ONE;
    assert!(
        verify_history(&whole, &vk).is_err(),
        "a relabeled final_root must be REJECTED by verify_history"
    );
    whole.final_root = honest_final;
    verify_history(&whole, &vk).expect("the restored real-cell play verifies again");

    // ANTI-GHOST: the SAME play whose leaf prefix is the FIXTURE's roots (not the real cell's) is
    // UNSAT over the real leg — the state node connects the leaf's [old8 ‖ new8] to the leg's REAL
    // rotated roots, so a fixture prefix has no satisfying fold.
    let (_real_old8, real_new8) = cell_rotated_roots(&real);
    let forged_leaf = membership_leaf_bound(fixture_wire_commit8(), real_new8, &proof)
        .expect("the leaf lowers (the membership fact is honest; only the prefix is wrong)");
    let t0 = mint_membership_turn_over_cell(&real, &forged_leaf);
    let t1 = plain_turn_over_cell(&nonce_bumped(&real));
    let forged = if t0.new_root() != t1.old_root() {
        Err("link".to_string())
    } else {
        prove_turn_chain_recursive(&[t0, t1]).map_err(|e| format!("{e}"))
    };
    assert!(
        forged.is_err(),
        "a membership leaf whose state prefix is the fixture's roots (not the real cell's) must be \
         UNSAT over the real leg — the fixture receipt does not fold (got Ok, the weld leaks!)"
    );
    eprintln!(
        "MULTIWAY-TUG REAL-CELL PLAY REFUSE: a fixture-prefix membership leaf is UNSAT over the \
         real cell's leg — the per-play receipt is welded to real state."
    );
}
