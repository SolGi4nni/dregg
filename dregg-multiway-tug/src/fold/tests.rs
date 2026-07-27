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

/// ⚑ THE NON-IGNORED LEG-MINT CANARY (the E1-compaction ↔ wide-producer coherence gate).
///
/// The E1 dead-column cutover (`bd21266e6b`) shipped an E1 kill-set that reached PAST the wide
/// custom producer's post-S2 row — into the prove-time gentian refuse-aux block the producer does
/// NOT emit — so `mint_custom_leg`'s wide `Custom` leg PANICKED in the shared trace generator:
/// `compact_e1_columns: customVmDescriptor2R24 row width 1627 < E1 band end 1675`. It landed
/// INVISIBLY because every leg-minting test was `#[ignore]`d (the lib was 39/39 green, but nothing
/// FAST drove leg minting). This canary closes that gap: it drives the EXACT broken path — the wide
/// dispatch's widen → S2-compact → **E1-compact** → descriptor-tail pairing — in milliseconds (no
/// STARK; the full leaf-wrap recursive prove is ~50s), and asserts the producer trace, after the
/// prove-time gentian fill, is COHERENT with the committed E1-compacted descriptor. Any future
/// E1/producer-width disagreement (a stale `e1_compact_generated.rs` vs the wide generator, a
/// regressed emit ceiling) fails HERE, on every `cargo test`, not a day later in an `#[ignore]`d fold.
#[test]
fn mint_custom_leg_wide_geometry_is_coherent_fast() {
    use dregg_circuit::effect_vm::bare_floor_refuse_weld::fill_refuse_aux;
    use dregg_circuit::field::BabyBear;

    let before = producer_cell(1000, 0);
    let after = producer_cell(1000, 1);
    let commit = [BabyBear::ZERO; 8];
    let (desc, mut trace, dpis, _map_heaps, _mb) =
        super::custom_leg_wide_desc_trace(&before, &after, commit).expect(
            "the wide custom dispatch must NOT err/panic at compact_e1 — the bd21266e6b E1 cutover \
             break (row width < E1 band end). If this fails, the E1 table disagrees with the wide \
             custom producer's row width again.",
        );

    // The dispatch S2+E1-COMPACTED the custom member (the point of the cutover): the producer row is
    // far narrower than the un-compacted wide custom width (host 1627 + 960 appendix + 48 gentian).
    let producer_w = trace[0].len();
    assert!(
        (1400..1700).contains(&producer_w),
        "the wide custom producer row must be S2+E1-compacted to the host band (got {producer_w})"
    );
    // The PI vector matches the committed descriptor exactly.
    assert_eq!(
        dpis.len(),
        desc.public_input_count,
        "custom leg PI count must match the committed descriptor"
    );
    // The published 8-felt commitment rides PI 46..54 (the leg's binding anchor).
    assert_eq!(
        &dpis[46..54],
        &commit[..],
        "the leg publishes the commitment at PI 46..53"
    );

    // THE COHERENCE THE PANIC BROKE: the prove-time gentian refuse fill grows the producer row to
    // EXACTLY the committed descriptor width. desc.trace_width - producer_w is the gentian block the
    // Rust prover fills AFTER compaction; if the E1 kill-set had (again) eaten into that block, either
    // the producer row would be too short (Err above) or this delta would be wrong.
    assert!(
        desc.trace_width >= producer_w,
        "descriptor width {} must be >= the producer row {producer_w} (the gentian fills the delta)",
        desc.trace_width
    );
    for row in &mut trace {
        row.resize(desc.trace_width, BabyBear::ZERO);
        fill_refuse_aux(&desc, row);
    }
    assert!(
        trace.iter().all(|r| r.len() == desc.trace_width),
        "after the prove-time gentian fill EVERY wide custom row must equal the descriptor width \
         {} (a ragged row is a STARK reject)",
        desc.trace_width
    );
}

/// ⚑ THE NON-IGNORED FILLER-LEG GATE — BOTH POLES OF THE ARM-SELECTION GUARD, IN MILLISECONDS.
///
/// The linking tail turn of every real-cell fold (`fold_win_over_cell`,
/// `fold_win_over_cell_state_node_canary`, `fold_membership_play_over_cell`) is a plain nonce bump.
/// It used to be minted as a `Custom` leg publishing the literal `[1..8]` as its
/// `custom_proof_commitment` with NO carrier witness — a claim about a sub-proof that did not
/// exist, riding the fold's plain-segment arm where nothing constrains it. The deployed fold now
/// refuses that arm selection structurally (`require_no_unbacked_proof_bind`), so the tail rides
/// `cell_plain_nonce_leg` (`incrementNonceVmDescriptor2R24`) instead.
///
/// This drives BOTH poles of the real guard against the descriptors these two minters ACTUALLY
/// emit, through the fast wide-dispatch half (no STARK — the fold that would exercise it end to end
/// is `#[ignore]`d and takes minutes):
///   * the filler leg the tail rides is ACCEPTED on the plain arm (no proof-bind declared);
///   * the custom leg the tail used to ride is REFUSED there (it declares one).
/// A future filler swapped back to a proof-bind member, or a guard that stopped firing, fails HERE
/// on every `cargo test`.
#[test]
fn the_tail_filler_leg_clears_the_arm_selection_guard_and_the_custom_leg_does_not_fast() {
    use dregg_circuit::effect_vm_descriptors::{
        proof_bind_declarations, require_no_unbacked_proof_bind,
    };
    use dregg_circuit::field::BabyBear;

    // The EXACT two-turn shape `fold_win_over_cell` builds: the head turn over `cell @ n -> n+1`,
    // the tail filler over `n+1 -> n+2`.
    let cell = producer_cell(1000, 0);
    let bumped = super::nonce_bumped(&cell);
    let twice = super::nonce_bumped(&bumped);

    // POLE 1 — the filler the tail turn now rides: allowed on the plain (no-witness) arm.
    let (filler, _t, tail_pis, _mh, _mb) = super::plain_nonce_leg_wide_desc_trace(&bumped, &twice)
        .expect("the plain nonce-bump wide dispatch must not err");
    assert!(
        filler.name.contains("incrementNonce"),
        "the tail filler must be the deployed plain nonce-bump member, got '{}'",
        filler.name
    );
    assert_eq!(
        proof_bind_declarations(&filler),
        0,
        "the filler declares no recursive proof-binding"
    );
    require_no_unbacked_proof_bind(&filler)
        .expect("the filler leg is ALLOWED on the fold's plain-segment arm");
    assert_eq!(
        tail_pis.len(),
        filler.public_input_count,
        "filler PI count must match its committed descriptor"
    );

    // POLE 2 — the custom leg the tail USED to ride: REFUSED on that same arm. (This is also the
    // head turn's member, which is fine there: the head DOES carry a carrier witness.)
    let (custom, _t, head_pis, _mh, _mb) =
        super::custom_leg_wide_desc_trace(&cell, &bumped, [BabyBear::ZERO; 8])
            .expect("the wide custom dispatch must not err");
    let refusal = require_no_unbacked_proof_bind(&custom)
        .expect_err("a proof-bind member with no carrier witness must be REFUSED on the plain arm");
    assert_eq!(refusal.declarations, 1);
    assert_eq!(refusal.name, custom.name);

    // THE LINK the swap must not break: the head's AFTER 8-felt anchor IS the tail's BEFORE anchor
    // (`turn_anchors8` continuity, the last 16 PIs of each leg). Changing the tail's descriptor
    // family would be a silent chain break if the anchors were derived differently — they are not.
    let (hn, tn) = (head_pis.len(), tail_pis.len());
    let head_new8 = &head_pis[hn - 8..];
    let tail_old8 = &tail_pis[tn - 16..tn - 8];
    assert_eq!(
        head_new8, tail_old8,
        "the custom head turn's AFTER anchor must equal the incrementNonce tail's BEFORE anchor"
    );
    assert_eq!(
        head_new8,
        &cell_wire_commit8(&bumped)[..],
        "and both are the shared no-STARK v9 chip commitment of the once-bumped cell"
    );
    assert_ne!(
        tail_old8,
        &tail_pis[tn - 8..],
        "a nonce bump MOVES the anchor — the link check above is not 0 == 0"
    );
}

/// ⚑ THE NON-IGNORED OCTET-POSITION CANARY (the offset-drift gate).
///
/// `probe_leg_field_octet` and the DEPLOYED app-root arm both locate the wide custom leg's committed
/// `fields[0..8]` octet with `ivc_turn_chain::custom_leg_field_octet_lo`. That offset used to be
/// hand-written as `n - 24` in the probe, and when the 8-felt post-state fields-root pins
/// (`withAfterFieldsRootPins`) were inserted BETWEEN the octet and the 16 wide anchors the octet
/// moved to `n - 32` — so the stale probe silently read the fields-root instead of the fields. The
/// drift was invisible because the only test over the octet was `#[ignore]`d.
///
/// This canary is INDEPENDENT of the derivation: it stamps a distinctive marker into each of the
/// cell's eight lane-0 field slots, runs the fast wide dispatch (no STARK, ~0.1s), then MEASURES
/// where those markers actually land in the PI vector and requires that to be exactly the window
/// `custom_leg_field_octet_lo` names. Any future PI-tail relayout that moves the octet fails HERE on
/// every `cargo test`.
#[test]
fn the_field_octet_sits_where_the_deployed_derivation_says_fast() {
    use dregg_circuit::effect_vm::field_limbs8;
    use dregg_circuit::field::BabyBear;
    use dregg_circuit_prove::ivc_turn_chain::custom_leg_field_octet_lo;

    // Distinctive per-slot markers, far from any structural PI value the leg publishes.
    let mut before = producer_cell(1000, 0);
    for i in 0..LEG_FIELD_OCTET_LEN {
        before.state.fields[i] = field_from_u64(7_000_001 + (i as u64) * 13);
    }
    let mut after = before.clone();
    let _ = after.state.increment_nonce();

    let (desc, _trace, dpis, _map_heaps, _mb) =
        super::custom_leg_wide_desc_trace(&before, &after, [BabyBear::ZERO; 8])
            .expect("the wide custom dispatch must not err");
    assert_eq!(dpis.len(), desc.public_input_count);

    let n = dpis.len();
    let octet_lo = custom_leg_field_octet_lo(n)
        .expect("the wide custom leg carries the octet + fields-root + anchors PI tail");
    let marker = |i: usize| field_limbs8(&before.state.fields[i])[0];

    // MEASURED, not derived: each marker occurs exactly once in the PI vector, and slot `i` lands at
    // `octet_lo + i`. If the octet moves, this is where it is caught.
    for i in 0..LEG_FIELD_OCTET_LEN {
        let hits: Vec<usize> = dpis
            .iter()
            .enumerate()
            .filter(|(_, v)| **v == marker(i))
            .map(|(j, _)| j)
            .collect();
        assert_eq!(
            hits,
            vec![octet_lo + i],
            "committed fields[{i}] must be published exactly once, at the derived octet index \
             {} (custom_leg_field_octet_lo({n}) = {octet_lo}) — measured {hits:?}. The wide \
             custom PI tail is [octet 8 ‖ post-fields-root 8 ‖ old8 ‖ new8]; if a wrapper was \
             added or removed, re-derive the offset there, do NOT hand-patch a reader.",
            octet_lo + i
        );
    }

    // And the whole exposed octet reads back as the committed values — what the app-root weld's
    // `field_key` indexes, and what `probe_leg_field_octet` returns.
    let octet: Vec<u32> = dpis[octet_lo..octet_lo + LEG_FIELD_OCTET_LEN]
        .iter()
        .map(|f| f.as_u32())
        .collect();
    let committed: Vec<u32> = (0..LEG_FIELD_OCTET_LEN)
        .map(|i| marker(i).as_u32())
        .collect();
    assert_eq!(
        octet, committed,
        "the derived octet window IS the committed fields"
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
// ⚑ BLOCKED, NOT SUPERSEDED — and the reasons below used to say the wrong one of those.
//
// MEASURED 2026-07-27 (435s, `--ignored`), both tests refuse at mint with the same text:
//
//   custom state-binding sub-proof leaf mint failed: the sub-program publishes 2 public
//   input(s), but the state-binding ABI requires at least 16 ([old_commit8 ‖ new_commit8] ‖
//   ..app). A program that cannot express the binding is refused rather than zero-padded into
//   a false one.
//
// That is the deployed custom state-binding node (`circuit/src/effect_vm/custom_state_binding.rs`)
// doing its job: these two fold 2-felt leaves (`[leaf, root]` / `[charm, winner]`) that PREDATE it.
//
// "SUPERSEDED" was wrong because what they cover is not covered elsewhere: both real-cell folds
// (`membership_play_folds_over_the_real_cell_and_lightclient_accepts` here, and
// `tests/fold_real_cell.rs`) fold ONE turn, and these are the only TWO-PLAY private match and the
// only win-output attestation over a hidden-hand play. Calling a hole a duplicate is how it stops
// being counted.
//
// The prefix machinery is NOT missing any more — the per-play membership leaf carries
// `[old8 ‖ new8]` over the real cell and is green (measured in the same run). THE RESIDUAL IS
// EXACTLY: drive TWO plays on the real `WorldCell` and fold their real-prefixed leaves, i.e. extend
// the green single-play real-cell body to a second turn. It is not a prover gap and not an ABI gap.
#[test]
#[ignore = "BLOCKED (measured 2026-07-27): the 2-PI membership leaf is REFUSED by the deployed \
            state-binding ABI (needs >=16 PIs: [old8 || new8] || ..app). NOT superseded — this is \
            the only TWO-PLAY private match; the real-cell folds are single-turn. Residual: drive \
            two plays on the real WorldCell and fold their real-prefixed leaves."]
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
#[ignore = "BLOCKED (measured 2026-07-27): the 2-PI leaf is REFUSED by the deployed state-binding \
            ABI (needs >=16 PIs). The real-cell win fold covers the WIN leaf; it does NOT cover a \
            win FOLLOWING a hidden-hand membership play, which is this test. Residual: the same \
            two-turn real-cell drive."]
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
    use crate::reference::{ActionKind, Engine};
    let seed = 0u64;
    let mut eng = Engine::new(seed);
    let game = MultiwayTug::deploy(seed as u8).expect("deploy");
    game.seed(&eng.projection()).expect("genesis seeds");
    // Three PRIVATE turns (Secret, Secret, Discard). These open no offer, so no response is
    // needed — and a response would be refused today, since `respond_gift`/`respond_comp` are
    // not yet in the Lean-emitted program. This helper only needs a cell with real committed
    // state, so the private opening line is exactly as good as any other.
    for kind in [ActionKind::Secret, ActionKind::Secret, ActionKind::Discard] {
        let p = eng.current_player();
        let d = eng
            .legal_decisions()
            .into_iter()
            .find(|d| d.kind() == Some(kind))
            .expect("an unused kind is always affordable");
        let mv = eng.apply(p, d).expect("a legal decision applies");
        let proj = eng.projection();
        game.commit_projection(mv.method(), &proj)
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
