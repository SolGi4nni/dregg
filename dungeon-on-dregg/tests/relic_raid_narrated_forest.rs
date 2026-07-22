#![cfg(feature = "private-raid-assignment")]

//! One coherent Dungeon receipt chain: oath, guardian consequence, then an atomic
//! proof-assigned + narrated relic awakening forest.

use dregg_turn::verify_receipt_chain;
use dungeon_on_dregg::narrator::{Command, Narrated, bound_narration_commit, narration_commitment};
use dungeon_on_dregg::private_raid::{RaidRole, prove_private_assignment};
use dungeon_on_dregg::relic_resonance::{
    AWAKEN_SUNBLADE, AtomicRaidNarratedResonance, ROOM_AFTERMATH, raid_statement_commitment,
};

fn scores() -> [[u8; 4]; 4] {
    // Seat 2 is the unique Mender; the other three seats uniquely maximize the
    // remaining roles. The proof reveals the permutation, not this matrix.
    [[0, 3, 0, 0], [3, 0, 0, 0], [0, 0, 3, 0], [0, 0, 0, 3]]
}

#[test]
fn relic_raid_allocation_and_narration_compose_in_one_receipt_chain_and_forest() {
    const PROOF_SESSION: u32 = 771_091;
    const MENDER_SEAT: usize = 2;
    const WORLD_SEED: u8 = 91;
    const NARRATION: &str =
        "The freed guardian names the party's hidden Mender, and the Sunblade answers with dawn.";

    let proof = prove_private_assignment(PROOF_SESSION, scores(), [[true; 4]; 4])
        .expect("the real private raid allocation proves");
    assert_eq!(
        RaidRole::try_from(proof.statement().roles[MENDER_SEAT]).unwrap(),
        RaidRole::Mender
    );
    let narrated = Narrated::new(Command::at(ROOM_AFTERMATH, AWAKEN_SUNBLADE), NARRATION);

    // RED polarity: root one can verify this exact proof, but root two reaches the
    // relic before the guardian consequence exists. The late refusal must roll the
    // already-evaluated proof root back with the resonance root.
    let mut premature =
        AtomicRaidNarratedResonance::new(WORLD_SEED + 1, proof.clone(), MENDER_SEAT)
            .expect("the hostile joined image deploys");
    premature.take_sunblade().unwrap();
    assert!(
        premature
            .awaken_with_private_raid_narration(&narrated)
            .is_err(),
        "a valid allocation cannot skip the guardian-authored resonance precondition"
    );
    assert!(!premature.proof_landed());
    assert!(!premature.resonance_gate_landed());
    assert_eq!(premature.read_relic_var("relic_awakened"), 0);

    let mut scenario = AtomicRaidNarratedResonance::new(WORLD_SEED, proof.clone(), MENDER_SEAT)
        .expect("the joined executor deploys");
    scenario
        .take_sunblade()
        .expect("the oath follows joined genesis");
    scenario
        .free_guardian()
        .expect("the mercy consequence follows the oath");
    assert_eq!(scenario.read_relic_var("oath"), 1);
    assert_eq!(scenario.read_relic_var("mercy"), 1);
    assert_eq!(scenario.read_relic_var("relic_awakened"), 0);
    assert!(!scenario.proof_landed());
    assert!(!scenario.resonance_gate_landed());

    let prepared = scenario
        .prepare_narrated_resonance(&narrated)
        .expect("the confined narration prepares");
    assert_eq!(prepared.turn().call_forest.roots.len(), 2);
    assert_eq!(prepared.turn().action_count(), 2);
    assert_eq!(
        prepared.narration_commitment(),
        narration_commitment(NARRATION)
    );

    let composed = scenario
        .commit_narrated_resonance(prepared)
        .expect("proof root and narrated resonance root commit atomically");
    assert_eq!(composed.receipt.action_count, 2);
    assert_eq!(composed.assigned_seat, MENDER_SEAT);
    assert_eq!(composed.narrated, narrated);
    assert_eq!(
        composed.raid_statement_commitment,
        raid_statement_commitment(&proof)
    );
    assert_eq!(
        bound_narration_commit(&composed.receipt),
        Some(narration_commitment(NARRATION)),
        "the prose commitment rides the same receipt as proof materialization and awakening"
    );
    assert_eq!(scenario.read_relic_var("relic_awakened"), 1);
    assert!(scenario.proof_landed());
    assert!(scenario.resonance_gate_landed());

    assert_eq!(scenario.receipts().len(), 4);
    verify_receipt_chain(scenario.receipts())
        .expect("genesis, oath, encounter, and the two-root awakening form one receipt chain");
    assert_eq!(
        scenario.receipts()[3].pre_state_hash,
        scenario.receipts()[2].post_state_hash
    );

    // Reconstruct the same joined image and re-drive the exact public receipt. The
    // proof is reverified by the custom executor predicate; no private score matrix
    // or narrator prose is consulted as state authority during replay.
    let mut replay = AtomicRaidNarratedResonance::new(WORLD_SEED, proof, MENDER_SEAT)
        .expect("the replay image deploys");
    replay.take_sunblade().unwrap();
    replay.free_guardian().unwrap();
    replay
        .awaken_with_private_raid_narration(&narrated)
        .expect("the composed forest replays");
    verify_receipt_chain(replay.receipts()).expect("the replay chain links");
    assert_eq!(replay.read_relic_var("relic_awakened"), 1);
    assert_eq!(
        scenario
            .receipts()
            .iter()
            .map(|receipt| receipt.turn_hash)
            .collect::<Vec<_>>(),
        replay
            .receipts()
            .iter()
            .map(|receipt| receipt.turn_hash)
            .collect::<Vec<_>>(),
        "the same typed choices, proof receipt, and narration reproduce the same turn forest"
    );
}
