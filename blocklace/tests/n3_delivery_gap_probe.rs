//! n3_delivery_gap_probe.rs — THROWAWAY diagnostic (root-cause of the n=3 plateau).
//!
//! NOT a product invariant. Written to answer one question empirically: when an
//! n=3 committee fails to super-ratify a wave, which STEP breaks — and is it a
//! fundamental degeneracy of the n=3 boundary or a bug that n=4 masks?
//!
//! It drives the EXACT ordering rule the live node runs (`ordering::tau`, via the
//! `finalized_order` projection lifted verbatim from `poll_finalized_blocks`) over
//! hand-built, causally-CLOSED DAGs, so the only variable is which blocks a node
//! has RECEIVED. It isolates the ordering/finality math from gossip and cadence.
//!
//! Findings it witnesses:
//!   1. A perfect round-synchronous n=3 DAG finalizes EVERY wave (rule is correct).
//!   2. At n=3, dropping ONE block from a wave's LAST round from a node's view
//!      drops that node BELOW super-ratification — the wave does NOT finalize.
//!      supermajority_threshold(3) == 3 == n: ZERO slack, unanimity per round.
//!   3. The SAME single-block gap at n=4 still finalizes: supermajority(4)==3<4,
//!      so one lagging/late block is routed around. This is the slack n=3 lacks.

use std::collections::HashMap;

use dregg_blocklace::finality::{Block, BlockId, Blocklace, Payload};
use dregg_blocklace::ordering::supermajority_threshold;
use ed25519_dalek::SigningKey;

fn key(seed: u8) -> SigningKey {
    SigningKey::from_bytes(&[seed; 32])
}
fn pubkey(sk: &SigningKey) -> [u8; 32] {
    sk.verifying_key().to_bytes()
}

fn round_block(sk: &SigningKey, seq: u64, preds: &[BlockId]) -> Block {
    Block::new(sk, seq, Payload::Turn(vec![seq as u8]), preds.to_vec())
}

/// Build a fully round-synchronous DAG: every creator authors one block per round,
/// each citing ALL of the previous round's blocks (exactly `produce_round_block`'s
/// whole-cohort predecessor rule). Returns blocks grouped by round.
fn build_rounds(keys: &[&SigningKey], rounds: u64) -> Vec<Vec<Block>> {
    let mut by_round: Vec<Vec<Block>> = Vec::new();
    for r in 0..rounds {
        let preds: Vec<BlockId> = if r == 0 {
            vec![]
        } else {
            by_round[(r - 1) as usize].iter().map(|b| b.id()).collect()
        };
        let round: Vec<Block> = keys.iter().map(|sk| round_block(sk, r, &preds)).collect();
        by_round.push(round);
    }
    by_round
}

/// Finalized `(creator, seq)` order — EXACT `poll_finalized_blocks` projection
/// (build the unsigned ordering lace, run `ordering::tau`, map ids back).
fn finalized_order(lace: &Blocklace, participants: &[[u8; 32]]) -> Vec<([u8; 32], u64)> {
    let mut ordering_lace = dregg_blocklace::Blocklace::new();
    let mut to_ord: HashMap<BlockId, dregg_blocklace::BlockId> = HashMap::new();
    let mut to_cs: HashMap<dregg_blocklace::BlockId, ([u8; 32], u64)> = HashMap::new();

    let mut blocks: Vec<(&BlockId, &Block)> = lace.iter().collect();
    blocks.sort_by(|(_, a), (_, b)| a.seq.cmp(&b.seq).then_with(|| a.creator.cmp(&b.creator)));

    for (fid, block) in blocks {
        let predecessors: Vec<dregg_blocklace::BlockId> = block
            .predecessors
            .iter()
            .filter_map(|p| to_ord.get(p).copied())
            .collect();
        let payload = match &block.payload {
            Payload::Turn(d) => d.clone(),
            Payload::Ack => vec![],
            _ => vec![0x00],
        };
        let ob = dregg_blocklace::Block::new(block.creator, block.seq, predecessors, payload);
        let oid = ob.id();
        let _ = ordering_lace.insert_unverified(ob);
        to_ord.insert(*fid, oid);
        to_cs.insert(oid, (block.creator, block.seq));
    }

    dregg_blocklace::ordering::tau(&ordering_lace, participants)
        .into_iter()
        .filter_map(|oid| to_cs.get(&oid).copied())
        .collect()
}

/// A node that has RECEIVED some causally-closed subset of the DAG. `merge` is the
/// live catch-up path (topo-sort + closure check); it REJECTS a non-closed delta,
/// so every subset we feed must itself be causally closed.
fn node_view(self_key: &SigningKey, participants: &[[u8; 32]], received: Vec<Block>) -> Blocklace {
    let quorum = supermajority_threshold(participants.len());
    let mut lace = Blocklace::new(self_key.clone(), quorum);
    lace.merge(received)
        .expect("delivered subset must be causally closed");
    lace
}

// ── 1. Baseline: a PERFECT n=3 DAG finalizes every wave (rule is correct). ──────
#[test]
fn n3_full_dag_finalizes_both_waves() {
    let keys: Vec<SigningKey> = (0..3).map(|i| key(10 + i)).collect();
    let ks: Vec<&SigningKey> = keys.iter().collect();
    let participants: Vec<[u8; 32]> = keys.iter().map(pubkey).collect();

    let by_round = build_rounds(&ks, 6); // 2 waves of wavelength 3
    let all: Vec<Block> = by_round.into_iter().flatten().collect();

    let lace = node_view(&keys[0], &participants, all);
    let order = finalized_order(&lace, &participants);
    eprintln!("[n3 full 6 rounds] finalized {} blocks", order.len());
    assert_eq!(
        order.len(),
        18,
        "perfect n=3 DAG must finalize all 18 blocks (2 waves)"
    );
}

// ── 1b. n=3, FOUR clean waves finalize (rule is not the 2-wave ceiling). ────────
//    If the pure round-synchronous rule finalizes 4 waves at n=3, then the LIVE
//    "stall after 2 turns" is NOT the ordering rule on a clean DAG — it must be a
//    live DAG-SHAPE defect (frontier skew / mixed-round predecessors / a duplicate
//    leader block) that the producer creates under the zero-slack leap-frog.
#[test]
fn n3_four_clean_waves_all_finalize() {
    let keys: Vec<SigningKey> = (0..3).map(|i| key(10 + i)).collect();
    let ks: Vec<&SigningKey> = keys.iter().collect();
    let participants: Vec<[u8; 32]> = keys.iter().map(pubkey).collect();

    let by_round = build_rounds(&ks, 12); // 4 waves of wavelength 3
    let all: Vec<Block> = by_round.into_iter().flatten().collect();
    let lace = node_view(&keys[0], &participants, all);
    let order = finalized_order(&lace, &participants);
    eprintln!(
        "[n3 clean 12 rounds / 4 waves] finalized {} of 36 blocks",
        order.len()
    );
    assert_eq!(
        order.len(),
        36,
        "a clean n=3 DAG must finalize ALL 4 waves — the rule has no 2-wave ceiling"
    );
}

// ── 1c. n=3, wave leader has a DUPLICATE block at the wave-start round → that
//    wave (and every wave whose coverage depends on ratifying it) is SKIPPED.
//    Models the live hazard: the faucet node is BOTH turn-carrier AND the wave's
//    round-robin leader; if it emits two blocks that land at the same DAG-depth
//    round (the leap-frog under zero slack), `find_all_final_leaders` requires
//    `leader_blocks.len()==1` and skips the wave.
#[test]
fn n3_duplicate_leader_block_skips_the_wave() {
    let keys: Vec<SigningKey> = (0..3).map(|i| key(10 + i)).collect();
    let ks: Vec<&SigningKey> = keys.iter().collect();
    let participants: Vec<[u8; 32]> = keys.iter().map(pubkey).collect();

    // Wave 1 = rounds 4..6, leader = participants[1 % 3] = key(11). Build 6 clean
    // rounds, then ADD a second block by the wave-1 leader at the wave-start round
    // (round 4 / seq 3) citing the same round-3 cohort — a duplicate leader block.
    let by_round = build_rounds(&ks, 6);
    let mut all: Vec<Block> = by_round.iter().flatten().cloned().collect();
    let round3_ids: Vec<BlockId> = by_round[2].iter().map(|b| b.id()).collect();
    // key(11) is participants[1], the wave-1 leader. A second, DIFFERENT round-4
    // block (distinct payload → distinct id) at the same round.
    let dup = Block::new(&keys[1], 3, Payload::Turn(vec![0xAA]), round3_ids);
    all.push(dup);

    let lace = node_view(&keys[0], &participants, all);
    let order = finalized_order(&lace, &participants);
    // Wave 0 (rounds 1..3, leader key(10)) still finalizes; wave 1 is skipped
    // because its leader has 2 blocks at the wave start.
    eprintln!(
        "[n3 duplicate wave-1 leader] finalized {} blocks (wave 1 leader duplicated)",
        order.len()
    );
    assert!(
        order.len() < 18,
        "a duplicated wave leader must SKIP that wave (fewer than all 18 finalize)"
    );
}

// ── 2. n=3, ONE last-round block missing from a node's view → NO finalization. ──
//    This is the DELIVER step at the zero-slack boundary: the observer holds a
//    causally-closed DAG that is complete EXCEPT one creator's wave-last-round
//    block. supermajority(3)==3, so 2 ratifiers at the wave end < 3 → the wave
//    leader is never super-ratified and the observer finalizes NOTHING.
#[test]
fn n3_one_missing_last_round_block_halts_finalization() {
    let keys: Vec<SigningKey> = (0..3).map(|i| key(10 + i)).collect();
    let ks: Vec<&SigningKey> = keys.iter().collect();
    let participants: Vec<[u8; 32]> = keys.iter().map(pubkey).collect();

    // Wave 0 = rounds 1..3 (seq 0..2). Deliver rounds 0,1 in full, but at the
    // wave's LAST round (seq 2) drop creator-0's block. The remaining two
    // round-2 blocks (from creators 1,2) cite the full round-1 cohort, so the
    // delivered subset is still causally closed.
    let by_round = build_rounds(&ks, 3);
    let mut delivered: Vec<Block> = Vec::new();
    delivered.extend(by_round[0].iter().cloned()); // round 1: all 3
    delivered.extend(by_round[1].iter().cloned()); // round 2: all 3
    // round 3 (last of wave 0): DROP creator-0's block; keep creators 1 and 2.
    delivered.extend(by_round[2].iter().skip(1).cloned());

    let gapped = node_view(&keys[0], &participants, delivered);
    let order_gapped = finalized_order(&gapped, &participants);

    // Control: the same DAG WITH creator-0's last-round block finalizes wave 0.
    let full: Vec<Block> = by_round.into_iter().flatten().collect();
    let full_lace = node_view(&keys[0], &participants, full);
    let order_full = finalized_order(&full_lace, &participants);

    eprintln!(
        "[n3 wave-last gap] supermajority(3)={}, gapped finalized {}, full finalized {}",
        supermajority_threshold(3),
        order_gapped.len(),
        order_full.len()
    );
    assert!(
        !order_full.is_empty(),
        "control: the COMPLETE wave-0 DAG must finalize"
    );
    assert!(
        order_gapped.is_empty(),
        "n=3 zero-slack: one missing wave-last-round block must drop below super-ratification"
    );
}

// ── 3. n=4, the SAME single-block gap still finalizes (the slack n=3 lacks). ────
#[test]
fn n4_one_missing_last_round_block_still_finalizes() {
    let keys: Vec<SigningKey> = (0..4).map(|i| key(20 + i)).collect();
    let ks: Vec<&SigningKey> = keys.iter().collect();
    let participants: Vec<[u8; 32]> = keys.iter().map(pubkey).collect();

    let by_round = build_rounds(&ks, 3);
    let mut delivered: Vec<Block> = Vec::new();
    delivered.extend(by_round[0].iter().cloned()); // round 1: all 4
    delivered.extend(by_round[1].iter().cloned()); // round 2: all 4
    delivered.extend(by_round[2].iter().skip(1).cloned()); // round 3: drop 1 of 4

    let gapped = node_view(&keys[0], &participants, delivered);
    let order = finalized_order(&gapped, &participants);

    eprintln!(
        "[n4 wave-last gap] supermajority(4)={}, finalized {} blocks",
        supermajority_threshold(4),
        order.len()
    );
    assert!(
        !order.is_empty(),
        "n=4 has slack (supermajority(4)=3<4): one missing wave-last-round block is routed around"
    );
}
