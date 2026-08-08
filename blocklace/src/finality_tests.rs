//! Tests for the blocklace data structure.

use std::collections::HashSet;

use ed25519_dalek::SigningKey;
use rand::rngs::OsRng;

use crate::dregg_bridge::{CodManager, DreggBlocklaceBridge, ExecutionTier, classify_turn};
use crate::finality::{
    Block, BlockError, Blocklace, CONSENSUS_TIME_V1_MAX_FORWARD_SECONDS,
    CONSENSUS_TIME_V1_WIRE_LEN, ConsensusTimePolicyV1, ConsensusTimeV1, ConsensusTimeWireError,
    ConsensusTimedTurnPayloadV1, CreatorTips, FinalityLevel, FinalityTracker, Payload,
    TurnArtifactBundle,
};

fn random_key() -> SigningKey {
    SigningKey::generate(&mut OsRng)
}

// ─── Signature Verification ──────────────────────────────────────────────────

#[test]
fn create_block_and_verify_signature() {
    let key = random_key();
    let mut lace = Blocklace::new_simple(key);
    let block = lace.add_block(Payload::Data(b"hello".to_vec()));
    assert_eq!(block.seq, 1);
    assert!(block.verify_signature().is_ok());
}

#[test]
fn tampered_block_fails_verification() {
    let key = random_key();
    let mut lace = Blocklace::new_simple(key);
    let mut block = lace.add_block(Payload::Data(b"hello".to_vec()));
    // Tamper with the payload.
    block.payload = Payload::Data(b"tampered".to_vec());
    assert!(block.verify_signature().is_err());
}

#[test]
fn turn_bundle_payload_roundtrips_and_binds_signature() {
    let key = random_key();
    let bundle = TurnArtifactBundle {
        signed_turn: b"signed-turn".to_vec(),
        receipt: Some(b"receipt".to_vec()),
        witnessed_receipts: vec![b"witness-a".to_vec(), b"witness-b".to_vec()],
    };

    let block = Block::new(&key, 7, Payload::TurnBundle(bundle.clone()), Vec::new());
    let encoded = block.to_bytes();
    let decoded = Block::from_bytes(&encoded).expect("bundle block decodes");

    assert_eq!(decoded.payload, Payload::TurnBundle(bundle));
    assert!(decoded.verify_signature().is_ok());

    let mut tampered = decoded.clone();
    if let Payload::TurnBundle(tampered_bundle) = &mut tampered.payload {
        tampered_bundle.witnessed_receipts[0][0] ^= 0x01;
    } else {
        panic!("decoded payload must be a turn bundle");
    }
    assert!(tampered.verify_signature().is_err());
}

// ─── Consensus-authenticated time ───────────────────────────────────────────

#[test]
fn consensus_time_wire_is_fixed_width_and_strict() {
    let claim = ConsensusTimeV1::new(-1_234_567_890);
    let encoded = claim.encode();
    assert_eq!(encoded.len(), CONSENSUS_TIME_V1_WIRE_LEN);
    assert_eq!(ConsensusTimeV1::decode(&encoded), Ok(claim));

    assert!(matches!(
        ConsensusTimeV1::decode(&encoded[..encoded.len() - 1]),
        Err(ConsensusTimeWireError::Length(_))
    ));
    let mut trailing = encoded.to_vec();
    trailing.push(0);
    assert!(matches!(
        ConsensusTimeV1::decode(&trailing),
        Err(ConsensusTimeWireError::Length(_))
    ));
    let mut bad_magic = encoded;
    bad_magic[0] ^= 1;
    assert_eq!(
        ConsensusTimeV1::decode(&bad_magic),
        Err(ConsensusTimeWireError::Magic)
    );
    let mut bad_version = encoded;
    bad_version[4] = 2;
    assert_eq!(
        ConsensusTimeV1::decode(&bad_version),
        Err(ConsensusTimeWireError::Version(2))
    );
    let mut bad_reserved = encoded;
    bad_reserved[6] = 1;
    assert_eq!(
        ConsensusTimeV1::decode(&bad_reserved),
        Err(ConsensusTimeWireError::Reserved)
    );
}

#[test]
fn consensus_time_is_signed_block_identity_not_local_clock_input() {
    let key = random_key();
    let unrelated_local_clock_a = 1_i64;
    let unrelated_local_clock_b = i64::MAX;
    assert_ne!(unrelated_local_clock_a, unrelated_local_clock_b);

    let payload = ConsensusTimedTurnPayloadV1::with_artifacts(
        1_700_000_000,
        b"signed-turn".to_vec(),
        Some(b"receipt".to_vec()),
        vec![b"witness".to_vec()],
    );
    let a = Block::new(
        &key,
        7,
        Payload::ConsensusTimedTurnV1(payload.clone()),
        vec![],
    );
    let b = Block::new(&key, 7, Payload::ConsensusTimedTurnV1(payload), vec![]);
    assert_eq!(a.id(), b.id(), "local clocks are not an execution input");
    assert_eq!(a.signature, b.signature);

    let different_time = Block::new(
        &key,
        7,
        Payload::ConsensusTimedTurnV1(ConsensusTimedTurnPayloadV1::new(
            1_700_000_001,
            b"signed-turn".to_vec(),
        )),
        vec![],
    );
    assert_ne!(a.id(), different_time.id());
    assert_ne!(a.signature, different_time.signature);

    let decoded = Block::from_bytes(&a.to_bytes()).expect("timed block decodes");
    assert_eq!(decoded, a);
    assert!(decoded.verify_signature().is_ok());
    let mut tampered = decoded;
    if let Payload::ConsensusTimedTurnV1(payload) = &mut tampered.payload {
        *payload = ConsensusTimedTurnPayloadV1::new(1_700_000_002, b"signed-turn".to_vec());
    }
    assert!(tampered.verify_signature().is_err());
}

#[test]
fn consensus_time_admission_is_causal_bounded_and_ack_transparent() {
    let anchor = 1_700_000_000;
    let key_a = random_key();
    let key_b = random_key();
    let mut lace = Blocklace::new_simple(random_key());
    lace.enable_consensus_time_v1(ConsensusTimePolicyV1::new(anchor))
        .unwrap();

    let genesis = Block::new(
        &key_a,
        1,
        Payload::ConsensusTimedTurnV1(ConsensusTimedTurnPayloadV1::new(anchor, b"g".to_vec())),
        vec![],
    );
    lace.receive_block(genesis.clone()).unwrap();

    // A non-turn block inherits the frontier. The next turn need inspect only this immediate ACK,
    // not walk through it to rediscover the timed ancestor.
    let ack = Block::new(&key_b, 1, Payload::Ack, vec![genesis.id()]);
    lace.receive_block(ack.clone()).unwrap();
    let at_bound = Block::new(
        &key_a,
        2,
        Payload::ConsensusTimedTurnV1(ConsensusTimedTurnPayloadV1::new(
            anchor + CONSENSUS_TIME_V1_MAX_FORWARD_SECONDS,
            b"at-bound".to_vec(),
        )),
        vec![ack.id()],
    );
    lace.receive_block(at_bound.clone()).unwrap();

    let regression = Block::new(
        &key_b,
        2,
        Payload::ConsensusTimedTurnV1(ConsensusTimedTurnPayloadV1::new(
            anchor + CONSENSUS_TIME_V1_MAX_FORWARD_SECONDS - 1,
            b"regression".to_vec(),
        )),
        vec![at_bound.id()],
    );
    assert!(matches!(
        lace.receive_block(regression),
        Err(BlockError::ConsensusTimeRegression { .. })
    ));

    let too_far = Block::new(
        &key_b,
        3,
        Payload::ConsensusTimedTurnV1(ConsensusTimedTurnPayloadV1::new(
            anchor + 2 * CONSENSUS_TIME_V1_MAX_FORWARD_SECONDS + 1,
            b"future".to_vec(),
        )),
        vec![at_bound.id()],
    );
    assert!(matches!(
        lace.receive_block(too_far),
        Err(BlockError::ConsensusTimeForwardBound { .. })
    ));

    let legacy = Block::new(
        &key_b,
        4,
        Payload::Turn(b"timestamp-less".to_vec()),
        vec![at_bound.id()],
    );
    assert!(matches!(
        lace.receive_block(legacy),
        Err(BlockError::LegacyTurnAfterConsensusTimeCutover)
    ));
}

#[test]
fn consensus_time_flag_day_and_failed_local_production_are_atomic() {
    let anchor = 1_700_000_000;
    let mut nonempty = Blocklace::new_simple(random_key());
    nonempty.add_block(Payload::Data(b"prehistory".to_vec()));
    assert!(matches!(
        nonempty.enable_consensus_time_v1(ConsensusTimePolicyV1::new(anchor)),
        Err(BlockError::ConsensusTimeFlagDayRequiresEmptyLace)
    ));

    let mut lace = Blocklace::new_simple(random_key());
    lace.enable_consensus_time_v1(ConsensusTimePolicyV1::new(anchor))
        .unwrap();
    let before_tips = lace.tips().clone();
    assert!(matches!(
        lace.try_add_block(Payload::ConsensusTimedTurnV1(
            ConsensusTimedTurnPayloadV1::new(anchor + 1, b"wrong-genesis".to_vec())
        )),
        Err(BlockError::ConsensusGenesisTimeMismatch { .. })
    ));
    assert_eq!(lace.len(), 0);
    assert_eq!(lace.tips(), &before_tips);

    let first = lace
        .add_consensus_timed_turn_v1(ConsensusTimedTurnPayloadV1::new(anchor, b"first".to_vec()))
        .unwrap();
    assert_eq!(first.seq, 1, "failed attempt must not consume sequence");
    let before_len = lace.len();
    let before_tips = lace.tips().clone();
    assert!(matches!(
        lace.try_add_block(Payload::Turn(b"legacy".to_vec())),
        Err(BlockError::LegacyTurnAfterConsensusTimeCutover)
    ));
    assert_eq!(lace.len(), before_len);
    assert_eq!(lace.tips(), &before_tips);
}

#[test]
fn consensus_time_restart_rebuilds_authenticated_frontier_and_continues() {
    let anchor = 1_700_000_000;
    let key = random_key();
    let mut live = Blocklace::new(key.clone(), 3);
    live.enable_consensus_time_v1(ConsensusTimePolicyV1::new(anchor))
        .unwrap();

    let first = live
        .add_consensus_timed_turn_v1_with_predecessors(
            ConsensusTimedTurnPayloadV1::new(anchor, b"first".to_vec()),
            Vec::new(),
        )
        .unwrap();
    let ack = live.add_block_with_predecessors(Payload::Ack, vec![first.id()]);
    let checkpoint = live.checkpoint();

    // The checkpoint contains signed authority only; policy and its derived cache are rebuilt.
    let mut restarted = Blocklace::from_checkpoint(&checkpoint, key, 3).unwrap();
    assert_eq!(restarted.consensus_time_policy_v1(), None);
    restarted
        .restore_consensus_time_v1(ConsensusTimePolicyV1::new(anchor))
        .unwrap();
    assert_eq!(
        restarted.consensus_time_policy_v1(),
        Some(ConsensusTimePolicyV1::new(anchor))
    );

    let proposed = restarted
        .suggest_consensus_time_v1(&[ack.id()], i64::MAX)
        .unwrap();
    assert_eq!(proposed, anchor + CONSENSUS_TIME_V1_MAX_FORWARD_SECONDS);
    let next = restarted
        .add_consensus_timed_turn_v1_with_predecessors(
            ConsensusTimedTurnPayloadV1::new(proposed, b"after-restart".to_vec()),
            vec![ack.id()],
        )
        .unwrap();
    assert_eq!(
        next.payload,
        Payload::ConsensusTimedTurnV1(ConsensusTimedTurnPayloadV1::new(
            proposed,
            b"after-restart".to_vec()
        ))
    );
}

#[test]
fn consensus_time_restore_refuses_legacy_turn_history_atomically() {
    let anchor = 1_700_000_000;
    let key = random_key();
    let mut old = Blocklace::new(key.clone(), 3);
    old.add_block(Payload::Turn(b"timestamp-less-history".to_vec()));
    let checkpoint = old.checkpoint();
    let mut restarted = Blocklace::from_checkpoint(&checkpoint, key, 3).unwrap();

    assert!(matches!(
        restarted.restore_consensus_time_v1(ConsensusTimePolicyV1::new(anchor)),
        Err(BlockError::LegacyTurnAfterConsensusTimeCutover)
    ));
    assert_eq!(
        restarted.consensus_time_policy_v1(),
        None,
        "failed migration must not partially install the flag day"
    );
}

#[test]
fn consensus_time_suggestion_is_anchor_exact_then_causally_clamped() {
    let anchor = 1_700_000_000;
    let mut lace = Blocklace::new_simple(random_key());
    lace.enable_consensus_time_v1(ConsensusTimePolicyV1::new(anchor))
        .unwrap();

    assert_eq!(
        lace.suggest_consensus_time_v1(&[], i64::MIN).unwrap(),
        anchor
    );
    assert_eq!(
        lace.suggest_consensus_time_v1(&[], i64::MAX).unwrap(),
        anchor,
        "opposite producer clocks must still yield identical genesis claims"
    );

    let genesis = lace
        .add_consensus_timed_turn_v1_with_predecessors(
            ConsensusTimedTurnPayloadV1::new(anchor, b"genesis".to_vec()),
            Vec::new(),
        )
        .unwrap();
    assert_eq!(
        lace.suggest_consensus_time_v1(&[genesis.id()], i64::MIN)
            .unwrap(),
        anchor
    );
    assert_eq!(
        lace.suggest_consensus_time_v1(&[genesis.id()], i64::MAX)
            .unwrap(),
        anchor + CONSENSUS_TIME_V1_MAX_FORWARD_SECONDS
    );
}

#[test]
fn consensus_time_v1_explicitly_permits_hostile_repeated_max_steps() {
    let anchor = 1_700_000_000;
    let mut lace = Blocklace::new_simple(random_key());
    lace.enable_consensus_time_v1(ConsensusTimePolicyV1::new(anchor))
        .unwrap();

    let mut predecessor = lace
        .add_consensus_timed_turn_v1_with_predecessors(
            ConsensusTimedTurnPayloadV1::new(anchor, b"genesis".to_vec()),
            Vec::new(),
        )
        .unwrap()
        .id();
    for step in 1..=4 {
        let hostile_wall = i64::MAX;
        let claim = lace
            .suggest_consensus_time_v1(&[predecessor], hostile_wall)
            .unwrap();
        assert_eq!(claim, anchor + step * CONSENSUS_TIME_V1_MAX_FORWARD_SECONDS);
        predecessor = lace
            .add_consensus_timed_turn_v1_with_predecessors(
                ConsensusTimedTurnPayloadV1::new(claim, vec![step as u8]),
                vec![predecessor],
            )
            .unwrap()
            .id();
    }

    // This is intentionally a pinned limitation, not a fairness claim: CTM1 gives deterministic
    // replay and a per-edge bound. A federation-grade policy must replace producer choice with an
    // agreed round/beacon/median rule before this coordinate governs real-time expiries.
    let final_claim = lace
        .get(&predecessor)
        .and_then(|block| match &block.payload {
            Payload::ConsensusTimedTurnV1(payload) => Some(payload.consensus_time().unix_seconds()),
            _ => None,
        })
        .unwrap();
    assert_eq!(
        final_claim,
        anchor + 4 * CONSENSUS_TIME_V1_MAX_FORWARD_SECONDS
    );
}

// ─── Virtual Chain ───────────────────────────────────────────────────────────

#[test]
fn virtual_chain_is_ordered() {
    let key = random_key();
    let mut lace = Blocklace::new_simple(key);
    let creator = lace.self_creator();

    lace.add_block(Payload::Data(b"a".to_vec()));
    lace.add_block(Payload::Data(b"b".to_vec()));
    lace.add_block(Payload::Data(b"c".to_vec()));

    let chain = lace.virtual_chain(&creator);
    assert_eq!(chain.len(), 3);
    assert_eq!(chain[0].seq, 1);
    assert_eq!(chain[1].seq, 2);
    assert_eq!(chain[2].seq, 3);
}

// ─── Merge ───────────────────────────────────────────────────────────────────

#[test]
fn merge_two_independent_blocklaces() {
    let key_a = random_key();
    let key_b = random_key();
    let creator_a = Block::hybrid_id(&key_a);
    let creator_b = Block::hybrid_id(&key_b);

    let mut lace_a = Blocklace::new_simple(key_a);
    let mut lace_b = Blocklace::new_simple(key_b);

    lace_a.add_block(Payload::Data(b"from A".to_vec()));
    lace_a.add_block(Payload::Data(b"from A2".to_vec()));
    lace_b.add_block(Payload::Data(b"from B".to_vec()));

    // Merge B's blocks into A.
    let delta = lace_b.all_blocks();
    lace_a.merge(delta).unwrap();

    assert_eq!(lace_a.len(), 3);
    assert_eq!(lace_a.virtual_chain(&creator_a).len(), 2);
    assert_eq!(lace_a.virtual_chain(&creator_b).len(), 1);
}

// ─── Equivocation Detection ──────────────────────────────────────────────────

#[test]
fn detect_equivocation_same_seq() {
    let key = random_key();
    let creator = Block::hybrid_id(&key);

    // Create two blocks with same seq but different content.
    let block_a = Block::new(&key, 1, Payload::Data(b"version A".to_vec()), vec![]);
    let block_b = Block::new(&key, 1, Payload::Data(b"version B".to_vec()), vec![]);

    let mut lace = Blocklace::new_simple(random_key());

    // Insert block_a directly.
    lace.receive_block(block_a.clone()).unwrap();

    // Receiving block_b should detect equivocation.
    let result = lace.receive_block(block_b.clone());
    assert!(result.is_err());
    match result.unwrap_err() {
        BlockError::Equivocation { creator: c, .. } => {
            assert_eq!(c, creator);
        }
        other => panic!("expected equivocation, got: {other:?}"),
    }

    assert!(lace.equivocators().contains(&creator));
}

#[test]
fn detect_equivocation_incomparable_different_seq() {
    // The NEW case that the old `(creator, seq, id≠)` heuristic MISSED:
    // an equivocator forks its virtual chain and extends ONE branch, so the two
    // tip blocks have DIFFERENT seq numbers yet are mutually non-preceding
    // (incomparable). Under the paper's content-independent Def 4.2 this is an
    // equivocation; under the old same-seq heuristic it slips through.
    //
    // Construct:
    //   base (seq 1, no preds)                      ← genesis of the chain
    //   branch_a (seq 2, preds = [base])            ← honest-looking extension
    //   branch_b (seq 3, preds = [base])            ← FORK: extends base, NOT branch_a
    // branch_a (seq 2) and branch_b (seq 3) are by the same creator, distinct,
    // and neither is in the other's causal past (both only see `base`).
    let key = random_key();
    let creator = Block::hybrid_id(&key);

    let base = Block::new(&key, 1, Payload::Data(b"base".to_vec()), vec![]);
    let base_id = base.id();
    let branch_a = Block::new(&key, 2, Payload::Data(b"branch A".to_vec()), vec![base_id]);
    // FORK at a *different* seq than branch_a, pointing only at `base`.
    let branch_b = Block::new(&key, 3, Payload::Data(b"branch B".to_vec()), vec![base_id]);

    let mut lace = Blocklace::new_simple(random_key());
    lace.receive_block(base).unwrap();
    lace.receive_block(branch_a).unwrap(); // honest extension: NOT an equivocation
    assert!(
        !lace.equivocators().contains(&creator),
        "a single chain extension must not be flagged"
    );

    // Receiving branch_b (different seq, incomparable with branch_a) MUST be
    // detected as an equivocation. The old same-seq heuristic would have
    // returned Ok here (no other block at seq 3).
    let result = lace.receive_block(branch_b);
    match result {
        Err(BlockError::Equivocation { creator: c, .. }) => assert_eq!(c, creator),
        other => panic!("expected different-seq incomparable equivocation, got: {other:?}"),
    }
    assert!(lace.equivocators().contains(&creator));
}

#[test]
fn causally_ordered_blocks_not_flagged() {
    // The no-false-positive case: two blocks by ONE author where one observes
    // the other (a genuine honest virtual chain) must NOT be flagged. seq 1 →
    // seq 2 → seq 3, each acking the previous tip, are pairwise comparable.
    let key = random_key();
    let creator = Block::hybrid_id(&key);

    let b1 = Block::new(&key, 1, Payload::Data(b"1".to_vec()), vec![]);
    let b1_id = b1.id();
    let b2 = Block::new(&key, 2, Payload::Data(b"2".to_vec()), vec![b1_id]);
    let b2_id = b2.id();
    let b3 = Block::new(&key, 3, Payload::Data(b"3".to_vec()), vec![b2_id]);

    let mut lace = Blocklace::new_simple(random_key());
    lace.receive_block(b1).unwrap();
    lace.receive_block(b2).unwrap();
    lace.receive_block(b3).unwrap();

    assert!(
        !lace.equivocators().contains(&creator),
        "a straight-line virtual chain (each block observes its predecessor) \
         must never be flagged as equivocation"
    );
    assert_eq!(lace.equivocators().len(), 0);
}

// ─── Closure Enforcement ─────────────────────────────────────────────────────

#[test]
fn closure_enforcement() {
    let key = random_key();
    use crate::finality::BlockId;

    // Create a block that references a non-existent predecessor.
    let fake_pred = BlockId([0xAB; 32]);
    let block = Block::new(&key, 1, Payload::Ack, vec![fake_pred]);

    let mut lace = Blocklace::new_simple(random_key());
    let result = lace.receive_block(block);
    assert!(matches!(result, Err(BlockError::MissingPredecessor { .. })));
}

// ─── Causal Past ─────────────────────────────────────────────────────────────

#[test]
fn causal_past_computation() {
    let key = random_key();
    let mut lace = Blocklace::new_simple(key);

    let b1 = lace.add_block(Payload::Data(b"1".to_vec()));
    let b1_id = b1.id();
    let b2 = lace.add_block(Payload::Data(b"2".to_vec()));
    let b2_id = b2.id();
    let b3 = lace.add_block(Payload::Data(b"3".to_vec()));
    let b3_id = b3.id();

    // b3's causal past should include b2 and b1.
    let past = lace.causal_past(&b3_id);
    assert!(past.contains(&b2_id));
    assert!(past.contains(&b1_id));

    // b1's causal past should be empty.
    let past_b1 = lace.causal_past(&b1_id);
    assert!(past_b1.is_empty());
}

#[test]
fn is_predecessor_relation() {
    let key = random_key();
    let mut lace = Blocklace::new_simple(key);

    let b1 = lace.add_block(Payload::Data(b"1".to_vec()));
    let b1_id = b1.id();
    let b2 = lace.add_block(Payload::Data(b"2".to_vec()));
    let b2_id = b2.id();

    assert!(lace.is_predecessor(&b1_id, &b2_id));
    assert!(!lace.is_predecessor(&b2_id, &b1_id));
    assert!(!lace.is_predecessor(&b1_id, &b1_id));
}

// ─── Frontier ────────────────────────────────────────────────────────────────

#[test]
fn frontier_computation() {
    let key = random_key();
    let mut lace = Blocklace::new_simple(key);

    let _b1 = lace.add_block(Payload::Data(b"1".to_vec()));
    let _b2 = lace.add_block(Payload::Data(b"2".to_vec()));
    let b3 = lace.add_block(Payload::Data(b"3".to_vec()));

    // Only b3 should be in the frontier.
    let frontier = lace.frontier();
    assert_eq!(frontier.len(), 1);
    assert_eq!(frontier[0], b3.id());
}

#[test]
fn frontier_with_multiple_creators() {
    let key_a = random_key();
    let key_b = random_key();

    let mut lace = Blocklace::new_simple(key_a);

    // A creates a block.
    let _a1 = lace.add_block(Payload::Data(b"A1".to_vec()));

    // B creates an independent block (no predecessors in common).
    let b_block = Block::new(&key_b, 1, Payload::Data(b"B1".to_vec()), vec![]);
    lace.receive_block(b_block.clone()).unwrap();

    // Frontier should have both A's tip and B's block.
    let frontier = lace.frontier();
    assert_eq!(frontier.len(), 2);
}

// ─── CRDT Properties ─────────────────────────────────────────────────────────

#[test]
fn crdt_associativity() {
    let key_a = random_key();
    let key_b = random_key();
    let key_c = random_key();

    let mut source_a = Blocklace::new_simple(key_a.clone());
    let mut source_b = Blocklace::new_simple(key_b.clone());
    let mut source_c = Blocklace::new_simple(key_c.clone());

    source_a.add_block(Payload::Data(b"A1".to_vec()));
    source_b.add_block(Payload::Data(b"B1".to_vec()));
    source_c.add_block(Payload::Data(b"C1".to_vec()));

    let delta_a = source_a.all_blocks();
    let delta_b = source_b.all_blocks();
    let delta_c = source_c.all_blocks();

    // merge(A, merge(B, C))
    let mut lace_1 = Blocklace::new_simple(random_key());
    lace_1.merge(delta_b.clone()).unwrap();
    lace_1.merge(delta_c.clone()).unwrap();
    lace_1.merge(delta_a.clone()).unwrap();

    // merge(merge(A, B), C)
    let mut lace_2 = Blocklace::new_simple(random_key());
    lace_2.merge(delta_a.clone()).unwrap();
    lace_2.merge(delta_b.clone()).unwrap();
    lace_2.merge(delta_c.clone()).unwrap();

    // Both should have the same set of blocks.
    assert_eq!(lace_1.len(), lace_2.len());
    for (id, _) in lace_1.iter() {
        assert!(lace_2.contains(id));
    }
}

#[test]
fn crdt_idempotent() {
    let key = random_key();
    let mut source = Blocklace::new_simple(key);
    source.add_block(Payload::Data(b"x".to_vec()));

    let delta = source.all_blocks();

    let mut target = Blocklace::new_simple(random_key());
    target.merge(delta.clone()).unwrap();
    let len_after_first = target.len();

    // Merging again should not change anything.
    target.merge(delta).unwrap();
    assert_eq!(target.len(), len_after_first);
}

#[test]
fn crdt_commutative() {
    let key_a = random_key();
    let key_b = random_key();

    let mut source_a = Blocklace::new_simple(key_a);
    let mut source_b = Blocklace::new_simple(key_b);

    source_a.add_block(Payload::Data(b"A".to_vec()));
    source_b.add_block(Payload::Data(b"B".to_vec()));

    let delta_a = source_a.all_blocks();
    let delta_b = source_b.all_blocks();

    // A then B
    let mut lace_1 = Blocklace::new_simple(random_key());
    lace_1.merge(delta_a.clone()).unwrap();
    lace_1.merge(delta_b.clone()).unwrap();

    // B then A
    let mut lace_2 = Blocklace::new_simple(random_key());
    lace_2.merge(delta_b).unwrap();
    lace_2.merge(delta_a).unwrap();

    assert_eq!(lace_1.len(), lace_2.len());
    for (id, _) in lace_1.iter() {
        assert!(lace_2.contains(id));
    }
}

// ─── Large Scale ─────────────────────────────────────────────────────────────

#[test]
fn large_scale_merge() {
    let num_creators = 100;
    let blocks_per_creator = 10;

    let keys: Vec<SigningKey> = (0..num_creators).map(|_| random_key()).collect();
    let mut sources: Vec<Blocklace> = keys
        .iter()
        .map(|k| Blocklace::new_simple(k.clone()))
        .collect();

    // Each creator produces their blocks.
    for source in &mut sources {
        for i in 0..blocks_per_creator {
            source.add_block(Payload::Data(format!("block {i}").into_bytes()));
        }
    }

    // Merge all into one target.
    let mut target = Blocklace::new_simple(random_key());
    for source in &sources {
        let delta = source.all_blocks();
        target.merge(delta).unwrap();
    }

    assert_eq!(target.len(), num_creators * blocks_per_creator);

    // Each creator's virtual chain should be totally ordered.
    for key in &keys {
        let creator = Block::hybrid_id(&key);
        let chain = target.virtual_chain(&creator);
        assert_eq!(chain.len(), blocks_per_creator);
        for (i, block) in chain.iter().enumerate() {
            assert_eq!(block.seq, (i + 1) as u64);
        }
    }
}

// ─── Approval ────────────────────────────────────────────────────────────────

#[test]
fn approved_by_without_equivocation() {
    let key_a = random_key();
    let key_b = random_key();

    let mut lace = Blocklace::new_simple(key_a.clone());

    // B creates a block.
    let b_block = Block::new(&key_b, 1, Payload::Data(b"from B".to_vec()), vec![]);
    let b_id = b_block.id();
    lace.receive_block(b_block).unwrap();

    // A creates a block that sees B's block (through tips).
    let a_block = lace.add_block(Payload::Ack);
    let a_id = a_block.id();

    // A's block should approve B's block.
    assert!(lace.approved_by(&a_id, &b_id));
}

// ─── Delta For Peer ──────────────────────────────────────────────────────────

#[test]
fn delta_for_peer() {
    let key = random_key();
    let mut lace = Blocklace::new_simple(key);

    let b1 = lace.add_block(Payload::Data(b"1".to_vec()));
    let b1_id = b1.id();
    let _b2 = lace.add_block(Payload::Data(b"2".to_vec()));

    // Peer knows only b1.
    let known: HashSet<_> = [b1_id].into();
    let delta = lace.delta_for(&known);
    assert_eq!(delta.len(), 1);
    assert_eq!(delta[0].seq, 2);
}

// ─── Bridge Tests ────────────────────────────────────────────────────────────

#[test]
fn classify_turn_tiers() {
    let cod = CodManager::new(5);

    // Sovereign marker.
    let sovereign_turn = vec![0x01, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    assert_eq!(
        classify_turn(&sovereign_turn, &cod),
        ExecutionTier::Sovereign
    );

    // Optimistic marker (with budget).
    let optimistic_turn = vec![0x02, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    assert_eq!(
        classify_turn(&optimistic_turn, &cod),
        ExecutionTier::Optimistic
    );

    // Unknown marker -> Ordered.
    let ordered_turn = vec![0xFF, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    assert_eq!(classify_turn(&ordered_turn, &cod), ExecutionTier::Ordered);

    // Too short -> Ordered.
    let short_turn = vec![0x01, 0x02];
    assert_eq!(classify_turn(&short_turn, &cod), ExecutionTier::Ordered);
}

#[test]
fn cod_budget_management() {
    let mut cod = CodManager::new(2);
    let cell = [0x42; 32];

    assert!(cod.has_budget_for(&cell));
    cod.consume(&cell);
    assert!(cod.has_budget_for(&cell));
    cod.consume(&cell);
    assert!(!cod.has_budget_for(&cell)); // Budget exhausted.
    cod.release(&cell);
    assert!(cod.has_budget_for(&cell)); // Budget restored.
}

#[test]
fn bridge_submit_and_process() {
    let key = random_key();
    let mut lace = Blocklace::new(key, 3);
    let bridge = DreggBlocklaceBridge::new(5);

    let block_id = bridge.submit_turn(&mut lace, vec![0x01, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    assert!(lace.contains(&block_id));
    assert_eq!(lace.len(), 1);
}

// ─── Merge with causal closure failure ───────────────────────────────────────

#[test]
fn merge_not_causally_closed() {
    use crate::finality::{BlockId, MergeError};

    let key = random_key();
    // Create a block that references a non-existent predecessor.
    let fake_pred = BlockId([0xDE; 32]);
    let block = Block::new(&key, 1, Payload::Data(b"orphan".to_vec()), vec![fake_pred]);

    let mut target = Blocklace::new_simple(random_key());
    let result = target.merge(vec![block]);
    assert!(matches!(result, Err(MergeError::NotCausallyClosed { .. })));
}

// ─── Finality Level Ordering ────────────────────────────────────────────────

#[test]
fn finality_level_ordering_is_monotone() {
    // Verify the partial order: Local < Bilateral < Attested < Ordered
    assert!(FinalityLevel::Local < FinalityLevel::Bilateral);
    assert!(FinalityLevel::Bilateral < FinalityLevel::Attested);
    assert!(FinalityLevel::Attested < FinalityLevel::Ordered);
}

#[test]
fn finality_never_regresses() {
    let mut tracker = FinalityTracker::new(3); // quorum = 3
    let block_id = crate::finality::BlockId([0x42; 32]);

    // Start at Local.
    assert_eq!(tracker.finality_of(&block_id), FinalityLevel::Local);

    // First ack -> Bilateral.
    let level = tracker.record_ack(block_id, [1; 32]);
    assert_eq!(level, FinalityLevel::Bilateral);
    assert_eq!(tracker.finality_of(&block_id), FinalityLevel::Bilateral);

    // Second ack -> still Bilateral (not yet quorum).
    let level = tracker.record_ack(block_id, [2; 32]);
    assert_eq!(level, FinalityLevel::Bilateral);

    // Third ack -> Attested (quorum reached).
    let level = tracker.record_ack(block_id, [3; 32]);
    assert_eq!(level, FinalityLevel::Attested);
    assert_eq!(tracker.finality_of(&block_id), FinalityLevel::Attested);

    // Mark as ordered -> Ordered (strongest level).
    tracker.mark_ordered(block_id);
    assert_eq!(tracker.finality_of(&block_id), FinalityLevel::Ordered);

    // Additional acks don't regress it.
    tracker.record_ack(block_id, [4; 32]);
    assert_eq!(tracker.finality_of(&block_id), FinalityLevel::Ordered);
}

// ─── Remove Equivocator ─────────────────────────────────────────────────────

#[test]
fn remove_equivocator_excludes_from_tips() {
    let key_a = random_key();
    let key_b = random_key();
    let creator_b = Block::hybrid_id(&key_b);

    let mut lace = Blocklace::new_simple(key_a);

    // Receive a block from B.
    let b_block = Block::new(&key_b, 1, Payload::Data(b"from B".to_vec()), vec![]);
    lace.receive_block(b_block).unwrap();

    // B should be in tips.
    assert!(lace.tips().contains_key(&creator_b));

    // Remove B as equivocator.
    assert!(lace.remove_equivocator(&creator_b));

    // B should no longer be in tips.
    assert!(!lace.tips().contains_key(&creator_b));

    // B is in equivocators set.
    assert!(lace.is_equivocator(&creator_b));

    // Removing again returns false (already known).
    assert!(!lace.remove_equivocator(&creator_b));
}

#[test]
fn equivocator_blocks_dont_update_tips() {
    let key_a = random_key();
    let key_b = random_key();
    let creator_b = Block::hybrid_id(&key_b);

    let mut lace = Blocklace::new_simple(key_a);

    // B equivocates: two blocks at seq 1.
    let b1 = Block::new(&key_b, 1, Payload::Data(b"first".to_vec()), vec![]);
    let b1_id = b1.id();
    let b2 = Block::new(&key_b, 1, Payload::Data(b"second".to_vec()), vec![]);
    let b2_id = b2.id();

    lace.receive_block(b1).unwrap();
    let err = lace.receive_block(b2);
    assert!(err.is_err()); // equivocation detected

    // B is marked as equivocator and its tips entry is the PINNED evidence
    // pair (CM Alg. 1:5 two-tips floor) — both halves, so the next authored
    // block carries the fork into its closure. The old shape (entry deleted)
    // left the second half unreferenced forever.
    assert!(lace.is_equivocator(&creator_b));
    assert_eq!(
        lace.tips().get(&creator_b),
        Some(&CreatorTips::pair(b1_id, b2_id)),
        "detection must pin the incomparable pair as B's tips"
    );

    // Further blocks from B must NOT update the pinned entry (frozen; the
    // flood bound stays ≤ 2 pointers for B no matter how much it forks).
    let b3 = Block::new(
        &key_b,
        2,
        Payload::Data(b"after equivocation".to_vec()),
        vec![],
    );
    // This will succeed since there's no matching seq=2 yet and it has no predecessors.
    let _ = lace.receive_block(b3);
    assert_eq!(
        lace.tips().get(&creator_b),
        Some(&CreatorTips::pair(b1_id, b2_id)),
        "the pinned pair is frozen against later blocks from the equivocator"
    );
}

// ─── Serialization Roundtrip ────────────────────────────────────────────────

#[test]
fn block_serialization_roundtrip() {
    let key = random_key();
    let block = Block::new(&key, 42, Payload::Data(b"payload data".to_vec()), vec![]);
    let id_before = block.id();

    let bytes = block.to_bytes();
    let restored = Block::from_bytes(&bytes).unwrap();

    assert_eq!(restored.id(), id_before);
    assert_eq!(restored.creator, block.creator);
    assert_eq!(restored.seq, block.seq);
    assert_eq!(restored.payload, block.payload);
    assert_eq!(restored.signature, block.signature);
    assert!(restored.verify_signature().is_ok());
}

#[test]
fn block_from_invalid_bytes_returns_none() {
    let garbage = vec![0xFF, 0xFE, 0xFD, 0xFC];
    assert!(Block::from_bytes(&garbage).is_none());
}

// ─── Checkpoint ─────────────────────────────────────────────────────────────

#[test]
fn checkpoint_and_restore() {
    let key = random_key();
    let mut lace = Blocklace::new(key.clone(), 3);

    // Add some blocks.
    let b1 = lace.add_block(Payload::Data(b"one".to_vec()));
    let b1_id = b1.id();
    let b2 = lace.add_block(Payload::Data(b"two".to_vec()));
    let b2_id = b2.id();
    let _b3 = lace.add_block(Payload::Data(b"three".to_vec()));

    // Mark one as ordered.
    lace.finality.mark_ordered(b1_id);

    // Take a checkpoint.
    let checkpoint = lace.checkpoint();

    // Restore from checkpoint.
    let restored = Blocklace::from_checkpoint(&checkpoint, key, 3).unwrap();

    // Verify state matches.
    assert_eq!(restored.len(), lace.len());
    assert!(restored.contains(&b1_id));
    assert!(restored.contains(&b2_id));
    assert_eq!(restored.finality.ordered_sequence().len(), 1);
    assert_eq!(restored.finality.ordered_sequence()[0], b1_id);
}

// ─── Metrics ────────────────────────────────────────────────────────────────

#[test]
fn metrics_reflect_state() {
    let key = random_key();
    let mut lace = Blocklace::new(key, 3);

    let metrics = lace.metrics();
    assert_eq!(metrics.block_count, 0);
    assert_eq!(metrics.equivocator_count, 0);
    assert_eq!(metrics.finality_lag, 0);

    // Add blocks.
    let b1 = lace.add_block(Payload::Data(b"one".to_vec()));
    let b1_id = b1.id();
    lace.add_block(Payload::Data(b"two".to_vec()));
    lace.add_block(Payload::Data(b"three".to_vec()));

    let metrics = lace.metrics();
    assert_eq!(metrics.block_count, 3);
    assert_eq!(metrics.finality_lag, 3); // 3 blocks, none ordered

    // Order one block.
    lace.finality.mark_ordered(b1_id);

    let metrics = lace.metrics();
    assert_eq!(metrics.ordered_count, 1);
    assert_eq!(metrics.finality_lag, 2); // 3 total - 1 ordered = 2
}

// ─── Process Finalized Idempotency ─────────────────────────────────────────

#[test]
fn process_finalized_no_duplicates() {
    let key = random_key();
    let mut lace = Blocklace::new(key, 3);
    let mut bridge = DreggBlocklaceBridge::new(5);

    // Submit turns.
    let turn_data = vec![0x01, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    let id1 = bridge.submit_turn(&mut lace, turn_data.clone());
    let id2 = bridge.submit_turn(&mut lace, turn_data.clone());

    // Mark both as ordered.
    lace.finality.mark_ordered(id1);
    lace.finality.mark_ordered(id2);

    // First call: should produce 2 receipts.
    let receipts = bridge.process_finalized(&lace);
    assert_eq!(receipts.len(), 2);
    assert_eq!(receipts[0].finality_height, 1);
    assert_eq!(receipts[1].finality_height, 2);

    // Second call: should produce 0 receipts (already processed).
    let receipts = bridge.process_finalized(&lace);
    assert_eq!(receipts.len(), 0);

    // Add a third turn and order it.
    let id3 = bridge.submit_turn(&mut lace, turn_data);
    lace.finality.mark_ordered(id3);

    // Third call: should produce exactly 1 receipt (only the new one).
    let receipts = bridge.process_finalized(&lace);
    assert_eq!(receipts.len(), 1);
    assert_eq!(receipts[0].finality_height, 3);
}

// ─── Merge with Equivocator Blocks ─────────────────────────────────────────

#[test]
fn merge_equivocator_blocks_marks_equivocator() {
    let key_a = random_key();
    let key_b = random_key();
    let creator_b = Block::hybrid_id(&key_b);

    let mut lace = Blocklace::new_simple(key_a);

    // Create two conflicting blocks from B.
    let b1 = Block::new(&key_b, 1, Payload::Data(b"version A".to_vec()), vec![]);
    let b2 = Block::new(&key_b, 1, Payload::Data(b"version B".to_vec()), vec![]);

    // Merge both at once (simulating receiving a delta from a peer who saw both).
    let result = lace.merge(vec![b1, b2]);
    // Merge succeeds (inserts both as evidence) but the equivocator is detected.
    assert!(result.is_ok());
    assert!(lace.is_equivocator(&creator_b));
    assert_eq!(lace.len(), 2); // Both blocks kept as evidence
}

#[test]
fn merge_pins_evidence_pair_on_equivocation_detection() {
    // Audit gap C, under the two-tips floor: merge() must mirror
    // receive_block() — flag the creator AND pin the detected pair as its
    // frozen tips entry, which later same-delta blocks must not overwrite.
    let key_a = random_key();
    let key_b = random_key();
    let creator_b = Block::hybrid_id(&key_b);

    let mut lace = Blocklace::new_simple(key_a);

    // Build three blocks: a good seq-1, a CONFLICTING seq-1, and a seq-2.
    // If merge fails to consult `equivocators` when deciding tips, the
    // seq-2 block from B (which arrives after the equivocation was
    // detected within this same merge) would overwrite the pinned pair,
    // leaving dissemination/frontier state inconsistent with B's exclusion.
    let b1_good = Block::new(&key_b, 1, Payload::Data(b"good".to_vec()), vec![]);
    let b1_bad = Block::new(&key_b, 1, Payload::Data(b"bad".to_vec()), vec![]);
    let b2 = Block::new(&key_b, 2, Payload::Data(b"after".to_vec()), vec![]);

    let result = lace.merge(vec![b1_good, b1_bad, b2]);
    assert!(result.is_ok());
    assert!(lace.is_equivocator(&creator_b));
    match lace.tips().get(&creator_b) {
        Some(CreatorTips::Pair(_, _)) => {}
        other => panic!(
            "merge must pin B's detected incomparable pair as its tips entry \
             (frozen against the same-delta seq-2 block); got {other:?}"
        ),
    }
}

#[test]
fn round_of_returns_dag_depth() {
    let key_a = random_key();
    let key_b = random_key();
    let mut lace = Blocklace::new_simple(key_a.clone());

    // Genesis block from A (round 1).
    let block0 = lace.add_block(Payload::Data(b"genesis".to_vec()));
    let r0 = lace.round_of(&block0.id()).expect("round for genesis");
    assert_eq!(r0, 1);

    // A second block from A predecessing block0 (round 2).
    let block1 = lace.add_block(Payload::Data(b"second".to_vec()));
    let r1 = lace.round_of(&block1.id()).expect("round for block1");
    assert_eq!(r1, 2);

    // A block from B predecessing both A's blocks (round 3).
    let block2 = Block::new(
        &key_b,
        1,
        Payload::Data(b"b1".to_vec()),
        vec![block0.id(), block1.id()],
    );
    lace.receive_block(block2.clone()).expect("receive block2");
    let r2 = lace.round_of(&block2.id()).expect("round for block2");
    assert_eq!(r2, 3);
}

// ─── DIFFERENTIAL: merge is a PURE JOIN on the keyset (Lean LaceMerge) ──────────
//
// Differential against the Lean executable model `Dregg2/Distributed/LaceMerge.lean`,
// which proves `merge` is a join on the content-addressed keyset (`laceIds`):
//   * `laceIds_mergeLace` : keyset(merge B Δ) = keyset(B) ∪ keyset(Δ)
//   * `merge_comm` / `merge_assoc` / `merge_idem` / `merge_absorb`
//   * `merge_monotone`
// proved `#assert_axioms`-clean at n>1 over a Byzantine-forked block set
// (`LaceMerge.{b0, fork1, fork2}` / `replica1..replica3`). This test reproduces THAT
// witness shape against the REAL `finality.rs::merge`: a genesis `b0` from an honest
// creator plus a FORK (two seq-1 blocks from a Byzantine creator, each acking b0 but
// NOT each other — `LaceMerge`'s `f1 ∥ f2`), merged in three different orders/groupings
// across three replicas. The Lean theorem says all three converge to the SAME keyset
// regardless of arrival order, THROUGH the fork; this asserts the node's `merge` agrees.
#[test]
fn merge_join_order_independent_with_fork_differential() {
    let key_honest = random_key(); // creator `7` in LaceMerge
    let key_byz = random_key(); // creator `9` in LaceMerge (the equivocator)

    // The three causally-closed blocks (LaceMerge §8: b0, fork1, fork2).
    // b0: honest genesis (no preds).
    let b0 = Block::new(&key_honest, 0, Payload::Data(b"b0".to_vec()), vec![]);
    // fork1, fork2: two seq-1 byz blocks, each acking b0 but NOT each other (incomparable).
    let fork1 = Block::new(&key_byz, 1, Payload::Data(b"fork1".to_vec()), vec![b0.id()]);
    let fork2 = Block::new(&key_byz, 1, Payload::Data(b"fork2".to_vec()), vec![b0.id()]);

    // The shared content-addressed keyset every replica must converge to.
    let expected: HashSet<_> = [b0.id(), fork1.id(), fork2.id()].into_iter().collect();

    // Each delta must be causally closed (the `merge` precondition, modelled in Lean as
    // the `WellFormedDelta` hypothesis). The three replicas vary the ORDER/GROUPING of
    // closed deltas — which is exactly what order-independence is about.
    //
    // Replica R1 — first the genesis delta [b0], then the fork delta [fork1, fork2]
    // (b0 already present ⇒ the fork delta is closed). LaceMerge `replica1`.
    let mut r1 = Blocklace::new_simple(random_key());
    r1.merge(vec![b0.clone()]).unwrap();
    r1.merge(vec![fork1.clone(), fork2.clone()]).unwrap();

    // Replica R2 — same two closed deltas but the fork delta REVERSED internally
    // [fork2, fork1] (intra-delta order flipped). LaceMerge `replica2` shape.
    let mut r2 = Blocklace::new_simple(random_key());
    r2.merge(vec![b0.clone()]).unwrap();
    r2.merge(vec![fork2.clone(), fork1.clone()]).unwrap();

    // Replica R3 — everything as ONE closed delta onto empty (a fresh joiner), with b0
    // listed AFTER the fork blocks (topological_sort reorders for insertion). `replica3`.
    let mut r3 = Blocklace::new_simple(random_key());
    r3.merge(vec![fork2.clone(), fork1.clone(), b0.clone()])
        .unwrap();

    let ids = |b: &Blocklace| -> HashSet<_> { b.iter().map(|(id, _)| *id).collect() };

    // ORDER-INDEPENDENCE at n>1 THROUGH a Byzantine fork: all three converge to the
    // SAME keyset = laceIds B ∪ laceIds Δ  (Lean `laceIds_mergeLace` + `merge_comm`/`_assoc`).
    assert_eq!(
        ids(&r1),
        expected,
        "R1 keyset must be the join {{b0,fork1,fork2}}"
    );
    assert_eq!(
        ids(&r1),
        ids(&r2),
        "merge_comm: R1 and R2 converge (opposite order)"
    );
    assert_eq!(ids(&r2), ids(&r3), "merge_assoc: R3 (single delta) agrees");

    // IDEMPOTENCE / ABSORPTION (Lean `merge_idem` / `merge_absorb`): re-merging
    // already-present blocks is inert on the keyset.
    r1.merge(vec![fork1.clone(), fork2.clone()]).unwrap();
    assert_eq!(
        ids(&r1),
        expected,
        "merge_idem: re-merging the fork delta is inert"
    );

    // MONOTONICITY (Lean `merge_monotone`): the honest genesis survives the fork-merge —
    // merging never drops a block.
    assert!(
        ids(&r1).contains(&b0.id()),
        "merge_monotone: b0 retained through fork"
    );

    // The fork IS detected (the equivocation view is a deterministic function of the
    // converged keyset — the same on every replica, per LaceMerge's §1 note).
    let byz_creator = Block::hybrid_id(&key_byz);
    assert!(r1.is_equivocator(&byz_creator));
    assert!(r2.is_equivocator(&byz_creator));
    assert!(r3.is_equivocator(&byz_creator));
}

// ─── Exclusion-by-past: the two-tips evidence floor and its poles ───────────
//
// Flag day 2026-08-08. Exclusion of an equivocator is a PREDICATE over each
// block's own causal closure (`node(b) ∉ byz(⌊b⌋)`, blocklace paper §4.3 —
// Lean spec + poles: `Dregg2.Distributed.ExclusionByPast`), never a mutation
// of live membership. What makes the predicate REACHABLE is the CM Alg. 1:5
// two-tips floor: detection pins the incomparable pair as the creator's
// `CreatorTips::Pair`, the next authored block points at both halves, and the
// fork enters every later closure. These tests drive the floor and the three
// poles the Lean theorems name: cross-node agreement (`excluded_agrees_across_
// nodes`), restart durability (`excluded_recomputed_after_restart`), and the
// partial-view safety pole (`honest_not_excluded`).

/// THE FLOOR: detection pins the pair; the next authored block carries BOTH
/// halves into its closure (asserted PRESENT before any verdict is read —
/// the falsifier discipline); the anchor-relative predicate then fires; and
/// the pin is welded away so later blocks repel the equivocator entirely.
#[test]
fn two_tips_floor_carries_pair_and_welds() {
    let key_a = random_key();
    let key_b = random_key();
    let creator_b = Block::hybrid_id(&key_b);

    let mut lace = Blocklace::new_simple(key_a);

    let b1 = Block::new(&key_b, 1, Payload::Data(b"fork L".to_vec()), vec![]);
    let b1_id = b1.id();
    let b2 = Block::new(&key_b, 1, Payload::Data(b"fork R".to_vec()), vec![]);
    let b2_id = b2.id();

    lace.receive_block(b1).unwrap();
    assert!(lace.receive_block(b2).is_err(), "fork detected");
    assert_eq!(
        lace.tips().get(&creator_b),
        Some(&CreatorTips::pair(b1_id, b2_id)),
        "detection pins the pair"
    );

    // The next authored block links BOTH halves (the tips ARE its predecessors).
    let w = lace.add_block(Payload::Ack);
    assert!(
        w.predecessors.contains(&b1_id) && w.predecessors.contains(&b2_id),
        "the authored block must point at both fork halves (CM Alg. 1:5)"
    );

    // MUTATION ASSERTED PRESENT BEFORE THE VERDICT: the pair is in w's closure.
    let past = lace.causal_past(&w.id());
    assert!(
        past.contains(&b1_id) && past.contains(&b2_id),
        "the incomparable pair must be IN the carrier's causal past"
    );
    // Now the verdict: the anchor-relative exclusion predicate fires — w
    // observes the fork, so it approves NEITHER half.
    assert!(!lace.approved_by(&w.id(), &b1_id));
    assert!(!lace.approved_by(&w.id(), &b2_id));

    // THE WELD: carrying the pair once clears the pin; from here on we repel —
    // no further direct acks of the equivocator, evidence rides our own chain.
    assert!(
        !lace.tips().contains_key(&creator_b),
        "the pinned pair is cleared once a local block carries both halves"
    );
    let w2 = lace.add_block(Payload::Ack);
    assert!(
        !w2.predecessors.contains(&b1_id) && !w2.predecessors.contains(&b2_id),
        "later blocks never directly ack the equivocator again (repelling)"
    );
    // ... but still observe the pair transitively through our own chain.
    let past2 = lace.causal_past(&w2.id());
    assert!(past2.contains(&b1_id) && past2.contains(&b2_id));
    assert!(!lace.approved_by(&w2.id(), &b1_id));
}

/// CROSS-NODE POLE: two nodes receive the fork halves in OPPOSITE orders —
/// the one thing that differs between honest nodes, and the input the deleted
/// `auto_evict` keyed consensus state on. After exchanging deltas their
/// verdicts are identical on every (anchor, target) pair.
#[test]
fn exclusion_verdict_identical_across_arrival_orders() {
    let key_a = random_key();
    let key_c = random_key();
    let key_b = random_key();
    let creator_b = Block::hybrid_id(&key_b);

    let b1 = Block::new(&key_b, 1, Payload::Data(b"fork L".to_vec()), vec![]);
    let b1_id = b1.id();
    let b2 = Block::new(&key_b, 1, Payload::Data(b"fork R".to_vec()), vec![]);
    let b2_id = b2.id();

    // Node A sees L then R; node C sees R then L.
    let mut lace_a = Blocklace::new_simple(key_a);
    lace_a.receive_block(b1.clone()).unwrap();
    let _ = lace_a.receive_block(b2.clone());
    let mut lace_c = Blocklace::new_simple(key_c);
    lace_c.receive_block(b2).unwrap();
    let _ = lace_c.receive_block(b1);

    // Both flag B (the global eqvc set is arrival-order independent) …
    assert!(lace_a.is_equivocator(&creator_b));
    assert!(lace_c.is_equivocator(&creator_b));
    // … and both pin the SAME pair as a set (the halves swap roles only).
    let pair_of = |l: &Blocklace| match l.tips().get(&creator_b) {
        Some(CreatorTips::Pair(x, y)) => {
            let mut v = [*x, *y];
            v.sort();
            v
        }
        other => panic!("expected a pinned pair, got {other:?}"),
    };
    assert_eq!(pair_of(&lace_a), pair_of(&lace_c));

    // Each authors a carrier, then they exchange everything (CRDT merge).
    let w_a = lace_a.add_block(Payload::Ack);
    let w_c = lace_c.add_block(Payload::Ack);
    lace_a.merge(lace_c.all_blocks()).unwrap();
    lace_c.merge(lace_a.all_blocks()).unwrap();
    assert_eq!(lace_a.len(), lace_c.len(), "converged block sets");

    // MUTATION PRESENT BEFORE VERDICT, on both nodes.
    for lace in [&lace_a, &lace_c] {
        for w in [&w_a, &w_c] {
            let past = lace.causal_past(&w.id());
            assert!(past.contains(&b1_id) && past.contains(&b2_id));
        }
    }
    // The verdict is a function of committed structure alone: IDENTICAL on
    // both nodes, for every anchor and every target (Lean
    // `excluded_agrees_across_nodes`).
    for anchor in [w_a.id(), w_c.id()] {
        for target in [b1_id, b2_id] {
            assert_eq!(
                lace_a.approved_by(&anchor, &target),
                lace_c.approved_by(&anchor, &target),
                "cross-node verdict divergence at anchor {anchor:?} target {target:?}"
            );
            assert!(!lace_a.approved_by(&anchor, &target));
        }
    }
}

/// RESTART POLE — the one the deleted mutation failed. The exclusion verdict
/// is recomputed identically from the persisted blocks by BOTH restore paths
/// (authenticated re-derivation and trusted verbatim), because it is a
/// function of the blocks alone (Lean `excluded_recomputed_after_restart`).
/// Before this flag day, the eviction lived in `constitution.participants`,
/// was never a block, and a restart silently reinstated the equivocator.
#[test]
fn exclusion_survives_restart_on_both_restore_paths() {
    let key_a = random_key();
    let key_b = random_key();
    let creator_b = Block::hybrid_id(&key_b);

    let mut lace = Blocklace::new_simple(key_a.clone());
    let b1 = Block::new(&key_b, 1, Payload::Data(b"fork L".to_vec()), vec![]);
    let b1_id = b1.id();
    let b2 = Block::new(&key_b, 1, Payload::Data(b"fork R".to_vec()), vec![]);
    let b2_id = b2.id();
    lace.receive_block(b1).unwrap();
    let _ = lace.receive_block(b2);
    let w = lace.add_block(Payload::Ack);
    let w_id = w.id();

    // Pre-restart verdict, with the pair asserted present first.
    assert!(lace.causal_past(&w_id).contains(&b1_id));
    assert!(lace.causal_past(&w_id).contains(&b2_id));
    assert!(!lace.approved_by(&w_id, &b1_id));
    assert!(lace.is_equivocator(&creator_b));

    let checkpoint = lace.checkpoint();

    // Authenticated re-derivation (`from_checkpoint`): everything re-verified,
    // tips/equivocators re-DERIVED from the blocks.
    let restored = Blocklace::from_checkpoint(&checkpoint, key_a.clone(), 1).unwrap();
    assert!(
        restored.is_equivocator(&creator_b),
        "equivocator flag re-derived from the blocks"
    );
    assert!(restored.causal_past(&w_id).contains(&b1_id));
    assert!(restored.causal_past(&w_id).contains(&b2_id));
    assert!(!restored.approved_by(&w_id, &b1_id));
    assert!(!restored.approved_by(&w_id, &b2_id));

    // Trusted verbatim restore (`from_checkpoint_trusted`, the node's own-disk
    // boot path): identical verdict.
    let trusted = Blocklace::from_checkpoint_trusted(&checkpoint, key_a, 1).unwrap();
    assert!(trusted.is_equivocator(&creator_b));
    assert!(!trusted.approved_by(&w_id, &b1_id));
    assert!(!trusted.approved_by(&w_id, &b2_id));
}

/// PARTIAL-VIEW POLE: a node holding only ONE fork half excludes nobody its
/// peers keep — no pair, no verdict (Lean `honest_not_excluded` /
/// `demo_half_view_keeps_f1`). Exclusion becomes expressible exactly when the
/// pair arrives, never on rumor.
#[test]
fn partial_view_does_not_exclude() {
    let key_d = random_key();
    let key_b = random_key();
    let creator_b = Block::hybrid_id(&key_b);

    let mut lace = Blocklace::new_simple(key_d);
    let b1 = Block::new(&key_b, 1, Payload::Data(b"only half".to_vec()), vec![]);
    let b1_id = b1.id();
    lace.receive_block(b1).unwrap();

    assert!(!lace.is_equivocator(&creator_b), "no pair ⇒ no flag");
    assert_eq!(
        lace.tips().get(&creator_b),
        Some(&CreatorTips::One(b1_id)),
        "B looks honest on this view: a single chain-head tip"
    );

    // A block authored on this view APPROVES B's half — B is kept.
    let w = lace.add_block(Payload::Ack);
    assert!(
        lace.approved_by(&w.id(), &b1_id),
        "a partial view must keep the member its peers keep"
    );
}

/// THE FLOOD BOUND: a k-way fork pins exactly the FIRST detected pair — the
/// pointer contribution per equivocator is ≤ 2 no matter how many
/// incomparable blocks it mints (the cap half of CM Alg. 1:5, structural).
#[test]
fn pinned_pair_bounds_flood_at_two() {
    let key_a = random_key();
    let key_b = random_key();
    let creator_b = Block::hybrid_id(&key_b);

    let mut lace = Blocklace::new_simple(key_a);
    let forks: Vec<Block> = (0..4u8)
        .map(|i| Block::new(&key_b, 1, Payload::Data(vec![i]), vec![]))
        .collect();
    lace.receive_block(forks[0].clone()).unwrap();
    for f in &forks[1..] {
        let _ = lace.receive_block(f.clone());
    }

    match lace.tips().get(&creator_b) {
        Some(CreatorTips::Pair(_, _)) => {}
        other => panic!("expected the first pinned pair, got {other:?}"),
    }
    let b_tips: Vec<_> = lace
        .tip_ids()
        .into_iter()
        .filter(|id| lace.get(id).map(|b| b.creator) == Some(creator_b))
        .collect();
    assert_eq!(
        b_tips.len(),
        2,
        "≤ 2 pointers per creator, k-way fork or not"
    );
    assert_eq!(lace.len(), 5, "all fork blocks retained as evidence");
}
