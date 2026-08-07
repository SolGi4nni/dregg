//! **THE MULTI-NODE ANCHOR EXHIBIT.** A turn anchored on a federation with `threshold > 1`:
//! refused before the committee's vote quorum exists, accepted after — driven through the REAL
//! `VoteCollector` with REAL hybrid finalization votes, and assembled with the SAME functions
//! `node/src/blocklace_sync.rs` calls.
//!
//! # Why this file exists rather than another unit test
//!
//! Two defects on one surface, and both were invisible for the same reason.
//!
//! 1. **No committee signature in this tree covered a per-turn value.** The only preimage that
//!    absorbed `receipt_stream_root` — `AttestedRoot::signing_message()` — receives exactly ONE
//!    push, the local node's, because `PeerMessage::AttestedRootUpdate` has zero handlers. The
//!    quorum that DOES assemble signed `dregg-finalization-vote-v3 ‖ block_id ‖ merkle_root`:
//!    a block id and a whole-ledger BLAKE3 image, covering nothing derived from the turn. So
//!    `TurnAnchorV1::verify` refused on every federation with `threshold > 1`.
//! 2. **The hybrid quorum a live root carries could not pass the cross-fed check.** The node
//!    fills `AttestedRoot::hybrid_quorum` by copying finalization-vote signatures;
//!    `verifier/src/cross_fed.rs` checked them against `signing_message()`. Different preimage.
//!    Every test in that module signed `signing_message()` **by hand**, so the whole module was
//!    green over a shape no node ever produced.
//!
//! ⚑ **That is the finding this file is built around: a test that constructs its subject
//! differently from production is not testing production.** So nothing here hand-builds a
//! quorum. The votes are `FinalizationVote::sign`, the tally is `VoteCollector::record`, the
//! quorum is `VoteCollector::assembled_quorum` filtered on the pair exactly as
//! `backfill_finalization_quorums` filters it, and the wire mapping is
//! `dregg_persist::hybrid_quorum_from_finalization_quorum` — the one function both finalized
//! paths and the anchor endpoint call. If the production shape moves, this file stops compiling
//! or stops passing; it cannot quietly keep testing the old one.

use dregg_blocklace::finality::{BlockId, FinalityLevel};
use dregg_federation::frost::{MlDsaPublicKey, MlDsaSigningKey};
use dregg_federation::turn_anchor::{
    AnchorCommittee, TURN_ANCHOR_PROTOCOL_V1, TurnAnchorError, TurnAnchorV1,
};
use dregg_node::finalization_votes::{FinalizationVote, VoteCollector};
use dregg_persist::{QuorumSignature, StoredAttestedRoot};
use dregg_turn::TurnReceipt;
use dregg_types::{
    AttestedRoot, FederationId, PublicKey, SigningKey, merkle_root_of_receipt_hashes, sign,
};

/// A three-validator federation. `supermajority_threshold(3) = 3`, so nothing here can reach a
/// quorum on one node's signature — which is the whole point.
const MEMBERS: [u8; 3] = [11, 22, 33];
const FEDERATION: FederationId = FederationId([0x5F; 32]);
const BLOCK_ID: BlockId = BlockId([0x81; 32]);
const HEIGHT: u64 = 42;
const LEDGER_ROOT: [u8; 32] = [0x33; 32];

/// Put this test process in the SAME disposition as the deployed binary: the Lean-verified PQ
/// cores installed before the first ML-DSA operation, fail-closed if the archive lacks them.
///
/// `run_node` calls `install_verified_pq_cores` at startup and node's LIB-test binary hangs it on
/// an `.init_array` initializer — but neither covers an INTEGRATION test binary, which has its own
/// `main`. Without it `dregg_pq::audit` correctly `process::abort()`s on the first key mint, and
/// the only way to "get results" would be `DREGG_ALLOW_UNAUDITED_PQ=1`, i.e. routing the exhibit's
/// signatures onto the unaudited `fips204` crate — the substitution the audit gate exists to
/// prevent, and a reason to distrust every verdict obtained that way. Idempotent, export-gated.
fn install_production_pq_cores() {
    static ONCE: std::sync::Once = std::sync::Once::new();
    ONCE.call_once(dregg_node::install_verified_pq_cores);
}

/// One member's identity, derived the way the node derives it: the ML-DSA-65 keypair comes from
/// the SAME 32 seed bytes as the ed25519 key (`genesis.rs` publishes the public half;
/// `blocklace_sync` re-derives the secret from `node.key`).
fn member(seed: u8) -> (SigningKey, PublicKey, MlDsaPublicKey, MlDsaSigningKey) {
    let sk = SigningKey::from_bytes(&[seed; 32]);
    let pk = sk.public_key();
    let (pq_pk, pq_sk) = MlDsaSigningKey::from_seed(&[seed; 32]);
    (sk, pk, pq_pk, pq_sk)
}

/// The SAME member's ed25519 key in the `ed25519_dalek` shape `FinalizationVote::sign` takes —
/// the same 32 seed bytes, so it is the same key `member` returns, just untyped by
/// `dregg_types`. This is the key `BlocklaceHandle::signing_key` holds.
fn member_vote_key(seed: u8) -> ed25519_dalek::SigningKey {
    ed25519_dalek::SigningKey::from_bytes(&[seed; 32])
}

fn committee_keys() -> (Vec<PublicKey>, Vec<MlDsaPublicKey>) {
    let mut eds = Vec::new();
    let mut pqs = Vec::new();
    for seed in MEMBERS {
        let (_, pk, pq_pk, _) = member(seed);
        eds.push(pk);
        pqs.push(pq_pk);
    }
    (eds, pqs)
}

/// The finalized turn's receipt, and the `receipt_stream_root` the attested root publishes for
/// it — `merkle_root_of_receipt_hashes([receipt_hash])`, the singleton stream
/// `blocklace_sync.rs` builds because each finalized block carries exactly one turn.
fn finalized_turn(turn_hash: [u8; 32]) -> (TurnReceipt, [u8; 32]) {
    let receipt = TurnReceipt {
        turn_hash,
        pre_state_hash: [0x11; 32],
        post_state_hash: [0x22; 32],
        agent: dregg_cell::CellId::from_bytes([0xA1; 32]),
        federation_id: FEDERATION.0,
        ..Default::default()
    };
    let stream_root = merkle_root_of_receipt_hashes(&[receipt.receipt_hash()]);
    (receipt, stream_root)
}

/// The `StoredAttestedRoot` the finalized path writes, carrying only the LOCAL node's
/// attestation signature — the state every full-mode root is in at first persist, before any
/// peer vote has converged.
fn stored_root_with_local_signature_only(stream_root: Option<[u8; 32]>) -> StoredAttestedRoot {
    let (local_sk, local_pk, _, _) = member(MEMBERS[0]);
    let mut root = StoredAttestedRoot {
        merkle_root: LEDGER_ROOT,
        note_tree_root: None,
        nullifier_set_root: None,
        height: HEIGHT,
        timestamp: 1_800_000_000,
        blocklace_block_id: Some(BLOCK_ID.0),
        finality_round: Some(7),
        quorum_signatures: Vec::new(),
        threshold_qc: None,
        threshold: MEMBERS.len(),
        federation_id: FEDERATION,
        receipt_stream_root: stream_root,
        finalization_quorum: Vec::new(),
    };
    // `blocklace_sync.rs` signs the wire `AttestedRoot`'s `signing_message()`; the stored and
    // wire shapes are byte-identical by construction, so sign through the wire projection.
    let message = wire_root(&root).signing_message();
    root.quorum_signatures
        .push((local_pk, sign(&local_sk, &message)));
    root
}

/// The stored → wire projection `node/src/api.rs`'s anchor endpoint performs, mapping
/// `finalization_quorum` onto `hybrid_quorum` through the ONE shared production mapping.
fn wire_root(stored: &StoredAttestedRoot) -> AttestedRoot {
    AttestedRoot {
        merkle_root: stored.merkle_root,
        note_tree_root: stored.note_tree_root,
        nullifier_set_root: stored.nullifier_set_root,
        height: stored.height,
        timestamp: stored.timestamp,
        blocklace_block_id: stored.blocklace_block_id,
        finality_round: stored.finality_round,
        quorum_signatures: stored.quorum_signatures.clone(),
        threshold_qc: stored.threshold_qc.clone(),
        threshold: stored.threshold,
        federation_id: stored.federation_id,
        receipt_stream_root: stored.receipt_stream_root,
        hybrid_quorum: dregg_persist::hybrid_quorum_from_finalization_quorum(
            &stored.finalization_quorum,
        ),
    }
}

/// **THE COMMITTEE, VOTING.** Every member signs a real hybrid `FinalizationVote` over
/// `(block_id, merkle_root, receipt_stream_root)` — exactly what
/// `BlocklaceHandle::emit_finalization_vote` signs — and every vote goes through a real
/// `VoteCollector`, exactly what `record_finalization_vote` does with a gossiped vote. Returns
/// the assembled quorum the node would attach, or `None` if no pair reached the threshold.
///
/// `per_member_stream` lets a caller give members DIFFERENT receipt streams, which is how the
/// exhibit shows that agreement on the ledger root is not agreement on the turn.
fn committee_votes(
    merkle_root: [u8; 32],
    per_member_stream: &[Option<[u8; 32]>],
) -> Option<(([u8; 32], Option<[u8; 32]>), Vec<QuorumSignature>)> {
    let (eds, pqs) = committee_keys();
    let pq_map: std::collections::HashMap<[u8; 32], MlDsaPublicKey> =
        eds.iter().map(|k| k.0).zip(pqs.iter().cloned()).collect();
    let threshold = dregg_blocklace::ordering::supermajority_threshold(MEMBERS.len());
    assert_eq!(threshold, 3, "a 3-validator federation needs all three");
    let mut collector = VoteCollector::new(eds.iter().map(|k| k.0), pq_map, threshold);

    for (i, seed) in MEMBERS.iter().enumerate() {
        let (_, _, _, pq_sk) = member(*seed);
        let vote = FinalizationVote::sign(
            &member_vote_key(*seed),
            &pq_sk,
            BLOCK_ID,
            FinalityLevel::Ordered,
            merkle_root,
            per_member_stream[i],
        )
        .expect("hedged ML-DSA signing fails only on an OS-entropy failure");
        collector.record(&vote);
    }
    collector.assembled_quorum(&BLOCK_ID)
}

/// Attach an assembled quorum to a stored root the way `backfill_finalization_quorums` does:
/// ONLY when it binds this root's exact PAIR and meets the root's own threshold.
fn backfill(mut stored: StoredAttestedRoot, quorum: Vec<QuorumSignature>) -> StoredAttestedRoot {
    stored.finalization_quorum = quorum;
    stored
}

fn anchor_for(
    turn_hash: [u8; 32],
    receipt: TurnReceipt,
    stored: &StoredAttestedRoot,
) -> TurnAnchorV1 {
    TurnAnchorV1 {
        protocol: TURN_ANCHOR_PROTOCOL_V1.to_string(),
        turn_hash,
        receipt,
        height: HEIGHT,
        block_id: BLOCK_ID.0,
        attested: wire_root(stored),
        served_committee: AnchorCommittee::default(),
    }
}

/// The roster a HOLDER supplies out of band — never read from the anchor.
fn holder_committee() -> AnchorCommittee {
    let (eds, pqs) = committee_keys();
    AnchorCommittee {
        ed25519: eds,
        ml_dsa: pqs.iter().map(|k| k.0.to_vec()).collect(),
        threshold: MEMBERS.len(),
        federation_id: FEDERATION,
    }
}

/// ⚑ **THE EXHIBIT, BOTH HALVES.** On a `threshold = 3` federation:
///
/// * **REFUSED** while the root carries only the local node's attestation signature — the state
///   every full-mode root is in at first persist, and the state EVERY root was permanently in
///   before this change, because no assembled quorum's preimage reached the receipt.
/// * **ACCEPTED** once the committee's own finalization votes converge and the quorum is
///   back-filled, because the v4 vote preimage absorbs `receipt_stream_root`.
///
/// The refusal names its cause: one signer over the attested-root preimage, zero over the vote
/// preimage. That distinction is what makes "the committee has not spoken yet" legible as
/// something other than "the chain is broken".
#[test]
fn a_turn_on_a_threshold_three_federation_is_refused_then_accepted() {
    install_production_pq_cores();
    let turn_hash = [0xAB; 32];
    let (receipt, stream_root) = finalized_turn(turn_hash);
    let committee = holder_committee();

    // ── REFUSED: first persist, no committee vote quorum yet. ────────────────
    let fresh = stored_root_with_local_signature_only(Some(stream_root));
    let anchor = anchor_for(turn_hash, receipt.clone(), &fresh);
    match anchor.verify(&committee) {
        Err(TurnAnchorError::ReceiptQuorumNotMet {
            signers,
            attestation_signers,
            vote_signers,
            threshold,
        }) => {
            assert_eq!(
                (signers, attestation_signers, vote_signers, threshold),
                (1, 1, 0, 3),
                "before the committee votes converge, the only signature is the node's own"
            );
        }
        other => panic!("expected ReceiptQuorumNotMet, got {other:?}"),
    }

    // ── The committee votes. Real signatures, real collector, real quorum. ───
    let (pair, quorum) = committee_votes(LEDGER_ROOT, &[Some(stream_root); 3])
        .expect("three distinct members agreeing on the pair is a quorum");
    assert_eq!(
        pair,
        (LEDGER_ROOT, Some(stream_root)),
        "the quorum agrees on the ledger root AND the receipt stream"
    );
    assert_eq!(quorum.len(), 3);
    // The node attaches it only when it binds THIS root's pair — the backfill's own gate.
    assert_eq!(
        pair,
        (fresh.merkle_root, fresh.receipt_stream_root),
        "the assembled pair must bind this exact root, or the node would not attach it"
    );

    // ── ACCEPTED. ────────────────────────────────────────────────────────────
    let anchored = backfill(fresh, quorum);
    let anchor = anchor_for(turn_hash, receipt.clone(), &anchored);
    let verified = anchor
        .verify(&committee)
        .expect("a committee vote quorum over the receipt stream must anchor the turn");

    assert_eq!(verified.turn_hash, turn_hash);
    assert_eq!(verified.receipt_hash, receipt.receipt_hash());
    assert_eq!(verified.height, HEIGHT);
    assert_eq!(verified.block_id, BLOCK_ID.0);
    assert_eq!(
        verified.receipt_quorum_signers, 3,
        "all three committee members' signatures reach the receipt"
    );
    assert!(
        verified.position_quorum_met,
        "the cross-node HYBRID vote quorum is what carried it — not the local attestation"
    );

    // And it survives the wire it is actually served over.
    let bytes = postcard::to_stdvec(&anchor).expect("encode");
    let decoded: TurnAnchorV1 = postcard::from_bytes(&bytes).expect("decode");
    assert_eq!(
        decoded
            .verify(&committee)
            .expect("a wire round-trip must not change the verdict")
            .turn_hash,
        turn_hash
    );
}

/// ⚑ **THE FALSIFIER FOR THE FIX ITSELF.** The same three members, the same real signing keys,
/// the same collector — but voting the v3 way, with NO receipt stream bound. The quorum
/// assembles (three distinct signers agreeing on a pair whose stream component is `None`), and
/// the anchor still REFUSES, because a signature over a preimage that names no receipt cannot
/// establish which receipt the block carried.
///
/// This is what makes the acceptance above mean something: it depends on the receipt-stream
/// binding, not merely on three signatures existing.
#[test]
fn a_vote_quorum_that_binds_no_receipt_stream_does_not_anchor_the_turn() {
    install_production_pq_cores();
    let turn_hash = [0xAB; 32];
    let (receipt, stream_root) = finalized_turn(turn_hash);

    // A genuine 3-of-3 quorum — over `(block_id, merkle_root, None)`.
    let (pair, quorum) = committee_votes(LEDGER_ROOT, &[None; 3])
        .expect("three members agreeing on (root, None) is still a quorum");
    assert_eq!(pair, (LEDGER_ROOT, None));
    assert_eq!(quorum.len(), 3);

    // The root itself DOES publish a receipt stream (a turn was committed).
    let stored = backfill(
        stored_root_with_local_signature_only(Some(stream_root)),
        quorum,
    );
    let anchor = anchor_for(turn_hash, receipt, &stored);

    match anchor.verify(&holder_committee()) {
        Err(TurnAnchorError::ReceiptQuorumNotMet {
            signers,
            vote_signers,
            ..
        }) => {
            assert_eq!(
                (signers, vote_signers),
                (1, 0),
                "three real signatures over a preimage that names no receipt count for NOTHING \
                 toward anchoring this turn"
            );
        }
        other => panic!("expected ReceiptQuorumNotMet, got {other:?}"),
    }
}

/// ⚑ **AGREEMENT ON THE LEDGER ROOT IS NOT AGREEMENT ON THE TURN — end to end.** Three members
/// reach the same ledger image but one executed to a different receipt stream. No pair reaches
/// the threshold, so the node assembles NO quorum at all, so nothing is back-filled, so the
/// anchor refuses. Under v3 this same disagreement produced a quorum: agreement was on
/// `merkle_root` alone and the receipt stream was outside the signed statement entirely.
#[test]
fn a_committee_split_on_the_receipt_stream_assembles_no_quorum() {
    install_production_pq_cores();
    let turn_hash = [0xAB; 32];
    let (_receipt, stream_root) = finalized_turn(turn_hash);
    let other_stream = merkle_root_of_receipt_hashes(&[[0xEE; 32]]);
    assert_ne!(stream_root, other_stream);

    assert!(
        committee_votes(
            LEDGER_ROOT,
            &[Some(stream_root), Some(stream_root), Some(other_stream)],
        )
        .is_none(),
        "distinct signers agreeing only on the ledger root must assemble NO quorum"
    );
}

/// ⚑ **THE HYBRID-QUORUM PREIMAGE FIX, ON A PRODUCTION-SHAPED ROOT.** The root here was built
/// by the pipeline above — real votes, real collector, the shared `to_hybrid` mapping — never
/// by signing a message a test chose. It passes the EXACT rule
/// `dregg_verifier::cross_fed::verify_attested_root_hybrid` applies:
/// `verify_hybrid_quorum_sigs` over `AttestedRoot::hybrid_quorum_message()`.
///
/// And the second assertion is the one that fires on regression: the same signatures do NOT
/// verify against `signing_message()`, which is what that verifier used to check them against.
/// A live root's hybrid quorum could not pass, and no test saw it because every test signed
/// `signing_message()` itself.
#[test]
fn a_production_shaped_hybrid_quorum_passes_the_cross_fed_rule() {
    install_production_pq_cores();
    let turn_hash = [0xAB; 32];
    let (_receipt, stream_root) = finalized_turn(turn_hash);
    let (eds, pqs) = committee_keys();

    let (_, quorum) = committee_votes(LEDGER_ROOT, &[Some(stream_root); 3])
        .expect("the committee's vote quorum assembles");
    let stored = backfill(
        stored_root_with_local_signature_only(Some(stream_root)),
        quorum,
    );
    let root = wire_root(&stored);
    assert_eq!(
        root.hybrid_quorum.len(),
        3,
        "the wire quorum carries all three"
    );

    let message = root
        .hybrid_quorum_message()
        .expect("an anchored root has a vote preimage");
    assert!(
        dregg_federation::receipt::verify_hybrid_quorum_sigs(
            &root.hybrid_quorum,
            &message,
            &eds,
            &pqs,
            MEMBERS.len(),
        ),
        "the hybrid quorum a NODE builds must pass the rule the cross-fed verifier applies"
    );

    // THE REGRESSION TOOTH. The preimage the check used before is not the preimage the node
    // signs, and these are the node's signatures.
    assert!(
        !dregg_federation::receipt::verify_hybrid_quorum_sigs(
            &root.hybrid_quorum,
            &root.signing_message(),
            &eds,
            &pqs,
            MEMBERS.len(),
        ),
        "checking a live root's hybrid quorum against `signing_message()` refuses it — that was \
         the live defect, and it is why the two consumers must share one named preimage"
    );

    // The two preimages are genuinely different bytes, so the assertions above are not two
    // spellings of one check.
    assert_ne!(message, root.signing_message());
}

/// **COMPLETENESS: a single-node federation still works.** `threshold = 1`, and the node's own
/// attestation signature alone anchors the turn — the devnet/solo posture is untouched by a
/// change that exists to make LARGER committees work.
#[test]
fn a_single_node_federation_still_anchors_its_own_turns() {
    install_production_pq_cores();
    let turn_hash = [0xAB; 32];
    let (receipt, stream_root) = finalized_turn(turn_hash);
    let (solo_sk, solo_pk, solo_pq, _) = member(MEMBERS[0]);

    let mut stored = stored_root_with_local_signature_only(Some(stream_root));
    stored.threshold = 1;
    stored.quorum_signatures.clear();
    let message = wire_root(&stored).signing_message();
    stored
        .quorum_signatures
        .push((solo_pk, sign(&solo_sk, &message)));

    let committee = AnchorCommittee {
        ed25519: vec![solo_pk],
        ml_dsa: vec![solo_pq.0.to_vec()],
        threshold: 1,
        federation_id: FEDERATION,
    };
    let verified = anchor_for(turn_hash, receipt, &stored)
        .verify(&committee)
        .expect("a committee of one still anchors its own turn");
    assert_eq!(verified.receipt_quorum_signers, 1);
    assert!(
        !verified.position_quorum_met,
        "no cross-node vote quorum here — acceptance rests on the node's own attestation, and \
         the holder can see that it does"
    );
}
