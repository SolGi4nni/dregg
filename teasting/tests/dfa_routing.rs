//! DFA routing integration tests: governed route tables, classification, and amendment.
//!
//! Tests the full lifecycle of DFA-governed message routing:
//! - Compile route patterns into a DFA table
//! - Classify messages and verify correct dispatch
//! - Governance: propose new routes, update atomically (compare-and-swap)
//! - Verify classification changes after route amendment
//! - Revocation: remove a route, messages get Drop classification

use dregg_captp::FederationId;
use dregg_dfa_federation::{FederationQcVerifier, governed_router_with_committee};
use dregg_federation::threshold::{
    FederationCommittee, MemberSecret, PartialSignature, generate_test_committee,
    generate_test_committee_with_seed,
};
use dregg_teasting::federation::quick_federation;
use dregg_types::CellId;
use dregg_wire::dfa_router::{
    DispatchDecision, GovernanceProof, GovernedRouter, RouteTarget, RouteUpdateError, Router,
    cell_target, compile_routes, dispatch_path, federation_target, target_as_cell,
    target_as_federation,
};

// THE VERIFIED PQ CORES, for THIS test binary. Every node this file builds derives a
// HYBRID identity — `H(ed25519_pk ‖ ml_dsa_pk)` — through `dregg_blocklace`, and
// `dregg-blocklace` installs a core only under its OWN `cfg(test)`, which is not set when
// it is compiled as a dependency here. With nothing installed `dregg-pq` refuses the
// ML-DSA keygen with an uncatchable `process::abort()`, so every test in this binary died
// as a bare SIGABRT having asserted NOTHING. Process-start, so no test can beat it and
// `--test-threads` cannot change the outcome. See `dregg-pq-testkit`'s crate docs.
dregg_pq_testkit::install_at_process_start!();

fn cell_id(byte: u8) -> CellId {
    CellId([byte; 32])
}

fn fed_id(byte: u8) -> FederationId {
    FederationId([byte; 32])
}

/// Sign `old ‖ new` with `signer_count` committee members and postcard-encode
/// the resulting `ThresholdQC` exactly as `FederationQcVerifier::verify`
/// expects it on the wire. This is the SAME construction as
/// `dfa-federation`'s model test `governance_swap_requires_real_threshold_signature`;
/// it produces a genuine BLS aggregate threshold signature, not an arbitrary blob.
fn sign_swap(
    committee: &FederationCommittee,
    members: &[MemberSecret],
    signer_count: usize,
    old: &[u8; 32],
    new: &[u8; 32],
) -> Vec<u8> {
    let message = FederationQcVerifier::signing_message(old, new);
    let shares: Vec<(usize, PartialSignature)> = members[..signer_count]
        .iter()
        .map(|m| (m.index, committee.sign_share(m, &message)))
        .collect();
    let qc = committee
        .aggregate(&shares, &message)
        .expect("aggregate above threshold");
    postcard::to_allocvec(&qc).expect("QC postcard encode")
}

/// A valid governance proof: a real threshold signature over `old ‖ new`,
/// carrying the CAS hint `expected_old_commitment = old`.
fn signed_proof(
    committee: &FederationCommittee,
    members: &[MemberSecret],
    signer_count: usize,
    old: [u8; 32],
    new: [u8; 32],
) -> GovernanceProof {
    GovernanceProof {
        expected_old_commitment: old,
        proof_data: sign_swap(committee, members, signer_count, &old, &new),
    }
}

#[test]
fn test_compile_route_table() {
    let _harness = quick_federation();

    let table = compile_routes(&[
        ("/cells/stablecoin/*", cell_target(cell_id(0x01))),
        ("/cells/oracle/*", cell_target(cell_id(0x02))),
        ("/intents/*", RouteTarget::handler("intent_pool")),
        ("/admin/*", RouteTarget::handler("admin")),
        ("/federated/*", federation_target(fed_id(0x42))),
    ]);
    assert!(table.num_states > 5);
    assert_eq!(table.accept_map.len(), 5);
    assert_ne!(table.commitment, [0u8; 32]);

    let table2 = compile_routes(&[
        ("/cells/stablecoin/*", cell_target(cell_id(0x01))),
        ("/cells/oracle/*", cell_target(cell_id(0x02))),
        ("/intents/*", RouteTarget::handler("intent_pool")),
        ("/admin/*", RouteTarget::handler("admin")),
        ("/federated/*", federation_target(fed_id(0x42))),
    ]);
    assert_eq!(table.commitment, table2.commitment);
}

#[test]
fn test_classify_messages_to_correct_handlers() {
    let _harness = quick_federation();

    let table = compile_routes(&[
        ("/cells/stablecoin/*", cell_target(cell_id(0x01))),
        ("/cells/oracle/*", cell_target(cell_id(0x02))),
        ("/intents/*", RouteTarget::handler("intent_pool")),
        ("/admin/*", RouteTarget::handler("admin")),
        ("/federated/*", federation_target(fed_id(0x42))),
    ]);
    let router = Router::new(table);

    assert_eq!(
        target_as_cell(
            router
                .classify_path(b"/cells/stablecoin/transfer")
                .unwrap()
                .target
        ),
        Some(cell_id(0x01))
    );
    assert_eq!(
        target_as_cell(
            router
                .classify_path(b"/cells/stablecoin/balance")
                .unwrap()
                .target
        ),
        Some(cell_id(0x01))
    );
    assert_eq!(
        target_as_cell(
            router
                .classify_path(b"/cells/oracle/price_feed")
                .unwrap()
                .target
        ),
        Some(cell_id(0x02))
    );

    let c = router.classify_path(b"/intents/submit_swap").unwrap();
    assert_eq!(c.target, &RouteTarget::handler("intent_pool"));

    let c = router.classify_path(b"/admin/status").unwrap();
    assert_eq!(c.target, &RouteTarget::handler("admin"));

    assert_eq!(
        target_as_federation(router.classify_path(b"/federated/sync").unwrap().target),
        Some(fed_id(0x42))
    );

    assert!(router.classify_path(b"/unknown/path").is_none());
    assert!(router.classify_path(b"/cells/unknown/x").is_none());
}

#[test]
fn test_governance_route_update() {
    let _harness = quick_federation();

    // Real 4-member committee, threshold 3 (BFT: tolerates 1 fault). Swaps are
    // gated by the production `FederationQcVerifier`, NOT the CAS-only stub.
    let (committee, members) = generate_test_committee(4, 3).unwrap();

    let initial_table = compile_routes(&[
        ("/cells/stablecoin/*", cell_target(cell_id(0x01))),
        ("/intents/*", RouteTarget::handler("intent_pool")),
    ]);
    let initial_commitment = initial_table.commitment;
    let mut governed = governed_router_with_committee(initial_table, committee.clone());

    assert_eq!(
        target_as_cell(
            governed
                .classify_path(b"/cells/stablecoin/transfer")
                .unwrap()
                .target
        ),
        Some(cell_id(0x01))
    );
    assert!(governed.classify_path(b"/cells/oracle/price").is_none());

    let new_table = compile_routes(&[
        ("/cells/stablecoin/*", cell_target(cell_id(0x01))),
        ("/cells/oracle/*", cell_target(cell_id(0x02))),
        ("/intents/*", RouteTarget::handler("intent_pool")),
    ]);
    let new_commitment = new_table.commitment;

    // REJECTION POLE: a QC genuinely signed by a DIFFERENT (rogue) committee
    // over the correct transition must NOT verify against the real committee,
    // even though its CAS hint is correct. Asserts the specific variant.
    let (rogue, rogue_members) = generate_test_committee_with_seed(4, 3, [9u8; 32]).unwrap();
    let forged = GovernanceProof {
        expected_old_commitment: initial_commitment,
        proof_data: sign_swap(
            &rogue,
            &rogue_members,
            3,
            &initial_commitment,
            &new_commitment,
        ),
    };
    assert!(
        matches!(
            governed.update_routes(new_table.clone(), &forged),
            Err(RouteUpdateError::ThresholdVerificationFailed(_))
        ),
        "a swap signed by a rogue committee must be rejected"
    );
    // State unchanged: the rejected swap did not add the oracle route.
    assert_ne!(governed.commitment(), &new_commitment);
    assert!(governed.classify_path(b"/cells/oracle/price").is_none());

    // SUCCESS POLE: a valid threshold signature over `old ‖ new` commits.
    let good = signed_proof(&committee, &members, 3, initial_commitment, new_commitment);
    governed.update_routes(new_table, &good).unwrap();

    assert_ne!(governed.commitment(), &initial_commitment);
    assert_eq!(
        target_as_cell(
            governed
                .classify_path(b"/cells/oracle/price")
                .unwrap()
                .target
        ),
        Some(cell_id(0x02))
    );
    assert_eq!(
        target_as_cell(
            governed
                .classify_path(b"/cells/stablecoin/transfer")
                .unwrap()
                .target
        ),
        Some(cell_id(0x01))
    );
}

#[test]
fn test_classification_changes_after_amendment() {
    let _harness = quick_federation();

    let (committee, members) = generate_test_committee(4, 3).unwrap();

    let table_v1 = compile_routes(&[("/cells/stablecoin/*", cell_target(cell_id(0x01)))]);
    let commitment_v1 = table_v1.commitment;
    let mut governed = governed_router_with_committee(table_v1, committee.clone());

    assert_eq!(
        target_as_cell(
            governed
                .classify_path(b"/cells/stablecoin/transfer")
                .unwrap()
                .target
        ),
        Some(cell_id(0x01))
    );

    let table_v2 = compile_routes(&[("/cells/stablecoin/*", cell_target(cell_id(0x02)))]);
    let commitment_v2 = table_v2.commitment;

    // REJECTION POLE: a CAS-only garbage blob (the kind the old `StubVerifier`
    // waved through) is now rejected — the amendment does NOT take effect
    // without a real threshold signature. Classification stays at v1.
    let cas_only = GovernanceProof {
        expected_old_commitment: commitment_v1,
        proof_data: vec![1, 2, 3],
    };
    assert!(
        matches!(
            governed.update_routes(table_v2.clone(), &cas_only),
            Err(RouteUpdateError::ThresholdVerificationFailed(_))
        ),
        "a CAS-only amendment with no threshold signature must be rejected"
    );
    assert_eq!(
        target_as_cell(
            governed
                .classify_path(b"/cells/stablecoin/transfer")
                .unwrap()
                .target
        ),
        Some(cell_id(0x01)),
        "rejected amendment must not change classification"
    );

    // SUCCESS POLE: the amendment gated behind a genuine QC now reclassifies.
    let good = signed_proof(&committee, &members, 3, commitment_v1, commitment_v2);
    governed.update_routes(table_v2, &good).unwrap();

    assert_eq!(
        target_as_cell(
            governed
                .classify_path(b"/cells/stablecoin/transfer")
                .unwrap()
                .target
        ),
        Some(cell_id(0x02))
    );
}

#[test]
fn test_route_revocation_classifies_as_drop() {
    let _harness = quick_federation();

    let (committee, members) = generate_test_committee(4, 3).unwrap();

    let table_v1 = compile_routes(&[
        ("/cells/stablecoin/*", cell_target(cell_id(0x01))),
        ("/cells/oracle/*", cell_target(cell_id(0x02))),
    ]);
    let commitment_v1 = table_v1.commitment;
    let mut governed = governed_router_with_committee(table_v1, committee.clone());

    assert_eq!(
        target_as_cell(
            governed
                .classify_path(b"/cells/oracle/price")
                .unwrap()
                .target
        ),
        Some(cell_id(0x02))
    );

    let table_v2 = compile_routes(&[
        ("/cells/stablecoin/*", cell_target(cell_id(0x01))),
        ("/cells/oracle/*", RouteTarget::Drop),
    ]);
    let commitment_v2 = table_v2.commitment;

    // REJECTION POLE: the RIGHT committee but the WRONG message — a valid
    // threshold signature over `old ‖ old` (not `old ‖ new`). The signature is
    // real yet authorizes no transition → rejected. The revocation must NOT
    // take effect; oracle still routes to its cell.
    let wrong_msg = GovernanceProof {
        expected_old_commitment: commitment_v1,
        proof_data: sign_swap(&committee, &members, 3, &commitment_v1, &commitment_v1),
    };
    assert!(
        matches!(
            governed.update_routes(table_v2.clone(), &wrong_msg),
            Err(RouteUpdateError::ThresholdVerificationFailed(_))
        ),
        "a threshold sig over the wrong (old‖old) message must be rejected"
    );
    assert_eq!(
        target_as_cell(
            governed
                .classify_path(b"/cells/oracle/price")
                .unwrap()
                .target
        ),
        Some(cell_id(0x02)),
        "rejected revocation must not drop the oracle route"
    );

    // SUCCESS POLE: a genuine QC over `old ‖ new` commits the revocation.
    let good = signed_proof(&committee, &members, 3, commitment_v1, commitment_v2);
    governed.update_routes(table_v2, &good).unwrap();

    let c = governed.classify_path(b"/cells/oracle/price").unwrap();
    assert_eq!(c.target, &RouteTarget::Drop);

    assert_eq!(
        target_as_cell(
            governed
                .classify_path(b"/cells/stablecoin/transfer")
                .unwrap()
                .target
        ),
        Some(cell_id(0x01))
    );

    let router = governed.router();
    assert_eq!(
        dispatch_path(router, b"/cells/oracle/anything"),
        DispatchDecision::Discard
    );
}

#[test]
fn test_cas_rejects_stale_commitment() {
    let _harness = quick_federation();

    let table_v1 = compile_routes(&[("/cells/alpha/*", cell_target(cell_id(0x01)))]);
    let mut governed = GovernedRouter::new(table_v1);

    let new_table = compile_routes(&[("/cells/alpha/*", cell_target(cell_id(0x02)))]);
    let bad_proof = GovernanceProof {
        expected_old_commitment: [0xFF; 32],
        proof_data: vec![0xAA],
    };

    let result = governed.update_routes(new_table, &bad_proof);
    assert!(matches!(
        result,
        Err(RouteUpdateError::CommitmentMismatch { .. })
    ));

    assert_eq!(
        target_as_cell(governed.classify_path(b"/cells/alpha/x").unwrap().target),
        Some(cell_id(0x01))
    );
}

#[test]
fn test_shared_prefix_disambiguation() {
    let _harness = quick_federation();

    let table = compile_routes(&[
        ("/cells/alpha/*", cell_target(cell_id(0x01))),
        ("/cells/alpha-beta/*", cell_target(cell_id(0x02))),
        ("/cells/alpha-gamma/*", cell_target(cell_id(0x03))),
    ]);
    let router = Router::new(table);

    assert_eq!(
        target_as_cell(router.classify_path(b"/cells/alpha/action").unwrap().target),
        Some(cell_id(0x01))
    );
    assert_eq!(
        target_as_cell(
            router
                .classify_path(b"/cells/alpha-beta/action")
                .unwrap()
                .target
        ),
        Some(cell_id(0x02))
    );
    assert_eq!(
        target_as_cell(
            router
                .classify_path(b"/cells/alpha-gamma/action")
                .unwrap()
                .target
        ),
        Some(cell_id(0x03))
    );
}

#[test]
fn test_raw_wire_message_classification() {
    let _harness = quick_federation();

    let table = compile_routes(&[("/cells/stablecoin/*", cell_target(cell_id(0x10)))]);
    let router = Router::new(table);

    let msg = b"/cells/stablecoin/transfer\x00\x01\x02\x03\x04payload_bytes";
    let c = router.classify(msg).unwrap();
    assert_eq!(target_as_cell(c.target), Some(cell_id(0x10)));
}
