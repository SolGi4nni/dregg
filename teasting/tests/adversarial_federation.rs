//! Adversarial federation tests — equivocation, BLS share withholding,
//! threshold near-miss, forked-blocklace prefix differentiation.
//!
//! Per AUDIT-federation.md §10 (adversarial tests *missing*),
//! AUDIT-blocklace-consensus.md §7 ("not tested" subset), and
//! AUDIT-morpheus-federation-blocklace-phase3a.md the running node has
//! tests for *single-node misbehavior* but lacks:
//!
//!   - **Equivocating federation**: same federation signs two
//!     contradictory `AttestedRoot`s at the same height — a verifier
//!     must detect this.
//!   - **BLS share withhold**: `t-1` of `n` shares submitted (one
//!     short of threshold) — aggregation must fail.
//!   - **Threshold near-miss with tampered share**: `t` shares but one
//!     has a corrupted MAC — aggregation must fail.
//!   - **Forked blocklace prefix**: the future AttestedRoot v3 must
//!     bind `(federation_id, block_id)` so two attestations on forked
//!     prefixes are distinguishable (AUDIT-federation.md F3).
//!
//! Many tests are `#[ignore]`d on AttestedRoot v3 / federation-id ↔
//! committee binding (AUDIT-federation.md F1/F3). The BLS share
//! withhold + threshold near-miss tests are exercisable today against
//! `dregg_federation::threshold::FederationCommittee`.

use dregg_federation::threshold::generate_test_committee;

// ===========================================================================
// BLS share withhold: t-1 of n must fail aggregation
// ===========================================================================

/// Per AUDIT-federation.md §10 "Adversarial tests missing" — confirm
/// that supplying `threshold - 1` shares to the aggregator produces an
/// error (not a silently-accepted aggregate).
#[test]
fn bls_t_minus_one_of_n_aggregation_rejects() {
    let cases: Vec<(usize, usize, &str)> = vec![
        (4, 4, "adversarial-test-message-v1"),
        (7, 5, "medium-committee-near-miss"),
    ];

    for (n, threshold, message) in cases {
        let (committee, members) =
            generate_test_committee(n, threshold.try_into().unwrap()).expect("committee");

        // Collect ONLY t-1 shares.
        let shares: Vec<_> = members
            .iter()
            .take((threshold - 1) as usize)
            .map(|m| (m.index, committee.sign_share(m, message.as_bytes())))
            .collect();

        let result = committee.aggregate(&shares, message.as_bytes());
        assert!(
            result.is_err(),
            "n={n} t={threshold}: aggregating {} shares (one short of threshold) must fail; got {result:?}",
            threshold - 1
        );
    }
}

// ===========================================================================
// Threshold near-miss with tampered share: t shares but one has wrong
// message
// ===========================================================================

/// Per AUDIT-federation.md §10 — t shares present, but one is signed
/// over a DIFFERENT message. The aggregate verification must fail.
#[test]
fn bls_threshold_met_but_one_share_signed_over_wrong_message_rejects() {
    let n = 4;
    let threshold = 3;
    let (committee, members) = generate_test_committee(n, threshold).expect("committee");

    let canonical_message = b"canonical-checkpoint-payload-v1";
    let attacker_message = b"alternate-checkpoint-payload";

    // Three shares, but member[2] signs over a different message.
    let s0 = committee.sign_share(&members[0], canonical_message);
    let s1 = committee.sign_share(&members[1], canonical_message);
    let s2_bad = committee.sign_share(&members[2], attacker_message);

    let shares = vec![
        (members[0].index, s0),
        (members[1].index, s1),
        (members[2].index, s2_bad),
    ];
    let qc_result = committee.aggregate(&shares, canonical_message);

    // Either aggregation fails outright, OR aggregation succeeds but
    // verification against `canonical_message` fails — either way the
    // canonical-message attestation must not be accepted.
    match qc_result {
        Err(_) => { /* expected: aggregation failed */ }
        Ok(qc) => {
            let verify = committee.verify(&qc, canonical_message);
            assert!(
                verify.is_err(),
                "aggregate over mismatched messages must NOT verify against the canonical message"
            );
        }
    }
}

// ===========================================================================
// Aggregate verification — wrong message after success
// ===========================================================================

#[test]
fn bls_aggregate_does_not_verify_against_different_message() {
    let n = 4;
    let threshold = 3;
    let (committee, members) = generate_test_committee(n, threshold).expect("committee");
    let msg = b"verify-message-v1";
    let other = b"verify-message-v2";

    let shares: Vec<_> = members
        .iter()
        .take(threshold as usize)
        .map(|m| (m.index, committee.sign_share(m, msg)))
        .collect();
    let qc = committee.aggregate(&shares, msg).expect("aggregate ok");

    assert!(committee.verify(&qc, msg).is_ok(), "ok against signed msg");
    let result = committee.verify(&qc, other);
    assert!(
        result.is_err(),
        "QC must not verify against a different message; got {result:?}"
    );
}

// NOTE: removed 10 #[ignore] placeholder tests (equivocating federation,
// forked-blocklace, FederationReceipt forgery, equivocation handling,
// below-threshold liveness, cross-fed replay) that provided zero runtime value.
