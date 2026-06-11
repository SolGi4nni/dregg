//! # Differential: Lean `EpochReconfig` model  ⟺  the REAL `federation::epoch`.
//!
//! This is the Rust side of the differential for
//! `metatheory/Dregg2/Distributed/EpochReconfig.lean` — the faithful executable Lean model of the
//! federation's validator-set reconfiguration / epoch handoff (`federation/src/epoch.rs`). The Lean
//! side proves the NO-SAFETY-GAP property: a verified epoch transition advances the epoch by exactly
//! one, is attested by an OLD-epoch BFT quorum of DISTINCT old members, and births the successor
//! with the correct supermajority threshold for its own (well-formed) member set.
//!
//! The Lean `quorumThreshold` / `applyDelta` / `verifyTransition` are tiny, total transcriptions of
//! `quorum_threshold` / the `apply_epoch_transition` set transform / the `verify_epoch_transition`
//! gate. This differential pins that the verified Lean semantics IS the semantics the federation
//! actually computes — same discipline as `threshold_decrypt_diff` and `BlocklaceFinality`'s golden
//! vectors:
//!
//!  1. **Threshold agreement** — the Lean `quorumThreshold` (= `n − n/3`) is re-run here against the
//!     REAL `quorum_threshold`/`compute_bft_threshold` over the Lean `#guard` golden values AND an
//!     exhaustive `0..=256` sweep (the Lean side samples; here we close the range).
//!  2. **Set-transform agreement** — the Lean `applyDelta` (filter removals, append additions) and
//!     `applyDelta_count` are re-run against the REAL `apply_epoch_transition` member set and count.
//!  3. **No-gap gate agreement** — the Lean `verifyTransition`'s teeth (sequential epochs, old-epoch
//!     quorum of valid distinct-member signatures, supermajority new-threshold) are re-run against
//!     the REAL `verify_epoch_transition` admit/reject behaviour, including the four NEGATIVE
//!     witnesses the Lean `Demo` section proves UNSAT: under-quorum, outsider signer, wrong
//!     threshold, non-sequential epoch.
//!
//! The Ed25519 per-vote signature check is the Lean `SigValid` PORTAL (the EUF-CMA assumption); here
//! it is driven through the REAL `PublicKey::verify` over genuine keypairs, so the "valid distinct
//! old-member signers" notion is exercised concretely, not abstractly.

#![cfg(test)]

use crate::epoch::{
    EpochConfig, ValidatorInfo, apply_epoch_transition, compute_bft_threshold,
    propose_epoch_transition, verify_epoch_transition,
};
use crate::quorum_threshold;
use crate::types::{PublicKey, QuorumCertificate, Signature, SigningKey, generate_keypair, sign};

// ───────────────────────────── Lean model, transcribed to Rust ─────────────────────────────
// These mirror `EpochReconfig.lean` §1–§2 exactly.

/// Lean `quorumThreshold n = n - n/3` (`EpochReconfig.lean` §1). Total `Nat` transcription.
fn lean_quorum_threshold(n: usize) -> usize {
    n - n / 3
}

/// Lean `applyDelta old d` (`EpochReconfig.lean` §2): drop removals (by key), append additions —
/// returns the new member key list.
fn lean_apply_delta(
    old: &[PublicKey],
    added: &[PublicKey],
    removed: &[PublicKey],
) -> Vec<PublicKey> {
    let mut out: Vec<PublicKey> = old
        .iter()
        .filter(|m| !removed.iter().any(|r| r == *m))
        .cloned()
        .collect();
    out.extend(added.iter().cloned());
    out
}

// ───────────────────────────── helpers ─────────────────────────────

fn make_validator(epoch: u64) -> (ValidatorInfo, SigningKey) {
    let (sk, pk) = generate_keypair();
    let mut root = [0u8; 32];
    getrandom::fill(&mut root).unwrap();
    let info = ValidatorInfo {
        public_key: pk,
        signing_key_root: root,
        stake: 1,
        joined_epoch: epoch,
    };
    (info, sk)
}

/// Fill a transition's attestation with `n` genuinely-signed old-member votes (voter ids `0..n`).
fn sign_quorum(transition_qc: &mut QuorumCertificate, sks: &[&SigningKey], n: usize) {
    let vote_message = QuorumCertificate::vote_message(
        &transition_qc.block_hash,
        transition_qc.height,
        transition_qc.view,
    );
    transition_qc.votes = (0..n).map(|i| (i, sign(sks[i], &vote_message))).collect();
}

// ───────────────────────────── §1 threshold agreement ─────────────────────────────

#[test]
fn lean_threshold_matches_rust_golden() {
    // The Lean `#guard` golden values (`EpochReconfig.lean` §1).
    for (n, t) in [
        (1usize, 1usize),
        (2, 2),
        (3, 2),
        (4, 3),
        (5, 4),
        (6, 4),
        (7, 5),
        (10, 7),
        (13, 9),
    ] {
        assert_eq!(lean_quorum_threshold(n), t, "lean golden n={n}");
        assert_eq!(quorum_threshold(n), t, "rust quorum_threshold n={n}");
        assert_eq!(
            compute_bft_threshold(n),
            t,
            "rust compute_bft_threshold n={n}"
        );
    }
}

#[test]
fn lean_threshold_matches_rust_exhaustive() {
    // Close the whole 0..=256 range: Lean transcription ≡ real quorum_threshold ≡ compute_bft.
    for n in 0..=256usize {
        assert_eq!(
            lean_quorum_threshold(n),
            quorum_threshold(n),
            "lean vs quorum_threshold n={n}"
        );
        assert_eq!(
            quorum_threshold(n),
            compute_bft_threshold(n),
            "quorum_threshold vs compute_bft n={n}"
        );
        // Lean `quorum_gt_half`: for n ≥ 1, n < 2*quorum (strict-majority / intersection backbone).
        if n >= 1 {
            assert!(n < 2 * quorum_threshold(n), "quorum_gt_half n={n}");
        }
        // Lean `quorum_le`: quorum ≤ n.
        assert!(quorum_threshold(n) <= n, "quorum_le n={n}");
    }
}

// ───────────────────────────── §2 set-transform + count agreement ─────────────────────────────

#[test]
fn lean_apply_delta_matches_rust_member_set_and_count() {
    // Build a 4-member epoch-0 config; propose add v4 / remove v3 → new count 4, threshold 3.
    let (v0, sk0) = make_validator(0);
    let (v1, sk1) = make_validator(0);
    let (v2, sk2) = make_validator(0);
    let (v3, _sk3) = make_validator(0);
    let (v4, _sk4) = make_validator(1);

    let mut config =
        EpochConfig::genesis(vec![v0.clone(), v1.clone(), v2.clone(), v3.clone()], 100);
    assert_eq!(config.threshold, 3);

    let old_keys: Vec<PublicKey> = config
        .members
        .iter()
        .map(|m| m.public_key.clone())
        .collect();

    // Real propose.
    let mut transition =
        propose_epoch_transition(&config, &[v4.clone()], &[v3.public_key.clone()]).unwrap();
    assert_eq!(transition.new_threshold, 3);

    // Lean applyDelta on the SAME delta.
    let lean_new = lean_apply_delta(
        &old_keys,
        &[v4.public_key.clone()],
        &[v3.public_key.clone()],
    );

    // Lean `applyDelta_count`: |old| - |removed| + |added|.
    assert_eq!(lean_new.len(), old_keys.len() - 1 + 1);
    assert_eq!(lean_new.len(), 4);

    // Lean new-threshold = quorumThreshold of new count.
    assert_eq!(
        transition.new_threshold,
        lean_quorum_threshold(lean_new.len())
    );

    // Drive the REAL apply with a genuine old-epoch quorum (3 valid old-member sigs).
    sign_quorum(&mut transition.attestation, &[&sk0, &sk1, &sk2], 3);
    transition.attestation.threshold = config.threshold;
    apply_epoch_transition(&mut config, &transition).unwrap();

    // Real applied member-key set ≡ Lean applyDelta (as a set: removals gone, additions present).
    let rust_new: Vec<PublicKey> = config
        .members
        .iter()
        .map(|m| m.public_key.clone())
        .collect();
    for k in &lean_new {
        assert!(rust_new.contains(k), "lean member missing from rust");
    }
    for k in &rust_new {
        assert!(lean_new.contains(k), "rust member missing from lean");
    }
    assert_eq!(rust_new.len(), lean_new.len());
    // Real applied threshold ≡ supermajority of new count (Lean applied_threshold_is_supermajority).
    assert_eq!(
        config.threshold,
        lean_quorum_threshold(config.members.len())
    );
    assert_eq!(config.current_epoch, 1); // apply_advances_one
}

// ───────────────────────────── §3 no-gap gate agreement ─────────────────────────────

/// Build a verifiable 3→4-member transition with a genuine old-epoch quorum, ready to mutate for
/// the negative cases. Returns (old_config, transition, [sk0,sk1,sk2]).
fn build_verifiable() -> (
    EpochConfig,
    crate::epoch::EpochTransition,
    (SigningKey, SigningKey, SigningKey),
) {
    let (v0, sk0) = make_validator(0);
    let (v1, sk1) = make_validator(0);
    let (v2, sk2) = make_validator(0);
    let (v3, _sk3) = make_validator(1);

    let config = EpochConfig::genesis(vec![v0, v1, v2], 100);
    let mut transition = propose_epoch_transition(&config, &[v3], &[]).unwrap();
    sign_quorum(
        &mut transition.attestation,
        &[&sk0, &sk1, &sk2],
        config.threshold,
    );
    transition.attestation.threshold = config.threshold;
    (config, transition, (sk0, sk1, sk2))
}

#[test]
fn positive_witness_verifies() {
    // Lean `Demo` POSITIVE witness: a properly-attested, sequential, supermajority transition verifies.
    let (config, transition, _) = build_verifiable();
    assert!(verify_epoch_transition(&transition, &config));
    // No-gap: to = from + 1.
    assert_eq!(transition.to_epoch, transition.from_epoch + 1);
    assert_eq!(transition.from_epoch, config.current_epoch);
    // Quorum: ≥ quorumThreshold |old| valid old-member sigs.
    assert!(transition.attestation.votes.len() >= lean_quorum_threshold(config.members.len()));
}

#[test]
fn negative_under_quorum_rejected() {
    // Lean `Demo` NEGATIVE #1: too few valid signers ⇒ verify fails (no-minority-seizure).
    let (config, mut transition, (sk0, sk1, _)) = build_verifiable();
    // Only TWO sigs (threshold is quorumThreshold(3) = 2... so drop to ONE to go under).
    sign_quorum(&mut transition.attestation, &[&sk0, &sk1], 1);
    assert!(transition.attestation.votes.len() < config.threshold);
    assert!(!verify_epoch_transition(&transition, &config));
}

#[test]
fn negative_outsider_signer_rejected() {
    // Lean `Demo` NEGATIVE #2: an OUTSIDER's vote (a non-old-member key id) ⇒ verify fails.
    let (config, mut transition, (sk0, sk1, _)) = build_verifiable();
    // Replace the third vote with voter_id 99 (out of range of the 3-member old set).
    let vote_message = QuorumCertificate::vote_message(
        &transition.attestation.block_hash,
        transition.attestation.height,
        transition.attestation.view,
    );
    transition.attestation.votes = vec![
        (0, sign(&sk0, &vote_message)),
        (1, sign(&sk1, &vote_message)),
        (99, Signature([7u8; 64])), // outsider id, garbage sig
    ];
    assert!(!verify_epoch_transition(&transition, &config));
}

#[test]
fn negative_forged_signature_rejected() {
    // Sharper than the Lean toy portal: a vote claiming a REAL old member but with a FORGED
    // signature (zeros) ⇒ the REAL Ed25519 `verify` rejects (the EUF-CMA assumption the Lean
    // `SigValid` portal abstracts, discharged here concretely).
    let (config, mut transition, (sk0, sk1, _)) = build_verifiable();
    let vote_message = QuorumCertificate::vote_message(
        &transition.attestation.block_hash,
        transition.attestation.height,
        transition.attestation.view,
    );
    transition.attestation.votes = vec![
        (0, sign(&sk0, &vote_message)),
        (1, sign(&sk1, &vote_message)),
        (2, Signature([0u8; 64])), // member 2, but a bogus signature
    ];
    assert!(!verify_epoch_transition(&transition, &config));
}

#[test]
fn negative_wrong_threshold_rejected() {
    // Lean `Demo` NEGATIVE #3: declaring a new_threshold ≠ supermajority of new count ⇒ verify fails.
    let (config, mut transition, _) = build_verifiable();
    transition.new_threshold += 1; // anything but the correct quorum
    assert_ne!(
        transition.new_threshold,
        lean_quorum_threshold(config.members.len() + 1)
    );
    assert!(!verify_epoch_transition(&transition, &config));
}

#[test]
fn negative_non_sequential_rejected() {
    // Lean `Demo` NEGATIVE #4: non-sequential epoch (replay/skip) ⇒ verify fails.
    let (config, mut transition, _) = build_verifiable();
    transition.from_epoch = 5; // != config.current_epoch (0)
    assert!(!verify_epoch_transition(&transition, &config));
}
