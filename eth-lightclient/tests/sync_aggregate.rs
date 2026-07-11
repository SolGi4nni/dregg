//! Full `verify_sync_aggregate` flow — SELF-SIGNED round-trip fixture.
//!
//! HONEST NAMING: this test constructs a 512-key committee, signs the *real*
//! signing root with the same `blst` library, aggregates, and verifies. It
//! therefore proves the END-TO-END WIRING — SSZ header hash_tree_root, the
//! sync-committee domain, compute_signing_root, aggregation, the 2/3 threshold,
//! and fail-closed behaviour on tamper / wrong-domain — is internally correct and
//! consistent. It does NOT independently prove ciphersuite spec-conformance;
//! that is proven separately by the external ethereum/bls12-381-tests KATs in
//! `kat_bls.rs`. Together: KATs pin the ciphersuite; this pins the wiring.

use blst::min_pk::{AggregateSignature, SecretKey, Signature};
use eth_lightclient::{
    compute_signing_root, verify_sync_aggregate, BeaconBlockHeader, Error, SyncAggregate, DST,
    SYNC_COMMITTEE_SIZE,
};

const FORK_VERSION: [u8; 4] = [0x03, 0x00, 0x00, 0x00]; // e.g. a Capella-ish fork version
const GVR: [u8; 32] = [0x42u8; 32]; // an arbitrary but fixed genesis_validators_root

fn committee_keys() -> Vec<SecretKey> {
    (0..SYNC_COMMITTEE_SIZE as u32)
        .map(|i| {
            let mut ikm = [0u8; 32];
            ikm[..4].copy_from_slice(&i.to_be_bytes());
            ikm[4] = 0xA5; // domain-separate the IKM a bit
            SecretKey::key_gen(&ikm, &[]).unwrap()
        })
        .collect()
}

fn header() -> BeaconBlockHeader {
    BeaconBlockHeader {
        slot: 7_654_321,
        proposer_index: 12345,
        parent_root: [0x11u8; 32],
        state_root: [0x22u8; 32],
        body_root: [0x33u8; 32],
    }
}

fn pubkeys(keys: &[SecretKey]) -> Vec<[u8; 48]> {
    keys.iter().map(|k| k.sk_to_pk().compress()).collect()
}

/// Build a SyncAggregate signing `signing_root` with the members in `participants`.
fn make_aggregate(
    keys: &[SecretKey],
    participants: &[usize],
    signing_root: &[u8; 32],
) -> SyncAggregate {
    let sigs: Vec<Signature> = participants
        .iter()
        .map(|&i| keys[i].sign(signing_root, DST, &[]))
        .collect();
    let refs: Vec<&Signature> = sigs.iter().collect();
    let agg = AggregateSignature::aggregate(&refs, true).unwrap();
    let sig_bytes = agg.to_signature().compress();

    let mut bits = [0u8; SYNC_COMMITTEE_SIZE / 8];
    for &i in participants {
        bits[i / 8] |= 1 << (i % 8);
    }
    SyncAggregate {
        sync_committee_bits: bits,
        sync_committee_signature: sig_bytes,
    }
}

#[test]
fn full_participation_accepts() {
    let keys = committee_keys();
    let hdr = header();
    let sr = compute_signing_root(&hdr, FORK_VERSION, GVR);
    let all: Vec<usize> = (0..SYNC_COMMITTEE_SIZE).collect();
    let agg = make_aggregate(&keys, &all, &sr);
    assert!(verify_sync_aggregate(&hdr, &agg, &pubkeys(&keys), FORK_VERSION, GVR).is_ok());
}

#[test]
fn exactly_two_thirds_accepts() {
    // required = ceil(2*512/3) = 342.
    let keys = committee_keys();
    let hdr = header();
    let sr = compute_signing_root(&hdr, FORK_VERSION, GVR);
    let parts: Vec<usize> = (0..342).collect();
    let agg = make_aggregate(&keys, &parts, &sr);
    assert!(verify_sync_aggregate(&hdr, &agg, &pubkeys(&keys), FORK_VERSION, GVR).is_ok());
}

#[test]
fn one_below_threshold_rejects() {
    // 341 participants: 341*3 = 1023 < 1024. Must reject even though every
    // signature is individually valid -> the threshold is load-bearing.
    let keys = committee_keys();
    let hdr = header();
    let sr = compute_signing_root(&hdr, FORK_VERSION, GVR);
    let parts: Vec<usize> = (0..341).collect();
    let agg = make_aggregate(&keys, &parts, &sr);
    let r = verify_sync_aggregate(&hdr, &agg, &pubkeys(&keys), FORK_VERSION, GVR);
    assert_eq!(
        r,
        Err(Error::InsufficientParticipation {
            participants: 341,
            required: 342
        })
    );
}

#[test]
fn half_participation_rejects() {
    // The adversarial "50% update" — a 256-of-512 majority-but-not-supermajority
    // signature with genuinely valid member sigs must NOT slip through.
    let keys = committee_keys();
    let hdr = header();
    let sr = compute_signing_root(&hdr, FORK_VERSION, GVR);
    let parts: Vec<usize> = (0..256).collect();
    let agg = make_aggregate(&keys, &parts, &sr);
    assert!(matches!(
        verify_sync_aggregate(&hdr, &agg, &pubkeys(&keys), FORK_VERSION, GVR),
        Err(Error::InsufficientParticipation { .. })
    ));
}

#[test]
fn tampered_signature_rejects() {
    let keys = committee_keys();
    let hdr = header();
    let sr = compute_signing_root(&hdr, FORK_VERSION, GVR);
    let all: Vec<usize> = (0..SYNC_COMMITTEE_SIZE).collect();
    let mut agg = make_aggregate(&keys, &all, &sr);
    agg.sync_committee_signature[95] ^= 0xff; // flip a byte
    assert!(verify_sync_aggregate(&hdr, &agg, &pubkeys(&keys), FORK_VERSION, GVR).is_err());
}

#[test]
fn wrong_fork_version_rejects() {
    // Adversarial domain test: the aggregate was signed under FORK_VERSION, but
    // the verifier is told a DIFFERENT fork -> different signing root -> reject.
    // (A wrong fork_version silently accepting forgeries is exactly the hole.)
    let keys = committee_keys();
    let hdr = header();
    let sr = compute_signing_root(&hdr, FORK_VERSION, GVR);
    let all: Vec<usize> = (0..SYNC_COMMITTEE_SIZE).collect();
    let agg = make_aggregate(&keys, &all, &sr);
    let wrong_fork = [0x04, 0x00, 0x00, 0x00];
    assert_eq!(
        verify_sync_aggregate(&hdr, &agg, &pubkeys(&keys), wrong_fork, GVR),
        Err(Error::BadSignature)
    );
}

#[test]
fn wrong_genesis_validators_root_rejects() {
    let keys = committee_keys();
    let hdr = header();
    let sr = compute_signing_root(&hdr, FORK_VERSION, GVR);
    let all: Vec<usize> = (0..SYNC_COMMITTEE_SIZE).collect();
    let agg = make_aggregate(&keys, &all, &sr);
    let wrong_gvr = [0x99u8; 32];
    assert_eq!(
        verify_sync_aggregate(&hdr, &agg, &pubkeys(&keys), FORK_VERSION, wrong_gvr),
        Err(Error::BadSignature)
    );
}

#[test]
fn tampered_header_rejects() {
    let keys = committee_keys();
    let hdr = header();
    let sr = compute_signing_root(&hdr, FORK_VERSION, GVR);
    let all: Vec<usize> = (0..SYNC_COMMITTEE_SIZE).collect();
    let agg = make_aggregate(&keys, &all, &sr);
    let mut hdr2 = header();
    hdr2.state_root = [0xEEu8; 32]; // the header the committee did NOT sign
    assert_eq!(
        verify_sync_aggregate(&hdr2, &agg, &pubkeys(&keys), FORK_VERSION, GVR),
        Err(Error::BadSignature)
    );
}

#[test]
fn wrong_participants_rejects() {
    // The signature aggregates members [0..342) but the BITFIELD claims a
    // different set [10..352). The aggregate pubkey won't match -> reject.
    let keys = committee_keys();
    let hdr = header();
    let sr = compute_signing_root(&hdr, FORK_VERSION, GVR);
    let signers: Vec<usize> = (0..342).collect();
    let mut agg = make_aggregate(&keys, &signers, &sr);
    // Rewrite the bitfield to claim members [10..352).
    let mut bits = [0u8; SYNC_COMMITTEE_SIZE / 8];
    for i in 10..352 {
        bits[i / 8] |= 1 << (i % 8);
    }
    agg.sync_committee_bits = bits;
    assert_eq!(
        verify_sync_aggregate(&hdr, &agg, &pubkeys(&keys), FORK_VERSION, GVR),
        Err(Error::BadSignature)
    );
}
