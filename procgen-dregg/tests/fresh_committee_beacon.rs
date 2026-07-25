//! FRESH-GENESIS BEACON PQ HALF — driven against a real re-genesis committee.
//!
//! The beacon's post-quantum day-seed half (`procgen_dregg::beacon`) authenticates
//! a finalized ledger root against a genesis-PINNED [`FederationCommittee`]: an
//! ed25519 signer set and an index-aligned ENROLLED ML-DSA-65 roster, plus the
//! `2f+1` quorum threshold. A committee with an EMPTY ML-DSA roster is refused at
//! construction (`RootError::MisalignedCommittee`) — so the STALE devnet genesis
//! (no `ml_dsa_public_key` on any validator) can NOT furnish a committee, and the
//! beacon PQ half is BLOCKED.
//!
//! This test proves the FRESH re-genesis unblocks it. Pointed at an out-of-tree
//! genesis directory (`FRESH_GENESIS_DIR`) produced by
//! `dregg-node genesis --validators N` (each validator enrolls BOTH an ed25519 and
//! an ML-DSA-65 key), it:
//!
//!   1. parses the PUBLIC `genesis.json` roster (ed25519 + ML-DSA-65 pubkeys +
//!      the hybrid id + the threshold);
//!   2. re-derives each signer's `(ed25519, ML-DSA-65)` keypair from its raw
//!      `node-i.key` seed and asserts the derived public halves MATCH the manifest
//!      — the committed manifest and the private keys are the same committee, and
//!      the published `hybrid_id` is exactly `H(ed25519 ‖ ml_dsa)` (the enrollment
//!      pin);
//!   3. pins a real [`FederationCommittee`] from the manifest roster (this is the
//!      construction the stale genesis can NOT satisfy);
//!   4. assembles a real HYBRID `FinalizedRootAttestation` — `2f+1` distinct
//!      members each signing the canonical finalization preimage over a finalized
//!      `merkle_root` with BOTH halves — and asserts it VERIFIES against the fresh
//!      committee, so the beacon's hybrid day seed can now quorum on a real root;
//!   5. asserts the teeth still bite on the fresh committee: below-threshold is
//!      refused, a forged ML-DSA half is refused (no ed25519-only downgrade).
//!
//! Skips (green) when `FRESH_GENESIS_DIR` is unset, so the offline suite is
//! unaffected; the re-genesis harness sets it to drive the real proof.

use std::path::PathBuf;

use dregg_federation::frost::{MlDsaPublicKey, MlDsaSigningKey};
use dregg_types::{HybridQuorumSig, PublicKey, Signature};
use ed25519_dalek::{Signer, SigningKey};
use procgen_dregg::beacon::{FederationCommittee, FinalizedRootAttestation, RootError};

/// One committee member re-derived from its raw genesis `node-i.key` seed.
struct Member {
    ed_sk: SigningKey,
    pq_sk: MlDsaSigningKey,
    ed_pk: PublicKey,
    pq_pk: MlDsaPublicKey,
}

fn hex_decode(s: &str) -> Vec<u8> {
    hex::decode(s).expect("manifest field is valid hex")
}

/// Re-derive a member from a raw 32-byte node key seed — EXACTLY the production
/// derivation (`node/src/genesis.rs`: ed25519 from the seed, ML-DSA-65 from the
/// same seed via `MlDsaSigningKey::from_seed`).
fn member_from_seed(seed: &[u8; 32]) -> Member {
    let ed_sk = SigningKey::from_bytes(seed);
    let (pq_pk, pq_sk) = MlDsaSigningKey::from_seed(seed);
    Member {
        ed_pk: PublicKey(ed_sk.verifying_key().to_bytes()),
        pq_pk,
        ed_sk,
        pq_sk,
    }
}

fn hybrid_sig(m: &Member, msg: &[u8]) -> HybridQuorumSig {
    HybridQuorumSig {
        pubkey: m.ed_pk,
        signature: Signature(m.ed_sk.sign(msg).to_bytes()),
        ml_dsa_pubkey: m.pq_pk.0.to_vec(),
        pq_signature: m.pq_sk.sign(msg).expect("ML-DSA hedged signing"),
    }
}

#[test]
fn fresh_genesis_committee_authenticates_a_beacon_finalized_root() {
    let Ok(dir) = std::env::var("FRESH_GENESIS_DIR") else {
        // ARMABLE skip, mirroring `dregg_lean_ffi::demand_lean`'s grammar. A loud `eprintln!` is
        // not enough on its own: CI reads the exit code, not stderr, so a lane that BELIEVES it is
        // driving a re-genesis beacon (and forgot to export the dir) gets a green run in which
        // nothing below executed. Under `DREGG_TEST_REQUIRE_FRESH_GENESIS=1` that is a hard fail.
        let armed = matches!(
            std::env::var("DREGG_TEST_REQUIRE_FRESH_GENESIS")
                .ok()
                .as_deref(),
            Some("1") | Some("true") | Some("TRUE") | Some("on") | Some("ON")
        );
        assert!(
            !armed,
            "DREGG_TEST_REQUIRE_FRESH_GENESIS=1 but FRESH_GENESIS_DIR is unset — this test would \
             have SILENTLY SKIPPED the committee/beacon authentication assertions and reported \
             `ok`. Point FRESH_GENESIS_DIR at a re-genesis output dir; do not weaken the hard mode."
        );
        eprintln!("SKIP: FRESH_GENESIS_DIR unset (set it to a re-genesis output dir to drive)");
        return;
    };
    let dir = PathBuf::from(dir);
    let genesis: serde_json::Value = serde_json::from_slice(
        &std::fs::read(dir.join("genesis.json")).expect("read genesis.json"),
    )
    .expect("parse genesis.json");

    let validators = genesis["validators"].as_array().expect("validators array");
    let n = validators.len();
    let threshold = genesis["threshold"].as_u64().expect("threshold") as usize;
    assert!(n >= 4, "re-genesis must be n>=4 (fault slack); got n={n}");
    assert!(
        threshold >= 3 && threshold <= n,
        "threshold {threshold} must be a sane 2f+1 for n={n}"
    );

    // ── Parse the PUBLIC roster + re-derive each signer from its private seed. ──
    let mut ed_roster: Vec<PublicKey> = Vec::with_capacity(n);
    let mut pq_roster: Vec<MlDsaPublicKey> = Vec::with_capacity(n);
    let mut members: Vec<Member> = Vec::with_capacity(n);

    for (i, v) in validators.iter().enumerate() {
        // Every validator MUST carry the PQ half — this is the field the stale
        // genesis lacks entirely.
        let ml_dsa_hex = v["ml_dsa_public_key"]
            .as_str()
            .unwrap_or_else(|| panic!("validator {i} has NO ml_dsa_public_key — stale genesis"));
        let hybrid_id_hex = v["hybrid_id"]
            .as_str()
            .unwrap_or_else(|| panic!("validator {i} has NO hybrid_id — stale genesis"));
        let ed_hex = v["public_key"].as_str().expect("public_key");

        let published_ed = hex_decode(ed_hex);
        let published_ml = hex_decode(ml_dsa_hex);
        assert_eq!(published_ml.len(), 1952, "ML-DSA-65 pubkey is 1952 bytes");

        // Re-derive from the raw node-i.key seed and PIN it to the manifest.
        let seed_bytes = std::fs::read(dir.join(format!("node-{i}.key")))
            .unwrap_or_else(|_| panic!("read node-{i}.key"));
        let seed: [u8; 32] = seed_bytes
            .as_slice()
            .try_into()
            .expect("node key is 32 bytes");
        let m = member_from_seed(&seed);

        assert_eq!(
            m.ed_pk.0.to_vec(),
            published_ed,
            "validator {i}: derived ed25519 pubkey must match the manifest"
        );
        assert_eq!(
            m.pq_pk.0.to_vec(),
            published_ml,
            "validator {i}: derived ML-DSA-65 pubkey must match the manifest roster"
        );
        // The published hybrid id is the enrollment pin: H(ed25519 ‖ ml_dsa).
        assert_eq!(
            hex::encode(dregg_types::hybrid_id_commitment(&m.ed_pk.0, &m.pq_pk.0)),
            hybrid_id_hex,
            "validator {i}: hybrid_id must be the enrolled commitment of BOTH keys"
        );

        ed_roster.push(m.ed_pk);
        pq_roster.push(m.pq_pk.clone());
        members.push(m);
    }

    // ── (3) Pin the committee the STALE genesis could never build. ──
    let committee = FederationCommittee::new(ed_roster.clone(), pq_roster.clone(), threshold)
        .expect("the fresh roster pins a well-formed hybrid committee");
    assert_eq!(committee.size(), n);
    assert_eq!(committee.quorum_threshold(), threshold);

    // A committee with the ML-DSA roster STRIPPED (the stale-genesis shape) is
    // refused at construction — the concrete blocker this re-genesis removes.
    assert!(matches!(
        FederationCommittee::new(ed_roster.clone(), Vec::new(), threshold),
        Err(RootError::MisalignedCommittee { .. })
    ));

    // ── (4) A real hybrid finalized-root attestation from 2f+1 fresh members. ──
    let block_id = [0xB1u8; 32];
    let merkle_root = [0x5Au8; 32];
    let msg = dregg_types::finalization_vote_signing_message(&block_id, &merkle_root);

    let quorum: Vec<HybridQuorumSig> = members[..threshold]
        .iter()
        .map(|m| hybrid_sig(m, &msg))
        .collect();
    let root = FinalizedRootAttestation {
        block_id,
        merkle_root,
        fixed_at_unix: 0,
        quorum,
    };
    assert_eq!(
        root.verify(&committee),
        Ok(()),
        "a 2f+1 hybrid quorum from the FRESH committee must authenticate the finalized root — \
         the beacon PQ half is unblocked"
    );

    // ── (5) The teeth still bite on the fresh committee. ──

    // Below threshold: one fewer distinct signer is refused.
    let short: Vec<HybridQuorumSig> = members[..threshold - 1]
        .iter()
        .map(|m| hybrid_sig(m, &msg))
        .collect();
    assert_eq!(
        FinalizedRootAttestation {
            block_id,
            merkle_root,
            fixed_at_unix: 0,
            quorum: short,
        }
        .verify(&committee),
        Err(RootError::QuorumRefused),
        "a sub-threshold quorum must be refused"
    );

    // A forged ML-DSA half (ed25519 half impeccable) is refused — no downgrade.
    let mut forged = FinalizedRootAttestation {
        block_id,
        merkle_root,
        fixed_at_unix: 0,
        quorum: members[..threshold]
            .iter()
            .map(|m| hybrid_sig(m, &msg))
            .collect(),
    };
    forged.quorum[threshold - 1].pq_signature[0] ^= 0xFF;
    assert_eq!(
        forged.verify(&committee),
        Err(RootError::QuorumRefused),
        "a forged ML-DSA half must never authenticate a root (post-quantum teeth)"
    );

    eprintln!(
        "OK: fresh n={n} committee (threshold {threshold}) authenticates a beacon finalized root; \
         the hybrid ed25519 ∧ ML-DSA-65 quorum verifies; the PQ teeth bite."
    );
}
