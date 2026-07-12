//! Shared loaders for the genuine cosmoshub-4 fixtures (see `tests/fixtures/`).
//!
//! The fixtures are REAL mainnet data pulled from `cosmos-rpc.publicnode.com`:
//!   - `commit_h.json`      — SignedHeader at height 31989760 (the trusted anchor)
//!   - `commit_h1.json`     — SignedHeader at height 31989761 (the untrusted advance)
//!   - `validators_h1.json` — the full 180-validator set at height 31989761
//!   - `membership_proof.json` — a genuine ICS-23 proof (uatom bank supply) at
//!     height 31989760, whose app_hash is committed in commit_h1's header.
#![allow(dead_code)]

use base64::engine::general_purpose::STANDARD;
use base64::Engine;
use core::time::Duration;

use cosmos_lightclient::{decode_commitment_proof, CosmosMembershipProof, TrustedCosmosState};
use tendermint::block::signed_header::SignedHeader;
use tendermint::validator::{Info, Set as ValidatorSet};
use tendermint::Time;

const DIR: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures");

pub fn read(name: &str) -> String {
    std::fs::read_to_string(format!("{DIR}/{name}")).expect("fixture present")
}

/// The genuine untrusted SignedHeader at height 31989761 (parses as raw JSON so
/// individual reject tests can also tamper it).
pub fn untrusted_value() -> serde_json::Value {
    serde_json::from_str(&read("commit_h1.json")).unwrap()
}

pub fn signed_header_from(v: &serde_json::Value) -> SignedHeader {
    serde_json::from_value(v.clone()).expect("SignedHeader parses")
}

pub fn untrusted_signed_header() -> SignedHeader {
    signed_header_from(&untrusted_value())
}

pub fn trusted_signed_header() -> SignedHeader {
    serde_json::from_str(&read("commit_h.json")).expect("SignedHeader parses")
}

/// The full validator set at height 31989761 (both the untrusted validators AND
/// the trusted `next_validators`, because 31989761 = 31989760 + 1 is adjacent).
pub fn validators_h1() -> ValidatorSet {
    let infos: Vec<Info> = serde_json::from_str(&read("validators_h1.json")).expect("validators");
    ValidatorSet::without_proposer(infos)
}

/// The trusted anchor state derived from the genuine header at height 31989760.
pub fn trusted_state() -> TrustedCosmosState {
    let th = trusted_signed_header();
    TrustedCosmosState {
        chain_id: th.header.chain_id.clone(),
        header_time: th.header.time,
        height: th.header.height,
        next_validators: validators_h1(),
        next_validators_hash: th.header.next_validators_hash,
    }
}

/// A deterministic `now` shortly after the untrusted header's block time (so the
/// trusting-period / clock-drift checks are anchored to the fixture, not the wall
/// clock).
pub fn now_after_untrusted() -> Time {
    untrusted_signed_header()
        .header
        .time
        .checked_add(Duration::from_secs(60))
        .unwrap()
}

/// A generous trusting period (the fixture header is verified as within it).
pub fn trusting_period() -> Duration {
    Duration::from_secs(14 * 24 * 60 * 60) // 14 days
}

// ---- membership fixture ----

pub struct MembershipFixture {
    pub app_hash: Vec<u8>,
    pub proof: CosmosMembershipProof,
    pub key: Vec<u8>,
    pub value: Vec<u8>,
}

pub fn membership_fixture() -> MembershipFixture {
    let v: serde_json::Value = serde_json::from_str(&read("membership_proof.json")).unwrap();
    let b64 = |k: &str| STANDARD.decode(v[k].as_str().unwrap()).unwrap();
    let app_hash = hex::decode(v["app_hash_hex"].as_str().unwrap()).unwrap();
    let iavl_proof = decode_commitment_proof(&b64("iavl_proof_b64")).unwrap();
    let store_proof = decode_commitment_proof(&b64("simple_proof_b64")).unwrap();
    MembershipFixture {
        app_hash,
        proof: CosmosMembershipProof {
            store_key: v["store_key"].as_str().unwrap().as_bytes().to_vec(),
            iavl_proof,
            store_proof,
        },
        key: b64("iavl_key_b64"),
        value: b64("value_b64"),
    }
}
