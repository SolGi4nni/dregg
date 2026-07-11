//! REAL EXTERNAL BLS ciphersuite conformance KATs.
//!
//! These vectors are the genuine `ethereum/bls12-381-tests` v0.1.2 release
//! vectors (the canonical consensus-spec BLS test suite for the ciphersuite
//! `BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_`). The signatures were produced
//! by an INDEPENDENT implementation, not by this crate — so passing them proves
//! our BLS path + DST are actually spec-conformant, not merely round-trip
//! self-consistent.
//!
//! Source: `gh release download v0.1.2 -R ethereum/bls12-381-tests`
//!   - verify/verify_valid_case_3208262581c8fc09.json            (accept)
//!   - verify/verify_tampered_signature_case_3208262581c8fc09.json (reject)
//!   - verify/verify_infinity_pubkey_and_infinity_signature.json  (reject)
//!   - fast_aggregate_verify/fast_aggregate_verify_valid_3d7576f3c0e3570a.json (accept)
//!   - fast_aggregate_verify/fast_aggregate_verify_tampered_signature_3d7576f3c0e3570a.json (reject)

use eth_lightclient::{bls_fast_aggregate_verify, bls_verify};

fn h48(s: &str) -> [u8; 48] {
    let v = hex::decode(s.trim_start_matches("0x")).unwrap();
    v.try_into().unwrap()
}
fn h96(s: &str) -> [u8; 96] {
    let v = hex::decode(s.trim_start_matches("0x")).unwrap();
    v.try_into().unwrap()
}
fn hbytes(s: &str) -> Vec<u8> {
    hex::decode(s.trim_start_matches("0x")).unwrap()
}

// --- verify (single) ------------------------------------------------------

const V_PUBKEY: &str = "0xb301803f8b5ac4a1133581fc676dfedc60d891dd5fa99028805e5ea5b08d3491af75d0707adab3b70c6a6a580217bf81";
const V_MESSAGE: &str = "0x5656565656565656565656565656565656565656565656565656565656565656";
const V_SIG_VALID: &str = "0xaf1390c3c47acdb37131a51216da683c509fce0e954328a59f93aebda7e4ff974ba208d9a4a2a2389f892a9d418d618418dd7f7a6bc7aa0da999a9d3a5b815bc085e14fd001f6a1948768a3f4afefc8b8240dda329f984cb345c6363272ba4fe";
// same as valid but last 4 bytes tampered to 0xffffffff
const V_SIG_TAMPERED: &str = "0xaf1390c3c47acdb37131a51216da683c509fce0e954328a59f93aebda7e4ff974ba208d9a4a2a2389f892a9d418d618418dd7f7a6bc7aa0da999a9d3a5b815bc085e14fd001f6a1948768a3f4afefc8b8240dda329f984cb345c6363ffffffff";

#[test]
fn kat_verify_valid_accepts() {
    assert!(
        bls_verify(&h48(V_PUBKEY), &hbytes(V_MESSAGE), &h96(V_SIG_VALID)).is_ok(),
        "real ETH2 verify vector must accept"
    );
}

#[test]
fn kat_verify_tampered_rejects() {
    assert!(
        bls_verify(&h48(V_PUBKEY), &hbytes(V_MESSAGE), &h96(V_SIG_TAMPERED)).is_err(),
        "tampered signature must reject"
    );
}

#[test]
fn kat_verify_wrong_message_rejects() {
    // Same valid signature, different message -> must reject (domain/message binding).
    let wrong_msg = [0u8; 32];
    assert!(
        bls_verify(&h48(V_PUBKEY), &wrong_msg, &h96(V_SIG_VALID)).is_err(),
        "valid sig over a different message must reject"
    );
}

const INF_PUBKEY: &str = "0xc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
const INF_MESSAGE: &str = "0x1212121212121212121212121212121212121212121212121212121212121212";
const INF_SIG: &str = "0xc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";

#[test]
fn kat_infinity_pubkey_and_signature_rejects() {
    // NOMAD-LAW at the ciphersuite level: the identity pubkey + identity signature
    // must NEVER verify (this is the classic BLS forgery hole; blst rejects the
    // infinity pubkey via pk_validate).
    assert!(
        bls_verify(&h48(INF_PUBKEY), &hbytes(INF_MESSAGE), &h96(INF_SIG)).is_err(),
        "infinity pubkey + infinity signature must reject"
    );
}

// --- fast_aggregate_verify (the sync-aggregate analog) --------------------

const FA_PK0: &str = "0xa491d1b0ecd9bb917989f0e74f0dea0422eac4a873e5e2644f368dffb9a6e20fd6e10c1b77654d067c0618f6e5a7f79a";
const FA_PK1: &str = "0xb301803f8b5ac4a1133581fc676dfedc60d891dd5fa99028805e5ea5b08d3491af75d0707adab3b70c6a6a580217bf81";
const FA_PK2: &str = "0xb53d21a4cfd562c469cc81514d4ce5a6b577d8403d32a394dc265dd190b47fa9f829fdd7963afdf972e5e77854051f6f";
const FA_MESSAGE: &str = "0xabababababababababababababababababababababababababababababababab";
const FA_SIG_VALID: &str = "0x9712c3edd73a209c742b8250759db12549b3eaf43b5ca61376d9f30e2747dbcf842d8b2ac0901d2a093713e20284a7670fcf6954e9ab93de991bb9b313e664785a075fc285806fa5224c82bde146561b446ccfc706a64b8579513cfc4ff1d930";
const FA_SIG_TAMPERED: &str = "0x9712c3edd73a209c742b8250759db12549b3eaf43b5ca61376d9f30e2747dbcf842d8b2ac0901d2a093713e20284a7670fcf6954e9ab93de991bb9b313e664785a075fc285806fa5224c82bde146561b446ccfc706a64b8579513cfcffffffff";

#[test]
fn kat_fast_aggregate_valid_accepts() {
    let pks = [h48(FA_PK0), h48(FA_PK1), h48(FA_PK2)];
    assert!(
        bls_fast_aggregate_verify(&pks, &hbytes(FA_MESSAGE), &h96(FA_SIG_VALID)).is_ok(),
        "real ETH2 fast_aggregate_verify vector must accept"
    );
}

#[test]
fn kat_fast_aggregate_tampered_rejects() {
    let pks = [h48(FA_PK0), h48(FA_PK1), h48(FA_PK2)];
    assert!(
        bls_fast_aggregate_verify(&pks, &hbytes(FA_MESSAGE), &h96(FA_SIG_TAMPERED)).is_err(),
        "tampered aggregate signature must reject"
    );
}

#[test]
fn kat_fast_aggregate_dropped_pubkey_rejects() {
    // Drop one signer: the aggregate no longer matches -> reject.
    let pks = [h48(FA_PK0), h48(FA_PK1)];
    assert!(
        bls_fast_aggregate_verify(&pks, &hbytes(FA_MESSAGE), &h96(FA_SIG_VALID)).is_err(),
        "aggregate missing a signer must reject"
    );
}
