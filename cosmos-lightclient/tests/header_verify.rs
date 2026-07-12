//! Header-verification KATs against genuine cosmoshub-4 data, BOTH polarities,
//! all default-run.
//!
//! ACCEPT: the real height-31989761 SignedHeader + its real 180-validator set
//! verifies as an advance from the real height-31989760 anchor (>= 2/3 of the
//! actual voting power signed the real commit — genuine Ed25519 verification by
//! tendermint-light-client-verifier).
//!
//! REJECT (fail-closed): a tampered commit signature, a wrong chain id, an
//! expired trusting period, a mismatched validator set. NOMAD-LAW: an empty
//! validator set / zero voting power never verifies.

mod common;

use core::time::Duration;

use cosmos_lightclient::{verify_cosmos_header, HeaderVerifyError};
use tendermint::validator::Set as ValidatorSet;
use tendermint_light_client_verifier::types::TrustThreshold;

fn tt() -> TrustThreshold {
    TrustThreshold::TWO_THIRDS
}

// ---------------------------------------------------------------- ACCEPT KAT

#[test]
fn accept_real_cosmoshub_header_advance() {
    let trusted = common::trusted_state();
    let ush = common::untrusted_signed_header();
    let vals = common::validators_h1();

    let verified = verify_cosmos_header(
        &trusted,
        &ush,
        &vals,
        None,
        tt(),
        common::trusting_period(),
        common::now_after_untrusted(),
    )
    .expect("genuine cosmoshub-4 header must verify");

    assert_eq!(verified.chain_id(), "cosmoshub-4");
    assert_eq!(verified.height(), 31989761);
    // The verified app_hash is the one committed in the real header, and equals
    // the root the membership fixture opens into.
    assert_eq!(verified.app_hash(), common::membership_fixture().app_hash);
}

// ---------------------------------------------------------------- REJECT: sig

#[test]
fn reject_tampered_commit_signature() {
    // Flip one base64 char inside the FIRST present commit signature. The verifier
    // verifies every committing signature's real Ed25519 sig; a single corrupted
    // signature fails the whole commit (never silently skipped).
    let mut v = common::untrusted_value();
    let sigs = v["commit"]["signatures"].as_array_mut().unwrap();
    let mut tampered = false;
    for s in sigs.iter_mut() {
        if let Some(sig) = s["signature"].as_str() {
            if !sig.is_empty() {
                let mut bytes = sig.as_bytes().to_vec();
                // flip the first char to a different valid base64 char
                bytes[0] = if bytes[0] == b'A' { b'B' } else { b'A' };
                s["signature"] = serde_json::Value::String(String::from_utf8(bytes).unwrap());
                tampered = true;
                break;
            }
        }
    }
    assert!(tampered, "found a signature to tamper");

    let ush = common::signed_header_from(&v);
    let r = verify_cosmos_header(
        &common::trusted_state(),
        &ush,
        &common::validators_h1(),
        None,
        tt(),
        common::trusting_period(),
        common::now_after_untrusted(),
    );
    assert!(
        r.is_err(),
        "a tampered commit signature must never verify, got {r:?}"
    );
}

// ------------------------------------------------------------ REJECT: chain id

#[test]
fn reject_wrong_chain_id() {
    let mut trusted = common::trusted_state();
    trusted.chain_id = "osmosis-1".parse().unwrap();
    let r = verify_cosmos_header(
        &trusted,
        &common::untrusted_signed_header(),
        &common::validators_h1(),
        None,
        tt(),
        common::trusting_period(),
        common::now_after_untrusted(),
    );
    assert!(
        matches!(r, Err(HeaderVerifyError::Invalid(_))),
        "a chain-id mismatch must be refused, got {r:?}"
    );
}

// ------------------------------------------------------------- REJECT: expired

#[test]
fn reject_expired_trusting_period() {
    // A 1-second trusting period, with `now` a minute after the block: the trusted
    // header is long outside the trusting window -> refused.
    let r = verify_cosmos_header(
        &common::trusted_state(),
        &common::untrusted_signed_header(),
        &common::validators_h1(),
        None,
        tt(),
        Duration::from_secs(1),
        common::now_after_untrusted(),
    );
    assert!(
        matches!(r, Err(HeaderVerifyError::Invalid(_))),
        "an expired trusting period must be refused, got {r:?}"
    );
}

// --------------------------------------------------- REJECT: wrong validator set

#[test]
fn reject_mismatched_validator_set() {
    // Drop one validator: the set hash no longer matches the header's
    // validators_hash -> refused (the validator-set binding).
    let mut infos: Vec<tendermint::validator::Info> =
        serde_json::from_str(&common::read("validators_h1.json")).unwrap();
    infos.pop();
    let vals = ValidatorSet::without_proposer(infos);

    let r = verify_cosmos_header(
        &common::trusted_state(),
        &common::untrusted_signed_header(),
        &vals,
        None,
        tt(),
        common::trusting_period(),
        common::now_after_untrusted(),
    );
    assert!(
        r.is_err(),
        "a validator set that does not hash to the header must be refused, got {r:?}"
    );
}

// ----------------------------------------------------------------- NOMAD LAW

#[test]
fn nomad_empty_validator_set_never_verifies() {
    // An empty validator set (zero total voting power) can never carry a >= 2/3
    // commit, and its hash cannot match the header -> refused.
    let empty = ValidatorSet::without_proposer(vec![]);
    let r = verify_cosmos_header(
        &common::trusted_state(),
        &common::untrusted_signed_header(),
        &empty,
        None,
        tt(),
        common::trusting_period(),
        common::now_after_untrusted(),
    );
    assert!(
        r.is_err(),
        "empty validator set / zero power must never verify, got {r:?}"
    );
}

#[test]
fn nomad_zero_power_validators_never_verify() {
    // Take the real validators but zero every voting power. Total power 0; even if
    // the (now different) hash somehow slipped through, no >= 2/3 threshold exists.
    let mut infos: Vec<tendermint::validator::Info> =
        serde_json::from_str(&common::read("validators_h1.json")).unwrap();
    for i in infos.iter_mut() {
        i.power = 0u32.into();
    }
    let vals = ValidatorSet::without_proposer(infos);
    let r = verify_cosmos_header(
        &common::trusted_state(),
        &common::untrusted_signed_header(),
        &vals,
        None,
        tt(),
        common::trusting_period(),
        common::now_after_untrusted(),
    );
    assert!(
        r.is_err(),
        "all-zero voting power must never verify, got {r:?}"
    );
}
