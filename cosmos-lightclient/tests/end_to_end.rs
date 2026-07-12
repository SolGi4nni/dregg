//! End-to-end: a genuine cosmoshub-4 header verifies (>= 2/3 voting power), and
//! under ITS verified app_hash a genuine ICS-23 proof binds a `ProvenCosmosFact` —
//! the Cosmos analog of `ProvenHolding`. This is the whole inbound socket: dregg
//! verifying Cosmos state by proof, from consensus down to a single key.
//!
//! REJECT (fail-closed): the same verified header, but a wrong value never binds
//! a fact.

mod common;

use cosmos_lightclient::{prove_cosmos_fact, verify_cosmos_header, MembershipError};
use tendermint_light_client_verifier::types::TrustThreshold;

fn verified_header() -> cosmos_lightclient::VerifiedHeader {
    verify_cosmos_header(
        &common::trusted_state(),
        &common::untrusted_signed_header(),
        &common::validators_h1(),
        None,
        TrustThreshold::TWO_THIRDS,
        common::trusting_period(),
        common::now_after_untrusted(),
    )
    .expect("genuine header verifies")
}

#[test]
fn accept_proven_fact_under_verified_header() {
    let header = verified_header();
    let f = common::membership_fixture();
    // The verified header's app_hash IS the membership root (the header at
    // 31989761 commits the app state produced by executing 31989760, which the
    // proof opens into).
    assert_eq!(header.app_hash(), f.app_hash.as_slice());

    let fact = prove_cosmos_fact(&header, &f.proof, &f.key, &f.value)
        .expect("genuine state proof binds a fact");

    assert_eq!(fact.chain_id(), "cosmoshub-4");
    assert_eq!(fact.height(), 31989761);
    assert_eq!(fact.store_key(), b"bank");
    assert_eq!(fact.key(), f.key.as_slice());
    assert_eq!(fact.value(), f.value.as_slice());
    // The proven value is the real uatom total supply committed on cosmoshub-4.
    assert_eq!(fact.value(), b"518912156523696");
}

#[test]
fn reject_fact_with_wrong_value() {
    let header = verified_header();
    let f = common::membership_fixture();
    let mut wrong = f.value.clone();
    wrong[0] ^= 0xFF;
    let r = prove_cosmos_fact(&header, &f.proof, &f.key, &wrong);
    assert_eq!(
        r,
        Err(MembershipError::IavlProofInvalid),
        "a fact must never bind to a value the state proof does not commit"
    );
}
