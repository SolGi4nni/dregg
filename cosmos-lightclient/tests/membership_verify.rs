//! ICS-23 membership KATs against a genuine cosmoshub-4 proof, BOTH polarities,
//! all default-run.
//!
//! ACCEPT: the real two-op proof (iavl `0x00 uatom` bank-supply exist + tendermint
//! `bank`-store exist) verifies `key -> value` under the real app_hash committed
//! in the height-31989761 header.
//!
//! REJECT (fail-closed): a tampered iavl proof, a tampered store proof, a wrong
//! value, a wrong key, a wrong app_hash, a non-existence proof passed as
//! membership.

mod common;

use cosmos_lightclient::{verify_cosmos_membership, MembershipError};

// ---------------------------------------------------------------- ACCEPT KAT

#[test]
fn accept_real_ics23_membership() {
    let f = common::membership_fixture();
    verify_cosmos_membership(&f.app_hash, &f.proof, &f.key, &f.value)
        .expect("genuine cosmoshub-4 uatom-supply proof must verify");
}

// ----------------------------------------------------------- REJECT: bad value

#[test]
fn reject_wrong_value() {
    let f = common::membership_fixture();
    let mut wrong = f.value.clone();
    wrong[0] ^= 0xFF; // any different value
    let r = verify_cosmos_membership(&f.app_hash, &f.proof, &f.key, &wrong);
    assert_eq!(
        r,
        Err(MembershipError::IavlProofInvalid),
        "a wrong value must break the iavl leaf binding"
    );
}

#[test]
fn reject_wrong_key() {
    let f = common::membership_fixture();
    let mut wrong = f.key.clone();
    *wrong.last_mut().unwrap() ^= 0x01; // 0x00 "uato" + tampered last byte
    let r = verify_cosmos_membership(&f.app_hash, &f.proof, &wrong, &f.value);
    assert!(r.is_err(), "a wrong key must not verify, got {r:?}");
}

// ----------------------------------------------------- REJECT: tampered proofs

#[test]
fn reject_tampered_iavl_proof() {
    // Corrupt a byte in the iavl leaf value: recomputing the sub-root gives a
    // different root, which no longer matches what the store proof commits ->
    // refused.
    let f = common::membership_fixture();
    let mut proof = f.proof.clone();
    if let Some(ics23::commitment_proof::Proof::Exist(ex)) = proof.iavl_proof.proof.as_mut() {
        // flip a byte in the leaf value the proof carries
        if let Some(b) = ex.value.first_mut() {
            *b ^= 0xFF;
        }
    } else {
        panic!("iavl op is an existence proof");
    }
    let r = verify_cosmos_membership(&f.app_hash, &proof, &f.key, &f.value);
    assert!(
        r.is_err(),
        "a tampered iavl proof must not verify, got {r:?}"
    );
}

#[test]
fn reject_tampered_store_proof() {
    // Corrupt the outer tendermint proof: its recomputed top root will differ from
    // the real app_hash -> AppHashMismatch (or a spec failure). Either way refused.
    let f = common::membership_fixture();
    let mut proof = f.proof.clone();
    if let Some(ics23::commitment_proof::Proof::Exist(ex)) = proof.store_proof.proof.as_mut() {
        if let Some(step) = ex.path.first_mut() {
            // perturb an inner node hash suffix
            step.suffix.push(0xAB);
        } else if let Some(b) = ex.value.first_mut() {
            *b ^= 0xFF;
        }
    } else {
        panic!("store op is an existence proof");
    }
    let r = verify_cosmos_membership(&f.app_hash, &proof, &f.key, &f.value);
    assert!(
        r.is_err(),
        "a tampered store proof must not verify, got {r:?}"
    );
}

// ------------------------------------------------------- REJECT: wrong app_hash

#[test]
fn reject_wrong_app_hash() {
    let f = common::membership_fixture();
    let mut bad = f.app_hash.clone();
    bad[0] ^= 0xFF;
    let r = verify_cosmos_membership(&bad, &f.proof, &f.key, &f.value);
    assert_eq!(
        r,
        Err(MembershipError::AppHashMismatch),
        "a proof must not verify against the wrong app_hash"
    );
}

// ----------------------------------------------------- REJECT: non-existence op

#[test]
fn reject_non_existence_op_as_membership() {
    // Replace the iavl existence proof with a (empty) non-existence proof. A
    // non-membership proof can never prove membership -> NotExistenceProof.
    let f = common::membership_fixture();
    let mut proof = f.proof.clone();
    proof.iavl_proof.proof = Some(ics23::commitment_proof::Proof::Nonexist(
        ics23::NonExistenceProof::default(),
    ));
    let r = verify_cosmos_membership(&f.app_hash, &proof, &f.key, &f.value);
    assert_eq!(
        r,
        Err(MembershipError::NotExistenceProof),
        "a non-existence proof must never count as membership"
    );
}
