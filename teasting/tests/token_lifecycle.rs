//! Token lifecycle integration test: mint → attenuate → delegate → present → verify.
//!
//! This is the "happy path" end-to-end test. Alice mints a root token, attenuates it
//! for Bob with restricted permissions, Bob presents it to Carol's verification endpoint,
//! and Carol verifies the authorization proof.

use pyana_sdk::{Attenuation, AuthRequest};
use pyana_teasting::agent::{SimAgent, shared_root_key};

/// Full lifecycle: Alice mints → attenuates for Bob → Bob presents → Carol verifies.
#[test]
fn test_mint_attenuate_delegate_present_verify() {
    let mut alice = SimAgent::new("Alice");
    let mut bob = SimAgent::new("Bob");

    // Alice mints a root token for the "storage" service.
    let root_key = shared_root_key("storage-service");
    let root_token = alice.mint_token_with_key(&root_key, "storage");

    // Alice attenuates: Bob can only read from the "storage" service.
    let restrictions = Attenuation {
        services: vec![("storage".into(), "r".into())],
        ..Default::default()
    };
    let delegated = alice.delegate(&root_token, &bob, &restrictions).unwrap();

    // Bob receives the delegation.
    bob.receive_delegation(delegated).unwrap();

    // Bob's wallet now has the attenuated token.
    let bob_token = bob.wallet.find_token("attenuated:storage").unwrap();

    // Bob tries to read storage — should succeed.
    let read_request = AuthRequest {
        service: Some("storage".into()),
        action: Some("r".into()),
        ..Default::default()
    };
    assert!(
        bob.verify_token(bob_token, &read_request),
        "Bob should be authorized to read storage"
    );

    // Bob tries to write — should fail (only has read permission).
    let write_request = AuthRequest {
        service: Some("storage".into()),
        action: Some("w".into()),
        ..Default::default()
    };
    assert!(
        !bob.verify_token(bob_token, &write_request),
        "Bob should NOT be authorized to write"
    );
}

/// Delegation chain: Alice → Bob → Carol, each attenuating further.
#[test]
fn test_delegation_chain_three_levels() {
    let mut alice = SimAgent::new("Alice");
    let mut bob = SimAgent::new("Bob");
    let mut carol = SimAgent::new("Carol");

    let root_key = shared_root_key("api-service");
    let root_token = alice.mint_token_with_key(&root_key, "api");

    // Alice → Bob: read+write on api service
    let bob_restrictions = Attenuation {
        services: vec![("api".into(), "rw".into())],
        ..Default::default()
    };
    let delegated_to_bob = alice
        .delegate(&root_token, &bob, &bob_restrictions)
        .unwrap();
    bob.receive_delegation(delegated_to_bob).unwrap();

    let bob_token = bob.wallet.find_token("attenuated:api").unwrap().clone();

    // Bob → Carol: read only on api (further restriction)
    let carol_restrictions = Attenuation {
        services: vec![("api".into(), "r".into())],
        ..Default::default()
    };
    let delegated_to_carol = bob
        .delegate(&bob_token, &carol, &carol_restrictions)
        .unwrap();
    carol.receive_delegation(delegated_to_carol).unwrap();

    let carol_token = carol.wallet.find_token("attenuated:api").unwrap();

    // Carol can read api
    let read_req = AuthRequest {
        service: Some("api".into()),
        action: Some("r".into()),
        ..Default::default()
    };
    assert!(carol.verify_token(carol_token, &read_req));

    // Carol cannot write (Bob could, but Carol's further restriction removes it)
    let write_req = AuthRequest {
        service: Some("api".into()),
        action: Some("w".into()),
        ..Default::default()
    };
    assert!(!carol.verify_token(carol_token, &write_req));
}

/// Prove authorization with a STARK proof (root holder can generate proofs).
#[test]
fn test_prove_authorization_stark() {
    let mut alice = SimAgent::new("Alice");
    let root_key = shared_root_key("compute-service");
    let root_token = alice.mint_token_with_key(&root_key, "compute");

    let request = AuthRequest {
        service: Some("compute".into()),
        action: Some("exec".into()),
        ..Default::default()
    };

    // Generate a real STARK presentation proof.
    let proof = alice.prove_authorization(&root_token, &request).unwrap();

    // The proof should be valid.
    assert!(proof.is_valid(), "STARK proof should be valid");
    assert!(
        proof.is_constraint_checked(),
        "Constraints should be satisfied"
    );
}

/// Chain proof: root token + explicit attenuations → STARK proof.
#[test]
fn test_prove_with_attenuation_chain() {
    let mut alice = SimAgent::new("Alice");
    let root_key = shared_root_key("dns-service");
    let root_token = alice.mint_token_with_key(&root_key, "dns");

    let att1 = Attenuation {
        services: vec![("dns".into(), "r".into())],
        ..Default::default()
    };
    let att2 = Attenuation {
        features: vec!["example.com".into()],
        ..Default::default()
    };

    let request = AuthRequest {
        service: Some("dns".into()),
        action: Some("r".into()),
        features: vec!["example.com".into()],
        ..Default::default()
    };

    let proof = alice
        .prove_with_chain(&root_token, &[att1, att2], &request)
        .unwrap();

    assert!(proof.is_valid());
    assert!(proof.chain_length >= 2, "Should have at least 2 fold steps");
}
