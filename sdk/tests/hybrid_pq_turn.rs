//! HYBRID (ed25519 + ML-DSA-65) turn perimeter — the SDK signing side
//! (`dregg_turn::pq`). The client (cipherclerk) always signs BOTH halves over
//! the SAME canonical message; the verifier gates the PQ half (staged). These
//! integration tests pin that the cipherclerk PRODUCES verifiable hybrid
//! material end-to-end, and that a forged PQ half fails closed.

use dregg_sdk::{AgentCipherclerk, Signature, SignedTurn};
use dregg_turn::action::{Action, Authorization, CommitmentMode, DelegationMode};
use dregg_turn::executor::TurnExecutor;

fn empty_action(target: dregg_sdk::CellId, method: u8) -> Action {
    Action {
        target,
        method: [method; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    }
}

#[test]
fn sign_action_produces_verifiable_hybrid() {
    let cclerk = AgentCipherclerk::new();
    let fed = [7u8; 32];
    let target = cclerk.cell_id("default");
    // `sign_action` (the DEFAULT signing path) now emits the hybrid variant —
    // this pins the client-turn hybrid perimeter flip.
    let signed = cclerk.sign_action(empty_action(target, 1), &fed);

    let (ed25519, ml_dsa, ml_dsa_pk) = match &signed.authorization {
        Authorization::HybridSignature {
            ed25519,
            ml_dsa,
            ml_dsa_pk,
        } => (*ed25519, ml_dsa.clone(), ml_dsa_pk.clone()),
        other => panic!("sign_action must produce a HybridSignature, got {other:?}"),
    };

    // Both halves cover the SAME compute_signing_message (over the same
    // next-turn nonce `sign_action` bound).
    let unsigned = Action {
        authorization: Authorization::Unchecked,
        ..signed.clone()
    };
    let msg = TurnExecutor::compute_signing_message(&unsigned, &fed, cclerk.next_turn_nonce());
    // Classical half verifies against the clerk's ed25519 identity.
    assert!(cclerk.public_key().verify(&msg, &Signature(ed25519)));
    // Post-quantum half is present and verifies against the carried pk.
    assert!(!ml_dsa.is_empty(), "the client always signs the PQ half");
    assert_eq!(ml_dsa_pk.len(), dregg_turn::pq::ML_DSA_PK_LEN);
    assert!(dregg_turn::pq::ml_dsa_verify(&ml_dsa_pk, &msg, &ml_dsa));
    // Forged PQ half fails closed.
    let mut forged = ml_dsa.clone();
    forged[0] ^= 0xff;
    assert!(!dregg_turn::pq::ml_dsa_verify(&ml_dsa_pk, &msg, &forged));
}

#[test]
fn sign_turn_carries_verifiable_pq_envelope() {
    let cclerk = AgentCipherclerk::new();
    let target = cclerk.cell_id("default");
    let turn = cclerk.make_turn(empty_action(target, 2));
    let signed = cclerk.sign_turn(&turn);
    let h = signed.turn.hash();

    // Classical half verifies.
    assert!(signed.signer.verify(&h, &signed.signature));
    // PQ half is present and verifies over the SAME turn hash both halves cover.
    assert!(!signed.pq_signature.is_empty());
    assert_eq!(signed.pq_signer.len(), dregg_turn::pq::ML_DSA_PK_LEN);
    assert!(dregg_turn::pq::ml_dsa_verify(
        &signed.pq_signer,
        &h,
        &signed.pq_signature
    ));
    // Present-but-forged PQ half fails closed.
    let mut forged = signed.pq_signature.clone();
    forged[0] ^= 0xff;
    assert!(!dregg_turn::pq::ml_dsa_verify(
        &signed.pq_signer,
        &h,
        &forged
    ));

    // The widened envelope round-trips through postcard (the wire flag-day).
    let bytes = postcard::to_stdvec(&signed).expect("encode");
    let back: SignedTurn = postcard::from_bytes(&bytes).expect("decode");
    assert_eq!(back.pq_signature, signed.pq_signature);
    assert_eq!(back.pq_signer, signed.pq_signer);
}

#[test]
fn derivation_is_deterministic_across_signings() {
    // The same cipherclerk derives the SAME ML-DSA key on every signing (the
    // deterministic-from-seed property that lets a node/genesis fixture built
    // from the same mnemonic agree without a separate ceremony).
    let cclerk = AgentCipherclerk::new();
    let target = cclerk.cell_id("default");
    let a = cclerk.sign_turn(&cclerk.make_turn(empty_action(target, 3)));
    let b = cclerk.sign_turn(&cclerk.make_turn(empty_action(target, 3)));
    assert_eq!(
        a.pq_signer, b.pq_signer,
        "same identity → same ML-DSA pubkey"
    );
    // Distinct identities derive distinct PQ keys.
    let other = AgentCipherclerk::new();
    let c = other.sign_turn(&other.make_turn(empty_action(other.cell_id("default"), 3)));
    assert_ne!(a.pq_signer, c.pq_signer);
}

#[test]
fn hybrid_signed_turn_hash_is_deterministic() {
    // REGRESSION: `Action::hash` binds the ML-DSA half (discriminant 10, the
    // anti-strip binding), and that action hash flows into `Turn::hash`. With a
    // HEDGED (randomized) ML-DSA signature the SAME logical turn hashed DIFFERENTLY
    // on each signing — breaking turn identity (receipt matching, dedup,
    // exactly-once). The turn perimeter now signs DETERMINISTICALLY, so the turn
    // hash is stable across signings.
    let cclerk = AgentCipherclerk::new();
    let fed = [7u8; 32];
    let target = cclerk.cell_id("default");

    // Sign the SAME logical action twice via the DEFAULT (hybrid) path.
    let a1 = cclerk.sign_action(empty_action(target, 5), &fed);
    let a2 = cclerk.sign_action(empty_action(target, 5), &fed);
    // Both carry the hybrid PQ half (this is the path that binds the ML-DSA sig).
    for a in [&a1, &a2] {
        assert!(
            matches!(a.authorization, Authorization::HybridSignature { ref ml_dsa, .. } if !ml_dsa.is_empty()),
            "sign_action must produce a hybrid authorization with a present PQ half"
        );
    }
    // The two signings produce byte-identical ML-DSA halves ...
    let (ml1, ml2) = match (&a1.authorization, &a2.authorization) {
        (
            Authorization::HybridSignature { ml_dsa: m1, .. },
            Authorization::HybridSignature { ml_dsa: m2, .. },
        ) => (m1.clone(), m2.clone()),
        _ => unreachable!(),
    };
    assert_eq!(ml1, ml2, "deterministic signing ⇒ identical ML-DSA bytes");
    // ... so the anti-strip Action::hash is deterministic ...
    assert_eq!(
        a1.hash(),
        a2.hash(),
        "same hybrid-signed action ⇒ same Action::hash"
    );
    // ... and the whole turn hash (turn identity) is deterministic.
    let t1 = cclerk.make_turn(a1);
    let t2 = cclerk.make_turn(a2);
    assert_eq!(
        t1.hash(),
        t2.hash(),
        "same logical turn ⇒ same turn_hash (turn identity restored)"
    );
}

#[test]
fn anti_strip_binding_preserved_pq_material_is_bound() {
    // The anti-strip guarantee: `Action::hash` COMMITS to the exact ML-DSA
    // material, so under a signed-turn envelope (whose signature covers the turn
    // hash) a verifier detects any strip or swap of the PQ half — the hash changes.
    // Determinism must NOT weaken this: the hash still binds the sig byte-for-byte.
    let cclerk = AgentCipherclerk::new();
    let fed = [7u8; 32];
    let target = cclerk.cell_id("default");
    let signed = cclerk.sign_action(empty_action(target, 9), &fed);
    let h_full = signed.hash();

    let (ed25519, ml_dsa, ml_dsa_pk) = match &signed.authorization {
        Authorization::HybridSignature {
            ed25519,
            ml_dsa,
            ml_dsa_pk,
        } => (*ed25519, ml_dsa.clone(), ml_dsa_pk.clone()),
        other => panic!("expected HybridSignature, got {other:?}"),
    };

    // (1) STRIP the PQ half (empty ml_dsa) ⇒ Action::hash CHANGES (strip detected).
    let stripped = Action {
        authorization: Authorization::HybridSignature {
            ed25519,
            ml_dsa: Vec::new(),
            ml_dsa_pk: ml_dsa_pk.clone(),
        },
        ..signed.clone()
    };
    assert_ne!(
        h_full,
        stripped.hash(),
        "stripping the PQ half MUST change Action::hash (anti-strip binding)"
    );

    // (2) REPLACE the PQ half with tampered bytes ⇒ Action::hash CHANGES (swap detected).
    let mut forged = ml_dsa.clone();
    forged[0] ^= 0xff;
    let replaced = Action {
        authorization: Authorization::HybridSignature {
            ed25519,
            ml_dsa: forged,
            ml_dsa_pk: ml_dsa_pk.clone(),
        },
        ..signed.clone()
    };
    assert_ne!(
        h_full,
        replaced.hash(),
        "replacing the PQ half MUST change Action::hash (anti-strip binding)"
    );

    // (3) The genuine hybrid still verifies end-to-end (no soundness regression):
    // both halves cover compute_signing_message over the unsigned action (and
    // the same next-turn nonce `sign_action` bound).
    let unsigned = Action {
        authorization: Authorization::Unchecked,
        ..signed.clone()
    };
    let msg = TurnExecutor::compute_signing_message(&unsigned, &fed, cclerk.next_turn_nonce());
    assert!(cclerk.public_key().verify(&msg, &Signature(ed25519)));
    assert!(dregg_turn::pq::ml_dsa_verify(&ml_dsa_pk, &msg, &ml_dsa));
}
