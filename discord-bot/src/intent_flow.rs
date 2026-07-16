//! Real, canonical signed-intent flow — the bot brokers genuine signed Intents
//! between clique members (§4.7 "broker signed intents").
//!
//! This module is **Discord-independent**. A posted intent is a canonical
//! `dregg_turn::action::Action` with method `"intent.post"`, carrying the
//! human-readable spec in its `args`, and signed with the poster's real Ed25519
//! key through the canonical `AppCipherclerk::sign_action` path. The
//! authorization is a real `Authorization::Signature` over
//! `TurnExecutor::compute_signing_message(action, federation_id, turn_nonce)` — NOT a mock
//! string. Anyone can verify the signature against the poster's public key.
//!
//! # Why a signed Action, not `dregg_intent::Intent`
//!
//! The `dregg-intent` crate's `Intent` is an *anonymous-commitment* primitive
//! (Poseidon2 stake proofs, content-addressed ids, no signer identity) built
//! for the trustless solver/gossip path, and it pulls in circuit/commit deps
//! the bot deliberately does not carry. For a Discord clique where members post
//! intents under their own (hosted) identity and react to fulfill, the honest
//! real artifact is a *signed* canonical Action — the same envelope the node
//! ingests. If/when the bot should publish anonymous solver-network intents,
//! that is a separate, named follow-up (see the report).

use dregg_app_framework::AppCipherclerk;
use dregg_turn::action::{Action, Authorization};

/// A signed intent ready to post to a channel.
#[derive(Debug, Clone)]
pub struct SignedIntent {
    /// The canonical signed action (method `"intent.post"`).
    pub action: Action,
    /// The poster's public key bytes (for verification / display).
    pub poster_pk: [u8; 32],
    /// The federation id the signature is bound to.
    pub federation_id: [u8; 32],
    /// The turn nonce the signature is bound to (`dregg-action-sig-v3`): the
    /// poster's next submitting-turn nonce at sign time
    /// (`AppCipherclerk::next_turn_nonce`). Verifiers recompute the signing
    /// message over exactly this value.
    pub turn_nonce: u64,
    /// The human-readable spec, echoed for display.
    pub spec: String,
}

/// Build a **real** signed intent: a canonical `Action` carrying `spec`,
/// authorized with the poster's Ed25519 signature.
///
/// `cclerk` is the poster's hosted [`AppCipherclerk`]; the signature is
/// produced by `sign_action` and binds the spec bytes + federation id.
pub fn build_signed_intent(cclerk: &AppCipherclerk, spec: &str) -> SignedIntent {
    let target = cclerk.cell_id();
    // method "intent.post"; `args` are canonical field elements ([u8; 32]), so
    // we bind the spec by its BLAKE3 hash as the single arg. The canonical
    // signing message hashes target + method + args, so the signature is bound
    // to the exact spec content (full text is echoed in `spec` for display).
    let spec_hash = *blake3::hash(spec.as_bytes()).as_bytes();
    let mut action = cclerk.make_action(target, "intent.post", Vec::new());
    action.args = vec![spec_hash];
    // The nonce `sign_action` binds into the signature (dregg-action-sig-v3):
    // the poster's next submitting-turn nonce. Captured here so verifiers can
    // recompute the exact signing message.
    let turn_nonce = cclerk.next_turn_nonce();
    // Re-sign now that args carry the spec hash (make_action signed the empty form).
    let action = cclerk.sign_action(action);

    SignedIntent {
        action,
        poster_pk: cclerk.public_key().0,
        federation_id: *cclerk.federation_id(),
        turn_nonce,
        spec: spec.to_string(),
    }
}

/// Verify a signed intent's Ed25519 authorization against the poster's public
/// key. This is the canonical check the node executor performs.
pub fn verify_signed_intent(intent: &SignedIntent) -> bool {
    verify_action_signature(
        &intent.action,
        &intent.poster_pk,
        &intent.federation_id,
        intent.turn_nonce,
    )
}

/// Canonical Ed25519 verification of a signed action — classical
/// `Authorization::Signature` or the hybrid `Authorization::HybridSignature`
/// the framework signing path emits since the hybrid flip.
///
/// Verifies the ed25519 signature against
/// `compute_signing_message(action, federation_id, turn_nonce)` — exactly as
/// `dregg_turn`'s executor does, using `dregg_types::PublicKey::verify`
/// (`verify_strict` under the hood, rejecting malleable signatures). For the
/// hybrid variant it mirrors the executor's fail-closed rule: a
/// present-but-invalid ML-DSA half REJECTS.
pub fn verify_action_signature(
    action: &Action,
    signer_pk: &[u8; 32],
    federation_id: &[u8; 32],
    turn_nonce: u64,
) -> bool {
    use dregg_turn::executor::TurnExecutor;
    use dregg_types::{PublicKey, Signature};

    let (sig_bytes, pq_half) = match &action.authorization {
        Authorization::Signature(r, s) => {
            let mut sig = [0u8; 64];
            sig[..32].copy_from_slice(r);
            sig[32..].copy_from_slice(s);
            (sig, None)
        }
        Authorization::HybridSignature {
            ed25519,
            ml_dsa,
            ml_dsa_pk,
        } => (*ed25519, Some((ml_dsa, ml_dsa_pk))),
        _ => return false,
    };

    let message = TurnExecutor::compute_signing_message(action, federation_id, turn_nonce);
    if !PublicKey(*signer_pk).verify(&message, &Signature(sig_bytes)) {
        return false;
    }
    // Fail-closed on a present-but-invalid PQ half, as the executor does.
    match pq_half {
        Some((ml_dsa, ml_dsa_pk)) if !ml_dsa.is_empty() => {
            dregg_turn::pq::ml_dsa_verify(ml_dsa_pk, &message, ml_dsa)
        }
        _ => true,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cipherclerk::UserCipherclerk;

    fn cclerk_for(bot_secret: &[u8; 32], uid: u64, fed: [u8; 32]) -> AppCipherclerk {
        UserCipherclerk::derive(bot_secret, uid, fed).app
    }

    #[test]
    fn build_produces_a_real_signed_intent_that_verifies() {
        let fed = [11u8; 32];
        let cclerk = cclerk_for(&[1u8; 32], 4242, fed);
        let intent = build_signed_intent(&cclerk, "want: 5 GOOSE for 1 hr of compute");

        // Real Ed25519 signature over the canonical signing message — a mock
        // string could never satisfy verify_strict.
        assert!(
            verify_signed_intent(&intent),
            "signed intent must carry a valid Ed25519 authorization"
        );
        assert!(matches!(
            intent.action.authorization,
            Authorization::HybridSignature { .. }
        ));
        assert_eq!(
            intent.action.args,
            vec![*blake3::hash(intent.spec.as_bytes()).as_bytes()]
        );
        assert_eq!(intent.poster_pk, cclerk.public_key().0);
    }

    #[test]
    fn tampered_spec_fails_verification() {
        let fed = [12u8; 32];
        let cclerk = cclerk_for(&[2u8; 32], 1, fed);
        let mut intent = build_signed_intent(&cclerk, "original spec");

        // Mutate the spec args after signing — the signature must no longer
        // verify (the signing message hashes the args).
        intent.action.args = vec![*blake3::hash(b"forged spec").as_bytes()];
        assert!(
            !verify_signed_intent(&intent),
            "tampering with the intent spec must invalidate the signature"
        );
    }

    #[test]
    fn wrong_pubkey_fails_verification() {
        let fed = [13u8; 32];
        let cclerk = cclerk_for(&[3u8; 32], 7, fed);
        let other = cclerk_for(&[3u8; 32], 8, fed);
        let mut intent = build_signed_intent(&cclerk, "spec");
        // Claim a different poster — verification must fail.
        intent.poster_pk = other.public_key().0;
        assert!(!verify_signed_intent(&intent));
    }
}
