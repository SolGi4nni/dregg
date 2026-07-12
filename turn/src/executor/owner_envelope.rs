//! The OWNER-SIGNED ENVELOPE keystone — owner-key-gated c-list mutation for a
//! host-keyed worker grain (the upgrade-safety weld).
//!
//! An enveloped worker cell is minted by the HOST (`sdk::runtime::
//! spawn_sub_agent_scoped` gives it a FRESH host-retained cipherclerk), so the
//! cell's OWN ed25519 key is the host's. Any `AuthRequired::Signature` gate on
//! that cell is therefore satisfiable by the host — which is exactly why the
//! bare "the actor holds a Signature-floor cap whose breadstuff == the committed
//! root" check is host-forgeable (the host controls both the root slot and the
//! c-list). This module supplies the one key the host does NOT hold — the
//! renter/owner key (`agent_platform::RenterAnchor::pubkey`) — as the authority
//! that gates authority-WIDENING actions on the worker.
//!
//! Mechanism (reuses the in-tree `Authorization::Custom` seam verbatim — no new
//! executor path, no `CapabilityRef` field): the worker cell's `set_permissions`,
//! `delegate`, and `set_verification_key` permission slots are set to
//! `AuthRequired::Custom { vk_hash }`, where
//! `vk_hash == owner_envelope_vk(&owner_pubkey)`. A turn that mutates the worker's
//! c-list (`Delegate`), relaxes its gates (`SetPermissions`), or swaps its
//! verification key must therefore carry an `Authorization::Custom` predicate
//! whose registered verifier is this [`OwnerEnvelopeSigVerifier`]. The verifier
//! accepts ONLY a valid ed25519 signature by `owner_pubkey` over the executor's
//! canonical custom signing message (`compute_custom_signing_message` —
//! federation_id + turn_nonce + action shape). The host, lacking the owner key,
//! cannot produce that signature, so through the executor it cannot self-grant a
//! broader cap or relax the gate.
//!
//! Because the owner key is pinned in the cell's PERMISSIONS (not in a mutable
//! app-state slot), the gate is self-protecting: changing `set_permissions` on
//! the worker itself requires the owner key. Bootstrap happens at rent, while the
//! owner is active (`AgentPlatform::rent` holds the `RenterAnchor`).
//!
//! ## Honest scope (R1 hardening, NOT R3)
//!
//! This closes the c-list-mutation path for turns that go THROUGH the executor's
//! authorization seam — a provider running the standard node software cannot
//! craft a `Delegate`/`SetPermissions` turn that widens its own authority over
//! the worker. It does NOT, and cannot, stop a provider that runs MODIFIED
//! software and mutates its own in-process `Ledger` directly (that write bypasses
//! the executor entirely). Against that adversary the teeth are the owner's
//! checkpoint COUNTERSIGNATURE over the envelope root (Lane 3 —
//! `grain_verify` / `agent_platform::verify_landed`), which the modified host
//! still cannot forge, so its out-of-envelope state is rejected at the passive
//! owner's verify. A per-turn in-envelope proof that binds even the
//! direct-mutation path cryptographically is the open R3 follow-up. This module
//! is the R1 hardening that makes the honest-software authorization path
//! owner-rooted rather than an internal-consistency check.

use std::sync::Arc;

use dregg_cell::predicate::{
    PredicateInput, WitnessedPredicateError, WitnessedPredicateKind, WitnessedPredicateRegistry,
    WitnessedPredicateVerifier,
};
use ed25519_dalek::{Signature, VerifyingKey};

/// Domain separator for the owner-envelope custom verifier-key hash. Versioned:
/// a future signing-message-shape change bumps this so the vk_hash (and thus the
/// cell-committed `Custom { vk_hash }`) is unambiguous across versions.
pub const OWNER_ENVELOPE_VK_DOMAIN: &[u8] = b"dregg.envelope.owner-sig.v1";

/// The `Custom { vk_hash }` this verifier answers for, derived from the owner's
/// ed25519 public key. Binding the vk_hash to the owner key is what pins a
/// specific owner into the worker cell's permission slots: the executor's
/// `verify_custom_authorization` step-1 requires the presented predicate's
/// `Custom { vk_hash }` to equal the cell-committed one, so only the owner named
/// here satisfies the gate.
pub fn owner_envelope_vk(owner_pubkey: &[u8; 32]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(OWNER_ENVELOPE_VK_DOMAIN);
    hasher.update(owner_pubkey);
    *hasher.finalize().as_bytes()
}

/// Verifier for the OWNER-SIGNED ENVELOPE `Custom { vk_hash }` gate.
///
/// Holds the owner ed25519 public key it answers for; registered under
/// `owner_envelope_vk(&owner_pubkey)`. `verify` accepts ONLY a 64-byte ed25519
/// signature (the proof blob) by `owner_pubkey` over the executor-supplied
/// canonical custom signing message. Fails closed on any other input shape, a
/// malformed key/signature, a mismatched predicate commitment, or a bad
/// signature.
#[derive(Clone, Debug)]
pub struct OwnerEnvelopeSigVerifier {
    owner_pubkey: [u8; 32],
    vk_hash: [u8; 32],
}

impl OwnerEnvelopeSigVerifier {
    /// Construct the verifier answering for `owner_pubkey`.
    pub fn new(owner_pubkey: [u8; 32]) -> Self {
        let vk_hash = owner_envelope_vk(&owner_pubkey);
        Self {
            owner_pubkey,
            vk_hash,
        }
    }

    /// The owner key this verifier gates against.
    pub fn owner_pubkey(&self) -> &[u8; 32] {
        &self.owner_pubkey
    }

    /// The `Custom` vk_hash this verifier is registered under (the value stamped
    /// into the worker cell's `set_permissions`/`delegate`/`set_verification_key`
    /// slots via `dregg_cell::Permissions::enveloped_worker`).
    pub fn vk_hash(&self) -> [u8; 32] {
        self.vk_hash
    }
}

impl WitnessedPredicateVerifier for OwnerEnvelopeSigVerifier {
    fn name(&self) -> &'static str {
        "owner-envelope-sig"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::Custom {
            vk_hash: self.vk_hash,
        }
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        // The message the owner must have signed: the executor's canonical custom
        // signing message (federation_id + turn_nonce + action shape), supplied as
        // `AuthContext` at the authorization seam. Bind ONLY to that shape — a
        // plain `SigningMessage` is accepted identically (the cell pre-state leg is
        // unused here; the owner key is pinned via `vk_hash`, not a slot).
        let message: &[u8] = match input {
            PredicateInput::AuthContext {
                signing_message, ..
            } => signing_message,
            PredicateInput::SigningMessage(m) => m,
            other => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: "owner-envelope-sig",
                    expected: "AuthContext / SigningMessage (canonical custom-auth message bytes)",
                    actual: match other {
                        PredicateInput::Slot(_) => "Slot",
                        PredicateInput::Bytes(_) => "Bytes",
                        PredicateInput::PublicInput(_) => "PublicInput",
                        PredicateInput::Sender(_) => "Sender",
                        // AuthContext / SigningMessage handled above.
                        _ => "unexpected",
                    },
                });
            }
        };

        // Defense-in-depth: the on-wire predicate must name the owner it claims to
        // authorize under. The AUTHORITATIVE pin is the executor's step-1 check
        // (predicate.kind.vk_hash == the cell-committed vk_hash, which derives from
        // THIS owner key); this makes the predicate self-describing and rejects a
        // confusing accept under a mismatched commitment.
        if commitment != &self.owner_pubkey {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: "owner-envelope-sig",
                reason: "predicate commitment does not equal the gated owner public key".into(),
            });
        }

        // The proof blob is a raw 64-byte ed25519 signature.
        if proof_bytes.len() != 64 {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: "owner-envelope-sig",
                reason: format!(
                    "owner-envelope proof must be a 64-byte ed25519 signature, got {} bytes",
                    proof_bytes.len()
                ),
            });
        }
        let mut sig_bytes = [0u8; 64];
        sig_bytes.copy_from_slice(proof_bytes);
        let signature = Signature::from_bytes(&sig_bytes);

        let verifying_key = VerifyingKey::from_bytes(&self.owner_pubkey).map_err(|_| {
            WitnessedPredicateError::Rejected {
                kind_name: "owner-envelope-sig",
                reason: "gated owner public key is not a valid ed25519 point".into(),
            }
        })?;

        verifying_key
            .verify_strict(message, &signature)
            .map_err(|_| WitnessedPredicateError::Rejected {
                kind_name: "owner-envelope-sig",
                reason: "owner ed25519 signature over the turn's custom signing message did not \
                         verify (the actor does not hold the owner key)"
                    .into(),
            })
    }
}

/// Install an [`OwnerEnvelopeSigVerifier`] for `owner_pubkey` into `registry`,
/// returning the `Custom` vk_hash it was registered under (the value a caller
/// stamps into the worker cell's `set_permissions`/`delegate`/
/// `set_verification_key` slots via `dregg_cell::Permissions::enveloped_worker`).
/// Call this when building the executor that will admit the worker's turns (the
/// per-grain registration seam), after building the base production registry.
pub fn register_owner_envelope_verifier(
    registry: &mut WitnessedPredicateRegistry,
    owner_pubkey: [u8; 32],
) -> [u8; 32] {
    let verifier = OwnerEnvelopeSigVerifier::new(owner_pubkey);
    let vk_hash = verifier.vk_hash();
    registry.register_custom(vk_hash, Arc::new(verifier));
    vk_hash
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::predicate::WitnessedPredicate;
    use ed25519_dalek::{Signer, SigningKey};

    fn signing_key(seed: u8) -> SigningKey {
        SigningKey::from_bytes(&[seed; 32])
    }

    #[test]
    fn accepts_owner_signature_over_the_message() {
        let owner = signing_key(7);
        let owner_pk = owner.verifying_key().to_bytes();
        let v = OwnerEnvelopeSigVerifier::new(owner_pk);
        let msg = b"canonical-custom-signing-message-bytes";
        let sig = owner.sign(msg).to_bytes();
        let input = PredicateInput::SigningMessage(msg);
        assert!(v.verify(&owner_pk, &input, &sig).is_ok());
    }

    #[test]
    fn rejects_a_non_owner_signature() {
        // The "host" holds a DIFFERENT key and cannot forge the owner's signature.
        let owner = signing_key(7);
        let host = signing_key(9);
        let owner_pk = owner.verifying_key().to_bytes();
        let v = OwnerEnvelopeSigVerifier::new(owner_pk);
        let msg = b"canonical-custom-signing-message-bytes";
        let host_sig = host.sign(msg).to_bytes();
        let input = PredicateInput::SigningMessage(msg);
        assert!(v.verify(&owner_pk, &input, &host_sig).is_err());
    }

    #[test]
    fn rejects_owner_signature_over_a_different_message() {
        let owner = signing_key(7);
        let owner_pk = owner.verifying_key().to_bytes();
        let v = OwnerEnvelopeSigVerifier::new(owner_pk);
        let sig = owner.sign(b"a-benign-action").to_bytes();
        let input = PredicateInput::SigningMessage(b"a-widening-delegate-action");
        assert!(v.verify(&owner_pk, &input, &sig).is_err());
    }

    #[test]
    fn rejects_mismatched_commitment() {
        let owner = signing_key(7);
        let owner_pk = owner.verifying_key().to_bytes();
        let v = OwnerEnvelopeSigVerifier::new(owner_pk);
        let msg = b"m";
        let sig = owner.sign(msg).to_bytes();
        let input = PredicateInput::SigningMessage(msg);
        let wrong_commitment = [0u8; 32];
        assert!(v.verify(&wrong_commitment, &input, &sig).is_err());
    }

    #[test]
    fn vk_hash_is_owner_specific_and_stable() {
        let a = owner_envelope_vk(&[1u8; 32]);
        let b = owner_envelope_vk(&[2u8; 32]);
        assert_ne!(a, b);
        assert_eq!(a, owner_envelope_vk(&[1u8; 32]));
    }

    #[test]
    fn register_wires_the_verifier_under_its_vk() {
        let mut reg = WitnessedPredicateRegistry::default_builtins();
        let owner_pk = signing_key(7).verifying_key().to_bytes();
        let vk = register_owner_envelope_verifier(&mut reg, owner_pk);
        assert!(
            reg.get(WitnessedPredicateKind::Custom { vk_hash: vk })
                .is_some()
        );
        let _ = WitnessedPredicate {
            kind: WitnessedPredicateKind::Custom { vk_hash: vk },
            commitment: owner_pk,
            input_ref: dregg_cell::predicate::InputRef::SigningMessage,
            proof_witness_index: 0,
        };
    }

    // WAVE A / WELD — OWNER LIVENESS: building an executor via the
    // `with_owner_envelope` seam actually REGISTERS the verifier, so an
    // owner-signed Custom auth over the canonical message RESOLVES + verifies
    // through the executor's own registry (a bare executor would MISS it ->
    // AuthModeNotRegistered), and a wrong (host) key is rejected.
    #[test]
    fn with_owner_envelope_registers_verifier_on_the_executor() {
        use crate::executor::{ComputronCosts, TurnExecutor};
        use dregg_cell::predicate::{InputRef, WitnessedPredicate};

        let owner = signing_key(7);
        let owner_pk = owner.verifying_key().to_bytes();

        // Build the executor through the liveness seam.
        let exec = TurnExecutor::new(ComputronCosts::default_costs()).with_owner_envelope(owner_pk);
        let registry = exec
            .witnessed_registry
            .as_ref()
            .expect("with_owner_envelope leaves the witnessed registry populated");

        // The owner-envelope Custom kind now RESOLVES on this executor's registry.
        let vk = owner_envelope_vk(&owner_pk);
        assert!(
            registry
                .get(WitnessedPredicateKind::Custom { vk_hash: vk })
                .is_some(),
            "with_owner_envelope must register the OwnerEnvelopeSigVerifier under its vk_hash"
        );

        let wp = WitnessedPredicate {
            kind: WitnessedPredicateKind::Custom { vk_hash: vk },
            commitment: owner_pk,
            input_ref: InputRef::SigningMessage,
            proof_witness_index: 0,
        };
        let msg = b"canonical-custom-signing-message-bytes";

        // Owner-signed over the canonical message -> ACCEPTED (liveness).
        let owner_sig = owner.sign(msg).to_bytes();
        assert!(
            registry
                .verify(&wp, &PredicateInput::SigningMessage(msg), &owner_sig)
                .is_ok(),
            "a valid owner signature over the canonical message must verify through the seam-built executor's registry"
        );

        // A wrong (host) key -> REJECTED (the host cannot forge the owner sig).
        let host = signing_key(9);
        let host_sig = host.sign(msg).to_bytes();
        assert!(
            registry
                .verify(&wp, &PredicateInput::SigningMessage(msg), &host_sig)
                .is_err(),
            "a non-owner signature must be rejected"
        );
    }
}
