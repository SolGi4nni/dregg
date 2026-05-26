//! Authority key management and token minting.
//!
//! Each "silo" (organization) has its own authority keypair. The authority
//! signs tokens it mints, and those signatures are verifiable by anyone
//! who knows the authority's public key.
//!
//! Uses Ed25519 signatures for real asymmetric public-key verification.
//! Verification requires only the public key -- no secret key material.
//!
//! Cryptographic primitives (`PublicKey`, `SigningKey`, `hex_encode`) are
//! re-exported from the canonical `dregg-types` crate.

use crate::token::{Fact, Rule, TokenState};

// Re-export canonical types from dregg-types.
pub use dregg_types::{PublicKey, SigningKey, hex_encode};

/// An authority represents one organization's signing identity.
pub struct Authority {
    /// Human-readable name for the authority (e.g., "acme.corp").
    pub name: String,
    /// The private signing key (Ed25519).
    signing_key: SigningKey,
    /// The public key (Ed25519 verifying key).
    pub public_key: PublicKey,
}

impl Authority {
    /// Create a new authority with a random Ed25519 keypair.
    pub fn new(name: &str) -> Self {
        let (signing_key, public_key) = dregg_types::generate_keypair();

        Authority {
            name: name.to_string(),
            signing_key,
            public_key,
        }
    }

    /// Mint a new root token with the given facts and rules.
    ///
    /// The token is signed by this authority and includes:
    /// - A unique token ID
    /// - The authority's public key as issuer
    /// - The provided facts (capabilities)
    /// - The provided rules (authorization policies)
    /// - A state root commitment (BLAKE3 hash of the serialized state)
    pub fn mint_token(&self, facts: Vec<Fact>, rules: Vec<Rule>) -> TokenState {
        // Generate a unique token ID.
        let mut id_bytes = [0u8; 16];
        getrandom::fill(&mut id_bytes).expect("getrandom failed");
        let token_id = hex_encode(&id_bytes[..8]);

        // Build the token state.
        let mut token = TokenState {
            id: token_id,
            issuer: self.public_key.clone(),
            facts,
            rules,
            checks: Vec::new(),
            state_root: [0u8; 32],
            signature: [0u8; 64],
            derivation_trace: Vec::new(),
            revoked: false,
        };

        // Compute state root as BLAKE3 hash of the token's content.
        token.state_root = token.compute_state_root();

        // Sign the state root with Ed25519.
        token.signature = self.sign(&token.state_root);

        // Record the minting as the first derivation step.
        token.derivation_trace.push(crate::trace::DerivationStep {
            authority: self.public_key.clone(),
            input_root: [0u8; 32], // No input for minting.
            output_root: token.state_root,
            signature: token.signature,
        });

        token
    }

    /// Sign a message using the authority's Ed25519 signing key.
    /// Returns a 64-byte Ed25519 signature.
    pub fn sign(&self, message: &[u8; 32]) -> [u8; 64] {
        let sig = dregg_types::sign(&self.signing_key, message);
        sig.0
    }

    /// Sign an arbitrary-length message using the authority's Ed25519 signing key.
    /// Returns a 64-byte Ed25519 signature.
    pub fn sign_bytes(&self, message: &[u8]) -> [u8; 64] {
        let sig = dregg_types::sign(&self.signing_key, message);
        sig.0
    }

    /// Verify a signature against this authority's public key.
    /// Uses Ed25519 public-key verification -- no secret key needed.
    pub fn verify_signature(&self, message: &[u8; 32], signature: &[u8; 64]) -> bool {
        self.public_key
            .verify(message, &dregg_types::Signature(*signature))
    }
}

/// A signature verification context that only holds the public key.
/// Uses Ed25519 verification -- only the public key is needed.
#[derive(Clone)]
pub struct VerificationKey {
    /// The public key for display/identity purposes.
    pub public_key: PublicKey,
}

impl VerificationKey {
    /// Create a verification key from an authority (extracts public key only).
    pub fn from_authority(authority: &Authority) -> Self {
        VerificationKey {
            public_key: authority.public_key.clone(),
        }
    }

    /// Verify that a signature over `message` was produced by this key's authority.
    /// Only requires the public key -- true asymmetric verification.
    pub fn verify(&self, message: &[u8; 32], signature: &[u8; 64]) -> bool {
        self.public_key
            .verify(message, &dregg_types::Signature(*signature))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_authority_creation() {
        let auth = Authority::new("test.org");
        assert_eq!(auth.name, "test.org");
        assert_ne!(auth.public_key.0, [0u8; 32]);
    }

    #[test]
    fn test_sign_verify() {
        let auth = Authority::new("test.org");
        let message = blake3::hash(b"hello world");
        let sig = auth.sign(message.as_bytes());
        assert!(auth.verify_signature(message.as_bytes(), &sig));
    }

    #[test]
    fn test_verification_key() {
        let auth = Authority::new("test.org");
        let vk = VerificationKey::from_authority(&auth);
        let message = blake3::hash(b"test message");
        let sig = auth.sign(message.as_bytes());
        assert!(vk.verify(message.as_bytes(), &sig));
    }

    #[test]
    fn test_verification_key_wrong_message() {
        let auth = Authority::new("test.org");
        let vk = VerificationKey::from_authority(&auth);
        let message = blake3::hash(b"test message");
        let wrong_message = blake3::hash(b"wrong message");
        let sig = auth.sign(message.as_bytes());
        // Verification with wrong message should fail.
        assert!(!vk.verify(wrong_message.as_bytes(), &sig));
    }

    #[test]
    fn test_verification_key_wrong_key() {
        let auth1 = Authority::new("test.org");
        let auth2 = Authority::new("other.org");
        let vk2 = VerificationKey::from_authority(&auth2);
        let message = blake3::hash(b"test message");
        let sig = auth1.sign(message.as_bytes());
        // Verification with wrong key should fail.
        assert!(!vk2.verify(message.as_bytes(), &sig));
    }

    #[test]
    fn test_mint_token() {
        let auth = Authority::new("acme.corp");
        let facts = vec![Fact::app("frontend", "rwcd"), Fact::service("http", "rw")];
        let rules = vec![Rule::allow_app(), Rule::deny_default()];
        let token = auth.mint_token(facts, rules);

        assert_eq!(token.issuer, auth.public_key);
        assert_eq!(token.facts.len(), 2);
        assert_eq!(token.rules.len(), 2);
        assert_ne!(token.state_root, [0u8; 32]);
        assert_ne!(token.signature, [0u8; 64]);
        assert_eq!(token.derivation_trace.len(), 1);

        // Verify the signature with only the public key.
        assert!(
            auth.public_key
                .verify(&token.state_root, &dregg_types::Signature(token.signature))
        );
    }
}
