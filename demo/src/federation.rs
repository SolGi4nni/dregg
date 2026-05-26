//! Federation registry and issuer membership.
//!
//! A federation is a set of authorities that trust each other for cross-silo
//! authorization. The federation root is a BLAKE3 commitment to the set of
//! all member authorities' public keys.
//!
//! When a token crosses silo boundaries, the verifying silo checks that
//! the token's issuer is a member of the shared federation. This requires
//! only the federation root and the member list — no real-time communication
//! with the issuing silo.
//!
//! NOTE: This module is standalone for membership tracking and role-based access.
//! The real `dregg_federation` crate provides attested roots with quorum
//! certificates and Merkle-based revocation (live BFT consensus itself lives
//! in `dregg_blocklace`); those features are exercised via `revocation.rs`
//! (RevocationTree) and `main.rs` (STARK proof of issuer membership).
//!
//! // TODO: integrate with real dregg_federation::node::Federation for full consensus-
//! // based membership attestation (AttestedRoot with quorum signatures over the
//! // member set). Currently membership is checked via a simple HashMap lookup.

use std::collections::HashMap;

use crate::authority::{PublicKey, VerificationKey, hex_encode};

// =============================================================================
// Federation
// =============================================================================

/// A federation of trusted authorities.
///
/// The federation maintains:
/// - A registry of member authorities (public keys + verification keys)
/// - A merkle-like root commitment to the member set
/// - Metadata about each member (name, capabilities)
pub struct Federation {
    /// Human-readable name for this federation.
    pub name: String,
    /// The federation root: BLAKE3 hash of all member public keys.
    pub root: [u8; 32],
    /// Member authorities indexed by public key.
    members: HashMap<PublicKeyWrapper, FederationMember>,
    /// Ordered list of member public keys (for deterministic root computation).
    member_order: Vec<PublicKey>,
}

/// A member of the federation.
#[derive(Clone)]
pub struct FederationMember {
    /// Verification key for checking signatures.
    pub verification_key: VerificationKey,
    /// What roles this member plays in the federation.
    pub roles: Vec<FederationRole>,
}

/// Roles a member can have in the federation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FederationRole {
    /// Can issue tokens that other members will accept.
    Issuer,
    /// Can verify tokens from other members.
    Verifier,
    /// Can revoke tokens (has revocation authority).
    Revoker,
}

/// Wrapper for PublicKey that implements Hash+Eq for use as HashMap key.
#[derive(Clone, PartialEq, Eq)]
struct PublicKeyWrapper(PublicKey);

impl std::hash::Hash for PublicKeyWrapper {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.as_bytes().hash(state);
    }
}

impl Federation {
    /// Create a new empty federation.
    pub fn new(name: &str) -> Self {
        Federation {
            name: name.to_string(),
            root: [0u8; 32],
            members: HashMap::new(),
            member_order: Vec::new(),
        }
    }

    /// Add a member to the federation.
    ///
    /// After adding all members, call `compute_root()` to update the
    /// federation root commitment.
    pub fn add_member(
        &mut self,
        _name: &str,
        authority: &crate::authority::Authority,
        roles: Vec<FederationRole>,
    ) {
        let vk = VerificationKey::from_authority(authority);
        let member = FederationMember {
            verification_key: vk,
            roles,
        };
        let key = PublicKeyWrapper(authority.public_key.clone());
        self.members.insert(key, member);
        self.member_order.push(authority.public_key.clone());
    }

    /// Compute the federation root from the current member set.
    ///
    /// The root is a BLAKE3 hash of all member public keys in insertion order.
    /// This serves as a compact commitment to the federation membership.
    pub fn compute_root(&mut self) {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"dregg-federation-v1");
        hasher.update(&[0xff]);
        hasher.update(self.name.as_bytes());
        hasher.update(&[0xfe]);

        for pk in &self.member_order {
            hasher.update(pk.as_bytes());
            hasher.update(&[0xfd]);
        }

        self.root = *hasher.finalize().as_bytes();
    }

    /// Get the federation root as a short hex string.
    pub fn root_hex(&self) -> String {
        hex_encode(&self.root[..4])
    }

    /// Check if a public key is a member of this federation.
    pub fn is_member(&self, public_key: &PublicKey) -> bool {
        let key = PublicKeyWrapper(public_key.clone());
        self.members.contains_key(&key)
    }

    /// Check if a public key has a specific role in the federation.
    pub fn has_role(&self, public_key: &PublicKey, role: &FederationRole) -> bool {
        let key = PublicKeyWrapper(public_key.clone());
        self.members
            .get(&key)
            .is_some_and(|m| m.roles.contains(role))
    }

    /// Get the verification key for a member.
    pub fn get_verification_key(&self, public_key: &PublicKey) -> Option<&VerificationKey> {
        let key = PublicKeyWrapper(public_key.clone());
        self.members.get(&key).map(|m| &m.verification_key)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::authority::Authority;

    #[test]
    fn test_federation_creation() {
        let mut fed = Federation::new("test-federation");
        let auth1 = Authority::new("org1");
        let auth2 = Authority::new("org2");

        fed.add_member(
            "org1",
            &auth1,
            vec![FederationRole::Issuer, FederationRole::Verifier],
        );
        fed.add_member("org2", &auth2, vec![FederationRole::Verifier]);
        fed.compute_root();

        assert!(fed.is_member(&auth1.public_key));
        assert!(fed.is_member(&auth2.public_key));
        assert_ne!(fed.root, [0u8; 32]);
    }

    #[test]
    fn test_federation_roles() {
        let mut fed = Federation::new("test");
        let auth = Authority::new("org1");
        fed.add_member(
            "org1",
            &auth,
            vec![FederationRole::Issuer, FederationRole::Revoker],
        );

        assert!(fed.has_role(&auth.public_key, &FederationRole::Issuer));
        assert!(fed.has_role(&auth.public_key, &FederationRole::Revoker));
        assert!(!fed.has_role(&auth.public_key, &FederationRole::Verifier));
    }
}
