//! Distributed Intent Engine for Pyana.
//!
//! The intent engine inverts the capability discovery model. Instead of pages/services
//! needing to know exactly what capability to request, they broadcast what they NEED
//! or OFFER, and wallets privately match against held capabilities.
//!
//! # Architecture
//!
//! ```text
//! Page/Service                    Gossip Network                  Wallet
//!     |                                |                            |
//!     |--- postIntent(MatchSpec) ----->|--- broadcast(Intent) ----->|
//!     |                                |                            | (local Datalog eval)
//!     |                                |                            | match_intent()
//!     |                                |                            |
//!     |<---- fulfillment (direct) -----|<--- fulfill(Match) --------|
//!     |                                |                            |
//! ```
//!
//! # Privacy model
//!
//! - **Intents are public**: Everyone sees "someone needs capability X for resource Y".
//!   The creator is anonymous (identified only by a commitment, not an identity).
//! - **Matching is private**: The wallet evaluates "can I satisfy this?" using local
//!   Datalog evaluation, without revealing what it holds.
//! - **Fulfillment is private**: The proof reveals only "yes I can satisfy this intent"
//!   -- not what token, what delegation chain, or what else you hold.
//!
//! This IS the progressive disclosure story applied to discovery.

pub mod fulfillment;
pub mod gossip;
pub mod matcher;

use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// A commitment to an anonymous creator identity.
/// This is NOT a public key -- it's a blinded commitment that can only be
/// opened by the creator. Two intents from the same creator have different
/// CommitmentIds unless they choose to link them.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct CommitmentId(pub [u8; 32]);

impl CommitmentId {
    /// Generate a fresh random commitment ID.
    pub fn random() -> Self {
        let mut bytes = [0u8; 32];
        getrandom(&mut bytes);
        Self(bytes)
    }

    /// Derive a commitment from a secret and a domain separator.
    pub fn derive(secret: &[u8], domain: &str) -> Self {
        let hash = blake3::derive_key(domain, secret);
        Self(hash)
    }
}

/// Verification mode for match proofs -- how much to reveal.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum VerificationMode {
    /// Trusted: no proof, direct token presentation (fastest, least private).
    Trusted,
    /// Selective: prove specific facts about the token without revealing all.
    Selective,
    /// Private: full STARK proof that a valid token exists satisfying the intent.
    /// Reveals nothing about which token or what delegation chain.
    Private,
}

/// The kind of intent being broadcast.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum IntentKind {
    /// "I need a capability matching this spec" -- requesting authorization.
    Need,
    /// "I can provide a capability matching this spec" -- offering authorization.
    Offer,
    /// "Tell me if any matching capability exists" -- discovery query.
    Query,
}

/// A pattern matching a single action on a resource.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ActionPattern {
    /// The action required/offered. None = wildcard (any action).
    pub action: Option<String>,
    /// The resource the action applies to. None = any resource.
    pub resource: Option<String>,
}

/// A constraint on matching, expressed in Datalog-compatible terms.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Constraint {
    /// The token must grant access to this specific app.
    AppId(String),
    /// The token must grant access to this specific service.
    Service(String),
    /// The token must be valid for this user.
    UserId(String),
    /// The token must not be expired at this timestamp.
    NotExpiredAt(i64),
    /// The token must grant this feature.
    Feature(String),
    /// The token must have been issued by this OAuth provider.
    OAuthProvider(String),
    /// Custom predicate (for extensibility).
    Custom { predicate: String, value: String },
}

/// Specification of what capabilities are needed or offered.
///
/// This is the core matching language: a MatchSpec describes a "shape" of
/// capability that can be matched against held tokens.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MatchSpec {
    /// What actions are required/offered.
    pub actions: Vec<ActionPattern>,
    /// Datalog-style constraints that must be satisfied.
    pub constraints: Vec<Constraint>,
    /// Minimum budget required (if the intent involves budgeted resources).
    pub min_budget: Option<u64>,
    /// Glob or prefix pattern for resource matching.
    pub resource_pattern: Option<String>,
}

/// A broadcast intent: someone needs/offers/queries a capability.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Intent {
    /// Content-addressed ID: BLAKE3 hash of the serialized intent body.
    pub id: [u8; 32],
    /// What kind of intent this is.
    pub kind: IntentKind,
    /// What capabilities are needed/offered.
    pub matcher: MatchSpec,
    /// Anonymous creator commitment (not a public identity).
    pub creator: CommitmentId,
    /// Unix timestamp after which this intent expires and should be GC'd.
    pub expiry: u64,
    /// Optional stake proving seriousness (a note commitment).
    pub proof_of_stake: Option<pyana_cell::NoteCommitment>,
}

impl Intent {
    /// Create a new intent, computing its content-addressed ID.
    pub fn new(
        kind: IntentKind,
        matcher: MatchSpec,
        creator: CommitmentId,
        expiry: u64,
        proof_of_stake: Option<pyana_cell::NoteCommitment>,
    ) -> Self {
        let mut intent = Self {
            id: [0u8; 32],
            kind,
            matcher,
            creator,
            expiry,
            proof_of_stake,
        };
        intent.id = intent.compute_id();
        intent
    }

    /// Compute the content-addressed ID from the intent's fields.
    fn compute_id(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("pyana-intent-id-v1");
        // Hash kind
        hasher.update(&[self.kind as u8]);
        // Hash matcher (deterministic serialization via rmp would be better,
        // but for now we hash the debug repr -- the real implementation would
        // use a canonical encoding)
        hasher.update(format!("{:?}", self.matcher).as_bytes());
        // Hash creator
        hasher.update(&self.creator.0);
        // Hash expiry
        hasher.update(&self.expiry.to_le_bytes());
        // Hash stake if present
        if let Some(stake) = &self.proof_of_stake {
            hasher.update(&stake.0);
        }
        *hasher.finalize().as_bytes()
    }

    /// Check if this intent has expired.
    pub fn is_expired(&self, now: u64) -> bool {
        now > self.expiry
    }
}

/// A successful match: a held token can satisfy an intent.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Match {
    /// The intent that was matched.
    pub intent_id: [u8; 32],
    /// Anonymous commitment of the satisfier.
    pub satisfier: CommitmentId,
    /// Optional STARK proof that the match is valid.
    pub proof: Option<Vec<u8>>,
    /// How much was revealed in the proof.
    pub mode: VerificationMode,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Fill a buffer with random bytes (no-std compatible via getrandom).
fn getrandom(buf: &mut [u8]) {
    ::getrandom::fill(buf).expect("getrandom failed");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn intent_id_is_deterministic() {
        let spec = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: Some("documents/*".into()),
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
        };
        let creator = CommitmentId([0xAA; 32]);
        let i1 = Intent::new(IntentKind::Need, spec.clone(), creator, 1000, None);
        let i2 = Intent::new(IntentKind::Need, spec, creator, 1000, None);
        assert_eq!(i1.id, i2.id);
    }

    #[test]
    fn different_intents_have_different_ids() {
        let spec1 = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("read".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
        };
        let spec2 = MatchSpec {
            actions: vec![ActionPattern {
                action: Some("write".into()),
                resource: None,
            }],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
        };
        let creator = CommitmentId([0xBB; 32]);
        let i1 = Intent::new(IntentKind::Need, spec1, creator, 1000, None);
        let i2 = Intent::new(IntentKind::Need, spec2, creator, 1000, None);
        assert_ne!(i1.id, i2.id);
    }

    #[test]
    fn intent_expiry_check() {
        let spec = MatchSpec {
            actions: vec![],
            constraints: vec![],
            min_budget: None,
            resource_pattern: None,
        };
        let creator = CommitmentId([0xCC; 32]);
        let intent = Intent::new(IntentKind::Need, spec, creator, 1000, None);
        assert!(!intent.is_expired(500));
        assert!(!intent.is_expired(1000));
        assert!(intent.is_expired(1001));
    }

    #[test]
    fn commitment_id_derive_is_deterministic() {
        let c1 = CommitmentId::derive(b"secret", "test-domain");
        let c2 = CommitmentId::derive(b"secret", "test-domain");
        assert_eq!(c1, c2);

        let c3 = CommitmentId::derive(b"other", "test-domain");
        assert_ne!(c1, c3);
    }
}
