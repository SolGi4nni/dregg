//! Canonical signed-turn transport envelope.
//!
//! `Turn` owns the message and its hash; this leaf owns the byte-exact outer
//! Ed25519/PQ wire which every ingress decodes.  Signing-key custody and
//! envelope construction remain SDK responsibilities.  Keeping the wire beside
//! `Turn` lets lower finality and persistence crates decode it without taking a
//! dependency on the much larger SDK.

use dregg_types::{PublicKey, Signature};
use serde::{Deserialize, Serialize};

use crate::turn::Turn;

/// A turn signed by one agent identity, ready for submission.
///
/// Field order is the deployed postcard order.  Append-only compatibility is
/// intentional: the PQ vectors trail the original classical envelope and
/// retain their serde defaults for legacy decoders.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SignedTurn {
    /// The original turn.
    pub turn: Turn,
    /// The Ed25519 signature over [`Turn::hash`].
    pub signature: Signature,
    /// The signer's Ed25519 public key.
    pub signer: PublicKey,
    /// ML-DSA-65 signature over the same [`Turn::hash`].  Empty means the
    /// legacy classical-only envelope; admission policy decides whether that is
    /// permitted, never this transport type.
    #[serde(default)]
    pub pq_signature: Vec<u8>,
    /// Serialized ML-DSA-65 public key paired with `pq_signature`.  Empty means
    /// the legacy classical-only envelope.
    #[serde(default)]
    pub pq_signer: Vec<u8>,
}
