//! Caveat types, trait, and caveat set.
//!
//! Caveats are the authorization predicates chained into a macaroon. Each caveat
//! can only restrict access — adding caveats can never expand what a token allows.
//!
//! Caveat type ID ranges:
//! - 0..31:  Reserved for Dregg platform caveats
//! - 32..47: User-registerable (registered at runtime)
//! - 48+:    User-defined (no registration required)
//! - 254:    Third-party caveat
//! - 255:    BindToParentToken

use serde::{Deserialize, Serialize};

use crate::access::Access;
use crate::error::CaveatError;

/// Numeric identifier for a caveat type.
///
/// The type ID is encoded as the first field when serializing a caveat,
/// allowing the deserializer to dispatch to the correct implementation.
pub type CaveatType = u16;

// --- Reserved caveat type IDs ---

/// Minimum ID for Dregg platform caveats.
pub const CAV_PLATFORM_MIN: CaveatType = 0;
/// Maximum ID for Dregg platform caveats.
pub const CAV_PLATFORM_MAX: CaveatType = 31;

/// Minimum ID for user-registerable caveats.
pub const CAV_USER_REG_MIN: CaveatType = 32;
/// Maximum ID for user-registerable caveats.
pub const CAV_USER_REG_MAX: CaveatType = 47;

/// Minimum ID for user-defined caveats (no registration).
pub const CAV_USER_MIN: CaveatType = 48;
/// Maximum ID for user-defined caveats.
pub const CAV_USER_MAX: CaveatType = 253;

/// Third-party caveat type ID.
pub const CAV_THIRD_PARTY: CaveatType = 254;

/// BindToParentToken caveat type ID.
pub const CAV_BIND_TO_PARENT: CaveatType = 255;

/// A first-party caveat — checked directly against the access request.
///
/// Implementations must be deterministic and side-effect free.
pub trait Caveat: Send + Sync {
    /// The numeric type ID for this caveat.
    fn caveat_type(&self) -> CaveatType;

    /// Human-readable name for debugging/logging.
    fn name(&self) -> &str;

    /// Check whether this caveat prohibits the given access.
    ///
    /// Returns `Ok(())` if the access is allowed, or `Err(CaveatError)` if denied.
    fn prohibits(&self, access: &dyn Access) -> Result<(), CaveatError>;

    /// Serialize this caveat's body to bytes (MsgPack).
    ///
    /// The type ID is NOT included — it's prepended by the caller.
    fn encode_body(&self) -> Vec<u8>;
}

/// Wire representation of a caveat: `[type_id: u16][body: bytes]`.
///
/// This is what gets serialized into the macaroon and HMAC-chained.
/// The body is opaque — interpretation depends on the type_id.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WireCaveat {
    /// Caveat type identifier.
    pub caveat_type: CaveatType,
    /// Serialized caveat body.
    pub body: Vec<u8>,
}

impl WireCaveat {
    /// Create a new wire caveat from a type ID and body bytes.
    pub fn new(caveat_type: CaveatType, body: Vec<u8>) -> Self {
        Self { caveat_type, body }
    }

    /// Create from a `Caveat` trait object.
    pub fn from_caveat(caveat: &dyn Caveat) -> Self {
        Self {
            caveat_type: caveat.caveat_type(),
            body: caveat.encode_body(),
        }
    }

    /// Encode to bytes for HMAC chaining: `[type_id LE u16][body]`.
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(2 + self.body.len());
        out.extend_from_slice(&self.caveat_type.to_le_bytes());
        out.extend_from_slice(&self.body);
        out
    }
}

/// An ordered set of caveats.
///
/// During verification, all caveats in the set must be satisfied (AND semantics).
/// The order is significant for HMAC chain replay.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CaveatSet {
    caveats: Vec<WireCaveat>,
}

impl CaveatSet {
    /// Create an empty caveat set.
    pub fn new() -> Self {
        Self {
            caveats: Vec::new(),
        }
    }

    /// Add a wire caveat to the set.
    pub fn push(&mut self, caveat: WireCaveat) {
        self.caveats.push(caveat);
    }

    /// Add a caveat from a trait object.
    pub fn push_caveat(&mut self, caveat: &dyn Caveat) {
        self.caveats.push(WireCaveat::from_caveat(caveat));
    }

    /// Number of caveats.
    pub fn len(&self) -> usize {
        self.caveats.len()
    }

    /// Whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.caveats.is_empty()
    }

    /// Iterate over wire caveats.
    pub fn iter(&self) -> impl Iterator<Item = &WireCaveat> {
        self.caveats.iter()
    }

    /// Get a reference to the underlying vec.
    pub fn as_slice(&self) -> &[WireCaveat] {
        &self.caveats
    }

    /// Consume and return the inner vec.
    pub fn into_vec(self) -> Vec<WireCaveat> {
        self.caveats
    }

    /// Extend with caveats from another set.
    pub fn extend(&mut self, other: CaveatSet) {
        self.caveats.extend(other.caveats);
    }

    /// Check if any caveat is a third-party caveat.
    pub fn has_third_party(&self) -> bool {
        self.caveats
            .iter()
            .any(|c| c.caveat_type == CAV_THIRD_PARTY)
    }

    /// Get all third-party caveats.
    pub fn third_party_caveats(&self) -> Vec<&WireCaveat> {
        self.caveats
            .iter()
            .filter(|c| c.caveat_type == CAV_THIRD_PARTY)
            .collect()
    }

    /// Get all first-party caveats (non-3P, non-bind).
    pub fn first_party_caveats(&self) -> Vec<&WireCaveat> {
        self.caveats
            .iter()
            .filter(|c| c.caveat_type != CAV_THIRD_PARTY && c.caveat_type != CAV_BIND_TO_PARENT)
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wire_caveat_encode() {
        let wc = WireCaveat::new(1, vec![0x42, 0x43]);
        let encoded = wc.encode();
        assert_eq!(encoded, vec![0x01, 0x00, 0x42, 0x43]);
    }

    #[test]
    fn test_caveat_set_operations() {
        let mut set = CaveatSet::new();
        assert!(set.is_empty());

        set.push(WireCaveat::new(1, vec![0x01]));
        set.push(WireCaveat::new(CAV_THIRD_PARTY, vec![0x02]));
        set.push(WireCaveat::new(2, vec![0x03]));

        assert_eq!(set.len(), 3);
        assert!(set.has_third_party());
        assert_eq!(set.third_party_caveats().len(), 1);
        assert_eq!(set.first_party_caveats().len(), 2);
    }
}
