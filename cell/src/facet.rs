//! Faceted capabilities: E-language restricted object views.
//!
//! In E, a facet is a restricted view of an object that only exposes a subset
//! of the object's interface. In pyana, this is implemented as a bitmask on a
//! capability: when exercising a capability via `ExerciseViaCapability`, the
//! executor checks that every inner effect's kind is permitted by the
//! capability's facet mask.
//!
//! # Design
//!
//! Each effect type maps to a single bit in the mask. A capability with
//! `allowed_effects = Some(mask)` restricts the holder to only those effect
//! types whose bit is set. `None` or `Some(EFFECT_ALL)` means unrestricted.
//!
//! Facets compose with attenuation: when delegating a faceted capability, the
//! child's mask must be a subset (bitwise) of the parent's mask. This enforces
//! the E invariant that authority can only be narrowed, never amplified.
//!
//! # Predefined Facets
//!
//! - `FACET_READ_ONLY`: Only emit events (observation without mutation)
//! - `FACET_TRANSFER_ONLY`: Only send value from the target cell
//! - `FACET_STATE_WRITER`: Set fields + emit events
//! - `FACET_ADMIN`: Permission and key management only

use serde::{Deserialize, Serialize};

/// Bitmask identifying which effect types a faceted capability permits.
pub type EffectMask = u32;

// ─── Effect kind bits ────────────────────────────────────────────────────────
// Each bit corresponds to a category of effects that can be independently permitted.

pub const EFFECT_SET_FIELD: EffectMask = 1 << 0;
pub const EFFECT_TRANSFER: EffectMask = 1 << 1;
pub const EFFECT_GRANT_CAPABILITY: EffectMask = 1 << 2;
pub const EFFECT_REVOKE_CAPABILITY: EffectMask = 1 << 3;
pub const EFFECT_EMIT_EVENT: EffectMask = 1 << 4;
pub const EFFECT_INCREMENT_NONCE: EffectMask = 1 << 5;
pub const EFFECT_CREATE_CELL: EffectMask = 1 << 6;
pub const EFFECT_SET_PERMISSIONS: EffectMask = 1 << 7;
pub const EFFECT_SET_VERIFICATION_KEY: EffectMask = 1 << 8;
pub const EFFECT_NOTE_SPEND: EffectMask = 1 << 9;
pub const EFFECT_NOTE_CREATE: EffectMask = 1 << 10;
pub const EFFECT_SEAL_OPS: EffectMask = 1 << 11;
pub const EFFECT_BRIDGE_OPS: EffectMask = 1 << 12;
pub const EFFECT_INTRODUCE: EffectMask = 1 << 13;
pub const EFFECT_OBLIGATION_OPS: EffectMask = 1 << 14;
pub const EFFECT_ESCROW_OPS: EffectMask = 1 << 15;
pub const EFFECT_DELEGATION_OPS: EffectMask = 1 << 16;
pub const EFFECT_SOVEREIGN_OPS: EffectMask = 1 << 17;

/// All effect kinds permitted (equivalent to no restriction).
pub const EFFECT_ALL: EffectMask = 0xFFFF_FFFF;

// ─── Predefined facet masks ─────────────────────────────────────────────────

/// Read-only facet: only allows emitting events (observation without mutation).
pub const FACET_READ_ONLY: EffectMask = EFFECT_EMIT_EVENT;

/// Transfer-only facet: only allows sending value from the target cell.
pub const FACET_TRANSFER_ONLY: EffectMask = EFFECT_TRANSFER;

/// State-writer facet: allows setting fields and emitting events.
pub const FACET_STATE_WRITER: EffectMask = EFFECT_SET_FIELD | EFFECT_EMIT_EVENT;

/// Admin facet: allows permission and key management.
pub const FACET_ADMIN: EffectMask = EFFECT_SET_PERMISSIONS | EFFECT_SET_VERIFICATION_KEY;

/// Full delegation facet: grant/revoke capabilities + introduce.
pub const FACET_DELEGATOR: EffectMask =
    EFFECT_GRANT_CAPABILITY | EFFECT_REVOKE_CAPABILITY | EFFECT_INTRODUCE;

// ─── Facet validation ───────────────────────────────────────────────────────

/// Check whether `child_mask` is a valid attenuation of `parent_mask`.
///
/// Returns true if the child mask is a subset of the parent mask (no bits
/// enabled that the parent doesn't have). This enforces the E invariant:
/// facets can only restrict, never amplify.
pub fn is_facet_attenuation(parent_mask: EffectMask, child_mask: EffectMask) -> bool {
    child_mask & parent_mask == child_mask
}

/// Check whether a specific effect kind bit is permitted by a mask.
///
/// If `mask` is `None` or `EFFECT_ALL`, all effects are permitted.
pub fn is_effect_permitted(mask: Option<EffectMask>, effect_bit: EffectMask) -> bool {
    match mask {
        None => true,
        Some(0) => true, // zero mask = unrestricted (backward compat)
        Some(m) => effect_bit & m != 0,
    }
}

/// Human-readable description of which effect kinds are permitted by a mask.
pub fn describe_mask(mask: EffectMask) -> Vec<&'static str> {
    let mut names = Vec::new();
    if mask & EFFECT_SET_FIELD != 0 {
        names.push("SetField");
    }
    if mask & EFFECT_TRANSFER != 0 {
        names.push("Transfer");
    }
    if mask & EFFECT_GRANT_CAPABILITY != 0 {
        names.push("GrantCapability");
    }
    if mask & EFFECT_REVOKE_CAPABILITY != 0 {
        names.push("RevokeCapability");
    }
    if mask & EFFECT_EMIT_EVENT != 0 {
        names.push("EmitEvent");
    }
    if mask & EFFECT_INCREMENT_NONCE != 0 {
        names.push("IncrementNonce");
    }
    if mask & EFFECT_CREATE_CELL != 0 {
        names.push("CreateCell");
    }
    if mask & EFFECT_SET_PERMISSIONS != 0 {
        names.push("SetPermissions");
    }
    if mask & EFFECT_SET_VERIFICATION_KEY != 0 {
        names.push("SetVerificationKey");
    }
    if mask & EFFECT_NOTE_SPEND != 0 {
        names.push("NoteSpend");
    }
    if mask & EFFECT_NOTE_CREATE != 0 {
        names.push("NoteCreate");
    }
    if mask & EFFECT_SEAL_OPS != 0 {
        names.push("SealOps");
    }
    if mask & EFFECT_BRIDGE_OPS != 0 {
        names.push("BridgeOps");
    }
    if mask & EFFECT_INTRODUCE != 0 {
        names.push("Introduce");
    }
    if mask & EFFECT_OBLIGATION_OPS != 0 {
        names.push("ObligationOps");
    }
    if mask & EFFECT_ESCROW_OPS != 0 {
        names.push("EscrowOps");
    }
    if mask & EFFECT_DELEGATION_OPS != 0 {
        names.push("DelegationOps");
    }
    if mask & EFFECT_SOVEREIGN_OPS != 0 {
        names.push("SovereignOps");
    }
    names
}

/// A builder for constructing facet masks using a fluent API.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct FacetBuilder {
    mask: EffectMask,
}

impl FacetBuilder {
    pub fn new() -> Self {
        Self { mask: 0 }
    }

    /// Start from an existing mask.
    pub fn from_mask(mask: EffectMask) -> Self {
        Self { mask }
    }

    /// Allow setting state fields.
    pub fn allow_set_field(mut self) -> Self {
        self.mask |= EFFECT_SET_FIELD;
        self
    }

    /// Allow transferring value.
    pub fn allow_transfer(mut self) -> Self {
        self.mask |= EFFECT_TRANSFER;
        self
    }

    /// Allow granting capabilities.
    pub fn allow_grant_capability(mut self) -> Self {
        self.mask |= EFFECT_GRANT_CAPABILITY;
        self
    }

    /// Allow revoking capabilities.
    pub fn allow_revoke_capability(mut self) -> Self {
        self.mask |= EFFECT_REVOKE_CAPABILITY;
        self
    }

    /// Allow emitting events.
    pub fn allow_emit_event(mut self) -> Self {
        self.mask |= EFFECT_EMIT_EVENT;
        self
    }

    /// Allow incrementing nonce.
    pub fn allow_increment_nonce(mut self) -> Self {
        self.mask |= EFFECT_INCREMENT_NONCE;
        self
    }

    /// Allow creating cells.
    pub fn allow_create_cell(mut self) -> Self {
        self.mask |= EFFECT_CREATE_CELL;
        self
    }

    /// Allow setting permissions.
    pub fn allow_set_permissions(mut self) -> Self {
        self.mask |= EFFECT_SET_PERMISSIONS;
        self
    }

    /// Allow setting verification key.
    pub fn allow_set_verification_key(mut self) -> Self {
        self.mask |= EFFECT_SET_VERIFICATION_KEY;
        self
    }

    /// Build the final mask.
    pub fn build(self) -> EffectMask {
        self.mask
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_facet_attenuation_subset() {
        let parent = EFFECT_SET_FIELD | EFFECT_TRANSFER | EFFECT_EMIT_EVENT;
        let child = EFFECT_SET_FIELD | EFFECT_EMIT_EVENT;
        assert!(is_facet_attenuation(parent, child));
    }

    #[test]
    fn test_facet_attenuation_amplification_denied() {
        let parent = EFFECT_SET_FIELD | EFFECT_EMIT_EVENT;
        let child = EFFECT_SET_FIELD | EFFECT_TRANSFER; // TRANSFER not in parent
        assert!(!is_facet_attenuation(parent, child));
    }

    #[test]
    fn test_facet_attenuation_same_is_ok() {
        let mask = FACET_STATE_WRITER;
        assert!(is_facet_attenuation(mask, mask));
    }

    #[test]
    fn test_facet_all_permits_everything() {
        assert!(is_facet_attenuation(EFFECT_ALL, FACET_ADMIN));
        assert!(is_facet_attenuation(EFFECT_ALL, FACET_READ_ONLY));
        assert!(is_facet_attenuation(EFFECT_ALL, EFFECT_ALL));
    }

    #[test]
    fn test_effect_permitted_none_allows_all() {
        assert!(is_effect_permitted(None, EFFECT_SET_FIELD));
        assert!(is_effect_permitted(None, EFFECT_TRANSFER));
        assert!(is_effect_permitted(None, EFFECT_SOVEREIGN_OPS));
    }

    #[test]
    fn test_effect_permitted_mask_restricts() {
        let mask = FACET_TRANSFER_ONLY;
        assert!(is_effect_permitted(Some(mask), EFFECT_TRANSFER));
        assert!(!is_effect_permitted(Some(mask), EFFECT_SET_FIELD));
        assert!(!is_effect_permitted(Some(mask), EFFECT_SET_PERMISSIONS));
    }

    #[test]
    fn test_facet_builder() {
        let mask = FacetBuilder::new()
            .allow_set_field()
            .allow_emit_event()
            .build();
        assert_eq!(mask, FACET_STATE_WRITER);
    }

    #[test]
    fn test_describe_mask() {
        let names = describe_mask(FACET_STATE_WRITER);
        assert!(names.contains(&"SetField"));
        assert!(names.contains(&"EmitEvent"));
        assert!(!names.contains(&"Transfer"));
    }
}
