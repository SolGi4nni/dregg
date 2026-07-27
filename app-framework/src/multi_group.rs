//! Multi-group federation membership configuration.
//!
//! `MultiGroupConfig` lets an app declare which federation groups it
//! participates in. This is used during session establishment and routing:
//! a CapTP session from a peer in an unrecognized group will be rejected.
//!
//! # Usage
//!
//! ```
//! use dregg_app_framework::multi_group::{GroupId, MultiGroupConfig};
//! use dregg_captp::FederationId;
//!
//! # let main_group: GroupId = FederationId([1u8; 32]);
//! # let partner_group: GroupId = FederationId([2u8; 32]);
//! # let stranger: GroupId = FederationId([9u8; 32]);
//! let config = MultiGroupConfig::new(vec![main_group, partner_group]);
//! assert!(config.includes(&main_group));
//! assert!(config.includes(&partner_group));
//! // A session from an unrecognized group is refused.
//! assert!(!config.includes(&stranger));
//! ```

pub use dregg_captp::GroupId;

/// Configuration for multi-federation-group membership.
///
/// Apps that bridge multiple federations or operate as shared infrastructure
/// across groups store the accepted group IDs here and check incoming sessions
/// against it.
#[derive(Clone, Debug, Default)]
pub struct MultiGroupConfig {
    /// The groups this app participates in.
    pub groups: Vec<GroupId>,
}

impl MultiGroupConfig {
    /// Create a config accepting the given groups.
    pub fn new(groups: Vec<GroupId>) -> Self {
        Self { groups }
    }

    /// Return `true` if `group` is in the accepted list.
    pub fn includes(&self, group: &GroupId) -> bool {
        self.groups.iter().any(|g| g == group)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_captp::FederationId;

    fn gid(b: u8) -> GroupId {
        FederationId([b; 32])
    }

    #[test]
    fn empty_config_includes_nothing() {
        let config = MultiGroupConfig::default();
        assert!(!config.includes(&gid(1)));
    }

    #[test]
    fn includes_returns_true_for_known_group() {
        let g1 = gid(0xAA);
        let g2 = gid(0xBB);
        let config = MultiGroupConfig::new(vec![g1, g2]);
        assert!(config.includes(&g1));
        assert!(config.includes(&g2));
        assert!(!config.includes(&gid(0xFF)));
    }
}
