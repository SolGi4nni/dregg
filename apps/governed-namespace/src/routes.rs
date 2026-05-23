//! DFA-governed routing: compile path patterns into a prefix trie state machine.
//!
//! The routing table maps URL path prefixes to access classifications. When a request
//! arrives at `/namespace/*`, the DFA classifies it and determines:
//! - Which logical storage partition the request targets
//! - What permission level is required
//! - Whether the request is allowed under current governance
//!
//! The DFA is committed to via blake3 hash of its serialized route table. This
//! commitment is stored on-chain/in-federation and can be verified in a STARK proof:
//! "The route table I used to classify this request has commitment C, which matches
//! the governance-approved commitment."
//!
//! ## Simplification
//!
//! A full NFA→DFA compilation (as in rbg/routing.rs) handles regex patterns,
//! character classes, and alternation. For this demo we use prefix-match semantics:
//! longest-prefix wins, compiled into a sorted trie that acts as a DFA over path
//! segments.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

/// Access classification for a route.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RouteClass {
    /// Anyone can access (no auth required).
    Public,
    /// Only authenticated members can access.
    MembersOnly,
    /// Only administrators can access.
    AdminOnly,
    /// Requires multi-signature (e.g., treasury).
    Multisig { threshold: u32 },
    /// Custom classification with a named policy.
    Custom(String),
}

impl RouteClass {
    /// Human-readable label for the classification.
    pub fn label(&self) -> &str {
        match self {
            RouteClass::Public => "public",
            RouteClass::MembersOnly => "members_only",
            RouteClass::AdminOnly => "admin_only",
            RouteClass::Multisig { .. } => "multisig",
            RouteClass::Custom(name) => name.as_str(),
        }
    }
}

/// A single route entry: maps a path prefix to an access classification.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RouteEntry {
    /// The path prefix pattern (e.g., "/public/", "/treasury/").
    /// Always starts with "/" and ends with "/".
    pub prefix: String,
    /// The access classification for this route.
    pub class: RouteClass,
    /// Optional description for governance proposals.
    pub description: Option<String>,
}

/// The compiled DFA routing table.
///
/// Internally uses a BTreeMap for deterministic ordering (important for commitment
/// hashing). Routes are stored by prefix and looked up via longest-prefix match.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RoutingTable {
    /// Ordered map of prefix → route entry.
    routes: BTreeMap<String, RouteEntry>,
    /// The version number of this table (incremented on each governance amendment).
    pub version: u64,
}

/// The result of classifying a path through the DFA.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Classification {
    /// The matching route entry (None = no route matched, deny by default).
    pub route: Option<RouteEntry>,
    /// The matched prefix (longest match).
    pub matched_prefix: Option<String>,
    /// The remaining path after the prefix (the "file path" within the route).
    pub remainder: String,
}

impl RoutingTable {
    /// Create a new empty routing table at version 0.
    pub fn new() -> Self {
        Self {
            routes: BTreeMap::new(),
            version: 0,
        }
    }

    /// Create a routing table with the default DAO routes.
    pub fn default_dao() -> Self {
        let mut table = Self::new();
        table.add_route(RouteEntry {
            prefix: "/public/".to_string(),
            class: RouteClass::Public,
            description: Some("Publicly accessible files".to_string()),
        });
        table.add_route(RouteEntry {
            prefix: "/members/".to_string(),
            class: RouteClass::MembersOnly,
            description: Some("Member-only documents".to_string()),
        });
        table.add_route(RouteEntry {
            prefix: "/admin/".to_string(),
            class: RouteClass::AdminOnly,
            description: Some("Administrative files".to_string()),
        });
        table.add_route(RouteEntry {
            prefix: "/treasury/".to_string(),
            class: RouteClass::Multisig { threshold: 3 },
            description: Some("Treasury documents requiring multisig".to_string()),
        });
        table.add_route(RouteEntry {
            prefix: "/proposals/".to_string(),
            class: RouteClass::MembersOnly,
            description: Some("Governance proposals".to_string()),
        });
        table
    }

    /// Add or update a route entry.
    pub fn add_route(&mut self, entry: RouteEntry) {
        self.routes.insert(entry.prefix.clone(), entry);
    }

    /// Remove a route by prefix.
    pub fn remove_route(&mut self, prefix: &str) -> bool {
        self.routes.remove(prefix).is_some()
    }

    /// Classify a path by finding the longest matching prefix.
    ///
    /// This is the DFA step: given a path, we walk the sorted route table
    /// and find the longest prefix that matches. The classification determines
    /// what permissions are needed.
    pub fn classify(&self, path: &str) -> Classification {
        // Ensure path starts with /
        let normalized = if path.starts_with('/') {
            path.to_string()
        } else {
            format!("/{path}")
        };

        // Longest-prefix match: iterate all prefixes, find longest match.
        let mut best_match: Option<(&String, &RouteEntry)> = None;

        for (prefix, entry) in &self.routes {
            if normalized.starts_with(prefix.as_str()) {
                match best_match {
                    None => best_match = Some((prefix, entry)),
                    Some((current_prefix, _)) => {
                        if prefix.len() > current_prefix.len() {
                            best_match = Some((prefix, entry));
                        }
                    }
                }
            }
        }

        match best_match {
            Some((prefix, entry)) => {
                let remainder = normalized[prefix.len()..].to_string();
                Classification {
                    route: Some(entry.clone()),
                    matched_prefix: Some(prefix.clone()),
                    remainder,
                }
            }
            None => Classification {
                route: None,
                matched_prefix: None,
                remainder: normalized,
            },
        }
    }

    /// Compute the blake3 commitment hash of this routing table.
    ///
    /// The commitment is deterministic: same routes in same order produce same hash.
    /// This is used by governance to bind votes to specific route tables, and by
    /// STARK proofs to demonstrate that classification used the approved table.
    pub fn commitment(&self) -> [u8; 32] {
        let serialized =
            serde_json::to_vec(&self.routes).expect("route table serialization cannot fail");
        *blake3::hash(&serialized).as_bytes()
    }

    /// Get all route entries as a list (for API responses).
    pub fn entries(&self) -> Vec<&RouteEntry> {
        self.routes.values().collect()
    }

    /// Get the number of routes.
    pub fn len(&self) -> usize {
        self.routes.len()
    }

    /// Check if the table is empty.
    pub fn is_empty(&self) -> bool {
        self.routes.is_empty()
    }

    /// Replace the entire route set atomically (used when governance passes an amendment).
    pub fn replace_all(&mut self, new_routes: Vec<RouteEntry>) {
        self.routes.clear();
        for entry in new_routes {
            self.routes.insert(entry.prefix.clone(), entry);
        }
        self.version += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn classify_longest_prefix() {
        let table = RoutingTable::default_dao();

        let c = table.classify("/public/readme.txt");
        assert_eq!(c.route.as_ref().unwrap().class, RouteClass::Public);
        assert_eq!(c.matched_prefix.as_deref(), Some("/public/"));
        assert_eq!(c.remainder, "readme.txt");
    }

    #[test]
    fn classify_no_match_denies() {
        let table = RoutingTable::default_dao();
        let c = table.classify("/unknown/path");
        assert!(c.route.is_none());
    }

    #[test]
    fn classify_multisig() {
        let table = RoutingTable::default_dao();
        let c = table.classify("/treasury/budget.csv");
        assert_eq!(
            c.route.as_ref().unwrap().class,
            RouteClass::Multisig { threshold: 3 }
        );
        assert_eq!(c.remainder, "budget.csv");
    }

    #[test]
    fn commitment_is_deterministic() {
        let t1 = RoutingTable::default_dao();
        let t2 = RoutingTable::default_dao();
        assert_eq!(t1.commitment(), t2.commitment());
    }

    #[test]
    fn commitment_changes_on_mutation() {
        let t1 = RoutingTable::default_dao();
        let mut t2 = RoutingTable::default_dao();
        t2.add_route(RouteEntry {
            prefix: "/grants/".to_string(),
            class: RouteClass::MembersOnly,
            description: None,
        });
        assert_ne!(t1.commitment(), t2.commitment());
    }

    #[test]
    fn replace_all_bumps_version() {
        let mut table = RoutingTable::default_dao();
        assert_eq!(table.version, 0);

        table.replace_all(vec![RouteEntry {
            prefix: "/new/".to_string(),
            class: RouteClass::Public,
            description: None,
        }]);

        assert_eq!(table.version, 1);
        assert_eq!(table.len(), 1);
    }
}
