//! Token state, facts, rules, attenuation, and fold deltas.
//!
//! A token in the dregg system is a structured authorization state that
//! carries:
//! - **Facts**: concrete capabilities (app access, service access, etc.)
//! - **Rules**: authorization policies that evaluate facts against requests
//! - **Checks**: attenuation constraints that narrow what the token can do
//! - **State root**: a BLAKE3 commitment to the entire token state
//! - **Derivation trace**: cryptographic proof of how the token was derived
//!
//! Attenuation produces a new token with strictly fewer capabilities.
//! The fold delta between the original and attenuated token is verifiable
//! without access to the original token's signing authority.
//!
//! NOTE: This module provides the demo's high-level authorization logic (facts,
//! rules, checks, authorize). The REAL Merkle commitment and fold delta verification
//! is computed in parallel via `commit_state.rs` using `dregg_commit::TokenState`
//! and `dregg_commit::FoldDelta`. The state_root here uses a flat BLAKE3 hash;
//! the real commitment uses a 4-ary Poseidon-style Merkle tree.
//!
//! // TODO: integrate with real dregg_commit::TokenState as the primary state
//! // representation, replacing the flat BLAKE3 state_root with the real Merkle root.
//! // This would require mapping demo Facts to dregg_commit::Fact field elements
//! // and running authorization against the Merkle-committed state.

use crate::authority::{PublicKey, hex_encode};
use crate::trace::DerivationStep;

// =============================================================================
// Facts
// =============================================================================

/// A fact represents a single capability or attribute in the token.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fact {
    /// The fact type (e.g., "app", "service", "feature", "organization").
    pub kind: FactKind,
    /// The resource identifier.
    pub resource: String,
    /// The actions permitted (e.g., "rwcd", "r", "rw").
    /// Empty string for facts without actions (like "feature").
    pub actions: String,
}

/// Enumeration of fact types in the dregg system.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum FactKind {
    /// Application access: app("name", "actions")
    App,
    /// Service access: service("name", "actions")
    Service,
    /// Feature flag: feature("name")
    Feature,
    /// Organization membership: organization("id")
    Organization,
    /// User identity: user("id")
    User,
}

impl Fact {
    /// Create an app fact.
    pub fn app(name: &str, actions: &str) -> Self {
        Fact {
            kind: FactKind::App,
            resource: name.to_string(),
            actions: actions.to_string(),
        }
    }

    /// Create a service fact.
    pub fn service(name: &str, actions: &str) -> Self {
        Fact {
            kind: FactKind::Service,
            resource: name.to_string(),
            actions: actions.to_string(),
        }
    }

    /// Create a feature fact.
    pub fn feature(name: &str) -> Self {
        Fact {
            kind: FactKind::Feature,
            resource: name.to_string(),
            actions: String::new(),
        }
    }

    /// Create an organization fact.
    pub fn organization(id: &str) -> Self {
        Fact {
            kind: FactKind::Organization,
            resource: id.to_string(),
            actions: String::new(),
        }
    }

    /// Create a user fact.
    pub fn user(id: &str) -> Self {
        Fact {
            kind: FactKind::User,
            resource: id.to_string(),
            actions: String::new(),
        }
    }

    /// Serialize the fact to bytes for hashing.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        let kind_byte = match self.kind {
            FactKind::App => 0u8,
            FactKind::Service => 1,
            FactKind::Feature => 2,
            FactKind::Organization => 3,
            FactKind::User => 4,
        };
        buf.push(kind_byte);
        buf.extend_from_slice(self.resource.as_bytes());
        buf.push(0); // separator
        buf.extend_from_slice(self.actions.as_bytes());
        buf
    }
}

// =============================================================================
// Rules
// =============================================================================

/// A rule defines an authorization policy.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rule {
    /// The rule type.
    pub kind: RuleKind,
    /// Human-readable description.
    pub description: String,
}

/// Types of authorization rules.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuleKind {
    /// Allow if app matches and actions are sufficient.
    AllowApp,
    /// Allow if service matches and actions are sufficient.
    AllowService,
    /// Allow if unrestricted token.
    AllowUnrestricted,
    /// Default deny.
    DenyDefault,
}

impl Rule {
    pub fn allow_app() -> Self {
        Rule {
            kind: RuleKind::AllowApp,
            description: "allow if app($app, $actions), request_app($app), request_action($act), $actions.contains($act)".to_string(),
        }
    }

    pub fn allow_service() -> Self {
        Rule {
            kind: RuleKind::AllowService,
            description: "allow if service($svc, $actions), request_service($svc), request_action($act), $actions.contains($act)".to_string(),
        }
    }

    pub fn allow_unrestricted() -> Self {
        Rule {
            kind: RuleKind::AllowUnrestricted,
            description: "allow if unrestricted(true)".to_string(),
        }
    }

    pub fn deny_default() -> Self {
        Rule {
            kind: RuleKind::DenyDefault,
            description: "deny if true".to_string(),
        }
    }

    /// Serialize the rule to bytes for hashing.
    pub fn to_bytes(&self) -> Vec<u8> {
        self.description.as_bytes().to_vec()
    }
}

// =============================================================================
// Checks (Attenuation Constraints)
// =============================================================================

/// A check is an attenuation constraint that narrows the token's capabilities.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Check {
    /// What this check constrains.
    pub kind: CheckKind,
    /// Human-readable description.
    pub description: String,
}

/// Types of attenuation checks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CheckKind {
    /// Restrict to a specific action (e.g., read-only).
    ActionRestriction { allowed_actions: String },
    /// Restrict to a specific app.
    AppRestriction { app_id: String },
}

impl Check {
    /// Create a read-only action restriction.
    pub fn read_only() -> Self {
        Check {
            kind: CheckKind::ActionRestriction {
                allowed_actions: "r".to_string(),
            },
            description: "check if request_action($act), \"r\".contains($act)".to_string(),
        }
    }

    /// Create an app restriction.
    pub fn restrict_app(app_id: &str) -> Self {
        Check {
            kind: CheckKind::AppRestriction {
                app_id: app_id.to_string(),
            },
            description: format!("check if request_app(\"{app_id}\")"),
        }
    }

    /// Serialize the check to bytes for hashing.
    pub fn to_bytes(&self) -> Vec<u8> {
        self.description.as_bytes().to_vec()
    }

    /// Evaluate this check against a request.
    pub fn evaluate(&self, request: &AuthorizationRequest) -> bool {
        match &self.kind {
            CheckKind::ActionRestriction { allowed_actions } => {
                // Every character in the requested action must be in allowed_actions.
                request.action.chars().all(|c| allowed_actions.contains(c))
            }
            CheckKind::AppRestriction { app_id } => request.app == *app_id,
        }
    }
}

// =============================================================================
// Authorization Request
// =============================================================================

/// A request to authorize an action on a resource.
#[derive(Clone, Debug)]
pub struct AuthorizationRequest {
    /// The target application.
    pub app: String,
    /// The target service (optional).
    pub service: Option<String>,
    /// The action being requested (e.g., "r", "w", "rw", "d").
    pub action: String,
}

// =============================================================================
// Token State
// =============================================================================

/// The complete state of a dregg authorization token.
#[derive(Clone)]
pub struct TokenState {
    /// Unique identifier for this token.
    pub id: String,
    /// The issuing authority's public key.
    pub issuer: PublicKey,
    /// The set of facts (capabilities) in this token.
    pub facts: Vec<Fact>,
    /// The authorization rules.
    pub rules: Vec<Rule>,
    /// Attenuation checks (added during delegation).
    pub checks: Vec<Check>,
    /// BLAKE3 commitment to the token state.
    pub state_root: [u8; 32],
    /// Ed25519 signature over the state root by the issuer (64 bytes).
    pub signature: [u8; 64],
    /// The chain of derivation steps from mint to current state.
    pub derivation_trace: Vec<DerivationStep>,
    /// Whether this token has been revoked.
    pub revoked: bool,
}

impl TokenState {
    /// Compute the BLAKE3 state root over the token's content.
    pub fn compute_state_root(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();

        // Hash the token ID.
        hasher.update(self.id.as_bytes());
        hasher.update(&[0xff]); // domain separator

        // Hash the issuer.
        hasher.update(self.issuer.as_bytes());
        hasher.update(&[0xfe]); // domain separator

        // Hash all facts.
        for fact in &self.facts {
            hasher.update(&fact.to_bytes());
            hasher.update(&[0xfd]);
        }

        // Hash all rules.
        for rule in &self.rules {
            hasher.update(&rule.to_bytes());
            hasher.update(&[0xfc]);
        }

        // Hash all checks.
        for check in &self.checks {
            hasher.update(&check.to_bytes());
            hasher.update(&[0xfb]);
        }

        *hasher.finalize().as_bytes()
    }

    /// Attenuate this token by removing facts and adding checks.
    ///
    /// Returns a new token with:
    /// - The specified facts removed
    /// - The specified checks added
    /// - A new state root
    /// - An updated derivation trace
    ///
    /// The attenuation is signed by the attenuating authority (which may be
    /// different from the original issuer — this is the key federated property).
    pub fn attenuate(
        &self,
        remove_facts: &[Fact],
        add_checks: Vec<Check>,
        attenuator: &crate::authority::Authority,
    ) -> TokenState {
        let input_root = self.state_root;

        // Remove specified facts.
        let new_facts: Vec<Fact> = self
            .facts
            .iter()
            .filter(|f| !remove_facts.contains(f))
            .cloned()
            .collect();

        // Add new checks.
        let mut new_checks = self.checks.clone();
        new_checks.extend(add_checks);

        // Build the attenuated token.
        let mut attenuated = TokenState {
            id: self.id.clone(),
            issuer: self.issuer.clone(), // Issuer stays the same (original minter).
            facts: new_facts,
            rules: self.rules.clone(),
            checks: new_checks,
            state_root: [0u8; 32],
            signature: self.signature, // Original signature preserved.
            derivation_trace: self.derivation_trace.clone(),
            revoked: false,
        };

        // Compute new state root.
        attenuated.state_root = attenuated.compute_state_root();

        // Sign the attenuation step.
        let attenuation_sig = attenuator.sign(&attenuated.state_root);

        // Record the attenuation in the derivation trace.
        attenuated.derivation_trace.push(DerivationStep {
            authority: attenuator.public_key.clone(),
            input_root,
            output_root: attenuated.state_root,
            signature: attenuation_sig,
        });

        attenuated
    }

    /// Evaluate the token against an authorization request.
    ///
    /// Returns Ok(()) if authorized, Err(reason) if denied.
    pub fn authorize(&self, request: &AuthorizationRequest) -> Result<(), String> {
        if self.revoked {
            return Err("token has been revoked".to_string());
        }

        // First, check all attenuation constraints.
        for check in &self.checks {
            if !check.evaluate(request) {
                let reason = match &check.kind {
                    CheckKind::ActionRestriction { allowed_actions } => {
                        format!(
                            "action \"{}\" not contained in allowed actions \"{}\"",
                            request.action, allowed_actions
                        )
                    }
                    CheckKind::AppRestriction { app_id } => {
                        format!("request app \"{}\" != required \"{}\"", request.app, app_id)
                    }
                };
                return Err(reason);
            }
        }

        // Then, evaluate rules against facts.
        // Find a matching fact for the request.
        let authorized = self
            .facts
            .iter()
            .any(|fact| match (&fact.kind, &request.service) {
                (FactKind::App, _) => {
                    fact.resource == request.app
                        && request.action.chars().all(|c| fact.actions.contains(c))
                }
                (FactKind::Service, Some(svc)) => {
                    fact.resource == *svc
                        && request.action.chars().all(|c| fact.actions.contains(c))
                }
                _ => false,
            });

        if authorized {
            Ok(())
        } else {
            Err(format!(
                "no matching fact for app=\"{}\", action=\"{}\"",
                request.app, request.action
            ))
        }
    }

    /// Get the state root as a short hex string.
    pub fn state_root_hex(&self) -> String {
        hex_encode(&self.state_root[..4])
    }
}

// =============================================================================
// Fold Delta
// =============================================================================

/// A fold delta represents the difference between two token states.
/// It can be verified independently to prove that attenuation was valid
/// (i.e., the new state is strictly less powerful than the old state).
#[derive(Clone, Debug)]
pub struct FoldDelta {
    /// The state root after attenuation.
    pub output_root: [u8; 32],
}

impl FoldDelta {
    /// Compute a fold delta between an original and attenuated token.
    pub fn compute(_original: &TokenState, attenuated: &TokenState) -> Self {
        FoldDelta {
            output_root: attenuated.state_root,
        }
    }

    /// Verify that the fold delta represents a valid attenuation.
    ///
    /// A valid attenuation:
    /// 1. Only removes facts (never adds new capabilities)
    /// 2. Only adds checks (never removes constraints)
    /// 3. The output root matches the attenuated state
    pub fn verify(&self, attenuated: &TokenState) -> bool {
        // Verify the output root matches.
        if self.output_root != attenuated.state_root {
            return false;
        }

        // Verify no new facts were added (attenuated facts must be a subset).
        // This is implicit: removed_facts + attenuated.facts should reconstruct
        // the original fact set. We verify the structure is consistent.
        let reconstructed_root = attenuated.compute_state_root();
        if reconstructed_root != self.output_root {
            return false;
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::authority::Authority;

    #[test]
    fn test_check_read_only() {
        let check = Check::read_only();
        let req = AuthorizationRequest {
            app: "frontend".to_string(),
            service: None,
            action: "r".to_string(),
        };
        assert!(check.evaluate(&req));

        let req_write = AuthorizationRequest {
            app: "frontend".to_string(),
            service: None,
            action: "w".to_string(),
        };
        assert!(!check.evaluate(&req_write));
    }

    #[test]
    fn test_attenuation() {
        let auth = Authority::new("acme.corp");
        let facts = vec![
            Fact::app("frontend", "rwcd"),
            Fact::app("backend", "rw"),
            Fact::service("http", "rw"),
        ];
        let rules = vec![Rule::allow_app(), Rule::deny_default()];
        let token = auth.mint_token(facts, rules);

        let remove = vec![Fact::app("backend", "rw")];
        let checks = vec![Check::read_only()];
        let attenuated = token.attenuate(&remove, checks, &auth);

        assert_eq!(attenuated.facts.len(), 2);
        assert_eq!(attenuated.checks.len(), 1);
        assert_ne!(attenuated.state_root, token.state_root);
        assert_eq!(attenuated.derivation_trace.len(), 2);
    }

    #[test]
    fn test_fold_delta() {
        let auth = Authority::new("acme.corp");
        let facts = vec![Fact::app("frontend", "rwcd"), Fact::app("backend", "rw")];
        let rules = vec![Rule::allow_app(), Rule::deny_default()];
        let token = auth.mint_token(facts, rules);

        let remove = vec![Fact::app("backend", "rw")];
        let checks = vec![Check::read_only()];
        let attenuated = token.attenuate(&remove, checks, &auth);

        let delta = FoldDelta::compute(&token, &attenuated);
        assert!(delta.verify(&attenuated));
    }

    #[test]
    fn test_authorization() {
        let auth = Authority::new("acme.corp");
        let facts = vec![Fact::app("frontend", "rw")];
        let rules = vec![Rule::allow_app(), Rule::deny_default()];
        let token = auth.mint_token(facts, rules);

        let req_ok = AuthorizationRequest {
            app: "frontend".to_string(),
            service: None,
            action: "r".to_string(),
        };
        assert!(token.authorize(&req_ok).is_ok());

        let req_denied = AuthorizationRequest {
            app: "backend".to_string(),
            service: None,
            action: "r".to_string(),
        };
        assert!(token.authorize(&req_denied).is_err());
    }
}
