//! The deos-side mandate registry — what each Hermes tool is GRANTED.
//!
//! The [`ToolGateway`](dregg_sdk::ToolGateway) is policy-free: the GRANTOR pins
//! a [`ToolGrant`](dregg_sdk::ToolGrant) (SCOPE ∧ DEADLINE ∧ RATE) at delegation
//! time, and `ToolGateway::invoke` admits a call IFF the proven `delegAdmit`
//! predicate holds. The grantor here is DEOS: for Hermes to assist deos
//! development *confined*, deos decides — per tool — the scope, the rate
//! ceiling, and the deadline. This registry is that decision, expressed as a
//! default [`ToolGrant`] per [`ToolKind`].
//!
//! A grant per kind, NOT per individual tool, keeps the confinement legible:
//! the dangerous classes (`Edit`, `Execute`) get tight rate ceilings; the
//! read-only classes (`Read`, `Search`) get generous ones; an unknown tool
//! falls into `Other` (the tightest default) — fail-closed by classification.
//!
//! Each grant fixes a distinct `tool_id` (the SCOPE's in-band face) and a
//! `tool_method` (the SCOPE's executor face — the verb the worker's biscuit
//! credential covers). A `ToolGateway` admitted under a kind's grant therefore
//! refuses, in-band, any call whose tool maps to a DIFFERENT kind.

use std::collections::HashMap;

use dregg_sdk::ToolGrant;

use crate::acp::ToolKind;

/// A stable, distinct tool id per kind (the SCOPE's in-band face). Arbitrary but
/// fixed: the gate only checks the presented id equals the granted one.
fn tool_id_for(kind: ToolKind) -> i64 {
    match kind {
        ToolKind::Read => 10,
        ToolKind::Search => 20,
        ToolKind::Fetch => 30,
        ToolKind::Execute => 40,
        ToolKind::Edit => 50,
        ToolKind::Other => 90,
    }
}

/// The executor method verb the worker's credential is scoped to (the SCOPE's
/// executor face). A turn under any other verb is rejected by the executor with
/// `TokenInsufficientCapability`.
fn method_for(kind: ToolKind) -> &'static str {
    match kind {
        ToolKind::Read => "tool.read",
        ToolKind::Search => "tool.search",
        ToolKind::Fetch => "tool.fetch",
        ToolKind::Execute => "tool.execute",
        ToolKind::Edit => "tool.edit",
        ToolKind::Other => "tool.other",
    }
}

/// The DEFAULT rate ceiling per kind — deos's confinement of how many times,
/// per mandate window, Hermes may exercise this class of tool. The dangerous
/// classes are tight; the read-only classes are generous.
fn default_rate(kind: ToolKind) -> i64 {
    match kind {
        ToolKind::Read => 200,
        ToolKind::Search => 100,
        ToolKind::Fetch => 50,
        ToolKind::Execute => 20,
        ToolKind::Edit => 30,
        ToolKind::Other => 10,
    }
}

/// deos's mandate over a Hermes ACP session: one [`ToolGrant`] per [`ToolKind`].
///
/// Built with [`GrantRegistry::default_for_session`] (the standard confinement)
/// and consulted by [`crate::HermesGateway`] to admit a worker per kind on first
/// use. `deadline` is the session-wide mandate expiry (a clock/height ceiling);
/// every kind shares it.
#[derive(Clone, Debug)]
pub struct GrantRegistry {
    grants: HashMap<ToolKind, ToolGrant>,
}

impl GrantRegistry {
    /// The standard deos confinement for a Hermes session: every kind gets its
    /// default-rate grant, all sharing `deadline` (the session mandate expiry).
    pub fn default_for_session(deadline: i64) -> GrantRegistry {
        let mut grants = HashMap::new();
        for kind in [
            ToolKind::Read,
            ToolKind::Search,
            ToolKind::Fetch,
            ToolKind::Execute,
            ToolKind::Edit,
            ToolKind::Other,
        ] {
            grants.insert(
                kind,
                ToolGrant {
                    tool_id: tool_id_for(kind),
                    rate_limit: default_rate(kind),
                    deadline,
                    tool_method: method_for(kind).to_string(),
                },
            );
        }
        GrantRegistry { grants }
    }

    /// Override a single kind's grant (e.g. tighten `Execute` to rate 0 to deny
    /// shell entirely, or extend a deadline). Returns `self` for chaining.
    pub fn with_grant(mut self, kind: ToolKind, grant: ToolGrant) -> Self {
        self.grants.insert(kind, grant);
        self
    }

    /// The grant for a kind. Always present after `default_for_session`.
    pub fn grant_for(&self, kind: ToolKind) -> &ToolGrant {
        self.grants
            .get(&kind)
            .expect("every kind has a grant after default_for_session")
    }

    /// The canonical in-band tool id a call of this kind must present to be
    /// in-scope under its grant. (The ACP wire does not carry our scalar id, so
    /// the gate synthesizes it from the tool name's kind — see
    /// [`crate::HermesGateway::admit_call`].)
    pub fn tool_id_for(&self, kind: ToolKind) -> i64 {
        self.grant_for(kind).tool_id
    }
}
