//! The capability vocabulary on top of the [`crate::cred`] core — the powerbox
//! an agent's bundle is minted from.
//!
//! An agent is granted a set of named **capability** strings (the services it
//! may `invoke`: `run_tests`, `verify_deploy`, `check_health`, …) via a single
//! first-party caveat:
//!
//! ```text
//! AnyOf([ AttrEq{cap, "run_tests"}, AttrEq{cap, "check_health"} ])
//! ```
//!
//! The gate verifies the presented credential against a context binding
//! `cap = <the action's required capability>` and `clock = now`. The `AnyOf`
//! admits iff the requested cap is one the credential was granted. To confine to
//! a sub-agent, [`attenuate_caps`] appends a *narrower* `AnyOf` — the caveat meet
//! then rejects any cap outside the narrowed set, so a `check_health` credential
//! can never reach `verify_deploy` (the no-amplify property, proven in
//! `cred::tests::attenuation_only_narrows`).

use serde::{Deserialize, Serialize};

use crate::cred::{Caveat, Context, Credential, Pred, RootKey};

/// The request attribute key a capability is matched on.
pub const CAP_KEY: &str = "cap";

/// One grant in a cap bundle: an **exact** capability (the request cap must equal
/// it, e.g. `shell`, `invoke:run_tests`, `http:api.github.com`) or a **prefix**
/// capability — a resource-scoped grant that admits any request cap *starting
/// with* the prefix (e.g. a `Prefix("fs-read:/workdir")` admits
/// `fs-read:/workdir/repo/Cargo.toml` but not `fs-read:/etc/passwd`). The prefix
/// form rides [`Pred::AttrPrefix`], so resource scoping is part of the *signed*
/// authority, not an afterthought the run loop checks — a sub-agent can only ever
/// narrow it (`attenuate_subset`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CapGrant {
    /// The request cap must equal this string exactly.
    Exact(String),
    /// The request cap must start with this string (resource scoping).
    Prefix(String),
}

impl CapGrant {
    /// The predicate this grant contributes to the bundle's `AnyOf`.
    fn pred(&self) -> Pred {
        match self {
            CapGrant::Exact(v) => Pred::AttrEq {
                key: CAP_KEY.to_string(),
                value: v.clone(),
            },
            CapGrant::Prefix(p) => Pred::AttrPrefix {
                key: CAP_KEY.to_string(),
                prefix: p.clone(),
            },
        }
    }

    /// `true` iff this grant **covers** `child` — i.e. an agent holding `self`
    /// could itself hold (or hand down) `child` without amplifying. Exact covers
    /// only the identical cap; a prefix covers an equal/longer prefix and any
    /// exact cap under it. The no-amplify check `deploy_subagent` uses.
    pub fn covers(&self, child: &CapGrant) -> bool {
        match (self, child) {
            (CapGrant::Exact(a), CapGrant::Exact(b)) => a == b,
            (CapGrant::Prefix(p), CapGrant::Exact(b)) => b.starts_with(p.as_str()),
            (CapGrant::Prefix(p), CapGrant::Prefix(q)) => q.starts_with(p.as_str()),
            // An exact grant cannot cover a prefix (a prefix reaches strictly more).
            (CapGrant::Exact(_), CapGrant::Prefix(_)) => false,
        }
    }

    /// The wire/display string (`shell` / `fs-read:/workdir*`). A prefix renders
    /// with a trailing `*` so a reader sees it is resource-scoped.
    pub fn display(&self) -> String {
        match self {
            CapGrant::Exact(v) => v.clone(),
            CapGrant::Prefix(p) => format!("{p}*"),
        }
    }
}

/// Build the single caveat that grants exactly `caps` (all exact).
fn cap_caveat(caps: &[String]) -> Caveat {
    Caveat::FirstParty(Pred::AnyOf(
        caps.iter()
            .map(|c| Pred::AttrEq {
                key: CAP_KEY.to_string(),
                value: c.clone(),
            })
            .collect(),
    ))
}

/// Build the single caveat that grants a mix of exact + prefix [`CapGrant`]s.
fn grant_caveat(grants: &[CapGrant]) -> Caveat {
    Caveat::FirstParty(Pred::AnyOf(grants.iter().map(CapGrant::pred).collect()))
}

/// Mint a credential granting `caps`, optionally expiring at `until` (a unix
/// second / clock reading; `None` = no expiry).
pub fn mint_caps(
    root: &RootKey,
    caps: impl IntoIterator<Item = impl Into<String>>,
    until: Option<u64>,
) -> Credential {
    let caps: Vec<String> = caps.into_iter().map(Into::into).collect();
    let mut caveats = vec![cap_caveat(&caps)];
    if let Some(at) = until {
        caveats.push(Caveat::FirstParty(Pred::NotAfter { at }));
    }
    root.mint(caveats)
}

/// Narrow an existing credential to a subset of caps (and/or a tighter expiry).
/// Appends a confining `AnyOf` caveat — can only ever *remove* reach.
pub fn attenuate_caps(
    cred: Credential,
    caps: impl IntoIterator<Item = impl Into<String>>,
    until: Option<u64>,
) -> Credential {
    let caps: Vec<String> = caps.into_iter().map(Into::into).collect();
    let mut caveats = vec![cap_caveat(&caps)];
    if let Some(at) = until {
        caveats.push(Caveat::FirstParty(Pred::NotAfter { at }));
    }
    cred.attenuate(caveats)
}

/// Mint a credential granting a mix of exact + prefix [`CapGrant`]s (the
/// resource-scoped powerbox: per-tool AND per-resource authority in one signed
/// bundle), optionally expiring at `until`.
pub fn mint_grants(root: &RootKey, grants: &[CapGrant], until: Option<u64>) -> Credential {
    let mut caveats = vec![grant_caveat(grants)];
    if let Some(at) = until {
        caveats.push(Caveat::FirstParty(Pred::NotAfter { at }));
    }
    root.mint(caveats)
}

/// Narrow an existing credential to a subset of [`CapGrant`]s (the no-amplify
/// attenuation for the resource-scoped bundle). Appends a confining `AnyOf` — can
/// only ever *remove* reach.
pub fn attenuate_grants(cred: Credential, grants: &[CapGrant], until: Option<u64>) -> Credential {
    let mut caveats = vec![grant_caveat(grants)];
    if let Some(at) = until {
        caveats.push(Caveat::FirstParty(Pred::NotAfter { at }));
    }
    cred.attenuate(caveats)
}

/// Build the verification context for a request to `required_cap` at clock `now`.
pub fn cap_context(required_cap: &str, now: u64) -> Context {
    Context::new().at(now).attr(CAP_KEY, required_cap)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_prefix_grant_admits_under_it_and_refuses_outside() {
        let root = RootKey::from_seed([71u8; 32]);
        let cred = mint_grants(
            &root,
            &[
                CapGrant::Exact("shell".into()),
                CapGrant::Prefix("fs-read:/workdir".into()),
                CapGrant::Exact("http:api.github.com".into()),
            ],
            None,
        );
        let pubk = root.public();
        // Exact tool cap admits.
        assert!(cred.verify(&pubk, &cap_context("shell", 0)).is_ok());
        // A resource UNDER the prefix admits (per-resource scoping, cryptographic).
        assert!(
            cred.verify(&pubk, &cap_context("fs-read:/workdir/repo/Cargo.toml", 0))
                .is_ok()
        );
        // A resource OUTSIDE the prefix is refused.
        assert!(
            cred.verify(&pubk, &cap_context("fs-read:/etc/passwd", 0))
                .is_err()
        );
        // A different host is refused (per-host egress).
        assert!(
            cred.verify(&pubk, &cap_context("http:evil.example", 0))
                .is_err()
        );
    }

    #[test]
    fn attenuation_narrows_a_resource_prefix_no_amplify() {
        let root = RootKey::from_seed([72u8; 32]);
        let parent = mint_grants(&root, &[CapGrant::Prefix("fs-write:/workdir".into())], None);
        // Narrow to a SUBDIRECTORY only.
        let child = attenuate_grants(
            parent,
            &[CapGrant::Prefix("fs-write:/workdir/out".into())],
            None,
        );
        let pubk = root.public();
        // The narrowed subtree still admits.
        assert!(
            child
                .verify(&pubk, &cap_context("fs-write:/workdir/out/x", 0))
                .is_ok()
        );
        // A sibling the parent COULD reach is now refused (no-amplify, narrowed).
        assert!(
            child
                .verify(&pubk, &cap_context("fs-write:/workdir/other", 0))
                .is_err()
        );
    }

    #[test]
    fn covers_is_the_no_amplify_relation() {
        let shell = CapGrant::Exact("shell".into());
        let wd = CapGrant::Prefix("fs-read:/workdir".into());
        assert!(shell.covers(&CapGrant::Exact("shell".into())));
        assert!(!shell.covers(&CapGrant::Exact("http:x".into())));
        // A prefix covers an exact under it and a longer prefix.
        assert!(wd.covers(&CapGrant::Exact("fs-read:/workdir/a".into())));
        assert!(wd.covers(&CapGrant::Prefix("fs-read:/workdir/sub".into())));
        // It does NOT cover a broader prefix or a sibling tree.
        assert!(!wd.covers(&CapGrant::Prefix("fs-read:/".into())));
        assert!(!wd.covers(&CapGrant::Exact("fs-read:/etc".into())));
    }
}
