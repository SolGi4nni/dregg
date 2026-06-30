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

use crate::cred::{Caveat, Context, Credential, Pred, RootKey};

/// The request attribute key a capability is matched on.
pub const CAP_KEY: &str = "cap";

/// Build the single caveat that grants exactly `caps`.
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

/// Build the verification context for a request to `required_cap` at clock `now`.
pub fn cap_context(required_cap: &str, now: u64) -> Context {
    Context::new().at(now).attr(CAP_KEY, required_cap)
}
