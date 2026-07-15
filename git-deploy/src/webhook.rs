//! `webhook` — the push-triggered deploy receiver (a **reviewed-go seam**).
//!
//! This is a *library* seam, not a running server: it parses a git-host push payload into a
//! [`PushEvent`], verifies the payload's HMAC-SHA256 signature against a shared secret, and turns
//! an event into a [`DeploySpec`]. Standing up a public listener that calls these (binding a
//! port, terminating TLS, rate-limiting, the replay window) is an operator action — deliberately
//! not shipped here, so an untrusted public surface is never stood up implicitly.
//!
//! The verification is fail-closed: an unsigned or wrong-signature payload is refused before it
//! becomes a deploy, so a forged push cannot trigger a build.

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::workflow::DeploySpec;

/// A normalized push event: enough to source a [`DeploySpec`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PushEvent {
    /// The repo to clone (an `https`/`file` URL — the clone step re-validates the transport).
    pub repo_url: String,
    /// The pushed ref (branch/tag), if the payload carried one.
    pub git_ref: Option<String>,
    /// The pushed commit hash, if the payload carried one.
    pub commit: Option<String>,
    /// Who pushed (best-effort, for the audit trail).
    pub pusher: Option<String>,
}

/// Parse a git-host push payload (JSON) into a [`PushEvent`]. Tolerant of the common shapes:
/// a `repository.clone_url`/`repository.url`/`repo_url` for the source, `ref`, and
/// `after`/`commit`/`head_commit.id` for the commit. An unparseable payload (no repo URL) is an
/// error.
pub fn parse_push_event(body: &[u8]) -> anyhow::Result<PushEvent> {
    let v: serde_json::Value =
        serde_json::from_slice(body).map_err(|e| anyhow::anyhow!("parse push payload: {e}"))?;

    let repo_url = v
        .get("repository")
        .and_then(|r| {
            r.get("clone_url")
                .or_else(|| r.get("url"))
                .or_else(|| r.get("git_http_url"))
        })
        .or_else(|| v.get("repo_url"))
        .and_then(|s| s.as_str())
        .map(str::to_string)
        .ok_or_else(|| anyhow::anyhow!("push payload has no repository URL"))?;

    let git_ref = v.get("ref").and_then(|s| s.as_str()).map(strip_ref_prefix);
    let commit = v
        .get("after")
        .or_else(|| v.get("commit"))
        .or_else(|| v.get("head_commit").and_then(|h| h.get("id")))
        .and_then(|s| s.as_str())
        .filter(|s| !s.is_empty() && *s != "0000000000000000000000000000000000000000")
        .map(str::to_string);
    let pusher = v
        .get("pusher")
        .and_then(|p| p.get("name").or_else(|| p.get("email")))
        .or_else(|| v.get("sender").and_then(|s| s.get("login")))
        .and_then(|s| s.as_str())
        .map(str::to_string);

    Ok(PushEvent {
        repo_url,
        git_ref,
        commit,
        pusher,
    })
}

/// Turn `event` into a [`DeploySpec`] publishing under `site_name` for `owner` with the given
/// prepaid budget. The event's commit (when present) pins the deploy so the build is on exactly
/// the pushed source; otherwise the ref (or the default branch) is used.
pub fn deploy_spec_from_push(
    event: &PushEvent,
    site_name: impl Into<String>,
    owner: impl Into<String>,
    budget_units: i64,
    cost_per_step: i64,
) -> DeploySpec {
    let pin = event.commit.clone().or_else(|| event.git_ref.clone());
    DeploySpec {
        repo_url: event.repo_url.clone(),
        git_ref: pin,
        site_name: site_name.into(),
        owner: owner.into(),
        budget_units,
        cost_per_step,
        build_override: None,
    }
}

/// Verify a webhook payload's HMAC-SHA256 signature against `secret`. `signature` may carry a
/// `sha256=` prefix (the common git-host format). Fail-closed: a malformed or mismatched
/// signature returns `false`. The comparison is constant-time over the digest bytes.
pub fn verify_signature(secret: &[u8], body: &[u8], signature: &str) -> bool {
    let want = signature.trim();
    let want = want.strip_prefix("sha256=").unwrap_or(want);
    let Some(want_bytes) = decode_hex(want) else {
        return false;
    };
    let got = hmac_sha256(secret, body);
    constant_time_eq(&got, &want_bytes)
}

/// The hex-encoded HMAC-SHA256 of `body` under `secret` (the value a sender puts in the
/// `sha256=` signature header).
pub fn sign(secret: &[u8], body: &[u8]) -> String {
    encode_hex(&hmac_sha256(secret, body))
}

/// HMAC-SHA256(key, msg) per RFC 2104.
fn hmac_sha256(key: &[u8], msg: &[u8]) -> [u8; 32] {
    const BLOCK: usize = 64;
    let mut k = [0u8; BLOCK];
    if key.len() > BLOCK {
        let d = Sha256::digest(key);
        k[..32].copy_from_slice(&d);
    } else {
        k[..key.len()].copy_from_slice(key);
    }
    let mut ipad = [0x36u8; BLOCK];
    let mut opad = [0x5cu8; BLOCK];
    for i in 0..BLOCK {
        ipad[i] ^= k[i];
        opad[i] ^= k[i];
    }
    let mut inner = Sha256::new();
    inner.update(ipad);
    inner.update(msg);
    let inner = inner.finalize();
    let mut outer = Sha256::new();
    outer.update(opad);
    outer.update(inner);
    let mut out = [0u8; 32];
    out.copy_from_slice(&outer.finalize());
    out
}

fn strip_ref_prefix(r: &str) -> String {
    r.strip_prefix("refs/heads/")
        .or_else(|| r.strip_prefix("refs/tags/"))
        .unwrap_or(r)
        .to_string()
}

fn decode_hex(s: &str) -> Option<Vec<u8>> {
    if s.len() % 2 != 0 {
        return None;
    }
    let mut out = Vec::with_capacity(s.len() / 2);
    let b = s.as_bytes();
    let mut i = 0;
    while i < b.len() {
        let hi = (b[i] as char).to_digit(16)?;
        let lo = (b[i + 1] as char).to_digit(16)?;
        out.push(((hi << 4) | lo) as u8);
        i += 2;
    }
    Some(out)
}

fn encode_hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

fn constant_time_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut diff = 0u8;
    for (x, y) in a.iter().zip(b.iter()) {
        diff |= x ^ y;
    }
    diff == 0
}

#[cfg(test)]
mod tests {
    use super::*;

    const GITHUB_PUSH: &str = r#"{
        "ref": "refs/heads/main",
        "after": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        "repository": { "clone_url": "https://example.com/acme/site.git", "url": "x" },
        "pusher": { "name": "ember" }
    }"#;

    #[test]
    fn parses_a_github_style_push() {
        let ev = parse_push_event(GITHUB_PUSH.as_bytes()).unwrap();
        assert_eq!(ev.repo_url, "https://example.com/acme/site.git");
        assert_eq!(ev.git_ref.as_deref(), Some("main"));
        assert_eq!(
            ev.commit.as_deref(),
            Some("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
        );
        assert_eq!(ev.pusher.as_deref(), Some("ember"));
    }

    #[test]
    fn push_without_a_repo_url_is_an_error() {
        assert!(parse_push_event(br#"{"ref":"refs/heads/main"}"#).is_err());
    }

    #[test]
    fn spec_from_push_pins_the_commit() {
        let ev = parse_push_event(GITHUB_PUSH.as_bytes()).unwrap();
        let spec = deploy_spec_from_push(&ev, "blog", "agent:ember", 100, 1);
        assert_eq!(spec.repo_url, "https://example.com/acme/site.git");
        assert_eq!(
            spec.git_ref.as_deref(),
            Some("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
        );
        assert_eq!(spec.site_name, "blog");
        assert_eq!(spec.budget_units, 100);
    }

    /// HMAC-SHA256 matches a known RFC-style vector (`key`/`The quick brown fox...`).
    #[test]
    fn hmac_matches_known_vector() {
        // Standard test vector: HMAC-SHA256("key", "The quick brown fox jumps over the lazy dog").
        let mac = sign(b"key", b"The quick brown fox jumps over the lazy dog");
        assert_eq!(
            mac,
            "f7bc83f430538424b13298e6aa6fb143ef4d59a14946175997479dbc2d1a3cd8"
        );
    }

    #[test]
    fn signature_roundtrips_and_is_fail_closed() {
        let secret = b"deploy-hook-secret";
        let body = GITHUB_PUSH.as_bytes();
        let good = sign(secret, body);
        assert!(
            verify_signature(secret, body, &good),
            "correct signature accepted"
        );
        assert!(
            verify_signature(secret, body, &format!("sha256={good}")),
            "prefixed accepted"
        );
        assert!(
            !verify_signature(secret, body, "sha256=deadbeef"),
            "wrong signature refused"
        );
        assert!(
            !verify_signature(secret, body, ""),
            "empty signature refused"
        );
        assert!(
            !verify_signature(b"wrong-secret", body, &good),
            "wrong secret refused"
        );
    }
}
