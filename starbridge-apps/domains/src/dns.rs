//! The DNS challenge seam — the injected [`DnsResolver`] trait, the deterministic
//! [`MockDns`] test instance, the challenge-satisfaction check, domain validity, and
//! the deterministic challenge nonce.
//!
//! Verification is driven through the [`DnsResolver`] trait so the check is a real
//! DNS query in production (a host-wired client implementing the sync trait) and a
//! deterministic [`MockDns`] in tests — the bind -> challenge -> verify round-trip
//! proves locally with no live DNS and no real cert. The trait is kept minimal: only
//! the two record types a challenge needs (TXT and CNAME).
//!
//! A production resolver implements [`DnsResolver`] over a real DNS client (bridging
//! its async lookups to the sync trait the bind/verify state machine and the gateway
//! routing use). This crate ships no live client — the resolver is the injected seam,
//! wired by the host — so the crate stays portable and dependency-light.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

/// The DNS label a TXT challenge is published under: `_dregg-verify.<domain>`.
pub const TXT_CHALLENGE_PREFIX: &str = "_dregg-verify.";

/// The environment variable that overrides the hosting apex when set — so an operator
/// picks the deployment's apex (`dregg.fg-goose.online`, `dregg.net`, an arbitrary
/// domain) without a rebuild. Empty/unset falls back to [`DEFAULT_HOSTING_APEX`].
pub const HOSTING_APEX_ENV: &str = "DREGG_HOSTING_APEX";

/// The fallback platform apex when nothing is configured. A generic placeholder — the
/// real deployment apex is supplied by [`HOSTING_APEX_ENV`] or
/// [`DomainRegistry::with_apex`](crate::DomainRegistry::with_apex), never hardcoded to
/// one product's domain.
pub const DEFAULT_HOSTING_APEX: &str = "acme.dev";

/// Normalize an apex to its comparison form: trimmed, no trailing dot, lowercased.
/// An empty result is not a usable apex (the caller substitutes the default).
pub fn normalize_apex(apex: &str) -> String {
    apex.trim().trim_end_matches('.').to_ascii_lowercase()
}

/// The apex custom domains bind *onto* — a binding's site `<name>` serves at
/// `<name>.<apex>`, and a CNAME challenge points the custom domain here. A `<x>.<apex>`
/// host is the platform wildcard path, not a "custom" domain, so it is refused by
/// [`is_valid_domain`].
///
/// Resolution order: the [`HOSTING_APEX_ENV`] environment variable (normalized), else
/// [`DEFAULT_HOSTING_APEX`]. A [`DomainRegistry`](crate::DomainRegistry) reads this at
/// construction and can be overridden explicitly with
/// [`with_apex`](crate::DomainRegistry::with_apex), so the apex is configuration, not a
/// compile-time constant.
pub fn apex_from_env() -> String {
    match std::env::var(HOSTING_APEX_ENV) {
        Ok(v) => {
            let n = normalize_apex(&v);
            if n.is_empty() {
                DEFAULT_HOSTING_APEX.to_string()
            } else {
                n
            }
        }
        Err(_) => DEFAULT_HOSTING_APEX.to_string(),
    }
}

/// Which DNS record proves control of a custom domain.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ChallengeMethod {
    /// Publish a TXT record at `_dregg-verify.<domain>` equal to the nonce.
    Txt,
    /// Point `<domain>` (CNAME) at `<site>.<apex>`.
    Cname,
}

impl ChallengeMethod {
    /// The stable numeric code (for the field-image of a method, if committed).
    pub fn code(self) -> u64 {
        match self {
            ChallengeMethod::Txt => 0,
            ChallengeMethod::Cname => 1,
        }
    }
}

/// Whether a binding has proven control of its domain yet — the field-imaged
/// `verification_state` a domain cell commits (`Monotonic`, one-way).
///
/// The three codes are **strictly increasing** (`0 < 1 < 2`), so every legal
/// transition is a `Monotonic` advance the executor admits and every illegal one
/// (un-verify, un-revoke) is a refused rewind. `Revoked` is deliberately the
/// *highest* code: a domain that loses control (DNS re-pointed, owner takedown,
/// abuse) advances **past** `Verified` to a terminal state that no longer routes —
/// it is NOT an un-verify (which `Monotonic` would refuse), it is a distinct
/// forward transition. Once revoked, a binding can never be re-verified on the same
/// cell; the owner rebinds a fresh challenge instead.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum VerificationState {
    /// Bound, challenge issued, control not yet proven. Not routed; no cert.
    Pending,
    /// Control proven — the binding routes and is eligible for a certificate.
    Verified,
    /// Control was proven but has since been withdrawn — a periodic re-validation
    /// found the DNS record gone / re-pointed, the owner unbound, or an operator
    /// took the domain down for abuse. Terminal and one-way (a `Monotonic` advance
    /// past `Verified`, never a rewind): it stops routing and blocks cert renewal,
    /// and cannot be flipped back to `Verified` on the same cell.
    Revoked,
}

impl VerificationState {
    /// The stable numeric code committed at [`VERIFICATION_STATE_SLOT`](crate::VERIFICATION_STATE_SLOT):
    /// `0` pending, `1` verified, `2` revoked. The `Monotonic` caveat makes the
    /// sequence `0 -> 1 -> 2` one-way (no un-verify, no un-revoke).
    pub fn code(self) -> u64 {
        match self {
            VerificationState::Pending => 0,
            VerificationState::Verified => 1,
            VerificationState::Revoked => 2,
        }
    }

    /// Reconstruct a state from its committed numeric code (the inverse of
    /// [`code`](Self::code)); an unknown code reads as `None`.
    pub fn from_code(code: u64) -> Option<VerificationState> {
        match code {
            0 => Some(VerificationState::Pending),
            1 => Some(VerificationState::Verified),
            2 => Some(VerificationState::Revoked),
            _ => None,
        }
    }

    /// Whether this state is [`VerificationState::Verified`] — the ONLY state that
    /// routes and mints a certificate. `Pending` and `Revoked` both read `false`.
    pub fn is_verified(self) -> bool {
        matches!(self, VerificationState::Verified)
    }

    /// Whether control has been permanently withdrawn ([`VerificationState::Revoked`]).
    pub fn is_revoked(self) -> bool {
        matches!(self, VerificationState::Revoked)
    }
}

/// The DNS record that proves control of a custom domain — what the owner publishes
/// and what the verify path checks for.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DnsChallenge {
    /// TXT or CNAME.
    pub record_type: ChallengeMethod,
    /// The DNS name the record lives at (`_dregg-verify.<domain>` for TXT, the
    /// `<domain>` itself for CNAME).
    pub record_name: String,
    /// The value the record must carry (the nonce for TXT, `<site>.<apex>` for CNAME).
    pub expected_value: String,
}

/// A DNS resolver the verify check queries. The production instance is a host-wired
/// client over live DNS; tests use [`MockDns`]. Kept minimal — only the two record
/// types a challenge needs.
pub trait DnsResolver {
    /// The TXT values published at `name` (empty if none / NXDOMAIN).
    fn txt(&self, name: &str) -> Vec<String>;
    /// The CNAME target of `name`, if any. The returned target may carry a trailing
    /// dot (FQDN form); the verify check compares case-insensitively without it.
    fn cname(&self, name: &str) -> Option<String>;
}

/// An in-memory [`DnsResolver`] for tests: a fixed set of TXT and CNAME records.
/// Drives the verify path deterministically with no live DNS.
#[derive(Debug, Default, Clone)]
pub struct MockDns {
    txt: BTreeMap<String, Vec<String>>,
    cname: BTreeMap<String, String>,
}

impl MockDns {
    /// An empty resolver (no records — every lookup misses, so every verify is
    /// [`ChallengeUnmet`](crate::DomainError::ChallengeUnmet)).
    pub fn new() -> MockDns {
        MockDns::default()
    }

    /// Add a TXT value at `name`.
    pub fn with_txt(mut self, name: &str, value: &str) -> MockDns {
        self.txt
            .entry(name.to_ascii_lowercase())
            .or_default()
            .push(value.to_string());
        self
    }

    /// Add a CNAME target at `name`.
    pub fn with_cname(mut self, name: &str, target: &str) -> MockDns {
        self.cname
            .insert(name.to_ascii_lowercase(), target.to_string());
        self
    }
}

impl DnsResolver for MockDns {
    fn txt(&self, name: &str) -> Vec<String> {
        self.txt
            .get(&name.to_ascii_lowercase())
            .cloned()
            .unwrap_or_default()
    }
    fn cname(&self, name: &str) -> Option<String> {
        self.cname.get(&name.to_ascii_lowercase()).cloned()
    }
}

/// Whether a DNS `challenge` is satisfied by `dns`. TXT: any published value equals
/// the nonce. CNAME: the target (trailing dot tolerated) matches `<site>.<apex>`
/// case-insensitively. An unreachable resolver (empty answer) reads as "no proof" —
/// never a false positive.
pub fn challenge_satisfied(challenge: &DnsChallenge, dns: &impl DnsResolver) -> bool {
    match challenge.record_type {
        ChallengeMethod::Txt => dns
            .txt(&challenge.record_name)
            .iter()
            .any(|v| v == &challenge.expected_value),
        ChallengeMethod::Cname => dns
            .cname(&challenge.record_name)
            .map(|t| {
                t.trim_end_matches('.')
                    .eq_ignore_ascii_case(&challenge.expected_value)
            })
            .unwrap_or(false),
    }
}

/// Whether `domain` is a usable custom domain under the given `apex`: a multi-label
/// FQDN whose labels are each valid DNS labels, and which is NOT the platform `apex`
/// or a `<x>.<apex>` host (that is the wildcard hosting path, served without a
/// binding). The `apex` is the deployment's configured apex (see [`apex_from_env`] /
/// [`DomainRegistry::with_apex`](crate::DomainRegistry::with_apex)).
pub fn is_valid_domain(domain: &str, apex: &str) -> bool {
    let domain = domain.trim().trim_end_matches('.').to_ascii_lowercase();
    let apex = normalize_apex(apex);
    if domain.is_empty() || domain.len() > 253 {
        return false;
    }
    // A custom domain owns its own apex; the platform wildcard is not "custom".
    if !apex.is_empty() && (domain == apex || domain.ends_with(&format!(".{apex}"))) {
        return false;
    }
    let labels: Vec<&str> = domain.split('.').collect();
    if labels.len() < 2 {
        return false;
    }
    labels.iter().all(|l| is_valid_label(l))
}

/// A single DNS label: non-empty, `<= 63`, `[a-z0-9-]`, not edge-`-`. Used for both a
/// domain's per-label validity and a bound site `<name>`.
pub fn is_valid_label(label: &str) -> bool {
    let label = label.to_ascii_lowercase();
    if label.is_empty() || label.len() > 63 {
        return false;
    }
    if label.starts_with('-') || label.ends_with('-') {
        return false;
    }
    label
        .bytes()
        .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-')
}

/// The number of CSPRNG bytes behind a challenge nonce (256 bits — unguessable).
const CHALLENGE_ENTROPY_BYTES: usize = 32;

/// A **cryptographically-random** challenge nonce — the value the owner must place
/// in DNS to prove control. 256 bits of OS entropy ([`getrandom`]) rendered as
/// `dregg-verify-<64-hex>`, domain-separated by hashing the entropy together with
/// `(domain, owner)` so the wire form is bound to the binding it proves.
///
/// This is the security-critical replacement for the former deterministic FNV nonce:
/// a DNS control challenge MUST be unpredictable, or an attacker who knows the public
/// `(domain, owner, seq)` inputs could precompute a victim's expected value and
/// publish it (or race the bind) to pre-satisfy the challenge. With 256 bits of
/// CSPRNG entropy the value is unguessable and un-precomputable.
///
/// Falls back to [`challenge_token_from_commitment`] over a best-effort entropy mix
/// only if the OS RNG is unavailable (it essentially never is); the fallback still
/// folds in `getrandom`'s partial output when present, so it never degrades to the
/// old fully-predictable form.
pub fn random_challenge_token(domain: &str, owner: &str) -> String {
    let mut entropy = [0u8; CHALLENGE_ENTROPY_BYTES];
    match getrandom::fill(&mut entropy) {
        Ok(()) => challenge_token_from_commitment(domain, owner, &entropy),
        Err(_) => {
            // OS RNG unavailable: fold whatever high-resolution, per-process varying
            // material we can reach. Not a substitute for CSPRNG, but never the old
            // attacker-computable `(domain, owner, seq)`-only form.
            use std::time::{SystemTime, UNIX_EPOCH};
            let nanos = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0);
            let mut mix = Vec::with_capacity(48);
            mix.extend_from_slice(&nanos.to_le_bytes());
            mix.extend_from_slice(&(std::process::id() as u64).to_le_bytes());
            mix.extend_from_slice(&entropy);
            challenge_token_from_commitment(domain, owner, &mix)
        }
    }
}

/// A challenge nonce **drawn from a cell commitment** (or any unpredictable seed) —
/// the shape the per-domain cell weld uses. `commitment` is an unpredictable value
/// tied to the binding's cell (its post-register state root / turn-receipt hash);
/// this hashes it under a domain-separated key together with `(domain, owner)` and
/// renders the first 32 bytes as `dregg-verify-<64-hex>`. Because the seed is
/// unpredictable to anyone who cannot see the committed cell, the resulting nonce
/// is un-precomputable — the property the FNV placeholder lacked.
pub fn challenge_token_from_commitment(domain: &str, owner: &str, commitment: &[u8]) -> String {
    let mut buf = Vec::with_capacity(commitment.len() + domain.len() + owner.len() + 2);
    buf.extend_from_slice(domain.trim().to_ascii_lowercase().as_bytes());
    buf.push(0);
    buf.extend_from_slice(owner.as_bytes());
    buf.push(0);
    buf.extend_from_slice(commitment);
    let digest = blake3::derive_key("starbridge-domains-challenge-nonce-v1", &buf);
    let mut hex = String::with_capacity(13 + 64);
    hex.push_str("dregg-verify-");
    for b in digest.iter() {
        use std::fmt::Write;
        let _ = write!(hex, "{b:02x}");
    }
    hex
}

/// A **deterministic** challenge nonce for `(domain, owner, seq)` — FNV-1a/64 hex.
///
/// DEPRECATED for the live bind path: a deterministic nonce over public inputs is
/// precomputable, so `bind` now issues [`random_challenge_token`] instead. Retained
/// only for tests and for re-deriving a legacy binding's expected value; NEVER use
/// it to mint a fresh challenge.
pub fn challenge_token(domain: &str, owner: &str, seq: u64) -> String {
    const OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
    const PRIME: u64 = 0x0000_0100_0000_01b3;
    let mut h: u64 = OFFSET;
    let mut mix = |bytes: &[u8]| {
        for &b in bytes {
            h ^= b as u64;
            h = h.wrapping_mul(PRIME);
        }
        h ^= 0xff;
        h = h.wrapping_mul(PRIME);
    };
    mix(domain.as_bytes());
    mix(owner.as_bytes());
    mix(&seq.to_le_bytes());
    format!("dregg-verify-{h:016x}")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn domain_validity() {
        let apex = DEFAULT_HOSTING_APEX;
        assert!(is_valid_domain("blog.example.com", apex));
        assert!(is_valid_domain("shop.example.co.uk", apex));
        assert!(!is_valid_domain("", apex));
        assert!(!is_valid_domain("localhost", apex)); // single label
        assert!(!is_valid_domain("has space.com", apex));
        assert!(!is_valid_domain("-bad.com", apex));
        assert!(!is_valid_domain("bad-.com", apex));
        // The platform wildcard path is not a "custom" domain.
        assert!(!is_valid_domain(apex, apex));
        assert!(!is_valid_domain(&format!("blog.{apex}"), apex));
    }

    #[test]
    fn apex_is_configurable_not_hardcoded() {
        // A different deployment apex reclassifies which hosts are "custom".
        let apex = "dregg.fg-goose.online";
        // Under this apex, a `.dregg.fg-goose.online` host is the platform wildcard.
        assert!(!is_valid_domain(apex, apex));
        assert!(!is_valid_domain("launch.dregg.fg-goose.online", apex));
        // A truly custom domain is still valid, and the old default apex is now just
        // an ordinary custom domain (nothing is hardcoded to it).
        assert!(is_valid_domain("blog.example.com", apex));
        assert!(is_valid_domain(&format!("x.{DEFAULT_HOSTING_APEX}"), apex));
    }

    #[test]
    fn txt_challenge_is_satisfied_only_by_the_exact_nonce() {
        let challenge = DnsChallenge {
            record_type: ChallengeMethod::Txt,
            record_name: "_dregg-verify.blog.example.com".into(),
            expected_value: "dregg-verify-abc123".into(),
        };
        // No record → unmet.
        assert!(!challenge_satisfied(&challenge, &MockDns::new()));
        // A wrong value → unmet.
        let wrong = MockDns::new().with_txt(&challenge.record_name, "dregg-verify-WRONG");
        assert!(!challenge_satisfied(&challenge, &wrong));
        // The exact nonce → met.
        let right = MockDns::new().with_txt(&challenge.record_name, &challenge.expected_value);
        assert!(challenge_satisfied(&challenge, &right));
    }

    #[test]
    fn cname_challenge_tolerates_the_trailing_dot() {
        let challenge = DnsChallenge {
            record_type: ChallengeMethod::Cname,
            record_name: "www.example.com".into(),
            expected_value: "blog.acme.dev".into(),
        };
        let wrong = MockDns::new().with_cname("www.example.com", "evil.acme.dev");
        assert!(!challenge_satisfied(&challenge, &wrong));
        let right = MockDns::new().with_cname("www.example.com", "blog.acme.dev.");
        assert!(challenge_satisfied(&challenge, &right));
    }

    #[test]
    fn challenge_token_is_deterministic_and_owner_seq_bound() {
        let a = challenge_token("blog.example.com", "dregg:alice", 0);
        assert_eq!(a, challenge_token("blog.example.com", "dregg:alice", 0));
        assert!(a.starts_with("dregg-verify-"));
        // Different owner / seq → different nonce.
        assert_ne!(a, challenge_token("blog.example.com", "dregg:bob", 0));
        assert_ne!(a, challenge_token("blog.example.com", "dregg:alice", 1));
    }

    #[test]
    fn random_challenge_token_is_unpredictable_and_well_formed() {
        // 256-bit CSPRNG nonce: two draws for the SAME public inputs differ (so it is
        // not precomputable from `(domain, owner)`), and it is 32 hex-bytes long.
        let a = random_challenge_token("blog.example.com", "dregg:alice");
        let b = random_challenge_token("blog.example.com", "dregg:alice");
        assert_ne!(a, b, "a random nonce must not repeat for the same inputs");
        assert!(a.starts_with("dregg-verify-"));
        assert_eq!(a.len(), "dregg-verify-".len() + 64, "256-bit hex nonce");
        assert!(
            a["dregg-verify-".len()..]
                .bytes()
                .all(|c| c.is_ascii_hexdigit())
        );
    }

    #[test]
    fn commitment_nonce_is_bound_to_seed_and_binding() {
        // The commitment-derived nonce is deterministic in its seed, but a different
        // seed / domain / owner yields a different value — un-precomputable without
        // the (unpredictable) commitment.
        let seed = [9u8; 32];
        let a = challenge_token_from_commitment("blog.example.com", "dregg:alice", &seed);
        assert_eq!(
            a,
            challenge_token_from_commitment("blog.example.com", "dregg:alice", &seed)
        );
        assert_ne!(
            a,
            challenge_token_from_commitment("blog.example.com", "dregg:alice", &[8u8; 32])
        );
        assert_ne!(
            a,
            challenge_token_from_commitment("other.example.com", "dregg:alice", &seed)
        );
        assert_ne!(
            a,
            challenge_token_from_commitment("blog.example.com", "dregg:bob", &seed)
        );
    }

    #[test]
    fn verification_state_codes_are_stable_and_ordered() {
        assert_eq!(VerificationState::Pending.code(), 0);
        assert_eq!(VerificationState::Verified.code(), 1);
        assert_eq!(VerificationState::Revoked.code(), 2);
        // Strictly increasing: every legal transition is a Monotonic advance.
        assert!(VerificationState::Pending.code() < VerificationState::Verified.code());
        assert!(VerificationState::Verified.code() < VerificationState::Revoked.code());
        assert!(VerificationState::Verified.is_verified());
        assert!(!VerificationState::Pending.is_verified());
        // Revoked does NOT route and IS revoked.
        assert!(!VerificationState::Revoked.is_verified());
        assert!(VerificationState::Revoked.is_revoked());
        for s in [
            VerificationState::Pending,
            VerificationState::Verified,
            VerificationState::Revoked,
        ] {
            assert_eq!(VerificationState::from_code(s.code()), Some(s));
        }
        assert_eq!(VerificationState::from_code(3), None);
    }
}
