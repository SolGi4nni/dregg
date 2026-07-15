//! `admission` — the identity + capability gate in front of a durable workflow.
//!
//! The engine hosts other people's work and charges a lease for it. Before this
//! module the lease was prose: `lease_id` was literally the instance name, an
//! unauthenticated string, and `budget_units` was a self-asserted integer in the
//! input JSON. Anyone who could name an instance could run it and charge it. That is
//! the biggest "demo, not production" tell in the crate — the whole project's
//! through-line is *attenuable proof-carrying tokens* (macaroons / biscuits), and the
//! hosting substrate authorized nothing.
//!
//! This module makes admission a **capability check**: a [`LeaseAuthority`] (the
//! settlement rail that funds leases) issues a [`SignedGrant`] binding a specific
//! `lease_id` to a funded `budget_units` and an expiry. The host verifies the grant's
//! MAC (constant-time), its expiry, and that it authorizes *this* run before the
//! workflow may start. An unsigned or mismatched grant is refused — you can no longer
//! run a workload just by naming it.
//!
//! ## What this is and is not
//!
//! The grant is a symmetric-key capability: a keyed BLAKE3 MAC over the grant's
//! canonical bytes, the same shape (an unforgeable authenticated token) the project's
//! macaroon/biscuit layer takes further. It is deliberately self-contained — it does
//! not drag the full `hosted-lease` / `starbridge-execution-lease` cell stack into
//! this standalone durable-store workspace. In the composed system, the
//! [`LeaseAuthority`] is that funded-lease cell: `verify` is the point where a real
//! deployment checks the grant against a funded account and a not-yet-lapsed lease.
//! The engine's job is to *refuse to run without a verified grant*; this is that gate.

use serde::{Deserialize, Serialize};

/// The claims a lease authority signs: this grant authorizes running a workload under
/// exactly `lease_id`, charging up to `budget_units`, until `not_after_unix`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LeaseGrant {
    /// The instance / lease id this grant authorizes. The workflow MUST run under this
    /// id — a grant for lease "a" cannot start instance "b".
    pub lease_id: String,
    /// The funded ceiling, in meter units. The workflow's declared budget must not
    /// exceed this (a run may under-spend a grant, never over-spend it).
    pub budget_units: i64,
    /// Unix-seconds expiry. A grant presented at or after this instant is refused.
    pub not_after_unix: u64,
    /// A unique token id — an anti-replay / audit handle chosen by the issuer.
    pub nonce: String,
}

impl LeaseGrant {
    /// The canonical, length-framed byte encoding the MAC is computed over. Framing is
    /// explicit (each field length-prefixed) so no field boundary is ambiguous and the
    /// bytes never depend on JSON/serde ordering.
    fn canonical_bytes(&self) -> Vec<u8> {
        fn put_str(out: &mut Vec<u8>, s: &str) {
            out.extend_from_slice(&(s.len() as u64).to_le_bytes());
            out.extend_from_slice(s.as_bytes());
        }
        let mut out = Vec::new();
        out.extend_from_slice(b"durable-workflow/lease-grant/v1\0");
        put_str(&mut out, &self.lease_id);
        out.extend_from_slice(&self.budget_units.to_le_bytes());
        out.extend_from_slice(&self.not_after_unix.to_le_bytes());
        put_str(&mut out, &self.nonce);
        out
    }
}

/// A grant plus the authority's MAC over it. The `mac` is lowercase hex of a 32-byte
/// keyed BLAKE3 tag; it is what makes the grant unforgeable without the lease key.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SignedGrant {
    pub grant: LeaseGrant,
    /// Lowercase hex of the 32-byte keyed-BLAKE3 MAC over `grant.canonical_bytes()`.
    pub mac: String,
}

/// Why admission refused a run. Every variant is a *refusal to run*, never a warning.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AdmissionError {
    /// The MAC did not verify under the authority key — a forged or tampered grant.
    BadSignature,
    /// The grant's `not_after_unix` is in the past.
    Expired { not_after_unix: u64, now_unix: u64 },
    /// The grant does not authorize the instance the caller asked to run.
    LeaseMismatch { granted: String, requested: String },
    /// The workload's declared budget exceeds the funded grant ceiling.
    OverBudget { declared: i64, granted: i64 },
    /// The grant is structurally invalid (empty lease id, non-hex MAC, ...).
    Malformed(String),
}

impl std::fmt::Display for AdmissionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AdmissionError::BadSignature => write!(f, "lease grant signature did not verify"),
            AdmissionError::Expired {
                not_after_unix,
                now_unix,
            } => write!(
                f,
                "lease grant expired at {not_after_unix} (now {now_unix})"
            ),
            AdmissionError::LeaseMismatch { granted, requested } => write!(
                f,
                "lease grant authorizes `{granted}`, not requested instance `{requested}`"
            ),
            AdmissionError::OverBudget { declared, granted } => write!(
                f,
                "workload declares budget {declared} > funded grant ceiling {granted}"
            ),
            AdmissionError::Malformed(m) => write!(f, "malformed lease grant: {m}"),
        }
    }
}

impl std::error::Error for AdmissionError {}

/// The lease-issuing authority: holds the 32-byte MAC key. In the composed system this
/// is the funded-lease settlement rail; here it is the self-contained signer/verifier.
///
/// Construct from a shared key ([`LeaseAuthority::from_key`]) both the issuer and the
/// host hold, or freshly at random ([`LeaseAuthority::generate`]).
#[derive(Clone)]
pub struct LeaseAuthority {
    key: [u8; 32],
}

impl LeaseAuthority {
    /// Build from a shared 32-byte key.
    pub fn from_key(key: [u8; 32]) -> LeaseAuthority {
        LeaseAuthority { key }
    }

    /// A fresh random authority key (OS CSPRNG). Both sides that must agree should
    /// instead share one key via [`LeaseAuthority::from_key`].
    pub fn generate() -> LeaseAuthority {
        let mut key = [0u8; 32];
        getrandom::fill(&mut key).expect("OS CSPRNG");
        LeaseAuthority { key }
    }

    fn tag(&self, grant: &LeaseGrant) -> [u8; 32] {
        *blake3::keyed_hash(&self.key, &grant.canonical_bytes()).as_bytes()
    }

    /// Issue a signed grant for `grant`'s claims.
    pub fn issue(&self, grant: LeaseGrant) -> SignedGrant {
        let mac = hex_lower(&self.tag(&grant));
        SignedGrant { grant, mac }
    }

    /// Verify a signed grant at wall-clock `now_unix`. Constant-time MAC compare, then
    /// expiry and structural checks. On success returns a reference to the verified
    /// claims; the caller then binds them to a specific run with
    /// [`SignedGrant`]-level admission ([`admit`]).
    pub fn verify(&self, sg: &SignedGrant, now_unix: u64) -> Result<(), AdmissionError> {
        if sg.grant.lease_id.is_empty() {
            return Err(AdmissionError::Malformed("empty lease id".into()));
        }
        let presented = hex_decode_32(&sg.mac)
            .map_err(|_| AdmissionError::Malformed("mac is not 32 hex bytes".into()))?;
        let expected = self.tag(&sg.grant);
        // Constant-time compare: never leak how many leading bytes matched.
        if !constant_time_eq::constant_time_eq_32(&presented, &expected) {
            return Err(AdmissionError::BadSignature);
        }
        if now_unix >= sg.grant.not_after_unix {
            return Err(AdmissionError::Expired {
                not_after_unix: sg.grant.not_after_unix,
                now_unix,
            });
        }
        Ok(())
    }
}

/// Admit (or refuse) running `requested_instance` with declared `declared_budget`
/// under `grant`, verified by `authority` at `now_unix`. This is the single gate the
/// authenticated entry points call: it verifies the MAC + expiry AND binds the grant
/// to *this* run (the lease id and budget must match), so a valid grant for one lease
/// cannot authorize another.
pub fn admit(
    authority: &LeaseAuthority,
    grant: &SignedGrant,
    requested_instance: &str,
    declared_budget: i64,
    now_unix: u64,
) -> Result<(), AdmissionError> {
    authority.verify(grant, now_unix)?;
    if grant.grant.lease_id != requested_instance {
        return Err(AdmissionError::LeaseMismatch {
            granted: grant.grant.lease_id.clone(),
            requested: requested_instance.to_string(),
        });
    }
    if declared_budget > grant.grant.budget_units {
        return Err(AdmissionError::OverBudget {
            declared: declared_budget,
            granted: grant.grant.budget_units,
        });
    }
    Ok(())
}

/// Current wall-clock unix seconds — the `now` an online host passes to [`admit`].
pub fn now_unix() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

fn hex_lower(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for b in bytes {
        s.push(char::from_digit((b >> 4) as u32, 16).unwrap());
        s.push(char::from_digit((b & 0xf) as u32, 16).unwrap());
    }
    s
}

fn hex_decode_32(s: &str) -> Result<[u8; 32], ()> {
    if s.len() != 64 {
        return Err(());
    }
    let mut out = [0u8; 32];
    let bytes = s.as_bytes();
    for i in 0..32 {
        let hi = (bytes[2 * i] as char).to_digit(16).ok_or(())?;
        let lo = (bytes[2 * i + 1] as char).to_digit(16).ok_or(())?;
        out[i] = ((hi << 4) | lo) as u8;
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn grant(lease: &str, budget: i64, exp: u64) -> LeaseGrant {
        LeaseGrant {
            lease_id: lease.into(),
            budget_units: budget,
            not_after_unix: exp,
            nonce: "tok-1".into(),
        }
    }

    #[test]
    fn valid_grant_admits() {
        let auth = LeaseAuthority::from_key([7u8; 32]);
        let sg = auth.issue(grant("inst-a", 1000, 10_000));
        assert!(admit(&auth, &sg, "inst-a", 1000, 5_000).is_ok());
        // Under-spending a grant is fine.
        assert!(admit(&auth, &sg, "inst-a", 500, 5_000).is_ok());
    }

    #[test]
    fn forged_mac_is_refused() {
        let auth = LeaseAuthority::from_key([7u8; 32]);
        let mut sg = auth.issue(grant("inst-a", 1000, 10_000));
        // Flip one hex nibble.
        let mut chars: Vec<char> = sg.mac.chars().collect();
        chars[0] = if chars[0] == '0' { '1' } else { '0' };
        sg.mac = chars.into_iter().collect();
        assert_eq!(auth.verify(&sg, 0), Err(AdmissionError::BadSignature));
    }

    #[test]
    fn a_different_key_cannot_verify() {
        let issuer = LeaseAuthority::from_key([1u8; 32]);
        let host = LeaseAuthority::from_key([2u8; 32]);
        let sg = issuer.issue(grant("inst-a", 1000, 10_000));
        assert_eq!(host.verify(&sg, 0), Err(AdmissionError::BadSignature));
    }

    #[test]
    fn tampering_the_claims_breaks_the_mac() {
        let auth = LeaseAuthority::from_key([7u8; 32]);
        let mut sg = auth.issue(grant("inst-a", 1000, 10_000));
        // Raise the budget without re-signing: the MAC no longer matches.
        sg.grant.budget_units = 1_000_000;
        assert_eq!(auth.verify(&sg, 0), Err(AdmissionError::BadSignature));
    }

    #[test]
    fn expired_grant_is_refused() {
        let auth = LeaseAuthority::from_key([7u8; 32]);
        let sg = auth.issue(grant("inst-a", 1000, 1_000));
        match admit(&auth, &sg, "inst-a", 1000, 1_000) {
            Err(AdmissionError::Expired { .. }) => {}
            other => panic!("expected Expired, got {other:?}"),
        }
    }

    #[test]
    fn grant_for_one_lease_cannot_run_another() {
        let auth = LeaseAuthority::from_key([7u8; 32]);
        let sg = auth.issue(grant("inst-a", 1000, 10_000));
        match admit(&auth, &sg, "inst-b", 1000, 5_000) {
            Err(AdmissionError::LeaseMismatch { granted, requested }) => {
                assert_eq!(granted, "inst-a");
                assert_eq!(requested, "inst-b");
            }
            other => panic!("expected LeaseMismatch, got {other:?}"),
        }
    }

    #[test]
    fn over_budget_declaration_is_refused() {
        let auth = LeaseAuthority::from_key([7u8; 32]);
        let sg = auth.issue(grant("inst-a", 1000, 10_000));
        match admit(&auth, &sg, "inst-a", 5000, 5_000) {
            Err(AdmissionError::OverBudget { declared, granted }) => {
                assert_eq!(declared, 5000);
                assert_eq!(granted, 1000);
            }
            other => panic!("expected OverBudget, got {other:?}"),
        }
    }

    #[test]
    fn generated_authority_roundtrips() {
        let auth = LeaseAuthority::generate();
        let sg = auth.issue(grant("inst-x", 42, u64::MAX));
        assert!(auth.verify(&sg, now_unix()).is_ok());
    }
}
