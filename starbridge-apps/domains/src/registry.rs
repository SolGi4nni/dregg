//! The custom-domain **control plane** — the plaintext `domain -> binding` routing
//! index a gateway consults, the cap-gated `bind`, the DNS-driven `verify`, and the
//! two verified reads (`site_for_host` / `is_verified`).
//!
//! This is the routing-plane companion to the verified per-domain cell (`src/lib.rs`):
//! a gateway needs the plaintext `domain -> site` map to route, so the registry holds
//! the serializable [`DomainBinding`] records (the source of truth for routing) while
//! the cell mirrors their commitments under the executor-enforced `WriteOnce` /
//! `Monotonic` invariants ([`mirror_binding`](crate::mirror_binding)). Binding inserts
//! a cap-gated Pending record; [`verify`](DomainRegistry::verify) resolves its
//! challenge through a [`DnsResolver`] and flips it to Verified. Resolution
//! ([`site_for_host`](DomainRegistry::site_for_host)) and the cert ask
//! ([`is_verified`](DomainRegistry::is_verified)) read only *verified* bindings — a
//! byte is routed (and a cert minted) only for a domain a tenant has *proven*.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};

use dregg_auth::credential::PublicKey;
use serde::{Deserialize, Serialize};

use crate::cap::{DomainCap, credential_fingerprint, verify_bind_authority};
use crate::dns::{
    ChallengeMethod, DnsChallenge, DnsResolver, TXT_CHALLENGE_PREFIX, VerificationState,
    apex_from_env, challenge_satisfied, is_valid_domain, is_valid_label, normalize_apex,
    random_challenge_token,
};

/// A **domain binding** — the routing-plane record backing a custom-domain -> site
/// map. The committed state a domain cell mirrors: the custom `domain`, the bound
/// `site` (`<name>`, whose `<name>.<apex>` cell serves the bytes), the `owner` (the
/// bind cap's subject), the chosen challenge `method`, the `challenge` nonce, the
/// verification `state`, and the `verified_seq` of the verifying turn.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DomainBinding {
    /// The custom domain bound (lowercased).
    pub domain: String,
    /// The bound site `<name>` — the `<name>.<apex>` cell that serves the bytes.
    pub site: String,
    /// The owner (the bind cap's subject). Provable: the bind receipt binds
    /// `(domain, site, owner)`, and the owner is sealed `WriteOnce` on the cell.
    pub owner: String,
    /// Which DNS record proves control.
    pub method: ChallengeMethod,
    /// The challenge nonce (the value published in DNS; carried for both methods so
    /// the expected record value is re-derivable).
    pub challenge: String,
    /// Whether control has been proven.
    pub state: VerificationState,
    /// The registry-monotonic sequence of the verifying turn (who proved control,
    /// when), `None` while [`VerificationState::Pending`].
    pub verified_seq: Option<u64>,
}

impl DomainBinding {
    /// A bound-but-unproven binding (Pending, no verifying turn yet).
    pub fn pending(
        domain: &str,
        site: &str,
        owner: &str,
        method: ChallengeMethod,
        challenge: &str,
    ) -> DomainBinding {
        DomainBinding {
            domain: domain.trim().to_ascii_lowercase(),
            site: site.to_string(),
            owner: owner.to_string(),
            method,
            challenge: challenge.to_string(),
            state: VerificationState::Pending,
            verified_seq: None,
        }
    }

    /// A proven binding (Verified at `verified_seq`).
    pub fn verified(
        domain: &str,
        site: &str,
        owner: &str,
        method: ChallengeMethod,
        challenge: &str,
        verified_seq: u64,
    ) -> DomainBinding {
        DomainBinding {
            state: VerificationState::Verified,
            verified_seq: Some(verified_seq),
            ..DomainBinding::pending(domain, site, owner, method, challenge)
        }
    }

    /// The DNS record an owner must publish to satisfy this binding's challenge, under
    /// the deployment's configured `apex` (the CNAME target is `<site>.<apex>`). The
    /// TXT method does not depend on the apex; the CNAME method points at the apex the
    /// owning [`DomainRegistry`] was constructed with.
    pub fn dns_challenge(&self, apex: &str) -> DnsChallenge {
        match self.method {
            ChallengeMethod::Txt => DnsChallenge {
                record_type: ChallengeMethod::Txt,
                record_name: format!("{TXT_CHALLENGE_PREFIX}{}", self.domain),
                expected_value: self.challenge.clone(),
            },
            ChallengeMethod::Cname => DnsChallenge {
                record_type: ChallengeMethod::Cname,
                record_name: self.domain.clone(),
                expected_value: format!("{}.{}", self.site, normalize_apex(apex)),
            },
        }
    }

    /// Whether this binding has proven control.
    pub fn is_verified(&self) -> bool {
        self.state.is_verified()
    }
}

/// The verifiable record a bind leaves: who bound which domain to which site, under
/// what challenge. The routing-plane analog of the bind turn's receipt.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct BindReceipt {
    /// The registry-monotonic sequence of this bind (bind order).
    pub seq: u64,
    /// The custom domain bound.
    pub domain: String,
    /// The site `<name>` it was bound to.
    pub site: String,
    /// The owner (the cap's subject) that bound it.
    pub owner: String,
    /// The DNS challenge the owner must satisfy to verify.
    pub challenge: DnsChallenge,
}

/// A **durable snapshot** of a registry's control-plane state — the serializable form
/// a gateway persists so a process restart (or a fresh replica in a fleet) rehydrates
/// every binding + the revocation list + the sequence counter, instead of losing them
/// to an in-memory `BTreeMap`. Round-trips through [`serde_json`] via
/// [`DomainRegistry::snapshot`] / [`DomainRegistry::restore_from`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RegistrySnapshot {
    /// Snapshot schema version (for forward-compatible migration).
    pub version: u32,
    /// The next registry-monotonic sequence — restored so later turns stay monotonic
    /// across a restart.
    pub next_seq: u64,
    /// Every binding, keyed by domain.
    pub bindings: Vec<DomainBinding>,
    /// Revoked-credential fingerprints (hex of the 32-byte `blake3` image).
    #[serde(default)]
    pub revoked_credentials: Vec<String>,
}

/// The current [`RegistrySnapshot`] schema version.
pub const SNAPSHOT_VERSION: u32 = 1;

/// Why a domain operation was refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DomainError {
    /// The presented credential does not authorize binding `domain` (it did not
    /// decode, pins no subject, did not verify under the trusted root, or is scoped
    /// to a different domain).
    CapRefused { domain: String, reason: String },
    /// A rebind was attempted by a credential whose subject is not the existing
    /// binding's owner — only the owner may rebind (no takeover).
    OwnerMismatch { domain: String },
    /// The registry has no trusted root authority configured, so no credential can be
    /// verified — every bind is refused (fail-closed). Construct with
    /// [`DomainRegistry::with_authority`].
    NoAuthority,
    /// `domain` is not a usable custom domain (not a multi-label FQDN, a bad label, or
    /// it is a platform-apex host — the wildcard path, not a custom domain).
    InvalidDomain(String),
    /// `site` is not a valid site `<name>` label.
    InvalidSite(String),
    /// No binding exists for `domain` (verify/lookup on an unbound domain).
    NotBound(String),
    /// The DNS challenge is not (yet) satisfied — control is unproven.
    ChallengeUnmet { domain: String },
    /// The presented credential has been revoked (its fingerprint is on the
    /// registry's revocation list) — a leaked / compromised cap is refused even
    /// though it still verifies cryptographically.
    CredentialRevoked { domain: String },
    /// The binding for `domain` has been [`VerificationState::Revoked`] (control
    /// withdrawn: re-validation failed, the owner unbound, or an abuse takedown).
    /// A revoked binding is terminal — the owner must rebind a fresh challenge.
    BindingRevoked { domain: String },
}

impl std::fmt::Display for DomainError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DomainError::CapRefused { domain, reason } => {
                write!(
                    f,
                    "credential does not authorize binding `{domain}`: {reason}"
                )
            }
            DomainError::OwnerMismatch { domain } => {
                write!(
                    f,
                    "only the owner of the binding for `{domain}` may rebind it"
                )
            }
            DomainError::NoAuthority => write!(
                f,
                "no trusted root authority configured — binding is refused (fail-closed)"
            ),
            DomainError::InvalidDomain(d) => write!(f, "`{d}` is not a valid custom domain"),
            DomainError::InvalidSite(s) => write!(f, "`{s}` is not a valid site name"),
            DomainError::NotBound(d) => write!(f, "no binding for domain `{d}`"),
            DomainError::ChallengeUnmet { domain } => write!(
                f,
                "DNS challenge for `{domain}` is not satisfied (control unproven)"
            ),
            DomainError::CredentialRevoked { domain } => write!(
                f,
                "the credential presented for `{domain}` has been revoked"
            ),
            DomainError::BindingRevoked { domain } => write!(
                f,
                "the binding for `{domain}` is revoked (control withdrawn) — rebind a fresh challenge"
            ),
        }
    }
}

impl std::error::Error for DomainError {}

/// The registry of domain bindings — the custom-domain control plane.
pub struct DomainRegistry {
    bindings: Mutex<BTreeMap<String, DomainBinding>>,
    /// Fingerprints (`blake3` of the credential wire form) of caps an operator has
    /// revoked — a leaked / compromised broad `mint_domains_cap` is refused on the
    /// bind path even though it still verifies under the root (there is no expiry to
    /// wait out). See [`revoke_credential`](Self::revoke_credential).
    revoked_creds: Mutex<BTreeSet<[u8; 32]>>,
    next_seq: AtomicU64,
    /// The trusted root authority that mints domain-binding credentials. A bind must
    /// present a credential verifying under this root for the domain. `None` (the
    /// [`DomainRegistry::new`] default) = no authority → every bind is refused
    /// (fail-closed); the verify / route / `ask` read paths do not need it.
    authority: Option<PublicKey>,
    /// The deployment's hosting apex — the CNAME challenge target base (`<site>.<apex>`)
    /// and the wildcard host `is_valid_domain` refuses as "not custom". Configuration,
    /// not a compile-time constant: defaults to [`apex_from_env`] (the
    /// [`HOSTING_APEX_ENV`](crate::dns::HOSTING_APEX_ENV) variable, else
    /// [`DEFAULT_HOSTING_APEX`](crate::dns::DEFAULT_HOSTING_APEX)) and is overridable
    /// with [`with_apex`](Self::with_apex).
    apex: String,
}

impl Default for DomainRegistry {
    fn default() -> DomainRegistry {
        DomainRegistry {
            bindings: Mutex::new(BTreeMap::new()),
            revoked_creds: Mutex::new(BTreeSet::new()),
            next_seq: AtomicU64::new(0),
            authority: None,
            apex: apex_from_env(),
        }
    }
}

impl DomainRegistry {
    /// A fresh, empty registry with **no** binding authority configured — verify /
    /// route / cert-`ask` work, but [`bind`](Self::bind) is refused (fail-closed)
    /// until a root is set. A gateway adopts this read side; the binding control
    /// surface uses [`with_authority`](Self::with_authority). The hosting apex is read
    /// from the environment (see [`apex`](Self::apex)).
    pub fn new() -> DomainRegistry {
        DomainRegistry::default()
    }

    /// A registry whose binds are gated by credentials verifying under `root` — the
    /// trusted domain-binding authority. Only a holder of a credential this root
    /// minted (or attenuated) may bind, and the binding's owner is that credential's
    /// pinned subject.
    pub fn with_authority(root: PublicKey) -> DomainRegistry {
        DomainRegistry {
            authority: Some(root),
            ..Default::default()
        }
    }

    /// Set the deployment's hosting apex explicitly (e.g. `dregg.fg-goose.online`,
    /// `dregg.net`), overriding the environment-derived default. Builder form: chains
    /// after [`new`](Self::new) / [`with_authority`](Self::with_authority). An empty /
    /// whitespace apex is ignored (the prior value is kept).
    pub fn with_apex(mut self, apex: impl AsRef<str>) -> DomainRegistry {
        let normalized = normalize_apex(apex.as_ref());
        if !normalized.is_empty() {
            self.apex = normalized;
        }
        self
    }

    /// The deployment's configured hosting apex (the CNAME challenge target base and
    /// the wildcard host refused as "not custom").
    pub fn apex(&self) -> &str {
        &self.apex
    }

    /// The configured trusted-root authority (if any), so a wrapper (the cell-backed
    /// weld) can reuse the same gate.
    pub fn authority(&self) -> Option<&PublicKey> {
        self.authority.as_ref()
    }

    /// Draw the next registry-monotonic sequence (bind/verify order). Crate-internal:
    /// the cell-backed weld shares this counter so its receipts stay monotonic with the
    /// index's.
    pub(crate) fn next_sequence(&self) -> u64 {
        self.next_seq.fetch_add(1, Ordering::Relaxed)
    }

    /// Register a credential fingerprint as **revoked** — every later bind presenting
    /// it is refused ([`DomainError::CredentialRevoked`]) even though it still verifies
    /// under the trusted root. The fingerprint is [`credential_fingerprint`] of the
    /// cap's wire form. This is the revocation half of a leaked-credential response
    /// (the expiry half is [`crate::cap::mint_domains_cap_expiring`]).
    pub fn revoke_credential(&self, fingerprint: [u8; 32]) {
        self.revoked_creds
            .lock()
            .expect("revoked_creds poisoned")
            .insert(fingerprint);
    }

    /// Whether `fingerprint` is on the revocation list.
    pub fn is_credential_revoked(&self, fingerprint: &[u8; 32]) -> bool {
        self.revoked_creds
            .lock()
            .expect("revoked_creds poisoned")
            .contains(fingerprint)
    }

    /// **Authorize a bind without mutating the registry** — the full cap + validity +
    /// owner + revocation gate, returning the credential's pinned subject (the binding
    /// owner) on success. Shared by [`bind`](Self::bind) and the cell-backed weld
    /// ([`crate::CellBackedRegistry`]) so both enforce the identical gate before either
    /// writes the index or drives a cell turn.
    ///
    /// Checks, in order: `domain` is a custom FQDN; the cap is exercised for that
    /// domain; the credential is not revoked; it verifies under the trusted root for
    /// the domain at the current clock (an EXPIRED cap fails here); `site` is a valid
    /// label; and any existing binding is owned by this subject (no takeover) and not
    /// already [`VerificationState::Revoked`].
    pub fn authorize_bind(
        &self,
        cap: &DomainCap,
        domain: &str,
        site: &str,
    ) -> Result<String, DomainError> {
        let domain = domain.trim().to_ascii_lowercase();
        if !is_valid_domain(&domain, &self.apex) {
            return Err(DomainError::InvalidDomain(domain));
        }
        if cap.domain != domain {
            return Err(DomainError::CapRefused {
                domain,
                reason: format!(
                    "cap is exercised for `{}`, not the bound domain",
                    cap.domain
                ),
            });
        }
        // A revoked credential is refused before any signature check — fail-closed on
        // a known-compromised cap.
        if self.is_credential_revoked(&credential_fingerprint(&cap.credential)) {
            return Err(DomainError::CredentialRevoked { domain });
        }
        // Real cap authority: verify the credential under the trusted root at the
        // CURRENT clock (so a `NotAfter` expiry bites). A registry with no authority
        // refuses every bind (fail-closed).
        let root = self.authority.as_ref().ok_or(DomainError::NoAuthority)?;
        let owner = verify_bind_authority(&cap.credential, root, &domain, unix_now())?;
        if !is_valid_label(site) {
            return Err(DomainError::InvalidSite(site.to_string()));
        }
        // Owner-gated rebind: a different subject cannot overwrite (takeover) a
        // victim's binding, and a revoked binding is terminal.
        if let Some(existing) = self
            .bindings
            .lock()
            .expect("bindings poisoned")
            .get(&domain)
        {
            if existing.owner != owner {
                return Err(DomainError::OwnerMismatch { domain });
            }
            if existing.state.is_revoked() {
                return Err(DomainError::BindingRevoked { domain });
            }
        }
        Ok(owner)
    }

    /// Bind a custom domain to a site as a cap-gated turn (Pending).
    ///
    /// Runs the full [`authorize_bind`](Self::authorize_bind) gate, then issues a
    /// **cryptographically-random** challenge nonce ([`random_challenge_token`]) and
    /// writes the [`DomainBinding`] (owner = the credential's subject, state =
    /// Pending). A rebind by any other subject is refused
    /// ([`DomainError::OwnerMismatch`]); a rebind by the owner replaces the binding
    /// (a fresh nonce, back to Pending). To have the executor's `WriteOnce`/`Monotonic`
    /// teeth gate the routing record itself, drive the bind through
    /// [`crate::CellBackedRegistry`] instead.
    pub fn bind(
        &self,
        cap: &DomainCap,
        domain: &str,
        site: &str,
        method: ChallengeMethod,
    ) -> Result<BindReceipt, DomainError> {
        let owner = self.authorize_bind(cap, domain, site)?;
        let domain = domain.trim().to_ascii_lowercase();
        let seq = self.next_seq.fetch_add(1, Ordering::Relaxed);
        // A CSPRNG nonce: a DNS control challenge MUST be unpredictable, so an attacker
        // who knows the public `(domain, owner)` cannot precompute (or race) the value.
        let challenge = random_challenge_token(&domain, &owner);
        let binding = DomainBinding::pending(&domain, site, &owner, method, &challenge);
        let receipt = BindReceipt {
            seq,
            domain: domain.clone(),
            site: site.to_string(),
            owner,
            challenge: binding.dns_challenge(&self.apex),
        };
        // Re-acquire under the lock and re-check the owner-gate atomically with the
        // insert (authorize_bind checked it, but the lock was dropped in between).
        let mut guard = self.bindings.lock().expect("bindings poisoned");
        if let Some(existing) = guard.get(&domain) {
            if existing.owner != receipt.owner {
                return Err(DomainError::OwnerMismatch { domain });
            }
            if existing.state.is_revoked() {
                return Err(DomainError::BindingRevoked { domain });
            }
        }
        guard.insert(domain, binding);
        Ok(receipt)
    }

    /// Verify a binding's control by resolving its challenge through `dns`.
    ///
    /// On a satisfied challenge the binding flips to [`VerificationState::Verified`]
    /// (recording the verifying turn's sequence) and the now-verified binding is
    /// returned. An unmet challenge leaves the binding Pending and returns
    /// [`DomainError::ChallengeUnmet`]; an unbound domain is
    /// [`DomainError::NotBound`]. Idempotent: verifying an already-verified binding
    /// re-checks and is a no-op success.
    pub fn verify(
        &self,
        domain: &str,
        dns: &impl DnsResolver,
    ) -> Result<DomainBinding, DomainError> {
        let domain = domain.trim().to_ascii_lowercase();
        // Snapshot the binding, then release the lock for the (slow) DNS lookup so a
        // black-holed resolver cannot stall all routing / cert asks while it runs.
        let snapshot = {
            let guard = self.bindings.lock().expect("bindings poisoned");
            guard
                .get(&domain)
                .cloned()
                .ok_or_else(|| DomainError::NotBound(domain.clone()))?
        };
        if !challenge_satisfied(&snapshot.dns_challenge(&self.apex), dns) {
            return Err(DomainError::ChallengeUnmet { domain });
        }
        // Re-acquire to commit. The binding may have been rebound (a fresh nonce)
        // while the lock was dropped — only flip the binding whose challenge is the
        // one we actually proved, so a concurrent rebind is not wrongly verified.
        let mut guard = self.bindings.lock().expect("bindings poisoned");
        let binding = guard
            .get_mut(&domain)
            .ok_or_else(|| DomainError::NotBound(domain.clone()))?;
        if binding.challenge != snapshot.challenge || binding.method != snapshot.method {
            return Err(DomainError::ChallengeUnmet { domain });
        }
        // A revoked binding is terminal — control was withdrawn; it cannot be flipped
        // back to Verified (that would be the un-revoke a `Monotonic` cell refuses).
        if binding.state.is_revoked() {
            return Err(DomainError::BindingRevoked { domain });
        }
        if binding.state != VerificationState::Verified {
            binding.state = VerificationState::Verified;
            binding.verified_seq = Some(self.next_seq.fetch_add(1, Ordering::Relaxed));
        }
        Ok(binding.clone())
    }

    /// **Re-validate a verified binding against live DNS**, demoting it to
    /// [`VerificationState::Revoked`] if the control record is gone / re-pointed.
    ///
    /// The periodic re-check a hosting layer runs so a domain does not stay `Verified`
    /// forever after the owner loses DNS control (the domain expires, the record is
    /// deleted, DNS is re-pointed). Returns the binding's state after the check:
    /// `Verified` if the challenge still holds, `Revoked` if it no longer does. A
    /// `Pending` binding is left untouched (it was never verified); an unbound domain
    /// is [`DomainError::NotBound`]. Demotion is a distinct forward transition (NOT an
    /// un-verify): `site_for_host`/`is_verified` immediately stop routing it.
    pub fn revalidate(
        &self,
        domain: &str,
        dns: &impl DnsResolver,
    ) -> Result<VerificationState, DomainError> {
        let domain = domain.trim().to_ascii_lowercase();
        let snapshot = {
            let guard = self.bindings.lock().expect("bindings poisoned");
            guard
                .get(&domain)
                .cloned()
                .ok_or_else(|| DomainError::NotBound(domain.clone()))?
        };
        // Only a currently-Verified binding is subject to demotion.
        if snapshot.state != VerificationState::Verified {
            return Ok(snapshot.state);
        }
        let still_ok = challenge_satisfied(&snapshot.dns_challenge(&self.apex), dns);
        let mut guard = self.bindings.lock().expect("bindings poisoned");
        let binding = guard
            .get_mut(&domain)
            .ok_or_else(|| DomainError::NotBound(domain.clone()))?;
        // Re-check under the lock: only demote the binding we actually re-validated.
        if binding.state != VerificationState::Verified || binding.challenge != snapshot.challenge {
            return Ok(binding.state);
        }
        if !still_ok {
            binding.state = VerificationState::Revoked;
            binding.verified_seq = Some(self.next_seq.fetch_add(1, Ordering::Relaxed));
        }
        Ok(binding.state)
    }

    /// **Revoke a binding** (an abuse takedown / administrative demotion) — move it to
    /// the terminal [`VerificationState::Revoked`] regardless of DNS. It stops routing
    /// immediately and can never be re-verified on the same record. Idempotent;
    /// [`DomainError::NotBound`] for an unbound domain.
    pub fn revoke(&self, domain: &str) -> Result<DomainBinding, DomainError> {
        let domain = domain.trim().to_ascii_lowercase();
        let mut guard = self.bindings.lock().expect("bindings poisoned");
        let binding = guard
            .get_mut(&domain)
            .ok_or_else(|| DomainError::NotBound(domain.clone()))?;
        if !binding.state.is_revoked() {
            binding.state = VerificationState::Revoked;
            binding.verified_seq = Some(self.next_seq.fetch_add(1, Ordering::Relaxed));
        }
        Ok(binding.clone())
    }

    /// **Unbind a domain** — the owner removes the routing record entirely (a clean
    /// takedown, freeing the domain to be bound afresh). Returns the removed binding,
    /// or [`DomainError::NotBound`] if nothing was bound. Unlike [`revoke`](Self::revoke)
    /// (which keeps the record as terminal-revoked, auditable), this drops it so a
    /// later [`bind`](Self::bind) starts a fresh challenge from Pending.
    pub fn unbind(&self, domain: &str) -> Result<DomainBinding, DomainError> {
        let domain = domain.trim().to_ascii_lowercase();
        self.bindings
            .lock()
            .expect("bindings poisoned")
            .remove(&domain)
            .ok_or(DomainError::NotBound(domain))
    }

    /// Look up a binding by domain (a clone of the committed record).
    pub fn get(&self, domain: &str) -> Option<DomainBinding> {
        self.bindings
            .lock()
            .expect("bindings poisoned")
            .get(&domain.trim().to_ascii_lowercase())
            .cloned()
    }

    /// The bound site `<name>` for an inbound `Host`, **only when verified**.
    ///
    /// Strips a `:port` suffix and lowercases, then returns the verified binding's
    /// site. An unbound or still-Pending host yields `None` — a gateway routes (and
    /// the edge mints a cert for) only proven domains.
    pub fn site_for_host(&self, host: &str) -> Option<String> {
        let domain = host_key(host)?;
        let guard = self.bindings.lock().expect("bindings poisoned");
        let binding = guard.get(&domain)?;
        binding.is_verified().then(|| binding.site.clone())
    }

    /// Whether `host` is a verified custom domain — a gateway's on-demand-TLS `ask`
    /// gate (a cert is minted only for a proven domain).
    pub fn is_verified(&self, host: &str) -> bool {
        host_key(host)
            .and_then(|d| {
                self.bindings
                    .lock()
                    .expect("bindings poisoned")
                    .get(&d)
                    .map(|b| b.is_verified())
            })
            .unwrap_or(false)
    }

    /// All bindings, sorted by domain (a snapshot of the committed set).
    pub fn list(&self) -> Vec<DomainBinding> {
        self.bindings
            .lock()
            .expect("bindings poisoned")
            .values()
            .cloned()
            .collect()
    }

    /// Adopt a pre-existing [`DomainBinding`] (e.g. one mirrored from a domain cell or
    /// a persisted snapshot) into this registry — so a fresh process can drive
    /// [`verify`](Self::verify) / routing over bindings a prior turn created, without
    /// re-issuing the challenge nonce. The registry's sequence is bumped past the
    /// adopted binding's verifying turn so later turns stay monotonic.
    pub fn adopt(&self, binding: DomainBinding) {
        if let Some(seq) = binding.verified_seq {
            self.next_seq.fetch_max(seq + 1, Ordering::Relaxed);
        }
        self.bindings
            .lock()
            .expect("bindings poisoned")
            .insert(binding.domain.clone(), binding);
    }

    // ── Persistence: a durable, shareable control-plane snapshot. ────────────────

    /// Capture a durable [`RegistrySnapshot`] of the current bindings + revocation
    /// list + sequence counter. The authority root/apex are configuration (re-supplied
    /// at construction), not state, so they are not serialized.
    pub fn snapshot(&self) -> RegistrySnapshot {
        let bindings = self
            .bindings
            .lock()
            .expect("bindings poisoned")
            .values()
            .cloned()
            .collect();
        let revoked_credentials = self
            .revoked_creds
            .lock()
            .expect("revoked_creds poisoned")
            .iter()
            .map(hex32)
            .collect();
        RegistrySnapshot {
            version: SNAPSHOT_VERSION,
            next_seq: self.next_seq.load(Ordering::Relaxed),
            bindings,
            revoked_credentials,
        }
    }

    /// Rehydrate the registry from a [`RegistrySnapshot`] (adopt every binding, restore
    /// the revocation set, and bump the sequence past the snapshot's). Additive: a
    /// binding already present for a domain is overwritten by the snapshot's.
    pub fn restore_from(&self, snapshot: &RegistrySnapshot) {
        for b in &snapshot.bindings {
            self.adopt(b.clone());
        }
        self.next_seq
            .fetch_max(snapshot.next_seq, Ordering::Relaxed);
        let mut revoked = self.revoked_creds.lock().expect("revoked_creds poisoned");
        for hex in &snapshot.revoked_credentials {
            if let Some(fp) = unhex32(hex) {
                revoked.insert(fp);
            }
        }
    }

    /// Serialize [`snapshot`](Self::snapshot) to pretty JSON — the bytes a gateway
    /// writes to its durable store (a file, an object, a row).
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(&self.snapshot())
    }

    /// Rehydrate from JSON produced by [`to_json`](Self::to_json).
    pub fn restore_from_json(&self, json: &str) -> Result<(), serde_json::Error> {
        let snapshot: RegistrySnapshot = serde_json::from_str(json)?;
        self.restore_from(&snapshot);
        Ok(())
    }

    /// Atomically persist [`to_json`](Self::to_json) to `path` (write to a temp
    /// sibling, then rename) so a crash mid-write never leaves a truncated store.
    pub fn save_to_path(&self, path: impl AsRef<std::path::Path>) -> std::io::Result<()> {
        let path = path.as_ref();
        let json = self
            .to_json()
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
        let tmp = path.with_extension("tmp");
        std::fs::write(&tmp, json.as_bytes())?;
        std::fs::rename(&tmp, path)
    }

    /// Rehydrate from a file written by [`save_to_path`](Self::save_to_path). A missing
    /// file is `Ok(())` (a cold start with nothing to restore is not an error).
    pub fn restore_from_path(&self, path: impl AsRef<std::path::Path>) -> std::io::Result<()> {
        let path = path.as_ref();
        match std::fs::read_to_string(path) {
            Ok(json) => self
                .restore_from_json(&json)
                .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e)),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(()),
            Err(e) => Err(e),
        }
    }
}

/// Lowercase hex of a 32-byte image.
fn hex32(b: &[u8; 32]) -> String {
    use std::fmt::Write;
    let mut s = String::with_capacity(64);
    for x in b {
        let _ = write!(s, "{x:02x}");
    }
    s
}

/// Parse a 64-char lowercase-hex string back to a 32-byte image (`None` if malformed).
fn unhex32(s: &str) -> Option<[u8; 32]> {
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for (i, chunk) in s.as_bytes().chunks(2).enumerate() {
        let hi = (chunk[0] as char).to_digit(16)?;
        let lo = (chunk[1] as char).to_digit(16)?;
        out[i] = (hi * 16 + lo) as u8;
    }
    Some(out)
}

/// Normalize an inbound `Host` to a binding key: strip `:port`, trim, lowercase.
/// `None` for an empty host.
fn host_key(host: &str) -> Option<String> {
    let bare = host.split(':').next().unwrap_or(host).trim();
    if bare.is_empty() {
        return None;
    }
    Some(bare.to_ascii_lowercase())
}

/// The verifier's clock (unix seconds) — for a credential's temporal caveats. This IS
/// load-bearing: an expiring cap ([`crate::cap::mint_domains_cap_expiring`]) pins a
/// `NotAfter { at }` caveat, so a cap presented after `at` fails
/// [`verify_bind_authority`] here. Mint + verify agree on unix-seconds.
fn unix_now() -> u64 {
    use std::time::{SystemTime, UNIX_EPOCH};
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cap::mint_domains_cap;
    use crate::dns::MockDns;
    use dregg_auth::credential::RootKey;

    fn root() -> RootKey {
        RootKey::from_seed([7u8; 32])
    }

    fn registry() -> DomainRegistry {
        DomainRegistry::with_authority(root().public())
    }

    fn cap(domain: &str) -> DomainCap {
        DomainCap::new(mint_domains_cap(&root(), "dregg:alice").encode(), domain)
    }

    #[test]
    fn bind_requires_a_real_authorized_credential() {
        // No authority → every bind is refused (fail-closed).
        let no_auth = DomainRegistry::new();
        assert_eq!(
            no_auth.bind(
                &cap("blog.example.com"),
                "blog.example.com",
                "blog",
                ChallengeMethod::Txt
            ),
            Err(DomainError::NoAuthority),
        );

        // The rightful, root-minted credential binds; owner is its subject.
        let reg = registry();
        let r = reg
            .bind(
                &cap("blog.example.com"),
                "blog.example.com",
                "blog",
                ChallengeMethod::Txt,
            )
            .expect("bind");
        assert_eq!(r.domain, "blog.example.com");
        assert_eq!(r.site, "blog");
        assert_eq!(r.owner, "dregg:alice");
        assert_eq!(r.challenge.record_name, "_dregg-verify.blog.example.com");

        // A cap exercised for a different domain cannot bind blog.example.com.
        assert!(matches!(
            reg.bind(
                &cap("shop.example.com"),
                "blog.example.com",
                "blog",
                ChallengeMethod::Txt
            ),
            Err(DomainError::CapRefused { .. }),
        ));
        // Invalid site refused.
        assert!(matches!(
            reg.bind(
                &cap("x.example.com"),
                "x.example.com",
                "Bad.Name",
                ChallengeMethod::Txt
            ),
            Err(DomainError::InvalidSite(_)),
        ));
    }

    #[test]
    fn unverified_domain_does_not_resolve() {
        let reg = registry();
        let _ = reg
            .bind(
                &cap("blog.example.com"),
                "blog.example.com",
                "blog",
                ChallengeMethod::Txt,
            )
            .unwrap();
        // Pending → the gateway reads decline: no route, no cert.
        assert!(!reg.is_verified("blog.example.com"));
        assert_eq!(reg.site_for_host("blog.example.com"), None);
    }

    #[test]
    fn verify_flips_once_and_a_wrong_nonce_is_refused() {
        let reg = registry();
        let r = reg
            .bind(
                &cap("blog.example.com"),
                "blog.example.com",
                "blog",
                ChallengeMethod::Txt,
            )
            .unwrap();

        // A wrong TXT value → ChallengeUnmet, stays Pending.
        let wrong = MockDns::new().with_txt(&r.challenge.record_name, "dregg-verify-WRONG");
        assert_eq!(
            reg.verify("blog.example.com", &wrong),
            Err(DomainError::ChallengeUnmet {
                domain: "blog.example.com".into()
            }),
        );
        assert!(!reg.is_verified("blog.example.com"));

        // The exact nonce → Verified, and site_for_host now resolves.
        let dns = MockDns::new().with_txt(&r.challenge.record_name, &r.challenge.expected_value);
        let b = reg.verify("blog.example.com", &dns).expect("verify");
        assert!(b.is_verified());
        let seq = b.verified_seq.expect("a verifying turn was recorded");
        assert!(reg.is_verified("blog.example.com"));
        assert_eq!(
            reg.site_for_host("Blog.Example.Com:443").as_deref(),
            Some("blog")
        );

        // Idempotent re-verify does NOT advance the verifying sequence (flips once).
        let b2 = reg.verify("blog.example.com", &dns).expect("re-verify");
        assert_eq!(b2.verified_seq, Some(seq), "the flip happened once");
    }

    #[test]
    fn an_attacker_cannot_overwrite_a_victims_binding() {
        let reg = registry();
        let alice = DomainCap::new(
            mint_domains_cap(&root(), "dregg:alice").encode(),
            "blog.example.com",
        );
        reg.bind(&alice, "blog.example.com", "blog", ChallengeMethod::Txt)
            .unwrap();

        // Mallory holds her OWN valid root-minted credential — a different subject.
        let mallory = DomainCap::new(
            mint_domains_cap(&root(), "dregg:mallory").encode(),
            "blog.example.com",
        );
        assert_eq!(
            reg.bind(&mallory, "blog.example.com", "evil", ChallengeMethod::Txt),
            Err(DomainError::OwnerMismatch {
                domain: "blog.example.com".into()
            }),
        );
        assert_eq!(reg.get("blog.example.com").unwrap().owner, "dregg:alice");
    }

    #[test]
    fn verify_unbound_is_not_bound() {
        let reg = registry();
        assert_eq!(
            reg.verify("nope.example.com", &MockDns::new()),
            Err(DomainError::NotBound("nope.example.com".into())),
        );
    }

    fn bind_and_verify(reg: &DomainRegistry, domain: &str) -> DomainBinding {
        let r = reg
            .bind(&cap(domain), domain, "blog", ChallengeMethod::Txt)
            .expect("bind");
        let dns = MockDns::new().with_txt(&r.challenge.record_name, &r.challenge.expected_value);
        reg.verify(domain, &dns).expect("verify")
    }

    #[test]
    fn revalidate_demotes_a_verified_binding_whose_record_vanished() {
        let reg = registry();
        bind_and_verify(&reg, "blog.example.com");
        assert!(reg.is_verified("blog.example.com"));

        // Record still present → stays Verified.
        let b = reg.get("blog.example.com").unwrap();
        let present = MockDns::new().with_txt(
            &b.dns_challenge(reg.apex()).record_name,
            &b.dns_challenge(reg.apex()).expected_value,
        );
        assert_eq!(
            reg.revalidate("blog.example.com", &present).unwrap(),
            VerificationState::Verified
        );
        assert!(reg.is_verified("blog.example.com"));

        // Record gone → demoted to Revoked; stops routing; terminal.
        assert_eq!(
            reg.revalidate("blog.example.com", &MockDns::new()).unwrap(),
            VerificationState::Revoked
        );
        assert!(!reg.is_verified("blog.example.com"));
        assert_eq!(reg.site_for_host("blog.example.com"), None);
        // A revoked binding cannot be re-verified even if the record comes back.
        assert!(matches!(
            reg.verify("blog.example.com", &present),
            Err(DomainError::BindingRevoked { .. })
        ));
    }

    #[test]
    fn revoke_is_a_terminal_takedown_and_unbind_frees_the_domain() {
        let reg = registry();
        bind_and_verify(&reg, "blog.example.com");
        // Takedown: revoke stops routing but keeps the (auditable) record.
        reg.revoke("blog.example.com").unwrap();
        assert!(!reg.is_verified("blog.example.com"));
        assert!(reg.get("blog.example.com").unwrap().state.is_revoked());

        // Unbind drops the record entirely; a fresh bind then starts from Pending.
        reg.unbind("blog.example.com").unwrap();
        assert!(reg.get("blog.example.com").is_none());
        let r = reg
            .bind(
                &cap("blog.example.com"),
                "blog.example.com",
                "blog",
                ChallengeMethod::Txt,
            )
            .expect("rebind after unbind");
        assert_eq!(
            reg.get("blog.example.com").unwrap().state,
            VerificationState::Pending
        );
        assert!(r.challenge.expected_value.starts_with("dregg-verify-"));
    }

    #[test]
    fn a_revoked_credential_is_refused_on_bind() {
        use crate::cap::credential_fingerprint;
        let reg = registry();
        let c = cap("blog.example.com");
        reg.revoke_credential(credential_fingerprint(&c.credential));
        assert!(matches!(
            reg.bind(&c, "blog.example.com", "blog", ChallengeMethod::Txt),
            Err(DomainError::CredentialRevoked { .. })
        ));
    }

    #[test]
    fn an_expired_cap_is_refused_on_bind() {
        use crate::cap::mint_domains_cap_expiring;
        // A cap that expired at unix-second 1 — verify_bind_authority uses the live
        // clock (now), which is far past 1, so the bind is refused.
        let reg = registry();
        let expired = DomainCap::new(
            mint_domains_cap_expiring(&root(), "dregg:alice", 1).encode(),
            "blog.example.com",
        );
        assert!(matches!(
            reg.bind(&expired, "blog.example.com", "blog", ChallengeMethod::Txt),
            Err(DomainError::CapRefused { .. })
        ));
    }

    #[test]
    fn a_fresh_bind_issues_a_random_unpredictable_nonce() {
        let reg = registry();
        let r1 = reg
            .bind(
                &cap("a.example.com"),
                "a.example.com",
                "blog",
                ChallengeMethod::Txt,
            )
            .unwrap();
        let r2 = reg
            .bind(
                &cap("b.example.com"),
                "b.example.com",
                "blog",
                ChallengeMethod::Txt,
            )
            .unwrap();
        // 256-bit CSPRNG nonces: distinct, and not the old 16-hex FNV form.
        assert_ne!(r1.challenge.expected_value, r2.challenge.expected_value);
        assert_eq!(
            r1.challenge.expected_value.len(),
            "dregg-verify-".len() + 64
        );
    }

    #[test]
    fn snapshot_round_trips_bindings_revocations_and_sequence() {
        let reg = registry();
        bind_and_verify(&reg, "blog.example.com");
        reg.bind(
            &cap("shop.example.com"),
            "shop.example.com",
            "shop",
            ChallengeMethod::Txt,
        )
        .unwrap();
        reg.revoke_credential([0xabu8; 32]);

        let json = reg.to_json().expect("serialize");

        // A fresh process rehydrates every binding + the revocation + the sequence.
        let restored = registry();
        restored.restore_from_json(&json).expect("restore");
        assert_eq!(restored.list().len(), 2);
        assert!(restored.is_verified("blog.example.com"));
        assert_eq!(
            restored.get("shop.example.com").unwrap().state,
            VerificationState::Pending
        );
        assert!(restored.is_credential_revoked(&[0xabu8; 32]));

        // The restored binding's verifying sequence is preserved and the counter
        // advanced past it (later turns stay monotonic).
        let before = reg.snapshot();
        let after = restored.snapshot();
        assert_eq!(before.bindings.len(), after.bindings.len());
        assert!(after.next_seq >= before.next_seq);
    }

    #[test]
    fn save_and_restore_via_a_file_survive_a_restart() {
        let dir = std::env::temp_dir();
        let path = dir.join(format!(
            "starbridge-domains-snapshot-{}.json",
            std::process::id()
        ));
        let _ = std::fs::remove_file(&path);

        let reg = registry();
        bind_and_verify(&reg, "blog.example.com");
        reg.save_to_path(&path).expect("save");

        // A missing file restores as a clean cold start (no error).
        let cold = registry();
        cold.restore_from_path(dir.join("does-not-exist-xyz.json"))
            .expect("missing file is a cold start");
        assert_eq!(cold.list().len(), 0);

        // The real file rehydrates the verified binding.
        let reborn = registry();
        reborn.restore_from_path(&path).expect("restore");
        assert!(reborn.is_verified("blog.example.com"));
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn configured_apex_threads_into_the_cname_challenge_and_verify() {
        // A registry configured for a concrete deployment apex (no hardcoded value).
        let reg = registry().with_apex("dregg.fg-goose.online");
        assert_eq!(reg.apex(), "dregg.fg-goose.online");

        // The CNAME challenge target is `<site>.<configured-apex>`, not any built-in.
        let r = reg
            .bind(
                &cap("www.example.com"),
                "www.example.com",
                "blog",
                ChallengeMethod::Cname,
            )
            .expect("bind");
        assert_eq!(r.challenge.expected_value, "blog.dregg.fg-goose.online");

        // A CNAME pointing at that configured target verifies (trailing dot tolerated).
        let dns = MockDns::new().with_cname("www.example.com", "blog.dregg.fg-goose.online.");
        let b = reg.verify("www.example.com", &dns).expect("verify");
        assert!(b.is_verified());
        assert_eq!(
            reg.site_for_host("www.example.com").as_deref(),
            Some("blog")
        );

        // Under this apex a `<x>.dregg.fg-goose.online` host is the platform wildcard,
        // not a bindable custom domain.
        assert!(matches!(
            reg.bind(
                &cap("launch.dregg.fg-goose.online"),
                "launch.dregg.fg-goose.online",
                "launch",
                ChallengeMethod::Cname
            ),
            Err(DomainError::InvalidDomain(_)),
        ));
    }
}
