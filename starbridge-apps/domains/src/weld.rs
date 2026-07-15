//! # The WELD — the routing index and the executor cell, driven as one.
//!
//! [`DomainRegistry`] alone is a plaintext routing index: its `bind`/`verify` mutate a
//! `BTreeMap` and the per-domain cell's `WriteOnce`/`Monotonic` teeth (`src/lib.rs`)
//! never touch that path — the executor invariants are real only in isolated unit
//! tests. [`CellBackedRegistry`] closes that gap: every mutation drives a **real signed
//! turn against a per-domain executor cell FIRST**, so the committed cell (whose
//! program the executor re-enforces on every touch) gates the routing record, and only
//! then is the plaintext index updated to mirror the committed state.
//!
//! * `bind` (fresh) → a `register` turn seals `DOMAIN`+`OWNER` (`WriteOnce`), then a
//!   `bind` turn seals the `CHALLENGE_NONCE` (`WriteOnce`) and points `SITE`. A second
//!   register, or any attempt to re-issue the frozen nonce, is an executor refusal.
//! * `bind` (owner re-point) → a `repoint` turn writes the un-caveated `SITE` only
//!   (no re-proof of control) — the nonce and verification are preserved.
//! * `verify` → a `verify` turn flips `VERIFICATION_STATE` `0 -> 1` and advances
//!   `VERIFIED_SEQ`, under the executor's `Monotonic` teeth (a rewind is refused).
//! * `revoke` / failed `revalidate` → a `revoke` turn advances `VERIFICATION_STATE`
//!   to `Revoked` (`2`), a `Monotonic`-forward transition the executor admits and can
//!   never rewind.
//!
//! Each per-domain cell is derived from the operating identity's public key and the
//! domain (`CellId::derive_raw(pk, blake3("starbridge-domain-cell:<domain>"))`), lives
//! in the embedded ledger with [`domain_cell_program`] installed, and is reachable by
//! the operating agent through a granted capability (the operator owns the routing
//! fleet's cells; the [`DomainCap`] credential is the separate WHO-may-ask gate).
//!
//! The plaintext routing strings (`domain`/`site`/`owner`) live in the index — the
//! cell commits only their one-way commitments — so the durable
//! [`RegistrySnapshot`](crate::RegistrySnapshot) is what a restart rehydrates; the
//! cell is the source of truth for the enforced *transitions*.

use dregg_app_framework::{AppCipherclerk, AuthRequired, EmbeddedExecutor, TurnReceipt};
use dregg_auth::credential::PublicKey;
use dregg_cell::Cell;
use dregg_types::CellId;

use crate::cap::DomainCap;
use crate::dns::{
    ChallengeMethod, DnsResolver, VerificationState, challenge_satisfied,
    challenge_token_from_commitment,
};
use crate::registry::{BindReceipt, DomainBinding, DomainError, DomainRegistry};
use crate::{
    DOMAIN_SLOT, VERIFICATION_STATE_SLOT, VERIFIED_SEQ_SLOT, bind_effects, domain_cell_program,
    field_to_u64, register_effects, repoint_effects, revoke_effects, verify_effects,
};

/// Why a cell-backed operation failed — either the control-plane gate refused
/// ([`DomainError`]) or a cell turn did not commit at the executor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WeldError {
    /// The control-plane gate refused (cap / validity / owner / revocation / DNS).
    Domain(DomainError),
    /// A signed cell turn was rejected by the executor (e.g. a `WriteOnce`/`Monotonic`
    /// caveat bit) — the routing index was NOT mutated (fail-closed).
    Executor(String),
}

impl From<DomainError> for WeldError {
    fn from(e: DomainError) -> WeldError {
        WeldError::Domain(e)
    }
}

impl std::fmt::Display for WeldError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            WeldError::Domain(e) => write!(f, "{e}"),
            WeldError::Executor(e) => write!(f, "cell turn rejected by the executor: {e}"),
        }
    }
}

impl std::error::Error for WeldError {}

/// A domain registry whose `bind`/`verify`/`revoke` are gated by real executor cell
/// turns — the weld that makes the crate's headline (`WriteOnce`/`Monotonic` teeth
/// gate the routing record) true on the live path. See the module docs.
pub struct CellBackedRegistry {
    index: DomainRegistry,
    executor: EmbeddedExecutor,
    cipherclerk: AppCipherclerk,
}

impl CellBackedRegistry {
    /// A cell-backed registry gated by credentials verifying under `root`, driving
    /// per-domain cells on `executor` signed by `cipherclerk`.
    pub fn new(root: PublicKey, executor: EmbeddedExecutor, cipherclerk: AppCipherclerk) -> Self {
        CellBackedRegistry {
            index: DomainRegistry::with_authority(root),
            executor,
            cipherclerk,
        }
    }

    /// Wrap a pre-built index (e.g. one already configured with an apex, or restored
    /// from a snapshot) with the driving executor + cipherclerk.
    pub fn with_index(
        index: DomainRegistry,
        executor: EmbeddedExecutor,
        cipherclerk: AppCipherclerk,
    ) -> Self {
        CellBackedRegistry {
            index,
            executor,
            cipherclerk,
        }
    }

    /// Set the deployment's hosting apex (builder form).
    pub fn with_apex(self, apex: impl AsRef<str>) -> Self {
        let CellBackedRegistry {
            index,
            executor,
            cipherclerk,
        } = self;
        CellBackedRegistry {
            index: index.with_apex(apex),
            executor,
            cipherclerk,
        }
    }

    /// The underlying routing index — the read side (`site_for_host`, `is_verified`,
    /// `list`, `snapshot`/`save_to_path`, `revoke_credential`). A gateway consults this.
    pub fn index(&self) -> &DomainRegistry {
        &self.index
    }

    /// The embedded executor driving the per-domain cells.
    pub fn executor(&self) -> &EmbeddedExecutor {
        &self.executor
    }

    /// The signing cipherclerk.
    pub fn cipherclerk(&self) -> &AppCipherclerk {
        &self.cipherclerk
    }

    /// The stable per-domain cell token — `blake3("starbridge-domain-cell:<domain>")`.
    fn domain_token(domain: &str) -> [u8; 32] {
        let sep = format!(
            "starbridge-domain-cell:{}",
            domain.trim().to_ascii_lowercase()
        );
        *blake3::hash(sep.as_bytes()).as_bytes()
    }

    /// The [`CellId`] of the per-domain cell for `domain` (derived from the operating
    /// identity's public key + the domain token).
    pub fn domain_cell_id(&self, domain: &str) -> CellId {
        let pk = self.cipherclerk.public_key().0;
        CellId::derive_raw(&pk, &Self::domain_token(domain))
    }

    /// Ensure the per-domain cell exists in the ledger with [`domain_cell_program`]
    /// installed, and (on first creation) grant the operating agent a capability over
    /// it so it can author the cell's turns. Idempotent.
    fn ensure_cell(&self, domain: &str) -> CellId {
        let pk = self.cipherclerk.public_key().0;
        let token = Self::domain_token(domain);
        let cell_id = CellId::derive_raw(&pk, &token);
        let agent = self.cipherclerk.cell_id();
        self.executor.with_ledger_mut(|ledger| {
            if ledger.get(&cell_id).is_none() {
                let mut cell = Cell::new(pk, token);
                cell.program = domain_cell_program();
                let _ = ledger.insert_cell(cell);
                // The operator owns its routing-fleet cells: grant the agent a cap so
                // it can author this cell's turns (the DomainCap credential is the
                // separate WHO-may-ask gate, already checked upstream).
                if let Some(agent_cell) = ledger.get_mut(&agent) {
                    agent_cell
                        .capabilities
                        .grant(cell_id, AuthRequired::Signature);
                }
            }
        });
        // Idempotent re-assert of the program (a no-op if unchanged).
        self.executor
            .install_program(cell_id, domain_cell_program());
        cell_id
    }

    /// Whether the per-domain cell has already sealed its `DOMAIN` slot (i.e. a
    /// `register` turn has committed) — a non-zero `DOMAIN_SLOT` field.
    fn is_registered(&self, cell_id: CellId) -> bool {
        self.executor
            .cell_state(cell_id)
            .map(|s| s.fields[DOMAIN_SLOT as usize] != [0u8; 32])
            .unwrap_or(false)
    }

    fn submit(
        &self,
        method: &str,
        cell: CellId,
        effects: Vec<dregg_app_framework::Effect>,
    ) -> Result<TurnReceipt, WeldError> {
        let action = self.cipherclerk.make_action(cell, method, effects);
        self.executor
            .submit_action(&self.cipherclerk, action)
            .map_err(|e| WeldError::Executor(e.to_string()))
    }

    /// **Bind a custom domain to a site, gated by real cell turns.**
    ///
    /// Runs the full [`DomainRegistry::authorize_bind`] gate (cap + validity + owner +
    /// revocation), then: for a FRESH domain, submits a `register` turn (sealing
    /// `DOMAIN`+`OWNER` under `WriteOnce`) followed by a `bind` turn (sealing the
    /// `CHALLENGE_NONCE` under `WriteOnce`) — the nonce is drawn from the register
    /// turn's receipt commitment, so it is unpredictable AND the executor freezes it.
    /// For an owner RE-POINT of an already-registered domain, submits a `repoint` turn
    /// (writing only the un-caveated `SITE`), preserving the sealed nonce and the
    /// verification state. Only after the turn(s) commit is the routing index updated.
    pub fn bind(
        &self,
        cap: &DomainCap,
        domain: &str,
        site: &str,
        method: ChallengeMethod,
    ) -> Result<BindReceipt, WeldError> {
        let owner = self.index.authorize_bind(cap, domain, site)?;
        let domain = domain.trim().to_ascii_lowercase();
        let cell_id = self.ensure_cell(&domain);
        let seq = self.index.next_sequence();

        if self.is_registered(cell_id) {
            // Owner re-point: SITE is mutable, no re-proof. Keep the existing binding's
            // nonce + state; only the site changes.
            self.submit("repoint_domain", cell_id, repoint_effects(cell_id, site))?;
            let existing = self.index.get(&domain);
            let binding = match existing {
                Some(mut b) => {
                    b.site = site.to_string();
                    b
                }
                // Registered on the cell but missing from the index (e.g. a restart
                // without a restored snapshot): record a fresh Pending binding so the
                // owner can re-prove — the cell's sealed nonce is not recoverable.
                None => DomainBinding::pending(
                    &domain,
                    site,
                    &owner,
                    method,
                    &challenge_token_from_commitment(&domain, &owner, cell_id.as_bytes()),
                ),
            };
            let receipt = BindReceipt {
                seq,
                domain: domain.clone(),
                site: site.to_string(),
                owner,
                challenge: binding.dns_challenge(self.index.apex()),
            };
            self.index.adopt(binding);
            return Ok(receipt);
        }

        // Fresh bind: register (seal DOMAIN + OWNER), then bind (seal NONCE + point SITE).
        let register = self.submit(
            "register_domain",
            cell_id,
            register_effects(cell_id, &domain, &owner),
        )?;
        // The nonce is drawn from the register receipt's commitment — unpredictable to
        // anyone who cannot see the committed cell, and frozen by WriteOnce on bind.
        let nonce = challenge_token_from_commitment(&domain, &owner, &register.turn_hash);
        self.submit("bind_domain", cell_id, bind_effects(cell_id, site, &nonce))?;

        let binding = DomainBinding::pending(&domain, site, &owner, method, &nonce);
        let receipt = BindReceipt {
            seq,
            domain: domain.clone(),
            site: site.to_string(),
            owner,
            challenge: binding.dns_challenge(self.index.apex()),
        };
        self.index.adopt(binding);
        Ok(receipt)
    }

    /// **Verify a binding's control, gated by a real cell turn.**
    ///
    /// Checks the DNS challenge (via the index binding), then — if still Pending on the
    /// cell — submits a `verify` turn that flips `VERIFICATION_STATE` `0 -> 1` and
    /// advances `VERIFIED_SEQ` under the executor's `Monotonic` teeth, and finally
    /// mirrors the flip into the routing index. Idempotent: an already-verified cell is
    /// not flipped again. A revoked binding is terminal ([`DomainError::BindingRevoked`]).
    pub fn verify(&self, domain: &str, dns: &impl DnsResolver) -> Result<DomainBinding, WeldError> {
        let domain = domain.trim().to_ascii_lowercase();
        let binding = self
            .index
            .get(&domain)
            .ok_or_else(|| DomainError::NotBound(domain.clone()))?;
        if binding.state.is_revoked() {
            return Err(DomainError::BindingRevoked { domain }.into());
        }
        if !challenge_satisfied(&binding.dns_challenge(self.index.apex()), dns) {
            return Err(DomainError::ChallengeUnmet { domain }.into());
        }
        let cell_id = self.domain_cell_id(&domain);
        let live = self
            .executor
            .cell_state(cell_id)
            .ok_or_else(|| WeldError::Executor(format!("domain cell for `{domain}` not found")))?;
        let cur = field_to_u64(&live.fields[VERIFICATION_STATE_SLOT as usize]);
        if cur == VerificationState::Pending.code() {
            let live_seq = field_to_u64(&live.fields[VERIFIED_SEQ_SLOT as usize]);
            self.submit(
                "verify_domain",
                cell_id,
                verify_effects(cell_id, live_seq + 1),
            )?;
        }
        // Mirror into the routing index (idempotent flip-once).
        self.index.verify(&domain, dns).map_err(WeldError::from)
    }

    /// **Re-validate a verified binding against live DNS**, demoting it to `Revoked`
    /// (via a `revoke` cell turn) if control has been withdrawn. Returns the state
    /// after the check. See [`DomainRegistry::revalidate`].
    pub fn revalidate(
        &self,
        domain: &str,
        dns: &impl DnsResolver,
    ) -> Result<VerificationState, WeldError> {
        let domain = domain.trim().to_ascii_lowercase();
        let binding = self
            .index
            .get(&domain)
            .ok_or_else(|| DomainError::NotBound(domain.clone()))?;
        if binding.state != VerificationState::Verified {
            return Ok(binding.state);
        }
        if challenge_satisfied(&binding.dns_challenge(self.index.apex()), dns) {
            return Ok(VerificationState::Verified);
        }
        // Control is gone — demote via a Monotonic-forward cell turn, then the index.
        self.revoke_cell_and_index(&domain)?;
        Ok(VerificationState::Revoked)
    }

    /// **Revoke a binding** (abuse takedown / administrative demotion) via a `revoke`
    /// cell turn, then mirror into the index. Terminal + one-way.
    pub fn revoke(&self, domain: &str) -> Result<DomainBinding, WeldError> {
        let domain = domain.trim().to_ascii_lowercase();
        // Must be bound.
        if self.index.get(&domain).is_none() {
            return Err(DomainError::NotBound(domain).into());
        }
        self.revoke_cell_and_index(&domain)
    }

    /// Submit the `revoke` cell turn (if the cell is not already revoked) and mirror the
    /// terminal state into the routing index.
    fn revoke_cell_and_index(&self, domain: &str) -> Result<DomainBinding, WeldError> {
        let cell_id = self.domain_cell_id(domain);
        if let Some(live) = self.executor.cell_state(cell_id) {
            let cur = field_to_u64(&live.fields[VERIFICATION_STATE_SLOT as usize]);
            if cur != VerificationState::Revoked.code() {
                let live_seq = field_to_u64(&live.fields[VERIFIED_SEQ_SLOT as usize]);
                self.submit(
                    "revoke_domain",
                    cell_id,
                    revoke_effects(cell_id, live_seq + 1),
                )?;
            }
        }
        self.index.revoke(domain).map_err(WeldError::from)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cap::{credential_fingerprint, mint_domains_cap};
    use crate::dns::MockDns;
    use dregg_app_framework::AgentCipherclerk;
    use dregg_auth::credential::RootKey;

    fn root() -> RootKey {
        RootKey::from_seed([33u8; 32])
    }

    fn setup() -> (CellBackedRegistry, RootKey) {
        let r = root();
        let cipherclerk = AppCipherclerk::new(AgentCipherclerk::new(), [7u8; 32]);
        let executor = EmbeddedExecutor::new(&cipherclerk, "default");
        let reg = CellBackedRegistry::new(r.public(), executor, cipherclerk);
        (reg, r)
    }

    fn cap(root: &RootKey, subject: &str, domain: &str) -> DomainCap {
        DomainCap::new(mint_domains_cap(root, subject).encode(), domain)
    }

    #[test]
    fn welded_bind_seals_the_cell_and_verify_flips_through_the_executor() {
        let (reg, root) = setup();
        let c = cap(&root, "dregg:alice", "blog.example.com");
        let receipt = reg
            .bind(&c, "blog.example.com", "blog", ChallengeMethod::Txt)
            .expect("welded bind commits register + bind turns");
        assert_eq!(receipt.owner, "dregg:alice");

        // The per-domain cell actually carries the sealed DOMAIN + NONCE (the weld:
        // the routing record exists only because the cell turns committed).
        let cell = reg.domain_cell_id("blog.example.com");
        let st = reg.executor().cell_state(cell).expect("cell exists");
        assert_ne!(
            st.fields[DOMAIN_SLOT as usize], [0u8; 32],
            "DOMAIN sealed on the cell"
        );
        assert_ne!(
            st.fields[crate::CHALLENGE_NONCE_SLOT as usize],
            [0u8; 32],
            "CHALLENGE_NONCE sealed on the cell"
        );
        assert_eq!(
            field_to_u64(&st.fields[VERIFICATION_STATE_SLOT as usize]),
            VerificationState::Pending.code()
        );

        // Unverified → no route.
        assert!(!reg.index().is_verified("blog.example.com"));

        // Wrong nonce refused.
        let wrong = MockDns::new().with_txt(&receipt.challenge.record_name, "dregg-verify-nope");
        assert!(matches!(
            reg.verify("blog.example.com", &wrong),
            Err(WeldError::Domain(DomainError::ChallengeUnmet { .. }))
        ));

        // Right nonce → the verify TURN flips the cell 0 -> 1, and the index resolves.
        let dns = MockDns::new().with_txt(
            &receipt.challenge.record_name,
            &receipt.challenge.expected_value,
        );
        let b = reg.verify("blog.example.com", &dns).expect("welded verify");
        assert!(b.is_verified());
        let st = reg.executor().cell_state(cell).unwrap();
        assert_eq!(
            field_to_u64(&st.fields[VERIFICATION_STATE_SLOT as usize]),
            VerificationState::Verified.code(),
            "the cell flipped to Verified through a real turn"
        );
        assert_eq!(
            reg.index().site_for_host("blog.example.com").as_deref(),
            Some("blog")
        );
    }

    #[test]
    fn welded_revalidate_demotes_to_revoked_via_a_monotonic_forward_turn() {
        let (reg, root) = setup();
        let c = cap(&root, "dregg:alice", "shop.example.com");
        let r = reg
            .bind(&c, "shop.example.com", "shop", ChallengeMethod::Txt)
            .unwrap();
        let dns = MockDns::new().with_txt(&r.challenge.record_name, &r.challenge.expected_value);
        reg.verify("shop.example.com", &dns).unwrap();
        assert!(reg.index().is_verified("shop.example.com"));

        // The owner loses DNS control (record gone): re-validation demotes to Revoked.
        let gone = MockDns::new();
        let state = reg.revalidate("shop.example.com", &gone).unwrap();
        assert_eq!(state, VerificationState::Revoked);
        // Stops routing immediately.
        assert!(!reg.index().is_verified("shop.example.com"));
        assert_eq!(reg.index().site_for_host("shop.example.com"), None);
        // The cell advanced 1 -> 2 (a Monotonic-forward transition).
        let cell = reg.domain_cell_id("shop.example.com");
        let st = reg.executor().cell_state(cell).unwrap();
        assert_eq!(
            field_to_u64(&st.fields[VERIFICATION_STATE_SLOT as usize]),
            VerificationState::Revoked.code()
        );

        // Terminal: a revoked binding cannot be re-verified.
        assert!(matches!(
            reg.verify("shop.example.com", &dns),
            Err(WeldError::Domain(DomainError::BindingRevoked { .. }))
        ));
    }

    #[test]
    fn welded_owner_repoint_preserves_verification() {
        let (reg, root) = setup();
        let c = cap(&root, "dregg:alice", "www.example.com");
        let r = reg
            .bind(&c, "www.example.com", "one", ChallengeMethod::Txt)
            .unwrap();
        let dns = MockDns::new().with_txt(&r.challenge.record_name, &r.challenge.expected_value);
        reg.verify("www.example.com", &dns).unwrap();
        assert_eq!(
            reg.index().site_for_host("www.example.com").as_deref(),
            Some("one")
        );

        // Re-point to a different site: no re-proof, verification preserved.
        reg.bind(&c, "www.example.com", "two", ChallengeMethod::Txt)
            .expect("owner re-point");
        assert_eq!(
            reg.index().site_for_host("www.example.com").as_deref(),
            Some("two")
        );
        assert!(reg.index().is_verified("www.example.com"));
    }

    #[test]
    fn a_revoked_credential_cannot_bind_through_the_weld() {
        let (reg, root) = setup();
        let c = cap(&root, "dregg:mallory", "evil.example.com");
        reg.index()
            .revoke_credential(credential_fingerprint(&c.credential));
        assert!(matches!(
            reg.bind(&c, "evil.example.com", "evil", ChallengeMethod::Txt),
            Err(WeldError::Domain(DomainError::CredentialRevoked { .. }))
        ));
    }
}
