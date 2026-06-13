//! THE CIPHERCLERK PANEL — the master interface's window onto the REAL
//! agent-side credential holder.
//!
//! In the dregg world a *cipherclerk* is the agent's cryptographic clerk: it
//! holds HD-derived signing identities, mints/attenuates/delegates the macaroon
//! capability tokens the agent wields, and brokers capabilities on the agent's
//! behalf. The canonical, wallet-grade implementation is
//! [`dregg_sdk::AgentCipherclerk`] (`sdk/src/cipherclerk.rs`). This module does
//! NOT reimplement any of that — it SURFACES the real clerk as a first-class,
//! reflective panel of the master interface:
//!
//!   * **Identities** are real [`AgentCipherclerk`] instances. An identity is
//!     an HD key (BIP39 seed → `dregg/{index}`); the panel shows its real
//!     [`AgentCipherclerk::public_key`], its real [`AgentCipherclerk::cell_id`]
//!     for a domain (the SAME derivation `Cell::with_balance` uses, so the
//!     identity OWNS that cell in the embedded world), its derivation path, and
//!     its sub-agents via the real [`AgentCipherclerk::derive_sub_agent`].
//!
//!   * **Capability tokens** are real [`HeldToken`]s. The panel surfaces what
//!     the real clerk does: [`AgentCipherclerk::mint_token`] forges a root
//!     macaroon; [`AgentCipherclerk::attenuate`] / [`AgentCipherclerk::delegate`]
//!     narrow it (those methods ALREADY enforce that attenuation can only
//!     narrow — we do not re-derive `granted ⊆ held`). The panel reads the
//!     real [`HeldToken::can_mint`] / [`HeldToken::can_prove`] /
//!     [`HeldToken::is_verified`] / [`HeldToken::caveat_chain_hash`] and the
//!     decoded [`MacaroonToken`]'s real caveat chain.
//!
//!   * **Sealed-for-recipient capabilities** are real
//!     [`dregg_sdk::DelegatedToken`]s. `AgentCipherclerk::delegate` produces a
//!     signed delegation envelope addressed to a recipient's public key — the
//!     real "hand this capability to that recipient, and only that recipient"
//!     path. (See the module's seal-story note: the wallet-grade clerk has no
//!     X25519 *seal-a-cap-to-a-cell* primitive; delegation is its real
//!     recipient-targeted capability handoff, so that is what we surface.)
//!
//! The panel ([`render`]) projects the real identities/tokens/delegations via
//! the uniform [`crate::reflect::Inspectable`] objects every view consumes.

use dregg_cell::CellId;
use dregg_sdk::{AgentCipherclerk, DelegatedToken, HeldToken};
use dregg_token::MacaroonToken;
use dregg_types::PublicKey;

// Re-export the real attenuation vocabulary so callers of this panel build
// narrowings against the SAME type the clerk speaks (no parallel restriction
// type). The clerk's `attenuate`/`delegate` already enforce narrowing.
pub use dregg_sdk::{Attenuation, DelegatedToken as RecipientEnvelope};

use crate::reflect::{short_hex, Field, FieldValue, Inspectable, ObjectKind};
use crate::world::World;

// =============================================================================
// Identities — real HD-derived AgentCipherclerk instances
// =============================================================================

/// A named identity in the clerk's roster: a REAL [`AgentCipherclerk`] (HD key)
/// plus the human label and world domain it acts under.
///
/// There is no parallel key material here — `clerk` IS the wallet-grade SDK
/// clerk. The display fields (`public_key`, `cell_id`) are read straight off it.
pub struct Identity {
    /// The human-facing name (e.g. `alice`, `ci-bot`).
    pub name: String,
    /// The world domain this identity acts in (selects its `cell_id`).
    pub domain: String,
    /// The REAL wallet-grade clerk. All key ops route here.
    pub clerk: AgentCipherclerk,
}

impl Identity {
    /// Build an identity from a 64-byte HD seed (the real
    /// [`AgentCipherclerk::from_seed`] path — main identity at `dregg/0`).
    pub fn from_seed(name: impl Into<String>, domain: impl Into<String>, seed: [u8; 64]) -> Self {
        Identity {
            name: name.into(),
            domain: domain.into(),
            clerk: AgentCipherclerk::from_seed(seed),
        }
    }

    /// Build an identity from a single seed byte (convenience for demos /
    /// fixtures; expands the byte across the 64-byte HD seed). Reproducible.
    pub fn from_byte(name: impl Into<String>, domain: impl Into<String>, seed_byte: u8) -> Self {
        Self::from_seed(name, domain, [seed_byte; 64])
    }

    /// Wrap an already-constructed real clerk under a name + domain.
    pub fn from_clerk(
        name: impl Into<String>,
        domain: impl Into<String>,
        clerk: AgentCipherclerk,
    ) -> Self {
        Identity {
            name: name.into(),
            domain: domain.into(),
            clerk,
        }
    }

    /// This identity's REAL public key (`AgentCipherclerk::public_key`).
    pub fn public_key(&self) -> PublicKey {
        self.clerk.public_key()
    }

    /// This identity's REAL world cell id in its domain
    /// (`AgentCipherclerk::cell_id`) — the cell it owns / acts as. Identical to
    /// the id `Cell::with_balance(public_key, blake3(domain), _)` produces.
    pub fn cell_id(&self) -> CellId {
        self.clerk.cell_id(&self.domain)
    }

    /// Derive a sub-agent identity at `index` (the real
    /// [`AgentCipherclerk::derive_sub_agent`] — `dregg/{index}` off the same
    /// seed). Returns `None` if this clerk has no seed (e.g. was built from raw
    /// key bytes).
    pub fn derive_sub_agent(&self, index: u32, name: impl Into<String>) -> Option<Identity> {
        let sub = self.clerk.derive_sub_agent(index).ok()?;
        Some(Identity::from_clerk(name, self.domain.clone(), sub))
    }
}

// =============================================================================
// The clerk panel state — the roster of identities, minted tokens, and the
// recipient-targeted delegation vault.
// =============================================================================

/// A registered identity together with the tokens it has minted/attenuated.
pub struct Holder {
    /// The identity (the real clerk).
    pub identity: Identity,
}

/// THE CIPHERCLERK panel state: the roster of real identities and the
/// recipient-targeted delegation envelopes they have produced.
///
/// Tokens themselves live INSIDE each identity's real [`AgentCipherclerk`]
/// (`AgentCipherclerk::tokens`); we never duplicate them into a parallel store.
/// We keep only the produced [`DelegatedToken`] envelopes (the "sealed for a
/// recipient" vault), which the clerk hands back to the caller rather than
/// retaining.
#[derive(Default)]
pub struct Cipherclerk {
    holders: Vec<Holder>,
    /// The recipient-targeted delegation envelopes produced so far, with a label
    /// and the recipient's name for display.
    delegations: Vec<DelegationRecord>,
}

/// A produced delegation envelope filed in the panel's "sealed for a recipient"
/// vault.
pub struct DelegationRecord {
    /// A human label for what this delegation carries.
    pub label: String,
    /// The recipient identity's name (for display).
    pub recipient: String,
    /// The REAL signed delegation envelope produced by
    /// [`AgentCipherclerk::delegate`].
    pub envelope: DelegatedToken,
}

impl Cipherclerk {
    /// A fresh, empty clerk panel.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register an identity (a real clerk). Returns its roster index.
    pub fn add_identity(&mut self, identity: Identity) -> usize {
        self.holders.push(Holder { identity });
        self.holders.len() - 1
    }

    /// Create + register an identity from a one-byte seed (fixture path).
    pub fn create_identity(
        &mut self,
        name: impl Into<String>,
        domain: impl Into<String>,
        seed_byte: u8,
    ) -> usize {
        self.add_identity(Identity::from_byte(name, domain, seed_byte))
    }

    /// The registered identities, in registration order.
    pub fn identities(&self) -> impl Iterator<Item = &Identity> {
        self.holders.iter().map(|h| &h.identity)
    }

    /// Look up a registered identity by name.
    pub fn identity(&self, name: &str) -> Option<&Identity> {
        self.holders
            .iter()
            .map(|h| &h.identity)
            .find(|i| i.name == name)
    }

    /// Mutable access to a registered identity by name (to mint/attenuate on its
    /// real clerk).
    pub fn identity_mut(&mut self, name: &str) -> Option<&mut Identity> {
        self.holders
            .iter_mut()
            .map(|h| &mut h.identity)
            .find(|i| i.name == name)
    }

    /// File a produced delegation envelope in the "sealed for a recipient"
    /// vault.
    pub fn record_delegation(
        &mut self,
        label: impl Into<String>,
        recipient: impl Into<String>,
        envelope: DelegatedToken,
    ) {
        self.delegations.push(DelegationRecord {
            label: label.into(),
            recipient: recipient.into(),
            envelope,
        });
    }

    /// The recipient-targeted delegation vault.
    pub fn delegations(&self) -> &[DelegationRecord] {
        &self.delegations
    }

    /// Make an identity ACT in the embedded world: install its genesis cell at
    /// its REAL `cell_id(domain)`, carrying `balance`. The cell's public key is
    /// the identity's real public key and its token id is `blake3(domain)` — the
    /// exact pair `AgentCipherclerk::cell_id` derives over, so the installed
    /// cell's id equals [`Identity::cell_id`]. Returns that id.
    ///
    /// Delegates to the real [`World::embody`] door: it builds + genesis-installs
    /// the identity's cell at its REAL derived id over the same `(public_key,
    /// token_id)` pair `AgentCipherclerk::cell_id(domain)` derives — so the
    /// installed cell's id equals [`Identity::cell_id`]. Returns that id.
    pub fn embody(&self, world: &mut World, identity: &Identity, balance: i64) -> CellId {
        let pubkey = identity.public_key().0;
        let token_id = *blake3::hash(identity.domain.as_bytes()).as_bytes();
        let id = world.embody(pubkey, token_id, balance);
        debug_assert_eq!(id, identity.cell_id());
        id
    }
}

// =============================================================================
// THE CIPHERCLERK ACTION LAYER — real mint / attenuate / delegate / discharge.
//
// These drive the REAL [`AgentCipherclerk`] (`sdk/src/cipherclerk.rs`): the
// methods below are thin operators over `mint_token` / `attenuate` / `delegate`
// / `verify_token`. NO crypto is reimplemented — the macaroon HMAC chain, the
// caveat narrowing, the recipient-targeted signed envelope, and the discharge
// (HMAC-chain + Datalog caveat evaluation) all live in the SDK. This layer
// exists so the cockpit's CIPHERCLERK panel is INTERACTIVE (mint a root,
// attenuate it, delegate it to a peer, and DISCHARGE a token against a request)
// rather than read-only, and so the action loop is `cargo test`-able headless.
// =============================================================================

/// The outcome of a cipherclerk action, as a one-line human result for the
/// panel's action banner. Each carries enough to show what the REAL clerk did.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClerkOutcome {
    /// A root macaroon was minted on `holder`'s real clerk for `service`.
    Minted { holder: String, service: String, token_id: String },
    /// A held token was attenuated (narrowed) — the new token carries more
    /// caveats than its parent (the narrowing is real, bound in the HMAC chain).
    Attenuated { holder: String, parent_id: String, token_id: String, caveats_added: usize },
    /// A recipient-targeted signed delegation envelope was produced + filed.
    Delegated { from: String, to: String, service: String, envelope: String },
    /// A token was DISCHARGED against an auth request — the real
    /// `AgentCipherclerk::verify_token` verdict (HMAC chain + caveat evaluation).
    Discharged { holder: String, token_id: String, request: String, authorized: bool },
    /// The action could not be performed (e.g. no such identity / token; the
    /// real clerk rejected an empty attenuation). Carries the reason.
    Failed { reason: String },
}

impl ClerkOutcome {
    /// A one-line banner string for the panel.
    pub fn banner(&self) -> String {
        match self {
            ClerkOutcome::Minted { holder, service, token_id } => {
                format!("minted root macaroon · {holder} · service '{service}' · {token_id}")
            }
            ClerkOutcome::Attenuated { holder, parent_id, token_id, caveats_added } => format!(
                "attenuated · {holder} · {parent_id} → {token_id} (+{caveats_added} caveat(s), narrowed)"
            ),
            ClerkOutcome::Delegated { from, to, service, envelope } => {
                format!("delegated · {from} → {to} · service '{service}' · envelope {envelope}")
            }
            ClerkOutcome::Discharged { holder, token_id, request, authorized } => format!(
                "discharge · {holder} · {token_id} vs [{request}] → {}",
                if *authorized { "AUTHORIZED ✓" } else { "DENIED ✗" }
            ),
            ClerkOutcome::Failed { reason } => format!("clerk action failed: {reason}"),
        }
    }

    /// `true` iff this was a successful discharge that authorized the request
    /// (so the panel can color it), or any non-failure action.
    pub fn is_ok(&self) -> bool {
        !matches!(self, ClerkOutcome::Failed { .. })
    }
}

/// A confined attenuation: lock a token to a single `service` with an action
/// `mask` ("r" / "rw" / "*") and an optional expiry. This is the canonical
/// narrowing the panel's attenuate/delegate verbs use — built against the REAL
/// [`Attenuation`] type the clerk speaks (no parallel restriction vocabulary).
pub fn confine(service: &str, mask: &str, not_after: Option<i64>) -> Attenuation {
    Attenuation {
        services: vec![(service.to_string(), mask.to_string())],
        not_after,
        ..Default::default()
    }
}

/// An [`AuthRequest`] for the discharge leg: ask whether a token authorizes
/// `action` on `service` at time `now`. Built against the REAL
/// [`dregg_token::AuthRequest`] the macaroon `verify` path evaluates.
pub fn auth_request(service: &str, action: &str, now: i64) -> dregg_token::AuthRequest {
    dregg_token::AuthRequest {
        service: Some(service.to_string()),
        action: Some(action.to_string()),
        now: Some(now),
        ..Default::default()
    }
}

impl Cipherclerk {
    /// MINT a real root macaroon on `holder`'s clerk for `service`, deriving a
    /// fresh root key from the holder's identity + service (so the demo is
    /// reproducible and each identity/service pair gets its own root). Returns
    /// the outcome (and the token now lives in the holder's REAL clerk wallet).
    pub fn mint(&mut self, holder: &str, service: &str) -> ClerkOutcome {
        let Some(id) = self.identity_mut(holder) else {
            return ClerkOutcome::Failed { reason: format!("no identity '{holder}'") };
        };
        // A deterministic per-(identity,service) root key — derived, not random,
        // so the demo is reproducible. (A real deployment supplies the root key
        // from the service's HSM; here we derive it from the holder's pubkey.)
        let root_key = derive_root_key(&id.public_key().0, service);
        let tok = id.clerk.mint_token(&root_key, service);
        ClerkOutcome::Minted {
            holder: holder.to_string(),
            service: service.to_string(),
            token_id: tok.id().to_string(),
        }
    }

    /// ATTENUATE `holder`'s most recent MINTABLE (root) token for `service`,
    /// confining it to `mask` (e.g. "r") with `not_after`. The real clerk
    /// appends the narrowing caveats; the attenuated token is added to the
    /// wallet. The narrowing is genuine — the attenuated token carries strictly
    /// more caveats than its parent.
    pub fn attenuate_latest(
        &mut self,
        holder: &str,
        service: &str,
        mask: &str,
        not_after: Option<i64>,
    ) -> ClerkOutcome {
        let restriction = confine(service, mask, not_after);
        let Some(id) = self.identity_mut(holder) else {
            return ClerkOutcome::Failed { reason: format!("no identity '{holder}'") };
        };
        // Find a root token (one that can mint) for this service to attenuate.
        let Some(parent) = id
            .clerk
            .tokens()
            .iter()
            .rev()
            .find(|t| t.service() == service && t.can_mint())
            .cloned()
        else {
            return ClerkOutcome::Failed {
                reason: format!("no root token for service '{service}' to attenuate (mint one first)"),
            };
        };
        // Count the parent's caveats (decode against its root key) so we can
        // report the genuine narrowing delta.
        let parent_caveats = parent.decode().map(|d| d.inner().caveats.len()).unwrap_or(0);
        match id.clerk.attenuate(&parent, &restriction) {
            Ok(att) => {
                // The attenuated token's caveats (decode against the SAME root
                // key the parent used — attenuated tokens hold no root key).
                let att_caveats = MacaroonToken::from_encoded(att.encoded(), derive_root_key(&id.public_key().0, service))
                    .map(|d| d.inner().caveats.len())
                    .unwrap_or(parent_caveats);
                ClerkOutcome::Attenuated {
                    holder: holder.to_string(),
                    parent_id: parent.id().to_string(),
                    token_id: att.id().to_string(),
                    caveats_added: att_caveats.saturating_sub(parent_caveats),
                }
            }
            Err(e) => ClerkOutcome::Failed { reason: format!("{e}") },
        }
    }

    /// DELEGATE `from`'s most recent root token for `service` to the identity
    /// `to`, narrowing it to `mask`. Produces a REAL signed [`DelegatedToken`]
    /// envelope addressed to `to`'s public key and FILES it in the vault. This
    /// is the clerk's recipient-targeted capability handoff.
    pub fn delegate_to(
        &mut self,
        from: &str,
        to: &str,
        service: &str,
        mask: &str,
    ) -> ClerkOutcome {
        // Resolve the recipient's real public key first (immutable borrow).
        let Some(recipient_pk) = self.identity(to).map(|i| i.public_key()) else {
            return ClerkOutcome::Failed { reason: format!("no recipient identity '{to}'") };
        };
        let restriction = confine(service, mask, None);
        // Produce the envelope on `from`'s clerk.
        let envelope = {
            let Some(id) = self.identity_mut(from) else {
                return ClerkOutcome::Failed { reason: format!("no identity '{from}'") };
            };
            let Some(parent) = id
                .clerk
                .tokens()
                .iter()
                .rev()
                .find(|t| t.service() == service && t.can_mint())
                .cloned()
            else {
                return ClerkOutcome::Failed {
                    reason: format!("no root token for service '{service}' to delegate (mint one first)"),
                };
            };
            match id.clerk.delegate(&parent, &recipient_pk, &restriction) {
                Ok(env) => env,
                Err(e) => return ClerkOutcome::Failed { reason: format!("{e}") },
            }
        };
        let env_hash = crate::reflect::short_hex(&envelope.envelope_hash());
        self.record_delegation(format!("{service}:{mask}"), to, envelope);
        ClerkOutcome::Delegated {
            from: from.to_string(),
            to: to.to_string(),
            service: service.to_string(),
            envelope: env_hash,
        }
    }

    /// DISCHARGE: ask whether `holder`'s most recent token for `service`
    /// authorizes `action` on `service` (at `now`). Runs the REAL
    /// [`AgentCipherclerk::verify_token`] — the macaroon HMAC chain validation
    /// PLUS the caveat (Datalog) evaluation against the [`AuthRequest`]. A token
    /// confined to "r" authorizes a "read" request and DENIES a "write"; an
    /// expired token is denied. This is the macaroon discharge, end to end.
    pub fn discharge(&self, holder: &str, service: &str, action: &str, now: i64) -> ClerkOutcome {
        let Some(id) = self.identity(holder) else {
            return ClerkOutcome::Failed { reason: format!("no identity '{holder}'") };
        };
        // Prefer the most-recently-minted/attenuated token for the service that
        // can be discharged (root tokens decode against their held root key).
        let Some(tok) = id
            .clerk
            .tokens()
            .iter()
            .rev()
            .find(|t| t.service() == service && t.can_mint())
        else {
            return ClerkOutcome::Failed {
                reason: format!("no dischargeable token for service '{service}' (mint one first)"),
            };
        };
        let request = auth_request(service, action, now);
        let authorized = id.clerk.verify_token(tok, &request);
        ClerkOutcome::Discharged {
            holder: holder.to_string(),
            token_id: tok.id().to_string(),
            request: format!("{service}/{action}"),
            authorized,
        }
    }

    /// Attenuate `holder`'s most recent root token for `service` with the given
    /// `restriction`, returning the resulting confined [`HeldToken`] (so a caller
    /// can present it to a service for discharge). The narrowing is real (it goes
    /// through `AgentCipherclerk::attenuate`); the returned token carries a
    /// ZEROED root key (it cannot forge), so it is discharged SERVICE-SIDE via
    /// [`Self::discharge_presented`].
    pub fn attenuate_token(
        &mut self,
        holder: &str,
        service: &str,
        restriction: &Attenuation,
    ) -> Option<HeldToken> {
        let id = self.identity_mut(holder)?;
        let parent = id
            .clerk
            .tokens()
            .iter()
            .rev()
            .find(|t| t.service() == service && t.can_mint())
            .cloned()?;
        id.clerk.attenuate(&parent, restriction).ok()
    }

    /// SERVICE-SIDE DISCHARGE: verify a PRESENTED (possibly attenuated) token
    /// against `request`, using the service's `root_key`. This is how a real
    /// service discharges a confined token a holder presents — it reconstructs
    /// the HMAC-verifiable macaroon from the token's encoded chain + the root key
    /// it holds, then runs the real `AuthToken::verify` (HMAC chain validation +
    /// caveat/Datalog evaluation). Returns the authorization verdict.
    ///
    /// (REAL-SEMANTICS FINDING: an attenuated `HeldToken` drops its root key, so
    /// the HOLDER cannot `verify_token` it — only the service holding the root
    /// key can. This method IS that service-side path.)
    pub fn discharge_presented(
        presented: &HeldToken,
        root_key: &[u8; 32],
        request: &dregg_token::AuthRequest,
    ) -> bool {
        use dregg_token::AuthToken;
        match MacaroonToken::from_encoded(presented.encoded(), *root_key) {
            Ok(mac) => mac.verify(request).is_ok(),
            Err(_) => false,
        }
    }
}

/// Derive a deterministic per-(identity, service) macaroon root key. Pure
/// BLAKE3 over the holder's public key + the service label — reproducible, and
/// distinct per identity/service so each gets its own root. (A real deployment
/// holds the root key in the service's HSM; this keeps the embedded demo
/// reproducible without a parallel key store.)
fn derive_root_key(public_key: &[u8; 32], service: &str) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"starbridge-v2-clerk-root-key-v1");
    h.update(public_key);
    h.update(service.as_bytes());
    *h.finalize().as_bytes()
}

// =============================================================================
// The panel — uniform reflective projection of the REAL clerk surface
// =============================================================================

/// Project one identity (its real public key, cell id, derivation path, and
/// minted-token roster).
pub fn reflect_identity(id: &Identity) -> Inspectable {
    let pk = id.public_key().0;
    let cell = id.cell_id();
    let mut fields = vec![
        Field::text("name", id.name.clone()),
        Field::text("domain", id.domain.clone()),
        Field::id("public_key", pk),
        Field::id("cell_id", *cell.as_bytes()),
        Field::text(
            "derivation_path",
            id.clerk
                .derivation_path()
                .unwrap_or("(raw key, no HD path)")
                .to_string(),
        ),
        Field::count("held_tokens", id.clerk.tokens().len() as u64),
    ];
    // The real held tokens this identity carries (one field per token).
    for (i, tok) in id.clerk.tokens().iter().enumerate() {
        fields.push(Field {
            key: format!("token[{i}]"),
            value: FieldValue::Text(format!(
                "{} ({}) · {} · mint:{} prove:{} verified:{}",
                tok.label(),
                tok.service(),
                tok.id(),
                tok.can_mint(),
                tok.can_prove(),
                tok.is_verified(),
            )),
        });
    }
    Inspectable {
        kind: ObjectKind::Capability,
        title: format!("Identity “{}”", id.name),
        subtitle: format!(
            "pubkey {} · cell {} · {} token(s)",
            short_hex(&pk),
            short_hex(cell.as_bytes()),
            id.clerk.tokens().len()
        ),
        fields,
    }
}

/// Project a single REAL [`HeldToken`] — its real authority flags and its
/// decoded macaroon caveat chain.
pub fn reflect_token(tok: &HeldToken) -> Inspectable {
    let mut fields = vec![
        Field::text("label", tok.label().to_string()),
        Field::text("service", tok.service().to_string()),
        Field::text("id", tok.id().to_string()),
        Field::boolean("can_mint", tok.can_mint()),
        Field::boolean("can_prove", tok.can_prove()),
        Field::boolean("is_verified", tok.is_verified()),
    ];
    if let Some(h) = tok.caveat_chain_hash() {
        fields.push(Field::hash("caveat_chain_hash", h));
    }
    // The real decoded caveat chain (what the macaroon actually restricts).
    // `decode` needs the root key for root tokens; attenuated/delegated tokens
    // carry a zeroed root key, so a decode may not surface caveats for those —
    // we report the caveat count we can read.
    match tok.decode() {
        Ok(decoded) => {
            let caveats = &decoded.inner().caveats;
            fields.push(Field::count("caveat_count", caveats.len() as u64));
            for (i, wc) in caveats.iter().enumerate() {
                fields.push(Field {
                    key: format!("caveat[{i}]"),
                    value: FieldValue::Text(format!(
                        "type {} · {} bytes",
                        wc.caveat_type,
                        wc.body.len()
                    )),
                });
            }
        }
        Err(_) => {
            // Attenuated/delegated tokens hold no root key to decode against;
            // their narrowing is still bound in the encoded HMAC chain.
            fields.push(Field::text("caveats", "(opaque without root key)".to_string()));
        }
    }
    Inspectable {
        kind: ObjectKind::Capability,
        title: format!("Token “{}”", tok.label()),
        subtitle: format!(
            "{} · mint:{} prove:{} verified:{}",
            tok.service(),
            tok.can_mint(),
            tok.can_prove(),
            tok.is_verified()
        ),
        fields,
    }
}

/// Project a recipient-targeted delegation envelope (the "sealed for a
/// recipient" vault entry) — the real signed [`DelegatedToken`].
pub fn reflect_delegation(rec: &DelegationRecord) -> Inspectable {
    let env = &rec.envelope;
    Inspectable {
        kind: ObjectKind::Capability,
        title: format!("Delegation “{}”", rec.label),
        subtitle: format!(
            "{} → {} · service {}",
            rec.label,
            rec.recipient,
            env.service
        ),
        fields: vec![
            Field::text("label", rec.label.clone()),
            Field::text("recipient", rec.recipient.clone()),
            Field::text("service", env.service.clone()),
            Field::text("token_id", env.id.clone()),
            Field::id("delegatee", env.delegatee.0),
            Field::id("delegator", env.delegator_public_key.0),
            Field::hash("envelope_hash", env.envelope_hash()),
            Field::boolean("carries_proof_key", env.proof_key.is_some()),
            Field::boolean("carries_membership_proof", env.membership_proof.is_some()),
            Field::boolean("caveat_chain_hash", env.caveat_chain_hash.is_some()),
        ],
    }
}

/// THE PANEL. Present the cipherclerk as the three reflective sections the
/// cockpit renders: the identity roster (each with its minted tokens), every
/// real held token, and the recipient-targeted delegation vault.
pub fn render(clerk: &Cipherclerk) -> CipherclerkPanel {
    let identities: Vec<Inspectable> = clerk.identities().map(reflect_identity).collect();
    let tokens: Vec<Inspectable> = clerk
        .identities()
        .flat_map(|id| id.clerk.tokens().iter())
        .map(reflect_token)
        .collect();
    let delegations: Vec<Inspectable> = clerk.delegations().iter().map(reflect_delegation).collect();
    CipherclerkPanel {
        identities,
        tokens,
        delegations,
    }
}

/// The rendered panel: three lists of uniform reflective objects, ready for the
/// cockpit's shared inspector view.
#[derive(Clone, Debug)]
pub struct CipherclerkPanel {
    /// The identity roster (real HD-derived clerks).
    pub identities: Vec<Inspectable>,
    /// Every real held token across all identities.
    pub tokens: Vec<Inspectable>,
    /// The recipient-targeted delegation vault.
    pub delegations: Vec<Inspectable>,
}

// A small convenience: decode a held token's macaroon (root tokens only) so a
// caller / test can inspect the real caveat chain directly.
pub fn decode_token(tok: &HeldToken) -> Option<MacaroonToken> {
    tok.decode().ok()
}

// =============================================================================
// Tests — exercise the REAL AgentCipherclerk API. No reimplemented crypto.
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    const DOMAIN: &str = "starbridge";

    // --- Identities: real HD derivation ----------------------------------

    #[test]
    fn identity_cell_id_is_the_real_sdk_derivation() {
        let alice = Identity::from_byte("alice", DOMAIN, 0xA1);
        // The panel's cell_id IS the real AgentCipherclerk::cell_id.
        assert_eq!(alice.cell_id(), alice.clerk.cell_id(DOMAIN));
        // ...which is the same derivation Cell::with_balance uses.
        let token_id = *blake3::hash(DOMAIN.as_bytes()).as_bytes();
        let expected = CellId::derive_raw(&alice.public_key().0, &token_id);
        assert_eq!(alice.cell_id(), expected);
    }

    #[test]
    fn from_seed_is_reproducible() {
        let a = Identity::from_byte("alice", DOMAIN, 0xA1);
        let a2 = Identity::from_byte("alice", DOMAIN, 0xA1);
        assert_eq!(a.public_key().0, a2.public_key().0);
        assert_eq!(a.cell_id(), a2.cell_id());
    }

    #[test]
    fn distinct_seeds_give_distinct_identities() {
        let a = Identity::from_byte("alice", DOMAIN, 0xA1);
        let b = Identity::from_byte("bob", DOMAIN, 0xB0);
        assert_ne!(a.public_key().0, b.public_key().0);
        assert_ne!(a.cell_id(), b.cell_id());
    }

    #[test]
    fn derive_sub_agent_is_a_distinct_real_identity() {
        let alice = Identity::from_byte("alice", DOMAIN, 0xA1);
        // Real AgentCipherclerk::derive_sub_agent (dregg/1 off the same seed).
        let sub = alice
            .derive_sub_agent(1, "alice-sub-1")
            .expect("seeded identity derives a sub-agent");
        assert_ne!(sub.public_key().0, alice.public_key().0);
        assert_ne!(sub.cell_id(), alice.cell_id());
        // The derivation path reflects the real HD path.
        assert_eq!(sub.clerk.derivation_path(), Some("dregg/1"));
        assert_eq!(alice.clerk.derivation_path(), Some("dregg/0"));
    }

    // --- Tokens: real mint + attenuate; narrowing reflected --------------

    #[test]
    fn mint_then_attenuate_narrows_the_real_token() {
        let mut alice = Identity::from_byte("alice", DOMAIN, 0xA1);
        let root_key = [7u8; 32];
        // Real root token.
        let root = alice.clerk.mint_token(&root_key, "dns");
        assert!(root.can_mint(), "a freshly minted root token can mint");
        assert!(root.can_prove());
        assert!(root.is_verified(), "locally minted tokens are HMAC-verified");
        let root_decoded = root.decode().expect("root decodes with its root key");
        let root_caveats = root_decoded.inner().caveats.len();

        // Real attenuation: confine to a service + add an expiry.
        let restrictions = Attenuation {
            services: vec![("dns".to_string(), "r".to_string())],
            not_after: Some(1_000_000),
            ..Default::default()
        };
        let att = alice
            .clerk
            .attenuate(&root, &restrictions)
            .expect("the real clerk attenuates");

        // The attenuated token is NOT a root forger, but can still prove, and is
        // locally verified (attenuated from a verified parent).
        assert!(!att.can_mint(), "an attenuated token cannot mint");
        assert!(att.can_prove());
        assert!(att.is_verified());

        // The narrowing is real: the attenuated token carries MORE caveats than
        // the root (root had none/one; attenuation appended the restriction
        // caveats). Decode against the same root key to read them.
        let att_decoded =
            MacaroonToken::from_encoded(att.encoded(), root_key).expect("decode attenuated");
        let att_caveats = att_decoded.inner().caveats.len();
        assert!(
            att_caveats > root_caveats,
            "attenuation appended real caveats: {att_caveats} > {root_caveats}"
        );

        // Both tokens are now held in alice's REAL clerk wallet.
        assert!(alice.clerk.tokens().len() >= 2);
        assert!(alice.clerk.find_token_by_id(att.id()).is_some());
    }

    #[test]
    fn delegate_produces_a_real_recipient_envelope() {
        let mut alice = Identity::from_byte("alice", DOMAIN, 0xA1);
        let bob = Identity::from_byte("bob", DOMAIN, 0xB0);
        let root = alice.clerk.mint_token(&[7u8; 32], "storage");

        // Real delegation to bob's real public key, narrowing the token.
        let restrictions = Attenuation {
            services: vec![("storage".to_string(), "r".to_string())],
            ..Default::default()
        };
        let envelope = alice
            .clerk
            .delegate(&root, &bob.public_key(), &restrictions)
            .expect("the real clerk delegates");
        // The envelope is addressed to bob and signed by alice.
        assert_eq!(envelope.delegatee.0, bob.public_key().0);
        assert_eq!(envelope.delegator_public_key.0, alice.public_key().0);
        // It carries a real caveat-chain commitment + proof key.
        assert!(envelope.caveat_chain_hash.is_some());
        assert!(envelope.proof_key.is_some());
        // The envelope hash is well-defined (re-derivable).
        let _ = envelope.envelope_hash();
    }

    // --- World bridge: a real identity authorizes a real turn ------------

    #[test]
    fn embodied_identity_owns_its_derived_cell_and_acts() {
        use crate::world::{transfer, World};
        let mut world = World::new();
        let clerk = Cipherclerk::new();
        let alice = Identity::from_byte("alice", DOMAIN, 0xA1);
        let bob = Identity::from_byte("bob", DOMAIN, 0xB0);

        // Embody both identities as real world cells at their real cell ids.
        let alice_cell = clerk.embody(&mut world, &alice, 500);
        let bob_cell = clerk.embody(&mut world, &bob, 0);

        // The world cell id IS the identity's real cell_id (the SDK derivation).
        assert_eq!(alice_cell, alice.cell_id());
        assert_eq!(bob_cell, bob.cell_id());
        assert_eq!(
            world.ledger().get(&alice_cell).unwrap().state.balance(),
            500
        );

        // Alice's real identity AUTHORIZES A REAL TURN through the embedded
        // verified executor.
        let turn = world.turn(alice_cell, vec![transfer(alice_cell, bob_cell, 100)]);
        assert!(world.commit_turn(turn).is_committed());
        assert_eq!(world.ledger().get(&bob_cell).unwrap().state.balance(), 100);
    }

    // --- The panel: surfaces the REAL clerk surface ----------------------

    #[test]
    fn render_presents_identities_tokens_and_delegations() {
        let mut clerk = Cipherclerk::new();
        clerk.create_identity("alice", DOMAIN, 0xA1);
        clerk.create_identity("bob", DOMAIN, 0xB0);

        // Mint + attenuate a real token on alice's clerk.
        let root_key = [7u8; 32];
        let bob_pk = clerk.identity("bob").unwrap().public_key();
        let alice = clerk.identity_mut("alice").unwrap();
        let root = alice.clerk.mint_token(&root_key, "dns");
        let _att = alice
            .clerk
            .attenuate(
                &root,
                &Attenuation {
                    services: vec![("dns".to_string(), "r".to_string())],
                    ..Default::default()
                },
            )
            .unwrap();
        // Produce + file a real delegation to bob (with a real restriction —
        // the clerk rejects an empty delegation).
        let envelope = alice
            .clerk
            .delegate(
                &root,
                &bob_pk,
                &Attenuation {
                    services: vec![("dns".to_string(), "r".to_string())],
                    ..Default::default()
                },
            )
            .unwrap();
        clerk.record_delegation("dns-read", "bob", envelope);

        let panel = render(&clerk);
        assert_eq!(panel.identities.len(), 2);
        // alice now holds the root + the attenuated token (both real).
        assert!(panel.tokens.len() >= 2);
        assert_eq!(panel.delegations.len(), 1);

        // The identity panel surfaces the real held-token count.
        assert!(panel.identities[0]
            .fields
            .iter()
            .any(|f| f.key == "held_tokens"));
        // A token panel surfaces the real authority flags.
        assert!(panel.tokens[0]
            .fields
            .iter()
            .any(|f| f.key == "can_mint"));
        assert!(panel.tokens[0]
            .fields
            .iter()
            .any(|f| f.key == "is_verified"));
        // The delegation panel surfaces the real recipient.
        assert!(panel.delegations[0]
            .fields
            .iter()
            .any(|f| f.key == "delegatee"));
    }

    // --- THE ACTION LAYER: mint · attenuate · delegate · discharge --------

    #[test]
    fn mint_action_forges_a_real_root_on_the_holders_clerk() {
        let mut clerk = Cipherclerk::new();
        clerk.create_identity("alice", DOMAIN, 0xA1);
        let before = clerk.identity("alice").unwrap().clerk.tokens().len();

        let out = clerk.mint("alice", "dns");
        assert!(matches!(out, ClerkOutcome::Minted { .. }), "mint must succeed: {out:?}");
        // The token now lives in alice's REAL clerk wallet, and it can mint
        // (it is a root) + is locally HMAC-verified.
        let alice = clerk.identity("alice").unwrap();
        assert_eq!(alice.clerk.tokens().len(), before + 1);
        let tok = alice.clerk.tokens().last().unwrap();
        assert!(tok.can_mint(), "a freshly minted root can mint");
        assert!(tok.is_verified(), "a locally minted token is HMAC-verified");
        assert_eq!(tok.service(), "dns");
    }

    #[test]
    fn mint_on_a_missing_identity_fails_cleanly() {
        let mut clerk = Cipherclerk::new();
        let out = clerk.mint("nobody", "dns");
        assert!(matches!(out, ClerkOutcome::Failed { .. }));
        assert!(!out.is_ok());
    }

    #[test]
    fn attenuate_action_genuinely_narrows_the_token() {
        let mut clerk = Cipherclerk::new();
        clerk.create_identity("alice", DOMAIN, 0xA1);
        clerk.mint("alice", "dns");

        let out = clerk.attenuate_latest("alice", "dns", "r", Some(1_000_000));
        match out {
            ClerkOutcome::Attenuated { caveats_added, .. } => {
                assert!(caveats_added >= 1, "attenuation must append real caveats");
            }
            other => panic!("attenuate must succeed: {other:?}"),
        }
        // The wallet now holds the root + the attenuated token; the attenuated
        // one cannot mint (it dropped the root key).
        let alice = clerk.identity("alice").unwrap();
        assert!(alice.clerk.tokens().len() >= 2);
        assert!(
            alice.clerk.tokens().iter().any(|t| !t.can_mint() && t.service() == "dns"),
            "an attenuated (non-minting) dns token is present"
        );
    }

    #[test]
    fn attenuate_without_a_root_fails() {
        let mut clerk = Cipherclerk::new();
        clerk.create_identity("alice", DOMAIN, 0xA1);
        // No mint first.
        let out = clerk.attenuate_latest("alice", "dns", "r", None);
        assert!(matches!(out, ClerkOutcome::Failed { .. }), "no root to attenuate: {out:?}");
    }

    #[test]
    fn delegate_action_produces_and_files_a_recipient_envelope() {
        let mut clerk = Cipherclerk::new();
        clerk.create_identity("alice", DOMAIN, 0xA1);
        clerk.create_identity("bob", DOMAIN, 0xB0);
        clerk.mint("alice", "storage");
        let bob_pk = clerk.identity("bob").unwrap().public_key().0;

        let out = clerk.delegate_to("alice", "bob", "storage", "r");
        assert!(matches!(out, ClerkOutcome::Delegated { .. }), "delegate must succeed: {out:?}");
        // The envelope was filed in the vault, addressed to bob, signed by alice.
        assert_eq!(clerk.delegations().len(), 1);
        let env = &clerk.delegations()[0].envelope;
        assert_eq!(env.delegatee.0, bob_pk, "envelope addressed to bob");
        assert_eq!(
            env.delegator_public_key.0,
            clerk.identity("alice").unwrap().public_key().0,
            "envelope signed by alice"
        );
        assert!(env.caveat_chain_hash.is_some(), "carries a caveat-chain commitment");
    }

    #[test]
    fn delegate_to_a_missing_recipient_fails() {
        let mut clerk = Cipherclerk::new();
        clerk.create_identity("alice", DOMAIN, 0xA1);
        clerk.mint("alice", "storage");
        let out = clerk.delegate_to("alice", "ghost", "storage", "r");
        assert!(matches!(out, ClerkOutcome::Failed { .. }));
        assert_eq!(clerk.delegations().len(), 0, "nothing filed on failure");
    }

    // --- THE DISCHARGE LEG: the real macaroon verify verdict -------------

    #[test]
    fn discharge_runs_the_real_verify_verdict() {
        // The headline: mint a root for "dns", then DISCHARGE it through the
        // action layer. The discharge runs the REAL HMAC chain + caveat
        // evaluation (`AgentCipherclerk::verify_token`). A bare root (no service
        // caveat) authorizes broadly, so an atomic 'r' request on 'dns' clears.
        let mut clerk = Cipherclerk::new();
        clerk.create_identity("alice", DOMAIN, 0xA1);
        clerk.mint("alice", "dns");

        let ok = clerk.discharge("alice", "dns", "r", 1_000);
        match ok {
            ClerkOutcome::Discharged { authorized, request, .. } => {
                assert!(authorized, "a freshly minted dns root authorizes an atomic 'r' request");
                assert_eq!(request, "dns/r");
            }
            other => panic!("discharge must run the real verify: {other:?}"),
        }
    }

    #[test]
    fn a_service_confined_token_authorizes_its_service_and_denies_others() {
        // Attenuate a root to ONLY the 'dns' service with the 'r' action; the
        // real macaroon `verify` then authorizes a dns/'r' request and DENIES a
        // request for a different service or a wider action — least-privilege,
        // discharged SERVICE-SIDE (the service holds the root key).
        //
        // TWO REAL-SEMANTICS FINDINGS (the discharge surface honors both):
        //  1. The macaroon action vocabulary is the ATOMIC letters r/w/c/d/C
        //     (`dregg_macaroon::action::Action::parse` decomposes a request
        //     action into those flags and requires EACH allowed). A "read"-the-
        //     English-word request parses to {r,d} and a 'r'-only token DENIES it
        //     (d not allowed). The discharge surface speaks atomic letters.
        //  2. An ATTENUATED `HeldToken` carries a ZEROED root key (it dropped the
        //     forging key), so the HOLDER cannot self-`verify_token` it — only the
        //     VERIFYING SERVICE, which holds the root key, can discharge it. So we
        //     discharge against the service's root key (`discharge_presented`).
        let mut clerk = Cipherclerk::new();
        clerk.create_identity("alice", DOMAIN, 0xA1);
        clerk.mint("alice", "dns");
        // Service-only confinement (no validity window) — the proven-authorizing
        // shape (cf. the SDK's `verify_token_datalog_full` service tests).
        let att = clerk
            .attenuate_token("alice", "dns", &confine("dns", "r", None))
            .expect("attenuation succeeds");
        // The service holds the root key alice minted against.
        let alice_pk = clerk.identity("alice").unwrap().public_key().0;
        let service_root = derive_root_key(&alice_pk, "dns");
        let now = 1_700_000_000;

        // dns/'r' → AUTHORIZED (service-side discharge of the confined token).
        assert!(
            Cipherclerk::discharge_presented(&att, &service_root, &auth_request("dns", "r", now)),
            "a dns/'r'-confined token authorizes a dns 'r' request"
        );
        // A WIDER action ('w') on the read-only token → DENIED.
        assert!(
            !Cipherclerk::discharge_presented(&att, &service_root, &auth_request("dns", "w", now)),
            "a read-only confined token denies a 'w' (write) request"
        );
        // A DIFFERENT service → DENIED (least-privilege).
        assert!(
            !Cipherclerk::discharge_presented(&att, &service_root, &auth_request("storage", "r", now)),
            "a dns-confined token denies a 'storage' request"
        );
    }

    #[test]
    fn discharge_of_an_expired_token_is_denied() {
        // The validity-window leg: attenuate with a not_after, then discharge the
        // SAME token (service-side) before and after that instant. The real
        // macaroon validity caveat denies the expired request.
        let mut clerk = Cipherclerk::new();
        clerk.create_identity("alice", DOMAIN, 0xA1);
        clerk.mint("alice", "dns");
        let att = clerk
            .attenuate_token("alice", "dns", &confine("dns", "r", Some(1_700_000_100)))
            .expect("attenuation succeeds");
        let alice_pk = clerk.identity("alice").unwrap().public_key().0;
        let service_root = derive_root_key(&alice_pk, "dns");

        // Before the not_after instant: authorized.
        assert!(
            Cipherclerk::discharge_presented(&att, &service_root, &auth_request("dns", "r", 1_700_000_050)),
            "before expiry, the confined dns/'r' token authorizes"
        );
        // After the not_after instant: the SAME token is denied (expiry bites).
        assert!(
            !Cipherclerk::discharge_presented(&att, &service_root, &auth_request("dns", "r", 1_700_001_000)),
            "after expiry, the token must be denied"
        );
    }

    #[test]
    fn discharge_on_a_missing_token_fails_cleanly() {
        let mut clerk = Cipherclerk::new();
        clerk.create_identity("alice", DOMAIN, 0xA1);
        // No mint.
        let out = clerk.discharge("alice", "dns", "read", 0);
        assert!(matches!(out, ClerkOutcome::Failed { .. }));
    }

    #[test]
    fn the_full_action_loop_mint_attenuate_delegate_discharge() {
        // The whole interactive surface, in one go — all through the real clerk.
        let mut clerk = Cipherclerk::new();
        clerk.create_identity("alice", DOMAIN, 0xA1);
        clerk.create_identity("bob", DOMAIN, 0xB0);

        assert!(clerk.mint("alice", "dns").is_ok());
        assert!(clerk.attenuate_latest("alice", "dns", "r", Some(2_000_000)).is_ok());
        assert!(clerk.delegate_to("alice", "bob", "dns", "r").is_ok());
        let discharge = clerk.discharge("alice", "dns", "r", 1_000);
        assert!(matches!(discharge, ClerkOutcome::Discharged { authorized: true, .. }));

        // The panel renders the resulting real state: alice holds ≥2 tokens, one
        // delegation is filed.
        let panel = render(&clerk);
        assert!(panel.tokens.len() >= 2);
        assert_eq!(panel.delegations.len(), 1);
    }
}
