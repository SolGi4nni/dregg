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
}
