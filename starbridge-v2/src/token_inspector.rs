//! L7 — TOKENS & CIPHERCLERK on the moldable-inspector spine.
//!
//! `reflect.rs`/`cipherclerk.rs` already SURFACE the real agent-side credential
//! holder (`dregg_sdk::AgentCipherclerk`, its `HeldToken`s, its
//! `DelegatedToken` envelopes) as flat field trees. This module lifts the token
//! family onto the moldable-inspector spine (`presentable.rs`): each token kind
//! offers a presentation SET — the [`PresentationKind::Trace`] HMAC caveat chain,
//! the [`PresentationKind::Provenance`] attenuation lineage (mint→attenuate→
//! delegate), the [`PresentationKind::Source`] caveats in the atomic-letter
//! vocabulary (r/w/c/d/C — what the macaroon actually restricts, legible), and
//! the mandatory [`PresentationKind::RawFields`] floor.
//!
//! NO crypto is reinvented here. Every datum is read off the REAL machinery:
//!
//!   * the real [`HeldToken`] authority flags / decoded caveat chain
//!     (`dregg_sdk::HeldToken`),
//!   * the real macaroon HMAC chain tail and per-caveat advance
//!     (`dregg_token::dregg_macaroon::Macaroon` — `tail = HMAC(prev, wire)`),
//!   * the real attenuation/delegation actions
//!     (`crate::cipherclerk::Cipherclerk`'s mint/attenuate/delegate/discharge,
//!     which drive the REAL `AgentCipherclerk`),
//!   * the real DISCHARGE verdict (`AuthToken::verify` — HMAC chain validation +
//!     caveat/Datalog evaluation against an `AuthRequest`).
//!
//! Two real-semantics findings (mirrored from `cipherclerk.rs`) are honored:
//!   1. The macaroon action vocabulary is the ATOMIC letters r/w/c/d/C; a token
//!      confined to "r" DENIES a "w". The Source presentation speaks atomic
//!      letters via the real `Action` `Display` + `dregg_caveats::decode_grant`.
//!   2. An ATTENUATED `HeldToken` carries a ZEROED root key (it dropped the
//!      forging key) — so the HOLDER cannot self-verify a confined token; the
//!      SERVICE, holding the root key, discharges it. The committing gadget
//!      surfaces BOTH legs: the mint→attenuate→delegate construction, and the
//!      service-side discharge.
//!
//! Everything here is gpui-free and `cargo test`-able, exactly as
//! `presentable.rs`/`cipherclerk.rs` are. No gpui type crosses the boundary.

use dregg_sdk::{AgentCipherclerk, Attenuation, DelegatedToken, HeldToken};
use dregg_token::dregg_caveats::{decode_grant, DreggGrant};
use dregg_token::dregg_macaroon::{Macaroon, WireCaveat};
use dregg_token::{AuthRequest, AuthToken, MacaroonToken};

use crate::cipherclerk::{auth_request, confine};
use crate::presentable::{
    GadgetError, GadgetField, GadgetInput, GadgetValidation, Presentable, Presentation,
    PresentationBody, PresentationKind, TimelineEvent, TimelineView, TraceStep, TraceView,
};
use crate::reflect::{self, Field, FieldValue, Inspectable, ObjectKind};
use crate::{Gadget, PresentCtx};

// ===========================================================================
// §L7.0 — the legible caveat vocabulary (atomic letters r/w/c/d/C)
// ===========================================================================

/// Render one real [`WireCaveat`] in the legible vocabulary — the atomic-letter
/// action mask (r/w/c/d/C) for the grant it carries. Reads the REAL
/// `dregg_caveats::decode_grant`; the `Action` `Display` is the genuine
/// atomic-letter render (the same vocabulary the macaroon `verify` enforces).
pub fn caveat_legend(wc: &WireCaveat) -> String {
    match decode_grant(wc) {
        Ok(DreggGrant::App { id, actions }) => format!("app({id}) ⇒ {actions}"),
        Ok(DreggGrant::Service { name, actions }) => format!("service({name}) ⇒ {actions}"),
        Ok(DreggGrant::Feature(f)) => format!("feature({f})"),
        Ok(DreggGrant::ValidityWindow { not_before, not_after }) => format!(
            "valid[{}, {}]",
            not_before.map(|n| n.to_string()).unwrap_or_else(|| "-∞".into()),
            not_after.map(|n| n.to_string()).unwrap_or_else(|| "+∞".into()),
        ),
        Ok(DreggGrant::ConfineUser(u)) => format!("user({u})"),
        Ok(DreggGrant::OAuthProvider(p)) => format!("oauth-provider({p})"),
        Ok(DreggGrant::OAuthScope(s)) => format!("oauth-scope({s})"),
        Ok(DreggGrant::FeatureGlob { include, exclude }) => {
            format!("feature-glob(+{include:?} -{exclude:?})")
        }
        Ok(DreggGrant::Budget { id, class, limit, .. }) => {
            format!("budget({id} · {class} ≤ {limit})")
        }
        Ok(DreggGrant::Unknown(ty, body)) => format!("caveat#{ty} ({} bytes, opaque)", body.len()),
        // A caveat whose body cannot decode is still a real narrowing bound in the
        // HMAC chain — report its type honestly rather than swallow it.
        Err(_) => format!("caveat#{} ({} bytes, undecodable)", wc.caveat_type, wc.body.len()),
    }
}

// ===========================================================================
// §L7.1 — the Trace presentation: the real HMAC caveat chain, step by step
// ===========================================================================

/// Replay the REAL macaroon HMAC caveat chain into a [`TraceView`]: one step per
/// link, each showing the genuine running tail (`tail = HMAC(prev_tail, wire)`)
/// and the caveat that advanced it, legible in the atomic-letter vocabulary.
///
/// The chain is read off the real decoded [`Macaroon`] (`mac.tail` is the final
/// HMAC tail; `mac.caveats` is the genuine caveat chain). This is the macaroon's
/// integrity chain, not a re-derivation — the FINAL step prints the actual
/// committed `tail`, the value the real `verify` recomputes-and-compares against.
pub fn caveat_chain_trace(mac: &Macaroon) -> TraceView {
    let mut steps: Vec<TraceStep> = Vec::new();

    // Step 0 — the chain root: the initial tail seeded from the root key + nonce.
    steps.push(TraceStep {
        index: 0,
        label: format!(
            "root · kid={} · seeds tail = HMAC(root_key, nonce)",
            reflect::short_hex(&mac.nonce.kid)
        ),
    });

    // One step per caveat: the narrowing it adds. The macaroon advances its tail
    // as `tail = HMAC(prev_tail, wire.encode())`; the legend is the real grant.
    for (i, wc) in mac.caveats.iter().enumerate() {
        steps.push(TraceStep {
            index: i + 1,
            label: format!(
                "caveat[{i}] · {} · tail = HMAC(prev, [type {} · {} bytes])",
                caveat_legend(wc),
                wc.caveat_type,
                wc.body.len()
            ),
        });
    }

    // The terminal step: the genuine committed tail the real verify checks.
    steps.push(TraceStep {
        index: mac.caveats.len() + 1,
        label: format!(
            "committed tail = {} (verify recomputes from root_key and compares)",
            reflect::short_hex(&mac.tail)
        ),
    });

    TraceView { steps }
}

// ===========================================================================
// §L7.2 — the Provenance presentation: the attenuation lineage
// ===========================================================================

/// The lineage hops a token's authority passed through — mint → attenuate →
/// delegate. Reconstructed off the REAL token's own authority flags + caveat
/// chain (a root that `can_mint` is the mint origin; each caveat is an
/// attenuation hop; a `DelegatedToken` envelope is a delegation hop). This is a
/// real reading of the token, not a parallel history store.
pub fn attenuation_lineage(tok: &HeldToken, root_key: &[u8; 32]) -> TimelineView {
    let mut events: Vec<TimelineEvent> = Vec::new();

    // Hop 0 — MINT: the root macaroon for the service. A root token can mint.
    events.push(TimelineEvent {
        at: 0,
        label: format!(
            "mint · service '{}' · {}",
            tok.service(),
            if tok.can_mint() { "ROOT (can mint)" } else { "narrowed (cannot mint)" }
        ),
        hash: tok.caveat_chain_hash(),
    });

    // Hops 1..n — ATTENUATE: one per real caveat in the chain (the genuine
    // narrowing hops). Decode against the supplied root key (attenuated tokens
    // hold a zeroed root key, so the chain is read with the service's key).
    if let Ok(mac) = MacaroonToken::from_encoded(tok.encoded(), *root_key) {
        for (i, wc) in mac.inner().caveats.iter().enumerate() {
            events.push(TimelineEvent {
                at: (i as u64) + 1,
                label: format!("attenuate · {}", caveat_legend(wc)),
                hash: None,
            });
        }
    }

    TimelineView { events }
}

/// The delegation hop of a [`DelegatedToken`] envelope — the recipient-targeted
/// handoff (the third lineage stage). Reads the REAL signed envelope fields.
pub fn delegation_hop(env: &DelegatedToken) -> TimelineEvent {
    TimelineEvent {
        at: u64::MAX, // delegation is the terminal hop of the lineage
        label: format!(
            "delegate · service '{}' · → delegatee {} · signed by {}",
            env.service,
            reflect::short_hex(&env.delegatee.0),
            reflect::short_hex(&env.delegator_public_key.0),
        ),
        hash: Some(env.envelope_hash()),
    }
}

// ===========================================================================
// §L7.3 — the Source presentation: caveats in the atomic-letter vocabulary
// ===========================================================================

/// The decoded caveat catalog as legible prose (the Source/"what-is" face): each
/// caveat in the atomic-letter vocabulary, one per line. Reads the REAL caveat
/// chain off the decoded macaroon.
pub fn caveats_source(mac: &Macaroon) -> String {
    if mac.caveats.is_empty() {
        return format!(
            "token '{}': NO caveats — a bare root authorizes broadly until attenuated.",
            reflect::short_hex(&mac.nonce.kid)
        );
    }
    let mut s = String::new();
    s.push_str("caveats (each narrows the authority; ALL must clear at discharge):\n");
    for (i, wc) in mac.caveats.iter().enumerate() {
        s.push_str(&format!("  [{i}] {}\n", caveat_legend(wc)));
    }
    s
}

// ===========================================================================
// §L7.4 — the RawFields floor (the genuine reflect surface) + helpers
// ===========================================================================

/// Project a [`HeldToken`]'s RawFields floor — the genuine authority flags +
/// decoded caveat chain, reflected exactly as `cipherclerk::reflect_token` does.
fn held_raw_fields(tok: &HeldToken, root_key: &[u8; 32]) -> Inspectable {
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
    // Decode against the service's root key (attenuated tokens hold a zeroed key,
    // so the holder cannot decode them; the service-key path reads the chain).
    if let Ok(mac) = MacaroonToken::from_encoded(tok.encoded(), *root_key) {
        let caveats = &mac.inner().caveats;
        fields.push(Field::count("caveat_count", caveats.len() as u64));
        for (i, wc) in caveats.iter().enumerate() {
            fields.push(Field {
                key: format!("caveat[{i}]"),
                value: FieldValue::Text(caveat_legend(wc)),
            });
        }
    } else {
        fields.push(Field::text("caveats", "(opaque without the service root key)".to_string()));
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

/// A [`HeldToken`] wrapped together with the service root key it was minted
/// against — the inspectable token. The root key is what the SERVICE holds; it
/// is required to decode/discharge an attenuated token (whose own root key is
/// zeroed). This wrapper makes the token a [`Presentable`] without a parallel
/// model — every datum is read off the real `HeldToken` + `Macaroon`.
#[derive(Clone)]
pub struct InspectedToken {
    /// The REAL held token (its authority + encoded HMAC chain).
    pub token: HeldToken,
    /// The service root key the token was minted against (the SERVICE's key).
    pub root_key: [u8; 32],
}

impl InspectedToken {
    /// Wrap a real held token with the service root key it discharges against.
    pub fn new(token: HeldToken, root_key: [u8; 32]) -> Self {
        InspectedToken { token, root_key }
    }

    /// Decode the real macaroon against the service root key (`None` if the
    /// encoded chain does not validate under this key).
    pub fn macaroon(&self) -> Option<MacaroonToken> {
        MacaroonToken::from_encoded(self.token.encoded(), self.root_key).ok()
    }
}

impl Presentable for InspectedToken {
    fn object_kind(&self) -> ObjectKind {
        ObjectKind::Capability
    }

    fn present(&self, _ctx: &PresentCtx) -> Vec<Presentation> {
        let mut out: Vec<Presentation> = Vec::new();

        // (1) RawFields — the MANDATORY floor (the genuine reflect surface).
        let insp = held_raw_fields(&self.token, &self.root_key);
        out.push(Presentation {
            kind: PresentationKind::RawFields,
            label: "Token".to_string(),
            search_text: PresentationBody::Fields(insp.clone()).search_text(),
            body: PresentationBody::Fields(insp),
        });

        // The decoded macaroon (against the service key) backs the Trace/Source.
        let decoded = self.macaroon();

        // (2) Trace — the REAL HMAC caveat chain, step by step. (The step-by-step
        //     evaluation rides a `PresentationBody::Trace` payload under the
        //     `Invariant` kind — the integrity/commitment-binding readout the
        //     macaroon's HMAC chain IS.)
        if let Some(mac) = &decoded {
            let trace = caveat_chain_trace(mac.inner());
            out.push(Presentation {
                kind: PresentationKind::Invariant,
                label: "HMAC Caveat Chain".to_string(),
                search_text: format!(
                    "hmac chain {} {}",
                    self.token.service(),
                    trace.steps.iter().map(|s| s.label.as_str()).collect::<Vec<_>>().join(" ")
                ),
                body: PresentationBody::Trace(trace),
            });
        }

        // (3) Provenance — the attenuation lineage (mint → attenuate).
        let lineage = attenuation_lineage(&self.token, &self.root_key);
        out.push(Presentation {
            kind: PresentationKind::Provenance,
            label: "Attenuation Lineage".to_string(),
            search_text: format!(
                "lineage {} {}",
                self.token.service(),
                lineage.events.iter().map(|e| e.label.as_str()).collect::<Vec<_>>().join(" ")
            ),
            body: PresentationBody::Timeline(lineage),
        });

        // (4) Source — the caveats in the atomic-letter vocabulary, legible.
        let src = decoded
            .as_ref()
            .map(|m| caveats_source(m.inner()))
            .unwrap_or_else(|| "(token chain opaque without the service root key)".to_string());
        out.push(Presentation {
            kind: PresentationKind::Source,
            label: "Caveats".to_string(),
            search_text: format!("caveats source {src}"),
            body: PresentationBody::Prose(src),
        });

        out
    }
}

/// A [`DelegatedToken`] envelope wrapped as a [`Presentable`] — the recipient-
/// targeted handoff (the chain-of-trust face). Every datum reads off the real
/// signed envelope.
#[derive(Clone)]
pub struct InspectedDelegation {
    /// The REAL signed delegation envelope.
    pub envelope: DelegatedToken,
}

impl InspectedDelegation {
    /// Wrap a real delegation envelope.
    pub fn new(envelope: DelegatedToken) -> Self {
        InspectedDelegation { envelope }
    }
}

impl Presentable for InspectedDelegation {
    fn object_kind(&self) -> ObjectKind {
        ObjectKind::Capability
    }

    fn present(&self, _ctx: &PresentCtx) -> Vec<Presentation> {
        let env = &self.envelope;
        let mut out: Vec<Presentation> = Vec::new();

        // (1) RawFields — the genuine envelope reflection.
        let insp = Inspectable {
            kind: ObjectKind::Capability,
            title: format!("Delegation “{}”", env.label),
            subtitle: format!(
                "service {} · → {}",
                env.service,
                reflect::short_hex(&env.delegatee.0)
            ),
            fields: vec![
                Field::text("label", env.label.clone()),
                Field::text("service", env.service.clone()),
                Field::text("token_id", env.id.clone()),
                Field::id("delegatee", env.delegatee.0),
                Field::id("delegator", env.delegator_public_key.0),
                Field::hash("envelope_hash", env.envelope_hash()),
                Field::hash("parent_delegation_hash", env.parent_delegation_hash),
                Field::boolean("carries_proof_key", env.proof_key.is_some()),
                Field::boolean("carries_membership_proof", env.membership_proof.is_some()),
                Field::boolean("carries_caveat_chain_hash", env.caveat_chain_hash.is_some()),
            ],
        };
        out.push(Presentation {
            kind: PresentationKind::RawFields,
            label: "Envelope".to_string(),
            search_text: PresentationBody::Fields(insp.clone()).search_text(),
            body: PresentationBody::Fields(insp),
        });

        // (2) Provenance — the chain-of-trust hop: who → whom, signed.
        let hop = delegation_hop(env);
        let prov = TimelineView { events: vec![hop] };
        out.push(Presentation {
            kind: PresentationKind::Provenance,
            label: "Chain of Trust".to_string(),
            search_text: format!(
                "delegation {} {} {}",
                env.service,
                reflect::short_hex(&env.delegatee.0),
                reflect::short_hex(&env.delegator_public_key.0)
            ),
            body: PresentationBody::Timeline(prov),
        });

        out
    }
}

// ===========================================================================
// §L7.5 — the CommittingGadget: mint → attenuate → delegate → discharge
// ===========================================================================

/// The verdict a [`TokenLoopGadget`] yields: the confined [`HeldToken`] it built,
/// plus the real DISCHARGE verdict it ran (the authorize/deny of the confined
/// token's own service+action versus a wider one). This is the gadget's
/// `Output` — a real protocol value (a real token) AND the real verify verdict.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TokenLoopResult {
    /// The service the loop confined the token to.
    pub service: String,
    /// The atomic-letter action mask the token was confined to (e.g. "r").
    pub mask: String,
    /// `true` iff the confined token authorizes its OWN service+action when
    /// discharged service-side (the real `verify` verdict).
    pub authorizes_own: bool,
    /// `true` iff the confined token DENIES a wider action on its service (the
    /// least-privilege check — the real `verify` verdict).
    pub denies_wider: bool,
    /// The number of real caveats the attenuation appended (the genuine narrowing).
    pub caveats_added: usize,
}

/// THE mint → attenuate → delegate → discharge gadget. It reuses the REAL
/// cipherclerk action layer's primitives end to end — it does NOT reinvent any
/// crypto:
///
///   * MINT a root macaroon on the holder's real [`AgentCipherclerk`]
///     (`mint_token`),
///   * ATTENUATE it (confine to `service`/`mask`/`not_after`) via the real
///     `attenuate` (which already enforces narrowing; the confined token's root
///     key is ZEROED),
///   * DELEGATE the root to a recipient via the real `delegate` (a signed
///     recipient-targeted envelope),
///   * DISCHARGE the confined token SERVICE-SIDE — the holder cannot self-verify
///     a zeroed-root token, so we verify it against the service root key via the
///     real `AuthToken::verify` (HMAC chain validation + caveat evaluation).
///
/// It is a [`Gadget`] whose `Output` is the real verdict ([`TokenLoopResult`]);
/// it is a "verifier gadget" in the framework's taxonomy (it builds a real value
/// AND checks it against the live machinery), so `build()` runs the real crypto.
pub struct TokenLoopGadget {
    /// The HD seed the holder's real wallet-grade clerk is derived from. The
    /// gadget re-derives a fresh real [`AgentCipherclerk`] (via `from_seed`) for
    /// each loop, so `build(&self)` stays non-mutating without requiring the
    /// clerk to be `Clone` (it is not — it carries an IVC builder).
    seed: [u8; 64],
    /// The service the loop confines to.
    service: String,
    /// The atomic-letter action mask to confine to (default "r").
    mask: String,
    /// An optional expiry instant (the validity-window caveat).
    not_after: Option<i64>,
    /// The service root key the token is minted against (the SERVICE's key — what
    /// discharges the confined, zeroed-root token).
    root_key: [u8; 32],
}

impl TokenLoopGadget {
    /// Build the gadget over the holder's HD `seed` + the service root key the
    /// service holds. The derived clerk mints/attenuates against `root_key`, so
    /// the same key discharges the confined token service-side.
    pub fn new(seed: [u8; 64], service: impl Into<String>, root_key: [u8; 32]) -> Self {
        TokenLoopGadget {
            seed,
            service: service.into(),
            mask: "r".to_string(),
            not_after: None,
            root_key,
        }
    }

    /// A fresh real clerk derived from the holder's seed (`AgentCipherclerk::
    /// from_seed`) — the genuine wallet-grade clerk, re-derived per use.
    pub fn fresh_clerk(&self) -> AgentCipherclerk {
        AgentCipherclerk::from_seed(self.seed)
    }

    /// The confining [`Attenuation`] the gadget currently builds — against the
    /// REAL `Attenuation` type (`crate::cipherclerk::confine`), no parallel
    /// restriction vocabulary.
    pub fn restriction(&self) -> Attenuation {
        confine(&self.service, &self.mask, self.not_after)
    }

    /// MINT the root token for the service on `clerk`, returning the root
    /// [`HeldToken`] (it `can_mint`; it decodes against `root_key`).
    pub fn mint_root(&self, clerk: &mut AgentCipherclerk) -> HeldToken {
        clerk.mint_token(&self.root_key, &self.service)
    }

    /// ATTENUATE a root token to the confining restriction, via the REAL clerk
    /// `attenuate` (which enforces narrowing). The returned confined token holds
    /// a ZEROED root key (it cannot self-verify).
    pub fn attenuate(
        &self,
        clerk: &mut AgentCipherclerk,
        root: &HeldToken,
    ) -> Result<HeldToken, GadgetError> {
        let restriction = self.restriction();
        clerk
            .attenuate(root, &restriction)
            .map_err(|e| GadgetError::Lowering { reason: format!("attenuate failed: {e}") })
    }

    /// DELEGATE a root token to `recipient_pk` (a real signed envelope), via the
    /// REAL clerk `delegate`. The recipient-targeted capability handoff.
    pub fn delegate(
        &self,
        clerk: &mut AgentCipherclerk,
        root: &HeldToken,
        recipient_pk: &dregg_types::PublicKey,
    ) -> Result<DelegatedToken, GadgetError> {
        let restriction = self.restriction();
        clerk
            .delegate(root, recipient_pk, &restriction)
            .map_err(|e| GadgetError::Lowering { reason: format!("delegate failed: {e}") })
    }

    /// SERVICE-SIDE DISCHARGE of a confined token against `request` — the real
    /// `AuthToken::verify` (HMAC chain validation + caveat/Datalog evaluation)
    /// reconstructed from the encoded chain + the SERVICE's root key. This is how
    /// a service discharges a zeroed-root confined token a holder presents.
    pub fn discharge_presented(&self, presented: &HeldToken, request: &AuthRequest) -> bool {
        match MacaroonToken::from_encoded(presented.encoded(), self.root_key) {
            Ok(mac) => mac.verify(request).is_ok(),
            Err(_) => false,
        }
    }

    /// The number of real caveats a token carries (decoded against `root_key`).
    fn caveat_count(&self, tok: &HeldToken) -> usize {
        MacaroonToken::from_encoded(tok.encoded(), self.root_key)
            .map(|m| m.inner().caveats.len())
            .unwrap_or(0)
    }
}

impl Gadget for TokenLoopGadget {
    /// The real verdict: the confined token built + the real discharge verdict.
    type Output = TokenLoopResult;

    fn fields(&self) -> Vec<GadgetField> {
        vec![
            GadgetField::Enum {
                key: "service".to_string(),
                variants: vec![self.service.clone()],
            },
            // The atomic-letter action mask the macaroon vocabulary speaks.
            GadgetField::Enum {
                key: "mask".to_string(),
                variants: vec![
                    "r".to_string(),
                    "rw".to_string(),
                    "rwc".to_string(),
                    "*".to_string(),
                ],
            },
            GadgetField::U64 { key: "not_after".to_string(), min: 0, max: u64::MAX },
        ]
    }

    fn set(&mut self, field: &str, v: GadgetInput) {
        match (field, v) {
            ("service", GadgetInput::Variant(s)) => self.service = s,
            ("mask", GadgetInput::Variant(m)) => self.mask = m,
            ("not_after", GadgetInput::U64(t)) => self.not_after = Some(t as i64),
            _ => {}
        }
    }

    fn validate(&self) -> GadgetValidation {
        // Fail-closed: the macaroon action vocabulary is the atomic letters
        // r/w/c/d/C (and "*"); a mask must be non-empty and recognized — an empty
        // or all-unknown mask cannot confine, so it must not build.
        if self.service.trim().is_empty() {
            return GadgetValidation::Invalid { reason: "service must be non-empty".to_string() };
        }
        let recognized = self.mask.chars().any(|c| matches!(c, 'r' | 'w' | 'c' | 'd' | 'C' | '*'));
        if !recognized {
            return GadgetValidation::Invalid {
                reason: format!("mask '{}' has no atomic action letter (r/w/c/d/C/*)", self.mask),
            };
        }
        GadgetValidation::Ok
    }

    /// Run the full real loop and return the verdict. `build` clones the clerk so
    /// the gadget itself is unconsumed (a gadget's `build` reads, not mutates,
    /// `self`). The crypto is the REAL clerk's; nothing is reinvented.
    fn build(&self) -> Result<Self::Output, GadgetError> {
        if let GadgetValidation::Invalid { reason } = self.validate() {
            return Err(GadgetError::Incomplete { reason });
        }
        let mut clerk = self.fresh_clerk();
        let restriction = self.restriction();

        // MINT the root, ATTENUATE it to the confinement.
        let root = clerk.mint_token(&self.root_key, &self.service);
        let parent_caveats = self.caveat_count(&root);
        let confined = clerk
            .attenuate(&root, &restriction)
            .map_err(|e| GadgetError::Lowering { reason: format!("attenuate failed: {e}") })?;
        let caveats_added = self.caveat_count(&confined).saturating_sub(parent_caveats);

        // DISCHARGE service-side: the confined token authorizes ITS service+mask,
        // and DENIES a wider action (we widen 'r' → 'w'; if the mask is already
        // '*' there is no wider action, so the deny leg is vacuously satisfied).
        let now = self.not_after.map(|t| t - 1).unwrap_or(1_700_000_000);
        let own_action = first_atomic(&self.mask).unwrap_or('r');
        let authorizes_own = self.discharge_presented(
            &confined,
            &auth_request(&self.service, &own_action.to_string(), now),
        );
        let wider = wider_action(own_action);
        let denies_wider = match wider {
            Some(w) => {
                !self.discharge_presented(&confined, &auth_request(&self.service, &w.to_string(), now))
            }
            None => true, // mask already maximal — nothing wider to deny.
        };

        Ok(TokenLoopResult {
            service: self.service.clone(),
            mask: self.mask.clone(),
            authorizes_own,
            denies_wider,
            caveats_added,
        })
    }
}

/// The first atomic action letter of a mask (the action the confined token is
/// meant to authorize).
fn first_atomic(mask: &str) -> Option<char> {
    mask.chars().find(|c| matches!(c, 'r' | 'w' | 'c' | 'd' | 'C'))
}

/// A strictly-wider atomic action than `a` (for the least-privilege deny check):
/// read 'r' widens to write 'w'; write widens to control 'C'. `None` if there is
/// no canonical wider atomic (the deny leg is then vacuous).
fn wider_action(a: char) -> Option<char> {
    match a {
        'r' => Some('w'),
        'w' => Some('c'),
        'c' => Some('d'),
        'd' => Some('C'),
        _ => None,
    }
}

// ===========================================================================
// TESTS — the model, proven gpui-free, against the REAL AgentCipherclerk.
// No reimplemented crypto.
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::World;

    /// Alice's HD seed (for the gadget) + a real clerk + the service root key it
    /// mints against (the SERVICE's key).
    const ALICE_SEED: [u8; 64] = [0xA1; 64];

    fn alice_clerk() -> (AgentCipherclerk, [u8; 32]) {
        let clerk = AgentCipherclerk::from_seed(ALICE_SEED);
        let root_key = [7u8; 32];
        (clerk, root_key)
    }

    /// A throwaway PresentCtx — the token presentations don't read the world, so
    /// a minimal one cell-anchored world suffices.
    fn ctx_world() -> (World, dregg_cell::CellId) {
        let mut w = World::new();
        let anchor = w.genesis_cell(0x01, 0);
        (w, anchor)
    }

    // ── the RawFields floor + the multi-presentation set ────────────────────

    #[test]
    fn an_inspected_token_yields_the_raw_fields_floor_and_a_rich_set() {
        let (mut clerk, root_key) = alice_clerk();
        let root = clerk.mint_token(&root_key, "dns");
        let it = InspectedToken::new(root, root_key);

        let (w, anchor) = ctx_world();
        let ctx = PresentCtx::new(&w, anchor);
        let set = it.present(&ctx);

        // The MANDATORY floor is present and is a non-empty field tree.
        let raw = set
            .iter()
            .find(|p| p.kind == PresentationKind::RawFields)
            .expect("RawFields floor");
        match &raw.body {
            PresentationBody::Fields(i) => {
                assert!(i.fields.iter().any(|f| f.key == "service"));
                assert!(i.fields.iter().any(|f| f.key == "can_mint"));
            }
            other => panic!("RawFields must carry Fields, got {other:?}"),
        }

        // The token offers the HMAC-chain Trace (an Invariant-kind presentation
        // carrying a `PresentationBody::Trace`) + Provenance + Source beside the
        // RawFields floor.
        let kinds: Vec<_> = set.iter().map(|p| p.kind).collect();
        assert!(kinds.contains(&PresentationKind::Invariant), "Invariant present: {kinds:?}");
        assert!(kinds.contains(&PresentationKind::Provenance));
        assert!(kinds.contains(&PresentationKind::Source));
        // The HMAC-chain trace really is a Trace body (the step-by-step replay).
        assert!(
            set.iter().any(|p| matches!(p.body, PresentationBody::Trace(_))),
            "the HMAC caveat chain is a Trace body"
        );
    }

    // ── the Trace shows the real HMAC chain ─────────────────────────────────

    #[test]
    fn the_trace_replays_the_real_hmac_chain_and_grows_under_attenuation() {
        let (mut clerk, root_key) = alice_clerk();
        let root = clerk.mint_token(&root_key, "dns");

        // The root's trace: root step + committed-tail step (no caveats yet).
        let root_mac = MacaroonToken::from_encoded(root.encoded(), root_key).unwrap();
        let root_trace = caveat_chain_trace(root_mac.inner());
        let root_steps = root_trace.steps.len();
        // The committed-tail step prints the REAL macaroon tail.
        let tail_hex = reflect::short_hex(&root_mac.inner().tail);
        assert!(
            root_trace.steps.last().unwrap().label.contains(&tail_hex),
            "the terminal trace step prints the genuine committed HMAC tail"
        );

        // Attenuate → the confined token's trace has MORE steps (real caveats).
        let confined = clerk
            .attenuate(&root, &confine("dns", "r", Some(1_700_000_100)))
            .expect("attenuate");
        let att_mac = MacaroonToken::from_encoded(confined.encoded(), root_key).unwrap();
        let att_trace = caveat_chain_trace(att_mac.inner());
        assert!(
            att_trace.steps.len() > root_steps,
            "attenuation appends real HMAC links: {} > {}",
            att_trace.steps.len(),
            root_steps
        );
        // The added steps carry the legible atomic-letter caveats.
        assert!(
            att_trace.steps.iter().any(|s| s.label.contains("⇒ r") || s.label.contains("service")),
            "a confined-to-'r' caveat is legible in the trace: {:?}",
            att_trace.steps.iter().map(|s| &s.label).collect::<Vec<_>>()
        );
    }

    // ── attenuate genuinely narrows (more caveats) ──────────────────────────

    #[test]
    fn attenuate_genuinely_narrows_more_caveats_than_the_root() {
        let (mut clerk, root_key) = alice_clerk();
        let root = clerk.mint_token(&root_key, "dns");
        let root_caveats =
            MacaroonToken::from_encoded(root.encoded(), root_key).unwrap().inner().caveats.len();

        let confined = clerk
            .attenuate(&root, &confine("dns", "r", None))
            .expect("attenuate");
        let confined_caveats = MacaroonToken::from_encoded(confined.encoded(), root_key)
            .unwrap()
            .inner()
            .caveats
            .len();

        assert!(
            confined_caveats > root_caveats,
            "attenuation strictly narrows: {confined_caveats} > {root_caveats} caveats"
        );
        // The confined token dropped its forging key (the real-semantics finding).
        assert!(!confined.can_mint(), "an attenuated token carries a zeroed root key");
    }

    // ── discharge runs the REAL verify verdict (authorize own, deny wider) ───

    #[test]
    fn discharge_authorizes_the_confined_service_action_and_denies_a_wider_one() {
        // The headline: a token confined to dns/'r', discharged SERVICE-SIDE,
        // authorizes a dns/'r' request and DENIES a dns/'w' request — the real
        // `AuthToken::verify` (HMAC chain + caveat evaluation). The holder cannot
        // self-verify (zeroed root key); the service holds the root key.
        let (_clerk, root_key) = alice_clerk();
        let mut gadget = TokenLoopGadget::new(ALICE_SEED, "dns", root_key);
        gadget.set("mask", GadgetInput::Variant("r".to_string()));

        let mut clerk = gadget.fresh_clerk();
        let root = gadget.mint_root(&mut clerk);
        let confined = gadget.attenuate(&mut clerk, &root).expect("attenuate");

        let now = 1_700_000_000;
        // dns/'r' → AUTHORIZED.
        assert!(
            gadget.discharge_presented(&confined, &auth_request("dns", "r", now)),
            "a dns/'r'-confined token authorizes a dns 'r' request"
        );
        // dns/'w' → DENIED (least-privilege; 'w' wider than the confined 'r').
        assert!(
            !gadget.discharge_presented(&confined, &auth_request("dns", "w", now)),
            "a read-only confined token denies a 'w' request"
        );
        // A DIFFERENT service → DENIED.
        assert!(
            !gadget.discharge_presented(&confined, &auth_request("storage", "r", now)),
            "a dns-confined token denies a 'storage' request"
        );
    }

    #[test]
    fn the_gadget_build_runs_the_whole_loop_and_returns_the_real_verdict() {
        let (_clerk, root_key) = alice_clerk();
        let mut gadget = TokenLoopGadget::new(ALICE_SEED, "dns", root_key);
        gadget.set("mask", GadgetInput::Variant("r".to_string()));

        assert!(gadget.validate().is_ok());
        let result = gadget.build().expect("the loop builds + discharges");
        assert_eq!(result.service, "dns");
        assert_eq!(result.mask, "r");
        assert!(result.caveats_added >= 1, "the attenuation appended real caveats");
        assert!(result.authorizes_own, "the confined token authorizes its own service/action");
        assert!(result.denies_wider, "the confined token denies a wider action");
    }

    #[test]
    fn the_gadget_fails_closed_on_an_empty_mask() {
        let (_clerk, root_key) = alice_clerk();
        let mut gadget = TokenLoopGadget::new(ALICE_SEED, "dns", root_key);
        // A mask with no atomic action letter cannot confine — fail closed.
        gadget.set("mask", GadgetInput::Variant("xyz".to_string()));
        assert!(gadget.validate().is_fail_closed());
        assert!(matches!(gadget.build(), Err(GadgetError::Incomplete { .. })));
    }

    // ── the attenuation-lineage Provenance is real ──────────────────────────

    #[test]
    fn the_attenuation_lineage_provenance_is_real() {
        let (mut clerk, root_key) = alice_clerk();
        let root = clerk.mint_token(&root_key, "dns");
        let confined = clerk
            .attenuate(&root, &confine("dns", "r", Some(2_000_000)))
            .expect("attenuate");

        // The confined token's lineage: a mint hop + one attenuate hop per caveat.
        let lineage = attenuation_lineage(&confined, &root_key);
        assert!(!lineage.events.is_empty());
        assert!(
            lineage.events[0].label.contains("mint"),
            "hop 0 is the mint origin: {}",
            lineage.events[0].label
        );
        assert!(
            lineage.events.iter().any(|e| e.label.contains("attenuate")),
            "the lineage carries a real attenuation hop: {:?}",
            lineage.events.iter().map(|e| &e.label).collect::<Vec<_>>()
        );
        // The confined token is NOT a root (it cannot mint) — the lineage reads it.
        assert!(lineage.events[0].label.contains("cannot mint"));
    }

    // ── the delegation envelope presentation is real ────────────────────────

    #[test]
    fn the_delegation_envelope_presents_a_real_chain_of_trust() {
        let (mut clerk, root_key) = alice_clerk();
        let bob = AgentCipherclerk::from_seed([0xB0; 64]);
        let root = clerk.mint_token(&root_key, "storage");
        let env = clerk
            .delegate(&root, &bob.public_key(), &confine("storage", "r", None))
            .expect("delegate");

        let id = InspectedDelegation::new(env);
        let (w, anchor) = ctx_world();
        let ctx = PresentCtx::new(&w, anchor);
        let set = id.present(&ctx);

        // The RawFields floor surfaces the real recipient + signer.
        let raw = set.iter().find(|p| p.kind == PresentationKind::RawFields).unwrap();
        match &raw.body {
            PresentationBody::Fields(i) => {
                assert!(i.fields.iter().any(|f| f.key == "delegatee"));
                assert!(i.fields.iter().any(|f| f.key == "delegator"));
            }
            other => panic!("expected Fields, got {other:?}"),
        }

        // The Provenance chain-of-trust hop names the real recipient.
        let prov = set.iter().find(|p| p.kind == PresentationKind::Provenance).unwrap();
        match &prov.body {
            PresentationBody::Timeline(t) => {
                assert_eq!(t.events.len(), 1);
                assert!(t.events[0].label.contains("delegate"));
                assert!(
                    t.events[0].label.contains(&reflect::short_hex(&bob.public_key().0)),
                    "the chain-of-trust hop names the real delegatee"
                );
            }
            other => panic!("expected Timeline, got {other:?}"),
        }
    }

    // ── the Source presentation speaks the atomic-letter vocabulary ─────────

    #[test]
    fn the_source_presentation_speaks_the_atomic_letter_vocabulary() {
        let (mut clerk, root_key) = alice_clerk();
        let root = clerk.mint_token(&root_key, "dns");
        // A bare root has no caveats — the Source says so honestly.
        let root_mac = MacaroonToken::from_encoded(root.encoded(), root_key).unwrap();
        let root_src = caveats_source(root_mac.inner());
        assert!(root_src.contains("NO caveats"), "a bare root: {root_src}");

        // After confinement to 'r', the Source lists the real caveat legibly.
        let confined = clerk
            .attenuate(&root, &confine("dns", "r", None))
            .expect("attenuate");
        let att_mac = MacaroonToken::from_encoded(confined.encoded(), root_key).unwrap();
        let src = caveats_source(att_mac.inner());
        assert!(src.contains("caveats"), "the confined token lists its caveats: {src}");
        // The atomic-letter render appears (a service-confine to action 'r').
        assert!(
            src.contains("⇒ r") || src.contains("service"),
            "the caveat is legible in the atomic-letter vocabulary: {src}"
        );
    }
}
