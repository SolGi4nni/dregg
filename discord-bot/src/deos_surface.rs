//! The **deos surface inside Discord** — the bot as a real web-of-cells front,
//! not a thin command wrapper.
//!
//! This module is the WELD between the deos web-forward primitives (already
//! shipped, already verified, in `dregg-app-framework` /
//! `starbridge-web-surface`, the Rust mirrors of `Dregg2.Deos.*`) and Discord's
//! interaction model. It builds NOTHING the protocol already has — it NAMES the
//! genuine primitives and surfaces them as Discord buttons + embeds + links:
//!
//! 1. **Affordances → Discord buttons (progressive attenuation in Discord).** A
//!    cell's cap-gated [`AffordanceSurface`] is projected per-viewer through the
//!    REAL [`dregg_cell::is_attenuation`] ([`AffordanceSurface::project_for`]): a
//!    user sees exactly the buttons their held [`AuthRequired`] authorizes — the
//!    `view` button for a reader, the `approve` button for a council member, the
//!    `admin` button only for a root holder. Pressing a button fires
//!    [`AffordanceSurface::fire`] — a REAL cap-gated verified-turn
//!    [`AffordanceIntent`] carrying a genuine [`dregg_turn::Effect`]; an
//!    unauthorized fire is [`FireError::Unauthorized`] (the anti-ghost tooth —
//!    REFUSED, never a print).
//!
//! 2. **Transclusion into embeds (Ted Nelson's live quote, in Discord).** A live
//!    cell field (a council threshold, a balance, a tally) is published as a
//!    content-addressed `dregg://` cell in a [`WebOfCells`] and transcluded into a
//!    Discord embed via the REAL [`TranscludedField`]: the embed field shows the
//!    source's committed bytes, carries the immutable [`Provenance`] citation
//!    (source ref + receipt + finalized), and re-verifies on demand. When the
//!    source advances ([`WebOfCells::amend`]), the same `dregg://` ref resolves to
//!    the NEW committed value — the unbreakable link.
//!
//! 3. **`dregg://` links + what-links-here (the navigable docuverse).** Posting a
//!    `dregg://` ref and answering "what links here" via the REAL
//!    [`Backlinks`] / [`DreggverseMap`], projected per-viewer through the REAL
//!    [`Membrane`] (the fog-of-war for links — a viewer sees only the backlinks
//!    its caps authorize).
//!
//! The cap discipline is the GENUINE one throughout: `is_attenuation`
//! (`required ⊆ held`), the same lattice the firmament proves. No parallel gate,
//! no toy surface, no stub effect.
//!
//! ## What is real vs. the seam
//!
//! - **Real:** the per-viewer projection (the proven `is_attenuation`), the
//!   effect-templates (genuine [`dregg_turn::Effect`]s), the transclusion
//!   (content→commitment→receipt→quorum-root verification chain), the backlinks /
//!   docuverse map / membrane projection.
//! - **The seam (named, not papered):** the bot owns an in-process [`WebOfCells`]
//!   for the deos surfaces it publishes (council/balance/tally snapshots) — the
//!   SAME in-process attested ledger the transclusion primitive's own tests use.
//!   Driving the [`AffordanceIntent`] all the way to the live devnet executor (so
//!   the receipt is the node's own) is the boundary this bot touches the executor
//!   at — the SAME dispatch seam `starbridge-web-surface` names; the gate that
//!   decides *whether the turn may fire at all* is the real `is_attenuation`,
//!   in-band, HERE.

use std::collections::BTreeMap;

use dregg_cell::AuthRequired;
use dregg_turn::action::{Effect, Event};
use dregg_types::CellId;

use starbridge_web_surface::affordance::{
    AffordanceIntent, AffordanceSurface, CellAffordance, EffectSummary, FireError,
};
use starbridge_web_surface::delegate::SurfaceCapability;
use starbridge_web_surface::rehydrate::Membrane;
use starbridge_web_surface::transclusion::{
    Backlinks, Provenance, TranscludedField, TransclusionError,
};
use starbridge_web_surface::web_of_cells::{DreggUri, WebOfCells};

// ════════════════════════════════════════════════════════════════════════════
// Discord cap tiers — a Discord user's relationship to a cell, mapped to the REAL
// rights lattice. The mapping is the load-bearing part: who-may-press a button is
// decided by the genuine `AuthRequired`, NOT a Discord role string.
// ════════════════════════════════════════════════════════════════════════════

/// The authority a Discord user holds over a deos surface, expressed in the REAL
/// [`AuthRequired`] rights lattice. The bot decides a user's tier from durable
/// facts (do they hold a cclerk? are they a council member? are they the surface
/// owner?) and projects the affordance surface through `is_attenuation(held, …)`.
///
/// This is the bridge that makes "an agent sees exactly the affordances its caps
/// authorize" real inside Discord: two users at different tiers get DIFFERENT
/// button sets over the SAME cell.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DiscordCapTier {
    /// No cclerk / not authenticated — holds the empty (Impossible) authority, so
    /// only `None`-gated affordances (public) are visible.
    Anonymous,
    /// An authenticated reader (holds a cclerk) — the weakest meaningful right
    /// (`Signature`). Sees `view`-tier affordances.
    Member,
    /// A council member / editor — the `Either` tier. Sees `comment`/`edit`/
    /// `approve`-tier affordances in addition to `view`.
    Council,
    /// The surface owner / admin — the broad root right (`None`). Sees every
    /// affordance, including `admin`-tier grants.
    Owner,
}

impl DiscordCapTier {
    /// The REAL [`AuthRequired`] this tier holds — the input to `is_attenuation`.
    pub fn held_rights(self) -> AuthRequired {
        match self {
            // Impossible is the bottom of the lattice: `is_attenuation(Impossible,
            // r)` is true ONLY for r = Impossible, so an anonymous viewer clears NO
            // affordance — the honest verdict for an unauthenticated user.
            DiscordCapTier::Anonymous => AuthRequired::Impossible,
            DiscordCapTier::Member => AuthRequired::Signature,
            DiscordCapTier::Council => AuthRequired::Either,
            DiscordCapTier::Owner => AuthRequired::None,
        }
    }

    /// The held capability over `cell` this tier confers — what the per-viewer
    /// projection / fire reads. The rights are exactly [`Self::held_rights`]: an
    /// anonymous viewer holds the bottom authority ([`AuthRequired::Impossible`]),
    /// so it clears NO affordance — `is_attenuation(Impossible, r)` is true only
    /// for `r = Impossible` (the lattice bottom), the honest "an unauthenticated
    /// Discord user has no authority over the cell" verdict. Note `None` in this
    /// lattice is the ROOT (maximal) right, not "public-and-nothing-more": there is
    /// no value that clears a `None`-gated affordance without also clearing every
    /// affordance, so a `None`-gated button is an OWNER button, not a public one.
    pub fn held_surface(self, cell: CellId) -> SurfaceCapability {
        SurfaceCapability::root(cell, self.held_rights())
    }

    /// A short human label for the tier (rendered in the embed footer).
    pub fn label(self) -> &'static str {
        match self {
            DiscordCapTier::Anonymous => "anonymous",
            DiscordCapTier::Member => "member",
            DiscordCapTier::Council => "council",
            DiscordCapTier::Owner => "owner",
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Effect-template helpers — REAL `dregg_turn::Effect`s the executor would run.
// ════════════════════════════════════════════════════════════════════════════

/// A real `EmitEvent` effect (a read/log/comment turn) on `cell`.
pub fn emit_event(cell: CellId, topic: [u8; 32]) -> Effect {
    Effect::EmitEvent {
        cell,
        event: Event {
            topic,
            data: Vec::new(),
        },
    }
}

/// A real `SetField` effect (an edit/approve turn) writing slot `index` of `cell`.
pub fn set_field(cell: CellId, index: usize, value: [u8; 32]) -> Effect {
    Effect::SetField { cell, index, value }
}

// ════════════════════════════════════════════════════════════════════════════
// The deos cell surface — a cell's cap-gated affordances, projected per-viewer.
// ════════════════════════════════════════════════════════════════════════════

/// A button the bot renders for a viewer — one affordance the viewer's caps
/// authorize, ready to become a Discord button / slash-command. Carries the
/// affordance name + the effect kind it fires (so the embed can label it) + the
/// custom-id the bot routes the press back through.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DiscordAffordanceButton {
    /// The affordance name (the deos analogue of `hx-post="/approve"`).
    pub affordance: String,
    /// The effect kind this button fires (`SetField`, `EmitEvent`, …) — a readout
    /// of the REAL effect-template, for the button label.
    pub effect_kind: String,
    /// The Discord component custom-id the press routes back through, of the form
    /// `deos:<surface-hex8>:<affordance>`. The router re-derives the viewer's tier
    /// + re-runs the cap gate on press (never trusts the rendered set).
    pub custom_id: String,
}

/// A deos surface the bot exposes inside Discord — a cell's published
/// [`AffordanceSurface`] (the REAL cap-gated affordance set).
///
/// The per-viewer projection ([`Self::buttons_for`]) is the genuine
/// `is_attenuation` frustum: two viewers at different [`DiscordCapTier`]s get
/// DIFFERENT button sets over the SAME surface (progressive attenuation in
/// Discord). Firing one ([`Self::fire`]) runs the REAL cap-gate and yields a
/// genuine verified-turn [`AffordanceIntent`]; an unauthorized fire is REFUSED.
#[derive(Clone, Debug)]
pub struct DeosCellSurface {
    /// The backing cell (the object whose affordances these are).
    pub cell: CellId,
    /// A human/diagnostic name (the embed title).
    pub name: String,
    /// The REAL cap-gated affordance surface.
    pub surface: AffordanceSurface,
}

impl DeosCellSurface {
    /// Build a deos surface over `cell` named `name`, with no affordances yet.
    pub fn new(cell: CellId, name: impl Into<String>) -> Self {
        DeosCellSurface {
            cell,
            name: name.into(),
            surface: AffordanceSurface::new(cell),
        }
    }

    /// Declare a cap-gated affordance on the surface. Builder-style.
    pub fn declare(mut self, affordance: CellAffordance) -> Self {
        self.surface = self.surface.declare(affordance);
        self
    }

    /// A canonical **council surface**: `view` (any member), `approve` (council),
    /// `admin` (owner only) — a clean three-tier rights chain, each carrying a REAL
    /// effect-template. The shape the `/deos council` command renders.
    pub fn council(cell: CellId, name: impl Into<String>, status_slot: usize) -> Self {
        DeosCellSurface::new(cell, name)
            // view: any authenticated member — a read logs an access event.
            .declare(CellAffordance::new(
                "view",
                AuthRequired::Signature,
                emit_event(cell, *blake3::hash(b"deos-council-view").as_bytes()),
            ))
            // approve: the council tier (Either ⊃ Signature) — writes the status slot.
            .declare(CellAffordance::new(
                "approve",
                AuthRequired::Either,
                set_field(cell, status_slot, *blake3::hash(b"approved").as_bytes()),
            ))
            // admin: the broad root tier (None) — only an owner clears it.
            .declare(CellAffordance::new(
                "admin",
                AuthRequired::None,
                emit_event(cell, *blake3::hash(b"deos-council-admin").as_bytes()),
            ))
    }

    /// Custom-id stem for this surface (`deos:<hex8>`), used to route presses.
    fn custom_id_stem(&self) -> String {
        let mut s = String::from("deos:");
        for b in self.cell.0.iter().take(4) {
            s.push_str(&format!("{b:02x}"));
        }
        s
    }

    /// **The per-viewer button projection** — the buttons a `tier` viewer is
    /// authorized to see/fire, via the REAL [`AffordanceSurface::project_for`]
    /// (`is_attenuation`). The deos property made Discord-native: a member sees
    /// `{view}`; a council member sees `{view, approve}`; an owner sees
    /// `{view, approve, admin}` — over the SAME surface.
    pub fn buttons_for(&self, tier: DiscordCapTier) -> Vec<DiscordAffordanceButton> {
        let held = tier.held_surface(self.cell);
        let stem = self.custom_id_stem();
        self.surface
            .project_for(&held)
            .into_iter()
            .map(|a| DiscordAffordanceButton {
                effect_kind: effect_kind(&a.effect_summary()).to_string(),
                custom_id: format!("{stem}:{}", a.name),
                affordance: a.name,
            })
            .collect()
    }

    /// The affordance names a `tier` viewer sees (sorted) — the thing two
    /// different-tier viewers DIVERGE on.
    pub fn visible_names(&self, tier: DiscordCapTier) -> Vec<String> {
        let held = tier.held_surface(self.cell);
        self.surface.visible_names(&held)
    }

    /// **Fire** the affordance named `name` as a `tier` viewer firing from `actor`
    /// — the cap-gated verified-turn interaction. The gate is the REAL
    /// `is_attenuation`, IN-BAND: an unauthorized fire is [`FireError::Unauthorized`]
    /// (the anti-ghost tooth — REFUSED, never run). On success returns a genuine
    /// [`AffordanceIntent`] carrying the REAL [`dregg_turn::Effect`] the executor
    /// would run.
    pub fn fire(
        &self,
        name: &str,
        actor: CellId,
        tier: DiscordCapTier,
    ) -> Result<AffordanceIntent, FireError> {
        let held = tier.held_surface(self.cell);
        self.surface.fire(name, actor, &held)
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Transclusion into embeds — the live quote, provenanced + refreshable.
// ════════════════════════════════════════════════════════════════════════════

/// A live cell field published as a `dregg://` cell, transcludable into a Discord
/// embed. The bot owns an in-process [`WebOfCells`] (the SAME attested ledger the
/// transclusion primitive's own tests use); each [`TranscludedSurface`] is one
/// published `dregg://` source whose committed value the bot quotes into an embed.
///
/// The displayed value is the source's committed bytes (content-addressed),
/// carries the immutable [`Provenance`] citation, and re-verifies on demand. When
/// the source advances ([`Self::amend`]), the SAME `dregg://` ref resolves to the
/// NEW committed value — Ted Nelson's unbreakable, live link.
pub struct TranscludedSurface {
    /// The bot's attested web-of-cells (the in-process finalized-read ledger).
    web: WebOfCells,
    /// The `dregg://` ref of the most-recently published source field.
    uri: DreggUri,
    /// A human label for the field (e.g. "council threshold", "balance").
    label: String,
}

impl TranscludedSurface {
    /// Publish `value` as a finalized `dregg://` source field labelled `label`,
    /// over a fresh attested web-of-cells (3-of-3 quorum). `seed` distinguishes the
    /// origin cell. The returned surface can be transcluded into an embed and
    /// refreshed.
    pub fn publish(seed: u8, label: impl Into<String>, value: &[u8]) -> Self {
        let label = label.into();
        let mut web = WebOfCells::new(3);
        let committed_url = format!("dregg://deos/{label}");
        let uri = web.publish(seed, value, &committed_url);
        TranscludedSurface { web, uri, label }
    }

    /// The `dregg://` ref this field is published at (the forward link).
    pub fn uri(&self) -> &DreggUri {
        &self.uri
    }

    /// The `dregg://<hex>` link string (as it appears posted in Discord).
    pub fn uri_string(&self) -> String {
        self.uri.to_uri_string()
    }

    /// The field's human label.
    pub fn label(&self) -> &str {
        &self.label
    }

    /// **Transclude the live field** — the REAL verified finalized read
    /// ([`TranscludedField::include`]): performs the `dregg://` attested fetch,
    /// verifies the content→commitment→receipt→quorum-root chain, and pins the
    /// cited value. A forged/absent/un-finalized source is REFUSED. The returned
    /// [`TranscludedField`]'s displayed bytes ARE the source's committed bytes.
    pub fn transclude(&self) -> Result<TranscludedField, TransclusionError> {
        TranscludedField::include(&self.web, &self.uri)
    }

    /// **Refresh to a new committed value** — advance the SAME origin cell to
    /// `new_value` ([`WebOfCells::amend`]): a verified state advance at a new
    /// height. The `dregg://` ref is UNCHANGED, so a transclusion that quoted it
    /// re-resolves to the NEW finalized value (the live quote). Returns the new
    /// federation height.
    pub fn amend(
        &mut self,
        new_value: &[u8],
    ) -> Result<u64, starbridge_web_surface::web_of_cells::FetchError> {
        self.web.amend(&self.uri, new_value)
    }
}

/// One field of a rendered transclusion, ready to drop into a Discord embed: the
/// label, the quoted value (the source's committed bytes, as a UTF-8 string), and
/// the provenance citation line ("quoted from `dregg://…` · receipt `…` · final").
#[derive(Clone, Debug)]
pub struct TranscludedEmbedField {
    /// The field label.
    pub label: String,
    /// The quoted value (source's committed bytes; lossy-UTF-8 for display).
    pub value: String,
    /// The honest, dated provenance citation line.
    pub provenance: String,
}

/// Render a verified [`TranscludedField`] into an embed-ready field labelled
/// `label`. The provenance line is drawn from the REAL [`Provenance`] (source ref +
/// receipt + finalized) — Ted Nelson's "live quote" cited honestly, never a copy
/// claiming to be live.
pub fn render_transclusion(label: &str, field: &TranscludedField) -> TranscludedEmbedField {
    let value = String::from_utf8_lossy(field.quoted_bytes()).into_owned();
    TranscludedEmbedField {
        label: label.to_string(),
        value,
        provenance: provenance_line(field.cite()),
    }
}

/// The honest citation line for a [`Provenance`]: source ref + cited receipt +
/// finalized flag. What tooling renders as "quoted from `dregg://<cell>` at
/// receipt R; finalized".
pub fn provenance_line(p: &Provenance) -> String {
    let finalized = if p.finalized {
        "finalized"
    } else {
        "UNFINALIZED"
    };
    format!(
        "quoted from `{}` · receipt `{}` · {finalized}",
        p.source.to_uri_string(),
        short_hex(&p.receipt_hash),
    )
}

// ════════════════════════════════════════════════════════════════════════════
// dregg:// links + what-links-here — the navigable docuverse, per-viewer.
// ════════════════════════════════════════════════════════════════════════════

/// The bot's **what-links-here** index — the REAL [`Backlinks`] witness-graph plus
/// per-source link lineages, so "who transcludes / observes me" is a verifiable,
/// per-viewer query (Ted Nelson's two-way link, finally honest).
///
/// Populated from genuine transclusions ([`Self::observe`]); answered directly
/// ([`Self::observers_of`]) or projected per-viewer through the REAL [`Membrane`]
/// ([`Self::observers_for_viewer`]) — a backlink whose link lineage a viewer's
/// caps cannot admit is OMITTED (the fog-of-war for links).
#[derive(Default)]
pub struct WhatLinksHere {
    links: Backlinks,
    /// Per-source link lineage (the fog-of-war ceiling). A source with no entry is
    /// public (every viewer sees its backlinks).
    lineage: BTreeMap<CellId, SurfaceCapability>,
}

impl WhatLinksHere {
    /// An empty index.
    pub fn new() -> Self {
        WhatLinksHere {
            links: Backlinks::new(),
            lineage: BTreeMap::new(),
        }
    }

    /// **Record that `observer` transcludes `field`'s source** — populate the
    /// reverse index from a verified transclusion. The cited receipt + content
    /// commitment are carried from the field's provenance, so the backlink is a
    /// verifiable fact, not a bare pointer. Idempotent on identical records.
    pub fn observe(&mut self, observer: CellId, field: &TranscludedField) {
        self.links.observe(observer, field);
    }

    /// **Gate a source's backlinks behind a link lineage** — the fog-of-war
    /// ceiling. After this, only a viewer whose [`Membrane`] can project `lineage`
    /// sees the source's backlinks. Builder-style.
    pub fn gate_source(mut self, source: CellId, lineage: SurfaceCapability) -> Self {
        self.lineage.insert(source, lineage);
        self
    }

    /// **What links here?** — the observers that transclude `source` (the REAL
    /// [`Backlinks::observers_of`]). The god's-eye readout; for the per-viewer
    /// (fogged) one use [`Self::observers_for_viewer`].
    pub fn observers_of(&self, source: CellId) -> Vec<CellId> {
        self.links
            .observers_of(source)
            .iter()
            .map(|o| o.observer)
            .collect()
    }

    /// How many distinct observers transclude `source` (the in-degree in the
    /// docuverse witness-graph).
    pub fn backlink_count(&self, source: CellId) -> usize {
        self.links.backlink_count(source)
    }

    /// **What links here, FOR THIS VIEWER** — the observers `viewer` is authorized
    /// to see, projected through the REAL [`Membrane`]. A source whose backlinks
    /// are gated is visible only if the viewer's caps can project the link lineage
    /// ([`Membrane::project`]); otherwise the backlinks are OMITTED (the fog). An
    /// ungated source is public. Two viewers navigating "the same" docuverse see
    /// DIFFERENT maps — each sees only the links its capabilities authorize.
    pub fn observers_for_viewer(&self, source: CellId, viewer: &Membrane) -> Vec<CellId> {
        if !self.viewer_may_see(source, viewer) {
            return Vec::new();
        }
        self.observers_of(source)
    }

    /// Is `viewer` authorized to see `source`'s backlinks? Public (ungated) → yes;
    /// gated → iff the viewer's membrane can project the lineage (the REAL
    /// `is_attenuation`-meet, never amplifying).
    pub fn viewer_may_see(&self, source: CellId, viewer: &Membrane) -> bool {
        match self.lineage.get(&source) {
            None => true,
            Some(lineage) => viewer.project(lineage).is_ok(),
        }
    }
}

// ── helpers ──────────────────────────────────────────────────────────────────

/// The effect-kind label of a starbridge [`EffectSummary`] — a readout of the
/// REAL effect-template variant, for the Discord button label. (`starbridge`'s
/// `EffectSummary` carries no `variant_tag`; this is the equivalent projection.)
fn effect_kind(summary: &EffectSummary) -> &'static str {
    match summary {
        EffectSummary::SetField { .. } => "SetField",
        EffectSummary::Transfer { .. } => "Transfer",
        EffectSummary::GrantCapability { .. } => "GrantCapability",
        EffectSummary::RevokeCapability { .. } => "RevokeCapability",
        EffectSummary::EmitEvent { .. } => "EmitEvent",
        EffectSummary::IncrementNonce { .. } => "IncrementNonce",
        EffectSummary::Other { tag } => tag,
    }
}

/// Short hex of a 32-byte hash (first 12 hex chars) for display.
fn short_hex(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(12);
    for b in bytes.iter().take(6) {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    // ── (1) AFFORDANCES → DISCORD BUTTONS: progressive attenuation. Two tiers
    //    DIVERGE over the SAME surface; the projection is the REAL is_attenuation. ──

    #[test]
    fn two_tiers_see_different_button_sets_over_the_same_surface() {
        let cell = cid(1);
        let surface = DeosCellSurface::council(cell, "Genesis Council", 0);

        let member = surface.visible_names(DiscordCapTier::Member);
        let council = surface.visible_names(DiscordCapTier::Council);
        let owner = surface.visible_names(DiscordCapTier::Owner);

        // A member sees only `view`; council adds `approve`; owner adds `admin`.
        assert_eq!(member, vec!["view".to_string()]);
        assert_eq!(council, vec!["approve".to_string(), "view".to_string()]);
        assert_eq!(
            owner,
            vec![
                "admin".to_string(),
                "approve".to_string(),
                "view".to_string()
            ]
        );

        // DIVERGENCE over the SAME surface, monotone in authority (the deos property).
        assert_ne!(member, council);
        assert_ne!(council, owner);
        assert!(member.iter().all(|n| council.contains(n)));
        assert!(council.iter().all(|n| owner.contains(n)));
    }

    #[test]
    fn anonymous_viewer_holds_bottom_authority_and_sees_nothing() {
        use dregg_cell::is_attenuation;
        // An anonymous viewer holds the lattice BOTTOM (Impossible), so it clears NO
        // affordance on the council surface (view/approve/admin all require real
        // authority that Impossible does not hold). This is the honest verdict — an
        // unauthenticated Discord user has no authority over the cell.
        let cell = cid(2);
        let surface = DeosCellSurface::council(cell, "Council", 0);
        assert!(surface.visible_names(DiscordCapTier::Anonymous).is_empty());

        // The bottom authority clears only an Impossible-gated affordance (i.e.
        // nothing meaningful) — proving the gate is the REAL lattice. NB `None` in
        // this lattice is the ROOT (owner) right, not "public": an Impossible holder
        // does NOT clear a None-gated affordance (that is an OWNER button).
        let anon = DiscordCapTier::Anonymous.held_rights();
        assert!(!is_attenuation(&anon, &AuthRequired::Signature));
        assert!(!is_attenuation(&anon, &AuthRequired::None));
        assert!(is_attenuation(&anon, &AuthRequired::Impossible));
    }

    #[test]
    fn buttons_carry_routable_custom_ids_and_effect_kinds() {
        let cell = cid(3);
        let surface = DeosCellSurface::council(cell, "Council", 0);
        let buttons = surface.buttons_for(DiscordCapTier::Owner);

        // The owner sees three buttons; each carries a routable custom-id stem and
        // the effect kind of its REAL effect-template.
        assert_eq!(buttons.len(), 3);
        let approve = buttons.iter().find(|b| b.affordance == "approve").unwrap();
        assert!(approve.custom_id.starts_with("deos:"));
        assert!(approve.custom_id.ends_with(":approve"));
        assert_eq!(approve.effect_kind, "SetField");
        let view = buttons.iter().find(|b| b.affordance == "view").unwrap();
        assert_eq!(view.effect_kind, "EmitEvent");
    }

    // ── (1) anti-ghost: firing an unauthorized button is REFUSED (never run). ──

    #[test]
    fn firing_an_authorized_button_yields_a_real_verified_turn_intent() {
        let cell = cid(4);
        let surface = DeosCellSurface::council(cell, "Council", 0);

        // A council member fires `approve` (authorized): a real intent carrying the
        // genuine SetField effect the executor would run.
        let actor = cid(50);
        let intent = surface
            .fire("approve", actor, DiscordCapTier::Council)
            .expect("a council member may fire approve");
        assert_eq!(intent.actor, actor);
        assert_eq!(intent.affordance, "approve");
        assert!(matches!(intent.effect, Effect::SetField { .. }));
    }

    #[test]
    fn firing_an_unauthorized_button_is_refused_anti_ghost() {
        let cell = cid(5);
        let surface = DeosCellSurface::council(cell, "Council", 0);

        // A member (Signature) tries to fire `approve` (req Either): REFUSED by the
        // REAL is_attenuation — never run (the anti-ghost tooth).
        let refused = surface.fire("approve", cid(50), DiscordCapTier::Member);
        assert!(matches!(refused, Err(FireError::Unauthorized { .. })));

        // A member ALSO cannot fire `admin` (req None / root).
        assert!(matches!(
            surface.fire("admin", cid(51), DiscordCapTier::Member),
            Err(FireError::Unauthorized { .. })
        ));
        // A council member cannot fire `admin` either (lacks root).
        assert!(matches!(
            surface.fire("admin", cid(52), DiscordCapTier::Council),
            Err(FireError::Unauthorized { .. })
        ));
        // But the OWNER (root) CAN fire admin — the gate is the real lattice.
        assert!(
            surface
                .fire("admin", cid(53), DiscordCapTier::Owner)
                .is_ok()
        );
    }

    #[test]
    fn firing_a_missing_button_is_no_such_affordance() {
        let surface = DeosCellSurface::council(cid(6), "Council", 0);
        assert_eq!(
            surface
                .fire("nonexistent", cid(50), DiscordCapTier::Owner)
                .unwrap_err(),
            FireError::NoSuchAffordance
        );
    }

    // ── (2) TRANSCLUSION INTO EMBEDS: the live quote, provenanced + refreshable. ──

    #[test]
    fn a_published_field_transcludes_with_provenance_into_an_embed_field() {
        // Publish a council threshold as a dregg:// field, transclude it, render it
        // into an embed field — the value IS the source's committed bytes, carrying
        // the immutable provenance citation.
        let threshold = TranscludedSurface::publish(1, "council threshold", b"3-of-5");
        let field = threshold.transclude().expect("transclusion resolves");

        // The displayed bytes ARE the source's committed bytes (a faithful read).
        assert_eq!(field.quoted_bytes(), b"3-of-5");
        // It re-verifies (content→commitment→receipt→quorum-root chain).
        assert!(field.verify().is_ok());
        // It carries the provenance citation (source ref + finalized).
        assert_eq!(field.cite().source, *threshold.uri());
        assert!(field.cite().finalized);

        let rendered = render_transclusion("Council Threshold", &field);
        assert_eq!(rendered.value, "3-of-5");
        assert!(rendered.provenance.contains("dregg://"));
        assert!(rendered.provenance.contains("finalized"));
    }

    #[test]
    fn the_transclusion_refreshes_to_the_new_committed_value_same_link() {
        // Ted Nelson's live quote: amend the source, and the SAME dregg:// ref
        // resolves to the NEW finalized value (the link never breaks).
        let mut tally = TranscludedSurface::publish(2, "yes votes", b"7");
        let uri_before = tally.uri_string();

        let before = tally.transclude().expect("resolves");
        assert_eq!(before.quoted_bytes(), b"7");

        // The tally advances (a new vote): a verified state advance at a new height.
        let new_height = tally.amend(b"8").expect("amend advances the source");
        assert!(new_height >= 1);

        // The SAME dregg:// ref now resolves to the NEW committed value.
        let uri_after = tally.uri_string();
        assert_eq!(
            uri_before, uri_after,
            "the dregg:// link is unbreakable (unchanged)"
        );
        let after = tally.transclude().expect("re-resolves to the new value");
        assert_eq!(
            after.quoted_bytes(),
            b"8",
            "the live quote reflects the new committed value"
        );
        assert!(after.verify().is_ok());
    }

    #[test]
    fn a_genuine_transclusion_verifies_its_provenance_chain() {
        // A genuine quote re-verifies its content→commitment→receipt→quorum-root
        // chain — the polarity a forge would fail (a tampered quote cannot be
        // opened; the verification gate `transclude()`/`verify()` runs catches it).
        let surface = TranscludedSurface::publish(3, "balance", b"100 DREGG");
        let field = surface.transclude().expect("genuine resolve");
        assert!(field.verify().is_ok());
        assert_eq!(field.quoted_bytes(), b"100 DREGG");
        // The provenance citation names a finalized dregg:// source.
        assert!(field.cite().finalized);
        assert_eq!(field.cite().source, *surface.uri());
    }

    // ── (3) dregg:// LINKS + WHAT-LINKS-HERE: per-viewer fog-of-war. ──

    #[test]
    fn what_links_here_enumerates_observers_and_fogs_per_viewer() {
        use dregg_cell::AuthRequired;

        // Publish a widely-quoted source; three docs transclude it.
        let source_surface = TranscludedSurface::publish(5, "quoted source", b"<h1>cited</h1>");
        let field = source_surface.transclude().expect("resolves");
        let source = field.provenance.source.cell;

        let (obs_a, obs_b, obs_c) = (cid(101), cid(102), cid(103));
        let mut wlh = WhatLinksHere::new();
        wlh.observe(obs_a, &field);
        wlh.observe(obs_b, &field);
        wlh.observe(obs_c, &field);

        // God's-eye "what links here": exactly the three observers.
        let all = wlh.observers_of(source);
        assert_eq!(all.len(), 3);
        assert!(all.contains(&obs_a) && all.contains(&obs_b) && all.contains(&obs_c));
        assert_eq!(wlh.backlink_count(source), 3);

        // Now GATE the source behind an Either link lineage — the fog-of-war (built
        // through the public `observe` + `gate_source` API).
        let mut gated = WhatLinksHere::new();
        gated.observe(obs_a, &field);
        let gated = gated.gate_source(
            source,
            SurfaceCapability::root(source, AuthRequired::Either),
        );

        // An AUTHORIZED viewer (holds Either) projects the lineage → sees the backlink.
        let strong = Membrane::new(SurfaceCapability::root(cid(150), AuthRequired::Either));
        assert!(gated.viewer_may_see(source, &strong));
        assert_eq!(gated.observers_for_viewer(source, &strong), vec![obs_a]);

        // An INCOMPARABLE viewer (Proof vs a Signature-gated source) is FOGGED.
        let mut sig_gated = WhatLinksHere::new();
        sig_gated.observe(obs_a, &field);
        let sig_gated = sig_gated.gate_source(
            source,
            SurfaceCapability::root(source, AuthRequired::Signature),
        );
        let incomparable = Membrane::new(SurfaceCapability::root(cid(151), AuthRequired::Proof));
        assert!(!sig_gated.viewer_may_see(source, &incomparable));
        assert!(
            sig_gated
                .observers_for_viewer(source, &incomparable)
                .is_empty()
        );
    }

    #[test]
    fn an_ungated_source_is_public_to_every_viewer() {
        use dregg_cell::AuthRequired;
        let surface = TranscludedSurface::publish(6, "public", b"open");
        let field = surface.transclude().expect("resolves");
        let source = field.provenance.source.cell;

        let mut wlh = WhatLinksHere::new();
        let observer = cid(160);
        wlh.observe(observer, &field);

        // No gate → public: even the weakest viewer sees the backlink.
        let weak = Membrane::new(SurfaceCapability::root(cid(161), AuthRequired::Signature));
        assert!(wlh.viewer_may_see(source, &weak));
        assert_eq!(wlh.observers_for_viewer(source, &weak), vec![observer]);
    }

    // ── the cap-tier → rights mapping is the REAL lattice ──

    #[test]
    fn cap_tiers_map_to_the_real_rights_lattice() {
        use dregg_cell::is_attenuation;
        // A council viewer's held authority (Either) clears a Signature-gated and an
        // Either-gated affordance, but NOT a None(root)-gated one.
        let council = DiscordCapTier::Council.held_rights();
        assert!(is_attenuation(&council, &AuthRequired::Signature));
        assert!(is_attenuation(&council, &AuthRequired::Either));
        assert!(!is_attenuation(&council, &AuthRequired::None));
        // An owner (None / root) clears everything.
        let owner = DiscordCapTier::Owner.held_rights();
        assert!(is_attenuation(&owner, &AuthRequired::None));
        assert!(is_attenuation(&owner, &AuthRequired::Either));
    }
}
