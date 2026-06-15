//! The WEB-OF-CELLS browser — the cockpit as a native browser of the `dregg://`
//! docuverse.
//!
//! The cockpit ([`crate::cockpit`]) is the live verified image; the
//! [`starbridge_web_surface`] crate is the **web of cells**: a `dregg://<cell>`
//! link is a *capability into a cell*, "fetching" it is a **verified, attested
//! cross-cell read** (a receipt + a quorum-signed `AttestedRoot` the client
//! checks), a cell publishes typed **affordances** (cap-gated effect-templates —
//! htmx-on-crack), and "opening" a surface re-acquires a per-viewer projection
//! whose `Rehydration` liveness-type is *derived*, never hand-set. This module
//! fuses the two: it BROWSES the web of cells from inside the cockpit's own live
//! [`World`].
//!
//! Like [`crate::landing`], this is the browser's pure, gpui-free **text MODEL**:
//! a projection of the live image into addressable cells, each with its
//! trusted-path origin chrome, its per-viewer affordance surface, and its
//! rehydration liveness-type. The cockpit renders this model with native gpui —
//! but because the *content* is built here, gpui-free, it is `cargo test`-able:
//! a test asserts the browser speaks real, attested, cap-projected text about the
//! real cells, so "the cockpit browses the web of cells" is proven without a GPU.
//!
//! ## Everything here is the REAL web-of-cells, never a parallel model
//!
//! - The addressing + fetch is the genuine [`WebOfCells`] / [`DreggUri`]: each
//!   live World cell is published as a `dregg://` page and FETCHED back through
//!   the real attested-fetch path, so each row carries a real [`AttestedResource`]
//!   (content-addressed + receipt-in-stream + quorum-signed root, verified by the
//!   real [`AttestedResource::verify`]) and a real [`OriginChrome`] (drawn from
//!   the LEDGER, never the page — the structural anti-phishing badge).
//! - The affordance surface is the genuine web-surface
//!   [`web_aff::AffordanceSurface`]; the per-viewer rows are
//!   [`web_aff::AffordanceSurface::project_for`] through a real
//!   [`web_aff::SurfaceCapability`] — progressive enhancement becomes progressive
//!   **attenuation**, gated by the proven [`is_attenuation`] lattice. A viewer
//!   sees exactly the affordances its caps authorize.
//! - The liveness-type is the genuine [`web_aff::Rehydration`], **DERIVED** via
//!   [`web_aff::Rehydration::classify`] from a real [`web_aff::InteractionLog`] of
//!   the attested fetch — not a hand-assigned field.
//! - **Firing** an affordance does NOT stop at a modeled dispatch: the effect the
//!   web-surface affordance carries is the SAME real [`dregg_turn::Effect`] the
//!   cockpit's own [`crate::affordance::AffordanceIntent::fire_through_world`]
//!   runs through the embedded executor. [`WebCellsBrowser::fire_affordance`]
//!   lifts the projected effect across that one-type bridge and commits it as a
//!   REAL verified turn through the live [`World`] — the seam the web crate could
//!   only name is CLOSED here, because this process embeds the executor.
//!
//! ## What integrated vs. what is named-next
//!
//! - **Integrated (here):** the cockpit browses the web of cells natively — it
//!   lists the addressable `dregg://` cells with their attested origin chrome,
//!   opens one to its per-viewer affordance surface (the real `project_for`
//!   attenuation), shows its rehydration liveness-type + provenance, and FIRES an
//!   affordance through the real embedded executor.
//! - **Named-next (the SERVO layer):** the browser renders affordance *surfaces*
//!   natively today; embedding **servo** to render actual `dregg://` web *content*
//!   (the `WebViewDelegate` cap-gate, where the web-surface crate's `MockSurface`
//!   stands today) is the next layer — the servo Stage-A renderer lane.
//!   [`WebCellsBrowser::servo_layer_note`] states it in the model so it is visible
//!   in the panel, not buried.
//! - **Named-next (the TRANSCLUSION affordance):** [`Transclusion`] here shows ONE
//!   Ted-Nelson transcluded field — a cell that INCLUDES another cell's finalized
//!   content commitment, with the provenance receipt shown — built on the cleanly
//!   reachable web-of-cells `OriginChrome` provenance. The *verified cross-cell
//!   observation* form (the protocol's `ObservedFieldEquals` predicate, which
//!   lives below the web-surface crate's public API in `dregg_cell::predicate`)
//!   is named as the increment that hardens it into an in-circuit observation.

use starbridge_web_surface as web_aff;
use web_aff::{
    AffordanceSurface as WebAffordanceSurface, AttestedResource, AuthRequired, CellAffordance,
    DreggUri, Effect, InteractionLog, OriginChrome, Rehydration, SurfaceCapability, WebOfCells,
};
// The REAL verified transclusion — "Xanadu that shipped": a transclusion IS a
// verified cross-cell finalized read (content→commitment→receipt→receipt-stream
// root→quorum). We USE it, never reinvent the provenance.
use web_aff::transclusion::{TranscludedField, TransclusionError};

use dregg_cell::CellId;

use crate::affordance::FireOutcome;
use crate::reflect;
use crate::world::World;

/// One **addressable cell** in the web of cells — a `dregg://` row the browser
/// lists. Every field is a real read of the attested fetch / the ledger-drawn
/// origin chrome, never a hand-set string.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CellRow {
    /// The backing World cell this `dregg://` page denotes.
    pub cell: CellId,
    /// The `dregg://<hex>` address as it appears in the address bar — the
    /// content-addressed cell id, the access grant AND the identity.
    pub uri: String,
    /// The TRUSTED-PATH origin chrome badge — drawn from the LEDGER (cell id +
    /// committed URL + rights lineage + finality), never the page. dregg's
    /// structural answer to browser-chrome phishing.
    pub chrome_badge: String,
    /// Whether the full client-side attestation chain VERIFIED (content-addressed
    /// + receipt-in-stream + real receipt-stream-root reconstruction + quorum).
    /// The page renders only on `true`.
    pub attested: bool,
    /// The finalized content commitment (`blake3` of the served bytes), short-hex
    /// — the field a transclusion would include, and the page's self-certifying
    /// identity.
    pub content_commitment: String,
    /// The committed URL the origin cell carries (its trusted-chrome source).
    pub committed_url: Option<String>,
    /// A one-line human preview of the served page body (the real attested bytes).
    pub preview: String,
}

/// One affordance row in an opened cell's surface, AS PROJECTED FOR THE VIEWER.
/// Present in the list iff the viewer's caps authorize it — the rows the viewer
/// is NOT cleared for are absent (progressive attenuation), and the model records
/// how many were attenuated away.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AffordanceRow {
    /// The affordance name (the deos analogue of htmx's `hx-post` path).
    pub name: String,
    /// The authority a viewer must HOLD to fire it (`required ⊆ held`).
    pub required: String,
    /// The REAL effect this affordance would fire, summarized (`SetField` /
    /// `EmitEvent` / `GrantCapability` …) — the genuine turn the executor runs.
    pub effect: String,
}

/// The Ted-Nelson **transclusion** row — a cell surface that INCLUDES another
/// cell's finalized field, with the provenance receipt shown. Built from the REAL
/// [`TranscludedField`] (the verified cross-cell finalized read), so the displayed
/// commitment + receipt are drawn from a genuine, verified, quorum-finalized fetch
/// — a forged or un-finalized quote could not have been opened.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Transclusion {
    /// The host cell (the page doing the including).
    pub host: CellId,
    /// The source cell (the page whose field is transcluded).
    pub source: CellId,
    /// The transcluded field — the source's finalized content commitment
    /// (short-hex), drawn from the real [`web_aff::transclusion::Provenance`]; the
    /// field the host includes by reference (`content_hash == blake3(bytes)`).
    pub transcluded_field: String,
    /// The provenance RECEIPT: the cited receipt-stream Merkle leaf (short-hex) the
    /// quote is pinned to — the immutable past the citation dates, verified to be
    /// in the committed stream. Shown so the inclusion is checkable, not trusted.
    pub provenance_receipt: String,
    /// Whether the source's read was quorum-FINALIZED — the real
    /// [`TranscludedField::include`] REFUSES a non-finalized read, so this is
    /// always `true` for an opened transclusion (a transclusion quotes finalized
    /// state); a non-finalized source becomes `name`d-next, not shown.
    pub source_finalized: bool,
}

/// THE WEB-OF-CELLS BROWSER MODEL — the whole `dregg://` docuverse as the cockpit
/// browses it, built fresh from the live [`World`]. The numbers + addresses +
/// attestations it shows are the running image's actual cells.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WebCellsBrowser {
    /// The viewer identity the surface is projected FOR (the cockpit's own
    /// principal) — short-hex. The affordance rows are exactly what THIS identity
    /// is cleared for.
    pub viewer: CellId,
    /// The viewer's authority tier name (the `AuthRequired` the cockpit holds over
    /// the surface) — what decides the progressive attenuation.
    pub viewer_tier: String,
    /// Every addressable `dregg://` cell in the web of cells (one per live World
    /// cell), with its attested origin chrome.
    pub cells: Vec<CellRow>,
    /// The currently-opened cell's address (the focused row), if any.
    pub opened: Option<CellId>,
    /// The opened cell's affordance surface, AS PROJECTED FOR THE VIEWER — only
    /// the affordances the cockpit's caps authorize (progressive attenuation).
    pub affordances: Vec<AffordanceRow>,
    /// How many affordances the surface declares in total (so the panel can show
    /// "you see N of M — the rest are attenuated away by your caps").
    pub affordances_declared: usize,
    /// The opened surface's REHYDRATION liveness-type badge — DERIVED from the
    /// attested fetch's interaction log (LIVE / REPLAYED-DETERMINISTIC /
    /// RECONSTRUCTED-APPROXIMATE), so the system cannot lie about which kind of
    /// true the reacquisition is.
    pub rehydration_badge: String,
    /// ONE Ted-Nelson transclusion (the host cell including the source cell's
    /// finalized field with provenance), if at least two cells exist.
    pub transclusion: Option<Transclusion>,
}

impl WebCellsBrowser {
    /// Build the browser model from the live world, opening `opened` (if any) to
    /// its per-viewer affordance surface. `viewer` is the cockpit's own principal
    /// (the identity the surface is projected for); `viewer_rights` is the
    /// authority it holds over the surface (what gates the attenuation).
    ///
    /// This is the single source of the panel's content — the cockpit renders
    /// exactly these rows, so the `cargo test` that asserts they are real +
    /// attested + cap-projected proves the rendered tree browses the real web of
    /// cells.
    pub fn build(
        world: &World,
        viewer: CellId,
        viewer_rights: AuthRequired,
        opened: Option<CellId>,
    ) -> Self {
        // Build a REAL web of cells: publish each live World cell as a dregg://
        // page whose content is a genuine description of the cell (drawn from live
        // ledger state — its balance, its cap count, its address), then FETCH each
        // back through the real attested-fetch path. Each row carries a real
        // AttestedResource (verified) + a real OriginChrome (ledger-drawn).
        let mut web = WebOfCells::new(3);

        // Stable per-cell seeds so the published origin cells are deterministic
        // across frames (the browser address bar is stable as the image evolves).
        let mut rows: Vec<CellRow> = Vec::new();
        let mut published: Vec<(CellId, DreggUri, AttestedResource, OriginChrome)> = Vec::new();

        let ledger_cells: Vec<(CellId, i64, usize)> = world
            .ledger()
            .iter()
            .map(|(id, c)| (*id, c.state.balance(), c.capabilities.len()))
            .collect();

        for (seed, (cell, balance, caps)) in ledger_cells.iter().enumerate() {
            let body = page_body_for_cell(cell, *balance, *caps);
            let url = format!("dregg://cell/{}", reflect::short_hex(&cell.0));
            // publish() seeds a FRESH origin cell (the dregg:// page is its own
            // cell); we key the row by the WORLD cell it describes.
            let uri = web.publish(seed as u8, body.as_bytes(), &url);
            match web.fetch(&uri) {
                Ok((resource, chrome)) => {
                    let attested = resource.verify().is_ok();
                    rows.push(CellRow {
                        cell: *cell,
                        uri: uri.to_uri_string(),
                        chrome_badge: chrome.badge(),
                        attested,
                        content_commitment: reflect::short_hex(&resource.content_hash),
                        committed_url: chrome.committed_url.clone(),
                        preview: preview_of(&resource.content_bytes),
                    });
                    published.push((*cell, uri, resource, chrome));
                }
                Err(e) => {
                    // A dead/unattested link is shown honestly, never hidden.
                    rows.push(CellRow {
                        cell: *cell,
                        uri: uri.to_uri_string(),
                        chrome_badge: format!("dregg:// (fetch failed: {e:?})"),
                        attested: false,
                        content_commitment: "—".to_string(),
                        committed_url: Some(url),
                        preview: format!("(no attested content: {e:?})"),
                    });
                }
            }
        }

        // Resolve the opened cell (default: the first addressable cell, so the
        // panel always shows a live surface rather than an empty pane).
        let opened = opened
            .filter(|o| rows.iter().any(|r| &r.cell == o))
            .or_else(|| rows.first().map(|r| r.cell));

        // Project the opened cell's affordance surface FOR THE VIEWER. The surface
        // is the genuine web-surface AffordanceSurface; the viewer's authority is a
        // real web-surface SurfaceCapability over the cell; project_for runs the
        // real is_attenuation gate.
        let mut affordances = Vec::new();
        let mut affordances_declared = 0;
        let mut rehydration_badge =
            Rehydration::ReconstructedApproximate.badge().to_string();

        if let Some(cell) = opened {
            let surface = affordance_surface_for(cell, viewer);
            affordances_declared = surface.affordances.len();

            let held = SurfaceCapability::root(cell, viewer_rights.clone());
            for aff in surface.project_for(&held) {
                affordances.push(AffordanceRow {
                    name: aff.name.clone(),
                    required: format!("{:?}", aff.required_rights),
                    effect: effect_label(&aff.effect_template),
                });
            }

            // DERIVE the rehydration liveness-type from the attested fetch's
            // interaction log: the opened surface's content arrived via a dregg://
            // ATTESTED fetch (witnessed in the graph), so — with the source
            // context gone (a snapshot, not the live scene) — it replays
            // deterministically. The value is COMPUTED, never assigned.
            if let Some((_, uri, resource, _)) = published.iter().find(|(c, ..)| *c == cell) {
                let mut log = InteractionLog::new();
                log.record_attested_fetch(uri.clone(), resource.attested_root.clone());
                // sources_reachable = false: a browsed surface is a snapshot we
                // re-acquire, not a live socket to the origin context. The fetch
                // being witnessed makes it REPLAYED-DETERMINISTIC (confined), the
                // honest "every interaction went through the membrane" type.
                rehydration_badge = Rehydration::classify(&log, false).badge().to_string();
            }
        }

        // ONE Ted-Nelson transclusion via the REAL verified finalized read: the
        // opened (host) cell includes the NEXT addressable cell's finalized field
        // by reference, through `TranscludedField::include` (the genuine
        // content→commitment→receipt→root→quorum chain) — a forged/un-finalized
        // quote could not be opened.
        let transclusion = build_transclusion(&web, opened, &published);

        WebCellsBrowser {
            viewer,
            viewer_tier: format!("{viewer_rights:?}"),
            cells: rows,
            opened,
            affordances,
            affordances_declared,
            rehydration_badge,
            transclusion,
        }
    }

    /// **Fire an affordance through the REAL embedded executor.** This is the
    /// seam the web crate could only model, CLOSED: the affordance the web-surface
    /// surface projects carries a real [`dregg_turn::Effect`]; we instantiate it
    /// and hand it to the cockpit's [`crate::affordance::AffordanceIntent::fire_through_world`]
    /// — a verified turn through the live [`World`]. The executor EITHER commits (a
    /// real receipt) OR rejects (a guarantee fired) — both surfaced.
    ///
    /// The cap-gate that decides whether the affordance may fire AT ALL is the
    /// REAL `is_attenuation` (run by [`WebAffordanceSurface::fire`]); the gate that
    /// decides whether the resulting TURN commits is the real executor. Neither is
    /// faked. Returns the executor outcome, or the in-band `FireError` text if the
    /// viewer was not authorized for the affordance (the anti-ghost tooth).
    pub fn fire_affordance(
        world: &mut World,
        cell: CellId,
        viewer: CellId,
        viewer_rights: AuthRequired,
        affordance_name: &str,
    ) -> Result<FireOutcome, String> {
        let surface = affordance_surface_for(cell, viewer);
        let held = SurfaceCapability::root(cell, viewer_rights);
        // The web-surface fire runs the REAL is_attenuation gate (anti-ghost): an
        // unauthorized fire is refused IN-BAND here, before any executor turn.
        let intent = surface
            .fire(affordance_name, viewer, &held)
            .map_err(|e| format!("{e:?}"))?;

        // Lift the projected effect across the one-type bridge: the web-surface
        // affordance's effect IS the same dregg_turn::Effect the cockpit's
        // executor runs. Re-mint it as the cockpit's own AffordanceIntent and fire
        // it through the embedded executor (the closed seam).
        let cockpit_intent = crate::affordance::AffordanceIntent {
            surface_cell: cell,
            affordance: affordance_name.to_string(),
            actor: viewer,
            effect: intent.effect,
        };
        Ok(cockpit_intent.fire_through_world(world))
    }

    /// The SERVO layer note — stated in the model so it is VISIBLE in the panel,
    /// not buried in a doc. The browser renders affordance SURFACES natively
    /// today; embedding servo to render actual `dregg://` web CONTENT is the
    /// named next layer.
    pub fn servo_layer_note(&self) -> &'static str {
        "NATIVE today: this browser renders cap-gated affordance SURFACES (the \
         dregg:// addressing, the attested fetch, the per-viewer attenuation, the \
         rehydration liveness-type). NEXT layer: embed servo to render actual \
         dregg:// web CONTENT — the WebViewDelegate cap-gate (where the \
         web-surface crate's MockSurface stands), the servo Stage-A renderer lane."
    }

    /// Every line of real text the browser renders, flattened — used by tests to
    /// assert the panel speaks real, attested, cap-projected text about the real
    /// cells (the exact gpui tree content, so non-empty here == non-empty tree).
    pub fn all_text(&self) -> Vec<String> {
        let mut out = Vec::new();
        out.push(format!(
            "web of cells — viewer {} holds {} over the surface",
            reflect::short_hex(&self.viewer.0),
            self.viewer_tier
        ));
        for r in &self.cells {
            out.push(r.uri.clone());
            out.push(r.chrome_badge.clone());
            out.push(format!(
                "attested={} · commitment {} · {}",
                r.attested, r.content_commitment, r.preview
            ));
        }
        if let Some(o) = self.opened {
            out.push(format!("opened dregg://{}", reflect::short_hex(&o.0)));
        }
        out.push(format!(
            "affordances projected for you: {} of {} declared (the rest attenuated by your caps)",
            self.affordances.len(),
            self.affordances_declared
        ));
        for a in &self.affordances {
            out.push(format!("· {} (requires {}) → {}", a.name, a.required, a.effect));
        }
        out.push(format!("rehydration: {}", self.rehydration_badge));
        if let Some(t) = &self.transclusion {
            out.push(format!(
                "transcludes field {} from dregg://{} (receipt {}, finalized={})",
                t.transcluded_field,
                reflect::short_hex(&t.source.0),
                t.provenance_receipt,
                t.source_finalized
            ));
        }
        out.push(self.servo_layer_note().to_string());
        out
    }
}

// ── the model-building helpers (pure; each names the real web-of-cells primitive) ──

/// The page body a `dregg://` cell serves: a real, human-readable description of
/// the World cell drawn from LIVE ledger state. This is the attested content —
/// the bytes the receipt + quorum-signed root bind.
fn page_body_for_cell(cell: &CellId, balance: i64, caps: usize) -> String {
    format!(
        "<dregg-cell id=\"{}\"><balance>{}</balance><capabilities>{}</capabilities>\
         <p>A live capability-secured cell in the verified image. Every interaction \
         with it is a verified turn; this page is served from its committed state.</p>\
         </dregg-cell>",
        reflect::short_hex(&cell.0),
        balance,
        caps
    )
}

/// A one-line preview of the served page bytes (the real attested content).
fn preview_of(bytes: &[u8]) -> String {
    let s = String::from_utf8_lossy(bytes);
    let trimmed: String = s.chars().take(72).collect();
    if s.len() > 72 {
        format!("{trimmed}…")
    } else {
        trimmed
    }
}

/// Build the genuine web-surface [`AffordanceSurface`] a cell publishes — the
/// canonical doc-cell surface {view, comment, edit, admin} on the clean three-tier
/// rights chain `Signature ⊂ Either ⊂ None`, each carrying a REAL
/// [`dregg_turn::Effect`] template (the turn the executor would run). `viewer` is
/// the grantee an `admin` grant would target. This is the web-surface
/// `AffordanceSurface`, NOT a parallel one — its `project_for` runs the real
/// `is_attenuation`, and its effects are the genuine `Effect` the cockpit's
/// executor fires.
fn affordance_surface_for(cell: CellId, viewer: CellId) -> WebAffordanceSurface {
    WebAffordanceSurface::new(cell)
        // view: tier-1 (any authenticated reader holds Signature) → logs an access
        // event (a real EmitEvent turn).
        .declare(CellAffordance::new(
            "view",
            AuthRequired::Signature,
            emit_event(cell),
        ))
        // comment: tier-2 (the editor tier holds Either) → an EmitEvent turn.
        .declare(CellAffordance::new(
            "comment",
            AuthRequired::Either,
            emit_event(cell),
        ))
        // edit: tier-2 → writes a state field (a real SetField turn).
        .declare(CellAffordance::new(
            "edit",
            AuthRequired::Either,
            set_field(cell, 1),
        ))
        // admin: tier-3 (only a root holder of None clears it) → hands out a
        // capability (a real GrantCapability turn).
        .declare(CellAffordance::new(
            "admin",
            AuthRequired::None,
            grant_cap(cell, viewer),
        ))
}

/// A read logs an access event — a real [`Effect::EmitEvent`] turn.
fn emit_event(cell: CellId) -> Effect {
    Effect::EmitEvent {
        cell,
        event: web_aff::dregg_turn_reexport::Event {
            topic: [1u8; 32],
            data: vec![],
        },
    }
}

/// An edit writes a state field — a real [`Effect::SetField`] turn.
fn set_field(cell: CellId, index: usize) -> Effect {
    Effect::SetField {
        cell,
        index,
        value: [7u8; 32],
    }
}

/// An admin grant hands out a capability — a real [`Effect::GrantCapability`]
/// turn (the genuine grant the executor's no-amplification gate checks).
fn grant_cap(from: CellId, to: CellId) -> Effect {
    Effect::GrantCapability {
        from,
        to,
        cap: web_aff::dregg_turn_reexport::CapabilityRef {
            target: to,
            slot: 0,
            permissions: AuthRequired::Signature,
            breadstuff: None,
            expires_at: None,
            allowed_effects: None,
            stored_epoch: None,
        },
    }
}

/// A stable, human label for a real [`Effect`] (the `Effect` enum is not
/// `PartialEq`/`Display`; this is the readout the panel shows). Uses the
/// web-surface [`web_aff::EffectSummary`] — a readout of the GENUINE template.
fn effect_label(effect: &Effect) -> String {
    match web_aff::EffectSummary::of(effect) {
        web_aff::EffectSummary::SetField { index, .. } => format!("SetField(slot {index})"),
        web_aff::EffectSummary::EmitEvent { .. } => "EmitEvent".to_string(),
        web_aff::EffectSummary::GrantCapability { .. } => "GrantCapability".to_string(),
        web_aff::EffectSummary::Transfer { amount, .. } => format!("Transfer({amount})"),
        web_aff::EffectSummary::RevokeCapability { slot, .. } => format!("RevokeCapability(slot {slot})"),
        web_aff::EffectSummary::IncrementNonce { .. } => "IncrementNonce".to_string(),
        web_aff::EffectSummary::Other { tag } => tag.to_string(),
    }
}

/// Build ONE Ted-Nelson transclusion via the REAL [`TranscludedField::include`]:
/// the opened (host) cell includes the NEXT addressable cell's finalized field BY
/// REFERENCE — a genuine VERIFIED cross-cell finalized read
/// (content→commitment→receipt→receipt-stream root→quorum). The displayed
/// commitment + cited receipt are drawn from the real
/// [`web_aff::transclusion::Provenance`]; a forged or un-finalized quote could not
/// have been opened. Returns `None` if fewer than two cells exist (nothing to
/// transclude) or if the source read does not verify/finalize (then the
/// transclusion is honestly absent, never a faked inclusion).
fn build_transclusion(
    web: &WebOfCells,
    opened: Option<CellId>,
    published: &[(CellId, DreggUri, AttestedResource, OriginChrome)],
) -> Option<Transclusion> {
    let host = opened?;
    let host_idx = published.iter().position(|(c, ..)| *c == host)?;
    // The source is the NEXT addressable cell (wrap to the first), so a host
    // always has a distinct source when ≥2 cells exist.
    if published.len() < 2 {
        return None;
    }
    let source_idx = (host_idx + 1) % published.len();
    let (source_cell, source_uri, ..) = &published[source_idx];

    // THE REAL VERIFIED FINALIZED READ — `transclusion_is_observed_finalized_read`.
    // This re-fetches the source through the attested path, runs the genuine
    // provenance chain, and REFUSES a forged (`ProvenanceUnverified`) or
    // un-finalized (`NotFinalized`) quote. We show a transclusion ONLY on success.
    match TranscludedField::include(web, source_uri) {
        Ok(field) => {
            let cite = field.cite();
            Some(Transclusion {
                host,
                source: *source_cell,
                transcluded_field: reflect::short_hex(&cite.content_hash),
                provenance_receipt: reflect::short_hex(&cite.receipt_hash),
                source_finalized: cite.finalized,
            })
        }
        // A source that does not verify/finalize is honestly NOT transcluded (the
        // quote could not be opened) — never a faked inclusion.
        Err(TransclusionError::Fetch(_))
        | Err(TransclusionError::ProvenanceUnverified(_))
        | Err(TransclusionError::NotFinalized) => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::demo_world;

    /// The viewer rights the cockpit holds for the tests (the EDITOR tier:
    /// `Either` clears view/comment/edit but NOT admin — a clean attenuation
    /// witness).
    fn editor_rights() -> AuthRequired {
        AuthRequired::Either
    }

    #[test]
    fn browser_lists_the_real_attested_dregg_cells_of_the_live_image() {
        let (world, anchors) = demo_world();
        let viewer = anchors[2]; // the "user" anchor — the cockpit's principal
        let browser = WebCellsBrowser::build(&world, viewer, editor_rights(), None);

        // One addressable dregg:// cell per live World cell.
        assert_eq!(
            browser.cells.len(),
            world.cell_count(),
            "every live cell is addressable in the web of cells"
        );
        assert!(!browser.cells.is_empty(), "the demo image has cells to browse");

        for row in &browser.cells {
            // Each row is a real dregg:// address (64 hex chars for the cell id).
            assert!(row.uri.starts_with("dregg://"), "a row is a dregg:// address");
            assert_eq!(row.uri.len(), "dregg://".len() + 64, "the address is the content-addressed cell id");
            // The full attestation chain VERIFIED — the page is the page the
            // origin committed (content-addressed + receipt-in-stream + quorum).
            assert!(row.attested, "every browsed cell's attestation chain verifies");
            // The trusted-path chrome is drawn from the LEDGER (a dregg:// badge),
            // never the page.
            assert!(
                row.chrome_badge.starts_with("dregg://"),
                "the origin chrome is the ledger-drawn trusted-path badge"
            );
        }
    }

    #[test]
    fn opening_a_cell_projects_only_the_affordances_the_viewer_is_cleared_for() {
        // THE attenuation witness: the EDITOR tier (Either) sees view/comment/edit
        // but NOT admin (which requires the root None tier). progressive
        // enhancement → progressive ATTENUATION, via the REAL is_attenuation.
        let (world, anchors) = demo_world();
        let viewer = anchors[2];
        let opened = Some(anchors[0]); // open the treasury cell
        let browser = WebCellsBrowser::build(&world, viewer, editor_rights(), opened);

        assert_eq!(browser.opened, opened, "the requested cell is opened");
        // The surface DECLARES four affordances {view, comment, edit, admin}.
        assert_eq!(browser.affordances_declared, 4, "the surface declares four affordances");

        let names: Vec<&str> = browser.affordances.iter().map(|a| a.name.as_str()).collect();
        // The editor tier is cleared for view/comment/edit …
        assert!(names.contains(&"view"), "editor sees view");
        assert!(names.contains(&"comment"), "editor sees comment");
        assert!(names.contains(&"edit"), "editor sees edit");
        // … but NOT admin (the anti-ghost attenuation: it requires the root tier).
        assert!(
            !names.contains(&"admin"),
            "the editor tier is ATTENUATED away from admin — it requires the root None tier"
        );
        assert_eq!(browser.affordances.len(), 3, "editor sees 3 of 4 (admin attenuated)");
    }

    #[test]
    fn a_root_viewer_sees_strictly_more_than_an_editor_the_lattice_proof() {
        // The same surface projected for the ROOT tier (None) sees ALL four,
        // including admin — strictly MORE than the editor. Two viewers at
        // different authority get DIFFERENT projections of the SAME surface.
        let (world, anchors) = demo_world();
        let viewer = anchors[2];
        let opened = Some(anchors[0]);

        let editor = WebCellsBrowser::build(&world, viewer, AuthRequired::Either, opened);
        let root = WebCellsBrowser::build(&world, viewer, AuthRequired::None, opened);

        let root_names: Vec<&str> = root.affordances.iter().map(|a| a.name.as_str()).collect();
        assert!(root_names.contains(&"admin"), "the root tier sees admin");
        assert_eq!(root.affordances.len(), 4, "root sees all four affordances");
        assert!(
            root.affordances.len() > editor.affordances.len(),
            "the root viewer sees STRICTLY MORE than the editor — the attenuation lattice"
        );
    }

    #[test]
    fn the_opened_surface_carries_a_derived_rehydration_liveness_type() {
        // The liveness-type is DERIVED from the attested fetch (not hand-set): the
        // surface's content arrived via a dregg:// ATTESTED fetch (witnessed), and
        // the source context is gone (a snapshot) → REPLAYED-DETERMINISTIC, the
        // confined "every interaction went through the membrane" type.
        let (world, anchors) = demo_world();
        let browser = WebCellsBrowser::build(&world, anchors[2], editor_rights(), Some(anchors[0]));
        assert!(
            browser.rehydration_badge.starts_with("REPLAYED-DETERMINISTIC"),
            "the attested fetch yields the confined replay liveness-type, got: {}",
            browser.rehydration_badge
        );
    }

    #[test]
    fn it_shows_one_transcluded_field_with_a_provenance_receipt() {
        // The Ted-Nelson seam: the host cell includes the source cell's finalized
        // content commitment, with the source's serve-receipt as provenance — both
        // real reads of the attested fetch.
        let (world, anchors) = demo_world();
        let browser = WebCellsBrowser::build(&world, anchors[2], editor_rights(), Some(anchors[0]));
        let t = browser.transclusion.expect("≥2 cells → one transclusion");
        assert_ne!(t.host, t.source, "a transclusion includes a DISTINCT source cell");
        assert!(t.transcluded_field.len() >= 4, "the transcluded field is a real commitment");
        assert!(t.provenance_receipt.len() >= 4, "the provenance receipt is real");
        assert!(t.source_finalized, "the source's attestation finalized (quorum)");
    }

    #[test]
    fn firing_an_affordance_commits_a_real_verified_turn_through_the_embedded_executor() {
        // THE CLOSED SEAM: firing the editor-authorized `edit` affordance dispatches
        // its REAL effect through the embedded executor → a real receipt. This is
        // the web crate's named-not-closed seam, CLOSED in the cockpit.
        let (mut world, anchors) = demo_world();
        let viewer = anchors[0]; // the treasury — a powerful operator principal
        let cell = anchors[0];
        let receipts_before = world.receipts().len();

        let outcome = WebCellsBrowser::fire_affordance(
            &mut world,
            cell,
            viewer,
            AuthRequired::None, // root tier: clears every affordance
            "edit",
        )
        .expect("the root viewer is authorized for edit (in-band gate passes)");

        // The executor either committed (a real receipt) or refused (a guarantee
        // fired) — both are real verified-turn outcomes, neither faked. For an
        // operator editing its own cell's slot, it commits.
        assert!(
            outcome.is_committed(),
            "the affordance fired a real verified turn through the embedded executor: {outcome:?}"
        );
        assert!(
            world.receipts().len() > receipts_before,
            "the fire added a real receipt to the chain"
        );
    }

    #[test]
    fn firing_an_unauthorized_affordance_is_refused_in_band_the_anti_ghost_tooth() {
        // The anti-ghost tooth: the EDITOR tier firing `admin` (which requires the
        // root tier) is REFUSED IN-BAND by the real is_attenuation, before any
        // executor turn — never silently run.
        let (mut world, anchors) = demo_world();
        let err = WebCellsBrowser::fire_affordance(
            &mut world,
            anchors[0],
            anchors[0],
            AuthRequired::Either, // editor tier: does NOT clear admin
            "admin",
        )
        .unwrap_err();
        assert!(
            err.contains("Unauthorized"),
            "the editor firing admin is refused in-band (anti-ghost), got: {err}"
        );
    }

    #[test]
    fn the_browser_speaks_real_attested_text_about_the_real_cells() {
        // The anti-blank guarantee, mirroring landing.rs: the rendered panel
        // contains many lines of real text naming the real dregg:// cells, their
        // attestation, the per-viewer affordances, the liveness-type, and the
        // servo-next note.
        let (world, anchors) = demo_world();
        let browser = WebCellsBrowser::build(&world, anchors[2], editor_rights(), Some(anchors[0]));
        let text = browser.all_text();
        assert!(text.len() >= 12, "the panel renders many lines of real text, got {}", text.len());
        for line in &text {
            assert!(!line.trim().is_empty(), "every panel line is non-empty real text");
        }
        let blob = text.join("\n");
        // It names the genuine web-of-cells machinery.
        assert!(blob.contains("dregg://"), "names the dregg:// addressing");
        assert!(blob.contains("attested="), "shows the attestation verdict");
        assert!(blob.to_lowercase().contains("attenuat"), "names the progressive attenuation");
        assert!(blob.contains("rehydration:"), "names the rehydration liveness-type");
        // It names the servo NEXT layer honestly (integrated vs named-next).
        assert!(blob.contains("servo"), "names the servo next layer");
    }
}
