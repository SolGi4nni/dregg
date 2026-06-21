//! Whole-cell transclusion — the Nelson dream at CELL granularity.
//!
//! `docs/deos/DOC-CELL-COMPOSITION.md §"transclusion of whole cells"` (this module
//! is its bounded prototype). A document is a cell; today a document INCLUDES other
//! cells only by quoting a single committed FIELD VALUE (the Xanadu field-value
//! citation: `web_aff::transclusion::TranscludedField` = the Lean
//! `Dregg2.Deos.Transclusion` = `ImportedEq` of a peer cell's finalized scalar). This
//! module lifts that ONE rung: a document transcludes an **ENTIRE cell** — a live,
//! per-viewer, attenuated VIEW of a whole other cell (its rendered surface + its
//! affordances + its sub-document), confined by the membrane so the embed can never
//! amplify, provenanced + unforgeable exactly like the field-value quote.
//!
//! ## The single design move: cite a SURFACE, not a SCALAR.
//!
//! The kernel already gives whole-cell-as-capability for free: `Dregg2.Deos.Surface`
//! proves a deos window IS a `Cap.endpoint cell rights` — `Target::Surface(cell)` is a
//! point on the existing `(target, rights)` gradation, and `surfaceConfersExactly`
//! says a window confers EXACTLY its rights and the pixels add zero hidden authority.
//! So:
//!
//! - a **field-value** transclusion cites a scalar (`Provenance { content_hash,
//!   receipt_hash }` of one finalized field) — `TranscludedField`;
//! - a **whole-cell** transclusion cites a *surface* — the whole source cell, observed
//!   per-viewer through the [`web_aff::Membrane`] as an attenuated
//!   [`web_aff::SurfaceCapability`] (a `Target::Surface(cell)` cap) carrying the source
//!   cell's affordance set projected to what THIS reader's caps clear.
//!
//! Nothing here is new mathematics or a new gate. Every load-bearing piece is welded:
//!
//! | concern | reused organ | what it gives |
//! |---|---|---|
//! | the whole-cell handle | `Dregg2.Deos.Surface` / `SurfaceCapability` (`Target::Surface`) | a cell IS a cap; a window confers exactly its rights |
//! | provenance / anti-forge | `TranscludedField::include`/`verify` | the embedded cell's committed *surface root* is content-addressed + receipt-pinned + quorum-finalized; a forge cannot be cited |
//! | per-viewer projection (fog-of-war) | `Membrane::project` + `AffordanceSurface::project_for` | each reader sees the embed through their OWN caps; an unreachable embed darkens, never forges |
//! | reshare-hop non-amplification | `Membrane::reshare` (Lean `reshareN_attenuates`) | the embed re-shared down a chain only ever shrinks; a hop that amplifies is REFUSED |
//! | the unbreakable link | `transclusion_stable_under_source_advance` | the cited surface root pins an immutable receipt; the embed never rots |
//! | rehydration / liveness | `web_aff::rehydrate` + `Rehydration` | the embed re-expands per-viewer, liveness-typed (LIVE / REPLAYED / RECONSTRUCTED) |
//!
//! ## What this prototype IS and is NOT.
//!
//! It is a gpui-free, `cargo test`-able MODEL (like `web_cells.rs`): a
//! [`WholeCellTransclusion`] cites a source cell's finalized surface root via a REAL
//! [`TranscludedField`] (so provenance/forge/no-rot are the genuine proven properties),
//! and [`WholeCellTransclusion::project_for`] resolves a per-viewer
//! [`EmbeddedCellView`] through the REAL [`web_aff::Membrane`] +
//! [`web_aff::AffordanceSurface::project_for`]. It composes with the affordance /
//! rehydration stack by re-using [`web_aff::rehydrate`] for the liveness-type.
//!
//! It is NOT: a new circuit constraint (ZERO Rust-authored constraints — the embed's
//! soundness is the EXISTING `TranscludedField` provenance + `Membrane` non-amp), nor a
//! replacement for the field-value quote (both coexist — a document composes from BOTH
//! field-value spans and whole-cell embeds), nor a recursion engine (nested whole-cell
//! embeds are MODELLED to one depth here with the composition law stated; the fixpoint
//! is the named residual).

use std::collections::BTreeSet;

use starbridge_web_surface as web_aff;
use web_aff::affordance::{AffordanceSurface, CellAffordance};
use web_aff::delegate::SurfaceCapability;
use web_aff::rehydrate::{rehydrate, Membrane, RehydrateError, Rehydration, Sturdyref};
use web_aff::transclusion::{Provenance, TranscludedField, TransclusionError};
use web_aff::web_of_cells::{DreggUri, WebOfCells};
use web_aff::{AuthRequired, CellId};

/// A **whole-cell transclusion** — a document's first-class, provenanced inclusion of
/// an ENTIRE peer cell (vs. [`TranscludedField`], which includes one finalized field
/// VALUE).
///
/// The crucial distinction from the field-value quote: a `TranscludedField` cites a
/// scalar and renders bytes; a `WholeCellTransclusion` cites the source cell's
/// *finalized surface root* and renders a per-viewer attenuated VIEW of the whole cell
/// — its affordances, its sub-document, its rehydratable surface. The provenance is the
/// SAME shape (a content-addressed, receipt-pinned, quorum-finalized
/// [`Provenance`]) — but what it pins is the cell's surface commitment, not a field
/// value. So the embed inherits, verbatim, the four proven Xanadu properties of the
/// field-value quote (observed-finalized-read / provenance-faithful / no-amplify /
/// stable-under-advance), now over a WHOLE cell.
#[derive(Clone, Debug)]
pub struct WholeCellTransclusion {
    /// The HOST cell (the document doing the including).
    pub host: CellId,
    /// The SOURCE cell whose whole surface is embedded.
    pub source: CellId,
    /// The verified finalized read of the source cell's surface root — the REAL
    /// [`TranscludedField`] (the bytes are the source's committed surface commitment,
    /// content-addressed + receipt-pinned + quorum-finalized). This is what makes the
    /// embed UNFORGEABLE and NON-ROTTING by the existing proofs: a forged surface
    /// cannot be cited (`verify()` refuses), and the cited receipt is an immutable past.
    pub surface_read: TranscludedField,
    /// The source cell's DECLARED affordance surface — the full set of named,
    /// cap-gated effect-templates the embedded cell publishes. NOT yet projected: this
    /// is the source's whole surface; [`Self::project_for`] attenuates it per-viewer.
    /// (In the welded substrate this is re-derived AT the source on resolution; the
    /// prototype carries it so the model is self-contained and testable.)
    pub declared_surface: AffordanceSurface,
    /// The source cell's authority LINEAGE — the surface authority the embedded cell's
    /// view is a certified projection of (the ceiling any per-viewer projection
    /// attenuates from). The membrane re-derives every reader's view as `(reader held)
    /// ∧ (this lineage)`; a reader never gets more than the lineage permits.
    pub lineage: SurfaceCapability,
}

/// Why building a [`WholeCellTransclusion`] failed — the SAME refusal shapes as the
/// field-value quote (a forged/absent/non-finalized surface cannot be embedded).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WholeCellTransclusionError {
    /// The source cell's surface root did not resolve to a finalized read, or its
    /// provenance did not verify (a forged or absent embed). No opened provenance ⇒ no
    /// embed — the anti-forge tooth, inherited from [`TranscludedField::include`].
    Surface(TransclusionError),
}

impl WholeCellTransclusion {
    /// **Embed a whole peer cell by reference** — the whole-cell analogue of
    /// [`TranscludedField::include`].
    ///
    /// Performs the REAL `dregg://` attested fetch of the source cell's surface root
    /// against `web`, VERIFIES its provenance (content → commitment → receipt →
    /// receipt-stream root → quorum), and pins the cited surface. Refuses if the
    /// provenance does not verify (a forged surface cannot be cited) or the read is not
    /// quorum-finalized — exactly the field-value quote's gate, now over the whole
    /// cell. On success the embed's surface IS the source cell's committed surface, with
    /// the citation that dates it; the membrane will attenuate it per-viewer.
    ///
    /// `declared_surface` is the source cell's published affordance set (re-derived at
    /// the source in the welded substrate); `lineage` is the surface authority the
    /// embed is a certified projection of (the per-viewer ceiling).
    pub fn embed(
        web: &WebOfCells,
        host: CellId,
        source_uri: &DreggUri,
        declared_surface: AffordanceSurface,
        lineage: SurfaceCapability,
    ) -> Result<WholeCellTransclusion, WholeCellTransclusionError> {
        // The verified finalized read of the source cell's surface root. A forged or
        // absent or non-finalized surface fails HERE — the embed inherits the proven
        // anti-forge tooth (`transclusion_forge_refused`) verbatim.
        let surface_read = TranscludedField::include(web, source_uri)
            .map_err(WholeCellTransclusionError::Surface)?;
        Ok(WholeCellTransclusion {
            host,
            source: source_uri.cell,
            surface_read,
            declared_surface,
            lineage,
        })
    }

    /// The immutable provenance the embed carries (the source ref + the cited surface
    /// commitment + receipt + finalized flag) — what tooling renders as "embedding
    /// `dregg://<cell>` at receipt R; finalized". Honest, dated provenance, identical
    /// in shape to the field-value quote's.
    pub fn cite(&self) -> &Provenance {
        self.surface_read.cite()
    }

    /// **Re-verify the embed's provenance** (`transclusion_provenance_faithful`, whole-
    /// cell form) — the embedded surface root EQUALS the source's committed surface,
    /// recomputably. Inherits [`TranscludedField::verify`] verbatim: a tampered surface
    /// root REFUSES.
    pub fn verify(&self) -> bool {
        self.surface_read.verify().is_ok()
    }

    /// **Project the whole-cell embed PER-VIEWER through the membrane** — THE core of
    /// "fog-of-war inside a document": each reader sees the embedded cell through their
    /// OWN caps.
    ///
    /// Two moves, both on the REAL organs:
    ///
    /// 1. **the per-viewer surface cap** — meet the `viewer`'s held authority with the
    ///    embed's `lineage` through the REAL [`Membrane::project`] (the `is_attenuation`
    ///    lattice on window rights + set-intersection on web caveats). The result is the
    ///    cap the reader holds OVER the embedded cell — never wider than EITHER the
    ///    reader's held authority OR the lineage. If they are incomparable, the embed
    ///    DARKENS (no view both admit) — the whole-cell analogue of a darkened span.
    /// 2. **the per-viewer affordance set** — project the source cell's
    ///    `declared_surface` to exactly the affordances that per-viewer cap clears
    ///    ([`AffordanceSurface::project_for`], the SAME real `is_attenuation` gate). A
    ///    weaker reader sees FEWER affordances of the embedded cell; an admin reader
    ///    sees more — the embedded cell is itself a frustum re-derived per viewer.
    ///
    /// The provenance ALWAYS survives (the citation), even when darkened — bytes/
    /// affordances withheld, never forged, never substituted (the membrane non-amp:
    /// `transclusion_no_amplify`).
    pub fn project_for(&self, viewer: &Membrane) -> EmbeddedCellView {
        // (1) the per-viewer surface cap: (reader held) ∧ (embed lineage), REAL lattice.
        match viewer.project(&self.lineage) {
            Ok(projected) => {
                // (2) the per-viewer affordance set: only what this cap clears.
                let affordances = self.declared_surface.project_for(&projected);
                let affordance_names: Vec<String> =
                    affordances.iter().map(|a| a.name.clone()).collect();
                EmbeddedCellView {
                    source: self.source,
                    provenance: self.cite().clone(),
                    visibility: EmbedVisibility::Visible {
                        viewer_cap_rights: projected.window.rights.clone(),
                        affordances,
                        affordance_names,
                    },
                    declared_affordance_count: self.declared_surface.affordances.len(),
                }
            }
            // Incomparable authority: NO view both admit — the embed darkens. The
            // provenance survives; the surface + affordances are withheld (never
            // forged). This is the whole-cell analogue of `DocumentSpanKind::Darkened`.
            Err(RehydrateError::Amplification) => EmbeddedCellView {
                source: self.source,
                provenance: self.cite().clone(),
                visibility: EmbedVisibility::Darkened,
                declared_affordance_count: self.declared_surface.affordances.len(),
            },
            // A fetch failure inside the projection (cannot happen here — project does
            // no fetch — but the type forces honesty): treat as darkened.
            Err(RehydrateError::Fetch(_)) => EmbeddedCellView {
                source: self.source,
                provenance: self.cite().clone(),
                visibility: EmbedVisibility::Darkened,
                declared_affordance_count: self.declared_surface.affordances.len(),
            },
        }
    }

    /// **Reshare the embed down a hop** — the whole-cell analogue of the membrane
    /// reshare (Lean `reshareN_attenuates` / `reshare_refuses_amplification`).
    ///
    /// When a reader who holds the embed re-shares it to a downstream reader, the
    /// downstream cap MUST be an attenuation of what this reader held — a hop that
    /// tries to AMPLIFY (grant the downstream reader more authority over the embedded
    /// cell than the resharer held) is REFUSED ([`RehydrateError::Amplification`]).
    /// This rides [`Membrane::reshare`] verbatim, so the proven non-amplification is
    /// inherited: however many hops an embed travels, the last holder's authority over
    /// the embedded cell is bounded by the first holder's.
    pub fn reshare_to(
        holder: &Membrane,
        downstream: SurfaceCapability,
    ) -> Result<Membrane, RehydrateError> {
        holder.reshare(downstream)
    }

    /// **Rehydrate the embed PER-VIEWER with its liveness-type** — composing with the
    /// affordance/rehydration stack ([`web_aff::rehydrate`]).
    ///
    /// The embed's source cell is rehydrated through the reader's membrane against a
    /// [`Sturdyref`] over the source: the fetch is verified (an unattested embedded
    /// cell yields NO view — confinement before relation), the per-viewer projection is
    /// derived, and the [`Rehydration`] liveness-type is attached (LIVE / REPLAYED-
    /// DETERMINISTIC / RECONSTRUCTED-APPROXIMATE). So an embedded cell is not a dead
    /// snapshot — it is a liveness-typed, per-viewer re-expansion of a witnessed cell,
    /// the same kind of object a rehydrated surface is.
    pub fn rehydrate_embed(
        sturdyref: &Sturdyref,
        viewer: &Membrane,
        web: &WebOfCells,
    ) -> Result<Rehydration, RehydrateError> {
        let projection = rehydrate(sturdyref, viewer, web)?;
        Ok(projection.liveness)
    }
}

/// The per-viewer **view of an embedded whole cell** — what a specific reader sees of a
/// [`WholeCellTransclusion`] through their own caps. The whole-cell analogue of a
/// rendered document span (`DocumentSpanRow`), but the unit is a CELL.
#[derive(Clone, Debug)]
pub struct EmbeddedCellView {
    /// The embedded source cell (the `dregg://<cell>` the embed cites). Always present
    /// — the citation survives even when the embed is darkened.
    pub source: CellId,
    /// The immutable provenance — the cited surface commitment + receipt + finalized
    /// flag. ALWAYS present (the provenance survives darkening): the reader can always
    /// see WHAT cell is embedded and that it is genuinely cited, even if they cannot see
    /// INTO it. (Never forged, never substituted.)
    pub provenance: Provenance,
    /// What this reader can actually SEE of the embedded cell — visible (with their
    /// per-viewer affordance set) or darkened (authority withheld, provenance kept).
    pub visibility: EmbedVisibility,
    /// How many affordances the embedded cell DECLARES in total (so a panel can show
    /// "you see N of M — the rest are attenuated away by your caps").
    pub declared_affordance_count: usize,
}

/// Whether a reader can see INTO an embedded cell, and if so, at what cap level.
#[derive(Clone, Debug)]
pub enum EmbedVisibility {
    /// The reader's caps reach the embed: they see it at their per-viewer cap level,
    /// with the affordance set their caps clear.
    Visible {
        /// The per-viewer cap rights the reader holds over the embedded cell — the meet
        /// of (their held authority) ∧ (the embed lineage). Never wider than either.
        viewer_cap_rights: AuthRequired,
        /// The affordances of the embedded cell this reader's cap clears — the
        /// per-viewer projection. A weaker reader sees fewer; an admin sees more.
        affordances: Vec<CellAffordance>,
        /// The names of those affordances (sorted-stable readout for tests/panels).
        affordance_names: Vec<String>,
    },
    /// The reader's authority is INCOMPARABLE with the embed lineage — no view both
    /// admit. The embed darkens: provenance kept, surface + affordances withheld (never
    /// forged). The whole-cell analogue of `DocumentSpanKind::Darkened`.
    Darkened,
}

impl EmbeddedCellView {
    /// Is this embed visible to the reader (vs. darkened)?
    pub fn is_visible(&self) -> bool {
        matches!(self.visibility, EmbedVisibility::Visible { .. })
    }

    /// The affordance names this reader sees of the embedded cell (sorted); empty for a
    /// darkened embed. The per-viewer fog-of-war readout.
    pub fn visible_affordance_names(&self) -> Vec<String> {
        match &self.visibility {
            EmbedVisibility::Visible {
                affordance_names, ..
            } => {
                let mut names = affordance_names.clone();
                names.sort();
                names
            }
            EmbedVisibility::Darkened => Vec::new(),
        }
    }

    /// A one-line badge (the panel's per-embed readout) — visible-at-tier vs darkened,
    /// always carrying the surviving provenance citation.
    pub fn badge(&self) -> String {
        match &self.visibility {
            EmbedVisibility::Visible {
                viewer_cap_rights,
                affordance_names,
                ..
            } => format!(
                "EMBED visible @ {:?}: {} of {} affordances [{}] (cited dregg://, finalized={})",
                viewer_cap_rights,
                affordance_names.len(),
                self.declared_affordance_count,
                affordance_names.join(", "),
                self.provenance.finalized
            ),
            EmbedVisibility::Darkened => format!(
                "EMBED darkened (authority withheld; provenance kept; cited dregg://, finalized={})",
                self.provenance.finalized
            ),
        }
    }
}

/// A **document as a composition of whole cells** — the minimal model of ember's
/// question "should documents be composed FROM cells — include WHOLE cells, nest
/// cells, be a *composition* of cells?".
///
/// A composed document is the host cell's OWN affordance surface PLUS an ordered list
/// of whole-cell embeds. Resolving it per-viewer ([`Self::resolve_for`]) projects the
/// host's own affordances AND each embed through the SAME membrane — so the WHOLE
/// composed document is one frustum re-derived per viewer: a reader sees the host's
/// affordances their caps clear, and for each embed sees into it (or not) at their cap
/// level. This is the cell-granularity sibling of `DreggverseDocumentView` (which
/// composes from field-value spans); here the unit of composition is a CELL.
#[derive(Clone, Debug)]
pub struct ComposedCellDocument {
    /// The host document cell.
    pub host: CellId,
    /// The host's OWN affordance surface (the document's own affordances, not embedded).
    pub own_surface: AffordanceSurface,
    /// The whole-cell embeds, in document order.
    pub embeds: Vec<WholeCellTransclusion>,
}

impl ComposedCellDocument {
    /// A composed document over `host` with its own affordance surface and no embeds.
    pub fn new(host: CellId, own_surface: AffordanceSurface) -> Self {
        ComposedCellDocument {
            host,
            own_surface,
            embeds: Vec::new(),
        }
    }

    /// Add a whole-cell embed to the document (builder-style).
    pub fn embed(mut self, embed: WholeCellTransclusion) -> Self {
        self.embeds.push(embed);
        self
    }

    /// **Resolve the whole composed document PER-VIEWER** — the host's own affordances
    /// (projected to the reader's caps) plus each embed's per-viewer
    /// [`EmbeddedCellView`]. One membrane, one reader, one frustum over the WHOLE
    /// composition of cells.
    pub fn resolve_for(&self, viewer: &Membrane) -> ComposedCellDocumentView {
        let own_affordances = self.own_surface.project_for(viewer.held());
        let own_affordance_names: Vec<String> =
            own_affordances.iter().map(|a| a.name.clone()).collect();
        let embed_views: Vec<EmbeddedCellView> =
            self.embeds.iter().map(|e| e.project_for(viewer)).collect();
        let darkened_embeds = embed_views.iter().filter(|v| !v.is_visible()).count();
        ComposedCellDocumentView {
            host: self.host,
            own_affordance_names,
            embed_views,
            darkened_embeds,
        }
    }
}

/// The per-viewer rendered view of a [`ComposedCellDocument`] — the host's own
/// affordances the reader clears + each embedded cell's per-viewer view.
#[derive(Clone, Debug)]
pub struct ComposedCellDocumentView {
    /// The host document cell.
    pub host: CellId,
    /// The host's OWN affordance names this reader clears (projected per-viewer).
    pub own_affordance_names: Vec<String>,
    /// Each whole-cell embed's per-viewer view (visible-at-tier or darkened).
    pub embed_views: Vec<EmbeddedCellView>,
    /// How many embeds were darkened for this reader (authority withheld). `0` for a
    /// full-authority render.
    pub darkened_embeds: usize,
}

impl ComposedCellDocumentView {
    /// Did the whole composition render fully for this reader (no embed darkened)?
    pub fn full(&self) -> bool {
        self.darkened_embeds == 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use web_aff::affordance::CellAffordance;
    use web_aff::dregg_turn_reexport::Event;
    use web_aff::Effect;

    fn cid(b: u8) -> CellId {
        let mut k = [0u8; 32];
        k[0] = b;
        CellId::derive_raw(&k, &[0u8; 32])
    }

    /// A real `EmitEvent` effect (the genuine turn for a view/comment affordance).
    fn emit_event(cell: CellId) -> Effect {
        Effect::EmitEvent {
            cell,
            event: Event {
                topic: [1u8; 32],
                data: vec![],
            },
        }
    }

    /// A real `GrantCapability` effect (the genuine turn for an admin affordance).
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

    /// The source cell's published whole surface: the canonical {view, comment, edit,
    /// admin} on the three-tier rights chain `Signature ⊂ Either ⊂ None` — view at
    /// tier-1, comment+edit at tier-2, admin at tier-3. Each a REAL effect-template.
    fn source_surface(source: CellId) -> AffordanceSurface {
        AffordanceSurface::new(source)
            .declare(CellAffordance::new(
                "view",
                AuthRequired::Signature,
                emit_event(source),
            ))
            .declare(CellAffordance::new(
                "comment",
                AuthRequired::Either,
                emit_event(source),
            ))
            .declare(CellAffordance::new(
                "edit",
                AuthRequired::Either,
                emit_event(source),
            ))
            .declare(CellAffordance::new(
                "admin",
                AuthRequired::None,
                grant_cap(source, cid(99)),
            ))
    }

    /// Publish a source cell into a fresh web-of-cells (its surface root committed +
    /// 3-of-3 quorum-attested — a genuine finalized read) and build a whole-cell embed
    /// of it whose lineage is a strong (Either) authority over the source.
    fn embed_of(host_seed: u8, source_seed: u8) -> (WebOfCells, WholeCellTransclusion) {
        let mut web = WebOfCells::new(3);
        let uri = web.publish(source_seed, b"<cell surface root>", "dregg://embedded-cell");
        let host = cid(host_seed);
        let declared = source_surface(uri.cell);
        let lineage = SurfaceCapability::root(uri.cell, AuthRequired::Either);
        let embed = WholeCellTransclusion::embed(&web, host, &uri, declared, lineage)
            .expect("the source cell's surface is finalized and embeds");
        (web, embed)
    }

    // (1) THE DEFINITIONAL BRIDGE — a whole-cell embed IS a verified finalized read of
    //     the source cell's surface root (provenance carried, finalized).
    #[test]
    fn whole_cell_embed_is_a_verified_finalized_read() {
        let (_web, embed) = embed_of(1, 2);
        // The embed carries provenance: the source ref + a finalized flag.
        assert!(embed.cite().finalized, "an embedded cell's surface is finalized");
        // The content commitment is the content address of the cited surface root.
        assert_eq!(embed.cite().content_hash, embed.surface_read.resource.content_hash);
        // The embed re-verifies (provenance faithful — the surface equals its source).
        assert!(embed.verify(), "the embed's surface-root provenance chain verifies");
    }

    // (1b) ANTI-FORGE — an absent source cell cannot be embedded (no finalized read).
    #[test]
    fn an_absent_source_cell_cannot_be_embedded() {
        let web = WebOfCells::new(3);
        let absent = DreggUri::new(cid(200));
        let declared = source_surface(cid(200));
        let lineage = SurfaceCapability::root(cid(200), AuthRequired::Either);
        let r = WholeCellTransclusion::embed(&web, cid(1), &absent, declared, lineage);
        assert!(
            matches!(
                r,
                Err(WholeCellTransclusionError::Surface(TransclusionError::Fetch(_)))
            ),
            "an absent source cannot be embedded (no finalized read), got {r:?}"
        );
    }

    // ── THE BOTH-POLARITY CORE: a viewer sees the embed at THEIR cap level; an
    //    over-reach is refused. Fog-of-war inside a document. ──

    // (2) POSITIVE — a reader sees the embedded cell at their OWN cap level: the
    //     affordance set is exactly what their caps clear, and it GROWS with authority.
    #[test]
    fn each_reader_sees_the_embed_at_their_own_cap_level() {
        let (_web, embed) = embed_of(3, 4);

        // A tier-1 reader (Signature): sees only the `view` affordance of the embed.
        let viewer = Membrane::new(SurfaceCapability::root(cid(10), AuthRequired::Signature));
        let v = embed.project_for(&viewer);
        assert!(v.is_visible(), "a Signature reader can see into the embed");
        assert_eq!(
            v.visible_affordance_names(),
            vec!["view".to_string()],
            "a weak reader sees only the affordances their caps clear"
        );
        assert_eq!(v.declared_affordance_count, 4);

        // A tier-2 reader (Either): sees view + comment + edit (NOT admin).
        let editor = Membrane::new(SurfaceCapability::root(cid(11), AuthRequired::Either));
        let e = embed.project_for(&editor);
        assert!(e.is_visible());
        assert_eq!(
            e.visible_affordance_names(),
            vec!["comment".to_string(), "edit".to_string(), "view".to_string()]
        );

        // FOG-OF-WAR: the SAME embed, two readers, DIFFERENT views. The weaker reader's
        // view is a strict subset of the stronger's — the embed is a per-viewer frustum.
        let weak = v.visible_affordance_names();
        let strong = e.visible_affordance_names();
        assert_ne!(weak, strong, "two readers see the same embed differently");
        assert!(
            weak.iter().all(|n| strong.contains(n)),
            "the weaker reader's view is a subset of the stronger's"
        );
    }

    // (2b) The provenance ALWAYS survives, even at the weakest tier (never forged).
    #[test]
    fn the_embed_provenance_survives_for_every_reader() {
        let (_web, embed) = embed_of(5, 6);
        let weak = Membrane::new(SurfaceCapability::root(cid(10), AuthRequired::Signature));
        let v = embed.project_for(&weak);
        // The citation is present and equals the embed's: the reader always knows WHAT
        // cell is embedded and that it is genuinely cited.
        assert_eq!(v.provenance, *embed.cite());
        assert!(v.provenance.finalized);
    }

    // (3) NEGATIVE — an OVER-REACH is refused: a reader whose authority is INCOMPARABLE
    //     with the embed lineage darkens the embed (no view both admit). The
    //     whole-cell analogue of a darkened span — provenance kept, surface withheld.
    #[test]
    fn an_overreach_reader_sees_the_embed_darkened() {
        // The embed's lineage is Either. A reader holding `Proof` is INCOMPARABLE with
        // Either (neither attenuates the other) — there is NO projection both admit.
        let (_web, embed) = embed_of(7, 8);
        let proof_reader = Membrane::new(SurfaceCapability::root(cid(13), AuthRequired::Proof));
        let v = embed.project_for(&proof_reader);
        assert!(
            !v.is_visible(),
            "an incomparable-authority reader cannot see into the embed — it darkens"
        );
        assert!(matches!(v.visibility, EmbedVisibility::Darkened));
        // But the provenance STILL survives — darkening withholds, never forges.
        assert_eq!(v.provenance, *embed.cite());
        assert!(v.visible_affordance_names().is_empty());
    }

    // (4) RESHARE-HOP NON-AMPLIFICATION — re-sharing the embed down a chain can only
    //     shrink; a hop that amplifies is REFUSED (Lean reshareN_attenuates).
    #[test]
    fn resharing_the_embed_cannot_amplify() {
        use web_aff::delegate::PermissionKind;
        // The first holder A holds Either over {a, b}.
        let a = Membrane::new(SurfaceCapability::scoped(
            cid(80),
            AuthRequired::Either,
            ["https://a.example.com".to_string(), "https://b.example.com".to_string()],
            std::iter::empty::<PermissionKind>(),
        ));
        // A → B: narrow the embed to {a}. ADMITTED (a strict attenuation).
        let b = WholeCellTransclusion::reshare_to(
            &a,
            SurfaceCapability::scoped(
                cid(81),
                AuthRequired::Either,
                ["https://a.example.com".to_string()],
                std::iter::empty::<PermissionKind>(),
            ),
        )
        .expect("a narrowing reshare of the embed is admitted");
        assert!(b.held().may_fetch("https://a.example.com"));
        assert!(!b.held().may_fetch("https://b.example.com"));

        // B → C: try to AMPLIFY the embed back to {a, b} — REFUSED (the anti-ghost
        // tooth: C cannot receive more over the embedded cell than B held).
        let amplify = WholeCellTransclusion::reshare_to(
            &b,
            SurfaceCapability::scoped(
                cid(82),
                AuthRequired::Either,
                ["https://a.example.com".to_string(), "https://b.example.com".to_string()],
                std::iter::empty::<PermissionKind>(),
            ),
        );
        assert_eq!(amplify, Err(RehydrateError::Amplification));

        // …and widening the WINDOW RIGHTS of the embed (Either → None) is refused too.
        let widen_rights = WholeCellTransclusion::reshare_to(
            &b,
            SurfaceCapability::root(cid(83), AuthRequired::None),
        );
        assert_eq!(widen_rights, Err(RehydrateError::Amplification));
    }

    // (5) COMPOSITION — a document composed FROM whole cells resolves per-viewer: the
    //     host's own affordances + each embed, all through one membrane. Two readers
    //     get different views of the whole composition.
    #[test]
    fn a_document_composed_from_whole_cells_resolves_per_viewer() {
        let host = cid(20);
        let (_w1, embed_a) = embed_of(20, 30);
        let (_w2, embed_b) = embed_of(20, 31);
        // The host's OWN surface: a view + an edit affordance.
        let own = AffordanceSurface::new(host)
            .declare(CellAffordance::new(
                "doc-view",
                AuthRequired::Signature,
                emit_event(host),
            ))
            .declare(CellAffordance::new(
                "doc-edit",
                AuthRequired::Either,
                emit_event(host),
            ));
        let doc = ComposedCellDocument::new(host, own)
            .embed(embed_a)
            .embed(embed_b);

        // A tier-1 reader: sees only `doc-view` of the host, and only `view` of each
        // embed — the whole composition projected to their caps.
        let viewer = Membrane::new(SurfaceCapability::root(cid(10), AuthRequired::Signature));
        let view = doc.resolve_for(&viewer);
        assert_eq!(view.host, host);
        assert_eq!(view.own_affordance_names, vec!["doc-view".to_string()]);
        assert_eq!(view.embed_views.len(), 2);
        for ev in &view.embed_views {
            assert!(ev.is_visible());
            assert_eq!(ev.visible_affordance_names(), vec!["view".to_string()]);
        }
        assert!(view.full(), "both embeds are visible to the Signature reader");

        // A tier-2 reader: sees doc-view + doc-edit of the host, and view+comment+edit
        // of each embed — a strictly richer view of the SAME composition.
        let editor = Membrane::new(SurfaceCapability::root(cid(11), AuthRequired::Either));
        let eview = doc.resolve_for(&editor);
        assert_eq!(
            eview.own_affordance_names,
            vec!["doc-edit".to_string(), "doc-view".to_string()]
                .into_iter()
                .collect::<Vec<_>>()
        );
        for ev in &eview.embed_views {
            assert_eq!(
                ev.visible_affordance_names(),
                vec!["comment".to_string(), "edit".to_string(), "view".to_string()]
            );
        }

        // DIVERGENCE: the same composed document, two readers, different whole-document
        // views (the composition is one per-viewer frustum over cells).
        assert_ne!(view.own_affordance_names, eview.own_affordance_names);
    }

    // (5b) A reader incomparable with one embed's lineage darkens THAT embed but still
    //      sees the rest of the composition — fog-of-war is per-embed, not all-or-
    //      nothing. (A document stays usable while one embed is withheld.)
    #[test]
    fn a_reader_darkens_one_embed_but_sees_the_rest() {
        let host = cid(21);
        let (_w, normal_embed) = embed_of(21, 32);
        // A second embed whose lineage is Signature (so a Proof reader is incomparable
        // with it and darkens it), while the first (Either lineage) is ALSO incomparable
        // with Proof... so to get a MIXED result, make the second embed's lineage None
        // (root) — Proof ⊆ None, so a Proof reader CAN see it.
        let mut web2 = WebOfCells::new(3);
        let uri2 = web2.publish(33, b"<root-lineage cell>", "dregg://root-cell");
        let root_embed = WholeCellTransclusion::embed(
            &web2,
            host,
            &uri2,
            source_surface(uri2.cell),
            SurfaceCapability::root(uri2.cell, AuthRequired::None), // root lineage
        )
        .expect("embeds");

        let own = AffordanceSurface::new(host);
        let doc = ComposedCellDocument::new(host, own)
            .embed(normal_embed) // Either lineage — Proof incomparable → darkens
            .embed(root_embed); // None lineage — Proof ⊆ None → visible

        let proof_reader = Membrane::new(SurfaceCapability::root(cid(13), AuthRequired::Proof));
        let view = doc.resolve_for(&proof_reader);
        assert_eq!(view.embed_views.len(), 2);
        // First embed (Either lineage): darkened (Proof incomparable with Either).
        assert!(!view.embed_views[0].is_visible());
        // Second embed (None/root lineage): visible (Proof ⊆ None).
        assert!(view.embed_views[1].is_visible());
        // Exactly one embed darkened — the rest of the composition is usable.
        assert_eq!(view.darkened_embeds, 1);
        assert!(!view.full());
        // The darkened embed STILL carries its provenance (never forged).
        assert_eq!(view.embed_views[0].provenance, *doc.embeds[0].cite());
    }
}

// A tiny compile-time witness that the unused-import lint stays honest about the
// surface area this prototype welds (these are the organs the design leans on).
#[allow(dead_code)]
fn _organ_census() {
    let _: Option<BTreeSet<String>> = None;
}
