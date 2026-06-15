//! The **deos-app transclusion affordance** — the named consumer of the
//! transclusion primitive (`starbridge_web_surface::transclusion`).
//!
//! `starbridge_web_surface::transclusion` (the Rust mirror of
//! `Dregg2.Deos.Transclusion`) made Ted Nelson's Xanadu quote HONEST on the
//! verified substrate: a [`TranscludedField`] is a verified cross-cell finalized
//! read — its displayed bytes ARE the source's committed bytes, it carries an
//! immutable [`Provenance`] citation, a forged/absent provenance is REFUSED, and
//! it projects per-viewer through the REAL [`Membrane`] (a quote is a READ, never
//! a key — it cannot amplify). The module's own doc names THIS module as the
//! intended fast-follow (`transclusion.rs` §"Consumers"):
//!
//! > **The deos-app-framework transclusion affordance** — a `CellAffordance` whose
//! > render embeds a `TranscludedField`, so an app declares a quote the way it
//! > declares any other affordance, projected per-viewer through the same membrane.
//!
//! This is that consumer, built ON the REAL primitives — it NAMES
//! [`TranscludedField`], [`Provenance`], [`Backlinks`], [`Membrane`],
//! [`SurfaceCapability`], and [`WebOfCells`] from `starbridge-web-surface`, and the
//! REAL [`crate::affordance::CellAffordance`] / [`crate::affordance::AffordanceSurface`]
//! / [`crate::deos_app::DeosCell`] from the framework. It reinvents NONE of them
//! (no parallel attestation, no parallel cap model, no toy quote):
//!
//! - **declare a transclusion like any other affordance** — [`TranscludeAffordance`]
//!   pairs a framework [`CellAffordance`] (its name + cap-gate + effect-template)
//!   with the source `dregg://` ref it transcludes. A [`DeosCell`] declares it the
//!   same way it declares a `view`/`edit`/`admin` button (the
//!   [`DeosCellTranscludeExt`] extension trait), so the quote sits ALONGSIDE the
//!   cell's other affordances in its [`AffordanceSurface`].
//! - **render with provenance** — [`TranscludeAffordance::resolve`] performs the
//!   REAL [`TranscludedField::include`] (the verified finalized read), yielding a
//!   [`RenderedTransclusion`] that carries the quoted bytes AND the immutable
//!   [`Provenance`] citation (source ref + content commitment + receipt + finalized).
//! - **per-viewer through the membrane** — [`TranscludeAffordance::project_for`]
//!   gates the affordance with the framework's OWN cap-gate
//!   ([`CellAffordance::authorized_for`] = the REAL `is_attenuation`) AND projects
//!   the embedded quote through the REAL starbridge [`Membrane`]: a weaker viewer
//!   sees it strictly attenuated, never amplified — both teeth from the same
//!   attenuation lattice.
//! - **the witness-graph, the other way** — [`TranscludeAffordance::record_into`]
//!   populates a [`Backlinks`] registry (Nelson's two-way link, finally honest)
//!   from a resolved quote, so a cell's transclusion contributes a verifiable
//!   backlink ("observer O quoted source S at receipt R").
//!
//! ## Why this lives in the framework
//!
//! The transclusion PRIMITIVE (the verified read + the membrane + the backlinks)
//! is `starbridge-web-surface`'s. This module is the APP-FRAMEWORK surfacing of it:
//! it lets a [`DeosApp`](crate::deos_app::DeosApp) cell expose a transcluded peer
//! field as a first-class affordance, with the framework's affordance ergonomics
//! (declaration, per-viewer projection, the manifest readout). It adds NO new
//! semantics over either side — it is the WELD between the framework's affordance
//! model and the verified quote.

use starbridge_web_surface::delegate::SurfaceCapability;
use starbridge_web_surface::rehydrate::{Membrane, RehydrateError};
use starbridge_web_surface::transclusion::{
    Backlinks, Provenance, TranscludedField, TransclusionError,
};
use starbridge_web_surface::web_of_cells::{DreggUri, WebOfCells};

use dregg_cell::{AuthRequired, CellId};

use crate::affordance::{AffordanceSurface, CellAffordance};
use crate::deos_app::DeosCell;

// =============================================================================
// TranscludeAffordance — a framework affordance whose render embeds a quote
// =============================================================================

/// A **transclusion affordance** — a framework [`CellAffordance`] paired with the
/// source `dregg://` field it transcludes.
///
/// An app declares this the way it declares any other affordance: it carries a
/// `name`, a `required_rights` cap-gate, and a real effect-template (all in the
/// framework's own [`CellAffordance`]), PLUS the `source` ref whose finalized field
/// it quotes. When the framework renders the cell, this affordance's content is the
/// verified [`TranscludedField`] (the source's committed bytes + provenance),
/// projected per-viewer through the REAL [`Membrane`].
///
/// The cap-gate (who may SEE the affordance at all) is the framework's REAL
/// `is_attenuation` (via [`CellAffordance::authorized_for`]); the quote-projection
/// (what authority the quote confers over the source) is the starbridge
/// [`Membrane`]'s REAL `is_attenuation`-meet. Both teeth ride the same proven
/// attenuation lattice — a quote is a READ, per-viewer, never an amplification.
#[derive(Clone, Debug)]
pub struct TranscludeAffordance {
    /// The framework affordance the app declares (its name + the
    /// [`AuthRequired`] cap-gate + the real effect-template). The deos-app surfaces
    /// this in its [`AffordanceSurface`] alongside the cell's other affordances.
    pub affordance: CellAffordance,
    /// The source `dregg://` ref whose FINALIZED field this affordance transcludes —
    /// the cell whose committed value is quoted (the forward link's target).
    pub source: DreggUri,
}

impl TranscludeAffordance {
    /// Declare a transclusion affordance named `name`, requiring `required_rights`
    /// to be seen/fired, carrying `effect_template` (the real effect the framework
    /// would run for an interaction with the quote — e.g. an `EmitEvent` recording
    /// the citation), transcluding the finalized field at `source`.
    pub fn new(
        name: impl Into<String>,
        required_rights: AuthRequired,
        effect_template: dregg_turn::action::Effect,
        source: DreggUri,
    ) -> Self {
        TranscludeAffordance {
            affordance: CellAffordance::new(name, required_rights, effect_template),
            source,
        }
    }

    /// Pair an already-built framework [`CellAffordance`] with the `source` it
    /// transcludes — for callers who already have the affordance in hand.
    pub fn over(affordance: CellAffordance, source: DreggUri) -> Self {
        TranscludeAffordance { affordance, source }
    }

    /// The affordance's name (delegates to the carried [`CellAffordance`]).
    pub fn name(&self) -> &str {
        &self.affordance.name
    }

    /// The cap-gate authority a viewer must HOLD to see/fire this affordance (the
    /// `required ⊆ held` ceiling — the framework's REAL `is_attenuation`).
    pub fn required_rights(&self) -> &AuthRequired {
        &self.affordance.required_rights
    }

    /// The source `dregg://` ref this affordance transcludes (the forward link).
    pub fn source(&self) -> &DreggUri {
        &self.source
    }

    /// Is this affordance authorized for a holder of `held` authority? THE framework
    /// cap-gate, and it is the REAL one ([`CellAffordance::authorized_for`] =
    /// `is_attenuation`). A viewer who does not clear this gate does not see the
    /// quote at all (it is not in their [`AffordanceSurface::project_for`] slice).
    pub fn authorized_for(&self, held: &AuthRequired) -> bool {
        self.affordance.authorized_for(held)
    }

    /// **Resolve the embedded quote** — perform the REAL verified finalized read
    /// ([`TranscludedField::include`]) against `web` and render it WITH its
    /// provenance.
    ///
    /// This is the definitional bridge the primitive proves
    /// (`transclusion_is_observed_finalized_read`): the resolved content IS the
    /// source's committed bytes, carrying the immutable citation. A forged or absent
    /// provenance is REFUSED here (the `include` gate runs the genuine
    /// content→commitment→receipt→root→quorum chain), and an un-finalized read is
    /// refused — so a [`RenderedTransclusion`] only ever exists for a faithful,
    /// finalized quote.
    pub fn resolve(&self, web: &WebOfCells) -> Result<RenderedTransclusion, TransclusionError> {
        let field = TranscludedField::include(web, &self.source)?;
        Ok(RenderedTransclusion {
            affordance_name: self.affordance.name.clone(),
            field,
        })
    }

    /// **Project the affordance + its embedded quote PER-VIEWER** — both teeth of the
    /// attenuation lattice, in one call.
    ///
    /// 1. **the framework cap-gate** — if the viewer's `held` authority does not
    ///    clear [`CellAffordance::authorized_for`] (the REAL `is_attenuation`), the
    ///    affordance is not visible to them: returns
    ///    [`TranscludeProjectError::Unauthorized`] (the quote is not offered).
    /// 2. **the quote projection** — the quote is projected through the REAL
    ///    starbridge [`Membrane`]: the `viewer` membrane meets its held authority
    ///    with the source's `lineage` ([`TranscludedField::project_for`] →
    ///    [`Membrane::project`]). A weaker viewer receives a strictly attenuated
    ///    [`SurfaceCapability`]; the projection CANNOT amplify
    ///    (`transclusion_no_amplify`) — re-sharing the quote down a delegation chain
    ///    only shrinks what it grants. If the two authorities are incomparable, the
    ///    membrane refuses ([`TranscludeProjectError::Membrane`]).
    ///
    /// On success the viewer holds: the rendered quote (source's bytes + provenance)
    /// AND the attenuated surface capability the quote confers over the source — no
    /// more than `viewer ∧ lineage`.
    pub fn project_for(
        &self,
        rendered: &RenderedTransclusion,
        held: &AuthRequired,
        viewer: &Membrane,
        lineage: &SurfaceCapability,
    ) -> Result<ProjectedTransclusion, TranscludeProjectError> {
        // Tooth 1: the framework cap-gate. A viewer who cannot see the affordance is
        // not offered the quote at all (the affordance is absent from their surface).
        if !self.affordance.authorized_for(held) {
            return Err(TranscludeProjectError::Unauthorized {
                affordance: self.affordance.name.clone(),
                required: self.affordance.required_rights.clone(),
                held: held.clone(),
            });
        }
        // Tooth 2: the quote projection through the REAL membrane — a quote is a READ,
        // per-viewer, never amplified.
        let projected = rendered
            .field
            .project_for(viewer, lineage)
            .map_err(TranscludeProjectError::Membrane)?;
        Ok(ProjectedTransclusion {
            affordance_name: self.affordance.name.clone(),
            quoted_bytes: rendered.field.quoted_bytes().to_vec(),
            provenance: rendered.field.cite().clone(),
            surface: projected,
        })
    }

    /// **Record this transclusion into a [`Backlinks`] registry** — Nelson's two-way
    /// link, the other direction. From a resolved quote, register that `observer`
    /// (the cell that contains this affordance) transcludes the source, carrying the
    /// cited receipt + content commitment from the quote's provenance — a verifiable
    /// backlink, not a bare pointer. Idempotent on identical observations.
    pub fn record_into(
        &self,
        links: &mut Backlinks,
        observer: CellId,
        rendered: &RenderedTransclusion,
    ) {
        links.observe(observer, &rendered.field);
    }
}

// =============================================================================
// RenderedTransclusion — a resolved quote, ready to render
// =============================================================================

/// A **resolved transclusion affordance** — the verified finalized read, named by
/// the affordance that declared it.
///
/// Carries the REAL [`TranscludedField`] (the source's committed bytes + the
/// immutable provenance + the ledger-drawn origin chrome). Because it is minted only
/// by [`TranscludeAffordance::resolve`] (which runs the genuine `include` gate), its
/// existence witnesses that the quote is faithful and finalized.
#[derive(Clone, Debug)]
pub struct RenderedTransclusion {
    /// The name of the affordance this quote realizes (its identity in the surface).
    pub affordance_name: String,
    /// The verified transcluded field — the source's committed bytes + provenance +
    /// origin chrome. The REAL [`TranscludedField`], not a copy that may diverge.
    pub field: TranscludedField,
}

impl RenderedTransclusion {
    /// The quoted bytes — the source's committed content this transclusion displays.
    /// These ARE the source's bytes (content-addressed), per the primitive.
    pub fn quoted_bytes(&self) -> &[u8] {
        self.field.quoted_bytes()
    }

    /// The immutable provenance citation (source ref + content commitment + receipt +
    /// finalized) — what tooling renders as "quoted from `dregg://<cell>` at receipt
    /// R; finalized". The honest, dated provenance.
    pub fn provenance(&self) -> &Provenance {
        self.field.cite()
    }

    /// **Re-verify the provenance** — run the genuine
    /// content→commitment→receipt→root→quorum chain ([`TranscludedField::verify`]).
    /// A holder can recompute faithfulness at any time; a tampered quote REFUSES.
    pub fn verify(&self) -> Result<(), starbridge_web_surface::web_of_cells::FetchError> {
        self.field.verify()
    }
}

// =============================================================================
// ProjectedTransclusion — a quote projected for a specific viewer
// =============================================================================

/// A transclusion **projected for a specific viewer** — the per-viewer view the
/// membrane minted.
///
/// Carries the quoted bytes + provenance (the same faithful, finalized quote) AND
/// the attenuated [`SurfaceCapability`] the quote confers over the source for THIS
/// viewer (`≤ viewer ∧ lineage`). A weaker viewer's `surface` is strictly weaker —
/// the quote never amplified what they hold over the source.
#[derive(Clone, Debug)]
pub struct ProjectedTransclusion {
    /// The affordance this projection realizes.
    pub affordance_name: String,
    /// The source's committed bytes (the quote's content — same for every viewer; a
    /// quote is a faithful read).
    pub quoted_bytes: Vec<u8>,
    /// The immutable provenance citation (same for every viewer — the citation is a
    /// fact, not a per-viewer claim).
    pub provenance: Provenance,
    /// The attenuated surface capability this viewer holds over the SOURCE — the meet
    /// of the viewer's held authority and the source lineage, through the REAL
    /// membrane. Never amplified beyond either input.
    pub surface: SurfaceCapability,
}

// =============================================================================
// TranscludeProjectError — why a per-viewer projection was refused
// =============================================================================

/// Why a [`TranscludeAffordance::project_for`] was refused — either the framework
/// cap-gate did not admit the viewer (the affordance is invisible to them) or the
/// membrane refused the quote projection (incomparable authorities).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TranscludeProjectError {
    /// The viewer's held authority does NOT clear the affordance's cap-gate — the
    /// quote is not offered to them at all (the framework's REAL `is_attenuation`,
    /// `required ⊆ held`, failed). The same anti-ghost tooth a `view`/`admin` button
    /// uses.
    Unauthorized {
        /// The affordance the viewer could not see.
        affordance: String,
        /// The authority it required (which the viewer did not hold).
        required: AuthRequired,
        /// The authority the viewer actually held.
        held: AuthRequired,
    },
    /// The framework gate passed, but the membrane refused the quote projection: the
    /// viewer's held authority and the source lineage are INCOMPARABLE — there is no
    /// projection both admit ([`RehydrateError::Amplification`]). The structural
    /// no-amplification refusal.
    Membrane(RehydrateError),
}

impl std::fmt::Display for TranscludeProjectError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TranscludeProjectError::Unauthorized {
                affordance,
                required,
                held,
            } => write!(
                f,
                "transclusion `{affordance}` not visible: requires {required:?} but viewer holds {held:?}"
            ),
            TranscludeProjectError::Membrane(e) => {
                write!(
                    f,
                    "transclusion quote projection refused by membrane: {e:?}"
                )
            }
        }
    }
}

impl std::error::Error for TranscludeProjectError {}

// =============================================================================
// DeosCellTranscludeExt — declare a transclusion on a DeosCell, like any affordance
// =============================================================================

/// An extension trait letting a [`DeosCell`] declare a [`TranscludeAffordance`] the
/// same way it declares any other affordance — so a transcluded peer field sits in
/// the cell's [`AffordanceSurface`] alongside its `view`/`edit`/`admin` buttons.
///
/// The framework affordance half of the transclusion (its name + cap-gate + effect)
/// is folded into the cell's surface via the existing [`DeosCell::affordance`]; the
/// `source` ref is held by the [`TranscludeAffordance`] the caller keeps to
/// [`TranscludeAffordance::resolve`] the quote when rendering. (The surface holds the
/// declared affordance; the live quote is resolved per-render against the
/// [`WebOfCells`], because it is a verified read of CURRENT finalized state — never a
/// baked-in copy.)
pub trait DeosCellTranscludeExt {
    /// Declare a transclusion affordance on this cell — its framework affordance is
    /// added to the cell's surface (visible per-viewer like any other), and the
    /// returned [`TranscludeAffordance`] is what the caller resolves to render the
    /// embedded quote.
    fn transclude(self, t: TranscludeAffordance) -> (DeosCell, TranscludeAffordance);
}

impl DeosCellTranscludeExt for DeosCell {
    fn transclude(self, t: TranscludeAffordance) -> (DeosCell, TranscludeAffordance) {
        let cell = self.affordance(t.affordance.clone());
        (cell, t)
    }
}

/// Is `affordance_name` a transclusion affordance declared on `surface`? A small
/// helper for a renderer that walks a cell's surface and needs to know which
/// affordances carry an embedded quote (the renderer pairs the surface element with
/// its [`TranscludeAffordance`] to resolve the quote). Returns whether the surface
/// declares an affordance by that name (the transclusion's framework half).
pub fn surface_declares(surface: &AffordanceSurface, affordance_name: &str) -> bool {
    surface.get(affordance_name).is_some()
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_turn::action::{Effect, Event};

    fn cid(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    /// A real `EmitEvent` effect (the genuine turn for recording a citation) — the
    /// transclusion affordance's effect-template.
    fn cite_event(cell: CellId) -> Effect {
        Effect::EmitEvent {
            cell,
            event: Event {
                topic: [7u8; 32],
                data: vec![],
            },
        }
    }

    /// Publish a source document into a fresh web-of-cells and hand back the web +
    /// the `dregg://` ref to transclude (a genuine 3-of-3-attested finalized source —
    /// the SAME helper shape the primitive's own tests use).
    fn published_source(seed: u8, body: &[u8]) -> (WebOfCells, DreggUri) {
        let mut web = WebOfCells::new(3);
        let uri = web.publish(seed, body, "dregg://source-doc");
        (web, uri)
    }

    // (1) A CELL SHOWS A TRANSCLUDED PEER FIELD WITH PROVENANCE — the affordance,
    //     declared like any other, resolves to the source's committed bytes + the
    //     immutable citation.
    #[test]
    fn a_cell_shows_a_transcluded_peer_field_with_provenance() {
        let body = b"<h1>the quoted heading from the peer cell</h1>";
        let (web, uri) = published_source(1, body);

        // The doc cell declares a transclusion affordance ALONGSIDE its other
        // affordances, the same way it declares a `view` button.
        let doc = cid(10);
        let t = TranscludeAffordance::new(
            "peer-heading",
            AuthRequired::Signature,
            cite_event(doc),
            uri.clone(),
        );
        let (cell, t) = DeosCell::new(doc, "doc")
            .affordance(CellAffordance::new(
                "view",
                AuthRequired::Signature,
                cite_event(doc),
            ))
            .transclude(t);

        // The transclusion sits in the cell's surface beside `view` (it IS a
        // first-class affordance).
        assert!(surface_declares(cell.surface(), "peer-heading"));
        assert!(surface_declares(cell.surface(), "view"));
        assert_eq!(
            cell.surface().all_names(),
            vec!["peer-heading".to_string(), "view".to_string()]
        );

        // Resolving the affordance performs the REAL verified finalized read.
        let rendered = t.resolve(&web).expect("the transclusion resolves");

        // The displayed bytes ARE the source's committed bytes (not a copy).
        assert_eq!(rendered.quoted_bytes(), body);
        // It carries the provenance citation: the source ref + a finalized flag +
        // the content commitment (the content address of the quoted bytes).
        assert_eq!(rendered.provenance().source, uri);
        assert!(
            rendered.provenance().finalized,
            "a published+attested source is finalized"
        );
        assert_eq!(
            rendered.provenance().content_hash,
            rendered.field.resource.content_hash
        );
        // And the resolved quote re-verifies (the value EQUALS its source, recomputably).
        assert!(
            rendered.verify().is_ok(),
            "the quote's provenance chain must verify"
        );
    }

    // (2) A FORGED PROVENANCE IS REFUSED — no opened provenance ⇒ no quote. The
    //     affordance cannot render a forged or absent peer field.
    #[test]
    fn a_forged_or_absent_provenance_is_refused() {
        // (a) ABSENT: an affordance transcluding a cell that was never published does
        //     not resolve — refused at the verified fetch (no finalized read).
        let (web, _uri) = published_source(2, b"<p>real published doc</p>");
        let absent = TranscludeAffordance::new(
            "missing-peer",
            AuthRequired::Signature,
            cite_event(cid(20)),
            DreggUri::new(cid(222)), // never published
        );
        let r = absent.resolve(&web);
        assert!(
            matches!(r, Err(TransclusionError::Fetch(_))),
            "an absent source cannot be transcluded (no finalized read), got {r:?}"
        );

        // (b) FORGED: take a genuine attested resource, tamper its bytes, and confirm
        //     the verification chain catches it — a forged quote cannot be opened.
        //     (The affordance's `resolve` runs THIS same `include` gate, which
        //     verifies before handing back a RenderedTransclusion; we assert the
        //     gate's polarity on the real resource directly.)
        let (web2, uri2) = published_source(3, b"<p>genuine bytes</p>");
        let (mut resource, _chrome) = web2.fetch(&uri2).expect("genuine fetch");
        resource.content_bytes = b"<p>FORGED - different bytes</p>".to_vec();
        assert!(
            resource.verify().is_err(),
            "tampered content must fail the provenance chain — a forged quote is refused"
        );
    }

    // (3) A WEAKER VIEWER SEES IT ATTENUATED — the per-viewer projection through the
    //     REAL membrane: a quote is a READ, never amplified.
    #[test]
    fn a_weaker_viewer_sees_the_transclusion_attenuated() {
        let body = b"<h1>doc body</h1>";
        let (web, uri) = published_source(4, body);

        let doc = cid(30);
        // The affordance requires only Signature to be SEEN (the framework cap-gate);
        // the quote's SOURCE lineage is a strong (Either) authority over the source.
        let t = TranscludeAffordance::new(
            "peer-body",
            AuthRequired::Signature,
            cite_event(doc),
            uri.clone(),
        );
        let rendered = t.resolve(&web).expect("resolves");
        let lineage = SurfaceCapability::root(uri.cell, AuthRequired::Either);

        // A WEAKER viewer holds only Signature. They clear the framework cap-gate
        // (Signature ⊇ Signature) AND the membrane projects an ATTENUATED quote:
        // their surface confers only Signature over the source, never the strong Either.
        let weak_held = AuthRequired::Signature;
        let weak = Membrane::new(SurfaceCapability::root(cid(91), AuthRequired::Signature));
        let weak_proj = t
            .project_for(&rendered, &weak_held, &weak, &lineage)
            .expect("weaker viewer projects a strictly attenuated quote");
        assert_eq!(
            weak_proj.surface.window.rights,
            AuthRequired::Signature,
            "the transclusion is attenuated to the weaker viewer, never amplified"
        );
        // The quote bytes + provenance are the SAME faithful read (a quote is a
        // faithful observation — only the conferred authority attenuates).
        assert_eq!(weak_proj.quoted_bytes, body);
        assert_eq!(weak_proj.provenance.source, uri);

        // A STRONG viewer (Either) gets the full meet — the distinction is real.
        let strong_held = AuthRequired::Either;
        let strong = Membrane::new(SurfaceCapability::root(cid(92), AuthRequired::Either));
        let strong_proj = t
            .project_for(&rendered, &strong_held, &strong, &lineage)
            .expect("strong viewer projects");
        assert_eq!(strong_proj.surface.window.rights, AuthRequired::Either);
    }

    // (3b) THE FRAMEWORK CAP-GATE TOOTH — a viewer who does not clear the affordance's
    //      required rights is NOT offered the quote at all (anti-ghost: the
    //      transclusion is invisible, never rendered, for an unauthorized viewer).
    #[test]
    fn an_unauthorized_viewer_is_not_offered_the_quote() {
        let (web, uri) = published_source(5, b"<p>gated peer field</p>");
        let doc = cid(40);
        // The affordance requires `None` (root) to be seen — only a powerful holder.
        let t = TranscludeAffordance::new(
            "admin-only-peer",
            AuthRequired::None,
            cite_event(doc),
            uri.clone(),
        );
        let rendered = t
            .resolve(&web)
            .expect("resolves (resolution is the source's gate, not the viewer's)");

        // A viewer holding only Signature does NOT clear the affordance's `None`
        // (root) requirement — the quote is not offered to them (the framework
        // cap-gate, the REAL is_attenuation).
        let weak_held = AuthRequired::Signature;
        let viewer = Membrane::new(SurfaceCapability::root(cid(93), AuthRequired::Signature));
        let lineage = SurfaceCapability::root(uri.cell, AuthRequired::None);
        match t.project_for(&rendered, &weak_held, &viewer, &lineage) {
            Err(TranscludeProjectError::Unauthorized { affordance, .. }) => {
                assert_eq!(affordance, "admin-only-peer");
            }
            other => panic!("expected an Unauthorized (cap-gate) refusal, got {other:?}"),
        }
        // The affordance's own gate agrees, both polarities (it IS is_attenuation):
        assert!(!t.authorized_for(&AuthRequired::Signature));
        assert!(t.authorized_for(&AuthRequired::None));
    }

    // (4) THE BACKLINKS — a cell's transclusion contributes a verifiable backlink
    //     ("who quotes the source"), Nelson's two-way link the other direction.
    #[test]
    fn a_cell_transclusion_records_a_verifiable_backlink() {
        let (web, uri) = published_source(6, b"<h1>widely-quoted source</h1>");
        let doc = cid(50);
        let t = TranscludeAffordance::new(
            "peer",
            AuthRequired::Signature,
            cite_event(doc),
            uri.clone(),
        );
        let rendered = t.resolve(&web).expect("resolves");

        let mut links = Backlinks::new();
        // The doc cell (the observer) transcludes the source — record the backlink.
        t.record_into(&mut links, doc, &rendered);
        // Idempotent: recording the same observation again does not double-count.
        t.record_into(&mut links, doc, &rendered);

        let observers = links.observers_of(uri.cell);
        assert_eq!(observers.len(), 1, "exactly one observer (idempotent)");
        assert_eq!(
            observers[0].observer, doc,
            "the doc cell is the backlink observer"
        );
        // The backlink cites the receipt + content commitment from the quote's
        // provenance — a verifiable fact, not a bare pointer.
        assert_eq!(
            observers[0].receipt_hash,
            rendered.provenance().receipt_hash
        );
        assert_eq!(
            observers[0].content_hash,
            rendered.provenance().content_hash
        );
        assert_eq!(links.backlink_count(uri.cell), 1);
    }
}
