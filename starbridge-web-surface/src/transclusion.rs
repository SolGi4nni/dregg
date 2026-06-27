//! Transclusion — Ted Nelson's Xanadu docuverse, made HONEST on the verified
//! substrate (the Rust mirror of `Dregg2.Deos.Transclusion`).
//!
//! Nelson's Xanadu promised **transclusion**: include-by-reference where the quoted
//! material keeps its identity and provenance — the same bytes, the same source,
//! visibly cited, never copied-and-cut — joined by **two-way links** that cannot
//! break. Xanadu could never make it honest, because in an ambient-authority world
//! a "transcluded" quote is just a copy: nothing forces it to equal the source,
//! nothing stops it rotting when the source moves, nothing bounds what authority the
//! quote confers, and the "back-link" to the source was a hand-maintained index, not
//! a fact. dregg already ships the missing piece — **the verified cross-cell
//! finalized read** (the `dregg://` attested fetch in [`crate::web_of_cells`], whose
//! Lean is `Dregg2.Authority.CrossCellImport` / its binding
//! `Authority.ImportBinding.ImportedEq`): the bytes are content-addressed AND carry a
//! receipt + a quorum-signed [`AttestedRoot`], so a quote IS the value the source
//! committed at a cited, immutable receipt. This module NAMES that as transclusion
//! and surfaces the four Xanadu properties the Lean proves:
//!
//! 1. **A transclusion IS a verified observation** — [`TranscludedField::include`]
//!    performs the REAL `dregg://` finalized read ([`WebOfCells::fetch`]) and pins
//!    the quoted field; the displayed value is the source's committed value
//!    (`transclusion_is_observed_finalized_read`).
//! 2. **Provenance faithful / a forge cannot be cited** —
//!    [`TranscludedField::verify`] runs the genuine content→commitment→receipt→
//!    receipt-stream-root→quorum chain ([`AttestedResource::verify`]); a forged or
//!    absent provenance is REFUSED (`transclusion_provenance_faithful` +
//!    `transclusion_forge_refused`). No opened provenance ⇒ no quote.
//! 3. **No amplification — a quote is a READ, per-viewer** —
//!    [`TranscludedField::project_for`] projects through the REAL [`Membrane`]; a
//!    weaker viewer sees the transclusion attenuated, and the projection cannot
//!    amplify (`transclusion_no_amplify`, the membrane non-amp).
//! 4. **The UNBREAKABLE BIDIRECTIONAL LINK** — the citation pins an immutable
//!    receipt, so the quote never rots (`transclusion_stable_under_source_advance`,
//!    the I-confluence crown), and [`Backlinks`] renders the *other* direction Nelson
//!    wanted: the witness-graph as "who transcludes / observes me" — the receipt
//!    chain + observation records ARE the two-way structure, finally honest.
//!
//! Everything here drives the REAL cap + attestation primitives: the `dregg://`
//! attested fetch, [`AttestedResource::verify`], and [`Membrane::project`]. No
//! parallel attestation, no parallel cap model. The Lean is the spec; this is the
//! named realization.
//!
//! ### Consumers (named fast-follows, NOT built here)
//!
//! - **The leptos reactive-transclusion** — a Leptos signal that reactively reflects
//!   a transcluded field (the "live quote": when the source finalizes a new height,
//!   the signal re-fetches and the view updates). Rides this module's
//!   [`TranscludedField::include`] + the `Rehydration` liveness-type.
//! - **The deos-app-framework transclusion affordance** — a [`CellAffordance`] whose
//!   render embeds a [`TranscludedField`], so an app declares a quote the way it
//!   declares any other affordance, projected per-viewer through the same membrane.

use std::collections::BTreeMap;

use crate::affordance::CellAffordance;
use crate::delegate::SurfaceCapability;
use crate::rehydrate::{Membrane, RehydrateError};
use crate::web_of_cells::{AttestedResource, DreggUri, FetchError, OriginChrome, WebOfCells};
use dregg_cell::CellId;

/// The provenance a transclusion carries — the cited, immutable source citation.
///
/// This is the "imported at receipt R, height H" record the Lean `Import` carries
/// (`{ source_cell, source_field, value, provenance: receipt }`), realized over the
/// crate's attested-fetch envelope. It is drawn from the verified fetch, never from
/// the displayed content: the `source` ref + the receipt-stream Merkle leaf + the
/// quorum-signed root are exactly what makes the quote recomputable by a verifier
/// and datable by tooling (a stale quote is *visible*, never a silent live read).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Provenance {
    /// The source `dregg://<cell>` reference the value was quoted FROM.
    pub source: DreggUri,
    /// The content commitment the source cell finalized (`blake3` of the bytes the
    /// quote includes) — the value's content address.
    pub content_hash: [u8; 32],
    /// The receipt Merkle leaf binding the serve (the cited receipt — the immutable
    /// past the citation is pinned to; the Lean `Import.provenance`).
    pub receipt_hash: [u8; 32],
    /// Whether the source's attestation carried quorum at the cited point — the
    /// "finalized" flag (the Lean `importValid` well-linkedness, structurally: only a
    /// quorum-attested, receipt-complete root is a faithful finalized read).
    pub finalized: bool,
}

/// A transcluded field — Xanadu's quote made literal: a first-class provenanced
/// inclusion of a peer cell's finalized field.
///
/// It carries the verified [`AttestedResource`] the `dregg://` fetch returned (the
/// finalized read), the [`Provenance`] citation drawn from it, the ledger-drawn
/// [`OriginChrome`] (the trusted-path badge — never the page's own claim), and the
/// quoted byte range within the resource. The displayed bytes ARE the source's
/// committed bytes; a verifier recomputes them; the citation dates them. This is the
/// Lean `Transclusion` (= `ImportedEq`), realized.
#[derive(Clone, Debug)]
pub struct TranscludedField {
    /// The verified attested content the source committed (the finalized read result).
    pub resource: AttestedResource,
    /// The immutable citation (source ref + receipt + content commitment + finalized).
    pub provenance: Provenance,
    /// The ledger-drawn origin badge (trusted path — from the cell's lineage, not the
    /// fetched content; dregg's structural answer to chrome phishing).
    pub chrome: OriginChrome,
}

/// What can go wrong building a transclusion — either the `dregg://` finalized read
/// failed to resolve, or its provenance did not verify (a forged/absent quote).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TransclusionError {
    /// The source `dregg://` ref did not resolve to a finalized read.
    Fetch(FetchError),
    /// The fetched content's provenance did not verify against the committed root —
    /// a FORGED or ABSENT provenance. No opened provenance ⇒ no quote.
    ProvenanceUnverified(FetchError),
    /// The source was finalized, but did not carry quorum — an un-finalized read is
    /// not a faithful transclusion (a transclusion quotes FINALIZED state).
    NotFinalized,
}

impl TranscludedField {
    /// **Include a peer cell's finalized field by reference** — the definitional
    /// bridge (`transclusion_is_observed_finalized_read`): a transclusion IS a
    /// verified cross-cell finalized read.
    ///
    /// Performs the REAL `dregg://` attested fetch against `web`, VERIFIES the
    /// provenance (content → commitment → receipt → receipt-stream root → quorum),
    /// and pins the cited value. Refuses (`ProvenanceUnverified`) if the provenance
    /// does not verify — a forged or absent quote cannot be opened — and refuses
    /// (`NotFinalized`) if the read is not quorum-finalized. On success the field's
    /// displayed bytes ARE the source's committed bytes, with the citation that dates
    /// them.
    pub fn include(
        web: &WebOfCells,
        source: &DreggUri,
    ) -> Result<TranscludedField, TransclusionError> {
        // (1) THE FINALIZED READ — the real verified cross-cell observation.
        let (resource, chrome) = web.fetch(source).map_err(TransclusionError::Fetch)?;
        // (2) PROVENANCE FAITHFUL — run the genuine verification chain. A forged or
        //     absent provenance fails here; no opened provenance ⇒ reject.
        resource
            .verify()
            .map_err(TransclusionError::ProvenanceUnverified)?;
        // (3) FINALIZED — a transclusion quotes FINALIZED state; a non-quorum read is
        //     not a faithful quote (the Lean importValid well-linkedness, structurally).
        if !chrome.finalized {
            return Err(TransclusionError::NotFinalized);
        }
        let provenance = Provenance {
            source: source.clone(),
            content_hash: resource.content_hash,
            receipt_hash: resource.receipt_hash,
            finalized: chrome.finalized,
        };
        Ok(TranscludedField {
            resource,
            provenance,
            chrome,
        })
    }

    /// **The quoted bytes** — the source's committed content the transclusion
    /// displays. These ARE the source's bytes (content-addressed: `content_hash ==
    /// blake3(bytes)`), not a copy that may diverge.
    pub fn quoted_bytes(&self) -> &[u8] {
        &self.resource.content_bytes
    }

    /// **Re-verify the provenance** (`transclusion_provenance_faithful` — the quoted
    /// value EQUALS its source). Runs the genuine content→commitment→receipt→
    /// receipt-stream-root→quorum chain; a transclusion whose bytes were tampered, or
    /// whose receipt is not in the committed stream, REFUSES. Idempotent with
    /// [`Self::include`]'s check — a holder can recompute faithfulness at any time.
    pub fn verify(&self) -> Result<(), FetchError> {
        self.resource.verify()
    }

    /// **Project the transclusion PER-VIEWER through the membrane**
    /// (`transclusion_no_amplify` — a quote is a READ, not a key).
    ///
    /// A transclusion confers no authority over the source beyond observing the cited
    /// value. The `viewer` membrane meets its held authority with the source's
    /// `lineage` through the REAL [`Membrane::project`] (`is_attenuation` on window
    /// rights, set-intersection on the web caveats). A weaker viewer receives a
    /// strictly attenuated surface; the projection CANNOT amplify — re-sharing the
    /// quote down a delegation chain only ever shrinks what it grants.
    pub fn project_for(
        &self,
        viewer: &Membrane,
        lineage: &SurfaceCapability,
    ) -> Result<SurfaceCapability, RehydrateError> {
        viewer.project(lineage)
    }

    /// The immutable citation this transclusion carries (the source ref + receipt +
    /// content commitment + finalized flag) — what tooling renders as "quoted from
    /// `dregg://<cell>` at receipt R; finalized". The honest, dated provenance.
    pub fn cite(&self) -> &Provenance {
        &self.provenance
    }
}

/// **The deos-app transclusion affordance** (a named fast-follow seam, minimal here):
/// declare a transclusion the way an app declares any other affordance — a
/// [`CellAffordance`] whose render embeds the quote, projected per-viewer through the
/// same membrane. This helper names the source cell an affordance transcludes so the
/// app framework can wire the embed; the heavy Leptos render is the consumer.
#[derive(Clone, Debug)]
pub struct TransclusionAffordance {
    /// The affordance the app declares (its cap-gate + effect-template).
    pub affordance: CellAffordance,
    /// The source `dregg://` ref whose finalized field this affordance transcludes.
    pub source: DreggUri,
}

impl TransclusionAffordance {
    /// Pair an app affordance with the source it transcludes.
    pub fn new(affordance: CellAffordance, source: DreggUri) -> Self {
        TransclusionAffordance { affordance, source }
    }

    /// Resolve the embedded quote by performing the finalized read (the same verified
    /// observation [`TranscludedField::include`] runs).
    pub fn resolve(&self, web: &WebOfCells) -> Result<TranscludedField, TransclusionError> {
        TranscludedField::include(web, &self.source)
    }
}

/// One backlink record — an observer that transcludes (or otherwise observes) a
/// source cell, with the cited receipt it observed at.
///
/// This is the *other half* of Nelson's two-way link: where a forward link says
/// "this quote points at cell X", a backlink says "cell X is quoted by observer O at
/// receipt R". In Xanadu the back-link was a hand-maintained index that could drift;
/// here it is a fact derived from the same receipts/observations the forward
/// transclusion carries — the witness-graph, rendered the other way.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Observer {
    /// The cell doing the observing (the document that contains the transclusion).
    pub observer: CellId,
    /// The receipt the observation was pinned to (the cited immutable past).
    pub receipt_hash: [u8; 32],
    /// The source content commitment that was observed (what value was quoted).
    pub content_hash: [u8; 32],
}

/// **Backlinks** — Ted Nelson's two-way link, finally honest: the witness-graph
/// rendered as "who transcludes / observes me".
///
/// A registry keyed by SOURCE cell: for each source, the observers that transclude
/// it. The forward direction (a [`TranscludedField`] citing a source) is the
/// attested fetch; this is the *reverse* index, populated as observations are
/// recorded. Because each record carries the cited receipt + content commitment, the
/// back-link is a verifiable claim ("observer O quoted source S's value V at receipt
/// R"), not a hand-maintained pointer that can dangle — the receipt chain + the
/// observation records ARE the bidirectional structure the docuverse always needed.
#[derive(Clone, Debug, Default)]
pub struct Backlinks {
    /// source cell → the observers transcluding it (insertion-ordered per source).
    by_source: BTreeMap<CellId, Vec<Observer>>,
}

impl Backlinks {
    /// An empty witness-graph readout.
    pub fn new() -> Self {
        Backlinks {
            by_source: BTreeMap::new(),
        }
    }

    /// **Record that `observer` transcludes the source named by `field`** — populate
    /// the reverse index from a verified transclusion. The cited receipt + content
    /// commitment are carried from the transclusion's provenance, so the backlink is a
    /// verifiable fact, not a bare pointer. (Idempotent on identical records: the same
    /// observer at the same receipt + commitment is not double-counted.)
    pub fn observe(&mut self, observer: CellId, field: &TranscludedField) {
        let source = field.provenance.source.cell;
        let record = Observer {
            observer,
            receipt_hash: field.provenance.receipt_hash,
            content_hash: field.provenance.content_hash,
        };
        let entry = self.by_source.entry(source).or_default();
        if !entry.contains(&record) {
            entry.push(record);
        }
    }

    /// **Who transcludes / observes me?** — enumerate the observers of a source cell
    /// (the backlink readout). The reverse of "what does this quote point at": "what
    /// points at this cell". Empty if no recorded observer transcludes it.
    pub fn observers_of(&self, source: CellId) -> &[Observer] {
        self.by_source
            .get(&source)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    /// How many distinct observers transclude the source — the in-degree of a cell in
    /// the docuverse witness-graph (a measure of how widely a value is quoted).
    pub fn backlink_count(&self, source: CellId) -> usize {
        self.observers_of(source).len()
    }

    /// Every source cell that has at least one recorded observer (the nodes that are
    /// quoted somewhere) — sorted by cell.
    pub fn observed_sources(&self) -> Vec<CellId> {
        self.by_source.keys().copied().collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::delegate::SurfaceCapability;
    use crate::rehydrate::Membrane;
    use dregg_cell::AuthRequired;

    fn cid(b: u8) -> CellId {
        let mut bytes = [0u8; 32];
        bytes[0] = b;
        CellId::from_bytes(bytes)
    }

    /// Publish a source document into a fresh web-of-cells and hand back the web +
    /// the `dregg://` ref to transclude. The publish writes the content commitment
    /// into the origin cell's real state (slot 0) and attests it with a 3-of-3
    /// quorum — a genuine finalized read source.
    fn published_source(seed: u8, body: &[u8]) -> (WebOfCells, DreggUri) {
        let mut web = WebOfCells::new(3);
        let uri = web.publish(seed, body, "dregg://source-doc");
        (web, uri)
    }

    // (1) THE BRIDGE — a transclusion IS the verified finalized read: it shows the
    //     source's committed bytes + carries its provenance.
    #[test]
    fn transclusion_shows_source_value_and_provenance() {
        let body = b"<h1>the quoted heading</h1>";
        let (web, uri) = published_source(1, body);

        let quote = TranscludedField::include(&web, &uri).expect("transclusion resolves");

        // the displayed bytes ARE the source's committed bytes (not a copy):
        assert_eq!(quote.quoted_bytes(), body);
        // it carries the provenance citation: the source ref + a finalized flag:
        assert_eq!(quote.cite().source, uri);
        assert!(
            quote.cite().finalized,
            "a published+attested source is finalized"
        );
        // and the content commitment is the content address of the quoted bytes:
        assert_eq!(quote.cite().content_hash, quote.resource.content_hash);
    }

    // (2) PROVENANCE FAITHFUL — the resolved transclusion re-verifies (the quoted
    //     value equals its source, recomputably).
    #[test]
    fn transclusion_provenance_verifies() {
        let (web, uri) = published_source(2, b"<p>provenanced</p>");
        let quote = TranscludedField::include(&web, &uri).expect("resolves");
        assert!(
            quote.verify().is_ok(),
            "the quote's content→commitment→receipt→root→quorum chain must verify"
        );
    }

    // (2b) A FORGED / ABSENT PROVENANCE IS REFUSED — no opened provenance ⇒ no quote.
    #[test]
    fn forged_or_absent_provenance_is_refused() {
        let (web, _uri) = published_source(3, b"<p>real</p>");

        // (a) ABSENT: a dregg:// ref to a cell that was never published does not
        //     resolve to a finalized read — the quote is refused at the fetch.
        let absent = DreggUri::new(cid(200));
        let r = TranscludedField::include(&web, &absent);
        assert!(
            matches!(r, Err(TransclusionError::Fetch(_))),
            "an absent source cannot be transcluded (no finalized read), got {r:?}"
        );

        // (b) FORGED: take a genuine attested resource and tamper its bytes. The
        //     content no longer matches the committed hash, so verify() refuses —
        //     a forged quote cannot be opened.
        let (web2, uri2) = published_source(4, b"<p>genuine</p>");
        let (mut resource, chrome) = web2.fetch(&uri2).expect("genuine fetch");
        resource.content_bytes = b"<p>FORGED - different bytes</p>".to_vec();
        // The verification chain catches the tamper:
        assert!(
            resource.verify().is_err(),
            "tampered content must fail the provenance chain"
        );
        // …and so a TranscludedField built around it would not have passed include's
        // verify gate (we assert the gate's polarity directly):
        let _ = chrome; // chrome is ledger-drawn (trusted path), unaffected by the forge
    }

    // (3) NO AMPLIFY — a weaker viewer sees the transclusion ATTENUATED; the
    //     projection cannot amplify (a quote is a read, per-viewer).
    #[test]
    fn weaker_viewer_sees_transclusion_attenuated() {
        let (web, uri) = published_source(5, b"<h1>doc</h1>");
        let quote = TranscludedField::include(&web, &uri).expect("resolves");

        // The source lineage: a strong (Either) authority over the doc cell.
        let lineage = SurfaceCapability::root(uri.cell, AuthRequired::Either);

        // A WEAKER viewer holds only Signature authority. is_attenuation(Either,
        // Signature) holds, so the projection succeeds but is attenuated to the
        // viewer's ceiling.
        let weak = Membrane::new(SurfaceCapability::root(cid(51), AuthRequired::Signature));
        let projected = quote
            .project_for(&weak, &lineage)
            .expect("weaker viewer projects (a strictly attenuated view)");

        // The projected surface confers no MORE than the weaker viewer held — its
        // window rights are the viewer's, not the strong lineage's. The quote did not
        // hand the weak viewer the strong authority.
        assert_eq!(
            projected.window.rights,
            AuthRequired::Signature,
            "the transclusion is attenuated to the weaker viewer, never amplified"
        );

        // A STRONG viewer (Either) gets the full meet — the distinction is real.
        let strong = Membrane::new(SurfaceCapability::root(cid(52), AuthRequired::Either));
        let projected_strong = quote
            .project_for(&strong, &lineage)
            .expect("strong viewer projects");
        assert_eq!(projected_strong.window.rights, AuthRequired::Either);
    }

    // (4) THE BACKLINKS — the witness-graph rendered as "who transcludes me": the
    //     backlinks enumerate the observers (Nelson's two-way link).
    #[test]
    fn backlinks_enumerate_observers() {
        let (web, uri) = published_source(6, b"<h1>widely-quoted source</h1>");
        let quote = TranscludedField::include(&web, &uri).expect("resolves");

        let mut links = Backlinks::new();
        // Three observer documents transclude the same source:
        let obs_a = cid(101);
        let obs_b = cid(102);
        let obs_c = cid(103);
        links.observe(obs_a, &quote);
        links.observe(obs_b, &quote);
        links.observe(obs_c, &quote);
        // …and obs_a quoting it again at the same receipt is idempotent (not
        // double-counted):
        links.observe(obs_a, &quote);

        // "Who observes me?" — exactly the three observers, each carrying the cited
        // receipt + content commitment (a verifiable backlink, not a bare pointer):
        let observers = links.observers_of(uri.cell);
        assert_eq!(
            observers.len(),
            3,
            "three distinct observers transclude the source"
        );
        let names: Vec<CellId> = observers.iter().map(|o| o.observer).collect();
        assert!(names.contains(&obs_a) && names.contains(&obs_b) && names.contains(&obs_c));
        // each backlink cites the receipt the observation was pinned to:
        assert!(observers
            .iter()
            .all(|o| o.receipt_hash == quote.provenance.receipt_hash));
        assert_eq!(links.backlink_count(uri.cell), 3);

        // a source nobody quotes has no backlinks (empty readout, not an error):
        assert!(links.observers_of(cid(199)).is_empty());
        // the observed-sources index lists exactly the quoted cell:
        assert_eq!(links.observed_sources(), vec![uri.cell]);
    }
}
