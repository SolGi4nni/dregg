//! `dregg://` LINK-PASTE — Xanadu links, made usable (hyperdreggmedia authoring
//! surface #5, `docs/deos/HYPERDREGGMEDIA-NOTES.md §6`).
//!
//! The other Nelson surfaces in this crate ([`crate::web_cells`],
//! [`crate::cell_transclusion`], [`crate::links_here`]) BUILD the docuverse — the
//! addressing, the verified per-viewer transclusion, the two-way witness-graph. This
//! one makes the *authoring gesture* usable: **select a cell → copy a `dregg://` URI →
//! PASTE a live provenanced transclusion into a document.** On the open web a paste is
//! a dead copy (or a brittle `<iframe src=…>` that trusts whatever bytes the host
//! returns); here a paste is a REAL verified embed — receipt-pinned, per-viewer,
//! darkening for an unauthorized reader, and *unforgeable* (a bad/forged URI resolves
//! to NOTHING, never a faked inclusion).
//!
//! ## Everything here is the REAL machinery, never a parallel model
//!
//! - The URI is the genuine [`web_aff::DreggUri`] scheme `web_cells` already speaks:
//!   [`uri_for`] is `DreggUri::new(cell).to_uri_string()` (the content-addressed
//!   `dregg://<hex>` cell id — the address IS the access grant and the identity), and
//!   [`parse_uri`] round-trips it back to a [`CellRef`]. A copy then a paste of the
//!   SAME cell is the same `dregg://` page the browser lists.
//! - The PASTE is a real [`WholeCellTransclusion::embed`] ([`crate::cell_transclusion`])
//!   — the verified `dregg://` finalized read of the source cell's surface root
//!   (content → commitment → receipt → receipt-stream root → quorum). A forged or
//!   absent or non-finalized URI fails HERE: no opened provenance ⇒ NO embed (the
//!   anti-forge tooth, inherited verbatim from [`TranscludedField::include`]).
//! - The per-viewer DARKENING is the real [`WholeCellTransclusion::project_for`]
//!   through the genuine [`web_aff::Membrane`]: an authorized reader gets the embed at
//!   their cap level (content + affordances + the cited receipt); an under-capped /
//!   incomparable reader gets a DARKENED paste — the citation (provenance) survives,
//!   the content is withheld (never forged, never substituted).
//!
//! ## What this IS and is NOT
//!
//! It is a gpui-free, `cargo test`-able **logic core** (like `web_cells.rs` /
//! `cell_transclusion.rs`): a [`LinkPasteDoc`] accumulates [`Paste`]s, each a real
//! [`WholeCellTransclusion`] resolved per-viewer to a [`ResolveStatus`]
//! (Resolved / Darkened / Unresolvable + the cited receipt). The cockpit renders these
//! rows; because they are built here gpui-free, a `cargo test` proves a paste is a real
//! verified embed without a GPU.
//!
//! It is NOT a new circuit constraint or a new attestation: the soundness is the
//! EXISTING `WholeCellTransclusion` provenance + `Membrane` non-amp. It reinvents
//! nothing — it composes the proven embed with the proven URI scheme into the one
//! gesture authoring needs.

use starbridge_web_surface as web_aff;
use web_aff::affordance::AffordanceSurface;
use web_aff::delegate::SurfaceCapability;
use web_aff::rehydrate::Membrane;
use web_aff::transclusion::Provenance;
use web_aff::web_of_cells::{DreggUri, WebOfCells};
use web_aff::CellId;

use crate::cell_transclusion::{
    EmbedVisibility, EmbeddedCellView, WholeCellTransclusion, WholeCellTransclusionError,
};
use crate::reflect;
use dregg_cell::{Credential, Requirement};

/// A parsed `dregg://<cell>` reference — the round-trip target of [`uri_for`] /
/// [`parse_uri`]. A thin newtype over the cell the URI denotes (the content-addressed
/// origin), so a copied address is a checkable handle, not a bare string.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CellRef {
    /// The origin cell the `dregg://` URI denotes (already unforgeable: the address IS
    /// the content-addressed cell id).
    pub cell: CellId,
}

impl CellRef {
    /// The [`DreggUri`] this ref denotes — the genuine `web_cells` addressing object
    /// (so `uri_for`/`parse_uri` ride the SAME scheme the browser lists, never a
    /// parallel one).
    pub fn uri(&self) -> DreggUri {
        DreggUri::new(self.cell)
    }
}

/// **The `dregg://` URI for a cell** — what the "copy link" gesture yields.
///
/// This is exactly the address `web_cells` puts in the browser's address bar:
/// `DreggUri::new(cell).to_uri_string()` = `dregg://` + the 64-hex content-addressed
/// cell id. Selecting a cell and copying its link produces this; pasting it (below)
/// resolves it back to a real verified embed.
pub fn uri_for(cell: CellId) -> String {
    DreggUri::new(cell).to_uri_string()
}

/// **Parse a `dregg://<hex>` URI back to a [`CellRef`]** — the round-trip of
/// [`uri_for`].
///
/// Accepts exactly the `web_cells` scheme: the literal `dregg://` prefix followed by
/// 64 lowercase hex characters (the 32-byte content-addressed cell id). Returns `None`
/// for anything else — a wrong prefix, a wrong length, or non-hex — so a malformed
/// paste cannot masquerade as a cell ref (it becomes [`ResolveStatus::Unresolvable`]
/// downstream, never a faked inclusion).
pub fn parse_uri(uri: &str) -> Option<CellRef> {
    let hex = uri.strip_prefix("dregg://")?;
    if hex.len() != 64 {
        return None;
    }
    let mut id = [0u8; 32];
    for (i, byte) in id.iter_mut().enumerate() {
        let pair = hex.get(i * 2..i * 2 + 2)?;
        *byte = u8::from_str_radix(pair, 16).ok()?;
    }
    Some(CellRef { cell: CellId(id) })
}

/// The resolve-status of a [`Paste`] — what the document shows for one pasted
/// `dregg://` link, per-viewer. The cockpit styles on this discriminant; every variant
/// carries the cited receipt when there is one to cite (an honest, dated provenance).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResolveStatus {
    /// The viewer's caps reach the embed: a real provenanced transclusion renders — the
    /// source's content (its per-viewer affordance set) PLUS the cited receipt. The
    /// honest live embed.
    Resolved {
        /// The cited receipt-stream leaf (short-hex) the embed is pinned to — the
        /// immutable past the citation dates.
        receipt: String,
        /// The source's content commitment (short-hex) the embed quotes — the value's
        /// content address.
        commitment: String,
        /// How many affordances of the embedded cell this viewer's caps clear (the
        /// per-viewer content readout).
        visible_affordances: usize,
        /// How many affordances the embedded cell DECLARES in total, so a surface can
        /// say "you see N of M — the rest are attenuated away by your caps" rather than
        /// a bare count whose denominator the reader has to guess. Read straight off
        /// [`EmbeddedCellView::declared_affordance_count`].
        declared_affordances: usize,
    },
    /// The embed resolved + verified, but THIS viewer's authority cannot reach it — the
    /// paste DARKENS: the citation (provenance) survives, the content is withheld
    /// (never forged, never substituted). The Xanadu link still points, honestly.
    Darkened {
        /// The cited receipt-stream leaf (short-hex) — the citation survives darkening.
        receipt: String,
        /// The source's content commitment (short-hex) — the reader always knows WHAT
        /// cell is pasted and that it is genuinely cited.
        commitment: String,
    },
    /// The URI did not resolve to a verified finalized embed (a dead, forged, or
    /// un-finalized link). NO embed is produced — the anti-forge tooth: an unresolvable
    /// paste yields nothing, never a faked inclusion.
    Unresolvable {
        /// Why the resolve failed (the genuine [`WholeCellTransclusionError`] reason),
        /// so the document shows an honest "dregg: unresolvable link" rather than a
        /// blank or a forgery.
        reason: String,
    },
}

impl ResolveStatus {
    /// The one-word badge the cockpit shows for this status.
    pub fn badge(&self) -> &'static str {
        match self {
            ResolveStatus::Resolved { .. } => "resolved",
            ResolveStatus::Darkened { .. } => "darkened",
            ResolveStatus::Unresolvable { .. } => "unresolvable",
        }
    }

    /// The cited receipt (short-hex) this status pins to, if any. Present for both
    /// Resolved and Darkened (the citation survives darkening); `None` only for an
    /// Unresolvable link (there is nothing genuine to cite).
    pub fn receipt(&self) -> Option<&str> {
        match self {
            ResolveStatus::Resolved { receipt, .. } | ResolveStatus::Darkened { receipt, .. } => {
                Some(receipt)
            }
            ResolveStatus::Unresolvable { .. } => None,
        }
    }

    /// Did the paste render a real provenanced embed for this viewer (content present)?
    pub fn is_resolved(&self) -> bool {
        matches!(self, ResolveStatus::Resolved { .. })
    }
}

/// One **pasted `dregg://` link** in a document — a real verified transclusion, plus
/// the source ref the paste cites. The whole point: a paste is not a copy but a
/// receipt-pinned, per-viewer embed.
#[derive(Clone, Debug)]
pub struct Paste {
    /// The source `dregg://<cell>` the paste cites (the EEL anchor — "jump to source").
    pub source_uri: String,
    /// The host document cell the paste was inserted INTO.
    pub host: CellId,
    /// The per-viewer resolution of the paste — Resolved / Darkened / Unresolvable.
    pub status: ResolveStatus,
    /// The immutable provenance the paste carries (the cited surface commitment +
    /// receipt + finalized flag), if the URI resolved at all. ALWAYS present for a
    /// Resolved or Darkened paste (the citation survives darkening); `None` for an
    /// Unresolvable link.
    pub provenance: Option<Provenance>,
}

impl Paste {
    /// A one-line readout of the paste (for the panel + tests): the source, the badge,
    /// and the cited receipt if there is one.
    pub fn line(&self) -> String {
        match self.status.receipt() {
            Some(receipt) => format!(
                "[{}] {} · receipt {}",
                self.status.badge(),
                self.source_uri,
                receipt
            ),
            None => format!("[{}] {} · (no embed)", self.status.badge(), self.source_uri),
        }
    }

    /// The cited receipt of this paste (short-hex), if any — `resolve_status`'s
    /// receipt readout, lifted to the paste.
    pub fn cited_receipt(&self) -> Option<&str> {
        self.status.receipt()
    }
}

/// **The resolve-status of a paste** — Resolved / Darkened / Unresolvable plus the
/// cited receipt, as the cockpit renders it. A thin accessor (the status is computed at
/// [`LinkPasteDoc::paste`] time, against the viewer the document is being read by), so
/// the panel reads exactly what the paste resolved to.
pub fn resolve_status(paste: &Paste) -> &ResolveStatus {
    &paste.status
}

/// A document the user pastes `dregg://` links INTO — the link-paste authoring surface.
///
/// It owns the host cell, the per-viewer [`Membrane`] the pastes are resolved through,
/// and the accumulated [`Paste`]s. Each [`Self::paste`] resolves a URI against the live
/// [`WebOfCells`] into a real verified embed and records its per-viewer status; the
/// cockpit renders the resulting rows.
#[derive(Clone, Debug)]
pub struct LinkPasteDoc {
    /// The host document cell (the page the pastes are inserted into).
    pub host: CellId,
    /// The accumulated pasted links, in document order.
    pub pastes: Vec<Paste>,
}

impl LinkPasteDoc {
    /// A fresh link-paste document over `host` with no pastes.
    pub fn new(host: CellId) -> Self {
        LinkPasteDoc {
            host,
            pastes: Vec::new(),
        }
    }

    /// **Paste a `dregg://` URI into the document** — the core gesture.
    ///
    /// Resolves `uri` (1) by parsing it to a [`CellRef`] (a malformed string is
    /// Unresolvable immediately — it cannot masquerade as a cell), (2) by embedding the
    /// source cell's whole surface via the REAL [`WholeCellTransclusion::embed`] (the
    /// verified `dregg://` finalized read — a forged/absent/un-finalized URI fails
    /// here, NO embed), and (3) by projecting that embed PER-VIEWER through the
    /// `viewer` membrane: an authorized reader gets a Resolved paste (content + cited
    /// receipt), an under-capped reader gets a Darkened paste (citation kept, content
    /// withheld). Records the paste and returns a reference to it.
    ///
    /// `declared_surface` is the source cell's published affordance set (re-derived at
    /// the source in the welded substrate); `lineage` is the surface authority the
    /// embed is a certified projection of (the per-viewer ceiling the membrane meets).
    pub fn paste(
        &mut self,
        web: &WebOfCells,
        uri: &str,
        viewer: &Membrane,
        declared_surface: AffordanceSurface,
        lineage: SurfaceCapability,
    ) -> &Paste {
        let host = self.host;
        let paste = resolve_paste(web, host, uri, viewer, declared_surface, lineage);
        self.pastes.push(paste);
        self.pastes.last().expect("just pushed a paste")
    }

    /// Every line of real text the document renders, flattened — used by tests/panels
    /// to assert the surface speaks real, cited, per-viewer paste text (non-empty here
    /// == non-empty rendered tree).
    pub fn all_text(&self) -> Vec<String> {
        let mut out = Vec::new();
        out.push(format!(
            "link-paste document {} — {} pasted dregg:// link(s)",
            reflect::short_hex(&self.host.0),
            self.pastes.len()
        ));
        for p in &self.pastes {
            out.push(p.line());
        }
        out
    }
}

/// Resolve ONE `dregg://` URI into a per-viewer [`Paste`] — the pure core
/// [`LinkPasteDoc::paste`] drives. Parses, embeds (the verified finalized read), and
/// projects per-viewer, mapping each outcome to a [`ResolveStatus`]. Pure + gpui-free.
fn resolve_paste(
    web: &WebOfCells,
    host: CellId,
    uri: &str,
    viewer: &Membrane,
    declared_surface: AffordanceSurface,
    lineage: SurfaceCapability,
) -> Paste {
    // (0) A malformed string is Unresolvable BEFORE any fetch — it cannot masquerade as
    //     a cell ref (no faked inclusion from a bad paste).
    let Some(cref) = parse_uri(uri) else {
        return Paste {
            source_uri: uri.to_string(),
            host,
            status: ResolveStatus::Unresolvable {
                reason: "not a dregg:// URI (bad prefix / length / hex)".to_string(),
            },
            provenance: None,
        };
    };
    let source_uri = cref.uri();

    // (1) THE VERIFIED FINALIZED READ — embed the source cell's whole surface via the
    //     real WholeCellTransclusion::embed. A forged/absent/un-finalized URI fails HERE
    //     → Unresolvable, NO embed (the anti-forge tooth inherited verbatim).
    let embed =
        match WholeCellTransclusion::embed(web, host, &source_uri, declared_surface, lineage) {
            Ok(embed) => embed,
            Err(WholeCellTransclusionError::Surface(e)) => {
                return Paste {
                    source_uri: source_uri.to_uri_string(),
                    host,
                    status: ResolveStatus::Unresolvable {
                        reason: format!("{e:?}"),
                    },
                    provenance: None,
                };
            }
        };
    let provenance = embed.cite().clone();

    // (2) THE PER-VIEWER PROJECTION — resolve the embed through the viewer's membrane.
    //     A reachable viewer gets a Resolved paste (content + cited receipt); an
    //     under-capped / incomparable viewer gets a Darkened paste (citation kept,
    //     content withheld — never forged).
    let view: EmbeddedCellView = embed.project_for(viewer);
    let receipt = reflect::short_hex(&provenance.receipt_hash);
    let commitment = reflect::short_hex(&provenance.content_hash);
    let status = match &view.visibility {
        EmbedVisibility::Visible {
            affordance_names, ..
        } => ResolveStatus::Resolved {
            receipt,
            commitment,
            visible_affordances: affordance_names.len(),
            declared_affordances: view.declared_affordance_count,
        },
        EmbedVisibility::Darkened => ResolveStatus::Darkened {
            receipt,
            commitment,
        },
    };

    Paste {
        source_uri: source_uri.to_uri_string(),
        host,
        status,
        provenance: Some(provenance),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use web_aff::affordance::CellAffordance;
    use web_aff::dregg_turn_reexport::Event;
    use web_aff::{AuthRequired, Effect};

    /// A deterministic cell id from a seed byte (mirrors `cell_transclusion`'s `cid`).
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
                provenance: [0u8; 32],
            },
        }
    }

    /// The source cell's published whole surface: {view, comment, edit, admin} on the
    /// three-tier rights chain `Signature ⊂ Either ⊂ None` — each a REAL effect-template
    /// (the same canonical doc-cell surface `cell_transclusion`'s tests use).
    fn source_surface(source: CellId) -> AffordanceSurface {
        AffordanceSurface::new(source)
            .declare(CellAffordance::new(
                "view",
                Requirement::AtLeast(Credential::Signature),
                emit_event(source),
            ))
            .declare(CellAffordance::new(
                "comment",
                Requirement::AtLeast(Credential::Either),
                emit_event(source),
            ))
            .declare(CellAffordance::new(
                "edit",
                Requirement::AtLeast(Credential::Either),
                emit_event(source),
            ))
            .declare(CellAffordance::new(
                "admin",
                Requirement::Root,
                grant_cap(source, cid(99)),
            ))
    }

    /// Publish a source cell into a fresh web-of-cells (surface root committed +
    /// quorum-attested — a genuine finalized read), returning the web and its
    /// `dregg://` URI. The strong (`Either`) lineage is the per-viewer ceiling.
    fn publish_source(seed: u8) -> (WebOfCells, DreggUri, SurfaceCapability) {
        let mut web = WebOfCells::new(3);
        let uri = web.publish(seed, b"<cell surface root>", "dregg://embedded-cell");
        let lineage = SurfaceCapability::root(uri.cell, AuthRequired::Either);
        (web, uri, lineage)
    }

    // (1) THE ROUND-TRIP — `uri_for` then `parse_uri` recovers the SAME cell, and the
    //     URI is the genuine `web_cells` `dregg://<64-hex>` scheme.
    #[test]
    fn uri_for_then_parse_uri_round_trips_a_cell() {
        let cell = cid(7);
        let uri = uri_for(cell);
        // The genuine web_cells scheme: dregg:// + 64 hex chars (the content-addressed id).
        assert!(uri.starts_with("dregg://"), "the genuine dregg:// scheme");
        assert_eq!(
            uri.len(),
            "dregg://".len() + 64,
            "the content-addressed cell id"
        );
        // Round-trips back to the SAME cell.
        let parsed = parse_uri(&uri).expect("a well-formed dregg:// URI parses");
        assert_eq!(parsed.cell, cell, "uri_for ∘ parse_uri = identity");
        // And it denotes the same DreggUri web_cells speaks.
        assert_eq!(parsed.uri(), DreggUri::new(cell));
    }

    // (1b) A malformed string does NOT parse — it cannot masquerade as a cell ref.
    #[test]
    fn a_malformed_uri_does_not_parse() {
        assert!(
            parse_uri("https://evil.example.com").is_none(),
            "wrong scheme"
        );
        assert!(parse_uri("dregg://tooshort").is_none(), "wrong length");
        assert!(
            parse_uri(&format!("dregg://{}", "zz".repeat(32))).is_none(),
            "non-hex"
        );
    }

    // (2) PASTE OF AN AUTHORIZED CELL — a real provenanced embed: the cited receipt +
    //     the content (the per-viewer affordance set) are present, not faked.
    #[test]
    fn paste_of_an_authorized_cell_yields_a_real_provenanced_embed() {
        let (web, uri, lineage) = publish_source(2);
        let host = cid(1);
        let mut doc = LinkPasteDoc::new(host);

        // An EDITOR-tier viewer (Either) clears view/comment/edit of the embed.
        let viewer = Membrane::new(SurfaceCapability::root(cid(10), AuthRequired::Either));
        let paste = doc.paste(
            &web,
            &uri.to_uri_string(),
            &viewer,
            source_surface(uri.cell),
            lineage,
        );

        // The paste RESOLVED — a real verified embed for this viewer.
        match resolve_status(paste) {
            ResolveStatus::Resolved {
                receipt,
                commitment,
                visible_affordances,
                declared_affordances,
            } => {
                // The cited receipt + content commitment are real (drawn from the
                // verified finalized read), not blank.
                assert!(receipt.len() >= 4, "the cited receipt is real");
                assert!(commitment.len() >= 4, "the content commitment is real");
                // The CONTENT is present: the editor sees view+comment+edit (3 of 4).
                assert_eq!(
                    *visible_affordances, 3,
                    "the editor sees the embed's content (view/comment/edit), not admin"
                );
                assert_eq!(
                    *declared_affordances, 4,
                    "…out of the FOUR the source declares (the denominator is carried, \
                     not guessed)"
                );
            }
            other => panic!("an authorized paste must resolve, got {other:?}"),
        }
        // The provenance survives on the paste (a checkable citation).
        assert!(
            paste.provenance.is_some(),
            "a resolved paste carries provenance"
        );
        assert!(paste.cited_receipt().is_some(), "and a cited receipt");
    }

    // (3) PASTE FOR AN UNDER-CAPPED VIEWER — a DARKENED embed: the citation present,
    //     the content WITHHELD (never forged). The Xanadu link still points, honestly.
    #[test]
    fn an_under_capped_viewer_gets_a_darkened_embed_citation_present_content_withheld() {
        let (web, uri, lineage) = publish_source(3);
        let host = cid(1);
        let mut doc = LinkPasteDoc::new(host);

        // A viewer holding a `Custom { vk_hash }` identity is INCOMPARABLE with the
        // embed's `Either` lineage (neither attenuates the other) — no view both admit,
        // so the paste DARKENS. (Same property `cell_transclusion`'s darkening test uses.)
        let viewer = Membrane::new(SurfaceCapability::root(
            cid(13),
            AuthRequired::Custom { vk_hash: [7u8; 32] },
        ));
        let paste = doc.paste(
            &web,
            &uri.to_uri_string(),
            &viewer,
            source_surface(uri.cell),
            lineage,
        );

        match resolve_status(paste) {
            ResolveStatus::Darkened {
                receipt,
                commitment,
            } => {
                // The CITATION survives — the reader knows WHAT cell is pasted and that
                // it is genuinely cited (provenance kept).
                assert!(
                    receipt.len() >= 4,
                    "the citation (receipt) survives darkening"
                );
                assert!(
                    commitment.len() >= 4,
                    "the cited commitment survives darkening"
                );
            }
            other => panic!("an under-capped paste must darken, got {other:?}"),
        }
        // The provenance + cited receipt STILL survive on the paste — withheld content,
        // never a forgery.
        assert!(
            paste.provenance.is_some(),
            "a darkened paste keeps its provenance"
        );
        assert!(
            paste.cited_receipt().is_some(),
            "a darkened paste keeps its citation"
        );
        // But the status is NOT resolved (content withheld).
        assert!(!resolve_status(paste).is_resolved(), "content is withheld");
    }

    // (4) A BAD / FORGED URI IS UNRESOLVABLE — NO embed. The anti-forge tooth: an
    //     unresolvable paste yields nothing, never a faked inclusion.
    #[test]
    fn a_bad_or_forged_uri_is_unresolvable_no_embed() {
        let (web, _uri, _lineage) = publish_source(4);
        let host = cid(1);
        let viewer = Membrane::new(SurfaceCapability::root(cid(10), AuthRequired::Either));

        // (a) A malformed paste — not even a cell ref. Unresolvable, no embed.
        {
            let mut doc = LinkPasteDoc::new(host);
            let absent = cid(200);
            let paste = doc.paste(
                &web,
                "dregg://not-a-real-hex-address",
                &viewer,
                source_surface(absent),
                SurfaceCapability::root(absent, AuthRequired::Either),
            );
            assert!(
                matches!(resolve_status(paste), ResolveStatus::Unresolvable { .. }),
                "a malformed URI is unresolvable"
            );
            assert!(paste.provenance.is_none(), "no embed ⇒ no provenance");
            assert!(
                paste.cited_receipt().is_none(),
                "no embed ⇒ no cited receipt"
            );
        }

        // (b) A well-formed URI to a cell that was NEVER published (a dead/forged link).
        //     The verified finalized read fails → Unresolvable, NO faked inclusion.
        {
            let mut doc = LinkPasteDoc::new(host);
            let absent = cid(201);
            let dead_uri = uri_for(absent); // well-formed dregg://, but no such page
            let paste = doc.paste(
                &web,
                &dead_uri,
                &viewer,
                source_surface(absent),
                SurfaceCapability::root(absent, AuthRequired::Either),
            );
            assert!(
                matches!(resolve_status(paste), ResolveStatus::Unresolvable { .. }),
                "a dead/forged URI cannot be embedded — it is unresolvable, never forged"
            );
            assert!(
                paste.provenance.is_none(),
                "a forged link produces no embed"
            );
        }
    }

    // (5) THE DOCUMENT SPEAKS REAL PASTE TEXT — the anti-blank guarantee (mirrors
    //     web_cells.rs / links_here.rs): the rendered surface names the host and each
    //     pasted link with its status badge + cited receipt.
    #[test]
    fn the_document_speaks_real_per_viewer_paste_text() {
        let (web, uri, lineage) = publish_source(5);
        let host = cid(1);
        let mut doc = LinkPasteDoc::new(host);
        let viewer = Membrane::new(SurfaceCapability::root(cid(10), AuthRequired::Either));
        doc.paste(
            &web,
            &uri.to_uri_string(),
            &viewer,
            source_surface(uri.cell),
            lineage,
        );

        let text = doc.all_text();
        assert!(
            text.len() >= 2,
            "the document renders real lines, got {}",
            text.len()
        );
        for line in &text {
            assert!(!line.trim().is_empty(), "every line is non-empty real text");
        }
        let blob = text.join("\n");
        assert!(blob.contains("link-paste document"), "names the surface");
        assert!(
            blob.contains("dregg://"),
            "names the dregg:// paste addressing"
        );
        assert!(blob.contains("resolved"), "shows the resolve-status badge");
        assert!(blob.contains("receipt"), "shows the cited receipt");
    }
}
