//! The WHAT-LINKS-HERE panel — Ted Nelson's two-way link, made navigable in the
//! cockpit.
//!
//! The web-of-cells browser ([`crate::web_cells`]) renders the *forward* link: a
//! cell's `dregg://` page transcludes ANOTHER cell's finalized field (the
//! [`TranscludedField`] verified read). The forward link only ever points OUT. Ted
//! Nelson's grievance with the web was exactly this **one-way link**: nothing points
//! back, so "what links here" is unanswerable except by a crawler's best-effort guess.
//!
//! This panel renders the link the OTHER way — **who transcludes / observes ME** —
//! and it is not a hand-maintained index that drifts: it is the genuine
//! [`Backlinks`] witness-graph, navigated by the REAL
//! [`DreggverseMap`](crate::dreggverse_map::DreggverseMap) (the vendored, byte-
//! identical `dregg_app_framework::dreggverse_map`). Each backlink carries the cited
//! **receipt + content commitment** of the observation, so it is a *verifiable fact*
//! ("observer O quoted source S's value V at receipt R"), never a dangling pointer.
//!
//! Like [`crate::web_cells`] and [`crate::landing`], this is the panel's pure, gpui-
//! free **text MODEL**: a projection of the live image's witness-graph into navigable
//! backlink rows. The cockpit renders this model with native gpui — but because the
//! *content* is built here, gpui-free, it is `cargo test`-able: a test asserts the
//! panel speaks real, attested, per-viewer backlink text about the real cells, so
//! "the cockpit shows what-links-here" is proven without a GPU.
//!
//! ## Everything here is the REAL witness-graph, never a parallel model
//!
//! - The graph is built by resolving GENUINE transclusions among the live World
//!   cells: each cell is published as a `dregg://` page into one [`WebOfCells`], and
//!   each cell transcludes the NEXT cell's finalized field through the real
//!   [`TranscludedField::include`] (the same content→commitment→receipt→quorum read
//!   the web-of-cells transclusion row uses). Each resolved quote is recorded into a
//!   real [`Backlinks`] via [`Backlinks::observe`] — so the backlink of cell *N* is
//!   cell *N−1*, a verifiable fact, not a fabricated edge.
//! - The navigation is the genuine [`DreggverseMap`](crate::dreggverse_map::DreggverseMap):
//!   [`DreggverseMap::transitive_map`] is the god's-eye depth-bounded backlinks-of-
//!   backlinks graph; [`DreggverseMap::project_for`] is that graph PROJECTED through
//!   the focused agent's REAL [`Membrane`] — a backlink whose link lineage the
//!   viewer's held authority cannot admit (the membrane's `Membrane::project` refuses,
//!   the proven `is_attenuation` lattice) is **OMITTED**. The fog-of-war for links.
//! - To make that fog TRUE and not decorative, one source's backlinks are GATED
//!   behind a real link lineage (`DreggverseMap::gate_source`): the focused-cell
//!   membrane sees them when (and only when) its held authority can project the
//!   lineage. The "view as ROOT / EDITOR" toggle the cockpit drives is exactly the
//!   viewer's held authority — so flipping it can reveal/omit a gated backlink, the
//!   property made tangible.
//!
//! ## What is integrated vs. named-next
//!
//! - **Integrated (here):** the cockpit answers "what links here" for the focused
//!   cell — it lists the backlinks (observer → focused) the agent's membrane
//!   authorizes, each with its cited receipt + content commitment + a depth tag, each
//!   CLICKABLE to navigate into the observing cell (whose own "what links here" then
//!   renders). The god's-eye link count vs. the per-viewer count is shown, so the fog
//!   is visible: a viewer sees ≤ the god's-eye map.
//! - **Named-next:** the witness-graph here is seeded from the cockpit's own cell ring
//!   (a deterministic, demonstrable docuverse). Recording the backlinks of REAL
//!   user-authored transclusions as they are committed (so the graph grows with the
//!   image's genuine quoting activity, not a seeded ring) is the increment that makes
//!   the docuverse map reflect organic use — named in [`LinksHerePanel::seeded_note`]
//!   so it is visible in the panel, not buried.

use starbridge_web_surface as web;
use web::delegate::SurfaceCapability;
use web::rehydrate::Membrane;
use web::transclusion::{Backlinks, TranscludedField};
use web::web_of_cells::{DreggUri, WebOfCells};
use web::AuthRequired;

use dregg_cell::CellId;

use crate::dreggverse_map::{DreggverseGraph, DreggverseMap};
use crate::reflect;
use crate::world::World;

/// One **backlink row** the WHAT-LINKS-HERE panel renders — a verifiable two-way
/// link the focused agent's membrane authorizes it to see. Every field is a real
/// read of the witness-graph, never a hand-set string.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BacklinkRow {
    /// The cell that observes/transcludes — the *navigable* end ("what links here
    /// points back FROM"). Clicking this row refocuses the panel on `observer`, so
    /// its OWN what-links-here renders (recursive navigation).
    pub observer: CellId,
    /// The cell being observed (the `source` end of this particular edge). For a
    /// depth-1 row this is the focused cell; for a deeper row it is an intermediate
    /// source (who links to the things that link here).
    pub source: CellId,
    /// The `dregg://<hex>` address of the observer (the clickable navigation target).
    pub observer_uri: String,
    /// The cited RECEIPT the observation was pinned to (short-hex) — the immutable
    /// past that dates the backlink, making it a verifiable fact, not a bare pointer.
    pub receipt_hash: String,
    /// The source content commitment that was observed (short-hex) — what value was
    /// quoted (the content address of the finalized read).
    pub content_hash: String,
    /// How many hops out from the focused cell this backlink sits (1 = a direct
    /// backlink of the focus; 2 = a backlink-of-a-backlink; …). The map is depth-
    /// bounded, so this is always `≤ depth`.
    pub hops: usize,
}

/// THE WHAT-LINKS-HERE MODEL — the focused cell's backlink docuverse as the cockpit
/// shows it, built fresh from the live [`World`]'s witness-graph and projected through
/// the focused agent's membrane. The addresses, receipts, and the visible-vs-total
/// link counts it shows are the running image's actual two-way links.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinksHerePanel {
    /// The cell the question "what links here?" is asked OF — the focus.
    pub focus: CellId,
    /// The `dregg://<hex>` address of the focused cell (its docuverse identity).
    pub focus_uri: String,
    /// The viewer authority the panel projects the backlink graph FOR (the
    /// `AuthRequired` the focused agent holds) — what decides the link fog-of-war.
    pub viewer_tier: String,
    /// The depth bound the transitive walk used (how many hops of backlinks-of-
    /// backlinks the map reaches — always finite + cheap).
    pub depth: usize,
    /// The backlink rows the agent's MEMBRANE authorizes it to see — the projected
    /// (`project_for`) per-viewer map, sorted by (hops, observer). A row the viewer's
    /// caps cannot admit is ABSENT (the fog), and `total_link_count` records how many
    /// the god's-eye map has so the omission is visible.
    pub backlinks: Vec<BacklinkRow>,
    /// How many backlink edges the GOD'S-EYE (unprojected) map has within the depth
    /// bound — the total the docuverse holds. The panel shows "you see N of M", so a
    /// viewer can tell when the membrane has fogged links away (`backlinks.len() ≤ M`).
    pub total_link_count: usize,
    /// How many distinct cells appear as navigable nodes in the focused agent's
    /// projected map (the focus + every observer it can see) — the reachable docuverse.
    pub visible_nodes: usize,
    /// Whether at least one source in the docuverse is GATED behind a link lineage
    /// (so the fog-of-war is genuinely in play). Shown so the panel can explain why a
    /// viewer might see fewer links than the god's-eye count.
    pub has_gated_links: bool,
}

impl LinksHerePanel {
    /// Build the panel model from the live world, answering "what links here?" for
    /// `focus`. `viewer_rights` is the authority the focused agent holds (the
    /// "view as ROOT/EDITOR" toggle the cockpit drives); `depth` is the hop bound.
    ///
    /// This is the single source of the panel's content — the cockpit renders exactly
    /// these rows, so the `cargo test` that asserts they are real + cited + per-viewer
    /// proves the rendered tree shows the real what-links-here.
    pub fn build(
        world: &World,
        focus: CellId,
        viewer_rights: AuthRequired,
        depth: usize,
    ) -> Self {
        // Build a REAL witness-graph from the live image: publish each World cell as a
        // dregg:// page into one WebOfCells, then resolve a genuine transclusion of the
        // NEXT cell from each cell (a ring), recording each into the real Backlinks.
        //
        // The witness-graph is keyed by the PUBLISHED ORIGIN cells (the `dregg://` page
        // cells `WebOfCells::publish` seeds, which is the cell a transclusion's
        // provenance names) — NOT the World cell ids directly. `Graph` carries both the
        // graph and the origin↔world maps so we can ask the question about the focused
        // WORLD cell (mapping it to its page cell) and present observers as World cells
        // (so the cockpit's click-to-navigate uses World ids).
        let g = build_witness_graph(world);
        let links = &g.links;

        // The focused World cell's `dregg://` PAGE cell (the node the question is asked
        // of in the witness-graph). If the focus has no published page (e.g. it is not
        // in the ledger), the map is honestly empty.
        let focus_page = g.page_of_world.get(&focus).copied();

        // GATE the focused page's backlinks behind a `Proof` link lineage so the
        // per-viewer fog-of-war is TRUE, not decorative. The membrane meet
        // (`is_attenuation`) admits it for a viewer holding `None` (root, projects
        // everything) or `Proof`/`Either` (Proof ⊆ both), but REFUSES it for a
        // `Signature` viewer — `Signature` and `Proof` are INCOMPARABLE (neither
        // attenuates the other), so the meet has no common authority and the backlink is
        // fogged. (Every OTHER source stays public — ungated — so the panel is never
        // empty.) The cockpit's None ⇄ Signature toggle is exactly this reveal/fog line.
        let map = match focus_page {
            Some(page) => {
                let lineage = SurfaceCapability::root(page, AuthRequired::Proof);
                DreggverseMap::new(links).gate_source(page, lineage)
            }
            None => DreggverseMap::new(links),
        };
        let has_gated_links = focus_page.is_some();

        // Resolve the maps over the focused page cell. If the focus has no page, both
        // are the empty (root-only) maps — an honest empty readout, never an error.
        let (godseye, projected, visible_nodes) = match focus_page {
            Some(page) => {
                // The god's-eye map (everything within the depth bound, no fog).
                let godseye = map.transitive_map(page, depth);
                // The PER-VIEWER projection through the focused agent's REAL membrane: a
                // gated source the viewer cannot project is OMITTED (and so is anything
                // reachable only through it — you cannot navigate a link you cannot see).
                let viewer = Membrane::new(SurfaceCapability::root(page, viewer_rights.clone()));
                let projected = map.project_for(page, depth, &viewer);
                let vis = projected.nodes.len();
                (godseye, projected, vis)
            }
            None => (DreggverseGraph::default(), DreggverseGraph::default(), 0),
        };
        let total_link_count = godseye.link_count();

        // Annotate each projected edge with its hop distance from the focused page (a
        // BFS over the projected edges, so the depth tag matches what the viewer sees).
        let hops_of = focus_page
            .map(|page| hop_distances(&projected, page))
            .unwrap_or_default();

        // Map each projected edge's page cells BACK to World cells for the rows, so the
        // cockpit's click-to-navigate uses World ids (and the addresses are the live
        // image's cells). A page with no World mapping (impossible here) is skipped.
        let mut backlinks: Vec<BacklinkRow> = projected
            .edges
            .iter()
            .filter_map(|e| {
                let observer_world = *g.world_of_page.get(&e.observer)?;
                let source_world = *g.world_of_page.get(&e.source)?;
                Some(BacklinkRow {
                    observer: observer_world,
                    source: source_world,
                    observer_uri: uri_string_for(&g.uris, observer_world),
                    receipt_hash: reflect::short_hex(&e.receipt_hash),
                    content_hash: reflect::short_hex(&e.content_hash),
                    hops: hops_of.get(&e.observer).copied().unwrap_or(1),
                })
            })
            .collect();
        // Stable order: nearest backlinks first, then by observer (deterministic).
        backlinks.sort_by(|a, b| a.hops.cmp(&b.hops).then(a.observer.0.cmp(&b.observer.0)));

        LinksHerePanel {
            focus,
            focus_uri: format!("dregg://{}", reflect::short_hex(&focus.0)),
            viewer_tier: format!("{viewer_rights:?}"),
            depth,
            backlinks,
            total_link_count,
            visible_nodes,
            has_gated_links,
        }
    }

    /// The seeded-graph note — stated in the model so it is VISIBLE in the panel,
    /// not buried in a doc. The witness-graph is the cockpit's own deterministic cell
    /// ring today; recording REAL committed transclusions is the named increment.
    pub fn seeded_note(&self) -> &'static str {
        "REAL today: this is the genuine `Backlinks` witness-graph, navigated by the \
         real `DreggverseMap` and projected through your membrane — each backlink \
         carries its cited receipt + content commitment (a verifiable fact). NEXT: \
         seed it from REAL user-committed transclusions (not the cockpit's cell ring) \
         so the docuverse map grows with the image's organic quoting activity."
    }

    /// Is the focused cell transcluded by NOBODY the viewer can see (an empty
    /// readout, never an error)? The panel renders an honest "no backlinks" then.
    pub fn is_empty(&self) -> bool {
        self.backlinks.is_empty()
    }

    /// How many backlinks the membrane FOGGED away (the god's-eye total minus what the
    /// viewer sees) — the count the panel surfaces so the omission is legible.
    pub fn fogged_count(&self) -> usize {
        self.total_link_count.saturating_sub(self.backlinks.len())
    }

    /// Every line of real text the panel renders, flattened — used by tests to assert
    /// the panel speaks real, cited, per-viewer backlink text about the real cells
    /// (the exact gpui tree content, so non-empty here == non-empty rendered tree).
    pub fn all_text(&self) -> Vec<String> {
        let mut out = Vec::new();
        out.push(format!(
            "what links here — {} (focus) · viewer holds {} · depth {}",
            self.focus_uri, self.viewer_tier, self.depth
        ));
        out.push(format!(
            "you see {} of {} backlink(s) the docuverse holds within {} hop(s) — {} fogged by your caps · {} navigable node(s)",
            self.backlinks.len(),
            self.total_link_count,
            self.depth,
            self.fogged_count(),
            self.visible_nodes,
        ));
        if self.backlinks.is_empty() {
            out.push(
                "no backlinks visible to you — nobody you are cleared to see transcludes this cell"
                    .to_string(),
            );
        }
        for b in &self.backlinks {
            out.push(format!(
                "← {} transcludes dregg://{} (hop {}) · receipt {} · commitment {}",
                b.observer_uri,
                reflect::short_hex(&b.source.0),
                b.hops,
                b.receipt_hash,
                b.content_hash,
            ));
        }
        out.push(self.seeded_note().to_string());
        out
    }
}

// ── the model-building helpers (pure; each names the real witness-graph primitive) ──

/// Build a REAL [`Backlinks`] witness-graph from the live world: publish each cell as
/// a `dregg://` page into one [`WebOfCells`], then resolve a genuine
/// [`TranscludedField::include`] of the NEXT cell from each cell (a ring), recording
/// each resolved quote with [`Backlinks::observe`]. Returns the populated witness-graph
/// and the per-cell published `dregg://` URI map (for the navigable observer addresses).
///
/// The ring is the SAME forward-transclusion relationship the web-of-cells panel shows
/// (cell *N* transcludes cell *N+1*); read the OTHER way it is the backlink "cell *N+1*
/// is transcluded by cell *N*". Every edge is a verifiable finalized read (content →
/// commitment → receipt → quorum), never a fabricated pointer — a forged/un-finalized
/// quote could not be `include`d, so it could not be recorded.
struct Graph {
    /// The REAL witness-graph, keyed by PAGE (published origin) cells.
    links: Backlinks,
    /// `(world_cell, dregg://uri)` per published cell — the navigable addresses.
    uris: Vec<(CellId, DreggUri)>,
    /// World cell → its `dregg://` PAGE (origin) cell (to map a focus into the graph).
    page_of_world: std::collections::BTreeMap<CellId, CellId>,
    /// PAGE (origin) cell → the World cell it denotes (to map graph nodes back out).
    world_of_page: std::collections::BTreeMap<CellId, CellId>,
}

/// Build a REAL [`Backlinks`] witness-graph from the live world, plus the origin↔world
/// cell maps. Each World cell is published as a `dregg://` page (a fresh origin cell)
/// into one [`WebOfCells`], and each cell transcludes the NEXT cell's finalized field
/// through the real [`TranscludedField::include`] (a ring). Each resolved quote is
/// recorded into the [`Backlinks`] via [`Backlinks::observe`], keyed by the source the
/// quote points at — the PUBLISHED PAGE cell (`field.provenance.source.cell`). The maps
/// let the panel ask the question about a World cell (→ its page) and present observers
/// as World cells. Every edge is a verified finalized read, never a fabricated pointer.
fn build_witness_graph(world: &World) -> Graph {
    use std::collections::BTreeMap;
    let mut web = WebOfCells::new(3);

    // Publish every live cell as its own dregg:// page (stable per-cell seeds so the
    // addresses are deterministic across frames — the navigable backlink URIs are
    // stable as the image evolves).
    let cells: Vec<CellId> = {
        let mut v: Vec<CellId> = world.ledger().iter().map(|(id, _)| *id).collect();
        v.sort_by(|a, b| a.0.cmp(&b.0));
        v
    };
    let mut uris: Vec<(CellId, DreggUri)> = Vec::new();
    let mut page_of_world: BTreeMap<CellId, CellId> = BTreeMap::new();
    let mut world_of_page: BTreeMap<CellId, CellId> = BTreeMap::new();
    for (seed, cell) in cells.iter().enumerate() {
        let (balance, caps) = world
            .ledger()
            .get(cell)
            .map(|c| (c.state.balance(), c.capabilities.len()))
            .unwrap_or((0, 0));
        let body = page_body_for_cell(cell, balance, caps);
        let url = format!("dregg://cell/{}", reflect::short_hex(&cell.0));
        // `seed` is the cell INDEX (distinct per cell), so each gets a distinct page.
        let uri = web.publish(seed as u8, body.as_bytes(), &url);
        page_of_world.insert(*cell, uri.cell);
        world_of_page.insert(uri.cell, *cell);
        uris.push((*cell, uri));
    }

    // The ring of REAL transclusions: cell N transcludes cell N+1's finalized field.
    // Recorded the OTHER way, this is the backlink "page(N+1) ← page(N)". With ≥2 cells
    // every page has exactly one distinct backlink (its predecessor in the ring) — a
    // rich-enough docuverse to navigate at any depth. `observe` keys by the source page
    // the quote points at (`field.provenance.source.cell` = the published page cell).
    let mut links = Backlinks::new();
    if uris.len() >= 2 {
        for i in 0..uris.len() {
            let (observer_world, _observer_uri) = &uris[i];
            let (_source_world, source_uri) = &uris[(i + 1) % uris.len()];
            // The observer recorded is the PAGE cell of the observing World cell (so the
            // graph is wholly in page-cell space, consistent with how `observe` keys the
            // source). We map back to World cells when building the rows.
            let observer_page = *page_of_world.get(observer_world).expect("observer published");
            if let Ok(field) = TranscludedField::include(&web, source_uri) {
                links.observe(observer_page, &field);
            }
        }
    }
    Graph { links, uris, page_of_world, world_of_page }
}

/// The page body a `dregg://` cell serves (the attested content the receipt + quorum
/// bind). A real, human-readable description drawn from LIVE ledger state — the same
/// shape the web-of-cells browser publishes, so the two panels quote the same pages.
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

/// The `dregg://<hex>` address string of `cell` (its navigable identity), from the
/// published URI map. Falls back to deriving it from the id if (impossibly) absent.
fn uri_string_for(uris: &[(CellId, DreggUri)], cell: CellId) -> String {
    uris.iter()
        .find(|(c, _)| *c == cell)
        .map(|(_, u)| u.to_uri_string())
        .unwrap_or_else(|| format!("dregg://{}", reflect::short_hex(&cell.0)))
}

/// BFS the projected backlink graph from `focus` to tag each observer with its hop
/// distance (1 = a direct backlink of the focus, 2 = a backlink-of-a-backlink, …).
/// Walks the SAME edges the viewer sees, so the depth tag is faithful to the
/// projection (a fogged edge contributes no hop). Uses the projected graph's own
/// `observers_of` so it never reaches past what the membrane admitted.
fn hop_distances(graph: &DreggverseGraph, focus: CellId) -> std::collections::BTreeMap<CellId, usize> {
    use std::collections::{BTreeMap, BTreeSet, VecDeque};
    let mut dist: BTreeMap<CellId, usize> = BTreeMap::new();
    let mut seen: BTreeSet<CellId> = BTreeSet::new();
    let mut queue: VecDeque<(CellId, usize)> = VecDeque::new();
    seen.insert(focus);
    queue.push_back((focus, 0));
    while let Some((cell, hops)) = queue.pop_front() {
        // The observers of `cell` within the projected map are one hop further out.
        for observer in graph.observers_of(cell) {
            // The nearest hop wins (BFS order guarantees first-seen is nearest).
            dist.entry(observer).or_insert(hops + 1);
            if seen.insert(observer) {
                queue.push_back((observer, hops + 1));
            }
        }
    }
    dist
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::World;

    /// The EDITOR tier (`Either`) — its membrane CAN project the gated focus lineage
    /// (`Proof`), since `Proof ⊆ Either`, so the editor viewer SEES the focus's
    /// backlinks (a clean "authorized" witness).
    fn editor_rights() -> AuthRequired {
        AuthRequired::Either
    }

    /// A multi-cell GENESIS-ONLY world (no committed turns) — three open cells, enough
    /// for the ring witness-graph. The panel's witness-graph needs CELLS, not committed
    /// turns (it publishes each cell as a `dregg://` page and transcludes the ring), so
    /// genesis cells suffice — and this keeps the tests off the turn executor entirely.
    /// Returns the world and the three cell ids (a stand-in for `[treasury, service,
    /// user]`).
    fn ring_world() -> (World, [CellId; 3]) {
        let mut w = World::new();
        let a = w.genesis_cell(0x11, 1_000);
        let b = w.genesis_cell(0x22, 0);
        let c = w.genesis_cell(0x33, 5_00);
        (w, [a, b, c])
    }

    #[test]
    fn what_links_here_lists_the_real_backlinks_of_the_focused_cell() {
        // The two-way link: in the cockpit's cell ring, the focused cell's predecessor
        // transcludes it — so "what links here" for the focus is a real, cited backlink.
        let (world, anchors) = ring_world();
        let focus = anchors[1]; // the "service" cell
        let panel = LinksHerePanel::build(&world, focus, editor_rights(), 2);

        assert_eq!(panel.focus, focus, "the panel is rooted at the focused cell");
        assert!(panel.focus_uri.starts_with("dregg://"), "the focus has a dregg:// identity");
        // An authorized (Either) viewer clears the gated focus lineage → sees backlinks.
        assert!(
            !panel.is_empty(),
            "the authorized viewer sees the focused cell's backlinks"
        );
        for b in &panel.backlinks {
            // Each backlink is a real dregg:// address (64 hex chars for the cell id).
            assert!(b.observer_uri.starts_with("dregg://"), "an observer is a dregg:// address");
            assert_eq!(
                b.observer_uri.len(),
                "dregg://".len() + 64,
                "the observer address is the content-addressed cell id"
            );
            // The backlink carries its cited receipt + content commitment — a
            // verifiable fact, not a bare pointer.
            assert!(b.receipt_hash.len() >= 4, "the cited receipt is real");
            assert!(b.content_hash.len() >= 4, "the observed content commitment is real");
            assert!(b.hops >= 1 && b.hops <= panel.depth, "the hop tag is within the depth bound");
        }
    }

    #[test]
    fn a_fogged_viewer_sees_fewer_backlinks_than_the_godseye_the_membrane_proof() {
        // THE FOG-OF-WAR: the focus's backlinks are gated behind a `Proof` link
        // lineage. A viewer holding `None` (root) projects everything → sees them. A
        // `Signature` viewer is INCOMPARABLE to `Proof` (neither attenuates the other),
        // so its membrane cannot meet the lineage → the backlinks are OMITTED. The
        // fogged viewer sees STRICTLY FEWER than the god's-eye map — the property, the
        // SAME None ⇄ Signature line the cockpit toggle drives.
        let (world, anchors) = ring_world();
        let focus = anchors[1];

        let authorized = LinksHerePanel::build(&world, focus, AuthRequired::None, 2);
        let fogged = LinksHerePanel::build(&world, focus, AuthRequired::Signature, 2);

        assert!(panel_has_focus_backlink(&authorized, focus), "the root viewer sees the focus's direct backlink");
        // The fogged (incomparable Signature) viewer sees the focus's DIRECT backlinks
        // omitted: the gate is on `focus`, so its observers are fogged for an
        // incomparable viewer.
        assert!(
            !panel_has_focus_backlink(&fogged, focus),
            "the Signature viewer's membrane (incomparable to the Proof lineage) fogs the focus's gated backlinks"
        );
        assert!(
            fogged.backlinks.len() < authorized.backlinks.len()
                || fogged.fogged_count() > authorized.fogged_count(),
            "the fogged viewer sees fewer backlinks than the root one (the fog-of-war)"
        );
        // The god's-eye total is the SAME for both — the map is relational, only the
        // PROJECTION differs (the membrane decides visibility, not the graph).
        assert_eq!(
            authorized.total_link_count, fogged.total_link_count,
            "the god's-eye docuverse is the same; only the per-viewer projection differs"
        );
        assert!(fogged.fogged_count() >= 1, "the incomparable viewer has ≥1 fogged backlink");
    }

    #[test]
    fn the_panel_speaks_real_cited_per_viewer_backlink_text() {
        // The anti-blank guarantee, mirroring web_cells.rs / landing.rs: the rendered
        // panel contains many lines of real text naming the focus, the per-viewer
        // visible-vs-total counts, the real dregg:// backlinks with their cited
        // receipts + commitments, and the seeded-graph note.
        let (world, anchors) = ring_world();
        let panel = LinksHerePanel::build(&world, anchors[1], editor_rights(), 2);
        let text = panel.all_text();
        assert!(text.len() >= 4, "the panel renders several lines of real text, got {}", text.len());
        for line in &text {
            assert!(!line.trim().is_empty(), "every panel line is non-empty real text");
        }
        let blob = text.join("\n");
        assert!(blob.contains("what links here"), "names the what-links-here question");
        assert!(blob.contains("dregg://"), "names the dregg:// backlink addressing");
        assert!(blob.contains("receipt"), "shows the cited receipt (the verifiable fact)");
        assert!(blob.contains("commitment"), "shows the observed content commitment");
        assert!(blob.to_lowercase().contains("fog") || blob.contains("of"), "surfaces the per-viewer fog/visible-of-total");
    }

    #[test]
    fn depth_one_is_direct_backlinks_only_depth_bounds_the_walk() {
        // The transitive map is depth-bounded: depth 1 is the direct backlinks of the
        // focus only; a deeper walk can reach backlinks-of-backlinks. The walk is
        // always finite (cycle-safe), so even a large depth terminates.
        let (world, anchors) = ring_world();
        let focus = anchors[1];
        let d1 = LinksHerePanel::build(&world, focus, AuthRequired::None, 1);
        let d_big = LinksHerePanel::build(&world, focus, AuthRequired::None, 9);

        // depth 1: every visible backlink is exactly one hop out.
        for b in &d1.backlinks {
            assert_eq!(b.hops, 1, "at depth 1 only direct backlinks appear");
        }
        // A deeper walk reaches at least as many backlinks (and terminates — cycle-safe).
        assert!(
            d_big.total_link_count >= d1.total_link_count,
            "a deeper walk reaches ≥ the depth-1 backlinks (and the walk terminates)"
        );
    }

    #[test]
    fn an_empty_world_focus_has_no_backlinks_an_honest_empty_readout() {
        // A cell nobody transcludes (a one-cell world: no ring, no observers) yields an
        // empty readout — never an error, never a fabricated edge.
        let mut world = World::new();
        let lonely = world.genesis_cell(0x01, 0);
        let panel = LinksHerePanel::build(&world, lonely, AuthRequired::None, 3);
        assert!(panel.is_empty(), "a cell nobody transcludes has no backlinks");
        assert_eq!(panel.total_link_count, 0, "the god's-eye map is also empty");
        // The text is still non-blank — it renders an honest "no backlinks" line.
        let blob = panel.all_text().join("\n");
        assert!(blob.contains("no backlinks"), "an empty readout renders an honest line, not a blank");
    }

    /// Does `panel` contain a backlink whose SOURCE is the focus (a direct backlink of
    /// the focused cell)?
    fn panel_has_focus_backlink(panel: &LinksHerePanel, focus: CellId) -> bool {
        panel.backlinks.iter().any(|b| b.source == focus)
    }
}
