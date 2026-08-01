//! **THE DESKTOP'S DOCUVERSE** — the live World's cells, addressable as `dregg://`
//! origins, so the desktop's transclude gesture is a REAL verified transclusion.
//!
//! ## The wound this closes
//!
//! `DeosDesktop::transclude_into` (drag a cell-icon onto an open document) used to
//! build a `format!` string of four ledger fields — id · kind · balance · lifecycle —
//! and append it to the text buffer. That string had three defects, and only the first
//! is cosmetic:
//!
//! 1. it baked the CURRENT balance into prose, which rots the instant the source moves;
//! 2. it cited NOTHING — no finalized read, no receipt, no attestation, so a reader had
//!    no way to check that the quoted cell ever said any of it;
//! 3. **a `format!` interpolates any 32 bytes.** A cell id that names nothing on the
//!    ledger rendered a perfectly ordinary-looking `{transclude dregg://…}` line. The
//!    forgery and the genuine quote were the same string shape.
//!
//! This module is the substrate that makes the gesture honest. It owns a real
//! [`WebOfCells`] fed from the LIVE World through
//! [`WebOfCells::publish_as`] — the door that publishes the cell id the caller already
//! holds, rather than deriving a fresh one from a seed — and resolves a transclusion
//! through the pipeline [`crate::link_paste`] already runs: parse → the verified
//! finalized read ([`crate::cell_transclusion::WholeCellTransclusion::embed`]) →
//! per-viewer projection through the real [`Membrane`]. Nothing here is a new gate; it
//! is the wiring that puts the existing ones IN FRONT of the desktop's compose.
//!
//! ## What is real, and where the seams are
//!
//! **REAL.** The published origin is the live cell: [`Docuverse::publish_live`] reads
//! `world.ledger()` and refuses an id the ledger does not hold, so an unpublished id
//! never becomes a `dregg://` page (**the anti-forge tooth's root** — you cannot open a
//! finalized read of a page that does not exist). The published bytes are a canonical
//! encoding of the cell's COMMITTED surface (its id, balance, nonce, lifecycle, and its
//! umem `heap_root`), so a source that advances re-publishes to a different content
//! commitment and a different serve receipt. The viewer's held authority is read off
//! the viewing user's REAL c-list ([`held_rights`]): a live `CapabilityRef` targeting
//! the source yields exactly that grant's `permissions`; the source's own cell holds
//! root over itself; everyone else is the bare authenticated reader.
//!
//! **NAMED SEAMS.**
//!
//! * The declared affordance surface is the repo's canonical doc-cell surface
//!   `{view, comment, edit, admin}` on the three-tier chain `Signature ⊂ Either ⊂ None`
//!   (the same one `web_cells.rs`, `cell_transclusion.rs` and `link_paste.rs` all
//!   declare), carrying REAL [`Effect`] templates over the source cell. It is NOT read
//!   off the cell's committed [`dregg_cell::Permissions`], and that is deliberate:
//!   `Permissions::access = None` means "**no** authorization needed" (wide open),
//!   while an affordance requiring the root tier is [`dregg_cell::Requirement::Root`] —
//!   the two are oriented oppositely, and mapping one onto the other would silently
//!   inverse every tier. They no longer share a TYPE (that is what `Requirement` is
//!   for), so the mapping cannot be written by accident; deriving a per-cell surface
//!   from committed state still needs a real published-surface field on the cell, and
//!   that is the seam this note names.
//! * The federation attesting these origins is this desktop's own
//!   [`WebOfCells`] quorum, not the World's validator set. The attestation chain
//!   (content → commitment → receipt → receipt-stream root → quorum-signed root) is
//!   genuine and the client-side `verify` runs; the committee it verifies against is
//!   the docuverse's.

use starbridge_web_surface as web_aff;
use web_aff::affordance::{AffordanceSurface, CellAffordance};
use web_aff::delegate::SurfaceCapability;
use web_aff::rehydrate::Membrane;
use web_aff::transclusion::Provenance;
use web_aff::web_of_cells::{DreggUri, WebOfCells};
use web_aff::{AuthRequired, CellId, Effect};

use dregg_cell::lifecycle::CellLifecycle;
use dregg_cell::Cell;

use crate::link_paste::{uri_for, LinkPasteDoc, ResolveStatus};
use crate::world::World;
use dregg_cell::{Credential, Requirement};

/// The quorum size of the docuverse's attesting federation. Three signers, deterministic
/// keys — the same shape every other `WebOfCells` in this crate builds, so a published
/// origin's [`web_aff::AttestedResource::verify`] runs the real receipt-stream
/// reconstruction + quorum gate rather than a degenerate one.
const DOCUVERSE_QUORUM: usize = 3;

/// The surface authority a LIVE cell's embed is served under — the ceiling every
/// per-viewer projection attenuates from.
///
/// `Either` is the editor tier of the canonical `Signature ⊂ Either ⊂ None` chain: a
/// reader who holds a real capability over the source (or is the source) reaches
/// view/comment/edit of the embed; the bare authenticated reader reaches `view` alone;
/// `admin` needs the root authority no embed lineage ever confers. This is a POLICY of
/// the docuverse (which tier it serves embeds at), stated once here rather than spelled
/// at each call site — see the module note on why it is not read off the cell's
/// committed `Permissions`.
const LIVE_LINEAGE_RIGHTS: AuthRequired = AuthRequired::Either;

/// The docuverse's `dregg://` origin surface — a real [`WebOfCells`] whose origins are
/// the live World's own cells.
///
/// One per desktop. Publishing is idempotent-by-content: re-publishing a cell whose
/// committed surface has not moved re-commits the same content hash (so the cited
/// receipt is stable), while a cell that advanced publishes a new commitment and
/// therefore a new serve receipt — the "the source finalized a new height" signal a
/// live quote reads.
pub struct Docuverse {
    web: WebOfCells,
}

impl Default for Docuverse {
    fn default() -> Self {
        Self::new()
    }
}

/// Why a transclusion was REFUSED — the states in which the document must be left
/// exactly as it was.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TranscludeRefusal {
    /// The id names no cell of the live World, so the docuverse never published it as a
    /// `dregg://` origin and there is nothing to open. **The anti-forge tooth**: a
    /// well-formed 32-byte id is not evidence of a cell.
    NotALiveCell {
        /// The id that was dropped (rendered short-hex for the narration).
        cell: CellId,
    },
    /// The origin exists but its verified finalized read did not open — the genuine
    /// [`crate::cell_transclusion::WholeCellTransclusionError`] reason, surfaced
    /// verbatim rather than swallowed.
    Unresolvable {
        /// The `dregg://` URI that failed to resolve.
        uri: String,
        /// The refusal reason from the real transclusion path.
        reason: String,
    },
}

impl TranscludeRefusal {
    /// The line the desktop narrates for this refusal — an honest "nothing was written
    /// and here is why", never a silent no-op.
    pub fn narration(&self) -> String {
        match self {
            TranscludeRefusal::NotALiveCell { cell } => format!(
                "COMPOSE REFUSED: {} is not a cell of this World — never published as a \
                 dregg:// origin, so there is no finalized read to quote. Nothing transcluded.",
                crate::reflect::short_hex(&cell.0)
            ),
            TranscludeRefusal::Unresolvable { uri, reason } => format!(
                "COMPOSE REFUSED: {uri} did not resolve to a verified finalized read ({reason}). \
                 Nothing transcluded."
            ),
        }
    }
}

/// A resolved transclusion — the verified embed, per-viewer, plus the ONE document line
/// it renders.
#[derive(Clone, Debug)]
pub struct Transclusion {
    /// The source cell's `dregg://` origin (the content-addressed address the line
    /// carries, and the anchor `parse_transclusion_ref` reads back).
    pub uri: String,
    /// The per-viewer resolution of the embed — [`ResolveStatus::Resolved`] (content at
    /// the viewer's cap level) or [`ResolveStatus::Darkened`] (citation kept, content
    /// withheld). Never `Unresolvable`: an unresolvable read is a
    /// [`TranscludeRefusal`], not a line.
    pub status: ResolveStatus,
    /// The immutable citation the embed carries — the cited surface commitment +
    /// receipt + finalized flag of the verified read.
    pub provenance: Provenance,
    /// The single document line this transclusion writes.
    pub line: String,
}

impl Docuverse {
    /// A fresh docuverse with no published origins.
    pub fn new() -> Self {
        Docuverse {
            web: WebOfCells::new(DOCUVERSE_QUORUM),
        }
    }

    /// **Publish a LIVE cell as a `dregg://` origin** — and refuse everything else.
    ///
    /// Reads the cell out of `world.ledger()`. If it is not there, this returns `None`
    /// and publishes NOTHING: the docuverse serves exactly the cells the World holds,
    /// which is what makes an unpublished id un-transcludable. (Note that
    /// [`WebOfCells::publish_as`] would happily install a landing site for ANY id — the
    /// ledger read here is the whole tooth, and deleting it is the mutation that kills
    /// the desktop's anti-forge gate.)
    ///
    /// The published bytes are the cell's committed surface encoding
    /// ([`committed_surface_bytes`]) — so the `dregg://` content commitment is a real
    /// function of live committed state, and a source that moves re-publishes to a new
    /// commitment and a new serve receipt.
    pub fn publish_live(&mut self, world: &World, cell: CellId) -> Option<DreggUri> {
        let live = world.ledger().get(&cell)?;
        let bytes = committed_surface_bytes(live);
        let url = format!("dregg://cell/{}", crate::reflect::short_hex(&cell.0));
        Some(self.web.publish_as(cell, &bytes, &url))
    }

    /// **THE ONE TRANSCLUDE PATH** — publish the live source, open it through the REAL
    /// verified finalized read, project it through the viewing user's membrane, and
    /// render the one line the document gets.
    ///
    /// Every step is the existing machinery: [`Docuverse::publish_live`] (the ledger
    /// gate), [`LinkPasteDoc::paste`] (parse → [`crate::cell_transclusion::
    /// WholeCellTransclusion::embed`] → [`crate::cell_transclusion::
    /// WholeCellTransclusion::project_for`]), and the viewer membrane derived from the
    /// real c-list. A refusal returns [`TranscludeRefusal`] and the caller MUST write
    /// nothing.
    ///
    /// `host` is the document cell the embed lands in; `viewer` is the desktop's
    /// operator (whose caps decide what the embed shows).
    pub fn transclude(
        &mut self,
        world: &World,
        host: CellId,
        src: CellId,
        viewer: CellId,
    ) -> Result<Transclusion, TranscludeRefusal> {
        // (1) THE LEDGER GATE — only a live cell of this World becomes an origin.
        let uri = self
            .publish_live(world, src)
            .ok_or(TranscludeRefusal::NotALiveCell { cell: src })?;

        // (2) THE PIPELINE — the same one `link_paste` runs: parse the `dregg://` URI,
        //     open the VERIFIED FINALIZED READ of the source's surface root, and
        //     project the embed through the viewer's membrane.
        let declared = declared_surface_of(src, viewer);
        let lineage = SurfaceCapability::root(src, lineage_rights(world, src));
        let membrane = viewer_membrane(world, viewer, src);

        let mut doc = LinkPasteDoc::new(host);
        let paste = doc.paste(
            &self.web,
            &uri_for(src),
            &membrane,
            declared,
            lineage.clone(),
        );

        // (3) An unresolvable read is a REFUSAL, never a line. (Unreachable from a
        //     just-published origin — but the type forces honesty, and if the read
        //     ever stops opening, the document stays clean rather than gaining an
        //     uncited quote.)
        let provenance = match (&paste.status, &paste.provenance) {
            (ResolveStatus::Unresolvable { reason }, _) => {
                return Err(TranscludeRefusal::Unresolvable {
                    uri: uri.to_uri_string(),
                    reason: reason.clone(),
                })
            }
            (_, Some(p)) => p.clone(),
            (_, None) => {
                return Err(TranscludeRefusal::Unresolvable {
                    uri: uri.to_uri_string(),
                    reason: "resolved without provenance".to_string(),
                })
            }
        };

        let line = transclusion_line(&uri, &paste.status);
        Ok(Transclusion {
            uri: uri.to_uri_string(),
            status: paste.status.clone(),
            provenance,
            line,
        })
    }
}

/// **The one document line a verified transclusion renders.**
///
/// The head is the source's content-addressed `dregg://<64-hex>` origin — the SAME
/// anchor `deos_desktop::parse_transclusion_ref` reads back, so the two-way backlink
/// inversion keeps working unchanged. What follows it is the per-viewer resolution and
/// the CITATION (the cited receipt + finalized flag of the verified read) — a dated,
/// checkable fact, in place of the balance snapshot the old `format!` baked in and
/// which rotted on the source's very next turn.
pub fn transclusion_line(uri: &DreggUri, status: &ResolveStatus) -> String {
    match status {
        ResolveStatus::Resolved {
            receipt,
            commitment,
            visible_affordances,
            declared_affordances,
        } => format!(
            "{{transclude {} · visible: {visible_affordances} of {declared_affordances} \
             affordances · surface {commitment} · receipt {receipt} · finalized}}",
            uri.to_uri_string()
        ),
        ResolveStatus::Darkened {
            receipt,
            commitment,
        } => format!(
            "{{transclude {} · DARKENED: content withheld · surface {commitment} · \
             receipt {receipt} · finalized}}",
            uri.to_uri_string()
        ),
        // An unresolvable read never becomes a line (the caller refuses first); the arm
        // exists so this function is total, and it renders the refusal honestly rather
        // than a plausible-looking quote.
        ResolveStatus::Unresolvable { reason } => format!(
            "{{transclude {} · UNRESOLVABLE: {reason} · no embed}}",
            uri.to_uri_string()
        ),
    }
}

/// **The viewing user's membrane over `src`** — built from their REAL capabilities.
///
/// The membrane's held authority is [`held_rights`]; the projection the embed runs is
/// `(held) ∧ (lineage)` through the genuine [`Membrane::project`] lattice, so it can
/// never exceed either.
pub fn viewer_membrane(world: &World, viewer: CellId, src: CellId) -> Membrane {
    Membrane::new(SurfaceCapability::root(
        viewer,
        held_rights(world, viewer, src),
    ))
}

/// **The authority `viewer` really holds over `src`**, read off the live ledger:
///
/// * the viewer IS the source → [`AuthRequired::None`], the root authority a cell holds
///   over itself;
/// * the viewer's c-list carries a live [`dregg_cell::CapabilityRef`] targeting `src` →
///   EXACTLY that grant's `permissions` (the same field the executor's own gate reads;
///   a frozen `Impossible` grant is skipped, matching
///   [`dregg_cell::CapabilitySet::has_access`]);
/// * otherwise → [`AuthRequired::Signature`], the bare authenticated reader: they can
///   prove they are themselves and nothing more. This is the tier-1 of the canonical
///   `Signature ⊂ Either ⊂ None` chain, so a capless reader reaches `view` and no more.
pub fn held_rights(world: &World, viewer: CellId, src: CellId) -> AuthRequired {
    if viewer == src {
        return AuthRequired::None;
    }
    let held = world.ledger().get(&viewer).and_then(|c| {
        c.capabilities
            .iter()
            .find(|r| r.target == src && r.permissions != AuthRequired::Impossible)
            .map(|r| r.permissions.clone())
    });
    held.unwrap_or(AuthRequired::Signature)
}

/// **The authority the source cell's embed is SERVED under** — the lineage ceiling.
///
/// A LIVE cell serves at [`LIVE_LINEAGE_RIGHTS`]. A cell that is no longer live (sealed
/// / migrated / destroyed / archived) serves at [`AuthRequired::Impossible`]: its
/// surface confers nothing, so the embed keeps its citation and shows no content. That
/// distinction is read off committed lifecycle state, not asserted.
pub fn lineage_rights(world: &World, src: CellId) -> AuthRequired {
    match world.ledger().get(&src).map(|c| &c.lifecycle) {
        Some(CellLifecycle::Live) => LIVE_LINEAGE_RIGHTS,
        Some(_) => AuthRequired::Impossible,
        // Unreachable on the transclude path (the ledger gate ran first); a cell that
        // vanished between the two reads confers nothing.
        None => AuthRequired::Impossible,
    }
}

/// **The source cell's committed surface, as published bytes.**
///
/// A canonical, domain-separated encoding of the cell's COMMITTED state — its
/// content-addressed id, its balance, its nonce, its lifecycle tag and its umem
/// `heap_root` (the document boundary the desktop already treats as the commitment).
/// `publish_as` hashes exactly these bytes into the origin cell's slot-0 content
/// commitment, so the `dregg://` content address is a function of live committed state:
/// a source that advances re-publishes to a DIFFERENT commitment and therefore a
/// different serve receipt.
pub fn committed_surface_bytes(cell: &Cell) -> Vec<u8> {
    let mut out = Vec::with_capacity(128);
    out.extend_from_slice(b"dregg-desktop-docuverse-surface-v1\0");
    out.extend_from_slice(&cell.id().0);
    out.extend_from_slice(&cell.state.balance().to_le_bytes());
    out.extend_from_slice(&cell.state.nonce().to_le_bytes());
    out.push(lifecycle_tag(&cell.lifecycle));
    out.extend_from_slice(&cell.state.heap_root.to_bytes32());
    out
}

/// A stable one-byte tag for a cell's lifecycle (part of the published surface bytes).
fn lifecycle_tag(life: &CellLifecycle) -> u8 {
    match life {
        CellLifecycle::Live => 0,
        CellLifecycle::Sealed { .. } => 1,
        CellLifecycle::Migrated { .. } => 2,
        CellLifecycle::Destroyed { .. } => 3,
        CellLifecycle::Archived { .. } => 4,
    }
}

/// **The affordance surface a cell publishes** — the canonical doc-cell surface
/// `{view, comment, edit, admin}` on the three-tier chain `Signature ⊂ Either ⊂ None`,
/// each carrying a REAL [`Effect`] template over `source` (the turn the executor would
/// actually run). This is the surface `web_cells.rs`, `cell_transclusion.rs` and
/// `link_paste.rs` all declare — one shape across the docuverse, not a parallel one.
///
/// `viewer` is the grantee an `admin` grant would target (so the template names real
/// cells on both ends). See the module note for why this is NOT derived from the cell's
/// committed [`dregg_cell::Permissions`].
pub fn declared_surface_of(source: CellId, viewer: CellId) -> AffordanceSurface {
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
            set_field(source),
        ))
        .declare(CellAffordance::new(
            "admin",
            Requirement::Root,
            grant_cap(source, viewer),
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
fn set_field(cell: CellId) -> Effect {
    Effect::SetField {
        cell,
        index: 1,
        value: [7u8; 32],
    }
}

/// An admin grant hands out a capability — a real [`Effect::GrantCapability`] turn.
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::{demo_world, make_open_cell, World};

    /// A cell id that names nothing on any ledger — the forger's 32 bytes.
    fn absent() -> CellId {
        CellId::from_bytes([0xAB; 32])
    }

    // ── (1) THE ANTI-FORGE TOOTH ────────────────────────────────────────────────
    // An id the World does not hold never becomes a `dregg://` origin, and therefore
    // never becomes a transclusion. NOTHING is returned that a document could render.
    #[test]
    fn an_id_the_world_does_not_hold_is_never_published_and_never_transcludes() {
        let (world, [_treasury, _service, user]) = demo_world();
        let mut dv = Docuverse::new();

        assert_eq!(
            dv.publish_live(&world, absent()),
            None,
            "an absent id must not become a dregg:// origin"
        );
        match dv.transclude(&world, user, absent(), user) {
            Err(TranscludeRefusal::NotALiveCell { cell }) => assert_eq!(cell, absent()),
            other => panic!(
                "an absent id must be REFUSED, never rendered; got {:?}",
                other.map(|t| t.line)
            ),
        }

        // And the refusal is narrated (the desktop shows it, never a silent no-op).
        let n = TranscludeRefusal::NotALiveCell { cell: absent() }.narration();
        assert!(n.contains("REFUSED"), "the refusal names itself: {n}");
        // …and it mints no ADDRESS: the narration explains that there is no dregg://
        // origin, it never renders one. (The full 64-hex anchor is what a document line
        // carries and what `parse_transclusion_ref` would resolve; a refusal has none.)
        let forged_hex: String = absent().0.iter().map(|b| format!("{b:02x}")).collect();
        assert!(
            !n.contains(&forged_hex),
            "a refusal must not render the forged id as an address: {n}"
        );
    }

    // ── (2) A LIVE CELL TRANSCLUDES THROUGH THE VERIFIED READ ───────────────────
    #[test]
    fn a_live_cell_transcludes_to_a_receipt_pinned_per_viewer_embed() {
        let (world, [treasury, _service, user]) = demo_world();
        let mut dv = Docuverse::new();

        let t = dv
            .transclude(&world, user, treasury, user)
            .expect("a live cell of this World transcludes");

        // The citation is real: the finalized read carried a content commitment and a
        // receipt, and the federation attested it.
        assert!(t.provenance.finalized, "the cited read is finalized");
        assert_ne!(
            t.provenance.receipt_hash, [0u8; 32],
            "a real serve receipt is cited"
        );
        assert_ne!(
            t.provenance.content_hash, [0u8; 32],
            "a real surface commitment is cited"
        );

        // The line carries the content-addressed origin AND the citation.
        let hex: String = treasury.0.iter().map(|b| format!("{b:02x}")).collect();
        assert!(
            t.line.contains(&format!("dregg://{hex}")),
            "the line names the source's content-addressed origin: {}",
            t.line
        );
        assert!(t.line.contains("receipt"), "the line cites a receipt");
        // …and NOT a balance snapshot (the thing that used to rot).
        assert!(
            !t.line.contains("balance"),
            "the line must not bake a rotting balance: {}",
            t.line
        );
    }

    // ── (3) THE PUBLISHED COMMITMENT TRACKS LIVE COMMITTED STATE ────────────────
    // The old line's "balance 500" was a snapshot in prose. The new citation is a
    // commitment: advance the source and the cited receipt MOVES, so a reader can tell
    // the quote is dated rather than silently stale.
    #[test]
    fn advancing_the_source_moves_the_cited_receipt() {
        let (mut world, [treasury, _service, user]) = demo_world();
        let mut dv = Docuverse::new();

        let before = dv
            .transclude(&world, user, treasury, user)
            .expect("transcludes")
            .provenance;

        // A REAL verified turn on the source (the executor's own transfer path).
        let turn = world.turn(
            treasury,
            vec![Effect::Transfer {
                from: treasury,
                to: user,
                amount: 7,
            }],
        );
        assert!(
            world.commit_turn(turn).is_committed(),
            "the source really advanced"
        );

        let after = dv
            .transclude(&world, user, treasury, user)
            .expect("transcludes")
            .provenance;

        assert_ne!(
            before.content_hash, after.content_hash,
            "an advanced source publishes a NEW surface commitment"
        );
        assert_ne!(
            before.receipt_hash, after.receipt_hash,
            "…and therefore cites a NEW serve receipt"
        );
    }

    // ── (4) THE MEMBRANE IS THE VIEWER'S REAL CAPS ──────────────────────────────
    // Two viewers, one source, DIFFERENT embeds — and the difference is a real c-list
    // read, not a parameter. `service` is born holding a genuine capability over `user`
    // (`World::genesis_cell_with_cap`); `treasury` holds none.
    #[test]
    fn two_viewers_get_different_embeds_of_the_same_cell_from_their_real_caps() {
        let (world, [treasury, service, user]) = demo_world();

        // The premise, read off the live ledger (not assumed).
        assert!(
            world
                .ledger()
                .get(&service)
                .expect("service cell")
                .capabilities
                .has_access(&user),
            "the service really holds a capability over the user cell"
        );
        assert!(
            !world
                .ledger()
                .get(&treasury)
                .expect("treasury cell")
                .capabilities
                .has_access(&user),
            "the treasury really holds none"
        );

        assert_eq!(
            held_rights(&world, service, user),
            AuthRequired::None,
            "the cap holder's authority IS the granted one"
        );
        assert_eq!(
            held_rights(&world, treasury, user),
            AuthRequired::Signature,
            "a capless reader is the bare authenticated reader"
        );

        let mut dv = Docuverse::new();
        let by_service = dv
            .transclude(&world, service, user, service)
            .expect("transcludes");
        let by_treasury = dv
            .transclude(&world, treasury, user, treasury)
            .expect("transcludes");

        let (svc_visible, tre_visible) = match (&by_service.status, &by_treasury.status) {
            (
                ResolveStatus::Resolved {
                    visible_affordances: a,
                    ..
                },
                ResolveStatus::Resolved {
                    visible_affordances: b,
                    ..
                },
            ) => (*a, *b),
            other => panic!("both readers reach the embed, got {other:?}"),
        };
        assert!(
            svc_visible > tre_visible,
            "the capability holder sees MORE of the embed ({svc_visible}) than the bare \
             reader ({tre_visible})"
        );
        assert_eq!(tre_visible, 1, "the bare reader sees `view` alone");
        assert_ne!(
            by_service.line, by_treasury.line,
            "the SAME cell renders differently for two readers — the embed is a frustum"
        );
    }

    // ── (5) DARKENING IS REACHABLE FROM A REAL CAPABILITY ───────────────────────
    // A reader whose real grant is a `Custom { vk_hash }` predicate is INCOMPARABLE
    // with the embed's `Either` lineage — no view both admit — so the embed DARKENS:
    // the citation survives, the content is withheld, never forged. This is the desktop
    // path reaching the same state `link_paste`'s
    // `an_under_capped_viewer_gets_a_darkened_embed_citation_present_content_withheld`
    // pins, driven by a capability that really sits in a cell's c-list.
    #[test]
    fn an_incomparably_capped_reader_gets_a_darkened_embed_citation_kept() {
        let mut world = World::new();
        let source = world.genesis_install(make_open_cell(0x51, 100));

        // A reader whose c-list carries a REAL Custom-predicate grant over the source.
        let mut reader_cell = make_open_cell(0x52, 10);
        reader_cell
            .capabilities
            .grant(source, AuthRequired::Custom { vk_hash: [9u8; 32] })
            .expect("fresh c-list has a free slot");
        let reader = world.genesis_install(reader_cell);

        assert_eq!(
            held_rights(&world, reader, source),
            AuthRequired::Custom { vk_hash: [9u8; 32] },
            "the held authority IS the c-list's grant"
        );

        let mut dv = Docuverse::new();
        let t = dv
            .transclude(&world, reader, source, reader)
            .expect("the embed resolves — darkening is a PROJECTION outcome, not a refusal");

        match &t.status {
            ResolveStatus::Darkened {
                receipt,
                commitment,
            } => {
                assert!(!receipt.is_empty(), "the citation survives darkening");
                assert!(!commitment.is_empty(), "…and so does the commitment");
            }
            other => panic!("an incomparably-capped reader must darken, got {other:?}"),
        }
        assert!(
            t.line.contains("DARKENED"),
            "the document says so plainly: {}",
            t.line
        );
        assert!(
            t.line.contains("receipt"),
            "…while still carrying the citation: {}",
            t.line
        );
        // The provenance survives on the transclusion itself (withheld, never forged).
        assert!(t.provenance.finalized);
    }

    // ── (6) A NON-LIVE SOURCE SERVES NOTHING ────────────────────────────────────
    // The lineage is read off committed lifecycle: a sealed cell's surface confers
    // nothing, so its embed keeps the citation and shows zero affordances.
    #[test]
    fn a_sealed_source_serves_a_citation_and_no_content() {
        let mut world = World::new();
        let mut cell = make_open_cell(0x61, 50);
        cell.lifecycle = CellLifecycle::Sealed {
            reason_hash: [1u8; 32],
            sealed_at: 1,
        };
        let sealed = world.genesis_install(cell);
        let reader = world.genesis_install(make_open_cell(0x62, 5));

        assert_eq!(lineage_rights(&world, sealed), AuthRequired::Impossible);

        let mut dv = Docuverse::new();
        let t = dv
            .transclude(&world, reader, sealed, reader)
            .expect("a sealed cell is still a cell — it transcludes, at zero authority");
        match &t.status {
            ResolveStatus::Resolved {
                visible_affordances,
                ..
            } => assert_eq!(
                *visible_affordances, 0,
                "a sealed source's surface confers nothing"
            ),
            ResolveStatus::Darkened { .. } => { /* also an honest withholding */ }
            other => panic!("a sealed cell still cites its read, got {other:?}"),
        }
        assert!(t.provenance.finalized, "the citation survives");
    }

    // ── (7) THE LINE STILL PARSES BACK ──────────────────────────────────────────
    // The two-way link inversion reads the `dregg://<64-hex>` head. Whatever the
    // per-viewer body says, the anchor must round-trip — otherwise the backlink graph
    // silently empties.
    #[test]
    fn every_rendered_line_carries_a_parseable_dregg_anchor() {
        let (world, [treasury, service, user]) = demo_world();
        let mut dv = Docuverse::new();
        for (src, viewer) in [(treasury, user), (user, service), (service, treasury)] {
            let t = dv
                .transclude(&world, user, src, viewer)
                .expect("transcludes");
            let after = t
                .line
                .split("dregg://")
                .nth(1)
                .expect("the line carries a dregg:// anchor");
            let hex: String = after
                .chars()
                .take_while(|c| c.is_ascii_hexdigit())
                .collect();
            assert_eq!(
                hex.len(),
                64,
                "the anchor is a full 64-hex cell id: {}",
                t.line
            );
            let expect: String = src.0.iter().map(|b| format!("{b:02x}")).collect();
            assert_eq!(hex, expect, "…and it is the SOURCE cell's id");
        }
    }
}
