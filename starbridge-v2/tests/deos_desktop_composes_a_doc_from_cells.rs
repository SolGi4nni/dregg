//! **COMPOSE A DOCUMENT *FROM CELLS*, BY HAND — AND REFUSE A CELL THAT IS NOT THERE.**
//!
//! `starbridge_v2::document_composer` is hyperdreggmedia authoring surface #7
//! (`docs/deos/HYPERDREGGMEDIA-NOTES.md` §6): add an embed, reorder children, remove
//! one, set a child's role — each a real `dregg_doc::composition` patch
//! (`Op::Embed` / `Op::Order` / `Op::Remove`) on the document cell's layout. 776 lines,
//! 6 green unit tests, and — until this test — **zero callers**: a complete authoring
//! surface with no entry point and no body in the desktop.
//!
//! This drives every gesture through the LIVE `DeosDesktop` over the real `World` and
//! asserts the thing a unit test structurally cannot: that a composition gesture leaves
//! a **receipt on the chain and a citation in the committed cell heap**.
//!
//! THE TOOTH: the composer's `ChildCellId` is an opaque integer — `add_embed` will
//! happily place ANY value, so a hand-authored embed of a cell that does not exist
//! renders exactly like a real one (the same defect the transclude gesture had, in the
//! embed algebra instead of the quote algebra). The desktop's compose therefore runs the
//! SAME ledger gate `docuverse::publish_live` runs: an id the live World does not hold
//! is never embedded, the layout is left exactly as it was, no patch, no heap write, no
//! revision turn, and the refusal is narrated.
//!
//! Run: `cd starbridge-v2 && cargo test --features native-full \
//!   --test deos_desktop_composes_a_doc_from_cells -- --nocapture`

#![cfg(all(feature = "gpui-ui", feature = "embedded-executor"))]

use std::borrow::Cow;
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use gpui::{px, size, AppContext, HeadlessAppContext, PlatformTextSystem};
use gpui_wgpu::CosmicTextSystem;

use dregg_types::CellId;
use starbridge_v2::deos_desktop::DeosDesktop;
use starbridge_v2::document_composer::Role;
use starbridge_v2::world::{demo_world, World};

static LILEX: &[u8] = include_bytes!("../assets/fonts/Lilex-Regular.ttf");
static IBM_PLEX: &[u8] = include_bytes!("../assets/fonts/IBMPlexSans-Regular.ttf");

/// A cell id that names NOTHING on the live ledger — 32 well-formed bytes a forger
/// picked. The id space is not a permission system; being a `CellId` is not evidence
/// of being a cell.
fn forged_id() -> CellId {
    CellId::from_bytes([0xCD; 32])
}

/// The full 64-hex rendering of a cell id — what a composed citation must carry (the
/// same anchor width the transclude line uses).
fn hex(c: &CellId) -> String {
    c.0.iter().map(|b| format!("{b:02x}")).collect()
}

/// Read prose back out of a cell's committed **umem-heap** (`heap_map`, collection
/// `dregg_doc::COLL_TEXT`) — the committed truth, not the window's buffer.
fn read_doc(w: &World, cell: &CellId) -> Option<String> {
    let state = &w.ledger().get(cell)?.state;
    dregg_doc::text_from_heap(&state.heap_map)
}

/// Stand up a headless desktop over `demo_world`, seated on the `user` anchor.
/// Returns the shared world, the anchors, the app context and the desktop entity.
#[allow(clippy::type_complexity)]
fn desktop(
    tag: &str,
) -> (
    Rc<RefCell<World>>,
    [CellId; 3],
    HeadlessAppContext,
    gpui::Entity<DeosDesktop>,
    std::path::PathBuf,
) {
    let layout_path =
        std::env::temp_dir().join(format!("deos-compose-{tag}-{}.json", std::process::id()));
    let _ = std::fs::remove_file(&layout_path);

    let (world, anchors) = demo_world();
    let [_treasury, _service, user] = anchors;
    let shared = Rc::new(RefCell::new(world));

    let text_system: Arc<dyn PlatformTextSystem> =
        Arc::new(CosmicTextSystem::new_without_system_fonts("Lilex"));
    text_system
        .add_fonts(vec![Cow::Borrowed(LILEX), Cow::Borrowed(IBM_PLEX)])
        .expect("fonts");
    let mut cx = HeadlessAppContext::with_platform(text_system, Arc::new(()), || {
        gpui_platform::current_headless_renderer()
    });
    cx.update(gpui_component::init);

    let world_for_view = shared.clone();
    let lp = layout_path.clone();
    let desk_cell: Rc<RefCell<Option<gpui::Entity<DeosDesktop>>>> = Rc::new(RefCell::new(None));
    let desk_sink = desk_cell.clone();
    cx.open_window(size(px(900.), px(640.)), move |window, cx| {
        let view = cx.new(|cx| DeosDesktop::new(world_for_view, user, lp, window, cx));
        *desk_sink.borrow_mut() = Some(view.clone());
        cx.new(|cx| gpui_component::Root::new(gpui::AnyView::from(view), window, cx))
    })
    .expect("open the headless desktop window");
    cx.run_until_parked();
    let desk = desk_cell.borrow().clone().expect("desktop entity captured");

    (shared, anchors, cx, desk, layout_path)
}

// ─────────────────────────────────────────────────────────────────────────────
// (1) ADD · ROLE · REMOVE — each a receipted turn, each visible in the committed heap
// ─────────────────────────────────────────────────────────────────────────────
#[test]
fn composing_a_document_from_cells_lands_receipts_and_citations_in_the_committed_heap() {
    let (shared, [treasury, service, user], mut cx, desk, layout_path) = desktop("add");

    desk.update(&mut cx, |d, _cx| d.bake_open_doc(user));

    // ── THE FORGERY, FIRST ── an embed of a cell the World does not hold. Run before
    //    any real embed so a refusal cannot hide behind an earlier success.
    let h_before_forge = shared.borrow().height();
    let text_before_forge = read_doc(&shared.borrow(), &user).unwrap_or_default();
    let refused = desk.update(&mut cx, |d, _cx| {
        d.bake_compose_embed(user, forged_id(), Role::Section)
    });
    assert!(
        !refused,
        "an embed of an id the live ledger does not hold must be REFUSED"
    );
    assert!(
        cx.update(|cx| desk.read(cx).bake_composed_children(user))
            .is_empty(),
        "a refused embed places NO child in the layout"
    );
    assert_eq!(
        shared.borrow().height(),
        h_before_forge,
        "a refused embed must not commit a revision turn"
    );
    assert_eq!(
        read_doc(&shared.borrow(), &user).unwrap_or_default(),
        text_before_forge,
        "a refused embed must leave the committed heap EXACTLY as it was"
    );
    let narration = cx.update(|cx| desk.read(cx).bake_status_line());
    assert!(
        narration.to_ascii_lowercase().contains("refus"),
        "the desktop must narrate the refusal; the status bar said {narration:?}"
    );
    assert!(
        !narration.contains(&hex(&forged_id())),
        "a refusal must not render the forged id as a citation: {narration:?}"
    );

    // ── ADD ── a REAL live cell, placed as a Section.
    let h0 = shared.borrow().height();
    let ok = desk.update(&mut cx, |d, _cx| {
        d.bake_compose_embed(user, treasury, Role::Section)
    });
    assert!(ok, "a live cell of this World embeds");

    let kids = cx.update(|cx| desk.read(cx).bake_composed_children(user));
    assert_eq!(kids.len(), 1, "one live child: {kids:?}");
    assert_eq!(kids[0].0, treasury, "…and it is the cell that was embedded");
    assert_eq!(kids[0].1, Role::Section, "in the role it was placed in");
    assert!(kids[0].3, "live");

    // PROVENANCE: the child carries who placed it — the seated operator's author,
    // derived from the user anchor (a FACT off the layout, never a guess).
    let seated = u64::from_le_bytes(user.as_bytes()[..8].try_into().unwrap());
    assert_eq!(
        kids[0].2, seated,
        "the embed is attributed to the seated author"
    );

    // A REAL TURN LANDED — the document cell's revision advanced on the chain.
    let h1 = shared.borrow().height();
    assert!(
        h1 > h0,
        "an embed commits a real verified turn on the document cell ({h0} -> {h1})"
    );

    // THE CITATION IS IN THE COMMITTED HEAP — full 64-hex, plus the role. Read off
    // the ledger, not the window buffer: this is what a light client sees.
    let committed = read_doc(&shared.borrow(), &user).unwrap_or_default();
    assert!(
        committed.contains(&format!("dregg://{}", hex(&treasury))),
        "the composed embed's FULL-WIDTH citation is committed: {committed:?}"
    );
    assert!(
        committed.contains("Section"),
        "the role is committed with it: {committed:?}"
    );

    // ── ROLE ── re-role a second child; the citation survives, the role changes.
    desk.update(&mut cx, |d, _cx| {
        d.bake_compose_embed(user, service, Role::Figure)
    });
    assert_eq!(
        cx.update(|cx| desk.read(cx).bake_composed_children(user))
            .iter()
            .find(|k| k.0 == service)
            .map(|k| k.1),
        Some(Role::Figure)
    );
    let h2 = shared.borrow().height();
    let re_roled = desk.update(&mut cx, |d, _cx| {
        d.bake_compose_set_role(user, service, Role::Citation)
    });
    assert!(re_roled, "re-roling a live child succeeds");
    let kids = cx.update(|cx| desk.read(cx).bake_composed_children(user));
    let svc = kids
        .iter()
        .find(|k| k.0 == service)
        .expect("the child survives the re-role — its CITATION is preserved");
    assert_eq!(svc.1, Role::Citation, "the role reads back changed");
    assert_eq!(kids.len(), 2, "re-roled, not duplicated: {kids:?}");
    assert!(
        shared.borrow().height() > h2,
        "the re-role is itself a receipted turn"
    );
    let committed = read_doc(&shared.borrow(), &user).unwrap_or_default();
    assert!(
        committed.contains("Citation") && committed.contains(&format!("dregg://{}", hex(&service))),
        "the changed role and the preserved citation are BOTH committed: {committed:?}"
    );

    // ── REMOVE ── tombstoned, not lost: gone from the live render, RETAINED in the
    //    roster with its provenance — and the tombstone is a COMMITTED fact.
    let h3 = shared.borrow().height();
    let removed = desk.update(&mut cx, |d, _cx| d.bake_compose_remove(user, treasury));
    assert!(removed, "removing a live child succeeds");
    let kids = cx.update(|cx| desk.read(cx).bake_composed_children(user));
    assert!(
        !kids.iter().any(|k| k.0 == treasury),
        "the removed child drops off the live render: {kids:?}"
    );
    let roster = cx.update(|cx| desk.read(cx).bake_composition_roster(user));
    let tomb = roster
        .iter()
        .find(|k| k.0 == treasury)
        .expect("the removed child is RETAINED in the roster (tombstoned, not lost)");
    assert!(!tomb.3, "…marked not-live");
    assert_eq!(
        tomb.2, seated,
        "…and it keeps its provenance — gone-but-provenanced, never silently lost"
    );
    assert!(
        shared.borrow().height() > h3,
        "the remove is itself a receipted turn"
    );
    let committed = read_doc(&shared.borrow(), &user).unwrap_or_default();
    assert!(
        committed.contains(&hex(&treasury)),
        "the tombstoned child's citation SURVIVES in the committed heap (retained, \
         not deleted): {committed:?}"
    );

    let _ = std::fs::remove_file(&layout_path);
    println!("OK compose: add/role/remove each landed a turn; committed heap:\n{committed}");
}

// ─────────────────────────────────────────────────────────────────────────────
// (2) REORDER — a layout FORK (two siblings at one anchor, an antichain) collapses
//     into the author's chosen order, and the order is a COMMITTED fact.
// ─────────────────────────────────────────────────────────────────────────────
#[test]
fn a_reorder_resolves_a_layout_fork_and_commits_the_authors_chosen_order() {
    let (shared, [treasury, service, user], mut cx, desk, layout_path) = desktop("order");

    desk.update(&mut cx, |d, _cx| d.bake_open_doc(user));

    // Place BOTH at the head — a layout fork (no order between them). The composed
    // walk stops at the (empty) clean prefix: neither leads yet.
    desk.update(&mut cx, |d, _cx| {
        d.bake_compose_embed_at(user, treasury, None, Role::Section);
        d.bake_compose_embed_at(user, service, None, Role::Section);
    });
    assert!(
        cx.update(|cx| desk.read(cx).bake_composed_children(user))
            .is_empty(),
        "two siblings at one anchor are a FORK — an antichain, not a silent order"
    );

    // REORDER: constrain treasury before service. The fork collapses into a chain.
    let h0 = shared.borrow().height();
    let ok = desk.update(&mut cx, |d, _cx| {
        d.bake_compose_reorder(user, service, Some(treasury))
    });
    assert!(ok, "the reorder applies");
    let order: Vec<CellId> = cx
        .update(|cx| desk.read(cx).bake_composed_children(user))
        .iter()
        .map(|k| k.0)
        .collect();
    assert_eq!(
        order,
        vec![treasury, service],
        "the reorder resolved the fork into the author's order"
    );
    assert!(
        shared.borrow().height() > h0,
        "the reorder is itself a receipted turn"
    );

    // THE ORDER IS COMMITTED — the two citations appear in the chosen order in the
    // cell's heap, so the composed layout is a fact on the ledger, not window state.
    let committed = read_doc(&shared.borrow(), &user).unwrap_or_default();
    let ti = committed
        .find(&hex(&treasury))
        .expect("treasury cited in the committed heap");
    let si = committed
        .find(&hex(&service))
        .expect("service cited in the committed heap");
    assert!(
        ti < si,
        "the committed heap carries the chosen ORDER (treasury before service): {committed:?}"
    );

    let _ = std::fs::remove_file(&layout_path);
    println!("OK reorder: fork collapsed to the authored chain; committed:\n{committed}");
}
