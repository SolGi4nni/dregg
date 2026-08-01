//! **EVERY COMPOSER GESTURE HAS A REAL ENTRY POINT — NOT JUST `embed`.**
//!
//! A previous pass gave ONE of the five composition gestures a user-reachable path
//! (`ActionKind::ComposeInto` → `actuate` → `compose_embed`) and said so in its own
//! residual: `compose_embed_at`, `compose_reorder`, `compose_set_role` and
//! `compose_remove` still had **exactly one caller each — their own `bake_compose_*`
//! test hook**. A gesture only the test suite can perform is a gesture the shipped
//! desktop cannot perform, however green its unit tests are.
//!
//! THE GATE: drive all four the way a user does — right-click the cell (the REAL
//! `actions_for` menu), find the row among the offered entries, and click it through the
//! same dispatch the rendered menu row runs. **There is no `bake_compose_*` anywhere in
//! this file** (grep it): every state change asserted below was caused by a menu click.
//! If the menu does not OFFER a gesture, or the click does not reach the composer, this
//! fails. (The only thing standing in for the user is the mouse hit-test, which a
//! headless window cannot perform.)
//!
//! It also pins the composer's real algebra, because the menu must not lie about it:
//! two children placed AT THE HEAD are a layout **fork** (an antichain — neither leads),
//! and it takes an **order** gesture to collapse it into the author's chain. A menu that
//! offered "compose at the head" without offering the order that resolves it would put a
//! user in a state they cannot get out of — which is why the enablement of the order /
//! re-role / remove rows is read off the composer's own `live_atom`, not off the composed
//! walk (a forked child is absent from the walk and is exactly who needs ordering).
//!
//! Run: `cd starbridge-v2 && cargo test --features native-full \
//!   --test deos_desktop_every_composer_gesture_is_reachable -- --nocapture`

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

/// The menu entry index whose label contains `needle`, if any.
fn entry_with(entries: &[(String, bool)], needle: &str) -> Option<usize> {
    entries.iter().position(|(l, _)| l.contains(needle))
}

/// `cell`'s right-click menu entries (the real `actions_for` output).
fn menu_of(
    cx: &mut HeadlessAppContext,
    desk: &gpui::Entity<DeosDesktop>,
    cell: CellId,
) -> Vec<(String, bool)> {
    desk.update(cx, |d, _cx| d.bake_open_menu(cell, 40.0, 40.0));
    cx.update(|cx| desk.read(cx).bake_menu_entries())
}

/// Right-click `cell`, find the entry containing `needle`, assert it is LIVE, and click
/// it through the shipped dispatch. Panics (printing the whole offered menu) if the
/// gesture is not offered — "no entry point" is exactly what this test exists to catch.
fn click_menu(
    cx: &mut HeadlessAppContext,
    desk: &gpui::Entity<DeosDesktop>,
    cell: CellId,
    needle: &str,
) -> String {
    let entries = menu_of(cx, desk, cell);
    let idx = entry_with(&entries, needle).unwrap_or_else(|| {
        panic!(
            "the cell menu must OFFER a gesture matching {needle:?}; it offered: {:?}",
            entries.iter().map(|(l, _)| l).collect::<Vec<_>>()
        )
    });
    assert!(
        entries[idx].1,
        "the {needle:?} entry must be LIVE here, not dimmed: {:?}",
        entries[idx]
    );
    let label = entries[idx].0.clone();
    let clicked = desk.update(cx, |d, _cx| d.bake_menu_click(idx));
    cx.run_until_parked();
    assert!(clicked, "the live {needle:?} entry must actuate");
    println!("clicked: {label:?}");
    label
}

/// Stand up a headless desktop over `demo_world`, seated on the `user` anchor, with a
/// document editor open on `user` carrying one line of prose.
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
    let layout_path = std::env::temp_dir().join(format!(
        "deos-composer-all-{tag}-{}.json",
        std::process::id()
    ));
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

    desk.update(&mut cx, |d, _cx| {
        d.bake_open_doc(user);
        d.bake_edit_doc(user, "A document composed of live cells.\n");
    });
    cx.run_until_parked();

    (shared, anchors, cx, desk, layout_path)
}

// ─────────────────────────────────────────────────────────────────────────────
// (1) EMBED-AT · ORDER — the fork placement and the gesture that resolves it, both
//     clicked off the real menu.
// ─────────────────────────────────────────────────────────────────────────────
#[test]
fn the_fork_placement_and_the_order_that_resolves_it_are_both_clickable() {
    let (shared, [treasury, service, user], mut cx, desk, layout_path) = desktop("fork");

    // ── (0) BEFORE ANYTHING IS COMPOSED: the child-gestures are still TAUGHT, dimmed. ──
    //    A verb that only appears once you have already discovered it teaches nobody.
    let cold = menu_of(&mut cx, &desk, treasury);
    let cold_idx = entry_with(&cold, "Order · re-role · remove").unwrap_or_else(|| {
        panic!(
            "a cell that is not yet composed into the open document must still be TAUGHT \
             the order/re-role/remove verbs (dimmed); the menu offered: {:?}",
            cold.iter().map(|(l, _)| l).collect::<Vec<_>>()
        )
    });
    assert!(
        !cold[cold_idx].1,
        "a cell that is not a child of the composition cannot be ordered/re-roled/removed \
         — the row must be DIMMED, not live: {:?}",
        cold[cold_idx]
    );
    assert!(
        !desk.update(&mut cx, |d, _cx| d.bake_menu_click(cold_idx)),
        "a dimmed row must not actuate"
    );

    // ── (1) EMBED-AT ── place treasury AT THE HEAD (the fork placement, which does NOT
    //     advance the append tail — the gesture `compose_embed_at` performs).
    let h0 = shared.borrow().height();
    click_menu(&mut cx, &desk, treasury, "at the head");
    let kids = cx.update(|cx| desk.read(cx).bake_composed_children(user));
    assert_eq!(
        kids.iter().map(|k| k.0).collect::<Vec<_>>(),
        vec![treasury],
        "one child at the head composes into the document: {kids:?}"
    );
    assert!(
        shared.borrow().height() > h0,
        "an embed-at is a REAL verified turn on the document cell"
    );

    // ── (2) EMBED-AT again ── service at the SAME anchor: a layout FORK (an antichain,
    //     two siblings with no order between them — neither leads the walk).
    click_menu(&mut cx, &desk, service, "at the head");
    assert!(
        cx.update(|cx| desk.read(cx).bake_composed_children(user))
            .is_empty(),
        "two children placed at ONE anchor are a fork; the composed walk has no linear \
         reading until an order gesture resolves it"
    );

    // ── (3) ORDER ── the menu must still offer the gesture that gets the user OUT of the
    //     fork — naming the sibling it orders against — even though the forked child is
    //     absent from the composed walk.
    let h2 = shared.borrow().height();
    click_menu(&mut cx, &desk, service, "Order after");
    let order: Vec<CellId> = cx
        .update(|cx| desk.read(cx).bake_composed_children(user))
        .iter()
        .map(|k| k.0)
        .collect();
    assert_eq!(
        order,
        vec![treasury, service],
        "the clicked order gesture collapsed the fork into the author's chain"
    );
    assert!(
        shared.borrow().height() > h2,
        "the reorder is itself a receipted turn"
    );

    let _ = std::fs::remove_file(&layout_path);
    println!("OK embed-at + order actuated from the real right-click menu");
}

// ─────────────────────────────────────────────────────────────────────────────
// (2) SET-ROLE · REMOVE — on an appended child, both clicked off the real menu, and
//     the menu follows the composition's state back down again.
// ─────────────────────────────────────────────────────────────────────────────
#[test]
fn re_roling_and_removing_a_composed_child_are_both_clickable() {
    let (shared, [treasury, _service, user], mut cx, desk, layout_path) = desktop("role");

    // Compose treasury in as a Section (the entry point that already existed).
    click_menu(&mut cx, &desk, treasury, "Compose into doc");
    let kids = cx.update(|cx| desk.read(cx).bake_composed_children(user));
    assert_eq!(
        kids.iter().map(|k| (k.0, k.1)).collect::<Vec<_>>(),
        vec![(treasury, Role::Section)],
        "the child is composed in, in the role the entry names: {kids:?}"
    );

    // ── SET-ROLE ── the citation is preserved, only the role reads back changed.
    let h0 = shared.borrow().height();
    click_menu(&mut cx, &desk, treasury, "Set role: Figure");
    let kids = cx.update(|cx| desk.read(cx).bake_composed_children(user));
    assert_eq!(
        kids.iter().map(|k| (k.0, k.1)).collect::<Vec<_>>(),
        vec![(treasury, Role::Figure)],
        "the clicked re-role changed the role and kept the citation: {kids:?}"
    );
    assert!(
        shared.borrow().height() > h0,
        "the re-role is itself a receipted turn"
    );

    // The menu now offers the roles it is NOT in, and not the one it is.
    let m = menu_of(&mut cx, &desk, treasury);
    assert!(
        entry_with(&m, "Set role: Section").is_some(),
        "the role it left is offered again: {m:?}"
    );
    assert!(
        entry_with(&m, "Set role: Figure").is_none(),
        "the role it already plays is not offered as a change: {m:?}"
    );

    // ── REMOVE ── tombstoned: gone from the live render, RETAINED in the roster with
    //     its provenance.
    let h1 = shared.borrow().height();
    click_menu(&mut cx, &desk, treasury, "Remove from doc");
    let kids = cx.update(|cx| desk.read(cx).bake_composed_children(user));
    assert!(
        !kids.iter().any(|k| k.0 == treasury),
        "the clicked remove drops the child from the live render: {kids:?}"
    );
    let roster = cx.update(|cx| desk.read(cx).bake_composition_roster(user));
    let tomb = roster
        .iter()
        .find(|k| k.0 == treasury)
        .expect("the removed child is RETAINED in the roster (tombstoned, not lost)");
    assert!(!tomb.3, "…marked not-live");
    assert!(
        shared.borrow().height() > h1,
        "the remove is itself a receipted turn"
    );

    // ── AND THE MENU FOLLOWS THE STATE BACK ── with the child tombstoned the
    //     child-gestures dim again and the placement gesture comes back live. The menu
    //     is derived from the composition, not from a flag someone remembered to set.
    let after = menu_of(&mut cx, &desk, treasury);
    let back = entry_with(&after, "Order · re-role · remove")
        .unwrap_or_else(|| panic!("the verbs stay taught: {after:?}"));
    assert!(
        !after[back].1,
        "a tombstoned child is no longer orderable/re-roleable/removable: {:?}",
        after[back]
    );
    let head = entry_with(&after, "at the head").expect("the placement gesture is still offered");
    assert!(
        after[head].1,
        "a tombstoned child can be composed in again: {:?}",
        after[head]
    );

    let _ = std::fs::remove_file(&layout_path);
    println!("OK set-role + remove actuated from the real right-click menu");
}
