//! THE FELT-LIVENESS BAR: a turn on ONE `(cell, slot)` re-renders ONLY its bound
//! element — not the whole tree.
//!
//! This is the consumer side of deos-js's `signals.rs` `BindingRegistry` (the 8-green
//! `(cell, slot) → bindings` reverse index): the renderer (`AppletView`) registers each
//! `bind` node on its source, and a committed turn folds the touched slots through
//! `invalidate`, re-reading ONLY the dirty bindings into the value cache.
//!
//! A two-binding scene proves the fine-grained win directly (no gpui window needed —
//! `AppletView` constructs gpui-free; only `render` paints): two `bind` nodes on two
//! different slots of the applet's cell, a turn that writes ONLY slot A, and the
//! assertion that the turn dirtied binding A but NOT binding B — and that binding B's
//! cached value never re-read.

use std::cell::RefCell;
use std::rc::Rc;

use deos_js::applet::{pack_u64, Affordance, Applet};
use deos_js::signals::BindingId;
use dregg_cell::AuthRequired;

use deos_view::tree::ViewNode;
use deos_view::AppletView;

/// A two-slot applet: slot 0 = "a", slot 1 = "b". `incA` adds `arg` to slot 0 ONLY
/// (slot 1 untouched); `incB` adds to slot 1 only. Both Signature-gated and held.
fn two_slot_applet(seed: u8) -> Applet {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    let inc_a = Affordance {
        name: "incA".into(),
        required: AuthRequired::Signature,
        apply: Box::new(|model, arg| {
            let cur = model.field_u64(0);
            vec![(0usize, pack_u64(cur + arg.max(0) as u64))]
        }),
    };
    let inc_b = Affordance {
        name: "incB".into(),
        required: AuthRequired::Signature,
        apply: Box::new(|model, arg| {
            let cur = model.field_u64(1);
            vec![(1usize, pack_u64(cur + arg.max(0) as u64))]
        }),
    };
    Applet::mint(
        pk,
        [0u8; 32],
        &[(0usize, pack_u64(10)), (1usize, pack_u64(20))],
        vec![inc_a, inc_b],
        AuthRequired::Signature,
    )
}

/// The view-tree (built directly as `ViewNode`, the same shape the JS engine produces):
/// a vstack of two binds — binding 0 reads slot 0, binding 1 reads slot 1.
fn two_bind_tree() -> ViewNode {
    ViewNode::VStack(vec![
        ViewNode::Text("two binds".into()),
        ViewNode::Bind {
            slot: 0,
            label: "a: ".into(),
        },
        ViewNode::Bind {
            slot: 1,
            label: "b: ".into(),
        },
    ])
}

#[test]
fn a_turn_on_slot_a_dirties_only_binding_a() {
    let applet = two_slot_applet(0x7A);
    let shared = Rc::new(RefCell::new(applet));
    let view = AppletView::new(shared.clone(), two_bind_tree());

    // Two `bind` nodes were registered (one BindingId each).
    assert_eq!(view.binding_count(), 2, "two binds registered");

    // Prime the cache (what the first paint does): both bindings read their live slots.
    // BindingId(0) reads slot 0 (=10); BindingId(1) reads slot 1 (=20).
    // We seed the cache via on_committed_turn over BOTH slots so the values are present
    // exactly as a first paint would lazily fill them.
    let _seed = view.on_committed_turn(&[0, 1]);
    assert_eq!(view.cached(BindingId(0)), Some(10), "binding A primed to 10");
    assert_eq!(view.cached(BindingId(1)), Some(20), "binding B primed to 20");

    // ── Fire a REAL verified turn that writes ONLY slot 0 (the +5 on "a") ────────────
    shared
        .borrow_mut()
        .fire("incA", 5)
        .expect("incA fires a verified turn");
    assert_eq!(shared.borrow().get_u64(0), 15, "slot 0 advanced 10 -> 15");
    assert_eq!(shared.borrow().get_u64(1), 20, "slot 1 untouched");

    // ── THE FINE-GRAINED HOOK: the turn touched only slot 0 ──────────────────────────
    let dirty = view.on_committed_turn(&[0]);

    // THE BAR: a turn on slot A re-evaluated ONLY binding A — NOT binding B.
    assert_eq!(
        dirty,
        vec![BindingId(0)],
        "the dirty set is EXACTLY binding A (slot-0 bind), not the whole tree"
    );
    assert_eq!(
        view.last_dirty(),
        vec![BindingId(0)],
        "last_dirty reflects only the touched binding"
    );

    // Binding A re-read the live ledger (10 -> 15); binding B kept its cached value (20),
    // never re-read — the fine-grained re-render, not a world repaint.
    assert_eq!(
        view.cached(BindingId(0)),
        Some(15),
        "binding A re-read the new value"
    );
    assert_eq!(
        view.cached(BindingId(1)),
        Some(20),
        "binding B was NOT re-evaluated (still its cached value)"
    );
}

/// A turn touching a slot NO bind reads dirties nothing — the whole view stays still.
#[test]
fn a_turn_on_an_unbound_slot_dirties_nothing() {
    let applet = two_slot_applet(0x7B);
    let shared = Rc::new(RefCell::new(applet));
    let view = AppletView::new(shared.clone(), two_bind_tree());

    view.on_committed_turn(&[0, 1]); // prime

    // Slot 7 is read by no bind node.
    let dirty = view.on_committed_turn(&[7]);
    assert!(
        dirty.is_empty(),
        "a turn on an unbound slot re-renders nothing"
    );
    // Both cached values are intact.
    assert_eq!(view.cached(BindingId(0)), Some(10));
    assert_eq!(view.cached(BindingId(1)), Some(20));
}
