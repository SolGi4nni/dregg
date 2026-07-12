//! **THE ONE GATE** — an actuation node's `enabled` from the FULL four-conjunct
//! membrane/reactive gate, NOT the `is_attenuation` frustum alone.
//!
//! `docs/SURFACE-ONE-GATE-FOUR-PLANES.md` (the load-bearing correction): the enabled
//! bit of an actuation affordance is a **4-conjunct** gate, and the repo's own Lean
//! (`Dregg2.Deos.Reactive`) proves the last three IRREDUCIBLE — forcing everything
//! through `is_attenuation` deletes banked proofs (the adversary's #1 finding):
//!
//! ```text
//!   enabled = is_attenuation ∧ disclosure ∧ transition ∧ window
//!             └───────────┬──────────┘   └──────────┬─────────┘
//!             project_membrane(viewer)          reactive_ok(ctx)
//!             (Viewer::membrane_shows)     (ReactiveAffordance transition + window)
//! ```
//!
//! - **is_attenuation** — `required ⊆ held`, the proven cap lattice
//!   ([`starbridge_web_surface::CellAffordance::authorized_for`]).
//! - **disclosure** — the per-viewer witness-graph permit bit
//!   ([`starbridge_web_surface::Viewer::permits`]); two viewers at EQUAL authority can
//!   see DISTINCT surfaces (the Lean `membrane_two_viewers_distinct`). Cap AND
//!   disclosure together are [`starbridge_web_surface::Viewer::membrane_shows`] =
//!   `project_membrane`'s per-affordance test.
//! - **transition** — the relational `pre(old) ∧ post(new) ∧ link(old,new)` gate that
//!   reads BOTH records ([`starbridge_web_surface::TransitionGate::transition_ok`]); a
//!   property of `new` alone can never witness it (the same-`new`-wrong-`old` fire is
//!   dark).
//! - **window** — the inclusive `[open, close]` deadline over the turn height
//!   ([`starbridge_web_surface::ReactiveAffordance::in_window`]).
//!
//! This module does NOT reduce the gate: [`reactive_membrane_enabled`] is the AND of
//! all four, and [`gate_actuation_nodes`] threads that bit onto the `ViewNode`
//! actuation nodes that carry an `enabled` flag (`Menu` rows, `Halo` handles) whose
//! `turn` names a reactive affordance — replacing the author bool (ViewNode growth #1)
//! with the computed gate. A node whose turn is NOT a reactive affordance keeps its
//! authored `enabled` (strictly additive: unrecognized actuations are untouched).
//!
//! HONEST SCOPE: this is the pure helper + a driven proof. Wiring it into the live
//! render walk (`resolve_mounts → disclose → gate_actuation_nodes → backend.render`)
//! is the named next step — the existing renderers (`render.rs`, `web.rs`) already
//! honor `item.enabled` (dimmed, non-firing), so the walk needs only to call
//! [`gate_actuation_nodes`] after disclosure, with the surface's reactive gate.

use crate::tree::{HaloHandle, MenuItem, ViewNode};
use dregg_cell::state::CellState;
use starbridge_web_surface::{EvalContext, ReactiveAffordance, Viewer};

/// **The FULL four-conjunct actuation gate** — `is_attenuation ∧ disclosure ∧
/// transition ∧ window`. Returns whether the reactive affordance may fire RIGHT NOW,
/// for THIS viewer, on THIS transition, at THIS height.
///
/// This is `project_membrane(viewer)` (the membrane: is_attenuation ∧ disclosure, via
/// [`Viewer::membrane_shows`]) AND `reactive_ok(ctx)`'s temporal half (transition ∧
/// window). It is deliberately NOT [`ReactiveAffordance::reactive_ok`] alone: that
/// carries the cap + transition + window but DROPS the disclosure bit — so this helper
/// composes the membrane's `membrane_shows` (cap ∧ disclosure) with the reactive
/// transition + window, preserving all four. Drop ANY one conjunct and it is `false`.
pub fn reactive_membrane_enabled(
    viewer: &Viewer,
    reactive: &ReactiveAffordance,
    ctx: &EvalContext,
    old: &CellState,
    new: &CellState,
) -> bool {
    // conjunct 1 (is_attenuation) ∧ conjunct 2 (disclosure): the two-dimensional membrane.
    viewer.membrane_shows(&reactive.affordance)
        // conjunct 3 (transition): pre(old) ∧ post(new) ∧ relational link(old, new).
        && reactive.gate.transition_ok(old, new)
        // conjunct 4 (window): the inclusive [open, close] deadline over the height.
        && reactive.in_window(ctx)
}

/// **Set the `enabled` bit of every actuation node from an `enabled_for(turn)` oracle.**
///
/// A pure pre-walk (like [`crate::tree::disclose`]): for each [`ViewNode::Menu`] row and
/// [`ViewNode::Halo`] handle whose `turn` the oracle recognizes, replace its authored
/// `enabled` with the oracle's verdict (`Some(bool)`); an unrecognized turn keeps its
/// authored value (`None` → additive, never darkens an actuation the gate does not
/// govern). All containers recurse; leaves clone. The renderers already dim a
/// `!enabled` row/handle in-band (the cap tooth SHOWN, not hidden), so the gated tree
/// they then walk paints the four-conjunct verdict.
pub fn gate_actuation_nodes<F>(tree: &ViewNode, enabled_for: &F) -> ViewNode
where
    F: Fn(&str) -> Option<bool>,
{
    fn menu_item(it: &MenuItem, enabled_for: &dyn Fn(&str) -> Option<bool>) -> MenuItem {
        MenuItem {
            label: it.label.clone(),
            turn: it.turn.clone(),
            arg: it.arg,
            enabled: enabled_for(&it.turn).unwrap_or(it.enabled),
        }
    }
    fn halo_handle(h: &HaloHandle, enabled_for: &dyn Fn(&str) -> Option<bool>) -> HaloHandle {
        HaloHandle {
            glyph: h.glyph.clone(),
            turn: h.turn.clone(),
            arg: h.arg,
            enabled: enabled_for(&h.turn).unwrap_or(h.enabled),
        }
    }
    fn rec(node: &ViewNode, enabled_for: &dyn Fn(&str) -> Option<bool>) -> ViewNode {
        let kids = |cs: &[ViewNode]| cs.iter().map(|c| rec(c, enabled_for)).collect::<Vec<_>>();
        match node {
            ViewNode::Menu { items } => ViewNode::Menu {
                items: items.iter().map(|it| menu_item(it, enabled_for)).collect(),
            },
            ViewNode::Halo {
                target_slot,
                handles,
            } => ViewNode::Halo {
                target_slot: *target_slot,
                handles: handles
                    .iter()
                    .map(|h| halo_handle(h, enabled_for))
                    .collect(),
            },
            ViewNode::VStack(cs) => ViewNode::VStack(kids(cs)),
            ViewNode::Row(cs) => ViewNode::Row(kids(cs)),
            ViewNode::List(cs) => ViewNode::List(kids(cs)),
            ViewNode::Table(cs) => ViewNode::Table(kids(cs)),
            ViewNode::Section {
                title,
                tag,
                children,
            } => ViewNode::Section {
                title: title.clone(),
                tag: tag.clone(),
                children: kids(children),
            },
            ViewNode::Tabs {
                tabs,
                selected_slot,
                select_turn,
                panels,
            } => ViewNode::Tabs {
                tabs: tabs.clone(),
                selected_slot: *selected_slot,
                select_turn: select_turn.clone(),
                panels: kids(panels),
            },
            ViewNode::Grid { cols, children } => ViewNode::Grid {
                cols: *cols,
                children: kids(children),
            },
            ViewNode::Host { cell, view } => ViewNode::Host {
                cell: cell.clone(),
                view: view.as_ref().map(|v| Box::new(rec(v, enabled_for))),
            },
            ViewNode::Adept(inner) => ViewNode::Adept(Box::new(rec(inner, enabled_for))),
            // Leaves (incl. the other actuation nodes that carry NO `enabled` flag —
            // Button/Slider/Toggle) are cloned through unchanged.
            other => other.clone(),
        }
    }
    rec(tree, &|t| enabled_for(t))
}

/// A **reactive surface** — the set of [`ReactiveAffordance`]s a cell publishes — as an
/// `enabled_for(turn)` oracle. [`ReactiveSurfaceGate::gate_tree`] darkens every
/// actuation node whose `turn` names one of these, using the FULL four-conjunct
/// [`reactive_membrane_enabled`]; an actuation whose turn is not published stays
/// authored.
pub struct ReactiveSurfaceGate<'a> {
    /// The published reactive affordances (each names its `turn` via `affordance.name`).
    pub reactives: &'a [ReactiveAffordance],
}

impl<'a> ReactiveSurfaceGate<'a> {
    /// Wrap a slice of reactive affordances.
    pub fn new(reactives: &'a [ReactiveAffordance]) -> Self {
        ReactiveSurfaceGate { reactives }
    }

    /// Is the actuation named `turn` enabled for `viewer` on `(old → new)` at
    /// `ctx.height`? `None` if `turn` is not a published reactive affordance.
    pub fn enabled_for(
        &self,
        turn: &str,
        viewer: &Viewer,
        ctx: &EvalContext,
        old: &CellState,
        new: &CellState,
    ) -> Option<bool> {
        self.reactives
            .iter()
            .find(|r| r.affordance.name == turn)
            .map(|r| reactive_membrane_enabled(viewer, r, ctx, old, new))
    }

    /// Rewrite `tree`, setting every recognized actuation node's `enabled` from the
    /// FULL four-conjunct gate for `viewer` on `(old → new)` at `ctx.height`.
    pub fn gate_tree(
        &self,
        tree: &ViewNode,
        viewer: &Viewer,
        ctx: &EvalContext,
        old: &CellState,
        new: &CellState,
    ) -> ViewNode {
        gate_actuation_nodes(tree, &|turn| self.enabled_for(turn, viewer, ctx, old, new))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tree::{MenuItem, ViewNode};
    use starbridge_web_surface::{
        AuthRequired, CellAffordance, CellId, Effect, SurfaceCapability, TransitionGate,
    };

    // ── Test scaffolding: mirrors starbridge-web-surface's own Reactive tests exactly
    //    (a council cell with a status slot + a tally slot; the VOTE reactive button). ──

    const STATUS_SLOT: usize = 0;
    const TALLY_SLOT: usize = 1;
    const PENDING: u64 = 1;

    fn cid(b: u8) -> CellId {
        let mut k = [0u8; 32];
        k[0] = b;
        CellId::derive_raw(&k, &[0u8; 32])
    }

    fn fe(n: u64) -> [u8; 32] {
        let mut b = [0u8; 32];
        b[24..32].copy_from_slice(&n.to_be_bytes());
        b
    }

    fn slot_u64(s: &CellState, slot: usize) -> Option<u64> {
        s.get_field(slot).map(|f| {
            let mut last8 = [0u8; 8];
            last8.copy_from_slice(&f[24..32]);
            u64::from_be_bytes(last8)
        })
    }

    /// A council-cell state `(status, tally)` — the `old`/`new` the transition reads.
    fn council(status: u64, tally: u64) -> CellState {
        let mut s = CellState::new(0);
        s.set_field(STATUS_SLOT, fe(status));
        s.set_field(TALLY_SLOT, fe(tally));
        s
    }

    /// The VOTE gate: PENDING → PENDING AND the tally went up by EXACTLY ONE (the
    /// relational `link` reading BOTH records).
    fn vote_gate() -> TransitionGate {
        TransitionGate::new(
            Box::new(|s: &CellState| slot_u64(s, STATUS_SLOT) == Some(PENDING)),
            Box::new(|s: &CellState| slot_u64(s, STATUS_SLOT) == Some(PENDING)),
            Box::new(|old: &CellState, new: &CellState| {
                match (slot_u64(old, TALLY_SLOT), slot_u64(new, TALLY_SLOT)) {
                    (Some(a), Some(b)) => b == a + 1,
                    _ => false,
                }
            }),
        )
    }

    /// The "vote" reactive button: the ballot cap (`Either`) AND the add-a-ballot
    /// transition AND inside `[10, 20]`.
    fn vote_btn(cell: CellId) -> ReactiveAffordance {
        ReactiveAffordance::new(
            CellAffordance::new(
                "vote",
                AuthRequired::Either,
                Effect::SetField {
                    cell,
                    index: TALLY_SLOT,
                    value: [0u8; 32],
                },
            ),
            vote_gate(),
            10,
            20,
        )
    }

    /// A viewer holding `rights`, whose disclosure `permits` shows the named affordance
    /// iff `discloses`.
    fn viewer(rights: AuthRequired, discloses: bool) -> Viewer {
        Viewer::new(
            SurfaceCapability::root(cid(9), rights),
            Box::new(move |_name: &str| discloses),
        )
    }

    // ══════════════════════════════════════════════════════════════════════════════
    // THE DRIVEN PROOF: each of the four conjuncts INDEPENDENTLY darkens the affordance
    // — none is dropped. Baseline lights; flipping ANY one conjunct (holding the other
    // three) darkens.
    // ══════════════════════════════════════════════════════════════════════════════

    #[test]
    fn four_conjunct_gate_each_conjunct_independently_darkens() {
        let doc = cid(30);
        let btn = vote_btn(doc);
        let ctx_in = EvalContext::at_height(15); // inside [10, 20]
        let good_old = council(PENDING, 0);
        let good_new = council(PENDING, 1); // tally 0 → 1: the link holds

        // BASELINE — all four conjuncts hold ⇒ ENABLED.
        let member = viewer(AuthRequired::Either, true);
        assert!(
            reactive_membrane_enabled(&member, &btn, &ctx_in, &good_old, &good_new),
            "all four conjuncts hold ⇒ enabled"
        );

        // CONJUNCT 1 — is_attenuation. A Signature holder does NOT satisfy `Either`
        // (incomparable): cap fails, other three hold ⇒ DARK.
        let underauthorized = viewer(AuthRequired::Signature, true);
        assert!(
            !reactive_membrane_enabled(&underauthorized, &btn, &ctx_in, &good_old, &good_new),
            "conjunct 1 (is_attenuation) dropped ⇒ dark"
        );

        // CONJUNCT 2 — disclosure. SAME authority as the member (Either), but the
        // witness-graph does NOT permit the name: cap holds, disclosure fails ⇒ DARK.
        // Two EQUAL-authority viewers, different surfaces — the membrane divides BEYOND
        // caps (the Lean `membrane_two_viewers_distinct`).
        let undisclosed = viewer(AuthRequired::Either, false);
        assert!(
            !reactive_membrane_enabled(&undisclosed, &btn, &ctx_in, &good_old, &good_new),
            "conjunct 2 (disclosure) dropped ⇒ dark, at EQUAL authority to the lit member"
        );
        // And the two Either-holders genuinely DIVERGE on the same affordance:
        assert_ne!(
            reactive_membrane_enabled(&member, &btn, &ctx_in, &good_old, &good_new),
            reactive_membrane_enabled(&undisclosed, &btn, &ctx_in, &good_old, &good_new),
            "two equal-authority viewers see DIFFERENT surfaces (disclosure is load-bearing)"
        );

        // CONJUNCT 3 — transition. SAME `new` (PENDING, tally 1), but reached from a
        // WRONG `old` (tally 3, so 1 != 3+1): the relational link fails ⇒ DARK, even
        // with full cap, disclosure, and an open window. The half a single-state gate
        // can never witness.
        let wrong_old = council(PENDING, 3);
        assert!(
            !reactive_membrane_enabled(&member, &btn, &ctx_in, &wrong_old, &good_new),
            "conjunct 3 (transition) dropped: same `new`, wrong `old` ⇒ dark"
        );

        // CONJUNCT 4 — window. All of cap, disclosure, transition hold, but the height
        // is OUTSIDE [10, 20]: the deadline tooth ⇒ DARK.
        let ctx_out = EvalContext::at_height(25);
        assert!(
            !reactive_membrane_enabled(&member, &btn, &ctx_out, &good_old, &good_new),
            "conjunct 4 (window) dropped: height 25 ∉ [10,20] ⇒ dark"
        );
    }

    // ── The tree-rewrite applies the FOUR-CONJUNCT bit to actuation nodes; leaves an
    //    unrecognized actuation authored (additive). ──

    #[test]
    fn gate_tree_sets_enabled_on_actuation_nodes_from_the_full_gate() {
        let doc = cid(31);
        let btn = vote_btn(doc);
        let reactives = [btn];
        let surface = ReactiveSurfaceGate::new(&reactives);

        // A menu with a `vote` row (a published reactive affordance) and an `other` row
        // (NOT published) — both authored `enabled: true`.
        let tree = ViewNode::Menu {
            items: vec![
                MenuItem {
                    label: "Vote".into(),
                    turn: "vote".into(),
                    arg: 1,
                    enabled: true,
                },
                MenuItem {
                    label: "Other".into(),
                    turn: "other".into(),
                    arg: 0,
                    enabled: true,
                },
            ],
        };

        let ctx = EvalContext::at_height(15);
        let old = council(PENDING, 0);
        let new = council(PENDING, 1);

        // A fully-cleared member (cap ∧ disclosure ∧ transition ∧ window) ⇒ vote stays
        // enabled; `other` (unrecognized) keeps its authored `true`.
        let member = viewer(AuthRequired::Either, true);
        let gated = surface.gate_tree(&tree, &member, &ctx, &old, &new);
        let ViewNode::Menu { items } = &gated else {
            panic!("menu")
        };
        assert!(
            items[0].enabled,
            "vote enabled for the fully-cleared member"
        );
        assert!(
            items[1].enabled,
            "unrecognized `other` keeps its authored enabled"
        );

        // A viewer who fails the disclosure conjunct (equal authority, no permit) ⇒ the
        // vote row DARKENS from the FULL gate, while `other` is untouched — proving the
        // rewrite carries the four-conjunct verdict, not is_attenuation alone.
        let undisclosed = viewer(AuthRequired::Either, false);
        let gated2 = surface.gate_tree(&tree, &undisclosed, &ctx, &old, &new);
        let ViewNode::Menu { items } = &gated2 else {
            panic!("menu")
        };
        assert!(
            !items[0].enabled,
            "vote DARK for the undisclosed (equal-authority) viewer — disclosure conjunct bit"
        );
        assert!(
            items[1].enabled,
            "`other` still authored-enabled (additive)"
        );
    }
}
