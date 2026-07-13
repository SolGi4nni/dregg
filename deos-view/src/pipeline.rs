//! **THE RENDER PIPELINE** — the one render entry, with the FOUR-conjunct gate LIVE in it.
//!
//! `docs/SURFACE-ONE-GATE-FOUR-PLANES.md` names the walk exactly:
//!
//! ```text
//!   render(view, surface, viewer, disclosure, ctx)
//!     = resolve_mounts(tree)              // plane D — the Host composition operator
//!     → disclose(tree, level)             // the third frustum axis (Simple / Adept)
//!     → gate_actuation_nodes(tree, …)     // THE ONE GATE — 4-conjunct, per viewer, per height
//!     → backend.render(tree, binds)       // plane B → the channel (web / discord / chat / gpui)
//! ```
//!
//! [`crate::gate`] was the pure helper; THIS is the wiring. An actuation node's `enabled` no longer
//! comes from the AUTHOR's bool — it is COMPUTED at render time from
//!
//! ```text
//!   enabled = is_attenuation ∧ disclosure ∧ transition ∧ window
//! ```
//!
//! ([`crate::gate::reactive_membrane_enabled`], all four conjuncts, none reduced), for THIS viewer,
//! on THIS `(old → new)` transition, at THIS height. Two viewers of EQUAL authority get DIFFERENT
//! enabled sets (the disclosure conjunct is live — the Lean `membrane_two_viewers_distinct`), and an
//! affordance whose window has closed renders DISABLED for everyone (the deadline conjunct is live).
//!
//! ORDER IS LOAD-BEARING:
//! * mounts FIRST — a hosted cell's subtree carries actuations too; gating before resolving would
//!   leave them at the author's bool (the composition hole).
//! * disclosure BEFORE the gate — the Simple projection DROPS `Adept` subtrees, so the gate never
//!   spends a verdict on a node no one will see, and the bind cursor the backend walks matches the
//!   tree that was gated.
//! * the gate BEFORE the backend — every backend already honours `enabled` (a dimmed, non-firing
//!   row); the pipeline is what makes that bit MEAN the membrane.
//!
//! WHAT A FRONTEND CALLS (the honest integration seam): build a [`RenderRequest`] (viewer + the
//! cell's reactive affordances + the height + the `old`/`new` records + the disclosure level + a
//! mount source + the pre-read bind values), then either
//! * [`render_surface`] — `tree` → the backend's output, gated; or
//! * [`gated_view`] — the gated tree, if the frontend renders it itself; and
//! * [`render_actuations`] — the gated actuation list a non-DOM channel needs to build its inline
//!   keyboard / numbered reply list (it also carries the gate verdict onto `Button`/`Tabs`/
//!   `Breadcrumb`, which the IR gives no `enabled` field).
//!
//! The `enabled` bit is a RENDER-TIME projection, never a substitute for the executor's own gate:
//! a forged press still meets [`starbridge_web_surface::ReactiveAffordance::fire`]'s refusal.

use crate::backend::{actuations_with, Actuation, SurfaceBackend};
use crate::gate::{gate_actuation_nodes, reactive_membrane_enabled};
use crate::tree::{disclose, resolve_mounts, Disclosure, MountSource, ViewNode};
use dregg_cell::state::CellState;
use starbridge_web_surface::{AffordanceSurface, EvalContext, ReactiveAffordance, Viewer};

/// A [`MountSource`] that hosts nothing — the default for a surface with no `host` nodes (every
/// `host` stays the honest `‹mount cell …: unresolved›` placeholder).
pub struct NoMounts;

impl MountSource for NoMounts {
    fn hosted_tree(&self, _cell: &str) -> Option<ViewNode> {
        None
    }
}

/// **Everything the render walk needs to compute a viewer's surface** — the arguments of the doc's
/// `render(view, surface, viewer, disclosure, ctx)`, as one borrow-only request.
///
/// Required: the `viewer` (held caps + the witness-graph permit fn), the height `ctx`, and the
/// `(old, new)` records the transition conjunct reads. Optional (builder-style, each defaulting to
/// the inert value): the reactive affordances, a plain affordance surface, the disclosure level, the
/// mount source, the pre-read bind values.
pub struct RenderRequest<'a> {
    /// WHO is looking — held authority (conjunct 1) + the witness-graph permit bit (conjunct 2).
    pub viewer: &'a Viewer,
    /// The cell's REACTIVE affordances — each carries its transition gate (conjunct 3) and its
    /// `[open, close]` window (conjunct 4). An actuation whose `turn` names one of these gets the
    /// FULL four-conjunct verdict.
    pub reactives: &'a [ReactiveAffordance],
    /// An optional PLAIN affordance surface (plane A). A [`starbridge_web_surface::CellAffordance`]
    /// declares NO transition and NO window, so its verdict is the two-dimensional membrane
    /// (`is_attenuation ∧ disclosure`, [`Viewer::membrane_shows`]).
    ///
    /// This is NOT the four-conjunct gate reduced: it is the gate on an affordance whose transition
    /// and window conjuncts are *undeclared*. An affordance that DOES declare them must be passed in
    /// [`Self::reactives`] — and the oracle consults `reactives` FIRST, so listing an affordance in
    /// both can only ever apply the STRICTER (four-conjunct) verdict, never downgrade it.
    pub surface: Option<&'a AffordanceSurface>,
    /// WHEN — the turn height the window conjunct is evaluated at.
    pub ctx: EvalContext,
    /// The PRE-state of the transition conjunct's relational `link(old, new)`.
    pub old: &'a CellState,
    /// The POST-state of the transition conjunct (`post(new)` + `link(old, new)`).
    pub new: &'a CellState,
    /// The progressive-disclosure projection (the third frustum axis): Simple DROPS `Adept` detail.
    pub disclosure: Disclosure,
    /// Where a `host` node's mounted view-tree comes from (the cell heap, a map, nothing).
    pub mounts: &'a dyn MountSource,
    /// The live bind values, pre-read in tree-walk order (a stateless backend's `bind` cursor).
    pub binds: &'a [u64],
}

impl<'a> RenderRequest<'a> {
    /// The minimal request: a viewer, a height, and the `(old, new)` records. No reactives (nothing
    /// is gated yet — add them), Simple disclosure, no mounts, no binds.
    pub fn new(
        viewer: &'a Viewer,
        ctx: EvalContext,
        old: &'a CellState,
        new: &'a CellState,
    ) -> Self {
        RenderRequest {
            viewer,
            reactives: &[],
            surface: None,
            ctx,
            old,
            new,
            disclosure: Disclosure::Simple,
            mounts: &NoMounts,
            binds: &[],
        }
    }

    /// The reactive affordances whose `turn`s the gate governs with all FOUR conjuncts.
    pub fn with_reactives(mut self, reactives: &'a [ReactiveAffordance]) -> Self {
        self.reactives = reactives;
        self
    }

    /// A plain affordance surface (plane A) — its affordances are gated by the 2-D membrane (they
    /// declare no transition/window). See [`Self::surface`].
    pub fn with_surface(mut self, surface: &'a AffordanceSurface) -> Self {
        self.surface = Some(surface);
        self
    }

    /// The disclosure projection (Simple = the newcomer's card; Adept = see the bones).
    pub fn with_disclosure(mut self, disclosure: Disclosure) -> Self {
        self.disclosure = disclosure;
        self
    }

    /// The source of hosted view-trees for `host` mounts.
    pub fn with_mounts(mut self, mounts: &'a dyn MountSource) -> Self {
        self.mounts = mounts;
        self
    }

    /// The pre-read live bind values (tree-walk order).
    pub fn with_binds(mut self, binds: &'a [u64]) -> Self {
        self.binds = binds;
        self
    }

    /// **THE GATE ORACLE** — may the actuation named `turn` fire, for THIS viewer, on THIS
    /// transition, at THIS height? `None` if the surface does not govern `turn` (the node keeps its
    /// authored bit — strictly additive; the pipeline never darkens an affordance it knows nothing
    /// about).
    ///
    /// A REACTIVE affordance answers with the FULL four-conjunct
    /// [`reactive_membrane_enabled`]; a plain one with the 2-D membrane ([`Viewer::membrane_shows`],
    /// its transition/window conjuncts undeclared). Reactives are consulted FIRST.
    pub fn enabled_for(&self, turn: &str) -> Option<bool> {
        if let Some(r) = self.reactives.iter().find(|r| r.affordance.name == turn) {
            return Some(reactive_membrane_enabled(
                self.viewer,
                r,
                &self.ctx,
                self.old,
                self.new,
            ));
        }
        self.surface
            .and_then(|s| s.affordances.iter().find(|a| a.name == turn))
            .map(|a| self.viewer.membrane_shows(a))
    }
}

/// **The gated view-tree** — `resolve_mounts → disclose → gate_actuation_nodes`, the render walk up
/// to (but not including) the backend. Every actuation node the surface governs carries the LIVE
/// four-conjunct verdict; every other node is untouched.
///
/// Call this when the frontend owns its own painting (the gpui `AppletView`, a bespoke DOM);
/// [`render_surface`] is the same walk plus the backend's projection.
pub fn gated_view(tree: &ViewNode, req: &RenderRequest) -> ViewNode {
    let mounted = resolve_mounts(tree, req.mounts);
    let disclosed = disclose(&mounted, req.disclosure);
    gate_actuation_nodes(&disclosed, &|turn| req.enabled_for(turn))
}

/// **THE RENDER ENTRY** — the full pipeline: `resolve_mounts → disclose → gate_actuation_nodes →
/// backend.render`. The actuation nodes' `enabled` the backend paints is the LIVE four-conjunct
/// gate's verdict for `req.viewer` at `req.ctx.height`, not the author's bool.
pub fn render_surface<B: SurfaceBackend>(
    backend: &B,
    tree: &ViewNode,
    req: &RenderRequest,
) -> B::Rendered {
    backend.render(&gated_view(tree, req), req.binds)
}

/// **The gated actuation list** — the affordance half a non-DOM channel carries outside the prose
/// (Telegram's inline keyboard, WeChat's numbered reply list), each entry stamped with the gate's
/// verdict.
///
/// Runs the same pipeline and then collects ([`crate::backend::actuations_with`]) with the gate
/// oracle, so even the nodes the IR gives no `enabled` field (`Button`/`Tabs`/`Breadcrumb`) carry a
/// LIVE verdict at the transport boundary — a refused affordance rides as a LOCKED entry (the cap
/// tooth shown, not hidden), never as a live button.
pub fn render_actuations(tree: &ViewNode, req: &RenderRequest) -> Vec<Actuation> {
    let view = gated_view(tree, req);
    actuations_with(&view, &|turn| req.enabled_for(turn))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::affordance::AffordanceTransport;
    use crate::tree::{MapMountSource, MenuItem};
    use starbridge_web_surface::{
        AuthRequired, CellAffordance, CellId, Effect, SurfaceCapability, TransitionGate,
    };

    // ── The scaffolding mirrors `gate.rs`'s (a council cell: a status slot + a tally slot; the
    //    VOTE reactive button — cap `Either`, tally+1, window [10, 20]). ──

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

    fn council(status: u64, tally: u64) -> CellState {
        let mut s = CellState::new(0);
        s.set_field(STATUS_SLOT, fe(status));
        s.set_field(TALLY_SLOT, fe(tally));
        s
    }

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

    fn vote_affordance(cell: CellId) -> CellAffordance {
        CellAffordance::new(
            "vote",
            AuthRequired::Either,
            Effect::SetField {
                cell,
                index: TALLY_SLOT,
                value: [0u8; 32],
            },
        )
    }

    fn vote_btn(cell: CellId) -> ReactiveAffordance {
        ReactiveAffordance::new(vote_affordance(cell), vote_gate(), 10, 20)
    }

    /// A viewer holding `rights` whose witness-graph disclosure `permits` the affordance iff
    /// `discloses` — the two viewers below differ ONLY in this bit.
    fn viewer(rights: AuthRequired, discloses: bool) -> Viewer {
        Viewer::new(
            SurfaceCapability::root(cid(9), rights),
            Box::new(move |_name: &str| discloses),
        )
    }

    /// A council card: a hosted subtree (so the mount step is exercised) holding the VOTE menu, an
    /// ungoverned `look` row, an ADEPT-only menu (dropped at Simple), and a `vote` Button (the node
    /// the IR gives no `enabled` field).
    fn card() -> ViewNode {
        ViewNode::VStack(vec![
            ViewNode::Text("The council is in session.".into()),
            ViewNode::Host {
                cell: "c0ffee".into(),
                view: None, // filled by resolve_mounts from the MountSource
            },
            ViewNode::Button {
                label: "Vote".into(),
                turn: "vote".into(),
                arg: 1,
            },
            ViewNode::Adept(Box::new(ViewNode::Menu {
                items: vec![MenuItem {
                    label: "raw tally".into(),
                    turn: "vote".into(),
                    arg: 99,
                    enabled: true,
                }],
            })),
        ])
    }

    fn hosted() -> MapMountSource {
        MapMountSource::default().with(
            "c0ffee",
            ViewNode::Section {
                title: "Ballot".into(),
                tag: String::new(),
                children: vec![ViewNode::Menu {
                    items: vec![
                        MenuItem {
                            label: "Vote".into(),
                            turn: "vote".into(),
                            arg: 1,
                            enabled: true, // the AUTHOR's optimistic bool — the gate overrides it
                        },
                        MenuItem {
                            label: "Look".into(),
                            turn: "look".into(),
                            arg: 0,
                            enabled: true, // ungoverned → keeps the authored bit
                        },
                    ],
                }],
            },
        )
    }

    /// The menu rows a rendered tree offers, as `(turn, arg, enabled)` — read off the GATED tree.
    fn enabled_set(tree: &ViewNode) -> Vec<(String, i64, bool)> {
        crate::backend::actuations(tree)
            .into_iter()
            .map(|a| (a.turn, a.arg, a.enabled))
            .collect()
    }

    /// A minimal [`SurfaceBackend`] that paints exactly what is load-bearing here: one
    /// `turn:arg[=on|off]` line per actuation, in walk order. It reads ONLY the tree's `enabled`
    /// bits — so what it prints IS what the pipeline computed.
    struct ProbeBackend;

    impl SurfaceBackend for ProbeBackend {
        type Rendered = String;
        fn transport(&self) -> AffordanceTransport {
            AffordanceTransport::Web
        }
        fn render(&self, tree: &ViewNode, _binds: &[u64]) -> String {
            crate::backend::actuations(tree)
                .into_iter()
                .map(|a| {
                    format!(
                        "{}:{}={}",
                        a.turn,
                        a.arg,
                        if a.enabled { "on" } else { "off" }
                    )
                })
                .collect::<Vec<_>>()
                .join(" ")
        }
    }

    // ══════════════════════════════════════════════════════════════════════════════════════
    // THE DRIVEN PROOF — the gate is LIVE in the render pipeline (not a helper on the shelf).
    // ══════════════════════════════════════════════════════════════════════════════════════

    /// **Two EQUAL-authority, different-permit viewers render DIFFERENT enabled sets.** Both hold
    /// `AuthRequired::Either` (conjunct 1 identical); they differ ONLY in the witness-graph
    /// disclosure bit (conjunct 2) — and the SAME card, through the SAME pipeline, at the SAME
    /// height, on the SAME transition, comes out with different `enabled` sets. The disclosure
    /// conjunct is LIVE in the render, not just in a unit helper.
    #[test]
    fn pipeline_two_equal_authority_viewers_diverge_on_the_disclosure_conjunct() {
        let doc = cid(30);
        let reactives = [vote_btn(doc)];
        let mounts = hosted();
        let old = council(PENDING, 0);
        let new = council(PENDING, 1); // tally 0 → 1: the relational link holds
        let ctx = EvalContext::at_height(15); // inside [10, 20]
        let tree = card();

        let member = viewer(AuthRequired::Either, true);
        let undisclosed = viewer(AuthRequired::Either, false); // SAME authority, no permit

        // The SAME card, the SAME surface, the SAME height, the SAME transition — only the viewer
        // differs, and only in the disclosure bit.
        let req_member = RenderRequest::new(&member, ctx, &old, &new)
            .with_reactives(&reactives)
            .with_mounts(&mounts);
        let req_undisclosed = RenderRequest::new(&undisclosed, ctx, &old, &new)
            .with_reactives(&reactives)
            .with_mounts(&mounts);

        let seen_by_member = gated_view(&tree, &req_member);
        let seen_by_undisclosed = gated_view(&tree, &req_undisclosed);

        assert_eq!(
            enabled_set(&seen_by_member),
            vec![
                ("vote".to_string(), 1, true), // the HOSTED menu row — gate says fire
                ("look".to_string(), 0, true), // ungoverned → the authored bit survives
                ("vote".to_string(), 1, true), // the Button (no IR enabled field → true)
            ],
            "the fully-cleared member: the governed row is LIT"
        );
        assert_eq!(
            enabled_set(&seen_by_undisclosed),
            vec![
                ("vote".to_string(), 1, false), // DARK — the disclosure conjunct alone
                ("look".to_string(), 0, true),  // untouched (additive)
                ("vote".to_string(), 1, true),  // the Button carries no IR enabled bit …
            ],
            "the equal-authority, undisclosed viewer: the governed row is DARK"
        );
        assert_ne!(
            enabled_set(&seen_by_member),
            enabled_set(&seen_by_undisclosed),
            "two viewers at EQUAL authority see DIFFERENT surfaces (membrane_two_viewers_distinct)"
        );

        // … and the BACKEND paints exactly that divergence (the pipeline reaches the channel):
        assert_eq!(
            render_surface(&ProbeBackend, &tree, &req_member),
            "vote:1=on look:0=on vote:1=on"
        );
        assert_eq!(
            render_surface(&ProbeBackend, &tree, &req_undisclosed),
            "vote:1=off look:0=on vote:1=on"
        );

        // … and at the TRANSPORT boundary the gate ALSO reaches the Button (which the IR gives no
        // `enabled` field), so a chat channel's keyboard/numbered list locks it too:
        let acts = render_actuations(&tree, &req_undisclosed);
        assert_eq!(
            acts.iter()
                .map(|a| (a.turn.as_str(), a.arg, a.enabled))
                .collect::<Vec<_>>(),
            vec![("vote", 1, false), ("look", 0, true), ("vote", 1, false)],
            "the oracle darkens the Button too — no ViewNode change needed"
        );

        // The Adept-only menu row (`vote`/arg 99) is in NEITHER: `disclose` ran BEFORE the gate.
        assert!(
            !enabled_set(&seen_by_member)
                .iter()
                .any(|(_, arg, _)| *arg == 99),
            "the Simple projection dropped the adept subtree (disclosure precedes the gate)"
        );
        let adept = RenderRequest::new(&member, ctx, &old, &new)
            .with_reactives(&reactives)
            .with_mounts(&mounts)
            .with_disclosure(Disclosure::Adept);
        assert!(
            enabled_set(&gated_view(&tree, &adept))
                .iter()
                .any(|(t, arg, en)| t == "vote" && *arg == 99 && *en),
            "at Adept the row appears — and is GATED by the same four-conjunct verdict"
        );
    }

    /// **An out-of-window affordance renders DISABLED** — for a viewer who passes all three other
    /// conjuncts. The deadline tooth is live at render time: the surface reacts to the CLOCK.
    #[test]
    fn pipeline_out_of_window_affordance_renders_disabled() {
        let doc = cid(31);
        let reactives = [vote_btn(doc)]; // window [10, 20]
        let mounts = hosted();
        let old = council(PENDING, 0);
        let new = council(PENDING, 1);
        let tree = card();
        let member = viewer(AuthRequired::Either, true); // cap ✓ disclosure ✓ transition ✓

        let inside = RenderRequest::new(&member, EvalContext::at_height(15), &old, &new)
            .with_reactives(&reactives)
            .with_mounts(&mounts);
        let after = RenderRequest::new(&member, EvalContext::at_height(25), &old, &new)
            .with_reactives(&reactives)
            .with_mounts(&mounts);

        assert_eq!(
            render_surface(&ProbeBackend, &tree, &inside),
            "vote:1=on look:0=on vote:1=on",
            "height 15 ∈ [10, 20] — the affordance is live"
        );
        assert_eq!(
            render_surface(&ProbeBackend, &tree, &after),
            "vote:1=off look:0=on vote:1=on",
            "height 25 ∉ [10, 20] — the DEADLINE tooth darkens it in the rendered surface"
        );
    }

    /// **The transition conjunct is live too** — the SAME `new`, reached from a WRONG `old`, renders
    /// the affordance DARK for a fully-authorized, in-window, disclosed viewer. (The half a
    /// single-state gate can never witness — and the pipeline carries it to the pixel.)
    #[test]
    fn pipeline_wrong_old_renders_disabled() {
        let doc = cid(32);
        let reactives = [vote_btn(doc)];
        let mounts = hosted();
        let good_new = council(PENDING, 1);
        let wrong_old = council(PENDING, 3); // 1 != 3 + 1 → the relational link fails
        let good_old = council(PENDING, 0); // 1 == 0 + 1 → the link holds
        let member = viewer(AuthRequired::Either, true);
        let tree = card();

        let right = RenderRequest::new(&member, EvalContext::at_height(15), &good_old, &good_new)
            .with_reactives(&reactives)
            .with_mounts(&mounts);
        let wrong = RenderRequest::new(&member, EvalContext::at_height(15), &wrong_old, &good_new)
            .with_reactives(&reactives)
            .with_mounts(&mounts);

        assert_eq!(
            render_surface(&ProbeBackend, &tree, &right),
            "vote:1=on look:0=on vote:1=on",
            "tally 0 → 1: the relational link holds"
        );
        assert_eq!(
            render_surface(&ProbeBackend, &tree, &wrong),
            "vote:1=off look:0=on vote:1=on",
            "the SAME `new` from a WRONG `old` (3 → 1) renders DARK — the transition tooth"
        );
    }

    /// **A plain (non-reactive) affordance is gated by the 2-D membrane — and listing it as a
    /// REACTIVE one can only make the gate STRICTER, never weaker.** The anti-downgrade tooth: the
    /// oracle consults `reactives` FIRST, so an affordance that appears in both lists gets the
    /// four-conjunct verdict (here: DARK, window closed) even though its plain-membrane verdict
    /// would pass.
    #[test]
    fn plain_surface_membrane_and_the_reactive_list_cannot_be_downgraded() {
        let doc = cid(33);
        let plain = AffordanceSurface::new(doc).declare(vote_affordance(doc));
        let reactives = [vote_btn(doc)]; // window [10, 20]
        let mounts = hosted();
        let old = council(PENDING, 0);
        let new = council(PENDING, 1);
        let tree = card();

        // PLAIN ONLY, cleared viewer: the membrane passes ⇒ lit (no transition/window declared).
        let member = viewer(AuthRequired::Either, true);
        let plain_only = RenderRequest::new(&member, EvalContext::at_height(25), &old, &new)
            .with_surface(&plain)
            .with_mounts(&mounts);
        assert_eq!(
            render_surface(&ProbeBackend, &tree, &plain_only),
            "vote:1=on look:0=on vote:1=on",
            "a plain affordance declares no window — the membrane alone lights it"
        );

        // PLAIN ONLY, undisclosed viewer at EQUAL authority: the membrane's disclosure bit darkens.
        let undisclosed = viewer(AuthRequired::Either, false);
        let plain_undisclosed =
            RenderRequest::new(&undisclosed, EvalContext::at_height(25), &old, &new)
                .with_surface(&plain)
                .with_mounts(&mounts);
        assert_eq!(
            render_surface(&ProbeBackend, &tree, &plain_undisclosed),
            "vote:1=off look:0=on vote:1=on",
            "the 2-D membrane (cap ∧ disclosure) is the plain affordance's gate"
        );

        // BOTH lists, same cleared viewer, height 25 (window CLOSED): the reactive verdict wins.
        let both = RenderRequest::new(&member, EvalContext::at_height(25), &old, &new)
            .with_surface(&plain)
            .with_reactives(&reactives)
            .with_mounts(&mounts);
        assert_eq!(
            render_surface(&ProbeBackend, &tree, &both),
            "vote:1=off look:0=on vote:1=on",
            "reactives are consulted FIRST — the 4-conjunct gate cannot be downgraded to the membrane"
        );
    }

    /// **The pipeline drives a REAL backend end-to-end** — the same card, through the same four-
    /// conjunct gate, into a WeChat OA numbered-reply message: the out-of-window affordance arrives
    /// LOCKED in the message text and is refused at the reply loop, while the in-window one is live.
    /// (The `enabled` bit the channel paints IS the gate's verdict — nothing else computed it.)
    #[cfg(feature = "wechat")]
    #[test]
    fn the_gate_reaches_the_wechat_numbered_message() {
        use crate::wechat::WeChatBackend;

        let doc = cid(34);
        let reactives = [vote_btn(doc)]; // window [10, 20]
        let mounts = hosted();
        let old = council(PENDING, 0);
        let new = council(PENDING, 1);
        let tree = card();
        let member = viewer(AuthRequired::Either, true);

        let inside = RenderRequest::new(&member, EvalContext::at_height(15), &old, &new)
            .with_reactives(&reactives)
            .with_mounts(&mounts);
        let after = RenderRequest::new(&member, EvalContext::at_height(25), &old, &new)
            .with_reactives(&reactives)
            .with_mounts(&mounts);

        let live = render_surface(&WeChatBackend, &tree, &inside);
        assert!(
            live.content.contains("1. Vote") && !live.content.contains("🔒"),
            "in-window: the numbered option is live —\n{}",
            live.content
        );
        assert_eq!(live.resolve_enabled("1"), Some(("vote".to_string(), 1)));

        let closed = render_surface(&WeChatBackend, &tree, &after);
        assert!(
            closed.content.contains("1. 🔒 Vote (locked)"),
            "the CLOSED window darkens the numbered option (shown, not hidden) —\n{}",
            closed.content
        );
        assert_eq!(
            closed.resolve_enabled("1"),
            None,
            "and the reply loop refuses the pick"
        );
        // The ungoverned `Look` row is untouched in BOTH (additive).
        assert!(closed.content.contains("2. Look"));
    }

    /// The pipeline is ADDITIVE: with NO governed affordances at all, every actuation keeps exactly
    /// the bit its author wrote (the gate never darkens what it does not govern).
    #[test]
    fn pipeline_without_a_surface_keeps_every_authored_bit() {
        let old = council(PENDING, 0);
        let new = council(PENDING, 1);
        let member = viewer(AuthRequired::Either, true);
        let mounts = hosted();
        let req = RenderRequest::new(&member, EvalContext::at_height(15), &old, &new)
            .with_mounts(&mounts);
        assert_eq!(
            render_surface(&ProbeBackend, &card(), &req),
            "vote:1=on look:0=on vote:1=on",
            "no reactives, no surface ⇒ the authored bits stand (strictly additive)"
        );
    }
}
