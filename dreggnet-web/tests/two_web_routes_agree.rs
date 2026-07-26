//! # The two web routes must not disagree — a REAL cross-route affordance differential.
//!
//! `dreggnet-web` renders a deos `Surface` two ways: the single-session games go through the shared
//! [`deos_view::web::SessionFormBackend`] (`WebFrontend::render`), and the multi-offering catalog
//! goes through this crate's own [`render_catalog_forms`] walker (it POSTs to a DIFFERENT route and
//! adds editable-arg inputs + sprite tiles). The pathology this kills: the two routes silently
//! DISAGREEING — the catalog walker rendered the `CoordGrid` board while the session backend lost
//! it, and BOTH silently dropped `Halo` / clickable `Breadcrumb` / `Tabs`-select affordances via a
//! `_ => {}`, with no test to notice because every prior "parity" test compared a route to itself.
//!
//! This suite compares the `{turn, arg}` set the two routes actually make fireable — parsed out of
//! their REAL HTML — against each other AND against the canonical carrier
//! ([`deos_view::actuations`], what Telegram's keyboard / WeChat's numbered list / Discord's buttons
//! are all built from). If the routes disagree, or either drops a canonical affordance, a concrete
//! assertion fails.

use std::collections::BTreeSet;

use deos_view::web::SessionFormBackend;
use deos_view::{BindFmt, SurfaceBackend, ViewNode, actuations};
use deos_view::{CoordCell, Crumb, HaloHandle, MenuItem};

use dreggnet_web::render_catalog_forms;

type AffSet = BTreeSet<(String, i64)>;

/// The CANONICAL affordance set — the shared carrier every chat surface is built from.
fn canonical(tree: &ViewNode) -> AffSet {
    actuations(tree)
        .into_iter()
        .map(|a| (a.turn, a.arg))
        .collect()
}

/// The `{turn, arg}` set a POST-form route actually makes fireable, parsed from its REAL HTML: each
/// `name="turn" value="…"` paired with the next `name="arg" value="…"` in the same `<form>`. This
/// reads the served surface, not a mirror of it — so a silently-dropped affordance is genuinely
/// absent from this set.
fn form_affordances(html: &str) -> AffSet {
    let mut out = AffSet::new();
    let mut rest = html;
    const TURN: &str = "name=\"turn\" value=\"";
    const ARG: &str = "name=\"arg\" value=\"";
    while let Some(ti) = rest.find(TURN) {
        let after_turn = &rest[ti + TURN.len()..];
        let turn = match after_turn.find('"') {
            Some(end) => after_turn[..end].to_string(),
            None => break,
        };
        if let Some(ai) = after_turn.find(ARG) {
            let after_arg = &after_turn[ai + ARG.len()..];
            if let Some(end) = after_arg.find('"') {
                if let Ok(arg) = after_arg[..end].parse::<i64>() {
                    out.insert((turn, arg));
                }
            }
        }
        rest = after_turn;
    }
    out
}

fn web_route(tree: &ViewNode) -> AffSet {
    form_affordances(
        &SessionFormBackend {
            session_id: "sess".into(),
        }
        .render(tree, &[]),
    )
}
fn catalog_route(tree: &ViewNode) -> AffSet {
    form_affordances(&render_catalog_forms(tree, "offering", "sess"))
}

/// A rich surface using every affordance carrier (Button / Menu incl. a refused row / Halo incl. a
/// refused handle / clickable Breadcrumb / Tabs-select / clickable CoordGrid cells) plus display
/// leaves — the shape that hid the real drift. No `Input` here (its wants_text move is a web-only
/// control beyond the chat carrier — tested separately).
fn rich_surface() -> ViewNode {
    ViewNode::VStack(vec![
        ViewNode::Section {
            title: "Board".into(),
            tag: String::new(),
            children: vec![ViewNode::CoordGrid {
                cols: 2,
                cells: vec![
                    CoordCell {
                        glyph: "·".into(),
                        tag: String::new(),
                        turn: "move".into(),
                        arg: 0,
                        highlight: false,
                    },
                    CoordCell {
                        glyph: "R".into(),
                        tag: String::new(),
                        turn: String::new(),
                        arg: 0,
                        highlight: true,
                    },
                    CoordCell {
                        glyph: "·".into(),
                        tag: String::new(),
                        turn: "move".into(),
                        arg: 2,
                        highlight: true,
                    },
                    CoordCell {
                        glyph: "a".into(),
                        tag: "goal".into(),
                        turn: String::new(),
                        arg: 0,
                        highlight: false,
                    },
                ],
            }],
        },
        ViewNode::Button {
            label: "Inc".into(),
            turn: "inc".into(),
            arg: 1,
        },
        ViewNode::Menu {
            items: vec![
                MenuItem {
                    label: "Vote".into(),
                    turn: "vote".into(),
                    arg: 1,
                    enabled: true,
                    wants_text: false,
                },
                MenuItem {
                    label: "Pass".into(),
                    turn: "pass".into(),
                    arg: 0,
                    enabled: false,
                    wants_text: false,
                },
            ],
        },
        ViewNode::Halo {
            target_slot: 0,
            handles: vec![
                HaloHandle {
                    glyph: "✂".into(),
                    turn: "cut".into(),
                    arg: 3,
                    enabled: true,
                },
                HaloHandle {
                    glyph: "⟳".into(),
                    turn: "rot".into(),
                    arg: 4,
                    enabled: false,
                },
            ],
        },
        ViewNode::Breadcrumb {
            items: vec![
                Crumb {
                    label: "root".into(),
                    turn: "nav".into(),
                    arg: 0,
                },
                Crumb {
                    label: "here".into(),
                    turn: String::new(),
                    arg: 0,
                },
            ],
        },
        ViewNode::Tabs {
            tabs: vec!["A".into(), "B".into()],
            selected_slot: 5,
            select_turn: "tab".into(),
            panels: vec![
                ViewNode::Divider,
                ViewNode::Button {
                    label: "Deep".into(),
                    turn: "deep".into(),
                    arg: 9,
                },
            ],
        },
        // Display leaves — must not become fireable affordances on either route.
        ViewNode::Bind {
            slot: 0,
            label: "count: ".into(),
            fmt: BindFmt::Raw,
        },
        ViewNode::Gauge {
            slot: 1,
            max: 100,
            label: "hp".into(),
        },
        ViewNode::Pill {
            text: "LIVE".into(),
            tag: "good".into(),
            slot: None,
            cases: vec![],
        },
        ViewNode::Progress {
            value: 3,
            max: 10,
            label: "prog ".into(),
        },
        ViewNode::Icon {
            glyph: "✦".into(),
            tag: "accent".into(),
        },
    ])
}

/// **The two web routes render the SAME affordance set, and it is EXACTLY the canonical carrier.**
/// This is the assertion the crate never had: `SessionFormBackend` had ZERO test references, the
/// catalog walker was compared only to itself, and they disagreed (the board, and the silently-
/// dropped Halo/Breadcrumb/Tabs). If this passes, a game author cannot ship a surface whose halo
/// handle fires on one web route and vanishes on the other.
#[test]
fn the_two_web_routes_render_the_same_affordance_set() {
    let tree = rich_surface();
    let reference = canonical(&tree);
    let web = web_route(&tree);
    let catalog = catalog_route(&tree);

    assert_eq!(
        web,
        catalog,
        "the two web routes must not disagree.\n\
         only on the session route: {:?}\n\
         only on the catalog route: {:?}",
        web.difference(&catalog).collect::<Vec<_>>(),
        catalog.difference(&web).collect::<Vec<_>>(),
    );
    assert_eq!(
        web,
        reference,
        "the web routes must reach EXACTLY the canonical carrier's affordance set.\n\
         missing on web (dropped!): {:?}\n\
         extra on web: {:?}",
        reference.difference(&web).collect::<Vec<_>>(),
        web.difference(&reference).collect::<Vec<_>>(),
    );

    // The affordances the old subset walkers dropped are concretely present on BOTH routes.
    for want in [
        ("cut", 3),
        ("rot", 4),
        ("nav", 0),
        ("tab", 0),
        ("tab", 1),
        ("move", 0),
        ("move", 2),
    ] {
        let w = (want.0.to_string(), want.1);
        assert!(web.contains(&w), "the session route reaches {want:?}");
        assert!(catalog.contains(&w), "the catalog route reaches {want:?}");
    }
    // A display leaf must never have leaked a fireable turn on either route.
    for leak in ["count: ", "hp", "prog ", "LIVE", "✦"] {
        assert!(
            !web.iter().any(|(t, _)| t == leak),
            "session: {leak:?} is not fireable"
        );
        assert!(
            !catalog.iter().any(|(t, _)| t == leak),
            "catalog: {leak:?} is not fireable"
        );
    }
}

/// **Both web routes render the `wants_text` / `Input` control** — its `fire_turn` is a real
/// editable-arg POST on each route (a web/DOM control beyond the chat keyboard carrier, which routes
/// free text via `Action::wants_text`). The two routes must AGREE that the move is reachable; the
/// old `_ => {}` silently dropped `Input` on the session route.
#[test]
fn both_web_routes_render_the_wants_text_control() {
    let tree = ViewNode::VStack(vec![
        ViewNode::Text("Edit:".into()),
        ViewNode::Input {
            bind_view: "draft".into(),
            fire_turn: "insert".into(),
            submit_label: "Insert".into(),
        },
    ]);
    let web = web_route(&tree);
    let catalog = catalog_route(&tree);

    assert!(
        web.iter().any(|(t, _)| t == "insert"),
        "the session route renders the wants_text `insert` move (was silently dropped by `_ => {{}}`)"
    );
    assert!(
        catalog.iter().any(|(t, _)| t == "insert"),
        "the catalog route renders the wants_text `insert` move"
    );
    // It is (correctly) NOT on the chat carrier — a declared, documented boundary.
    assert!(
        !canonical(&tree).iter().any(|(t, _)| t == "insert"),
        "the wants_text move is not on the fixed-press chat carrier (routed via Action::wants_text)"
    );
}
