//! # The REAL cross-surface affordance differential — every fireable move reachable on EVERY glass.
//!
//! ## Why this exists (the pathology it kills)
//!
//! A `ViewNode` surface is authored ONCE; four+ backends project it (native gpui, web client-JS,
//! web server-form, Telegram/WeChat prose+carrier, Discord embed+components). The bug this suite
//! is the antidote to: a first-class affordance node (a `Halo` handle, a clickable `Breadcrumb`
//! crumb, a `Tabs` select, an `Input` text move) that a backend SILENTLY drops — it fires on one
//! surface and does *nothing*, with no log and no failing test, because every prior "parity" test
//! compared a surface *to itself* (`telegram == render_text` is `render_text == render_text`).
//!
//! This one does NOT compare a surface to itself. It takes ONE `ViewNode` tree, computes the
//! CANONICAL affordance set from the shared collector ([`deos_view::actuations`] — the exact set
//! Telegram's inline keyboard / WeChat's numbered list / Discord's buttons are all built from),
//! and asserts that the set of `{turn, arg}` a backend actually makes *reachable* MATCHES it —
//! with DECLARED, documented exceptions, never silent loss.
//!
//! ## The backends compared (the real ones a bot/game renders through)
//!
//!  * **`SessionFormBackend`** — the production web server-form frontend (`WebFrontend::render`
//!    renders through it). Parsed back out of its real HTML.
//!  * **WeChat** — [`deos_view::wechat::render_message`]'s numbered reply list.
//!  * **Discord** — [`deos_view::discord::render_card`]'s button components (custom-ids decoded).
//!  * The **chat carrier** — [`deos_view::actuations`] itself, which IS what the Telegram keyboard
//!    and the WeChat list are constructed from, so it is the canonical reference.
//!
//! ## The DECLARED exceptions (documented, not silent)
//!
//!  * `Slider` / `Toggle` — VALUE-DEPENDENT: the fired `{turn, arg}` is chosen by the live slot,
//!    not fixed by the node, so a keyboard button / numbered reply / no-JS POST form (each of which
//!    must name a *constant* press) cannot express it. Only the live surfaces (Discord's static
//!    both-transitions buttons, the native/web-client controls) render them. Excluded from the
//!    canonical set by [`deos_view::actuations`] itself.
//!  * `Input` (`wants_text`) — TEXT-SHAPED: its `fire_turn` fires with the user's supplied value,
//!    not a fixed index. A chat surface solicits that via `Action::wants_text` (the next inbound
//!    message), so it is NOT on the keyboard/numbered carrier; the DOM/server-form/Discord paths
//!    render it as a real control. Checked explicitly in [`wants_text_is_reachable_where_a_control_exists`].

#![cfg(all(feature = "web", feature = "wechat", feature = "discord"))]

use std::collections::BTreeSet;

use deos_view::web::SessionFormBackend;
use deos_view::wechat::render_message;
use deos_view::{actuations, BindFmt, SurfaceBackend, ViewNode};
use deos_view::{CoordCell, Crumb, HaloHandle, MenuItem};

type AffSet = BTreeSet<(String, i64)>;

/// The CANONICAL affordance set of a tree — the shared collector every chat carrier is built from.
/// This is the reference every renderable backend's *reachable* set is diffed against.
fn canonical(tree: &ViewNode) -> AffSet {
    actuations(tree)
        .into_iter()
        .map(|a| (a.turn, a.arg))
        .collect()
}

/// Parse the `{turn, arg}` set a `SessionFormBackend` (or any of our POST-form renderers) actually
/// makes fireable, straight out of its real HTML: each `name="turn" value="…"` paired with the next
/// `name="arg" value="…"` that follows it (the shape every `session_form` / editable-arg / coordgrid
/// cell emits). This reads the ACTUAL served surface — not a mirror of it.
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
        // The paired arg is the FIRST `name="arg"` after this turn (both are emitted adjacently in
        // the same <form>). If none follows, the turn carries no arg control — skip it.
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

/// The `{turn, arg}` set the WeChat numbered reply list makes fireable.
fn wechat_affordances(tree: &ViewNode) -> AffSet {
    render_message(tree)
        .options
        .into_iter()
        .map(|o| (o.turn, o.arg))
        .collect()
}

/// The `{turn, arg}` set the Discord card's button components make fireable — decoded from the REAL
/// serenity component builders (serialized to their wire JSON, every `custom_id` decoded through the
/// ONE affordance codec). This reads what Discord would actually post, not a hand-mirror of it.
fn discord_affordances(title: &str, tree: &ViewNode) -> AffSet {
    let card = deos_view::discord::render_card(title, tree, &[]);
    let json = serde_json::to_value(&card.components).expect("components serialize to wire JSON");
    let mut ids = Vec::new();
    collect_custom_ids(&json, &mut ids);
    ids.iter()
        .filter_map(|id| deos_view::discord::parse_affordance_id(id))
        .collect()
}

fn collect_custom_ids(v: &serde_json::Value, out: &mut Vec<String>) {
    match v {
        serde_json::Value::Object(map) => {
            if let Some(serde_json::Value::String(id)) = map.get("custom_id") {
                out.push(id.clone());
            }
            for (_k, child) in map {
                collect_custom_ids(child, out);
            }
        }
        serde_json::Value::Array(items) => {
            for item in items {
                collect_custom_ids(item, out);
            }
        }
        _ => {}
    }
}

// ─────────────────────────────────────────────────────────────────────────────────────────────
// Representative trees — deliberately exercise the nodes prior tests never touched.
// ─────────────────────────────────────────────────────────────────────────────────────────────

/// A rich surface using EVERY affordance carrier (Button / Menu / Halo / clickable Breadcrumb /
/// Tabs select / clickable CoordGrid cell) AND every non-affordance display leaf (Bind / Gauge /
/// Pill / Progress / Icon) AND the value-dependent Slider/Toggle — all nested inside containers so a
/// dropped affordance can hide the way the real bug did.
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
                    }, // inert
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
                    }, // inert goal
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
                }, // dimmed, still reachable
            ],
        },
        // THE HALO — the handle-ring that used to fire on native/discord and do NOTHING on web.
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
        // THE BREADCRUMB — a clickable crumb (nav) + an inert tail crumb.
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
        // THE TABS — a tab-switch is an actuation (select_turn, arg=index) PLUS a nested affordance.
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
        // ── Non-affordance display leaves — must NOT contribute a fireable turn on any surface. ──
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
        // ── VALUE-DEPENDENT (declared exception): reachable only on live surfaces. ──
        ViewNode::Slider {
            slot: 2,
            min: 0,
            max: 9,
            turn: "seek".into(),
        },
        ViewNode::Toggle {
            slot: 3,
            on_turn: "on".into(),
            off_turn: "off".into(),
            glyph_on: "✓".into(),
            glyph_off: "○".into(),
            label: "mute".into(),
        },
    ])
}

/// The set of turns the DECLARED value-dependent exception covers on the rich surface.
fn value_dependent_turns() -> BTreeSet<String> {
    ["seek", "on", "off"]
        .into_iter()
        .map(String::from)
        .collect()
}

// ─────────────────────────────────────────────────────────────────────────────────────────────
// THE DIFFERENTIAL
// ─────────────────────────────────────────────────────────────────────────────────────────────

/// **The web server-form route makes EXACTLY the canonical affordance set reachable** — no fixed
/// `{turn, arg}` move on any other glass is silently dropped here. This is the assertion that used
/// to be impossible: `SessionFormBackend` had ZERO test references, and it dropped Halo / clickable
/// Breadcrumb / Tabs-select while the chat carrier surfaced them. If this passes, the halo handle
/// that "fires on other surfaces and does NOTHING on web" no longer exists.
#[test]
fn session_form_route_reaches_the_whole_canonical_set() {
    let tree = rich_surface();
    let reference = canonical(&tree);

    let html = SessionFormBackend {
        session_id: "s1".into(),
    }
    .render(&tree, &[]);
    let web = form_affordances(&html);

    assert_eq!(
        web,
        reference,
        "the web server-form route must make EXACTLY the canonical affordance set fireable.\n\
         missing on web (dropped!): {:?}\n\
         extra on web (unexpected): {:?}",
        reference.difference(&web).collect::<Vec<_>>(),
        web.difference(&reference).collect::<Vec<_>>(),
    );

    // The affordance carriers the bug dropped are concretely present.
    for want in [("cut", 3), ("rot", 4), ("nav", 0), ("tab", 0), ("tab", 1)] {
        assert!(
            web.contains(&(want.0.to_string(), want.1)),
            "the web server-form route reaches {want:?} (a Halo/Breadcrumb/Tabs affordance the \
             old subset walker silently dropped)"
        );
    }
    // A pure display leaf must never have leaked a fireable turn.
    for leak in ["count: ", "hp", "prog "] {
        assert!(
            !web.iter().any(|(t, _)| t == leak),
            "a display leaf ({leak:?}) must not become a fireable affordance"
        );
    }
}

/// **The WeChat numbered list and the canonical carrier agree** — one numbered reply per canonical
/// affordance. (WeChat's list IS built from the carrier, so this pins the construction, and doubles
/// as the golden that the carrier itself covers Halo/Breadcrumb/Tabs — which it does, and always
/// did; the gap was only ever on the server-form/catalog routes.)
#[test]
fn wechat_list_equals_the_canonical_set() {
    let tree = rich_surface();
    assert_eq!(
        wechat_affordances(&tree),
        canonical(&tree),
        "every canonical affordance is one WeChat numbered reply, and no more"
    );
}

/// **Discord reaches the whole canonical set, plus ONLY the declared value-dependent extras** — the
/// superset direction. Discord renders `Slider`/`Toggle` as static buttons (it can, being a live
/// surface); those are the ONLY turns it may add over the canonical set, and they are exactly the
/// declared exception. Nothing else diverges.
#[test]
fn discord_is_the_canonical_set_plus_only_declared_value_dependent_extras() {
    let tree = rich_surface();
    let reference = canonical(&tree);
    let discord = discord_affordances("Rich", &tree);

    // Every canonical fixed affordance is reachable on Discord.
    for aff in &reference {
        assert!(
            discord.contains(aff),
            "Discord must reach canonical affordance {aff:?}"
        );
    }
    // Discord's extras are EXACTLY the declared value-dependent turns — no undeclared divergence.
    let extras: BTreeSet<String> = discord
        .difference(&reference)
        .map(|(t, _)| t.clone())
        .collect();
    let declared = value_dependent_turns();
    assert!(
        extras.is_subset(&declared),
        "Discord's only extra turns beyond the canonical set must be the DECLARED value-dependent \
         exception ({declared:?}); undeclared extras: {:?}",
        extras.difference(&declared).collect::<Vec<_>>(),
    );
}

/// **The value-dependent exception is REAL, not a fig leaf** — `seek`/`on`/`off` are genuinely
/// absent from the fixed-press carriers (web form, WeChat), and genuinely present on Discord (the
/// live surface). This proves the exception is a true platform boundary, declared in both directions.
#[test]
fn value_dependent_moves_are_a_declared_boundary_in_both_directions() {
    let tree = rich_surface();
    let web = form_affordances(
        &SessionFormBackend {
            session_id: "s".into(),
        }
        .render(&tree, &[]),
    );
    let wechat = wechat_affordances(&tree);
    let discord = discord_affordances("Rich", &tree);

    for vd in value_dependent_turns() {
        assert!(
            !web.iter().any(|(t, _)| *t == vd) && !wechat.iter().any(|(t, _)| *t == vd),
            "value-dependent {vd:?} is (correctly) NOT on a fixed-press carrier"
        );
        assert!(
            discord.iter().any(|(t, _)| *t == vd),
            "value-dependent {vd:?} IS reachable on Discord (the live surface renders both transitions)"
        );
    }
}

/// **A `wants_text` / `Input` affordance is reachable everywhere a control can exist, and its chat
/// absence is the DECLARED text-shaped exception.** `Input.fire_turn` fires with a user-supplied
/// value, so: the web server-form route renders a real editable-arg POST (reachable); Discord
/// renders a submit button (reachable); the chat carrier does NOT list it (it rides
/// `Action::wants_text` — the next inbound message — a declared, documented exception, mirrored by
/// [`deos_view::actuations`] excluding `Input`).
#[test]
fn wants_text_is_reachable_where_a_control_exists() {
    let tree = ViewNode::VStack(vec![
        ViewNode::Text("Edit the document:".into()),
        ViewNode::Input {
            bind_view: "draft".into(),
            fire_turn: "insert".into(),
            submit_label: "Insert".into(),
        },
    ]);

    let web = form_affordances(
        &SessionFormBackend {
            session_id: "s".into(),
        }
        .render(&tree, &[]),
    );
    let discord = discord_affordances("Doc", &tree);
    let wechat = wechat_affordances(&tree);

    assert!(
        web.iter().any(|(t, _)| t == "insert"),
        "the web server-form route must render the wants_text `insert` move as a real POST control \
         (it was SILENTLY DROPPED by the old `_ => {{}}` — that was the bug)"
    );
    assert!(
        discord.iter().any(|(t, _)| t == "insert"),
        "Discord must render the wants_text `insert` move as a submit control"
    );
    // The DECLARED text-shaped exception: chat carriers do not keyboard-list it (routed via
    // Action::wants_text instead), exactly as `actuations` excludes `Input`.
    assert!(
        !wechat.iter().any(|(t, _)| t == "insert")
            && !canonical(&tree).iter().any(|(t, _)| t == "insert"),
        "the wants_text move is (by declared design) not on the chat keyboard/numbered carrier"
    );
}

// ─────────────────────────────────────────────────────────────────────────────────────────────
// NEGATIVE CONTROL — proof the differential has TEETH (a mutation canary).
// ─────────────────────────────────────────────────────────────────────────────────────────────

/// **If a backend drops even one affordance, the differential CATCHES it.** A green suite that
/// coexists with a silent drop is exactly the pathology this file kills, so we prove the check is
/// not vacuous: a deliberately-lossy affordance set (the canonical set minus the Halo handle) is
/// NOT equal to the reference — the same `assert_eq!` the real backends face would fail on it.
#[test]
fn the_differential_would_catch_a_dropped_affordance() {
    let tree = rich_surface();
    let reference = canonical(&tree);

    // Simulate a subset walker that drops the halo handle `cut`.
    let mut lossy = reference.clone();
    assert!(
        lossy.remove(&("cut".to_string(), 3)),
        "the canonical set contained the halo handle"
    );

    assert_ne!(
        lossy, reference,
        "the differential's equality is the teeth: a dropped affordance makes the sets unequal"
    );
}
