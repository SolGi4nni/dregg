//! # OBJECT BUILDERS — authoring the bytes a mirror serves.
//!
//! An object's body is canonical JSON whose blake3 IS its address, carrying the object's
//! **view-tree** in the raw `deos.ui.*` shape (`{kind, props, children}`) that
//! `deos_view::parse_view_tree` eats. This module is a thin authoring helper for that
//! shape — deliberately NOT a second renderer and NOT a second parser: it emits JSON, and
//! `deos-view` remains the only thing in the system that knows what a view-tree means.
//!
//! `builders_round_trip_through_the_real_parser` is the guard that keeps it thin: every
//! builder here is parsed back by `deos-view` itself, so a drift in the `deos.ui.*` shape
//! turns this module red instead of silently emitting nodes that lift to placeholders.
//!
//! Used by the tests, and by the binary's `--seed-demo` so a fresh deployment has
//! something to look at before any real object is published.

use serde_json::{json, Value};

// ── the raw `deos.ui.*` node builders ────────────────────────────────────────

/// A raw node: `{kind, props, children}`.
pub fn node(kind: &str, props: Value, children: Vec<Value>) -> Value {
    json!({ "kind": kind, "props": props, "children": children })
}

/// `text(s)` — a label.
pub fn text(s: &str) -> Value {
    node("text", json!({ "text": s }), vec![])
}

/// `vstack(...)` — a column.
pub fn vstack(children: Vec<Value>) -> Value {
    node("vstack", json!({}), children)
}

/// `row(...)` — a row.
pub fn row(children: Vec<Value>) -> Value {
    node("row", json!({}), children)
}

/// `section(title, tag, ...)` — a titled, bordered container.
pub fn section(title: &str, tag: &str, children: Vec<Value>) -> Value {
    node("section", json!({ "title": title, "tag": tag }), children)
}

/// `list(...)` — a vertical list.
pub fn list(children: Vec<Value>) -> Value {
    node("list", json!({}), children)
}

/// `table(rows)` — a table; each row is itself a node.
pub fn table(rows: Vec<Value>) -> Value {
    node("table", json!({}), rows)
}

/// `button(label, turn, arg)` — an affordance. On the mirror it renders INERT (the page
/// wraps the card in a disabled fieldset), but it is still part of the object's real
/// surface, so it is still shown.
pub fn button(label: &str, turn: &str, arg: i64) -> Value {
    node(
        "button",
        json!({ "label": label, "onClick": { "turn": turn, "arg": arg } }),
        vec![],
    )
}

/// `bind(slot, label)` — a bound value. The mirror paints the snapshot the object commits
/// to (`binds[n]` in tree-walk order), which is inside the content address.
pub fn bind(slot: usize, label: &str) -> Value {
    node("bind", json!({ "slot": slot, "label": label }), vec![])
}

/// `divider()`.
pub fn divider() -> Value {
    node("divider", json!({}), vec![])
}

/// `progress(value, max, label)` — a literal (non-bound) bar.
pub fn progress(value: u64, max: u64, label: &str) -> Value {
    node(
        "progress",
        json!({ "value": value, "max": max, "label": label }),
        vec![],
    )
}

// ── whole objects ────────────────────────────────────────────────────────────

/// Assemble the canonical object bytes. `binds` are the bind values in tree-walk order.
pub fn object(kind: &str, title: &str, view: Value, binds: &[u64], note: Option<&str>) -> Vec<u8> {
    let mut o = json!({
        "kind": kind,
        "title": title,
        "view": view,
        "binds": binds,
    });
    if let Some(n) = note {
        o["note"] = json!(n);
    }
    serde_json::to_vec(&o).expect("object is serializable")
}

/// A poll: options with their committed tallies, and the quorum. The tallies ride in
/// `binds`, so they are inside the address — the origin cannot show a different number
/// under the same link.
pub fn poll(title: &str, options: &[(&str, u64)], quorum: u64) -> Vec<u8> {
    let total: u64 = options.iter().map(|(_, n)| *n).sum();
    let mut rows = Vec::new();
    let mut binds = Vec::new();
    for (i, (label, count)) in options.iter().enumerate() {
        rows.push(row(vec![
            text(label),
            bind(i, "votes"),
            button("vote", "castBallot", i as i64),
        ]));
        binds.push(*count);
    }
    let view = section(
        "the choice",
        "accent",
        vec![
            list(rows),
            divider(),
            progress(total, quorum.max(1), "toward quorum"),
            text(&format!("quorum: {quorum} · counted: {total}")),
        ],
    );
    object("poll", title, view, &binds, None)
}

/// A document. A conflict is held as BOTH alternatives side by side — never silently
/// resolved (DREGG-QUIET-UPGRADE.md §8).
pub fn doc(title: &str, paragraphs: &[&str], conflict: Option<(&str, &str)>) -> Vec<u8> {
    let mut kids: Vec<Value> = paragraphs.iter().map(|p| text(p)).collect();
    if let Some((a, b)) = conflict {
        kids.push(divider());
        kids.push(section(
            "unresolved conflict — both alternatives stand",
            "refusal",
            vec![
                row(vec![text("A"), text(a), button("take A", "resolve", 0)]),
                row(vec![text("B"), text(b), button("take B", "resolve", 1)]),
            ],
        ));
    }
    object("doc", title, section(title, "", kids), &[], None)
}

/// A collaboratively edited text.
pub fn doctext(title: &str, body: &str, revision: u64) -> Vec<u8> {
    let view = section(
        "text",
        "",
        vec![text(body), divider(), bind(0, "revision")],
    );
    object("doctext", title, view, &[revision], None)
}

/// A branching story: the scene, and the choices that lead out of it.
pub fn story(title: &str, scene: &str, choices: &[&str]) -> Vec<u8> {
    let rows: Vec<Value> = choices
        .iter()
        .enumerate()
        .map(|(i, c)| button(c, "choose", i as i64))
        .collect();
    let view = section(
        "scene",
        "",
        vec![text(scene), divider(), list(rows)],
    );
    object("story", title, view, &[], None)
}

/// A descent run, pinned to a committed epoch, with its leaderboard.
pub fn descent(title: &str, epoch_hex: &str, board: &[(&str, u64, u64)]) -> Vec<u8> {
    let mut rows = vec![row(vec![
        text("runner"),
        text("depth"),
        text("score"),
    ])];
    for (who, depth, score) in board {
        rows.push(row(vec![
            text(who),
            text(&depth.to_string()),
            text(&score.to_string()),
        ]));
    }
    let view = section(
        "the day",
        "accent",
        vec![
            text(&format!("epoch {epoch_hex}")),
            divider(),
            table(rows),
            text("every entry is a replayed run — the board is re-derivable, not asserted"),
        ],
    );
    object("descent", title, view, &[], None)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// THE ANTI-DRIFT GUARD. Every builder is parsed by the REAL `deos-view` parser, and
    /// the resulting tree is rendered by the REAL web renderer. If the `deos.ui.*` shape
    /// moves, this goes red here rather than silently lifting to placeholder nodes on a
    /// live page.
    #[test]
    fn builders_round_trip_through_the_real_parser() {
        let cases: Vec<Vec<u8>> = vec![
            poll("q", &[("yes", 3), ("no", 1)], 4),
            doc("d", &["one", "two"], Some(("left", "right"))),
            doctext("t", "the quick brown fox", 7),
            story("s", "a dark room", &["north", "south"]),
            descent("run", "abcd", &[("ember", 12, 900)]),
        ];
        for bytes in cases {
            let o: crate::object::MirrorObject = serde_json::from_slice(&bytes).unwrap();
            let tree = deos_view::parse_view_tree(&o.view.to_string())
                .unwrap_or_else(|e| panic!("{} view did not parse: {e}", o.kind));
            let html = deos_view::web::render_html(&tree, &o.binds);
            assert!(!html.is_empty());
            // `RawNode::lift`'s fallback for a kind it cannot map.
            assert!(
                !html.contains("unmapped node"),
                "{} lifted to a placeholder — the deos.ui shape drifted",
                o.kind
            );
        }
    }

    #[test]
    fn a_polls_tally_is_inside_its_address() {
        let a = crate::object::content_addr(&poll("q", &[("yes", 3), ("no", 1)], 4));
        let b = crate::object::content_addr(&poll("q", &[("yes", 4), ("no", 1)], 4));
        assert_ne!(a, b, "changing the tally MUST change the address");
    }
}
