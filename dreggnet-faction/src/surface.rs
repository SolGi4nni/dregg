//! # The standing read-surface — reputation, made visible.
//!
//! Faction standing was invisible: real committed cell state no frontend rendered. This module
//! turns a world's standing into a plain [`deos_view::ViewNode`] — a titled section of standing
//! bars, one row per faction (name · a [`Progress`](deos_view::ViewNode::Progress) bar of `rep`
//! against its full trust · a status [`Pill`](deos_view::ViewNode::Pill)). Because a `ViewNode` is
//! the do-once affordance tree, every frontend (web / discord / telegram / wechat) paints it for
//! free — the exact [`dreggnet_surfaces`](../../dreggnet_surfaces/index.html) path.
//!
//! Wiring it as a registered `dreggnet_offerings::Offering` (so it mounts alongside the market /
//! guild / cheevo surfaces) is a one-line seam in `dreggnet-surfaces` — this crate produces the
//! render payload; the host registers it.

use deos_view::ViewNode;
use spween_dregg::WorldCell;

use crate::roster::Roster;
use crate::standing::{FactionStanding, read_all};

fn text(s: impl Into<String>) -> ViewNode {
    ViewNode::Text(s.into())
}

fn pill(text: impl Into<String>, tag: &str) -> ViewNode {
    ViewNode::Pill {
        text: text.into(),
        tag: tag.to_string(),
        slot: None,
        cases: Vec::new(),
    }
}

/// The semantic palette tag for a standing's status pill.
fn status_tag(fs: &FactionStanding) -> &'static str {
    if fs.betrayed {
        "bad"
    } else if fs.unlocked {
        "good"
    } else if fs.meets_threshold() {
        "accent"
    } else {
        "muted"
    }
}

/// Render one faction's standing as a table row: name · a `rep` progress bar (scaled to the
/// faction's full trust) · a status pill.
pub fn standing_row(fs: &FactionStanding) -> ViewNode {
    // The bar scale: the full trust the faction extends, never below the current rep (a rep that
    // has climbed past the nominal ceiling still paints full, not overflowed).
    let max = fs.trust_ceiling.max(fs.rep).max(1);
    ViewNode::Row(vec![
        text(&fs.name),
        ViewNode::Progress {
            value: fs.rep,
            max,
            label: format!("rep {}/{}", fs.rep, fs.threshold),
        },
        pill(fs.label(), status_tag(fs)),
    ])
}

/// **The standing surface for a set of standings** — a titled section of one bar per faction.
pub fn standing_bars_of(standings: &[FactionStanding], title: impl Into<String>) -> ViewNode {
    let rows: Vec<ViewNode> = standings.iter().map(standing_row).collect();
    ViewNode::Section {
        title: title.into(),
        tag: "accent".to_string(),
        children: vec![ViewNode::Table(rows)],
    }
}

/// **The standing surface for a deployed world** — read the standing off `world`, render the bars.
pub fn standing_bars(world: &WorldCell, roster: &Roster) -> ViewNode {
    standing_bars_of(
        &read_all(world, roster),
        format!("Standing — {}", roster.title),
    )
}
