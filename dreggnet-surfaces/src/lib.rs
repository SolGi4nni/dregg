//! # `dreggnet-surfaces` — the DO-ONCE frontend batch.
//!
//! An [`Offering`](dreggnet_offerings::Offering)'s [`render`](dreggnet_offerings::Offering::render)
//! returns a [`Surface`](dreggnet_offerings::Surface) — and a `Surface` IS a
//! [`deos_view::ViewNode`]. Every frontend (the native cockpit, `deos-view`'s web/discord/
//! telegram/wechat renderers, the test [`MockFrontend`](dreggnet_offerings::mock::MockFrontend))
//! is a *renderer of that one tree*. So writing `render -> ViewNode` ONCE per feature lights up
//! EVERY surface — the do-once path the frontend plan (`docs/FRONTEND-PLAN.md`) confirmed is ~80%
//! of the work. [`dreggnet_market`](../dreggnet_market/index.html) was the only prior new-domain
//! Offering; this crate adds four more, following that reference:
//!
//! * [`trade::TradeOffering`] — a **playable market #2** over [`dreggnet_trade`]: list a good, then
//!   settle a real atomic **asset swap** (the seller's owned note crosses to the buyer for a
//!   trade-coin, each move a real owner-signed transfer turn — a non-owner / paid-out buyer is a
//!   real executor refusal). The listings render as a `Section{Menu}`; the actions fire real turns.
//! * [`inventory::InventoryOffering`] — a **read-surface** over [`dreggnet_asset`]: a player's owned
//!   notes (gear / cards / trophies) as a `Table` (name / rarity / kind / provenance / owner), the
//!   provenance + owner read off the real substrate.
//! * [`cheevo::CheevoShowcase`] — a **read-surface** over [`dreggnet_cheevo`]: the earned soulbound
//!   achievements + their proofs (the predicate, the witness, the run's turn count, the seal).
//! * [`guild::GuildPage`] — a **read-surface** over [`dreggnet_guild`]: the roster + the aggregate
//!   **verified-clears** leaderboard (every clear passed the no-cheat verify).
//!
//! ## Honest scope
//!
//! ONE of the four is a *playable* Offering (trade — its `advance` fires real transfer turns); the
//! other three are *read-surfaces* (`advance` is a read-only refusal, `render` is the payload). The
//! do-once reach is real: each `render` is a plain [`ViewNode`] tree, so the web one-line register
//! ([`register_surfaces`]) AND the discord/telegram/wechat renderers inherit it with no per-surface
//! code. NAMED NEXT (not built here): the rest of the feature Offerings (craft / companion / tavern /
//! party); the discord command shells (the generic `/offering` adapter gives discord the four for
//! free once registered); and the *games'* Offerings (which need `render_for(viewer)` for the hidden
//! hand + a coordinate-grid ViewNode — Tier C, gated on the game fold lanes).

pub mod cheevo;
pub mod guild;
pub mod inventory;
pub mod trade;

use deos_view::{MenuItem, ViewNode};
use dreggnet_offerings::OfferingHost;

pub use cheevo::CheevoShowcase;
pub use guild::GuildPage;
pub use inventory::{InventoryItem, InventoryOffering};
pub use trade::TradeOffering;

// ── Shared ViewNode builders — the ONE place these four surfaces compose the vocab, so every
//    surface reads the same and a renderer change is felt uniformly. ─────────────────────────

/// A plain `text(s)` leaf.
pub(crate) fn text(s: impl Into<String>) -> ViewNode {
    ViewNode::Text(s.into())
}

/// A titled, bordered `section(title, tag, ...children)` container (the uniform styled block).
pub(crate) fn section(title: impl Into<String>, tag: &str, children: Vec<ViewNode>) -> ViewNode {
    ViewNode::Section {
        title: title.into(),
        tag: tag.to_string(),
        children,
    }
}

/// A `row(...cells)` — a horizontal line of cells (a table row).
pub(crate) fn row(cells: Vec<ViewNode>) -> ViewNode {
    ViewNode::Row(cells)
}

/// A static `pill(text, tag)` status badge (leaf).
pub(crate) fn pill(text: impl Into<String>, tag: &str) -> ViewNode {
    ViewNode::Pill {
        text: text.into(),
        tag: tag.to_string(),
        slot: None,
        cases: Vec::new(),
    }
}

/// A `menu(...items)` — an actuation list of cap-gated `{label, turn, arg, enabled}` rows.
pub(crate) fn menu(items: Vec<MenuItem>) -> ViewNode {
    ViewNode::Menu { items }
}

/// Lift an offering's [`Action`](dreggnet_offerings::Action)s into `menu` rows (the affordance
/// `{turn, arg}` shape a renderer fires) — the same mapping `dreggnet-market`'s `render` uses.
pub(crate) fn action_menu(actions: Vec<dreggnet_offerings::Action>) -> Vec<MenuItem> {
    actions
        .into_iter()
        .map(|a| MenuItem {
            label: a.label,
            turn: a.turn,
            arg: a.arg,
            enabled: a.enabled,
        })
        .collect()
}

/// A short display handle for an opaque 32-byte key/seal/id — the first 6 hex chars (the
/// friendly projection a renderer would otherwise apply; done here so a `Text` cell reads clean).
pub(crate) fn short_hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(6);
    for b in bytes.iter().take(3) {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

/// **Register all four surfaces on an [`OfferingHost`]** — the do-once web/discord/telegram reach.
///
/// This is the ONE call a frontend makes to mount trade + inventory + cheevo + guild alongside the
/// market (it avoids editing `dreggnet-web`: the web's `catalog_default_host` calls this after
/// registering the dungeon/council/market, and the generic `/offering` discord adapter + the
/// telegram/wechat frontends reach the four the same way — each renders the SAME `render->ViewNode`).
/// The read-surfaces mount their populated `demo()` state; the trade market opens fresh per session.
pub fn register_surfaces(host: &mut OfferingHost) {
    host.register(
        "trade",
        "DreggNet Trade — a player market (list · settle an atomic asset swap)",
        TradeOffering::new(),
    );
    host.register(
        "inventory",
        "Inventory — your owned notes (gear · cards · trophies), provenance-checked",
        InventoryOffering::demo("Adventurer"),
    );
    host.register(
        "cheevos",
        "Achievements — earned soulbound proofs over verified runs",
        CheevoShowcase::demo(),
    );
    host.register(
        "guild",
        "Guild — the roster + the aggregate verified-clears leaderboard",
        GuildPage::demo("The Iron Wardens"),
    );
}
