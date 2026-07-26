//! # `dreggnet-surfaces` — the DO-ONCE frontend batch.
//!
//! An [`Offering`](dreggnet_offerings::Offering)'s [`render`](dreggnet_offerings::Offering::render)
//! returns a [`Surface`](dreggnet_offerings::Surface) — and a `Surface` IS a
//! [`deos_view::ViewNode`]. Every frontend (the native cockpit, `deos-view`'s web/discord/
//! telegram/wechat renderers, the test [`MockFrontend`](dreggnet_offerings::mock::MockFrontend))
//! is a *renderer of that one tree*. So writing `render -> ViewNode` ONCE per feature lights up
//! EVERY surface — the do-once path the frontend plan (`docs/FRONTEND-PLAN.md`) confirmed is ~80%
//! of the work. [`dreggnet_market`](../dreggnet_market/index.html) was the only prior new-domain
//! Offering; this crate now adds nine, following that reference:
//!
//! * [`trade::TradeOffering`] — a **playable market #2** over [`dreggnet_trade`]: list a good, then
//!   settle a real atomic **asset swap** (the seller's owned note crosses to the buyer for a
//!   trade-coin, each move a real owner-signed transfer turn — a non-owner / paid-out buyer is a
//!   real executor refusal). The listings render as a `Section{Menu}`; the actions fire real turns.
//! * [`inventory::InventoryOffering`] — an owned-notes surface over [`dreggnet_asset`]: a player's
//!   notes (gear / cards / trophies) as a `Table` (name / rarity / kind / provenance / holder), the
//!   provenance + holder read off the real substrate, plus one interactive move — **gift** a note to
//!   a friend (a real owner-signed transfer turn; a re-gift of a note you no longer hold is a real
//!   executor refusal).
//! * [`cheevo::CheevoShowcase`] — a **read-surface** over [`dreggnet_cheevo`]: the earned soulbound
//!   achievements + their proofs (the predicate, the witness, the run's turn count, the seal). Read
//!   by design — a cheevo is SOULBOUND (earned by a verified run, never transferred), so the
//!   substrate exposes no write to surface here.
//! * [`guild::GuildPage`] — the roster + the aggregate **verified-clears** leaderboard over
//!   [`dreggnet_guild`] (every clear passed the no-cheat verify), plus one interactive move —
//!   **admit** a pending applicant (a real cap grant + committed membership turn; a non-member's
//!   write is a real `CapabilityNotHeld` refusal).
//!
//! ## Batch 2 — the next four feature crates as Offerings
//!
//! * [`craft::CraftOffering`] — a **playable forge loop** over [`dreggnet_craft`]: pick a recipe,
//!   the forge consumes real material notes (the sink) + rolls a provably-fair quality, and mints a
//!   real owned output — `advance` fires a real craft turn (a below-floor / consumed-input craft is
//!   a real refusal).
//! * [`companion::CompanionOffering`] — a **playable hatch + collection** over [`dreggnet_companion`]:
//!   hatch a companion from a fair draw (a real owned note) + raise it through XP-gated committed
//!   turns; the collection renders as a `Table` of your companions + their live levels.
//! * [`tavern::TavernOffering`] — a **read-surface posting board** over the shared hub
//!   [`dreggnet_tavern`] models: presence + the LFG board + the party roster (render-only — the live
//!   node/mozjs post path stays off this light layer).
//! * [`party::PartyOffering`] — a **playable roster + fork ballot** over [`dreggnet_party`]: a seat
//!   acts in its role (a cross-role misplay is a real cap refusal) and the party resolves a fork via
//!   `advance_collective` (a real quorum-certified signed ballot into the shared world).
//! * [`quest::AshenmoorErrandOffering`] — a **playable faction-to-quest composition** over
//!   [`dreggnet_faction`] + [`dreggnet_quest`]: one identity earns committed Ember standing,
//!   passes its executor-gated trial, then completes the ordered errand. Both ledgers replay from
//!   genesis, and every landed move commits the owning actor into that same world turn.
//!
//! ## Honest scope
//!
//! *Playable* Offerings (their `advance`/`advance_collective` fire real committed turns): trade,
//! craft, companion, party, quest — and, at one move each, inventory (**gift**) + guild (**admit**). Pure
//! *read-surfaces* (`advance` is a read-only refusal, `render` is the payload): cheevo (soulbound —
//! nothing to write) and tavern (a read mirror + a `join` link-out to the live async node). The
//! do-once reach is real: each `render` is a plain [`ViewNode`] tree, so the web one-line register
//! ([`register_surfaces`]) AND the discord/telegram/wechat renderers inherit all nine with no
//! per-surface code — proven by the cross-backend golden tests (`tests/golden_render.rs`) that walk
//! each surface through the real `text`/`telegram`/`wechat`/`web` backends. NAMED NEXT (not built here): the
//! discord command shells (the generic `/offering` adapter gives discord these for free once
//! registered); a booted-node tavern post path (the mozjs-weight async surface). The *games'*
//! Offerings — once gated here as Tier C — are BUILT in their own crates and registered in the web
//! catalog: `dregg_multiway_tug::surface::TugOffering` (per-viewer `render_for` hidden-hand fog) and
//! `dregg_automatafl::surface::AutomataflOffering` (the `ViewNode::CoordGrid` board, rendered by
//! every backend).

pub mod cheevo;
pub mod companion;
pub mod craft;
pub mod guild;
pub mod inventory;
pub mod party;
#[cfg(feature = "private-raid")]
pub mod private_raid;
pub mod quest;
pub mod tavern;
pub mod trade;
pub mod world;

use deos_view::{MenuItem, ViewNode};
use dreggnet_offerings::OfferingHost;

pub use cheevo::CheevoShowcase;
pub use companion::CompanionOffering;
pub use craft::CraftOffering;
pub use guild::GuildPage;
pub use inventory::{InventoryItem, InventoryOffering};
pub use party::PartyOffering;
#[cfg(feature = "private-raid")]
pub use private_raid::{HostedProofAssignedRaidOffering, ProofAssignedRaidOffering};
pub use quest::AshenmoorErrandOffering;
pub use tavern::TavernOffering;
pub use trade::TradeOffering;
pub use world::{GameWorld, ItemRecord, Origin, SharedWorld};

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
            wants_text: a.wants_text,
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

/// **Register all nine surfaces on an [`OfferingHost`]** — the do-once web/discord/telegram reach.
///
/// This is the ONE call a frontend makes to mount trade + inventory + cheevo + guild + craft +
/// companion + quest + tavern + party alongside the market (it avoids editing `dreggnet-web`: the web's
/// `catalog_default_host` calls this after registering the dungeon/council/market, and the generic
/// `/offering` discord adapter + the telegram/wechat frontends reach them the same way — each
/// renders the SAME `render->ViewNode`).
///
/// **The craft / inventory / trade surfaces are mounted onto ONE [`SharedWorld`]** — one
/// [`dreggnet_asset::AssetWorld`], one item registry, one canonical player. So the demo IS the
/// composition: forge a Greatblade on the craft surface and it is in your inventory and listable on
/// your market stall, as the SAME note-cell (`dreggnet-saga`'s craft→trade handoff, in the shape
/// live coexisting surfaces need — see [`world`]). The remaining six mount their own state:
/// cheevo/guild/tavern are read-surfaces over other substrates, party has no asset ledger,
/// companion mints into its own `CompanionRoost`, and quest composes its own faction + errand
/// cells (the named next graduation is a single cross-ledger witness).
///
/// **Anonymous/demo only.** This mounts ONE world named for [`DEMO_PLAYER`], shared by every
/// session on the host — right for a single-player demo host, and WRONG for any host serving more
/// than one person (every viewer would read and write the same ledger, as "Adventurer"). A frontend
/// with identified viewers mounts one host per identity through [`register_surfaces_for`] — see
/// `dreggnet_catalog::PlayerWorlds`, the shared per-identity host registry.
pub fn register_surfaces(host: &mut OfferingHost) {
    register_surfaces_for(host, DEMO_PLAYER);
}

/// The canonical anonymous player label — the shelf [`register_surfaces`] mounts when there is no
/// identified viewer (a single-player demo host).
pub const DEMO_PLAYER: &str = "Adventurer";

/// **Register all nine surfaces on a world owned by `player`** — the per-identity mount.
///
/// Identical to [`register_surfaces`] except that the ONE [`SharedWorld`] carrying trade / craft /
/// inventory is seeded for `player` (their bench, their shelf, their stock), so the shelf label
/// every surface keys on is the viewer's own derived identity rather than a shared `"Adventurer"`.
///
/// **Isolation comes from the HOST, not from the label**: two identities are disjoint because they
/// are mounted on two hosts, each with its own world, forge, ledger and registry. Give each viewer
/// their own [`OfferingHost`] (as `dreggnet_catalog::PlayerWorlds` does, and as the Discord bot's
/// `build_player_host` does) — mounting two `register_surfaces_for` calls on ONE host would simply
/// have the second registration replace the first under the same nine keys.
pub fn register_surfaces_for(host: &mut OfferingHost, player: &str) {
    register_surfaces_in_world(host, SharedWorld::demo(player));
}

/// **Register the eight identity-owned surfaces for one player.** This is the production
/// per-identity mount: trade, inventory, cheevos, guild, craft, companion, quest, and tavern. `party` is
/// deliberately absent because it is a shared multi-identity table; mounting it in one host per
/// viewer would give every player a private lobby nobody else could join.
///
/// [`register_surfaces_for`] remains the complete nine-surface demo registrar. Frontends that
/// split identity-owned worlds from shared games should use this narrower registrar for their
/// player hosts and keep the globally registered [`PartyOffering`] on the shared catalog host.
pub fn register_player_surfaces_for(host: &mut OfferingHost, player: &str) {
    register_player_surfaces_in_world(host, SharedWorld::demo(player));
}

/// **Register all nine surfaces onto a caller-supplied [`SharedWorld`]** — the primitive behind
/// [`register_surfaces`] and [`register_surfaces_for`], for a frontend that wants to seed the
/// world itself (a different starting stock, a world it also reads directly).
pub fn register_surfaces_in_world(host: &mut OfferingHost, world: SharedWorld) {
    register_player_surfaces_in_world(host, world);
    host.register(
        "party",
        "Party — a seated roster + a quorum-certified fork ballot",
        PartyOffering::new(),
    );
}

/// Register only the eight surfaces whose state belongs to one identity. This is the primitive
/// behind [`register_player_surfaces_for`]; callers supplying their own world retain the same
/// craft → inventory → trade composition without accidentally privatizing the party lobby.
pub fn register_player_surfaces_in_world(host: &mut OfferingHost, world: SharedWorld) {
    host.register(
        "trade",
        "DreggNet Trade — a player market (list · settle an atomic asset swap)",
        TradeOffering::in_world(world.clone()),
    );
    host.register(
        "inventory",
        "Inventory — your owned notes (gear · cards · trophies), provenance-checked",
        InventoryOffering::in_world(world.clone()),
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
    host.register(
        "craft",
        "Forge — a provably-fair craft loop (consume materials · mint a bound output)",
        CraftOffering::in_world(world),
    );
    host.register(
        "companion",
        "Companions — hatch a fair-drawn companion · raise it through XP-gated turns",
        CompanionOffering::demo(),
    );
    host.register(
        quest::KEY,
        quest::DESCRIPTION,
        AshenmoorErrandOffering::new(),
    );
    host.register(
        "tavern",
        "Tavern — the shared hub: presence · the LFG board · the party roster",
        TavernOffering::demo("The Salted Tankard"),
    );
}

#[cfg(test)]
mod tests {
    //! Unit tests for the shared ViewNode vocab builders — the ONE place all nine surfaces compose
    //! the tree, so a regression here is felt uniformly. Driven, not named.
    use super::*;
    use deos_view::ViewNode;
    use dreggnet_offerings::Action;

    #[test]
    fn short_hex_is_the_first_three_bytes() {
        // Exactly six hex chars off the first three bytes; the tail is ignored (a stable handle).
        assert_eq!(short_hex(&[0xab, 0xcd, 0xef, 0x99, 0x00]), "abcdef");
        assert_eq!(short_hex(&[0x00, 0x01, 0x02]), "000102");
        // Fewer than three bytes: as many pairs as there are bytes (no panic).
        assert_eq!(short_hex(&[0x0f]), "0f");
        assert_eq!(short_hex(&[]), "");
    }

    #[test]
    fn builders_produce_the_expected_viewnode_variants() {
        assert!(matches!(text("hi"), ViewNode::Text(s) if s == "hi"));
        assert!(matches!(
            section("Title", "accent", vec![]),
            ViewNode::Section { title, tag, children }
                if title == "Title" && tag == "accent" && children.is_empty()
        ));
        assert!(matches!(row(vec![text("a")]), ViewNode::Row(cs) if cs.len() == 1));
        assert!(matches!(
            pill("badge", "good"),
            ViewNode::Pill { text, tag, .. } if text == "badge" && tag == "good"
        ));
    }

    #[test]
    fn action_menu_preserves_each_actions_turn_arg_and_enabled() {
        // The affordance mapping every surface's render relies on — label/turn/arg/enabled carried
        // through 1:1 (a renderer fires exactly `{turn, arg}`; a disabled row stays, shown locked).
        let actions = vec![
            Action::new("List Ember Cloak", "list", 0, true),
            Action::new("Buy Frost Charm", "buy", 2, false),
        ];
        let items = action_menu(actions);
        assert_eq!(items.len(), 2);
        assert_eq!(items[0].turn, "list");
        assert_eq!(items[0].arg, 0);
        assert!(items[0].enabled);
        assert_eq!(items[1].turn, "buy");
        assert_eq!(items[1].arg, 2);
        assert!(
            !items[1].enabled,
            "a disabled action stays in the menu, locked"
        );
        assert!(matches!(menu(items), ViewNode::Menu { items } if items.len() == 2));
    }
}
