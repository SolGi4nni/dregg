//! The bot's surfaces, authored ONCE as `deos-view` [`ViewNode`] cards and rendered
//! through the **Discord backend** (`deos_view::discord`).
//!
//! This is the discord-bot's end of the card-authored-once-renders-everywhere thesis: the
//! SAME [`ViewNode`] IR the desktop renders to gpui pixels and the browser renders to HTML
//! is, here, rendered to a serenity `CreateEmbed` (+ button components) by
//! [`deos_view::discord::render_card`]. A surface is a TREE — `vstack`/`row`/`text`/
//! `bind`/`button` — and the renderer decides what it looks like on Discord. The bot does
//! not hand-roll embeds for these surfaces; it authors the card and projects it.
//!
//! Each builder returns the structural embed (title/description/fields) + any button
//! components; the caller may chain presentation (`.color()`, `.footer()`) onto the embed
//! before sending — the tree owns the STRUCTURE, the surface owns the color.

use deos_view::ViewNode;
use deos_view::discord::{DiscordCard, render_card};

use crate::devnet::RecentEvent;

/// A `text` node (a description line / a row cell).
fn text(s: impl Into<String>) -> ViewNode {
    ViewNode::Text(s.into())
}

/// A `row` of `[name, value]` → one embed field (the renderer maps `row` → a field).
fn field_row(name: impl Into<String>, value: impl Into<String>) -> ViewNode {
    ViewNode::Row(vec![text(name), text(value)])
}

/// A `button` firing affordance `turn(arg)` — becomes a Discord button component whose
/// custom-id carries the affordance (`deos_view::discord::affordance_custom_id`).
fn button(label: impl Into<String>, turn: impl Into<String>, arg: i64) -> ViewNode {
    ViewNode::Button {
        label: label.into(),
        turn: turn.into(),
        arg,
    }
}

// ════════════════════════════════════════════════════════════════════════════
// (1) THE ACTIVITY FEED — a devnet event, authored as a card (routed LIVE).
// ════════════════════════════════════════════════════════════════════════════

/// The shared explorer reference builder ([`crate::explorer_link`]) — one rule for every
/// surface: `DREGG_EXPLORER_BASE` configured → a `[`id...`](…/explorer/{kind}/{id})` link;
/// no base → the FULL id as copyable code (never a dead link, never a truncated dead end).
use crate::explorer_link::{explorer_base, short_ref_with_base as explorer_ref};

/// A devnet activity event, authored as a `ViewNode` card and rendered to a Discord embed.
///
/// The tree is `vstack[ text(summary), row(Time…), row(Cell…), row(Transaction…) ]`: the
/// summary becomes the description, each `row` an embed field. When `DREGG_EXPLORER_BASE` is
/// configured, explorer links ride as markdown inside the `text` cells (the IR carries arbitrary
/// strings); otherwise the cell/tx ids render as plain code text ([`explorer_ref`]). The caller
/// applies `.color()`/`.footer()`.
pub fn activity_event_card(title: &str, event: &RecentEvent) -> DiscordCard {
    activity_event_card_with_base(title, event, explorer_base().as_deref())
}

/// [`activity_event_card`] with the explorer base explicit (the pure core the tests drive).
fn activity_event_card_with_base(
    title: &str,
    event: &RecentEvent,
    base: Option<&str>,
) -> DiscordCard {
    let mut children = vec![text(&event.summary)];

    if !event.timestamp.is_empty() {
        children.push(field_row("Time", &event.timestamp));
    }
    if let Some(cell_id) = &event.cell_id {
        children.push(field_row("Cell", explorer_ref(base, "cell", cell_id, 16)));
    }
    if let Some(tx_hash) = &event.tx_hash {
        children.push(field_row(
            "Transaction",
            explorer_ref(base, "tx", tx_hash, 12),
        ));
    }

    render_card(title, &ViewNode::VStack(children), &[])
}

// ════════════════════════════════════════════════════════════════════════════
// (2) THE GALLERY — a list of items, authored as a card.
// ════════════════════════════════════════════════════════════════════════════

/// One gallery tile (artwork / auction) for [`gallery_card`].
pub struct GalleryItem {
    /// The item's display name.
    pub name: String,
    /// A one-line blurb (artist · price · id, the surface's choice).
    pub blurb: String,
}

/// A gallery (artworks / auctions), authored as a `ViewNode` card: a `vstack` whose rows are
/// the tiles (`name → blurb` fields). The SAME shape the web renderer's `render_gallery_document`
/// lays out as tiles — here projected to a Discord embed of fields.
pub fn gallery_card(title: &str, items: &[GalleryItem]) -> DiscordCard {
    let mut children: Vec<ViewNode> = Vec::with_capacity(items.len());
    for it in items {
        children.push(field_row(&it.name, &it.blurb));
    }
    render_card(title, &ViewNode::VStack(children), &[])
}

// ════════════════════════════════════════════════════════════════════════════
// (3) IDENTITY / PRESENCE — a handle card + a presence card.
// ════════════════════════════════════════════════════════════════════════════

/// A custodial handle card (an AppCipherclerk handle), authored as a `ViewNode`: the handle
/// name heads it, its cell + status are fields, and (optionally) cap-gated affordance buttons
/// ride along — the affordance is in each button's custom-id (the verified-turn payload).
pub fn handle_card(
    handle: &str,
    cell_hex: &str,
    status: &str,
    affordances: &[(&str, &str)],
) -> DiscordCard {
    let short = if cell_hex.len() > 16 {
        &cell_hex[..16]
    } else {
        cell_hex
    };
    let mut children = vec![
        text(format!("Handle `@{handle}`")),
        field_row("Cell", format!("`{short}...`")),
        field_row("Status", status),
    ];
    for (label, turn) in affordances {
        children.push(button(*label, *turn, 0));
    }
    render_card(&format!("@{handle}"), &ViewNode::VStack(children), &[])
}

/// A presence card (the identity/presence surface), authored as a `ViewNode`: status,
/// session duration, last-online — each a field. Mirrors `commands/presence.rs`'s embed shape.
pub fn presence_card(
    who: &str,
    status: &str,
    session_duration: &str,
    last_online: &str,
) -> DiscordCard {
    let tree = ViewNode::VStack(vec![
        text(format!("Presence for {who}")),
        field_row("Status", status),
        field_row("Session Duration", session_duration),
        field_row("Last Online", last_online),
    ]);
    render_card("Presence", &tree, &[])
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The activity-feed surface, authored as a card, renders to the SAME embed shape the
    /// hand-rolled `event_to_embed` produced: a title, a summary description, and Time/Cell/
    /// Transaction fields — but now from the renderer-independent `ViewNode` IR.
    #[test]
    fn activity_event_renders_to_the_expected_embed_shape() {
        let event = RecentEvent {
            event_type: "Transfer".to_string(),
            summary: "alice → bob: 100 DREGG".to_string(),
            timestamp: "2026-06-25T00:00:00Z".to_string(),
            cell_id: Some("abcdef0123456789abcdef".to_string()),
            tx_hash: Some("deadbeefcafef00d".to_string()),
        };
        let card = activity_event_card_with_base(
            "\u{1f7e2} Transfer",
            &event,
            Some("https://explorer.example.test"),
        );
        let embed = serde_json::to_value(&card.embed).expect("embed serializes");

        assert_eq!(embed["title"], "\u{1f7e2} Transfer");
        assert!(
            embed["description"]
                .as_str()
                .unwrap()
                .contains("alice \u{2192} bob"),
            "the summary became the description"
        );
        let fields = embed["fields"].as_array().expect("rows became fields");
        let names: Vec<&str> = fields.iter().map(|f| f["name"].as_str().unwrap()).collect();
        assert_eq!(names, vec!["Time", "Cell", "Transaction"]);
        // The explorer link survived the projection (markdown carried in the text cell),
        // rooted at the CONFIGURED base.
        assert!(
            fields[1]["value"]
                .as_str()
                .unwrap()
                .contains("https://explorer.example.test/explorer/cell/"),
            "the cell link rode the card into the embed field"
        );
    }

    /// With NO explorer base configured (the default), the ids render as plain copyable code
    /// text — the FULL id, a non-link — never the dead hardcoded fg-goose URL a browser can't
    /// reach (the shared `explorer_link` rule: copy-paste must work when the link is absent).
    #[test]
    fn without_an_explorer_base_the_ids_are_plain_text_not_dead_links() {
        let event = RecentEvent {
            event_type: "Transfer".to_string(),
            summary: "alice → bob: 100 DREGG".to_string(),
            timestamp: String::new(),
            cell_id: Some("abcdef0123456789abcdef".to_string()),
            tx_hash: Some("deadbeefcafef00d".to_string()),
        };
        let card = activity_event_card_with_base("Transfer", &event, None);
        let embed = serde_json::to_value(&card.embed).unwrap();
        let fields = embed["fields"].as_array().unwrap();
        for f in fields {
            let value = f["value"].as_str().unwrap();
            assert!(!value.contains("http"), "no link without a base: {value}");
            assert!(
                !value.contains("fg-goose"),
                "the dead domain is gone: {value}"
            );
        }
        assert_eq!(fields[0]["value"], "`abcdef0123456789abcdef`");
        assert_eq!(fields[1]["value"], "`deadbeefcafef00d`");

        // A configured base turns the same ids into real links.
        assert_eq!(
            explorer_ref(Some("https://x.test"), "tx", "deadbeefcafef00d", 12),
            "[`deadbeefcafe...`](https://x.test/explorer/tx/deadbeefcafef00d)"
        );
    }

    #[test]
    fn an_event_without_optional_fields_renders_description_only() {
        let event = RecentEvent {
            event_type: "Block".to_string(),
            summary: "block 42 sealed".to_string(),
            timestamp: String::new(),
            cell_id: None,
            tx_hash: None,
        };
        let card = activity_event_card("Block", &event);
        let embed = serde_json::to_value(&card.embed).unwrap();
        assert!(embed["description"].as_str().unwrap().contains("block 42"));
        // No optional rows → no fields.
        assert!(
            embed["fields"]
                .as_array()
                .map(|a| a.is_empty())
                .unwrap_or(true)
        );
    }

    #[test]
    fn gallery_card_renders_one_field_per_tile() {
        let items = vec![
            GalleryItem {
                name: "Sunrise".into(),
                blurb: "by ada · 50 DEC".into(),
            },
            GalleryItem {
                name: "Dusk".into(),
                blurb: "by bee · 75 DEC".into(),
            },
        ];
        let card = gallery_card("Gallery", &items);
        let embed = serde_json::to_value(&card.embed).unwrap();
        let fields = embed["fields"].as_array().unwrap();
        assert_eq!(fields.len(), 2);
        assert_eq!(fields[0]["name"], "Sunrise");
        assert_eq!(fields[1]["value"], "by bee \u{b7} 75 DEC");
    }

    #[test]
    fn handle_card_carries_affordance_buttons_with_routable_custom_ids() {
        let card = handle_card(
            "ada",
            "00112233445566778899aabb",
            "live",
            &[("Rotate Key", "rotate"), ("Revoke", "revoke")],
        );
        let embed = serde_json::to_value(&card.embed).unwrap();
        assert_eq!(embed["title"], "@ada");
        // The affordances became button components, the verb in each custom-id.
        let rows = serde_json::to_value(&card.components).unwrap();
        let buttons = rows[0]["components"].as_array().unwrap();
        assert_eq!(buttons.len(), 2);
        assert_eq!(buttons[0]["custom_id"], "deosturn:rotate:0");
        assert_eq!(buttons[1]["custom_id"], "deosturn:revoke:0");
    }

    #[test]
    fn presence_card_renders_the_three_status_fields() {
        let card = presence_card("<@123>", "Online", "2h 15m", "now");
        let embed = serde_json::to_value(&card.embed).unwrap();
        let fields = embed["fields"].as_array().unwrap();
        let names: Vec<&str> = fields.iter().map(|f| f["name"].as_str().unwrap()).collect();
        assert_eq!(names, vec!["Status", "Session Duration", "Last Online"]);
    }
}
