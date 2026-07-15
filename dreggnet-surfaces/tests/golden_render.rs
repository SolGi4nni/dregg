//! # Cross-backend GOLDEN render tests — the do-once promise, PROVEN.
//!
//! The whole point of this crate is *do-once*: each surface writes `render -> ViewNode` ONCE, and
//! every frontend renders it for free. This suite drives each surface's real [`ViewNode`] through
//! the **actual** gpui-free `deos-view` bake backends a frontend uses —
//! [`text::render_text`](deos_view::text::render_text) (the shared prose walk),
//! [`TelegramBackend`](deos_view::telegram::TelegramBackend), the WeChat
//! [`render_message`](deos_view::wechat::render_message) (prose + the NUMBERED reply list that
//! carries the actuations), and the [`web::render_html`](deos_view::web::render_html) DOM string —
//! and asserts golden, stable output. A broken surface (an empty tree, a dropped section, a lost
//! action) fails a concrete assertion here, on every channel at once.
//!
//! The cross-backend INVARIANTS proven for all eight surfaces:
//!  * the Telegram text IS the shared prose walk (`telegram == text`) — one walk, never two;
//!  * the WeChat message body opens with that same prose, then appends its numbered reply block;
//!  * the WeChat numbered options are EXACTLY the tree's actuations (the do-once affordance reach —
//!    a playable surface's moves become numbered replies on a button-less channel with no per-
//!    surface code); and
//!  * the web HTML is a non-empty DOM string carrying the surface's title.

use deos_view::telegram::TelegramBackend;
use deos_view::text::render_text;
use deos_view::web::render_html;
use deos_view::wechat::render_message;
use deos_view::{SurfaceBackend, actuations};

use dreggnet_offerings::{Action, DreggIdentity, Offering, SessionConfig};
use dreggnet_surfaces::{
    CheevoShowcase, CompanionOffering, CraftOffering, GuildPage, InventoryOffering, PartyOffering,
    TavernOffering, TradeOffering,
};

fn actor() -> DreggIdentity {
    DreggIdentity("golden".into())
}
fn act(turn: &str, arg: i64) -> Action {
    Action::new(turn, turn, arg, true)
}

/// Everything the four real backends emit for one surface render.
struct Rendered {
    text: String,
    telegram: String,
    wechat_content: String,
    wechat_opts: usize,
    html: String,
    actuations: usize,
}

/// Render `o`'s `s` through every real bake backend + assert the cross-backend invariants that hold
/// for ALL surfaces, then hand the pieces back for per-surface golden assertions.
fn render_all<O: Offering>(o: &O, s: &O::Session, title_word: &str) -> Rendered {
    let surface = o.render(s);
    let root = surface.view();

    let text = render_text(root);
    let telegram = TelegramBackend.render(root, &[]);
    let msg = render_message(root);
    let html = render_html(root, &[]);
    let acts = actuations(root);

    // INVARIANT 1 — the Telegram backend IS the shared prose walk.
    assert_eq!(telegram, text, "telegram render is the shared text walk");
    // INVARIANT 2 — the WeChat body opens with that same prose.
    assert!(
        msg.content.starts_with(&text),
        "wechat content opens with the shared prose:\n--- text ---\n{text}\n--- wechat ---\n{}",
        msg.content
    );
    // INVARIANT 3 — the WeChat numbered options ARE exactly the tree's actuations (the affordance
    // reach — one option per actuation, in walk order).
    assert_eq!(
        msg.options.len(),
        acts.len(),
        "wechat surfaces every actuation as a numbered reply"
    );
    for (i, (opt, a)) in msg.options.iter().zip(acts.iter()).enumerate() {
        assert_eq!(opt.index, i + 1, "wechat replies are 1-based, in order");
        assert_eq!(
            opt.turn, a.turn,
            "the numbered reply fires the actuation's turn"
        );
        assert_eq!(opt.arg, a.arg, "…with its arg");
    }
    // INVARIANT 4 — the web HTML is a non-empty DOM string carrying the title.
    assert!(!html.is_empty(), "web renders a non-empty DOM string");
    assert!(
        html.contains(title_word),
        "web HTML carries the `{title_word}` title"
    );

    Rendered {
        text,
        telegram,
        wechat_content: msg.content,
        wechat_opts: msg.options.len(),
        html,
        actuations: acts.len(),
    }
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// EXACT goldens — the empty-state prose is small + stable; pin it byte-for-byte on every channel.
// ═══════════════════════════════════════════════════════════════════════════════════════════

#[test]
fn empty_inventory_is_byte_stable_across_backends() {
    let offering = InventoryOffering::new("Newcomer");
    let s = offering.open(SessionConfig::default()).expect("open");
    let r = render_all(&offering, &s, "Inventory");

    const GOLDEN: &str = "Inventory — Newcomer\n\
        — Owner\n\
        Newcomer · 0 note(s) · 0 held · 0 gifted\n\
        — Items\n\
        No items owned yet — clear a run or trade for a drop.";

    assert_eq!(r.text, GOLDEN, "the empty-inventory prose is byte-stable");
    assert_eq!(r.telegram, GOLDEN, "…identically on telegram");
    // No actions on an empty inventory → the WeChat body is the bare prose (no reply block).
    assert_eq!(
        r.wechat_content, GOLDEN,
        "…and on wechat (no numbered block)"
    );
    assert_eq!(r.wechat_opts, 0, "an empty inventory offers no replies");
    assert_eq!(r.actuations, 0);
}

#[test]
fn empty_guild_prose_is_stable() {
    let offering = GuildPage::new("Nascent Order");
    let s = offering.open(SessionConfig::default()).expect("open");
    let r = render_all(&offering, &s, "Guild");

    // The empty-guild prose walks the header, the empty roster, and the (all-zero) leaderboard —
    // stable line-for-line on every channel.
    assert_eq!(
        r.text,
        "Guild — Nascent Order\n\
         — Guild\n\
         Nascent Order · 0 member(s)\n\
         — Roster\n\
         No members yet — admit a founder.\n\
         — Leaderboard (aggregate proven)\n\
         Verified clears\n0\n\
         Total verified turns\n0\n\
         Survivors\n0\n\
         Members\n0",
        "the empty-guild prose is byte-stable"
    );
    assert_eq!(
        r.wechat_opts, 0,
        "an empty guild has no applicants to admit"
    );
    let _ = &r.telegram; // proven equal to text by the shared invariant
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// The READ surfaces — content present on every channel; no actuations (cheevo) / the link-out only.
// ═══════════════════════════════════════════════════════════════════════════════════════════

#[test]
fn cheevo_showcase_golden_read_surface() {
    let offering = CheevoShowcase::demo();
    let s = offering.open(SessionConfig::default()).expect("open");
    let r = render_all(&offering, &s, "Achievements");

    // The earner + the witness prose reach every channel (pills — the achievement titles — are the
    // affordance-free badge layer and do not project to prose; the text cells do).
    assert!(r.text.contains("Ada"), "the earner renders");
    assert!(
        r.text.contains("reached depth 3") || r.text.contains("won in 4 turns"),
        "the witness renders: {}",
        r.text
    );
    // Soulbound → nothing to actuate; the WeChat message is pure prose (no numbered block).
    assert_eq!(r.actuations, 0, "a read-only showcase surfaces no moves");
    assert_eq!(r.wechat_content, r.text);
}

#[test]
fn tavern_golden_read_mirror_with_link_out() {
    let offering = TavernOffering::demo("The Salted Tankard");
    let s = offering.open(SessionConfig::default()).expect("open");
    let r = render_all(&offering, &s, "Tavern");

    assert!(r.text.contains("The Salted Tankard"), "the hall renders");
    assert!(
        r.text.contains("LFG the Salt Shore — need a healer"),
        "an LFG post renders: {}",
        r.text
    );
    // The DECIDED story: exactly one actuation — the `join` link-out to the live node — surfaces as
    // the single numbered WeChat reply (the read mirror carries the way to reach the real transport).
    assert_eq!(r.actuations, 1, "just the join link-out");
    assert_eq!(r.wechat_opts, 1);
    assert!(
        r.wechat_content.contains("Enter The Salted Tankard"),
        "the join link-out is the numbered reply: {}",
        r.wechat_content
    );
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// The PLAYABLE surfaces — the moves become numbered WeChat replies (the do-once actuation reach).
// ═══════════════════════════════════════════════════════════════════════════════════════════

#[test]
fn trade_actions_become_numbered_wechat_replies() {
    let offering = TradeOffering::new();
    let mut s = offering.open(SessionConfig::default()).expect("open");

    // At open: three `list` actions → three numbered replies, each a `list` turn.
    let r = render_all(&offering, &s, "DreggNet Trade");
    assert!(r.wechat_opts >= 3, "the list moves surface as replies");
    let msg = render_message(offering.render(&s).view());
    assert!(
        msg.options
            .iter()
            .any(|o| o.turn == "list" && o.label.contains("List")),
        "a numbered `list` reply is present"
    );

    // After a list, a `buy` reply appears (the actuation reach tracks state).
    assert!(offering.advance(&mut s, act("list", 0), actor()).landed());
    let msg = render_message(offering.render(&s).view());
    assert!(
        msg.options.iter().any(|o| o.turn == "buy"),
        "listing a good adds a numbered `buy` reply"
    );
}

#[test]
fn inventory_gift_moves_become_numbered_wechat_replies() {
    let offering = InventoryOffering::demo("Adventurer");
    let mut s = offering.open(SessionConfig::default()).expect("open");

    let r = render_all(&offering, &s, "Inventory");
    // Five owned notes → five `gift` replies; the item names reach the prose.
    assert_eq!(r.actuations, 5, "a gift move per owned note");
    assert_eq!(r.wechat_opts, 5);
    assert!(
        r.text.contains("Ember Cloak"),
        "an item name renders in prose"
    );
    let msg = render_message(offering.render(&s).view());
    assert!(
        msg.options.iter().all(|o| o.turn == "gift"),
        "every reply is a gift"
    );

    // After gifting one away, only four remain giftable on every channel.
    assert!(offering.advance(&mut s, act("gift", 0), actor()).landed());
    let r = render_all(&offering, &s, "Inventory");
    assert_eq!(r.wechat_opts, 4, "the gifted note is no longer a reply");
}

#[test]
fn guild_admit_moves_become_numbered_wechat_replies() {
    let offering = GuildPage::demo("The Iron Wardens");
    let mut s = offering.open(SessionConfig::default()).expect("open");

    let r = render_all(&offering, &s, "Guild");
    // Two pending applicants → two `admit` replies; a member name reaches the prose.
    assert_eq!(r.actuations, 2, "an admit move per applicant");
    assert_eq!(r.wechat_opts, 2);
    assert!(r.text.contains("Aria"), "a member renders in prose");
    let msg = render_message(offering.render(&s).view());
    assert!(msg.options.iter().all(|o| o.turn == "admit"));

    // After admitting one, one reply remains.
    assert!(offering.advance(&mut s, act("admit", 0), actor()).landed());
    let r = render_all(&offering, &s, "Guild");
    assert_eq!(r.wechat_opts, 1, "one applicant left to admit");
}

#[test]
fn craft_party_companion_render_across_backends() {
    // The remaining playable surfaces render valid non-empty prose + carry their moves as replies.
    let craft = CraftOffering::new();
    let cs = craft.open(SessionConfig::default()).expect("open");
    let r = render_all(&craft, &cs, "Forge");
    assert!(r.actuations >= 2, "craftable recipes surface as replies");
    assert!(!r.text.is_empty());

    let party = PartyOffering::new();
    let ps = party.open(SessionConfig::default()).expect("open");
    let r = render_all(&party, &ps, "Party");
    assert!(r.actuations >= 1, "seat moves surface as replies");

    let comp = CompanionOffering::demo();
    let ds = comp.open(SessionConfig::default()).expect("open");
    let r = render_all(&comp, &ds, "Companions");
    assert!(!r.text.is_empty() && !r.html.is_empty());
}
