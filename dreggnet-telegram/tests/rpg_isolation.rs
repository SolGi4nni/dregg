//! **THE PER-IDENTITY INVENTORY ISOLATION FALSIFIER, DRIVEN THROUGH THE TELEGRAM HOST.**
//!
//! The bot↔game review's last live CRITICAL: every Telegram player shared ONE inventory, because
//! the eight RPG feature surfaces (trade / inventory / craft / …) were mounted on the ONE shared
//! `SharedWorld::demo("Adventurer")` catalog host — so one presser could forge an item and it
//! appeared in another presser's inventory. This proves the fix over the real host router (no
//! token, no network — `MockTransport`):
//!
//! - **(a) ISOLATION** — two different Telegram users (`ALICE` / `BOB`) have DISJOINT RPG worlds:
//!   alice forges a Greatblade on `craft`, it is on HER `inventory`, and bob's `inventory` — a
//!   live, seeded world of his own — does not hold it.
//! - **(b) THE REGRESSION GUARD** — a SHARED multi-party table (`council`) is still shared, NOT
//!   split per-identity: alice proposes and BOB approves the SAME proposal, reaching the 2-of-2
//!   quorum and enacting — only possible if both press ONE shared council.
//! - **(c) PARTY IS SHARED** — two users in one group claim distinct roles in one live roster.

use dreggnet_telegram::api::encode_callback;
use dreggnet_telegram::host::{HostPress, TelegramHost};
use dreggnet_telegram::transport::{MessageId, MockTransport};
use dreggnet_telegram::{CallbackQuery, TelegramFrontend};

const BOT_SECRET: [u8; 32] = [7u8; 32];
const ALICE: u64 = 1001;
const BOB: u64 = 1002;

fn host() -> TelegramHost<MockTransport> {
    TelegramHost::new(BOT_SECRET, MockTransport::new(), &[ALICE, BOB])
}

/// The current rendered text of `key`'s surface message in `chat`.
fn surface_text(h: &TelegramHost<MockTransport>, chat: i64, key: &str) -> String {
    let surface = TelegramFrontend::<MockTransport>::surface_id(chat, None, key);
    let msg: MessageId = h
        .frontend()
        .session(&surface)
        .and_then(|s| s.message_id)
        .unwrap_or_else(|| panic!("{key} has a live surface in chat {chat}"));
    h.frontend()
        .transport()
        .visible(msg)
        .unwrap_or_else(|| panic!("{key}'s surface message is live"))
        .text
        .clone()
}

/// **(a) Two identities' RPG worlds are ISOLATED.** Alice (in her DM) forges a Greatblade on
/// `craft`; it is on HER `inventory`, and bob's `inventory` (in his own DM) does not hold it.
#[test]
fn two_identities_have_isolated_rpg_inventories() {
    let mut h = host();
    let alice_chat: i64 = 5001; // positive → a DM (single reader)
    let bob_chat: i64 = 5002;

    // Alice opens her forge and forges the safe Greatblade (bench recipe 0) — one real landed turn.
    h.open("craft", alice_chat, None, ALICE)
        .expect("craft opens");
    match h.press(CallbackQuery::press(
        alice_chat,
        ALICE,
        encode_callback("craft", 0),
    )) {
        HostPress::Advanced { key, outcome } => {
            assert_eq!(key, "craft");
            assert!(
                outcome.landed(),
                "alice's forge lands a real receipt: {outcome:?}"
            );
        }
        other => panic!("alice's forge must advance the craft, got {other:?}"),
    }

    // …and it is on ALICE's own inventory shelf (craft → inventory compose over her ONE world).
    h.open("inventory", alice_chat, None, ALICE)
        .expect("alice's inventory opens");
    let alice_inv = surface_text(&h, alice_chat, "inventory");
    assert!(
        alice_inv.contains("Greatblade"),
        "alice's forged Greatblade is on her own inventory: {alice_inv}"
    );

    // BOB — a different identity — opens HIS inventory (a live, seeded world of his own) and it
    // holds NO note alice forged. (Before the fix, this listed alice's Greatblade: one shared world.)
    h.open("inventory", bob_chat, None, BOB)
        .expect("bob's inventory opens");
    let bob_inv = surface_text(&h, bob_chat, "inventory");
    assert!(
        !bob_inv.contains("Greatblade"),
        "bob's inventory holds no note alice forged — the worlds are disjoint: {bob_inv}"
    );
}

/// **(b) THE REGRESSION GUARD — a shared table stays shared.** `council` is a multi-party offering,
/// so it must NOT be split per-identity by over-applying the RPG fix. In one group chat alice
/// proposes proposal 0 and BOB approves the SAME proposal; the 2-of-2 quorum is reached and alice
/// enacts — which is only possible if both press ONE shared council.
#[test]
fn a_shared_council_is_not_split_per_identity() {
    let mut h = host();
    let chat: i64 = -6001; // negative → a group (a shared, full-information table)

    h.open("council", chat, None, ALICE).expect("council opens");

    // alice proposes catalog item 0 ("Fund the archive").
    match h.press(CallbackQuery::press(
        chat,
        ALICE,
        encode_callback("propose", 0),
    )) {
        HostPress::Advanced { key, outcome } => {
            assert_eq!(key, "council");
            assert!(outcome.landed(), "alice's proposal lands: {outcome:?}");
        }
        other => panic!("alice's propose must advance the council, got {other:?}"),
    }

    // alice approves proposal 0.
    match h.press(CallbackQuery::press(
        chat,
        ALICE,
        encode_callback("approve", 0),
    )) {
        HostPress::Advanced { outcome, .. } => {
            assert!(outcome.landed(), "alice's approve lands: {outcome:?}")
        }
        other => panic!("alice's approve must advance the council, got {other:?}"),
    }

    // BOB approves the SAME proposal alice made — this only counts toward the quorum because it is
    // the SAME shared council (a per-identity split would give bob a fresh council of his own).
    match h.press(CallbackQuery::press(
        chat,
        BOB,
        encode_callback("approve", 0),
    )) {
        HostPress::Advanced { outcome, .. } => {
            assert!(
                outcome.landed(),
                "bob's approve lands on the shared council: {outcome:?}"
            )
        }
        other => panic!("bob's approve must advance the SHARED council, got {other:?}"),
    }

    // With the 2-of-2 quorum reached, alice enacts proposal 0 — the shared-table payoff.
    match h.press(CallbackQuery::press(
        chat,
        ALICE,
        encode_callback("enact", 0),
    )) {
        HostPress::Advanced { outcome, .. } => assert!(
            outcome.landed(),
            "the 2-of-2 quorum enacts on the ONE shared council: {outcome:?}"
        ),
        other => panic!("the quorum must let alice enact on the shared council, got {other:?}"),
    }
}

/// **(c) THE PARTY ROUTING FALSIFIER.** Alice and Bob claim different roles from one group-chat
/// surface; the resulting message contains one two-player roster. Per-identity routing would leave
/// each user in a separate one-role lobby.
#[test]
fn a_party_lobby_is_shared_between_group_members() {
    let mut h = host();
    let chat: i64 = -6002;

    h.open("party", chat, None, ALICE).expect("party opens");
    match h.press(CallbackQuery::press(
        chat,
        ALICE,
        encode_callback("claim-role", 0),
    )) {
        HostPress::Advanced { outcome, .. } => {
            assert!(outcome.landed(), "alice claims Tank: {outcome:?}")
        }
        other => panic!("alice's claim must advance the party, got {other:?}"),
    }
    match h.press(CallbackQuery::press(
        chat,
        BOB,
        encode_callback("claim-role", 1),
    )) {
        HostPress::Advanced { outcome, .. } => {
            assert!(outcome.landed(), "bob claims Scout: {outcome:?}")
        }
        other => panic!("bob's claim must advance the same party, got {other:?}"),
    }

    let party = surface_text(&h, chat, "party");
    assert!(
        party.contains("2 / 4 roles"),
        "the shared group lobby contains both players: {party}"
    );
}
