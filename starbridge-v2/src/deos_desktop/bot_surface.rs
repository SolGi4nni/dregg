//! **THE DISCORD-BOT SURFACE ON THE deos DESKTOP** — the desktop face of the one
//! dregg-driven bot.
//!
//! The `discord-bot` is a custodial dregg peer: a Discord slash command turns into a
//! REAL signed dregg turn on the node, recorded as an activity and reflected to a
//! channel. This surface gives that SAME bot a desktop face: a "discord-bot" card,
//! reachable via the Spotter, that
//!
//!   1. **drives the bot's ops as dregg turns ON-CHAIN** — register a name, attest
//!      presence, issue a credential. A desktop drive is the SAME op a Discord
//!      command fires, and it is delivered the on-chain way: the desktop submits a
//!      real dregg turn to the bot's **command cell** ([`command_cell`]) — the
//!      chain is the message bus. The op rides as the command cell's committed
//!      state ([`drive_command_on_world`] on the embedded verified [`World`], or
//!      the same turn against a live node); the bot's `bot_reactor` WATCHES that
//!      cell and reacts. There is NO HTTP command path (the legacy [`op_request`]
//!      body is relegated), and
//!   2. **renders the bot's activity feed as a live desktop card** — the bot's
//!      `GET /api/apps/activity/recent` folded into a portable [`deos_view::ViewNode`]
//!      (the SAME card shape the bot renders as a Discord embed via
//!      `deos_view::discord` — `discord-bot/src/cards.rs`), painted natively in a
//!      `ViewNodePane` window.
//!
//! So the desktop and Discord are two faces of ONE dregg-driven bot: a drive on
//! either face is the same dregg op; the activity is one feed rendered to both.
//!
//! ## What is real vs. the seam
//!
//! - **Real (in-session, no live bot):** [`drive_command_on_world`] lands a
//!   genuine dregg command turn to the [`command_cell`] on the embedded verified
//!   executor (a `TurnReceipt`, a committed state change carrying the op) — the
//!   on-chain message the bot's reactor reads; [`activity_card`] folds the feed
//!   into a real `ViewNode` the native renderer paints.
//! - **The seam (named):** against a LIVE node the SAME command turn is submitted
//!   to the node (so the receipt is the node's and the bot's reactor sees it over
//!   the node's event/state surface). The command encoding (slots + JSON-bytes
//!   payload, [`CMD_SEQ_SLOT`]/[`CMD_LEN_SLOT`]/[`CMD_PAYLOAD_BASE`]) mirrors
//!   `discord-bot`'s `deos_drive` exactly, so the bot decodes the desktop's
//!   on-chain command byte-for-byte.
//! - **Relegated (HTTP):** [`op_request`] (`POST /api/op`) is NO LONGER the command
//!   path; it survives only as a legacy wire body. The command path is the on-chain
//!   turn.

use serde::{Deserialize, Serialize};

use dregg_types::CellId;

use dregg_turn::action::Effect;

use crate::world::{World, set_field};

/// The state slot a presence attestation writes its epoch into (matches the bot's
/// `deos_drive::PRESENCE_SLOT` — presence as a witnessed, receipted on-ledger state).
pub const PRESENCE_SLOT: usize = 10;

/// The slot a name registration writes its name-hash into (the nameservice
/// `NAME_HASH_SLOT`).
pub const NAME_HASH_SLOT: usize = 2;

/// The slot a credential issuance bumps (a running count of credentials issued to the
/// cell — the local-World stand-in for the credential turn).
pub const CRED_COUNT_SLOT: usize = 11;

/// The deterministic anchor cell the desktop hosts the discord-bot surface window
/// under — a distinct, non-ledger cell (like the World-Board's) so the bot card opens
/// as its OWN `ViewNodePane` window. The render path special-cases this cell to paint
/// the activity card instead of the World-Status panel.
pub fn bot_surface_window_cell() -> CellId {
    CellId::from_bytes([0xB0u8; 32]) // 'B0t'
}

/// Whether `cell` keys the discord-bot surface window (drives the pane header + body).
pub fn is_bot_surface(cell: &CellId) -> bool {
    cell == &bot_surface_window_cell()
}

/// **The ops the desktop can drive on the bot as dregg turns.** The wire shape mirrors
/// `discord-bot`'s `deos_drive::BotOp` exactly (tagged `op`, snake_case), so
/// [`op_request`] serializes to the body the bot's `POST /api/op` accepts.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "op", rename_all = "snake_case")]
pub enum BotOp {
    /// Register a name on the bot/user cell (the nameservice `register_name` turn).
    RegisterName {
        /// The name to bind.
        name: String,
    },
    /// Attest presence ON-LEDGER (a receipted `SetField(PRESENCE_SLOT, epoch)`).
    AttestPresence,
    /// Issue a verifiable credential to the cell (the Starbridge identity turn).
    IssueCredential {
        /// The credential schema name (`kyc` / `gov_id` / `employment`).
        schema: String,
        /// The credential attributes as a JSON object.
        attributes: serde_json::Value,
    },
}

impl BotOp {
    /// The reader-legible verb shown on the desktop card / Spotter row.
    pub fn label(&self) -> String {
        match self {
            BotOp::RegisterName { name } => format!("Register name “{name}”"),
            BotOp::AttestPresence => "Attest presence (online)".to_string(),
            BotOp::IssueCredential { schema, .. } => format!("Issue {schema} credential"),
        }
    }

    /// The activity-feed action label this op records under (stable across faces).
    pub fn action_label(&self) -> &'static str {
        match self {
            BotOp::RegisterName { .. } => "name.register",
            BotOp::AttestPresence => "presence.attest",
            BotOp::IssueCredential { .. } => "credential.issue",
        }
    }

    /// The complete catalog of drivable ops the desktop surface offers (sample
    /// instances for the card / Spotter; the live surface fills names/attrs from
    /// input).
    pub fn catalog() -> Vec<BotOp> {
        vec![
            BotOp::AttestPresence,
            BotOp::RegisterName {
                name: "deos".to_string(),
            },
            BotOp::IssueCredential {
                schema: "kyc".to_string(),
                attributes: serde_json::json!({ "over_18": true }),
            },
        ]
    }
}

/// The request body the desktop POSTs to the live bot's `POST /api/op` — the mirror of
/// `discord-bot`'s `deos_drive::DriveRequest` (acting user + op + guild context).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DriveRequest {
    /// The Discord user id whose custodial cipherclerk the bot signs with.
    pub user_id: u64,
    /// The originating guild, if any.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub guild_id: Option<String>,
    /// The op to drive.
    #[serde(flatten)]
    pub op: BotOp,
}

/// **RELEGATED legacy HTTP wire body — NOT the command path.** The desktop now
/// commands the bot ON-CHAIN ([`drive_command_on_world`] → the [`command_cell`]),
/// which the bot's `bot_reactor` watches. This body is retained only for the
/// bot's optional legacy `/api/op` nudge surface, not as how the desktop drives
/// the bot.
pub fn op_request(user_id: u64, guild_id: Option<&str>, op: &BotOp) -> serde_json::Value {
    serde_json::to_value(DriveRequest {
        user_id,
        guild_id: guild_id.map(str::to_string),
        op: op.clone(),
    })
    .expect("a BotOp drive request always serializes")
}

/// **Drive a bot op as a real dregg turn on the embedded verified World** — the
/// in-session, receipted half of the drive (no live bot needed). Maps the op to its
/// genuine [`Effect`](dregg_turn::action::Effect) on `bot_cell` and commits it,
/// returning whether the turn committed (a `TurnReceipt` on the cell's chain). The
/// SAME op, against a live bot, is the [`op_request`] POST.
pub fn drive_on_world(world: &mut World, bot_cell: CellId, op: &BotOp) -> bool {
    let effect = match op {
        BotOp::RegisterName { name } => {
            set_field(bot_cell, NAME_HASH_SLOT, fe_u64(name_hash(name)))
        }
        BotOp::AttestPresence => set_field(bot_cell, PRESENCE_SLOT, fe_u64(current_epoch())),
        BotOp::IssueCredential { .. } => {
            let next = read_field_u64(world, bot_cell, CRED_COUNT_SLOT) + 1;
            set_field(bot_cell, CRED_COUNT_SLOT, fe_u64(next))
        }
    };
    let turn = world.turn(bot_cell, vec![effect]);
    world.commit_turn(turn).is_committed()
}

// ─── The on-chain command path (the chain is the message bus) ─────────────────────
//
// The desktop commands the bot by submitting a real dregg turn to a well-known
// COMMAND CELL whose committed state carries the op. The bot's `bot_reactor`
// watches that cell and reacts. This mirrors `discord-bot`'s `deos_drive` command
// encoding byte-for-byte so the bot decodes the desktop's on-chain command.

/// The deterministic, well-known **bot-command cell** — the on-chain mailbox the
/// desktop submits command turns to (mirrors `discord-bot`'s
/// `deos_drive::command_cell`, `0xC0…`).
pub fn command_cell() -> CellId {
    CellId::from_bytes([0xC0u8; 32])
}

/// Command-cell slot: the monotonic command sequence (mirrors the bot).
pub const CMD_SEQ_SLOT: usize = 0;
/// Command-cell slot: the payload byte length (mirrors the bot).
pub const CMD_LEN_SLOT: usize = 1;
/// Command-cell base slot: the serialized [`DriveRequest`] payload, 31 bytes per
/// field element (mirrors the bot).
pub const CMD_PAYLOAD_BASE: usize = 2;

/// Bytes packed per field element (31; high byte zero — mirrors the bot).
const CMD_CHUNK: usize = 31;

/// Encode a u64 as a big-endian-trailing field element — the SAME convention as
/// `dregg_app_framework::field_from_u64`, so the bot's `field_to_u64` reads the
/// desktop's seq/len.
fn fe_u64_be(value: u64) -> dregg_cell::FieldElement {
    let mut fe = [0u8; 32];
    fe[24..32].copy_from_slice(&value.to_be_bytes());
    fe
}

/// **Build the on-chain command turn's effects** — the SetField sequence that
/// writes a serialized [`DriveRequest`] (`{user_id, guild_id?, op}`) into the
/// command cell's committed state, exactly as the bot's `deos_drive::decode_command`
/// reconstructs it. The op is delivered as cell STATE (faithfully readable off any
/// node), not an HTTP body.
pub fn command_effects(user_id: u64, guild_id: Option<&str>, op: &BotOp, seq: u64) -> Vec<Effect> {
    let req = DriveRequest {
        user_id,
        guild_id: guild_id.map(str::to_string),
        op: op.clone(),
    };
    let payload = serde_json::to_vec(&req).expect("a DriveRequest always serializes");
    let cell = command_cell();

    let mut effects = vec![
        set_field(cell, CMD_SEQ_SLOT, fe_u64_be(seq)),
        set_field(cell, CMD_LEN_SLOT, fe_u64_be(payload.len() as u64)),
    ];
    for (i, chunk) in payload.chunks(CMD_CHUNK).enumerate() {
        let mut fe = [0u8; 32];
        fe[..chunk.len()].copy_from_slice(chunk);
        effects.push(set_field(cell, CMD_PAYLOAD_BASE + i, fe));
    }
    effects
}

/// **Drive a bot op as a real dregg COMMAND turn on the embedded verified World** —
/// the on-chain command path (no HTTP, no live bot needed for the in-session
/// half). Submits a turn (signed by `signer_cell`) to the [`command_cell`] whose
/// committed state carries the op; the bot's reactor watches that cell and reacts.
/// Returns whether the command turn committed.
pub fn drive_command_on_world(
    world: &mut World,
    signer_cell: CellId,
    user_id: u64,
    guild_id: Option<&str>,
    op: &BotOp,
    seq: u64,
) -> bool {
    let effects = command_effects(user_id, guild_id, op, seq);
    let turn = world.turn(signer_cell, effects);
    world.commit_turn(turn).is_committed()
}

/// Read state slot `index` of `cell` as a u64 (the low 8 bytes) — the surface's
/// read-back of a driven op's effect (e.g. the attested presence epoch).
pub fn read_field_u64(world: &World, cell: CellId, index: usize) -> u64 {
    world
        .ledger()
        .get(&cell)
        .and_then(|c| c.state.fields.get(index).copied())
        .map(|f| u64::from_le_bytes(f[..8].try_into().unwrap_or([0u8; 8])))
        .unwrap_or(0)
}

// ─── The activity feed, mirrored + folded into a card ────────────────────────────

/// **The bot's activity feed entry** — the desktop's mirror of the bot's
/// `StarbridgeActivityView` (`GET /api/apps/activity/recent`), so the feed JSON
/// deserializes straight off the wire.
#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
pub struct BotActivity {
    /// The app the activity belongs to (`deos-desktop` for desktop-driven ops).
    pub app: String,
    /// The action label (`name.register`, `presence.attest`, …).
    pub action: String,
    /// The acting Discord user id.
    #[serde(default)]
    pub actor_discord_id: String,
    /// The originating guild, if any.
    #[serde(default)]
    pub guild_id: Option<String>,
    /// A short subject (the name / schema / "online").
    #[serde(default)]
    pub subject: Option<String>,
    /// The op's status (`committed` / `rejected`).
    #[serde(default)]
    pub status: String,
    /// The activity timestamp.
    #[serde(default)]
    pub timestamp: i64,
}

#[cfg(feature = "card-pane")]
mod card {
    use super::BotActivity;
    use deos_view::ViewNode;

    /// **Fold the bot's activity feed into the portable [`ViewNode`] card** — the SAME
    /// shape `discord-bot/src/cards.rs` renders as a Discord embed (`text` header over
    /// one `row[name, value]` per activity → an embed field / a native widget row). One
    /// card authored once; rendered on both faces.
    pub fn activity_card(activities: &[BotActivity]) -> ViewNode {
        let mut children = vec![ViewNode::Text("dregg discord-bot · activity".to_string())];
        if activities.is_empty() {
            children.push(ViewNode::Text("no activity yet".to_string()));
        }
        for a in activities.iter().take(12) {
            let subject = a.subject.clone().unwrap_or_default();
            let value = if subject.is_empty() {
                a.status.clone()
            } else {
                format!("{} · {}", a.status, subject)
            };
            children.push(ViewNode::Row(vec![
                ViewNode::Text(format!("{} · {}", a.app, a.action)),
                ViewNode::Text(value),
            ]));
        }
        ViewNode::VStack(children)
    }

    /// Count the activity rows in a rendered card (the bake's witness that the feed
    /// reached the card).
    pub fn card_row_count(tree: &ViewNode) -> usize {
        match tree {
            ViewNode::VStack(kids) => kids
                .iter()
                .filter(|k| matches!(k, ViewNode::Row(_)))
                .count(),
            _ => 0,
        }
    }

    /// **Build the discord-bot surface pane** — a [`deos_view::AppletView`] gpui entity
    /// over the activity [`activity_card`], backed by a minimal embedded applet (the
    /// card carries no `bind`s, so the backing is a placeholder). The desktop hosts the
    /// returned entity as a `ViewNodePane` window body, exactly as the World-Status
    /// pane is hosted — the bot's feed painted by the SAME native renderer.
    pub fn build_bot_surface_view(
        cx: &mut gpui::App,
        activities: &[BotActivity],
    ) -> gpui::Entity<deos_view::AppletView> {
        use gpui::AppContext as _;
        use std::cell::RefCell;
        use std::rc::Rc;
        let applet: deos_view::SharedApplet = Rc::new(RefCell::new(
            super::super::viewnode_pane::status_panel_applet(),
        ));
        let tree = activity_card(activities);
        cx.new(|_cx| deos_view::AppletView::new(applet, tree))
    }
}

#[cfg(feature = "card-pane")]
pub use card::{activity_card, build_bot_surface_view, card_row_count};

// ─── Pure helpers ────────────────────────────────────────────────────────────────

fn fe_u64(v: u64) -> dregg_cell::FieldElement {
    let mut fe = [0u8; 32];
    fe[..8].copy_from_slice(&v.to_le_bytes());
    fe
}

/// A deterministic 64-bit fold of a name into a field value (FNV-1a) — the
/// witnessed name binding the register turn writes. (The live bot writes the
/// nameservice `field_from_bytes(name)`; this is the embedded-World stand-in.)
fn name_hash(name: &str) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for b in name.as_bytes() {
        h ^= *b as u64;
        h = h.wrapping_mul(0x00000100000001B3);
    }
    h
}

fn current_epoch() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn op_request_matches_the_bots_drive_endpoint_shape() {
        // The desktop's op-request is the EXACT body the bot's `POST /api/op` accepts
        // (`discord-bot::deos_drive::DriveRequest`): `{user_id, guild_id?, op, …}`.
        let body = op_request(
            4242,
            Some("guild-1"),
            &BotOp::RegisterName {
                name: "ember".to_string(),
            },
        );
        assert_eq!(body["user_id"], 4242);
        assert_eq!(body["guild_id"], "guild-1");
        assert_eq!(body["op"], "register_name");
        assert_eq!(body["name"], "ember");

        // Presence has no extra fields; guild omitted when None.
        let p = op_request(7, None, &BotOp::AttestPresence);
        assert_eq!(p["op"], "attest_presence");
        assert!(
            p.get("guild_id").is_none(),
            "None guild is omitted from the body"
        );
    }

    #[test]
    fn bot_activity_deserializes_from_the_feed_json() {
        // The shape the bot's `GET /api/apps/activity/recent` returns.
        let json = serde_json::json!([
            {
                "id": 1,
                "app": "deos-desktop",
                "action": "name.register",
                "actor_discord_id": "4242",
                "guild_id": null,
                "subject": "ember",
                "status": "committed",
                "details": {},
                "timestamp": 100
            }
        ]);
        let feed: Vec<BotActivity> = serde_json::from_value(json).unwrap();
        assert_eq!(feed.len(), 1);
        assert_eq!(feed[0].action, "name.register");
        assert_eq!(feed[0].subject.as_deref(), Some("ember"));
        assert_eq!(feed[0].status, "committed");
    }

    #[test]
    fn desktop_submits_an_on_chain_command_turn_to_the_command_cell() {
        // THE ON-CHAIN COMMAND PATH (no HTTP): a desktop drive submits a real
        // dregg turn to the COMMAND CELL whose committed state carries the op —
        // the message the bot's reactor reads. The seq + length land in the
        // command cell's state, receipted.
        let (mut world, anchors) = crate::world::demo_world();
        let signer = anchors[0];
        let cmd = command_cell();

        let before_height = world.height();
        assert_eq!(read_field_u64(&world, cmd, CMD_SEQ_SLOT), 0);

        let committed = drive_command_on_world(
            &mut world,
            signer,
            4242,
            Some("guild-1"),
            &BotOp::RegisterName {
                name: "ember".to_string(),
            },
            1,
        );
        assert!(committed, "the on-chain command turn must commit");
        assert!(
            world.height() > before_height,
            "a receipt advanced the chain"
        );

        // The command cell's committed STATE carries the command: seq + a non-zero
        // payload length (the serialized DriveRequest the bot decodes).
        let seq = world
            .ledger()
            .get(&cmd)
            .and_then(|c| c.state.fields.get(CMD_SEQ_SLOT).copied())
            .map(|f| u64::from_be_bytes(f[24..32].try_into().unwrap()))
            .unwrap_or(0);
        assert_eq!(seq, 1, "the command seq is committed to the command cell");
        let len = world
            .ledger()
            .get(&cmd)
            .and_then(|c| c.state.fields.get(CMD_LEN_SLOT).copied())
            .map(|f| u64::from_be_bytes(f[24..32].try_into().unwrap()))
            .unwrap_or(0);
        assert!(len > 0, "the serialized op payload length is committed");

        // A second command advances the seq (the watcher's new-command signal).
        assert!(drive_command_on_world(
            &mut world,
            signer,
            4242,
            None,
            &BotOp::AttestPresence,
            2,
        ));
        let seq2 = world
            .ledger()
            .get(&cmd)
            .and_then(|c| c.state.fields.get(CMD_SEQ_SLOT).copied())
            .map(|f| u64::from_be_bytes(f[24..32].try_into().unwrap()))
            .unwrap_or(0);
        assert_eq!(seq2, 2, "the second command advanced the on-chain seq");
    }

    #[test]
    fn desktop_drives_a_bot_op_as_a_receipted_dregg_turn() {
        // THE BAKE: a desktop action → a real dregg turn on the embedded verified
        // World → the bot cell's state changes, receipted. Presence attestation writes
        // a non-zero epoch into PRESENCE_SLOT; the receipt count advances.
        let (mut world, anchors) = crate::world::demo_world();
        let bot_cell = anchors[0];

        let before_height = world.height();
        assert_eq!(read_field_u64(&world, bot_cell, PRESENCE_SLOT), 0);

        let committed = drive_on_world(&mut world, bot_cell, &BotOp::AttestPresence);
        assert!(
            committed,
            "the presence-attest turn must commit on the World"
        );
        assert!(
            read_field_u64(&world, bot_cell, PRESENCE_SLOT) > 0,
            "presence wrote a witnessed epoch into the bot cell's state"
        );
        assert!(
            world.height() > before_height,
            "a receipt advanced the chain"
        );

        // A name registration writes the name-hash; a credential issuance bumps a count.
        assert!(drive_on_world(
            &mut world,
            bot_cell,
            &BotOp::RegisterName {
                name: "ember".to_string()
            }
        ));
        assert_eq!(
            read_field_u64(&world, bot_cell, NAME_HASH_SLOT),
            name_hash("ember"),
            "the name binding is committed to the registry slot"
        );

        assert!(drive_on_world(
            &mut world,
            bot_cell,
            &BotOp::IssueCredential {
                schema: "kyc".to_string(),
                attributes: serde_json::json!({}),
            }
        ));
        assert_eq!(
            read_field_u64(&world, bot_cell, CRED_COUNT_SLOT),
            1,
            "the credential count advanced"
        );
    }

    #[cfg(feature = "card-pane")]
    #[test]
    fn activity_feed_renders_as_a_desktop_card() {
        // THE SECOND HALF: the bot's activity feed folds into a portable ViewNode card
        // (the SAME shape the bot renders as a Discord embed) — one row per activity.
        let feed = vec![
            BotActivity {
                app: "deos-desktop".to_string(),
                action: "presence.attest".to_string(),
                actor_discord_id: "4242".to_string(),
                guild_id: None,
                subject: Some("online".to_string()),
                status: "committed".to_string(),
                timestamp: 1,
            },
            BotActivity {
                app: "deos-desktop".to_string(),
                action: "name.register".to_string(),
                actor_discord_id: "4242".to_string(),
                guild_id: None,
                subject: Some("ember".to_string()),
                status: "committed".to_string(),
                timestamp: 2,
            },
        ];
        let tree = activity_card(&feed);
        assert_eq!(card_row_count(&tree), 2, "two activities → two card rows");
        // The header text leads the card.
        match &tree {
            deos_view::ViewNode::VStack(kids) => {
                assert!(matches!(&kids[0], deos_view::ViewNode::Text(t) if t.contains("activity")));
            }
            other => panic!("expected a vstack card, got {other:?}"),
        }
    }
}
