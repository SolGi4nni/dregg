//! **The deos-desktop ↔ discord-bot drive seam** — the desktop and Discord as two
//! faces of ONE dregg-driven bot.
//!
//! The discord-bot is a custodial dregg peer: it holds per-user cipherclerks and
//! turns user intent into REAL signed dregg turns on the node (`credential_issue`,
//! `starbridge_nameservice::build_register_action`, …), recording each as a
//! `StarbridgeActivity` and reflecting it to Discord. This module opens the SAME
//! ops to the **deos desktop**: a desktop surface POSTs a [`BotOp`] to the bot's
//! HTTP surface (`POST /api/op`), the bot builds + signs + submits the SAME real
//! dregg turn, records the SAME activity, and the bot can reflect it to Discord —
//! so a click on the desktop and a slash command in Discord are two faces of one
//! dregg-driven bot.
//!
//! ## What is real vs. the seam
//!
//! - **Real:** the op → a genuine signed `dregg_turn` ([`build_register_action`] /
//!   [`build_presence_action`] / the credential path), carrying real
//!   [`dregg_app_framework::Effect`]s; the activity record (the bot's own state);
//!   the [`activity_card`] / [`op_receipt_card`] as a portable `deos_view::ViewNode`
//!   that renders to a Discord embed via the SAME [`deos_view::discord::render_card`]
//!   the desktop renders natively.
//! - **The seam (named):** the turn's *commit* is the live node's
//!   ([`crate::devnet::DevnetClient::submit_app_action`]) — the SAME boundary every
//!   other bot op touches the executor at. A desktop drive with no live node still
//!   builds the genuine signed turn (the build is pure, [`build_op_action`]); the
//!   submit is the node's.

use serde::{Deserialize, Serialize};

use deos_view::tree::ViewNode;
use dregg_app_framework::{Action, CellId, Effect, field_from_u64, symbol};

use crate::BotState;
use crate::cipherclerk::UserCipherclerk;
use crate::db::StarbridgeActivity;
use crate::devnet::SubmitSignedTurnResult;

/// The app name every desktop-driven op is recorded under in the activity feed —
/// so the desktop face is legible in the SAME `StarbridgeActivity` stream the
/// Discord activity feed + dashboard read.
pub const DRIVE_APP: &str = "deos-desktop";

/// The state slot a presence attestation writes its epoch into (the on-ledger
/// "last seen" witness — presence as a witnessed, receipted state, not only a
/// local MAC). Chosen above the nameservice slots (2..=4) so the two ops never
/// collide on a self-registry cell.
pub const PRESENCE_SLOT: usize = 10;

/// A default name lease length (in node blocks) for a desktop-driven name
/// registration when the live height is unknown — long enough to be useful, finite
/// so the lease is real.
pub const DEFAULT_NAME_LEASE: u64 = 100_000;

/// **The ops the deos desktop (or any peer) can drive on the bot as dregg turns.**
/// The desktop POSTs one of these (tagged JSON) to `POST /api/op`; the bot builds +
/// signs + submits the corresponding real dregg turn. Each variant maps to an
/// existing bot op so the desktop and Discord drive the SAME thing.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(tag = "op", rename_all = "snake_case")]
pub enum BotOp {
    /// Register a name on the user's own cell as a self-registry (the nameservice
    /// `register_name` turn: `SetField(NAME_HASH/OWNER/EXPIRY)` + `EmitEvent`).
    RegisterName {
        /// The name to bind (hashed into the registry cell's `NAME_HASH_SLOT`).
        name: String,
    },
    /// Attest the user's presence ON-LEDGER — a receipted `SetField` writing the
    /// current epoch into [`PRESENCE_SLOT`] of the user's cell.
    AttestPresence,
    /// Issue a verifiable credential to the user's own cell (the canonical
    /// Starbridge identity issuance turn — see [`crate::credential_issue`]).
    IssueCredential {
        /// The credential schema name (`kyc` / `gov_id` / `employment`).
        schema: String,
        /// The credential attributes as a JSON object matching the schema.
        attributes: serde_json::Value,
    },
}

impl BotOp {
    /// The activity-feed action label this op records under (stable across the
    /// desktop + Discord faces).
    pub fn action_label(&self) -> &'static str {
        match self {
            BotOp::RegisterName { .. } => "name.register",
            BotOp::AttestPresence => "presence.attest",
            BotOp::IssueCredential { .. } => "credential.issue",
        }
    }

    /// The dregg method name the op's resulting turn targets — the method the
    /// bot's reaction action carries (matching [`build_op_action`]'s built
    /// `Action::method`). Stable, so the reactor's [`ReactionPlan`] re-hashes the
    /// SAME symbol.
    ///
    /// [`ReactionPlan`]: dregg_app_framework::ReactionPlan
    pub fn method_name(&self) -> &'static str {
        match self {
            BotOp::RegisterName { .. } => "register_name",
            BotOp::AttestPresence => "attest_presence",
            BotOp::IssueCredential { .. } => "issue_credential",
        }
    }

    /// A short, reader-legible subject for the activity record (the name / schema /
    /// "online").
    pub fn subject(&self) -> String {
        match self {
            BotOp::RegisterName { name } => name.clone(),
            BotOp::AttestPresence => "online".to_string(),
            BotOp::IssueCredential { schema, .. } => schema.clone(),
        }
    }
}

/// The request body the desktop POSTs to `POST /api/op`: the acting Discord user
/// (whose custodial cipherclerk signs) + the op + the optional guild context.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DriveRequest {
    /// The Discord user id whose custodial cipherclerk signs the turn.
    pub user_id: u64,
    /// The originating guild (recorded on the activity), if any.
    #[serde(default)]
    pub guild_id: Option<String>,
    /// The op to drive.
    #[serde(flatten)]
    pub op: BotOp,
}

/// The outcome of a desktop-driven op: whether the node accepted it, the turn hash
/// (the receipt handle), the recorded activity row, and the op's action label.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DriveOutcome {
    /// Whether the node accepted + committed the turn.
    pub accepted: bool,
    /// The committed turn's hash (the receipt handle), when accepted.
    pub turn_hash: Option<String>,
    /// The action label recorded in the activity feed.
    pub action: String,
    /// The row id of the recorded `StarbridgeActivity` (the bot's state change).
    pub activity_id: i64,
}

// ─── The pure turn builders (node-free, the testable core) ───────────────────────

/// Build the REAL signed-action core for an op WITHOUT touching the node — the pure,
/// deterministic half of [`drive`] (the submit is the node's). Returns the genuine
/// `dregg_turn::Action` the bot would sign + submit. Credential issuance is NOT here
/// (its build is interleaved with the issuer-key derivation in
/// [`crate::credential_issue`]); this covers the two ops with a pure builder.
pub fn build_op_action(cclerk: &UserCipherclerk, op: &BotOp, expiry_height: u64) -> Option<Action> {
    match op {
        BotOp::RegisterName { name } => Some(build_register_action(cclerk, name, expiry_height)),
        BotOp::AttestPresence => Some(build_presence_action(cclerk, current_epoch())),
        BotOp::IssueCredential { .. } => None,
    }
}

/// Build the real `register_name` action on the user's own cell as a self-registry —
/// the nameservice primitive ([`starbridge_nameservice::build_register_action`]): a
/// `SetField(NAME_HASH/OWNER/EXPIRY)` + `EmitEvent("name-registered")`. No new Effect
/// variant; the SAME turn the `/name-register` Discord command builds.
pub fn build_register_action(cclerk: &UserCipherclerk, name: &str, expiry_height: u64) -> Action {
    let registry_cell = CellId(cclerk.cell_id_bytes());
    let owner = cclerk.app.public_key().0;
    starbridge_nameservice::build_register_action(
        &cclerk.app,
        registry_cell,
        name,
        owner,
        expiry_height,
    )
}

/// Build the real presence-attestation action — a `SetField(PRESENCE_SLOT, epoch)`
/// on the user's own cell (presence as a witnessed, receipted on-ledger state).
pub fn build_presence_action(cclerk: &UserCipherclerk, epoch: u64) -> Action {
    let cell = CellId(cclerk.cell_id_bytes());
    cclerk.app.make_action(
        cell,
        "attest_presence",
        vec![Effect::SetField {
            cell,
            index: PRESENCE_SLOT,
            value: field_from_u64(epoch),
        }],
    )
}

// ─── The on-chain command cell (the message bus) ─────────────────────────────────
//
// The desktop drives a bot op NOT by an HTTP POST but by submitting a real dregg
// turn to a well-known **command cell** — the chain is the message bus. The op
// (the full [`DriveRequest`]) is carried as the committed STATE of that cell
// (SetField slots, faithfully readable off any node's `/api/cell` fields) plus an
// `EmitEvent` announcement the bot's reactor keys on. The bot WATCHES this cell
// (via [`app_framework::Reactor`]) and reacts — no HTTP command path.

/// The deterministic, well-known **bot-command cell**: the on-chain mailbox the
/// desktop submits command turns to and the bot's reactor watches. A distinct,
/// out-of-band address (`0xC0…`, "COmmand") so it never collides with a user's
/// self-registry cell.
pub fn command_cell() -> CellId {
    CellId([0xC0u8; 32])
}

/// The method every on-chain command turn targets — what the bot's
/// [`crate::bot_reactor::BotCommandReactor`] filter watches for.
pub const COMMAND_METHOD: &str = "bot_command";

/// The event topic the command turn emits (the on-chain announcement the reactor
/// keys on, indexed for off-chain consumption).
pub const COMMAND_TOPIC: &str = "bot-command";

/// Command-cell state slot: the monotonic command sequence. The watcher detects a
/// NEW command when this advances, and dedupes already-handled commands.
pub const CMD_SEQ_SLOT: usize = 0;
/// Command-cell state slot: the payload byte length.
pub const CMD_LEN_SLOT: usize = 1;
/// Command-cell state base slot: the serialized [`DriveRequest`] payload, packed
/// 31 bytes per field element from here upward.
pub const CMD_PAYLOAD_BASE: usize = 2;

/// Bytes packed per field element (31, leaving the high byte zero so the value is
/// safely below any ~255-bit field modulus — no canonicalization surprises).
const CHUNK: usize = 31;

/// Pack arbitrary bytes into field elements, 31 bytes each (high byte zero).
fn pack_bytes(bytes: &[u8]) -> Vec<[u8; 32]> {
    bytes
        .chunks(CHUNK)
        .map(|c| {
            let mut fe = [0u8; 32];
            fe[..c.len()].copy_from_slice(c);
            fe
        })
        .collect()
}

/// Reconstruct `len` bytes from packed field elements (the inverse of
/// [`pack_bytes`]).
fn unpack_bytes(chunks: &[[u8; 32]], len: usize) -> Vec<u8> {
    let mut out = Vec::with_capacity(len);
    for fe in chunks {
        out.extend_from_slice(&fe[..CHUNK]);
    }
    out.truncate(len);
    out
}

/// **Build the on-chain command turn the desktop submits to the [`command_cell`].**
/// The full [`DriveRequest`] is serialized and written as the command cell's
/// committed state (a `SetField` per payload chunk + the seq + the length), and an
/// [`Effect::EmitEvent`] announces it under [`COMMAND_TOPIC`]. The returned
/// [`Action`] is UNSIGNED — the desktop (the acting peer) signs + submits it; the
/// bot never sees an HTTP body, only this committed turn. `seq` is the desktop's
/// monotonic command counter (so re-submits are distinguishable + dedupable).
pub fn build_command_action(req: &DriveRequest, seq: u64) -> Action {
    let payload = serde_json::to_vec(req).expect("a DriveRequest always serializes");
    let cell = command_cell();
    let chunks = pack_bytes(&payload);

    let mut effects = vec![
        Effect::SetField {
            cell,
            index: CMD_SEQ_SLOT,
            value: field_from_u64(seq),
        },
        Effect::SetField {
            cell,
            index: CMD_LEN_SLOT,
            value: field_from_u64(payload.len() as u64),
        },
    ];
    for (i, chunk) in chunks.iter().enumerate() {
        effects.push(Effect::SetField {
            cell,
            index: CMD_PAYLOAD_BASE + i,
            value: *chunk,
        });
    }
    // The on-chain announcement: topic the reactor keys on, data = [seq, len, payload..].
    let mut event_data = vec![field_from_u64(seq), field_from_u64(payload.len() as u64)];
    event_data.extend(chunks);
    effects.push(Effect::EmitEvent {
        cell,
        event: dregg_app_framework::Event::new(symbol(COMMAND_TOPIC), event_data),
    });

    Action {
        target: cell,
        method: symbol(COMMAND_METHOD),
        args: vec![field_from_u64(seq)],
        authorization: dregg_turn::action::Authorization::Unchecked,
        preconditions: Default::default(),
        effects,
        may_delegate: dregg_turn::action::DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: Vec::new(),
    }
}

/// **Decode the [`DriveRequest`] + seq from a command turn's committed effects** —
/// the inverse of [`build_command_action`]. The bot's reactor reads the command
/// cell's `SetField`s (its committed state — what `/api/cell` exposes) and
/// reconstructs the exact op the desktop submitted. `None` if the effects do not
/// carry a well-formed command (fail-closed).
pub fn decode_command(effects: &[Effect]) -> Option<(DriveRequest, u64)> {
    let cell = command_cell();
    let mut seq: Option<u64> = None;
    let mut len: Option<usize> = None;
    let mut chunks: Vec<(usize, [u8; 32])> = Vec::new();

    for effect in effects {
        if let Effect::SetField {
            cell: c,
            index,
            value,
        } = effect
        {
            if *c != cell {
                continue;
            }
            match *index {
                CMD_SEQ_SLOT => seq = Some(field_to_u64(value)),
                CMD_LEN_SLOT => len = Some(field_to_u64(value) as usize),
                i if i >= CMD_PAYLOAD_BASE => chunks.push((i - CMD_PAYLOAD_BASE, *value)),
                _ => {}
            }
        }
    }

    let seq = seq?;
    let len = len?;
    chunks.sort_by_key(|(i, _)| *i);
    let ordered: Vec<[u8; 32]> = chunks.into_iter().map(|(_, fe)| fe).collect();
    let bytes = unpack_bytes(&ordered, len);
    let req: DriveRequest = serde_json::from_slice(&bytes).ok()?;
    Some((req, seq))
}

/// Read the trailing-8-bytes big-endian u64 from a `field_from_u64`-encoded field.
fn field_to_u64(fe: &[u8; 32]) -> u64 {
    u64::from_be_bytes(fe[24..32].try_into().unwrap_or([0u8; 8]))
}

// ─── The driver (build → sign → submit → record) ─────────────────────────────────

/// **Drive a bot op as a real dregg turn from the desktop.** Builds + signs the
/// genuine turn under the user's custodial cipherclerk, submits it to the node
/// ([`crate::devnet::DevnetClient::submit_app_action`]), records the outcome as a
/// `StarbridgeActivity` (the bot's own state change, visible in the SAME feed the
/// Discord face reads), and returns the [`DriveOutcome`]. The submit is the live
/// node's boundary; everything else is the bot's, in-process.
pub async fn drive(state: &BotState, req: &DriveRequest) -> Result<DriveOutcome, String> {
    let cclerk = UserCipherclerk::derive(
        &state.config.bot_secret,
        req.user_id,
        state.federation_id_bytes,
    );

    let (turn, subject): (SubmitSignedTurnResult, String) = match &req.op {
        BotOp::IssueCredential { schema, attributes } => {
            // The canonical identity issuance path already builds + signs + submits
            // the real credential turn; reuse it verbatim (one issuance code path).
            let result = crate::credential_issue::issue_from_discord_input(
                state,
                req.user_id,
                cclerk.cell_id_hex(),
                schema,
                &attributes.to_string(),
            )
            .await?;
            (result.turn, schema.clone())
        }
        op => {
            let expiry = state
                .devnet
                .current_height()
                .await
                .map(|h| h + DEFAULT_NAME_LEASE)
                .unwrap_or(DEFAULT_NAME_LEASE);
            let action = build_op_action(&cclerk, op, expiry)
                .ok_or_else(|| "op has no pure builder".to_string())?;
            let result = state
                .devnet
                .submit_app_action(
                    &cclerk,
                    action,
                    Some(format!("deos-desktop:{}", op.action_label())),
                )
                .await
                .map_err(|e| e.to_string())?;
            (result, op.subject())
        }
    };

    let action_label = req.op.action_label();
    let status = if turn.accepted {
        "committed"
    } else {
        "rejected"
    };
    let details = serde_json::json!({
        "turn_hash": turn.turn_hash,
        "signer": cclerk.cell_id_hex(),
        "face": "deos-desktop",
        "error": turn.error,
    });
    let activity_id = state
        .db
        .record_starbridge_activity(
            DRIVE_APP,
            action_label,
            &req.user_id.to_string(),
            req.guild_id.as_deref(),
            Some(&subject),
            status,
            details,
        )
        .await
        .map_err(|e| format!("failed to record desktop-drive activity: {e}"))?;

    Ok(DriveOutcome {
        accepted: turn.accepted,
        turn_hash: turn.turn_hash,
        action: action_label.to_string(),
        activity_id,
    })
}

// ─── The portable activity card (the shared `ViewNode` shape) ─────────────────────

/// **Fold the bot's activity feed into a portable [`ViewNode`] card** — the SAME
/// card shape the deos desktop renders natively (`deos_view::AppletView`) and this
/// crate renders as a Discord embed ([`deos_view::discord::render_card`]). One card
/// authored once; rendered on both faces. A titled header over one `Row` per
/// activity (`app · action` → `status · subject`), so the Discord renderer maps each
/// row to an embed field and the native renderer to a row of widgets.
pub fn activity_card(activities: &[StarbridgeActivity]) -> ViewNode {
    let mut rows = vec![ViewNode::Text("dregg discord-bot · activity".to_string())];
    if activities.is_empty() {
        rows.push(ViewNode::Text("no activity yet".to_string()));
    }
    for a in activities.iter().take(12) {
        let subject = a.subject.clone().unwrap_or_default();
        rows.push(ViewNode::Row(vec![
            ViewNode::Text(format!("{} · {}", a.app, a.action)),
            ViewNode::Text(if subject.is_empty() {
                a.status.clone()
            } else {
                format!("{} · {}", a.status, subject)
            }),
        ]));
    }
    ViewNode::VStack(rows)
}

/// **The receipt card for one desktop-driven op** — a small portable [`ViewNode`] the
/// bot reflects to Discord after a desktop drive (the "the bot can reflect it to
/// Discord" half), rendered through the SAME renderer the desktop uses. A titled
/// header + a row naming the op, its status, and the turn hash.
pub fn op_receipt_card(op: &BotOp, outcome: &DriveOutcome) -> ViewNode {
    let status = if outcome.accepted {
        "committed"
    } else {
        "rejected"
    };
    let turn = outcome
        .turn_hash
        .as_deref()
        .map(|h| h.chars().take(16).collect::<String>())
        .unwrap_or_else(|| "—".to_string());
    ViewNode::VStack(vec![
        ViewNode::Text(format!("deos-desktop drove · {}", op.action_label())),
        ViewNode::Row(vec![
            ViewNode::Text(op.subject()),
            ViewNode::Text(format!("{status} · {turn}")),
        ]),
    ])
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
    use crate::db::Database;

    fn test_cclerk() -> UserCipherclerk {
        UserCipherclerk::derive(&[7u8; 32], 4242, [0u8; 32])
    }

    #[test]
    fn register_op_builds_a_real_register_name_turn() {
        // A desktop `register_name` op → a GENUINE dregg action: method
        // `register_name`, carrying the nameservice SetField + EmitEvent effects.
        let cclerk = test_cclerk();
        let op = BotOp::RegisterName {
            name: "ember".to_string(),
        };
        let action = build_op_action(&cclerk, &op, 50_000).expect("register has a pure builder");
        assert_eq!(action.method, symbol("register_name"));
        // The registry is the user's OWN cell (self-registry).
        assert_eq!(action.target, CellId(cclerk.cell_id_bytes()));
        let set_fields = action
            .effects
            .iter()
            .filter(|e| matches!(e, Effect::SetField { .. }))
            .count();
        assert!(
            set_fields >= 3,
            "register_name writes NAME/OWNER/EXPIRY (>=3 SetField), got {set_fields}"
        );
        assert!(
            action
                .effects
                .iter()
                .any(|e| matches!(e, Effect::EmitEvent { .. })),
            "register_name emits the name-registered event"
        );
    }

    #[test]
    fn presence_op_builds_a_real_setfield_turn() {
        // A desktop presence attestation → a real `SetField(PRESENCE_SLOT, epoch)`
        // on the user's own cell (presence as witnessed on-ledger state).
        let cclerk = test_cclerk();
        let action = build_op_action(&cclerk, &BotOp::AttestPresence, 0).expect("presence builds");
        assert_eq!(action.method, symbol("attest_presence"));
        match action.effects.as_slice() {
            [Effect::SetField { cell, index, .. }] => {
                assert_eq!(*cell, CellId(cclerk.cell_id_bytes()));
                assert_eq!(*index, PRESENCE_SLOT);
            }
            other => panic!("presence must be one SetField, got {other:?}"),
        }
    }

    #[test]
    fn command_action_round_trips_the_drive_request_on_chain() {
        // THE ON-CHAIN BUS: a DriveRequest → a real command turn to the command
        // cell (the desktop's submission) → decode it back from the committed
        // effects (what the bot's reactor reads off the cell's state). No HTTP.
        for op in [
            BotOp::AttestPresence,
            BotOp::RegisterName {
                name: "ember-the-goose".to_string(),
            },
            BotOp::IssueCredential {
                schema: "kyc".to_string(),
                attributes: serde_json::json!({ "over_18": true, "region": "earth" }),
            },
        ] {
            let req = DriveRequest {
                user_id: 4242,
                guild_id: Some("guild-7".to_string()),
                op: op.clone(),
            };
            let action = build_command_action(&req, 9);
            // The command turn targets the command cell with the command method.
            assert_eq!(action.target, command_cell());
            assert_eq!(action.method, symbol(COMMAND_METHOD));
            // It announces the op on-chain (the topic the reactor keys on).
            assert!(
                action.effects.iter().any(|e| matches!(
                    e,
                    Effect::EmitEvent { event, .. } if event.topic == symbol(COMMAND_TOPIC)
                )),
                "the command turn emits the bot-command announcement"
            );
            // The bot's reactor reads it back EXACTLY off the committed effects.
            let (decoded, seq) =
                decode_command(&action.effects).expect("a well-formed command turn must decode");
            assert_eq!(seq, 9);
            assert_eq!(decoded.user_id, 4242);
            assert_eq!(decoded.guild_id.as_deref(), Some("guild-7"));
            assert_eq!(decoded.op, op, "the op round-trips on-chain, faithfully");
        }
    }

    #[test]
    fn malformed_command_effects_decode_to_none() {
        // Fail-closed: an unrelated turn's effects carry no command → None.
        let junk = vec![Effect::SetField {
            cell: CellId([0x11u8; 32]),
            index: 5,
            value: [0u8; 32],
        }];
        assert!(decode_command(&junk).is_none());
    }

    #[test]
    fn drive_request_round_trips_through_json() {
        // The exact wire shape the desktop POSTs to `/api/op`.
        let req = DriveRequest {
            user_id: 99,
            guild_id: Some("123".to_string()),
            op: BotOp::RegisterName {
                name: "deos".to_string(),
            },
        };
        let json = serde_json::to_value(&req).unwrap();
        assert_eq!(json["op"], "register_name");
        assert_eq!(json["name"], "deos");
        assert_eq!(json["user_id"], 99);
        let back: DriveRequest = serde_json::from_value(json).unwrap();
        assert_eq!(back.op, req.op);
    }

    #[tokio::test]
    async fn drive_records_the_op_in_the_bots_activity_feed() {
        // The bot's STATE CHANGE half of a desktop drive: the recorded
        // `StarbridgeActivity` is readable back from the SAME feed the Discord face
        // reads — the desktop's action is legible in the bot's state. (The node
        // submit is the live boundary; this exercises the record leg directly.)
        let db = Database::connect("sqlite::memory:").await.unwrap();
        let op = BotOp::RegisterName {
            name: "ember".to_string(),
        };
        let id = db
            .record_starbridge_activity(
                DRIVE_APP,
                op.action_label(),
                "4242",
                Some("guild-1"),
                Some(&op.subject()),
                "committed",
                serde_json::json!({ "face": "deos-desktop", "turn_hash": "deadbeef" }),
            )
            .await
            .unwrap();
        assert!(id > 0, "the activity row was written");

        let recent = db.get_recent_starbridge_activity(10).await.unwrap();
        let row = recent
            .iter()
            .find(|a| a.id == id)
            .expect("the desktop-driven op appears in the feed");
        assert_eq!(row.app, DRIVE_APP);
        assert_eq!(row.action, "name.register");
        assert_eq!(row.subject.as_deref(), Some("ember"));
    }

    fn sample_activity(id: i64, action: &str, subject: &str) -> StarbridgeActivity {
        StarbridgeActivity {
            id,
            app: DRIVE_APP.to_string(),
            action: action.to_string(),
            actor_discord_id: "4242".to_string(),
            guild_id: None,
            subject: Some(subject.to_string()),
            status: "committed".to_string(),
            details_json: "{}".to_string(),
            timestamp: id,
        }
    }

    #[test]
    fn activity_card_renders_to_a_discord_embed() {
        // The portable card → a Discord embed via the SAME renderer the desktop
        // renders natively (the two-faces card). Each activity Row becomes a field.
        let activities = vec![
            sample_activity(1, "name.register", "ember"),
            sample_activity(2, "presence.attest", "online"),
        ];
        let tree = activity_card(&activities);
        let card = deos_view::discord::render_card("dregg discord-bot", &tree, &[]);
        let embed = serde_json::to_value(&card.embed).expect("embed serializes");
        assert!(
            embed["description"]
                .as_str()
                .unwrap()
                .contains("dregg discord-bot · activity"),
            "the header text became the description"
        );
        let fields = embed["fields"].as_array().expect("rows became fields");
        assert_eq!(fields.len(), 2, "two activity rows → two embed fields");
        assert_eq!(fields[0]["name"], "deos-desktop · name.register");
    }

    #[test]
    fn op_receipt_card_reflects_the_driven_op_to_discord() {
        // The bot reflects a desktop-driven op back to Discord through the SAME
        // renderer — the receipt card names the op, its status, and the turn hash.
        let op = BotOp::RegisterName {
            name: "ember".to_string(),
        };
        let outcome = DriveOutcome {
            accepted: true,
            turn_hash: Some("abc123def4567890".to_string()),
            action: "name.register".to_string(),
            activity_id: 1,
        };
        let card = deos_view::discord::render_card("driven", &op_receipt_card(&op, &outcome), &[]);
        let embed = serde_json::to_value(&card.embed).unwrap();
        assert!(
            embed["description"]
                .as_str()
                .unwrap()
                .contains("deos-desktop drove · name.register")
        );
        let fields = embed["fields"].as_array().unwrap();
        assert_eq!(fields[0]["name"], "ember");
        assert!(fields[0]["value"].as_str().unwrap().contains("committed"));
    }
}
