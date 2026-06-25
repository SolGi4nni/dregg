//! mud_client.rs — A PLAYABLE TEXT-MUD CLIENT over the node-hosted deos-js world.
//!
//! This is the CLIENT half of the deos-host MUD made interactive: you actually PLAY the
//! living world the GM (`mud_play_gm.js`) stood up on the node's ledger, driving it with
//! REAL verified turns over the node's HTTP wire.
//!
//! THE ARCHITECTURE (what this binary proves you can do):
//!   * a headless dregg node HOSTS the GM (a pure deos-js program) — it spawns the rooms,
//!     the character, the NPC, grants the player a cap over its character, forks dungeon
//!     instances, and publishes the cap-gated gameplay affordances (`move`, `gain-xp`,
//!     `descend`) for discovery;
//!   * a CLIENT (this code) connects over real HTTP, DISCOVERS those affordances
//!     ([`dregg_sdk_net::discover_server_affordances`]), and FIRES them as signed turns
//!     ([`dregg_sdk_net::fire_affordance`]) — each `move`/`gain-xp`/`descend` is a genuine
//!     verified turn committed on the node's live ledger;
//!   * `look` reads the room/character/NPC cells back off the ledger (`GET /api/cell/{id}`),
//!     so the world you see is the REAL committed state, advancing turn by turn;
//!   * a `tick` re-hosts the GM's reactive program (`mud_play_tick.js`): the GM observes the
//!     ledger and the WORLD RESPONDS — a level-up, the NPC going alert. A player cannot
//!     reach these GM superpowers;
//!   * THE ASYMMETRY is playable too: `descend` into the player's PERSONAL dungeon succeeds
//!     (the GM admitted them), but `descend` into the SEALED dungeon — or any forbidden
//!     cross-cell write — is REFUSED by the executor's authority gate (a receipted refusal).
//!
//! The engine ([`MudClient`]) is pure HTTP — it talks to any node URL. [`boot_mud_world`]
//! stands up an in-process node + hosts the GM + binds a real TCP listener so a single
//! `dregg-node mud-client` invocation gives you a complete, self-contained playable world.
#![cfg(feature = "deos-host")]

use std::io::{BufRead, Write};
use std::net::SocketAddr;

use dregg_cell::{AuthRequired, Cell, CellId, Permissions};
use dregg_sdk::AgentCipherclerk;
use dregg_turn::action::Effect;

use crate::state::NodeState;

/// Field-slot layout the GM stamps (matches `mud_play_gm.js` / `mud_play_tick.js`).
const CHAR_LEVEL: usize = 0;
const CHAR_XP: usize = 1;
const CHAR_ROOM: usize = 2;
const CHAR_SAY_COUNT: usize = 3;
const NPC_MOOD: usize = 0;
const DUNGEON_DESCENDED: usize = 0;
/// Item-cell field layout (the torch / the locked chest).
const ITEM_HELD: usize = 0;
const ITEM_ROOM: usize = 1;

/// The XP a `gain-xp` kill awards (crosses the level-up threshold of 100 the GM watches).
const GAIN_XP_VALUE: u64 = 120;
/// Room ids of the explorable map.
const ENTRANCE_ROOM: u64 = 1;
const HALL_ROOM: u64 = 2;
const TOWER_ROOM: u64 = 3;
const CELLAR_ROOM: u64 = 4;

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn default_token_id() -> [u8; 32] {
    *blake3::hash(b"default").as_bytes()
}

fn hex_of(id: &CellId) -> String {
    dregg_types::hex_encode(id.as_bytes())
}

/// Pack a u64 into a `FieldElement` (LE low 8 bytes) — matches deos-js `pack_u64`.
fn pack_u64(v: u64) -> dregg_cell::state::FieldElement {
    let mut fe = [0u8; 32];
    fe[..8].copy_from_slice(&v.to_le_bytes());
    fe
}

/// Decode a hex string into bytes (`None` on malformed input). The `GET /api/cell` `fields`
/// are 64-char hex `FieldElement`s; the node has no public hex-decode helper, so a tiny one.
fn decode_hex(s: &str) -> Option<Vec<u8>> {
    let s = s.trim();
    if !s.len().is_multiple_of(2) {
        return None;
    }
    let mut out = Vec::with_capacity(s.len() / 2);
    let bytes = s.as_bytes();
    for pair in bytes.chunks_exact(2) {
        let hi = (pair[0] as char).to_digit(16)?;
        let lo = (pair[1] as char).to_digit(16)?;
        out.push((hi * 16 + lo) as u8);
    }
    Some(out)
}

/// Read a u64 back out of a hex-encoded `FieldElement` (the `GET /api/cell` `fields` shape:
/// 64-char hex; the value is the LE low 8 bytes, matching deos-js `pack_u64`).
fn unpack_u64_hex(field_hex: &str) -> u64 {
    let bytes = match decode_hex(field_hex) {
        Some(b) if b.len() >= 8 => b,
        _ => return 0,
    };
    let mut b = [0u8; 8];
    b.copy_from_slice(&bytes[..8]);
    u64::from_le_bytes(b)
}

/// Derive the player's agent cell id the way the node's signed-turn ingress does.
fn agent_cell_for(pubkey: &[u8; 32]) -> CellId {
    CellId(dregg_cell::CellId::derive_raw(pubkey, &default_token_id()).0)
}

/// Derive a cell id the way `deos.server.spawnCell(seed, ...)` / `fork(seed)` do: the seed
/// is hashed to a pubkey, then derived against the default token domain.
fn spawned_cell_for(seed: &str) -> CellId {
    let pubkey = *blake3::hash(seed.as_bytes()).as_bytes();
    CellId(dregg_cell::CellId::derive_raw(&pubkey, &default_token_id()).0)
}

/// The cells of the playable MUD world (re-derived from `mud_play_gm.js`'s deterministic
/// seeds), so the client can read their state back over HTTP.
#[derive(Clone, Debug)]
pub struct MudWorld {
    pub character: CellId,
    pub watchman: CellId,
    pub entrance: CellId,
    pub hall: CellId,
    pub tower: CellId,
    pub cellar: CellId,
    /// The torch — an item the player holds a cap on (takeable).
    pub torch: CellId,
    /// The locked chest — an item the player has NO cap on (a `take` is refused).
    pub chest: CellId,
    /// The dungeon the player was ADMITTED into (a `descend` here succeeds).
    pub dungeon: CellId,
    /// The dungeon the player was NOT admitted into (a `descend` here is refused).
    pub sealed_dungeon: CellId,
}

impl MudWorld {
    fn derive() -> Self {
        MudWorld {
            character: spawned_cell_for("mud-play-char-aria"),
            watchman: spawned_cell_for("mud-play-npc-watchman"),
            entrance: spawned_cell_for("mud-play-room-entrance"),
            hall: spawned_cell_for("mud-play-room-hall"),
            tower: spawned_cell_for("mud-play-room-tower"),
            cellar: spawned_cell_for("mud-play-room-cellar"),
            torch: spawned_cell_for("mud-play-item-torch"),
            chest: spawned_cell_for("mud-play-item-chest"),
            dungeon: spawned_cell_for("mud-play-dungeon-aria"),
            sealed_dungeon: spawned_cell_for("mud-play-dungeon-sealed"),
        }
    }

    /// A friendly room name from a ROOM field value.
    fn room_name(room: u64) -> &'static str {
        match room {
            1 => "the Entrance",
            2 => "the Hall",
            3 => "the Tower",
            4 => "the Cellar",
            _ => "an unknown place",
        }
    }

    /// Resolve a movement direction from a given room into a target room id, per the exit
    /// graph (the fiction the GM laid out). `None` ⇒ there is no exit that way.
    fn exit(room: u64, dir: &str) -> Option<u64> {
        let dir = dir.trim().to_lowercase();
        match (room, dir.as_str()) {
            (ENTRANCE_ROOM, "north" | "n") => Some(HALL_ROOM),
            (HALL_ROOM, "south" | "s") => Some(ENTRANCE_ROOM),
            (HALL_ROOM, "up" | "u") => Some(TOWER_ROOM),
            (HALL_ROOM, "down" | "d") => Some(CELLAR_ROOM),
            (TOWER_ROOM, "down" | "d") => Some(HALL_ROOM),
            (CELLAR_ROOM, "up" | "u") => Some(HALL_ROOM),
            _ => None,
        }
    }

    /// The exits leaving a room, as `(direction, destination-name)` — for `look`.
    fn exits(room: u64) -> &'static [(&'static str, &'static str)] {
        match room {
            ENTRANCE_ROOM => &[("north", "the Hall")],
            HALL_ROOM => &[
                ("south", "the Entrance"),
                ("up", "the Tower"),
                ("down", "the Cellar"),
            ],
            TOWER_ROOM => &[("down", "the Hall")],
            CELLAR_ROOM => &[("up", "the Hall")],
            _ => &[],
        }
    }
}

/// A booted, self-contained playable MUD: an in-process node (its `NodeState` + the served
/// HTTP listener) with the GM hosted, plus the player identity to play AS. Dropping it tears
/// the world down. The handles (`_state`, `_tmp`, `_server`) keep the node alive.
pub struct MudSession {
    /// The node URL the client talks to (a real `http://127.0.0.1:PORT`).
    pub node_url: String,
    /// The player's signer (the client identity).
    pub player_cclerk: AgentCipherclerk,
    /// The player's agent cell on the ledger.
    pub player_cell: CellId,
    /// The GM (root server) cell — the discovery key for `move` / `gain-xp`.
    pub server_cell_hex: String,
    /// The executor federation id discovery hands back (the fire-signing binding).
    pub federation_id_hex: String,
    /// The world cells (re-derived from the GM program's seeds).
    pub world: MudWorld,
    // Kept alive for the session lifetime — the in-process node + its served port.
    _state: NodeState,
    _tmp: tempfile::TempDir,
    _server: tokio::task::JoinHandle<()>,
}

impl MudSession {
    /// The in-process node's state (for the GM `tick` superpower, which re-hosts the GM's
    /// reactive program against this live ledger — a server-side power, not a client fire).
    pub fn node_state(&self) -> &NodeState {
        &self._state
    }
}

/// BOOT a complete, self-contained playable MUD world: an in-process headless node, the GM
/// (`mud_play_gm.js`) hosted on it (spawning the world + publishing the affordances), a
/// funded+open player cell, and a real TCP HTTP listener the client drives over the wire.
///
/// `player_seed` derives the player identity (so re-runs play the SAME character). Returns a
/// [`MudSession`] whose handles keep the node alive until dropped.
pub async fn boot_mud_world(player_seed: &str) -> Result<MudSession, String> {
    let _ = rustls::crypto::ring::default_provider().install_default();

    // ── (1) a headless NodeState (NO gpui — node + deos-js only) ────────────────────
    let tmp = tempfile::tempdir().map_err(|e| format!("tempdir: {e}"))?;
    let state = NodeState::new(tmp.path(), vec![]).map_err(|e| format!("NodeState: {e}"))?;
    {
        let mut s = state.write().await;
        s.unlocked = true; // the signed-turn ingress requires an unlocked node
    }

    // THE PLAYER — its own cipherclerk + a funded, open cell (the client identity).
    let player_cclerk = AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(
        *blake3::hash(player_seed.as_bytes()).as_bytes(),
    ));
    let player_pubkey = player_cclerk.public_key().0;
    let player_cell = agent_cell_for(&player_pubkey);
    {
        let mut s = state.write().await;
        let mut player = Cell::with_balance(player_pubkey, default_token_id(), 1_000_000);
        player.permissions = open_permissions();
        if player.id() != player_cell {
            return Err("player cell id derivation mismatch".to_string());
        }
        if s.ledger.get(&player_cell).is_none() {
            s.ledger
                .insert_cell(player)
                .map_err(|e| format!("insert player cell: {e}"))?;
        }
    }

    // ── (2) HOST mud_play_gm.js — the GM spawns the world + registers the affordances ─
    let gm_program = include_str!("../tests/fixtures/mud_play_gm.js")
        .replace("__PLAYER__", &hex_of(&player_cell));
    let gm_cell = crate::deos_host::host_server_program(
        &state,
        "mud-play-gamemaster",
        AuthRequired::None,
        gm_program,
    )
    .await
    .map_err(|e| format!("host mud_play_gm.js: {e}"))?;

    // ── (3) bind a REAL HTTP listener so the client drives the genuine wire ──────────
    let metrics_handle = crate::metrics::install_recorder();
    let router = crate::api::router_with_cors(
        state.clone(),
        false,
        metrics_handle,
        std::collections::HashSet::new(),
    );
    let listener = tokio::net::TcpListener::bind("127.0.0.1:0")
        .await
        .map_err(|e| format!("bind listener: {e}"))?;
    let addr = listener
        .local_addr()
        .map_err(|e| format!("local addr: {e}"))?;
    let server = tokio::spawn(async move {
        let _ = axum::serve(
            listener,
            router.into_make_service_with_connect_info::<SocketAddr>(),
        )
        .await;
    });
    let node_url = format!("http://{addr}");

    // ── (4) one discovery round-trip to learn the federation id (the fire binding) ───
    let discovery =
        dregg_sdk_net::discover_server_affordances(&node_url, &hex_of(&gm_cell), "signature")
            .await
            .map_err(|e| format!("initial discovery: {e}"))?;

    Ok(MudSession {
        node_url,
        player_cclerk,
        player_cell,
        server_cell_hex: hex_of(&gm_cell),
        federation_id_hex: discovery.executor_federation_id,
        world: MudWorld::derive(),
        _state: state,
        _tmp: tmp,
        _server: server,
    })
}

/// The result of one fired affordance — printable, carrying whether the verified turn
/// committed on the ledger and the turn hash (the receipt id) the node reported.
#[derive(Clone, Debug)]
pub struct PlayOutcome {
    pub accepted: bool,
    pub turn_hash: Option<String>,
    pub error: Option<String>,
}

/// The PLAYABLE CLIENT engine: pure HTTP against a node URL. Connects to a hosted MUD,
/// discovers + fires the cap-gated affordances as signed turns, and reads world state back.
///
/// Borrows the player's signer (`AgentCipherclerk` is not `Clone`) from the [`MudSession`].
pub struct MudClient<'a> {
    node_url: String,
    player_cclerk: &'a AgentCipherclerk,
    player_cell: CellId,
    federation_id_hex: String,
    world: MudWorld,
    http: reqwest::Client,
}

impl<'a> MudClient<'a> {
    /// Build a client over a booted [`MudSession`].
    pub fn from_session(session: &'a MudSession) -> Self {
        MudClient {
            node_url: session.node_url.clone(),
            player_cclerk: &session.player_cclerk,
            player_cell: session.player_cell,
            federation_id_hex: session.federation_id_hex.clone(),
            world: session.world.clone(),
            http: reqwest::Client::new(),
        }
    }

    /// Read a u64 field off a cell on the live ledger (`GET /api/cell/{id}`).
    async fn read_field(&self, cell: &CellId, index: usize) -> Result<u64, String> {
        let url = format!("{}/api/cell/{}", self.node_url, hex_of(cell));
        let body: serde_json::Value = self
            .http
            .get(&url)
            .send()
            .await
            .map_err(|e| format!("cell read request: {e}"))?
            .json()
            .await
            .map_err(|e| format!("cell read parse: {e}"))?;
        if body.get("found").and_then(|f| f.as_bool()) != Some(true) {
            return Err(format!("cell {} not found on the node", hex_of(cell)));
        }
        let field_hex = body
            .get("fields")
            .and_then(|f| f.as_array())
            .and_then(|arr| arr.get(index))
            .and_then(|v| v.as_str())
            .unwrap_or("");
        Ok(unpack_u64_hex(field_hex))
    }

    /// DISCOVER the affordances visible to a signature-holding player on a given surface
    /// (the root server, or a forked dungeon instance cell).
    pub async fn discover(&self, surface_cell_hex: &str) -> Result<Vec<String>, String> {
        let d = dregg_sdk_net::discover_server_affordances(
            &self.node_url,
            surface_cell_hex,
            "signature",
        )
        .await
        .map_err(|e| format!("discover {surface_cell_hex}: {e}"))?;
        Ok(d.affordances.into_iter().map(|a| a.name).collect())
    }

    /// FIRE an affordance: build + sign a turn carrying `effects` named `method` and POST it
    /// to the node's `/turns/submit` ingress — a real verified turn on the live ledger.
    async fn fire(&self, method: &str, effects: Vec<Effect>) -> Result<PlayOutcome, String> {
        let outcome = dregg_sdk_net::fire_affordance(
            &self.node_url,
            self.player_cclerk,
            self.player_cell,
            method,
            effects,
            &self.federation_id_hex,
        )
        .await
        .map_err(|e| format!("fire {method}: {e}"))?;
        Ok(PlayOutcome {
            accepted: outcome.accepted,
            turn_hash: outcome.turn_hash,
            error: outcome.error,
        })
    }

    /// LOOK — render the room the player is in: the character's stats, the room + its exits,
    /// the NPC, the items lying here, and the player's inventory — all read off the REAL
    /// ledger (the room's items + the inventory are item-cell `HELD`/`ROOM` fields).
    pub async fn look(&self) -> Result<String, String> {
        let level = self.read_field(&self.world.character, CHAR_LEVEL).await?;
        let xp = self.read_field(&self.world.character, CHAR_XP).await?;
        let room = self.read_field(&self.world.character, CHAR_ROOM).await?;
        let said = self
            .read_field(&self.world.character, CHAR_SAY_COUNT)
            .await?;
        let mood = self.read_field(&self.world.watchman, NPC_MOOD).await?;

        let mut out = String::new();
        out.push_str(&format!("You are in {}.\n", MudWorld::room_name(room)));
        out.push_str(&format!(
            "  Aria — level {level}, {xp} xp{}.\n",
            if said > 0 {
                format!(" (you have spoken {said}×)")
            } else {
                String::new()
            }
        ));

        // The watchman patrols the Entrance/Hall; describe it where it is relevant.
        if room == ENTRANCE_ROOM {
            out.push_str("  A watchman stands by the gate, ");
            out.push_str(if mood == 0 {
                "calm.\n"
            } else {
                "ALERT — eyeing you.\n"
            });
        } else if room == HALL_ROOM {
            out.push_str("  The watchman from the entrance is ");
            out.push_str(if mood == 0 {
                "still calm.\n"
            } else {
                "ALERT and watching you closely.\n"
            });
        } else if room == TOWER_ROOM {
            out.push_str("  Wind whistles through the high Tower windows.\n");
        } else if room == CELLAR_ROOM {
            out.push_str("  The Cellar is dim and close. A dark stair descends here.\n");
        }

        // ITEMS lying in THIS room (an item is "here" iff its ROOM == room and it is not held).
        for (item, name) in self.items() {
            let held = self.read_field(item, ITEM_HELD).await.unwrap_or(0);
            let iroom = self.read_field(item, ITEM_ROOM).await.unwrap_or(0);
            if held == 0 && iroom == room {
                out.push_str(&format!("  A {name} lies here.\n"));
            }
        }

        // INVENTORY — the items the player holds (HELD == 1).
        let carried = self.inventory().await?;
        if carried.is_empty() {
            out.push_str("  You carry nothing.\n");
        } else {
            out.push_str(&format!("  You carry: {}.\n", carried.join(", ")));
        }

        // EXITS — the room graph.
        let exits = MudWorld::exits(room);
        if exits.is_empty() {
            out.push_str("  There are no obvious exits.\n");
        } else {
            let rendered: Vec<String> = exits
                .iter()
                .map(|(d, dest)| format!("{d} (to {dest})"))
                .collect();
            out.push_str(&format!("  Exits: {}.\n", rendered.join(", ")));
        }
        if room == HALL_ROOM {
            out.push_str("  A dark stair descends into a dungeon here.\n");
        }
        Ok(out)
    }

    /// The named items of the world (the takeable torch + the locked chest).
    fn items(&self) -> [(&CellId, &'static str); 2] {
        [
            (&self.world.torch, "torch"),
            (&self.world.chest, "sealed chest"),
        ]
    }

    /// INVENTORY — the names of the items the player currently holds (HELD == 1).
    pub async fn inventory(&self) -> Result<Vec<String>, String> {
        let mut held = Vec::new();
        for (item, name) in self.items() {
            if self.read_field(item, ITEM_HELD).await.unwrap_or(0) == 1 {
                held.push(name.to_string());
            }
        }
        Ok(held)
    }

    /// MOVE — walk the character into the Hall (fire the `move` affordance: ROOM := 2).
    pub async fn do_move(&self) -> Result<PlayOutcome, String> {
        self.fire(
            "move",
            vec![Effect::SetField {
                cell: self.world.character,
                index: CHAR_ROOM,
                value: pack_u64(HALL_ROOM),
            }],
        )
        .await
    }

    /// GAIN-XP — a kill awards XP (fire the `gain-xp` affordance: XP := 120).
    pub async fn gain_xp(&self) -> Result<PlayOutcome, String> {
        self.fire(
            "gain-xp",
            vec![Effect::SetField {
                cell: self.world.character,
                index: CHAR_XP,
                value: pack_u64(GAIN_XP_VALUE),
            }],
        )
        .await
    }

    /// GO — walk a direction across the exit graph. Resolves `dir` against the player's
    /// CURRENT room; if there's no exit that way, returns `Ok(None)` (no turn fired). On a
    /// valid exit, fires a `go` turn writing the character's ROOM field to the destination
    /// (the player's own location) — authorized because the player holds its character cap.
    /// Returns `(destination_room, outcome)`.
    pub async fn go(&self, dir: &str) -> Result<Option<(u64, PlayOutcome)>, String> {
        let room = self.read_field(&self.world.character, CHAR_ROOM).await?;
        let Some(dest) = MudWorld::exit(room, dir) else {
            return Ok(None);
        };
        let outcome = self
            .fire(
                "go",
                vec![Effect::SetField {
                    cell: self.world.character,
                    index: CHAR_ROOM,
                    value: pack_u64(dest),
                }],
            )
            .await?;
        Ok(Some((dest, outcome)))
    }

    /// TAKE — pick up an item: flip its HELD flag to 1 (the item enters your inventory).
    /// Authorized iff you hold a cap over that item-cell — holding the cap IS being able to
    /// take it. Taking the locked chest (no cap) is REFUSED by the executor's authority gate.
    /// Returns `None` if no such item / it is not in your room; else `Some(outcome)`.
    pub async fn take_item(&self, name: &str) -> Result<Option<PlayOutcome>, String> {
        let Some(item) = self.item_named(name) else {
            return Ok(None);
        };
        let room = self.read_field(&self.world.character, CHAR_ROOM).await?;
        let iroom = self.read_field(&item, ITEM_ROOM).await.unwrap_or(0);
        let held = self.read_field(&item, ITEM_HELD).await.unwrap_or(0);
        // You can only take an item that lies (un-held) in the room you are standing in.
        if held == 1 || iroom != room {
            return Ok(None);
        }
        let outcome = self
            .fire(
                "take",
                vec![Effect::SetField {
                    cell: item,
                    index: ITEM_HELD,
                    value: pack_u64(1),
                }],
            )
            .await?;
        Ok(Some(outcome))
    }

    /// DROP — set an item down in your current room: flip HELD to 0 + stamp its ROOM to here.
    /// Authorized iff you hold the item's cap (you carry it). Returns `None` if not carried.
    pub async fn drop_item(&self, name: &str) -> Result<Option<PlayOutcome>, String> {
        let Some(item) = self.item_named(name) else {
            return Ok(None);
        };
        if self.read_field(&item, ITEM_HELD).await.unwrap_or(0) != 1 {
            return Ok(None); // not carried
        }
        let room = self.read_field(&self.world.character, CHAR_ROOM).await?;
        let outcome = self
            .fire(
                "drop",
                vec![
                    Effect::SetField {
                        cell: item,
                        index: ITEM_HELD,
                        value: pack_u64(0),
                    },
                    Effect::SetField {
                        cell: item,
                        index: ITEM_ROOM,
                        value: pack_u64(room),
                    },
                ],
            )
            .await?;
        Ok(Some(outcome))
    }

    /// SAY — speak in the room: bump your character's utterance counter (your own field).
    pub async fn say(&self) -> Result<PlayOutcome, String> {
        let count = self
            .read_field(&self.world.character, CHAR_SAY_COUNT)
            .await
            .unwrap_or(0);
        self.fire(
            "say",
            vec![Effect::SetField {
                cell: self.world.character,
                index: CHAR_SAY_COUNT,
                value: pack_u64(count + 1),
            }],
        )
        .await
    }

    /// Resolve an item name (loose match) to its cell id.
    fn item_named(&self, name: &str) -> Option<CellId> {
        let n = name.trim().to_lowercase();
        if n.contains("torch") {
            Some(self.world.torch)
        } else if n.contains("chest") {
            Some(self.world.chest)
        } else {
            None
        }
    }

    /// Whether an item (by name) is currently held by the player — for tests/narration.
    pub async fn holds(&self, name: &str) -> Result<bool, String> {
        let Some(item) = self.item_named(name) else {
            return Ok(false);
        };
        Ok(self.read_field(&item, ITEM_HELD).await.unwrap_or(0) == 1)
    }

    /// DESCEND — enter the player's PERSONAL dungeon instance (fire the instance-scoped
    /// `descend`: the dungeon's DESCENDED slot := 1). The player was admitted, so this
    /// authorizes. Returns `(surface_visible, outcome)`.
    pub async fn descend(&self) -> Result<(bool, PlayOutcome), String> {
        let names = self.discover(&hex_of(&self.world.dungeon)).await?;
        let visible = names.iter().any(|n| n == "descend");
        let outcome = self
            .fire(
                "descend",
                vec![Effect::SetField {
                    cell: self.world.dungeon,
                    index: DUNGEON_DESCENDED,
                    value: pack_u64(1),
                }],
            )
            .await?;
        Ok((visible, outcome))
    }

    /// Whether the player has descended into their personal dungeon (the instance's flag).
    pub async fn dungeon_descended(&self) -> Result<bool, String> {
        Ok(self
            .read_field(&self.world.dungeon, DUNGEON_DESCENDED)
            .await?
            == 1)
    }

    /// THE ASYMMETRY (the refusal): attempt to `descend` into the SEALED dungeon — an
    /// instance the player was NOT admitted to. Discoverable, but the fire is REFUSED by the
    /// executor's reach gate (fork isolation). Returns `(surface_visible, outcome)`; a
    /// well-behaved node returns `accepted == false`.
    pub async fn descend_sealed(&self) -> Result<(bool, PlayOutcome), String> {
        let names = self.discover(&hex_of(&self.world.sealed_dungeon)).await?;
        let visible = names.iter().any(|n| n == "descend");
        let outcome = self
            .fire(
                "descend",
                vec![Effect::SetField {
                    cell: self.world.sealed_dungeon,
                    index: DUNGEON_DESCENDED,
                    value: pack_u64(1),
                }],
            )
            .await?;
        Ok((visible, outcome))
    }

    /// THE ASYMMETRY (the refusal): attempt a GM-only move — a cross-cell write on the NPC
    /// the player holds NO cap over. REFUSED by the executor's authority gate.
    pub async fn forge_npc(&self) -> Result<PlayOutcome, String> {
        self.fire(
            "forge-npc",
            vec![Effect::SetField {
                cell: self.world.watchman,
                index: NPC_MOOD,
                value: pack_u64(99),
            }],
        )
        .await
    }

    /// The player's current room (1 = Entrance, 2 = Hall).
    pub async fn room(&self) -> Result<u64, String> {
        self.read_field(&self.world.character, CHAR_ROOM).await
    }

    /// The player's (level, xp).
    pub async fn stats(&self) -> Result<(u64, u64), String> {
        let level = self.read_field(&self.world.character, CHAR_LEVEL).await?;
        let xp = self.read_field(&self.world.character, CHAR_XP).await?;
        Ok((level, xp))
    }

    /// The watchman NPC's mood (0 = calm, 1 = alert).
    pub async fn npc_mood(&self) -> Result<u64, String> {
        self.read_field(&self.world.watchman, NPC_MOOD).await
    }

    /// The world cells (for the `tick` re-host, which needs the character + NPC hexes).
    pub fn world(&self) -> &MudWorld {
        &self.world
    }
}

/// RE-HOST the GM's reactive tick (`mud_play_tick.js`) against the live `state`: the GM
/// observes the ledger and the WORLD RESPONDS (level-up + NPC reaction). This is a GM
/// superpower (a player cannot reach it); the playable harness exposes it as a `tick`
/// command so you can watch the world react to what you did.
pub async fn gm_tick(state: &NodeState, world: &MudWorld) -> Result<(), String> {
    let tick = include_str!("../tests/fixtures/mud_play_tick.js")
        .replace("__CHAR__", &hex_of(&world.character))
        .replace("__NPC__", &hex_of(&world.watchman));
    crate::deos_host::host_server_program(
        state,
        "mud-play-gamemaster-tick",
        AuthRequired::None,
        tick,
    )
    .await
    .map(|_| ())
    .map_err(|e| format!("host mud_play_tick.js: {e}"))
}

/// THE INTERACTIVE REPL — play the MUD from a terminal. Reads commands off `input`, drives
/// the world over real HTTP through [`MudClient`], and writes the narration to `output`.
///
/// Commands: `look`, `move`, `gain-xp`, `tick`, `descend`, `forge`, `help`, `quit`.
pub async fn run_repl<R: BufRead, W: Write>(
    session: &MudSession,
    mut input: R,
    mut output: W,
) -> std::io::Result<()> {
    let client = MudClient::from_session(session);

    writeln!(output, "{}", BANNER)?;
    writeln!(
        output,
        "Connected to the MUD at {} as Aria (player cell {}…).",
        session.node_url,
        &hex_of(&session.player_cell)[..12]
    )?;
    writeln!(output, "Type `help` for commands, `look` to begin.\n")?;
    output.flush()?;

    loop {
        write!(output, "> ")?;
        output.flush()?;
        let mut line = String::new();
        let n = input.read_line(&mut line)?;
        if n == 0 {
            break; // EOF
        }
        let cmd = line.trim();
        if cmd.is_empty() {
            continue;
        }
        let mut words = cmd.split_whitespace();
        let verb = words.next().unwrap_or("").to_lowercase();
        let arg = words.collect::<Vec<_>>().join(" ");

        match verb.as_str() {
            "help" | "?" => {
                writeln!(output, "{}", HELP)?;
            }
            "look" | "l" => match client.look().await {
                Ok(view) => write!(output, "{view}")?,
                Err(e) => writeln!(output, "(the world is hazy: {e})")?,
            },
            // Directional movement across the exit graph: `go north`, or bare `north`/`n`/…
            "go" | "north" | "n" | "south" | "s" | "up" | "u" | "down" => {
                let dir = if verb == "go" {
                    arg.clone()
                } else {
                    verb.clone()
                };
                match client.go(&dir).await {
                    Ok(Some((dest, o))) => {
                        render_outcome(
                            &mut output,
                            &format!("You head {dir} into {}", MudWorld::room_name(dest)),
                            &o,
                        )?;
                        if o.accepted {
                            if let Ok(view) = client.look().await {
                                write!(output, "{view}")?;
                            }
                        }
                    }
                    Ok(None) => writeln!(output, "You can't go {dir} from here.")?,
                    Err(e) => writeln!(output, "(your step falters: {e})")?,
                }
            }
            // The legacy fixed `move` verb (walks north into the Hall) — kept for compat.
            "move" => match client.do_move().await {
                Ok(o) => {
                    render_outcome(&mut output, "You walk north into the Hall", &o)?;
                    if o.accepted {
                        if let Ok(view) = client.look().await {
                            write!(output, "{view}")?;
                        }
                    }
                }
                Err(e) => writeln!(output, "(your step falters: {e})")?,
            },
            "take" | "get" => match client.take_item(&arg).await {
                Ok(Some(o)) => {
                    if o.accepted {
                        render_outcome(&mut output, &format!("You take the {arg}"), &o)?;
                    } else {
                        writeln!(
                            output,
                            "You reach for the {arg}, but the world REFUSES you: {}",
                            o.error
                                .unwrap_or_else(|| "(no cap over it — it is locked)".to_string())
                        )?;
                    }
                }
                Ok(None) => writeln!(output, "There is no {arg} here to take.")?,
                Err(e) => writeln!(output, "(your hand passes through it: {e})")?,
            },
            "drop" => match client.drop_item(&arg).await {
                Ok(Some(o)) => render_outcome(&mut output, &format!("You set down the {arg}"), &o)?,
                Ok(None) => writeln!(output, "You aren't carrying a {arg}.")?,
                Err(e) => writeln!(output, "(it sticks to your hand: {e})")?,
            },
            "inventory" | "inv" | "i" => match client.inventory().await {
                Ok(items) if items.is_empty() => writeln!(output, "You carry nothing.")?,
                Ok(items) => writeln!(output, "You carry: {}.", items.join(", "))?,
                Err(e) => writeln!(output, "(your pack is a blur: {e})")?,
            },
            "say" | "speak" => {
                let words = if arg.is_empty() { "Hello?" } else { &arg };
                match client.say().await {
                    Ok(o) => render_outcome(&mut output, &format!("You say, \"{words}\""), &o)?,
                    Err(e) => writeln!(output, "(your voice catches: {e})")?,
                }
            }
            "gain-xp" | "kill" | "fight" => match client.gain_xp().await {
                Ok(o) => {
                    render_outcome(&mut output, "You strike down a foe and gain experience", &o)?
                }
                Err(e) => writeln!(output, "(the foe slips away: {e})")?,
            },
            "tick" | "wait" => {
                writeln!(output, "Time passes. The Gamemaster observes the world…")?;
                match gm_tick(&session._state, client.world()).await {
                    Ok(()) => {
                        let (level, xp) = client.stats().await.unwrap_or((0, 0));
                        let mood = client.npc_mood().await.unwrap_or(0);
                        writeln!(
                            output,
                            "  The world responds: Aria is level {level} ({xp} xp); the watchman is {}.",
                            if mood == 0 { "calm" } else { "ALERT" }
                        )?;
                    }
                    Err(e) => writeln!(output, "  (the world is still: {e})")?,
                }
            }
            "descend" | "dungeon" | "enter" => match client.descend().await {
                Ok((visible, o)) => {
                    if !visible {
                        writeln!(output, "(you sense no stair here)")?;
                    }
                    render_outcome(&mut output, "You descend into your dungeon instance", &o)?;
                }
                Err(e) => writeln!(output, "(the stair crumbles: {e})")?,
            },
            "forge" | "cheat" => {
                writeln!(
                    output,
                    "You try to bend the watchman to your will (a forbidden GM-only write)…"
                )?;
                match client.forge_npc().await {
                    Ok(o) => {
                        if o.accepted {
                            writeln!(
                                output,
                                "  …it WORKED?! (this should not happen — the asymmetry broke)"
                            )?;
                        } else {
                            writeln!(
                                output,
                                "  …the world REFUSES you. {}",
                                o.error.unwrap_or_else(
                                    || "(no cap over the NPC — GM-only)".to_string()
                                )
                            )?;
                        }
                    }
                    Err(e) => writeln!(output, "  …the attempt fizzles: {e}")?,
                }
            }
            "quit" | "exit" | "q" => {
                writeln!(output, "You step out of the world. Farewell.")?;
                break;
            }
            other => {
                writeln!(output, "You can't `{other}` here. Type `help`.")?;
            }
        }
        output.flush()?;
    }
    Ok(())
}

fn render_outcome<W: Write>(
    output: &mut W,
    narration: &str,
    o: &PlayOutcome,
) -> std::io::Result<()> {
    if o.accepted {
        let receipt = o
            .turn_hash
            .as_deref()
            .map(|h| format!(" [receipt {}…]", &h[..h.len().min(12)]))
            .unwrap_or_default();
        writeln!(output, "{narration}.{receipt}")
    } else {
        writeln!(
            output,
            "{narration}… but the turn was REFUSED: {}",
            o.error
                .clone()
                .unwrap_or_else(|| "(no reason given)".to_string())
        )
    }
}

const BANNER: &str = "\
╔══════════════════════════════════════════════════════════════╗
║  THE DREGG MUD — a living world hosted on a verified ledger   ║
║  every move you make is a real, signed, verified turn.        ║
╚══════════════════════════════════════════════════════════════╝";

const HELP: &str = "\
Commands:
  look      (l)            — look around the room you're in
  go <dir>  (north/up/…)   — walk an exit (north, south, up, down) across the map
  take <it> (get)          — pick up an item lying here (the cap IS the takeability)
  drop <it>                — set an item down in this room
  inventory (inv / i)      — list what you carry
  say <msg> (speak)        — speak in the room (a receipted utterance)
  gain-xp   (kill / fight) — strike down a foe and gain experience
  tick      (wait)         — let the Gamemaster observe; the world responds
  descend   (dungeon)      — descend into your personal dungeon instance
  forge     (cheat)        — try a forbidden GM-only write (it is refused)
  help      (?)            — show this
  quit      (q / exit)     — leave the world";

/// THE PLAYABLE BINARY ENTRY — boot a self-contained world and drop you into the REPL,
/// playing over real HTTP against the in-process node's live ledger.
pub async fn play_interactive(player_seed: &str) {
    let session = match boot_mud_world(player_seed).await {
        Ok(s) => s,
        Err(e) => {
            eprintln!("failed to boot the MUD world: {e}");
            std::process::exit(1);
        }
    };
    let stdin = std::io::stdin();
    let stdout = std::io::stdout();
    if let Err(e) = run_repl(&session, stdin.lock(), stdout.lock()).await {
        eprintln!("mud client error: {e}");
    }
}
