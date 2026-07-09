//! shared_world.rs — A LIVE SHARED WORLD two identities co-inhabit, over the node wire.
//!
//! This is the first REAL rung of MULTI-PERSON deos: not one client firing into a hosted
//! world (that is [`crate::mud_client`]), and not two ISOLATED forks (that is the
//! membrane), but TWO distinct key-ceremony identities co-inhabiting ONE shared space —
//! each seeing the other's actions LIVE.
//!
//! THE ARCHITECTURE (what this proves):
//!   * a headless dregg node HOSTS a shared-world GM (`shared_world_gm.js`) — it spawns a
//!     shared BOARD cell, a presence SEAT per identity, and a PRIVATE cell, then grants
//!     EACH connecting identity a cap over the SHARED board + its own seat (a genuinely
//!     shared space, not isolated forks);
//!   * TWO clients ([`SharedClient`]), each a DISTINCT identity ([`dregg_sdk::AgentCipherclerk`]
//!     from its own key-ceremony seed), connect over real HTTP, discover the affordances,
//!     and FIRE cap-gated turns into the shared board — each `post` a genuine verified turn
//!     committed on the node's ONE ledger, attributed to the firing identity (`receipt.agent`);
//!   * LIVE SYNC: each client SUBSCRIBES to the node's receipt event stream
//!     ([`dregg_sdk_net::NodeEvents`] over `/api/events/stream`), so when identity A commits
//!     a turn, identity B's client OBSERVES it live (receives the receipt, re-reads the
//!     changed board) — the world updates for EVERYONE, not just the actor;
//!   * PRESENCE + ATTRIBUTION: each identity flips its seat's present flag on connect, and
//!     every observed receipt carries `agent` (which identity acted) + `turn_hash` (the
//!     receipt) — so a watcher sees WHO is connected and WHO did each turn;
//!   * THE OVER-REACH (the refusal): identity B fires `touch-private` over PRIVATE-A — a
//!     cell only A was granted a cap on. B can SEE the verb but the executor's authority
//!     gate REFUSES the B-signed write (a receipted refusal), leaving the cell unchanged.
//!
//! The cockpit RENDERING this shared world live (two seats, the board updating for both as
//! turns land) is the explicit follow-on; this module is the headless, gpui-free engine the
//! cockpit (or any thin client) drives — proven by the [`crate::shared_world_e2e`] harness.
#![cfg(feature = "deos-host")]
// The shared-world boot harness + client surface are consumed by the `shared_world_e2e`
// integration proof (a `cfg(test)` sibling) and are the engine a cockpit / thin client
// drives; the plain `--bin` build (no `cfg(test)`) compiles them but reaches none, so the
// honest annotation is that this is a demonstrative harness surface, not bin-dead code.

use dregg_cell::{AuthRequired, Cell, CellId, Permissions};
use dregg_sdk::AgentCipherclerk;
use dregg_sdk_net::{NodeEvents, ReceiptFilter, ReceiptStream};
use dregg_turn::action::Effect;

use crate::state::NodeState;

/// Field-slot layout the GM stamps (matches `shared_world_gm.js`).
const BOARD_POST_COUNT: usize = 0;
const BOARD_LAST_FROM_A: usize = 1;
const BOARD_LAST_FROM_B: usize = 2;
const SEAT_PRESENT: usize = 0;
const SEAT_LAST_POSTED: usize = 1;
const PRIVATE_TOUCHED: usize = 0;

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

fn decode_hex(s: &str) -> Option<Vec<u8>> {
    let s = s.trim();
    if !s.len().is_multiple_of(2) {
        return None;
    }
    let mut out = Vec::with_capacity(s.len() / 2);
    for pair in s.as_bytes().chunks_exact(2) {
        let hi = (pair[0] as char).to_digit(16)?;
        let lo = (pair[1] as char).to_digit(16)?;
        out.push((hi * 16 + lo) as u8);
    }
    Some(out)
}

/// Read a u64 back out of a hex-encoded `FieldElement` (LE low 8 bytes).
fn unpack_u64_hex(field_hex: &str) -> u64 {
    let bytes = match decode_hex(field_hex) {
        Some(b) if b.len() >= 8 => b,
        _ => return 0,
    };
    let mut b = [0u8; 8];
    b.copy_from_slice(&bytes[..8]);
    u64::from_le_bytes(b)
}

/// Derive an agent cell id the way the node's signed-turn ingress does.
fn agent_cell_for(pubkey: &[u8; 32]) -> CellId {
    CellId(dregg_cell::CellId::derive_raw(pubkey, &default_token_id()).0)
}

/// Derive a cell id the way `deos.server.spawnCell(seed, ...)` does.
fn spawned_cell_for(seed: &str) -> CellId {
    let pubkey = *blake3::hash(seed.as_bytes()).as_bytes();
    CellId(dregg_cell::CellId::derive_raw(&pubkey, &default_token_id()).0)
}

/// The cells of the shared world (re-derived from `shared_world_gm.js`'s seeds).
#[derive(Clone, Debug)]
pub struct SharedWorld {
    /// The shared board both identities hold a cap over (the co-act surface).
    pub board: CellId,
    /// Identity A's presence seat.
    pub seat_a: CellId,
    /// Identity B's presence seat.
    pub seat_b: CellId,
    /// A cell ONLY identity A was granted a cap over (the over-reach foil).
    pub private_a: CellId,
}

impl SharedWorld {
    fn derive() -> Self {
        SharedWorld {
            board: spawned_cell_for("shared-world-board"),
            seat_a: spawned_cell_for("shared-world-seat-a"),
            seat_b: spawned_cell_for("shared-world-seat-b"),
            private_a: spawned_cell_for("shared-world-private-a"),
        }
    }
}

/// Which seat an identity occupies in the shared world.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Seat {
    A,
    B,
}

/// A booted shared world: an in-process node with the shared-world GM hosted, a served TCP
/// listener, and the two identities the clients play AS. Dropping it tears the world down.
/// The handles (`_state`, `_tmp`, `_server`) keep the node alive.
pub struct SharedSession {
    /// The node URL both clients talk to (a real `http://127.0.0.1:PORT`).
    pub node_url: String,
    /// Identity A's signer + its agent cell.
    pub a_cclerk: AgentCipherclerk,
    pub a_cell: CellId,
    /// Identity B's signer + its agent cell.
    pub b_cclerk: AgentCipherclerk,
    pub b_cell: CellId,
    /// The GM (root server) cell — the discovery key.
    pub server_cell_hex: String,
    /// The executor federation id (the fire-signing binding).
    pub federation_id_hex: String,
    /// The shared world cells.
    pub world: SharedWorld,
    _state: NodeState,
    _tmp: tempfile::TempDir,
    _server: tokio::task::JoinHandle<()>,
}

/// BOOT a complete shared world: an in-process headless node, two funded+open identity
/// cells (from `seed_a` / `seed_b`), the shared-world GM hosted (spawning the board + seats,
/// granting each identity its caps, publishing the affordances), and a real TCP listener.
pub async fn boot_shared_world(seed_a: &str, seed_b: &str) -> Result<SharedSession, String> {
    let _ = rustls::crypto::ring::default_provider().install_default();

    // ── (1) a headless NodeState (NO gpui — node + deos-js only) ────────────────────
    let tmp = tempfile::tempdir().map_err(|e| format!("tempdir: {e}"))?;
    let state = NodeState::new(tmp.path(), vec![]).map_err(|e| format!("NodeState: {e}"))?;
    {
        let mut s = state.write().await;
        s.unlocked = true; // the signed-turn ingress requires an unlocked node
    }

    // ── THE TWO IDENTITIES — each its own cipherclerk + a funded, open agent cell ────
    let (a_cclerk, a_cell) = mint_identity(&state, seed_a).await?;
    let (b_cclerk, b_cell) = mint_identity(&state, seed_b).await?;

    // ── (2) HOST shared_world_gm.js — spawn the board+seats, grant each identity ─────
    let gm_program = include_str!("../tests/fixtures/shared_world_gm.js")
        .replace("__PLAYER_A__", &hex_of(&a_cell))
        .replace("__PLAYER_B__", &hex_of(&b_cell));
    let gm_cell = crate::deos_host::host_server_program(
        &state,
        "shared-world-gamemaster",
        AuthRequired::None,
        gm_program,
    )
    .await
    .map_err(|e| format!("host shared_world_gm.js: {e}"))?;

    // ── (3) bind a REAL HTTP listener so both clients drive the genuine wire ─────────
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
            router.into_make_service_with_connect_info::<std::net::SocketAddr>(),
        )
        .await;
    });
    let node_url = format!("http://{addr}");

    // ── (4) one discovery round-trip to learn the federation id (the fire binding) ───
    let discovery =
        dregg_sdk_net::discover_server_affordances(&node_url, &hex_of(&gm_cell), "signature")
            .await
            .map_err(|e| format!("initial discovery: {e}"))?;

    Ok(SharedSession {
        node_url,
        a_cclerk,
        a_cell,
        b_cclerk,
        b_cell,
        server_cell_hex: hex_of(&gm_cell),
        federation_id_hex: discovery.executor_federation_id,
        world: SharedWorld::derive(),
        _state: state,
        _tmp: tmp,
        _server: server,
    })
}

/// Mint one identity: a fresh cipherclerk from `seed`, plus its funded, open agent cell on
/// the node's ledger (the client identity). Returns `(signer, agent_cell)`.
async fn mint_identity(
    state: &NodeState,
    seed: &str,
) -> Result<(AgentCipherclerk, CellId), String> {
    let cclerk = AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(
        *blake3::hash(seed.as_bytes()).as_bytes(),
    ));
    let pubkey = cclerk.public_key().0;
    let cell = agent_cell_for(&pubkey);
    {
        let mut s = state.write().await;
        let mut agent = Cell::with_balance(pubkey, default_token_id(), 1_000_000);
        agent.permissions = open_permissions();
        if agent.id() != cell {
            return Err("identity cell id derivation mismatch".to_string());
        }
        if s.ledger.get(&cell).is_none() {
            s.ledger
                .insert_cell(agent)
                .map_err(|e| format!("insert identity cell: {e}"))?;
        }
    }
    Ok((cclerk, cell))
}

/// The result of one fired affordance — whether it committed + the turn hash (receipt id).
#[derive(Clone, Debug)]
pub struct PostOutcome {
    pub accepted: bool,
    pub turn_hash: Option<String>,
    pub error: Option<String>,
}

/// ONE identity's client onto the shared world: pure HTTP against the node URL, signing AS
/// its own identity. Two of these (Seat A + Seat B) co-inhabit the one shared world.
///
/// Borrows the identity's signer (`AgentCipherclerk` is not `Clone`) from the session.
pub struct SharedClient<'a> {
    node_url: String,
    cclerk: &'a AgentCipherclerk,
    agent_cell: CellId,
    seat: Seat,
    federation_id_hex: String,
    world: SharedWorld,
    http: reqwest::Client,
    events: NodeEvents,
}

impl<'a> SharedClient<'a> {
    /// Build identity A's client onto the shared session.
    pub fn seat_a(session: &'a SharedSession) -> Self {
        Self::new(session, Seat::A, &session.a_cclerk, session.a_cell)
    }

    /// Build identity B's client onto the shared session.
    pub fn seat_b(session: &'a SharedSession) -> Self {
        Self::new(session, Seat::B, &session.b_cclerk, session.b_cell)
    }

    fn new(
        session: &'a SharedSession,
        seat: Seat,
        cclerk: &'a AgentCipherclerk,
        agent_cell: CellId,
    ) -> Self {
        SharedClient {
            node_url: session.node_url.clone(),
            cclerk,
            agent_cell,
            seat,
            federation_id_hex: session.federation_id_hex.clone(),
            world: session.world.clone(),
            http: reqwest::Client::new(),
            events: NodeEvents::new(session.node_url.clone()),
        }
    }

    /// This client's identity agent cell (its attribution key on every receipt).
    pub fn identity(&self) -> CellId {
        self.agent_cell
    }

    /// This client's seat cell.
    fn seat_cell(&self) -> CellId {
        match self.seat {
            Seat::A => self.world.seat_a,
            Seat::B => self.world.seat_b,
        }
    }

    /// The board slot this identity stamps when it posts (A → slot 1, B → slot 2).
    fn board_lane(&self) -> usize {
        match self.seat {
            Seat::A => BOARD_LAST_FROM_A,
            Seat::B => BOARD_LAST_FROM_B,
        }
    }

    /// SUBSCRIBE to the live turns of a SPECIFIC other identity — the LIVE SYNC edge a
    /// watcher uses to see a co-inhabitant act. Every turn that identity commits arrives
    /// here as a [`dregg_sdk::receipt::Receipt`] carrying `agent` (who acted, == `who`) +
    /// `turn_hash` (the receipt). The node's stream `?cell=` filter matches a receipt whose
    /// `agent` is `who`, so a fire signed AS `who` (its posts + presence) lands on this feed
    /// — exactly "B watches A's actions on the shared world."
    pub fn subscribe_to_identity(&self, who: CellId) -> ReceiptStream {
        self.events.subscribe(ReceiptFilter::default().cell(who))
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

    /// DISCOVER the affordances visible to this signature-holding identity on the root
    /// server surface.
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

    /// FIRE an affordance: sign a turn AS this identity carrying `effects` named `method`
    /// and POST it to `/turns/submit` — a real verified turn on the one shared ledger,
    /// attributed to this identity.
    async fn fire(&self, method: &str, effects: Vec<Effect>) -> Result<PostOutcome, String> {
        let outcome = dregg_sdk_net::fire_affordance(
            &self.node_url,
            self.cclerk,
            self.agent_cell,
            method,
            effects,
            &self.federation_id_hex,
        )
        .await
        .map_err(|e| format!("fire {method}: {e}"))?;
        Ok(PostOutcome {
            accepted: outcome.accepted,
            turn_hash: outcome.turn_hash,
            error: outcome.error,
        })
    }

    /// PRESENT — announce yourself in the room: flip this identity's seat PRESENT flag.
    pub async fn present(&self) -> Result<PostOutcome, String> {
        self.fire(
            "present",
            vec![Effect::SetField {
                cell: self.seat_cell(),
                index: SEAT_PRESENT,
                value: pack_u64(1),
            }],
        )
        .await
    }

    /// POST — the co-act: write the SHARED board. Bumps the shared post count, stamps this
    /// identity's lane on the board, AND records the value on this identity's seat — three
    /// cells, all of which this identity holds caps over, so the executor authorizes the
    /// whole turn. `value` is what this identity posts.
    pub async fn post(&self, value: u64) -> Result<PostOutcome, String> {
        // Bump the shared count off its current ledger value (a genuine read-modify-write
        // on shared state — the next post by EITHER identity sees this).
        let count = self
            .read_field(&self.world.board, BOARD_POST_COUNT)
            .await
            .unwrap_or(0);
        self.fire(
            "post",
            vec![
                Effect::SetField {
                    cell: self.world.board,
                    index: BOARD_POST_COUNT,
                    value: pack_u64(count + 1),
                },
                Effect::SetField {
                    cell: self.world.board,
                    index: self.board_lane(),
                    value: pack_u64(value),
                },
                Effect::SetField {
                    cell: self.seat_cell(),
                    index: SEAT_LAST_POSTED,
                    value: pack_u64(value),
                },
            ],
        )
        .await
    }

    /// THE OVER-REACH — attempt to write PRIVATE-A. Discoverable, but only identity A holds
    /// a cap; a B-signed fire is REFUSED by the executor's authority gate.
    pub async fn touch_private(&self) -> Result<PostOutcome, String> {
        self.fire(
            "touch-private",
            vec![Effect::SetField {
                cell: self.world.private_a,
                index: PRIVATE_TOUCHED,
                value: pack_u64(1),
            }],
        )
        .await
    }

    // ── shared-state readers (what every identity sees of the one world) ─────────────

    /// The shared board's post count (how many co-acts have landed).
    pub async fn board_count(&self) -> Result<u64, String> {
        self.read_field(&self.world.board, BOARD_POST_COUNT).await
    }

    /// The last value A posted to the shared board.
    pub async fn board_last_from_a(&self) -> Result<u64, String> {
        self.read_field(&self.world.board, BOARD_LAST_FROM_A).await
    }

    /// The last value B posted to the shared board.
    pub async fn board_last_from_b(&self) -> Result<u64, String> {
        self.read_field(&self.world.board, BOARD_LAST_FROM_B).await
    }

    /// Whether identity A is present (seat A's flag) — the presence readout.
    pub async fn a_present(&self) -> Result<bool, String> {
        Ok(self.read_field(&self.world.seat_a, SEAT_PRESENT).await? == 1)
    }

    /// Whether identity B is present (seat B's flag).
    pub async fn b_present(&self) -> Result<bool, String> {
        Ok(self.read_field(&self.world.seat_b, SEAT_PRESENT).await? == 1)
    }

    /// Whether PRIVATE-A has been touched (the over-reach must NOT flip this for B).
    pub async fn private_touched(&self) -> Result<bool, String> {
        Ok(self
            .read_field(&self.world.private_a, PRIVATE_TOUCHED)
            .await?
            == 1)
    }
}
