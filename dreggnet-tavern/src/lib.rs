//! dreggnet-tavern — THE SHARED HUB / TAVERN: a persistent social place players inhabit
//! between runs, re-homing the deployed live-co-inhabitance rung (`node/src/shared_world.rs`).
//!
//! This is the connective tissue that makes every other social system discoverable: a
//! persistent shared PLACE cell that N distinct key-ceremony identities co-inhabit, each
//! seeing the others act LIVE, every act a real verified turn on the node's ONE ledger,
//! attributed to the firing identity.
//!
//! THE ARCHITECTURE (re-homed, NOT reinvented — the same primitive `shared_world` is):
//!   * a headless dregg node HOSTS a tavern GM (a generated deos-js program) via
//!     [`dregg_node::deos_host::host_server_program`] — it spawns the shared BOARD cell, a
//!     presence SEAT per patron, a private STALL per patron, and a shared PARTY roster, then
//!     grants EACH connecting identity a cap over the shared board + party + its OWN seat +
//!     its OWN stall (a genuinely shared place, not isolated forks);
//!   * N clients ([`Patron`]), each a DISTINCT identity ([`dregg_sdk::AgentCipherclerk`] from
//!     its own key-ceremony seed), connect over real HTTP, discover the affordances, and FIRE
//!     cap-gated turns into the tavern — each an LFG `post`, a stall `list`, a `party_up`, a
//!     presence `enter` — a genuine verified turn committed on the node's ONE ledger,
//!     attributed to the firing identity (`receipt.agent`);
//!   * LIVE SYNC: each client SUBSCRIBES to the node's receipt event stream
//!     ([`dregg_sdk_net::NodeEvents`] over `/api/events/stream`), so when patron A commits a
//!     turn, patron B's client OBSERVES it live — the tavern updates for EVERYONE;
//!   * UN-FAKEABLE PRESENCE + ATTRIBUTION: each identity flips its seat's PRESENT flag on
//!     entering, and every observed receipt carries `agent` (which identity acted). You
//!     CANNOT fake being present as someone else: a fire is signed by YOUR cipherclerk and
//!     the executor attributes the receipt to YOUR agent cell — a B-signed turn can never
//!     flip A's seat, because B holds no cap over seat A;
//!   * THE OVER-REACH (the refusal): a patron pokes ANOTHER patron's private STALL — a cell
//!     only its owner was granted a cap on. The poker can SEE the verb but the executor's
//!     authority gate REFUSES the un-capped write (a receipted refusal), leaving the stall
//!     unchanged — "you cannot touch another's stall."
//!
//! NAMED RESIDUALS (honest scope): many concurrent tavern ROOMS via a Lobby; spatial
//! presence; tavern furniture as owned assets; the live cockpit/bot render; and the
//! party-roster / stall listings graduating to first-class `dreggnet-party` / `dreggnet-trade`
//! crates (today they are real committed cells inside the tavern — the party-up + market
//! hooks, live and attributed, ready to be routed onward).

use dregg_cell::{AuthRequired, Cell, CellId, Permissions};
use dregg_sdk::AgentCipherclerk;
use dregg_sdk_net::{NodeEvents, ReceiptFilter, ReceiptStream};
use dregg_turn::action::Effect;

use dregg_node::state::NodeState;

// ── Field-slot layout the tavern GM stamps (mirrors the generated program below) ────────
/// Board slot 0 = how many LFG posts have landed (the shared co-act counter).
const BOARD_POST_COUNT: usize = 0;
/// Board slot `1 + i` = the last value patron `i` posted to the LFG board (its lane).
const BOARD_LANE_BASE: usize = 1;
/// Party-roster slot 0 = the formed party's size (how many patrons joined up).
const PARTY_SIZE: usize = 0;
/// Party-roster slot `1 + i` = patron `i`'s member marker (0 = not in the party).
const PARTY_MEMBER_BASE: usize = 1;
/// Seat slot 0 = the PRESENT flag (1 iff this patron is in the tavern).
const SEAT_PRESENT: usize = 0;
/// Seat slot 1 = the last value this patron posted (its personal echo of a board post).
const SEAT_LAST_POSTED: usize = 1;
/// Stall slot 0 = the listing price the owner set (a market listing).
const STALL_PRICE: usize = 0;
/// Stall slot 1 = the LISTED flag (1 iff the owner has an open listing).
const STALL_LISTED: usize = 1;

/// The GM cell seed label (the discovery key of the tavern surface).
const TAVERN_GM_LABEL: &str = "dreggnet-tavern-gamemaster";

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

/// Pack a u64 into a `FieldElement` using the AUTHORITATIVE (verified Lean) producer's field-lane
/// convention: the u64 lives in the HIGH 8 bytes (`field[24..32]`), BIG-endian — the encoding
/// `exec-lean` reads + writes on the commit path (`field_to_i128` reads `field[24..32]` via
/// `from_be_bytes`; `i128_to_field` writes `(v as u64).to_be_bytes()` into `out[24..32]`).
/// Packing into the SDK-era `field[0..8]` little-endian lane makes the producer read the effect
/// value as 0 and commit a zero, so the field never lands; this lane is what round-trips.
fn pack_u64(v: u64) -> dregg_cell::state::FieldElement {
    let mut fe = [0u8; 32];
    fe[24..32].copy_from_slice(&v.to_be_bytes());
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

/// Read a u64 back out of a hex-encoded `FieldElement` — the inverse of [`pack_u64`]: the u64
/// lane is the HIGH 8 bytes (`field[24..32]`), BIG-endian, matching the producer's convention.
fn unpack_u64_hex(field_hex: &str) -> u64 {
    let bytes = match decode_hex(field_hex) {
        Some(b) if b.len() >= 32 => b,
        _ => return 0,
    };
    let mut b = [0u8; 8];
    b.copy_from_slice(&bytes[24..32]);
    u64::from_be_bytes(b)
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

fn board_seed() -> String {
    "dreggnet-tavern-board".to_string()
}
fn party_seed() -> String {
    "dreggnet-tavern-party".to_string()
}
fn seat_seed(i: usize) -> String {
    format!("dreggnet-tavern-seat-{i}")
}
fn stall_seed(i: usize) -> String {
    format!("dreggnet-tavern-stall-{i}")
}

/// The cells of the tavern (re-derived from the generated GM program's seeds). The board +
/// party are shared (every patron holds a cap); each seat + stall is owned by one patron.
#[derive(Clone, Debug)]
pub struct TavernCells {
    /// The LFG board every patron co-writes (the shared co-act surface).
    pub board: CellId,
    /// The party roster every patron may join (the party-up hook).
    pub party: CellId,
    /// One presence seat per patron (index-aligned with the boot seeds).
    pub seats: Vec<CellId>,
    /// One private market stall per patron (the over-reach foil: only the owner is capped).
    pub stalls: Vec<CellId>,
}

impl TavernCells {
    fn derive(n: usize) -> Self {
        TavernCells {
            board: spawned_cell_for(&board_seed()),
            party: spawned_cell_for(&party_seed()),
            seats: (0..n).map(|i| spawned_cell_for(&seat_seed(i))).collect(),
            stalls: (0..n).map(|i| spawned_cell_for(&stall_seed(i))).collect(),
        }
    }
}

/// GENERATE the tavern GM deos-js program for `n` patrons whose agent-cell hexes are
/// `patron_hex`. It spawns the shared board + party, a seat + stall per patron, grants each
/// patron its caps (shared board + party + its OWN seat + its OWN stall — NOT another's
/// stall), and registers the cap-gated verbs. Returns the program source the host evals.
fn tavern_gm_program(patron_hex: &[String]) -> String {
    let n = patron_hex.len();
    let mut js = String::new();
    js.push_str("// dreggnet-tavern GM — generated. A persistent shared PLACE cell + a\n");
    js.push_str("// presence SEAT per patron + a private STALL per patron + a shared PARTY.\n\n");

    // ── the shared LFG board (slot 0 = post count, slot 1+i = patron i's last post) ──
    js.push_str(&format!(
        "var board = deos.server.spawnCell(\"{}\", \"open\");\n",
        board_seed()
    ));
    js.push_str("deos.server.setField(board, 0, 0);\n");
    for i in 0..n {
        js.push_str(&format!(
            "deos.server.setField(board, {}, 0);\n",
            BOARD_LANE_BASE + i
        ));
    }

    // ── the shared PARTY roster (slot 0 = size, slot 1+i = patron i's member marker) ──
    js.push_str(&format!(
        "var party = deos.server.spawnCell(\"{}\", \"open\");\n",
        party_seed()
    ));
    js.push_str("deos.server.setField(party, 0, 0);\n");
    for i in 0..n {
        js.push_str(&format!(
            "deos.server.setField(party, {}, 0);\n",
            PARTY_MEMBER_BASE + i
        ));
    }

    // ── a presence SEAT + a private STALL per patron ──────────────────────────────────
    for i in 0..n {
        js.push_str(&format!(
            "var seat{i} = deos.server.spawnCell(\"{}\", \"open\");\n",
            seat_seed(i)
        ));
        js.push_str(&format!("deos.server.setField(seat{i}, 0, 0);\n"));
        js.push_str(&format!("deos.server.setField(seat{i}, 1, 0);\n"));
        js.push_str(&format!(
            "var stall{i} = deos.server.spawnCell(\"{}\", \"open\");\n",
            stall_seed(i)
        ));
        js.push_str(&format!("deos.server.setField(stall{i}, 0, 0);\n"));
        js.push_str(&format!("deos.server.setField(stall{i}, 1, 0);\n"));
    }

    // ── GRANTS: each patron -> shared board + party + its OWN seat + its OWN stall.
    //    Deliberately NOT another patron's stall — that is the over-reach foil. ────────
    for (i, holder) in patron_hex.iter().enumerate() {
        js.push_str(&format!(
            "deos.server.grant(\"{holder}\", board, \"none\");\n"
        ));
        js.push_str(&format!(
            "deos.server.grant(\"{holder}\", party, \"none\");\n"
        ));
        js.push_str(&format!(
            "deos.server.grant(\"{holder}\", seat{i}, \"none\");\n"
        ));
        js.push_str(&format!(
            "deos.server.grant(\"{holder}\", stall{i}, \"none\");\n"
        ));
    }

    // ── AFFORDANCES: the cap-gated verbs every patron discovers + fires. The advertised
    //    effect is illustrative; each patron fires with its OWN concrete effects (on cells
    //    it holds caps over), so the executor authorizes per-effect. ────────────────────
    js.push_str(
        "deos.server.defineAffordance({ name: \"enter\", required: \"signature\", \
         effects: [ { type: \"setField\", cell: seat0, index: 0, value: 1 } ] });\n",
    );
    js.push_str(
        "deos.server.defineAffordance({ name: \"post\", required: \"signature\", \
         effects: [ { type: \"setField\", cell: board, index: 0, value: 1 } ] });\n",
    );
    js.push_str(
        "deos.server.defineAffordance({ name: \"list\", required: \"signature\", \
         effects: [ { type: \"setField\", cell: stall0, index: 0, value: 1 } ] });\n",
    );
    js.push_str(
        "deos.server.defineAffordance({ name: \"party_up\", required: \"signature\", \
         effects: [ { type: \"setField\", cell: party, index: 0, value: 1 } ] });\n",
    );
    js.push_str(
        "deos.server.defineAffordance({ name: \"poke_stall\", required: \"signature\", \
         effects: [ { type: \"setField\", cell: stall0, index: 0, value: 1 } ] });\n",
    );

    // ── witness: 1 iff every spawn produced a 64-char hex id (the whole tavern stood up).
    let mut checks = vec![
        "board && board.length === 64".to_string(),
        "party && party.length === 64".to_string(),
    ];
    for i in 0..n {
        checks.push(format!("seat{i} && seat{i}.length === 64"));
        checks.push(format!("stall{i} && stall{i}.length === 64"));
    }
    js.push_str(&format!("({}) ? 1 : 0;\n", checks.join(" &&\n ")));
    js
}

/// A booted tavern: an in-process node with the tavern GM hosted, a served TCP listener, and
/// the N identities the patrons play AS. Dropping it tears the tavern down. The handles keep
/// the node alive.
pub struct TavernSession {
    /// The node URL every patron talks to (a real `http://127.0.0.1:PORT`).
    pub node_url: String,
    /// Each patron's signer (index-aligned with `patron_cells`).
    pub patron_clerks: Vec<AgentCipherclerk>,
    /// Each patron's agent cell (its attribution key on every receipt).
    pub patron_cells: Vec<CellId>,
    /// The GM (root server) cell — the discovery key of the tavern surface.
    pub server_cell_hex: String,
    /// The executor federation id (the fire-signing binding).
    pub federation_id_hex: String,
    /// The tavern's cells.
    pub cells: TavernCells,
    _state: NodeState,
    _tmp: tempfile::TempDir,
    _server: tokio::task::JoinHandle<()>,
}

impl TavernSession {
    /// How many patrons this tavern hosts.
    pub fn patron_count(&self) -> usize {
        self.patron_cells.len()
    }
}

/// BOOT a complete tavern: an in-process headless node, N funded+open identity cells (from
/// `seeds`), the tavern GM hosted (spawning the board + party + per-patron seats/stalls,
/// granting each identity its caps, publishing the affordances), and a real TCP listener.
///
/// `seeds` are the per-patron key-ceremony seeds; `seeds.len()` is N. Each seed yields a
/// DISTINCT identity — you cannot fake being a patron whose seed you do not hold.
pub async fn boot_tavern(seeds: &[&str]) -> Result<TavernSession, String> {
    if seeds.is_empty() {
        return Err("a tavern needs at least one patron seed".to_string());
    }
    let _ = rustls::crypto::ring::default_provider().install_default();

    // ── (1) a headless NodeState (NO gpui — node + deos-js only) ────────────────────
    let tmp = tempfile::tempdir().map_err(|e| format!("tempdir: {e}"))?;
    let state = NodeState::new(tmp.path(), vec![]).map_err(|e| format!("NodeState: {e}"))?;
    {
        let mut s = state.write().await;
        s.unlocked = true; // the signed-turn ingress requires an unlocked node
        // SOLO consensus (a committee of one). Without it, `is_solo` is false and the submit
        // path treats every FOREIGN client turn as MULTI-PARTY: it runs the turn in-place only
        // to build the HTTP receipt, then ROLLS THE LEDGER BACK, deferring the authoritative
        // commit to a BFT finalization pass. A single in-process node has no finalization
        // crank, so a patron's `enter`/`post` would never become readable (it commits the
        // receipt but the seat flag never lands). Solo — exactly what the real node runs with
        // no peers (node/src/lib.rs) — keeps the in-place commit authoritatively, so a foreign
        // patron's turn is live on the one ledger the moment `/turns/submit` returns.
        let signing_key = s.cclerk.gossip_signing_key().to_bytes();
        s.solo_consensus = Some(dregg_federation::solo::SoloConsensusState::new(signing_key));
    }

    // ── THE N IDENTITIES — each its own cipherclerk + a funded, open agent cell ──────
    let mut clerks = Vec::with_capacity(seeds.len());
    let mut cells = Vec::with_capacity(seeds.len());
    for seed in seeds {
        let (clerk, cell) = mint_identity(&state, seed).await?;
        clerks.push(clerk);
        cells.push(cell);
    }
    let patron_hex: Vec<String> = cells.iter().map(hex_of).collect();

    // ── (2) HOST the generated tavern GM — spawn the place, grant each identity ───────
    let gm_program = tavern_gm_program(&patron_hex);
    let gm_cell = dregg_node::deos_host::host_server_program(
        &state,
        TAVERN_GM_LABEL,
        AuthRequired::None,
        gm_program,
    )
    .await
    .map_err(|e| format!("host tavern GM: {e}"))?;

    // ── (3) bind a REAL HTTP listener so every patron drives the genuine wire ─────────
    let metrics_handle = dregg_node::metrics::install_recorder();
    let router = dregg_node::api::router_with_cors(
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

    let n = cells.len();
    Ok(TavernSession {
        node_url,
        patron_clerks: clerks,
        patron_cells: cells,
        server_cell_hex: hex_of(&gm_cell),
        federation_id_hex: discovery.executor_federation_id,
        cells: TavernCells::derive(n),
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

/// ONE patron's client onto the tavern: pure HTTP against the node URL, signing AS its own
/// identity. N of these co-inhabit the one tavern.
///
/// Borrows the identity's signer (`AgentCipherclerk` is not `Clone`) from the session.
pub struct Patron<'a> {
    node_url: String,
    cclerk: &'a AgentCipherclerk,
    agent_cell: CellId,
    /// This patron's index (its seat + stall + lane).
    seat_index: usize,
    federation_id_hex: String,
    cells: TavernCells,
    http: reqwest::Client,
    events: NodeEvents,
}

impl<'a> Patron<'a> {
    /// Build the client for patron `index` onto the tavern session.
    pub fn seat(session: &'a TavernSession, index: usize) -> Self {
        Patron {
            node_url: session.node_url.clone(),
            cclerk: &session.patron_clerks[index],
            agent_cell: session.patron_cells[index],
            seat_index: index,
            federation_id_hex: session.federation_id_hex.clone(),
            cells: session.cells.clone(),
            http: reqwest::Client::new(),
            events: NodeEvents::new(session.node_url.clone()),
        }
    }

    /// This patron's identity agent cell (its attribution key on every receipt).
    pub fn identity(&self) -> CellId {
        self.agent_cell
    }

    /// This patron's seat index (its lane on the board + party roster).
    pub fn index(&self) -> usize {
        self.seat_index
    }

    fn seat_cell(&self) -> CellId {
        self.cells.seats[self.seat_index]
    }

    fn own_stall(&self) -> CellId {
        self.cells.stalls[self.seat_index]
    }

    fn board_lane(&self) -> usize {
        BOARD_LANE_BASE + self.seat_index
    }

    /// SUBSCRIBE to the live turns of a SPECIFIC other patron — the LIVE SYNC edge a watcher
    /// uses to see a co-inhabitant act. Every turn that identity commits arrives here as a
    /// [`dregg_sdk::receipt::Receipt`] carrying `agent` (who acted, == `who`) + `turn_hash`.
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

    /// DISCOVER the affordances visible to this signature-holding identity on the tavern
    /// surface.
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

    /// FIRE an affordance: sign a turn AS this identity carrying `effects` named `method` and
    /// POST it to `/turns/submit` — a real verified turn on the one tavern ledger, attributed
    /// to this identity.
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

    // ── the tavern verbs ─────────────────────────────────────────────────────────────

    /// ENTER — walk into the tavern: flip this patron's seat PRESENT flag. This is
    /// UN-FAKEABLE presence: the turn is signed by THIS patron's cipherclerk and the executor
    /// attributes it to THIS agent cell; no one else can flip your seat (they hold no cap
    /// over it) and you cannot flip theirs.
    pub async fn enter(&self) -> Result<PostOutcome, String> {
        self.fire(
            "enter",
            vec![Effect::SetField {
                cell: self.seat_cell(),
                index: SEAT_PRESENT,
                value: pack_u64(1),
            }],
        )
        .await
    }

    /// POST — the LFG board co-act: write the SHARED board. Bumps the shared post count,
    /// stamps this patron's lane, AND records the value on this patron's seat — cells this
    /// patron holds caps over, so the executor authorizes the whole turn. Each post is a real
    /// attributed turn every other patron sees.
    pub async fn post(&self, value: u64) -> Result<PostOutcome, String> {
        let count = self
            .read_field(&self.cells.board, BOARD_POST_COUNT)
            .await
            .unwrap_or(0);
        self.fire(
            "post",
            vec![
                Effect::SetField {
                    cell: self.cells.board,
                    index: BOARD_POST_COUNT,
                    value: pack_u64(count + 1),
                },
                Effect::SetField {
                    cell: self.cells.board,
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

    /// LIST — open a market stall: write YOUR OWN private stall's listing. The market hook.
    /// Only you hold a cap over your stall, so this commits; another patron writing it is
    /// refused (see [`Patron::poke_stall`]).
    pub async fn list(&self, price: u64) -> Result<PostOutcome, String> {
        self.fire(
            "list",
            vec![
                Effect::SetField {
                    cell: self.own_stall(),
                    index: STALL_PRICE,
                    value: pack_u64(price),
                },
                Effect::SetField {
                    cell: self.own_stall(),
                    index: STALL_LISTED,
                    value: pack_u64(1),
                },
            ],
        )
        .await
    }

    /// PARTY_UP — join the shared party roster: bump the party size + stamp this patron's
    /// member marker. The party-up hook: a formed party is the roster with N members. Every
    /// patron holds a cap over the shared roster, so each join commits — attributed.
    pub async fn party_up(&self, marker: u64) -> Result<PostOutcome, String> {
        let size = self
            .read_field(&self.cells.party, PARTY_SIZE)
            .await
            .unwrap_or(0);
        self.fire(
            "party_up",
            vec![
                Effect::SetField {
                    cell: self.cells.party,
                    index: PARTY_SIZE,
                    value: pack_u64(size + 1),
                },
                Effect::SetField {
                    cell: self.cells.party,
                    index: PARTY_MEMBER_BASE + self.seat_index,
                    value: pack_u64(marker),
                },
            ],
        )
        .await
    }

    /// POKE_STALL — attempt to write patron `owner_index`'s private stall. Discoverable, but
    /// only that patron holds a cap; a fire by anyone else is REFUSED by the executor's
    /// authority gate. Firing against your OWN index is authorized (proving the refusal is
    /// authority, not a broken verb) — "you cannot touch another's stall."
    pub async fn poke_stall(&self, owner_index: usize, value: u64) -> Result<PostOutcome, String> {
        self.fire(
            "poke_stall",
            vec![Effect::SetField {
                cell: self.cells.stalls[owner_index],
                index: STALL_PRICE,
                value: pack_u64(value),
            }],
        )
        .await
    }

    /// POKE_SEAT — attempt to flip patron `index`'s presence seat. Firing against your OWN
    /// index is [`Patron::enter`]; firing against ANOTHER'S is the presence forge — you sign
    /// AS yourself and hold no cap over their seat, so the executor REFUSES it. This is the
    /// negative witness that presence is un-fakeable: you cannot fake being online as someone
    /// else.
    pub async fn poke_seat(&self, index: usize) -> Result<PostOutcome, String> {
        self.fire(
            "enter",
            vec![Effect::SetField {
                cell: self.cells.seats[index],
                index: SEAT_PRESENT,
                value: pack_u64(1),
            }],
        )
        .await
    }

    // ── shared-state readers (what every patron sees of the one tavern) ────────────────

    /// The LFG board's post count (how many co-acts have landed).
    pub async fn board_count(&self) -> Result<u64, String> {
        self.read_field(&self.cells.board, BOARD_POST_COUNT).await
    }

    /// The last value patron `index` posted to the shared board.
    pub async fn board_last_from(&self, index: usize) -> Result<u64, String> {
        self.read_field(&self.cells.board, BOARD_LANE_BASE + index)
            .await
    }

    /// Whether patron `index` is present (its seat's flag) — the presence readout.
    pub async fn present(&self, index: usize) -> Result<bool, String> {
        Ok(self
            .read_field(&self.cells.seats[index], SEAT_PRESENT)
            .await?
            == 1)
    }

    /// The formed party's size (how many patrons have joined the roster).
    pub async fn party_size(&self) -> Result<u64, String> {
        self.read_field(&self.cells.party, PARTY_SIZE).await
    }

    /// Patron `index`'s member marker on the party roster (0 = not joined).
    pub async fn party_member(&self, index: usize) -> Result<u64, String> {
        self.read_field(&self.cells.party, PARTY_MEMBER_BASE + index)
            .await
    }

    /// Patron `index`'s stall listing price (0 = nothing listed).
    pub async fn stall_price(&self, index: usize) -> Result<u64, String> {
        self.read_field(&self.cells.stalls[index], STALL_PRICE)
            .await
    }

    /// Whether patron `index` has an open stall listing.
    pub async fn stall_listed(&self, index: usize) -> Result<bool, String> {
        Ok(self
            .read_field(&self.cells.stalls[index], STALL_LISTED)
            .await?
            == 1)
    }
}
