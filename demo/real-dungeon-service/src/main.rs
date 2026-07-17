//! # real-dungeon-service — the REAL `dungeon-on-dregg` engine, played + verified over HTTP.
//!
//! The honest replacement for the LARP `/game` lane. It hosts the committed real game —
//! [`dungeon_on_dregg::deploy_keep`] (The Warden's Keep) — on `spween-dregg`'s real
//! [`WorldCell`](spween_dregg::WorldCell), the same `EmbeddedExecutor`/cell/`TurnReceipt` the
//! flagship substrate uses. Not a re-skin of `attested-dm`'s toy `WorldCell`/blake3 ledger:
//! this service does not depend on `attested-dm` at all.
//!
//! ## A move is a real executor turn over the wire
//!
//! `POST /session/move {"index":N}` looks up the chosen [`spween::Choice`] at the player's
//! current room and drives it at the real executor via
//! [`WorldCell::apply_choice`](spween_dregg::WorldCell::apply_choice): the choice's effects
//! become `Effect::SetField` cell writes, its navigation advances the passage slot, and the
//! whole thing is ONE cap-bounded turn the [`EmbeddedExecutor`] admits IFF the installed
//! [`CellProgram`] gate case passes on the post-state. A LEGAL move returns a real
//! [`TurnReceipt`](dregg_app_framework::TurnReceipt) (its `turnHash`/`preStateHash`/
//! `postStateHash` surfaced verbatim from the wire). An ILLEGAL move — e.g. claiming the
//! already-held crown for a rival banner (a `WriteOnce` tooth), an over-budget second ward
//! (a cross-slot `FieldLteField`), a killing blow (a `FieldGte` HP floor), climbing the
//! collapsed stair (a `Monotonic` ratchet) — is a real [`WorldError::Refused`] from the
//! executor that commits NOTHING (anti-ghost: the session state is unchanged).
//!
//! ## The endpoints
//!
//! * `POST /session/start {"seed":N?}` — (re)deploy a fresh keep WorldCell; seed the
//!   fight/budget the intro passage sets at genesis (`hp = 50`, `mana_budget = 50`).
//! * `GET  /session/state` — the current room, the executor-committed vars, ended/won, the
//!   committed receipt count + the last few receipt hashes.
//! * `GET  /session/moves` — the LEGAL moves at the current room, each with the real executor
//!   `StateConstraint` teeth guarding it (proof the rule is a kernel predicate, not app code).
//! * `POST /session/move {"index":N}` — one real cap-bounded turn (see above).
//! * `GET  /session/verify` — re-drive a fresh, identically-seeded keep through the recorded
//!   choice sequence ([`verify_by_replay`](spween_dregg::verify_by_replay)) and check the
//!   receipt chain links (`pre == prev.post`). Returns `verified: true` for an honest run.
//! * `GET  /` help; `GET /play` a minimal browser play page.
//!
//! ## The authoring lane — text-authored dungeons on the SAME real executor
//!
//! The `.dungeon` compiler ([`dungeon_on_dregg::dsl`]) is exposed live:
//!
//! * `POST /validate` — body is a `.dungeon` source (raw text, or JSON `{"source": "…"}`).
//!   Parse + validate, PURE (no deploy, no state). Always a structured `200` —
//!   `{ok, issues:[{severity, line?, message}], rooms?, exits?, gates?}` — so a forge UI
//!   can lint live; a parse error is an `ok:false` issue with its source line, never a 500.
//! * `POST /author` — body is a `.dungeon` source (+ optional `seed`). Parse → validate
//!   (blocking errors are a `400` carrying every issue) → [`compile_world`] (an
//!   [`CompileError::Unsupported`] construct or a translation-validation failure is an
//!   honest `422` NAMING the construct/mismatch) → deploy on a fresh real [`WorldCell`] →
//!   register as a new session. Returns the session id + the initial state/moves; the
//!   caller drives it through the SAME `/session/{state,moves,move,verify}` routes by
//!   passing the id (`?session=<id>` on GETs, `"session":"<id>"` in the move body). Every
//!   authored gate is a real `CellProgram` tooth the executor re-checks per turn — same
//!   substrate, same receipts, same replay verification as the keep.
//!
//! ## Honest scope
//!
//! Verification here is **O(N) `verify_by_replay` + chain-linkage** — a stranger re-executes
//! the whole recorded turn sequence. It is NOT the succinct light client (a separate,
//! Lane-D-blocked workstream); this service does not claim it. A production deployment still
//! needs: player authentication + per-identity sessions (this is one in-memory session behind a
//! mutex), durable persistence of the ledger/receipts (state is process memory), and real
//! hosting/TLS (it binds a plain local HTTP/1.1 loop).
//!
//! Start: `cargo run -p real-dungeon-service` (binds `127.0.0.1:7879`; override
//! `REAL_DUNGEON_BIND`). `--self-check` drives a full playthrough in-process and exits.

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use dregg_app_framework::TurnReceipt;
use dungeon_on_dregg::dsl::{
    CompileError, CompiledDungeon, DUNGEON_WON_VAR, Severity, compile_world, parse_world, validate,
};
use dungeon_on_dregg::{
    KP_CAST_WARD, KP_CLAIM_BLUE, KP_CLAIM_RED, KP_DESCEND, KP_PRESS_ON, KP_SEIZE, KP_TRADE_BLOWS,
    case_constraints, choice_at, deploy_keep, keep_compiled, keep_scene,
};
use http_serve::{HttpMethod, ServeRequest, WebResponse, serve_http};
use serde_json::{Value as Json, json};
use spween::{Choice, PassageContent};
use spween_dregg::{
    CompiledStory, Playthrough, Scene, StepReceipt, Value, WorldCell, WorldError, choice_method,
    verify_by_replay,
};

mod run_credit;
use run_credit::{ChargeOutcome, RunCreditRail};

/// The bind address (override with `REAL_DUNGEON_BIND`). Distinct from the LARP
/// `dungeon-service`'s `:7878` so both can run side by side.
const DEFAULT_BIND: &str = "127.0.0.1:7879";

/// The default deploy seed (deterministic cell identity + state hashes; a re-deploy at the
/// same seed reproduces exactly — what the replay verifier leans on).
const DEFAULT_SEED: u8 = 70;

// ─────────────────────────────────────────────────────────────────────────────
// The session — ONE real keep WorldCell + the recorded (verifiable) choice chain.
// ─────────────────────────────────────────────────────────────────────────────

/// A live game session over one real [`WorldCell`]. The `world` is the sole authority (its
/// committed cell state IS the game state); `steps` records each committed move so `/verify`
/// can rebuild a [`Playthrough`] and re-drive it by replay.
struct Session {
    /// The deploy seed (a fresh identically-seeded keep reproduces this session on replay).
    seed: u8,
    /// The real world-cell hosting the keep (the executor + ledger live inside it).
    world: WorldCell,
    /// The keep scene (the choice/passage source the moves + replay speak in).
    scene: Scene,
    /// The compiled + augmented program, for introspecting the executor teeth on each move.
    compiled: CompiledStory,
    /// passage index → room name (read off the committed passage slot).
    names: Vec<String>,
    /// The committed slot vector right after deploy+seed — the replay `genesis_state`.
    genesis_state: Vec<u64>,
    /// The committed move steps, in order (the input to `verify_by_replay`).
    steps: Vec<StepReceipt>,
}

impl Session {
    /// Deploy a fresh keep and seed the fight/budget the intro passage sets at genesis.
    fn new(seed: u8) -> Session {
        let mut world = deploy_keep(seed);
        // The KEEP intro passage's entry effects (`~ hp = 50`, `~ mana_budget = 50`) are what
        // the stock `Driver` commits at genesis. This service drives the executor directly via
        // `apply_choice` (the executor as sole referee, bypassing the client runtime), so it
        // seeds the same slots here — exactly as `examples/universe.rs` does — so a fresh
        // Driver-based replay (which DOES run the intro effects) reproduces the same state.
        world.seed_var("hp", Value::Int(50));
        world.seed_var("mana_budget", Value::Int(50));

        let compiled = keep_compiled();
        let mut names = vec![String::new(); compiled.passage_index.len()];
        for (name, &idx) in &compiled.passage_index {
            if idx < names.len() {
                names[idx] = name.clone();
            }
        }
        let genesis_state = world.snapshot();
        Session {
            seed,
            world,
            scene: keep_scene(),
            compiled,
            names,
            genesis_state,
            steps: Vec::new(),
        }
    }

    /// The player's current room name, or `None` if the scene has ended (won).
    fn current_room(&self) -> Option<&str> {
        self.world
            .read_passage()
            .and_then(|i| self.names.get(i))
            .map(|s| s.as_str())
    }

    /// The choices at `room` (in order), as `(index, &Choice)`.
    fn choices_of<'a>(scene: &'a Scene, room: &str) -> Vec<(usize, &'a Choice)> {
        scene
            .passages
            .iter()
            .find(|p| p.name.as_str() == room)
            .map(|p| {
                p.content
                    .iter()
                    .filter_map(|c| match c {
                        PassageContent::Choice(ch) => Some(ch),
                        _ => None,
                    })
                    .enumerate()
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Has the keep been cleared (a real WIN)? The scene ended AND the hoard was seized.
    fn won(&self) -> bool {
        self.world.read_passage().is_none() && self.world.read_var("gold") == 500
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Authored sessions — text-authored `.dungeon` worlds on the SAME real substrate.
// ─────────────────────────────────────────────────────────────────────────────

/// A live session over an AUTHORED dungeon: the compiled + translation-validated
/// [`CompiledDungeon`] deployed on a real [`WorldCell`], driven and recorded exactly
/// like the keep [`Session`] (same `apply_choice` primitive, same [`StepReceipt`]
/// record, same replay verification).
struct AuthoredSession {
    /// The deploy seed (a fresh identically-seeded deploy reproduces this session).
    seed: u8,
    /// The real world-cell hosting the authored dungeon.
    world: WorldCell,
    /// The compiled artifact: scene + augmented program + room/choice mapping tables.
    dungeon: CompiledDungeon,
    /// passage index → room id.
    names: Vec<String>,
    /// The committed slot vector right after deploy — the replay `genesis_state`.
    /// (A compiled dungeon has no intro entry effects and its start room is passage 0,
    /// so the fresh `Driver` genesis a replay runs reproduces this bare-deploy state —
    /// nothing to seed, unlike the keep.)
    genesis_state: Vec<u64>,
    /// The committed move steps, in order (the input to `verify_by_replay`).
    steps: Vec<StepReceipt>,
}

impl AuthoredSession {
    /// Deploy `dungeon` on a fresh real world-cell at `seed`.
    fn new(dungeon: CompiledDungeon, seed: u8) -> Result<AuthoredSession, WorldError> {
        let world = dungeon.deploy(seed)?;
        let mut names = vec![String::new(); dungeon.rooms.len()];
        for (room, &idx) in &dungeon.rooms {
            if idx < names.len() {
                names[idx] = room.clone();
            }
        }
        let genesis_state = world.snapshot();
        Ok(AuthoredSession {
            seed,
            world,
            dungeon,
            names,
            genesis_state,
            steps: Vec::new(),
        })
    }

    /// The player's current room id, or `None` if the dungeon has ended.
    fn current_room(&self) -> Option<&str> {
        self.world
            .read_passage()
            .and_then(|i| self.names.get(i))
            .map(|s| s.as_str())
    }

    /// Was the objective claimed? (`dungeon_won = 1` is the win choice's committed write.)
    fn won(&self) -> bool {
        self.world.read_var(DUNGEON_WON_VAR) == 1
    }
}

/// The registry of authored sessions, keyed by the id `/author` handed out.
struct AuthoredStore {
    next_id: u64,
    sessions: BTreeMap<String, AuthoredSession>,
}

/// The whole service state: the stock keep session, the authored-session registry, and
/// the protocol-native run-credit rail (the run boundary charges through it).
struct App {
    keep: Mutex<Session>,
    authored: Mutex<AuthoredStore>,
    /// The run-credit rail (`RunSettlementMode`): the protocol-native conserved-transfer
    /// rail, or the free custodial-mock rail (the default). A run start charges through it.
    run_credit: Mutex<RunCreditRail>,
}

impl App {
    /// The default service: the free CUSTODIAL rail (no protocol-native charge), so every
    /// existing route behaves exactly as before. (The live binary always constructs via
    /// [`App::with_rail`] from env; this convenience constructor is used by the tests.)
    #[cfg_attr(not(test), allow(dead_code))]
    fn new(keep_seed: u8) -> App {
        App::with_rail(keep_seed, RunCreditRail::custodial())
    }

    /// The service with an explicit run-credit rail — the protocol-native no-custody loop
    /// selects [`RunCreditRail::protocol_native`] here.
    fn with_rail(keep_seed: u8, rail: RunCreditRail) -> App {
        App {
            keep: Mutex::new(Session::new(keep_seed)),
            authored: Mutex::new(AuthoredStore {
                next_id: 1,
                sessions: BTreeMap::new(),
            }),
            run_credit: Mutex::new(rail),
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// JSON views.
// ─────────────────────────────────────────────────────────────────────────────

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn hex8(h: &[u8; 32]) -> String {
    hex(&h[..8])
}

/// The receipt hashes, verbatim from the wire.
fn receipt_json(r: &TurnReceipt) -> Json {
    json!({
        "turnHash": hex(&r.turn_hash),
        "preStateHash": hex(&r.pre_state_hash),
        "postStateHash": hex(&r.post_state_hash),
    })
}

/// The full game state read off the committed cell.
fn state_json(s: &Session) -> Json {
    let ended = s.world.read_passage().is_none();
    let last: Vec<Json> = s
        .steps
        .iter()
        .rev()
        .take(3)
        .map(|st| {
            json!({
                "room": st.passage,
                "choice": st.choice_index,
                "turnHash": hex(&st.receipt.turn_hash),
            })
        })
        .collect();
    json!({
        "game": "The Warden's Keep",
        "room": s.current_room().unwrap_or("(cleared)"),
        "ended": ended,
        "won": s.won(),
        "vars": {
            "hp": s.world.read_var("hp"),
            "gold": s.world.read_var("gold"),
            "depth": s.world.read_var("depth"),
            "relic_owner": s.world.read_var("relic_owner"),
            "mana_spent": s.world.read_var("mana_spent"),
            "mana_budget": s.world.read_var("mana_budget"),
        },
        "committedMoves": s.steps.len(),
        "cellId": hex8(&s.world.cell_id().0),
        "recentReceipts": last,
    })
}

/// The legal moves at the current room, each with the real executor teeth guarding it.
fn moves_json(s: &Session) -> Json {
    let Some(room) = s.current_room().map(|r| r.to_string()) else {
        return json!({ "room": "(cleared)", "ended": true, "moves": [] });
    };
    let moves: Vec<Json> = Session::choices_of(&s.scene, &room)
        .into_iter()
        .map(|(i, ch)| {
            let teeth: Vec<String> = case_constraints(&s.compiled, &choice_method(&room, i))
                .iter()
                .map(|c| format!("{c:?}"))
                .collect();
            json!({
                "index": i,
                "text": ch.text.as_str(),
                "hasSpweenCondition": ch.condition.is_some(),
                "executorTeeth": teeth,
            })
        })
        .collect();
    json!({ "room": room, "ended": false, "moves": moves })
}

/// A 200 JSON response with an explicit status (the `/author` refusals are honest 4xx).
fn json_status(status: u16, v: Json) -> WebResponse {
    WebResponse {
        status,
        content_type: "application/json".to_string(),
        body: v.to_string().into_bytes(),
    }
}

/// The full game state of an AUTHORED session, read off the committed cell — every
/// compiled var by name (the layout is dungeon-specific, so the view is generic).
fn authored_state_json(id: &str, s: &AuthoredSession) -> Json {
    let ended = s.world.read_passage().is_none();
    let mut vars = serde_json::Map::new();
    for name in s.dungeon.story.var_slots.keys() {
        vars.insert(name.clone(), json!(s.world.read_var(name)));
    }
    let last: Vec<Json> = s
        .steps
        .iter()
        .rev()
        .take(3)
        .map(|st| {
            json!({
                "room": st.passage,
                "choice": st.choice_index,
                "turnHash": hex(&st.receipt.turn_hash),
            })
        })
        .collect();
    json!({
        "session": id,
        "authored": true,
        "room": s.current_room().unwrap_or("(ended)"),
        "ended": ended,
        "won": s.won(),
        "vars": Json::Object(vars),
        "committedMoves": s.steps.len(),
        "cellId": hex8(&s.world.cell_id().0),
        "recentReceipts": last,
    })
}

/// The legal moves at an AUTHORED session's current room, each with the real executor
/// teeth guarding it (same introspection proof the keep view gives).
fn authored_moves_json(id: &str, s: &AuthoredSession) -> Json {
    let Some(room) = s.current_room().map(|r| r.to_string()) else {
        return json!({ "session": id, "room": "(ended)", "ended": true, "moves": [] });
    };
    let moves: Vec<Json> = Session::choices_of(&s.dungeon.scene, &room)
        .into_iter()
        .map(|(i, ch)| {
            let teeth: Vec<String> = s
                .dungeon
                .gate_constraints(&room, i)
                .iter()
                .map(|c| format!("{c:?}"))
                .collect();
            json!({
                "index": i,
                "text": ch.text.as_str(),
                "hasSpweenCondition": ch.condition.is_some(),
                "executorTeeth": teeth,
            })
        })
        .collect();
    json!({ "session": id, "room": room, "ended": false, "moves": moves })
}

// ─────────────────────────────────────────────────────────────────────────────
// Handlers.
// ─────────────────────────────────────────────────────────────────────────────

/// `POST /session/start {"seed":N?}` — the RUN BOUNDARY. Charge one run-credit (the
/// protocol-native conserved transfer), then — only on a successful conserving charge —
/// (re)deploy a fresh keep and return the opening state. Fail-closed: an empty budget
/// refuses the run (nothing moves, no deploy/narration).
fn handle_start(state: &Mutex<Session>, rail: &Mutex<RunCreditRail>, body: &[u8]) -> WebResponse {
    let seed = serde_json::from_slice::<Json>(body)
        .ok()
        .and_then(|v| v.get("seed").and_then(Json::as_u64))
        .map(|n| n as u8)
        .unwrap_or(DEFAULT_SEED);

    // ── RUN BOUNDARY ── charge one run-credit BEFORE the run starts. On the
    // protocol-native rail this is one conserving `Effect::Transfer` the player cell
    // authorizes (per-asset Σδ=0); fail-closed on an empty budget. Lock the rail before
    // the session (a consistent order) so a refused charge never touches the session.
    let mut r = rail.lock().unwrap();
    let total_before = r.total();
    let outcome = r.charge_one_run();
    if let ChargeOutcome::Refused(why) = &outcome {
        // Fail-closed: nothing moved, so the run does NOT start (no deploy, no narration).
        debug_assert_eq!(r.total(), total_before, "a refused run must move nothing");
        return json_status(
            402,
            json!({
                "ok": false,
                "refused": true,
                "settlement": "protocol-native",
                "reason": why.to_string(),
                "moved": "nothing",
                "runBudgetRemaining": r.balance(),
                "note": "fail-closed: the run-credit budget is empty, so the run was NOT started (no deploy, no narration) and the conserved run-credit total is unchanged \u{2014} no custody key, no sweeper.",
            }),
        );
    }
    // Charged (protocol-native) or skipped (free custodial rail): render the receipt,
    // then start the run.
    let charge = charge_json(&outcome, &r);
    let mut s = state.lock().unwrap();
    *s = Session::new(seed);
    WebResponse::json(
        json!({ "ok": true, "seed": seed, "charge": charge, "state": state_json(&s) })
            .to_string()
            .into_bytes(),
    )
}

/// Render the run charge as JSON: the conserving transfer on the protocol-native rail, or
/// the honest "no charge" note on the free custodial rail.
fn charge_json(outcome: &ChargeOutcome, rail: &RunCreditRail) -> Json {
    match outcome {
        ChargeOutcome::Skipped => json!({
            "settlement": "custodial",
            "charged": false,
            "note": "custodial/mock rail \u{2014} no protocol-native run-credit charge (the free demo path).",
        }),
        ChargeOutcome::Charged(receipt) => {
            let (from, to, amount) = receipt
                .transfer()
                .expect("a settled protocol-native run carries exactly one conserving Transfer");
            json!({
                "settlement": "protocol-native",
                "charged": true,
                "debited": receipt.debited,
                "remaining": receipt.remaining,
                "conserved": true,
                "asset": "internal run-credit (rung-2a; no bridged value)",
                "transfer": {
                    "from": hex8(&from.0),
                    "to": hex8(&to.0),
                    "amount": amount,
                },
                "runBudgetTotal": rail.total() as u64,
                "note": "one conserving Effect::Transfer authorized by the player cell (per-asset \u{03a3}\u{03b4}=0) \u{2014} no custody key, no sweeper.",
            })
        }
        // Unreachable: the caller handles `Refused` fail-closed before rendering.
        ChargeOutcome::Refused(_) => json!({ "settlement": "protocol-native", "charged": false }),
    }
}

/// `GET /session/state`.
fn handle_state(state: &Mutex<Session>) -> WebResponse {
    let s = state.lock().unwrap();
    WebResponse::json(state_json(&s).to_string().into_bytes())
}

/// `GET /session/moves`.
fn handle_moves(state: &Mutex<Session>) -> WebResponse {
    let s = state.lock().unwrap();
    WebResponse::json(moves_json(&s).to_string().into_bytes())
}

/// `POST /session/move {"index":N}` — drive one real cap-bounded turn at the executor.
fn handle_move(state: &Mutex<Session>, body: &[u8]) -> WebResponse {
    let parsed: Json = match serde_json::from_slice(body) {
        Ok(v) => v,
        Err(e) => return WebResponse::error(400, format!("bad JSON: {e}")),
    };
    let index = match parsed.get("index").and_then(Json::as_u64) {
        Some(n) => n as usize,
        None => return WebResponse::error(400, "missing integer field `index`"),
    };

    let mut s = state.lock().unwrap();
    let Some(room) = s.current_room().map(|r| r.to_string()) else {
        return WebResponse::json(
            json!({
                "ok": false, "refused": true,
                "reason": "the keep is already cleared \u{2014} the scene has ended",
                "state": state_json(&s),
            })
            .to_string()
            .into_bytes(),
        );
    };

    let choices = Session::choices_of(&s.scene, &room);
    if index >= choices.len() {
        return WebResponse::json(
            json!({
                "ok": false, "refused": true,
                "reason": format!("room `{room}` has no choice {index} (it has {})", choices.len()),
                "state": state_json(&s),
            })
            .to_string()
            .into_bytes(),
        );
    }

    // Look up the exact `Choice` and drive it at the real executor. `apply_choice` is the
    // primitive where the executor is the SOLE referee: an ineligible/forged pick is refused
    // in-band by the installed `CellProgram` gate case, and nothing commits (anti-ghost).
    let choice = choice_at(&s.scene, &room, index);
    match s.world.apply_choice(&room, index, &choice) {
        Ok(receipt) => {
            let step = StepReceipt {
                passage: room.clone(),
                choice_index: index,
                receipt: receipt.clone(),
                state: s.world.snapshot(),
                // Single-player `apply_choice` turn: nothing pinned in DECISION_EXT_KEY
                // (`Some` is only for collective `advance_certified` turns).
                decision_commitment: None,
            };
            s.steps.push(step);
            WebResponse::json(
                json!({
                    "ok": true,
                    "committed": true,
                    "move": { "room": room, "index": index, "text": choice.text.as_str() },
                    "receipt": receipt_json(&receipt),
                    "state": state_json(&s),
                })
                .to_string()
                .into_bytes(),
            )
        }
        Err(WorldError::Refused(why)) => WebResponse::json(
            json!({
                "ok": false,
                "refused": true,
                "reason": why,
                "note": "refused by the real executor (an installed StateConstraint tooth failed on the post-state) \u{2014} nothing committed (anti-ghost)",
                "state": state_json(&s),
            })
            .to_string()
            .into_bytes(),
        ),
        Err(other) => WebResponse::json(
            json!({ "ok": false, "error": other.to_string(), "state": state_json(&s) })
                .to_string()
                .into_bytes(),
        ),
    }
}

/// `GET /session/verify` — re-drive a fresh, identically-seeded keep through the recorded
/// choice sequence (replay) and check the receipt chain links.
fn handle_verify(state: &Mutex<Session>) -> WebResponse {
    let s = state.lock().unwrap();

    // (1) CHAIN LINKAGE over the committed step receipts: each turn is genuine (non-zero,
    //     distinct) and links to its predecessor (`pre == prev.post`). Splicing / dropping /
    //     reordering / tampering breaks a link. (Mirrors `verify_chain_linkage` over the
    //     move steps; the seeded genesis is a setup write, not a turn, so it is not in the
    //     receipt chain — the same pairwise linkage `examples/universe.rs` checks.)
    let (chain_ok, chain_note) = chain_links(&s.steps);

    // (2) REPLAY: re-drive a FRESH, identically-seeded keep through the recorded choices and
    //     confirm every step reproduces the recorded committed state, in passage order. A
    //     forged/ineligible pick is refused by the real executor on replay; an altered record
    //     diverges. The fresh keep's stock `Driver` runs the intro entry-effects as genesis,
    //     so it needs no manual seeding.
    let play = Playthrough {
        genesis: TurnReceipt::default(),
        genesis_state: s.genesis_state.clone(),
        steps: s.steps.clone(),
    };
    let replay = verify_by_replay(deploy_keep(s.seed), &s.scene, &play);
    let (replay_ok, replay_note) = match &replay {
        Ok(()) => (true, "replay reproduced every committed state".to_string()),
        Err(e) => (false, e.to_string()),
    };

    WebResponse::json(
        json!({
            "verified": chain_ok && replay_ok,
            "chainLinks": chain_ok,
            "chainNote": chain_note,
            "replayOk": replay_ok,
            "replayNote": replay_note,
            "committedMoves": s.steps.len(),
            "scope": "O(N) verify_by_replay + chain-linkage (a stranger re-executes the recorded turn sequence). NOT the succinct light client (separate, Lane-D-blocked) \u{2014} not claimed here.",
            "note": "verify_by_replay is the authoritative un-retconnable tooth (it reproduces every committed state). chainLinks holds when the winning moves are contiguous; a refused move interleaved between them advances the AGENT receipt chain (anti-replay) and discontinues the world-move pre/post chain without changing any committed state \u{2014} so demonstrate illegal refusals in a separate probe.",
        })
        .to_string()
        .into_bytes(),
    )
}

/// Chain-linkage check over the committed move steps (non-zero, distinct, `pre == prev.post`).
fn chain_links(steps: &[StepReceipt]) -> (bool, String) {
    let mut seen = std::collections::HashSet::new();
    for (i, st) in steps.iter().enumerate() {
        if st.receipt.turn_hash == [0u8; 32] {
            return (false, format!("step {i} has a zero turn hash"));
        }
        if !seen.insert(st.receipt.turn_hash) {
            return (false, format!("step {i} duplicates an earlier turn hash"));
        }
        if i > 0 && st.receipt.pre_state_hash != steps[i - 1].receipt.post_state_hash {
            return (
                false,
                format!("chain broken at step {i} (pre != prev.post)"),
            );
        }
    }
    (
        true,
        format!(
            "{} move receipts link cleanly (pre == prev.post)",
            steps.len()
        ),
    )
}

// ─────────────────────────────────────────────────────────────────────────────
// The authoring lane — `/validate` (pure) + `/author` (compile → deploy → session).
// ─────────────────────────────────────────────────────────────────────────────

/// Extract the `.dungeon` source (+ optional seed) from a request body: JSON
/// `{"source": "…", "seed": N?}`, a bare JSON string, or the raw text itself.
fn source_of(body: &[u8]) -> Result<(String, Option<u8>), String> {
    if let Ok(v) = serde_json::from_slice::<Json>(body) {
        match v {
            Json::Object(ref obj) => {
                let Some(src) = obj.get("source").and_then(Json::as_str) else {
                    return Err("JSON body needs a string field `source`".to_string());
                };
                let seed = obj.get("seed").and_then(Json::as_u64).map(|n| n as u8);
                return Ok((src.to_string(), seed));
            }
            Json::String(s) => return Ok((s, None)),
            // Any other JSON scalar/array is not a plausible .dungeon source.
            _ => return Err("body must be .dungeon text or JSON {\"source\": …}".to_string()),
        }
    }
    match std::str::from_utf8(body) {
        Ok(src) if !src.trim().is_empty() => Ok((src.to_string(), None)),
        Ok(_) => Err("empty body: send .dungeon text or JSON {\"source\": …}".to_string()),
        Err(_) => Err("body is neither UTF-8 .dungeon text nor JSON".to_string()),
    }
}

/// One validator/parse finding as JSON (`line` only when known — parse errors carry it).
fn issue_json(severity: &str, line: Option<usize>, message: &str) -> Json {
    match line {
        Some(n) if n > 0 => json!({ "severity": severity, "line": n, "message": message }),
        _ => json!({ "severity": severity, "message": message }),
    }
}

/// Parse + validate `src`; returns `(issues, world-counts-if-parsed, has_errors)`.
/// Shared by `/validate` (which always answers 200) and `/author` (which refuses on
/// blocking errors).
fn lint_source(src: &str) -> (Vec<Json>, Option<Json>, bool) {
    match parse_world(src) {
        Err(e) => (
            vec![issue_json("error", Some(e.line), &e.message)],
            None,
            true,
        ),
        Ok(world) => {
            let findings = validate(&world);
            let has_errors = findings.iter().any(|i| i.is_error());
            let issues: Vec<Json> = findings
                .iter()
                .map(|i| {
                    let sev = match i.severity {
                        Severity::Error => "error",
                        Severity::Warning => "warning",
                    };
                    issue_json(sev, None, &i.message)
                })
                .collect();
            let exits: usize = world.rooms.values().map(|r| r.exits.len()).sum();
            let gates: usize = world
                .rooms
                .values()
                .flat_map(|r| r.exits.values())
                .filter(|e| e.gate.is_some())
                .count();
            let counts = json!({
                "rooms": world.rooms.len(),
                "exits": exits,
                "gates": gates,
            });
            (issues, Some(counts), has_errors)
        }
    }
}

/// `POST /validate` — parse + validate a `.dungeon` source, PURE (no deploy, no
/// state). Always a structured 200 (the forge lints live): a parse error is an
/// `ok:false` issue carrying its source line, never a 500.
fn handle_validate(body: &[u8]) -> WebResponse {
    let (src, _) = match source_of(body) {
        Ok(s) => s,
        Err(e) => return WebResponse::error(400, e),
    };
    let (issues, counts, has_errors) = lint_source(&src);
    let mut out = json!({ "ok": !has_errors, "issues": issues });
    if let (Some(counts), Some(obj)) = (counts, out.as_object_mut()) {
        obj.insert("rooms".into(), counts["rooms"].clone());
        obj.insert("exits".into(), counts["exits"].clone());
        obj.insert("gates".into(), counts["gates"].clone());
    }
    WebResponse::json(out.to_string().into_bytes())
}

/// `POST /author` — a `.dungeon` source becomes a LIVE session on the real executor:
/// parse → validate (blocking errors are a 400 carrying every issue) → `compile_world`
/// (an unsupported construct / translation-validation failure is an honest 422 naming
/// it) → deploy on a fresh real `WorldCell` → register. The response carries the
/// session id + the initial state/moves; drive it via `/session/move` with
/// `"session":"<id>"`.
fn handle_author(authored: &Mutex<AuthoredStore>, body: &[u8]) -> WebResponse {
    let (src, seed) = match source_of(body) {
        Ok(s) => s,
        Err(e) => return WebResponse::error(400, e),
    };
    let seed = seed.unwrap_or(DEFAULT_SEED);

    // Parse + validate — reject on hard errors WITH the issues (same shape /validate gives).
    let (issues, counts, has_errors) = lint_source(&src);
    if has_errors {
        return json_status(
            400,
            json!({ "ok": false, "stage": "validate", "issues": issues }),
        );
    }
    // The parse succeeded (a parse failure is `has_errors`), so re-parse is infallible here.
    let world = match parse_world(&src) {
        Ok(w) => w,
        Err(e) => return WebResponse::error(500, format!("re-parse diverged: {e}")),
    };

    // Compile: lowering + staple-closure augmentation + translation validation.
    let dungeon = match compile_world(&world) {
        Ok(d) => d,
        Err(CompileError::Unsupported { construct }) => {
            return json_status(
                422,
                json!({
                    "ok": false, "stage": "compile",
                    "error": "unsupported construct",
                    "construct": construct,
                    "note": "refused BY NAME, never silently dropped — see the compiler's residual list",
                }),
            );
        }
        Err(CompileError::ValidationFailed { mismatch }) => {
            return json_status(
                422,
                json!({
                    "ok": false, "stage": "compile",
                    "error": "translation validation failed",
                    "mismatch": mismatch,
                }),
            );
        }
        Err(CompileError::WorldInvalid { first, errors }) => {
            return json_status(
                400,
                json!({
                    "ok": false, "stage": "compile",
                    "error": format!("world fails validation ({errors} error(s))"),
                    "first": first,
                }),
            );
        }
        Err(CompileError::Scene(e)) => {
            return WebResponse::error(500, format!("scene compile: {e}"));
        }
    };

    // Deploy on a fresh real world-cell and register the session.
    let session = match AuthoredSession::new(dungeon, seed) {
        Ok(s) => s,
        Err(e) => return WebResponse::error(500, format!("deploy failed: {e}")),
    };
    let mut store = authored.lock().unwrap();
    let id = format!("a{}", store.next_id);
    store.next_id += 1;
    let state = authored_state_json(&id, &session);
    let moves = authored_moves_json(&id, &session);
    store.sessions.insert(id.clone(), session);
    let mut out = json!({
        "ok": true,
        "session": id,
        "seed": seed,
        "issues": issues,
        "state": state,
        "moves": moves,
        "drive": "POST /session/move {\"session\":\"<id>\",\"index\":N}; GET /session/{state,moves,verify}?session=<id>",
    });
    if let (Some(counts), Some(obj)) = (counts, out.as_object_mut()) {
        obj.insert("rooms".into(), counts["rooms"].clone());
        obj.insert("exits".into(), counts["exits"].clone());
        obj.insert("gates".into(), counts["gates"].clone());
    }
    WebResponse::json(out.to_string().into_bytes())
}

// ─────────────────────────────────────────────────────────────────────────────
// Authored-session drive handlers — the SAME route surface, selected by session id.
// ─────────────────────────────────────────────────────────────────────────────

/// Run `f` over the authored session `id`, or 404 with the unknown id named.
fn with_authored<F>(authored: &Mutex<AuthoredStore>, id: &str, f: F) -> WebResponse
where
    F: FnOnce(&mut AuthoredSession) -> WebResponse,
{
    let mut store = authored.lock().unwrap();
    match store.sessions.get_mut(id) {
        Some(s) => f(s),
        None => WebResponse::error(404, format!("no authored session `{id}`")),
    }
}

/// `GET /session/state?session=<id>`.
fn handle_authored_state(authored: &Mutex<AuthoredStore>, id: &str) -> WebResponse {
    with_authored(authored, id, |s| {
        WebResponse::json(authored_state_json(id, s).to_string().into_bytes())
    })
}

/// `GET /session/moves?session=<id>`.
fn handle_authored_moves(authored: &Mutex<AuthoredStore>, id: &str) -> WebResponse {
    with_authored(authored, id, |s| {
        WebResponse::json(authored_moves_json(id, s).to_string().into_bytes())
    })
}

/// `POST /session/move {"session":"<id>","index":N}` — one real cap-bounded turn at
/// the executor, on the AUTHORED world (mirrors the keep `handle_move` exactly).
fn handle_authored_move(authored: &Mutex<AuthoredStore>, id: &str, index: usize) -> WebResponse {
    with_authored(authored, id, |s| {
        let Some(room) = s.current_room().map(|r| r.to_string()) else {
            return WebResponse::json(
                json!({
                    "ok": false, "refused": true,
                    "reason": "the dungeon has already ended",
                    "state": authored_state_json(id, s),
                })
                .to_string()
                .into_bytes(),
            );
        };
        let choices = Session::choices_of(&s.dungeon.scene, &room);
        if index >= choices.len() {
            return WebResponse::json(
                json!({
                    "ok": false, "refused": true,
                    "reason": format!("room `{room}` has no choice {index} (it has {})", choices.len()),
                    "state": authored_state_json(id, s),
                })
                .to_string()
                .into_bytes(),
            );
        }
        let Some(choice) = s.dungeon.choice(&room, index) else {
            return WebResponse::error(500, format!("choice ({room}, {index}) has no scene entry"));
        };
        match s.world.apply_choice(&room, index, &choice) {
            Ok(receipt) => {
                let step = StepReceipt {
                    passage: room.clone(),
                    choice_index: index,
                    receipt: receipt.clone(),
                    state: s.world.snapshot(),
                    decision_commitment: None,
                };
                s.steps.push(step);
                WebResponse::json(
                    json!({
                        "ok": true,
                        "committed": true,
                        "move": { "room": room, "index": index, "text": choice.text.as_str() },
                        "receipt": receipt_json(&receipt),
                        "state": authored_state_json(id, s),
                    })
                    .to_string()
                    .into_bytes(),
                )
            }
            Err(WorldError::Refused(why)) => WebResponse::json(
                json!({
                    "ok": false,
                    "refused": true,
                    "reason": why,
                    "note": "refused by the real executor (an installed StateConstraint tooth failed on the post-state) \u{2014} nothing committed (anti-ghost)",
                    "state": authored_state_json(id, s),
                })
                .to_string()
                .into_bytes(),
            ),
            Err(other) => WebResponse::json(
                json!({ "ok": false, "error": other.to_string(), "state": authored_state_json(id, s) })
                    .to_string()
                    .into_bytes(),
            ),
        }
    })
}

/// `GET /session/verify?session=<id>` — the same two teeth as the keep verify:
/// chain-linkage over the committed steps + `verify_by_replay` against a fresh,
/// identically-seeded deploy of the SAME compiled dungeon.
fn handle_authored_verify(authored: &Mutex<AuthoredStore>, id: &str) -> WebResponse {
    with_authored(authored, id, |s| {
        let (chain_ok, chain_note) = chain_links(&s.steps);
        let play = Playthrough {
            genesis: TurnReceipt::default(),
            genesis_state: s.genesis_state.clone(),
            steps: s.steps.clone(),
        };
        let (replay_ok, replay_note) = match s.dungeon.deploy(s.seed) {
            Ok(fresh) => match verify_by_replay(fresh, &s.dungeon.scene, &play) {
                Ok(()) => (true, "replay reproduced every committed state".to_string()),
                Err(e) => (false, e.to_string()),
            },
            Err(e) => (false, format!("fresh deploy for replay failed: {e}")),
        };
        WebResponse::json(
            json!({
                "session": id,
                "verified": chain_ok && replay_ok,
                "chainLinks": chain_ok,
                "chainNote": chain_note,
                "replayOk": replay_ok,
                "replayNote": replay_note,
                "committedMoves": s.steps.len(),
                "scope": "O(N) verify_by_replay + chain-linkage on the authored world (a stranger re-executes the recorded turn sequence). NOT the succinct light client \u{2014} not claimed here.",
            })
            .to_string()
            .into_bytes(),
        )
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// Routing + serving.
// ─────────────────────────────────────────────────────────────────────────────

/// The `session=<id>` query parameter, if present (selects an AUTHORED session on the
/// shared `/session/*` GET routes; absent = the stock keep session, unchanged).
fn session_param(target: &str) -> Option<&str> {
    let query = target.split_once('?')?.1;
    query
        .split('&')
        .find_map(|kv| kv.strip_prefix("session="))
        .filter(|v| !v.is_empty())
}

fn route(app: &App, req: &ServeRequest) -> WebResponse {
    let path = req.target.split('?').next().unwrap_or(&req.target);
    let state = &app.keep;
    let sid = session_param(&req.target).map(|s| s.to_string());
    match (req.method, path) {
        (HttpMethod::Post, "/validate") => handle_validate(&req.body),
        (HttpMethod::Post, "/author") => handle_author(&app.authored, &req.body),
        (HttpMethod::Post, "/session/start") => handle_start(state, &app.run_credit, &req.body),
        (HttpMethod::Get, "/session/state") => match sid {
            Some(id) => handle_authored_state(&app.authored, &id),
            None => handle_state(state),
        },
        (HttpMethod::Get, "/session/moves") => match sid {
            Some(id) => handle_authored_moves(&app.authored, &id),
            None => handle_moves(state),
        },
        (HttpMethod::Post, "/session/move") => {
            // A `"session":"<id>"` field in the move body targets an AUTHORED session;
            // without it the route drives the stock keep session, unchanged.
            let body_session = serde_json::from_slice::<Json>(&req.body)
                .ok()
                .and_then(|v| v.get("session").and_then(Json::as_str).map(String::from));
            match body_session {
                Some(id) => {
                    let index = serde_json::from_slice::<Json>(&req.body)
                        .ok()
                        .and_then(|v| v.get("index").and_then(Json::as_u64));
                    match index {
                        Some(n) => handle_authored_move(&app.authored, &id, n as usize),
                        None => WebResponse::error(400, "missing integer field `index`"),
                    }
                }
                None => handle_move(state, &req.body),
            }
        }
        (HttpMethod::Get, "/session/verify") => match sid {
            Some(id) => handle_authored_verify(&app.authored, &id),
            None => handle_verify(state),
        },
        (HttpMethod::Get, "/") => WebResponse::text(INDEX_HELP),
        (HttpMethod::Get, "/play") => WebResponse {
            status: 200,
            content_type: "text/html; charset=utf-8".to_string(),
            body: PLAY_HTML.as_bytes().to_vec(),
        },
        _ => WebResponse::error(404, "not found"),
    }
}

const INDEX_HELP: &str = "real-dungeon-service \u{2014} the REAL dungeon-on-dregg engine (The Warden's Keep) over HTTP\n\
    a move is one cap-bounded turn at the real executor; an illegal move is a real executor refusal.\n\n\
    POST /session/start {\"seed\":N?}   (re)deploy a fresh keep WorldCell\n\
    GET  /session/state                the executor-committed game state\n\
    GET  /session/moves                the legal moves + the executor teeth guarding each\n\
    POST /session/move  {\"index\":N}    drive one real turn -> a real TurnReceipt (or a real refusal)\n\
    GET  /session/verify               replay + chain-linkage over the recorded receipt chain\n\
    GET  /play                         a minimal browser play page\n\n\
    THE AUTHORING LANE (the .dungeon compiler, live):\n\
    POST /validate                     body = .dungeon text (or {\"source\":...}): parse + validate, pure -> {ok, issues, rooms, exits, gates}\n\
    POST /author                       body = .dungeon text (or {\"source\":..., \"seed\":N}): compile -> deploy on a REAL WorldCell -> a new session id\n\
    then drive it on the SAME routes:  POST /session/move {\"session\":\"<id>\",\"index\":N};\n\
                                       GET /session/{state,moves,verify}?session=<id>\n";

const PLAY_HTML: &str = r#"<!doctype html><meta charset=utf-8><title>The Warden's Keep — real dregg</title>
<style>body{font:15px/1.5 ui-monospace,monospace;max-width:44rem;margin:2rem auto;padding:0 1rem;background:#12100e;color:#e8e0d0}
h1{font-size:1.2rem}button{font:inherit;margin:.15rem;padding:.3rem .6rem;background:#2a2620;color:#e8e0d0;border:1px solid #5a5040;border-radius:4px;cursor:pointer}
button:hover{background:#3a342a}pre{white-space:pre-wrap;background:#1c1a16;padding:.6rem;border-radius:6px}.r{color:#c9a227}.bad{color:#d06a5a}.ok{color:#7ac07a}</style>
<h1>The Warden's Keep <span style=opacity:.6>— the real dungeon-on-dregg engine</span></h1>
<div><button onclick=start()>▶ New session</button><button onclick=verify()>✓ Verify (replay)</button></div>
<div id=moves></div><pre id=log></pre>
<script>
const log=(m)=>{document.getElementById('log').textContent=m};
async function j(u,b){const r=await fetch(u,b?{method:'POST',body:JSON.stringify(b)}:{});return r.json()}
async function refresh(){const s=await j('/session/state');const mv=await j('/session/moves');
 let h='<div>room: <b>'+s.room+'</b> · hp '+s.vars.hp+' · gold '+s.vars.gold+' · depth '+s.vars.depth+(s.won?' · <span class=ok>WON</span>':'')+'</div>';
 (mv.moves||[]).forEach(m=>{h+='<button onclick="mv('+m.index+')">'+m.text+(m.executorTeeth.length?' 🔒':'')+'</button>'});
 document.getElementById('moves').innerHTML=h;return s}
async function start(){await j('/session/start',{});log('new keep deployed');refresh()}
async function mv(i){const r=await j('/session/move',{index:i});
 if(r.ok){log('✔ committed turn '+r.receipt.turnHash.slice(0,16)+'…\npre '+r.receipt.preStateHash.slice(0,16)+'… post '+r.receipt.postStateHash.slice(0,16)+'…')}
 else{log('REFUSED by the executor: '+r.reason)}refresh()}
async function verify(){const v=await j('/session/verify');log((v.verified?'✓ VERIFIED':'✗ FAILED')+' — replay '+v.replayOk+', chain '+v.chainLinks+'\n'+v.scope)}
start();
</script>"#;

fn main() -> std::io::Result<()> {
    if std::env::args().any(|a| a == "--self-check") {
        return self_check();
    }
    if std::env::args().any(|a| a == "--pay-demo") {
        return pay_demo();
    }
    let bind = std::env::var("REAL_DUNGEON_BIND").unwrap_or_else(|_| DEFAULT_BIND.to_string());
    let rail = RunCreditRail::from_env();
    let settlement = if rail.is_protocol_native() {
        format!(
            "protocol-native (conserved run-credit transfer; player budget {}, no custody key, no sweeper)",
            rail.balance()
        )
    } else {
        "custodial/mock (free demo path; no protocol-native charge)".to_string()
    };
    let app = Arc::new(App::with_rail(DEFAULT_SEED, rail));
    eprintln!(
        "real-dungeon-service: hosting the REAL dungeon-on-dregg engine (The Warden's Keep) on \
         http://{bind}  (POST /session/start, GET /session/moves, POST /session/move, GET /session/verify;\n\
         the .dungeon authoring lane: POST /validate, POST /author)\n\
         run settlement: {settlement}"
    );
    let handler = move |req: &ServeRequest| route(&app, req);
    serve_http(&bind, handler)
}

// ─────────────────────────────────────────────────────────────────────────────
// The protocol-native pay demo — pay-credit → run → receipt, all in-process, no custody.
// ─────────────────────────────────────────────────────────────────────────────

/// `--pay-demo` — drive the no-custody run-credit loop through the REAL routes in
/// process: a run START charges one run-credit as a conserving transfer, a MOVE lands a
/// real `TurnReceipt`, and an emptied budget refuses the next run fail-closed. Zero real
/// money, zero custody key.
fn pay_demo() -> std::io::Result<()> {
    println!("== real-dungeon-service :: protocol-native pay demo ==");
    println!(
        "a dungeon RUN charged as a CONSERVED, no-custody run-credit transfer \u{2014} zero real money, zero custody key.\n"
    );
    let mut fails = 0;

    // A protocol-native rail with a 2-credit player budget.
    let app = App::with_rail(DEFAULT_SEED, RunCreditRail::protocol_native(2));
    let total_before = app.run_credit.lock().unwrap().total();

    // ── STEP 1 · pay-credit at the run boundary (a conserving transfer). ──
    println!("── STEP 1 · pay-credit (POST /session/start = the run boundary) ──");
    let start = post_route(&app, "/session/start", json!({ "seed": DEFAULT_SEED }));
    let charge = &start["charge"];
    println!(
        "  settlement={} debited={} remaining={} conserved={}",
        charge["settlement"], charge["debited"], charge["remaining"], charge["conserved"]
    );
    println!(
        "  conserving transfer: from {}\u{2026} -> to {}\u{2026} amount {}",
        charge["transfer"]["from"].as_str().unwrap_or("?"),
        charge["transfer"]["to"].as_str().unwrap_or("?"),
        charge["transfer"]["amount"]
    );
    let total_after = app.run_credit.lock().unwrap().total();
    println!("  run-credit total conserved: {total_before} -> {total_after} (\u{03a3}\u{03b4}=0)");
    if !(start["ok"].as_bool() == Some(true)
        && charge["debited"].as_u64() == Some(1)
        && total_after == total_before)
    {
        fails += 1;
    }

    // ── STEP 2 · run → a real executor turn → a real TurnReceipt. ──
    println!("\n── STEP 2 · run -> receipt (POST /session/move = a real executor turn) ──");
    let mv = post_route(&app, "/session/move", json!({ "index": KP_TRADE_BLOWS }));
    let th = mv["receipt"]["turnHash"].as_str().unwrap_or("");
    println!(
        "  committed turn {}\u{2026} (a real TurnReceipt)",
        &th[..th.len().min(16)]
    );
    if !(mv["ok"].as_bool() == Some(true) && th.len() == 64 && th != "0".repeat(64)) {
        fails += 1;
    }

    // ── STEP 3 · empty the budget → the next run refuses fail-closed. ──
    // Start #2 spends the last credit; start #3 hits an empty budget.
    let _ = post_route(&app, "/session/start", json!({ "seed": DEFAULT_SEED }));
    let refused = post_route(&app, "/session/start", json!({ "seed": DEFAULT_SEED }));
    println!("\n── STEP 3 · empty budget -> fail-closed ──");
    println!(
        "  POST /session/start (budget empty) -> ok={} refused={} moved={}",
        refused["ok"], refused["refused"], refused["moved"]
    );
    let final_total = app.run_credit.lock().unwrap().total();
    println!(
        "  conserved throughout: run-credit total still {final_total} (nothing minted, nothing swept)"
    );
    if !(refused["refused"].as_bool() == Some(true)
        && refused["moved"].as_str() == Some("nothing")
        && final_total == total_before)
    {
        fails += 1;
    }

    // ── The no-custody falsifier: the run path references no custodial types. ──
    let src = include_str!("run_credit.rs");
    let clean = [
        "Sweeper",
        "HdDeposit",
        "SolanaSweeper",
        "SolanaWatcher",
        "Seed",
    ]
    .iter()
    .all(|t| !src.contains(t));
    println!("\n  protocol-native run path free of Seed/Sweeper custody types: {clean}");
    if !clean {
        fails += 1;
    }

    println!();
    if fails == 0 {
        println!(
            "PAY DEMO OK \u{2014} pay-credit (conserving transfer) -> run -> a real receipt, empty budget refused fail-closed, no custody."
        );
        Ok(())
    } else {
        println!("{fails} PAY-DEMO CHECK(S) FAILED");
        std::process::exit(1);
    }
}

/// Drive one POST through the REAL route dispatch and parse the JSON body.
fn post_route(app: &App, target: &str, body: Json) -> Json {
    let req = ServeRequest {
        method: HttpMethod::Post,
        host: String::new(),
        target: target.to_string(),
        body: body.to_string().into_bytes(),
        headers: Vec::new(),
    };
    serde_json::from_slice(&route(app, &req).body).unwrap_or(Json::Null)
}

// ─────────────────────────────────────────────────────────────────────────────
// In-process self-check — drives a full playthrough to a WIN, an illegal refusal, and verify.
// ─────────────────────────────────────────────────────────────────────────────

fn self_check() -> std::io::Result<()> {
    println!("== real-dungeon-service :: self-check ==");
    println!(
        "hosting the REAL dungeon-on-dregg engine (The Warden's Keep) \u{2014} a move is a real executor turn.\n"
    );
    let mut fails = 0;

    // ── PHASE 1 — the winning run (contiguous legal moves) → a real receipt chain → /verify true.
    println!("── PHASE 1 · play The Warden's Keep to a WIN (real executor turns) ──");
    let state = Mutex::new(Session::new(DEFAULT_SEED));
    let plan: &[(usize, &str)] = &[
        (
            KP_TRADE_BLOWS,
            "trade blows with the warden (FieldGte hp floor)",
        ),
        (KP_PRESS_ON, "press on into the hall"),
        (KP_CLAIM_RED, "claim the crown for the Red Hand (WriteOnce)"),
        (
            KP_DESCEND,
            "descend the collapsing stair (Monotonic ratchet)",
        ),
        (KP_CAST_WARD, "cast the sealing ward (FieldLteField budget)"),
        (KP_SEIZE, "seize the hoard"),
    ];
    for (idx, label) in plan {
        let resp = move_via(&state, *idx);
        if resp["ok"].as_bool().unwrap_or(false) {
            let th = resp["receipt"]["turnHash"].as_str().unwrap_or("");
            println!(
                "  [OK ] move {idx} {label} -> committed turn {}…",
                &th[..th.len().min(16)]
            );
        } else {
            println!(
                "  [BAD] move {idx} {label} -> {}",
                resp["reason"].as_str().unwrap_or("?")
            );
            fails += 1;
        }
    }
    let won = state.lock().unwrap().won();
    println!("  WIN state reached: {won}");
    fails += (!won) as i32;

    let v = verify_via(&state);
    println!(
        "  /session/verify -> verified={} (replay={}, chain={})",
        v["verified"], v["replayOk"], v["chainLinks"]
    );
    println!("  chainNote: {}", v["chainNote"].as_str().unwrap_or(""));
    if v["verified"].as_bool() != Some(true) {
        fails += 1;
    }

    // ── PHASE 2 — an ILLEGAL move over the wire is a REAL executor refusal (anti-ghost).
    // A fresh session: walk to the hall, let the Red Hand claim the crown, then attempt the
    // rival Blue-Hand claim on the SAME crown. The executor's WriteOnce tooth refuses it in-band
    // and nothing commits (relic_owner still Red). Kept separate from the verified run because a
    // refused turn advances the AGENT's receipt chain (anti-replay), which would discontinue the
    // world-move pre/post chain — see the /verify note.
    println!("\n── PHASE 2 · an illegal move is a REAL executor refusal (anti-ghost) ──");
    let s2 = Mutex::new(Session::new(DEFAULT_SEED));
    move_via(&s2, KP_PRESS_ON); // gatehall -> hall
    let red = move_via(&s2, KP_CLAIM_RED);
    println!(
        "  Red claims the crown -> ok={}, relic_owner={}",
        red["ok"], red["state"]["vars"]["relic_owner"]
    );
    let blue = move_via(&s2, KP_CLAIM_BLUE);
    let refused = blue["refused"].as_bool().unwrap_or(false);
    let owner_after = blue["state"]["vars"]["relic_owner"].as_u64().unwrap_or(0);
    println!(
        "  Blue claims the SAME crown -> refused={refused}: {}",
        blue["reason"].as_str().unwrap_or("")
    );
    println!("  anti-ghost: relic_owner still {owner_after} (unchanged, Red holds it)");
    if !(refused && owner_after == 1) {
        fails += 1;
    }

    println!();
    if fails == 0 {
        println!(
            "ALL CHECKS PASSED \u{2014} the real keep is deployed, played to a WIN with a real receipt chain, /verify true, and an illegal move refused by the real executor (anti-ghost)."
        );
        Ok(())
    } else {
        println!("{fails} CHECK(S) FAILED");
        std::process::exit(1);
    }
}

fn move_via(state: &Mutex<Session>, index: usize) -> Json {
    let body = json!({ "index": index }).to_string();
    serde_json::from_slice(&handle_move(state, body.as_bytes()).body).unwrap_or(Json::Null)
}
fn verify_via(state: &Mutex<Session>) -> Json {
    serde_json::from_slice(&handle_verify(state).body).unwrap_or(Json::Null)
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests — the authoring lane driven through the REAL route dispatch, both polarities.
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    /// A good hand-authored dungeon (attested-dm's Clockwork Orchard: 5 rooms, 8
    /// exits, exactly 1 item-gated exit).
    const ORCHARD: &str = include_str!("../tests/fixtures/clockwork_orchard.dungeon");
    /// A deliberately broken dungeon (a dangling exit target `antechamer` + an
    /// unplaced win item).
    const BROKEN: &str = include_str!("../tests/fixtures/broken.dungeon");
    /// A good dungeon whose `hostile` the compiler does not lower yet — the named
    /// `Unsupported` refusal.
    const LANTERN_FEN: &str = include_str!("../tests/fixtures/lantern_fen.dungeon");

    /// Drive one request through the REAL route dispatch (method, target, body).
    fn drive(app: &App, method: HttpMethod, target: &str, body: Json) -> (u16, Json) {
        let body = match &body {
            Json::Null => Vec::new(),
            Json::String(s) => s.clone().into_bytes(),
            v => v.to_string().into_bytes(),
        };
        let req = ServeRequest {
            method,
            host: String::new(),
            target: target.to_string(),
            body,
            headers: Vec::new(),
        };
        let resp = route(app, &req);
        let json = serde_json::from_slice(&resp.body).unwrap_or(Json::Null);
        (resp.status, json)
    }

    fn post(app: &App, target: &str, body: Json) -> (u16, Json) {
        drive(app, HttpMethod::Post, target, body)
    }
    fn get(app: &App, target: &str) -> (u16, Json) {
        drive(app, HttpMethod::Get, target, Json::Null)
    }

    // ── /validate — both polarities, pure (no session ever created). ──

    /// A clean fixture validates ok with the exact room/exit/gate counts the compiler
    /// tests hardcode from the source (5 rooms, 8 exits, 1 gated exit).
    #[test]
    fn validate_clean_fixture_is_ok_with_sane_counts() {
        let app = App::new(DEFAULT_SEED);
        let (status, v) = post(&app, "/validate", json!({ "source": ORCHARD }));
        assert_eq!(status, 200);
        assert_eq!(v["ok"], json!(true), "clean source is ok: {v}");
        assert_eq!(v["rooms"], json!(5));
        assert_eq!(v["exits"], json!(8));
        assert_eq!(v["gates"], json!(1));
        assert_eq!(
            v["issues"].as_array().map(Vec::len),
            Some(0),
            "no issues on the orchard: {v}"
        );
        // Raw-text body (no JSON wrapper) is accepted too — the forge can POST the file.
        let (status, v) = post(&app, "/validate", json!(ORCHARD));
        assert_eq!((status, v["ok"].clone()), (200, json!(true)));
    }

    /// A broken fixture is a structured 200-with-issues (the forge lints live) naming
    /// the dangling exit target — NOT a 500, and no session is created.
    #[test]
    fn validate_broken_fixture_names_the_specific_issue() {
        let app = App::new(DEFAULT_SEED);
        let (status, v) = post(&app, "/validate", json!({ "source": BROKEN }));
        assert_eq!(
            status, 200,
            "a broken dungeon is a structured lint, not a 500"
        );
        assert_eq!(v["ok"], json!(false));
        let issues = v["issues"].as_array().expect("issues array");
        assert!(
            issues.iter().any(|i| {
                i["severity"] == json!("error")
                    && i["message"]
                        .as_str()
                        .is_some_and(|m| m.contains("antechamer"))
            }),
            "the dangling exit target is NAMED: {v}"
        );
        assert!(
            app.authored.lock().unwrap().sessions.is_empty(),
            "/validate is pure — no session"
        );
    }

    /// A SYNTACTIC parse error carries its source line in the issue.
    #[test]
    fn validate_parse_error_carries_the_source_line() {
        let app = App::new(DEFAULT_SEED);
        let src = "start: gate\nobjective: reach gate holding gem\n\nroom gate \"The Gate\"\n  items: gem\n  exit north ->\n";
        let (status, v) = post(&app, "/validate", json!({ "source": src }));
        assert_eq!(status, 200);
        assert_eq!(v["ok"], json!(false));
        let issues = v["issues"].as_array().expect("issues array");
        assert!(
            issues
                .iter()
                .any(|i| i["severity"] == json!("error") && i["line"].as_u64().is_some()),
            "a parse error is localized to a line: {v}"
        );
    }

    // ── /author — a text-authored dungeon becomes a REAL executor-refereed session. ──

    /// The full plumbing, driven: /author on a clean fixture returns a session id +
    /// initial state; legal moves via the EXISTING /session/move LAND with real
    /// TurnReceipts to the win; and /session/verify replays the authored session
    /// clean. (The refusal polarity lives in its own session below — a refused turn
    /// advances the agent receipt chain and discontinues the world-move pre/post
    /// chain, same as the keep's /verify note documents.)
    #[test]
    fn author_deploys_a_playable_executor_refereed_session() {
        let app = App::new(DEFAULT_SEED);
        let (status, v) = post(&app, "/author", json!({ "source": ORCHARD, "seed": 7 }));
        assert_eq!(status, 200, "a clean dungeon authors: {v}");
        assert_eq!(v["ok"], json!(true));
        let sid = v["session"].as_str().expect("a session id").to_string();
        assert_eq!(v["state"]["room"], json!("gate"), "opens at the start room");
        assert_eq!(v["rooms"], json!(5));

        // The choice indices, resolved by NAME through the compiled mapping table
        // (never guessed) — the same resolution the compiler's own tests use.
        let world = parse_world(ORCHARD).expect("fixture parses");
        let d = compile_world(&world).expect("fixture compiles");
        let mv = |idx: usize| {
            post(
                &app,
                "/session/move",
                json!({ "session": sid, "index": idx }),
            )
        };

        // A LEGAL move lands a real TurnReceipt through the existing /session/move.
        let (status, r) = mv(d.exit_index("gate", "north").unwrap());
        assert_eq!(status, 200);
        assert_eq!(r["ok"], json!(true), "the legal move commits: {r}");
        let th = r["receipt"]["turnHash"].as_str().expect("a turn hash");
        assert_eq!(th.len(), 64, "a real 32-byte turn hash");
        assert_ne!(th, "0".repeat(64), "a genuine committed turn");
        assert_eq!(r["state"]["room"], json!("rows"));

        // The honest critical path: apple → the Keeper's trade → the gated door →
        // the Heartspring → the sundial claim. Every step a real committed turn.
        let path = [
            d.take_index("rows", "brass_apple").unwrap(),
            d.exit_index("rows", "east").unwrap(),
            d.talk_index("shed", 0).unwrap(), // topic `key`: apple → winding_key
            d.exit_index("shed", "west").unwrap(),
            d.exit_index("rows", "north").unwrap(), // the GATED exit — key now held
            d.take_index("greenhouse", "heartspring").unwrap(),
            d.exit_index("greenhouse", "west").unwrap(),
            d.objective_index("sundial").unwrap(),
        ];
        for (i, idx) in path.iter().enumerate() {
            let (_, r) = mv(*idx);
            assert_eq!(r["ok"], json!(true), "legal step {i} commits: {r}");
        }
        let (_, s) = get(&app, &format!("/session/state?session={sid}"));
        assert_eq!(s["won"], json!(true), "the objective was claimed: {s}");
        assert_eq!(s["ended"], json!(true));
        assert_eq!(s["vars"][DUNGEON_WON_VAR], json!(1));

        // The recorded authored playthrough re-verifies by replay + chain linkage.
        let (status, v) = get(&app, &format!("/session/verify?session={sid}"));
        assert_eq!(status, 200);
        assert_eq!(v["verified"], json!(true), "the authored run verifies: {v}");
        assert_eq!(v["committedMoves"], json!(9));
    }

    /// The authored GATE bites ON THE EXECUTOR: the keyless walk through the gated
    /// exit is a real `WorldError::Refused` committing NOTHING (anti-ghost read-back
    /// over the wire shapes) — in its own session, mirroring the keep's phase split.
    #[test]
    fn authored_gate_refuses_the_keyless_walk_anti_ghost() {
        let app = App::new(DEFAULT_SEED);
        let (_, v) = post(&app, "/author", json!({ "source": ORCHARD, "seed": 9 }));
        let sid = v["session"].as_str().expect("a session id").to_string();
        let world = parse_world(ORCHARD).expect("fixture parses");
        let d = compile_world(&world).expect("fixture compiles");
        let mv = |idx: usize| {
            post(
                &app,
                "/session/move",
                json!({ "session": sid, "index": idx }),
            )
        };

        let (_, r) = mv(d.exit_index("gate", "north").unwrap());
        assert_eq!(r["ok"], json!(true), "walk to the rows: {r}");

        // Keyless, drive the item-gated exit: REFUSED by the installed FieldGte tooth.
        let (status, r) = mv(d.exit_index("rows", "north").unwrap());
        assert_eq!(status, 200);
        assert_eq!(r["ok"], json!(false), "the keyless gated walk refuses: {r}");
        assert_eq!(r["refused"], json!(true));
        assert_eq!(
            r["state"]["room"],
            json!("rows"),
            "anti-ghost: still in the rows"
        );
        assert_eq!(
            r["state"]["vars"]["has_winding_key"],
            json!(0),
            "anti-ghost: no key materialized"
        );
        assert_eq!(
            r["state"]["committedMoves"],
            json!(1),
            "the refused turn committed nothing"
        );

        // The moves view names the executor tooth guarding the gated exit.
        let (_, m) = get(&app, &format!("/session/moves?session={sid}"));
        let gated = d.exit_index("rows", "north").unwrap();
        let teeth = m["moves"][gated]["executorTeeth"]
            .as_array()
            .expect("teeth listed");
        assert!(
            teeth
                .iter()
                .any(|t| t.as_str().is_some_and(|s| s.contains("FieldGte"))),
            "the gate is a real FieldGte tooth: {m}"
        );
    }

    /// An unsupported construct (the Lantern Fen's `hostile`) is the honest NAMED
    /// 4xx — never a silent accept, never a 500 — and no session is registered.
    #[test]
    fn author_refuses_an_unsupported_construct_by_name() {
        let app = App::new(DEFAULT_SEED);
        let (status, v) = post(&app, "/author", json!({ "source": LANTERN_FEN }));
        assert_eq!(status, 422, "an unlowered construct is a 4xx: {v}");
        assert_eq!(v["ok"], json!(false));
        assert_eq!(v["error"], json!("unsupported construct"));
        let construct = v["construct"].as_str().expect("the construct is named");
        assert!(
            construct.contains("hostile") && construct.contains("gargoyle"),
            "named, not generic: {construct}"
        );
        assert!(app.authored.lock().unwrap().sessions.is_empty());
    }

    /// A validator-broken source is rejected with the issues (the same shape /validate
    /// gives), and no session is registered.
    #[test]
    fn author_rejects_a_broken_world_with_the_issues() {
        let app = App::new(DEFAULT_SEED);
        let (status, v) = post(&app, "/author", json!({ "source": BROKEN }));
        assert_eq!(status, 400, "hard validation errors reject: {v}");
        assert_eq!(v["ok"], json!(false));
        assert!(
            v["issues"]
                .as_array()
                .is_some_and(|a| a.iter().any(|i| i["message"]
                    .as_str()
                    .is_some_and(|m| m.contains("antechamer")))),
            "the rejection carries the issues: {v}"
        );
        assert!(app.authored.lock().unwrap().sessions.is_empty());
    }

    /// A move naming an unknown session id is a 404, and the keep is untouched.
    #[test]
    fn unknown_authored_session_is_a_404() {
        let app = App::new(DEFAULT_SEED);
        let (status, v) = post(
            &app,
            "/session/move",
            json!({ "session": "a999", "index": 0 }),
        );
        assert_eq!(status, 404, "{v}");
    }

    /// The EXISTING keep routes are unchanged: a session-less /session/move drives the
    /// keep and lands a real receipt; /session/state answers the keep view.
    #[test]
    fn keep_routes_still_work_without_a_session_id() {
        let app = App::new(DEFAULT_SEED);
        let (status, r) = post(&app, "/session/move", json!({ "index": KP_TRADE_BLOWS }));
        assert_eq!(status, 200);
        assert_eq!(r["ok"], json!(true), "the keep move commits: {r}");
        assert!(r["receipt"]["turnHash"].as_str().is_some());
        let (status, s) = get(&app, "/session/state");
        assert_eq!(status, 200);
        assert_eq!(s["game"], json!("The Warden's Keep"));
        assert_eq!(s["committedMoves"], json!(1));
    }

    // ── The protocol-native run-credit rail, driven through the REAL route dispatch. ──

    fn native_app(budget: u64) -> App {
        App::with_rail(DEFAULT_SEED, RunCreditRail::protocol_native(budget))
    }

    /// A funded run START debits exactly ONE run-credit as a conserving transfer (per-asset
    /// total unchanged, player -1, operator +1) and the run proceeds; a MOVE then lands a
    /// real TurnReceipt — the pay-credit -> run -> receipt loop, no custody.
    #[test]
    fn protocol_native_start_debits_one_conserving_credit_then_runs() {
        let app = native_app(3);
        let total_before = app.run_credit.lock().unwrap().total();

        // Pay-credit: the run boundary charges one conserving transfer.
        let (status, v) = post(&app, "/session/start", json!({ "seed": 70 }));
        assert_eq!(status, 200, "a funded run starts: {v}");
        assert_eq!(v["ok"], json!(true));
        assert_eq!(v["charge"]["settlement"], json!("protocol-native"));
        assert_eq!(v["charge"]["charged"], json!(true));
        assert_eq!(v["charge"]["debited"], json!(1), "exactly one run-credit");
        assert_eq!(v["charge"]["remaining"], json!(2));
        assert_eq!(v["charge"]["conserved"], json!(true));
        assert_eq!(v["charge"]["transfer"]["amount"], json!(1));
        // The run STARTED: the opening keep state is present.
        assert_eq!(v["state"]["game"], json!("The Warden's Keep"));

        // Conserving: per-asset Σδ=0, player debited exactly one, operator credited one.
        {
            let rail = app.run_credit.lock().unwrap();
            assert_eq!(
                rail.total(),
                total_before,
                "per-asset Σδ=0 across the run charge"
            );
            assert_eq!(rail.balance(), 2, "player debited exactly one credit");
            assert_eq!(
                rail.operator_balance(),
                1,
                "operator credited exactly one credit"
            );
        }

        // pay-credit -> run -> receipt: a move now lands a real committed TurnReceipt.
        let (status, r) = post(&app, "/session/move", json!({ "index": KP_TRADE_BLOWS }));
        assert_eq!(status, 200);
        assert_eq!(r["ok"], json!(true), "the run produces a real receipt: {r}");
        let th = r["receipt"]["turnHash"].as_str().expect("a turn hash");
        assert_eq!(th.len(), 64, "a real 32-byte turn hash");
        assert_ne!(th, "0".repeat(64), "a genuine committed turn");
    }

    /// An empty run budget refuses the run fail-closed: nothing moves AND the run does not
    /// start (the session is not redeployed — no narration).
    #[test]
    fn empty_run_budget_refuses_the_run_fail_closed_and_moves_nothing() {
        let app = native_app(0);

        // Mark the lobby session so a redeploy would be observable.
        let _ = post(&app, "/session/move", json!({ "index": KP_TRADE_BLOWS }));
        let (_, before) = get(&app, "/session/state");
        assert_eq!(
            before["committedMoves"],
            json!(1),
            "one move committed on the lobby session"
        );

        let total_before = app.run_credit.lock().unwrap().total();
        assert_eq!(total_before, 0);

        // START with an empty budget: fail-closed 402, nothing moves, the run does NOT start.
        let (status, v) = post(&app, "/session/start", json!({ "seed": 99 }));
        assert_eq!(status, 402, "an empty budget refuses the run: {v}");
        assert_eq!(v["ok"], json!(false));
        assert_eq!(v["refused"], json!(true));
        assert_eq!(v["moved"], json!("nothing"));

        // Nothing moved: the conserved total is unchanged and the player still has 0.
        {
            let rail = app.run_credit.lock().unwrap();
            assert_eq!(rail.total(), total_before, "a refused run moves nothing");
            assert_eq!(rail.balance(), 0);
            assert_eq!(
                rail.operator_balance(),
                0,
                "the operator was credited nothing"
            );
        }

        // The run did NOT start: the session was not redeployed (no narration).
        let (_, after) = get(&app, "/session/state");
        assert_eq!(
            after["committedMoves"],
            json!(1),
            "the run did not start \u{2014} no redeploy/narration on a refused charge"
        );
        assert_eq!(
            after["room"], before["room"],
            "same lobby session, unchanged"
        );
    }

    /// The default (custodial) rail starts a run FREE — additive, the existing behavior.
    #[test]
    fn custodial_default_rail_starts_free_with_no_charge() {
        let app = App::new(DEFAULT_SEED); // custodial default
        let (status, v) = post(&app, "/session/start", json!({ "seed": 70 }));
        assert_eq!(status, 200);
        assert_eq!(v["ok"], json!(true));
        assert_eq!(v["charge"]["settlement"], json!("custodial"));
        assert_eq!(
            v["charge"]["charged"],
            json!(false),
            "the free demo path charges nothing"
        );
        // The run still starts and plays exactly as before.
        assert_eq!(v["state"]["game"], json!("The Warden's Keep"));
    }

    /// The falsifier: the protocol-native run path references NO custodial types
    /// (Seed / Sweeper / HD deposit). Grep the module and find nothing.
    #[test]
    fn protocol_native_run_path_has_no_seed_or_sweeper() {
        let src = include_str!("run_credit.rs");
        for forbidden in [
            "Sweeper",
            "HdDeposit",
            "SolanaSweeper",
            "SolanaWatcher",
            "DREGG_PAY_SEED",
            "Seed",
        ] {
            assert!(
                !src.contains(forbidden),
                "the protocol-native run path must not reference the custodial type `{forbidden}`"
            );
        }
    }
}
