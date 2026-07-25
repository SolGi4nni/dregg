//! RED-TEAM (F1, HIGH / CRITICAL on an open cockpit) — a model's `run_js` ATTACHED to a
//! live World cannot reach the `deos.server.*` GM superpowers.
//!
//! This is the TRUE exploit surface the DEOS capability audit named: the model's hands on
//! the real glass. A confined agent drives a live World through
//! [`RunJsTool::run_attached_on`]; the audit found the `deos.server.*` GM natives
//! (`spawnCell`/`fork` mint OPEN funded cells, `setField` writes any OPEN cell, `grant`
//! hands out caps — all with NO `held` cap tooth) were installed into the SAME global the
//! model's script evaluates in, so a script emitting `deos.server.spawnCell(...)` minted
//! unlimited funded cells / wrote / granted on the live ledger as ONE metered turn, wholly
//! outside its mandate. The existing red-team suite missed it
//! (`red_team_authority_amplification` attacks the SDK ToolGateway;
//! `red_team_sandbox_escape` attacks OS confinement) — NEITHER tested run_js → deos.server.
//!
//! The fix routes every model path through [`deos_js::JsRuntime::eval`] (the CONFINED
//! surface — no `deos.server.*`, no `__deos_server_*` natives); the GM surface installs
//! ONLY in the operator's `eval_trusted` (deos-host). This test proves it AT the live
//! attach path: the model's script (a) cannot even SEE the GM surface, and (b) THROWS if
//! it tries to call it — committing nothing — while (c) the legit `app.fire` path still
//! lands a real verified turn on the SAME live World (so the block is confinement, not a
//! dead sink).
//!
//! Run: `cd deos-hermes && cargo test --features js-agent --test red_team_run_js_server_surface`

#![cfg(feature = "js-agent")]

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::{Arc, RwLock};

use deos_hermes::run_js::RunJsTool;
use deos_hermes::{GrantRegistry, HermesGateway, ToolCallRequest};
use deos_js::{JsRuntime, WorldSink};
use dregg_cell::{AuthRequired, Cell, CellId, Permissions};
use dregg_sdk::embed::{DreggEngine, EngineConfig};
use dregg_sdk::{AgentCipherclerk, AgentRuntime, HeldToken};
use dregg_turn::action::Effect;
use dregg_turn::builder::{ActionBuilder, TurnBuilder};

// ───────────────────────── a self-contained live World ──────────────────────
// A `WorldSink` over an embedded `DreggEngine` (the SAME verified executor a real cockpit
// World drives). It commits each fire as a real verified turn — the live ledger the
// receipts land on, re-read to prove the counter genuinely climbed. It ALSO implements
// `mint_open_cell` (the GM mint the exploit would abuse) so the block below is proven to
// be the CONFINEMENT, not a sink that couldn't have minted anyway.

struct EmbeddedWorld {
    engine: DreggEngine,
    prev: Option<[u8; 32]>,
}

impl EmbeddedWorld {
    fn new() -> Self {
        let engine = DreggEngine::new(EngineConfig::for_testing());
        engine
            .executor()
            .set_witness_mode(dregg_turn::collapse::WitnessMode::Symbolic);
        EmbeddedWorld { engine, prev: None }
    }

    fn seed_agent(&mut self, pk: [u8; 32], tok: [u8; 32]) -> CellId {
        let mut agent_cell = Cell::with_balance(pk, tok, 1_000_000);
        agent_cell.permissions = open_permissions();
        let id = agent_cell.id();
        self.engine
            .ledger_mut()
            .insert_cell(agent_cell)
            .expect("seed the agent cell");
        id
    }

    fn field_u64(&self, cell: &CellId, slot: usize) -> u64 {
        self.engine
            .ledger()
            .get(cell)
            .and_then(|c| c.state.get_field(slot))
            .map(|fe| {
                let mut b = [0u8; 8];
                b.copy_from_slice(&fe[..8]);
                u64::from_le_bytes(b)
            })
            .unwrap_or(0)
    }

    fn cell_count(&self) -> usize {
        self.engine.ledger().len()
    }
}

struct EmbeddedSink {
    world: Rc<RefCell<EmbeddedWorld>>,
}

impl WorldSink for EmbeddedSink {
    fn with_ledger(&self, f: &mut dyn FnMut(&dregg_cell::Ledger)) {
        f(self.world.borrow().engine.ledger());
    }

    fn fire_effects(
        &mut self,
        agent: CellId,
        method: &str,
        effects: Vec<Effect>,
    ) -> Result<[u8; 32], String> {
        let mut w = self.world.borrow_mut();
        let nonce = w
            .engine
            .ledger()
            .get(&agent)
            .map(|c| c.state.nonce())
            .unwrap_or(0);
        let mut action = ActionBuilder::new_unchecked_for_tests(agent, method, agent);
        for e in effects {
            action = action.effect(e);
        }
        let action = action.build();
        let mut tb = TurnBuilder::new(agent, nonce);
        tb.set_fee(10_000);
        if let Some(prev) = w.prev {
            tb.set_previous_receipt_hash(prev);
        }
        tb.add_action(action);
        let turn = tb.build();
        let receipt = w.engine.execute_turn(&turn).map_err(|e| e.to_string())?;
        let rh = receipt.receipt_hash();
        w.prev = Some(rh);
        Ok(rh)
    }

    // The GM mint the exploit would abuse — a REAL open, funded cell on the live ledger.
    // Present so the confinement (not a missing capability) is what blocks Scripts A/B.
    fn mint_open_cell(&mut self, seed: &str, funding: u64) -> Result<CellId, String> {
        let pk = *blake3::hash(seed.as_bytes()).as_bytes();
        let tok = *blake3::hash(b"default").as_bytes();
        let mut cell = Cell::with_balance(pk, tok, funding as i64);
        cell.permissions = open_permissions();
        let id = cell.id();
        let mut w = self.world.borrow_mut();
        if w.engine.ledger().get(&id).is_none() {
            w.engine
                .ledger_mut()
                .insert_cell(cell)
                .map_err(|e| format!("mint_open_cell insert: {e}"))?;
        }
        Ok(id)
    }
}

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

fn grantor() -> (AgentRuntime, HeldToken) {
    let mut cclerk = AgentCipherclerk::new();
    let root = cclerk.mint_token(&[7u8; 32], "deos");
    let rt = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    (rt, root)
}

/// A `run_js` grant with ample rate head-room (the binding here is confinement, not rate).
fn session_registry() -> GrantRegistry {
    GrantRegistry::default_for_session(10_000).with_tool_grant("run_js", 50, 10_000)
}

fn agent_tool(pk: [u8; 32], tok: [u8; 32]) -> RunJsTool {
    RunJsTool::new(
        AuthRequired::Signature,
        pk,
        tok,
        vec![(0, deos_js::applet::pack_u64(0))],
        vec![("inc".to_string(), AuthRequired::Signature)],
    )
}

fn run(
    tool: &RunJsTool,
    js: &mut JsRuntime,
    world: &Rc<RefCell<EmbeddedWorld>>,
    agent: CellId,
    gw: &mut HermesGateway<'_>,
    id: &str,
    script: &str,
) -> deos_hermes::run_js::RunJsOutcome {
    let sink = Box::new(EmbeddedSink {
        world: world.clone(),
    });
    let call = ToolCallRequest::new(
        "sess",
        id,
        "run_js",
        serde_json::json!({ "script": script }),
    );
    tool.run_attached_on(js, sink, agent, gw, &call, 50, script)
        .expect("run_js boots")
}

#[test]
fn a_model_run_js_attached_to_a_live_world_cannot_reach_deos_server() {
    let mut js = JsRuntime::new().expect("boot SpiderMonkey once");
    let (runtime, root) = grantor();
    let mut gw = HermesGateway::new(&runtime, root, session_registry());

    let world = Rc::new(RefCell::new(EmbeddedWorld::new()));
    let agent = world.borrow_mut().seed_agent([0x42; 32], [0x01; 32]);
    let tool = agent_tool([0x42; 32], [0x01; 32]);

    let cells_before = world.borrow().cell_count();

    // ── (A) PROBE — the model script (attached to the LIVE World) cannot even SEE the
    //    GM surface: `deos.server` undefined, the raw `__deos_server_*` natives absent. ─
    let probe = r#"
        var app = deos.applet({ affordances: ["inc"] });
        var blocked = 1;
        if (typeof deos.server !== "undefined") blocked = 0;
        if (typeof __deos_server_spawn_cell !== "undefined") blocked = 0;
        if (typeof __deos_server_grant !== "undefined") blocked = 0;
        if (typeof __deos_server_set_field !== "undefined") blocked = 0;
        blocked;
    "#;
    let a = run(&tool, &mut js, &world, agent, &mut gw, "tc-probe", probe);
    assert!(
        a.js_error.is_none(),
        "the probe ran cleanly: {:?}",
        a.js_error
    );
    assert_eq!(
        a.result,
        Some(1),
        "F1 HOLE — a live-attached model script can SEE the deos.server GM surface"
    );
    assert_eq!(a.fires_committed, 0, "the probe committed no turn");

    // ── (B) EXPLOIT — the model tries the audit's attack: mint an OPEN funded cell via
    //    the GM path. `deos.server` is undefined → the script THROWS before any fire,
    //    committing NOTHING and minting NO cell on the live ledger. ────────────────────
    let exploit = r#"
        var app = deos.applet({ affordances: ["inc"] });
        deos.server.spawnCell("deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef", "open");
        app.inc(1);
        99;
    "#;
    let b = run(
        &tool,
        &mut js,
        &world,
        agent,
        &mut gw,
        "tc-exploit",
        exploit,
    );
    assert!(
        b.js_error.is_some(),
        "F1 HOLE — the GM-mint exploit did NOT throw (deos.server was reachable)"
    );
    assert_eq!(
        b.fires_committed, 0,
        "F1 HOLE — the exploit committed a turn on the live World"
    );
    assert_eq!(
        world.borrow().field_u64(&agent, 0),
        0,
        "the live World counter is untouched by the thrown exploit"
    );
    assert_eq!(
        world.borrow().cell_count(),
        cells_before,
        "F1 HOLE — the exploit minted a cell on the live ledger"
    );

    // ── (C) LEGIT — the SAME live World + sink still commits a real verified turn via the
    //    bounded `app.fire` path (the counter climbs to 1): the block above is the
    //    confinement, not a dead sink. ─────────────────────────────────────────────────
    let legit = r#"
        var app = deos.applet({ affordances: ["inc"] });
        app.inc(1);
    "#;
    let c = run(&tool, &mut js, &world, agent, &mut gw, "tc-legit", legit);
    assert!(
        c.js_error.is_none(),
        "the legit fire ran cleanly: {:?}",
        c.js_error
    );
    assert_eq!(
        c.fires_committed, 1,
        "the legit app.fire path commits one verified turn on the live World"
    );
    assert_eq!(
        world.borrow().field_u64(&agent, 0),
        1,
        "the live World counter climbed to 1 — the bounded surface still works"
    );
}
