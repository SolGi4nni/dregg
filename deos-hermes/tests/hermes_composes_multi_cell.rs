//! THE USEFUL, BOUNDED MULTI-CELL TASK, PROVEN BY RUNNING — a confined agent's brain
//! decides + drives JavaScript that composes a story spanning MULTIPLE cells as ONE
//! all-or-nothing bounded gesture on a live World, refused in-band on over-reach.
//!
//! Run: `cd deos-hermes && cargo test --features js-agent --test hermes_composes_multi_cell`
//! (the default `cargo test` is mozjs-free — the compose `run_js` path pulls deos-js /
//! real SpiderMonkey via the `js-agent` feature.)
//!
//! ## What gap this closes
//!
//! Today the confined agent can drive, through `run_js`, exactly ONE bounded thing per
//! call: fire a single affordance (a counter bump — `hermes_runs_js`) or edit one card
//! (`hermes_authors_card_via_run_js`). The MULTI-cell path that DID exist
//! (`deos.server.*`: `spawnCell`/`grant`/`setField`) is the UNBOUNDED GM superpower —
//! it acts AS each governed cell with NO `held` cap tooth. And `deos_js::multi_cell`'s
//! bounded composer (cap tooth + scope tooth + atomic pre-screen) ran only on its own
//! private embedded engine, unreachable from the brain.
//!
//! `deos.compose([...])` (this surface) is the missing piece: the brain decides-and-
//! executes a genuinely useful multi-cell task — here "stand up a shared notebook for me
//! and a collaborator" = MINT the notebook cell + SEED its title + GRANT the collaborator
//! a cap — as ONE bounded, receipted gesture on the live World.
//!
//! ## What is proven
//!
//!   (a) THE USEFUL TASK — the agent's `deos.compose` story (mint + seed + grant)
//!       commits THREE verified turns on the live World: real receipts, real cells. A
//!       re-read off the live ledger shows the notebook cell exists with the seeded
//!       title, and the collaborator holds the granted cap.
//!   (b) ACCOUNTABLE — the `run_js` tool-call ITSELF is admitted by the proven
//!       `HermesGateway` (the metered, receipted accountability turn); refused ⇒ no JS.
//!   (c) BOUNDED (THE EDGE) — an over-reaching story is refused IN-BAND with NOTHING
//!       committed (no partial leg): (i) a grant WIDER than the agent's `held`, and
//!       (ii) a `setField` on a FOREIGN cell outside the agent's scope. Each aborts the
//!       whole story at the atomic pre-screen — the live ledger is untouched.

#![cfg(feature = "js-agent")]

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::{Arc, RwLock};

use deos_hermes::acp_client::AcpClient;
use deos_hermes::{
    GrantRegistry, HermesGateway, LiveComposeHands, MockHermesPeer, RunJsComposeTool, ScriptedCall,
    ToolCallRequest,
};
use deos_js::{JsRuntime, WorldSink};
use dregg_cell::{AuthRequired, Cell, CellId, Permissions};
use dregg_sdk::embed::{DreggEngine, EngineConfig};
use dregg_sdk::{AgentCipherclerk, AgentRuntime, HeldToken};
use dregg_turn::action::Effect;
use dregg_turn::builder::{ActionBuilder, TurnBuilder};

// ───────────────────────── a self-contained live World ──────────────────────
//
// A `WorldSink` over an embedded `DreggEngine` (the SAME verified executor `Applet` and
// `multi_cell::MultiCellAuthor` drive). It commits each leg as a real verified turn and
// implements `mint_open_cell` exactly like the node's `NodeWorldSink` (an open, funded
// cell + the agent's c-list standing), so the agent's `mintCard` legs stand up real cells
// the composer can then write + grant over. This is the live ledger the receipts land on.

struct EmbeddedWorld {
    engine: DreggEngine,
    prev: Option<[u8; 32]>,
}

impl EmbeddedWorld {
    fn new() -> Self {
        let mut engine = DreggEngine::new(EngineConfig::for_testing());
        engine
            .executor()
            .set_witness_mode(dregg_turn::collapse::WitnessMode::Symbolic);
        EmbeddedWorld { engine, prev: None }
    }

    /// Seed an OPEN, funded cell with the agent's c-list standing over `scope` cells (the
    /// genesis standing a cross-cell write needs — mirrors `MultiCellAuthor::mint`).
    fn seed_agent(&mut self, pk: [u8; 32], tok: [u8; 32], scope: &[([u8; 32], [u8; 32])]) -> CellId {
        let agent = CellId::derive_raw(&pk, &tok);
        let mut agent_cell = Cell::with_balance(pk, tok, 1_000_000);
        agent_cell.permissions = open_permissions();
        for (spk, stok) in scope {
            let id = CellId::derive_raw(spk, stok);
            let mut card = Cell::with_balance(*spk, *stok, 100_000);
            card.permissions = open_permissions();
            let _ = self.engine.ledger_mut().insert_cell(card);
            agent_cell.capabilities.grant(id, AuthRequired::None);
        }
        self.engine
            .ledger_mut()
            .insert_cell(agent_cell)
            .expect("seed the agent cell");
        agent
    }

    /// Seed a FOREIGN cell (default perms, NO agent standing) — exists so a grant has a
    /// real recipient and a foreign-cell over-reach has a real target.
    fn seed_foreign(&mut self, pk: [u8; 32], tok: [u8; 32]) -> CellId {
        let id = CellId::derive_raw(&pk, &tok);
        let _ = self.engine.ledger_mut().insert_cell(Cell::with_balance(pk, tok, 0));
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

    /// Whether `holder` holds a c-list capability whose target is `on` (the grant landed).
    fn holds_cap_to(&self, holder: &CellId, on: &CellId) -> bool {
        self.engine
            .ledger()
            .get(holder)
            .map(|c| c.capabilities.iter().any(|cap| &cap.target == on))
            .unwrap_or(false)
    }
}

/// A `WorldSink` over a shared `Rc<RefCell<EmbeddedWorld>>` — the live ledger the agent's
/// compose legs commit onto.
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
        let nonce = w.engine.ledger().get(&agent).map(|c| c.state.nonce()).unwrap_or(0);
        // Build the action carrying the leg's effects, bump the actor's nonce so each leg
        // chains, and commit the verified turn (the SAME shape `multi_cell::commit_step` uses).
        let mut action = ActionBuilder::new_unchecked_for_tests(agent, method, agent);
        for e in effects {
            action = action.effect(e);
        }
        let action = action.effect_increment_nonce(agent).build();
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

    /// Mint an OPEN, funded cell + give the agent c-list standing — mirrors the node's
    /// `NodeWorldSink::mint_open_cell` (so a later in-story `setField`/`grant` on it
    /// authorizes). The minting agent is the world's sole agent in this harness.
    fn mint_open_cell(&mut self, seed: &str, funding: u64) -> Result<CellId, String> {
        let public_key = *blake3::hash(seed.as_bytes()).as_bytes();
        let token_id = *blake3::hash(b"default").as_bytes();
        let mut w = self.world.borrow_mut();
        let mut cell = Cell::with_balance(public_key, token_id, funding as i64);
        cell.permissions = open_permissions();
        let id = cell.id();
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

// ───────────────────────────── the grantor + grant ──────────────────────────

/// deos the grantor: the runtime that admits the agent's `run_js` worker and runs its
/// accountability turns.
fn grantor() -> (AgentRuntime, HeldToken) {
    let mut cclerk = AgentCipherclerk::new();
    let root = cclerk.mint_token(&[7u8; 32], "deos");
    let rt = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
    (rt, root)
}

/// A scoped, rate-limited `run_js` grant for the agent (the accountability mandate the
/// gateway meters the tool-call on).
fn session_registry() -> GrantRegistry {
    GrantRegistry::default_for_session(10_000).with_tool_grant("run_js", 50, 10_000)
}

fn pk(b: u8) -> [u8; 32] {
    let mut k = [0u8; 32];
    k[0] = b;
    k
}
fn tok(b: u8) -> [u8; 32] {
    let mut t = [0u8; 32];
    t[0] = b;
    t
}

/// The model slot a notebook's title hash lands in (the brain's seeded field).
const TITLE_SLOT: usize = 0;

// ── (a) THE USEFUL TASK + (b) ACCOUNTABLE + (c) BOUNDED, on ONE shared engine ─
//
// SpiderMonkey's `JSEngine::init()` is PROCESS-GLOBAL and one-shot, so every scenario
// shares ONE `JsRuntime`. Each `eval` runs on a fresh global, so reuse is sound.

#[test]
fn agent_composes_a_useful_bounded_multi_cell_story_on_the_live_world() {
    let (rt, root) = grantor();
    let mut gw = HermesGateway::new(&rt, root, session_registry());

    // The live World + the agent cell. The agent holds the broad-but-not-root `Either`
    // (admits Signature/Proof grants below), seeded with a fee balance + open perms.
    let world = Rc::new(RefCell::new(EmbeddedWorld::new()));
    let collaborator = world.borrow_mut().seed_foreign(pk(9), tok(9));
    let agent = world.borrow_mut().seed_agent(pk(1), tok(1), &[]);
    let held = AuthRequired::Either;

    // The agent's compose tool over the live World (mounted under `held`, the agent's own
    // cell is its starting scope — the notebook it MINTS joins the scope mid-story).
    let tool = RunJsComposeTool::new(held.clone(), agent, vec![]);

    // ONE process-global SpiderMonkey engine, shared across every scenario.
    let mut js = JsRuntime::new().expect("boot SpiderMonkey once");

    // The deterministic id the `mintCard { seed: "notebook" }` leg will stand up — the
    // collaborator is granted a cap OVER this notebook.
    let notebook = {
        let pk_nb = *blake3::hash(b"notebook").as_bytes();
        let tok_nb = *blake3::hash(b"default").as_bytes();
        CellId::derive_raw(&pk_nb, &tok_nb)
    };
    let collab_hex = hex::encode(collaborator.as_bytes());

    // ── (a) THE USEFUL TASK — the agent's chosen compose JS: stand up a shared notebook.
    //   leg 1: MINT the notebook cell (seeded title hash 0xBEEF in slot 0).
    //   leg 2: SET a second field on the just-minted notebook (in scope after the mint).
    //   leg 3: GRANT the collaborator a Signature cap OVER the notebook (the outward reach).
    // Returns a witness int: committed*100 + (ok?1:0)*10 + (minted==1?1:0).
    let useful = format!(
        r#"
        var out = deos.compose([
            {{ op: "mintCard", seed: "notebook",
               fields: [[{title}, 48879]], required: "signature" }},
            {{ op: "setField", cell: "{nb}", slot: 1, value: 7, required: "signature" }},
            {{ op: "grant", from: "{nb}", to: "{collab}",
               granted: "signature", required: "signature" }}
        ]);
        (out.committed * 100) + (out.ok ? 10 : 0) + (out.minted.length === 1 ? 1 : 0);
        "#,
        title = TITLE_SLOT,
        nb = hex::encode(notebook.as_bytes()),
        collab = collab_hex,
    );

    let sink = Box::new(EmbeddedSink { world: world.clone() });
    let call = ToolCallRequest::new(
        "s",
        "tc-compose-1",
        "run_js",
        serde_json::json!({ "script": "compose: shared notebook" }),
    );
    let o = tool.run_attached_on(&mut js, sink, &mut gw, &call, 50, &useful);

    // The `run_js` tool-call itself was admitted accountably (a metered, receipted turn).
    assert!(
        o.tool_admitted(),
        "the run_js tool-call is admitted by the gateway (the accountability turn): {:?}",
        o.tool_outcome
    );
    assert_eq!(
        gw.calls_made_for_tool("run_js"),
        1,
        "the run_js call is metered — every agent action is receipted, never free"
    );
    assert!(o.js_error.is_none(), "the compose JS ran cleanly: {:?}", o.js_error);

    // THE USEFUL TASK COMMITTED: three legs ⇒ three verified turns on the live World.
    assert!(o.composed(), "the bounded story committed (no over-reach)");
    assert_eq!(o.committed(), 3, "three legs = three verified turns on the live ledger");
    let compose = o.compose.as_ref().expect("a compose outcome");
    assert_eq!(compose.receipts.len(), 3, "three real receipts on the live ledger");
    assert_eq!(compose.minted, vec![notebook], "the notebook cell was minted + reported");
    // The witness int confirms the JS saw committed=3, ok=true, minted.length=1.
    assert_eq!(o.result, Some(311), "JS observed committed=3, ok, one minted cell");

    // A RE-READ OFF THE LIVE LEDGER proves the world actually changed:
    let w = world.borrow();
    //   * the notebook cell exists with the seeded title (0xBEEF) + the leg-2 field (7).
    assert_eq!(w.field_u64(&notebook, TITLE_SLOT), 0xBEEF, "the notebook's title was seeded");
    assert_eq!(w.field_u64(&notebook, 1), 7, "the leg-2 write landed on the notebook");
    //   * the collaborator now HOLDS a cap over the notebook (the grant landed).
    assert!(
        w.holds_cap_to(&collaborator, &notebook),
        "the collaborator holds the granted cap over the notebook — the shared notebook is real"
    );
    drop(w);

    // ── (c) BOUNDED — an over-reaching grant (WIDER than held) is refused in-band. ───────
    // The agent re-attaches (a fresh composer over the same live World) and composes a
    // story whose grant hands over `proof` while the agent only... wait: held is Either,
    // which admits both. To make the grant genuinely over-reach, use a NARROW agent.
    let narrow_world = Rc::new(RefCell::new(EmbeddedWorld::new()));
    let narrow_collab = narrow_world.borrow_mut().seed_foreign(pk(9), tok(9));
    let narrow_agent = narrow_world.borrow_mut().seed_agent(pk(2), tok(2), &[]);
    // The agent holds ONLY Signature — it cannot grant the wider `Either`.
    let narrow_tool = RunJsComposeTool::new(AuthRequired::Signature, narrow_agent, vec![]);

    let over_grant = format!(
        r#"
        var out = deos.compose([
            {{ op: "setField", cell: "{agent}", slot: 0, value: 1, required: "signature" }},
            {{ op: "grant", from: "{agent}", to: "{collab}",
               granted: "either", required: "signature" }}
        ]);
        (out.committed * 10) + (out.ok ? 1 : 0);
        "#,
        agent = hex::encode(narrow_agent.as_bytes()),
        collab = hex::encode(narrow_collab.as_bytes()),
    );
    let sink2 = Box::new(EmbeddedSink { world: narrow_world.clone() });
    let call2 = ToolCallRequest::new(
        "s",
        "tc-compose-2",
        "run_js",
        serde_json::json!({ "script": "compose: over-grant" }),
    );
    let o2 = narrow_tool.run_attached_on(&mut js, sink2, &mut gw, &call2, 51, &over_grant);

    assert!(o2.tool_admitted(), "run_js is still granted (the bound is on the compose)");
    assert!(!o2.composed(), "the over-reaching grant story did NOT commit");
    assert_eq!(o2.committed(), 0, "OVER-REACH — nothing committed (no partial leg)");
    assert!(
        o2.refusal().is_some_and(|r| r.contains("over-reach")),
        "the over-reach is named in-band: {:?}",
        o2.refusal()
    );
    // THE ATOMIC FACE: even the AUTHORIZED leg-1 (setField on the agent's own cell) did
    // NOT land — the whole story aborted at the pre-screen before any turn committed.
    assert_eq!(
        narrow_world.borrow().field_u64(&narrow_agent, 0),
        0,
        "the authorized leg-1 write never happened — the story is all-or-nothing"
    );
    assert_eq!(o2.result, Some(0), "JS observed committed=0, not ok");

    // ── (c) BOUNDED — a setField on a FOREIGN cell (outside scope) is refused in-band. ───
    let foreign_world = Rc::new(RefCell::new(EmbeddedWorld::new()));
    let foreign_cell = foreign_world.borrow_mut().seed_foreign(pk(9), tok(9));
    let scoped_agent = foreign_world.borrow_mut().seed_agent(pk(3), tok(3), &[]);
    let scoped_tool = RunJsComposeTool::new(AuthRequired::Either, scoped_agent, vec![]);

    let foreign_touch = format!(
        r#"
        var out = deos.compose([
            {{ op: "setField", cell: "{agent}", slot: 0, value: 5, required: "signature" }},
            {{ op: "setField", cell: "{foreign}", slot: 0, value: 9, required: "signature" }}
        ]);
        out.committed;
        "#,
        agent = hex::encode(scoped_agent.as_bytes()),
        foreign = hex::encode(foreign_cell.as_bytes()),
    );
    let sink3 = Box::new(EmbeddedSink { world: foreign_world.clone() });
    let call3 = ToolCallRequest::new(
        "s",
        "tc-compose-3",
        "run_js",
        serde_json::json!({ "script": "compose: foreign touch" }),
    );
    let o3 = scoped_tool.run_attached_on(&mut js, sink3, &mut gw, &call3, 52, &foreign_touch);

    assert!(!o3.composed(), "the foreign-cell story did NOT commit");
    assert_eq!(o3.committed(), 0, "SCOPE OVER-REACH — nothing committed (no partial leg)");
    assert!(
        o3.refusal().is_some_and(|r| r.contains("scope") || r.contains("over-reach")),
        "the scope over-reach is named in-band: {:?}",
        o3.refusal()
    );
    assert_eq!(
        foreign_world.borrow().field_u64(&scoped_agent, 0),
        0,
        "the authorized leg-1 write never happened — the foreign touch aborted the story"
    );
    assert_eq!(o3.result, Some(0), "JS observed committed=0");

    // ── (b) THE LIVE-DECIDE PATH — the compose JS arrives as a run_js call over ACP. ─────
    // The MockHermesPeer is the faithful scripted-brain stand-in: it emits a `run_js`
    // tool-call whose `rawInput.script` IS the agent's decided `deos.compose([...])` story,
    // exactly as the real `acp_adapter` would frame the model's chosen script. The real
    // AcpClient drives the session and dispatches the call to LiveComposeHands, which runs
    // the bounded compose against the live World. This exercises the full run_js → hook →
    // run_compose → deos.compose path end-to-end over the ACP wire. Runs LAST because it
    // consumes the shared `js` runtime.
    {
        let live_world = Rc::new(RefCell::new(EmbeddedWorld::new()));
        let live_collab = live_world.borrow_mut().seed_foreign(pk(9), tok(9));
        let live_agent = live_world.borrow_mut().seed_agent(pk(4), tok(4), &[]);

        let (rt_s, root_s) = grantor();
        let session_gw = HermesGateway::new(&rt_s, root_s, session_registry());
        // The hook owns its OWN gateway over the same grantor (a self-borrow would block
        // borrowing the client's gateway); both share the grantor's ledger.
        let (rt_h, root_h) = grantor();
        let hook_gw = HermesGateway::new(&rt_h, root_h, session_registry());

        let tool = RunJsComposeTool::new(AuthRequired::Either, live_agent, vec![]);
        // The sink factory hands a fresh sink over the SAME live World each call.
        let world_for_factory = live_world.clone();
        let sink_factory = move || -> Box<dyn WorldSink> {
            Box::new(EmbeddedSink {
                world: world_for_factory.clone(),
            })
        };

        // SpiderMonkey is already booted (one-shot, process-global); thread the test's
        // runtime in via `with_runtime` rather than booting another.
        let hands = LiveComposeHands::with_runtime(tool, hook_gw, sink_factory, js);

        // The deterministic notebook id the brain's compose will stand up.
        let live_notebook = deos_js::mint_id_of("live-notebook");
        let brain_compose = format!(
            r#"
            var out = deos.compose([
                {{ op: "mintCard", seed: "live-notebook",
                   fields: [[0, 4660]], required: "signature" }},
                {{ op: "grant", from: "{nb}", to: "{collab}",
                   granted: "signature", required: "signature" }}
            ]);
            out.committed;
            "#,
            nb = deos_js::id_hex(&live_notebook),
            collab = deos_js::id_hex(&live_collab),
        );

        // The brain's `run_js` call: the body is the decided compose JS.
        let peer = MockHermesPeer::new(
            "sess-compose",
            vec![ScriptedCall::new(
                "run_js",
                serde_json::json!({ "script": brain_compose }),
            )],
        );

        let mut client = AcpClient::new(peer, session_gw, 10).with_run_js_hook(hands.into_hook());
        let run = client
            .run_prompt("/tmp", "Stand up a shared notebook and grant my collaborator a cap on it.")
            .expect("the ACP session drives the run_js compose call");

        // The gateway admitted the `run_js` tool-call (the accountability turn).
        assert_eq!(run.verdicts.len(), 1, "one run_js permission round-trip");
        assert!(
            run.verdicts[0].1.allowed(),
            "deos admitted the run_js compose call over ACP: {:?}",
            run.verdicts[0].1
        );

        // The brain's JS composed the multi-cell story: the hook's record carries the
        // receipts the bounded story landed (recorded as `fires_committed`).
        let js_runs = client.js_runs();
        assert_eq!(js_runs.len(), 1, "one run_js compose run recorded");
        let rec = &js_runs[0];
        assert!(
            rec.js_error.is_none(),
            "the live-decided compose JS ran cleanly over ACP: {:?}",
            rec.js_error
        );
        assert_eq!(
            rec.fires_committed, 2,
            "the live-decided run_js composed TWO verified turns (mint + grant) on the live World"
        );
        assert!(
            rec.receipts.len() == 2 && rec.receipts.iter().all(|h| h != &[0u8; 32]),
            "each composed leg left a real receipt over ACP: {:?}",
            rec.receipts
        );
        assert_eq!(rec.result, Some(2), "the brain's compose observed committed=2");
        // The exact JS the brain decided is captured on the record (the auditable body).
        assert!(
            rec.script.contains("deos.compose"),
            "the recorded brain script is the compose JS it decided"
        );

        // A RE-READ OFF THE LIVE LEDGER: the notebook exists (seeded title 0x1234) and the
        // collaborator holds the granted cap — the shared notebook is real, over the wire.
        let w = live_world.borrow();
        assert_eq!(w.field_u64(&live_notebook, 0), 0x1234, "the live notebook was seeded over ACP");
        assert!(
            w.holds_cap_to(&live_collab, &live_notebook),
            "the collaborator holds the cap over the notebook — composed end-to-end over ACP"
        );
    }
}
