//! THE DEOS-HOST — the dregg node hosts a headless userspace deos-js "private server".
//!
//! THE ARCHITECTURE (the keystone this module proves): a private server is a userspace
//! JS program hosted INSIDE a dregg node — it holds state (real cells on the node's
//! ledger) and offers cap-gated affordances players connect to and fire. The cockpit is
//! then just ONE client of this; the node is a headless deos-js-server-host.
//!
//! deos-js links SpiderMonkey (`mozjs`), single-threaded + process-global one-shot
//! engine init, so the host runs on a DEDICATED std thread that owns the [`JsRuntime`].
//! It attaches the runtime to a [`NodeWorldSink`] — a [`deos_js::WorldSink`] over the
//! node's `NodeState` — so the program's affordances commit REAL verified turns on the
//! node's ledger (through the factored [`crate::executor_setup::commit_effects_as`], the
//! same producer-gated commit core the signed-turn HTTP ingress runs).
//!
//! THE BOOT (`run_program_setup`): mint the server cell (open-perms) onto the ledger,
//! boot the runtime, attach it as the server agent, run the program (which registers its
//! cells + affordances via `deos.server.*`), then DRAIN the registered affordance
//! surface and publish it into `NodeState::deos_server_surfaces` keyed by the server
//! cell — where the discovery route reads it. The runtime/thread can then be dropped;
//! the published surface + the committed door cells live on the ledger, and a client
//! fires an affordance through the node's `/turns/submit` ingress (a real turn).

use std::sync::mpsc;
use std::thread;

use dregg_cell::{AuthRequired, Cell, CellId, Permissions};
use dregg_turn::action::Effect;

use deos_js::{AttachedApplet, JsRuntime, WorldSink};

use crate::state::NodeState;

/// A fully-open permission set so the verified executor authorizes effects the server
/// program fires (SetField / CreateCell / GrantCapability) without a separate grant —
/// the GM holds broad authority over its own world.
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

/// The default token domain (matches the node's agent domain, `blake3("default")`).
fn default_token_id() -> [u8; 32] {
    *blake3::hash(b"default").as_bytes()
}

/// A [`deos_js::WorldSink`] over the node's [`NodeState`]. The crawl reads the node's
/// live ledger; a fire commits through the factored producer-gated commit core
/// ([`crate::executor_setup::commit_effects_as`]) — the SAME path the signed-turn HTTP
/// ingress runs, minus the wire shell.
///
/// The sink owns a tokio runtime [`Handle`](tokio::runtime::Handle): it runs on a
/// dedicated NON-worker thread (the SpiderMonkey thread), so `block_on` over the node's
/// async `RwLock` is sound (it is not nested inside a worker future).
pub struct NodeWorldSink {
    state: NodeState,
    handle: tokio::runtime::Handle,
}

impl NodeWorldSink {
    pub fn new(state: NodeState, handle: tokio::runtime::Handle) -> Self {
        NodeWorldSink { state, handle }
    }
}

impl WorldSink for NodeWorldSink {
    fn with_ledger(&self, f: &mut dyn FnMut(&dregg_cell::Ledger)) {
        let s = self.handle.block_on(self.state.read());
        f(&s.ledger);
    }

    fn fire_effects(
        &mut self,
        agent: CellId,
        method: &str,
        effects: Vec<Effect>,
    ) -> Result<[u8; 32], String> {
        let mut s = self.handle.block_on(self.state.write());
        crate::executor_setup::commit_effects_as(&mut s, agent, method, effects)
    }
}

/// THE DEOS-HOST BOOT: mint the server cell onto the node ledger, run the program's
/// setup on a dedicated SpiderMonkey thread bound to a [`NodeWorldSink`], then publish
/// the registered affordance surface into `NodeState` for client discovery.
///
/// Returns the minted server cell id (the discovery key) on success. The program text is
/// `program_js`; it should register its surface via `deos.server.defineAffordance(...)`
/// and may use `deos.server.spawnCell` / `deos.server.grant` (GM superpowers — real
/// verified turns committed through the sink during setup).
///
/// `seed_label` derives the server cell's deterministic key. `held` is the authority the
/// server program is mounted under (the GM's broad cap; `None` = the open top).
pub async fn host_server_program(
    state: &NodeState,
    seed_label: &str,
    held: AuthRequired,
    program_js: String,
) -> Result<CellId, String> {
    // (1) Mint the server cell (open-perms, balance 0) onto the node's ledger — the
    //     server's sovereign vessel. Deterministic id from the seed label.
    let public_key = *blake3::hash(seed_label.as_bytes()).as_bytes();
    let token_id = default_token_id();
    let server_cell = {
        let mut s = state.write().await;
        let mut cell = Cell::with_balance(public_key, token_id, 0);
        cell.permissions = open_permissions();
        let id = cell.id();
        // Idempotent: if already present (re-boot), keep it.
        if s.ledger.get(&id).is_none() {
            s.ledger
                .insert_cell(cell)
                .map_err(|e| format!("insert server cell: {e}"))?;
        }
        id
    };

    // (2) Run the program on a dedicated SpiderMonkey thread (engine init is
    //     process-global + one-shot; SpiderMonkey is single-threaded). The thread owns
    //     the JsRuntime + the NodeWorldSink, attaches, evals, and drains the registry.
    let handle = tokio::runtime::Handle::current();
    let sink_state = state.clone();
    let (tx, rx) = mpsc::channel::<Result<Vec<deos_js::js::ServerAffordanceDef>, String>>();
    let held_for_thread = held.clone();

    thread::Builder::new()
        .name("deos-host".into())
        .spawn(move || {
            let result = run_on_thread(
                sink_state,
                handle,
                server_cell,
                held_for_thread,
                &program_js,
            );
            let _ = tx.send(result);
        })
        .map_err(|e| format!("spawn deos-host thread: {e}"))?;

    let defs = rx
        .recv()
        .map_err(|_| "deos-host thread vanished".to_string())??;

    // (3) Publish the registered affordance surface for client discovery.
    {
        let mut s = state.write().await;
        let specs: Vec<(String, AuthRequired)> = defs
            .iter()
            .map(|d| (d.name.clone(), d.required.clone()))
            .collect();
        s.deos_server_surfaces.insert(server_cell, specs);
    }

    Ok(server_cell)
}

/// The dedicated-thread body: boot the runtime, attach to the node World as the server
/// agent (mounting the registered affordances with their real effects), eval the
/// program, and return the registered server-affordance defs.
fn run_on_thread(
    state: NodeState,
    handle: tokio::runtime::Handle,
    server_cell: CellId,
    held: AuthRequired,
    program_js: &str,
) -> Result<Vec<deos_js::js::ServerAffordanceDef>, String> {
    let mut rt = JsRuntime::new()?;
    deos_js::js::reset_server_registry();

    // Attach the runtime to the node World as the server agent, mounted under `held`.
    // The server program's GM superpowers (spawnCell/grant) commit through this sink;
    // defineAffordance accumulates into the thread-local server registry.
    let sink = NodeWorldSink::new(state, handle);
    let applet = AttachedApplet::attach_with(
        Box::new(sink),
        server_cell,
        held,
        Vec::new(),
        0,
    );
    deos_js::js::set_current_target(deos_js::JsTarget::Attached(applet));

    let eval = rt.eval(program_js);
    // Take the target back (drop it) regardless; we only need the registry.
    let _ = deos_js::js::take_current_target();
    eval?;

    Ok(deos_js::js::take_server_registry())
}
