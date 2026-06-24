//! THE DEOS-HOST — the dregg node hosts a headless userspace deos-js "private server".
//!
//! THE ARCHITECTURE (the keystone this module proves): a private server is a userspace
//! JS program hosted INSIDE a dregg node — it holds state (real cells on the node's
//! ledger) and offers cap-gated affordances players connect to and fire. The cockpit is
//! then just ONE client of this; the node is a headless deos-js-server-host.
//!
//! deos-js links SpiderMonkey (`mozjs`), single-threaded + process-global one-shot engine
//! init (and the engine must NEVER be dropped — a re-init on a later thread is rejected
//! `AlreadyShutDown`). So the host is a SINGLE long-lived thread that owns ONE
//! [`JsRuntime`] for the process lifetime and runs every hosted program on it (jobs over a
//! channel). This makes hosting REPEATABLE — a setup program, then reactive ticks — the
//! faithful "the GM is a live server" model. Each program binds a fresh [`NodeWorldSink`]
//! — a [`deos_js::WorldSink`] over the node's `NodeState` — so its affordances commit REAL
//! verified turns on the node's ledger (through [`crate::executor_setup::commit_effects_as`],
//! the same producer-gated commit core the signed-turn HTTP ingress runs).
//!
//! THE BOOT (`host_server_program`): mint the server cell (open-perms) onto the ledger,
//! dispatch the program to the persistent host thread, which attaches it as the server
//! agent and runs it (registering cells + affordances + forked instances via
//! `deos.server.*`), then DRAIN the registered surface and publish it into
//! `NodeState::deos_server_surfaces` — the root surface keyed by the server cell, each
//! forked instance keyed by its own cell — where the discovery route reads it. The
//! committed world cells live on the ledger; a client fires an affordance through the
//! node's `/turns/submit` ingress (a real turn).

use std::sync::OnceLock;
use std::sync::mpsc;
use std::thread;

use dregg_cell::{AuthRequired, Cell, CellId, Permissions};
use dregg_turn::action::Effect;

use deos_js::{AttachedApplet, JsRuntime, WorldSink};

use crate::state::NodeState;

/// One program to run on the persistent SpiderMonkey host thread: the bound World (a node
/// `NodeState` + the tokio handle), the server cell to attach AS, its held authority, the
/// program text, and a reply channel for the drained affordance surface (or the error).
struct HostJob {
    state: NodeState,
    handle: tokio::runtime::Handle,
    server_cell: CellId,
    held: AuthRequired,
    program_js: String,
    reply: mpsc::Sender<Result<HostedSurface, String>>,
}

/// What a hosted program's setup produced: the registered cap-gated affordances (each
/// possibly scoped to a forked instance) plus the forked instances it stood up. The host
/// publishes the root surface (instance-less affordances) keyed by the server cell, and
/// each fork keyed by its instance cell carrying exactly the affordances scoped to it.
struct HostedSurface {
    affordances: Vec<deos_js::js::ServerAffordanceDef>,
    forks: Vec<deos_js::js::ServerFork>,
}

/// THE PERSISTENT DEOS-HOST THREAD. SpiderMonkey's engine init is process-global +
/// one-shot, and shutting the engine down (dropping the `JSEngine`) forbids re-init on a
/// later thread (`AlreadyShutDown`). So the host is a SINGLE long-lived thread that owns
/// ONE `JsRuntime` for the process lifetime and runs every hosted program on it — the
/// faithful "the GM is a live server" model: one boot, many program runs (a setup, then
/// reactive ticks). Jobs arrive over this channel.
static HOST_THREAD: OnceLock<mpsc::Sender<HostJob>> = OnceLock::new();

/// Lazily start (once) the persistent host thread and return its job sender.
fn host_thread() -> &'static mpsc::Sender<HostJob> {
    HOST_THREAD.get_or_init(|| {
        let (tx, rx) = mpsc::channel::<HostJob>();
        thread::Builder::new()
            .name("deos-host".into())
            .spawn(move || {
                // ONE runtime for the process lifetime (never dropped → engine stays up).
                let mut rt = match JsRuntime::new() {
                    Ok(rt) => rt,
                    Err(e) => {
                        // Drain jobs reporting the init failure so callers don't hang.
                        while let Ok(job) = rx.recv() {
                            let _ = job.reply.send(Err(format!("JsRuntime::new: {e}")));
                        }
                        return;
                    }
                };
                while let Ok(job) = rx.recv() {
                    let result = run_program(
                        &mut rt,
                        job.state,
                        job.handle,
                        job.server_cell,
                        job.held,
                        &job.program_js,
                    );
                    let _ = job.reply.send(result);
                }
            })
            .expect("spawn persistent deos-host thread");
        tx
    })
}

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

    /// Mint an OPEN, funded world cell directly onto the node's ledger — the GM
    /// superpower of standing up a world vessel (a room, a character, an NPC). This is
    /// the SAME open-perms direct mint the node does at genesis and the deos-host spike's
    /// harness does for the door: the host operator's privilege over its own ledger, the
    /// concrete meaning of "the GM holds broad caps over its world". The cell is derived
    /// from `seed` (hashed to the pubkey against the node's token domain), funded so it
    /// can pay its own self-stamp turns, and opened so the GM's stamps + a player's
    /// cap-bounded writes authorize without a signature. Idempotent on an existing id.
    fn mint_open_cell(&mut self, seed: &str, funding: u64) -> Result<CellId, String> {
        let public_key = *blake3::hash(seed.as_bytes()).as_bytes();
        let token_id = default_token_id();
        let mut s = self.handle.block_on(self.state.write());
        let mut cell = Cell::with_balance(public_key, token_id, funding as i64);
        cell.permissions = open_permissions();
        let id = cell.id();
        if s.ledger.get(&id).is_none() {
            s.ledger
                .insert_cell(cell)
                .map_err(|e| format!("mint_open_cell insert: {e}"))?;
        }
        Ok(id)
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
        // Funded so the server program's own setup turns (GM superpowers: spawnCell /
        // grant) cover their computron fees — the GM holds resources in its world.
        let mut cell = Cell::with_balance(public_key, token_id, 1_000_000);
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

    // (2) Run the program on the PERSISTENT SpiderMonkey host thread (engine init is
    //     process-global + one-shot, and the engine must never be dropped, so a single
    //     long-lived thread owns one JsRuntime and runs every program on it). The thread
    //     binds a fresh NodeWorldSink over this `state`, attaches, evals, drains the
    //     registry, and replies. Hosting is thus repeatable: a setup, then reactive ticks.
    let handle = tokio::runtime::Handle::current();
    let (reply_tx, reply_rx) = mpsc::channel::<Result<HostedSurface, String>>();
    host_thread()
        .send(HostJob {
            state: state.clone(),
            handle,
            server_cell,
            held: held.clone(),
            program_js,
            reply: reply_tx,
        })
        .map_err(|_| "deos-host thread vanished".to_string())?;

    let surface = reply_rx
        .recv()
        .map_err(|_| "deos-host thread vanished".to_string())??;

    // (3) Publish the discoverable surfaces. The ROOT surface (instance-less affordances)
    //     keyed by the server cell; each FORKED INSTANCE keyed by its own cell, carrying
    //     exactly the affordances scoped to it (a cap-bounded per-party/session surface a
    //     client connects to + fires into, isolated from the root + sibling instances).
    {
        let mut s = state.write().await;

        let root_specs: Vec<(String, AuthRequired)> = surface
            .affordances
            .iter()
            .filter(|d| d.instance.is_none())
            .map(|d| (d.name.clone(), d.required.clone()))
            .collect();
        s.deos_server_surfaces.insert(server_cell, root_specs);

        for fork in &surface.forks {
            let fork_specs: Vec<(String, AuthRequired)> = surface
                .affordances
                .iter()
                .filter(|d| d.instance == Some(fork.cell))
                .map(|d| (d.name.clone(), d.required.clone()))
                .collect();
            s.deos_server_surfaces.insert(fork.cell, fork_specs);
        }
    }

    Ok(server_cell)
}

/// Run ONE hosted program on the persistent runtime `rt`: attach to the node World as the
/// server agent (mounting the registered affordances with their real effects), eval the
/// program, and return the registered server-affordance defs. The runtime is reused across
/// programs (the engine is never re-initialized), so each run resets the server registry
/// and installs a fresh global.
fn run_program(
    rt: &mut JsRuntime,
    state: NodeState,
    handle: tokio::runtime::Handle,
    server_cell: CellId,
    held: AuthRequired,
    program_js: &str,
) -> Result<HostedSurface, String> {
    deos_js::js::reset_server_registry();

    // Attach the runtime to the node World as the server agent, mounted under `held`.
    // The server program's GM superpowers (spawnCell/grant/fork) commit through this sink;
    // defineAffordance accumulates into the thread-local server registry.
    let sink = NodeWorldSink::new(state, handle);
    let applet = AttachedApplet::attach_with(Box::new(sink), server_cell, held, Vec::new(), 0);
    deos_js::js::set_current_target(deos_js::JsTarget::Attached(applet));

    let eval = rt.eval(program_js);
    // Take the target back (drop it) regardless; we only need the registry.
    let _ = deos_js::js::take_current_target();
    eval?;

    Ok(HostedSurface {
        affordances: deos_js::js::take_server_registry(),
        forks: deos_js::js::take_fork_registry(),
    })
}
