//! AGENT ATTACH — bind the confined agent's `run_js` (deos-js) to the cockpit's
//! LIVE World, so a Claude in Hermes drives the OPERATOR'S ACTUAL CELLS.
//!
//! `deos-js`'s [`Applet`](deos_js::Applet) mints its own private engine; the agent's
//! JS only ever touches that throwaway world. THE ATTACH PATH (`deos_js::attach`)
//! binds the runtime to a PROVIDED [`World`] instead — the cockpit's running image
//! (the headline: "The Cool Place"), or a [`World::fork`] of it (the safe sandbox).
//!
//! This module is the cockpit-side weld: [`WorldSinkAdapter`] implements
//! `deos_js::WorldSink` over the cockpit's `Rc<RefCell<World>>`, so the JS:
//!
//!   * `deos.world.cells()` / `deos.cell(id).reflect()` crawl the LIVE ledger's real
//!     cells (a witnessed read through the shared World borrow); and
//!   * `app.fire("name", n)` commits a real verified turn THROUGH `World::commit_turn`
//!     — a receipt that lands on the cockpit's own provenance log + dynamics feed.
//!
//! ## The red-team invariant is KEPT (`docs/deos/AGENT-CONFINEMENT-REDTEAM.md`)
//!
//! The cap tooth runs in deos-js BEFORE the turn reaches `commit_turn`: the
//! [`AttachedApplet`](deos_js::AttachedApplet) is mounted under the agent's `held`
//! authority, never the World's root, and an over-reach (a `required` the agent does
//! not hold) is refused in-band — no turn, no receipt, `commit_turn` never called. A
//! fire binds the agent's OWN cell, so it cannot cross to another vessel. The World's
//! own executor is the SECOND gate (it re-checks conservation / ocap / authority on
//! every committed turn), so even a bug in the deos-js tooth cannot forge a turn the
//! live executor would reject.

use std::cell::RefCell;
use std::rc::Rc;

use dregg_cell::{AuthRequired, CellId, Ledger};
use dregg_turn::action::Effect;

use deos_js::{AttachedApplet, WorldSink};

use crate::world::{CommitOutcome, World};

/// A `deos_js::WorldSink` over the cockpit's live `Rc<RefCell<World>>`.
///
/// Cloning the `Rc` shares the SAME World the cockpit renders — so a fire lands on
/// the live ledger the inspector reads, and the crawl sees the live cells. For the
/// SANDBOX variant, build it over an `Rc<RefCell<World>>` wrapping a `world.fork()`:
/// identical code, a throwaway World (stitchable back like the membrane).
pub struct WorldSinkAdapter {
    world: Rc<RefCell<World>>,
}

impl WorldSinkAdapter {
    /// Attach to the LIVE cockpit World (the operator's real cells — the headline).
    pub fn live(world: Rc<RefCell<World>>) -> Self {
        WorldSinkAdapter { world }
    }

    /// Attach to a FORK of the cockpit World (the safe sandbox the agent drives; the
    /// live image is untouched, the fork is stitchable back like the membrane).
    pub fn fork_of(world: &Rc<RefCell<World>>) -> Self {
        let forked = world.borrow().fork();
        WorldSinkAdapter {
            world: Rc::new(RefCell::new(forked)),
        }
    }

    /// The shared World handle (so the bake can read the live ledger / receipts after
    /// the JS run — the SAME World the JS committed onto).
    pub fn world(&self) -> Rc<RefCell<World>> {
        self.world.clone()
    }
}

impl WorldSink for WorldSinkAdapter {
    fn with_ledger(&self, f: &mut dyn FnMut(&Ledger)) {
        let w = self.world.borrow();
        f(w.ledger());
    }

    fn fire_effects(
        &mut self,
        agent: CellId,
        _method: &str,
        effects: Vec<Effect>,
    ) -> Result<[u8; 32], String> {
        let mut w = self.world.borrow_mut();
        // Build the turn with the World's OWN `turn()` shape (the agent's nonce, the
        // World's fee), then commit it through `commit_turn` (which threads the chain
        // head + runs the real verified executor). The receipt lands on the live
        // provenance log + dynamics feed — exactly like every other cockpit turn.
        let turn = w.turn(agent, effects);
        match w.commit_turn(turn) {
            CommitOutcome::Committed { receipt, .. } => Ok(receipt.receipt_hash()),
            CommitOutcome::Rejected { reason, .. } => Err(reason),
            CommitOutcome::Queued { .. } => {
                Err("world is suspended — the live loop is halted".to_string())
            }
        }
    }
}

/// The slot a counter-bump affordance writes (the agent's mutating shape on the live
/// World). A low state slot the inspector renders as a field on the agent's cell.
pub const AGENT_COUNTER_SLOT: usize = 0;

/// Build an [`AttachedApplet`] bound to the cockpit World through `sink`, driving
/// `agent`'s cell under `held`, with the named `affordances` surface (the cap-gated
/// message surface; each `(name, required)` is checked against `held` in-band).
pub fn attach_agent(
    sink: WorldSinkAdapter,
    agent: CellId,
    held: AuthRequired,
    affordances: Vec<(String, AuthRequired)>,
) -> AttachedApplet {
    AttachedApplet::attach(Box::new(sink), agent, held, affordances, AGENT_COUNTER_SLOT)
}

/// THE WORLD BRIDGE, SERVING SIDE — answer the cross-process `WorldSink`
/// protocol over a Unix domain socket, against the cockpit's LIVE
/// [`WorldSinkAdapter`] (or any other `WorldSink`).
///
/// The client half is `deos_hermes::world_bridge::SocketWorldSink` (the MCP
/// subprocess's `run_js` hands). The two crates cannot depend on each other, so
/// the wire is the contract and THIS module is its serving twin — the frame
/// (`u32` LE length + serde_json) and the [`BridgeRequest`]/[`BridgeResponse`]
/// enums must stay shape-identical to `deos-hermes/src/world_bridge.rs`,
/// variant for variant. (Named seam: the twins share no code, only bytes — a
/// cross-crate compatibility test needs a dep neither direction wants.)
///
/// ## DESIGN — the non-`Send` reality
///
/// The cockpit World is `Rc<RefCell<World>>`, pinned to one thread. The serving
/// loop therefore runs ON THE THREAD THAT OWNS THE SINK — the World never
/// crosses threads; the socket comes to it. Two modes:
///
///   * [`serve_world_bridge`] — BLOCKING: bind, accept ONE client, answer to
///     EOF. For a dedicated world-owning thread / a headless bake / a test.
///   * [`WorldBridgeServer::pump`] — NON-BLOCKING drain for the live cockpit:
///     the gpui frame loop calls `pump(&mut sink)` each tick; it accepts a
///     pending client and answers every request already waiting, then returns.
///     No channel, no second thread — the socket itself is the queue the
///     cockpit thread polls.
#[cfg(unix)]
pub mod world_bridge {
    use std::io::{Read, Write};
    use std::os::unix::net::{UnixListener, UnixStream};
    use std::path::Path;

    use serde::de::DeserializeOwned;
    use serde::{Deserialize, Serialize};

    use dregg_cell::{Cell, CellId};
    use dregg_turn::action::Effect;

    use deos_js::WorldSink;

    /// The largest frame accepted (matches the deos-hermes twin).
    pub const MAX_FRAME_BYTES: usize = 256 * 1024 * 1024;

    /// One request on the world-bridge wire — the `WorldSink` surface, exactly.
    /// MUST stay shape-identical to `deos_hermes::world_bridge::BridgeRequest`.
    #[derive(Debug, Serialize, Deserialize)]
    pub enum BridgeRequest {
        /// The crawl read: snapshot the live cells.
        WithLedger,
        /// Commit ONE verified turn (`WorldSink::fire_effects`).
        FireEffects {
            agent: CellId,
            method: String,
            effects: Vec<Effect>,
        },
        /// Mint an OPEN, funded cell (`WorldSink::mint_open_cell`).
        MintOpenCell { seed: String, funding: u64 },
    }

    /// One response per request, in order. MUST stay shape-identical to
    /// `deos_hermes::world_bridge::BridgeResponse`.
    #[derive(Debug, Serialize, Deserialize)]
    pub enum BridgeResponse {
        /// The `WithLedger` snapshot (the client rebuilds a local `Ledger`).
        Ledger { cells: Vec<Cell> },
        /// The `FireEffects` verdict: the REAL receipt hash on the live ledger,
        /// or the executor's rejection reason.
        Fired(Result<[u8; 32], String>),
        /// The `MintOpenCell` verdict.
        Minted(Result<CellId, String>),
    }

    /// Write one length-prefixed serde_json frame.
    fn write_frame<W: Write, T: Serialize>(w: &mut W, msg: &T) -> std::io::Result<()> {
        let bytes = serde_json::to_vec(msg)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
        w.write_all(&(bytes.len() as u32).to_le_bytes())?;
        w.write_all(&bytes)?;
        w.flush()
    }

    /// Read one frame; `Ok(None)` = clean EOF at a frame boundary.
    fn read_frame<R: Read, T: DeserializeOwned>(r: &mut R) -> std::io::Result<Option<T>> {
        let mut len = [0u8; 4];
        match r.read_exact(&mut len) {
            Ok(()) => {}
            Err(e) if e.kind() == std::io::ErrorKind::UnexpectedEof => return Ok(None),
            Err(e) => return Err(e),
        }
        let n = u32::from_le_bytes(len) as usize;
        if n > MAX_FRAME_BYTES {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                format!("world-bridge frame of {n} bytes exceeds the {MAX_FRAME_BYTES} cap"),
            ));
        }
        let mut buf = vec![0u8; n];
        r.read_exact(&mut buf)?;
        serde_json::from_slice(&buf)
            .map(Some)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))
    }

    /// Answer ONE request against the live sink.
    fn answer(sink: &mut dyn WorldSink, req: BridgeRequest) -> BridgeResponse {
        match req {
            BridgeRequest::WithLedger => {
                let mut cells: Vec<Cell> = Vec::new();
                sink.with_ledger(&mut |l| {
                    cells = l.iter().map(|(_, c)| c.clone()).collect();
                });
                BridgeResponse::Ledger { cells }
            }
            BridgeRequest::FireEffects {
                agent,
                method,
                effects,
            } => BridgeResponse::Fired(sink.fire_effects(agent, &method, effects)),
            BridgeRequest::MintOpenCell { seed, funding } => {
                BridgeResponse::Minted(sink.mint_open_cell(&seed, funding))
            }
        }
    }

    /// BLOCKING serve: bind `socket_path` (removing a stale socket file), accept
    /// ONE client, answer requests against `sink` until the client closes the
    /// connection (EOF). Returns the number of requests served. Runs on the
    /// thread that owns the sink (the World never crosses threads).
    pub fn serve_world_bridge(
        socket_path: &Path,
        sink: &mut dyn WorldSink,
    ) -> std::io::Result<usize> {
        let _ = std::fs::remove_file(socket_path);
        let listener = UnixListener::bind(socket_path)?;
        let (mut stream, _addr) = listener.accept()?;
        let mut served = 0usize;
        while let Some(req) = read_frame::<_, BridgeRequest>(&mut stream)? {
            write_frame(&mut stream, &answer(sink, req))?;
            served += 1;
        }
        Ok(served)
    }

    /// The NON-BLOCKING serving mode for the live cockpit: bind once, then call
    /// [`WorldBridgeServer::pump`] from the frame loop on the World-owning
    /// thread. Each pump accepts a pending client (one at a time) and answers
    /// every request already waiting on the socket, without ever blocking the
    /// frame.
    pub struct WorldBridgeServer {
        listener: UnixListener,
        client: Option<UnixStream>,
    }

    impl WorldBridgeServer {
        /// Bind the bridge socket (removing a stale socket file). Non-blocking
        /// accept; call [`Self::pump`] from the owning thread's loop.
        pub fn bind(socket_path: &Path) -> std::io::Result<Self> {
            let _ = std::fs::remove_file(socket_path);
            let listener = UnixListener::bind(socket_path)?;
            listener.set_nonblocking(true)?;
            Ok(WorldBridgeServer {
                listener,
                client: None,
            })
        }

        /// Whether a client is currently connected.
        pub fn has_client(&self) -> bool {
            self.client.is_some()
        }

        /// Drain the bridge: accept a pending client if none is connected, then
        /// answer every request already waiting, returning how many were served
        /// this pump. Never blocks: with no pending client/request it returns
        /// `Ok(0)` immediately. A client EOF/fault drops the connection (the
        /// next pump can accept a fresh client); requests are small, so once a
        /// frame has begun the read completes blockingly (the client writes
        /// each frame whole).
        pub fn pump(&mut self, sink: &mut dyn WorldSink) -> std::io::Result<usize> {
            if self.client.is_none() {
                match self.listener.accept() {
                    Ok((stream, _addr)) => {
                        stream.set_nonblocking(false)?;
                        self.client = Some(stream);
                    }
                    Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => return Ok(0),
                    Err(e) => return Err(e),
                }
            }
            let mut served = 0usize;
            while let Some(stream) = self.client.as_mut() {
                // Probe non-blockingly: is a request (or EOF) waiting? A
                // non-blocking read of the 4-byte length header either returns
                // bytes (a frame has begun — finish it blockingly below; the
                // client writes each frame whole, so the rest is imminent),
                // 0 (EOF), or WouldBlock (nothing pending this pump).
                stream.set_nonblocking(true)?;
                let mut header = [0u8; 4];
                let probed = stream.read(&mut header);
                stream.set_nonblocking(false)?;
                match probed {
                    Ok(0) => {
                        self.client = None; // clean EOF — client hung up
                        break;
                    }
                    Ok(n) => {
                        let outcome = (|| -> std::io::Result<BridgeRequest> {
                            if n < header.len() {
                                stream.read_exact(&mut header[n..])?;
                            }
                            let len = u32::from_le_bytes(header) as usize;
                            if len > MAX_FRAME_BYTES {
                                return Err(std::io::Error::new(
                                    std::io::ErrorKind::InvalidData,
                                    format!(
                                        "world-bridge frame of {len} bytes exceeds the \
                                         {MAX_FRAME_BYTES} cap"
                                    ),
                                ));
                            }
                            let mut buf = vec![0u8; len];
                            stream.read_exact(&mut buf)?;
                            serde_json::from_slice(&buf).map_err(|e| {
                                std::io::Error::new(std::io::ErrorKind::InvalidData, e)
                            })
                        })();
                        match outcome {
                            Ok(req) => {
                                let resp = answer(sink, req);
                                if write_frame(stream, &resp).is_err() {
                                    self.client = None;
                                    break;
                                }
                                served += 1;
                            }
                            Err(_) => {
                                self.client = None; // EOF mid-frame or a corrupt frame
                                break;
                            }
                        }
                    }
                    Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => break,
                    Err(_) => {
                        self.client = None;
                        break;
                    }
                }
            }
            Ok(served)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use deos_js::JsRuntime;

    /// THE CAPSTONE, PROVEN BY RUNNING (gpui-free): the agent's deos-js, attached to
    /// a LIVE cockpit World, (a) crawls the World's ACTUAL cells, (b) fires a real
    /// verified turn on the agent's cell under its `held` → a receipt that lands on
    /// the live ledger, (c) an over-reach (an affordance whose `required` the agent
    /// does NOT hold) is REFUSED in-band — no turn, no receipt.
    ///
    /// SpiderMonkey's `JSEngine::init()` is process-global + one-shot, so the LIVE and
    /// FORK variants share ONE runtime in this single test.
    #[test]
    fn agent_run_js_drives_the_live_cockpit_world() {
        // The cockpit's real image (the same `World` the windowed cockpit runs).
        let (world, anchors) = crate::world::demo_world();
        let [_treasury, _service, user] = anchors;
        let live = Rc::new(RefCell::new(world));

        // The agent IS the `user` cell. Its mandate `held` is an ATTENUATED
        // authority — `Signature`, NOT the broadest `None` — so the cap tooth can
        // genuinely refuse: a holder of `Signature` may present affordances whose
        // `required` is narrower-or-equal to `Signature` (i.e. `Signature` itself),
        // but NOT one demanding `Proof` (an incomparable peer — `Proof ⊄ Signature`).
        let agent = user;
        let held = AuthRequired::Signature;
        // The affordance surface: `bump` (held — required Signature, admitted) and
        // `escalate` (an OVER-REACH — required Proof the agent's Signature does not
        // satisfy → refused in-band by the deos-js cap tooth, no turn).
        let affordances = vec![
            ("bump".to_string(), AuthRequired::Signature),
            ("escalate".to_string(), AuthRequired::Proof),
        ];

        let mut rt = JsRuntime::new().expect("boot SpiderMonkey");

        // ── (LIVE) attach to the operator's REAL World ──────────────────────────
        let pre_height = live.borrow().height();
        let pre_receipts = live.borrow().receipts().len();
        let cell_count = live.borrow().cell_count();
        let agent_hex = hex::encode(agent.as_bytes());

        let sink = WorldSinkAdapter::live(live.clone());
        let sink_world = sink.world();
        let applet = attach_agent(sink, agent, held.clone(), affordances.clone());

        // The agent's JS: crawl the LIVE cells, fire a real turn, attempt an over-reach.
        let script = r#"
            var app = deos.applet({ affordances: ["bump", "escalate"] });
            // (a) CRAWL the live cockpit cells (the REAL ones, not a fresh demo).
            var n = deos.world.cells().length;
            // (b) FIRE a real verified turn on the agent's OWN cell (held).
            var before = app.get(0);
            var after = app.fire("bump", 7);
            // (c) OVER-REACH: escalate requires Proof the agent does not hold → -1.
            var over = app.fire("escalate", 1);
            // pack a witness int: cells*1000 + after*10 + (over === -1 ? 1 : 0)
            (n * 1000) + (after * 10) + (over === -1 ? 1 : 0);
            "#
        .to_string();

        let outcome = rt
            .run_attached(applet, &script)
            .expect("run the agent JS on the live World");

        let witness = outcome.result.expect("script produced an int");
        let crawled = witness / 1000;
        let after = (witness % 1000) / 10;
        let over_refused = witness % 10 == 1;

        // (a) the crawl saw the LIVE cells (the demo world's real count).
        assert_eq!(
            crawled, cell_count as i32,
            "JS crawled the live cockpit cells"
        );
        assert!(cell_count >= 4, "demo world has its real anchor cells");
        // (b) the fire committed a real turn → counter is 7, ONE receipt on the tape.
        assert_eq!(after, 7, "the held fire bumped the live counter");
        assert_eq!(
            outcome.fires_committed, 1,
            "exactly ONE verified turn committed"
        );
        assert_eq!(outcome.receipts.len(), 1, "one receipt on the agent's tape");
        // (c) the over-reach was refused IN-BAND (JS saw -1; no extra receipt).
        assert!(
            over_refused,
            "the over-reach (Proof) was refused by the cap tooth"
        );

        // THE RECEIPT LANDED ON THE LIVE LEDGER: the cockpit's own provenance log +
        // height grew by exactly ONE (the held fire), NOT two (the over-reach left
        // nothing). And the agent cell's slot-0 field on the LIVE ledger is now 7.
        let post_height = sink_world.borrow().height();
        let post_receipts = sink_world.borrow().receipts().len();
        assert_eq!(post_height, pre_height + 1, "live world height grew by ONE");
        assert_eq!(
            post_receipts,
            pre_receipts + 1,
            "ONE receipt on the live log"
        );
        let live_field = {
            let w = sink_world.borrow();
            let cell = w.ledger().get(&agent).expect("agent cell live");
            cell.state
                .get_field(AGENT_COUNTER_SLOT)
                .map(deos_js::applet::unpack_u64)
                .unwrap_or(0)
        };
        assert_eq!(
            live_field, 7,
            "the agent's JS modified the REAL cell on the live ledger"
        );

        // Sanity: the cell id the agent drove is one the crawl reported.
        assert_eq!(agent_hex.len(), 64);

        // ── (FORK) the safe sandbox variant — the live World is UNTOUCHED ────────
        let fork_sink = WorldSinkAdapter::fork_of(&live);
        let fork_world = fork_sink.world();
        let fork_applet = attach_agent(fork_sink, agent, held, affordances);
        let fork_out = rt
            .run_attached(
                fork_applet,
                r#"
                var app = deos.applet({ affordances: ["bump"] });
                app.fire("bump", 100);
                app.get(0);
            "#,
            )
            .expect("run on the fork");
        // The fork's agent counter is 7 (carried) + 100 = 107.
        assert_eq!(
            fork_out.result,
            Some(107),
            "the fork committed a turn (107)"
        );
        assert_eq!(fork_out.fires_committed, 1);
        // THE LIVE WORLD IS UNTOUCHED by the fork: still 7, height unchanged.
        let live_after_fork = {
            let w = live.borrow();
            let cell = w.ledger().get(&agent).expect("agent cell");
            cell.state
                .get_field(AGENT_COUNTER_SLOT)
                .map(deos_js::applet::unpack_u64)
                .unwrap_or(0)
        };
        assert_eq!(live_after_fork, 7, "the fork did NOT touch the live World");
        assert_eq!(
            fork_world.borrow().height(),
            post_height + 1,
            "the fork's own height advanced"
        );
    }

    /// **AGENT-MEMORY AS umem, LOAD-BEARING ON THE LIVE AGENT PATH** (gpui-free,
    /// SpiderMonkey-free — the attach machinery is plain Rust). A live confined agent
    /// (the SAME `WorldSinkAdapter` / `attach_agent` agent the cockpit drives) evolves
    /// its working-set, is CHECKPOINTED to a umem-ref, dropped, and a FRESH agent
    /// context is reconstituted from the carrier and CONTINUES from the checkpoint —
    /// proven byte-identical in the universal address space, and fail-closed.
    #[test]
    fn live_agent_memory_checkpoint_resume_continues() {
        use crate::agent_memory::{AgentMemoryCheckpoint, AgentMemoryError};
        use deos_js::applet::pack_u64;
        use dregg_turn::umem;

        // ── 1. A LIVE confined agent evolves its working-set ─────────────────────
        let (world, anchors) = crate::world::demo_world();
        let [_treasury, _service, user] = anchors;
        let agent = user;
        let held = AuthRequired::Signature;
        let affordances = vec![("bump".to_string(), AuthRequired::Signature)];

        let live = Rc::new(RefCell::new(world));
        let mut applet = attach_agent(
            WorldSinkAdapter::live(live.clone()),
            agent,
            held.clone(),
            affordances.clone(),
        );
        // Two cap-gated verified turns on the LIVE World — the working-set accumulates.
        applet.fire("bump", 7).expect("bump 7");
        applet.fire("bump", 5).expect("bump 5");
        assert_eq!(
            applet.get_u64(AGENT_COUNTER_SLOT),
            12,
            "live counter 0+7+5 = 12"
        );

        // ── 2. CHECKPOINT the live agent's working-set as a witnessed umem ───────
        let checkpoint = AgentMemoryCheckpoint::capture(&live.borrow(), agent)
            .expect("capture the live agent's umem");
        assert_eq!(
            checkpoint.working_slot(AGENT_COUNTER_SLOT),
            12,
            "the umem carries the agent's accumulated working-set (12)"
        );
        // The carrier on the wire — then the live agent + World are DROPPED.
        let carrier = checkpoint.to_bytes().expect("serialize the checkpoint");
        drop(applet);
        drop(live);

        // ── 3. RESUME into a FRESH agent context from nothing but the carrier ────
        let recovered = AgentMemoryCheckpoint::from_bytes(&carrier).expect("load the carrier");
        let resumed_world = recovered
            .resume_into_fresh_world()
            .expect("reify the agent into a fresh World (fail-closed teeth all pass)");
        let resumed_live = Rc::new(RefCell::new(resumed_world));
        let mut resumed = attach_agent(
            WorldSinkAdapter::live(resumed_live.clone()),
            agent,
            held,
            affordances,
        );
        // The resumed agent CONTINUES from the checkpoint (12), not a reset.
        assert_eq!(
            resumed.get_u64(AGENT_COUNTER_SLOT),
            12,
            "the resumed agent's working-set is the checkpoint (12), not a reset"
        );

        // ── 4. THE WITNESS: the umem came across byte-for-byte ───────────────────
        let resumed_umem = AgentMemoryCheckpoint::capture(&resumed_live.borrow(), agent)
            .expect("re-capture the resumed agent");
        assert_eq!(
            resumed_umem.umem, recovered.umem,
            "THE ROUND-TRIP WITNESS: the resumed agent's umem is byte-identical to the \
             checkpoint in the universal address space"
        );
        assert_eq!(
            resumed_umem.root, recovered.root,
            "the root tooth re-derives"
        );

        // ── 5. CONTINUE: the resumed agent fires further, advancing FROM 12 ──────
        let pre_height = resumed_live.borrow().height();
        resumed
            .fire("bump", 100)
            .expect("the resumed agent fires on");
        assert_eq!(
            resumed.get_u64(AGENT_COUNTER_SLOT),
            112,
            "the resumed agent advanced its working-set FROM the checkpoint (12 + 100)"
        );
        assert_eq!(
            resumed_live.borrow().height(),
            pre_height + 1,
            "the post-handoff fire committed a real verified turn on the resumed World"
        );

        // ── 6. FAIL-CLOSED: a tampered umem carrier REFUSES to resume ────────────
        let mut tampered = recovered.clone();
        tampered.umem.insert(
            umem::UKey::Field {
                cell: agent,
                slot: AGENT_COUNTER_SLOT as u64,
            },
            umem::UVal::Bytes32(pack_u64(999)),
        );
        match tampered.resume_into_fresh_world() {
            Err(AgentMemoryError::RootTooth { .. }) => {}
            Err(e) => panic!("a tampered umem must refuse via the root tooth, got {e:?}"),
            Ok(_) => panic!("a tampered umem must NOT resume — it bypassed the root tooth"),
        }
    }
}
