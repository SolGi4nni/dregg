//! THE WORLD BRIDGE — the socket that lands the MCP server's `run_js` on the
//! COCKPIT'S live World.
//!
//! ## Why this exists (the cross-process seam, closed)
//!
//! An MCP server is a SEPARATE subprocess Hermes spawns, so it cannot share the
//! cockpit's `Rc<RefCell<World>>` (single-threaded, non-`Send`, in-process). The
//! server's `run_js` therefore drove its OWN embedded verified World — a real
//! receipted turn, but on its own ledger, not the operator's live one.
//! `docs/deos/LOG-A-HERMES-IN.md` named the fix: `RunJsTool::run_attached_on`
//! already accepts ANY `WorldSink`, so "the wire is a socket-backed sink
//! adapter". THIS is that adapter:
//!
//!   * [`SocketWorldSink`] (client half, THIS process) — presents the exact
//!     `WorldSink` surface (`with_ledger` / `fire_effects` / `mint_open_cell`)
//!     over a Unix domain socket. Under `js-agent` it literally
//!     `impl deos_js::WorldSink`, so `run_attached_on(Box::new(sink), …)` drives
//!     the cockpit's live World from inside the MCP subprocess.
//!   * [`serve_world_bridge`] (serving half) — the cockpit process binds the
//!     socket NEXT TO its live `WorldSinkAdapter` and answers the protocol; the
//!     starbridge-v2 twin lives in `starbridge-v2/src/agent_attach.rs`
//!     (`world_bridge` submodule). The serving loop here (over [`BridgeWorld`])
//!     exists so the protocol is testable inside this crate without gpui/mozjs.
//!
//! ## The wire (the contract BOTH twins must keep, byte for byte)
//!
//! One frame = a `u32` little-endian byte length + that many bytes of
//! `serde_json`. Requests are [`BridgeRequest`], responses [`BridgeResponse`],
//! strictly one response per request, in order, over ONE client connection:
//!
//!   * `WithLedger` → `Ledger { cells }` — a SNAPSHOT of the live cells (the
//!     `Ledger` itself is not serde; the client rebuilds a local `Ledger` from
//!     the cells and runs the crawl closure over it). A witnessed read of the
//!     REAL cells at request time.
//!   * `FireEffects { agent, method, effects }` → `Fired(Result<receipt, err>)`
//!     — the host builds the turn with its OWN `World::turn` shape (nonce, fee,
//!     chain head threaded host-side) and commits it through the verified
//!     executor. The receipt hash that comes back is the REAL one on the live
//!     ledger.
//!   * `MintOpenCell { seed, funding }` → `Minted(Result<cell_id, err>)`.
//!
//! ## FAIL-CLOSED (the load-bearing property)
//!
//! A bridge-configured `run_js` NEVER silently falls back to the embedded
//! World: socket absent ⇒ [`SocketWorldSink::connect`] errs and the tool call
//! REFUSES ([`crate::McpToolHost::with_world_bridge`]); socket dying mid-run ⇒
//! the sink latches [`SocketWorldSink::is_dead`], every subsequent fire errs
//! (the JS sees the executor refusal in-band) and a crawl reads NOTHING (the
//! closure is not run — never a stale or substitute world).

#![cfg(unix)]

use std::cell::RefCell;
use std::io::{Read, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::Path;
use std::rc::Rc;

use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

use dregg_cell::{Cell, CellId, Ledger};
use dregg_turn::action::Effect;

/// The largest frame either side will read (a whole-ledger snapshot rides in one
/// frame; a cockpit image is far below this). A frame claiming more is a
/// protocol fault, not an allocation request.
pub const MAX_FRAME_BYTES: usize = 256 * 1024 * 1024;

// ────────────────────────────── the wire types ──────────────────────────────

/// One request on the world-bridge wire — exactly the `WorldSink` surface,
/// nothing else. The starbridge-v2 twin (`agent_attach::world_bridge`) must
/// keep these variants shape-identical (serde_json is the contract).
#[derive(Debug, Serialize, Deserialize)]
pub enum BridgeRequest {
    /// The crawl read: snapshot the live cells.
    WithLedger,
    /// Commit ONE verified turn on the served World (`WorldSink::fire_effects`).
    FireEffects {
        agent: CellId,
        method: String,
        effects: Vec<Effect>,
    },
    /// Mint an OPEN, funded cell (`WorldSink::mint_open_cell`).
    MintOpenCell { seed: String, funding: u64 },
}

/// One response on the world-bridge wire (strictly one per request, in order).
#[derive(Debug, Serialize, Deserialize)]
pub enum BridgeResponse {
    /// The `WithLedger` snapshot: every live cell (the client rebuilds a local
    /// `Ledger` to run the crawl closure over).
    Ledger { cells: Vec<Cell> },
    /// The `FireEffects` verdict: the REAL receipt hash on the served ledger,
    /// or the executor's rejection reason.
    Fired(Result<[u8; 32], String>),
    /// The `MintOpenCell` verdict.
    Minted(Result<CellId, String>),
}

// ────────────────────────────── the framing ─────────────────────────────────

/// Write one length-prefixed serde_json frame.
pub fn write_frame<W: Write, T: Serialize>(w: &mut W, msg: &T) -> std::io::Result<()> {
    let bytes = serde_json::to_vec(msg)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
    w.write_all(&(bytes.len() as u32).to_le_bytes())?;
    w.write_all(&bytes)?;
    w.flush()
}

/// Read one length-prefixed serde_json frame. `Ok(None)` = a clean EOF at a
/// frame boundary (the peer closed the bridge).
pub fn read_frame<R: Read, T: DeserializeOwned>(r: &mut R) -> std::io::Result<Option<T>> {
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

// ─────────────────────────── the serving half ───────────────────────────────

/// The surface a served world presents — the `deos_js::WorldSink` methods,
/// verbatim (same signatures, same semantics), restated here so the serving
/// loop compiles WITHOUT the optional multi-GB deos-js dep. Under `js-agent`
/// every `WorldSink` is a `BridgeWorld` (the blanket impl below welds the two
/// to one semantics); this trait adds none of its own.
pub trait BridgeWorld {
    /// `WorldSink::with_ledger` — run `f` over a borrow of the live ledger.
    fn with_ledger(&self, f: &mut dyn FnMut(&Ledger));
    /// `WorldSink::fire_effects` — commit ONE verified turn, returning the real
    /// receipt hash or the executor's rejection reason.
    fn fire_effects(
        &mut self,
        agent: CellId,
        method: &str,
        effects: Vec<Effect>,
    ) -> Result<[u8; 32], String>;
    /// `WorldSink::mint_open_cell` — same default: a host must opt in.
    fn mint_open_cell(&mut self, _seed: &str, _funding: u64) -> Result<CellId, String> {
        Err("mint_open_cell requires an attached host ledger".into())
    }
}

/// Every `deos_js::WorldSink` IS a `BridgeWorld` — one semantics, no drift.
#[cfg(feature = "js-agent")]
impl<T: deos_js::WorldSink> BridgeWorld for T {
    fn with_ledger(&self, f: &mut dyn FnMut(&Ledger)) {
        deos_js::WorldSink::with_ledger(self, f)
    }
    fn fire_effects(
        &mut self,
        agent: CellId,
        method: &str,
        effects: Vec<Effect>,
    ) -> Result<[u8; 32], String> {
        deos_js::WorldSink::fire_effects(self, agent, method, effects)
    }
    fn mint_open_cell(&mut self, seed: &str, funding: u64) -> Result<CellId, String> {
        deos_js::WorldSink::mint_open_cell(self, seed, funding)
    }
}

/// Serve the world bridge at `socket_path` over `world`: bind (removing a stale
/// socket file), accept ONE client, answer requests until the client closes the
/// connection (EOF). Returns the number of requests served.
///
/// DESIGN (non-`Send` reality): the served world is typically an
/// `Rc<RefCell<World>>` pinned to one thread, so this loop is single-threaded
/// and BLOCKING — it runs on the thread that OWNS the world (a test moves its
/// world into the serving thread; the cockpit either parks a dedicated
/// world-owning thread here or uses the starbridge-v2 twin's non-blocking
/// `WorldBridgeServer::pump` from its frame loop). The world never crosses a
/// thread; the socket comes to IT.
pub fn serve_world_bridge(
    socket_path: &Path,
    world: &mut dyn BridgeWorld,
) -> std::io::Result<usize> {
    // A stale socket file from a dead server would make `bind` fail; a LIVE
    // server's bind still fails (the listener holds the name) — no takeover.
    let _ = std::fs::remove_file(socket_path);
    let listener = UnixListener::bind(socket_path)?;
    let (mut stream, _addr) = listener.accept()?;
    serve_connection(&mut stream, world)
}

/// Answer bridge requests on an accepted `stream` until EOF. Returns the number
/// of requests served. (Split from [`serve_world_bridge`] so a host that owns
/// its own listener/accept lifecycle can reuse the request loop.)
pub fn serve_connection(
    stream: &mut UnixStream,
    world: &mut dyn BridgeWorld,
) -> std::io::Result<usize> {
    let mut served = 0usize;
    while let Some(req) = read_frame::<_, BridgeRequest>(stream)? {
        let resp = match req {
            BridgeRequest::WithLedger => {
                let mut cells: Vec<Cell> = Vec::new();
                world.with_ledger(&mut |l| {
                    cells = l.iter().map(|(_, c)| c.clone()).collect();
                });
                BridgeResponse::Ledger { cells }
            }
            BridgeRequest::FireEffects {
                agent,
                method,
                effects,
            } => BridgeResponse::Fired(world.fire_effects(agent, &method, effects)),
            BridgeRequest::MintOpenCell { seed, funding } => {
                BridgeResponse::Minted(world.mint_open_cell(&seed, funding))
            }
        };
        write_frame(stream, &resp)?;
        served += 1;
    }
    Ok(served)
}

// ─────────────────────────── the client half ────────────────────────────────

/// The socket-backed `WorldSink` — the MCP subprocess's handle on the COCKPIT'S
/// live World. Presents the exact `WorldSink` surface over the bridge protocol;
/// under `js-agent` it `impl deos_js::WorldSink`, so
/// `RunJsTool::run_attached_on(Box::new(sink), …)` needs no other glue.
///
/// Clones share ONE connection (`Rc<RefCell<UnixStream>>` — the whole path is
/// single-threaded), so the host keeps a session-long connection while each
/// `run_js` call boxes a clone. FAIL-CLOSED: any transport fault latches the
/// sink dead — a dead sink's fire ERRS (in-band, visible to the JS) and its
/// crawl runs the closure over NOTHING; there is no embedded world in here to
/// fall back to, by construction.
#[derive(Clone)]
pub struct SocketWorldSink {
    stream: Rc<RefCell<UnixStream>>,
    /// Latched on the first transport fault (shared across clones).
    dead: Rc<std::cell::Cell<bool>>,
}

impl SocketWorldSink {
    /// Connect to the cockpit's world-bridge socket. Errs if the socket is
    /// absent or refuses — the caller REFUSES the tool call (fail-closed).
    pub fn connect(socket_path: &Path) -> std::io::Result<Self> {
        let stream = UnixStream::connect(socket_path)?;
        Ok(SocketWorldSink {
            stream: Rc::new(RefCell::new(stream)),
            dead: Rc::new(std::cell::Cell::new(false)),
        })
    }

    /// Whether the bridge has faulted (latched; shared across clones).
    pub fn is_dead(&self) -> bool {
        self.dead.get()
    }

    /// One request/response round-trip. Any transport or protocol fault latches
    /// the sink dead and errs.
    fn request(&self, req: &BridgeRequest) -> Result<BridgeResponse, String> {
        if self.dead.get() {
            return Err("world bridge is dead (a prior transport fault latched it)".into());
        }
        let mut stream = self.stream.borrow_mut();
        if let Err(e) = write_frame(&mut *stream, req) {
            self.dead.set(true);
            return Err(format!("world bridge write failed: {e}"));
        }
        match read_frame::<_, BridgeResponse>(&mut *stream) {
            Ok(Some(resp)) => Ok(resp),
            Ok(None) => {
                self.dead.set(true);
                Err("world bridge closed by the cockpit (EOF)".into())
            }
            Err(e) => {
                self.dead.set(true);
                Err(format!("world bridge read failed: {e}"))
            }
        }
    }

    /// The `with_ledger` crawl over the bridge: fetch the cell snapshot, rebuild
    /// a local `Ledger`, run `f` over it. On a bridge fault `f` is NOT run (a
    /// degraded read of nothing — never a substitute world).
    pub fn crawl_ledger(&self, f: &mut dyn FnMut(&Ledger)) {
        match self.request(&BridgeRequest::WithLedger) {
            Ok(BridgeResponse::Ledger { cells }) => {
                let mut ledger = Ledger::new();
                for cell in cells {
                    // The served cells satisfy the content-address invariant by
                    // construction; a corrupt one is dropped rather than trusted.
                    let _ = ledger.insert_cell(cell);
                }
                f(&ledger);
            }
            Ok(_) => self.dead.set(true), // out-of-order response = protocol fault
            Err(_) => {}
        }
    }

    /// The `fire_effects` commit over the bridge — the receipt hash that comes
    /// back is the REAL one on the served (cockpit) ledger.
    pub fn commit_fire(
        &mut self,
        agent: CellId,
        method: &str,
        effects: Vec<Effect>,
    ) -> Result<[u8; 32], String> {
        match self.request(&BridgeRequest::FireEffects {
            agent,
            method: method.to_string(),
            effects,
        })? {
            BridgeResponse::Fired(r) => r,
            other => {
                self.dead.set(true);
                Err(format!(
                    "world bridge protocol fault: expected Fired, got {other:?}"
                ))
            }
        }
    }

    /// The `mint_open_cell` superpower over the bridge.
    pub fn mint_remote(&mut self, seed: &str, funding: u64) -> Result<CellId, String> {
        match self.request(&BridgeRequest::MintOpenCell {
            seed: seed.to_string(),
            funding,
        })? {
            BridgeResponse::Minted(r) => r,
            other => {
                self.dead.set(true);
                Err(format!(
                    "world bridge protocol fault: expected Minted, got {other:?}"
                ))
            }
        }
    }
}

/// THE WELD: the socket sink IS a `WorldSink`, so `run_attached_on` drives the
/// cockpit's live World across the process boundary with no other glue.
#[cfg(feature = "js-agent")]
impl deos_js::WorldSink for SocketWorldSink {
    fn with_ledger(&self, f: &mut dyn FnMut(&Ledger)) {
        self.crawl_ledger(f);
    }
    fn fire_effects(
        &mut self,
        agent: CellId,
        method: &str,
        effects: Vec<Effect>,
    ) -> Result<[u8; 32], String> {
        self.commit_fire(agent, method, effects)
    }
    fn mint_open_cell(&mut self, seed: &str, funding: u64) -> Result<CellId, String> {
        self.mint_remote(seed, funding)
    }
}
