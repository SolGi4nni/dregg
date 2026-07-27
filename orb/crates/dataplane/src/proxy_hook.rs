//! The reverse-proxy lane wired into the running dataplane.
//!
//! This is the seam that turns the proxy/fabric scenarios from UNWIRED into a
//! real forward: a request under a proxy route (`/api`) is sent to a LIVE backend
//! over a real socket, and the upstream's response bytes come back.
//!
//! It keeps the sans-IO split intact:
//!
//! * the CORE decides WHICH backend — the proven `Reactor.ProxyDial.pick`
//!   (`Proxy.selectChain` over the live-health-masked fleet, honouring health
//!   ejection, the circuit breaker, and sticky affinity), exported as
//!   `drorb_proxy_pick`. That decision is crossed on the runtime-owner serve
//!   thread through [`crate::serve::Seam::ProxyPick`], the same single-owner
//!   discipline as every other Lean seam — no thread but the serve owner ever
//!   touches the runtime.
//! * the HOST opens the TCP connection and moves the bytes — [`proxy_dial`]'s
//!   `forward`, run HERE on the caller's connection thread so a blocking upstream
//!   dial never stalls the serve thread.
//!
//! The backend fleet is configured out of band via `DRORB_PROXY_BACKENDS`
//! (e.g. `0=127.0.0.1:9400,1=127.0.0.1:9401`). When it is unset there is no
//! fleet, `/api` is not treated as a proxy route, and the request falls through
//! to the normal serve. When it is set, a background active-health loop probes
//! each backend so a dead one is ejected from the proven pick's eligible pool.

use std::net::TcpStream;
use std::sync::mpsc::{Receiver, Sender};
use std::sync::{Arc, OnceLock};
use std::time::Duration;

use crate::pool::PooledBuf;
use crate::proxy_dial::{self, Fleet};
use crate::serve::{Seam, ServeGateway};

pub use crate::proxy_dial::is_proxy_path;

/// How often the background loop re-probes every configured backend.
const HEALTH_INTERVAL: Duration = Duration::from_millis(500);

/// Process-global proxy fleet, initialised once from `DRORB_PROXY_BACKENDS`.
/// `None` when the variable is unset (no proxy routing configured).
static FLEET: OnceLock<Option<Arc<Fleet>>> = OnceLock::new();

/// The configured fleet, or `None` when `DRORB_PROXY_BACKENDS` is unset. On first
/// access with a fleet present, the active-health loop is spawned so the mask the
/// proven pick consumes tracks real backend liveness.
pub(crate) fn fleet() -> Option<&'static Arc<Fleet>> {
    FLEET
        .get_or_init(|| {
            let f = Fleet::from_env().map(Arc::new);
            if let Some(fl) = &f {
                Arc::clone(fl).spawn_health_checks(HEALTH_INTERVAL);
            }
            f
        })
        .as_ref()
}

/// The STREAMING reverse-proxy hop for one request, when a fleet is configured:
/// the proven-chosen backend is dialled and its response is written to `client` as
/// it arrives instead of buffered whole. On Linux the response BODY crosses
/// kernel-side via the splice relay (upstream socket → pipe → client socket,
/// never entering this process); elsewhere it is the bounded userspace pump.
/// Either way the wire bytes are identical and back-pressure holds. Returns
/// `None` when no fleet is
/// configured (the caller falls through to the normal serve), `Some(Ok(outcome))`
/// with what the host records after streaming, or `Some(Err(_))` when a client
/// write failed and the connection must be dropped.
///
/// The WHICH-backend decision is always the proven `drorb_proxy_pick`, crossed on
/// the serve thread via `gw`; this function never selects a backend.
pub fn handle_proxy_streaming(
    req: &[u8],
    keepalive_req: bool,
    client: &mut TcpStream,
    gw: &ServeGateway,
    reply_tx: &Sender<PooledBuf>,
    reply_rx: &Receiver<PooledBuf>,
) -> Option<std::io::Result<proxy_dial::StreamOutcome>> {
    let fleet = fleet()?;
    Some(proxy_dial::handle_streaming_tcp(
        req,
        keepalive_req,
        fleet,
        client,
        |mask, key| {
            // The config LB policy (DRORB_LB_POLICY) + the live per-backend load
            // reach the proven pick here; unset => rendezvous (byte 3), the same
            // selection the prior fixed-rendezvous dial made.
            let pol = lb_policy_byte();
            let round = fleet.next_round();
            let conns = fleet.conns_bytes();
            pick_lb_via_seam(pol, round, mask, &conns, key, gw, reply_tx, reply_rx)
        },
    ))
}

/// Whether a request must leave a COMPLETION REACTOR's shard for the reverse-proxy
/// lane: a proxy route (`/api`, with a backend fleet configured through
/// `DRORB_PROXY_BACKENDS`) with the effect seam OFF, or an operator-config proxy
/// vhost (which forwards independent of the seam). Exactly the two conditions
/// `blocking::handle_conn` forks on, read from the same state — this predicate
/// decides only WHERE a request is served, never how.
///
/// With no fleet configured there is nothing to forward to, so `/api` is not a
/// proxy route and the request stays on the shard for the ordinary serve
/// ([`handle_proxy_streaming`] returns `None` on the portable path for the same
/// reason). With the effect seam ON the proven core yields `proxyDial` and the
/// io_uring shard drives that dial natively on a second socket
/// (`uring::start_proxy_dial`), so the fork stands down.
///
/// The reactors need the fork because [`handle_proxy_streaming`] dials the upstream
/// and pumps its reply with BLOCKING I/O, which a shard may never do. Without it a
/// reactor has NO proxy path at all: `/api` falls through to the route table and
/// 404s — which is what `conformance/proxy/battery.py` measured (14/14 -> 3/14) the
/// moment it stopped pinning `--io blocking` and started grading the reactor
/// production actually runs.
pub fn takes_over_connection(req: &[u8]) -> bool {
    if fleet().is_none() {
        return false;
    }
    if !crate::interp::enabled() && is_proxy_path(req) {
        return true;
    }
    crate::config::get()
        .map(|d| d.is_vhost_proxy(req))
        .unwrap_or(false)
}

/// The config LB-policy byte the running reverse-proxy dial threads to the proven
/// `drorb_lb_pick`, read from `DRORB_LB_POLICY`. The byte convention matches the
/// proven codec (`Reactor.LoadBalance.policyOfByte` / `Dsl.Config.policyOfByte`):
/// `0` weighted round-robin, `1` least-connections, `2` weighted-least-connections,
/// else rendezvous hash. Unset defaults to rendezvous (byte 3) - the same
/// session-affinity selection the prior fixed dial made, so an unconfigured
/// deployment is unchanged.
pub fn lb_policy_byte() -> u8 {
    match std::env::var("DRORB_LB_POLICY").ok().as_deref() {
        Some("roundRobin") | Some("round_robin") | Some("rr") | Some("wrr") | Some("0") => 0,
        Some("leastConn") | Some("least_conn") | Some("leastconn") | Some("1") => 1,
        Some("wLeastConn") | Some("weighted_least_conn") | Some("wleastconn") | Some("2") => 2,
        _ => 3,
    }
}

/// Cross the proven `drorb_lb_pick` seam on the runtime-owner serve thread: marshal
/// `(pol, round, mask, conns, key)` into the frame the export decodes -
/// `pol :: round :: mask :: n :: conns[n] :: key` - submit across [`Seam::LbPick`],
/// and parse the decimal-ASCII backend id it returns. EMPTY output means no backend
/// is eligible (whole pool down / breaker-open), which maps to `None` => the host
/// serves 503 and dials nothing. Health ejection holds for every policy byte
/// (`Reactor.LoadBalance.pick_health_ejects`).
fn pick_lb_via_seam(
    pol: u8,
    round: u8,
    mask: u8,
    conns: &[u8],
    key: &[u8],
    gw: &ServeGateway,
    reply_tx: &Sender<PooledBuf>,
    reply_rx: &Receiver<PooledBuf>,
) -> Option<u32> {
    let mut input = gw.pool().take();
    input.push(pol);
    input.push(round);
    input.push(mask);
    input.push(conns.len() as u8);
    input.extend_from_slice(conns);
    input.extend_from_slice(key);
    let out = gw.call_seam(input, Seam::LbPick, reply_tx, reply_rx)?;
    if out.is_empty() {
        return None;
    }
    std::str::from_utf8(&out).ok()?.trim().parse().ok()
}
