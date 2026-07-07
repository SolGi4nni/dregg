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

/// The reverse-proxy hop for one request, when a fleet is configured. Returns
/// `Some(response bytes)` if the host handled the request as a proxy forward
/// (dialled the proven-chosen backend and returned its bytes, or produced a
/// 502/503), or `None` when no fleet is configured so the caller falls through to
/// the normal serve.
///
/// The WHICH-backend decision is always the proven `drorb_proxy_pick`, crossed on
/// the serve thread via `gw`; this function never selects a backend.
pub fn handle_proxy(
    req: &[u8],
    gw: &ServeGateway,
    reply_tx: &Sender<PooledBuf>,
    reply_rx: &Receiver<PooledBuf>,
) -> Option<(Vec<u8>, Option<String>)> {
    let fleet = fleet()?;
    Some(proxy_dial::handle(req, fleet, |mask, key| {
        pick_via_seam(mask, key, gw, reply_tx, reply_rx)
    }))
}

/// Cross the proven `drorb_proxy_pick` seam on the runtime-owner serve thread:
/// marshal `(mask, key)` into the input bytes the export decodes — byte 0 = the
/// live health/breaker mask, bytes 1.. = the sticky-affinity key — submit across
/// [`Seam::ProxyPick`], and parse the decimal-ASCII backend id it returns. EMPTY
/// output means no backend is eligible (whole pool down / breaker-open), which
/// maps to `None` ⇒ the host serves 503 and dials nothing.
fn pick_via_seam(
    mask: u8,
    key: &[u8],
    gw: &ServeGateway,
    reply_tx: &Sender<PooledBuf>,
    reply_rx: &Receiver<PooledBuf>,
) -> Option<u32> {
    let mut input = gw.pool().take();
    input.push(mask);
    input.extend_from_slice(key);
    let out = gw.call_seam(input, Seam::ProxyPick, reply_tx, reply_rx)?;
    if out.is_empty() {
        return None;
    }
    std::str::from_utf8(&out).ok()?.trim().parse().ok()
}
