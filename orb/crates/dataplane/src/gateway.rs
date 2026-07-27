//! The `DRORB_GATEWAY` selector: choose the compiled-in Gateway umbrella config the
//! deployed serve dispatches through `drorb_serve_gateway` (the proven
//! `Dsl.Config.Gateway.denoteOn` host -> vhost -> route -> action fold).
//!
//! Config-as-data: the umbrella lives as a Lean VALUE (`Dsl.Config.Gateway.dreggNet`);
//! this env selector only picks WHICH compiled-in value the running binary serves. Unset
//! (or an unknown value) leaves the gateway lane inert, so the default serve path is
//! byte-identical (the Lean `drorbServeGateway_empty_eq` no-regression anchor).

use std::sync::OnceLock;

/// The Gateway umbrella selector from `DRORB_GATEWAY`, read once for the process
/// lifetime. `dreggnet` (or `dregg.net` / `1`) selects the replicated dregg.net
/// umbrella (`gatewayConfigOf 1 = Dsl.Config.Gateway.dreggNet`). Anything else ⇒ `None`
/// (the gateway lane does not fire).
pub fn selector() -> Option<u64> {
    static SEL: OnceLock<Option<u64>> = OnceLock::new();
    *SEL.get_or_init(|| {
        match std::env::var("DRORB_GATEWAY")
            .ok()
            .as_deref()
            .map(str::trim)
        {
            Some("dreggnet") | Some("dregg.net") | Some("1") => Some(1),
            _ => None,
        }
    })
}

/// Frame `gwSel(8 BE) :: request` into a fresh pooled buffer and submit it across the
/// Gateway-umbrella metered seam ASYNCHRONOUSLY — the completion-reactor (io_uring /
/// kqueue) analogue of [`crate::serve::ServeGateway::call_gateway`]: identical framing,
/// identical proven seam (`drorb_serve_gateway`), no blocking recv.
///
/// The gateway seam consumes a PREFIXED frame, so — exactly like the metered cfg seam
/// (`ServeGateway::submit_metered_cfg_bytes`) — the 8 selector bytes cannot be
/// prepended inside a leased io_uring buffer-ring slot; this path copies the request
/// out. The zero-copy borrow path stays reserved for the raw-request seams.
///
/// Every reactor calls THIS (or `call_gateway`, its blocking twin), so
/// `DRORB_GATEWAY` selects the same proven `Gateway.denoteOn` dispatch whichever IO
/// path the deployment runs. Returns `false` only if the serve thread is gone.
pub fn submit_bytes(
    gw: &crate::serve::ServeGateway,
    sel: u64,
    req: &[u8],
    meter: crate::serve::Meter,
    reply: crate::serve::ServeReply,
) -> bool {
    let mut framed = gw.pool().take();
    framed.clear();
    framed.extend_from_slice(&sel.to_be_bytes());
    framed.extend_from_slice(req);
    gw.submit_gateway(framed, meter, reply)
}
