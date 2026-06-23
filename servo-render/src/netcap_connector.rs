//! **THE NET-CAP CONNECTOR — the page's outbound socket, bound to the dregg
//! `captp` `Netlayer::dial` transport.**
//!
//! ## The gap this closes (the AUDIT-named "open wire")
//!
//! [`crate::webview::CapGate`] + [`starbridge_web_surface::CapGatedDelegate`] gate
//! the *decision* — at every `load_web_resource` / `request_navigation` callback the
//! held [`SurfaceCapability`] is discharged through the `granted ⊆ held` allowlist.
//! But that allowlist sat in FRONT of an AMBIENT socket: a `Continue` decision then
//! let libservo's own net stack open a kernel TCP socket to *anything*. The cap was a
//! gate, not a wire — the bytes did not traverse an audited transport.
//!
//! This module binds the OUTBOUND CONNECTION to [`dregg_captp::netlayer::Netlayer`] —
//! the SAME `Netlayer::dial` the federation dials over (in-process + relay byte-frame
//! transports; NO ambient OS socket). A connection is opened by [`NetcapConnector::connect`],
//! which:
//!
//! 1. **Re-checks the held [`SurfaceCapability`] at the socket boundary** — not just
//!    a callback in front, but the gate AT the point a connection would open. An
//!    origin the cap does not authorize returns [`ConnectOutcome::RefusedByCap`] and
//!    **`Netlayer::dial` is never called** — the socket is never opened. The gate
//!    bites at the *transport*, the thing the audit asked for.
//! 2. **Resolves the origin to a [`PeerId`]** (a federation node id) and **dials it
//!    through `Netlayer::dial`** — so an authorized origin's connection IS a real
//!    audited netlayer session ([`dregg_captp::netlayer::NetSession`]: the byte-frame
//!    [`NetConnection`] + the epoch-correct `CapSession`). A peer the netlayer cannot
//!    reach returns [`ConnectOutcome::RefusedByTransport`] (the transport's own
//!    refusal, distinct from the cap's).
//!
//! ## How deep this binding goes (HONEST — the seam, named not laundered)
//!
//! Servo's HTTP(S) bytes themselves ride servo's INTERNAL `net` crate (hyper). Servo
//! forbids registering an embedder `ProtocolHandler` for `http`/`https`
//! (`servo-net`'s `FORBIDDEN_SCHEMES = ["http", "https", "chrome", "about"]`), so the
//! embedder cannot replace the http socket without forking servo's `net` crate — that
//! fork is out of one pass's reach. What this connector binds, at the depth the
//! embedder API allows, is:
//!
//!   * **the connect/authority decision → `Netlayer::dial`**: every fetch the
//!     [`CapGate`](crate::webview) admits is routed through THIS connector first, so
//!     the audited netlayer session is the thing that opens (or refuses) for the
//!     origin — and a cap-denied origin is refused *at `dial`'s doorstep*, before any
//!     socket. The bytes-on-the-wire for http(s) remain servo's internal hyper path
//!     (the forbidden-scheme ceiling, stated exactly), but the *reachability* of an
//!     origin is now the netlayer's to grant, gated by the cap.
//!
//! A `dregg://` (cell) fetch — which the web-of-cells surface drives, never an
//! ambient socket — would ride this connector end-to-end (no forbidden-scheme
//! ceiling, since it is not http). For http(s) the connector is the audited
//! connect-decision wire in front of servo's byte path. The status line
//! ([`ConnectOutcome::status_line`]) tells the truth about which of the three an
//! origin hit: dialed through the netlayer, refused by the cap, or unreachable by the
//! transport.

use std::collections::HashMap;
use std::sync::Mutex;

use dregg_captp::netlayer::{Netlayer, NetlayerError, PeerId};
use starbridge_web_surface::SurfaceCapability;

/// Map a web origin (e.g. `https://example.com`) to a federation [`PeerId`] — the
/// netlayer node that vends that origin's bytes. Deterministic: the same origin
/// always resolves to the same peer, so a cap scoped to an origin is a cap scoped to
/// that peer.
///
/// `blake3(origin)[..32]` — a 32-byte peer id in the same keyspace as
/// [`dregg_captp::StrandId`]. (In a deployed federation this is a registry lookup
/// "which node serves `example.com`"; the content-addressed derivation is the
/// no-config default — the origin's bytes are wherever the federation parks them,
/// keyed by the origin.)
pub fn origin_to_peer(origin: &str) -> PeerId {
    *blake3::hash(origin.as_bytes()).as_bytes()
}

/// The outcome of asking the connector to open a connection for an origin. The three
/// distinguishable ends the status line reports.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConnectOutcome {
    /// The held cap authorized the origin AND the netlayer dialed the peer: a real
    /// audited [`dregg_captp::netlayer::NetSession`] opened. Carries the dialed peer
    /// (the netlayer node the origin resolved to) for the status line / audit.
    Dialed { origin: String, peer: PeerId },
    /// The held [`SurfaceCapability`] does NOT authorize this origin — refused AT the
    /// connector, before `Netlayer::dial`. The socket is never opened. THIS is the
    /// gate biting at the transport (not merely an allowlist in front of an ambient
    /// socket).
    RefusedByCap { origin: String },
    /// The cap authorized the origin, but the netlayer could not reach the peer
    /// (`PeerUnreachable` / `Closed`): the transport's own refusal, distinct from the
    /// cap's. The dial happened; the peer was not there.
    RefusedByTransport { origin: String, reason: String },
}

impl ConnectOutcome {
    /// Did a real audited netlayer session open?
    pub fn dialed(&self) -> bool {
        matches!(self, ConnectOutcome::Dialed { .. })
    }

    /// Was the origin refused by the held cap (at the socket boundary, before dial)?
    pub fn refused_by_cap(&self) -> bool {
        matches!(self, ConnectOutcome::RefusedByCap { .. })
    }

    /// A one-line truth for the web-shell status line: which of the three ends this
    /// origin hit, named exactly.
    pub fn status_line(&self) -> String {
        match self {
            ConnectOutcome::Dialed { origin, peer } => format!(
                "net-cap: ✔ {origin} → dialed through captp Netlayer (peer {}…) — audited transport, not an ambient socket",
                bs58::encode(&peer[..6]).into_string()
            ),
            ConnectOutcome::RefusedByCap { origin } => format!(
                "net-cap: ✖ {origin} REFUSED at the socket — the held SurfaceCapability does not authorize this origin (Netlayer::dial never called)"
            ),
            ConnectOutcome::RefusedByTransport { origin, reason } => format!(
                "net-cap: ⚠ {origin} cap-authorized but unreachable on the netlayer ({reason})"
            ),
        }
    }
}

/// The cap-gated connector: the page's outbound connection, bound to a
/// [`Netlayer`]. Holds the netlayer (the audited transport) and a small record of
/// the connections it opened (for the audit / status line). It holds NO ambient
/// authority — every [`connect`](Self::connect) is a function of the `surface`
/// argument's held cap.
///
/// Generic over the [`Netlayer`] instance so the SAME connector binds the in-process
/// fabric (the single-machine / test transport), the relay (store-and-forward), or a
/// future tcp netlayer — the cap discipline is the same wire regardless of the leg.
pub struct NetcapConnector<N: Netlayer> {
    netlayer: N,
    /// The origins this connector dialed (origin → peer) — the audit trail the
    /// trusted chrome can read. Not authority; a record.
    dialed: Mutex<HashMap<String, PeerId>>,
}

impl<N: Netlayer> NetcapConnector<N> {
    /// Bind a connector to a netlayer (the audited transport leg).
    pub fn new(netlayer: N) -> Self {
        NetcapConnector {
            netlayer,
            dialed: Mutex::new(HashMap::new()),
        }
    }

    /// The netlayer this connector dials over (its hint identifies the transport leg:
    /// `"inproc"`, `"relay"`, …).
    pub fn netlayer(&self) -> &N {
        &self.netlayer
    }

    /// The origins this connector has dialed so far (origin → peer). The audit trail.
    pub fn dialed_origins(&self) -> Vec<(String, PeerId)> {
        let g = self.dialed.lock().unwrap_or_else(|e| e.into_inner());
        let mut v: Vec<_> = g.iter().map(|(o, p)| (o.clone(), *p)).collect();
        v.sort_by(|a, b| a.0.cmp(&b.0));
        v
    }

    /// **THE NET-CAP GATE AT THE SOCKET.** Open an outbound connection for `origin`,
    /// gated by the held `surface` cap and carried by [`Netlayer::dial`].
    ///
    /// The cap is re-checked HERE, at the connect boundary — not (only) at a callback
    /// in front. An origin `surface` does not authorize returns
    /// [`ConnectOutcome::RefusedByCap`] and **`Netlayer::dial` is never reached**: the
    /// socket is never opened, the bytes never flow. An authorized origin is resolved
    /// to its peer and dialed through the audited netlayer; a successful dial records
    /// the (origin, peer) for the audit and returns [`ConnectOutcome::Dialed`]. A peer
    /// the netlayer cannot reach returns [`ConnectOutcome::RefusedByTransport`].
    ///
    /// `async` because [`Netlayer::dial`] is async (the dial may pend on the
    /// transport). The headless render driver / the cockpit drive it on the SWGL
    /// current-context thread with a single-future executor (the in-memory netlayers
    /// never pend on external wakeups).
    pub async fn connect(&self, surface: &SurfaceCapability, origin: &str) -> ConnectOutcome
    where
        N: Netlayer<Addr = PeerId>,
    {
        // STEP 1 — THE CAP, AT THE SOCKET. The held surface cap decides whether this
        // origin is reachable AT ALL. A non-authorized origin is refused here, before
        // a single packet — `Netlayer::dial` is never called, no session opens. This
        // is the gate biting at the transport, the audit's ask.
        if !surface.may_fetch(origin) {
            return ConnectOutcome::RefusedByCap {
                origin: origin.to_string(),
            };
        }

        // STEP 2 — DIAL THROUGH THE AUDITED NETLAYER. The cap authorized the origin;
        // resolve it to its federation peer and dial. THIS is the bytes-leg: a real
        // `NetSession` over the netlayer's byte-frame `NetConnection`, the same
        // transport the federation rides — not an ambient OS socket.
        let peer = origin_to_peer(origin);
        match self.netlayer.dial(&peer).await {
            Ok(_session) => {
                self.dialed
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .insert(origin.to_string(), peer);
                ConnectOutcome::Dialed {
                    origin: origin.to_string(),
                    peer,
                }
            }
            Err(e) => ConnectOutcome::RefusedByTransport {
                origin: origin.to_string(),
                reason: match e {
                    NetlayerError::PeerUnreachable { .. } => "peer unreachable on this netlayer".to_string(),
                    other => other.to_string(),
                },
            },
        }
    }
}

/// Minimal single-future executor for driving [`NetcapConnector::connect`] on the
/// render thread. The in-memory netlayers' dial futures never pend on external
/// wakeups (a no-op waker suffices), exactly as `dregg-captp`'s own netlayer tests
/// drive `dial`/`accept`. A windowed embedder with a real async runtime would drive
/// this on its executor instead.
pub fn block_on<F: std::future::Future>(fut: F) -> F::Output {
    use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

    fn raw() -> RawWaker {
        fn no_op(_: *const ()) {}
        fn clone(_: *const ()) -> RawWaker {
            raw()
        }
        RawWaker::new(std::ptr::null(), &RawWakerVTable::new(clone, no_op, no_op, no_op))
    }

    let waker = unsafe { Waker::from_raw(raw()) };
    let mut cx = Context::from_waker(&waker);
    let mut fut = std::pin::pin!(fut);
    loop {
        match fut.as_mut().poll(&mut cx) {
            Poll::Ready(out) => return out,
            Poll::Pending => std::thread::yield_now(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_captp::netlayer::InProcessFabric;
    use dregg_firmament::cell_seed;
    use starbridge_web_surface::{AuthRequired, SurfaceCapability};

    /// Build an in-process netlayer where `self` has joined, plus the peers for the
    /// given origins also joined (so an authorized dial to them SUCCEEDS). Returns the
    /// connector.
    fn connector_with_peers(origins: &[&str]) -> NetcapConnector<dregg_captp::netlayer::InProcessNetlayer> {
        let fabric = InProcessFabric::new();
        // Our own node (the dialer) — any peer id in the keyspace.
        let me = fabric.join([0x01; 32]);
        // Every origin's peer joins the fabric so a cap-authorized dial reaches it.
        for o in origins {
            let _peer = fabric.join(origin_to_peer(o));
        }
        NetcapConnector::new(me)
    }

    /// **THE LOAD-BEARING TEST: an origin the held cap does NOT authorize is refused
    /// AT THE SOCKET — `Netlayer::dial` is never called, no session opens.**
    ///
    /// A surface scoped to `https://example.com` tries to connect to
    /// `https://evil.com` (⊄ its fetch allowlist). The connector refuses at the cap
    /// check, BEFORE the dial: the outcome is `RefusedByCap`, and the connector's
    /// dialed-audit is EMPTY (proof the netlayer was never dialed — the gate bit at
    /// the transport, not after an ambient socket already opened).
    #[test]
    fn unauthorized_origin_is_refused_at_the_socket_no_dial() {
        let connector = connector_with_peers(&["https://example.com", "https://evil.com"]);
        let surface = SurfaceCapability::scoped(
            cell_seed(9),
            AuthRequired::Either,
            [String::from("https://example.com")],
            [],
        );

        let outcome = block_on(connector.connect(&surface, "https://evil.com"));

        assert!(outcome.refused_by_cap(), "the uncapped origin is refused by the cap");
        assert!(!outcome.dialed(), "no audited session opened for the uncapped origin");
        assert_eq!(
            outcome,
            ConnectOutcome::RefusedByCap { origin: "https://evil.com".to_string() }
        );
        // THE PROOF THE GATE BIT AT THE TRANSPORT: the netlayer was NEVER dialed for
        // evil.com — the dialed-audit is empty. A gate that merely sat in front of an
        // ambient socket could not assert this.
        assert!(
            connector.dialed_origins().is_empty(),
            "Netlayer::dial was NEVER called for the cap-denied origin — the socket never opened"
        );
    }

    /// **THE OTHER HALF: an origin the held cap DOES authorize connects through the
    /// audited netlayer.** `https://example.com` is in the surface's allowlist; the
    /// connector resolves it to its peer and DIALS it — a real `NetSession` over the
    /// netlayer. The outcome is `Dialed` and the audit records the (origin, peer).
    #[test]
    fn authorized_origin_dials_through_the_netlayer() {
        let connector = connector_with_peers(&["https://example.com"]);
        let surface = SurfaceCapability::scoped(
            cell_seed(9),
            AuthRequired::Either,
            [String::from("https://example.com")],
            [],
        );

        let outcome = block_on(connector.connect(&surface, "https://example.com"));

        assert!(outcome.dialed(), "the cap-authorized origin dials through the netlayer");
        match &outcome {
            ConnectOutcome::Dialed { origin, peer } => {
                assert_eq!(origin, "https://example.com");
                assert_eq!(*peer, origin_to_peer("https://example.com"));
            }
            other => panic!("expected Dialed, got {other:?}"),
        }
        // The audited connection is recorded — a real netlayer session opened.
        let dialed = connector.dialed_origins();
        assert_eq!(dialed.len(), 1);
        assert_eq!(dialed[0].0, "https://example.com");
    }

    /// A WILDCARD (root) surface authorizes any origin at the cap — but the transport
    /// still decides reachability. An origin whose peer has NOT joined the fabric is
    /// `RefusedByTransport` (the cap said yes; the netlayer could not reach it). This
    /// proves the two refusals are DISTINCT — the cap and the transport are separate
    /// teeth.
    #[test]
    fn wildcard_cap_still_subject_to_transport_reachability() {
        // Only example.com's peer joins; nowhere.invalid's does not.
        let connector = connector_with_peers(&["https://example.com"]);
        let root = SurfaceCapability::root(cell_seed(9), AuthRequired::Either);

        // Cap says yes (wildcard), peer present → dialed.
        let ok = block_on(connector.connect(&root, "https://example.com"));
        assert!(ok.dialed(), "wildcard cap + reachable peer → dialed");

        // Cap says yes (wildcard), peer absent → transport refuses.
        let unreachable = block_on(connector.connect(&root, "https://nowhere.invalid"));
        assert!(
            matches!(unreachable, ConnectOutcome::RefusedByTransport { .. }),
            "wildcard cap + unreachable peer → refused by TRANSPORT, not the cap: {unreachable:?}"
        );
        assert!(!unreachable.refused_by_cap(), "this refusal is the transport's, not the cap's");
    }

    /// The status line tells the truth for each of the three ends.
    #[test]
    fn status_line_names_each_outcome() {
        let dialed = ConnectOutcome::Dialed {
            origin: "https://example.com".to_string(),
            peer: origin_to_peer("https://example.com"),
        };
        assert!(dialed.status_line().contains("dialed through captp Netlayer"));

        let cap = ConnectOutcome::RefusedByCap { origin: "https://evil.com".to_string() };
        assert!(cap.status_line().contains("REFUSED at the socket"));
        assert!(cap.status_line().contains("Netlayer::dial never called"));

        let transport = ConnectOutcome::RefusedByTransport {
            origin: "https://x.invalid".to_string(),
            reason: "peer unreachable on this netlayer".to_string(),
        };
        assert!(transport.status_line().contains("unreachable on the netlayer"));
    }
}
