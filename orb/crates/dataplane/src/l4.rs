//! The layer-4 (raw TCP / UDP) passthrough listener: the running host shell of
//! the proven `Reactor.L4` forwarding model.
//!
//! Every other listener in this host parses HTTP and drives the proven request
//! pipeline. An L4 listener does not: it accepts a connection (or a datagram),
//! asks the load balancer for an upstream, dials it, and moves bytes VERBATIM in
//! both directions until each side finishes — the `mode tcp` / `stream {}`
//! posture of a general-purpose proxy, for protocols the HTTP engine has no
//! business reading (databases, message queues, TLS-passthrough SNI backends,
//! bespoke wire protocols).
//!
//! It keeps the sans-IO split intact, exactly as the reverse-proxy hop does:
//!
//! * the CORE decides WHICH upstream — the proven `Reactor.ProxyDial.pick`
//!   (`Proxy.selectChain` over the live-health-masked fleet, honouring health
//!   ejection, the circuit breaker, and per-source affinity), exported as
//!   `drorb_proxy_pick` and crossed on the runtime-owner serve thread via
//!   [`crate::serve::Seam::ProxyPick`]. This module never selects a backend.
//! * the HOST owns the sockets and the byte splice — [`splice`], a blocking
//!   two-way pump run on the caller's connection thread so a slow peer never
//!   stalls the serve thread. On Linux each direction moves kernel-side via
//!   `splice(2)` (socket → pipe → socket; the payload never enters this
//!   process), with the portable userspace copy as the fallback.
//!
//! The proven model this shell realises is `Reactor.L4`: `stepTcp` (the TCP
//! splice state machine) and `udpStep` (the datagram forwarder), whose
//! conservation theorems (`session_up_exact`, `runTcp_down_faithful`,
//! `udpRun_faithful`) prove bytes-in = bytes-out, verbatim, in order — and whose
//! `deployed_accept_dials_pick` pins that the upstream this shell dials is exactly
//! the `drorb_proxy_pick` backend.
//!
//! The upstream fleet is the same one the reverse-proxy lane configures
//! (`DRORB_PROXY_BACKENDS`, id→socket), so the L4 pick maps the proven backend id
//! to the same configured socket. The listener bind is `DRORB_L4_LISTEN` (TCP)
//! and `DRORB_L4_UDP` (UDP); when unset the L4 subsystem does not bind.

use std::io::copy;
use std::net::{Shutdown, SocketAddr, TcpListener, TcpStream, UdpSocket};
use std::sync::Arc;
use std::sync::atomic::Ordering;
use std::sync::mpsc::{Receiver, Sender};
use std::time::Duration;

use crate::pool::PooledBuf;
use crate::proxy_dial::Fleet;
use crate::serve::{Seam, ServeGateway};

/// How long to wait dialling the chosen upstream before giving up.
const DIAL_TIMEOUT: Duration = Duration::from_secs(5);

/// The per-source affinity key an L4 flow hashes to a backend: the client's IP,
/// so one source pins to one upstream across connections (the proven rendezvous
/// policy makes the pick a pure function of this key). No HTTP is parsed, so
/// there is no cookie/target to key on — the source address is the flow identity.
pub(crate) fn affinity_key(peer: Option<SocketAddr>) -> Vec<u8> {
    peer.map(|a| a.ip().to_string().into_bytes())
        .unwrap_or_default()
}

/// Cross the proven `drorb_proxy_pick` seam on the runtime-owner serve thread:
/// byte 0 = the live health/breaker mask, bytes 1.. = the affinity key; the
/// output is the decimal-ASCII chosen backend id, or empty when no backend is
/// eligible (⇒ `None`, the host dials nothing and closes). Identical marshalling
/// to the reverse-proxy lane — the same export, the same single-owner discipline.
pub(crate) fn pick_via_seam(
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

/// The blocking two-way byte splice: move bytes verbatim between `client` and
/// `upstream` in both directions until each side finishes, honouring half-close
/// per direction (an EOF on one lane shuts down the write half of the other, so
/// the peer sees the close, while the opposite lane keeps draining). This is the
/// host realisation of `Reactor.L4.stepTcp`'s `established`/`drainDown`/`drainUp`
/// splice: every client chunk goes to the upstream unchanged, every upstream
/// chunk back to the client unchanged, order preserved.
fn splice(client: TcpStream, upstream: TcpStream) {
    let (mut c_read, mut c_write) = match (client.try_clone(), client) {
        (Ok(r), w) => (r, w),
        (Err(_), w) => {
            let _ = w.shutdown(Shutdown::Both);
            return;
        }
    };
    let (mut u_read, mut u_write) = match (upstream.try_clone(), upstream) {
        (Ok(r), w) => (r, w),
        (Err(_), w) => {
            let _ = w.shutdown(Shutdown::Both);
            let _ = c_write.shutdown(Shutdown::Both);
            return;
        }
    };

    // client → upstream on a helper thread; upstream → client on this one.
    let up = std::thread::spawn(move || {
        pump_dir(&mut c_read, &mut u_write);
        let _ = u_write.shutdown(Shutdown::Write); // client EOF: half-close upstream
    });
    pump_dir(&mut u_read, &mut c_write);
    let _ = c_write.shutdown(Shutdown::Write); // upstream EOF: half-close client
    let _ = up.join();
}

/// One direction of the verbatim pump, until EOF on `from`. On Linux the bytes
/// move kernel-side — `from` socket → pipe → `to` socket via `splice(2)`, never
/// entering this process — with the portable userspace `io::copy` as the
/// fallback when the relay cannot run at all (nothing moved, so the copy starts
/// from byte 0). Byte semantics are identical either way: verbatim, in order,
/// until `from` closes or the direction fails.
fn pump_dir(from: &mut TcpStream, to: &mut TcpStream) {
    #[cfg(target_os = "linux")]
    {
        if crate::proxy_dial::splice_to_eof(from, to) {
            return;
        }
    }
    let _ = copy(from, to);
}

/// Handle one accepted L4 connection: choose the upstream via `pick` (the proven
/// `drorb_proxy_pick`), dial it, and splice. On no eligible backend, or a dial
/// failure, the client is closed and nothing is dialled — the host meaning of
/// `Reactor.L4.accept_none_closes`. The backend is ALWAYS the pick's; this
/// function never selects (the `pick` closure is the only chooser).
pub fn handle_conn<P>(client: TcpStream, fleet: &Fleet, pick: P)
where
    P: Fn(u8, &[u8]) -> Option<u32>,
{
    let key = affinity_key(client.peer_addr().ok());
    let id = match pick(fleet.mask(), &key) {
        Some(id) => id,
        None => {
            let _ = client.shutdown(Shutdown::Both); // no healthy upstream
            return;
        }
    };
    let addr = match fleet.addr(id) {
        Some(a) => a,
        None => {
            let _ = client.shutdown(Shutdown::Both);
            return;
        }
    };
    let upstream = match TcpStream::connect_timeout(&addr, DIAL_TIMEOUT) {
        Ok(u) => u,
        Err(_) => {
            let _ = client.shutdown(Shutdown::Both);
            return;
        }
    };
    let _ = client.set_nodelay(true);
    let _ = upstream.set_nodelay(true);
    splice(client, upstream);
}

/// Bind `listen_addr` as a raw-TCP passthrough listener and forward every
/// connection to the proven-chosen upstream until shutdown. Non-blocking accept
/// so the SIGINT flag is observed promptly; a thread per connection runs the
/// splice (and its own reusable reply channel for the pick seam).
/// Bind `listen_addr` as a raw-TCP passthrough listener. On Linux the flows are
/// driven by the single-shard `io_uring` SPLICE reactor ([`crate::l4_uring`]) —
/// one thread, kernel-side splice, the proven lockstep fill/drain — and this
/// function only falls through to the portable blocking pump below if the ring
/// could not be initialised. Off Linux the blocking thread-per-connection pump is
/// the path.
pub fn run(listen_addr: &str, fleet: Arc<Fleet>, gw: ServeGateway) {
    #[cfg(target_os = "linux")]
    {
        if crate::l4_uring::run(listen_addr, Arc::clone(&fleet), gw.clone()) {
            return;
        }
        eprintln!("dataplane: L4 falling back to the portable blocking splice pump");
    }
    run_threaded(listen_addr, fleet, gw);
}

/// The portable blocking realisation: non-blocking accept, a thread per connection
/// running the two-way blocking splice. The Linux fallback and the sole path on
/// every other platform.
fn run_threaded(listen_addr: &str, fleet: Arc<Fleet>, gw: ServeGateway) {
    let listener = match TcpListener::bind(listen_addr) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("dataplane: L4 TCP bind {listen_addr} failed: {e}");
            return;
        }
    };
    let local = listener
        .local_addr()
        .map(|a| a.to_string())
        .unwrap_or_else(|_| listen_addr.to_string());
    if listener.set_nonblocking(true).is_err() {
        eprintln!("dataplane: L4 TCP {local}: cannot set non-blocking; not serving");
        return;
    }
    eprintln!(
        "dataplane: listening on {local} (L4 raw-TCP passthrough; upstream = proven drorb_proxy_pick, bytes spliced verbatim)"
    );

    loop {
        if crate::SHUTDOWN.load(Ordering::SeqCst) {
            eprintln!("dataplane: SIGINT — stopping L4 accept loop");
            return;
        }
        match listener.accept() {
            Ok((stream, _peer)) => {
                let fleet = Arc::clone(&fleet);
                let gw = gw.clone();
                let _ = std::thread::Builder::new()
                    .name("drorb-l4".into())
                    .spawn(move || {
                        let (reply_tx, reply_rx) = std::sync::mpsc::channel::<PooledBuf>();
                        handle_conn(stream, &fleet, |mask, key| {
                            pick_via_seam(mask, key, &gw, &reply_tx, &reply_rx)
                        });
                    });
            }
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                std::thread::sleep(Duration::from_millis(20));
            }
            Err(_) => std::thread::sleep(Duration::from_millis(20)),
        }
    }
}

/// One UDP datagram's forward: choose the upstream via `pick`, send the datagram
/// to it verbatim from an ephemeral socket, wait briefly for the reply, and send
/// it back to the client — boundary-preserved, payload-verbatim (the host
/// realisation of `Reactor.L4.udpStep` / `udpRun_faithful`). Drops (sends
/// nothing) when no backend is eligible. Returns the reply bytes it relayed, for
/// logging.
fn forward_datagram<P>(
    client_sock: &UdpSocket,
    peer: SocketAddr,
    data: &[u8],
    fleet: &Fleet,
    pick: P,
) -> Option<usize>
where
    P: Fn(u8, &[u8]) -> Option<u32>,
{
    let key = affinity_key(Some(peer));
    let id = pick(fleet.mask(), &key)?; // no backend ⇒ drop, never misroute
    let addr = fleet.addr(id)?;
    let ephemeral = UdpSocket::bind("0.0.0.0:0").ok()?;
    ephemeral.set_read_timeout(Some(DIAL_TIMEOUT)).ok();
    ephemeral.send_to(data, addr).ok()?;
    let mut buf = [0u8; 65536];
    let (n, _from) = ephemeral.recv_from(&mut buf).ok()?;
    client_sock.send_to(&buf[..n], peer).ok()?;
    Some(n)
}

/// Bind `listen_addr` as a UDP datagram passthrough listener and forward every
/// datagram to the proven-chosen upstream until shutdown. Blocking recv with a
/// short timeout so the SIGINT flag is observed promptly.
pub fn run_udp(listen_addr: &str, fleet: Arc<Fleet>, gw: ServeGateway) {
    let sock = match UdpSocket::bind(listen_addr) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("dataplane: L4 UDP bind {listen_addr} failed: {e}");
            return;
        }
    };
    let local = sock
        .local_addr()
        .map(|a| a.to_string())
        .unwrap_or_else(|_| listen_addr.to_string());
    let _ = sock.set_read_timeout(Some(Duration::from_millis(200)));
    eprintln!(
        "dataplane: listening on {local}/udp (L4 datagram passthrough; upstream = proven drorb_proxy_pick, payload verbatim)"
    );

    let (reply_tx, reply_rx) = std::sync::mpsc::channel::<PooledBuf>();
    let mut buf = [0u8; 65536];
    loop {
        if crate::SHUTDOWN.load(Ordering::SeqCst) {
            return;
        }
        let (n, peer) = match sock.recv_from(&mut buf) {
            Ok(x) => x,
            Err(e)
                if e.kind() == std::io::ErrorKind::WouldBlock
                    || e.kind() == std::io::ErrorKind::TimedOut =>
            {
                continue;
            }
            Err(_) => continue,
        };
        let data = buf[..n].to_vec();
        forward_datagram(&sock, peer, &data, &fleet, |mask, key| {
            pick_via_seam(mask, key, &gw, &reply_tx, &reply_rx)
        });
    }
}
