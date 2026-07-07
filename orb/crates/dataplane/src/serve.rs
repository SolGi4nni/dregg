//! The Lean seam: boot the proven runtime and cross it, once per request.
//!
//! Every crossing is one call to the exported `drorb_serve`
//! (`ByteArray -> ByteArray`), the same proven pipeline the shipped binaries
//! run. The bytes read off the wire go in unchanged and the proven response
//! bytes come back unchanged; the host decides nothing about a request's
//! meaning.
//!
//! ## Concurrency model
//!
//! The Lean runtime is a process-global singleton: `initialize_Dataplane`
//! installs the module's top-level constants once, and there is no way to stand
//! up N independent runtimes in one process. So a per-worker runtime is not an
//! option, and rather than rely on the compiled serve being safe to call from
//! many threads (the closure inc/dec's runtime objects and the small allocator
//! keeps thread-local state), the host confines every seam crossing to a single
//! dedicated thread that owns the runtime. That thread runs [`lean_boot`] and is
//! the only thread that ever calls `drorb_serve`; correctness never depends on
//! the compiled serve being reentrant.
//!
//! IO concurrency lives elsewhere (the event loops in `blocking`/`uring`): many
//! connections read and write in parallel and funnel completed requests to this
//! one serve thread over a channel. The serve computation itself is serialized
//! on the runtime-owner thread — the deliberate trade, and the one shared
//! resource in an otherwise share-nothing design (see `SINGLE-OWNER` note in
//! [`spawn_serve_thread`]).

use std::net::IpAddr;
use std::slice;
use std::sync::mpsc::{channel, Receiver, Sender};
use std::sync::Arc;

use crate::pool::{BufferPool, PooledBuf};

/// Opaque Lean heap object. We only ever hold `*mut LeanObject` and hand it
/// straight back across the FFI; its layout is the runtime's concern.
#[repr(C)]
struct LeanObject {
    _private: [u8; 0],
}

unsafe extern "C" {
    // Real exported runtime + module symbols (libleanshared / the drorb archive).
    fn lean_initialize_runtime_module();
    fn lean_io_mark_end_initialization();
    fn initialize_Dataplane(builtin: u8, world: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve] drorbServe : ByteArray -> ByteArray` — the proven
    /// pipeline (TCP byte stream: HTTP/1.1 + h2c fork to the real H2 engine).
    /// Consumes its argument, returns an owned ByteArray.
    fn drorb_serve(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_metered] drorbServeMetered : ByteArray -> UInt64 ->
    /// ByteArray -> ByteArray` — the same deployed HTTP/1.1 fold as `drorb_serve`,
    /// but the host supplies the connection context the two metered gates read:
    /// `peer` (the client address, family-tagged bit-encoded per
    /// `Reactor.Stage.IpFilter.encodeAddr`) feeds the real IP-filter deny gate, and
    /// `seq` (the 0-based per-connection request index) feeds the real rate token
    /// bucket. Consumes both ByteArray arguments; returns an owned ByteArray. The C
    /// ABI passes `seq` as an unboxed `uint64_t` (leanc lowering).
    fn drorb_serve_metered(
        peer: *mut LeanObject,
        seq: u64,
        input: *mut LeanObject,
    ) -> *mut LeanObject;
    /// `@[export drorb_serve_ws_frame]` (Dataplane.Multi) — one inbound masked
    /// WebSocket frame's bytes in; the proven `wsFeedFn`/`wsEncodeFn` echo bytes
    /// out. Same `ByteArray -> ByteArray` ABI as `drorb_serve`.
    fn drorb_serve_ws_frame(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_datagram]` (Dataplane.Multi) — one UDP datagram (a
    /// QUIC Initial packet) in; verified EverCrypt decrypt → proven H3 dispatch →
    /// served response bytes out (empty on any parse/AEAD-auth failure).
    fn drorb_serve_datagram(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_upgrade_gate]` (Dataplane.Multi) — a protocol-upgrade
    /// REQUEST's bytes in; the deployed `/admin` JWT auth gate runs on it. Returns
    /// the serialized 401 bytes if the upgrade targets a protected path with no /
    /// invalid credentials (the host writes them instead of 101), or EMPTY bytes
    /// if the upgrade is authorized (the host completes the RFC 6455 handshake).
    fn drorb_upgrade_gate(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_proxy_pick]` (Reactor.ProxyDial) — the proven reverse-proxy
    /// backend pick: `Proxy.selectChain` over the live-health-masked fleet,
    /// honouring health ejection, the circuit breaker, and sticky affinity. Input
    /// byte 0 = the health/breaker mask (bit `i` ⇒ backend `i` up), bytes 1.. =
    /// the sticky-affinity key; output = the decimal-ASCII chosen backend id, or
    /// EMPTY when no backend is eligible. Same `ByteArray -> ByteArray` ABI as
    /// `drorb_serve`; crossed only on the runtime-owner thread, then the host
    /// (`proxy_hook`/`proxy_dial`) dials the chosen backend off this thread.
    fn drorb_proxy_pick(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_step]` (Reactor.ServeStep) — the effect/continuation
    /// serve STEP: input byte 0 = the live health mask, bytes 1.. = the request;
    /// output is the encoded `Step` (byte 0 = tag: `0` DONE + response bytes, `1`
    /// YIELD proxyDial + backend-id byte + forward-request bytes). Same `ByteArray
    /// -> ByteArray` ABI, crossed on the runtime-owner thread.
    fn drorb_serve_step(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_resume]` (Reactor.ServeStep) — resume the serve after
    /// the shell executed a yielded effect. Input frames the ORIGINAL request plus
    /// the effect result as `mask :: reqLen(4, big-endian) :: request :: result`;
    /// output is the resumed response bytes. Same ABI, same single-owner thread.
    fn drorb_serve_resume(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_step_cfg]` (Dataplane) — the config-driven serve STEP:
    /// input byte 0 = the deployment LB selector (`DRORB_LB_POLICY`), byte 1 = the
    /// health mask, bytes 2.. = the request. The proxy branch dials the backend the
    /// CONFIG-declared LB policy selects; selector `0` reproduces `drorb_serve_step`.
    fn drorb_serve_step_cfg(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_resume_cfg]` (Dataplane) — resume the config-driven
    /// serve: input byte 0 = the deployment LB selector, then the ORIGINAL
    /// `mask :: reqLen(4 BE) :: request :: result` frame. Replays
    /// `serveStepWith (deploymentDialChain sel)` so the resumed continuation matches
    /// the config chain the step used.
    fn drorb_serve_resume_cfg(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_l4_bind]` (Dataplane) — the layer-4 accept-surface
    /// projection: input byte 0 = the deployment selector; output = the newline-
    /// joined `bind\tpool\tmode\tid,id,…` lines the config DECLARES
    /// (`DeploymentConfig.l4Listeners`), empty for the default deployment.
    fn drorb_l4_bind(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_deployment_of_config]` (Dataplane) — parse an ARBITRARY
    /// textual `DeploymentConfig` (UTF-8 bytes in) into the running projections:
    /// output is `lb\t<policyByte>` then one `bind\tpool\tmode\tid,id,…` line per
    /// declared L4 listener, or EMPTY on a parse failure (the host then runs the
    /// byte-identical default). `Dsl.Config.parseChars` + `denoteOn defaultDeployment`.
    fn drorb_deployment_of_config(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_step_pol]` (Dataplane) — the effect/continuation STEP
    /// dialed by a config LB-policy byte: input byte 0 = the LB-policy byte (from
    /// `drorb_deployment_of_config`), byte 1 = the health mask, bytes 2.. = the
    /// request. The proxy branch dials the backend the parsed config's declared LB
    /// policy selects (`Dsl.Config.dialChainOfByte`).
    fn drorb_serve_step_pol(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_resume_pol]` (Dataplane) — resume the config-policy
    /// STEP: input byte 0 = the same LB-policy byte, then the ORIGINAL
    /// `mask :: reqLen(4 BE) :: request :: result` frame. Replays
    /// `serveStepWith (dialChainOfByte pol)` so the resumed continuation matches.
    fn drorb_serve_resume_pol(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_cfg]` (Dataplane) — serve one request under an operator
    /// config's ROUTE TABLE. Input framing `cfgLen(4 BE) :: configBytes ::
    /// requestBytes`; the proven `Dsl.Config.parseChars` parses the config and, when
    /// it declares routes, serves the request through `servePipelineOf (denoteOn
    /// defaultDeployment pc)` — the same fourteen-stage fold over the config's route
    /// table (redirect/respond/static answered directly). A parse failure / routeless
    /// config serves the byte-identical default. Same `ByteArray -> ByteArray` ABI.
    fn drorb_serve_cfg(input: *mut LeanObject) -> *mut LeanObject;

    /// `@[export drorb_tls_serve] Dataplane.Tls.drorbTlsServe : UInt32 ->
    /// ByteArray^8 -> IO Unit` — run one accepted TCP connection's whole VERIFIED
    /// TLS 1.3 server in-process: the RFC 8446 handshake
    /// (`TlsHandshake.serverStep`, presenting the certificate the proven
    /// `chooseCert` selects from the pool per the client's
    /// `signature_algorithms`), then the established record layer
    /// (`TlsHandshake.appStep`) serving each decrypted request through the SAME
    /// proven `drorb_serve` and sealing the response. `fd` is the connected
    /// socket (unboxed `uint32_t`), consumed and closed by the Lean side. The
    /// certificate material is owned ByteArrays it consumes: the Ed25519 default
    /// (`cert` DER end-entity, `seed` 32-byte RFC 8032 signing seed), then the
    /// optional ECDSA-P256 leaf (`ecdsa_cert` DER, `ecdsa_priv` 32-byte raw
    /// scalar) and RSA-PSS-2048 leaf (`rsa_cert` DER, `rsa_n`/`rsa_e`/`rsa_d`
    /// big-endian modulus / public / private exponent). An EMPTY ByteArray for a
    /// pool member means "absent". Returns the IO result object; crossed only on
    /// the runtime-owner thread, and BLOCKS it for the connection's lifetime (see
    /// `run_tls_conn`).
    fn drorb_tls_serve(
        fd: u32,
        cert: *mut LeanObject,
        seed: *mut LeanObject,
        ecdsa_cert: *mut LeanObject,
        ecdsa_priv: *mut LeanObject,
        rsa_cert: *mut LeanObject,
        rsa_n: *mut LeanObject,
        rsa_e: *mut LeanObject,
        rsa_d: *mut LeanObject,
        world: *mut LeanObject,
    ) -> *mut LeanObject;

    // Byte-marshalling adapter (ffi/drorb_ffi.c) for lean.h's inline sarray API.
    fn drorb_sarray_of_bytes(p: *const u8, n: usize) -> *mut LeanObject;
    fn drorb_sarray_len(o: *mut LeanObject) -> usize;
    fn drorb_sarray_ptr(o: *mut LeanObject) -> *const u8;
    fn drorb_obj_dec(o: *mut LeanObject);
    fn drorb_io_world() -> *mut LeanObject;
    fn drorb_io_ok(o: *mut LeanObject) -> i32;
}

/// Which proven seam a job crosses. All three are exported `ByteArray ->
/// ByteArray` functions with the SAME marshalling; they differ only in which
/// proven pipeline runs on the bytes. Every one is called on the single
/// runtime-owner thread.
#[derive(Clone, Copy, PartialEq)]
pub enum Seam {
    /// `drorb_serve` — the TCP byte-stream fork (HTTP/1.1 + h2c → real H2).
    Http,
    /// `drorb_serve_ws_frame` — the proven WebSocket frame engine (echo).
    WsFrame,
    /// `drorb_serve_datagram` — QUIC-Initial decrypt → proven H3 dispatch.
    Datagram,
    /// `drorb_upgrade_gate` — the deployed `/admin` JWT auth gate on a protocol
    /// upgrade request (401 bytes if refused, empty if authorized).
    UpgradeGate,
    /// `drorb_proxy_pick` — the proven reverse-proxy backend pick
    /// (`Reactor.ProxyDial`): `(mask, key)` bytes in, the chosen backend id (decimal
    /// ASCII) out, or empty when no backend is eligible.
    ProxyPick,
    /// `drorb_serve_step` — the effect/continuation serve STEP (`Reactor.ServeStep`):
    /// `mask :: request` in, the encoded `Step` out.
    ServeStep,
    /// `drorb_serve_resume` — resume the serve after a yielded effect: the framed
    /// `mask :: reqLen :: request :: result` in, the resumed response bytes out.
    ServeResume,
    /// `drorb_serve_step_cfg` — the config-driven serve STEP: `sel :: mask ::
    /// request` in, the encoded `Step` out (config LB policy decides the backend).
    ServeStepCfg,
    /// `drorb_serve_resume_cfg` — resume the config-driven serve: `sel :: mask ::
    /// reqLen :: request :: result` in, the resumed response bytes out.
    ServeResumeCfg,
    /// `drorb_l4_bind` — the layer-4 accept-surface projection: `sel` in, the
    /// config's declared L4 bindings (newline/tab-joined) out.
    L4Bind,
    /// `drorb_deployment_of_config` — parse an arbitrary textual config: the config
    /// UTF-8 bytes in, `lb\t<byte>` + the declared L4 lines out (empty on failure).
    DeploymentOfConfig,
    /// `drorb_serve_step_pol` — the config-policy serve STEP: `pol :: mask ::
    /// request` in, the encoded `Step` out (the config LB byte decides the backend).
    ServeStepPol,
    /// `drorb_serve_resume_pol` — resume the config-policy serve: `pol :: mask ::
    /// reqLen :: request :: result` in, the resumed response bytes out.
    ServeResumePol,
    /// `drorb_serve_cfg` — serve under a config's route table: `cfgLen(4 BE) ::
    /// config :: request` in, the served response bytes out.
    ServeCfg,
}

impl Seam {
    /// The exported entry for this seam.
    ///
    /// SAFETY: each is a real `@[export] ByteArray -> ByteArray` symbol in the
    /// drorb archive; the returned pointer is only ever invoked from the
    /// runtime-owner thread by [`serve_into`], with the same marshalling.
    fn entry(self) -> unsafe extern "C" fn(*mut LeanObject) -> *mut LeanObject {
        match self {
            Seam::Http => drorb_serve,
            Seam::WsFrame => drorb_serve_ws_frame,
            Seam::Datagram => drorb_serve_datagram,
            Seam::UpgradeGate => drorb_upgrade_gate,
            Seam::ProxyPick => drorb_proxy_pick,
            Seam::ServeStep => drorb_serve_step,
            Seam::ServeResume => drorb_serve_resume,
            Seam::ServeStepCfg => drorb_serve_step_cfg,
            Seam::ServeResumeCfg => drorb_serve_resume_cfg,
            Seam::L4Bind => drorb_l4_bind,
            Seam::DeploymentOfConfig => drorb_deployment_of_config,
            Seam::ServeStepPol => drorb_serve_step_pol,
            Seam::ServeResumePol => drorb_serve_resume_pol,
            Seam::ServeCfg => drorb_serve_cfg,
        }
    }
}

/// Bring up the Lean runtime and initialize the proven module. Must run once,
/// before any `drorb_serve` call, on the thread that will own the runtime.
fn lean_boot() {
    // SAFETY: the exact runtime-init sequence leanc emits for a module main:
    // init the runtime, run the module initializer once against a fresh IO
    // world, check it succeeded, drop the result, then mark init end. Called
    // exactly once, on the runtime-owner thread, before any `drorb_serve`.
    unsafe {
        lean_initialize_runtime_module();
        let res = initialize_Dataplane(1, drorb_io_world());
        if drorb_io_ok(res) == 0 {
            panic!("initialize_Dataplane returned an IO error");
        }
        drorb_obj_dec(res);
        lean_io_mark_end_initialization();
    }
}

/// The one and only seam crossing: run the proven pipeline over `req` and
/// append the response bytes into `out` (cleared first). `out` is a pooled
/// buffer, so no response `Vec` is allocated per request on the host side.
/// Only ever invoked from the runtime-owning serve thread.
fn serve_into(req: &[u8], seam: Seam, out: &mut Vec<u8>) {
    // SAFETY: `drorb_sarray_of_bytes` copies `req` into a fresh owned Lean
    // ByteArray (the runtime's per-call input alloc); the seam entry consumes it
    // and returns an owned ByteArray whose bytes we copy out before dropping our
    // reference with `drorb_obj_dec`. Pointers from `drorb_sarray_ptr` are valid
    // for `len` bytes until that dec. All calls are on the single runtime-owner
    // thread.
    unsafe {
        let input = drorb_sarray_of_bytes(req.as_ptr(), req.len());
        let output = (seam.entry())(input); // consumes `input`, returns owned ByteArray
        let len = drorb_sarray_len(output);
        out.clear();
        out.extend_from_slice(slice::from_raw_parts(drorb_sarray_ptr(output), len));
        drorb_obj_dec(output);
    }
}

/// Connection context the metered serve carries alongside the request bytes: the
/// client address the two connection-aware gates decide on, and the per-connection
/// request index the rate bucket depletes against. `Copy` and heap-free, so it
/// rides the serve channel without allocating.
#[derive(Clone, Copy)]
pub struct Meter {
    /// The client IP the IP-filter gate decides on (the accept peer, or the
    /// forwarded client address when the immediate peer is a trusted proxy).
    pub client: IpAddr,
    /// 0-based index of this request within its connection; the rate token bucket
    /// treats it as the standing depletion (`cap - seq` tokens remain).
    pub seq: u64,
}

/// Encode a client address into the attribute-byte shape the proven IP-filter gate
/// decodes (`Reactor.Stage.IpFilter.encodeAddr`): a family tag byte (`4` for IPv4,
/// `6` for IPv6) followed by one `0`/`1` byte per address bit, MSB-first per octet.
/// Writes into `buf` (large enough for the IPv6 case: `1 + 128`) and returns the
/// number of bytes written. No allocation.
fn encode_addr(client: IpAddr, buf: &mut [u8; 129]) -> usize {
    fn push_octets(octets: &[u8], buf: &mut [u8; 129], mut n: usize) -> usize {
        for &octet in octets {
            let mut bit = 7i32;
            while bit >= 0 {
                buf[n] = (octet >> bit) & 1;
                n += 1;
                bit -= 1;
            }
        }
        n
    }
    match client {
        IpAddr::V4(v4) => {
            buf[0] = 4;
            push_octets(&v4.octets(), buf, 1)
        }
        IpAddr::V6(v6) => {
            buf[0] = 6;
            push_octets(&v6.octets(), buf, 1)
        }
    }
}

/// The metered seam crossing: run the proven HTTP/1.1 fold over `req` with the
/// connection context `meter` in scope, so the real IP-filter and rate gates fire
/// on a genuine client address and per-connection sequence. Appends the response
/// bytes into `out` (cleared first). Only ever invoked from the runtime-owner
/// serve thread.
fn serve_metered_into(req: &[u8], meter: Meter, out: &mut Vec<u8>) {
    let mut peer_buf = [0u8; 129];
    let peer_len = encode_addr(meter.client, &mut peer_buf);
    // SAFETY: identical discipline to `serve_into` — both ByteArray arguments are
    // freshly allocated owned sarrays consumed by `drorb_serve_metered`; the
    // returned owned ByteArray's bytes are copied out before the `drorb_obj_dec`.
    // `seq` crosses as an unboxed `uint64_t`. All on the single runtime-owner
    // thread.
    unsafe {
        let peer = drorb_sarray_of_bytes(peer_buf.as_ptr(), peer_len);
        let input = drorb_sarray_of_bytes(req.as_ptr(), req.len());
        let output = drorb_serve_metered(peer, meter.seq, input);
        let len = drorb_sarray_len(output);
        out.clear();
        out.extend_from_slice(slice::from_raw_parts(drorb_sarray_ptr(output), len));
        drorb_obj_dec(output);
    }
}

/// One accepted TLS connection to terminate in-process: the raw connected
/// socket fd (the Lean side owns and closes it) plus the certificate pool the
/// verified handshake selects from and presents. The pool (`crate::tls::TlsCert`)
/// is shared (loaded once at boot), so a connection carries only a pointer.
pub struct TlsConn {
    pub fd: std::os::fd::RawFd,
    pub cert: Arc<crate::tls::TlsCert>,
}

/// Run one whole TLS connection over the verified TLS 1.3 server
/// (`drorb_tls_serve`). Only ever invoked from the runtime-owner serve thread;
/// it BLOCKS that thread for the connection's lifetime (handshake + record-layer
/// serve + close), since the compiled proven core is single-owner and the seam
/// does its own blocking socket I/O. A short per-record recv timeout (Lean side)
/// bounds how long a stalled peer can hold the thread. This head-of-line cost is
/// the honest first-cut trade; the follow-on is a per-record crossing that keeps
/// the socket I/O off the serve thread.
fn run_tls_conn(tls: &TlsConn) {
    // SAFETY: each pool member is copied into a fresh owned Lean ByteArray that
    // `drorb_tls_serve` consumes (an EMPTY vec yields an empty ByteArray = "this
    // pool member is absent"); `fd` crosses as an unboxed `uint32_t`; the returned
    // IO-result object is dropped with `drorb_obj_dec`. All on the single
    // runtime-owner thread. The Lean side closes `fd`.
    let p = &tls.cert;
    unsafe {
        let ba = |v: &[u8]| drorb_sarray_of_bytes(v.as_ptr(), v.len());
        let cert = ba(&p.cert_der);
        let seed = ba(&p.seed);
        let ecdsa_cert = ba(&p.ecdsa_cert);
        let ecdsa_priv = ba(&p.ecdsa_priv);
        let rsa_cert = ba(&p.rsa_cert);
        let rsa_n = ba(&p.rsa_n);
        let rsa_e = ba(&p.rsa_e);
        let rsa_d = ba(&p.rsa_d);
        let world = drorb_io_world();
        let res = drorb_tls_serve(
            tls.fd as u32,
            cert,
            seed,
            ecdsa_cert,
            ecdsa_priv,
            rsa_cert,
            rsa_n,
            rsa_e,
            rsa_d,
            world,
        );
        drorb_obj_dec(res);
    }
}

/// How a finished response is delivered back to the IO path that requested it.
pub enum ServeReply {
    /// Blocking thread-per-connection path: the worker blocks on this channel.
    Sync(Sender<PooledBuf>),
    /// io_uring path: the completed response is posted to the requesting
    /// shard's mailbox and the shard is woken through its eventfd.
    #[cfg(target_os = "linux")]
    Shard(Sender<ShardDone>, std::os::fd::RawFd, u32),
}

/// A response delivered to an io_uring shard: which connection it belongs to
/// and the pooled response bytes to write.
#[cfg(target_os = "linux")]
pub struct ShardDone {
    pub conn: u32,
    pub resp: PooledBuf,
}

/// A unit of work for the serve thread: request bytes, which proven seam to
/// cross, and where to deliver the response.
pub struct ServeJob {
    pub req: PooledBuf,
    pub seam: Seam,
    pub reply: ServeReply,
    /// When present (only on the `Seam::Http` byte-stream path), the connection
    /// context the metered serve reads: the request crosses `drorb_serve_metered`
    /// instead of `drorb_serve`, so the IP-filter and rate gates fire. `None`
    /// keeps the original non-metered `drorb_serve` behavior (h2c, WS, datagram,
    /// or any caller without a peer/sequence, e.g. the stdin orb).
    pub meter: Option<Meter>,
    /// When present, this job is NOT a byte-stream serve: the owner thread runs
    /// the verified TLS 1.3 server over `tls.fd` (`drorb_tls_serve`) instead, and
    /// signals completion on `reply`. `req`/`seam`/`meter` are unused.
    pub tls: Option<TlsConn>,
}

/// A cloneable handle the IO paths use to reach the serve thread.
#[derive(Clone)]
pub struct ServeGateway {
    tx: Sender<ServeJob>,
    pool: Arc<BufferPool>,
}

impl ServeGateway {
    /// The shared buffer pool. IO paths draw request/receive buffers from the
    /// same pool the serve thread draws response buffers from, so buffers
    /// recycle across the whole hot path.
    pub fn pool(&self) -> &Arc<BufferPool> {
        &self.pool
    }

    /// Submit one request across `seam` to the proven core. The response is
    /// delivered per `reply`. Returns `false` only if the serve thread is gone.
    pub fn submit(&self, req: PooledBuf, seam: Seam, reply: ServeReply) -> bool {
        self.tx
            .send(ServeJob {
                req,
                seam,
                reply,
                meter: None,
                tls: None,
            })
            .is_ok()
    }

    /// Submit one HTTP/1.1 request across the metered seam: same delivery as
    /// [`submit`], but the request crosses `drorb_serve_metered` with `meter` in
    /// scope so the proven IP-filter and rate gates decide on the real client
    /// address and per-connection sequence. Returns `false` only if the serve
    /// thread is gone.
    pub fn submit_metered(&self, req: PooledBuf, meter: Meter, reply: ServeReply) -> bool {
        self.tx
            .send(ServeJob {
                req,
                seam: Seam::Http,
                reply,
                meter: Some(meter),
                tls: None,
            })
            .is_ok()
    }

    /// Terminate one accepted TLS connection in-process on the verified TLS 1.3
    /// server: submit the connection fd + certificate material to the runtime-owner
    /// thread (which crosses `drorb_tls_serve`) and BLOCK until the whole
    /// connection — handshake, record-layer serve through the proven core, close —
    /// completes. The owner thread is held for that duration (see `run_tls_conn`).
    /// Returns once the connection is done (or immediately if the serve thread is
    /// gone). The Lean side owns and closes `fd`.
    pub fn serve_tls(&self, fd: std::os::fd::RawFd, cert: Arc<crate::tls::TlsCert>) {
        let (reply_tx, reply_rx) = channel::<PooledBuf>();
        let job = ServeJob {
            req: self.pool.take(),
            seam: Seam::Http,
            reply: ServeReply::Sync(reply_tx),
            meter: None,
            tls: Some(TlsConn { fd, cert }),
        };
        if self.tx.send(job).is_ok() {
            let _ = reply_rx.recv();
        }
    }

    /// Blocking convenience: submit `req` across `seam` and wait for the pooled
    /// response. `reply_tx`/`reply_rx` are the caller's own reusable channel
    /// (one per connection, reused across keep-alive requests — no per-request
    /// channel allocation on the hot path). Returns `None` if the serve thread
    /// is gone.
    pub fn call_seam(
        &self,
        req: PooledBuf,
        seam: Seam,
        reply_tx: &Sender<PooledBuf>,
        reply_rx: &Receiver<PooledBuf>,
    ) -> Option<PooledBuf> {
        if !self.submit(req, seam, ServeReply::Sync(reply_tx.clone())) {
            return None;
        }
        reply_rx.recv().ok()
    }

    /// Blocking HTTP call — the byte-stream `drorb_serve` seam.
    pub fn call(
        &self,
        req: PooledBuf,
        reply_tx: &Sender<PooledBuf>,
        reply_rx: &Receiver<PooledBuf>,
    ) -> Option<PooledBuf> {
        self.call_seam(req, Seam::Http, reply_tx, reply_rx)
    }

    /// Blocking config-route serve — cross `drorb_serve_cfg` with the operator
    /// config's route table in scope. Frames `cfgLen(4 BE) :: config :: request`
    /// into a fresh pooled buffer and serves the request through the config's
    /// declared routes (the proven core re-parses `config` and serves through
    /// `servePipelineOf (denoteOn defaultDeployment pc)`). Returns `None` if the
    /// serve thread is gone.
    pub fn call_cfg(
        &self,
        config: &[u8],
        req: &[u8],
        reply_tx: &Sender<PooledBuf>,
        reply_rx: &Receiver<PooledBuf>,
    ) -> Option<PooledBuf> {
        let mut framed = self.pool.take();
        framed.clear();
        framed.extend_from_slice(&(config.len() as u32).to_be_bytes());
        framed.extend_from_slice(config);
        framed.extend_from_slice(req);
        self.call_seam(framed, Seam::ServeCfg, reply_tx, reply_rx)
    }

    /// Blocking metered HTTP call — the byte-stream path through
    /// `drorb_serve_metered`, carrying the connection context `meter` (client
    /// address + per-connection sequence) so the proven IP-filter and rate gates
    /// fire. `reply_tx`/`reply_rx` are the caller's reusable per-connection
    /// channel. Returns `None` if the serve thread is gone.
    pub fn call_metered(
        &self,
        req: PooledBuf,
        meter: Meter,
        reply_tx: &Sender<PooledBuf>,
        reply_rx: &Receiver<PooledBuf>,
    ) -> Option<PooledBuf> {
        if !self.submit_metered(req, meter, ServeReply::Sync(reply_tx.clone())) {
            return None;
        }
        reply_rx.recv().ok()
    }
}

/// Boot the runtime on a dedicated thread and return a gateway to it. Blocks
/// until the runtime is up so bind failures are reported before we accept.
///
/// SINGLE-OWNER: this thread is the sole caller of `drorb_serve`. Every request
/// from every connection/shard serializes here, so the steady-state throughput
/// ceiling is `1 / (serve latency)` — one core's worth of the proven pipeline,
/// however many IO cores feed it. The IO path (recv/send, framing, TLS) scales
/// across cores; the pure `ByteArray -> ByteArray` transform does not, because
/// the runtime is a process-global singleton. This is the honest bottleneck to
/// measure and, if it binds, to lift only by a design that admits multiple
/// runtime owners.
pub fn spawn_serve_thread(pool: Arc<BufferPool>) -> ServeGateway {
    let (tx, rx) = channel::<ServeJob>();
    let (ready_tx, ready_rx) = channel::<()>();
    let serve_pool = Arc::clone(&pool);
    std::thread::Builder::new()
        .name("drorb-serve".into())
        .spawn(move || {
            lean_boot();
            let _ = ready_tx.send(());
            for job in rx {
                // A TLS connection: run the whole verified handshake + record-layer
                // serve on this owner thread, then signal completion. No response
                // bytes cross back (the seam wrote them straight to the socket).
                if let Some(tls) = &job.tls {
                    run_tls_conn(tls);
                    // (On non-Linux `ServeReply` has only the `Sync` variant, so
                    // this pattern is irrefutable there; on Linux the io_uring
                    // `Shard` variant makes it refutable — the TLS path always
                    // delivers `Sync`.)
                    #[allow(irrefutable_let_patterns)]
                    if let ServeReply::Sync(tx) = job.reply {
                        let _ = tx.send(serve_pool.take());
                    }
                    continue;
                }
                let mut resp = serve_pool.take();
                match job.meter {
                    Some(meter) => serve_metered_into(&job.req, meter, &mut resp),
                    None => serve_into(&job.req, job.seam, &mut resp),
                }
                // `job.req` drops here, returning the request buffer to the pool.
                match job.reply {
                    ServeReply::Sync(tx) => {
                        let _ = tx.send(resp);
                    }
                    #[cfg(target_os = "linux")]
                    ServeReply::Shard(mailbox, efd, conn) => {
                        if mailbox.send(ShardDone { conn, resp }).is_ok() {
                            crate::uring::wake(efd);
                        }
                    }
                }
            }
        })
        .expect("failed to spawn the drorb serve thread");
    ready_rx
        .recv()
        .expect("serve thread died before finishing runtime init");
    ServeGateway { tx, pool }
}
