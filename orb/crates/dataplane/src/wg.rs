//! The WireGuard transport tunnel seam: seal an outbound datagram and open an
//! inbound one — with the RFC-6479 sliding-window anti-replay filter — entirely
//! through the PROVEN transport data plane.
//!
//! The deployed L4 UDP relay ([`crate::l4::forward_datagram`]) moves datagrams in
//! PLAINTEXT. This module is the encrypted tunnel over that plaintext relay: the
//! payload is sealed into a type-4 transport packet (`Wire.sealPacket` — header ‖
//! AEAD(key, counter, payload) on the verified `Crypto` ChaCha20-Poly1305) before
//! it leaves, and an inbound packet is opened (`Wire.openPacket`) and admitted only
//! by the proven anti-replay decision (`Window.willAccept` / `Window.mark`). Both
//! ride the C-ABI seam `drorb_wg_seal` / `drorb_wg_open` (`Wireguard.Export`); this
//! host keeps only the socket, the per-flow send counter, and the receive window's
//! bytes. The verdicts — a sealed wire packet, and open-or-reject with the window
//! advance — are the proven core's:
//!
//! * `Wire.wg_transport_wire_roundtrip` — a sealed packet opens under the same key
//!   to exactly the counter and plaintext sealed.
//! * `Window.replay_rejected` / `Window.too_old_rejected` — a counter already
//!   accepted, or more than `windowSize` behind the high-water mark, is refused.
//!
//! SCOPE (honest): this deploys the transport DATA plane — per-packet seal/open and
//! the anti-replay filter — over an ALREADY-ESTABLISHED transport key (supplied by
//! the host: `DRORB_L4_WG_KEY`, 64 hex = 32 bytes). It does NOT run the Noise IK
//! handshake in-band; that FSM is proven and cross-checked live elsewhere
//! (`WgLive` / `WgResponder`) but is not part of THIS seam. The far end of the
//! tunnel must be a cooperating peer holding the same transport key.

use std::net::UdpSocket;
use std::time::Duration;

// ---------------------------------------------------------------------------
// The proven transport-tunnel seam: `drorb_wg_seal` / `drorb_wg_open`
// (`Wireguard.Export`). Own declarations (captp.rs / ws.rs / http.rs keep their
// own sets); the crossing is made from threads registered through the crate-wide
// runtime guard (`http::ensure_lean_thread`).
// ---------------------------------------------------------------------------

/// The RFC-6479 window width the proven filter models (`Wireguard.windowSize`).
/// A counter more than this far behind the high-water mark is refused by the
/// proven `Window.willAccept` too-old branch regardless of the `seen` set — so
/// pruning such counters from the crossed window leaves the proven decision
/// unchanged while keeping the state bounded.
const WINDOW_SIZE: u64 = 64;

/// Opaque Lean heap object; only `*mut LeanObject` is ever held.
#[repr(C)]
struct LeanObject {
    _private: [u8; 0],
}

unsafe extern "C" {
    /// `initialize_Wireguard_Export` — module initializer for the proven
    /// transport seam's closure (`Wireguard.Export` → `Wireguard` → `Crypto`).
    #[link_name = "initialize_drorb_Wireguard_Export"]
    fn initialize_Wireguard_Export(builtin: u8, world: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_wg_seal]` — `key(32) ‖ recv(4,LE) ‖ ctr(8,LE) ‖ payload`
    /// in, `1 ‖ <wire>` (the sealed type-4 packet) or `0` (AEAD failure) out.
    fn drorb_wg_seal(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_wg_open]` — `key(32) ‖ next(8,LE) ‖ nSeen(4,LE) ‖
    /// (nSeen×8,LE) ‖ wire` in, `0` (AEAD reject OR anti-replay reject) or
    /// `1 ‖ next'(8,LE) ‖ nSeen'(4,LE) ‖ (seen'×8,LE) ‖ plaintext` out.
    fn drorb_wg_open(input: *mut LeanObject) -> *mut LeanObject;

    // Byte-marshalling adapter (ffi/drorb_ffi.c) — stateless.
    fn drorb_sarray_of_bytes(p: *const u8, n: usize) -> *mut LeanObject;
    fn drorb_sarray_len(o: *mut LeanObject) -> usize;
    fn drorb_sarray_ptr(o: *mut LeanObject) -> *const u8;
    fn drorb_obj_dec(o: *mut LeanObject);
    fn drorb_io_world() -> *mut LeanObject;
    fn drorb_io_ok(o: *mut LeanObject) -> i32;
}

/// Ensure this thread may cross the transport-tunnel seam: registered with the
/// runtime, and the `Wireguard.Export` module closure initialized once
/// process-wide.
fn ensure_wg_seam() {
    use std::sync::Once;
    static MODULE: Once = Once::new();
    // Register the thread FIRST — the module init below allocates on it.
    crate::http::ensure_lean_thread();
    MODULE.call_once(|| {
        // SAFETY: standard guarded module init on a registered thread, after the
        // process-global runtime is up (same pattern as the CapTP seam boot).
        unsafe {
            let res = initialize_Wireguard_Export(1, drorb_io_world());
            assert!(
                drorb_io_ok(res) == 1,
                "initialize_Wireguard_Export returned an IO error"
            );
            drorb_obj_dec(res);
        }
    });
}

/// Cross one seam call: marshal `input` into a fresh sarray the callee consumes,
/// copy the owned result sarray out, release it. Created, consumed, and dropped
/// on the calling thread (registered on first use).
fn cross(seam: unsafe extern "C" fn(*mut LeanObject) -> *mut LeanObject, input: &[u8]) -> Vec<u8> {
    ensure_wg_seam();
    // SAFETY: `seam` is a real `@[export]` symbol; the argument is a fresh sarray
    // the callee consumes, the result an owned sarray copied out then released.
    unsafe {
        let arg = drorb_sarray_of_bytes(input.as_ptr(), input.len());
        let out = seam(arg);
        let n = drorb_sarray_len(out);
        let v = std::slice::from_raw_parts(drorb_sarray_ptr(out), n).to_vec();
        drorb_obj_dec(out);
        v
    }
}

/// Seal one datagram into a type-4 transport packet under `key` and `(receiver,
/// counter)`, via the proven `Wire.sealPacket`. `None` on an AEAD failure.
pub fn seal(key: &[u8; 32], receiver: u32, counter: u64, payload: &[u8]) -> Option<Vec<u8>> {
    let mut input = Vec::with_capacity(32 + 4 + 8 + payload.len());
    input.extend_from_slice(key);
    input.extend_from_slice(&receiver.to_le_bytes());
    input.extend_from_slice(&counter.to_le_bytes());
    input.extend_from_slice(payload);
    let out = cross(drorb_wg_seal, &input);
    match out.first() {
        Some(1) => Some(out[1..].to_vec()),
        _ => None,
    }
}

/// The receive-side anti-replay window: the high-water mark and the accepted
/// counters still inside the window. This host holds only the BYTES — every
/// admission decision and state advance is the proven core's (`Window.willAccept`
/// / `Window.mark`, crossed via `drorb_wg_open`).
pub struct Window {
    next: u64,
    seen: Vec<u64>,
}

impl Window {
    /// A fresh window (`Window.fresh`): nothing received yet.
    pub fn new() -> Self {
        Window {
            next: 0,
            seen: Vec::new(),
        }
    }

    /// Open one inbound datagram under `key` and take the anti-replay decision.
    /// Returns the recovered plaintext on accept (advancing the window by the
    /// proven `Window.mark`), or `None` on a bounded reject — the packet did not
    /// AEAD-open, or the proven `Window.willAccept` refused the counter (a replay,
    /// or too old). Never faults.
    pub fn open(&mut self, key: &[u8; 32], wire: &[u8]) -> Option<Vec<u8>> {
        let mut input = Vec::with_capacity(32 + 8 + 4 + self.seen.len() * 8 + wire.len());
        input.extend_from_slice(key);
        input.extend_from_slice(&self.next.to_le_bytes());
        input.extend_from_slice(&(self.seen.len() as u32).to_le_bytes());
        for c in &self.seen {
            input.extend_from_slice(&c.to_le_bytes());
        }
        input.extend_from_slice(wire);
        let out = cross(drorb_wg_open, &input);
        if out.first() != Some(&1) || out.len() < 13 {
            return None; // bounded reject: AEAD failure or proven anti-replay refusal
        }
        // 1 ‖ next'(8) ‖ nSeen'(4) ‖ (seen'×8) ‖ plaintext
        let next = u64::from_le_bytes(out[1..9].try_into().ok()?);
        let n_seen = u32::from_le_bytes(out[9..13].try_into().ok()?) as usize;
        let seen_end = 13 + n_seen * 8;
        if out.len() < seen_end {
            return None;
        }
        let mut seen: Vec<u64> = out[13..seen_end]
            .chunks_exact(8)
            .map(|c| u64::from_le_bytes(c.try_into().unwrap()))
            .collect();
        // Prune counters the proven too-old branch already rejects regardless of
        // membership — keeps the crossed window bounded, decision unchanged.
        seen.retain(|&c| c + WINDOW_SIZE >= next);
        self.next = next;
        self.seen = seen;
        Some(out[seen_end..].to_vec())
    }
}

impl Default for Window {
    fn default() -> Self {
        Self::new()
    }
}

/// Gated my-hand self-test (`DRORB_WG_SELFTEST`): drive the proven transport
/// tunnel over a REAL loopback UDP socket pair, and check, end to end:
///
/// 1. `seal` produces a type-4 packet whose bytes differ from the plaintext
///    (the datagram is actually encrypted, not passed through);
/// 2. the sealed packet, sent over UDP and received on the far socket, `open`s
///    under the same key and the proven window back to the EXACT plaintext;
/// 3. a REPLAY of that same packet into the same window is refused by the proven
///    anti-replay filter (`Window.willAccept` = false → `None`);
/// 4. a fresh higher-counter packet still opens (legitimate traffic continues).
///
/// Returns `true` iff every step holds. Off by default; the serve path is
/// untouched. The proven core is CALLED on every seal and every open.
pub fn selftest() -> bool {
    let key: [u8; 32] = {
        let mut k = [0u8; 32];
        for (i, b) in k.iter_mut().enumerate() {
            *b = (i as u8).wrapping_mul(7).wrapping_add(1);
        }
        k
    };
    let receiver: u32 = 0x0102_0304;
    let plaintext = b"drorb wireguard transport datagram - encrypted over the plaintext relay";

    // Real loopback UDP sockets: A (tunnel ingress) seals and sends; B (tunnel
    // egress) receives and opens.
    let sock_b = match UdpSocket::bind("127.0.0.1:0") {
        Ok(s) => s,
        Err(_) => return false,
    };
    let sock_a = match UdpSocket::bind("127.0.0.1:0") {
        Ok(s) => s,
        Err(_) => return false,
    };
    let b_addr = match sock_b.local_addr() {
        Ok(a) => a,
        Err(_) => return false,
    };
    let _ = sock_b.set_read_timeout(Some(Duration::from_secs(2)));

    let mut win = Window::new();

    // (1) seal counter 0 and confirm the wire is ciphertext, not the plaintext.
    let wire0 = match seal(&key, receiver, 0, plaintext) {
        Some(w) => w,
        None => {
            eprintln!("wg selftest: seal(ctr=0) failed");
            return false;
        }
    };
    if wire0.first() != Some(&4) {
        eprintln!("wg selftest: sealed packet is not a type-4 transport message");
        return false;
    }
    if wire0.windows(plaintext.len()).any(|w| w == plaintext) {
        eprintln!("wg selftest: plaintext appears verbatim in the sealed wire (NOT encrypted)");
        return false;
    }

    // (2) send it over the real UDP loopback; the far socket opens it.
    if sock_a.send_to(&wire0, b_addr).is_err() {
        eprintln!("wg selftest: UDP send failed");
        return false;
    }
    let mut buf = [0u8; 65536];
    let n = match sock_b.recv_from(&mut buf) {
        Ok((n, _)) => n,
        Err(_) => {
            eprintln!("wg selftest: UDP recv timed out (no datagram)");
            return false;
        }
    };
    let received = &buf[..n];
    if received == &plaintext[..] {
        eprintln!("wg selftest: received bytes equal the plaintext (tunnel not encrypting)");
        return false;
    }
    match win.open(&key, received) {
        Some(pt) if pt == plaintext => {}
        Some(_) => {
            eprintln!("wg selftest: open recovered the WRONG plaintext");
            return false;
        }
        None => {
            eprintln!("wg selftest: open REJECTED a legitimate first packet");
            return false;
        }
    }

    // (3) replay the exact same wire packet — the proven anti-replay must refuse.
    if win.open(&key, received).is_some() {
        eprintln!("wg selftest: REPLAY was accepted (anti-replay broken)");
        return false;
    }

    // (4) a fresh higher counter still opens (legitimate traffic continues).
    let wire1 = match seal(&key, receiver, 1, b"second datagram") {
        Some(w) => w,
        None => {
            eprintln!("wg selftest: seal(ctr=1) failed");
            return false;
        }
    };
    match win.open(&key, &wire1) {
        Some(pt) if pt == b"second datagram" => {}
        _ => {
            eprintln!("wg selftest: a fresh higher-counter packet was not accepted");
            return false;
        }
    }

    true
}
