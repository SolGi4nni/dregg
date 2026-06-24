//! Host witness for the firmament INGRESS weld (sel4/dregg.system): the net_client
//! (ingress) PD's SignedTurn Ed25519 gate + the turn_in framing it stages for the
//! verified executor PD.
//!
//! It INCLUDES the SAME `turn_gate.rs` the net_client PD carries (via `#[path]`)
//! and drives it as a normal host binary + `#[test]`s. The gate's two no_std
//! dependencies — `alloc::vec::Vec` and the `sel4_microkit::debug_println!` macro —
//! are satisfied here by `extern crate alloc` (std re-exports it) and a tiny
//! `sel4_microkit` shim module mapping `debug_println!` to `eprintln!`. The crypto
//! (ed25519-dalek 2, `verify_strict`) is byte-identical to the PD + the SDK.
//!
//! The turn_in framing test mirrors the EXACT decode the executor PD's
//! `run_turn_from_turn_in` performs (4-byte LE length prefix + message), proving a
//! staged turn round-trips net_client -> turn_in -> executor.

extern crate alloc;

use ed25519_dalek::{Signer, SigningKey};

/// A tiny shim standing in for the `sel4_microkit` crate the no_std PD links: the
/// gate only uses `debug_println!`. On the host it goes to stderr (so stdout stays
/// the witness narration). Same call shape as the real macro.
pub mod sel4_microkit {
    #[macro_export]
    macro_rules! __host_debug_println {
        ($($arg:tt)*) => { eprintln!($($arg)*) };
    }
    pub use crate::__host_debug_println as debug_println;
}

/// Include the PD's gate verbatim inside a module that brings the `sel4_microkit`
/// shim into scope, so the gate's `sel4_microkit::debug_println!` + `alloc::vec`
/// paths resolve on the host without editing the no_std source.
mod turn_gate {
    #[allow(unused_imports)]
    use crate::sel4_microkit;
    include!("../../dregg-pd/net-client/src/turn_gate.rs");
}

use turn_gate::ENVELOPE_MAGIC;

/// Build a SignedTurn envelope: [DRGT][pk 32][sig 64][msg]. This is EXACTLY the
/// frame the dregg SDK emits and the net_client gate consumes.
fn envelope(sk: &SigningKey, msg: &[u8]) -> Vec<u8> {
    let pk = sk.verifying_key().to_bytes(); // 32
    let sig = sk.sign(msg).to_bytes(); // 64
    let mut out = Vec::with_capacity(4 + 32 + 64 + msg.len());
    out.extend_from_slice(ENVELOPE_MAGIC);
    out.extend_from_slice(&pk);
    out.extend_from_slice(&sig);
    out.extend_from_slice(msg);
    out
}

fn fresh_key() -> SigningKey {
    SigningKey::generate(&mut rand_core::OsRng)
}

/// The EXACT framing the net_client's `stage_turn_to_executor` writes into turn_in:
/// a 4-byte little-endian length prefix followed by the verified message bytes.
fn frame_for_turn_in(msg: &[u8]) -> Vec<u8> {
    let len = msg.len() as u32;
    let mut out = Vec::with_capacity(4 + msg.len());
    out.extend_from_slice(&len.to_le_bytes());
    out.extend_from_slice(msg);
    out
}

/// The EXACT decode the executor PD's `run_turn_from_turn_in` performs: read the
/// 4-byte LE length, then the message bytes. Returns the recovered message.
fn decode_turn_in(framed: &[u8]) -> Option<&[u8]> {
    if framed.len() < 4 {
        return None;
    }
    let len = (framed[0] as u32)
        | ((framed[1] as u32) << 8)
        | ((framed[2] as u32) << 16)
        | ((framed[3] as u32) << 24);
    let len = len as usize;
    if len == 0 || 4 + len > framed.len() {
        return None;
    }
    Some(&framed[4..4 + len])
}

fn main() {
    println!("== firmament ingress weld — host witness (net_client gate + turn_in framing) ==");
    println!("   (a SignedTurn on :5555 -> Ed25519 gate -> stage into turn_in -> verified executor)\n");

    let sk = fresh_key();
    let msg = b"{\"demo\":\"firmament-ingress\"}";

    // ---- 1. a GOOD envelope is ACCEPTED and yields exactly the message ----------
    let good = envelope(&sk, msg);
    let out = turn_gate::handle_chunk(&good);
    let accepted = out.accepted.as_deref();
    assert_eq!(accepted, Some(&msg[..]), "good envelope must accept the exact msg");
    assert!(out.reply.starts_with(b"TURN-ACCEPTED"), "good reply is TURN-ACCEPTED");
    println!("  [1] GOOD SignedTurn ({} B envelope) -> ACCEPTED; staged {} msg bytes",
        good.len(), accepted.unwrap().len());

    // ---- 2. a BAD-signature envelope is REFUSED, NOTHING accepted ---------------
    let mut bad = good.clone();
    bad[4 + 32] ^= 0xFF; // flip a signature byte
    let out = turn_gate::handle_chunk(&bad);
    assert!(out.accepted.is_none(), "a bad signature must NOT accept (never reaches the heart)");
    assert!(out.reply.starts_with(b"TURN-REFUSED"), "bad reply is TURN-REFUSED");
    println!("  [2] tampered-signature envelope -> REFUSED; nothing staged (boundary holds)");

    // ---- 3. a WRONG-KEY envelope (sig good, but for another key) is REFUSED ------
    let other = fresh_key();
    let mut wrong = envelope(&other, msg);
    // splice in `sk`'s public key so pk != the signing key -> sig mismatch
    wrong[4..4 + 32].copy_from_slice(&sk.verifying_key().to_bytes());
    let out = turn_gate::handle_chunk(&wrong);
    assert!(out.accepted.is_none(), "wrong-key envelope must be refused");
    println!("  [3] wrong-key envelope -> REFUSED; nothing staged");

    // ---- 4. a plain line is echoed, never accepted ------------------------------
    let out = turn_gate::handle_chunk(b"hello-firmament\n");
    assert!(out.accepted.is_none(), "a plain line is never an accepted turn");
    assert_eq!(out.reply, b"hello-firmament\n", "plain line echoed verbatim");
    println!("  [4] plain line -> echoed; nothing staged");

    // ---- 5. the staged turn ROUND-TRIPS net_client -> turn_in -> executor -------
    let accepted = turn_gate::handle_chunk(&good).accepted.expect("accepted");
    let framed = frame_for_turn_in(&accepted);
    let recovered = decode_turn_in(&framed).expect("executor decodes turn_in framing");
    assert_eq!(recovered, &msg[..], "turn_in framing round-trips to the executor reader");
    println!("  [5] staged {} B -> turn_in frame ({} B) -> executor decode recovers the EXACT turn",
        accepted.len(), framed.len());

    println!("\n== ingress weld GREEN: only Ed25519-valid SignedTurns are staged into turn_in,");
    println!("== and the staged framing decodes byte-identically under the executor's reader ( ◕‿◕ ) ==");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn good_envelope_accepts_exact_msg() {
        let sk = fresh_key();
        let msg = b"turn-bytes-A";
        let out = turn_gate::handle_chunk(&envelope(&sk, msg));
        assert_eq!(out.accepted.as_deref(), Some(&msg[..]));
        assert!(out.reply.starts_with(b"TURN-ACCEPTED"));
    }

    #[test]
    fn tampered_signature_is_refused() {
        let sk = fresh_key();
        let mut e = envelope(&sk, b"turn-bytes-B");
        e[4 + 32 + 10] ^= 0x01; // flip inside the signature
        let out = turn_gate::handle_chunk(&e);
        assert!(out.accepted.is_none());
        assert!(out.reply.starts_with(b"TURN-REFUSED"));
    }

    #[test]
    fn tampered_message_is_refused() {
        let sk = fresh_key();
        let mut e = envelope(&sk, b"turn-bytes-C");
        let last = e.len() - 1;
        e[last] ^= 0x01; // flip the message after signing
        let out = turn_gate::handle_chunk(&e);
        assert!(out.accepted.is_none(), "a mutated message no longer verifies");
    }

    #[test]
    fn wrong_key_is_refused() {
        let sk = fresh_key();
        let other = fresh_key();
        let msg = b"turn-bytes-D";
        let mut e = envelope(&other, msg);
        e[4..4 + 32].copy_from_slice(&sk.verifying_key().to_bytes());
        assert!(turn_gate::handle_chunk(&e).accepted.is_none());
    }

    #[test]
    fn short_envelope_is_refused_not_panics() {
        // magic present but truncated before a full pk+sig: refused, never panics.
        let mut e = Vec::new();
        e.extend_from_slice(ENVELOPE_MAGIC);
        e.extend_from_slice(&[0u8; 20]);
        let out = turn_gate::handle_chunk(&e);
        assert!(out.accepted.is_none());
    }

    #[test]
    fn plain_line_is_echoed_never_accepted() {
        let out = turn_gate::handle_chunk(b"ping\n");
        assert!(out.accepted.is_none());
        assert_eq!(out.reply, b"ping\n");
    }

    #[test]
    fn turn_in_framing_round_trips_to_executor_reader() {
        let sk = fresh_key();
        let msg = b"a-real-turn-payload-of-some-length";
        let accepted = turn_gate::handle_chunk(&envelope(&sk, msg))
            .accepted
            .expect("accepted");
        let framed = frame_for_turn_in(&accepted);
        // the 4-byte LE prefix is the executor's frame contract
        assert_eq!(&framed[..4], &(msg.len() as u32).to_le_bytes());
        assert_eq!(decode_turn_in(&framed), Some(&msg[..]));
    }

    #[test]
    fn empty_turn_in_frame_is_rejected_by_reader() {
        // a zero-length frame (len prefix 0) the executor refuses -> None.
        let framed = frame_for_turn_in(b"");
        assert_eq!(decode_turn_in(&framed), None);
    }
}
