//
// turn_gate — the firmament-boundary SignedTurn admission gate.
//
// An arriving chunk is one of two things:
//
//   * A SignedTurn ENVELOPE, framed as
//         [ 32-byte Ed25519 public key ][ 64-byte signature ][ message bytes ]
//     (>= 97 bytes, the message being the canonical turn bytes the signer
//     signed). We Ed25519-`verify_strict` the signature over the message under
//     the embedded key. ACCEPTED only if the check passes — this is the seL4
//     net-PD enforcing "signature-bad turns never reach the verified core"
//     (docs/SEL4-EMBEDDING.md §4). On accept we'd hand the message to the
//     executor PD; here (no executor PD on the bare target yet) we reply with
//     the verdict so the gate is observable over the wire.
//
//   * Anything shorter / not so framed: a plain line, echoed verbatim (the
//     bare TCP-echo smoke test, so `nc host 5555` round-trips).
//
// The Ed25519 verification is ed25519-dalek 2, the SAME crate major the dregg
// SDK signs `SignedTurn` with — so this is the deployed verification path
// carried to the edge, not a parallel reimplementation.

use alloc::vec::Vec;

use ed25519_dalek::{Signature, VerifyingKey};

/// The envelope magic: a SignedTurn frame begins with these 4 bytes, so a plain
/// line is never mistaken for an envelope (and vice-versa). "DRGT" = dregg turn.
pub const ENVELOPE_MAGIC: &[u8; 4] = b"DRGT";

const PK_LEN: usize = 32;
const SIG_LEN: usize = 64;
const HEADER_LEN: usize = ENVELOPE_MAGIC.len() + PK_LEN + SIG_LEN; // 4 + 32 + 64 = 100

/// The outcome of deciding what an arriving chunk is: the bytes to reply over the
/// wire, and — on an ACCEPTED SignedTurn — the verified message bytes the caller
/// must STAGE into turn_in and hand to the executor. `accepted` is `Some(msg)`
/// only after `verify_strict` passes, so a bad signature can NEVER produce turn
/// bytes for the heart (the firmament-boundary invariant, in the type).
pub struct GateOutcome {
    pub reply: Vec<u8>,
    pub accepted: Option<Vec<u8>>,
}

/// Decide what an arriving chunk is, producing the wire reply and — on accept —
/// the verified turn message to stage for the executor.
pub fn handle_chunk(chunk: &[u8]) -> GateOutcome {
    if is_envelope(chunk) {
        match verify_envelope(chunk) {
            Ok(msg) => {
                let msg_len = msg.len();
                sel4_microkit::debug_println!(
                    "[net-client] SignedTurn ACCEPTED at the edge: sig verified over {} msg bytes — handing to the executor boundary",
                    msg_len
                );
                let mut reply = Vec::new();
                reply.extend_from_slice(b"TURN-ACCEPTED ");
                push_usize(&mut reply, msg_len);
                reply.extend_from_slice(b"\n");
                GateOutcome { reply, accepted: Some(msg.to_vec()) }
            }
            Err(why) => {
                sel4_microkit::debug_println!(
                    "[net-client] SignedTurn REFUSED at the edge: {} — it never reaches the heart",
                    why
                );
                let mut reply = Vec::new();
                reply.extend_from_slice(b"TURN-REFUSED ");
                reply.extend_from_slice(why.as_bytes());
                reply.extend_from_slice(b"\n");
                GateOutcome { reply, accepted: None }
            }
        }
    } else {
        // Plain echo — the bare smoke test. Never an accepted turn.
        sel4_microkit::debug_println!("[net-client] echo {} bytes", chunk.len());
        GateOutcome { reply: chunk.to_vec(), accepted: None }
    }
}

fn is_envelope(chunk: &[u8]) -> bool {
    chunk.len() >= HEADER_LEN && &chunk[..ENVELOPE_MAGIC.len()] == ENVELOPE_MAGIC
}

/// Verify a SignedTurn envelope. Returns the (borrowed) message bytes on success,
/// or a static reason string on refusal. NEVER panics on adversarial bytes.
fn verify_envelope(chunk: &[u8]) -> Result<&[u8], &'static str> {
    if chunk.len() < HEADER_LEN {
        return Err("short-envelope");
    }
    let off = ENVELOPE_MAGIC.len();

    let pk_bytes: [u8; PK_LEN] = chunk[off..off + PK_LEN]
        .try_into()
        .map_err(|_| "bad-pk-len")?;
    let sig_bytes: [u8; SIG_LEN] = chunk[off + PK_LEN..off + PK_LEN + SIG_LEN]
        .try_into()
        .map_err(|_| "bad-sig-len")?;
    let msg = &chunk[HEADER_LEN..];

    let vk = VerifyingKey::from_bytes(&pk_bytes).map_err(|_| "bad-pubkey")?;
    let sig = Signature::from_bytes(&sig_bytes);

    // verify_strict: the cofactorless, malleability-resistant check (the one
    // dalek and the dregg verifier path use).
    vk.verify_strict(msg, &sig).map_err(|_| "sig-mismatch")?;
    Ok(msg)
}

fn push_usize(out: &mut Vec<u8>, mut n: usize) {
    if n == 0 {
        out.push(b'0');
        return;
    }
    let mut digits = [0u8; 20];
    let mut i = 0;
    while n > 0 {
        digits[i] = b'0' + (n % 10) as u8;
        n /= 10;
        i += 1;
    }
    while i > 0 {
        i -= 1;
        out.push(digits[i]);
    }
}
