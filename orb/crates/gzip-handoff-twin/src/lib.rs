//! Executable model (twin) of the **CRC-checked gzip handoff** at the reactor
//! seam — `crates/dataplane/src/gzip.rs::recompress` in `drorb`.
//!
//! # The seam and the invariant
//!
//! The deployed proven pipeline runs the VERIFIED `Reactor.Stage.Gzip.gzipStage`,
//! whose body transform is Lean `Gzip.gzipStored`: a DEFLATE *stored* block (no
//! compression) wrapped in the RFC 1952 gzip container, with an 8-byte trailer
//! carrying `CRC-32(body)` and `ISIZE`. Theorems `gzipStage_ce_header` /
//! `gzipStage_body_gzipped` prove the emitted bytes ARE `gzipStored body`. A
//! stored block does no compression, so the "gzip" response is *larger* than the
//! plaintext — correct, verified, and useless for bandwidth.
//!
//! `recompress` (the seam this crate models) replaces that stored block with REAL
//! DEFLATE from the trusted `flate2`/`miniz_oxide` codec. The compression itself
//! is principled TCB — trusted, not proven, exactly like the EverCrypt FFI for
//! crypto. What is NOT blindly trusted is the **handoff**: the plaintext fed to
//! `flate2` is not taken on faith, it is *recovered by gunzipping the proven
//! stage's own gzip output*. Because that stream carries `CRC-32(body)` in a
//! trailer the PROVEN core computed, `flate2`'s decoder verifies the CRC while
//! inflating. So the bytes handed to the compressor equal the serve body,
//! confirmed byte-for-byte by a checksum from the verified core.
//!
//! ```text
//!   proven gzipStore(body)  --GzDecoder (CRC-32 checked)-->  plain == body
//!                                                                  |
//!                                            GzEncoder(best) (TRUSTED flate2)
//!                                                                  v
//!                                            real DEFLATE gzip of the SAME body
//! ```
//!
//! ## The three claims this twin makes executable
//!
//! 1. **HANDOFF (checked, not blindly trusted).** For every response the proven
//!    stage produced, the plaintext `recompress` re-compresses equals the serve
//!    body — because it is `gunzip(proven output)` and the gunzip verifies the
//!    proven CRC-32. Modeled by [`handoff`] round-trip tests: the re-emitted body
//!    always decodes back to exactly what the *input* body decodes to.
//! 2. **FAILURE-SAFE (proven output preserved).** On ANY decode failure — a
//!    corrupted stored-gzip stream, a bad CRC, a truncated trailer — `recompress`
//!    leaves the response byte-for-byte untouched. Never a silent truncation or a
//!    wrong body. This mirrors Lean `gzip_crc_checked` (a wrong CRC is *rejected*,
//!    `crcMismatch`, nothing handed back). Modeled by the adversarial-corruption
//!    tests: the CRC guard makes the handoff CHECKED.
//! 3. **NON-CORRUPTING ENVELOPE.** For ANY input at all (not just well-formed
//!    proven output), `recompress` either leaves it untouched or produces a valid
//!    gzip body that decodes to the same content as the input body — it is never
//!    lossy. Modeled by the fuzz envelope test.
//!
//! # Why this is NOT a loom crate
//!
//! `recompress` is called post-serve, pre-write at each IO backend's response
//! funnel (`blocking.rs:570`, `kqueue.rs:587`, `uring.rs:992`), each time on its
//! OWN per-connection `&mut Vec<u8>`. The only process-shared state is a read-once
//! `OnceLock<bool>` config gate. `GzEncoder`/`GzDecoder` are stack-local per call.
//! There is no cross-thread shared mutable state and no handoff of ownership
//! across threads — every shard recompresses disjoint responses. A loom model
//! would explore a state space with no shared cell and prove nothing. The real
//! handoff here is a *data-flow* invariant WITHIN one thread (decode ⟶ re-encode,
//! with a failure-safe early return), which is exactly what the property model
//! below exercises.
//!
//! # Correspondence to the deployed code (faithfulness, honestly stated)
//!
//! [`recompress`] / [`find_ci`] / [`header_value`] / [`rebuild_head`] below are a
//! byte-faithful transcription of `crates/dataplane/src/gzip.rs` (only the
//! `enabled()` env gate is dropped — it does not affect the transform). This twin
//! is EVIDENCE FOR THE MODEL; correspondence to the deployed function is by
//! transcription, not by linking (the dataplane package links the Lean runtime,
//! which is why the twins are separate crates). If `gzip.rs::recompress` changes,
//! this transcription must be re-synced — a residual noted in the lane report. A
//! future cleanup could hoist the pure transform into a shared no-Lean crate that
//! both `dataplane` and this twin depend on, removing the transcription gap.

#![deny(unsafe_op_in_unsafe_fn)]

use std::io::{Read, Write};

use flate2::Compression;
use flate2::read::GzDecoder;
use flate2::write::GzEncoder;

/// Case-insensitive subslice search (both sides folded to ASCII-lowercase).
/// Transcribed from `gzip.rs::find_ci`.
pub fn find_ci(hay: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() || hay.len() < needle.len() {
        return None;
    }
    (0..=hay.len() - needle.len()).find(|&i| {
        hay[i..i + needle.len()]
            .iter()
            .zip(needle)
            .all(|(a, b)| a.eq_ignore_ascii_case(b))
    })
}

/// The trimmed value of header `name` in a response head block (through
/// CRLFCRLF), first match, or `None`. Transcribed from `gzip.rs::header_value`.
pub fn header_value<'a>(head: &'a [u8], name: &[u8]) -> Option<&'a [u8]> {
    let mut i = 0;
    while i < head.len() {
        let line_end = head[i..]
            .windows(2)
            .position(|w| w == b"\r\n")
            .map(|p| i + p)
            .unwrap_or(head.len());
        let line = &head[i..line_end];
        if let Some(colon) = line.iter().position(|&c| c == b':') {
            let (n, v) = line.split_at(colon);
            if n.eq_ignore_ascii_case(name) {
                let val = &v[1..]; // skip ':'
                let start = val
                    .iter()
                    .position(|&c| c != b' ' && c != b'\t')
                    .unwrap_or(val.len());
                let end = val
                    .iter()
                    .rposition(|&c| c != b' ' && c != b'\t')
                    .map(|p| p + 1)
                    .unwrap_or(start);
                return Some(&val[start..end]);
            }
        }
        i = line_end + 2;
    }
    None
}

/// Rebuild a response head block setting `Content-Length` to `new_len`.
/// Transcribed from `gzip.rs::rebuild_head`.
pub fn rebuild_head(head: &[u8], new_len: usize) -> Vec<u8> {
    let mut out = Vec::with_capacity(head.len() + 8);
    let cl = new_len.to_string();
    let mut wrote_cl = false;
    let mut i = 0;
    while i < head.len() {
        let line_end = head[i..]
            .windows(2)
            .position(|w| w == b"\r\n")
            .map(|p| i + p)
            .unwrap_or(head.len());
        let line = &head[i..line_end];
        if line.is_empty() {
            if !wrote_cl {
                out.extend_from_slice(b"Content-Length: ");
                out.extend_from_slice(cl.as_bytes());
                out.extend_from_slice(b"\r\n");
            }
            out.extend_from_slice(b"\r\n");
            return out;
        }
        let is_cl = line
            .iter()
            .position(|&c| c == b':')
            .map(|colon| line[..colon].eq_ignore_ascii_case(b"content-length"))
            .unwrap_or(false);
        if is_cl {
            out.extend_from_slice(b"Content-Length: ");
            out.extend_from_slice(cl.as_bytes());
            out.extend_from_slice(b"\r\n");
            wrote_cl = true;
        } else {
            out.extend_from_slice(line);
            out.extend_from_slice(b"\r\n");
        }
        i = line_end + 2;
    }
    out
}

/// Replace a proven stored-block gzip response body with REAL `flate2` gzip, in
/// place — the seam under study. Byte-faithful transcription of
/// `gzip.rs::recompress` (the `enabled()` gate is applied by the caller and is
/// not part of the transform).
///
/// FAILURE-SAFE: every early `return` leaves `resp` byte-for-byte unchanged. The
/// only mutation is the final `clear()` + rebuild, reached ONLY after a
/// CRC-verified gunzip succeeded and the real gzip is strictly smaller.
pub fn recompress(resp: &mut Vec<u8>) {
    let Some(head_end) = resp
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .map(|p| p + 4)
    else {
        return;
    };

    {
        let head = &resp[..head_end];
        match header_value(head, b"content-encoding") {
            Some(v) if find_ci(v, b"gzip").is_some() => {}
            _ => return,
        }
        if let Some(te) = header_value(head, b"transfer-encoding") {
            if find_ci(te, b"chunked").is_some() {
                return;
            }
        }
    }

    let body = &resp[head_end..];
    if body.is_empty() {
        return;
    }

    // HANDOFF: gunzip the proven stage's gzip stream back to the exact plaintext.
    // flate2 verifies the RFC 1952 CRC-32 trailer (the one the PROVEN core
    // computed) while inflating — so `plain` IS the serve's body, CRC-confirmed.
    let mut plain = Vec::new();
    if GzDecoder::new(body).read_to_end(&mut plain).is_err() {
        return; // not a decodable gzip stream — leave the proven output alone
    }

    // REAL COMPRESSION (trusted flate2 / miniz_oxide DEFLATE).
    let mut enc = GzEncoder::new(Vec::new(), Compression::best());
    if enc.write_all(&plain).is_err() {
        return;
    }
    let Ok(gz) = enc.finish() else {
        return;
    };

    if gz.len() >= body.len() {
        return;
    }

    let new_head = rebuild_head(&resp[..head_end], gz.len());
    resp.clear();
    resp.extend_from_slice(&new_head);
    resp.extend_from_slice(&gz);
}

// ---------------------------------------------------------------------------
// Test helpers / model harness (used by tests/handoff.rs).
// ---------------------------------------------------------------------------

/// Build a proven-style stored-block gzip response — the byte shape the VERIFIED
/// Lean `gzipStage` (`Gzip.gzipStored`) emits: a valid RFC 1952 stream whose
/// payload is a stored DEFLATE block, so the body is LARGER than the plaintext.
/// `Compression::none()` selects flate2's stored (level-0) encoder, byte-shape
/// equivalent to `Gzip.gzipStored` for the handoff's purposes.
pub fn stored_gzip_response(plain: &[u8]) -> Vec<u8> {
    let mut enc = GzEncoder::new(Vec::new(), Compression::none());
    enc.write_all(plain).unwrap();
    let stored = enc.finish().unwrap();
    let mut resp = Vec::new();
    resp.extend_from_slice(b"HTTP/1.1 200 OK\r\n");
    resp.extend_from_slice(b"Content-Encoding: gzip\r\n");
    resp.extend_from_slice(format!("Content-Length: {}\r\n", stored.len()).as_bytes());
    resp.extend_from_slice(b"\r\n");
    resp.extend_from_slice(&stored);
    resp
}

/// Split a response at the head/body boundary (`\r\n\r\n`).
pub fn split_head_body(resp: &[u8]) -> (&[u8], &[u8]) {
    let he = resp.windows(4).position(|w| w == b"\r\n\r\n").unwrap() + 4;
    (&resp[..he], &resp[he..])
}

/// gunzip a body, `None` on any decode/CRC failure. This is the *observer* the
/// twin uses to state the handoff invariant: it verifies the same RFC 1952
/// CRC-32 the seam relies on, so `decode(body)` witnesses "the CRC-checked
/// plaintext" — exactly the bytes the handoff hands to the compressor.
pub fn decode(body: &[u8]) -> Option<Vec<u8>> {
    let mut out = Vec::new();
    GzDecoder::new(body).read_to_end(&mut out).ok().map(|_| out)
}

/// Deterministic zero-dependency PRNG (xorshift64*) for reproducible fuzzing —
/// no `proptest`/`rand` dependency, so the model stays self-contained and the
/// exact schedule is replayable from the seed printed by each test.
pub struct Rng(pub u64);
impl Rng {
    pub fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    /// A random byte vector of length `0..=max_len` with a mix of repetitive
    /// (compressible) and high-entropy (incompressible) content.
    pub fn body(&mut self, max_len: usize) -> Vec<u8> {
        let len = (self.next_u64() as usize) % (max_len + 1);
        let compressible = self.next_u64() & 1 == 0;
        (0..len)
            .map(|i| {
                if compressible {
                    // low-entropy: a handful of byte values, long runs
                    (b'a' + ((i / 7) % 5) as u8) as u8
                } else {
                    (self.next_u64() >> ((i % 8) * 8)) as u8
                }
            })
            .collect()
    }
}
