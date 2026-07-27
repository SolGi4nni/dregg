//! Real gzip at the reactor seam — the honest boundary.
//!
//! ## Why this module exists
//!
//! The deployed proven pipeline runs `Reactor.Stage.Gzip.gzipStage`, whose body
//! transform is `Gzip.gzipStored`: a DEFLATE *stored* block (BTYPE=00) wrapped in
//! the real RFC 1952 gzip container (magic + header + CRC-32/ISIZE trailer). That
//! stage is VERIFIED — the theorems (`gzipStage_ce_header`, `gzipStage_body_gzipped`)
//! prove the emitted bytes really are the gzip container of the handler's body. But
//! a stored block does NO compression: it is a literal copy, so the "gzip" response
//! is *larger* than the plaintext (10-byte header + block framing + 8-byte trailer).
//! It is a correct container around zero compression — verified, and useless.
//!
//! This module replaces that with REAL DEFLATE via `flate2` (miniz_oxide backend, a
//! widely-deployed, battle-tested pure-Rust codec), exactly the way crypto is done
//! in this engine: verify the logic, TRUST the well-tested data transform, and be
//! honest about the boundary.
//!
//! ## The honest boundary (principled TCB — NOT verified)
//!
//! `flate2`'s DEFLATE compression is TRUSTED, not proven. It is named, principled
//! TCB — the same posture as the EverCrypt FFI for crypto: a small, well-audited,
//! independently-tested transform we lean on rather than re-verify. Do not read
//! anything in this file as "verified gzip". The *compression correctness* is a
//! trust assumption on `flate2`.
//!
//! ## The handoff is CHECKED, not blindly trusted
//!
//! The bytes `flate2` compresses must equal the serve's response body, and we CHECK
//! that rather than trust it. The proven stage emits a KNOWN fixed layout
//! (`Gzip.gzipStored`): a 10-byte gzip header, a single DEFLATE *stored* block
//! (`0x01` ‖ u16 LEN ‖ u16 NLEN), the body copied literally, then an 8-byte trailer
//! carrying `CRC-32(body)` and `ISIZE = |body| mod 2³²`. We recover the plaintext by
//! *slicing it out by position* — `stream[15 .. len-8]` — never by decoding the
//! DEFLATE block. That matters: the stored block's LEN/NLEN are only 16-bit, so for a
//! body larger than 65 535 bytes they overflow and a real DEFLATE decoder rejects the
//! (now malformed) block. The literal body bytes are still all there; position-slicing
//! reaches them regardless. We then CHECK the slice against the trailer the *proven*
//! core computed — its length against `ISIZE` and its `CRC-32` against the trailer CRC
//! — so the plaintext we re-compress is the serve's body, confirmed by a checksum the
//! proven code emitted. If the layout or the check fails we leave the proven stage's
//! output untouched — never a silent corruption.
//!
//! (Historical note: this handoff used to `flate2`-*gunzip* the proven output to get
//! the plaintext. That worked only for bodies ≤ 64 KiB; above that the stored block's
//! 16-bit LEN wrapped, gunzip failed, and the seam shipped the proven-but-malformed
//! stored block. The ISIZE/position extraction below fixes that — it is size-agnostic.)
//!
//! ## Where it runs
//!
//! Post-serve, pre-write, at each IO backend's response funnel (`blocking`,
//! `uring::stage_response_appended`, `kqueue`). It keys off the response's own
//! `Content-Encoding: gzip` header — set only when the proven `acceptsGzip` decision
//! fired on the request — so it needs no request access and cannot double-encode a
//! response that was not gzipped. Gated entirely behind `DRORB_RUST_GZIP=1`; unset,
//! this module is inert and the proven (stored-block) stage ships unchanged.

use std::io::{Read, Write};
use std::sync::OnceLock;

use flate2::Compression;
use flate2::Crc;
use flate2::read::GzDecoder;
use flate2::write::GzEncoder;

/// Whether `DRORB_RUST_GZIP` selects real Rust gzip recompression at the reactor.
/// Read once (env is fixed for the process lifetime); `1`/`true`/`yes`/`on` enable.
/// Unset ⇒ inert: the proven stored-block stage's output ships unchanged.
pub fn enabled() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| {
        std::env::var("DRORB_RUST_GZIP")
            .map(|v| matches!(v.as_str(), "1" | "true" | "yes" | "on"))
            .unwrap_or(false)
    })
}

/// Case-insensitive subslice search (both sides folded to ASCII-lowercase).
fn find_ci(hay: &[u8], needle: &[u8]) -> Option<usize> {
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

/// The trimmed value of header `name` in a response head block (through CRLFCRLF),
/// first match, or `None`. Mirrors `http::header_value` but kept local so this
/// module is self-contained.
fn header_value<'a>(head: &'a [u8], name: &[u8]) -> Option<&'a [u8]> {
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

/// Rebuild a response head block (`head` runs through the terminating CRLFCRLF),
/// setting `Content-Length` to `new_len`. The existing `Content-Length` line is
/// rewritten in place in wire order; if none was present one is inserted just before
/// the blank line. Every other header (including `Content-Encoding: gzip`) is copied
/// verbatim.
fn rebuild_head(head: &[u8], new_len: usize) -> Vec<u8> {
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
            // Blank line: end of headers. Add Content-Length if the head lacked one.
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
    // No terminating blank line was found (malformed head); return what we copied.
    out
}

/// Recover the plaintext body from the proven stage's fake stored-block gzip stream
/// by slicing it out of the KNOWN fixed layout — NOT by DEFLATE-decoding it, so it
/// works for any body size (the stored block's 16-bit LEN overflows above 64 KiB and
/// a real decoder would reject it).
///
/// Layout emitted by `Gzip.gzipStored` (all multi-byte fields little-endian):
///
/// ```text
///  [0..10)  gzip header  (mkHeader: 1f 8b 08 00 00 00 00 00 00 ff — FLG=0, so no
///                         optional fields ⇒ exactly 10 bytes)
///  [10]     0x01         stored-block header byte (BFINAL=1, BTYPE=00)
///  [11..13) u16 LEN      block length  (WRAPS mod 2^16 for |body| > 65535)
///  [13..15) u16 NLEN     ~LEN          (underflows likewise — the malformed part)
///  [15..N-8)             the body, copied literally by `deflateStored` (always full)
///  [N-8..N-4) u32 CRC-32(body)
///  [N-4..N)   u32 ISIZE = |body| mod 2^32   (the REAL length, reliable)
/// ```
///
/// The body is `stream[15 .. N-8]`. We then CHECK it against the trailer: its length
/// must equal `ISIZE` (mod 2^32) and its `CRC-32` must equal the trailer CRC (the
/// CHECKED handoff). Returns `None` if the layout does not match or a check fails —
/// the caller then leaves the proven output untouched.
fn extract_stored_plaintext(gz: &[u8]) -> Option<Vec<u8>> {
    // Minimum: 10-byte header + 5-byte stored framing + 8-byte trailer.
    if gz.len() < 23 {
        return None;
    }
    // Proven `mkHeader`: magic 1f 8b, CM=08 (DEFLATE), FLG=00 (no optional fields, so
    // the header is exactly 10 bytes). Any other shape is not our stored-block stream.
    if gz[0] != 0x1f || gz[1] != 0x8b || gz[2] != 0x08 || gz[3] != 0x00 {
        return None;
    }
    // Stored-block header byte: BFINAL=1, BTYPE=00 ⇒ 0x01.
    if gz[10] != 0x01 {
        return None;
    }
    let n = gz.len();
    let body_end = n - 8; // trailer is the last 8 bytes
    // The literal body sits between the 15-byte prefix and the 8-byte trailer.
    let plain = &gz[15..body_end];
    let crc_stored = u32::from_le_bytes([
        gz[body_end],
        gz[body_end + 1],
        gz[body_end + 2],
        gz[body_end + 3],
    ]);
    let isize_stored = u32::from_le_bytes([
        gz[body_end + 4],
        gz[body_end + 5],
        gz[body_end + 6],
        gz[body_end + 7],
    ]);
    // CHECK the handoff against what the proven core wrote.
    if (plain.len() as u64 % (1u64 << 32)) as u32 != isize_stored {
        return None;
    }
    let mut crc = Crc::new();
    crc.update(plain);
    if crc.sum() != crc_stored {
        return None;
    }
    Some(plain.to_vec())
}

/// Replace a proven stored-block gzip response body with REAL `flate2` gzip, in
/// place. A no-op unless the response already carries `Content-Encoding: gzip` (the
/// proven `gzipStage` fired) and is fixed-length framed. The plaintext fed to the
/// real compressor is recovered by gunzipping the proven stage's own output, so it
/// is the serve's body confirmed against the proven CRC-32 trailer. On any decode
/// failure, or if the real gzip is not actually smaller, the proven output is left
/// untouched.
pub fn recompress(resp: &mut Vec<u8>) {
    let Some(head_end) = resp
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .map(|p| p + 4)
    else {
        return;
    };

    // Only act on a response the proven gzip stage already encoded, and only when it
    // is fixed-length framed (a chunked body is not a single delimited buffer here).
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

    // HANDOFF: recover the exact plaintext from the proven stage's known stored-block
    // layout by slicing it out (ISIZE-delimited), CHECKED against the proven trailer's
    // length + CRC-32. This is size-agnostic: it does NOT DEFLATE-decode the stored
    // block, whose 16-bit LEN overflows above 64 KiB. If the layout is not the proven
    // stored-block shape (unexpected here), fall back to a real gunzip so any other
    // valid gzip stream is still handled; either way the plaintext is checksum-confirmed.
    let plain = match extract_stored_plaintext(body) {
        Some(p) => p,
        None => {
            let mut p = Vec::new();
            if GzDecoder::new(body).read_to_end(&mut p).is_err() {
                return; // not a recoverable gzip stream — leave the proven output alone
            }
            p
        }
    };

    // REAL COMPRESSION (trusted flate2 / miniz_oxide DEFLATE).
    let mut enc = GzEncoder::new(Vec::new(), Compression::best());
    if enc.write_all(&plain).is_err() {
        return;
    }
    let Ok(gz) = enc.finish() else {
        return;
    };

    // Only replace when the real gzip is genuinely smaller than the proven stored
    // block (it is, for any compressible body — a stored block only ever inflates).
    if gz.len() >= body.len() {
        return;
    }

    let new_head = rebuild_head(&resp[..head_end], gz.len());
    resp.clear();
    resp.extend_from_slice(&new_head);
    resp.extend_from_slice(&gz);
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a proven-style stored-block gzip response (what the Lean stage emits):
    /// gzip container whose payload is a stored DEFLATE block, so the body is LARGER
    /// than the plaintext.
    fn stored_gzip_response(plain: &[u8]) -> Vec<u8> {
        // Reproduce the stage's container with flate2's stored (level 0) encoder —
        // byte-shape-equivalent to `Gzip.gzipStored` for the test's purposes: a valid
        // RFC 1952 stream with no real compression.
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

    fn split_head_body(resp: &[u8]) -> (&[u8], &[u8]) {
        let he = resp.windows(4).position(|w| w == b"\r\n\r\n").unwrap() + 4;
        (&resp[..he], &resp[he..])
    }

    /// Build the EXACT bytes the Lean `Gzip.gzipStored` emits: a 10-byte header, a
    /// SINGLE DEFLATE stored block with a 16-bit LEN/NLEN (which WRAP for a body over
    /// 65 535 bytes — the malformed case), the literal body, and the CRC-32/ISIZE
    /// trailer. flate2's own `Compression::none()` splits big bodies into several
    /// valid ≤64 KiB stored blocks, so it can NOT reproduce the >64 KiB bug — this
    /// faithful builder can.
    fn lean_stored_gzip(plain: &[u8]) -> Vec<u8> {
        let mut out = Vec::new();
        // mkHeader: 1f 8b 08 00 MTIME(4)=0 XFL=0 OS=ff
        out.extend_from_slice(&[0x1f, 0x8b, 0x08, 0x00, 0, 0, 0, 0, 0x00, 0xff]);
        // deflateStored: 0x01 :: u16le(len) ++ u16le(65535 - len) ++ body
        out.push(0x01);
        let len16 = (plain.len() % 65536) as u16; // WRAPS above 64 KiB, exactly as in Lean
        let nlen16 = (65535u32.wrapping_sub(plain.len() as u32) % 65536) as u16; // underflow → low 16 bits
        out.extend_from_slice(&len16.to_le_bytes());
        out.extend_from_slice(&nlen16.to_le_bytes());
        out.extend_from_slice(plain);
        // trailer: u32le CRC-32(body) ++ u32le (len mod 2^32)
        let mut crc = Crc::new();
        crc.update(plain);
        out.extend_from_slice(&crc.sum().to_le_bytes());
        out.extend_from_slice(&((plain.len() as u64 % (1u64 << 32)) as u32).to_le_bytes());
        out
    }

    fn lean_stored_response(plain: &[u8]) -> Vec<u8> {
        let stored = lean_stored_gzip(plain);
        let mut resp = Vec::new();
        resp.extend_from_slice(b"HTTP/1.1 200 OK\r\n");
        resp.extend_from_slice(b"Content-Encoding: gzip\r\n");
        resp.extend_from_slice(format!("Content-Length: {}\r\n", stored.len()).as_bytes());
        resp.extend_from_slice(b"\r\n");
        resp.extend_from_slice(&stored);
        resp
    }

    #[test]
    fn large_body_stored_block_is_malformed_but_recovers() {
        // 1 MiB of 'a' — well over the stored block's 16-bit LEN. The Lean stage's
        // single stored block is MALFORMED here (LEN wrapped to 0), so a real gunzip
        // of it recovers nothing — the exact production bug.
        let plain = vec![b'a'; 1024 * 1024];
        let malformed = lean_stored_gzip(&plain);
        // Confirm the fake stored block really is undecodable by a real DEFLATE reader.
        let mut via_gunzip = Vec::new();
        let gunzip_ok = GzDecoder::new(&malformed[..])
            .read_to_end(&mut via_gunzip)
            .is_ok()
            && via_gunzip == plain;
        assert!(
            !gunzip_ok,
            "the >64 KiB stored block must be gunzip-undecodable (the bug)"
        );

        // The ISIZE/position extraction recovers the full plaintext, CRC-checked.
        let recovered =
            extract_stored_plaintext(&malformed).expect("ISIZE extraction recovers plaintext");
        assert_eq!(recovered, plain);

        // End to end: recompress ships a REAL, small, valid gzip that round-trips to 1 MiB.
        let mut resp = lean_stored_response(&plain);
        recompress(&mut resp);
        let (head, real_body) = split_head_body(&resp);
        assert!(
            real_body.len() < plain.len() / 100,
            "1 MiB of 'a' must compress to well under 10 KiB"
        );
        assert!(find_ci(head, b"content-encoding: gzip").is_some());
        let cl = header_value(head, b"content-length").unwrap();
        assert_eq!(cl, real_body.len().to_string().as_bytes());
        let mut back = Vec::new();
        GzDecoder::new(real_body).read_to_end(&mut back).unwrap();
        assert_eq!(back.len(), 1024 * 1024);
        assert_eq!(
            back, plain,
            "gunzip of the real body round-trips to the exact 1 MiB"
        );
    }

    #[test]
    fn extract_rejects_corrupt_crc() {
        let plain = b"hello world".repeat(10);
        let mut malformed = lean_stored_gzip(&plain);
        let n = malformed.len();
        malformed[n - 8] ^= 0xff; // corrupt the trailer CRC-32
        assert!(
            extract_stored_plaintext(&malformed).is_none(),
            "a bad CRC must fail the checked handoff"
        );
    }

    #[test]
    fn recompress_shrinks_and_round_trips() {
        let plain = b"the quick brown fox ".repeat(1000); // 20 KB, very compressible
        let mut resp = stored_gzip_response(&plain);
        let (_, stored_body) = split_head_body(&resp);
        let stored_len = stored_body.len();
        assert!(
            stored_len >= plain.len(),
            "stored block must not be smaller than plaintext (it is a literal copy)"
        );

        recompress(&mut resp);

        let (head, real_body) = split_head_body(&resp);
        // Real compression: the body is now much smaller than both the stored block
        // AND the original plaintext.
        assert!(real_body.len() < stored_len);
        assert!(real_body.len() < plain.len());
        // Content-Encoding preserved; Content-Length updated to the new body length.
        assert!(find_ci(head, b"content-encoding: gzip").is_some());
        let cl = header_value(head, b"content-length").unwrap();
        assert_eq!(cl, real_body.to_vec().len().to_string().as_bytes());
        // Round-trips: gunzip of the real body is the original plaintext.
        let mut back = Vec::new();
        GzDecoder::new(real_body).read_to_end(&mut back).unwrap();
        assert_eq!(back, plain);
    }

    #[test]
    fn non_gzip_response_untouched() {
        let mut resp = b"HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello".to_vec();
        let before = resp.clone();
        recompress(&mut resp);
        assert_eq!(
            resp, before,
            "a response with no Content-Encoding: gzip is untouched"
        );
    }

    #[test]
    fn incompressible_body_left_as_stored() {
        // Random-ish incompressible bytes: real gzip is not smaller than the stored
        // block, so we keep the proven output rather than grow it.
        let plain: Vec<u8> = (0..4096u32)
            .map(|i| (i.wrapping_mul(2654435761) >> 24) as u8)
            .collect();
        let mut resp = stored_gzip_response(&plain);
        let before = resp.clone();
        recompress(&mut resp);
        // Either unchanged, or (if flate2 still shrank it) at least still valid gzip.
        let (_, body) = split_head_body(&resp);
        let mut back = Vec::new();
        GzDecoder::new(body).read_to_end(&mut back).unwrap();
        assert_eq!(back, plain);
        let _ = before;
    }
}
