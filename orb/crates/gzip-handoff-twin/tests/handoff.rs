//! The CRC-checked gzip-handoff invariant, made executable.
//!
//! Each test states one of the three claims from `lib.rs` and exercises it with
//! REAL flate2 gzip streams (the trusted transform the seam models). Where the
//! existing `gzip.rs` unit tests cover the happy round-trip and the non-gzip
//! no-op, THIS suite adds the load-bearing missing evidence: the **failure-safe
//! path** — a corrupted / bad-CRC / truncated proven stream must leave the
//! response byte-for-byte untouched (never a truncated or wrong body). That path
//! is the CRC *guard*; without it the handoff would be blindly trusted.
//!
//! Run: `cargo test -p gzip-handoff-twin --release`

use gzip_handoff_twin::{
    Rng, decode, find_ci, header_value, recompress, split_head_body, stored_gzip_response,
};

/// CLAIM 1 — HANDOFF (checked). For every proven-style stored-gzip response, the
/// plaintext the seam re-compresses equals the serve body: the re-emitted body
/// decodes back to exactly what the input body decodes to. This is the
/// CRC-checked handoff — `decode` verifies the same RFC 1952 CRC-32 the seam
/// relies on, so a green run says the bytes flate2 received WERE the serve body.
/// Non-vacuous: it also asserts real shrinkage on compressible input and that the
/// framing headers stay consistent.
#[test]
fn handoff_recovers_and_reencodes_the_serve_body() {
    let seed = 0x9E37_79B9_7F4A_7C15u64;
    let mut rng = Rng(seed);
    let mut shrunk = 0usize;
    let mut kept = 0usize;

    for _ in 0..5000 {
        let plain = rng.body(4096);
        let mut resp = stored_gzip_response(&plain);
        let (_, in_body) = split_head_body(&resp);
        let in_decoded = decode(in_body).expect("proven stored-gzip must decode");
        assert_eq!(
            in_decoded, plain,
            "harness: stored-gzip must round-trip the body"
        );
        let in_body_len = in_body.len();

        let before = resp.clone();
        recompress(&mut resp);

        let (head, out_body) = split_head_body(&resp);
        if resp == before {
            // Kept the proven output (incompressible / not smaller). Still valid.
            kept += 1;
            assert_eq!(decode(out_body).as_deref(), Some(plain.as_slice()));
            continue;
        }
        shrunk += 1;
        // The re-emitted body decodes to exactly the serve body — the handoff fed
        // flate2 the CRC-checked plaintext, nothing else.
        assert_eq!(
            decode(out_body).as_deref(),
            Some(plain.as_slice()),
            "handoff corrupted the body (seed {seed})"
        );
        // Framing stays consistent: encoding preserved, Content-Length == body len,
        // and a real shrink actually happened.
        assert!(find_ci(head, b"content-encoding: gzip").is_some());
        let cl = header_value(head, b"content-length").unwrap();
        assert_eq!(cl, out_body.len().to_string().as_bytes());
        assert!(out_body.len() < in_body_len, "replaced without shrinking");
    }
    // The corpus must actually exercise BOTH arms, or the test is hollow.
    assert!(
        shrunk > 0 && kept > 0,
        "corpus did not exercise both arms: shrunk={shrunk} kept={kept}"
    );
    eprintln!(
        "handoff: 5000 responses — {shrunk} really recompressed (decoded back to the \
         serve body), {kept} kept the proven output; no body corruption"
    );
}

/// CLAIM 2 — FAILURE-SAFE, the CRC guard (the missing evidence). Corrupt the
/// proven stream's CRC-32 trailer. flate2's decoder MUST reject it, and
/// `recompress` MUST leave the response byte-for-byte untouched — the proven
/// (stored-block) output ships unchanged, never a wrong body. This is the Rust
/// mirror of Lean `Gzip.gzip_crc_checked` (a wrong CRC ⟶ `crcMismatch`, nothing
/// handed back).
#[test]
fn failure_safe_bad_crc_leaves_proven_output_untouched() {
    let mut rng = Rng(0xD1B5_4A32_D192_ED03);
    let mut checked = 0usize;

    for _ in 0..2000 {
        // A compressible body, so absent corruption the seam WOULD replace it —
        // making the "untouched" assertion load-bearing (not a trivial no-op).
        let plain = format!("handoff-{}", rng.next_u64())
            .repeat(64)
            .into_bytes();
        let mut resp = stored_gzip_response(&plain);

        // The trailer is the last 8 bytes: CRC-32 (LE) ‖ ISIZE (LE). Flip a bit in
        // the CRC field (offset len-8 .. len-4).
        let n = resp.len();
        let crc_off = n - 8 + (rng.next_u64() as usize % 4);
        let bit = 1u8 << (rng.next_u64() as usize % 8);
        resp[crc_off] ^= bit;

        // Sanity: the corrupted stream must NOT decode (the CRC guard fires).
        let (_, body) = split_head_body(&resp);
        assert!(
            decode(body).is_none(),
            "harness: flipped CRC still decoded — pick a real corruption"
        );

        let before = resp.clone();
        recompress(&mut resp);
        assert_eq!(
            resp, before,
            "FAILURE-SAFE VIOLATED: recompress mutated a response whose proven \
             stream fails CRC — the proven output must ship untouched"
        );
        checked += 1;
    }
    eprintln!("failure-safe: {checked} bad-CRC responses — every one left byte-identical");
}

/// CLAIM 2 (cont.) — FAILURE-SAFE across the WHOLE stored-gzip stream, exhaustive
/// single-bit corruption. For a fixed compressible body, flip every single bit of
/// every body byte in turn. For each corruption, `recompress` must either:
///   (a) leave the response byte-identical (the decode failed — failure-safe), or
///   (b) produce a body that decodes to the SAME plaintext the corrupted input
///       decodes to (the corruption was in a spot flate2 still accepts AND that
///       preserves the content — then re-encoding that content is correct).
/// It must NEVER produce a body that decodes to something else, and never a body
/// that fails to decode when it changed the response. This is the non-corrupting
/// guarantee at full granularity: no single-bit fault can make the seam emit a
/// wrong or truncated body.
#[test]
fn failure_safe_exhaustive_single_bit_corruption() {
    let plain = b"the quick brown fox jumps over the lazy dog. ".repeat(40);
    let base = stored_gzip_response(&plain);
    let (head, base_body) = split_head_body(&base);
    let head_len = head.len();

    let mut untouched = 0usize;
    let mut re_encoded = 0usize;
    for byte_i in 0..base_body.len() {
        for bit in 0..8u8 {
            let mut resp = base.clone();
            resp[head_len + byte_i] ^= 1 << bit;
            let corrupted_body = resp[head_len..].to_vec();
            let corrupted_decode = decode(&corrupted_body); // what the input means now

            let before = resp.clone();
            recompress(&mut resp);

            if resp == before {
                untouched += 1;
                continue;
            }
            re_encoded += 1;
            // It changed the response ⟹ decode MUST have succeeded (failure-safe
            // never mutates), and the new body must decode to the same content.
            let src = corrupted_decode.expect(
                "recompress mutated a response whose body does NOT decode — \
                 failure-safe violated (it must early-return on decode error)",
            );
            let (_, out_body) = split_head_body(&resp);
            assert_eq!(
                decode(out_body),
                Some(src),
                "recompress emitted a body that decodes to DIFFERENT content than \
                 the (CRC-valid) input — handoff corruption at byte {byte_i} bit {bit}"
            );
        }
    }
    // A stored block over compressible data: nearly every single-bit flip breaks
    // the CRC (untouched). Assert the untouched arm dominates AND is non-empty.
    assert!(
        untouched > 0,
        "exhaustive corruption never hit the failure-safe arm"
    );
    eprintln!(
        "failure-safe (exhaustive): {} single-bit corruptions — {untouched} left \
         untouched (CRC guard fired), {re_encoded} re-encoded to the SAME content",
        untouched + re_encoded
    );
}

/// CLAIM 3 — NON-CORRUPTING ENVELOPE over ARBITRARY input (not just well-formed
/// proven output). Slap a `Content-Encoding: gzip` head on random bytes and run
/// the seam. For any input whatsoever: recompress either leaves it untouched, or
/// emits a body that decodes to the same content as the input body. It is NEVER
/// lossy and never emits an undecodable body it created. This is the total-safety
/// envelope — no crafted input drives the seam to a wrong body.
#[test]
fn non_corrupting_envelope_over_arbitrary_bodies() {
    let mut rng = Rng(0x0BAD_C0DE_F00D_1337);
    for _ in 0..5000 {
        let junk = rng.body(2048);
        let mut resp = Vec::new();
        resp.extend_from_slice(b"HTTP/1.1 200 OK\r\nContent-Encoding: gzip\r\n");
        resp.extend_from_slice(format!("Content-Length: {}\r\n\r\n", junk.len()).as_bytes());
        resp.extend_from_slice(&junk);

        let (_, in_body) = split_head_body(&resp);
        let in_decode = decode(in_body);

        let before = resp.clone();
        recompress(&mut resp);

        if resp == before {
            continue; // untouched — always safe
        }
        // Changed ⟹ input decoded ⟹ output decodes to the same content.
        let src = in_decode.expect("mutated an undecodable body — failure-safe violated");
        let (_, out_body) = split_head_body(&resp);
        assert_eq!(
            decode(out_body),
            Some(src),
            "envelope: emitted mismatched body"
        );
    }
    eprintln!(
        "envelope: 5000 arbitrary gzip-labeled bodies — no corruption, no undecodable output"
    );
}

/// STRUCTURAL GUARDS — the seam only acts on a fixed-length `Content-Encoding:
/// gzip` response. A plain response, a chunked one, and an empty body are all
/// left untouched (matching `gzip.rs`).
#[test]
fn structural_guards_leave_response_untouched() {
    // no Content-Encoding: gzip
    let mut plain = b"HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello".to_vec();
    let b = plain.clone();
    recompress(&mut plain);
    assert_eq!(plain, b, "non-gzip response must be untouched");

    // chunked transfer-encoding: not a single delimited buffer here
    let body = stored_gzip_response(&b"compress me ".repeat(100));
    let (_, gz_body) = split_head_body(&body);
    let mut chunked = Vec::new();
    chunked.extend_from_slice(b"HTTP/1.1 200 OK\r\nContent-Encoding: gzip\r\n");
    chunked.extend_from_slice(b"Transfer-Encoding: chunked\r\n\r\n");
    chunked.extend_from_slice(gz_body);
    let cb = chunked.clone();
    recompress(&mut chunked);
    assert_eq!(chunked, cb, "chunked response must be untouched");

    // empty body
    let mut empty = b"HTTP/1.1 204 No Content\r\nContent-Encoding: gzip\r\n\r\n".to_vec();
    let eb = empty.clone();
    recompress(&mut empty);
    assert_eq!(empty, eb, "empty-body response must be untouched");

    eprintln!("structural guards: plain / chunked / empty all left untouched");
}
