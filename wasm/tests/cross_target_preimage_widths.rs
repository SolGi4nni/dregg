//! **A PREIMAGE WHOSE LENGTH DEPENDS ON THE TARGET — measured on both, not read.**
//!
//! `usize::to_le_bytes()` is 8 bytes on x86_64/aarch64 and **4 on wasm32**. A `usize` fed
//! straight into a hash preimage therefore makes a native producer and a browser consumer
//! commit to different bytes from identical inputs, with nothing red — this repo has already
//! paid for that once, and `wasm` is in the root `exclude` list so no workspace check reaches
//! it.
//!
//! Two live sites carried it into the wasm32 bundle until 2026-08-01, both fixed to `as u64`
//! (byte-identical on a 64-bit host, so no native value moved):
//!
//! * `dregg_intent::pir::EncryptedDatabase::{encrypt, decrypt_row}` — the per-row key of
//!   download-all PIR. The row cipher is a bare XOR keystream with **no tag**, so a tab
//!   decrypting a natively-encrypted row got silent garbage felts rather than an error. Row 0
//!   diverged too: it is the concat LENGTH that differs, not the digits.
//! * `dregg_bridge::present::hash_index` — a BLAKE3 preimage folded to a `BabyBear` sibling
//!   felt, i.e. a Merkle tree built differently on the two targets.
//!
//! ## Why the expectations here are not decoration
//!
//! Each pin RESTATES the preimage with an explicit `[u8; 8]` written out digit by digit, so it
//! is target-independent BY CONSTRUCTION and never calls `usize::to_le_bytes` itself. A native
//! run cannot see a revert — on a 64-bit host the two spellings are the same bytes — which is
//! exactly why this file must run on `wasm32`:
//!
//!   `wasm-pack test --node wasm --test cross_target_preimage_widths`
//!   `cargo test -p dregg-wasm --test cross_target_preimage_widths`   (host leg)
//!
//! ⚠ The cargo filter goes BEFORE `--`. `wasm-pack test … -- --test <name>` (the spelling in a
//! sibling test file's header) reaches `wasm-bindgen-test-runner`, not cargo, and errors with
//! "unexpected argument '--test' found".
//!
//! Both legs assert the SAME constants, so the pair is the real gate: agreement across the two
//! targets is the property, and a revert breaks the wasm32 leg while leaving the host leg green.

use dregg_circuit::field::BABYBEAR_P;
use dregg_intent::pir::EncryptedDatabase;

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::wasm_bindgen_test;

/// Fixed inputs — nothing here is derived from `usize`.
const SECRET: [u8; 32] = [0xa5; 32];
const NONCE: [u8; 32] = [0x5a; 32];
const KEY: [u8; 32] = [0x11; 32];

/// A ciphertext row of fixed bytes (the plaintext is irrelevant — what is under test is
/// which key the row index derives).
fn fixed_rows() -> Vec<Vec<u8>> {
    (0..4u8)
        .map(|r| (0..32u8).map(|b| b ^ r).collect::<Vec<u8>>())
        .collect()
}

/// The per-row key, restated with the row index written as an EXPLICIT 8-byte little-endian
/// value. This never calls `usize::to_le_bytes`, so it means the same thing on every target.
fn expected_row_key(row_idx: u8) -> [u8; 32] {
    let idx8: [u8; 8] = [row_idx, 0, 0, 0, 0, 0, 0, 0];
    let mut ctx = Vec::new();
    ctx.extend_from_slice(&SECRET);
    ctx.extend_from_slice(&idx8);
    ctx.extend_from_slice(&NONCE);
    blake3::derive_key("dregg-pir-download-all-row-key", &ctx)
}

/// The plaintext felts that key implies, restated from the algorithm rather than captured
/// from a run.
fn expected_row_felts(row_idx: u8, cipher: &[u8]) -> Vec<u32> {
    let mut keystream = vec![0u8; cipher.len()];
    let mut hasher = blake3::Hasher::new_keyed(&expected_row_key(row_idx));
    hasher.update(b"keystream");
    hasher.finalize_xof().fill(&mut keystream);
    cipher
        .iter()
        .zip(keystream.iter())
        .map(|(a, b)| a ^ b)
        .collect::<Vec<u8>>()
        .chunks(4)
        // `decrypt_row` decodes each 4-byte chunk through `BabyBear::new`, which reduces mod
        // the prime. That canonicalisation is not what is under test, so restate it rather
        // than compare a raw `u32` against a reduced one.
        .map(|c| {
            dregg_circuit::field::BabyBear::new(u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
                .as_u32()
        })
        .collect()
}

/// **PIR download-all derives the same per-row key on both targets.** Reverting the `as u64`
/// in `intent/src/pir.rs` shortens the context by four bytes on `wasm32` only, and this fails
/// there while staying green on the host.
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
#[cfg_attr(not(target_arch = "wasm32"), test)]
fn pir_per_row_key_does_not_depend_on_the_width_of_usize() {
    let rows = fixed_rows();
    let db = EncryptedDatabase {
        encrypted_rows: rows.clone(),
        session_nonce: NONCE,
        real_row_count: rows.len(),
    };
    // Row 0 is included DELIBERATELY: the divergence is in the context LENGTH, so even an
    // all-zero index derives a different key when the width moves.
    for row_idx in 0u8..4 {
        let got: Vec<u32> = db
            .decrypt_row(row_idx as usize, &SECRET)
            .expect("row present")
            .iter()
            .map(|f| f.as_u32())
            .collect();
        assert_eq!(
            got,
            expected_row_felts(row_idx, &rows[row_idx as usize]),
            "row {row_idx}: the per-row key must come from an 8-byte index on every target \
             (size_of::<usize>() here = {})",
            core::mem::size_of::<usize>()
        );
    }
}

/// **The synthetic-membership sibling felt is the same felt on both targets.** Reverting the
/// `as u64` in `bridge/src/present.rs` makes a native prover and a browser client build
/// different Merkle trees from identical inputs.
#[cfg_attr(target_arch = "wasm32", wasm_bindgen_test)]
#[cfg_attr(not(target_arch = "wasm32"), test)]
fn hash_index_does_not_depend_on_the_width_of_usize() {
    for (level, sib) in [(0u8, 0u8), (1, 2), (7, 3)] {
        let mut preimage = Vec::new();
        preimage.extend_from_slice(&[level, 0, 0, 0, 0, 0, 0, 0]);
        preimage.extend_from_slice(&[sib, 0, 0, 0, 0, 0, 0, 0]);
        preimage.extend_from_slice(&KEY);
        let d = blake3::hash(&preimage);
        let b = d.as_bytes();
        let expected = u32::from_le_bytes([b[0], b[1], b[2], b[3]]) % BABYBEAR_P;
        assert_eq!(
            dregg_bridge::present::hash_index(level as usize, sib as usize, &KEY),
            expected,
            "hash_index({level},{sib}) must absorb an 8-byte index on every target \
             (size_of::<usize>() here = {})",
            core::mem::size_of::<usize>()
        );

        // THE DISCRIMINATOR, so the pin above is visibly not vacuous. This is the felt the
        // PRE-FIX code produced on wasm32 — a 4-byte index — and it must not be the answer.
        // On a 64-bit host it is merely a different preimage; on wasm32 it is the exact value
        // reverting the `as u64` would restore, measured 2026-08-01 as 1651138428 for (1, 2).
        let mut short = Vec::new();
        short.extend_from_slice(&[level, 0, 0, 0]);
        short.extend_from_slice(&[sib, 0, 0, 0]);
        short.extend_from_slice(&KEY);
        let sd = blake3::hash(&short);
        let sb = sd.as_bytes();
        assert_ne!(
            dregg_bridge::present::hash_index(level as usize, sib as usize, &KEY),
            u32::from_le_bytes([sb[0], sb[1], sb[2], sb[3]]) % BABYBEAR_P,
            "hash_index({level},{sib}) absorbed a FOUR-byte index — the wasm32 width regression"
        );
    }
}

/// The meaningfulness guard for the `wasm32` leg: if `usize` were 8 bytes here, the two tests
/// above could not tell a reverted fix from a correct one.
#[cfg(target_arch = "wasm32")]
#[wasm_bindgen_test]
fn usize_is_four_bytes_on_this_target() {
    assert_eq!(
        core::mem::size_of::<usize>(),
        4,
        "the two pins above are only a gate on a 32-bit-usize target"
    );
}
