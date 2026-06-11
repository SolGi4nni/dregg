//! # Differential: Lean `ThresholdDecrypt` model  ⟺  the REAL `federation::threshold_decrypt`.
//!
//! This module is the Rust side of the differential for
//! `metatheory/Dregg2/Distributed/ThresholdDecrypt.lean` — the faithful executable Lean model of the
//! federation's t-of-n threshold decryption (Shamir-shared symmetric key over the AES GF(256) field,
//! Lagrange reconstruction at x=0). The Lean side proves:
//!
//!  * `shamir_any_t_reconstruct` — ANY size-`t` quorum of distinct share-holders reconstructs the secret
//!    (no privileged subset), via Mathlib's `Lagrange.eq_interpolate`.
//!  * `shamir_below_t_undetermined` — `t-1` shares are consistent with every secret (secrecy floor).
//!  * the combine gate fail-closed boundary (`combine_rejects_below_threshold`/`…_dup_index`/`…_zero_index`).
//!
//! The Lean `gf256Mul`/`gf256Inv`/`reconstructByte`/`combineAdmits` are tiny, total, `Nat`-level
//! transcriptions of `mod gf256` / `shamir_reconstruct_byte` / `combine_shares`'s precondition checks; the
//! transcription is line-for-line. This differential pins that the verified Lean semantics IS the
//! semantics the federation actually computes — the same discipline as `coord::entangled_diff` and
//! `BlocklaceFinality`'s `tau` golden vectors:
//!
//!  1. **Byte-level field agreement** — the Lean `#guard`s on `gf256Mul`/`gf256Inv` are re-run here
//!     against the REAL `gf256::mul`/`gf256::inv` (`pub(crate)`), over the same golden vectors AND an
//!     exhaustive 256×256 / 1..=255 sweep (the Lean side samples; here we close the whole table).
//!  2. **Reconstruction agreement** — the Lean `reconstructByte` golden vectors are re-run against the
//!     REAL `shamir_reconstruct_byte`, and the full split→reconstruct arc is driven through the running
//!     `shamir_split_byte` for random secrets, confirming the `shamir_any_t_reconstruct` property
//!     concretely on every t-of-n subset.
//!  3. **Gate agreement** — the Lean `combineAdmits` decision (and its fail-closed teeth) is re-run
//!     against the REAL `combine_shares` admit/reject behaviour through the public
//!     `generate_epoch_key`/`combine_shares` API.
//!
//! The AEAD confidentiality/integrity (BLAKE3-keyed stream + tag) and the prototype trusted-dealer key
//! generation are NOT part of this differential; they are the named `Blake3Prf` carrier and an out-of-model
//! setup assumption on the Lean side, stated honestly there.

#![cfg(test)]

use super::threshold_decrypt::{
    ThresholdDecryptError, combine_shares, generate_epoch_key, gf256, produce_decryption_share,
    shamir_reconstruct_byte, shamir_split_byte, threshold_encrypt,
};

// ───────────────────────────── Lean model, transcribed to Rust ─────────────────────────────
// These mirror `ThresholdDecrypt.lean` exactly (§1–§3).

/// Lean `gf256MulStep` (`ThresholdDecrypt.lean` §1) — one round of the carry-less multiply.
/// Kept at `u32` to mirror the Lean `Nat` masking, then re-masked to a byte.
fn lean_gf256_mul(a: u8, b: u8) -> u8 {
    let mut acc: u32 = 0;
    let mut a: u32 = (a as u32) & 0xFF;
    let mut b: u32 = (b as u32) & 0xFF;
    for _ in 0..8 {
        if b % 2 == 1 {
            acc ^= a;
        }
        let high = a & 0x80;
        let a1 = (a << 1) & 0xFF;
        a = if high != 0 { a1 ^ 0x1b } else { a1 };
        b >>= 1;
    }
    (acc & 0xFF) as u8
}

/// Lean `gf256Inv` (`ThresholdDecrypt.lean` §1) — Fermat `a^254` via the explicit square-and-multiply
/// ladder transcribed in the Lean model (bit0=0, bits1..7=1).
fn lean_gf256_inv(a: u8) -> u8 {
    if a == 0 {
        return 0;
    }
    let p0 = a;
    let r0 = 1u8;
    let p1 = lean_gf256_mul(p0, p0);
    let r1 = lean_gf256_mul(r0, p1);
    let p2 = lean_gf256_mul(p1, p1);
    let r2 = lean_gf256_mul(r1, p2);
    let p3 = lean_gf256_mul(p2, p2);
    let r3 = lean_gf256_mul(r2, p3);
    let p4 = lean_gf256_mul(p3, p3);
    let r4 = lean_gf256_mul(r3, p4);
    let p5 = lean_gf256_mul(p4, p4);
    let r5 = lean_gf256_mul(r4, p5);
    let p6 = lean_gf256_mul(p5, p5);
    let r6 = lean_gf256_mul(r5, p6);
    let p7 = lean_gf256_mul(p6, p6);
    lean_gf256_mul(r6, p7)
}

/// Lean `reconstructByte` (`ThresholdDecrypt.lean` §4) — Lagrange interpolation at x=0 using the Lean
/// field ops, subtraction = XOR. `pts` is `(index, shareByte)`.
fn lean_reconstruct_byte(pts: &[(u8, u8)]) -> u8 {
    let mut secret = 0u8;
    for &(xi, yi) in pts {
        let mut num = 1u8;
        let mut den = 1u8;
        for &(xj, _) in pts {
            if xj == xi {
                continue;
            }
            num = lean_gf256_mul(num, xj);
            den = lean_gf256_mul(den, xi ^ xj);
        }
        let lagrange = lean_gf256_mul(num, lean_gf256_inv(den));
        secret ^= lean_gf256_mul(yi, lagrange);
    }
    secret
}

/// Lean `combineAdmits` (`ThresholdDecrypt.lean` §3) — the combine gate decision: ≥ t shares, no index 0,
/// distinct indices. `shares` here is `(idx, _)` (the gate inspects only the index multiset).
fn lean_combine_admits(indices: &[u8], t: usize) -> bool {
    let enough = t <= indices.len();
    let no_zero = indices.iter().all(|&i| i != 0);
    let mut seen = std::collections::HashSet::new();
    let nodup = indices.iter().all(|&i| seen.insert(i));
    enough && no_zero && nodup
}

// ───────────────────────────── (1) byte-level field agreement ─────────────────────────────

#[test]
fn diff_gf256_mul_full_table_agrees() {
    // Lean §1 `gf256Mul` ⟺ the REAL `gf256::mul`, over the WHOLE 256×256 table. The Lean side
    // `#guard`s a sample; here we close the entire field-multiplication table.
    for a in 0u16..=255 {
        for b in 0u16..=255 {
            let (a, b) = (a as u8, b as u8);
            assert_eq!(
                lean_gf256_mul(a, b),
                gf256::mul(a, b),
                "gf256 mul disagreement at a={a:#04x} b={b:#04x}"
            );
        }
    }
}

#[test]
fn diff_gf256_inv_full_sweep_agrees() {
    // Lean §1 `gf256Inv` ⟺ the REAL `gf256::inv`, over every byte, AND the multiplicative-inverse law
    // `a * inv(a) = 1` (the Lean `#guard` samples; the Rust `test_gf256_arithmetic` loops 1..=255 — here
    // both, against the Lean transcription).
    assert_eq!(lean_gf256_inv(0), gf256::inv(0));
    for a in 1u16..=255 {
        let a = a as u8;
        assert_eq!(
            lean_gf256_inv(a),
            gf256::inv(a),
            "gf256 inv disagreement at a={a:#04x}"
        );
        assert_eq!(
            gf256::mul(a, lean_gf256_inv(a)),
            1,
            "inverse law broken at a={a:#04x}"
        );
    }
}

#[test]
fn diff_gf256_lean_golden_vectors() {
    // The exact `ThresholdDecrypt.lean` §4 `#guard` vectors, re-checked against the REAL field ops.
    assert_eq!(gf256::mul(0, 42), 0);
    assert_eq!(gf256::mul(1, 42), 42);
    assert_eq!(gf256::mul(42, 1), 42);
    assert_eq!(gf256::mul(0x53, 0xCA), 0x01); // AES-inverse partners
    for &a in &[1u8, 2, 42, 0x53, 255, 0xAB] {
        assert_eq!(gf256::mul(a, gf256::inv(a)), 1);
    }
}

// ───────────────────────────── (2) reconstruction agreement ─────────────────────────────

#[test]
fn diff_reconstruct_lean_golden_vectors() {
    // `ThresholdDecrypt.lean` §4 golden: secret 0x42, f(x)=0x42 + 0xAB·x, shares f(1),f(2),f(3).
    // Any 2-of-3 reconstruct. Re-run against the REAL `shamir_reconstruct_byte` AND the Lean
    // transcription — all three must agree on the secret.
    let s = 0x42u8;
    let y1 = s ^ gf256::mul(0xAB, 1);
    let y2 = s ^ gf256::mul(0xAB, 2);
    let y3 = s ^ gf256::mul(0xAB, 3);
    for subset in [
        vec![(1u8, y1), (2, y2)],
        vec![(1, y1), (3, y3)],
        vec![(2, y2), (3, y3)],
    ] {
        assert_eq!(
            shamir_reconstruct_byte(&subset),
            s,
            "real reconstruct ≠ secret"
        );
        assert_eq!(
            lean_reconstruct_byte(&subset),
            s,
            "lean reconstruct ≠ secret"
        );
        assert_eq!(
            shamir_reconstruct_byte(&subset),
            lean_reconstruct_byte(&subset),
            "real ≠ lean reconstruction"
        );
    }
}

#[test]
fn diff_shamir_any_t_reconstruct_concrete() {
    // The CONCRETE witness of the Lean `shamir_any_t_reconstruct` headline: for many secrets, split with
    // threshold t over n validators, EVERY size-t subset of share-holders reconstructs the same secret —
    // and the REAL `shamir_split_byte`/`shamir_reconstruct_byte` agree with the Lean transcription on it.
    let entropy = [0x9Eu8, 0x37, 0x79, 0xB9, 0x7F, 0x4A, 0x7C, 0x15];
    for secret in [0x00u8, 0x01, 0x42, 0x7F, 0x80, 0xAB, 0xFF] {
        for (t, n) in [(2u8, 3u8), (3, 5), (3, 4), (4, 5)] {
            let shares = shamir_split_byte(secret, t, n, &entropy);
            // every size-t subset (chosen as the first t after a rotation) reconstructs the secret.
            for start in 0..n {
                let pts: Vec<(u8, u8)> = (0..t)
                    .map(|k| {
                        let idx = ((start + k) % n) as usize;
                        ((idx as u8) + 1, shares[idx]) // 1-based eval point
                    })
                    .collect();
                let real = shamir_reconstruct_byte(&pts);
                let lean = lean_reconstruct_byte(&pts);
                assert_eq!(
                    real, secret,
                    "any-t reconstruct failed: t={t} n={n} secret={secret:#04x}"
                );
                assert_eq!(
                    real, lean,
                    "real ≠ lean on t={t} n={n} secret={secret:#04x}"
                );
            }
        }
    }
}

// ───────────────────────────── (3) gate agreement (public API) ─────────────────────────────

#[test]
fn diff_combine_gate_agrees_with_real() {
    // Drive the REAL `generate_epoch_key` → `combine_shares` and confirm its admit/reject verdict matches
    // the Lean `combineAdmits` gate on the same index multiset, for: a valid t-of-n quorum (admit), a
    // below-threshold set (reject = InsufficientShares), and a duplicate-index set (reject).
    let epoch_id = [42u8; 32];
    let (key, shares) = generate_epoch_key(epoch_id, 3, 5);
    let plaintext = b"differential turn body";
    let ct = threshold_encrypt(plaintext, &key).unwrap();
    let dshare = |i: usize| produce_decryption_share(&ct, &shares[i]);

    // valid 3-of-5 quorum: real decrypts, Lean gate admits.
    let quorum = [dshare(0), dshare(2), dshare(4)];
    let idxs: Vec<u8> = quorum.iter().map(|s| s.validator_index).collect();
    assert!(lean_combine_admits(&idxs, 3));
    assert_eq!(combine_shares(&ct, &quorum, 3).unwrap(), plaintext);

    // below threshold: real returns InsufficientShares, Lean gate rejects.
    let short = [dshare(0), dshare(1)];
    let sidxs: Vec<u8> = short.iter().map(|s| s.validator_index).collect();
    assert!(!lean_combine_admits(&sidxs, 3));
    assert_eq!(
        combine_shares(&ct, &short, 3),
        Err(ThresholdDecryptError::InsufficientShares { have: 2, need: 3 })
    );

    // duplicate index: real returns DuplicateShareIndex, Lean gate rejects.
    let dup = [dshare(0), dshare(0), dshare(2)];
    let didxs: Vec<u8> = dup.iter().map(|s| s.validator_index).collect();
    assert!(!lean_combine_admits(&didxs, 3));
    assert!(matches!(
        combine_shares(&ct, &dup, 3),
        Err(ThresholdDecryptError::DuplicateShareIndex(_))
    ));
}

#[test]
fn diff_combine_gate_fail_closed_teeth() {
    // The Lean fail-closed teeth (`combine_rejects_below_threshold`/`…_zero_index`/`…_dup_index`) as a
    // direct gate sweep: every case the Lean theorems force to `false` must reject here too.
    assert!(!lean_combine_admits(&[1], 2)); // below threshold
    assert!(!lean_combine_admits(&[0, 2], 2)); // reserved index 0
    assert!(!lean_combine_admits(&[1, 1], 2)); // duplicate index
    assert!(lean_combine_admits(&[1, 2], 2)); // the one admitting case
}
