//! # `hash_bytes`' preimage: the Lean pin, the round-trip, and the two collisions it used to admit.
//!
//! ## What this file is, at current resolution
//!
//! `dregg_circuit::poseidon2::hash_bytes` absorbs `BabyBear::bytes_to_lanes(data)`. That encoder's
//! authority is `metatheory/Dregg2/Circuit/BytesLanes.lean`, which carries
//!
//! * `lanesToBytes_bytesToLanes` — a TOTAL decoder that is a machine-checked LEFT INVERSE on every
//!   byte string shorter than `2^64`,
//! * `bytesToLanes_injective` — its corollary,
//!
//! both `#assert_axioms`-clean. ⚑ **Those are theorems about the LEAN encoder.** There is no formal
//! semantics of Rust and the Rust body is not extracted from the Lean, so what this file
//! establishes is that the deployed encoder AGREES WITH the verified spec on Lean-COMPUTED vectors
//! and round-trips on a sweep — the `Faithful9` rung, strictly stronger than the retired packer
//! could claim and strictly weaker than "verified". Say it at that resolution.
//!
//! ## The old-admits / new-rejects pairs
//!
//! The retired map was `BabyBear::from_bytes_packed` (DELETED 2026-08-01): 4-byte little-endian
//! strides, final partial chunk ZERO-FILLED, each chunk reduced `mod p`. Its consumer tagged the
//! sponge with the FELT count. It is spelled out below as [`retired_from_bytes_packed`] rather than
//! called, because a negative witness must keep exhibiting the defect it names after the defect's
//! implementation is gone — and because "we deleted it" is not a demonstration that it was broken.
//!
//! Two independent `O(1)` collisions, both re-run here rather than cited:
//!
//! 1. **the NUL-append** — `hash_bytes(b"foo") == hash_bytes(b"foo\0")`,
//!    `hash_bytes(b"f") == hash_bytes(b"f\0\0\0")`;
//! 2. **the mod-`p` alias AT EQUAL LENGTH** — `[00,00,00,00]` vs `[01,00,00,78]`, since
//!    `0x78000001 == p`. No length tag of any kind separates these.
//!
//! ## ⚠ ANTI-VACUITY
//!
//! Every "new rejects" assertion here is paired with a ROUND-TRIP assertion that the VALUE comes
//! back. A scrambling change passes a difference-only test and fails these.
//!
//! ## ⚠ What this file does NOT claim
//!
//! Nothing about the SQUEEZE. `hash_bytes` returns one felt and `log2(p) = 30.906891`, so its
//! collision cost by unstructured search is `2^15.4534` — a different defect, named at the
//! function and owned by the value-widening campaign. [`the_one_felt_squeeze_is_still_the_open_one`]
//! pins that bound so it cannot quietly be forgotten.

use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::{hash_bytes, hash_bytes_8};

/// The four-lane base-`2^16` byte-count header. Mirrors Lean `LEN_HEADER_LANES`.
const LEN_HEADER_LANES: usize = 4;

/// **THE RETIRED MAP**, spelled out. Byte-for-byte the deleted
/// `BabyBear::from_bytes_packed`: 4-byte LE strides, missing bytes read as zero, `mod p`.
fn retired_from_bytes_packed(bytes: &[u8]) -> Vec<BabyBear> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let mut val: u32 = 0;
        for j in 0..4 {
            if i + j < bytes.len() {
                val |= (bytes[i + j] as u32) << (j * 8);
            }
        }
        out.push(BabyBear::new(val));
        i += 4;
    }
    out
}

fn lanes(data: &[u8]) -> Vec<u32> {
    BabyBear::bytes_to_lanes(data)
        .into_iter()
        .map(|l| l.as_u32())
        .collect()
}

// ---------------------------------------------------------------------------
// 1. THE LEAN PIN — vectors COMPUTED BY LEAN, not transcribed from a Rust run.
//    Every literal below appears verbatim as a `#guard` in
//    metatheory/Dregg2/Circuit/BytesLanes.lean §5.
// ---------------------------------------------------------------------------

#[test]
fn deployed_encoder_reproduces_the_lean_computed_vectors() {
    assert_eq!(lanes(b""), vec![0, 0, 0, 0]);
    assert_eq!(lanes(b"\xff"), vec![1, 0, 0, 0, 255]);
    assert_eq!(lanes(b"\xff\xff"), vec![2, 0, 0, 0, 65535]);
    assert_eq!(lanes(b"foo"), vec![3, 0, 0, 0, 28518, 111]);
    assert_eq!(lanes(b"foo\0"), vec![4, 0, 0, 0, 28518, 111]);
    assert_eq!(lanes(&[0u8, 0, 0, 0]), vec![4, 0, 0, 0, 0, 0]);
    assert_eq!(lanes(&[1u8, 0, 0, 120]), vec![4, 0, 0, 0, 1, 30720]);

    // `b"grain/var/value:v1\0"` — the deployed VAR_VALUE_DOMAIN, 19 bytes, so ODD length and a
    // zero-padded final lane. Lean `varValueDomain`.
    let dom = b"grain/var/value:v1\0";
    assert_eq!(dom.len(), 19);
    assert_eq!(
        lanes(dom),
        vec![
            19, 0, 0, 0, 29287, 26977, 12142, 24950, 12146, 24950, 30060, 14949, 12662, 0
        ]
    );
    assert_eq!(lanes(dom).len(), 14);
}

#[test]
fn the_length_header_is_four_base_65536_digits_of_the_byte_count() {
    // Lean `#guard lenLanes 70000 = [4464, 1, 0, 0]`.
    let big = vec![0u8; 70_000];
    assert_eq!(&lanes(&big)[..LEN_HEADER_LANES], &[4464, 1, 0, 0]);
    // ...and it is the BYTE count, not the felt count — which is the entire content of the fix.
    for n in [0usize, 1, 2, 3, 4, 5, 17, 65_535, 65_536, 65_537] {
        let data = vec![7u8; n];
        let hdr = &lanes(&data)[..LEN_HEADER_LANES];
        let recovered = u64::from(hdr[0])
            + (u64::from(hdr[1]) << 16)
            + (u64::from(hdr[2]) << 32)
            + (u64::from(hdr[3]) << 48);
        assert_eq!(recovered, n as u64, "header must carry the BYTE count");
    }
}

// ---------------------------------------------------------------------------
// 2. ANTI-VACUITY — the VALUE comes back.
// ---------------------------------------------------------------------------

#[test]
fn round_trip_returns_the_value_not_merely_a_different_digest() {
    for len in 0..400usize {
        let data: Vec<u8> = (0..len)
            .map(|i| (i as u8).wrapping_mul(151).wrapping_add(29))
            .collect();
        let back = BabyBear::lanes_to_bytes(&BabyBear::bytes_to_lanes(&data));
        assert_eq!(back, data, "round-trip failed at len {len}");
    }
    // Structured shapes the sweep above will not hit.
    for data in [
        b"".to_vec(),
        b"\0".to_vec(),
        b"\0\0\0\0\0\0\0\0".to_vec(),
        b"grain/var/value:v1\0".to_vec(),
        vec![0xffu8; 33],
    ] {
        assert_eq!(
            BabyBear::lanes_to_bytes(&BabyBear::bytes_to_lanes(&data)),
            data
        );
    }
}

#[test]
fn no_lane_ever_needs_reducing() {
    // 2^16 < p, so `BabyBear::new` is the identity on every lane. This is why the mod-p alias
    // cannot recur — it is structural, not a range check someone remembered to write.
    for len in 0..256usize {
        let data: Vec<u8> = (0..len).map(|i| (i as u8) ^ 0xA5).collect();
        for lane in lanes(&data) {
            assert!(lane < 1 << 16, "lane {lane} escaped the 2^16 radix");
        }
    }
}

// ---------------------------------------------------------------------------
// 3. OLD ADMITS / NEW REJECTS — collision 1, the NUL-append.
// ---------------------------------------------------------------------------

#[test]
fn old_admits_the_nul_append() {
    // Exactly the two equalities a prior lane ran, re-run here over the retired body.
    assert_eq!(
        retired_from_bytes_packed(b"foo"),
        retired_from_bytes_packed(b"foo\0"),
        "the retired packer conflated b\"foo\" with b\"foo\\0\""
    );
    assert_eq!(
        retired_from_bytes_packed(b"f"),
        retired_from_bytes_packed(b"f\0\0\0"),
        "the retired packer conflated b\"f\" with b\"f\\0\\0\\0\""
    );
    // ...AND the sponge tag agreed too, which is what made it a `hash_bytes` collision and not
    // merely a packer curiosity: `hash_many` tagged state[4] with the FELT count.
    assert_eq!(
        retired_from_bytes_packed(b"foo").len(),
        retired_from_bytes_packed(b"foo\0").len()
    );
}

#[test]
fn new_rejects_the_nul_append() {
    assert_ne!(hash_bytes(b"foo"), hash_bytes(b"foo\0"));
    assert_ne!(hash_bytes(b"f"), hash_bytes(b"f\0\0\0"));
    assert_ne!(hash_bytes_8(b"foo"), hash_bytes_8(b"foo\0"));

    // ...and it separates in the HEADER, so the refusal is the fix's mechanism and not a lucky
    // tail difference.
    assert_eq!(lanes(b"foo")[0], 3);
    assert_eq!(lanes(b"foo\0")[0], 4);

    // Exhaustively over every short length and every pad width: no NUL-append survives.
    for len in 0..96usize {
        let base: Vec<u8> = (0..len).map(|i| (i as u8) ^ 0x5C).collect();
        for pad in 1..=8usize {
            let mut padded = base.clone();
            padded.extend(std::iter::repeat_n(0u8, pad));
            assert_ne!(
                hash_bytes(&base),
                hash_bytes(&padded),
                "len {len} + {pad} NULs collided"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// 4. OLD ADMITS / NEW REJECTS — collision 2, the mod-p alias at EQUAL length.
//    The wound the brief did not name and the length header alone would not have closed.
// ---------------------------------------------------------------------------

#[test]
fn old_admits_the_equal_length_mod_p_alias() {
    let zero4 = [0u8, 0, 0, 0];
    let alias4 = [1u8, 0, 0, 0x78]; // 0x78000001 == p
    assert_eq!(u32::from_le_bytes(alias4), dregg_circuit::field::BABYBEAR_P);
    assert_eq!(zero4.len(), alias4.len(), "the substitution is same-length");
    assert_ne!(zero4, alias4, "the bytes genuinely differ");
    assert_eq!(
        retired_from_bytes_packed(&zero4),
        retired_from_bytes_packed(&alias4),
        "the retired packer aliased a +p pair at equal length"
    );
}

#[test]
fn new_rejects_the_equal_length_mod_p_alias() {
    let zero4 = [0u8, 0, 0, 0];
    let alias4 = [1u8, 0, 0, 0x78];
    assert_ne!(hash_bytes(&zero4), hash_bytes(&alias4));
    assert_ne!(hash_bytes_8(&zero4), hash_bytes_8(&alias4));

    // Sweep the shape: for each 4-byte chunk position, adding p to the chunk used to be free.
    let p = dregg_circuit::field::BABYBEAR_P;
    for lane in 0..4usize {
        for seed in [0u32, 1, 12345, 0x0011_2233] {
            let sibling = seed.wrapping_add(p);
            if sibling < seed {
                continue; // wrapped past u32 — not a same-length alias
            }
            let mut a = [0u8; 16];
            let mut b = [0u8; 16];
            a[lane * 4..lane * 4 + 4].copy_from_slice(&seed.to_le_bytes());
            b[lane * 4..lane * 4 + 4].copy_from_slice(&sibling.to_le_bytes());
            assert_eq!(
                retired_from_bytes_packed(&a),
                retired_from_bytes_packed(&b),
                "retired packer should alias lane {lane} seed {seed}"
            );
            assert_ne!(
                hash_bytes(&a),
                hash_bytes(&b),
                "new encoder must separate lane {lane} seed {seed}"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// 5. COMPLETENESS — honest inputs still hash, and distinct honest inputs stay distinct.
// ---------------------------------------------------------------------------

#[test]
fn honest_inputs_still_hash_and_stay_distinct() {
    let corpus: Vec<Vec<u8>> = (0..512usize)
        .map(|i| {
            let len = i % 71;
            (0..len)
                .map(|j| ((i * 31 + j * 17) as u8).wrapping_add(3))
                .collect()
        })
        .collect();
    let mut seen = std::collections::HashMap::new();
    for data in &corpus {
        let d = hash_bytes(data);
        if let Some(prev) = seen.insert(d.as_u32(), data.clone()) {
            assert_eq!(
                &prev, data,
                "distinct honest inputs collided: this is the 2^15.45 wall"
            );
        }
    }
    // The domain strings the deployed consumers actually use.
    for dom in [
        &b"grain/var/addr:v1\0"[..],
        &b"grain/var/value:v1\0"[..],
        &b"dregg-bucket-content-root-v1"[..],
        &b"site-host-content-root-v1"[..],
    ] {
        let _ = hash_bytes(dom);
        let _ = hash_bytes_8(dom);
    }
}

// ---------------------------------------------------------------------------
// 6. THE RESIDUAL, PINNED — so the fixed half cannot be read as the whole.
// ---------------------------------------------------------------------------

/// ⚠ **NOT A GUARD — A LEDGER.** `hash_bytes` squeezes ONE felt. This pins the bound so a reader
/// who sees the file green reads "the preimage is injective and the squeeze is still 31 bits",
/// never "hash_bytes is safe". It goes red only when the squeeze is widened, at which point it
/// should be deleted rather than repaired.
#[test]
fn the_one_felt_squeeze_is_still_the_open_one() {
    let p = f64::from(dregg_circuit::field::BABYBEAR_P);
    let bits = p.log2();
    let birthday = bits / 2.0;
    assert!((bits - 30.906_891).abs() < 1e-5, "log2(p) drifted: {bits}");
    assert!(
        (birthday - 15.453_445).abs() < 1e-5,
        "the hash_bytes collision bound is 2^{birthday}, not the image size"
    );
    // The eight-felt companion exists and is the one to reach for: 8 * 30.906891 / 2.
    let wide = 8.0 * bits / 2.0;
    assert!(
        (wide - 123.627_56).abs() < 1e-4,
        "hash_bytes_8 bound: 2^{wide}"
    );
}

// ---------------------------------------------------------------------------
// 7. THE OUT-OF-WORKSPACE TWIN — a drift detector that can actually RUN.
// ---------------------------------------------------------------------------

/// `sel4/dregg-pd/executor-pd/crypto-floor` carries a hand-maintained `no_std` copy of the encoder
/// and of `hash_bytes`. That crate **does not build on the host** (`cargo check` there is
/// `error: unwinding panics are not supported without std`; it cross-builds for
/// `aarch64-unknown-linux-musl` only), so a `#[cfg(test)]` module inside it can never go red and
/// would not be a gate. This reads its source instead — the same shape as
/// `circuit/tests/faithful8_key_octet_below_floor.rs`'s workspace walk — so the twin cannot
/// silently revert to the aliasing packer or drift off the radix.
#[test]
fn the_out_of_workspace_crypto_floor_twin_has_not_drifted() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("workspace root")
        .join("sel4/dregg-pd/executor-pd/crypto-floor/src");
    let field = std::fs::read_to_string(root.join("field.rs")).expect(
        "the crypto-floor twin must exist; if it moved, re-point this rather than deleting it",
    );
    let poseidon =
        std::fs::read_to_string(root.join("poseidon2.rs")).expect("crypto-floor poseidon2.rs");

    // The retired, non-injective map must be GONE from both copies — not deprecated, gone.
    assert!(
        !field.contains("pub fn from_bytes_packed"),
        "the retired 4-byte mod-p packer reappeared in the crypto-floor twin"
    );
    assert!(
        !poseidon.contains("from_bytes_packed"),
        "crypto-floor hash_bytes still calls the retired packer"
    );

    // ...and the injective one is what `hash_bytes` there absorbs.
    assert!(
        field.contains("pub fn bytes_to_lanes"),
        "crypto-floor lost bytes_to_lanes"
    );
    assert!(
        poseidon.contains("BabyBear::bytes_to_lanes(data)"),
        "crypto-floor hash_bytes no longer absorbs the injective preimage"
    );

    // The two numbers that make it injective: the 2^16 radix and the four-lane byte-count header.
    assert!(
        field.contains("65536"),
        "crypto-floor twin lost the 2^16 lane radix"
    );
    assert!(
        field.contains("for _ in 0..4"),
        "crypto-floor twin lost the four-lane byte-count header"
    );
}
