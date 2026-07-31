//! **The nine-lane fields-octet encoder is an INJECTION, and this is where that is measured.**
//!
//! ═══ THE AUTHORITY ═══════════════════════════════════════════════════════════════
//! `metatheory/Dregg2/Circuit/FieldLanes9.lean` is the spec. It carries, `#assert_axioms`-clean:
//!
//!   * `lanes9ToField_fieldToLanes9` — the total decoder is a LEFT INVERSE on every 32-byte value;
//!   * `fieldToLanes9_injective` — `Function.Injective fieldToLanes9`, its corollary;
//!   * `nine_lanes_is_the_minimum` — `P^8 < 2^256 ≤ P^9`.
//!
//! Those are theorems about the LEAN encoder. **This file does not inherit them.** There is no
//! formal semantics of Rust and `dregg_circuit::effect_vm::field_limbs9` is not extracted from the
//! Lean, so what this file provides is a PIN: the six Lean-COMPUTED `#guard` vectors asserted
//! byte-for-byte, plus a round-trip sweep wide enough that a Rust body which diverged from the spec
//! anywhere would have to do so on a measure-zero set. Case tests prove nothing about all inputs.
//! Read the pairing as "a Rust twin case-tested against a verified spec", never as "verified".
//!
//! ⚑ The KAT vectors below are TRANSCRIBED FROM LEAN `#guard` OUTPUT, not re-derived from a Rust
//! run. Re-deriving them here would make this file a tautology over its own subject.
//!
//! ═══ WHAT THE NINTH LANE REPAIRS ═════════════════════════════════════════════════
//! `p = 2013265921`, `log₂ p = 30.907`: eight lanes carry **247.26 bits** against a 32-byte field's
//! **256**, so no 8-lane encoding of 32 bytes is injective under ANY chunking. The previous octet's
//! repairs each moved the attacker's COST — the last priced out at a `2^92.7` collision, below the
//! ~124-bit bar quoted elsewhere in this tree, making the fields octet the weakest collision term in
//! the rotated commitment. Nine lanes is the minimum and this is that encoding.
//!
//! ═══ THE TWO POLES ═══════════════════════════════════════════════════════════════
//! Both are asserted below and each would be worthless alone:
//!
//!   * the **ALIAS pole** — `x` and `x + p` STILL share lane 0 (that is the pinned deployed ABI,
//!     not a residual wound), and the full nine-lane vectors nevertheless differ, in lane 8
//!     specifically. Asserting the lane-0 collision explicitly is the point: it documents WHY a
//!     ninth lane was the repair rather than a re-chunking.
//!   * the **VALVE pole** — `field_limbs9(field_from_u64(v))[0] == v` for every `v < 2^31`, so the
//!     escrow / discharge / vault weld constants, `setfield_encoder_window_gate` and every app
//!     encoder are visibly unchanged.
//!
//! And the anti-vacuity everywhere is ROUND-TRIP, not "the vectors differ": `field_from_lanes9` must
//! return the VALUE. An encoder that scrambled its input would separate every pair by accident and
//! pass a differ-test; it cannot pass an inverse-test.

use dregg_circuit::effect_vm::{field_from_lanes9, field_limbs8, field_limbs9};
use dregg_circuit::field::BabyBear;

/// BabyBear's modulus — the reduction lanes 0 and 1 perform, and the alias generator.
const P: u32 = 2013265921;

/// `field_from_u64` twin (`cell/src/program/eval.rs`): the kernel numeric field encoding writes `v`
/// BIG-ENDIAN into bytes `24..32` and zeroes the rest. Reproduced here so the derivation is pinned
/// inside the circuit crate without a dep cycle, exactly as `helpers.rs`'s own unit tests do.
fn field_from_u64(v: u64) -> [u8; 32] {
    let mut f = [0u8; 32];
    f[24..32].copy_from_slice(&v.to_be_bytes());
    f
}

fn lanes_as_u32(b: &[u8; 32]) -> [u32; 9] {
    field_limbs9(b).map(|l| l.as_u32())
}

/// Bytes `b[i] = i`, the Lean `ascendingBytes`.
fn ascending_bytes() -> [u8; 32] {
    let mut b = [0u8; 32];
    for (i, byte) in b.iter_mut().enumerate() {
        *byte = i as u8;
    }
    b
}

// ═════════════════════════════════════════════════════════════════════════════════
// 1. THE LEAN-COMPUTED PROTOCOL VECTORS
// ═════════════════════════════════════════════════════════════════════════════════

/// The six `#guard` vectors from `FieldLanes9.lean`, asserted exactly.
///
/// Transcribed from the Lean file's computed guards — NOT produced by running this crate's encoder
/// and pasting the answer. If the Rust body diverges from the spec anywhere these vectors reach,
/// this test is the thing that says so.
#[test]
fn the_lean_computed_protocol_vectors_reproduce_exactly() {
    // ⚑ THE VALVE OUTCOME, PRESERVED: a small numeric field still puts its raw value in lane 0 and
    // ZERO in every free lane — `field_from_u64` leaves bytes 0..24 empty and no quotient is taken.
    assert_eq!(
        lanes_as_u32(&field_from_u64(1)),
        [1, 0, 0, 0, 0, 0, 0, 0, 0],
        "field_from_u64(1)"
    );
    assert_eq!(
        lanes_as_u32(&field_from_u64(1_000_000)),
        [1_000_000, 0, 0, 0, 0, 0, 0, 0, 0],
        "field_from_u64(1000000)"
    );
    assert_eq!(
        lanes_as_u32(&[0u8; 32]),
        [0, 0, 0, 0, 0, 0, 0, 0, 0],
        "the zero field"
    );

    // `2^32 - 1`: lane 0 reduces (`% p`) and the NINTH lane carries the quotient that used to be
    // lost outright. `268435453 = (2^32 - 1) mod p`; lane 8 `= 2·2^24` is `q₀ = 2` in the top digit.
    assert_eq!(
        lanes_as_u32(&field_from_u64(4_294_967_295)),
        [268435453, 0, 0, 0, 0, 0, 0, 0, 33554432],
        "field_from_u64(u32::MAX)"
    );

    // Both quotients at once: every byte 0xff, so `q₀ = q₁ = 2` and the carry digit is 10.
    assert_eq!(
        lanes_as_u32(&[0xffu8; 32]),
        [
            268435453, 268435453, 268435455, 268435455, 268435455, 268435455, 268435455, 268435455,
            184549375
        ],
        "the all-0xff field"
    );

    // A value with structure in every byte.
    assert_eq!(
        lanes_as_u32(&ascending_bytes()),
        [
            471670303, 404298267, 50462976, 6312000, 168364039, 13680816, 17829646, 21049633,
            1512981
        ],
        "b[i] = i"
    );
}

/// Every lane the encoder emits is a genuine BabyBear element, and the SEVEN FREE LANES never
/// reduce — they are `< 2^28 < p` by construction (Lean `chunks7_lt_CH` + `fieldToLanes9_lt_P`).
///
/// This is the property that makes the free lanes NOT the `u32 % p` shape that aliased: a lane that
/// never reduces cannot identify two preimages.
#[test]
fn the_seven_free_lanes_never_reduce() {
    const CH: u32 = 1 << 28;
    for seed in 0..512u64 {
        let b = mix32(seed);
        let lanes = lanes_as_u32(&b);
        for (i, &lane) in lanes.iter().enumerate() {
            assert!(lane < P, "lane {i} must be a BabyBear element");
            if i >= 2 {
                assert!(
                    lane < CH,
                    "free lane {i} = {lane} must be < 2^28 — a reducing free lane is the alias shape"
                );
            }
        }
    }
}

// ═════════════════════════════════════════════════════════════════════════════════
// 2. ROUND-TRIP — the anti-vacuity that "the hashes differ" cannot provide
// ═════════════════════════════════════════════════════════════════════════════════

/// A tiny deterministic xorshift64* — no `rand` dep, and the sweep is reproducible byte-for-byte.
fn xorshift64(state: &mut u64) -> u64 {
    let mut x = *state;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    *state = x;
    x.wrapping_mul(0x2545_F491_4F6C_DD1D)
}

/// A pseudorandom 32-byte value from a seed. Deliberately fills ALL 32 bytes, including the u64
/// window, so both the pinned pair and the free lanes are exercised (and quotients arise).
fn mix32(seed: u64) -> [u8; 32] {
    let mut s = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1;
    let mut b = [0u8; 32];
    for chunk in b.chunks_mut(8) {
        chunk.copy_from_slice(&xorshift64(&mut s).to_le_bytes());
    }
    b
}

#[test]
fn the_kat_inputs_round_trip() {
    let cases: [[u8; 32]; 6] = [
        field_from_u64(1),
        field_from_u64(1_000_000),
        [0u8; 32],
        field_from_u64(4_294_967_295),
        [0xffu8; 32],
        ascending_bytes(),
    ];
    for b in cases {
        assert_eq!(
            field_from_lanes9(&field_limbs9(&b)),
            b,
            "the KAT input {b:02x?} must come back — the VALUE, not merely a distinct vector"
        );
    }
}

/// ⚑ **THE MAIN ANTI-VACUITY POLE.** 100_000 deterministic pseudorandom values, each required to
/// come back byte-for-byte through the decoder. Injectivity follows from a left inverse, so this is
/// the property the Lean actually proves — sampled here rather than assumed.
///
/// Not a "hashes differ" sweep: a scrambling encoder separates everything and would pass that; only
/// an inverse-carrying encoder passes this.
#[test]
fn a_hundred_thousand_pseudorandom_values_round_trip() {
    let mut distinct_vectors = std::collections::HashSet::new();
    let mut quotients_seen = [false; 3];
    let mut hi_quotients_seen = [false; 3];

    for seed in 0..100_000u64 {
        let b = mix32(seed);
        let lanes = field_limbs9(&b);
        assert_eq!(
            field_from_lanes9(&lanes),
            b,
            "seed {seed}: {b:02x?} must round-trip"
        );
        distinct_vectors.insert(lanes.map(|l| l.as_u32()));

        // Coverage bookkeeping: the sweep must actually REACH the reducing cases, or it is a sweep
        // over the easy half of the domain.
        let lo = u32::from_be_bytes([b[28], b[29], b[30], b[31]]);
        let hi = u32::from_be_bytes([b[24], b[25], b[26], b[27]]);
        quotients_seen[(lo / P) as usize] = true;
        hi_quotients_seen[(hi / P) as usize] = true;
    }

    // A left inverse over 100_000 inputs forces 100_000 distinct vectors; asserting it makes the
    // injectivity consequence explicit rather than implied.
    assert_eq!(
        distinct_vectors.len(),
        100_000,
        "100_000 distinct inputs must give 100_000 distinct nine-lane vectors"
    );
    // ⚑ NON-VACUITY OF THE SWEEP ITSELF. Without this a generator that only ever produced
    // sub-modulus windows would look like full coverage.
    assert!(
        quotients_seen.iter().all(|&s| s),
        "the sweep must exercise lo-window quotients 0, 1 AND 2 — {quotients_seen:?}"
    );
    assert!(
        hi_quotients_seen.iter().all(|&s| s),
        "the sweep must exercise hi-window quotients 0, 1 AND 2 — {hi_quotients_seen:?}"
    );
}

/// The adversarial edges of the pinned window: exactly the values where `lo / p` steps.
#[test]
fn the_modulus_boundary_values_round_trip() {
    let p = P as u64;
    let edges: [u64; 10] = [
        0,
        1,
        p - 1,
        p,
        p + 1,
        2 * p - 1,
        2 * p,
        2 * p + 1,
        u32::MAX as u64,
        u64::MAX,
    ];
    for v in edges {
        let b = field_from_u64(v);
        let lanes = field_limbs9(&b);
        assert_eq!(
            field_from_lanes9(&lanes),
            b,
            "field_from_u64({v}) must round-trip — this is where lane 0's quotient steps"
        );
        // And the same values with the low 24 bytes NON-empty, so the carry digit shares W with
        // real byte content rather than sitting alone in the top digit.
        let mut b2 = b;
        b2[..24].copy_from_slice(&ascending_bytes()[..24]);
        assert_eq!(
            field_from_lanes9(&field_limbs9(&b2)),
            b2,
            "field_from_u64({v}) with a populated low half must round-trip"
        );
    }
    // The edge list straddles the whole reachable range: `2p = 4026531842 < 2^32`, which is exactly
    // why every residue has ≥2 u32 preimages and quotient 2 is REACHABLE — the property that made
    // the old octet O(1)-forgeable and that the carry digit now records.
    assert!(
        2 * p < u32::MAX as u64,
        "2p must fit a u32 — that is the alias generator"
    );
    assert_eq!(
        (u32::MAX as u64) / p,
        2,
        "the largest reachable lo-window quotient must be 2"
    );
}

// ═════════════════════════════════════════════════════════════════════════════════
// 3. THE ALIAS POLE — lane 0 still collides; the VECTOR does not
// ═════════════════════════════════════════════════════════════════════════════════

/// ⚑ **WHY THE NINTH LANE IS THE REPAIR, stated as two assertions that must BOTH hold.**
///
/// Lane 0 is `BE(b[28..32]) % p` and always was: `x` and `x + p` share it, and they must keep
/// sharing it — that lane is welded to the v1 face column and read by `field_to_u64`, so "fix the
/// alias by re-chunking lane 0" was never available. The repair is that the QUOTIENT lane 0 discards
/// is now carried, in the carry digit, and therefore in lane 8.
///
/// So the first assertion here is a COLLISION, asserted deliberately, and the second is its
/// containment.
#[test]
fn lane0_still_aliases_and_the_ninth_lane_is_what_separates() {
    let honest = field_from_u64(1);
    let sibling = field_from_u64(1 + P as u64);
    assert_ne!(
        honest, sibling,
        "the pair must be two DISTINCT 32-byte values"
    );

    let a = field_limbs9(&honest);
    let s = field_limbs9(&sibling);

    // (1) THE PINNED ABI, ASSERTED AS A COLLISION. If this ever fails, lane 0 moved, and the escrow
    // /discharge/vault welds and every app encoder moved with it — a far larger flag day than this
    // test.
    assert_eq!(
        a[0], s[0],
        "lane 0 MUST still alias `x` / `x + p` — it is `BE(b[28..32]) % p`, the deployed ABI"
    );
    assert_eq!(a[1], s[1], "lane 1 is empty for both and must agree too");

    // (2) THE CONTAINMENT: the full vector nevertheless separates, and specifically in lane 8.
    assert_ne!(
        a, s,
        "the NINE-lane vectors must differ — this is the wound the ninth lane closes"
    );
    assert_eq!(
        s[8],
        BabyBear::new(16777216),
        "the `+p` sibling's lane 8 is `q₀ = 1` in the top base-256 digit = 2^24"
    );
    assert_eq!(a[8], BabyBear::ZERO, "the honest value takes no quotient");

    // (3) ANTI-VACUITY: both members come back. A vector pair that differed because the encoder
    // scrambled would fail here.
    assert_eq!(field_from_lanes9(&a), honest);
    assert_eq!(field_from_lanes9(&s), sibling);

    // (4) And the alias family is not one lucky pair: every `c` / `c + p` in the u64 window
    // separates, and always in lane 8 alone.
    for c in [0u64, 2, 7, 1000, 0x0800_0000, (P - 1) as u64] {
        let x = field_limbs9(&field_from_u64(c));
        let y = field_limbs9(&field_from_u64(c + P as u64));
        assert_eq!(x[0], y[0], "c = {c}: lane 0 aliases by construction");
        assert_ne!(x[8], y[8], "c = {c}: lane 8 must carry the quotient");
        assert_ne!(x, y, "c = {c}: the vectors must separate");
    }
}

/// The other half of the old wound: a `c` / `c + p` pair planted in the LOW 24 bytes, which the
/// pinned lanes carry nothing at all about. Under the pre-ninth-lane `u32 % p` chunking these rode
/// one lane each and collided in `O(1)`; the free lanes carry those bytes verbatim now, so the pair
/// separates AND both members decode.
#[test]
fn constructed_low_half_aliases_separate_and_decode() {
    for chunk in 0..6usize {
        let (mut lo, mut hi) = ([0u8; 32], [0u8; 32]);
        lo[chunk * 4..chunk * 4 + 4].copy_from_slice(&0x0800_0000u32.to_le_bytes());
        hi[chunk * 4..chunk * 4 + 4].copy_from_slice(&(0x0800_0000u32 + P).to_le_bytes());
        assert_ne!(lo, hi, "chunk {chunk}: the pair must differ in bytes");
        assert_ne!(
            field_limbs9(&lo),
            field_limbs9(&hi),
            "chunk {chunk}: the constructed mod-p alias must SEPARATE"
        );
        assert_eq!(field_from_lanes9(&field_limbs9(&lo)), lo);
        assert_eq!(field_from_lanes9(&field_limbs9(&hi)), hi);
    }
}

/// Every byte of the 32 is READ and moves at least one lane — nothing is unbound. Injectivity
/// implies it; asserting it names the failure that a truncating encoder would produce.
#[test]
fn every_byte_moves_a_lane() {
    let base = ascending_bytes();
    let lanes0 = field_limbs9(&base);
    for i in 0..32usize {
        let mut b = base;
        b[i] ^= 0x5A;
        assert_ne!(
            field_limbs9(&b),
            lanes0,
            "byte {i} must move the vector — it is otherwise unbound"
        );
    }
}

// ═════════════════════════════════════════════════════════════════════════════════
// 4. THE VALVE POLE — the deployed weld constants are visibly unchanged
// ═════════════════════════════════════════════════════════════════════════════════

/// `field_limbs9(field_from_u64(v))[0].as_u32() == v` — RAW equality, for every sampled `v < p`.
///
/// This is the constraint the whole nine-lane design was built around: the escrow
/// (`Deposited = 1` / `Consumed = 2`) equalities, the discharge cursor/total additive advances with
/// their `DUE_BITS = 28` range check, the vault 15-bit operand decompositions,
/// `setfield_encoder_window_gate` and every app encoder (`deos-js-core::pack_u64`,
/// `starbridge-web-surface::pack_coord`) all read lane 0 and require the RAW numeric value.
///
/// ⚑ **THE STATED LIMIT IS `v < p`, NOT `v < 2^31`, AND THE DIFFERENCE IS 134 MILLION VALUES.**
/// `helpers.rs` carried "`field_limbs8(field_from_u64(v))[0] == v` for `v < 2^31`" for the whole
/// life of the v13 octet. `p = 2013265921 < 2^31 = 2147483648`, so the claim is FALSE across
/// `[p, 2^31)`: lane 0 there is `v − p`, not `v`. The reason nothing caught it is that the existing
/// pin asserts `lanes[0] == BabyBear::new(v as u32)` and `BabyBear::new` REDUCES — both sides go
/// through the same modulus, so the assertion holds for every `v < 2^32` and can never fail. It is
/// a tautology wearing a limit.
///
/// This test asserts the raw `u32` instead, so the limit is the thing measured, and the
/// `[p, 2^31)` regime gets its own pole below rather than being swept under `BabyBear::new`.
#[test]
fn lane0_is_the_raw_value_for_every_honest_numeric_field() {
    let mut sampled = 0usize;
    let mut check = |v: u64| {
        assert!(v < P as u64, "the raw-value domain is v < p");
        let lanes = field_limbs9(&field_from_u64(v));
        assert_eq!(
            lanes[0].as_u32(),
            v as u32,
            "lane 0 is the RAW value v = {v} — not merely congruent to it"
        );
        assert_eq!(lanes[1], BabyBear::ZERO, "hi32 is empty for v = {v} < 2^32");
        for k in 2..9 {
            assert_eq!(
                lanes[k],
                BabyBear::ZERO,
                "free lane {k} is zero for a kernel-numeric v = {v} — the low 24 bytes are empty \
                 and no quotient is taken"
            );
        }
        sampled += 1;
    };

    for v in [0u64, 1, 2, 3, 1000, 1_000_000, (1 << 30) - 1, P as u64 - 1] {
        check(v);
    }
    // A deterministic spread across the whole raw-value domain, not just the small end.
    let mut s = 0xD1CE_D1CE_D1CE_D1CEu64;
    for _ in 0..2048 {
        check(xorshift64(&mut s) % P as u64);
    }
    assert!(sampled >= 2048, "the valve sweep must actually run");

    // The escrow weld constants, spelled out, plus the non-vacuity that Empty (0) is distinguished.
    assert_eq!(field_limbs9(&field_from_u64(1))[0], BabyBear::new(1));
    assert_eq!(field_limbs9(&field_from_u64(2))[0], BabyBear::new(2));
    assert_ne!(
        field_limbs9(&field_from_u64(0))[0],
        field_limbs9(&field_from_u64(1))[0]
    );

    // Lane additivity on the welded limb — the discharge cursor/total gates and the vault deltas.
    for (before, delta) in [(1000u64, 100u64), (0, 1), (12345, 54321)] {
        let b = field_limbs9(&field_from_u64(before))[0];
        let a = field_limbs9(&field_from_u64(before + delta))[0];
        assert_eq!(a, b + BabyBear::new(delta as u32));
    }

    // And the hi window rides lane 1, unchanged.
    let v = (7u64 << 32) | 42;
    let lanes = field_limbs9(&field_from_u64(v));
    assert_eq!(lanes[0], BabyBear::new(42));
    assert_eq!(lanes[1], BabyBear::new(7));
}

/// ⚑ **THE POLE THE `v < 2^31` CLAIM HID.** For `v ∈ [p, 2^32)` lane 0 is NOT `v` — it is `v mod p`,
/// and the quotient it drops rides the ninth lane's top base-256 digit (`q₀ · 2^24`).
///
/// `[p, 2^31) = [2013265921, 2147483648)` is 134,217,727 values inside the range the deployed
/// docstring called raw. Any weld that assumed rawness up to `2^31` is reading a residue there. The
/// deployed welds are all far narrower (`DUE_BITS = 28`, 15-bit vault operands), so this is a
/// documentation defect and not a live one — but it is measured here rather than asserted in prose,
/// because the pin that was supposed to catch it could not (`BabyBear::new` reduces both sides).
#[test]
fn above_the_modulus_lane0_is_a_residue_and_the_ninth_lane_holds_the_quotient() {
    let p = P as u64;
    for (v, q) in [
        (p, 1u32),
        (p + 1, 1),
        (2 * p - 1, 1),
        (2 * p, 2),
        (2 * p + 1, 2),
        ((1u64 << 31) - 1, 1),
        (u32::MAX as u64, 2),
    ] {
        let lanes = field_limbs9(&field_from_u64(v));
        assert_eq!(
            lanes[0].as_u32(),
            (v % p) as u32,
            "v = {v}: lane 0 is the RESIDUE, not the raw value"
        );
        assert_ne!(
            lanes[0].as_u32(),
            v as u32,
            "v = {v}: the raw value is NOT recoverable from lane 0 — this is the claim that was \
             stated as `v < 2^31` and is really `v < p`"
        );
        assert_eq!(
            lanes[8].as_u32(),
            q * (1 << 24),
            "v = {v}: lane 8 must carry q₀ = {q} in the top base-256 digit"
        );
        // And the whole point: the value is still recoverable — from the VECTOR, not from lane 0.
        assert_eq!(field_from_lanes9(&lanes), field_from_u64(v));
    }
}

/// ⚑ **THE TWO ENCODERS MAY NOT DRIFT.** `field_limbs8` survives — the two rotated-pre-limb
/// producers write eight scattered limbs per field and the ninth column does not exist yet — so
/// while both are live, lanes 0 and 1 must agree BY MEASUREMENT and not merely by having been
/// written to agree. Every migrated `field_limbs9(&x)[0]` call site depends on exactly this.
#[test]
fn lanes_0_and_1_are_byte_identical_to_field_limbs8() {
    let mut cases: Vec<[u8; 32]> = vec![
        [0u8; 32],
        [0xffu8; 32],
        ascending_bytes(),
        field_from_u64(1),
        field_from_u64(1 + P as u64),
        field_from_u64(u64::MAX),
    ];
    for seed in 0..4096u64 {
        cases.push(mix32(seed ^ 0xBEEF));
    }
    for b in cases {
        let n = field_limbs9(&b);
        let o = field_limbs8(&b);
        assert_eq!(n[0], o[0], "lane 0 must not drift for {b:02x?}");
        assert_eq!(n[1], o[1], "lane 1 must not drift for {b:02x?}");
    }
}

// ═════════════════════════════════════════════════════════════════════════════════
// 5. THE DECODER IS TOTAL
// ═════════════════════════════════════════════════════════════════════════════════

/// A forged lane vector — free lanes at `p - 1`, far above the `2^28` an honest encoding emits —
/// must still decode without panic or wrap. The Lean decoder is total on every `Lanes9`, so a Rust
/// twin that panicked on off-image input would be a divergence, and an adversarial test that fed
/// one would report the panic as a finding.
#[test]
fn the_decoder_is_total_on_off_image_vectors() {
    let forged = [BabyBear::new(P - 1); 9];
    let out = field_from_lanes9(&forged);
    // No assertion about WHAT it returns — only that it returns. Re-encoding it lands back in the
    // image, which is the honest statement of what a total decoder buys.
    let back = field_limbs9(&out);
    assert_eq!(
        field_from_lanes9(&back),
        out,
        "the decoder's output must itself round-trip — its image is in the encoder's domain"
    );
    assert_ne!(
        back, forged,
        "a forged off-image vector is NOT a fixed point — re-encoding canonicalises it"
    );

    for pattern in [BabyBear::ZERO, BabyBear::new(1), BabyBear::new(P - 1)] {
        let v = [pattern; 9];
        let d = field_from_lanes9(&v);
        assert_eq!(field_from_lanes9(&field_limbs9(&d)), d);
    }
}

/// `Faithful9` is the typed sink, and its only constructor is the encoder.
#[test]
fn faithful9_wraps_the_encoder_and_reads_back() {
    use dregg_circuit::Faithful9;
    for seed in 0..256u64 {
        let b = mix32(seed ^ 0xF9);
        let f = Faithful9::from_field_lanes9(&b);
        assert_eq!(f.lanes(), field_limbs9(&b));
        assert_eq!(f.to_field_bytes(), b);
    }
}
