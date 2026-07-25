//! # THE FELT-WIDTH #25/#30 FALSIFIERS — the burn target's carrier AND the fold it rides.
//!
//! Two independent narrowings met at `PI[EFFECTS_HASH_BASE..+4]`, and fixing either
//! one alone would have been cosmetic:
//!
//! * **#25 — the COMPONENT.** `VmEffect::Burn.target_hash` was ONE felt
//!   (`fold_bytes32_to_bb`), the last 1-felt `target_hash` in an enum where
//!   `CellDestroy` / `CellSeal` / `CellUnseal` / `ReceiptArchive` / `Refusal` all
//!   carry `[BabyBear; 8]`. Two distinct target cells whose folds agreed produced a
//!   BYTE-IDENTICAL effects-hash preimage.
//!
//! * **#30 — the FOLD.** `compute_effects_hash_4` was
//!   `[h, hash_4_to_1([h,1,0,0]), hash_4_to_1([h,2,0,0]), hash_4_to_1([h,3,0,0])]`
//!   with `h` a SINGLE `hash_many` squeeze. All four published lanes were functions
//!   of that one ~31-bit felt, so the 4-tuple's image had at most `p ≈ 2^31` points
//!   — while the doc-comment claimed "~124-bit collision resistance". Widening any
//!   component into that fold bought nothing at the boundary: the
//!   `finalSqueezeOnly_still_conflates` shape (`Cell/InterfaceIdWidth.lean`).
//!
//! The perturbation used throughout is the campaign's standing one: **two 32-byte
//! targets that COLLIDE under the deployed narrow projection but differ outside it
//! must produce the SAME binding before the repair and DIFFERENT bindings after.**
//!
//! A sharpening this file pins as a first-class fact: `fold_bytes32_to_bb` is
//! `𝔽_p`-LINEAR in the limb vector (`Σ limbs[i]·MIX^i`), so a colliding pair is
//! CONSTRUCTED by one linear solve — no 2^31 grind, no 2^15.5 birthday search. The
//! ~2^31 figure only applies where the 32 bytes are constrained to be a hash image
//! (a `CellId::derive_raw` target); wherever a prover picks the 32 bytes directly,
//! collisions against this fold are FREE. Every assertion below runs in microseconds
//! for exactly that reason.
//!
//! Scope note: none of this is a live-soundness close. At HEAD the deployed
//! `burnVmDescriptor2R24` references the burn-target param column (68) ZERO times and
//! binds no PI in `EFFECTS_HASH_BASE..+4`, so both widths are PRE-PRICED liabilities
//! against the anchoring work, not gates that bite today. See
//! `docs/WOUND-felt-width-boundaries-2026-07-19.md` #25/#30/#31.

use dregg_circuit::effect_vm::{
    Effect as VmEffect, bytes32_to_8_limbs, compute_effects_hash, compute_effects_hash_4,
    fold_bytes32_to_bb,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::poseidon2::{hash_4_to_1, hash_many_8};

/// BabyBear modular inverse via Fermat (`p` is prime).
fn inv_p(a: u64) -> u64 {
    let p = BABYBEAR_P as u64;
    let mut result: u64 = 1;
    let mut base = a % p;
    let mut e = p - 2;
    while e > 0 {
        if e & 1 == 1 {
            result = result * base % p;
        }
        base = base * base % p;
        e >>= 1;
    }
    result
}

/// **The O(1) collision constructor.** `fold_bytes32_to_bb` is the linear form
/// `Σ_{i<8} limbs[i]·MIX^i`, so bumping limb 0 by `δ` and limb 1 by `−δ·MIX⁻¹`
/// lands on the SAME felt. Returns a 32-byte sibling of `base` that is a genuine
/// distinct value with an identical narrow fold.
fn fold_colliding_sibling(base: &[u8; 32], delta: u32) -> [u8; 32] {
    const MIX_RAW: u32 = 0x4FD3_9C8B;
    let p = BABYBEAR_P as u64;
    let mix = (MIX_RAW % BABYBEAR_P) as u64;
    let mut limbs = [0u64; 8];
    for (i, limb) in limbs.iter_mut().enumerate() {
        let off = i * 4;
        *limb =
            u32::from_le_bytes([base[off], base[off + 1], base[off + 2], base[off + 3]]) as u64 % p;
    }
    let d = delta as u64 % p;
    limbs[0] = (limbs[0] + d) % p;
    // limb1 -= d * mix^{-1}
    limbs[1] = (limbs[1] + p - d * inv_p(mix) % p) % p;
    let mut out = [0u8; 32];
    for (i, limb) in limbs.iter().enumerate() {
        out[i * 4..i * 4 + 4].copy_from_slice(&(*limb as u32).to_le_bytes());
    }
    out
}

/// Two distinct 32-byte targets, IDENTICAL under the narrow fold — built by one
/// linear solve, not by search. This is the pair every test below perturbs with.
fn colliding_target_pair() -> ([u8; 32], [u8; 32]) {
    let a: [u8; 32] = core::array::from_fn(|i| (i as u8).wrapping_mul(7).wrapping_add(3));
    let b = fold_colliding_sibling(&a, 0x0002_BEEF);
    (a, b)
}

#[test]
fn fold_bytes32_to_bb_collides_in_o1_because_it_is_linear() {
    let (a, b) = colliding_target_pair();
    assert_ne!(
        a, b,
        "the constructed sibling must be a DISTINCT 32-byte value"
    );
    assert_eq!(
        fold_bytes32_to_bb(&a),
        fold_bytes32_to_bb(&b),
        "fold_bytes32_to_bb is Σ limbs[i]·MIX^i — a linear form. A colliding pair is \
         SOLVED, not searched. If this ever fails the fold stopped being linear and the \
         catalogue's ~2^31 pricing needs re-deriving upward."
    );
    // The wide projection separates them — and does so on the two limbs the solve moved.
    let la = bytes32_to_8_limbs(&a);
    let lb = bytes32_to_8_limbs(&b);
    assert_ne!(
        la, lb,
        "the 8-limb projection must separate the colliding pair"
    );
    assert_ne!(la[0], lb[0]);
    assert_ne!(la[1], lb[1]);
    assert_eq!(
        &la[2..],
        &lb[2..],
        "only limbs 0/1 were perturbed — the rest agree, so the ONLY thing separating \
         these two effect lists after the widening is limb width"
    );
}

/// **#25 FALSIFIER — the component.** Two burn targets that the narrow fold conflates
/// bind DIFFERENTLY now. The `_narrow` half re-runs the exact pre-repair projection to
/// exhibit what the same pair used to do: one felt, one preimage, one hash.
#[test]
fn burn_target_collision_separates_after_the_8_limb_widening() {
    let (a, b) = colliding_target_pair();

    // BEFORE (re-enacted): the pre-repair bridge wrote `hash_to_bb(target)` into a
    // single `target_hash` felt, so both targets produced the SAME effect value…
    let narrow_a = fold_bytes32_to_bb(&a);
    let narrow_b = fold_bytes32_to_bb(&b);
    assert_eq!(
        narrow_a, narrow_b,
        "pre-repair, the two targets were the SAME felt — the effect lists were \
         indistinguishable at every downstream carrier"
    );

    // AFTER: the deployed bridge writes `hash_to_8(target)`, and `compute_effects_hash`
    // absorbs all 8 limbs.
    let burn = |t: &[u8; 32]| VmEffect::Burn {
        target_hash: bytes32_to_8_limbs(t),
        amount_lo: BabyBear::new(500),
        amount_full: 500,
    };
    let ha = compute_effects_hash_4(&[burn(&a)]);
    let hb = compute_effects_hash_4(&[burn(&b)]);
    assert_ne!(
        ha, hb,
        "a burn of cell A and a burn of cell B must publish DIFFERENT \
         PI[EFFECTS_HASH_BASE..+4] — this is the whole content of felt-width #25"
    );
    // …and the legacy 1-felt carrier separates them too (the widening is in the
    // PREIMAGE, so it lifts every squeeze taken over it).
    assert_ne!(
        compute_effects_hash(&[burn(&a)]).0,
        compute_effects_hash(&[burn(&b)]).0
    );
}

/// **THE "BEFORE" RUN, EXECUTED — not asserted from memory.** Reconstructs the exact
/// pre-repair pipeline (narrow Burn arm: `push(fold(target))`; derived-lane 4-felt:
/// `[h, hash_4_to_1([h,k,0,0])]`) against the REAL primitives and shows the
/// fold-colliding target pair produced a BYTE-IDENTICAL published PI vector. Paired
/// with `burn_target_collision_separates_after_the_8_limb_widening` this is the
/// same-before / different-after falsification in one file.
#[test]
fn burn_target_collision_was_byte_identical_before_the_repair() {
    let (a, b) = colliding_target_pair();

    // Pre-repair `effects_hash_inputs` for `[Burn { target, 500, 500 }]`: the Burn arm
    // pushed the domain tag, ONE folded target felt, amount_lo, then the 4×16-bit limbs.
    let old_preimage = |t: &[u8; 32]| {
        let mut v = vec![BabyBear::new(46), fold_bytes32_to_bb(t), BabyBear::new(500)];
        for i in 0..4 {
            v.push(BabyBear::new(((500u64 >> (i * 16)) & 0xFFFF) as u32));
        }
        v
    };
    assert_eq!(
        old_preimage(&a),
        old_preimage(&b),
        "pre-repair the two DISTINCT burn targets built the SAME effects-hash preimage"
    );

    // Pre-repair `compute_effects_hash_4`: lane 0 = the single squeeze, lanes 1..3
    // DERIVED from it. Both halves of the old pipeline agree on the pair.
    let old_four = |t: &[u8; 32]| {
        let h = dregg_circuit::poseidon2::hash_many(&old_preimage(t));
        [
            h,
            hash_4_to_1(&[h, BabyBear::ONE, BabyBear::ZERO, BabyBear::ZERO]),
            hash_4_to_1(&[h, BabyBear::new(2), BabyBear::ZERO, BabyBear::ZERO]),
            hash_4_to_1(&[h, BabyBear::new(3), BabyBear::ZERO, BabyBear::ZERO]),
        ]
    };
    assert_eq!(
        old_four(&a),
        old_four(&b),
        "pre-repair PI[EFFECTS_HASH_BASE..+4] was IDENTICAL for a burn of cell A and a \
         burn of cell B — the published binding did not distinguish which cell's supply \
         was destroyed"
    );
}

/// The same perturbation with the amount held fixed and only the target moved — a
/// burn of the SAME value from a DIFFERENT cell must not be substitutable.
#[test]
fn burn_target_is_the_only_moved_field_and_it_still_separates() {
    let (a, b) = colliding_target_pair();
    let mk = |t: &[u8; 32]| {
        vec![
            VmEffect::NoOp,
            VmEffect::Burn {
                target_hash: bytes32_to_8_limbs(t),
                amount_lo: BabyBear::new(7),
                amount_full: 7,
            },
        ]
    };
    assert_ne!(
        compute_effects_hash_4(&mk(&a)),
        compute_effects_hash_4(&mk(&b))
    );
}

/// **#30 FALSIFIER — the fold.** The published 4-felt effects hash must no longer
/// FACTOR THROUGH a single felt. Before the repair the whole tuple was recoverable
/// from lane 0 by a pure function; that is the property this asserts is gone.
#[test]
fn effects_hash_4_no_longer_factors_through_one_felt() {
    let effects = vec![
        VmEffect::Transfer {
            amount: 42,
            direction: 1,
        },
        VmEffect::Burn {
            target_hash: bytes32_to_8_limbs(&[9u8; 32]),
            amount_lo: BabyBear::new(11),
            amount_full: 11,
        },
    ];
    let four = compute_effects_hash_4(&effects);

    // The RETIRED derivation, recomputed here from lane 0 alone. If any lane still
    // matched it, that lane would carry no information beyond lane 0's ~31 bits.
    let h = four[0];
    let old_lane = |k: u32| hash_4_to_1(&[h, BabyBear::new(k), BabyBear::ZERO, BabyBear::ZERO]);
    for k in 1..4u32 {
        assert_ne!(
            four[k as usize],
            old_lane(k),
            "lane {k} still equals hash_4_to_1([lane0, {k}, 0, 0]) — the 4-felt effects \
             hash factors through ONE ~31-bit felt again, and its image is back to ≤ p \
             points. The '~124-bit' claim would be false."
        );
    }

    // Positive shape: the four lanes ARE the first four squeezes of the sponge that
    // absorbed the real preimage — every lane depends on the entire effect list.
    let ha = compute_effects_hash_4(&effects);
    let mut mutated = effects.clone();
    mutated[0] = VmEffect::Transfer {
        amount: 43,
        direction: 1,
    };
    let hb = compute_effects_hash_4(&mutated);
    for k in 0..4 {
        assert_ne!(
            ha[k], hb[k],
            "lane {k} did not move when the effect list moved — it is not squeezing the \
             real preimage"
        );
    }
}

/// The fold repair must use the shared wide primitive, not a hand-rolled salt ladder:
/// `compute_effects_hash_4` is exactly the first four lanes of `hash_many_8` over the
/// SAME preimage the legacy 1-felt squeeze absorbs. Pinning this keeps a future edit
/// from quietly reintroducing a derived-lane construction.
#[test]
fn effects_hash_4_is_the_wide_sponge_over_the_real_preimage() {
    let effects = vec![VmEffect::Burn {
        target_hash: bytes32_to_8_limbs(&[3u8; 32]),
        amount_lo: BabyBear::new(1),
        amount_full: 1,
    }];
    let four = compute_effects_hash_4(&effects);

    // Reconstruct the preimage independently: tag 46 ‖ 8 target limbs ‖ amount_lo ‖
    // 4×16-bit amount limbs (`compute_effects_hash`'s Burn arm).
    let mut preimage = vec![BabyBear::new(46)];
    preimage.extend_from_slice(&bytes32_to_8_limbs(&[3u8; 32]));
    preimage.push(BabyBear::new(1));
    for i in 0..4 {
        preimage.push(BabyBear::new(((1u64 >> (i * 16)) & 0xFFFF) as u32));
    }
    let wide = hash_many_8(&preimage);
    assert_eq!(
        four,
        [wide[0], wide[1], wide[2], wide[3]],
        "the published 4 felts must be the wide sponge's first four squeezes over the \
         genuine effect preimage (which now carries all 8 burn-target limbs)"
    );
}
