//! # The SOUND Pasta curve row, and the pole it refuses.
//!
//! ## The pole, and where it is already exhibited on a CURVE row
//!
//! `dregg-pasta-rcb-windowed::v1` **is** a curve row — one RCB Algorithm-7 complete addition over
//! `PastaField`'s `9×30` encoding, 45 constraints, 525 columns, `"tables":[]`. Both halves of the
//! nonzero-ℤ-body pole are already exhibited on it, in release, as ACCEPTS:
//!
//! * the MULTIPLY half — `pasta_field_felt_soundness.rs:89`
//!   `the_deployed_prover_accepts_a_nonzero_integer_body`: two cells of the honest 64-row fixture's
//!   row 1 (constraint 4's quotient limbs 0 and 1, cols 297/298, by `939524097` and `1`) take the
//!   gate's integer body from `0` to a nonzero **285-bit** value, leave it `0 mod p_felt`, and
//!   `prove_vm_descriptor2` + `verify_vm_descriptor2` both accept;
//! * the ADD/SUB half — `pasta_addsub_felt_soundness.rs:125` and `:156`: two cells of the LAST row
//!   (`z` limb 0 by `(−2^240) mod p_felt = 1450097237`, `z` limb 8 by `1`) on constraint 33 (an
//!   add) and constraint 30 (a sub) take the body to a nonzero **241-bit / 240-bit** value, leave
//!   it `0 mod p_felt`, disturb no other constraint on any row, and both accept.
//!
//! ⚑ **This file is the other half: the same arithmetic, against a SOUND curve row, REFUSED.**
//! `dregg-pasta-{pallas,vesta}-complete-add-sound::v1` is the same RCB Algorithm 7 — the same 33
//! SSA ops in the same order — composed out of `PastaFieldSound` / `PastaAddSubSound` /
//! `PastaCurveSound`'s constant-multiply through the `SoundCore` bridge, and lowered by
//! `EffectLower.lowerAir`. 4 476 constraints, 3 048 columns, three declared range tables.
//!
//! The reason the pole closes is not that the tamper is detected downstream. It is that the
//! forgery's **witness does not exist**: every gate body is bounded below `p_felt`
//! (`PastaFieldSound.coefBody_abs_lt_P` = 141 592 831, `PastaAddSubSound.adBody_abs_lt_P` = 33 916,
//! `PastaCurveSound.smBody_abs_lt_P` = 8 551 681), so a nonzero ℤ body cannot be `0 mod p_felt`;
//! and the compensating cell the `9×30` forgery needs is `≥ 2^8`, which the declared 8-bit lookup
//! has no decomposition for. Both facts are asserted below rather than described.
//!
//! ⚠ **Run in RELEASE.** The algebraic refusals are debug-assert panics in debug and clean `Err`s
//! in release:
//!
//! ```text
//! cargo test -p dregg-circuit --release --test pasta_curve_row_felt_soundness -- --nocapture
//! ```
//!
//! ## Provenance
//!
//! Descriptors: `metatheory/EmitByName.lean` rows `pasta-pallas-complete-add-sound.json` /
//! `pasta-vesta-complete-add-sound.json` → `PastaCurveSound.{pallas,vesta}CompleteAddSoundDesc`,
//! re-emitted by `scripts/emit-descriptors.sh`. Traces: `metatheory/EmitPastaCurveSound.lean`
//! (`pallastrace` / `vestatrace`), the Lean-generated honest witness for `G + G` — RCB's DOUBLING
//! case, so the row exercises strong unification. Rust fills cells; it authors nothing.

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};

const PALLAS_DESC_JSON: &str =
    include_str!("../descriptors/by-name/pasta-pallas-complete-add-sound.json");
const VESTA_DESC_JSON: &str =
    include_str!("../descriptors/by-name/pasta-vesta-complete-add-sound.json");
const PALLAS_TRACE: &str = include_str!("fixtures/pasta-pallas-complete-add-sound-trace.txt");
const VESTA_TRACE: &str = include_str!("fixtures/pasta-vesta-complete-add-sound-trace.txt");

const WIDTH: usize = 3048;
const ROWS: usize = 8;
const CONSTRAINTS: usize = 4476;
const P_FELT: u64 = 2_013_265_921;

/// `SK` — limbs per Pasta field element in the sound encoding.
const SK: usize = 32;

// ── The row layout, mirroring `PastaCurveSound.{vBase, mWit, sWit, aWit}` ────────────────────────
/// The six input blocks: `X1 Y1 Z1 X2 Y2 Z2` at `0, 32, 64, 96, 128, 160`.
const IN_X1: usize = 0;
/// The 33 SSA intermediates start here, 32 columns apart.
const V_BASE: usize = 6 * SK;
/// The 12 multiply witnesses: 32 quotient limbs then 62 sixteen-bit carries, 94 columns apart.
const MW_BASE: usize = V_BASE + 33 * SK;
/// The 2 constant-multiply witnesses: one quotient column then 31 carries.
const SW_BASE: usize = MW_BASE + 12 * 94;
/// The 19 add/sub witnesses: the carry/borrow bit then 31 carries.
const AW_BASE: usize = SW_BASE + 2 * SK;

/// The `i`-th SSA intermediate's limb block.
const fn v(i: usize) -> usize {
    V_BASE + SK * i
}
/// The `k`-th multiply's quotient block (its carries begin at `+ SK`).
const fn mw(k: usize) -> usize {
    MW_BASE + 94 * k
}
/// The `k`-th constant-multiply's quotient column (its carries begin at `+ 1`).
const fn sw(k: usize) -> usize {
    SW_BASE + SK * k
}
/// The `k`-th add/sub's carry/borrow bit (its carries begin at `+ 1`).
const fn aw(k: usize) -> usize {
    AW_BASE + SK * k
}

/// `X3` is SSA intermediate 26 (`X3g`), `Y3` is 29 (`Y3f`), `Z3` is 32 (`Z3c`).
const X3: usize = v(26);
const Z3: usize = v(32);

fn descriptor(json: &str) -> EffectVmDescriptor2 {
    parse_vm_descriptor2(json).expect("the STRICT deployed checker parses the sound curve row")
}

fn trace(text: &str) -> Vec<Vec<BabyBear>> {
    let rows: Vec<Vec<BabyBear>> = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|t| BabyBear::new(t.parse::<u32>().expect("cell is a u32 decimal")))
                .collect::<Vec<_>>()
        })
        .collect();
    assert_eq!(rows.len(), ROWS);
    assert!(rows.iter().all(|r| r.len() == WIDTH));
    rows
}

fn refuses(desc: &EffectVmDescriptor2, t: &[Vec<BabyBear>], why: &str) {
    assert!(
        prove_vm_descriptor2(desc, t, &[], &MemBoundaryWitness::default(), &[]).is_err(),
        "{why}"
    );
}

// ────────────────────────────────────────────────────────────────────────────────────────────────
// The shape, measured off the parsed descriptors.
// ────────────────────────────────────────────────────────────────────────────────────────────────

/// ⚑ **THE PRICE, off the emitted object.** `6·32` input lookups `+ 12·189` multiplies
/// `+ 2·96` constant-multiplies `+ 19·96` add/subs. The unsound row it replaces is 33 constraints
/// and 496 columns, so this is **135.6×** the arithmetic and **6.15×** the width.
///
/// ⚠ The in-tree figure (`Dregg2.lean`, `PastaMsmBucketed` §6d `soundRcbConstraintsHigh`) is
/// `4 470`, and it is within 0.13% of this **by two compensating errors**: it prices both
/// constant-multiplies at the multiply's marginal `189` (over by `2·93 = 186`) and omits the six
/// input limb blocks (`6·32 = 192`). `PastaCurveSound.the_in_tree_figure_is_right_for_two_wrong_reasons`
/// is that arithmetic in the kernel.
#[test]
fn the_sound_curve_row_costs_4476_constraints_and_3048_columns() {
    for (name, json) in [
        (
            "dregg-pasta-pallas-complete-add-sound::v1",
            PALLAS_DESC_JSON,
        ),
        ("dregg-pasta-vesta-complete-add-sound::v1", VESTA_DESC_JSON),
    ] {
        let d = descriptor(json);
        assert_eq!(d.name, name);
        assert_eq!(d.trace_width, WIDTH);
        assert_eq!(
            d.constraints.len(),
            CONSTRAINTS,
            "192 input lookups + 12·189 + 2·96 + 19·96"
        );
        assert_eq!(
            d.tables.len(),
            4,
            "main + range_w8 + range_w16 + range_w1 — the UNION of what the sound multiply \
             and the sound add/sub declare, and nothing new"
        );
        assert!(
            d.ranges.is_empty(),
            "IR-v2 carries ranges as lookups, not the v1 array"
        );
    }
}

/// ⚑ **AND IT PARSES STRICT.** The nine `pasta-rcb-*` descriptors need
/// `parse_vm_descriptor2_unsound_oversized` because the `9×30` encoding's largest coefficient is
/// 495 bits. Every coefficient here fits a felt, so the strict parser — the one the deployed path
/// uses — takes it. That is a consequence of the encoding, not a separate repair.
#[test]
fn the_sound_curve_row_needs_no_oversized_constant_escape() {
    assert!(parse_vm_descriptor2(PALLAS_DESC_JSON).is_ok());
    assert!(parse_vm_descriptor2(VESTA_DESC_JSON).is_ok());
}

// ────────────────────────────────────────────────────────────────────────────────────────────────
// The honest polarity.
// ────────────────────────────────────────────────────────────────────────────────────────────────

/// **The honest row proves and verifies, on both curves.** The witness is the Lean-generated
/// `PastaCurveSound.{pallas,vesta}HonestRow` for `G + G` — the doubling case, so the row is the one
/// RCB's strong unification has to handle. Timings are printed, not quoted from a caption.
#[test]
fn the_sound_curve_row_proves_and_verifies_on_both_curves() {
    for (curve, json, text) in [
        ("Pallas", PALLAS_DESC_JSON, PALLAS_TRACE),
        ("Vesta", VESTA_DESC_JSON, VESTA_TRACE),
    ] {
        let desc = descriptor(json);
        let t = trace(text);
        let t0 = std::time::Instant::now();
        let proof = prove_vm_descriptor2(&desc, &t, &[], &MemBoundaryWitness::default(), &[])
            .expect("the honest Lean witness proves under the SOUND curve row");
        let prove_ms = t0.elapsed().as_secs_f64() * 1000.0;
        let t1 = std::time::Instant::now();
        verify_vm_descriptor2(&desc, &proof, &[]).expect("and verifies");
        let verify_ms = t1.elapsed().as_secs_f64() * 1000.0;
        println!(
            "SOUND RCB complete add ({curve}): {CONSTRAINTS} constraints, {WIDTH} main columns, \
             {ROWS} rows — prove {prove_ms:.1} ms, verify {verify_ms:.1} ms"
        );
    }
}

// ────────────────────────────────────────────────────────────────────────────────────────────────
// The pole, refused — one test per gate kind in the row.
// ────────────────────────────────────────────────────────────────────────────────────────────────

/// ⚑ **THE MULTIPLY POLE, REFUSED.** `pasta_field_felt_soundness.rs:89` moves two quotient limbs of
/// a multiply inside `pasta-rcb-windowed.json` — a curve row — by `939524097` and `1`, takes the
/// gate's ℤ body to a nonzero 285-bit value, leaves it `0 mod p_felt`, and the deployed prover
/// **accepts**. Here the same two moves are made against multiply 0 of the sound row (`t0a = X1·X2`,
/// quotient block at column `mw(0)`), and both are refused.
///
/// The second one is the interesting one and its refusal is arithmetic, not detection: for the body
/// change to vanish mod `p_felt` the low limb must carry `p_felt − 2^8`, which is `≥ 2^8`, so the
/// declared 8-bit lookup has no decomposition for it. That is asserted before the prove.
#[test]
fn the_multiply_pole_that_the_unsound_curve_row_accepts_is_refused_here() {
    let desc = descriptor(PALLAS_DESC_JSON);

    // (a) the smallest possible quotient tamper: +1 on limb 0 of multiply 0. At 9×30 this class of
    //     move is absorbed by the unpinned quotient columns; here gate 0's body moves by `−p₀ ≠ 0`
    //     with `|p₀| < 2^8 < p_felt`, so it cannot vanish mod p_felt.
    let mut t = trace(PALLAS_TRACE);
    for row in t.iter_mut() {
        row[mw(0)] = row[mw(0)] + BabyBear::new(1);
    }
    refuses(
        &desc,
        &t,
        "a +1 quotient limb on a curve-row multiply must be REFUSED — \
         at 9×30 the same class of tamper PROVES (pasta_field_felt_soundness.rs:89)",
    );

    // (b) the compensating pair — the 9×30 falsifier transposed. The witness does not exist.
    let compensator = P_FELT - 256;
    assert!(
        compensator >= 256,
        "the cell the forgery needs is out of the declared 8-bit range — that IS the repair"
    );
    let mut t = trace(PALLAS_TRACE);
    for row in t.iter_mut() {
        row[mw(0)] = BabyBear::new(compensator as u32);
        row[mw(0) + 1] = row[mw(0) + 1] + BabyBear::new(1);
    }
    refuses(
        &desc,
        &t,
        "the compensating quotient pair must be REFUSED — the 8-bit lookup has no witness",
    );
}

/// ⚑ **THE ADD/SUB POLE, REFUSED.** `pasta_addsub_felt_soundness.rs:125`/`:156` move two cells of a
/// result block on `pasta-rcb-windowed.json` — `z` limb 0 by `(−2^240) mod p_felt = 1450097237` and
/// `z` limb 8 by `1` — so the ℤ body changes by `−(δ₀ + 2^240·δ₈)`, a nonzero multiple of `p_felt`,
/// and the prover **accepts**. `X3g` (`v(26)`) is the analogous block here: it is a SUB's result and
/// it is the row's `X3` output.
///
/// At `8×32` the limb weights are `2^(8i)`, so the compensating low limb would have to be
/// `(−2^(8·8)) mod p_felt`. That number is asserted out of range before the prove — the forgery has
/// no witness rather than being caught by a later check.
#[test]
fn the_addsub_pole_that_the_unsound_curve_row_accepts_is_refused_here() {
    let desc = descriptor(PALLAS_DESC_JSON);

    // The 9×30 move's own invariant, restated at 8×32: a compensating pair still exists over ℤ…
    let weight_8 = mod_pow2(8 * 8);
    let compensator = (P_FELT - weight_8) % P_FELT;
    assert_eq!(
        (compensator + weight_8) % P_FELT,
        0,
        "the pair is still invisible mod p_felt — the arithmetic did not change"
    );
    // …and it is STILL out of the declared range, which is what changed.
    assert!(
        compensator >= 256,
        "the compensating limb {compensator} must be outside [0, 2^8) — \
         that is why the 9×30 forgery has no 8×32 witness"
    );

    let mut t = trace(PALLAS_TRACE);
    for row in t.iter_mut() {
        row[X3] = BabyBear::new(compensator as u32);
        row[X3 + 8] = row[X3 + 8] + BabyBear::new(1);
    }
    refuses(
        &desc,
        &t,
        "the compensating result-limb pair must be REFUSED — \
         at 9×30 the same move PROVES (pasta_addsub_felt_soundness.rs:125)",
    );

    // And the smallest tamper — +1 on the low limb of the row's X3 output — moves gate 0 of that
    // sub's block by −1, whose absolute value is 1 < p_felt, so it cannot hide.
    let mut t = trace(PALLAS_TRACE);
    for row in t.iter_mut() {
        row[X3] = row[X3] + BabyBear::new(1);
    }
    refuses(&desc, &t, "a +1 on the X3 output limb must be REFUSED");
}

/// ⚑ **THE CONSTANT-MULTIPLY POLE, REFUSED — and this core did not exist before.**
/// `PastaMsmBucketed.lean:1206-1208` recorded that "no sound `smul` core exists at all", so RCB's
/// two `b3 = 15` multiplies were priced at the full multiply's shape by assumption. They are real
/// gates now, at 96 constraints and 32 columns each, and they carry their own bound
/// (`smBody_abs_lt_P` = 8 551 681 < p_felt, with 16-bit carries because the digit reaches `2^17`
/// where add/sub's reached `2^10`).
///
/// Both of its free witnesses are attacked: the single reduction-quotient column and the carry
/// chain.
#[test]
fn the_constant_multiply_witness_is_refused() {
    let desc = descriptor(PALLAS_DESC_JSON);

    // (a) the reduction quotient of `t2b = 15·t2a`.
    let mut t = trace(PALLAS_TRACE);
    for row in t.iter_mut() {
        row[sw(0)] = row[sw(0)] + BabyBear::new(1);
    }
    refuses(
        &desc,
        &t,
        "a +1 on the constant-multiply's reduction quotient must be REFUSED",
    );

    // (b) its carry chain — the columns a 16-bit lookup pins.
    let mut t = trace(PALLAS_TRACE);
    for row in t.iter_mut() {
        row[sw(1) + 1] = row[sw(1) + 1] + BabyBear::new(1);
    }
    refuses(
        &desc,
        &t,
        "a +1 on the constant-multiply's carry must be REFUSED",
    );

    // (c) an out-of-range quotient: the 8-bit lookup has no decomposition for 256.
    let mut t = trace(PALLAS_TRACE);
    for row in t.iter_mut() {
        row[sw(0)] = BabyBear::new(256);
    }
    refuses(
        &desc,
        &t,
        "an out-of-range constant-multiply quotient must be REFUSED",
    );
}

/// ⚑ **A WRONG POINT IS REFUSED.** Claim `Z3 + 1` as the third projective coordinate and try to
/// absorb it in the free witness of the add that produces it (its carry/borrow bit, its carry
/// chain). Every route is closed.
#[test]
fn a_wrong_output_point_is_refused() {
    let desc = descriptor(PALLAS_DESC_JSON);

    let mut t = trace(PALLAS_TRACE);
    for row in t.iter_mut() {
        row[Z3] = row[Z3] + BabyBear::new(1);
    }
    refuses(&desc, &t, "a wrong Z3 must be REFUSED");

    // …with a compensating carry-bit flip on the add that writes Z3 (`aWit 18`).
    let mut t = trace(PALLAS_TRACE);
    for row in t.iter_mut() {
        row[Z3] = row[Z3] + BabyBear::new(1);
        row[aw(18)] = row[aw(18)] + BabyBear::new(1);
    }
    refuses(&desc, &t, "a carry-compensated wrong Z3 must be REFUSED");

    // …and an out-of-range carry BIT is refused by the 1-bit table.
    let mut t = trace(PALLAS_TRACE);
    for row in t.iter_mut() {
        row[aw(18)] = BabyBear::new(2);
    }
    refuses(
        &desc,
        &t,
        "a carry bit of 2 must be REFUSED by the 1-bit table",
    );
}

/// ⚑ **AN OUT-OF-RANGE INPUT LIMB IS REFUSED.** The six input blocks are the ones a CHAINED row
/// does not pay for (their producer ranges them); a standalone row declares them, and the
/// declaration bites.
#[test]
fn an_out_of_range_input_limb_is_refused() {
    let desc = descriptor(PALLAS_DESC_JSON);
    let mut t = trace(PALLAS_TRACE);
    for row in t.iter_mut() {
        row[IN_X1] = BabyBear::new(256);
    }
    refuses(&desc, &t, "an out-of-range input limb must be REFUSED");
}

/// `2^e mod p_felt`, by repeated doubling — the same helper
/// `pasta_addsub_felt_soundness.rs:96` uses, so the two files compute the compensator the same way.
fn mod_pow2(e: u32) -> u64 {
    let mut acc: u64 = 1;
    for _ in 0..e {
        acc = (acc * 2) % P_FELT;
    }
    acc
}
