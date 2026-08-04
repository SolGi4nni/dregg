//! # The Pasta field gates at the field the prover actually checks: the falsifier, exhibited.
//!
//! ## Substrate, said out loud
//!
//! **The AIR is Lean-authored.** Nothing in this file authors a constraint, a gadget or an
//! `air_accepts` predicate. It parses `circuit/descriptors/by-name/pasta-rcb-windowed.json`
//! (= `Dregg2.Circuit.Emit.PastaMsmWindowed.windowedRowDesc`), moves trace CELLS, and asks the
//! deployed `descriptor_ir2` prover.
//!
//! ## What is exhibited (MEASURED, not described)
//!
//! `Dregg2.Circuit.Emit.PastaField.fpMulCore` is one degree-2 gate
//! `xVal·yVal − p·qVal − zVal = 0`, over the 9×30 encoding. Its forcing lemma
//! (`fpMulCore_forces`, axiom-clean) concludes `p ∣ x·y − z` **from the gate body vanishing over
//! ℤ**. The deployed prover does not check that. It checks the body mod BabyBear
//! (`p_felt = 2013265921`).
//!
//! The nine quotient limbs enter with weights `p·2^(30 i)`, every one of them a unit mod
//! `p_felt`, and nothing pins those columns (`pastaLimbRange` is emitted nowhere; the only two
//! booleanity gates are on `BIT`/`DBL`). So a prover can move the quotient block to absorb any
//! change: pick `δ₁ = 1` on limb 1 and `δ₀ ≡ −2^30 (mod p_felt) = 939524097` on limb 0, and the
//! body's change `p·(δ₀ + 2^30·δ₁)` is a NONZERO multiple of `p_felt` — invisible to the prover,
//! `2^285` over ℤ.
//!
//! `the_deployed_prover_accepts_a_nonzero_integer_body` is that witness, proved and VERIFIED end
//! to end. It is the thing a sound encoding has to refuse.
//!
//! ⚠ Run in RELEASE. These are proving tests.

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2,
    parse_vm_descriptor2_unsound_oversized, prove_vm_descriptor2, verify_vm_descriptor2,
};

/// The Lean-emitted windowed row descriptor (`dregg-pasta-rcb-windowed::v1`).
const DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-rcb-windowed.json");
/// A Lean-emitted HONEST witness (`metatheory/EmitPastaWindowedTrace.lean`).
const TRACE_64: &str = include_str!("fixtures/pasta-rcb-windowed-trace-64.txt");

const WIDTH: usize = 525;
/// BabyBear's modulus — the field the deployed prover reads every gate body in.
const P_FELT: u64 = 2_013_265_921;

/// Constraint index 4 of the emitted descriptor is a Pasta multiply: 36 columns, 81 var×var
/// products, largest constant 495 bits. Its quotient block is columns 297..=305, entering with
/// coefficients `−p_pasta·2^(30 i)`. Each of those nine columns appears in exactly ONE constraint.
const Q_LIMB0: usize = 297;
const Q_LIMB1: usize = 298;

/// `−2^30 mod p_felt`. Adding this to quotient limb 0 while adding 1 to limb 1 changes the gate
/// body by `−p_pasta·(2^30 − 2^30) = 0` mod `p_felt`, and by a nonzero multiple of `p_felt` over ℤ.
const DELTA0: u64 = 939_524_097;
const DELTA1: u64 = 1;

fn descriptor() -> EffectVmDescriptor2 {
    parse_vm_descriptor2_unsound_oversized(DESC_JSON)
        .expect("the deployed checker must parse the Lean descriptor")
}

fn fixture() -> Vec<Vec<BabyBear>> {
    let rows: Vec<Vec<BabyBear>> = TRACE_64
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|t| BabyBear::new(t.parse::<u32>().expect("cell is a u32 decimal")))
                .collect::<Vec<_>>()
        })
        .collect();
    assert_eq!(rows.len(), 64, "the Lean fixture is 64 rows");
    assert!(rows.iter().all(|r| r.len() == WIDTH));
    rows
}

fn prove_and_verify(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>]) -> Result<(), String> {
    let proof = prove_vm_descriptor2(desc, trace, &[], &MemBoundaryWitness::default(), &[])
        .map_err(|e| format!("prove: {e}"))?;
    verify_vm_descriptor2(desc, &proof, &[]).map_err(|e| format!("verify: {e}"))
}

/// ⚑ **THE FALSIFIER.** Two cells of an honest Lean-emitted witness are moved. The gate's integer
/// body goes from `0` to a 285-bit nonzero value. The deployed prover PROVES it and the deployed
/// verifier ACCEPTS the proof — because the change is a multiple of `p_felt`, and `p_felt` is the
/// only field the emitted object is ever read in.
///
/// This is the pre-image the repair must refuse. Without it, "the gate forces `x·y ≡ z (mod p)`"
/// is a true statement about ℤ and an empty one about the proof object.
#[test]
fn the_deployed_prover_accepts_a_nonzero_integer_body() {
    let desc = descriptor();
    let honest = fixture();

    prove_and_verify(&desc, &honest)
        .expect("baseline: the honest Lean witness proves and verifies");

    let mut forged = honest.clone();
    let before = (
        forged[1][Q_LIMB0].as_u32() as u64,
        forged[1][Q_LIMB1].as_u32() as u64,
    );
    forged[1][Q_LIMB0] = BabyBear::new(((before.0 + DELTA0) % P_FELT) as u32);
    forged[1][Q_LIMB1] = BabyBear::new(((before.1 + DELTA1) % P_FELT) as u32);
    let after = (
        forged[1][Q_LIMB0].as_u32() as u64,
        forged[1][Q_LIMB1].as_u32() as u64,
    );
    assert_ne!(before, after, "the forgery must actually move the trace");

    // The integer body of constraint 4 on row 1: `0` honest, nonzero forged. Recomputed here from
    // the SAME weights the Lean head carries, so the claim is arithmetic and not a caption.
    let z_body_delta = integer_body_delta(after.0 as i128 - before.0 as i128, 1);
    assert_ne!(z_body_delta, 0, "the forged integer body must be nonzero");
    assert_eq!(
        z_body_delta.rem_euclid(P_FELT as i128),
        0,
        "…and invisible mod p_felt"
    );

    prove_and_verify(&desc, &forged).expect(
        "⚑ THE FALSIFIER: the deployed prover accepts a witness whose gate body is nonzero over ℤ",
    );
}

/// The change the forgery makes to constraint 4's integer body, in units of `p_pasta`:
/// `−p·(δ₀ + 2^30·δ₁)`. Returned divided by `p_pasta` (which is a unit mod `p_felt`), so the
/// arithmetic fits `i128` while the two assertions above stay exact.
fn integer_body_delta(d0: i128, d1: i128) -> i128 {
    -(d0 + (1i128 << 30) * d1)
}

// ─────────────────────────────────────────────────────────────────────────────────────────────
// THE REPAIR: `dregg-pasta-fpmul-sound::v1`, and BOTH polarities against it.
//
// `Dregg2.Circuit.Emit.PastaFieldSound.fpMulSoundDesc` = `EffectLower.lowerAir` of the source
// `EffectAir` `soundMulAir pLimb`. 8-bit limbs, 32 of them, carries range-checked at 16 bits.
// 63 coefficient gates + 190 range lookups = 253 constraints, 190 main columns, and the largest
// constant it writes is `2^23` — 24 bits, so `parse_int_field`'s mod-BabyBear fold is never
// reached on this descriptor (the `9×30` one needs it at 495 bits).
//
// The Lean side proves `felt_gates_force_congruence`: from `P ∣ body` for all 63 gates plus the
// range facts, `p_pasta ∣ x·y − z`. What this file adds is that the DEPLOYED prover agrees —
// the honest witness proves and verifies, and the forgeries are REFUSED.
// ─────────────────────────────────────────────────────────────────────────────────────────────

/// The Lean-emitted sound `fpMul` descriptor.
const SOUND_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-fpmul-sound.json");
/// The Lean-emitted honest witness (`PastaFieldSound.fpHonestRow`, whose gate-satisfaction and
/// carry-range membership are `decide`-proved in the Lean kernel).
const SOUND_TRACE: &str = include_str!("fixtures/pasta-fpmul-sound-trace.txt");

const SOUND_WIDTH: usize = 190;
const X_BASE: usize = 0;
const Z_BASE: usize = 64;
const Q_BASE: usize = 96;
const C_BASE: usize = 128;

fn sound_descriptor() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(SOUND_DESC_JSON).expect("the deployed checker parses the sound descriptor")
}

fn sound_trace() -> Vec<Vec<BabyBear>> {
    let rows: Vec<Vec<BabyBear>> = SOUND_TRACE
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|t| BabyBear::new(t.parse::<u32>().expect("cell is a u32 decimal")))
                .collect::<Vec<_>>()
        })
        .collect();
    assert_eq!(rows.len(), 8);
    assert!(rows.iter().all(|r| r.len() == SOUND_WIDTH));
    rows
}

/// The shape, measured off the parsed descriptor rather than asserted in prose.
#[test]
fn the_sound_descriptor_costs_253_constraints_and_190_columns() {
    let d = sound_descriptor();
    assert_eq!(d.name, "dregg-pasta-fpmul-sound::v1");
    assert_eq!(d.trace_width, SOUND_WIDTH);
    assert_eq!(d.constraints.len(), 253, "63 gates + 190 range lookups");
    assert_eq!(
        d.tables.len(),
        3,
        "main + an 8-bit range table + a 16-bit one"
    );
    assert!(
        d.ranges.is_empty(),
        "IR-v2 carries ranges as lookups, not the v1 array"
    );
}

/// **The honest polarity.** The Lean-generated witness proves and verifies under the deployed
/// prover, and the measurement is printed rather than quoted from an older caption.
#[test]
fn the_sound_multiply_proves_and_verifies() {
    let desc = sound_descriptor();
    let trace = sound_trace();
    let t0 = std::time::Instant::now();
    let proof = prove_vm_descriptor2(&desc, &trace, &[], &MemBoundaryWitness::default(), &[])
        .expect("the honest Lean witness proves under the SOUND descriptor");
    let prove_ms = t0.elapsed().as_secs_f64() * 1000.0;
    let t1 = std::time::Instant::now();
    verify_vm_descriptor2(&desc, &proof, &[]).expect("and verifies");
    let verify_ms = t1.elapsed().as_secs_f64() * 1000.0;
    println!(
        "SOUND fpMul: 253 constraints, {SOUND_WIDTH} main columns, 8 rows — \
         prove {prove_ms:.1} ms, verify {verify_ms:.1} ms"
    );
}

/// ⚑ **THE FALSIFIER, REFUSED.** The exact move that works against the `9×30` gate — perturb the
/// quotient block so the body's change is a multiple of `p_felt` — needs `δ₀ + 2^8·δ₁ ≡ 0
/// (mod p_felt)` with the smallest nonzero solution far above `2^8`. Both limbs are lookup-pinned
/// into `[0, 2^8)`, so the witness does not exist. Here it is attempted and refused.
#[test]
fn the_quotient_forgery_that_works_at_9x30_is_refused_here() {
    let desc = sound_descriptor();

    // (a) the smallest possible quotient tamper: +1 on limb 0. At 9×30 this was absorbed; here
    //     gate 0's body moves by `−p₀ ≠ 0` and `|p₀| < p_felt`, so it cannot vanish mod p_felt.
    let mut t = sound_trace();
    for row in t.iter_mut() {
        row[Q_BASE] = row[Q_BASE] + BabyBear::new(1);
    }
    assert!(
        prove_vm_descriptor2(&desc, &t, &[], &MemBoundaryWitness::default(), &[]).is_err(),
        "a +1 quotient limb must be REFUSED (at 9×30 the same class of tamper proved)"
    );

    // (b) the compensating pair — the actual 9×30 falsifier, transposed. `δ₀ = p_felt − 2^8`
    //     is the value that keeps the body invisible mod p_felt; it is ≥ 2^8, so the 8-bit range
    //     lookup has no decomposition for it.
    let mut t = sound_trace();
    for row in t.iter_mut() {
        row[Q_BASE] = BabyBear::new((P_FELT - 256) as u32);
        row[Q_BASE + 1] = row[Q_BASE + 1] + BabyBear::new(1);
    }
    assert!(
        prove_vm_descriptor2(&desc, &t, &[], &MemBoundaryWitness::default(), &[]).is_err(),
        "the compensating quotient pair must be REFUSED — the range lookup has no witness for it"
    );
}

/// ⚑ **A WRONG PRODUCT IS REFUSED.** Claim `z + 1` as the Pasta product and try to absorb it
/// anywhere in the free witness (the quotient block, the carry chain). Every route is closed:
/// the carry columns are pinned to 16 bits and the quotient limbs to 8.
#[test]
fn a_wrong_product_is_refused() {
    let desc = sound_descriptor();

    // z limb 0 + 1, everything else honest.
    let mut t = sound_trace();
    for row in t.iter_mut() {
        row[Z_BASE] = row[Z_BASE] + BabyBear::new(1);
    }
    assert!(
        prove_vm_descriptor2(&desc, &t, &[], &MemBoundaryWitness::default(), &[]).is_err(),
        "an off-by-one product must be REFUSED"
    );

    // …and with the carry-in "repaired" to absorb it: `c₀` shifted by 1 changes gate 1, so the
    // chain cannot swallow a digit error either.
    let mut t = sound_trace();
    for row in t.iter_mut() {
        row[Z_BASE] = row[Z_BASE] + BabyBear::new(1);
        row[C_BASE] = row[C_BASE] - BabyBear::new(1);
    }
    assert!(
        prove_vm_descriptor2(&desc, &t, &[], &MemBoundaryWitness::default(), &[]).is_err(),
        "a carry-compensated off-by-one product must be REFUSED"
    );
}

/// An out-of-range OPERAND limb is refused too — the bound `coefBody_abs_lt_P` is a hypothesis
/// about `x` and `y` as much as about `z` and `q`, and the descriptor emits the lookups that
/// discharge it. Without them the whole soundness argument is about a shape the prover does not
/// carry.
#[test]
fn an_out_of_range_operand_limb_is_refused() {
    let desc = sound_descriptor();
    let mut t = sound_trace();
    for row in t.iter_mut() {
        row[X_BASE] = BabyBear::new(256);
    }
    assert!(
        prove_vm_descriptor2(&desc, &t, &[], &MemBoundaryWitness::default(), &[]).is_err(),
        "an operand limb at 2^8 must be REFUSED by the 8-bit table"
    );
}
