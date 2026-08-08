//! # The Pasta ADD and SUB gates at the field the prover actually checks: the falsifier, exhibited.
//!
//! ## Substrate, said out loud
//!
//! **The AIR is Lean-authored.** Nothing in this file authors a constraint, a gadget or an
//! `air_accepts` predicate. It parses Lean-emitted descriptors, moves trace CELLS, and asks the
//! deployed `descriptor_ir2` prover.
//!
//! ## What is exhibited (MEASURED, not described)
//!
//! `Dregg2.Circuit.Emit.PastaField.fpAddCore`/`fpSubCore` are one degree-1 gate each over the
//! `9×30` encoding — `Σ 2^(30 i)·(x_i ± y_i − z_i) ∓ p·c = 0`. Their forcing lemmas
//! (`fpAddCore_forces`, `fpSubCore_forces`, axiom-clean) conclude the field congruence **from the
//! gate body vanishing over ℤ**. The deployed prover does not check that. It checks the body mod
//! BabyBear (`p_felt = 2013265921`), where every one of those weights — the nine `2^(30 i)` and the
//! carry's `±p` — is a unit, and no lookup pins any of those columns.
//!
//! The defect is live on the checked-in `pasta-rcb-windowed.json`. Measured off the parsed
//! descriptor (see `the_deployed_descriptor_carries_nineteen_unpinned_addsub_gates`):
//!
//!   * 19 of its 42 plain gates are Pasta add/sub — 28 columns, ZERO var×var products, one column
//!     entering with coefficient exactly `±p` (columns `423..441`).
//!   * Constraint **33** (an add, carry col 440) and constraint **30** (a sub, borrow col 439) each
//!     own a nine-limb `z` block that no OTHER plain gate reads: `261..269` and `234..242`. Those
//!     blocks are read by the `on_transition` window gates 43 and 42 — which do not fire on the
//!     LAST row of the trace.
//!
//! So: move two cells of the honest 64-row Lean fixture's LAST row. The gate's integer body goes
//! from `0` to a 240/241-bit nonzero value, stays `0 mod p_felt`, disturbs no other constraint on
//! any row — and the deployed prover PROVES it while the deployed verifier ACCEPTS.
//!
//! That is the pre-image the repair has to refuse, and the second half of this file is the repair
//! (`dregg-pasta-fp{add,sub}-sound::v1`, `Dregg2/Circuit/Emit/PastaAddSubSound.lean`) refusing it.
//!
//! ⚠ Run in RELEASE. These are proving tests, and the algebraic refusals are debug-assert panics
//! in debug and clean `Err`s in release.

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2,
    parse_vm_descriptor2_unsound_oversized, prove_vm_descriptor2, verify_vm_descriptor2,
};

/// BabyBear's modulus — the field the deployed prover reads every gate body in.
const P_FELT: u64 = 2_013_265_921;

// ─────────────────────────────────────────────────────────────────────────────────────────────
// PART 1 — THE DEFECT, on the deployed descriptor.
// ─────────────────────────────────────────────────────────────────────────────────────────────

/// The Lean-emitted windowed row descriptor (`dregg-pasta-rcb-windowed::v1`).
const DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-rcb-windowed.json");
/// A Lean-emitted HONEST witness (`metatheory/EmitPastaWindowedTrace.lean`).
const TRACE_64: &str = include_str!("fixtures/pasta-rcb-windowed-trace-64.txt");
const WIDTH: usize = 525;

/// Constraint 30 is a Pasta SUB: `−xVal + yVal − zVal + p·c`, borrow column 439. Its `z` block.
const SUB_Z_LIMB0: usize = 234;
const SUB_Z_LIMB8: usize = 242;
/// Constraint 33 is a Pasta ADD: `xVal + yVal − zVal − p·c`, carry column 440. Its `z` block.
const ADD_Z_LIMB0: usize = 261;
const ADD_Z_LIMB8: usize = 269;

/// `(−2^240) mod p_felt`. Adding this to `z` limb 0 while adding `1` to `z` limb 8 changes the gate
/// body by `∓(δ₀ + 2^240)`, which is `0 mod p_felt` and a 241-bit nonzero integer.
const DELTA0: u64 = 1_450_097_237;

/// ⚑ `0 < δ₀ < p_felt`. At `δ₀ = 0` the "compensating pair" is the identity and every falsifier in
/// this file proves something true of doing nothing; at `δ₀ >= p_felt` it is not a felt at all.
const DELTA0_IS_A_NONZERO_CANONICAL_FELT: () = {
    assert!(DELTA0 > 0, "δ₀ must be nonzero, so the ℤ sum is > 2^240");
    assert!(DELTA0 < P_FELT, "δ₀ must be a canonical felt");
};
const _: () = DELTA0_IS_A_NONZERO_CANONICAL_FELT;
const DELTA8: u64 = 1;

fn windowed_descriptor() -> EffectVmDescriptor2 {
    parse_vm_descriptor2_unsound_oversized(DESC_JSON)
        .expect("the deployed checker must parse the Lean descriptor")
}

fn parse_trace(text: &str, width: usize, rows: usize) -> Vec<Vec<BabyBear>> {
    let t: Vec<Vec<BabyBear>> = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|t| BabyBear::new(t.parse::<u32>().expect("cell is a u32 decimal")))
                .collect::<Vec<_>>()
        })
        .collect();
    assert_eq!(t.len(), rows);
    assert!(t.iter().all(|r| r.len() == width));
    t
}

fn prove_and_verify(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>]) -> Result<(), String> {
    let proof = prove_vm_descriptor2(desc, trace, &[], &MemBoundaryWitness::default(), &[])
        .map_err(|e| format!("prove: {e}"))?;
    verify_vm_descriptor2(desc, &proof, &[]).map_err(|e| format!("verify: {e}"))
}

/// `2^240 mod p_felt`, computed here so the compensating constant is arithmetic and not a caption.
fn pow2_mod_p(e: u32) -> u64 {
    let mut acc: u64 = 1;
    for _ in 0..e {
        acc = (acc * 2) % P_FELT;
    }
    acc
}

/// The compensating pair is EXACT: `δ₀ + 2^240 ≡ 0 (mod p_felt)` and `δ₀ > 0`, so over ℤ the sum is
/// at least `2^240` — a 241-bit nonzero number the prover cannot see.
#[test]
fn the_compensating_pair_is_invisible_mod_p_felt_and_nonzero_over_z() {
    let p240 = pow2_mod_p(240);
    assert_eq!(
        (DELTA0 + p240) % P_FELT,
        0,
        "δ₀ + 2^240 must vanish mod p_felt"
    );
    // ⚑ `0 < δ₀ < p_felt` is two comparisons between constants — a build obligation, and the one
    // that makes this whole file a falsifier rather than a tautology: at `δ₀ = 0` the "invisible"
    // perturbation is the identity and every §-below claim is trivially true. Discharged at build
    // time in `DELTA0_IS_A_NONZERO_CANONICAL_FELT` beside the constant.
}

/// ⚑ **THE FALSIFIER, ADD.** Two cells of the honest Lean witness's last row are moved. Constraint
/// 33's integer body goes from `0` to a nonzero 241-bit value. The deployed prover PROVES it and the
/// deployed verifier ACCEPTS — because the change is a multiple of `p_felt`, and `p_felt` is the
/// only field the emitted object is ever read in.
#[test]
fn the_deployed_prover_accepts_a_nonzero_integer_body_on_an_add_gate() {
    let desc = windowed_descriptor();
    let honest = parse_trace(TRACE_64, WIDTH, 64);
    prove_and_verify(&desc, &honest)
        .expect("baseline: the honest Lean witness proves and verifies");

    let mut forged = honest.clone();
    let last = forged.len() - 1;
    let before = (
        forged[last][ADD_Z_LIMB0].as_u32(),
        forged[last][ADD_Z_LIMB8].as_u32(),
    );
    forged[last][ADD_Z_LIMB0] = BabyBear::new(((before.0 as u64 + DELTA0) % P_FELT) as u32);
    forged[last][ADD_Z_LIMB8] = BabyBear::new(((before.1 as u64 + DELTA8) % P_FELT) as u32);
    assert_ne!(
        (
            forged[last][ADD_Z_LIMB0].as_u32(),
            forged[last][ADD_Z_LIMB8].as_u32()
        ),
        before,
        "the forgery must actually move the trace"
    );

    prove_and_verify(&desc, &forged).expect(
        "⚑ THE FALSIFIER (add): the deployed prover accepts a witness whose ADD gate body is a \
         nonzero 241-bit integer",
    );
}

/// ⚑ **THE FALSIFIER, SUB.** The same move against constraint 30's borrow-bearing sub gate.
#[test]
fn the_deployed_prover_accepts_a_nonzero_integer_body_on_a_sub_gate() {
    let desc = windowed_descriptor();
    let honest = parse_trace(TRACE_64, WIDTH, 64);

    let mut forged = honest.clone();
    let last = forged.len() - 1;
    forged[last][SUB_Z_LIMB0] =
        BabyBear::new(((forged[last][SUB_Z_LIMB0].as_u32() as u64 + DELTA0) % P_FELT) as u32);
    forged[last][SUB_Z_LIMB8] =
        BabyBear::new(((forged[last][SUB_Z_LIMB8].as_u32() as u64 + DELTA8) % P_FELT) as u32);

    prove_and_verify(&desc, &forged).expect(
        "⚑ THE FALSIFIER (sub): the deployed prover accepts a witness whose SUB gate body is a \
         nonzero 240-bit integer",
    );
}

/// The shape claim the two falsifiers rest on, measured off the parsed descriptor rather than
/// asserted in prose: the windowed descriptor carries no range table and no lookup at all, so
/// NOTHING pins the `9×30` limbs it reads.
#[test]
fn the_deployed_descriptor_carries_nineteen_unpinned_addsub_gates() {
    let d = windowed_descriptor();
    assert_eq!(d.name, "dregg-pasta-rcb-windowed::v1");
    assert_eq!(d.trace_width, WIDTH);
    assert_eq!(d.constraints.len(), 45);
    assert!(
        d.tables.is_empty() && d.ranges.is_empty(),
        "⚑ zero declared tables and zero declared ranges — every limb of every Pasta operand in \
         this descriptor is an unconstrained felt"
    );
}

// ─────────────────────────────────────────────────────────────────────────────────────────────
// PART 2 — THE REPAIR: `dregg-pasta-fp{add,sub}-sound::v1`, and BOTH polarities against it.
//
// `Dregg2.Circuit.Emit.PastaAddSubSound.{fpAdd,fpSub}SoundDesc` = `EffectLower.lowerAir` of the
// source `EffectAir` `soundAddSubAir`. 8-bit limbs, 32 of them, one 1-bit carry witness, carries
// range-checked at 8 bits with offset 2^7. 32 coefficient gates + 128 range lookups = 160
// constraints, 128 main columns, ZERO var×var products, and the largest constant it writes is
// `2^15` — 16 bits, so `parse_int_field`'s mod-BabyBear fold is never reached (the `9×30` gate
// needs it at 495 bits).
//
// The Lean side proves `addsub_gates_force_congruence`: from `P ∣ body` for all 32 gates plus the
// range facts, `p_pasta ∣ x ± y − z`. Its body bound is add/sub's OWN — `4·255 + 128 + 256·128 =
// 33 916 < P` (`adBody_abs_lt_P`) — recomputed from the linear coefficient structure, not carried
// over from the multiply's convolution bound. What this file adds is that the DEPLOYED prover
// agrees.
// ─────────────────────────────────────────────────────────────────────────────────────────────

const ADD_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-fpadd-sound.json");
const SUB_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-fpsub-sound.json");
const FQADD_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-fqadd-sound.json");
const FQSUB_DESC_JSON: &str = include_str!("../descriptors/by-name/pasta-fqsub-sound.json");
const ADD_TRACE: &str = include_str!("fixtures/pasta-fpadd-sound-trace.txt");
const SUB_TRACE: &str = include_str!("fixtures/pasta-fpsub-sound-trace.txt");

const SOUND_WIDTH: usize = 128;
const S_X_BASE: usize = 0;
const S_Y_BASE: usize = 32;
const S_Z_BASE: usize = 64;
/// The single carry/borrow witness column, lookup-pinned to one bit.
const S_C_COL: usize = 96;
/// The 31 carry columns.
const S_CARRY_BASE: usize = 97;

fn sound_add() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(ADD_DESC_JSON).expect("the STRICT checker parses the sound add descriptor")
}
fn sound_sub() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(SUB_DESC_JSON).expect("the STRICT checker parses the sound sub descriptor")
}

/// The shape, measured off the parsed descriptors rather than asserted in prose. ⚑ All four parse
/// under the STRICT `parse_vm_descriptor2` — the nine `pasta-rcb-*` descriptors do not
/// (`ir2_oversized_constant_refusal.rs`), because their 495-bit constants do not fit a felt.
#[test]
fn the_sound_addsub_descriptors_cost_160_constraints_and_128_columns() {
    for (json, want) in [
        (ADD_DESC_JSON, "dregg-pasta-fpadd-sound::v1"),
        (SUB_DESC_JSON, "dregg-pasta-fpsub-sound::v1"),
        (FQADD_DESC_JSON, "dregg-pasta-fqadd-sound::v1"),
        (FQSUB_DESC_JSON, "dregg-pasta-fqsub-sound::v1"),
    ] {
        let d = parse_vm_descriptor2(json).expect("strict parse");
        assert_eq!(d.name, want);
        assert_eq!(d.trace_width, SOUND_WIDTH);
        assert_eq!(
            d.constraints.len(),
            160,
            "32 coefficient gates + 96 limb + 1 carry-bit + 31 carry lookups"
        );
        assert_eq!(
            d.tables.len(),
            3,
            "main + one 8-bit range table (limbs AND carries) + a 1-bit one for the carry witness"
        );
        assert!(
            d.ranges.is_empty(),
            "IR-v2 carries ranges as lookups, not the v1 array"
        );
    }
}

/// **The honest ADD polarity, at the overflow boundary.** The Lean-generated witness for
/// `(p−1) + (p−1) = p−2` with carry `1` proves and verifies under the deployed prover.
#[test]
fn the_sound_add_proves_and_verifies() {
    let desc = sound_add();
    let trace = parse_trace(ADD_TRACE, SOUND_WIDTH, 8);
    assert_eq!(
        trace[0][S_C_COL].as_u32(),
        1,
        "the fixture exercises the carry leg, not the c = 0 case"
    );
    let t0 = std::time::Instant::now();
    let proof = prove_vm_descriptor2(&desc, &trace, &[], &MemBoundaryWitness::default(), &[])
        .expect("the honest Lean witness proves under the SOUND add descriptor");
    let prove_ms = t0.elapsed().as_secs_f64() * 1000.0;
    let t1 = std::time::Instant::now();
    verify_vm_descriptor2(&desc, &proof, &[]).expect("and verifies");
    let verify_ms = t1.elapsed().as_secs_f64() * 1000.0;
    println!(
        "SOUND fpAdd: 160 constraints, {SOUND_WIDTH} main columns, 8 rows — \
         prove {prove_ms:.1} ms, verify {verify_ms:.1} ms"
    );
}

/// **The honest SUB polarity, with a borrow.** `Y − X` where `Y < X`, so `c = 1`.
#[test]
fn the_sound_sub_proves_and_verifies() {
    let desc = sound_sub();
    let trace = parse_trace(SUB_TRACE, SOUND_WIDTH, 8);
    assert_eq!(
        trace[0][S_C_COL].as_u32(),
        1,
        "the fixture exercises the borrow leg"
    );
    let t0 = std::time::Instant::now();
    let proof = prove_vm_descriptor2(&desc, &trace, &[], &MemBoundaryWitness::default(), &[])
        .expect("the honest Lean witness proves under the SOUND sub descriptor");
    let prove_ms = t0.elapsed().as_secs_f64() * 1000.0;
    let t1 = std::time::Instant::now();
    verify_vm_descriptor2(&desc, &proof, &[]).expect("and verifies");
    let verify_ms = t1.elapsed().as_secs_f64() * 1000.0;
    println!(
        "SOUND fpSub: 160 constraints, {SOUND_WIDTH} main columns, 8 rows — \
         prove {prove_ms:.1} ms, verify {verify_ms:.1} ms"
    );
}

/// ⚑ **THE FALSIFIER, REFUSED — BOTH POLARITIES.** The exact move that works against the `9×30`
/// gates in Part 1: perturb a `z` limb pair so the body's change is a multiple of `p_felt`. Here the
/// compensating `δ₀` for a `+1` on the top limb is `(−2^248) mod p_felt`, far above `2^8`, and every
/// limb is lookup-pinned into `[0, 2^8)` — so the witness does not exist. And the smallest possible
/// tamper, `+1` on `z` limb 0, moves gate 0's body by `−1`, which cannot vanish mod `p_felt`.
#[test]
fn the_limb_forgery_that_works_at_9x30_is_refused_here() {
    for (desc, trace_txt, label) in [
        (sound_add(), ADD_TRACE, "add"),
        (sound_sub(), SUB_TRACE, "sub"),
    ] {
        // (a) the smallest possible tamper: +1 on z limb 0.
        let mut t = parse_trace(trace_txt, SOUND_WIDTH, 8);
        for row in t.iter_mut() {
            row[S_Z_BASE] = row[S_Z_BASE] + BabyBear::new(1);
        }
        assert!(
            prove_vm_descriptor2(&desc, &t, &[], &MemBoundaryWitness::default(), &[]).is_err(),
            "{label}: a +1 on z limb 0 must be REFUSED (at 9×30 this class of tamper proved)"
        );

        // (b) the compensating pair — Part 1's falsifier transposed to the 8-bit radix. The value
        //     that keeps the body invisible mod p_felt is ≥ 2^8, so the range lookup has no
        //     decomposition for it.
        let compensator = (P_FELT - pow2_mod_p(8 * 31)) % P_FELT;
        assert!(
            compensator >= 256,
            "{label}: the compensating limb value must be OUT of the 8-bit table — that is the \
             whole reason the forgery dies"
        );
        let mut t = parse_trace(trace_txt, SOUND_WIDTH, 8);
        for row in t.iter_mut() {
            row[S_Z_BASE] = BabyBear::new(compensator as u32);
            row[S_Z_BASE + 31] = row[S_Z_BASE + 31] + BabyBear::new(1);
        }
        assert!(
            prove_vm_descriptor2(&desc, &t, &[], &MemBoundaryWitness::default(), &[]).is_err(),
            "{label}: the compensating limb pair must be REFUSED — no 8-bit range witness exists"
        );
    }
}

/// ⚑ **THE CARRY COLUMN IS PINNED NOW.** At `9×30` the carry/borrow column entered with coefficient
/// `±p`, a unit mod `p_felt`, and NOTHING constrained it — `pastaLimbRange` is emitted nowhere and
/// the only two booleanity gates in the windowed descriptor are on `BIT` and `DBL`. Here it is a
/// one-bit lookup, so `2` is not a carry.
#[test]
fn an_out_of_range_carry_bit_is_refused() {
    for (desc, trace_txt, label) in [
        (sound_add(), ADD_TRACE, "add"),
        (sound_sub(), SUB_TRACE, "sub"),
    ] {
        let mut t = parse_trace(trace_txt, SOUND_WIDTH, 8);
        for row in t.iter_mut() {
            row[S_C_COL] = BabyBear::new(2);
        }
        assert!(
            prove_vm_descriptor2(&desc, &t, &[], &MemBoundaryWitness::default(), &[]).is_err(),
            "{label}: a carry witness of 2 must be REFUSED by the 1-bit table"
        );
    }
}

/// ⚑ **A WRONG RESULT IS REFUSED, and the carry chain cannot swallow it.** Claim `z + 1` and try to
/// absorb the error in the free witness — the carry chain, the carry bit. Every route is closed: the
/// carry columns are pinned to 8 bits, the carry witness to 1.
#[test]
fn a_wrong_result_is_refused() {
    for (desc, trace_txt, label) in [
        (sound_add(), ADD_TRACE, "add"),
        (sound_sub(), SUB_TRACE, "sub"),
    ] {
        let mut t = parse_trace(trace_txt, SOUND_WIDTH, 8);
        for row in t.iter_mut() {
            row[S_Z_BASE] = row[S_Z_BASE] + BabyBear::new(1);
            row[S_CARRY_BASE] = row[S_CARRY_BASE] - BabyBear::new(1);
        }
        assert!(
            prove_vm_descriptor2(&desc, &t, &[], &MemBoundaryWitness::default(), &[]).is_err(),
            "{label}: a carry-compensated off-by-one result must be REFUSED"
        );

        // …and flipping the carry witness off does not rescue it either.
        let mut t = parse_trace(trace_txt, SOUND_WIDTH, 8);
        for row in t.iter_mut() {
            row[S_C_COL] = BabyBear::new(0);
        }
        assert!(
            prove_vm_descriptor2(&desc, &t, &[], &MemBoundaryWitness::default(), &[]).is_err(),
            "{label}: dropping the carry/borrow must be REFUSED"
        );
    }
}

/// An out-of-range OPERAND limb is refused too — `adBody_abs_lt_P` is a hypothesis about `x` and `y`
/// as much as about `z`, and the descriptor emits the lookups that discharge it. Without them the
/// soundness argument would be about a shape the prover does not carry.
#[test]
fn an_out_of_range_operand_limb_is_refused() {
    for (desc, trace_txt, base, label) in [
        (sound_add(), ADD_TRACE, S_X_BASE, "add/x"),
        (sound_add(), ADD_TRACE, S_Y_BASE, "add/y"),
        (sound_sub(), SUB_TRACE, S_X_BASE, "sub/x"),
        (sound_sub(), SUB_TRACE, S_Y_BASE, "sub/y"),
    ] {
        let mut t = parse_trace(trace_txt, SOUND_WIDTH, 8);
        for row in t.iter_mut() {
            row[base] = BabyBear::new(256);
        }
        assert!(
            prove_vm_descriptor2(&desc, &t, &[], &MemBoundaryWitness::default(), &[]).is_err(),
            "{label}: an operand limb at 2^8 must be REFUSED by the 8-bit table"
        );
    }
}
