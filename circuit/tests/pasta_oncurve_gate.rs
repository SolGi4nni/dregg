//! # The ON-CURVE GATE, and the absorbing-state forgery it kills.
//!
//! ## Substrate, said out loud
//!
//! **The AIRs are Lean-authored.** `dregg-pasta-rcb-sg-oncurve-<k>-of-4::v1` is
//! `Dregg2.Circuit.Emit.PastaMsmOnCurve.onCurveRowDesc 4 k 31 4 MinaWrapSrsG.SRS_G SCAL` — 98
//! constraints, of which the first 82 are `PastaMsmBound.boundRowDesc`'s verbatim
//! (`onCurveRowDesc_extends_bound` proves the prefix in the Lean kernel), the first 78 of THOSE are
//! `PastaMsmSliced`'s and the first 45 of those `PastaMsmWindowed`'s row template. Nothing in this
//! file or in `dregg_circuit::pasta_windowed_witness` authors a constraint, a builder gadget or an
//! `air_accepts` predicate. The Rust side parses the emitted descriptors, fills trace CELLS, and
//! runs the deployed prover and the deployed verifier.
//!
//! ## ⚑⚑ THE FORGERY THIS RUNG EXISTS TO KILL, and it was live in `main`
//!
//! Every binding rung up to `PastaMsmScalarBound` forces a fold of the RCB **FORMULA** over
//! projective triples. RCB Alg. 7 at `Q = O` returns `Y₁·(X₁, Y₁, Z₁)`, which at `Y₁ = 0` is
//! `(0,0,0)` — and `(0,0,0)` is **ABSORBING**: `rcb_add((0,0,0), Q) = (0,0,0)` for every `Q`.
//!
//! So take the initial accumulator — which nothing pins — to `(0,0,0)`. Every row's RCB add is then
//! honest arithmetic on `(0,0,0)`, every quotient and carry is real, the thread holds, the
//! `DBL` pins hold, and the exact-public lookup still carries **the real Mina SRS generators and
//! the real declared digits**, because `SRC` and `BIT` are untouched. The published partial is
//! `(0,0,0)`, which satisfies `PastaMsmAir`'s terminal `X ≡ 0 ∧ Z ≡ 0` predicate.
//!
//! `absorbing_state_before_and_after` runs both halves:
//!
//!   * the contents-bound descriptor (`pasta-rcb-sg-bound-<k>-of-4`, 82 constraints, 529 columns)
//!     **PROVES AND VERIFIES IT**;
//!   * the curve-gated descriptor (98 constraints, 799 columns) **REFUSES it**, with the deployed
//!     verifier's own verdict.
//!
//! That pair is the rung. Everything else here is control, coverage, and the two earlier tampers
//! re-fired on the SAME instance so all three are known live at once.
//!
//! ## Why the gate is `Y² Z = X³ + 5 Z³` AND `Y · YINV = 1`
//!
//! The projective curve equation is HOMOGENEOUS of degree 3, so `(0,0,0)` **satisfies it**. A curve
//! equation alone therefore cannot refuse the forgery. What refuses it is the non-degeneracy
//! witness: on Pallas — prime order, so no 2-torsion — `Y = 0` on a curve point is possible only
//! for `(0,0,0)`, so "`Y` is a unit" IS "this triple is a point". See `PastaMsmOnCurve` §5.2 for
//! the one hypothesis (cofactor 1) that is a fact about the curve rather than a gate.

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, TableSem, parse_vm_descriptor2, prove_vm_descriptors2_batch,
    verify_vm_descriptors2_batch,
};
use dregg_circuit::pasta_windowed_witness::{
    COL_ACCX, COL_ACCY, COL_ACCZ, COL_BIT, COL_DBL, COL_OC_ACC, COL_OC_SRC, COL_SRCX, COL_SRCY,
    COL_SRCZ, NUM_LIMBS, ONCURVE_WIDTH, Pt, RowSpec, TRACE_WIDTH, U256, build_trace, inv_mod_p,
    put_on_curve_block, put_on_curve_block_forged, read_point,
};
use dregg_circuit::refusal::{DEPLOYED_VERIFIER_REFUSAL_MARKERS, must_refuse};
use sha2::{Digest, Sha256};
use std::time::Instant;

// ---------------------------------------------------------------------------------------------
// The Lean-emitted artifacts, sha256-pinned so a silent re-emit cannot slide under a green test.
// ---------------------------------------------------------------------------------------------

/// The CURVE-GATED contents-bound descriptors: 82 bound constraints + 16 on-curve constraints,
/// same manifest, 799 columns. `scripts/regen-pasta-oncurve.sh` re-derives them.
const ONCURVE: [(&str, &str); 4] = [
    (
        include_str!("fixtures/pasta-sg-bound/pasta-rcb-sg-oncurve-0-of-4.json"),
        "e722b5002097ce42793999b58ac9368901e730ceefbf472b34721d24661c3feb",
    ),
    (
        include_str!("fixtures/pasta-sg-bound/pasta-rcb-sg-oncurve-1-of-4.json"),
        "57cf2c1251b9321118c25f9e043ce7fa48ed69722d3fb111168e42ed522901c9",
    ),
    (
        include_str!("fixtures/pasta-sg-bound/pasta-rcb-sg-oncurve-2-of-4.json"),
        "736e4d59652e56292f762433e1defc48a1de6ad81ef5f2863add86dbd41be1a5",
    ),
    (
        include_str!("fixtures/pasta-sg-bound/pasta-rcb-sg-oncurve-3-of-4.json"),
        "b78947997c6e5a5c5c3e0e326a587901c9f933c3bc2f966c50689010fa75f9ad",
    ),
];

/// The UNGATED contents-bound descriptors — `PastaMsmBound.boundRowDesc` at the same parameters,
/// the object this rung supersedes. Kept so the forgery can be shown to be ACCEPTED by it, which
/// is what makes the rung's value a measurement rather than a claim.
const BOUND: [(&str, &str); 4] = [
    (
        include_str!("fixtures/pasta-sg-bound/pasta-rcb-sg-bound-0-of-4.json"),
        "e01dd6f64611cfbe19663c35e9904a668570cdbeedabac911291b9b16ec5d18c",
    ),
    (
        include_str!("fixtures/pasta-sg-bound/pasta-rcb-sg-bound-1-of-4.json"),
        "6cb17500b17878327f50cacd36741bfe64b0845484127594a35bf5f946be192f",
    ),
    (
        include_str!("fixtures/pasta-sg-bound/pasta-rcb-sg-bound-2-of-4.json"),
        "f3712bca84e28bf3d48920081c57788b382007ae11806acada886a5f9e1dd728",
    ),
    (
        include_str!("fixtures/pasta-sg-bound/pasta-rcb-sg-bound-3-of-4.json"),
        "962705b50363b67557788a3dbee824c8d7c53f8f7015c029d7e3ef8ae10ee8ce",
    ),
];

/// `PastaMsmBound.WB` — the UNGATED width.
const BOUND_WIDTH: usize = 529;
/// `PastaMsmSliced.LO` / `HI`.
const COL_LO: usize = 525;
const COL_HI: usize = 526;
/// `PastaMsmBound.TIDX` / `GIDX`.
const COL_TIDX: usize = 527;
const COL_GIDX: usize = 528;
/// `PastaMsmSliced.PI_COUNT`.
const PI_COUNT: usize = 29;
/// Slices, generators per slice, bit planes, trace height.
const SLICES: usize = 4;
const W: usize = 31;
const PLANES: usize = 4;
const HEIGHT: usize = PLANES * (W + 1);

/// The degenerate triple the whole file is about (`PastaMsmOnCurve.origin_is_absorbing`).
const ORIGIN: Pt = Pt {
    x: U256::ZERO,
    y: U256::ZERO,
    z: U256::ZERO,
};

fn sha256_hex(bytes: &[u8]) -> String {
    let mut h = Sha256::new();
    h.update(bytes);
    h.finalize().iter().map(|b| format!("{b:02x}")).collect()
}

fn parse_set(set: &[(&str, &str); 4]) -> Vec<EffectVmDescriptor2> {
    set.iter()
        .map(|(json, _)| {
            parse_vm_descriptor2(json).expect("the deployed checker must parse the Lean descriptor")
        })
        .collect()
}

fn manifest_of(desc: &EffectVmDescriptor2) -> &Vec<Vec<u32>> {
    match &desc.tables[0].sem {
        TableSem::ExactPublicRows { rows } => rows,
        other => panic!("expected an exact-public generator table, got {other:?}"),
    }
}

fn point_of(row: &[u32]) -> Pt {
    let mut lx = [0u32; NUM_LIMBS];
    let mut ly = [0u32; NUM_LIMBS];
    let mut lz = [0u32; NUM_LIMBS];
    lx.copy_from_slice(&row[3..3 + NUM_LIMBS]);
    ly.copy_from_slice(&row[3 + NUM_LIMBS..3 + 2 * NUM_LIMBS]);
    lz.copy_from_slice(&row[3 + 2 * NUM_LIMBS..3 + 3 * NUM_LIMBS]);
    Pt {
        x: U256::from_limbs30(&lx),
        y: U256::from_limbs30(&ly),
        z: U256::from_limbs30(&lz),
    }
}

/// The schedule the manifest DECLARES: an all-zero manifest row is a doubling row, every other row
/// is a conditional add of the generator it names under the digit it names.
fn schedule_of(manifest: &[Vec<u32>]) -> Vec<RowSpec> {
    manifest
        .iter()
        .map(|row| {
            if row.iter().all(|&v| v == 0) {
                RowSpec::Double
            } else {
                RowSpec::CondAdd {
                    src: point_of(row),
                    bit: row[2] == 1,
                }
            }
        })
        .collect()
}

/// Widen a 525-column windowed trace to `width` and stamp the declaration/index columns. When
/// `width == ONCURVE_WIDTH`, also stamp both on-curve certificates from the row's own `ACC` and
/// `SRC` cells.
///
/// ⚑ The certificate written is always the BEST ONE THAT EXISTS for the point in the cells: honest
/// where the point has an inverse, and the `YINV = 0` fallback only where it has none. A forgery
/// test whose witness generator simply gave up would measure nothing.
fn widen(trace: Vec<Vec<BabyBear>>, lo: usize, hi: usize, width: usize) -> Vec<Vec<BabyBear>> {
    let mut gidx: usize = 0;
    trace
        .into_iter()
        .enumerate()
        .map(|(i, mut row)| {
            assert_eq!(row.len(), TRACE_WIDTH);
            let dbl = row[COL_DBL].as_u32() == 1;
            let acc = read_point(&row, COL_ACCX, COL_ACCY, COL_ACCZ);
            let src = read_point(&row, COL_SRCX, COL_SRCY, COL_SRCZ);
            row.resize(width, BabyBear::ZERO);
            row[COL_LO] = BabyBear::new(lo as u32);
            row[COL_HI] = BabyBear::new(hi as u32);
            row[COL_TIDX] = BabyBear::new(i as u32);
            row[COL_GIDX] = BabyBear::new(gidx as u32);
            if width == ONCURVE_WIDTH {
                for (base, pt) in [(COL_OC_ACC, acc), (COL_OC_SRC, src)] {
                    if pt.y == U256::ZERO {
                        put_on_curve_block_forged(&mut row, base, &pt);
                    } else {
                        put_on_curve_block(&mut row, base, &pt);
                    }
                }
            }
            gidx = if dbl { lo } else { gidx + 1 };
            row
        })
        .collect()
}

fn public_inputs_of(trace: &[Vec<BabyBear>], lo: usize, hi: usize) -> Vec<BabyBear> {
    let last = trace.last().expect("non-empty trace");
    let mut pis = Vec::with_capacity(PI_COUNT);
    pis.push(BabyBear::new(lo as u32));
    pis.push(BabyBear::new(hi as u32));
    for i in 0..27 {
        pis.push(last[COL_ACCX + i]);
    }
    pis
}

/// One slice's trace at a chosen width, starting from `acc0`.
fn slice_trace(
    manifest: &[Vec<u32>],
    k: usize,
    width: usize,
    acc0: &Pt,
    edit: Option<(usize, Pt)>,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let lo = W * k;
    let hi = lo + W;
    let mut sched = schedule_of(manifest);
    if let Some((row, src)) = edit {
        let bit = match sched[row] {
            RowSpec::CondAdd { bit, .. } => bit,
            RowSpec::Double => panic!("the edited row must be a conditional-add row"),
        };
        sched[row] = RowSpec::CondAdd { src, bit };
    }
    assert_eq!(sched.len(), HEIGHT);
    let trace = widen(build_trace(acc0, &sched), lo, hi, width);
    let pis = public_inputs_of(&trace, lo, hi);
    (trace, pis)
}

/// All four honest slices at a chosen width.
fn honest_cut(width: usize) -> (Vec<Vec<Vec<BabyBear>>>, Vec<Vec<BabyBear>>) {
    let descs = parse_set(&ONCURVE);
    let mut traces = Vec::new();
    let mut pis = Vec::new();
    for k in 0..SLICES {
        let (t, p) = slice_trace(manifest_of(&descs[k]), k, width, &Pt::INFINITY, None);
        traces.push(t);
        pis.push(p);
    }
    (traces, pis)
}

/// All four slices with the accumulator started at the ABSORBING triple `(0,0,0)`.
fn absorbing_cut(width: usize) -> (Vec<Vec<Vec<BabyBear>>>, Vec<Vec<BabyBear>>) {
    let descs = parse_set(&ONCURVE);
    let mut traces = Vec::new();
    let mut pis = Vec::new();
    for k in 0..SLICES {
        let (t, p) = slice_trace(manifest_of(&descs[k]), k, width, &ORIGIN, None);
        traces.push(t);
        pis.push(p);
    }
    (traces, pis)
}

fn prove_cut(
    descs: &[EffectVmDescriptor2],
    traces: &[Vec<Vec<BabyBear>>],
    pis: &[Vec<BabyBear>],
) -> Result<(), String> {
    let refs: Vec<&[Vec<BabyBear>]> = traces.iter().map(|t| t.as_slice()).collect();
    prove_vm_descriptors2_batch(descs, &refs, pis).map(|_| ())
}

// =============================================================================================
// (a) the artifacts are the ones this test was written against
// =============================================================================================

#[test]
fn lean_artifacts_are_pinned() {
    for (i, (json, want)) in ONCURVE.iter().enumerate() {
        assert_eq!(
            sha256_hex(json.as_bytes()),
            *want,
            "on-curve descriptor {i} was re-emitted; re-read the Lean and re-pin"
        );
    }
    let gated = parse_set(&ONCURVE);
    let ungated = parse_set(&BOUND);
    for (k, desc) in gated.iter().enumerate() {
        assert_eq!(
            desc.name,
            format!("dregg-pasta-rcb-sg-oncurve-{k}-of-4::v1")
        );
        assert_eq!(desc.trace_width, ONCURVE_WIDTH, "PastaMsmOnCurve.WOC");
        assert_eq!(desc.public_input_count, PI_COUNT, "the gate adds no PI");
        assert_eq!(desc.constraints.len(), 98, "82 bound + 16 on-curve");
        assert_eq!(desc.tables.len(), 1);
        // ⚑ THE PREFIX, checked on the EMITTED BYTES and not only in the Lean kernel: the first 82
        // constraints of the gated descriptor are the ungated one's, constraint for constraint. A
        // re-emit that quietly re-authored the row template would break here.
        assert_eq!(
            desc.constraints[..82],
            ungated[k].constraints[..],
            "slice {k}: the gated descriptor must EXTEND the bound one, not replace it"
        );
        // ⚑ …and the manifest is byte-identical, so the CONTENTS forcing is inherited unchanged.
        assert_eq!(
            manifest_of(desc),
            manifest_of(&ungated[k]),
            "slice {k}: the exact-public manifest must be untouched by the gate"
        );
    }
    // The price, read off the artifacts rather than off the docstring.
    println!(
        "[price] gate costs +{} constraints, +{} columns per row (82/{BOUND_WIDTH} -> 98/{})",
        98 - 82,
        ONCURVE_WIDTH - BOUND_WIDTH,
        ONCURVE_WIDTH
    );
}

/// ⚑ **THE MANIFEST'S GENERATORS ARE NOW GATED BY THE AIR, not only by a Rust assertion.** Every
/// declared generator is on the Pallas curve with `Y` invertible — which is exactly what the
/// emitted `onCurveGates` force of the `SRC` columns those manifest rows bind.
#[test]
fn every_declared_generator_satisfies_the_gate() {
    let mut checked = 0usize;
    for desc in parse_set(&ONCURVE).iter() {
        for row in manifest_of(desc) {
            if row.iter().all(|&v| v == 0) {
                continue; // a doubling row
            }
            let p = point_of(row);
            assert!(p.on_curve(), "a declared generator is off the Pallas curve");
            assert_ne!(p.y, U256::ZERO, "a declared generator has Y = 0");
            // the inverse the witness generator will write actually exists
            let (one, _) = dregg_circuit::pasta_windowed_witness::mul_mod_p(&p.y, &inv_mod_p(&p.y));
            assert_eq!(one, U256::ONE);
            checked += 1;
        }
    }
    assert_eq!(checked, SLICES * W * PLANES);
}

// =============================================================================================
// (b) ⚑ THE GATE — four curve-gated instances, ONE proof, DEPLOYED verifier
// =============================================================================================

/// ⚑ SATISFIABILITY AT BIRTH. A gadget demanding more than an honest proof supplies is TRUE
/// BECAUSE NOTHING SATISFIES IT. The honest cut must still prove AND verify.
#[test]
fn gated_cut_proves_and_verifies() {
    let descs = parse_set(&ONCURVE);
    let (traces, pis) = honest_cut(ONCURVE_WIDTH);
    let refs: Vec<&[Vec<BabyBear>]> = traces.iter().map(|t| t.as_slice()).collect();

    let t0 = Instant::now();
    let proof = prove_vm_descriptors2_batch(&descs, &refs, &pis).unwrap_or_else(|e| {
        panic!(
            "the LEAN-AUTHORED AIRs refused an HONEST witness: {e}\n\
             (that error is the AIR checking the witness — fix the WITNESS, never the AIR)"
        )
    });
    let prove_time = t0.elapsed();

    assert_eq!(
        proof.degree_bits.len(),
        SLICES * 2,
        "one main + ONE multiplicity-bearing table instance, per descriptor"
    );

    let t1 = Instant::now();
    verify_vm_descriptors2_batch(&descs, &proof, &pis).expect("the deployed verifier must accept");
    let verify_time = t1.elapsed();

    let bytes = postcard::to_allocvec(&proof).expect("serialize").len();
    println!(
        "[gated] {SLICES} slices x {HEIGHT} x {ONCURVE_WIDTH} cells | prove {prove_time:?} \
         | verify {verify_time:?} | proof {bytes} bytes"
    );
}

/// The honest fold really does pass through curve points at every row — the non-vacuity of the
/// gate's hypothesis, read off the trace the prover accepted rather than argued.
#[test]
fn every_honest_accumulator_is_a_curve_point() {
    let (traces, _) = honest_cut(ONCURVE_WIDTH);
    let mut non_affine = 0usize;
    for (k, t) in traces.iter().enumerate() {
        for (i, row) in t.iter().enumerate() {
            let acc = read_point(row, COL_ACCX, COL_ACCY, COL_ACCZ);
            let src = read_point(row, COL_SRCX, COL_SRCY, COL_SRCZ);
            assert!(acc.on_curve(), "slice {k} row {i}: ACC is off the curve");
            assert!(src.on_curve(), "slice {k} row {i}: SRC is off the curve");
            assert_ne!(acc.y, U256::ZERO, "slice {k} row {i}: ACC has Y = 0");
            assert_ne!(src.y, U256::ZERO, "slice {k} row {i}: SRC has Y = 0");
            if acc.z != U256::ONE && acc.z != U256::ZERO {
                non_affine += 1;
            }
        }
    }
    // ⚑ and most of them are NOT affine — RCB rescales — so a gate that only accepted `Z = 1`
    // would have refused the honest trace. `PastaMsmOnCurve` §3 exhibits the same fact in-kernel.
    assert!(
        non_affine > 3 * SLICES * HEIGHT / 4,
        "only {non_affine} non-affine accumulators; the gate is not being exercised on the shape \
         the fold actually produces"
    );
    println!(
        "[shape] {non_affine} of {} accumulators are non-affine",
        SLICES * HEIGHT
    );
}

// =============================================================================================
// (c) ⚑⚑ THE TAMPER THIS RUNG EXISTS FOR — before and after
// =============================================================================================

/// ⚑⚑ **THE ABSORBING-STATE FORGERY.** The initial accumulator is `(0,0,0)`, which nothing pins.
/// `rcb_add((0,0,0), Q) = (0,0,0)` for every `Q`, so the whole fold collapses while every RCB gate,
/// every carry, every quotient, every thread constraint and — crucially — the entire exact-public
/// lookup over the REAL Mina generators and their declared digits still hold exactly.
///
///   * the UNGATED contents-bound descriptor **PROVES AND VERIFIES IT**, and the partial it
///     publishes is `(0,0,0)`, which passes the terminal `X ≡ 0 ∧ Z ≡ 0` predicate. That is the
///     Mina claim, forged, with every binding rung green;
///   * the CURVE-GATED descriptor **REFUSES it**, with the deployed verifier's own verdict.
#[test]
fn absorbing_state_before_and_after() {
    // --- the forgery is what it claims to be ---------------------------------------------------
    let descs = parse_set(&ONCURVE);
    let (u_traces, u_pis) = absorbing_cut(BOUND_WIDTH);
    for (k, t) in u_traces.iter().enumerate() {
        for (i, row) in t.iter().enumerate() {
            let acc = read_point(row, COL_ACCX, COL_ACCY, COL_ACCZ);
            assert_eq!(
                acc, ORIGIN,
                "slice {k} row {i}: the forgery must be absorbed"
            );
        }
        // the manifest's own contents are UNTOUCHED: real generators, real digits.
        let manifest = manifest_of(&descs[k]);
        for (i, row) in t.iter().enumerate() {
            if manifest[i].iter().all(|&v| v == 0) {
                continue;
            }
            let src = read_point(row, COL_SRCX, COL_SRCY, COL_SRCZ);
            assert_eq!(src, point_of(&manifest[i]), "slice {k} row {i}: SRC moved");
            assert_eq!(
                row[COL_BIT].as_u32(),
                manifest[i][2],
                "slice {k} row {i}: BIT moved"
            );
        }
    }
    // and the published partial passes the terminal predicate `X ≡ 0 ∧ Z ≡ 0`.
    for pis in &u_pis {
        for i in 0..NUM_LIMBS {
            assert_eq!(pis[2 + i].as_u32(), 0, "published X limb is not zero");
            assert_eq!(
                pis[2 + 2 * NUM_LIMBS + i].as_u32(),
                0,
                "published Z limb is not zero"
            );
        }
    }

    // --- BEFORE: the UNGATED descriptor ACCEPTS it ---------------------------------------------
    let ungated = parse_set(&BOUND);
    let refs: Vec<&[Vec<BabyBear>]> = u_traces.iter().map(|t| t.as_slice()).collect();
    let proof = prove_vm_descriptors2_batch(&ungated, &refs, &u_pis).expect(
        "the contents-bound descriptor must ACCEPT the absorbing-state forgery — that acceptance \
         IS the hole this rung closes; if this line ever fails, the demonstration is gone",
    );
    verify_vm_descriptors2_batch(&ungated, &proof, &u_pis).expect(
        "…and the DEPLOYED VERIFIER must accept it too; a prover-only acceptance would be a \
         statement about `prove`, not about the constraint system",
    );
    println!(
        "[before] the contents-bound cut PROVED AND VERIFIED an all-(0,0,0) accumulator carrying \
         the real Mina generators, publishing a partial that passes the terminal predicate"
    );

    // --- AFTER: the CURVE-GATED descriptor REFUSES it -------------------------------------------
    let (g_traces, g_pis) = absorbing_cut(ONCURVE_WIDTH);
    let refusal = must_refuse("an all-(0,0,0) accumulator", || {
        prove_cut(&descs, &g_traces, &g_pis)
    });
    assert!(
        DEPLOYED_VERIFIER_REFUSAL_MARKERS
            .iter()
            .any(|m| refusal.contains(m)),
        "the absorbing state must be refused by the DEPLOYED verifier, got: {refusal}"
    );
    println!("[after]  the curve-gated cut REFUSED it: {refusal}");
}

/// ⚑ **A FORGED `Y = 0` MID-FOLD**, which is the state the `O`-skip collapses FROM rather than the
/// sink it collapses TO. One slice's accumulator is replaced by `(X, 0, Z)` at the start; the row
/// arithmetic is still honest, and the gate refuses it because `0` has no inverse.
#[test]
fn forged_zero_y_accumulator_is_refused() {
    let descs = parse_set(&ONCURVE);
    let mut traces = Vec::new();
    let mut pis = Vec::new();
    for k in 0..SLICES {
        let manifest = manifest_of(&descs[k]);
        let acc0 = if k == 1 {
            // a real generator's X and Z with Y forced to zero: on the curve nowhere, and the
            // exact input at which `P + O` returns `(0,0,0)`.
            let g = point_of(&manifest[1]);
            Pt {
                x: g.x,
                y: U256::ZERO,
                z: g.z,
            }
        } else {
            Pt::INFINITY
        };
        let (t, p) = slice_trace(manifest, k, ONCURVE_WIDTH, &acc0, None);
        traces.push(t);
        pis.push(p);
    }
    let refusal = must_refuse("slice 1 accumulator forged to Y = 0", || {
        prove_cut(&descs, &traces, &pis)
    });
    assert!(
        DEPLOYED_VERIFIER_REFUSAL_MARKERS
            .iter()
            .any(|m| refusal.contains(m)),
        "a Y = 0 accumulator must be refused by the DEPLOYED verifier, got: {refusal}"
    );
    println!("[tamper] REFUSED: a forged Y = 0 accumulator — {refusal}");
}

/// ⚑ **AN OFF-CURVE SOURCE POINT.** A point nobody could produce from the group law is planted in
/// one row's `SRC`, with a perfectly valid `Y` inverse so the refusal is the CURVE head's. It is
/// refused twice over — by the manifest lookup (its limbs are not the declared generator's) and now
/// by the curve equation — which is the point: the gate holds where the manifest does not, i.e. on
/// the descriptors that carry no manifest at all.
#[test]
fn off_curve_source_is_refused() {
    let descs = parse_set(&ONCURVE);
    let mut traces = Vec::new();
    let mut pis = Vec::new();
    for k in 0..SLICES {
        let manifest = manifest_of(&descs[k]);
        let edit = (k == 3).then(|| {
            let g = point_of(&manifest[5]);
            // bend one coordinate: `(x+1, y, 1)` is off `y² = x³ + 5` with overwhelming certainty.
            let off = Pt {
                x: g.x.adc(&U256::ONE).0,
                y: g.y,
                z: g.z,
            };
            assert!(!off.on_curve(), "the planted point must be off the curve");
            (5usize, off)
        });
        let (t, p) = slice_trace(manifest, k, ONCURVE_WIDTH, &Pt::INFINITY, edit);
        traces.push(t);
        pis.push(p);
    }
    let refusal = must_refuse("slice 3 row 5 source bent off the curve", || {
        prove_cut(&descs, &traces, &pis)
    });
    assert!(
        DEPLOYED_VERIFIER_REFUSAL_MARKERS
            .iter()
            .any(|m| refusal.contains(m)),
        "an off-curve source must be refused by the DEPLOYED verifier, got: {refusal}"
    );
    println!("[tamper] REFUSED: an off-curve source point — {refusal}");
}

// =============================================================================================
// (d) ⚑ ALL THREE TAMPERS LIVE ON ONE INSTANCE
// =============================================================================================

/// ⚑⚑ **THE GENERATOR TAMPER AND THE DIGIT TAMPER, RE-FIRED ON THE CURVE-GATED INSTANCE.**
/// `pasta_bound_sg_prove.rs` fires them on the ungated descriptor. A gate that quietly disarmed a
/// sibling's tooth would leave both files green, so they are re-run HERE, on the same 98-constraint
/// descriptors the absorbing-state tamper fires on — so all three are known live at once rather
/// than one at a time.
#[test]
fn generator_and_digit_tampers_still_fire_under_the_gate() {
    let descs = parse_set(&ONCURVE);

    // --- (1) A SUBSTITUTED GENERATOR: slice 2 row 6 rebuilt around the generator at the WRONG
    //         absolute index, the whole trace regenerated so every RCB add and carry holds.
    {
        let manifest = manifest_of(&descs[2]).clone();
        assert_eq!(manifest[6][1] as usize, W * 2 + 5 + 1);
        assert_eq!(manifest[7][1] as usize, W * 2 + 6 + 1);
        let substitute = point_of(&manifest[7]);
        assert!(
            substitute.on_curve(),
            "the substitute is a REAL Mina generator"
        );
        let mut traces = Vec::new();
        let mut pis = Vec::new();
        for k in 0..SLICES {
            let edit = (k == 2).then_some((6usize, substitute));
            let (t, p) = slice_trace(
                manifest_of(&descs[k]),
                k,
                ONCURVE_WIDTH,
                &Pt::INFINITY,
                edit,
            );
            traces.push(t);
            pis.push(p);
        }
        let refusal = must_refuse("slice 2 term 5 replaced by SRS generator 68", || {
            prove_cut(&descs, &traces, &pis)
        });
        assert!(
            DEPLOYED_VERIFIER_REFUSAL_MARKERS
                .iter()
                .any(|m| refusal.contains(m)),
            "the substituted generator must still be refused under the gate, got: {refusal}"
        );
        println!("[tamper] REFUSED (generator): {refusal}");
    }

    // --- (2) A FLIPPED DIGIT: the manifest's declared bit, bent in the trace.
    {
        let (mut traces, pis) = honest_cut(ONCURVE_WIDTH);
        let v = traces[2][5][COL_BIT].as_u32();
        traces[2][5][COL_BIT] = BabyBear::new(1 - v);
        let refusal = must_refuse("slice 2 row 5 digit flipped", || {
            prove_cut(&descs, &traces, &pis)
        });
        assert!(
            DEPLOYED_VERIFIER_REFUSAL_MARKERS
                .iter()
                .any(|m| refusal.contains(m)),
            "the flipped digit must still be refused under the gate, got: {refusal}"
        );
        println!("[tamper] REFUSED (digit): {refusal}");
    }
}

/// THE CONTROL. Without this the three red tampers above prove only that something is broken.
#[test]
fn honest_gated_cut_still_proves() {
    let descs = parse_set(&ONCURVE);
    let (traces, pis) = honest_cut(ONCURVE_WIDTH);
    prove_cut(&descs, &traces, &pis).expect("the honest curve-gated cut must prove");
}

/// An all-zeros cut must be refused — this path's own falsifier for the release-mode fail-open
/// class (`135e3382d`). Note it is NOT the absorbing-state forgery: an all-zeros TRACE fails the
/// lookup and the index threads too; the forgery above fails ONLY the curve gate.
#[test]
fn all_zeros_gated_cut_is_refused() {
    let descs = parse_set(&ONCURVE);
    let zeros: Vec<Vec<Vec<BabyBear>>> =
        vec![vec![vec![BabyBear::ZERO; ONCURVE_WIDTH]; HEIGHT]; SLICES];
    let pis = vec![vec![BabyBear::ZERO; PI_COUNT]; SLICES];
    let refusal = must_refuse("an all-zeros curve-gated cut", || {
        prove_cut(&descs, &zeros, &pis)
    });
    assert!(
        refusal.contains("self-verify failed"),
        "the producer must refuse an all-zeros cut in EVERY profile, got: {refusal}"
    );
}
