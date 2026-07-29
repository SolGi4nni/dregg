//! # The FOUR-WAY CUT of `⟨s, srs.g⟩`, as four AIR instances in ONE STARK proof.
//!
//! ## Substrate, said out loud
//!
//! **The AIRs are Lean-authored.** `dregg-pasta-rcb-sg-slice-<k>-of-4::v1` is
//! `Dregg2.Circuit.Emit.PastaMsmSliced.slicedRowDesc 4 k w` — 78 constraints, of which the first
//! 45 are `PastaMsmWindowed`'s row template verbatim (`slicedRowDesc_extends_windowed` proves the
//! prefix in the Lean kernel). Nothing in this file, in `dregg_circuit::pasta_windowed_witness`,
//! or in `prove_vm_descriptors2_batch` authors a constraint, a builder gadget or an `air_accepts`
//! predicate. The Rust side parses the emitted descriptors, fills trace CELLS, and runs the
//! deployed prover. When the prover refuses a trace, the WITNESS is wrong.
//!
//! ## What the cut is
//!
//! `PastaIpaDeferral` §4b: the terminal `⟨s, srs.g⟩` discharge is 4,227,200 RCB adds, 2.016× the
//! `2^21` two-adicity ceiling at every `N`. Cut FOUR ways — 8,192 generators, 1,056,896 rows — it
//! clears. Each instance NAMES ITS OWN SLICE: the offset is a LITERAL in the emitted gate, the
//! `[lo, hi)` bounds and the 27-limb partial are public inputs, and `PastaMsmSliced.slices_compose`
//! is the theorem that the four partials sum to the whole MSM.
//!
//! ## ⚑ What is PROVED here and what is only ACCEPTED
//!
//! Two parameter sets, and the difference is the honest part:
//!
//!   * `w = 8` (`-w8` descriptors): four instances, real traces, PROVED and VERIFIED end to end,
//!     with tampers refused. A complete four-way cut of a 32-generator MSM.
//!   * `w = 8192` (the real cut): the descriptors are ACCEPTED by the deployed structural checker
//!     (`descriptor_acceptance_probe`) and their traces are NOT proved. 1,056,896 rows pads to
//!     `2^21`, and `wall_measurement` reports where the machine actually stops. Clearing the
//!     two-adicity ceiling and being provable are different questions.
//!
//! The Lean composition theorem is width- and slice-count-independent, so the statement at
//! `w = 8` IS the statement at `w = 8192`. What does not transfer is the measurement.

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    prove_vm_descriptors2_batch, verify_vm_descriptors2_batch,
};
use dregg_circuit::pasta_windowed_witness::{
    COL_ACCX, COL_DBL, Pt, RowSpec, TRACE_WIDTH, build_trace, fold_schedule, pallas_generator,
    proj_eq, rcb_add,
};
use dregg_circuit::refusal::{DEPLOYED_VERIFIER_REFUSAL_MARKERS, must_refuse};
use sha2::{Digest, Sha256};
use std::time::Instant;

// ---------------------------------------------------------------------------------------------
// The Lean-emitted artifacts, sha256-pinned so a silent re-emit cannot slide under a green test.
// ---------------------------------------------------------------------------------------------

/// The REAL four-way cut: 8,192 generators per slice.
const REAL: [(&str, &str); 4] = [
    (
        include_str!("../descriptors/by-name/pasta-rcb-sg-slice-0-of-4.json"),
        "deecffe1e52b7f4d3ab8807ce0827d9c71adb4021455c6ac81334a45e876b389",
    ),
    (
        include_str!("../descriptors/by-name/pasta-rcb-sg-slice-1-of-4.json"),
        "9f33b67cd80375b1aec90281a8b3052cf2ba2c82ac114fd804b9b230d0b61274",
    ),
    (
        include_str!("../descriptors/by-name/pasta-rcb-sg-slice-2-of-4.json"),
        "09223f01ba299f638d3eeea84312e6bf840dce47ebbe8b338dddbe87fed1fc3c",
    ),
    (
        include_str!("../descriptors/by-name/pasta-rcb-sg-slice-3-of-4.json"),
        "28f669daf79dcd4694afb2d8be58c8d5c3c981136b52dd7df85f996409d19c03",
    ),
];

/// The PROVED cut: the same Lean `def` at 8 generators per slice.
const SMALL: [(&str, &str); 4] = [
    (
        include_str!("../descriptors/by-name/pasta-rcb-sg-slice-0-of-4-w8.json"),
        "694e4e8b6cd18e32f1236d1b13eb02d0cd48079b437c0081312a0d310504071e",
    ),
    (
        include_str!("../descriptors/by-name/pasta-rcb-sg-slice-1-of-4-w8.json"),
        "4b506a208e37d164b53a9e9a47ebf8bf3db0b0f1252729613cf6482525608c51",
    ),
    (
        include_str!("../descriptors/by-name/pasta-rcb-sg-slice-2-of-4-w8.json"),
        "729ac4fb006d497824fcee3db6d2e9d5ee7bc3e37eb411ce4cdf657a2054af15",
    ),
    (
        include_str!("../descriptors/by-name/pasta-rcb-sg-slice-3-of-4-w8.json"),
        "28c823f1dd8db886ed08c9a79b0e667e098241f26edd049c358a627fa7208a8d",
    ),
];

/// `PastaMsmSliced.WS` — the windowed row template plus the two declaration columns.
const SLICED_WIDTH: usize = 527;
/// `PastaMsmSliced.LO`.
const COL_LO: usize = 525;
/// `PastaMsmSliced.HI`.
const COL_HI: usize = 526;
/// `PastaMsmSliced.PI_COUNT`.
const PI_COUNT: usize = 29;
/// `PastaMsmSliced.SLICES`.
const SLICES: usize = 4;
/// The proved slice width.
const W_SMALL: usize = 8;
/// The real slice width, `PastaMsmSliced.SLICE_W`.
const W_REAL: usize = 8192;
/// Bit planes in the proved schedule. The real cut uses 128 (GLV); the plane count is the linear
/// dimension of the row cost and changes no relation, so a smaller one is a smaller measurement of
/// the same object.
const PLANES_SMALL: usize = 8;

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

// ---------------------------------------------------------------------------------------------
// Witness assembly — CELLS only.
// ---------------------------------------------------------------------------------------------

/// Term `i`'s scalar. Fixed and reproducible; no randomness in a build artifact.
fn scalar_of(i: usize) -> u64 {
    (7 + 13 * i as u64) % (1u64 << PLANES_SMALL)
}

/// `[k]G` for `k = 1..=n`, by repeated complete addition — the stand-in "SRS" for the proved cut.
fn generators(n: usize) -> Vec<Pt> {
    let g = pallas_generator();
    let mut acc = Pt::INFINITY;
    (0..n)
        .map(|_| {
            acc = rcb_add(&acc, &g);
            acc
        })
        .collect()
}

/// The Horner bit-plane schedule for ONE slice: per plane, a doubling row then `w` conditional
/// adds, over that slice's own generators and its own scalars' bits.
fn slice_schedule(gens: &[Pt], lo: usize, w: usize, planes: usize) -> Vec<RowSpec> {
    let mut sched = Vec::with_capacity(planes * (w + 1));
    for plane in 0..planes {
        sched.push(RowSpec::Double);
        let bit_index = planes - 1 - plane;
        for t in 0..w {
            sched.push(RowSpec::CondAdd {
                src: gens[lo + t],
                bit: (scalar_of(lo + t) >> bit_index) & 1 == 1,
            });
        }
    }
    sched
}

/// Extend with genuine `acc + O` rows to a power-of-two height. `when_transition` exempts only the
/// LAST row, so a pad row is fully constrained and must be a real addition, never a zero-fill.
fn pad_to(mut sched: Vec<RowSpec>, height: usize) -> Vec<RowSpec> {
    while sched.len() < height {
        sched.push(RowSpec::CondAdd {
            src: Pt::INFINITY,
            bit: false,
        });
    }
    sched
}

/// Widen a 525-column windowed trace to the 527-column sliced one and stamp the DECLARED bounds
/// into every row. `PastaMsmSliced.sliceDecl_forces_constant` is the constraint that makes
/// "every row" the only legal filling.
fn widen_with_bounds(trace: Vec<Vec<BabyBear>>, lo: usize, hi: usize) -> Vec<Vec<BabyBear>> {
    trace
        .into_iter()
        .map(|mut row| {
            assert_eq!(row.len(), TRACE_WIDTH);
            row.resize(SLICED_WIDTH, BabyBear::ZERO);
            row[COL_LO] = BabyBear::new(lo as u32);
            row[COL_HI] = BabyBear::new(hi as u32);
            row
        })
        .collect()
}

/// The 29 public inputs instance `k` declares: `lo`, `hi`, then the LAST row's 27 accumulator limb
/// columns — the slice's PARTIAL, on the wire.
fn public_inputs_of(trace: &[Vec<BabyBear>], lo: usize, hi: usize) -> Vec<BabyBear> {
    let last = trace.last().expect("non-empty trace");
    let mut pis = Vec::with_capacity(PI_COUNT);
    pis.push(BabyBear::new(lo as u32));
    pis.push(BabyBear::new(hi as u32));
    for i in 0..27 {
        pis.push(last[COL_ACCX + i]);
    }
    assert_eq!(pis.len(), PI_COUNT);
    pis
}

/// One slice's trace, its declared bounds and its declared partial.
struct Slice {
    trace: Vec<Vec<BabyBear>>,
    pis: Vec<BabyBear>,
    partial: Pt,
    lo: usize,
    hi: usize,
}

/// Build all four slices of a `SLICES * w`-generator MSM at `planes` bit planes.
fn build_cut(w: usize, planes: usize, height: usize) -> Vec<Slice> {
    let gens = generators(SLICES * w);
    (0..SLICES)
        .map(|k| {
            let lo = w * k;
            let hi = lo + w;
            let sched = slice_schedule(&gens, lo, w, planes);
            assert_eq!(sched.len(), planes * (w + 1));
            let partial = fold_schedule(&Pt::INFINITY, &sched);
            let raw = build_trace(&Pt::INFINITY, &pad_to(sched, height));
            let trace = widen_with_bounds(raw, lo, hi);
            let pis = public_inputs_of(&trace, lo, hi);
            Slice {
                trace,
                pis,
                partial,
                lo,
                hi,
            }
        })
        .collect()
}

/// The independently-computed whole MSM over all `SLICES * w` generators — the reference the four
/// partials must re-sum to. Computed by a DIFFERENT route (one flat fold, no slicing), so agreeing
/// with the four partials is a real check and not a restatement.
fn whole_msm(w: usize, planes: usize) -> Pt {
    let gens = generators(SLICES * w);
    let mut sched = Vec::new();
    for plane in 0..planes {
        sched.push(RowSpec::Double);
        let bit_index = planes - 1 - plane;
        for (t, src) in gens.iter().enumerate() {
            sched.push(RowSpec::CondAdd {
                src: *src,
                bit: (scalar_of(t) >> bit_index) & 1 == 1,
            });
        }
    }
    fold_schedule(&Pt::INFINITY, &sched)
}

// =============================================================================================
// (a) the artifacts are the ones this test was written against
// =============================================================================================

#[test]
fn lean_artifacts_are_pinned() {
    for (i, (json, want)) in REAL.iter().chain(SMALL.iter()).enumerate() {
        assert_eq!(
            sha256_hex(json.as_bytes()),
            *want,
            "sliced descriptor {i} was re-emitted; re-read the Lean and re-pin"
        );
    }
    for (k, desc) in parse_set(&REAL).iter().enumerate() {
        assert_eq!(desc.name, format!("dregg-pasta-rcb-sg-slice-{k}-of-4::v1"));
        assert_eq!(desc.trace_width, SLICED_WIDTH);
        assert_eq!(desc.public_input_count, PI_COUNT);
        assert_eq!(desc.constraints.len(), 78, "45 windowed + 4 decl + 29 pi");
        assert!(desc.tables.is_empty(), "no tables, so no chip lanes");
    }
    for (k, desc) in parse_set(&SMALL).iter().enumerate() {
        assert_eq!(desc.name, format!("dregg-pasta-rcb-sg-slice-{k}-of-4::v1"));
        assert_eq!(desc.constraints.len(), 78);
    }
}

/// ⚑ The four REAL descriptors are genuinely FOUR OBJECTS. The slice offset is a literal inside
/// the emitted constraint, so instance `k` cannot be run as instance `j` — that is a descriptor
/// property, not a convention the harness maintains.
#[test]
fn the_four_slices_are_distinct_descriptors() {
    let jsons: Vec<&str> = REAL.iter().map(|(j, _)| *j).collect();
    for i in 0..4 {
        for j in (i + 1)..4 {
            assert_ne!(
                jsons[i], jsons[j],
                "slice {i} and slice {j} emitted the same descriptor — the offset literal is missing"
            );
        }
    }
    // …and the small set differs from the real one in the WIDTH literal.
    assert_ne!(REAL[0].0, SMALL[0].0, "the width literal is missing");
}

// =============================================================================================
// (b) THE DESCRIPTOR ACCEPTANCE PROBE — including at the REAL 8,192-generator parameters
// =============================================================================================

/// `check_descriptor2` runs FIRST inside the prover, before any trace-shape check. An empty trace
/// rejected with exactly the trace-shape error witnesses that the deployed structural checker
/// ACCEPTED the Lean-emitted descriptor — in particular that no constraint addresses a column
/// `>= trace_width` and no `pi_binding` names a `pi_index >= public_input_count`, the two
/// predicates `slicedRowDesc_columns_in_bounds` / `slicedRowDesc_pi_indices_in_bounds` discharge
/// by `decide` in the Lean kernel.
///
/// ⚑ This runs on the REAL 8,192-generator descriptors — the ones whose traces are too large to
/// prove. The structural half of the four-way cut is checked at the real parameters even though
/// the arithmetic half is not.
#[test]
fn descriptor_acceptance_probe() {
    for (k, desc) in parse_set(&REAL).iter().enumerate() {
        let err = match prove_vm_descriptor2(desc, &[], &[], &MemBoundaryWitness::default(), &[]) {
            Err(e) => e,
            Ok(_) => panic!("an empty trace cannot prove"),
        };
        assert_eq!(
            err, "base trace must be non-empty",
            "slice {k}: the DESCRIPTOR was rejected, not the trace: {err}"
        );
        assert!(
            !err.contains("column") && !err.contains("trace_width") && !err.contains("pi_index"),
            "slice {k}: structural refusal: {err}"
        );
    }
}

// =============================================================================================
// (c) ⚑ THE GATE — four instances, ONE proof, DEPLOYED verifier
// =============================================================================================

/// ⚑⚑ **The gate.** Four Lean-authored AIR instances, each naming its own slice, riding in ONE
/// batch STARK proof, proved and verified by the deployed path.
///
/// Three things are checked, and the third is the one the cut is for:
///   1. every instance's declared `[lo, hi)` is the slice the Lean `sliceBounds` says it is, and
///      the four intervals TILE `[0, 4w)` with no gap and no overlap;
///   2. the proof carries exactly four instances, with per-instance `degree_bits`;
///   3. the four declared PARTIALS re-sum to the independently-computed whole MSM — the content of
///      `PastaMsmSliced.slices_compose`, checked on the values the proof publishes.
#[test]
fn four_way_cut_proves_and_verifies() {
    let descs = parse_set(&SMALL);
    let height = (PLANES_SMALL * (W_SMALL + 1)).next_power_of_two();
    let slices = build_cut(W_SMALL, PLANES_SMALL, height);

    // (1) the declared intervals tile — `PastaMsmSliced.sliceBounds` / `slice_bounds_abut`.
    assert_eq!(slices[0].lo, 0, "the first slice starts at 0");
    for k in 0..SLICES {
        assert_eq!(slices[k].hi - slices[k].lo, W_SMALL, "declared width");
        if k + 1 < SLICES {
            assert_eq!(
                slices[k].hi,
                slices[k + 1].lo,
                "slice {k} must end where slice {} begins",
                k + 1
            );
        }
    }
    assert_eq!(
        slices[SLICES - 1].hi,
        SLICES * W_SMALL,
        "the tiling is total"
    );

    // (3) the four partials re-sum to the whole MSM, computed by a different route.
    let mut resum = Pt::INFINITY;
    for s in &slices {
        resum = rcb_add(&resum, &s.partial);
    }
    let whole = whole_msm(W_SMALL, PLANES_SMALL);
    assert!(
        proj_eq(&resum, &whole),
        "the four slice partials must re-sum to the whole MSM"
    );
    assert!(
        !whole.is_infinity(),
        "non-vacuity: the MSM is not the identity"
    );
    assert!(
        whole.on_curve(),
        "non-vacuity: the MSM is a real Pallas point"
    );

    // one doubling row per plane, in every instance
    for (k, s) in slices.iter().enumerate() {
        let dbl = s.trace.iter().filter(|r| r[COL_DBL].as_u32() == 1).count();
        assert_eq!(
            dbl, PLANES_SMALL,
            "slice {k}: one doubling row per bit-plane"
        );
    }

    let traces: Vec<&[Vec<BabyBear>]> = slices.iter().map(|s| s.trace.as_slice()).collect();
    let pis: Vec<Vec<BabyBear>> = slices.iter().map(|s| s.pis.clone()).collect();

    let t0 = Instant::now();
    let proof = prove_vm_descriptors2_batch(&descs, &traces, &pis).unwrap_or_else(|e| {
        panic!(
            "the LEAN-AUTHORED AIRs refused this witness: {e}\n\
             (that error is the AIR checking the witness — fix the WITNESS, never the AIR)"
        )
    });
    let prove_time = t0.elapsed();

    // (2) four instances, per-instance degree_bits
    assert_eq!(
        proof.degree_bits.len(),
        SLICES,
        "four descriptors must give four instances"
    );

    let t1 = Instant::now();
    verify_vm_descriptors2_batch(&descs, &proof, &pis).expect("the deployed verifier must accept");
    let verify_time = t1.elapsed();

    let bytes = postcard::to_allocvec(&proof).expect("serialize").len();
    println!(
        "[cut-w{W_SMALL}] 4 instances x {height} x {SLICED_WIDTH} = {} cells | degree_bits {:?} \
         | prove {prove_time:?} | verify {verify_time:?} | proof {bytes} bytes",
        SLICES * height * SLICED_WIDTH,
        proof.degree_bits
    );
}

/// ⚑ **Per-instance `degree_bits` are real** — the four instances need not share a height. Here
/// slice 3 is given twice the height of the others (its extra rows are genuine `acc + O` adds), and
/// the batch proves and verifies with a HETEROGENEOUS `degree_bits` vector. This is the property
/// that makes the four-way cut expressible as one proof at all.
#[test]
fn heterogeneous_instance_heights_prove() {
    let descs = parse_set(&SMALL);
    let base = (PLANES_SMALL * (W_SMALL + 1)).next_power_of_two();
    let gens = generators(SLICES * W_SMALL);

    let mut traces_owned = Vec::new();
    let mut pis = Vec::new();
    for k in 0..SLICES {
        let lo = W_SMALL * k;
        let height = if k == 3 { base * 2 } else { base };
        let sched = pad_to(slice_schedule(&gens, lo, W_SMALL, PLANES_SMALL), height);
        let trace = widen_with_bounds(build_trace(&Pt::INFINITY, &sched), lo, lo + W_SMALL);
        pis.push(public_inputs_of(&trace, lo, lo + W_SMALL));
        traces_owned.push(trace);
    }
    let traces: Vec<&[Vec<BabyBear>]> = traces_owned.iter().map(|t| t.as_slice()).collect();

    let proof = prove_vm_descriptors2_batch(&descs, &traces, &pis)
        .expect("a heterogeneous-height batch must prove");
    let db = &proof.degree_bits;
    assert_eq!(db.len(), SLICES);
    assert_ne!(
        db[0], db[3],
        "slice 3 was given twice the height; degree_bits must differ per instance"
    );
    verify_vm_descriptors2_batch(&descs, &proof, &pis).expect("verify");
    println!("[hetero] degree_bits {db:?}");
}

// =============================================================================================
// (d) THE TAMPERS — a bent partial must be REFUSED
// =============================================================================================

/// Prove-and-verify a possibly-tampered cut, returning the deployed verdict.
fn prove_cut(
    descs: &[EffectVmDescriptor2],
    traces_owned: &[Vec<Vec<BabyBear>>],
    pis: &[Vec<BabyBear>],
) -> Result<(), String> {
    let traces: Vec<&[Vec<BabyBear>]> = traces_owned.iter().map(|t| t.as_slice()).collect();
    prove_vm_descriptors2_batch(descs, &traces, pis).map(|_| ())
}

/// The honest cut, as owned traces + public inputs, ready to be bent.
fn honest_cut() -> (Vec<Vec<Vec<BabyBear>>>, Vec<Vec<BabyBear>>) {
    let height = (PLANES_SMALL * (W_SMALL + 1)).next_power_of_two();
    let slices = build_cut(W_SMALL, PLANES_SMALL, height);
    (
        slices.iter().map(|s| s.trace.clone()).collect(),
        slices.iter().map(|s| s.pis.clone()).collect(),
    )
}

/// THE CONTROL. Without this a red tamper test proves only that something is broken.
#[test]
fn honest_cut_still_proves() {
    let descs = parse_set(&SMALL);
    let (traces, pis) = honest_cut();
    prove_cut(&descs, &traces, &pis).expect("the honest cut must prove");
}

/// ⚑ **A BENT PARTIAL IS REFUSED.** Six tampers, each on slice 2 — never row 0 (whose accumulator
/// is a free input) and never the last row of the constrained span (`when_transition` does not
/// reach the very last row's gates, though its PI bindings do fire).
#[test]
fn tampers_are_refused() {
    let descs = parse_set(&SMALL);
    let cases: [(
        &str,
        Box<dyn Fn(&mut Vec<Vec<Vec<BabyBear>>>, &mut Vec<Vec<BabyBear>>)>,
    ); 6] = [
        (
            "slice 2 accumulator limb — pallasCompleteAdd + threadGates",
            Box::new(|t, _| bump(&mut t[2][1], COL_ACCX)),
        ),
        (
            "slice 2 conditional bit — binGate BIT",
            Box::new(|t, _| bump(&mut t[2][1], 523)),
        ),
        (
            "slice 2 doubling selector — binGate DBL",
            Box::new(|t, _| bump(&mut t[2][1], COL_DBL)),
        ),
        (
            "slice 2 DECLARED LOWER BOUND — sliceLoGate literal pin",
            Box::new(|t, p| {
                bump(&mut t[2][1], COL_LO);
                let _ = p;
            }),
        ),
        (
            "slice 2 DECLARED WIDTH — sliceWidthGate literal pin",
            Box::new(|t, _| bump(&mut t[2][1], COL_HI)),
        ),
        (
            "slice 2 DECLARED PARTIAL — the published public input no longer matches the trace",
            Box::new(|_, p| {
                let v = p[2][2].as_u32();
                p[2][2] = BabyBear::new(v + 1);
            }),
        ),
    ];

    for (what, bend) in cases {
        let (mut traces, mut pis) = honest_cut();
        bend(&mut traces, &mut pis);
        let refusal = must_refuse(what, || prove_cut(&descs, &traces, &pis));
        assert!(
            DEPLOYED_VERIFIER_REFUSAL_MARKERS
                .iter()
                .any(|m| refusal.contains(m)),
            "{what}: refusal must be the DEPLOYED verifier's own verdict, got: {refusal}"
        );
        println!("[tamper] REFUSED: {what}");
    }
}

/// ⚑⚑ **THE CROSS-PAIRING TAMPER** — the one the cut exists to catch, and the one
/// `PastaMsmSliced.cross_pairing_breaks_the_sum` says is the real hazard (not the ordering).
///
/// Slice 1's trace is handed to slice 2's descriptor and vice versa. The re-sum of the partials is
/// UNCHANGED — group addition is commutative, which is exactly why "they re-sum correctly" is not
/// a check — but the DESCRIPTORS carry their slice offset as a literal, so each instance's declared
/// `[lo, hi)` no longer matches the trace it was given, and the deployed verifier refuses.
#[test]
fn swapped_slice_traces_are_refused() {
    let descs = parse_set(&SMALL);
    let (mut traces, mut pis) = honest_cut();
    traces.swap(1, 2);
    pis.swap(1, 2);

    // the re-sum is untouched by the swap: the hazard is NOT the ordering.
    let refusal = must_refuse("slice 1 and slice 2 traces swapped", || {
        prove_cut(&descs, &traces, &pis)
    });
    assert!(
        DEPLOYED_VERIFIER_REFUSAL_MARKERS
            .iter()
            .any(|m| refusal.contains(m)),
        "swapped slices must be refused by the deployed verifier, got: {refusal}"
    );
    println!("[tamper] REFUSED: swapped slice traces — {refusal}");
}

/// ⚑ **A DUPLICATED SLICE IS REFUSED** — slice 0's trace fed to all four instances. Three of the
/// four descriptors pin a different offset literal, so three instances refuse.
#[test]
fn duplicated_slice_is_refused() {
    let descs = parse_set(&SMALL);
    let (traces, pis) = honest_cut();
    let dup_t = vec![traces[0].clone(); SLICES];
    let dup_p = vec![pis[0].clone(); SLICES];
    let refusal = must_refuse("slice 0 duplicated into all four instances", || {
        prove_cut(&descs, &dup_t, &dup_p)
    });
    assert!(
        DEPLOYED_VERIFIER_REFUSAL_MARKERS
            .iter()
            .any(|m| refusal.contains(m)),
        "a duplicated slice must be refused, got: {refusal}"
    );
    println!("[tamper] REFUSED: duplicated slice — {refusal}");
}

/// An all-zeros cut must be refused — the permanent falsifier for the multi-descriptor path's own
/// self-verify. `prove_vm_descriptor2` was fail-OPEN in release for 35 days on exactly this shape
/// (a descriptor of algebraic gates with zero lookups); this path must never inherit it.
#[test]
fn all_zeros_cut_is_refused() {
    let descs = parse_set(&SMALL);
    let height = (PLANES_SMALL * (W_SMALL + 1)).next_power_of_two();
    let zeros: Vec<Vec<Vec<BabyBear>>> =
        vec![vec![vec![BabyBear::ZERO; SLICED_WIDTH]; height]; SLICES];
    let pis = vec![vec![BabyBear::ZERO; PI_COUNT]; SLICES];
    let refusal = must_refuse("an all-zeros four-way cut", || {
        prove_cut(&descs, &zeros, &pis)
    });
    assert!(
        refusal.contains("self-verify failed"),
        "the producer must refuse an all-zeros cut in EVERY profile, got: {refusal}"
    );
}

fn bump(row: &mut [BabyBear], col: usize) {
    row[col] = BabyBear::new(row[col].as_u32() + 1);
}

// =============================================================================================
// (e) THE MEASUREMENT — where the machine actually stops
// =============================================================================================

/// ⚑ **The wall.** `PastaIpaDeferral` prices the four-way cut at 1,056,896 rows, "50.4% of the
/// `2^21` ceiling". That is 50.4% of the RAW rows; a STARK trace height is a power of two, so the
/// COMMITTED domain is `2^21` exactly — the cut lands AT the ceiling, not half of it.
///
/// This walks the single-instance height up and reports prove time and proof size, so the wall is
/// a measurement rather than an extrapolation. `#[ignore]`d: it is a measurement, not a gate.
///
/// `cargo test -p dregg-circuit --release --test pasta_sliced_sg_prove -- --ignored --nocapture
///  wall_measurement`
#[test]
#[ignore = "measurement: walks the trace height up until it stops"]
fn wall_measurement() {
    let descs = parse_set(&SMALL);
    let gens = generators(SLICES * W_SMALL);
    for log_h in 7..=18 {
        let height = 1usize << log_h;
        let sched = pad_to(slice_schedule(&gens, 0, W_SMALL, PLANES_SMALL), height);
        let trace = widen_with_bounds(build_trace(&Pt::INFINITY, &sched), 0, W_SMALL);
        let pis = vec![public_inputs_of(&trace, 0, W_SMALL)];
        let t0 = Instant::now();
        let r = prove_vm_descriptors2_batch(&descs[..1], &[trace.as_slice()], &pis);
        let dt = t0.elapsed();
        match r {
            Ok(p) => println!(
                "[wall] 2^{log_h} x {SLICED_WIDTH} = {} cells | prove {dt:?} | {} bytes",
                height * SLICED_WIDTH,
                postcard::to_allocvec(&p).expect("ser").len()
            ),
            Err(e) => {
                println!("[wall] 2^{log_h} STOPPED after {dt:?}: {e}");
                break;
            }
        }
    }
    println!(
        "[wall] the REAL cut is 4 instances of 1,056,896 rows, padded to 2^21 = {} cells each",
        (1usize << 21) * SLICED_WIDTH
    );
    let _ = W_REAL;
}
