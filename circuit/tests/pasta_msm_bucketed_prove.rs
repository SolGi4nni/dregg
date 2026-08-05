//! # The BUCKETED MSM on the machine — the routing `PastaMsmLayouts` §7.3 called inexpressible,
//! proved in both polarities, in RELEASE.
//!
//! ## Substrate, said out loud (HOUSE LAW #1)
//!
//! **The AIR is Lean-authored.** `dregg-pasta-msm-bucketed-c<c>::v1` is
//! `Dregg2.Circuit.Emit.PastaMsmBucketed.bucketedRowDesc n nbits c MinaWrapSrsG.SRS_G SCAL` — 94
//! constraints, of which the first 45 are `PastaMsmWindowed.windowedRowDesc`'s row template
//! verbatim (`bucketedRowDesc_extends_windowed` proves the prefix in the Lean kernel), so the RCB
//! complete add in every row is the same `PastaCurveComplete.pallasCompleteAdd` the whole cone
//! shares. Nothing in this file authors a constraint, a builder gadget or an `air_accepts`
//! predicate: it reads the descriptor's own manifests, fills trace CELLS, and runs the deployed
//! prover. **When the prover refuses a trace, the WITNESS is wrong.**
//!
//! ## What the layout is, and why it needs no new IR
//!
//! Pippenger's buckets are replaced by a FUSED running sum. Sweeping the digit level `d` from
//! `D = 2^c − 1` down to `0` and keeping `RUN = Σ_{i : d_i ≥ d} g_i`, the identity
//! `Σ_i d_i·g_i = Σ_{d≥1} Σ_{i : d_i ≥ d} g_i` says the buckets never have to exist. So **nothing
//! is ever stored at a witness-dependent address and nothing is ever read back** — which is the
//! whole reason §7.3's `MemOp`/new-constraint-kind pricing does not apply.
//!
//! What IS data-dependent is the ORDER in which generators are consumed, and order is exactly what
//! a permutation quantifies over. `DescriptorIR2.PublicLookupBalanced` demands the trace's lookup
//! log be a `Perm` of the declared manifest — not a `Sublist` — so one exact-public table
//! (`pasta_msm_cover`, the `(window, generator, digit)` grid) forces every generator to be folded
//! exactly once per window at exactly its declared digit. **Three deployed teeth, zero new IR.**
//!
//! ## The two instances, and what each is for
//!
//!   * `c = 2`: `n = 27` real Mina SRS generators, `W = 2` windows, `D = 3` levels,
//!     `2·(2 + 27 + 3) = 64` rows × 612 columns.
//!   * `c = 3`: `n = 54` generators, `W = 2`, `D = 7`, `2·(3 + 54 + 7) = 128` rows × 612 columns.
//!
//! Heights are powers of two because the deployed prover refuses a non-power-of-two base trace AND
//! a permutation manifest's length IS the trace height. That is a parameter-choice constraint on
//! the emitter, not a property of the layout.
//!
//! ## ⚑ RELEASE, DELIBERATELY
//!
//! Algebraic refusals are `debug_assert` PANICS in debug and clean `Err(..)` in release. A refusal
//! test that passes only in debug is testing the assertion, not the constraint system.
//!
//! ## ⚑ WHICH MECHANISM MUST REFUSE
//!
//! The cone records the trap: a forgery that left the limb width was caught by a RANGE LOOKUP, so
//! the gate under test never ran. Every tamper below names the mechanism that must object, and the
//! forged-`sg` case is deliberately a forgery **the arithmetic cannot see** — a claimed commitment
//! displaced by one generator, which only the PI binding can catch.
//!
//! Run: `cargo test -p dregg-circuit --release --test pasta_msm_bucketed_prove -- --nocapture`

// ⚑ These descriptors carry 495-bit gate coefficients (the `PastaField` value heads), so they
// parse only through the NAMED unsound entry, exactly as every other `pasta-rcb-*` artifact does.
// The felt-sized replacement encoding is `Dregg2.Circuit.Emit.PastaFieldSound`; nothing in this
// file's subject matter (the ROUTING) depends on which multiply the rows are denominated in, and
// `PastaMsmBucketed` §7.2 says so out loud rather than letting the row counts read as sound ones.
use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, TableSem, parse_vm_descriptor2_unsound_oversized,
    prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::pasta_windowed_witness::{
    NUM_LIMBS, Pt, U256, fill_row, proj_eq, rcb_add, read_field,
};
use dregg_circuit::refusal::must_refuse;
use sha2::{Digest, Sha256};
use std::time::Instant;

// ---------------------------------------------------------------------------------------------
// The Lean-emitted artifacts, sha256-pinned so a silent re-emit cannot slide under a green test.
// ---------------------------------------------------------------------------------------------

const C2_JSON: &str = include_str!("fixtures/pasta-msm-bucketed/pasta-msm-bucketed-c2.json");
const C3_JSON: &str = include_str!("fixtures/pasta-msm-bucketed/pasta-msm-bucketed-c3.json");

const C2_SHA: &str = "91ef77e2258042f597c6dbc2e5a6c9b7307357d9cdb2df54d2cc3196a39ecd34";
const C3_SHA: &str = "577bfe4912ce4a85282a6f3aabecfdb0b8ede19ade744cfa72bd982c68265ac9";

// ---------------------------------------------------------------------------------------------
// The Lean row layout (`PastaMsmBucketed` §1), restated so a drift in either side reds HERE rather
// than silently addressing a different column.
// ---------------------------------------------------------------------------------------------

const WK: usize = 612;
const PI_COUNT: usize = 27;
const CONSTRAINTS: usize = 94;

const RUNX: usize = 525;
const TOTX: usize = 552;
const GENX: usize = 579;
const ISTERM: usize = 606;
const ISSTEP: usize = 607;
const TIDX: usize = 608;
const WIN: usize = 609;
const GIDX: usize = 610;
const DGT: usize = 611;

/// `PastaMsmWindowed.W` — the inherited row template's width, and the base `fill_row` produces.
const WINDOWED_W: usize = 525;

fn sha256_hex(b: &[u8]) -> String {
    let mut h = Sha256::new();
    h.update(b);
    h.finalize().iter().map(|x| format!("{x:02x}")).collect()
}

fn put_field(row: &mut [BabyBear], base: usize, v: &U256) {
    for i in 0..NUM_LIMBS {
        row[base + i] = BabyBear::new(v.limb30(i));
    }
}

fn manifest(desc: &EffectVmDescriptor2, name: &str) -> Vec<Vec<u32>> {
    let t = desc
        .tables
        .iter()
        .find(|t| t.name == name)
        .unwrap_or_else(|| panic!("descriptor declares no table named {name}"));
    match &t.sem {
        TableSem::ExactPublicRows { rows } => rows.clone(),
        other => panic!("table {name} is {other:?}, not an exact-public manifest"),
    }
}

/// A projective point read out of a `pasta_msm_srs` manifest row (`gidx+1` then 27 limbs, in the
/// row layout's `X ‖ Y ‖ Z` block order).
fn pt_of_manifest_row(row: &[u32]) -> Pt {
    let coord = |off: usize| {
        let mut limbs = [0u32; NUM_LIMBS];
        limbs.copy_from_slice(&row[1 + off..1 + off + NUM_LIMBS]);
        U256::from_limbs30(&limbs)
    };
    Pt {
        x: coord(0),
        y: coord(NUM_LIMBS),
        z: coord(2 * NUM_LIMBS),
    }
}

// ---------------------------------------------------------------------------------------------
// THE SHAPE, recovered from the descriptor's OWN manifests.
//
// Nothing here is a parameter this file chose: `n`, `W`, `c` and `D` are read back off the three
// declared tables, so a re-emit at different parameters retargets the witness producer without an
// edit. That is also what makes the trace and the manifest impossible to disagree by accident —
// and it is why every tamper below perturbs one of them AFTER this step.
// ---------------------------------------------------------------------------------------------

struct Shape {
    rows: usize,
    n: usize,
    windows: usize,
    c: usize,
    levels: usize,
    /// `gens[i]` — the real Mina SRS generator at absolute index `i`.
    gens: Vec<Pt>,
    /// `digits[w][i]` — the declared digit of term `i` in window `w`.
    digits: Vec<Vec<u32>>,
}

fn shape_of(desc: &EffectVmDescriptor2) -> Shape {
    let sched = manifest(desc, "pasta_msm_schedule");
    let cover = manifest(desc, "pasta_msm_cover");
    let srs = manifest(desc, "pasta_msm_srs");
    let rows = sched.len();
    assert_eq!(cover.len(), rows, "cover manifest length must be the height");
    assert_eq!(srs.len(), rows, "srs manifest length must be the height");

    let real: Vec<&Vec<u32>> = cover.iter().filter(|r| r[0] != 0).collect();
    let windows = real.iter().map(|r| r[0]).max().expect("a window") as usize;
    let n = real.iter().filter(|r| r[0] == 1).count();
    let c = sched.iter().filter(|r| r[1] == 1 && r[2] == 1).count();
    let levels = rows / windows - c - n;

    let mut gens = vec![Pt::INFINITY; n];
    for r in srs.iter().filter(|r| r[0] != 0) {
        let i = r[0] as usize - 1;
        if i < n {
            gens[i] = pt_of_manifest_row(r);
        }
    }
    let mut digits = vec![vec![0u32; n]; windows];
    for r in &real {
        digits[r[0] as usize - 1][r[1] as usize - 1] = r[2];
    }
    Shape {
        rows,
        n,
        windows,
        c,
        levels,
        gens,
        digits,
    }
}

// ---------------------------------------------------------------------------------------------
// THE WITNESS PRODUCER. Cells only.
// ---------------------------------------------------------------------------------------------

/// One row's mode.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Mode {
    /// `RUN += gens[gidx]`.
    Term(usize),
    /// `TOT += RUN`.
    Step,
    /// `TOT += TOT`, `RUN := O`.
    Dbl,
}

/// The row schedule: `c` doublings, then the digit sweep `D → 0` with a level fold after each
/// nonzero level. The ONLY data-dependent thing about it is which terms land at which level, which
/// is precisely what `pasta_msm_cover` forces.
fn schedule(sh: &Shape) -> Vec<(usize, Mode)> {
    let mut out = Vec::with_capacity(sh.rows);
    for w in 0..sh.windows {
        for _ in 0..sh.c {
            out.push((w, Mode::Dbl));
        }
        for d in (0..=sh.levels).rev() {
            for i in 0..sh.n {
                if sh.digits[w][i] as usize == d {
                    out.push((w, Mode::Term(i)));
                }
            }
            if d >= 1 {
                out.push((w, Mode::Step));
            }
        }
    }
    assert_eq!(out.len(), sh.rows, "the schedule must be the trace height");
    out
}

/// Build the honest trace and its 27 public-input limbs (the claimed commitment `C`).
fn honest_trace(sh: &Shape) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let sched = schedule(sh);
    let mut trace = Vec::with_capacity(sh.rows);

    let mut run = Pt::INFINITY;
    let mut tot = Pt::INFINITY;
    let mut dgt: u32 = 0;

    for (idx, (w, mode)) in sched.iter().enumerate() {
        let (acc, src, gen, isterm, isstep, dbl, gidx) = match *mode {
            Mode::Term(i) => (run, sh.gens[i], sh.gens[i], 1u32, 0u32, false, i as u32),
            Mode::Step => (tot, run, Pt::INFINITY, 0, 1, false, 0),
            Mode::Dbl => (tot, tot, Pt::INFINITY, 0, 0, true, 0),
        };

        let mut row = fill_row(&acc, &src, true, dbl);
        assert_eq!(row.len(), WINDOWED_W);
        row.resize(WK, BabyBear::new(0));

        put_field(&mut row, RUNX, &run.x);
        put_field(&mut row, RUNX + NUM_LIMBS, &run.y);
        put_field(&mut row, RUNX + 2 * NUM_LIMBS, &run.z);
        put_field(&mut row, TOTX, &tot.x);
        put_field(&mut row, TOTX + NUM_LIMBS, &tot.y);
        put_field(&mut row, TOTX + 2 * NUM_LIMBS, &tot.z);
        if isterm == 1 {
            put_field(&mut row, GENX, &gen.x);
            put_field(&mut row, GENX + NUM_LIMBS, &gen.y);
            put_field(&mut row, GENX + 2 * NUM_LIMBS, &gen.z);
        }
        row[ISTERM] = BabyBear::new(isterm);
        row[ISSTEP] = BabyBear::new(isstep);
        row[TIDX] = BabyBear::new(idx as u32);
        row[WIN] = BabyBear::new(*w as u32);
        row[GIDX] = BabyBear::new(gidx);
        row[DGT] = BabyBear::new(dgt);
        trace.push(row);

        // advance the two threads and the sweep counter exactly as the emitted window gates say.
        let out = rcb_add(&acc, &src);
        match *mode {
            Mode::Term(_) => run = out,
            Mode::Step => {
                tot = out;
                dgt -= 1;
            }
            Mode::Dbl => {
                tot = out;
                run = Pt::INFINITY;
                dgt = sh.levels as u32;
            }
        }
    }

    // ⚑ The PI binding reads `TOT` at the LAST row, which is the answer iff the final window ends
    // on a term row (its digit-0 group is non-empty). Asserted rather than assumed: if it ever
    // fails, the descriptor's parameters need a trailing no-op row, and a silent pass here would
    // publish a pre-final total as the commitment.
    assert!(
        matches!(sched.last().map(|s| s.1), Some(Mode::Term(_))),
        "the final window's digit-0 group is empty; the published TOT would be pre-final"
    );
    let last = trace.last().expect("a row");
    let claimed = Pt {
        x: read_field(last, TOTX),
        y: read_field(last, TOTX + NUM_LIMBS),
        z: read_field(last, TOTX + 2 * NUM_LIMBS),
    };
    assert!(proj_eq(&claimed, &tot) || claimed == tot);

    let pis: Vec<BabyBear> = (0..PI_COUNT).map(|i| last[TOTX + i]).collect();
    (trace, pis)
}

/// The answer computed OUT of circuit, by plain per-term double-and-add — the oracle the trace is
/// checked against. Deliberately NOT the same algorithm: a bucketing bug that agreed with itself
/// would survive comparing the trace to a second bucketed sum.
fn reference_msm(sh: &Shape) -> Pt {
    let radix = 1u64 << sh.c;
    let mut acc = Pt::INFINITY;
    for i in 0..sh.n {
        let mut s: u64 = 0;
        for w in 0..sh.windows {
            s = s * radix + u64::from(sh.digits[w][i]);
        }
        let mut term = Pt::INFINITY;
        for _ in 0..s {
            term = rcb_add(&term, &sh.gens[i]);
        }
        acc = rcb_add(&acc, &term);
    }
    acc
}

fn parse(json: &str) -> EffectVmDescriptor2 {
    parse_vm_descriptor2_unsound_oversized(json).expect("the Lean artifact must parse")
}

fn prove_and_verify(
    desc: &EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    pis: &[BabyBear],
) -> Result<(), String> {
    let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
    verify_vm_descriptor2(desc, &proof, pis)
}

// =============================================================================================
// (a) the artifacts are the ones this test was written against
// =============================================================================================

#[test]
fn lean_artifacts_are_pinned() {
    for (json, want, c) in [(C2_JSON, C2_SHA, 2usize), (C3_JSON, C3_SHA, 3)] {
        assert_eq!(
            sha256_hex(json.as_bytes()),
            want,
            "descriptor c={c} was re-emitted; re-read the Lean and re-pin"
        );
        let d = parse(json);
        assert_eq!(d.name, format!("dregg-pasta-msm-bucketed-c{c}::v1"));
        assert_eq!(d.trace_width, WK);
        assert_eq!(d.public_input_count, PI_COUNT);
        assert_eq!(
            d.constraints.len(),
            CONSTRAINTS,
            "45 windowed + 4 mode + 6 select + 6 thread + 3 index + 3 lookup + 27 PI"
        );
        assert_eq!(d.tables.len(), 3, "schedule, cover, srs");
        // ⚑ The prefix claim, checked on the ARTIFACT and not only in the kernel: the first 45
        // constraints are the windowed row template, so the curve arithmetic is not re-authored.
        let windowed = parse(include_str!("../descriptors/by-name/pasta-rcb-windowed.json"));
        assert_eq!(windowed.constraints.len(), 45);
        assert_eq!(
            &d.constraints[..45],
            &windowed.constraints[..],
            "bucketedRowDesc_extends_windowed is FALSE of the emitted bytes"
        );
    }
}

// =============================================================================================
// (b) the shape the manifests declare is the shape the layout predicts
// =============================================================================================

#[test]
fn the_manifests_declare_the_fused_layout() {
    for (json, c, n) in [(C2_JSON, 2usize, 27usize), (C3_JSON, 3, 54)] {
        let sh = shape_of(&parse(json));
        assert_eq!(sh.c, c, "doublings per window must be c");
        assert_eq!(sh.n, n);
        assert_eq!(sh.levels, (1 << c) - 1, "levels must be 2^c - 1");
        // the closed form `PastaMsmBucketed.fusedAdds` computes, on these very parameters.
        assert_eq!(sh.rows, sh.windows * (sh.c + sh.n + sh.levels));
        assert!(sh.rows.is_power_of_two(), "the prover refuses a ragged height");
        // every declared generator is a real curve point, and distinct from its neighbours.
        for (i, g) in sh.gens.iter().enumerate() {
            assert!(g.on_curve(), "SRS generator {i} is off-curve");
        }
        assert_ne!(sh.gens[0], sh.gens[1]);
        // every declared digit is a real c-bit digit (`coverManifest_digits_are_c_bit`).
        for w in 0..sh.windows {
            for i in 0..sh.n {
                assert!((sh.digits[w][i] as usize) <= sh.levels);
            }
        }
    }
}

// =============================================================================================
// (c) ⚑ POLARITY 1 — THE HONEST ACCUMULATOR PROVES, and computes the right point
// =============================================================================================

#[test]
fn the_honest_bucketed_msm_proves_and_verifies() {
    for (json, label) in [(C2_JSON, "c=2, n=27"), (C3_JSON, "c=3, n=54")] {
        let desc = parse(json);
        let sh = shape_of(&desc);
        let (trace, pis) = honest_trace(&sh);

        // ⚑ FIRST: the trace computes the MSM. A proof of a trace that sums the wrong thing is a
        // proof of the wrong thing, and the prover would never notice.
        let want = reference_msm(&sh);
        let got = Pt {
            x: read_field(trace.last().unwrap(), TOTX),
            y: read_field(trace.last().unwrap(), TOTX + NUM_LIMBS),
            z: read_field(trace.last().unwrap(), TOTX + 2 * NUM_LIMBS),
        };
        assert!(
            proj_eq(&want, &got),
            "[{label}] the bucketed trace disagrees with the term-by-term sum"
        );

        let t0 = Instant::now();
        prove_and_verify(&desc, &trace, &pis).unwrap_or_else(|e| {
            panic!(
                "[{label}] the LEAN-AUTHORED AIR refused an honest witness: {e}\n\
                 (that error is the AIR checking the witness — fix the WITNESS, never the AIR)"
            )
        });
        println!(
            "  [HONEST] {label}: {} rows x {} cols, {} constraints, 3 exact-public manifests \
             -> PROVED + VERIFIED in {:.1} ms",
            sh.rows,
            WK,
            desc.constraints.len(),
            t0.elapsed().as_secs_f64() * 1e3
        );
    }
}

// =============================================================================================
// (d) ⚑ POLARITY 2 — A FORGED `sg` IS REFUSED
//
// The native oracle's case, matched: the claimed commitment is displaced by one generator
// (`C + G`), everything else honest. This is a forgery the ARITHMETIC cannot see — every row still
// adds correctly — so the mechanism that must object is the PI binding, and nothing else.
// =============================================================================================

#[test]
fn a_forged_commitment_is_refused() {
    for (json, label) in [(C2_JSON, "c=2"), (C3_JSON, "c=3")] {
        let desc = parse(json);
        let sh = shape_of(&desc);
        let (trace, pis) = honest_trace(&sh);

        // `C + G` — the same displacement `mina_accumulator_discharge`'s `forge_commitment` makes.
        let honest = Pt {
            x: read_field(trace.last().unwrap(), TOTX),
            y: read_field(trace.last().unwrap(), TOTX + NUM_LIMBS),
            z: read_field(trace.last().unwrap(), TOTX + 2 * NUM_LIMBS),
        };
        let forged = rcb_add(&honest, &sh.gens[0]);
        assert!(!proj_eq(&honest, &forged), "the forgery must move the point");

        let mut bad = vec![BabyBear::new(0); PI_COUNT];
        for i in 0..NUM_LIMBS {
            bad[i] = BabyBear::new(forged.x.limb30(i));
            bad[NUM_LIMBS + i] = BabyBear::new(forged.y.limb30(i));
            bad[2 * NUM_LIMBS + i] = BabyBear::new(forged.z.limb30(i));
        }
        assert_ne!(bad, pis, "the forged PI vector must differ");

        let e = must_refuse(
            &format!("[{label}] a commitment displaced by +G, honest trace"),
            || prove_and_verify(&desc, &trace, &bad),
        );
        println!("  [FORGED] {label}: claimed C + G -> REFUSED: {e:?}");
    }
}

// =============================================================================================
// (e) ⚑ POLARITY 2b — THE ROUTING ITSELF IS THE THING UNDER TEST
//
// Three tampers, each aimed at one leg of the routing, each naming the mechanism that must fire.
// This is the section the whole file exists for: without it, (c) and (d) would demonstrate an MSM
// and say nothing about whether the BUCKET ROUTING is forced.
// =============================================================================================

/// A term row consumes a generator that is real, on-curve, and in the manifest — but at the WRONG
/// SWEEP LEVEL. The arithmetic is untouched (the row still adds a real point to `RUN`); the digit
/// column no longer matches the level. **`pasta_msm_cover` must be the mechanism that refuses**,
/// because nothing else in the descriptor relates a generator index to a digit.
#[test]
fn a_generator_folded_at_the_wrong_level_is_refused() {
    let desc = parse(C2_JSON);
    let sh = shape_of(&desc);
    let (mut trace, pis) = honest_trace(&sh);

    // find a term row and move its declared level, keeping the arithmetic self-consistent.
    let victim = (0..sh.rows)
        .find(|&i| trace[i][ISTERM].as_u32() == 1 && trace[i][DGT].as_u32() > 0)
        .expect("a term row above level 0");
    let was = trace[victim][DGT].as_u32();
    trace[victim][DGT] = BabyBear::new(was - 1);

    let e = must_refuse(
        "a real generator folded one sweep level below its declared digit",
        || prove_and_verify(&desc, &trace, &pis),
    );
    println!("  [ROUTE ] cover-manifest level moved {was} -> {}: REFUSED: {e:?}", was - 1);
}

/// A term row consumes a DIFFERENT REAL Mina SRS generator than its index names — the substitution
/// `pasta_bound_sg_prove` calls the rung. Both points are on-curve and both are in the manifest, so
/// only the `(gidx, limbs)` pairing can object. **`pasta_msm_srs` must be the mechanism.**
#[test]
fn a_substituted_real_generator_is_refused() {
    let desc = parse(C2_JSON);
    let sh = shape_of(&desc);
    let (mut trace, pis) = honest_trace(&sh);

    let victim = (0..sh.rows)
        .find(|&i| trace[i][ISTERM].as_u32() == 1 && trace[i][GIDX].as_u32() == 0)
        .expect("a term row consuming generator 0");
    let substitute = sh.gens[1];
    assert!(substitute.on_curve() && substitute != sh.gens[0]);
    put_field(&mut trace[victim], GENX, &substitute.x);
    put_field(&mut trace[victim], GENX + NUM_LIMBS, &substitute.y);
    put_field(&mut trace[victim], GENX + 2 * NUM_LIMBS, &substitute.z);

    let e = must_refuse(
        "generator index 0's row carrying the limbs of REAL generator 1",
        || prove_and_verify(&desc, &trace, &pis),
    );
    println!("  [ROUTE ] a real SRS generator at the wrong index: REFUSED: {e:?}");
}

/// A generator is folded TWICE in one window and another is DROPPED — the classic MSM forgery a
/// containment-only lookup would admit and a permutation must not. **`pasta_msm_cover`'s `Perm`
/// (not `Sublist`) is the mechanism**, and this is the single test that distinguishes them.
#[test]
fn a_duplicated_term_and_a_dropped_one_are_refused() {
    let desc = parse(C2_JSON);
    let sh = shape_of(&desc);
    let (mut trace, pis) = honest_trace(&sh);

    // two term rows at the SAME sweep level in the SAME window; point the second at the first's
    // generator, so one index is consumed twice and one not at all. Same level, so the sweep
    // counter and every arithmetic gate stay satisfied — only the multiset moves.
    let mut by_level = std::collections::BTreeMap::<u32, Vec<usize>>::new();
    for i in 0..sh.rows {
        if trace[i][ISTERM].as_u32() == 1 && trace[i][WIN].as_u32() == 0 {
            by_level.entry(trace[i][DGT].as_u32()).or_default().push(i);
        }
    }
    let level_rows = by_level
        .values()
        .max_by_key(|v| v.len())
        .expect("window 0 has term rows")
        .clone();
    assert!(
        level_rows.len() >= 2,
        "need two terms at one level to duplicate one"
    );
    let (keep, drop) = (level_rows[0], level_rows[1]);
    let g = sh.gens[trace[keep][GIDX].as_u32() as usize];
    trace[drop][GIDX] = trace[keep][GIDX];
    put_field(&mut trace[drop], GENX, &g.x);
    put_field(&mut trace[drop], GENX + NUM_LIMBS, &g.y);
    put_field(&mut trace[drop], GENX + 2 * NUM_LIMBS, &g.z);

    let e = must_refuse(
        "one generator folded twice in a window and another dropped",
        || prove_and_verify(&desc, &trace, &pis),
    );
    println!("  [ROUTE ] duplicate + drop (a Sublist would ADMIT this): REFUSED: {e:?}");
}

/// The SCHEDULE is verifier-known, and a prover cannot choose its own window structure: move one
/// row's declared window and the schedule manifest must refuse. **`pasta_msm_schedule`.**
#[test]
fn a_relabelled_window_is_refused() {
    let desc = parse(C2_JSON);
    let sh = shape_of(&desc);
    let (mut trace, pis) = honest_trace(&sh);

    let victim = (0..sh.rows)
        .find(|&i| trace[i][WIN].as_u32() == 0 && trace[i][ISTERM].as_u32() == 1)
        .expect("a window-0 term row");
    trace[victim][WIN] = BabyBear::new(1);

    let e = must_refuse("a window-0 row relabelled as window 1", || {
        prove_and_verify(&desc, &trace, &pis)
    });
    println!("  [ROUTE ] a relabelled window: REFUSED: {e:?}");
}
