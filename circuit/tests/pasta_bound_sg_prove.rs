//! # The CONTENTS-BOUND four-way cut of `⟨s, srs.g⟩`, over Mina's REAL Wrap SRS generators.
//!
//! ## Substrate, said out loud
//!
//! **The AIRs are Lean-authored.** `dregg-pasta-rcb-sg-bound-<k>-of-4::v1` is
//! `Dregg2.Circuit.Emit.PastaMsmBound.boundRowDesc 4 k 31 4 MinaWrapSrsG.SRS_G SCAL` — 82
//! constraints, of which the first 78 are `PastaMsmSliced.slicedRowDesc`'s verbatim
//! (`boundRowDesc_extends_sliced` proves the prefix in the Lean kernel) and the first 45 of THOSE
//! are `PastaMsmWindowed`'s row template. Nothing in this file, in
//! `dregg_circuit::pasta_windowed_witness`, or in `prove_vm_descriptors2_batch` authors a
//! constraint, a builder gadget or an `air_accepts` predicate. The Rust side parses the emitted
//! descriptors, fills trace CELLS, and runs the deployed prover. When the prover refuses a trace,
//! the WITNESS is wrong.
//!
//! ## ⚑⚑ What this test exists to show, and it is one thing
//!
//! `PastaMsmSliced` §7.1: *the slice DECLARATION is bound; the slice CONTENTS are not.* Nothing in
//! the four-way cut's emitted constraints said a row's `SRC` columns carry `srs.g[lo + t]`, so a
//! prover could declare `[lo, hi)` and fill the rows with any points at all — and a full-size run
//! would have proved a SHAPE, not the Mina claim.
//!
//! `substituted_generator_before_and_after` is the demonstration, and it runs BOTH sides:
//!
//!   * ONE conditional-add row's source is replaced by a DIFFERENT REAL Mina SRS generator, and the
//!     rest of the trace is REBUILT around it, so the witness is internally perfect — every RCB
//!     add, every carry, every thread holds. It is a forgery of the MSM's *terms*, not of its
//!     arithmetic.
//!   * the contents-UNBOUND descriptor (`pasta-rcb-sg-slice-<k>-of-4-w31`, the same Lean `def` at
//!     the same width, without the generator table) **PROVES AND VERIFIES IT.**
//!   * the contents-BOUND descriptor **REFUSES it**, with the deployed verifier's own LogUp verdict.
//!
//! That pair is the rung. Everything else here is control and coverage.
//!
//! ## Parameters, and why they are these
//!
//! 4 slices × 31 generators = **124 real `srs.g` entries**, 4 bit planes, `4 · 32 = 128` trace rows
//! per instance.
//!
//! ⚑ **The 128 used to be the deployed ceiling; since 2026-07-29 it is only these artifacts'
//! parameters.** `descriptor_ir2.rs` capped an exact-public manifest at `MAX_EXACT_PUBLIC_ROWS =
//! 128` / `MAX_EXACT_PUBLIC_CELLS = 4096` because `instance_airs` spent one batch AIR instance per
//! manifest ROW — and since the balance is a PERMUTATION (manifest rows = trace rows) that was a
//! 128-row ceiling on any contents-bound trace. `Ir2Air::ExactPublicTable` realizes a whole
//! manifest as ONE multiplicity-bearing instance with the rows in a preprocessed matrix, so this
//! cut costs 8 instances rather than 516 and the caps are now `2^21` rows / `2^25` cells. Nothing
//! about the FORCING moved: the multiplicities are PINNED, so the balance is still exact multiset
//! equality, and `PastaMsmBound`'s theorems — including the counting ones that derive the `DBL`
//! pattern — hold verbatim over the same emitted descriptors. See `PastaMsmBound` §6/§7 and
//! `descriptor_ir2::ExactPublicManifest`.
//!
//! ## Why the artifacts are under `tests/fixtures/`, not `circuit/descriptors/by-name/`
//!
//! The bound descriptors carry the real SRS generators INSIDE the artifact, so emitting them needs
//! `Dregg2.Circuit.Emit.MinaWrapSrsG` — allowlisted OUT of the `Dregg2` root
//! (`scripts/lean-orphans-allow.txt`) because rooting it made `lake build Dregg2` impossible to
//! finish. Routing them through `EmitByName.lean` would drag that module into the descriptor-drift
//! gate's hot path on every run. `scripts/regen-pasta-bound.sh` re-derives them from the Lean; the
//! sha256 pins in `lean_artifacts_are_pinned` are what stops a silent re-emit.

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, TableSem, parse_vm_descriptor2, prove_vm_descriptors2_batch,
    verify_vm_descriptors2_batch,
};
use dregg_circuit::pasta_windowed_witness::{
    COL_ACCX, COL_BIT, COL_DBL, COL_SRCX, NUM_LIMBS, Pt, RowSpec, TRACE_WIDTH, U256, build_trace,
    proj_eq, rcb_add,
};
use dregg_circuit::refusal::{DEPLOYED_VERIFIER_REFUSAL_MARKERS, must_refuse};
use sha2::{Digest, Sha256};
use std::time::Instant;

// ---------------------------------------------------------------------------------------------
// The Lean-emitted artifacts, sha256-pinned so a silent re-emit cannot slide under a green test.
// ---------------------------------------------------------------------------------------------

/// The CONTENTS-BOUND descriptors: 78 sliced constraints + 3 index gates + 1 exact-public lookup,
/// carrying a 128×30 manifest of `(row key, absolute generator index, digit, 27 generator limbs)`
/// over the REAL `srs.g[31k .. 31k+31)`.
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

/// The CONTENTS-UNBOUND descriptors at the SAME width and slice count — `PastaMsmSliced`'s own
/// `slicedRowDesc 4 k 31`, the object this rung supersedes. Kept so the forgery can be shown to be
/// ACCEPTED by it, which is what makes the rung's value a measurement rather than a claim.
const UNBOUND: [(&str, &str); 4] = [
    (
        include_str!("fixtures/pasta-sg-bound/pasta-rcb-sg-slice-0-of-4-w31.json"),
        "317b98ebf8166943e6e95bf552e7d03af2bf3dd3486d5f091e432d6dea56c880",
    ),
    (
        include_str!("fixtures/pasta-sg-bound/pasta-rcb-sg-slice-1-of-4-w31.json"),
        "f3de26d6632e04203c05f21001e733308acf1b2192dc194ea55fa6d1a1667c05",
    ),
    (
        include_str!("fixtures/pasta-sg-bound/pasta-rcb-sg-slice-2-of-4-w31.json"),
        "79e3c2fb6090632b38f6a32e03353080831fbf5adc441ba5012d6bd26b84d645",
    ),
    (
        include_str!("fixtures/pasta-sg-bound/pasta-rcb-sg-slice-3-of-4-w31.json"),
        "2fa4904bd302df5f0e4b7e7e518ba9fa5334ab6870e730b603474153a45dfc69",
    ),
];

/// `PastaMsmBound.WB`.
const BOUND_WIDTH: usize = 529;
/// `PastaMsmSliced.WS` — the contents-unbound width.
const SLICED_WIDTH: usize = 527;
/// `PastaMsmSliced.LO` / `HI`.
const COL_LO: usize = 525;
const COL_HI: usize = 526;
/// `PastaMsmBound.TIDX` / `GIDX`.
const COL_TIDX: usize = 527;
const COL_GIDX: usize = 528;
/// `PastaMsmSliced.PI_COUNT`.
const PI_COUNT: usize = 29;
/// `PastaMsmBound.TUP`.
const TUP: usize = 30;
/// Slices, generators per slice, bit planes, trace height.
const SLICES: usize = 4;
const W: usize = 31;
const PLANES: usize = 4;
const HEIGHT: usize = PLANES * (W + 1);

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
// Reading the WITNESS out of the Lean-emitted manifest — cells only, no constraints.
// ---------------------------------------------------------------------------------------------

/// The declared manifest of a contents-bound descriptor.
fn manifest_of(desc: &EffectVmDescriptor2) -> &Vec<Vec<u32>> {
    match &desc.tables[0].sem {
        TableSem::ExactPublicRows { rows } => rows,
        other => panic!("expected an exact-public generator table, got {other:?}"),
    }
}

/// Rebuild a projective point from a manifest row's 27 limb columns (`3 · NUM_LIMBS`, LSB-first,
/// `X` then `Y` then `Z` — `PastaMsmBound.coordLimb`'s order, which is the row layout's order).
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

/// Widen a 525-column windowed trace to the contents-bound 529 and stamp the four declaration /
/// index columns. `GIDX` follows the EMITTED thread exactly:
/// `nxt GIDX = DBL·lo + (1−DBL)·(GIDX+1)`.
fn widen(trace: Vec<Vec<BabyBear>>, lo: usize, hi: usize, width: usize) -> Vec<Vec<BabyBear>> {
    let mut gidx: usize = 0;
    trace
        .into_iter()
        .enumerate()
        .map(|(i, mut row)| {
            assert_eq!(row.len(), TRACE_WIDTH);
            let dbl = row[COL_DBL].as_u32() == 1;
            row.resize(width, BabyBear::ZERO);
            row[COL_LO] = BabyBear::new(lo as u32);
            row[COL_HI] = BabyBear::new(hi as u32);
            if width > COL_TIDX {
                row[COL_TIDX] = BabyBear::new(i as u32);
                row[COL_GIDX] = BabyBear::new(gidx as u32);
            }
            gidx = if dbl { lo } else { gidx + 1 };
            row
        })
        .collect()
}

/// The 29 public inputs an instance declares: `lo`, `hi`, then the LAST row's 27 accumulator limbs.
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

/// One slice's trace + declared public inputs, at a chosen width.
fn slice_trace(
    manifest: &[Vec<u32>],
    k: usize,
    width: usize,
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
    let trace = widen(build_trace(&Pt::INFINITY, &sched), lo, hi, width);
    let pis = public_inputs_of(&trace, lo, hi);
    (trace, pis)
}

/// All four honest slices at a chosen width.
fn honest_cut(width: usize) -> (Vec<Vec<Vec<BabyBear>>>, Vec<Vec<BabyBear>>) {
    let bound = parse_set(&BOUND);
    let mut traces = Vec::new();
    let mut pis = Vec::new();
    for k in 0..SLICES {
        let (t, p) = slice_trace(manifest_of(&bound[k]), k, width, None);
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
    for (i, (json, want)) in BOUND.iter().chain(UNBOUND.iter()).enumerate() {
        assert_eq!(
            sha256_hex(json.as_bytes()),
            *want,
            "descriptor {i} was re-emitted; re-read the Lean and re-pin"
        );
    }
    for (k, desc) in parse_set(&BOUND).iter().enumerate() {
        assert_eq!(desc.name, format!("dregg-pasta-rcb-sg-bound-{k}-of-4::v1"));
        assert_eq!(desc.trace_width, BOUND_WIDTH);
        assert_eq!(desc.public_input_count, PI_COUNT);
        assert_eq!(desc.constraints.len(), 82, "78 sliced + 3 index + 1 lookup");
        assert_eq!(desc.tables.len(), 1, "exactly one generator table");
        let m = manifest_of(desc);
        assert_eq!(
            m.len(),
            HEIGHT,
            "manifest rows = trace rows (the balance is a permutation)"
        );
        assert!(m.iter().all(|r| r.len() == TUP));
    }
    // ⚑ the four slices declare DISTINCT wire ids, so their LogUp buses are distinct. Sharing one
    // id would pool their manifests and let slice j's generator satisfy slice k's query
    // (`PastaMsmBound.GEN_TID`'s doc; `descriptor_ir2::exact_public_bus_name` keys on the id alone).
    let ids: Vec<usize> = parse_set(&BOUND).iter().map(|d| d.tables[0].id).collect();
    for i in 0..SLICES {
        for j in (i + 1)..SLICES {
            assert_ne!(ids[i], ids[j], "slices {i} and {j} share a LogUp bus");
        }
    }
}

/// ⚑ **The manifest carries MINA's generators.** Decoded back from limbs, every declared point is
/// on the Pallas curve, is affine (`Z = 1`), and matches the corresponding entry of the checked-in
/// `MinaWrapSrsG.lean` — the extractor's own dump of the devnet Wrap SRS. That last check is the
/// one that makes "the real `srs.g`" a verified statement rather than a label: it is a differential
/// between the LEAN SOURCE and the EMITTED DESCRIPTOR, across the emitter.
#[test]
fn manifest_is_the_real_srs_g() {
    let src = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../metatheory/Dregg2/Circuit/Emit/MinaWrapSrsG.lean"
    ))
    .expect("MinaWrapSrsG.lean is checked in");
    // Every generator line is `  (<x dec>, <y dec>, 1),` — in SRS order, blocks concatenated.
    let srs: Vec<(String, String)> = src
        .lines()
        .filter_map(|l| {
            let t = l.trim();
            let t = t.strip_prefix('(')?;
            let t = t.trim_end_matches(',').trim_end_matches(']');
            let t = t.strip_suffix(')')?;
            let mut it = t.split(", ");
            let x = it.next()?.to_string();
            let y = it.next()?.to_string();
            if it.next()? != "1" {
                return None;
            }
            Some((x, y))
        })
        .collect();
    assert!(
        srs.len() >= SLICES * W,
        "parsed only {} generators from MinaWrapSrsG.lean",
        srs.len()
    );

    let mut checked = 0usize;
    for (k, desc) in parse_set(&BOUND).iter().enumerate() {
        for row in manifest_of(desc) {
            if row.iter().all(|&v| v == 0) {
                continue; // a doubling row
            }
            let abs = (row[1] - 1) as usize; // the ABSOLUTE generator index the manifest names
            assert!(
                abs >= W * k && abs < W * (k + 1),
                "slice {k} names absolute index {abs}, outside its own [{}, {})",
                W * k,
                W * (k + 1)
            );
            let p = point_of(row);
            assert!(p.on_curve(), "slice {k} index {abs} is not a Pallas point");
            assert_eq!(p.z, U256::ONE, "SRS generators are affine");
            assert_eq!(p.x.to_dec(), srs[abs].0, "slice {k} index {abs}: X");
            assert_eq!(p.y.to_dec(), srs[abs].1, "slice {k} index {abs}: Y");
            checked += 1;
        }
    }
    // 4 slices x 31 generators x 4 planes = 496 conditional-add rows over 124 distinct generators.
    assert_eq!(checked, SLICES * W * PLANES);
    println!(
        "[srs] {checked} manifest rows verified against MinaWrapSrsG.lean ({} distinct generators)",
        SLICES * W
    );
}

// =============================================================================================
// (b) ⚑ THE GATE — four contents-bound instances, ONE proof, DEPLOYED verifier
// =============================================================================================

#[test]
fn bound_cut_proves_and_verifies() {
    let descs = parse_set(&BOUND);
    let (traces, pis) = honest_cut(BOUND_WIDTH);

    // the four declared intervals tile [0, 124).
    for k in 0..SLICES {
        assert_eq!(pis[k][0].as_u32() as usize, W * k);
        assert_eq!(pis[k][1].as_u32() as usize, W * (k + 1));
    }

    let refs: Vec<&[Vec<BabyBear>]> = traces.iter().map(|t| t.as_slice()).collect();
    let t0 = Instant::now();
    let proof = prove_vm_descriptors2_batch(&descs, &refs, &pis).unwrap_or_else(|e| {
        panic!(
            "the LEAN-AUTHORED AIRs refused this witness: {e}\n\
             (that error is the AIR checking the witness — fix the WITNESS, never the AIR)"
        )
    });
    let prove_time = t0.elapsed();

    // ⚑ 4 main instances + 4 exact-public TABLE instances. This assertion read
    // `SLICES * (1 + HEIGHT)` = 516 until `Ir2Air::ExactPublicTable` landed (2026-07-29): the
    // manifest used to cost one batch instance per ROW, which is what made 128 rows the ceiling.
    assert_eq!(
        proof.degree_bits.len(),
        SLICES * 2,
        "one main + ONE multiplicity-bearing table instance, per descriptor"
    );

    let t1 = Instant::now();
    verify_vm_descriptors2_batch(&descs, &proof, &pis).expect("the deployed verifier must accept");
    let verify_time = t1.elapsed();

    let bytes = postcard::to_allocvec(&proof).expect("serialize").len();
    let distinct: usize = {
        let m = manifest_of(&descs[0]);
        let mut d = m.clone();
        d.sort_unstable();
        d.dedup();
        d.len()
    };
    println!(
        "[bound] {SLICES} slices x {HEIGHT} x {BOUND_WIDTH} main cells | manifest {HEIGHT} rows \
         ({distinct} distinct) in {} instances | prove {prove_time:?} | verify {verify_time:?} \
         | proof {bytes} bytes",
        proof.degree_bits.len()
    );
}

/// ⚑ **THE VERIFIER RECOMPUTES THE MANIFEST — it does not accept the prover's.**
///
/// The single-instance realization moved the manifest into a PREPROCESSED matrix, and a
/// preprocessed matrix is only verifier-known if the verifier derives and commits it ITSELF. If
/// `verify_vm_descriptors2_batch` ever took the prover's preprocessed commitment on trust, every
/// contents-binding theorem above would be about a table the prover chose — the whole rung would
/// be laundered through the commitment, silently, with all the other tests still green.
///
/// So: prove the HONEST cut, then verify it against a descriptor set in which one slice's manifest
/// names a different generator. The trace is untouched and internally perfect; only the declared
/// table moved. It must refuse.
#[test]
fn verifier_rebuilds_the_manifest_and_refuses_a_swapped_one() {
    let descs = parse_set(&BOUND);
    let (traces, pis) = honest_cut(BOUND_WIDTH);
    let refs: Vec<&[Vec<BabyBear>]> = traces.iter().map(|t| t.as_slice()).collect();
    let proof =
        prove_vm_descriptors2_batch(&descs, &refs, &pis).expect("the honest cut must prove");
    verify_vm_descriptors2_batch(&descs, &proof, &pis)
        .expect("control: the honest cut verifies against its OWN descriptors");

    // bend ONE limb of ONE manifest row of slice 2's declared table.
    let mut bent = parse_set(&BOUND);
    match &mut bent[2].tables[0].sem {
        TableSem::ExactPublicRows { rows } => rows[6][3] += 1,
        other => panic!("expected an exact-public generator table, got {other:?}"),
    }
    let refusal = verify_vm_descriptors2_batch(&bent, &proof, &pis).expect_err(
        "a verifier that rebuilt the manifest must refuse a proof over a different one",
    );
    println!("[after]  the verifier REFUSED a swapped manifest: {refusal}");
}

/// THE CONTROL. Without this a red tamper test proves only that something is broken.
#[test]
fn honest_bound_cut_still_proves() {
    let descs = parse_set(&BOUND);
    let (traces, pis) = honest_cut(BOUND_WIDTH);
    prove_cut(&descs, &traces, &pis).expect("the honest contents-bound cut must prove");
}

// =============================================================================================
// (c) ⚑⚑ THE TAMPER THIS RUNG EXISTS FOR — before and after
// =============================================================================================

/// ⚑⚑ **A SUBSTITUTED GENERATOR.** Slice 2's conditional-add row 6 (plane 0, term 5) is rebuilt
/// around a DIFFERENT REAL Mina SRS generator — the one at absolute index `62 + 6` instead of
/// `62 + 5` — and the whole trace is regenerated around it, so every RCB add, every carry bit and
/// every thread constraint holds EXACTLY. The forgery is in the MSM's TERMS, not its arithmetic.
///
///   * the contents-UNBOUND descriptor at the same width PROVES AND VERIFIES it — that is what
///     `PastaMsmSliced` §7.1 meant by "a SHAPE, not the Mina claim";
///   * the contents-BOUND descriptor REFUSES it, with the deployed verifier's LogUp verdict.
#[test]
fn substituted_generator_before_and_after() {
    let bound = parse_set(&BOUND);
    let unbound = parse_set(&UNBOUND);
    let manifest = manifest_of(&bound[2]).clone();

    // the substitute: a real Mina SRS generator, at the WRONG index within the same slice.
    let victim_row = 6usize; // plane 0, term 5
    let donor_row = 7usize; //  plane 0, term 6
    assert_eq!(manifest[victim_row][1] as usize, W * 2 + 5 + 1);
    assert_eq!(manifest[donor_row][1] as usize, W * 2 + 6 + 1);
    let substitute = point_of(&manifest[donor_row]);
    assert!(substitute.on_curve());

    // --- the UNBOUND descriptor ACCEPTS the forgery ------------------------------------------
    let mut u_traces = Vec::new();
    let mut u_pis = Vec::new();
    for k in 0..SLICES {
        let edit = (k == 2).then_some((victim_row, substitute));
        let (t, p) = slice_trace(manifest_of(&bound[k]), k, SLICED_WIDTH, edit);
        u_traces.push(t);
        u_pis.push(p);
    }
    prove_cut(&unbound, &u_traces, &u_pis).expect(
        "the contents-UNBOUND descriptor must ACCEPT the substituted generator — that acceptance \
         IS the hole this rung closes; if this line ever fails, the demonstration is gone",
    );
    println!("[before] the contents-UNBOUND cut ACCEPTED a substituted Mina generator");

    // --- the BOUND descriptor REFUSES it ------------------------------------------------------
    let mut b_traces = Vec::new();
    let mut b_pis = Vec::new();
    for k in 0..SLICES {
        let edit = (k == 2).then_some((victim_row, substitute));
        let (t, p) = slice_trace(manifest_of(&bound[k]), k, BOUND_WIDTH, edit);
        b_traces.push(t);
        b_pis.push(p);
    }
    let refusal = must_refuse("slice 2 term 5 replaced by SRS generator 68", || {
        prove_cut(&bound, &b_traces, &b_pis)
    });
    assert!(
        DEPLOYED_VERIFIER_REFUSAL_MARKERS
            .iter()
            .any(|m| refusal.contains(m)),
        "the substituted generator must be refused by the DEPLOYED verifier, got: {refusal}"
    );
    println!("[after]  the contents-BOUND cut REFUSED it: {refusal}");
}

/// The other cells the manifest binds, each bent on slice 2 and each refused.
#[test]
fn bound_cell_tampers_are_refused() {
    let descs = parse_set(&BOUND);
    let cases: [(&str, Box<dyn Fn(&mut [Vec<Vec<BabyBear>>])>); 5] = [
        (
            "slice 2 THREADED ROW INDEX — tidxThreadGate / the manifest key",
            Box::new(|t| bump(&mut t[2][5], COL_TIDX)),
        ),
        (
            "slice 2 ABSOLUTE GENERATOR INDEX — gidxThreadGate / the manifest's index field",
            Box::new(|t| bump(&mut t[2][5], COL_GIDX)),
        ),
        (
            "slice 2 DIGIT — the manifest's declared bit",
            Box::new(|t| {
                let v = t[2][5][COL_BIT].as_u32();
                t[2][5][COL_BIT] = BabyBear::new(1 - v);
            }),
        ),
        (
            "slice 2 SOURCE LIMB — one limb of one generator",
            Box::new(|t| bump(&mut t[2][5], COL_SRCX)),
        ),
        (
            "slice 2 DECLARED LOWER BOUND — sliceLoGate literal pin",
            Box::new(|t| bump(&mut t[2][5], COL_LO)),
        ),
    ];
    for (what, bend) in cases {
        let (mut traces, pis) = honest_cut(BOUND_WIDTH);
        bend(&mut traces);
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

/// ⚑ **DROPPING A TERM.** A conditional-add row is turned into a doubling row: its lookup tuple
/// collapses to the manifest's all-zero row, so the generator it should have consumed is never
/// consumed. The multiset then has one zero row too many and one real row too few. This is what
/// makes the `DBL` PATTERN forced rather than hypothesised (`PastaMsmWindowed` §6.1).
#[test]
fn dropping_a_term_is_refused() {
    let descs = parse_set(&BOUND);
    let bound = parse_set(&BOUND);
    let mut traces = Vec::new();
    let mut pis = Vec::new();
    for k in 0..SLICES {
        let manifest = manifest_of(&bound[k]);
        let mut sched = schedule_of(manifest);
        if k == 2 {
            sched[9] = RowSpec::Double; // was a conditional add
        }
        let lo = W * k;
        let trace = widen(build_trace(&Pt::INFINITY, &sched), lo, lo + W, BOUND_WIDTH);
        pis.push(public_inputs_of(&trace, lo, lo + W));
        traces.push(trace);
    }
    let refusal = must_refuse("slice 2 row 9 turned into a doubling row", || {
        prove_cut(&descs, &traces, &pis)
    });
    assert!(
        DEPLOYED_VERIFIER_REFUSAL_MARKERS
            .iter()
            .any(|m| refusal.contains(m)),
        "a dropped term must be refused by the deployed verifier, got: {refusal}"
    );
    println!("[tamper] REFUSED: a dropped term — {refusal}");
}

/// An all-zeros cut must be refused — the permanent falsifier for this path's own unconditional
/// self-verify (`135e3382d`: this descriptor shape was fail-OPEN in release for 35 days).
#[test]
fn all_zeros_bound_cut_is_refused() {
    let descs = parse_set(&BOUND);
    let zeros: Vec<Vec<Vec<BabyBear>>> =
        vec![vec![vec![BabyBear::ZERO; BOUND_WIDTH]; HEIGHT]; SLICES];
    let pis = vec![vec![BabyBear::ZERO; PI_COUNT]; SLICES];
    let refusal = must_refuse("an all-zeros contents-bound cut", || {
        prove_cut(&descs, &zeros, &pis)
    });
    assert!(
        refusal.contains("self-verify failed"),
        "the producer must refuse an all-zeros cut in EVERY profile, got: {refusal}"
    );
}

/// The four slice partials re-sum to the whole 124-term MSM, computed by a different route — the
/// content of `PastaMsmSliced.slices_compose`, on the values the proof publishes, over generators
/// the emitted manifests now FORCE.
#[test]
fn bound_partials_resum_to_the_whole_msm() {
    let bound = parse_set(&BOUND);
    let mut resum = Pt::INFINITY;
    let mut all: Vec<(Pt, bool)> = Vec::new();
    for k in 0..SLICES {
        let manifest = manifest_of(&bound[k]);
        let sched = schedule_of(manifest);
        let mut acc = Pt::INFINITY;
        for spec in &sched {
            let addend = match spec {
                RowSpec::Double => acc,
                RowSpec::CondAdd { src, bit } => {
                    if *bit {
                        all.push((*src, *bit));
                        *src
                    } else {
                        Pt::INFINITY
                    }
                }
            };
            acc = rcb_add(&acc, &addend);
        }
        resum = rcb_add(&resum, &acc);
    }
    assert!(
        !resum.is_infinity(),
        "non-vacuity: the MSM is not the identity"
    );
    assert!(
        resum.on_curve(),
        "non-vacuity: the MSM is a real Pallas point"
    );
    assert!(!all.is_empty(), "non-vacuity: some digits are set");
    // and it agrees with the whole-cut fold, computed without slicing.
    let mut whole = Pt::INFINITY;
    for plane in 0..PLANES {
        whole = rcb_add(&whole, &whole);
        for k in 0..SLICES {
            let manifest = manifest_of(&bound[k]);
            for t in 0..W {
                let row = &manifest[plane * (W + 1) + t + 1];
                if row[2] == 1 {
                    whole = rcb_add(&whole, &point_of(row));
                }
            }
        }
    }
    assert!(
        proj_eq(&resum, &whole),
        "the four contents-bound partials must re-sum to the whole MSM"
    );
}

fn bump(row: &mut [BabyBear], col: usize) {
    row[col] = BabyBear::new(row[col].as_u32() + 1);
}
