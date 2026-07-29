//! # ⚑ HOW MANY OF MINA'S 32,768 WRAP-SRS GENERATORS CAN BE CONTENTS-BOUND — measured, not assumed.
//!
//! ## Substrate, said out loud
//!
//! **The AIRs are Lean-authored.** Every descriptor this file reads is
//! `Dregg2.Circuit.Emit.PastaMsmBound.boundRowDesc 4 k w 4 MinaWrapSrsG.SRS_G (SCAL 4 w 4)`,
//! rendered by `metatheory/EmitPastaBoundScaled.lean`, which lifts `w`/`planes` out of
//! `EmitPastaBound.lean`'s literals and authors nothing. Nothing in this file, in
//! `dregg_circuit::pasta_windowed_witness`, or in `prove_vm_descriptors2_batch` authors a
//! constraint, a builder gadget or an `air_accepts` predicate. Rust fills trace CELLS and runs the
//! deployed prover.
//!
//! ## What this measures and why it can be measured at all
//!
//! `pasta_bound_sg_prove.rs` binds 124 generators. The ceiling was never geometric: the deployed
//! exact-public tooth spent ONE batch AIR instance per manifest ROW and capped a manifest at
//! `MAX_EXACT_PUBLIC_ROWS = 128`, and since `PublicLookupBalanced` is a PERMUTATION (manifest rows
//! = trace rows) that was a 128-row ceiling on any contents-bound trace — 31 generators a slice.
//! `Ir2Air::ExactPublicTable` (2026-07-29) realizes a whole manifest as ONE multiplicity-bearing
//! instance, so the question became a MEASUREMENT, and this file is the instrument.
//!
//! ## ⚑ The geometry excludes 32,768 EXACTLY, and that is structural
//!
//! The trace height is `planes · (w + 1)` and p3 needs a power of two, so `w + 1` and `planes` are
//! powers of two and `w = 2^m − 1`. `n · w` is therefore never `2^15`: the best four-way cover is
//! `4 · 8191 = 32,764`, four generators short. That is the one-doubling-row-per-plane schedule,
//! not the realization — reaching 32,768 exactly needs a schedule change in Lean, not a bigger cap.
//!
//! ## ⚑ THE MEASUREMENT (2026-07-29, this laptop, `--release`, production `ir2_config`)
//!
//! Four slices, four bit planes, one batch proof, DEPLOYED verifier, substituted-generator tamper
//! re-run and REFUSED at every rung:
//!
//! ```text
//!   w      generators   rows x width   manifest rows   inst   prove      verify    proof
//!     31          124    128 x 529              128       8    0.58 s    0.042 s   360,333 B
//!    127          508    512 x 529              512       8    2.20 s    0.127 s   371,420 B
//!    511        2,044  2,048 x 529            2,048       8    9.09 s    0.478 s   387,288 B
//!  2,047        8,188  8,192 x 529            8,192       8   35.69 s    1.913 s   404,891 B
//!  8,191       32,764 32,768 x 529           32,768       8  146.35 s    8.024 s   418,905 B
//! ```
//!
//! **The ladder did not stop.** It was run to the top rung the schedule admits and every rung
//! proved, verified and refused the tamper — so the answer to "how many of Mina's 32,768
//! generators can be contents-bound" is **32,764, all but the four the geometry excludes**, and the
//! residual is a Lean-side schedule question, not a prover one. Instance count is CONSTANT at 8
//! across a 256-fold scale-up (it would have been 4 + 4·32,768 = 131,076 under the old
//! realization), and proof size grows 360 KB → 419 KB — 16% for 256x the generators.
//!
//! ⚠ What this does NOT touch, unchanged and still open: the scalars are SYNTHETIC (the s-vector
//! binding to the block's IPA challenges is a different rung), P10, the ℤ↔felt gap, and the
//! RCB-formula→group-law transport. This rung is about the GENERATORS.
//!
//! ## Running it
//!
//! The `w > 31` artifacts are 0.4–7 MB EACH and are deliberately NOT committed (the tree is under
//! an LFS budget). Re-derive them and point this at them:
//!
//! ```text
//! scripts/regen-pasta-bound-scaled.sh <hbox-lane> <outdir>
//! DREGG_PASTA_SCALE_DIR=<outdir> cargo test -p dregg-circuit --release \
//!     --test pasta_bound_sg_scale -- --nocapture
//! ```
//!
//! With the variable unset the test SKIPS and says so. It is a measurement lane, not a gate — the
//! GATE is `pasta_bound_sg_prove.rs`, which runs on committed artifacts every time.

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, TableSem, parse_vm_descriptor2, prove_vm_descriptors2_batch,
    verify_vm_descriptors2_batch,
};
use dregg_circuit::pasta_windowed_witness::{
    COL_ACCX, COL_DBL, NUM_LIMBS, Pt, RowSpec, TRACE_WIDTH, U256, build_trace,
};
use dregg_circuit::refusal::{DEPLOYED_VERIFIER_REFUSAL_MARKERS, must_refuse};
use sha2::{Digest, Sha256};
use std::time::Instant;

const SLICES: usize = 4;
const PLANES: usize = 4;
const BOUND_WIDTH: usize = 529;
const PI_COUNT: usize = 29;
const COL_LO: usize = 525;
const COL_HI: usize = 526;
const COL_TIDX: usize = 527;
const COL_GIDX: usize = 528;

/// The ladder. `w = 2^m − 1`, so `height = PLANES · (w+1)` is a power of two.
/// `4 · 8191 = 32,764` of Mina's 32,768 — the most the schedule admits (see the header).
const LADDER: [usize; 4] = [127, 511, 2047, 8191];

/// ⚑ **The sha256 of every ladder artifact, `(digest, w, k)`.** The bytes are NOT committed (39 MB
/// against a 3.0 MB, non-LFS `fixtures/` tree); these pins are what make the measurement
/// reproducible without them. `scripts/regen-pasta-bound-scaled.sh` re-derives the files from the
/// Lean, which is deterministic — a pin that misses means the emitter or `MinaWrapSrsG` moved, and
/// the measured numbers below no longer describe the artifact on disk.
const PINS: [(&str, usize, usize); 16] = [
    (
        "b9ff369efc8e77f4d6ff31afc4b38460941e43968a06af4a65bcd87520608bdb",
        127,
        0,
    ),
    (
        "c358529ebe5803e82e001f40fa8f1a05fcc6f7cd01e3d042a20976d602bfc021",
        127,
        1,
    ),
    (
        "d22400a06411079e27f6a28b2ed290efdff1799fcebf4e07c4fd059d0b51b822",
        127,
        2,
    ),
    (
        "b7d1fa88eb065864c1327465c12a1ba398a4417631255e0c107a3a466436d4de",
        127,
        3,
    ),
    (
        "7747770b42749d815a6da4c5549145fb605525cd61136c08809be256970ff932",
        511,
        0,
    ),
    (
        "11b30de3f014686d6f56de8eeb2e4b899eb8c665284c7ba91cda7723fd7b1680",
        511,
        1,
    ),
    (
        "dd4e7d278a9a26eed6f947420b02bde5508274a3a75a2ec759a968fd339db66e",
        511,
        2,
    ),
    (
        "976bf2eb3322c275dd42dc9caee57398abeea66a8ec309ccf5047acc001ca798",
        511,
        3,
    ),
    (
        "157929c9e447b0f9188d61417a242057da8daf1e722ba1316b8eed18a8179f04",
        2047,
        0,
    ),
    (
        "1954bf9b1cfc97538290ef69ffcf5247355cf20b942b744094c92f9b8c25ffdc",
        2047,
        1,
    ),
    (
        "fc78b82c00a2c473be339491cbd6d815153e88395f39b71b6b47c394bffc1720",
        2047,
        2,
    ),
    (
        "46417058a6e739ac5e93b76127287d14f7a860934aa8f83febaafb4ddbbfd121",
        2047,
        3,
    ),
    (
        "6a6ff08a8ba01656829e6189958d2c1ca5bfdf198d33108ee92d507d32574b92",
        8191,
        0,
    ),
    (
        "ff687039f02d0f57cca15d49912e88828fe420d918d2faed0548cd6962927afd",
        8191,
        1,
    ),
    (
        "d57fb3a21cae91f7af9b8c06f00b25228357f54d0887abe7dee981931c89b375",
        8191,
        2,
    ),
    (
        "d12a76a903706b71f3b29b8d9e825fc5bd63a68ede9e44258c809bbd7509e2fe",
        8191,
        3,
    ),
];

fn sha256_hex(bytes: &[u8]) -> String {
    let mut h = Sha256::new();
    h.update(bytes);
    h.finalize().iter().map(|b| format!("{b:02x}")).collect()
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

fn widen(trace: Vec<Vec<BabyBear>>, lo: usize, hi: usize) -> Vec<Vec<BabyBear>> {
    let mut gidx: usize = 0;
    trace
        .into_iter()
        .enumerate()
        .map(|(i, mut row)| {
            assert_eq!(row.len(), TRACE_WIDTH);
            let dbl = row[COL_DBL].as_u32() == 1;
            row.resize(BOUND_WIDTH, BabyBear::ZERO);
            row[COL_LO] = BabyBear::new(u32::try_from(lo).expect("lo fits"));
            row[COL_HI] = BabyBear::new(u32::try_from(hi).expect("hi fits"));
            row[COL_TIDX] = BabyBear::new(u32::try_from(i).expect("row index fits"));
            row[COL_GIDX] = BabyBear::new(u32::try_from(gidx).expect("gen index fits"));
            gidx = if dbl { lo } else { gidx + 1 };
            row
        })
        .collect()
}

fn public_inputs_of(trace: &[Vec<BabyBear>], lo: usize, hi: usize) -> Vec<BabyBear> {
    let last = trace.last().expect("non-empty trace");
    let mut pis = Vec::with_capacity(PI_COUNT);
    pis.push(BabyBear::new(u32::try_from(lo).expect("lo fits")));
    pis.push(BabyBear::new(u32::try_from(hi).expect("hi fits")));
    for i in 0..27 {
        pis.push(last[COL_ACCX + i]);
    }
    pis
}

fn slice_trace(
    manifest: &[Vec<u32>],
    k: usize,
    w: usize,
    edit: Option<(usize, Pt)>,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let lo = w * k;
    let mut sched = schedule_of(manifest);
    if let Some((row, src)) = edit {
        let bit = match sched[row] {
            RowSpec::CondAdd { bit, .. } => bit,
            RowSpec::Double => panic!("the edited row must be a conditional-add row"),
        };
        sched[row] = RowSpec::CondAdd { src, bit };
    }
    let trace = widen(build_trace(&Pt::INFINITY, &sched), lo, lo + w);
    let pis = public_inputs_of(&trace, lo, lo + w);
    (trace, pis)
}

/// Load the four slices of one ladder rung, or `None` if they are not on disk. Every file that IS
/// on disk is checked against its sha256 pin FIRST — a re-emitted artifact must not slide under a
/// green measurement.
fn load(dir: &str, w: usize) -> Option<Vec<EffectVmDescriptor2>> {
    (0..SLICES)
        .map(|k| {
            let path = format!("{dir}/pasta-rcb-sg-bound-{k}-of-4-w{w}-p4.json");
            let json = std::fs::read_to_string(&path).ok()?;
            let want = PINS
                .iter()
                .find(|&&(_, pw, pk)| pw == w && pk == k)
                .map(|&(digest, _, _)| digest)
                .unwrap_or_else(|| panic!("no sha256 pin recorded for w={w} k={k}"));
            assert_eq!(
                sha256_hex(json.as_bytes()),
                want,
                "{path} was re-emitted; re-read the Lean, re-measure, and re-pin"
            );
            Some(parse_vm_descriptor2(&json).unwrap_or_else(|e| {
                panic!("the deployed checker must parse the Lean descriptor {path}: {e}")
            }))
        })
        .collect()
}

/// ⚑ **THE LADDER.** For each rung: build the four honest slices, prove them as ONE batch, verify
/// with the DEPLOYED verifier, and re-run the substituted-generator tamper. Reports the measured
/// prove/verify/size/instance costs, and — the point — where it stops fitting.
#[test]
fn contents_bound_scale_ladder() {
    let Ok(dir) = std::env::var("DREGG_PASTA_SCALE_DIR") else {
        println!(
            "[skip] DREGG_PASTA_SCALE_DIR unset — re-derive the scaled artifacts with \
             scripts/regen-pasta-bound-scaled.sh and point this at them (see the header)."
        );
        return;
    };

    let mut reached = 0usize;
    for w in LADDER {
        let Some(descs) = load(&dir, w) else {
            println!("[skip] w={w}: artifacts not in {dir}");
            continue;
        };
        let height = PLANES * (w + 1);
        let manifest_rows = manifest_of(&descs[0]).len();
        assert_eq!(
            manifest_rows, height,
            "manifest rows = trace rows (the balance is a permutation)"
        );
        // the DISTINCT rows are what the single-instance table actually commits.
        let distinct = {
            let mut d = manifest_of(&descs[0]).clone();
            d.sort_unstable();
            d.dedup();
            d.len()
        };

        let t_wit = Instant::now();
        let mut traces = Vec::new();
        let mut pis = Vec::new();
        for k in 0..SLICES {
            let (t, p) = slice_trace(manifest_of(&descs[k]), k, w, None);
            traces.push(t);
            pis.push(p);
        }
        let witness_time = t_wit.elapsed();

        let refs: Vec<&[Vec<BabyBear>]> = traces.iter().map(|t| t.as_slice()).collect();
        let t0 = Instant::now();
        let proof = prove_vm_descriptors2_batch(&descs, &refs, &pis).unwrap_or_else(|e| {
            panic!(
                "w={w}: the LEAN-AUTHORED AIRs refused this witness: {e}\n\
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
        verify_vm_descriptors2_batch(&descs, &proof, &pis)
            .unwrap_or_else(|e| panic!("w={w}: the deployed verifier must accept: {e}"));
        let verify_time = t1.elapsed();
        let bytes = postcard::to_allocvec(&proof).expect("serialize").len();

        println!(
            "[rung] w={w:5} | {gens:6} generators | {height:6} rows x {BOUND_WIDTH} | manifest \
             {manifest_rows:6} rows ({distinct:6} distinct) | {inst} instances | witness \
             {witness_time:?} | prove {prove_time:?} | verify {verify_time:?} | proof {bytes} bytes",
            gens = SLICES * w,
            inst = proof.degree_bits.len(),
        );

        // ⚑ and the tamper that defines the rung must still fire AT THIS SCALE.
        let manifest = manifest_of(&descs[2]).clone();
        let victim = 6usize;
        let donor = 7usize;
        let substitute = point_of(&manifest[donor]);
        assert!(substitute.on_curve(), "the substitute must be a real point");
        let mut b_traces = Vec::new();
        let mut b_pis = Vec::new();
        for k in 0..SLICES {
            let edit = (k == 2).then_some((victim, substitute));
            let (t, p) = slice_trace(manifest_of(&descs[k]), k, w, edit);
            b_traces.push(t);
            b_pis.push(p);
        }
        let b_refs: Vec<&[Vec<BabyBear>]> = b_traces.iter().map(|t| t.as_slice()).collect();
        let refusal = must_refuse(&format!("w={w}: a substituted Mina generator"), || {
            prove_vm_descriptors2_batch(&descs, &b_refs, &b_pis).map(|_| ())
        });
        assert!(
            DEPLOYED_VERIFIER_REFUSAL_MARKERS
                .iter()
                .any(|m| refusal.contains(m)),
            "w={w}: the substituted generator must be refused by the DEPLOYED verifier, got: \
             {refusal}"
        );
        println!("[rung] w={w:5} | substituted-generator tamper REFUSED: {refusal}");
        reached = w;
    }
    println!(
        "[ladder] largest rung that PROVED AND VERIFIED on the deployed path: w={reached} \
         ({} of Mina's 32,768 generators)",
        SLICES * reached
    );
}
