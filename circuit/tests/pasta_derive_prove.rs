//! # The s-vector, DERIVED IN CIRCUIT — proved, verified, and four tampers deep.
//!
//! ## Substrate, said out loud
//!
//! **The AIRs are Lean-authored.** `dregg-pasta-rcb-sg-derive-<k>-of-10922::v1` is
//! `Dregg2.Circuit.Emit.PastaMsmScalarDerive.deriveRowDesc 15 10922 k 3 256 MinaWrapSrsG.SRS_G
//! (SCAL …)` — 1053 constraints, of which the first 98 are `PastaMsmOnCurve.onCurveRowDesc`'s
//! verbatim (`deriveRowDesc_extends_onCurve` proves the prefix in the Lean kernel), the first 82
//! of THOSE are `PastaMsmBound`'s, the first 78 of those `PastaMsmSliced`'s and the first 45 of
//! those `PastaMsmWindowed`'s row template. Nothing in this file or in
//! `dregg_circuit::pasta_windowed_witness` authors a constraint, a builder gadget or an
//! `air_accepts` predicate. The Rust side parses the emitted descriptors, fills trace CELLS, and
//! runs the deployed prover and the deployed verifier.
//!
//! ## ⚑⚑ WHAT THIS RUNG MOVES
//!
//! Every rung up to `PastaMsmScalarBound` bound the digit column to the descriptor's MANIFEST, and
//! the manifest to the block's challenges by a Lean `def`. So a verified proof said "these rows
//! carry the s-vector of the challenges the DESCRIPTOR AUTHOR chose". The tensor was never
//! recomputed by an emitted constraint, and `PastaMsmScalarBound` §7.1 said so in as many words.
//!
//! `PastaMsmScalarDerive` recomputes it. The 15 IPA challenges are **public inputs** (slots
//! 29..163), pinned on row 0 and threaded down every row, and the emitted gates force
//!
//! ```text
//!   PR 0 = 1,   PR (j+1) ≡ PR j · MU j  (mod q),   MU j = c_j if GIDX's digit (nb−1−j) else 1
//!   Σ_p 2^(planes−1−p) · SB p = PR nb                          (a canonical bit decomposition)
//!   (1 − DBL) · (BIT − Σ_p SE p · SB p) = 0                    (the row's plane reads its digit)
//! ```
//!
//! so `s_GIDX = ∏_j c_j^{bit_j(GIDX)}` is a value the AIR COMPUTES from the wire, and the row's
//! conditional-add bit is its digit. What the verifier now hands the circuit is the challenge
//! vector; what the circuit produces is the scalar. That is the thing this file proves.
//!
//! ## The shape, and why it is what it is
//!
//! `w = 3`, `planes = 256`, `nb = 15`, four slices. The trace height is `planes · (w + 1)` and
//! `prove_vm_descriptors2_batch` REFUSES a non-power-of-two height, so `w + 1` and `planes` are
//! both powers of two. An s-vector entry is a Pallas SCALAR field element
//! (`PastaMsmScalarBound.block_s_fits_255`), so `planes = 256` is the FIRST admissible plane
//! count: it is not a knob, it is what binding the real challenges costs.
//!
//! ⚑ THE FOUR SLICES ARE CHOSEN, NOT TILED — `k = 0, 3640, 7281, 10921`, i.e. absolute generator
//! indices 0, 10920, 21843 and 32763 of the 32,768-point Wrap SRS. A cut at `k = 0..3` would only
//! ever set index bits 0..2, under which ten of the fifteen challenges are selected OUT on every
//! row and their `b = 1` arm is never once exercised. `every_challenge_bit_is_exercised` measures
//! that the union really is all fifteen.
//!
//! ⚠ TOY IN ONE AXIS, DEPLOYED IN THE OTHER, and the labels are not decoration. The challenge
//! count (15), the challenges themselves (the block's own, from `MinaWrapOpeningGate.CHAL_F`), the
//! plane count (256), the generators (Mina's real Wrap SRS) and the column count (1876) are the
//! deployed ones. The number of GENERATORS PER SLICE is 3, against 8,192 in the full cut. Binding
//! more of them is `PastaMsmBound`'s axis, not this one.

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, TableSem, parse_vm_descriptor2, prove_vm_descriptors2_batch,
    verify_vm_descriptors2_batch,
};
use dregg_circuit::pasta_windowed_witness::{
    COL_ACCX, COL_ACCY, COL_ACCZ, COL_BIT, COL_DBL, COL_OC_ACC, COL_OC_SRC, COL_SRCX, COL_SRCY,
    COL_SRCZ, DeriveLayout, NUM_LIMBS, Pt, Q_PASTA, RowSpec, SLICED_PI_COUNT, TRACE_WIDTH, U256,
    build_trace, derive_scalar, mul_mod_q, put_derive_block, put_on_curve_block,
    put_on_curve_block_forged, read_point,
};
use dregg_circuit::refusal::{DEPLOYED_VERIFIER_REFUSAL_MARKERS, must_refuse};
use sha2::{Digest, Sha256};
use std::time::Instant;

// ---------------------------------------------------------------------------------------------
// The Lean-emitted artifacts, sha256-pinned so a silent re-emit cannot slide under a green test.
// `scripts/regen-pasta-derive.sh` re-derives every one of them.
// ---------------------------------------------------------------------------------------------

/// The four SCALAR-DERIVED descriptors of the proved cut.
const DERIVE: [(&str, &str); 4] = [
    (
        include_str!("fixtures/pasta-sg-derive/pasta-rcb-sg-derive-0-of-10922.json"),
        "5597c0fab01edf9eeb4f63c7bb93daee08b5f66dccd918da843efd9acedadd4d",
    ),
    (
        include_str!("fixtures/pasta-sg-derive/pasta-rcb-sg-derive-3640-of-10922.json"),
        "b37d83b77b86cbb567173b0a66de37d1e97ab594797a660df78f8d56e3d743b7",
    ),
    (
        include_str!("fixtures/pasta-sg-derive/pasta-rcb-sg-derive-7281-of-10922.json"),
        "81f209ddd76e2ae916a18635f5e633faa86023a3aaa7b6130dd2cc6034bcacb9",
    ),
    (
        include_str!("fixtures/pasta-sg-derive/pasta-rcb-sg-derive-10921-of-10922.json"),
        "9ea08d35b4d07c71e185c1fb4c595b9d6ad1e6be9ec2e62fd37cace405adc3e6",
    ),
];

/// ⚑ A DIFFERENT BLOCK, slice 0 only: the SAME shape with a different challenge vector's s-vector
/// in its manifest. It is what turns the challenge-inconsistency tamper into a MEASUREMENT — the
/// forged derivation is exhibited PROVING against its own challenges and REFUSED against ours.
const DERIVE_BLOCK_B: (&str, &str) = (
    include_str!("fixtures/pasta-sg-derive/pasta-rcb-sg-derive-0-of-10922-blockB.json"),
    "7c76e675d570c542411d4d0d5f6318ea06dca1d5e838536d8e072a8b7913f11c",
);

/// The challenge vectors. ⚑ NOT in the descriptors — they are PUBLIC INPUTS, so the harness must
/// carry them as data. `manifest_digits_are_the_derived_s_vector` CHECKS this copy against the
/// descriptor's own digit column rather than trusting it.
const CHALS_A: (&str, &str) = (
    include_str!("fixtures/pasta-sg-derive/chals-block0.json"),
    "69b820d49b2b29d0e17c5569ae174a7a7f4964baf97b5ff51af3d2ac7d8bcaff",
);
const CHALS_B: (&str, &str) = (
    include_str!("fixtures/pasta-sg-derive/chals-block1.json"),
    "3a8bb88fe2cdea76c039491a341b11849884461d41400656efa59ffc6e8e693a",
);

/// `PastaMsmBound.WB` / `PastaMsmSliced.LO` / `HI` / `PastaMsmBound.TIDX` / `GIDX`.
const COL_LO: usize = 525;
const COL_HI: usize = 526;
const COL_TIDX: usize = 527;
const COL_GIDX: usize = 528;

/// The emitted shape (`EmitPastaDerive.lean`'s kernel `#guard`s carry the same numbers).
const NB: usize = 15;
const PLANES: usize = 256;
const W: usize = 3;
const N: usize = 10922;
const KS: [usize; 4] = [0, 3640, 7281, 10921];
const HEIGHT: usize = PLANES * (W + 1);
const DERIVE_WIDTH: usize = 1876;
const DERIVE_PI_COUNT: usize = 164;
const DERIVE_CONSTRAINTS: usize = 1053;

/// `PastaMsmOnCurve.WOC` — the width this rung extends.
const ONCURVE_WIDTH: usize = 799;
/// `PastaMsmOnCurve.onCurveRowDesc`'s constraint count — the prefix this rung extends.
const ONCURVE_CONSTRAINTS: usize = 98;

/// The degenerate triple (`PastaMsmOnCurve.origin_is_absorbing`).
const ORIGIN: Pt = Pt {
    x: U256::ZERO,
    y: U256::ZERO,
    z: U256::ZERO,
};

fn layout() -> DeriveLayout {
    DeriveLayout {
        nb: NB,
        planes: PLANES,
    }
}

fn sha256_hex(bytes: &[u8]) -> String {
    let mut h = Sha256::new();
    h.update(bytes);
    h.finalize().iter().map(|b| format!("{b:02x}")).collect()
}

fn parse_cut() -> Vec<EffectVmDescriptor2> {
    DERIVE
        .iter()
        .map(|(json, _)| {
            parse_vm_descriptor2(json).expect("the deployed checker must parse the Lean descriptor")
        })
        .collect()
}

fn parse_block_b() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(DERIVE_BLOCK_B.0).expect("the deployed checker must parse block B")
}

/// Pull the decimal challenge strings out of `{"block":N,"challenges":["…",…]}`. Hand-rolled
/// because `dregg-circuit` keeps no JSON dependency at the verify floor.
fn parse_chals(json: &str) -> Vec<U256> {
    let start = json.find("\"challenges\":[").expect("challenges key") + "\"challenges\":[".len();
    let end = json[start..].find(']').expect("challenges close") + start;
    json[start..end]
        .split(',')
        .map(|s| U256::from_dec(s.trim().trim_matches('"')))
        .collect()
}

fn chals_a() -> Vec<U256> {
    parse_chals(CHALS_A.0)
}

fn chals_b() -> Vec<U256> {
    parse_chals(CHALS_B.0)
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

/// How a slice's derivation block should be filled.
#[derive(Clone, Copy)]
struct Fill<'a> {
    /// What the `CHc` columns carry — what the verifier pins.
    wire: &'a [U256],
    /// What the multiplier / product / digit columns carry — what the prover claims.
    derived: &'a [U256],
    /// ⚑ Rewrite the chain's LANDING BLOCK on every row consuming this generator index to the
    /// NON-CANONICAL representative `s + q`, adjusting the last step's quotient so the emitted
    /// `fqMulCore` still holds exactly. See `the_decomposition_is_not_canonical_and_the_manifest_
    /// is_what_catches_it`.
    noncanonical_at: Option<usize>,
}

fn honest_fill<'a>(chals: &'a [U256]) -> Fill<'a> {
    Fill {
        wire: chals,
        derived: chals,
        noncanonical_at: None,
    }
}

/// Write a 9x30 field element into a row (the witness module's `put_field`, which is private).
fn put_field_at(row: &mut [BabyBear], base: usize, v: &U256) {
    for l in 0..NUM_LIMBS {
        row[base + l] = BabyBear::new(v.limb30(l));
    }
}

/// The running product after `n` of the `nb` chain steps, at generator index `idx`.
fn partial_product(chals: &[U256], idx: usize, n: usize) -> U256 {
    let nb = chals.len();
    let mut acc = U256::ONE;
    for (j, c) in chals.iter().enumerate().take(n) {
        if (idx >> (nb - 1 - j)) & 1 == 1 {
            acc = mul_mod_q(&acc, c).0;
        }
    }
    acc
}

/// Rewrite one row's chain landing block and digits to the representative `s + q`, keeping every
/// emitted gate of the chain satisfied over ℤ. Returns that representative.
fn make_noncanonical(row: &mut [BabyBear], chals: &[U256], gidx: usize) -> U256 {
    let lay = layout();
    let nb = chals.len();
    let prev = partial_product(chals, gidx, nb - 1);
    let mu = if (gidx >> 0) & 1 == 1 {
        chals[nb - 1]
    } else {
        U256::ONE
    };
    let (s, quot) = mul_mod_q(&prev, &mu);
    assert!(
        quot != U256::ZERO,
        "the last step must actually reduce, or `quot − 1` is not a witness"
    );
    let (quot2, borrow) = quot.sbb(&U256::ONE);
    assert!(!borrow);
    let (s2, carry) = s.adc(&Q_PASTA);
    assert!(!carry, "s + q must fit 256 bits");
    put_field_at(row, lay.qu(NUM_LIMBS * (nb - 1)), &quot2);
    put_field_at(row, lay.pr(NUM_LIMBS * nb), &s2);
    for p in 0..PLANES {
        row[lay.sb(p)] = BabyBear::new(s2.bit(PLANES - 1 - p));
    }
    s2
}

/// Widen a 525-column windowed trace to the derived width: the four declaration/index columns, the
/// two on-curve certificates, and the derivation block.
///
/// ⚑ The certificate written is always the BEST ONE THAT EXISTS for the point in the cells: honest
/// where the point has an inverse, and the `YINV = 0` fallback only where it has none. A forgery
/// test whose witness generator simply gave up would measure nothing.
fn widen_derive(
    trace: Vec<Vec<BabyBear>>,
    lo: usize,
    hi: usize,
    fill: Fill<'_>,
    check_digits: bool,
) -> Vec<Vec<BabyBear>> {
    let lay = layout();
    let mut gidx: usize = 0;
    trace
        .into_iter()
        .enumerate()
        .map(|(i, mut row)| {
            assert_eq!(row.len(), TRACE_WIDTH);
            let dbl = row[COL_DBL].as_u32() == 1;
            let acc = read_point(&row, COL_ACCX, COL_ACCY, COL_ACCZ);
            let src = read_point(&row, COL_SRCX, COL_SRCY, COL_SRCZ);
            row.resize(lay.width(), BabyBear::ZERO);
            row[COL_LO] = BabyBear::new(lo as u32);
            row[COL_HI] = BabyBear::new(hi as u32);
            row[COL_TIDX] = BabyBear::new(i as u32);
            row[COL_GIDX] = BabyBear::new(gidx as u32);
            for (base, pt) in [(COL_OC_ACC, acc), (COL_OC_SRC, src)] {
                if pt.y == U256::ZERO {
                    put_on_curve_block_forged(&mut row, base, &pt);
                } else {
                    put_on_curve_block(&mut row, base, &pt);
                }
            }
            let plane = i / (W + 1);
            let mut s = put_derive_block(&mut row, &lay, fill.wire, fill.derived, gidx, plane);
            if fill.noncanonical_at == Some(gidx) {
                s = make_noncanonical(&mut row, fill.derived, gidx);
            }
            // ⚑ THE MANIFEST AND THE DERIVATION AGREE, checked at witness-build time on a
            // CONDITIONAL-ADD row: the descriptor's declared digit IS the derived scalar's digit
            // at this row's own plane. This is the belt-and-braces the manifest was kept for; if
            // the two ever disagreed the instance would have NO satisfying trace at all, and this
            // assert is what turns that into a legible failure instead of a mysterious refusal.
            if check_digits && !dbl {
                assert_eq!(
                    row[COL_BIT].as_u32(),
                    s.bit(PLANES - 1 - plane),
                    "row {i}: the manifest's declared digit is not the derived s-vector's bit"
                );
            }
            gidx = if dbl { lo } else { gidx + 1 };
            row
        })
        .collect()
}

fn public_inputs_of(trace: &[Vec<BabyBear>], lo: usize, hi: usize, wire: &[U256]) -> Vec<BabyBear> {
    let lay = layout();
    let last = trace.last().expect("non-empty trace");
    let mut pis = Vec::with_capacity(lay.pi_count());
    pis.push(BabyBear::new(lo as u32));
    pis.push(BabyBear::new(hi as u32));
    for i in 0..27 {
        pis.push(last[COL_ACCX + i]);
    }
    assert_eq!(pis.len(), SLICED_PI_COUNT);
    for c in wire {
        for l in 0..NUM_LIMBS {
            pis.push(BabyBear::new(c.limb30(l)));
        }
    }
    pis
}

/// One slice's trace, starting from `acc0`, with an optional source-point edit.
fn slice_trace(
    manifest: &[Vec<u32>],
    k: usize,
    acc0: &Pt,
    fill: Fill<'_>,
    edit: Option<(usize, Pt)>,
    check_digits: bool,
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
    let trace = widen_derive(build_trace(acc0, &sched), lo, hi, fill, check_digits);
    let pis = public_inputs_of(&trace, lo, hi, fill.wire);
    (trace, pis)
}

/// All four honest slices of the cut.
fn honest_cut(chals: &[U256]) -> (Vec<Vec<Vec<BabyBear>>>, Vec<Vec<BabyBear>>) {
    let descs = parse_cut();
    let fill = honest_fill(chals);
    let mut traces = Vec::new();
    let mut pis = Vec::new();
    for (i, k) in KS.iter().enumerate() {
        let (t, p) = slice_trace(manifest_of(&descs[i]), *k, &Pt::INFINITY, fill, None, true);
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
    for (i, (json, want)) in DERIVE.iter().enumerate() {
        assert_eq!(
            sha256_hex(json.as_bytes()),
            *want,
            "derive descriptor {i} was re-emitted; re-read the Lean and re-pin"
        );
    }
    for (json, want) in [DERIVE_BLOCK_B, CHALS_A, CHALS_B] {
        assert_eq!(sha256_hex(json.as_bytes()), want, "artifact was re-emitted");
    }
    let cut = parse_cut();
    for (i, desc) in cut.iter().enumerate() {
        assert_eq!(
            desc.name,
            format!("dregg-pasta-rcb-sg-derive-{}-of-{N}::v1", KS[i])
        );
        assert_eq!(desc.trace_width, DERIVE_WIDTH, "PastaMsmScalarDerive.WD");
        assert_eq!(desc.trace_width, layout().width(), "the Rust layout agrees");
        assert_eq!(desc.public_input_count, DERIVE_PI_COUNT, "29 + 9·15");
        assert_eq!(desc.public_input_count, layout().pi_count());
        assert_eq!(
            desc.constraints.len(),
            DERIVE_CONSTRAINTS,
            "98 on-curve + (8 + 29·15 + 2·256)"
        );
        assert_eq!(
            manifest_of(desc).len(),
            HEIGHT,
            "manifest rows = trace rows"
        );
    }
    // ⚑ THE PREFIX, on the EMITTED BYTES: block B differs from block A at slice 0 ONLY in the
    // manifest's digit column — same constraints, same generators, same schedule.
    let b = parse_block_b();
    assert_eq!(
        cut[0].constraints, b.constraints,
        "same emitted constraints"
    );
    let (ma, mb) = (manifest_of(&cut[0]), manifest_of(&b));
    let mut digit_diffs = 0usize;
    for (ra, rb) in ma.iter().zip(mb.iter()) {
        assert_eq!(ra[0], rb[0], "row key moved");
        assert_eq!(ra[1], rb[1], "generator index moved");
        assert_eq!(&ra[3..], &rb[3..], "generator limbs moved");
        if ra[2] != rb[2] {
            digit_diffs += 1;
        }
    }
    assert!(
        digit_diffs > 0,
        "the two blocks' s-vectors must actually disagree somewhere in this slice"
    );
    println!(
        "[shape] derive: {DERIVE_CONSTRAINTS} constraints / {DERIVE_WIDTH} columns / \
         {DERIVE_PI_COUNT} PIs / {HEIGHT} rows — against on-curve's {ONCURVE_CONSTRAINTS} / \
         {ONCURVE_WIDTH} / {SLICED_PI_COUNT} / 128. Block B differs in {digit_diffs} of {HEIGHT} \
         manifest digits."
    );
}

/// ⚑⚑ **THE MANIFEST IS THE DERIVED S-VECTOR, checked on the bytes.** The descriptor's declared
/// digit column is recomputed from the CHALLENGE VECTOR by the same tensor the AIR computes, row
/// by row, before any proof is attempted. This is the check that makes the challenge fixture data
/// rather than an article of faith — and it is also the answer to "you now have two shapes that
/// must agree": they are compared, here, mechanically.
#[test]
fn manifest_digits_are_the_derived_s_vector() {
    let cut = parse_cut();
    let a = chals_a();
    assert_eq!(a.len(), NB);
    for c in &a {
        assert!(*c < Q_PASTA, "a challenge is not a reduced Pallas scalar");
    }
    let mut checked = 0usize;
    for (i, desc) in cut.iter().enumerate() {
        let lo = W * KS[i];
        for (row_index, row) in manifest_of(desc).iter().enumerate() {
            if row.iter().all(|&v| v == 0) {
                continue; // a doubling row
            }
            assert_eq!(row[0] as usize, row_index + 1, "row key");
            let gidx = row[1] as usize - 1;
            let plane = row_index / (W + 1);
            assert!(
                (lo..lo + W).contains(&gidx),
                "generator index off the slice"
            );
            let s = derive_scalar(&a, gidx);
            assert_eq!(
                row[2],
                s.bit(PLANES - 1 - plane),
                "slice {i} row {row_index}: the manifest digit is not the s-vector's bit"
            );
            checked += 1;
        }
    }
    assert_eq!(checked, KS.len() * W * PLANES);
    // …and block B's manifest is NOT this challenge vector's s-vector, so the comparison bites.
    let b = parse_block_b();
    let mismatches = manifest_of(&b)
        .iter()
        .enumerate()
        .filter(|(row_index, row)| {
            !row.iter().all(|&v| v == 0)
                && row[2] != derive_scalar(&a, row[1] as usize - 1).bit(PLANES - 1 - row_index / 4)
        })
        .count();
    assert!(mismatches > 0, "block B must fail block A's own check");
    println!(
        "[bind]  {checked} manifest digits ARE the derived s-vector; block B misses {mismatches}"
    );
}

/// ⚑ The four slices were chosen so every one of the fifteen challenges is SELECTED on some row.
/// Without this the ten high challenges would only ever be exercised in their `b = 0` arm — the
/// chain would multiply by the field ONE fifteen times over and the demonstration would be of a
/// gate nothing drives.
#[test]
fn every_challenge_bit_is_exercised() {
    let mut seen = [false; NB];
    for k in KS {
        let lo = W * k;
        for gidx in lo..=lo + W {
            for (b, s) in seen.iter_mut().enumerate() {
                if (gidx >> b) & 1 == 1 {
                    *s = true;
                }
            }
        }
    }
    let missing: Vec<usize> = (0..NB).filter(|b| !seen[*b]).collect();
    assert!(
        missing.is_empty(),
        "index bits {missing:?} are never set, so those challenges' b = 1 arm is dead"
    );
    println!("[cover] all {NB} challenge selections are live across the cut");
}

/// ⚑ `MAX_TRACE_WIDTH = 1024` and `MAX_PUBLIC_INPUTS = 64` are the **v1 DSL** deploy caps
/// (`dsl::circuit::ProgramDescriptor::validate`). The IR-v2 path consults NEITHER: `check_descriptor2`
/// bounds every column against the descriptor's OWN `trace_width` and every PI index against its own
/// `public_input_count`, and nothing else. This test states that as a measurement rather than as a
/// reading of the source — the descriptor at 1876 columns and 164 PIs PARSES AND CHECKS, and the
/// proof below is what makes it more than a parse.
#[test]
fn the_v1_width_cap_does_not_bind_the_ir2_path() {
    use dregg_circuit::dsl::circuit::{MAX_PUBLIC_INPUTS, MAX_TRACE_WIDTH};
    assert_eq!(MAX_TRACE_WIDTH, 1024);
    assert_eq!(MAX_PUBLIC_INPUTS, 64);
    let cut = parse_cut();
    assert!(
        cut[0].trace_width > MAX_TRACE_WIDTH,
        "the demonstration is only meaningful past the v1 cap"
    );
    assert!(cut[0].public_input_count > MAX_PUBLIC_INPUTS);
    println!(
        "[cap]   IR-v2 accepted {} columns ({:.2}x the v1 cap of {MAX_TRACE_WIDTH}) and {} PIs \
         ({:.2}x the v1 cap of {MAX_PUBLIC_INPUTS})",
        cut[0].trace_width,
        cut[0].trace_width as f64 / MAX_TRACE_WIDTH as f64,
        cut[0].public_input_count,
        cut[0].public_input_count as f64 / MAX_PUBLIC_INPUTS as f64
    );
}

/// ⚑ **THE DERIVATION BLOCK'S MARGINAL COST, at the SAME SHAPE.** Comparing the derived cut
/// against `pasta_oncurve_gate.rs`'s measures two changes at once — the derivation block AND the
/// 128 → 1024 row count that binding a 255-bit s-vector forces. This isolates the first.
///
/// The baseline is the derived descriptor's own first 98 constraints at width 799 and 29 public
/// inputs. `PastaMsmScalarDerive.deriveRowDesc_extends_onCurve` proves in the Lean kernel that
/// that prefix IS `PastaMsmOnCurve.onCurveRowDesc` at these parameters, and `deriveRowDesc_tables`
/// that the manifest is the same object — so nothing is authored here, a PREFIX IS TAKEN, and the
/// two descriptors differ in exactly the derivation.
#[test]
fn the_derivation_block_marginal_cost_is_measured_at_the_same_shape() {
    let derived = parse_cut();
    let a = chals_a();
    let (traces, pis) = honest_cut(&a);

    let mut base: Vec<EffectVmDescriptor2> = derived.clone();
    for d in &mut base {
        d.constraints.truncate(ONCURVE_CONSTRAINTS);
        d.trace_width = ONCURVE_WIDTH;
        d.public_input_count = SLICED_PI_COUNT;
    }
    let base_traces: Vec<Vec<Vec<BabyBear>>> = traces
        .iter()
        .map(|t| t.iter().map(|r| r[..ONCURVE_WIDTH].to_vec()).collect())
        .collect();
    let base_pis: Vec<Vec<BabyBear>> = pis.iter().map(|p| p[..SLICED_PI_COUNT].to_vec()).collect();

    let refs: Vec<&[Vec<BabyBear>]> = base_traces.iter().map(|t| t.as_slice()).collect();
    let t0 = Instant::now();
    let bp = prove_vm_descriptors2_batch(&base, &refs, &base_pis)
        .expect("the pre-derivation prefix must prove on the same witness");
    let base_prove = t0.elapsed();
    let t1 = Instant::now();
    verify_vm_descriptors2_batch(&base, &bp, &base_pis).expect("…and verify");
    let base_verify = t1.elapsed();
    let base_bytes = postcard::to_allocvec(&bp).expect("serialize").len();

    let refs: Vec<&[Vec<BabyBear>]> = traces.iter().map(|t| t.as_slice()).collect();
    let t2 = Instant::now();
    let dp = prove_vm_descriptors2_batch(&derived, &refs, &pis).expect("the derived cut proves");
    let derive_prove = t2.elapsed();
    let t3 = Instant::now();
    verify_vm_descriptors2_batch(&derived, &dp, &pis).expect("…and verifies");
    let derive_verify = t3.elapsed();
    let derive_bytes = postcard::to_allocvec(&dp).expect("serialize").len();

    let base_area = KS.len() * HEIGHT * ONCURVE_WIDTH;
    let derive_area = KS.len() * HEIGHT * DERIVE_WIDTH;
    println!(
        "[marginal] SAME shape ({} slices x {HEIGHT} rows), derivation block ON vs OFF:\n  \
         area   {base_area} -> {derive_area}  ({:.3}x)\n  \
         cons   {ONCURVE_CONSTRAINTS} -> {DERIVE_CONSTRAINTS}  ({:.2}x)\n  \
         prove  {base_prove:?} -> {derive_prove:?}  ({:.3}x)\n  \
         verify {base_verify:?} -> {derive_verify:?}  ({:.3}x)\n  \
         proof  {base_bytes} -> {derive_bytes} bytes  ({:.3}x)",
        KS.len(),
        derive_area as f64 / base_area as f64,
        DERIVE_CONSTRAINTS as f64 / ONCURVE_CONSTRAINTS as f64,
        derive_prove.as_secs_f64() / base_prove.as_secs_f64(),
        derive_verify.as_secs_f64() / base_verify.as_secs_f64(),
        derive_bytes as f64 / base_bytes as f64,
    );
}

// =============================================================================================
// (b) ⚑⚑ THE RUNG — four derived instances, ONE proof, DEPLOYED verifier
// =============================================================================================

/// ⚑⚑ **THE PROOF.** Satisfiability at birth AND the thing the rung is for: the emitted derivation
/// is not merely a list of constraints that a kernel `#guard` can decide at `nb = 2`, it is a
/// system the DEPLOYED PROVER satisfies at `nb = 15, planes = 256` over the block's own challenges,
/// and the DEPLOYED VERIFIER accepts.
#[test]
fn derived_cut_proves_and_verifies() {
    let descs = parse_cut();
    let a = chals_a();
    let t_build = Instant::now();
    let (traces, pis) = honest_cut(&a);
    let build_time = t_build.elapsed();
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
        KS.len() * 2,
        "one main + ONE multiplicity-bearing table instance, per descriptor"
    );

    let t1 = Instant::now();
    verify_vm_descriptors2_batch(&descs, &proof, &pis).expect("the deployed verifier must accept");
    let verify_time = t1.elapsed();

    let bytes = postcard::to_allocvec(&proof).expect("serialize").len();
    let area = KS.len() * HEIGHT * DERIVE_WIDTH;
    println!(
        "[derived] {} slices x {HEIGHT} x {DERIVE_WIDTH} = {area} cells | witness {build_time:?} \
         | prove {prove_time:?} | verify {verify_time:?} | proof {bytes} bytes",
        KS.len()
    );
    // ⚠ NOT a measurement taken here, and it must not read as one: the curve-gated rung's own
    // numbers come from `pasta_oncurve_gate.rs::gated_cut_proves_and_verifies`, at a DIFFERENT
    // shape (128 rows, 4 bit planes). The apples-to-apples figure — the derivation block ON vs OFF
    // at the SAME shape — is measured live by
    // `the_derivation_block_marginal_cost_is_measured_at_the_same_shape`. Read that one.
    println!(
        "[against] for the cross-shape reference run `pasta_oncurve_gate` (4 x 128 x \
         {ONCURVE_WIDTH} = {} cells); for the marginal cost of THIS block see \
         `the_derivation_block_marginal_cost_is_measured_at_the_same_shape`",
        4 * 128 * ONCURVE_WIDTH
    );
}

/// The derived scalar really is the block's s-vector entry, read off the trace the prover
/// accepted rather than argued — and it is a 250-bit-plus number, so the 256 planes are not
/// decoration.
#[test]
fn the_derived_scalar_is_the_blocks_s_vector() {
    let lay = layout();
    let a = chals_a();
    let (traces, _) = honest_cut(&a);
    let mut wide = 0usize;
    let mut checked = 0usize;
    for (i, t) in traces.iter().enumerate() {
        let lo = W * KS[i];
        for (row_index, row) in t.iter().enumerate() {
            if row[COL_DBL].as_u32() == 1 {
                continue;
            }
            let gidx = row[COL_GIDX].as_u32() as usize;
            assert!((lo..lo + W).contains(&gidx));
            // the chain's landing block, read back out of the trace
            let mut limbs = [0u32; NUM_LIMBS];
            for (l, limb) in limbs.iter_mut().enumerate() {
                *limb = row[lay.pr(NUM_LIMBS * NB) + l].as_u32();
            }
            let s = U256::from_limbs30(&limbs);
            assert_eq!(
                s,
                derive_scalar(&a, gidx),
                "row {row_index}: chain landed elsewhere"
            );
            assert!(s < Q_PASTA);
            if s.bit(200) == 1 || s.bit(240) == 1 {
                wide += 1;
            }
            checked += 1;
        }
    }
    assert!(
        wide > checked / 4,
        "only {wide} of {checked} derived scalars have a high bit set; the 256 planes are not \
         being exercised and the demonstration is of a narrower object than it claims"
    );
    println!("[width] {wide} of {checked} derived scalars carry a bit above 2^200");
}

// =============================================================================================
// (c) ⚑⚑ THE FOUR TAMPERS, ON THE ONE PROVED INSTANCE
// =============================================================================================

/// ⚑⚑ **TAMPER 1 — A SUBSTITUTED GENERATOR.** Slice 2's row 2 rebuilt around the generator at the
/// WRONG absolute index, the whole trace regenerated so every RCB add and carry holds.
#[test]
fn tamper_1_substituted_generator_is_refused() {
    let descs = parse_cut();
    let a = chals_a();
    let fill = honest_fill(&a);
    let manifest2 = manifest_of(&descs[2]).clone();
    let substitute = point_of(&manifest2[3]);
    assert!(
        substitute.on_curve(),
        "the substitute is a REAL Mina SRS generator"
    );
    let mut traces = Vec::new();
    let mut pis = Vec::new();
    for (i, k) in KS.iter().enumerate() {
        let edit = (i == 2).then_some((2usize, substitute));
        // the digit cross-check is off for the edited slice: the row's DIGIT is untouched, it is
        // the SOURCE POINT that moved, so the manifest tuple mismatch is the whole tamper.
        let (t, p) = slice_trace(manifest_of(&descs[i]), *k, &Pt::INFINITY, fill, edit, true);
        traces.push(t);
        pis.push(p);
    }
    let refusal = must_refuse(
        "slice 2 term 1 replaced by the slice's OTHER generator",
        || prove_cut(&descs, &traces, &pis),
    );
    assert!(
        DEPLOYED_VERIFIER_REFUSAL_MARKERS
            .iter()
            .any(|m| refusal.contains(m)),
        "the substituted generator must be refused by the DEPLOYED verifier, got: {refusal}"
    );
    println!("[tamper 1] REFUSED (generator): {refusal}");
}

/// ⚑⚑ **TAMPER 2 — A WRONG-BLOCK SCALAR DIGIT.** One conditional-add row's `BIT` is set to the
/// digit A DIFFERENT BLOCK's s-vector would put there. It is not a random flip: the row is chosen
/// at a `(gidx, plane)` where the two blocks' s-vectors genuinely disagree, so what is planted is
/// a REAL s-vector entry's bit — of the wrong block.
#[test]
fn tamper_2_wrong_block_scalar_is_refused() {
    let descs = parse_cut();
    let (a, b) = (chals_a(), chals_b());
    let (mut traces, pis) = honest_cut(&a);

    // find a row where the two blocks' digits differ
    let lo = W * KS[0];
    let mut hit = None;
    'outer: for row_index in 0..HEIGHT {
        if row_index % (W + 1) == 0 {
            continue;
        }
        let gidx = lo + row_index % (W + 1) - 1;
        let plane = row_index / (W + 1);
        let da = derive_scalar(&a, gidx).bit(PLANES - 1 - plane);
        let db = derive_scalar(&b, gidx).bit(PLANES - 1 - plane);
        if da != db {
            hit = Some((row_index, da, db));
            break 'outer;
        }
    }
    let (row_index, da, db) = hit.expect("the two blocks must disagree somewhere in slice 0");
    assert_eq!(traces[0][row_index][COL_BIT].as_u32(), da);
    traces[0][row_index][COL_BIT] = BabyBear::new(db);

    let refusal = must_refuse(
        "slice 0 digit replaced by the OTHER block's s-vector bit",
        || prove_cut(&descs, &traces, &pis),
    );
    assert!(
        DEPLOYED_VERIFIER_REFUSAL_MARKERS
            .iter()
            .any(|m| refusal.contains(m)),
        "the wrong-block digit must be refused by the DEPLOYED verifier, got: {refusal}"
    );
    println!("[tamper 2] REFUSED (wrong-block scalar, row {row_index}: {da} -> {db}): {refusal}");
}

/// ⚑⚑ **TAMPER 3 — THE ABSORBING STATE.** The initial accumulator is `(0,0,0)`, which nothing
/// pins. `rcb_add((0,0,0), Q) = (0,0,0)` for every `Q`, so the whole fold collapses while every
/// RCB gate, every carry, every quotient, every thread constraint, the entire exact-public lookup
/// AND the whole derivation still hold exactly — the derivation says nothing about the
/// accumulator. `pasta_oncurve_gate.rs` shows the contents-bound descriptor ACCEPTING this exact
/// forgery; the curve gate this rung inherits refuses it, and it is re-fired here so it is known
/// live ON THIS INSTANCE rather than on a sibling's.
#[test]
fn tamper_3_absorbing_state_is_refused() {
    let descs = parse_cut();
    let a = chals_a();
    let fill = honest_fill(&a);
    let mut traces = Vec::new();
    let mut pis = Vec::new();
    for (i, k) in KS.iter().enumerate() {
        let (t, p) = slice_trace(manifest_of(&descs[i]), *k, &ORIGIN, fill, None, true);
        traces.push(t);
        pis.push(p);
    }
    // the forgery is what it claims to be: every accumulator absorbed, every declared generator
    // and every declared digit untouched.
    for (i, t) in traces.iter().enumerate() {
        for (row_index, row) in t.iter().enumerate() {
            assert_eq!(
                read_point(row, COL_ACCX, COL_ACCY, COL_ACCZ),
                ORIGIN,
                "slice {i} row {row_index}: the forgery must be absorbed"
            );
        }
    }
    let refusal = must_refuse("an all-(0,0,0) accumulator", || {
        prove_cut(&descs, &traces, &pis)
    });
    assert!(
        DEPLOYED_VERIFIER_REFUSAL_MARKERS
            .iter()
            .any(|m| refusal.contains(m)),
        "the absorbing state must be refused by the DEPLOYED verifier, got: {refusal}"
    );
    println!("[tamper 3] REFUSED (absorbing state): {refusal}");
}

/// ⚑⚑ **TAMPER 4 — THE CHALLENGE-INCONSISTENT DIGIT, and it is this rung's defining test.**
///
/// Slice 0's derivation columns — every multiplier, every quotient, the whole running product and
/// all 256 witnessed digits — are rebuilt from A DIFFERENT BLOCK's challenge vector. They are
/// internally consistent: the chain really does multiply out to that block's s-vector entry, and
/// the decomposition really is that entry's binary expansion. The ONLY thing that disagrees is the
/// challenge vector ON THE WIRE. REFUSED.
///
/// ⚑ This is the tamper NO EARLIER RUNG COULD SEE. Up to `PastaMsmScalarBound` the digit column
/// was bound to a manifest, and a manifest is whatever the descriptor author wrote; nothing in any
/// emitted constraint related it to a challenge. Here the relation is a gate.
#[test]
fn tamper_4_challenge_inconsistent_derivation_is_refused() {
    let descs = parse_cut();
    let (a, b) = (chals_a(), chals_b());
    let honest = honest_fill(&a);
    // ⚑ wire = THIS block, derivation = the OTHER block. `PastaMsmScalarDerive` §5's `katAsg cs ds`
    // with `cs ≠ ds`, on the deployed prover.
    let forged = Fill {
        wire: &a,
        derived: &b,
        noncanonical_at: None,
    };
    let mut traces = Vec::new();
    let mut pis = Vec::new();
    for (i, k) in KS.iter().enumerate() {
        let fill = if i == 0 { forged } else { honest };
        // the digit check is off on the forged slice: `BIT` is still the MANIFEST's (this block's)
        // digit, so the forgery is exactly "the derivation disagrees with the wire", not "the
        // digit column was edited".
        let (t, p) = slice_trace(
            manifest_of(&descs[i]),
            *k,
            &Pt::INFINITY,
            fill,
            None,
            i != 0,
        );
        traces.push(t);
        pis.push(p);
    }
    let refusal = must_refuse(
        "slice 0's derivation rebuilt from a DIFFERENT block's challenges",
        || prove_cut(&descs, &traces, &pis),
    );
    assert!(
        DEPLOYED_VERIFIER_REFUSAL_MARKERS
            .iter()
            .any(|m| refusal.contains(m)),
        "a challenge-inconsistent derivation must be refused by the DEPLOYED verifier, got: {refusal}"
    );
    println!("[tamper 4] REFUSED (challenge-inconsistent derivation): {refusal}");
}

/// ⚑⚑ **THE POLARITY — the forged derivation is not MALFORMED, it is UNBOUND.** The same shape,
/// built entirely from block B (block B's manifest, block B's derivation, block B's challenges on
/// the wire), PROVES AND VERIFIES. Then the very same descriptor and the very same trace, with THIS
/// block's challenges on the wire, is REFUSED. Without this pair, tamper 4 shows only that
/// something is broken.
#[test]
fn tamper_4_polarity_the_other_block_proves_against_its_own_challenges() {
    let desc = parse_block_b();
    let (a, b) = (chals_a(), chals_b());
    let fill_b = honest_fill(&b);
    let (trace, pis_b) = slice_trace(manifest_of(&desc), KS[0], &Pt::INFINITY, fill_b, None, true);

    // --- ACCEPTED against its OWN challenges ----------------------------------------------------
    let descs = [desc.clone()];
    let traces = [trace.clone()];
    let pis = [pis_b.clone()];
    let refs: Vec<&[Vec<BabyBear>]> = traces.iter().map(|t| t.as_slice()).collect();
    let proof = prove_vm_descriptors2_batch(&descs, &refs, &pis)
        .expect("block B's instance must PROVE against block B's challenges");
    verify_vm_descriptors2_batch(&descs, &proof, &pis)
        .expect("…and the DEPLOYED VERIFIER must accept it");
    println!(
        "[polarity] the other block's instance PROVED AND VERIFIED against its own challenges"
    );

    // --- REFUSED against ours -------------------------------------------------------------------
    // Only the wire moves. The trace is byte-identical; the public inputs carry THIS block's
    // challenge vector instead of that one's.
    let mut pis_a = pis_b.clone();
    for (j, c) in a.iter().enumerate() {
        for l in 0..NUM_LIMBS {
            pis_a[SLICED_PI_COUNT + NUM_LIMBS * j + l] = BabyBear::new(c.limb30(l));
        }
    }
    assert_ne!(pis_a, pis_b, "the two wires must differ");
    let pis = [pis_a];
    let refusal = must_refuse(
        "the other block's instance under OUR challenge vector",
        || prove_cut(&descs, &traces, &pis),
    );
    assert!(
        DEPLOYED_VERIFIER_REFUSAL_MARKERS
            .iter()
            .any(|m| refusal.contains(m)),
        "the wire must refuse it, got: {refusal}"
    );
    println!("[polarity] …and REFUSED under ours, with the trace unchanged: {refusal}");
}

// =============================================================================================
// (d) ⚑⚑ WHAT THE DERIVATION DOES *NOT* PIN — and therefore what the manifest is still for
// =============================================================================================

/// ⚑⚑ **THE DECOMPOSITION IS NOT CANONICAL, AND THE MANIFEST IS WHAT CATCHES IT.**
///
/// `PastaMsmScalarDerive` §2.5 says the boolean digits plus the weighted sum make the reconstructed
/// value "CANONICAL rather than merely congruent mod `q`". Read at the deployed shape that is
/// **too strong**, and the gap is exactly one plane wide: booleanity pins `PR nb` into
/// `[0, 2^planes)`, and `planes = 256` while `q < 2^255`. There are therefore FIVE representatives
/// of every s-vector entry inside the digit budget — `s, s+q, s+2q, s+3q, s+4q` — and the emitted
/// chain accepts any of them, because `fqMulCore` witnesses a QUOTIENT: shifting the landing block
/// by `q` and the last quotient limb-block by `1` keeps the gate exactly zero over ℤ.
///
/// So the derivation alone binds `BIT` to *a digit of some representative*, not to the digit of
/// **the** s-vector entry. What closes it on the deployed instance is the manifest, whose digit
/// column is the canonical `sNat`. This test measures that, in the only way that distinguishes the
/// two gates — by which one fires:
///
///   * with `BIT` left honest, the JOIN refuses (`OodEvaluationMismatch`) — the row's own digits no
///     longer agree with the digit it declares;
///   * with `BIT` moved to the non-canonical representative's digits (so the row is INTERNALLY
///     consistent, the fold rebuilt around the new schedule), the LOOKUP refuses
///     (`LookupError`) — and nothing else does.
///
/// The second refusal is the manifest's alone. **That is why the manifest is kept**, and it is a
/// stronger reason than "belt and braces": delete it and this forgery has a satisfying trace.
#[test]
fn the_decomposition_is_not_canonical_and_the_manifest_is_what_catches_it() {
    let descs = parse_cut();
    let a = chals_a();
    // slice 3 (lo = 32763) — its first term's index has bit 0 set, so the LAST chain step really
    // multiplies by challenge 14 and its quotient is nonzero, which is what makes `quot − 1` a
    // witness at all. At `gidx` with bit 0 clear the last multiplier is the field ONE and the
    // chain's last step does not reduce.
    let slice = 3usize;
    let lo = W * KS[slice];
    assert_eq!(lo & 1, 1, "the chosen slice's first index must be odd");
    let s = derive_scalar(&a, lo);
    let (s2, carry) = s.adc(&Q_PASTA);
    assert!(!carry, "s + q must fit the 256 digit budget");
    let differing: Vec<usize> = (0..PLANES)
        .filter(|p| s.bit(PLANES - 1 - p) != s2.bit(PLANES - 1 - p))
        .collect();
    assert!(
        !differing.is_empty(),
        "s and s+q must differ somewhere in the digit budget"
    );
    println!(
        "[canon] s and s+q are BOTH inside the {PLANES}-bit budget and differ at {} of {PLANES} \
         planes — the digits alone do not name a representative",
        differing.len()
    );

    let noncanon = Fill {
        wire: &a,
        derived: &a,
        noncanonical_at: Some(lo),
    };

    // --- (i) BIT honest: the JOIN refuses ------------------------------------------------------
    {
        let mut traces = Vec::new();
        let mut pis = Vec::new();
        for (i, k) in KS.iter().enumerate() {
            let fill = if i == slice {
                noncanon
            } else {
                honest_fill(&a)
            };
            let (t, p) = slice_trace(
                manifest_of(&descs[i]),
                *k,
                &Pt::INFINITY,
                fill,
                None,
                i != slice,
            );
            traces.push(t);
            pis.push(p);
        }
        let refusal = must_refuse(
            "a non-canonical representative with an honest digit",
            || prove_cut(&descs, &traces, &pis),
        );
        assert!(
            refusal.contains("OodEvaluationMismatch"),
            "the JOIN should be what fires here, got: {refusal}"
        );
        println!("[canon] REFUSED by the JOIN (BIT still the manifest's): {refusal}");
    }

    // --- (ii) BIT moved to the non-canonical digits: only the LOOKUP refuses --------------------
    {
        let mut traces = Vec::new();
        let mut pis = Vec::new();
        for (i, k) in KS.iter().enumerate() {
            let manifest = manifest_of(&descs[i]);
            if i != slice {
                let (t, p) = slice_trace(manifest, *k, &Pt::INFINITY, honest_fill(&a), None, true);
                traces.push(t);
                pis.push(p);
                continue;
            }
            // Rebuild the schedule around the NON-CANONICAL digits, so the RCB fold, the selector
            // and the whole row template stay honest and only the declared digit is out of step.
            let mut sched = schedule_of(manifest);
            let mut moved = 0usize;
            for (row_index, spec) in sched.iter_mut().enumerate() {
                if row_index % (W + 1) == 0 {
                    continue;
                }
                let gidx = lo + row_index % (W + 1) - 1;
                if gidx != lo {
                    continue;
                }
                let plane = row_index / (W + 1);
                if let RowSpec::CondAdd { src, .. } = *spec {
                    let want = s2.bit(PLANES - 1 - plane) == 1;
                    if want != matches!(*spec, RowSpec::CondAdd { bit: true, .. }) {
                        moved += 1;
                    }
                    *spec = RowSpec::CondAdd { src, bit: want };
                }
            }
            assert_eq!(
                moved,
                differing.len(),
                "the moved digits are the differing ones"
            );
            let hi = lo + W;
            let t = widen_derive(build_trace(&Pt::INFINITY, &sched), lo, hi, noncanon, false);
            let p = public_inputs_of(&t, lo, hi, &a);
            traces.push(t);
            pis.push(p);
        }
        let refusal = must_refuse(
            "an INTERNALLY CONSISTENT non-canonical representative",
            || prove_cut(&descs, &traces, &pis),
        );
        assert!(
            refusal.contains("LookupError"),
            "ONLY the manifest lookup should be able to catch this, got: {refusal}"
        );
        println!(
            "[canon] REFUSED by the MANIFEST alone (the row is internally consistent): {refusal}"
        );
    }
}

// =============================================================================================
// (e) controls
// =============================================================================================

/// THE CONTROL. Without this the four red tampers prove only that something is broken.
#[test]
fn honest_derived_cut_still_proves() {
    let descs = parse_cut();
    let a = chals_a();
    let (traces, pis) = honest_cut(&a);
    prove_cut(&descs, &traces, &pis).expect("the honest derived cut must prove");
}

/// An all-zeros cut must be refused — this path's own falsifier for the release-mode fail-open
/// class. Note it is NOT any of the four tampers: an all-zeros trace fails the lookup, the index
/// threads and the derivation at once.
#[test]
fn all_zeros_derived_cut_is_refused() {
    let descs = parse_cut();
    let zeros: Vec<Vec<Vec<BabyBear>>> =
        vec![vec![vec![BabyBear::ZERO; DERIVE_WIDTH]; HEIGHT]; KS.len()];
    let pis = vec![vec![BabyBear::ZERO; DERIVE_PI_COUNT]; KS.len()];
    let refusal = must_refuse("an all-zeros derived cut", || {
        prove_cut(&descs, &zeros, &pis)
    });
    assert!(
        refusal.contains("self-verify failed"),
        "the producer must refuse an all-zeros cut in EVERY profile, got: {refusal}"
    );
}
