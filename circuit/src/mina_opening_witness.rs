//! # `mina_opening_witness` — the WITNESS BUILDER for Mina's `⟨s, srs.g⟩` opening leg.
//!
//! ## Substrate, said out loud
//!
//! **The AIR is Lean-authored.** `dregg-pasta-rcb-sg-derive-<k>-of-10922::v1` is
//! `Dregg2.Circuit.Emit.PastaMsmScalarDerive.deriveRowDesc 15 10922 k 3 256 MinaWrapSrsG.SRS_G
//! (SCAL …)` — 1309 constraints / 2131 columns / 164 public inputs, emitted by
//! `metatheory/EmitPastaDerive.lean`. **Nothing in this file authors a constraint, a `Builder`
//! gadget or an `air_accepts` predicate.** It parses the emitted descriptor's manifest, fills
//! trace CELLS, and assembles public inputs. Every arithmetic helper it calls
//! ([`crate::pasta_windowed_witness::put_derive_block`], `build_trace`, `mul_mod_q`) already
//! existed for the same reason.
//!
//! ## Why this is a library module and not a test helper
//!
//! Until 2026-07-30 every line below lived inside `circuit/tests/pasta_derive_prove.rs`, so the
//! Mina opening AIR was reachable from **no runtime path at all** — a proof dregg could produce
//! and nothing could ask for. `bridge::mina_opening_check` is the caller that closes that; this
//! module is the one builder both it and the test use, so there is no twin to drift.
//!
//! ## What a caller supplies, and what is forced
//!
//! The 15 IPA challenges are **public inputs** (slots 29..163), not descriptor data:
//! `PastaMsmScalarDerive.chalPinGates` binds them to the wire, so the party that supplies them is
//! the VERIFIER. [`build_opening_cut`] therefore takes them as an argument, and
//! [`check_manifest_is_derived_s_vector`] recomputes the descriptor's whole digit column from them
//! before any proof is attempted — so a challenge vector that did not produce that manifest is a
//! REFUSAL at witness-build time rather than a mysterious prover error.

use crate::BabyBear;
use crate::descriptor_ir2::{EffectVmDescriptor2, TableSem};
use crate::pasta_windowed_witness::{
    CBITS, COL_ACCX, COL_ACCY, COL_ACCZ, COL_BIT, COL_DBL, COL_OC_ACC, COL_OC_SRC, COL_SRCX,
    COL_SRCY, COL_SRCZ, DeriveLayout, NUM_LIMBS, Pt, Q_PASTA, RowSpec, SLICED_PI_COUNT,
    TRACE_WIDTH, U256, build_trace, derive_scalar, mul_mod_q, put_derive_block, put_on_curve_block,
    put_on_curve_block_forged, read_point,
};

// ---------------------------------------------------------------------------------------------
// The emitted shape. `EmitPastaDerive.lean`'s kernel `#guard`s carry the same numbers, and
// `bridge::mina_opening_check` re-asserts every one of them against the parsed descriptor.
// ---------------------------------------------------------------------------------------------

/// The challenge count (`nb`) — the Wrap index's IPA round count.
pub const NB: usize = 15;
/// The bit-plane count. An s-vector entry is a Pallas SCALAR, so 256 is the first admissible
/// power of two; it is not a knob.
pub const PLANES: usize = 256;
/// Generators per slice (`w`).
pub const W: usize = 3;
/// The slice count the full 32,768-point Wrap SRS is cut into.
pub const N: usize = 10922;
/// ⚑ The four slices are CHOSEN, NOT TILED — absolute generator indices 0, 10920, 21843, 32763,
/// spread so the union of the index bits those rows carry is all fifteen. A cut at `k = 0..3`
/// would leave ten challenges' `b = 1` arm never once exercised.
pub const KS: [usize; 4] = [0, 3640, 7281, 10921];
/// Rows per slice — `planes · (w + 1)`, a power of two because the prover refuses anything else.
pub const HEIGHT: usize = PLANES * (W + 1);
/// `PastaMsmScalarDerive.WD`.
pub const DERIVE_WIDTH: usize = 2131;
/// `29 + 9·15`.
pub const DERIVE_PI_COUNT: usize = 164;
/// `98 on-curve + (264 + 29·15 + 2·256)`.
pub const DERIVE_CONSTRAINTS: usize = 1309;

/// `PastaMsmBound.WB` — the slice's low generator index.
pub const COL_LO: usize = 525;
/// `PastaMsmSliced.LO`/`HI` — the slice's high generator index.
pub const COL_HI: usize = 526;
/// `PastaMsmBound.TIDX` — the row index thread.
pub const COL_TIDX: usize = 527;
/// `PastaMsmBound.GIDX` — the absolute generator index thread.
pub const COL_GIDX: usize = 528;

/// The layout the emitted descriptor declares at this shape.
pub fn layout() -> DeriveLayout {
    DeriveLayout {
        nb: NB,
        planes: PLANES,
    }
}

/// The descriptor name a slice at cut index `k` must carry.
pub fn descriptor_name(k: usize) -> String {
    format!("dregg-pasta-rcb-sg-derive-{k}-of-{N}::v1")
}

// ---------------------------------------------------------------------------------------------
// The challenge vector — data, because it is a PUBLIC INPUT
// ---------------------------------------------------------------------------------------------

/// Pull the decimal challenge strings out of `{"block":N,"challenges":["…",…]}`, the shape
/// `metatheory/EmitPastaDeriveChals.lean` emits. Hand-rolled because `dregg-circuit` keeps no JSON
/// dependency at the verify floor.
///
/// Returns an error rather than panicking: this is on a runtime path.
pub fn parse_challenges(json: &str) -> Result<Vec<U256>, String> {
    const KEY: &str = "\"challenges\":[";
    let start = json
        .find(KEY)
        .ok_or_else(|| "challenge JSON has no `challenges` key".to_string())?
        + KEY.len();
    let end = json[start..]
        .find(']')
        .ok_or_else(|| "challenge JSON has an unterminated `challenges` array".to_string())?
        + start;
    let cs: Vec<U256> = json[start..end]
        .split(',')
        .map(|s| U256::from_dec(s.trim().trim_matches('"')))
        .collect();
    if cs.len() != NB {
        return Err(format!(
            "expected {NB} IPA challenges (the Wrap index's round count), got {}",
            cs.len()
        ));
    }
    for (j, c) in cs.iter().enumerate() {
        if !(*c < Q_PASTA) {
            return Err(format!(
                "challenge {j} is not a reduced Pallas scalar (>= q); no satisfying trace exists"
            ));
        }
    }
    Ok(cs)
}

// ---------------------------------------------------------------------------------------------
// The descriptor's manifest, read
// ---------------------------------------------------------------------------------------------

/// The exact-public generator table a derive descriptor declares.
pub fn manifest_of(desc: &EffectVmDescriptor2) -> Result<&Vec<Vec<u32>>, String> {
    match desc.tables.first().map(|t| &t.sem) {
        Some(TableSem::ExactPublicRows { rows }) => Ok(rows),
        Some(other) => Err(format!(
            "expected an exact-public generator table, got {other:?}"
        )),
        None => Err("descriptor declares no tables".to_string()),
    }
}

/// The generator a manifest row names, read out of its 3×9 limb block.
pub fn point_of(row: &[u32]) -> Pt {
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
pub fn schedule_of(manifest: &[Vec<u32>]) -> Vec<RowSpec> {
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

/// ⚑⚑ **THE MANIFEST IS THE DERIVED S-VECTOR, checked on the bytes, before any proof.**
///
/// Recompute `s_i = ∏_j c_j^{bit_j(i)}` from the supplied challenge vector and compare it against
/// the descriptor's own digit column, row by row. This is what makes a challenge vector *data* on
/// the runtime path rather than an article of faith: a vector that did not produce this manifest
/// is refused HERE, legibly, instead of surfacing as a `LookupError` from the prover.
///
/// Returns the number of conditional-add rows checked.
pub fn check_manifest_is_derived_s_vector(
    desc: &EffectVmDescriptor2,
    k: usize,
    chals: &[U256],
) -> Result<usize, String> {
    if chals.len() != NB {
        return Err(format!("expected {NB} challenges, got {}", chals.len()));
    }
    let manifest = manifest_of(desc)?;
    if manifest.len() != HEIGHT {
        return Err(format!(
            "manifest has {} rows, expected {HEIGHT}",
            manifest.len()
        ));
    }
    let lo = W * k;
    let mut checked = 0usize;
    for (row_index, row) in manifest.iter().enumerate() {
        if row.iter().all(|&v| v == 0) {
            continue; // a doubling row
        }
        if row.len() < 3 + 3 * NUM_LIMBS {
            return Err(format!("manifest row {row_index} is too short"));
        }
        if row[0] as usize != row_index + 1 {
            return Err(format!(
                "manifest row {row_index}: row key {} is not {}",
                row[0],
                row_index + 1
            ));
        }
        let gidx = (row[1] as usize)
            .checked_sub(1)
            .ok_or_else(|| format!("manifest row {row_index}: generator index 0 is reserved"))?;
        if !(lo..lo + W).contains(&gidx) {
            return Err(format!(
                "manifest row {row_index}: generator index {gidx} is off the slice [{lo}, {})",
                lo + W
            ));
        }
        let plane = row_index / (W + 1);
        let want = derive_scalar(chals, gidx).bit(PLANES - 1 - plane);
        if row[2] != want {
            return Err(format!(
                "manifest row {row_index}: the declared digit {} is not the derived s-vector's \
                 bit {want} at (gidx {gidx}, plane {plane}) — these challenges did not produce \
                 this descriptor",
                row[2]
            ));
        }
        checked += 1;
    }
    if checked != W * PLANES {
        return Err(format!(
            "checked {checked} conditional-add rows, expected {}",
            W * PLANES
        ));
    }
    Ok(checked)
}

// ---------------------------------------------------------------------------------------------
// The trace
// ---------------------------------------------------------------------------------------------

/// How a slice's derivation block is filled.
///
/// ⚑ THE TWO CHALLENGE VECTORS ARE SEPARATE ON PURPOSE. `wire` fills the `CHc` columns — the
/// PI-bound vector, i.e. WHAT THE VERIFIER SUPPLIES. `derived` fills the multiplier / product /
/// quotient / digit columns — what the PROVER claims. An honest fill passes the same slice twice;
/// passing two different blocks is `PastaMsmScalarDerive` §5's `katAsg cs ds`, the forgery the
/// deployed verifier refuses.
#[derive(Clone, Copy)]
pub struct OpeningFill<'a> {
    /// The challenge vector on the wire (the public inputs).
    pub wire: &'a [U256],
    /// The challenge vector the derivation columns are built from.
    pub derived: &'a [U256],
    /// ⚑ FORGERY KNOB, never set on a production path. Rewrite the chain's landing block on every
    /// row consuming this generator index to the NON-CANONICAL representative `s + q`. See
    /// [`make_noncanonical`].
    pub noncanonical_at: Option<usize>,
}

/// The honest fill: the same challenge vector on the wire and in the derivation.
pub fn honest_fill<'a>(chals: &'a [U256]) -> OpeningFill<'a> {
    OpeningFill {
        wire: chals,
        derived: chals,
        noncanonical_at: None,
    }
}

/// Write a 9x30 field element into a row.
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

/// ⚑ **FORGERY HELPER — never on a production path.** Rewrite one row's chain landing block and
/// digits to the representative `s + q`, keeping every emitted gate of the chain satisfied over ℤ.
/// Returns that representative.
///
/// The certificate columns get the BEST WITNESS THAT EXISTS, which is the whole point:
/// `q − 1 − (s + q) = −(s + 1)` is NEGATIVE, so no assignment of 255 boolean places reaches it and
/// `PastaMsmScalarDerive.canon_forces` proves there is none. What a real prover would write is the
/// 255-bit truncation `2^255 − (s + 1)`, and that is what goes in — a forgery test whose witness
/// generator simply gave up would measure nothing.
///
/// The sibling of [`crate::pasta_windowed_witness::put_on_curve_block_forged`], and public for the
/// same reason: a falsifier that cannot build the best forgery measures nothing.
#[doc(hidden)]
pub fn make_noncanonical(row: &mut [BabyBear], chals: &[U256], gidx: usize) -> U256 {
    let lay = layout();
    let nb = chals.len();
    let prev = partial_product(chals, gidx, nb - 1);
    let mu = if gidx & 1 == 1 {
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
    // `2^255 − (s + 1)`, the residue of `q − 1 − s2` in the 255-bit budget.
    let two_255 = U256([0, 0, 0, 1u64 << 63]);
    let (sp1, c1) = s.adc(&U256::ONE);
    assert!(!c1);
    let (trunc, b1) = two_255.sbb(&sp1);
    assert!(!b1);
    for p in 0..CBITS {
        row[lay.cb(p)] = BabyBear::new(trunc.bit(p));
    }
    s2
}

/// Widen a 525-column windowed trace to the derived width: the four declaration/index columns, the
/// two on-curve certificates, and the derivation block.
///
/// ⚑ The certificate written is always the BEST ONE THAT EXISTS for the point in the cells: honest
/// where the point has an inverse, and the `YINV = 0` fallback only where it has none.
///
/// `check_digits` cross-checks, at witness-build time on every conditional-add row, that the
/// descriptor's declared digit IS the derived scalar's digit at this row's own plane. If the two
/// ever disagreed the instance would have NO satisfying trace at all; this turns that into a
/// legible failure instead of a mysterious refusal. It is off only for a deliberate forgery.
pub fn widen_derive(
    trace: Vec<Vec<BabyBear>>,
    lo: usize,
    hi: usize,
    fill: OpeningFill<'_>,
    check_digits: bool,
) -> Result<Vec<Vec<BabyBear>>, String> {
    let lay = layout();
    let mut gidx: usize = 0;
    let mut out = Vec::with_capacity(trace.len());
    for (i, mut row) in trace.into_iter().enumerate() {
        if row.len() != TRACE_WIDTH {
            return Err(format!(
                "row {i} is {} wide, expected {TRACE_WIDTH}",
                row.len()
            ));
        }
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
        if check_digits && !dbl && row[COL_BIT].as_u32() != s.bit(PLANES - 1 - plane) {
            return Err(format!(
                "row {i}: the manifest's declared digit {} is not the derived s-vector's bit {} \
                 — these challenges did not produce this descriptor",
                row[COL_BIT].as_u32(),
                s.bit(PLANES - 1 - plane)
            ));
        }
        gidx = if dbl { lo } else { gidx + 1 };
        out.push(row);
    }
    Ok(out)
}

/// The public inputs a slice publishes: `[lo, hi]`, the 27 landing-accumulator limbs, and the
/// 9×15 limbs of the WIRE challenge vector.
pub fn public_inputs_of(
    trace: &[Vec<BabyBear>],
    lo: usize,
    hi: usize,
    wire: &[U256],
) -> Result<Vec<BabyBear>, String> {
    let lay = layout();
    let last = trace.last().ok_or_else(|| "empty trace".to_string())?;
    let mut pis = Vec::with_capacity(lay.pi_count());
    pis.push(BabyBear::new(lo as u32));
    pis.push(BabyBear::new(hi as u32));
    for i in 0..27 {
        pis.push(last[COL_ACCX + i]);
    }
    debug_assert_eq!(pis.len(), SLICED_PI_COUNT);
    for c in wire {
        for l in 0..NUM_LIMBS {
            pis.push(BabyBear::new(c.limb30(l)));
        }
    }
    Ok(pis)
}

/// One slice's trace and public inputs, starting from `acc0`, with an optional source-point edit
/// (a forgery knob — `None` on every production path).
pub fn slice_trace(
    manifest: &[Vec<u32>],
    k: usize,
    acc0: &Pt,
    fill: OpeningFill<'_>,
    edit: Option<(usize, Pt)>,
    check_digits: bool,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    let lo = W * k;
    let hi = lo + W;
    let mut sched = schedule_of(manifest);
    if let Some((row, src)) = edit {
        let bit = match sched.get(row) {
            Some(RowSpec::CondAdd { bit, .. }) => *bit,
            Some(RowSpec::Double) => {
                return Err("the edited row must be a conditional-add row".to_string());
            }
            None => return Err(format!("edited row {row} is past the schedule")),
        };
        sched[row] = RowSpec::CondAdd { src, bit };
    }
    if sched.len() != HEIGHT {
        return Err(format!(
            "schedule has {} rows, expected {HEIGHT}",
            sched.len()
        ));
    }
    let trace = widen_derive(build_trace(acc0, &sched), lo, hi, fill, check_digits)?;
    let pis = public_inputs_of(&trace, lo, hi, fill.wire)?;
    Ok((trace, pis))
}

/// ⚑⚑ **THE CUT.** All four honest slices' traces and public inputs, built from the descriptors
/// the caller resolved and the challenge vector the caller supplies.
///
/// This is the function a runtime path calls. It cross-checks the manifest against the challenges
/// on every slice first, so a wrong challenge vector is refused with a legible reason before the
/// prover is ever entered.
pub fn build_opening_cut(
    descs: &[EffectVmDescriptor2],
    chals: &[U256],
) -> Result<(Vec<Vec<Vec<BabyBear>>>, Vec<Vec<BabyBear>>), String> {
    if descs.len() != KS.len() {
        return Err(format!(
            "the cut is {} slices, got {} descriptors",
            KS.len(),
            descs.len()
        ));
    }
    if chals.len() != NB {
        return Err(format!("expected {NB} challenges, got {}", chals.len()));
    }
    let fill = honest_fill(chals);
    let mut traces = Vec::with_capacity(KS.len());
    let mut pis = Vec::with_capacity(KS.len());
    for (i, k) in KS.iter().enumerate() {
        check_manifest_is_derived_s_vector(&descs[i], *k, chals)?;
        let manifest = manifest_of(&descs[i])?;
        let (t, p) = slice_trace(manifest, *k, &Pt::INFINITY, fill, None, true)?;
        traces.push(t);
        pis.push(p);
    }
    Ok((traces, pis))
}

/// The cell count one cut occupies — reported by the runtime path so a cost figure is never a
/// remembered number.
pub const fn cut_cells() -> usize {
    KS.len() * HEIGHT * DERIVE_WIDTH
}
