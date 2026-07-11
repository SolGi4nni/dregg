//! Turn-wide CROSS-CELL value-conservation AIR (Σδ=0), emitted from Lean (law #1).
//!
//! ## The gap this closes (foolable gap #6)
//!
//! The deployed rotated per-cell proof forces the *per-cell* balance arithmetic + the per-cell
//! signed NET_DELTA public input (`crate::effect_vm::pi::{NET_DELTA_MAG, NET_DELTA_SIGN}` — the
//! `(magnitude, sign)` pair `extract_net_delta` reads back as a signed `i64`). It does NOT force
//! the *turn-wide cross-cell* pairing: a single-cell sovereign proof cannot conclude that no value
//! was MINTED across the whole turn. The cross-cell debit↔credit cancellation is reconstructed
//! OFF-AIR. So a prover could publish a turn whose cell A proof shows `−10` and cell B proof shows
//! `+999`, with no declared mint, and nothing in-circuit forces `Σδ = 0` across them.
//!
//! This AIR realizes the abstract `Dregg2.Spec.Conservation.conservedInDomain` (`deltas.sum = 0`)
//! as a CONCRETE aggregation over the per-cell proofs' published signed NET_DELTA PIs.
//!
//! ## The construction (mirrors `bilateral_aggregation_air::CrossSideExistenceAir`, over SIGNED
//! CELL DELTAS rather than edge fingerprints)
//!
//! A turn touches N cells. Each per-cell proof publishes a signed delta `δ = sign·mag`
//! (`sign ∈ {+1,−1}` from `NET_DELTA_SIGN`, `mag` from `NET_DELTA_MAG`, both already range-checked
//! in the per-cell proof). The aggregation trace has one row per contributing delta:
//!
//! ```text
//!   [0]  asset    — the asset / issuer-cell class this delta moves (AssetId := issuer-cell). All
//!                   contributing rows of one aggregation proof share the published pi[asset].
//!   [1]  mag      — |δ|, the per-cell NET_DELTA_MAG (range-checked < 2^30 in the per-cell proof).
//!   [2]  sign     — +1 (credit / inflow / mint) or −1 (debit / outflow / burn).
//!   [3]  present  — 1 for a real contributing row, 0 for padding.
//!   [4]  balance  — running signed prefix sum  balance[i] = balance[i-1] + sign[i]·mag[i].
//! ```
//!
//! The boundary pins `balance[last] = 0`: for ONE asset, the sum of every per-cell signed NET_DELTA
//! (plus the declared ±supply of any mint/burn rows) is zero. A matched honest transfer (A −10,
//! B +10) cancels; a forged turn (A −10, B +999, no declared mint) leaves `+989` and the boundary
//! rejects. Mint/burn are NOT a hole — they enter as explicit rows carrying their declared ±amount.
//!
//! ## The live-wire seam (ADDITIVE — NOT wired)
//!
//! This descriptor is BUILT + PROVED here, ADDITIVE. It is NOT invoked by the deployed
//! `turn/src/executor/proof_verify.rs`. The live verifier wiring is the main loop's serialized
//! handoff:
//!
//! > After verifying the N per-cell rotated proofs of a turn (`proof_verify.rs`'s per-cell verify
//! > loop), the verifier would, FOR EACH asset class touched by the turn: collect each per-cell
//! > proof's `(pi[NET_DELTA_MAG], pi[NET_DELTA_SIGN], asset_class)` into a
//! > `Vec<CrossCellDelta>`, append the turn's declared mint/burn supply-change effects as
//! > additional signed rows, call [`build_cross_cell_conservation_trace`] + [`prove_cross_cell_conservation`],
//! > and require [`verify_cross_cell_conservation`] to accept. The per-asset partition (pi[asset])
//! > makes a multi-asset turn run one aggregation proof per asset.
//!
//! The Lean twin is `metatheory/Dregg2/Circuit/CrossCellConservation.lean` (the v2 multi-limb
//! descriptor + the derived-conservation teeth `ccc_reconC_eq_creditSum` / `ccc_conserves` /
//! `ccc_psum_forgery_unsat`).

use crate::field::BabyBear;

// ---------------------------------------------------------------------------
// Lean-emitted descriptor (law #1): the cross-cell-conservation AIR, as a PROVED
// `EffectVmDescriptor2` (`Dregg2/Circuit/CrossCellConservation.lean`).
//
// **v2 MULTI-LIMB revision (wrap-class fix #3).** The v1 descriptor summed the running balance as a
// SINGLE BabyBear felt mod p and pinned `balance[last]=0`; two 30-bit credits summing to exactly
// `p ≡ 0` (`mag₁=1006632961, mag₂=1006632960`) forged value-conservation (minted ≈2·10⁹, no debit).
// v2 splits each row's signed delta into a NON-NEGATIVE credit / debit contribution and accumulates
// each into its own running 3×15-bit-limb value with per-row carry propagation (mirrors the vault's
// 15-bit limbs). Every limb + carry is range-checked `< 2^15`, so each transition residual is a sum
// of `< 2^15` terms (`< 2^17 < p`) — the field gate lifts to an EXACT-ℤ limb recurrence, NO wrap. The
// `.last` boundary pins the final credit limbs equal to the final debit limbs, so `Σ credits =
// Σ debits` over ℤ. The `2^45` ceiling exceeds the old `~2^31` honest range (no liveness loss) and
// fails CLOSED. Twin: `metatheory/Dregg2/Circuit/CrossCellConservation.lean` (`ccc_conserves`,
// `ccc_psum_forgery_unsat`).
// ---------------------------------------------------------------------------

/// The byte-pinned Lean emission of the cross-cell-conservation descriptor
/// (`emitVmJson2 crossCellConservationDescriptor`). Width 172, ONE public input (the asset class), NO
/// declared tables, an empty legacy range carrier (self-contained bit-decomposition range gates).
/// Re-emit via `lake env lean --run EmitCrossCellConservation.lean`; the shape is pinned by
/// `cross_cell_conservation_descriptor_matches_lean_pinned_shape`.
pub const CROSS_CELL_CONSERVATION_DESCRIPTOR_JSON: &str =
    include_str!("../descriptors/dregg-cross-cell-conservation-v2.json");

/// The descriptor's wire identity (matches `crossCellConservationDescriptor.name`).
pub const CROSS_CELL_CONSERVATION_DESCRIPTOR_NAME: &str = "dregg-cross-cell-conservation-v2";

// ---------------------------------------------------------------------------
// Trace column + PI layout (mirrors the Lean `Ccc.*` constants). v2 MULTI-LIMB.
// ---------------------------------------------------------------------------

/// Trace column: asset / issuer-cell class.
pub const CCC_ASSET_COL: usize = 0;
/// Trace column: the per-cell NET_DELTA magnitude `|δ|`.
pub const CCC_MAG_COL: usize = 1;
/// Trace column: the per-cell NET_DELTA sign (+1 / −1 / 0 on padding).
pub const CCC_SIGN_COL: usize = 2;
/// Trace column: 1 for a real contributing row, 0 for padding.
pub const CCC_PRESENT_COL: usize = 3;
/// Credit contribution limbs (`= mag` limbs on a credit row, else 0).
pub const CCC_CC0: usize = 4;
pub const CCC_CC1: usize = 5;
/// Debit contribution limbs.
pub const CCC_DC0: usize = 6;
pub const CCC_DC1: usize = 7;
/// Running credit accumulator (3×15-bit limbs).
pub const CCC_C0: usize = 8;
pub const CCC_C1: usize = 9;
pub const CCC_C2: usize = 10;
/// Running debit accumulator.
pub const CCC_D0: usize = 11;
pub const CCC_D1: usize = 12;
pub const CCC_D2: usize = 13;
/// Credit / debit add carries (each a bit).
pub const CCC_KC0: usize = 14;
pub const CCC_KC1: usize = 15;
pub const CCC_KD0: usize = 16;
pub const CCC_KD1: usize = 17;
/// First range-check bit column.
pub const CCC_BIT_BASE: usize = 18;
/// Total trace width (18 core + 10 limbs × 15 bits + 4 carries × 1 bit).
pub const CCC_WIDTH: usize = 172;

/// The ordered range-checked (column, bit-width) specs — the bit blocks are laid out from
/// [`CCC_BIT_BASE`] in THIS order, in lockstep with the Lean `rangeSpecs`.
pub const CCC_RANGE_SPECS: [(usize, usize); 14] = [
    (CCC_CC0, 15),
    (CCC_CC1, 15),
    (CCC_DC0, 15),
    (CCC_DC1, 15),
    (CCC_C0, 15),
    (CCC_C1, 15),
    (CCC_C2, 15),
    (CCC_D0, 15),
    (CCC_D1, 15),
    (CCC_D2, 15),
    (CCC_KC0, 1),
    (CCC_KC1, 1),
    (CCC_KD0, 1),
    (CCC_KD1, 1),
];

/// Public input: the asset / issuer-cell class.
pub const CCC_PI_ASSET: usize = 0;
/// Public input count.
pub const CCC_PI_COUNT: usize = 1;

/// Parse the byte-pinned Lean descriptor into an [`crate::descriptor_ir2::EffectVmDescriptor2`].
/// The prover/verifier route through `descriptor_ir2::{prove,verify}_vm_descriptor2` against THIS
/// descriptor — no Rust-authored constraint semantics (law #1). Fail-closed on any parse error.
pub fn cross_cell_conservation_descriptor() -> crate::descriptor_ir2::EffectVmDescriptor2 {
    crate::descriptor_ir2::parse_vm_descriptor2(CROSS_CELL_CONSERVATION_DESCRIPTOR_JSON)
        .expect("pinned cross-cell-conservation descriptor JSON must parse (Lean golden)")
}

// ---------------------------------------------------------------------------
// Witness construction.
// ---------------------------------------------------------------------------

/// One per-cell (or declared mint/burn) signed delta contributing to the turn-wide conservation.
/// The verifier builds this from each per-cell proof's `(NET_DELTA_MAG, NET_DELTA_SIGN)` PI pair
/// (or from a declared supply-change effect's ±amount).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CrossCellDelta {
    /// The asset / issuer-cell class this delta moves (all deltas of one aggregation proof share
    /// the same asset — the per-asset partition).
    pub asset: BabyBear,
    /// `|δ|`, the per-cell NET_DELTA magnitude (already range-checked in the per-cell proof).
    pub magnitude: u32,
    /// `true` = credit / inflow / mint (sign +1); `false` = debit / outflow / burn (sign −1).
    pub credit: bool,
}

impl CrossCellDelta {
    /// The signed delta as an `i64` (the `extract_net_delta` convention: credit = +, debit = −).
    pub fn signed(&self) -> i64 {
        if self.credit {
            self.magnitude as i64
        } else {
            -(self.magnitude as i64)
        }
    }

    /// Build a delta from a per-cell proof's published NET_DELTA PI pair (the off-AIR projection the
    /// live verifier would run). `mag_pi` = `pi[NET_DELTA_MAG]`, `sign_pi` = `pi[NET_DELTA_SIGN]`
    /// (0 = credit, 1 = debit — matching `encode_net_delta`).
    pub fn from_net_delta_pi(asset: BabyBear, mag_pi: BabyBear, sign_pi: BabyBear) -> Self {
        CrossCellDelta {
            asset,
            magnitude: mag_pi.0,
            credit: sign_pi.0 == 0,
        }
    }
}

/// The signed BabyBear of a sign bit: +1 for credit, `p - 1` (== −1) for debit.
fn sign_felt(credit: bool) -> BabyBear {
    if credit {
        BabyBear::ONE
    } else {
        BabyBear::ZERO - BabyBear::ONE
    }
}

/// Build the cross-cell-conservation trace from an ordered list of signed deltas (one per
/// contributing cell + declared supply-change row), returning `(trace, public_inputs)`. The PI is
/// `[asset]` (the partition class — read from the first delta; all deltas must share it).
///
/// **v2 MULTI-LIMB.** Each row splits its delta into a non-negative credit / debit contribution
/// (`cc/dc`, each 2×15-bit limbs) and advances a running 3×15-bit-limb credit and debit accumulator
/// with per-row carry propagation — computed over INTEGERS (`u64`), NOT mod `p`, so the running sums
/// never wrap. The bit columns hold the 15-bit / 1-bit decompositions of every limb + carry (the
/// self-contained range gates). The trace is padded to the next power of two with `present = 0`
/// INERT rows (contributions + carries `0`), guaranteeing at least ONE trailing inert (wrap) row so
/// the `.last` boundary sees the accumulators carried forward unchanged; the final credit / debit
/// limbs are pinned EQUAL there iff `Σ credits = Σ debits`.
///
/// If the running credit or debit total for the asset exceeds `2^45` the top-limb overflow makes a
/// `C2`/`D2` limb fall out of `[0, 2^15)`; the range gate then rejects (fail-closed) — an
/// astronomically high ceiling that exceeds the v1 design's `~2^31` honest range.
///
/// Panics if `deltas` is empty (a turn touches at least one cell) or if the deltas disagree on the
/// asset class (one aggregation proof certifies ONE asset — the caller partitions by asset).
pub fn build_cross_cell_conservation_trace(
    deltas: &[CrossCellDelta],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    assert!(
        !deltas.is_empty(),
        "cross-cell conservation needs at least one delta row"
    );
    let asset = deltas[0].asset;
    assert!(
        deltas.iter().all(|d| d.asset == asset),
        "all deltas of one aggregation proof must share the asset class (partition by asset)"
    );

    let n_active = deltas.len();
    // At least one TRAILING inert row (so `len - 1` is a wrap row): `+1` before the power-of-two.
    let n_padded = (n_active + 1).max(2).next_power_of_two();
    let mut trace: Vec<Vec<BabyBear>> = Vec::with_capacity(n_padded);

    // Previous-row accumulator limbs (seeded at 0, so row 0 satisfies the seed boundary).
    let (mut pc0, mut pc1, mut pc2) = (0u32, 0u32, 0u32);
    let (mut pd0, mut pd1, mut pd2) = (0u32, 0u32, 0u32);

    for i in 0..n_padded {
        let (present, credit, mag) = if i < n_active {
            (1u32, deltas[i].credit, deltas[i].magnitude)
        } else {
            (0u32, false, 0u32)
        };

        // Credit / debit contribution (a present row's `mag` goes to exactly one side).
        let (cc, dc) = if present == 1 {
            if credit { (mag, 0u32) } else { (0u32, mag) }
        } else {
            (0u32, 0u32)
        };
        let (cc0, cc1) = (cc & 0x7fff, cc >> 15);
        let (dc0, dc1) = (dc & 0x7fff, dc >> 15);

        // Carry-propagated limb addition: acc_k = prev_k + contrib_k (+carry), 15-bit-normalized.
        let s0 = pc0 + cc0;
        let (kc0, c0) = (s0 >> 15, s0 & 0x7fff);
        let s1 = pc1 + cc1 + kc0;
        let (kc1, c1) = (s1 >> 15, s1 & 0x7fff);
        let c2 = (pc2 + kc1) & 0x7fff; // top carry dropped: >2^45 total ⟹ C2 ∉ [0,2^15) ⟹ range rejects

        let t0 = pd0 + dc0;
        let (kd0, dd0) = (t0 >> 15, t0 & 0x7fff);
        let t1 = pd1 + dc1 + kd0;
        let (kd1, dd1) = (t1 >> 15, t1 & 0x7fff);
        let dd2 = (pd2 + kd1) & 0x7fff;

        let mut row = vec![BabyBear::ZERO; CCC_WIDTH];
        row[CCC_ASSET_COL] = asset;
        row[CCC_MAG_COL] = BabyBear::new(mag);
        row[CCC_SIGN_COL] = if present == 1 {
            sign_felt(credit)
        } else {
            BabyBear::ZERO
        };
        row[CCC_PRESENT_COL] = BabyBear::new(present);
        row[CCC_CC0] = BabyBear::new(cc0);
        row[CCC_CC1] = BabyBear::new(cc1);
        row[CCC_DC0] = BabyBear::new(dc0);
        row[CCC_DC1] = BabyBear::new(dc1);
        row[CCC_C0] = BabyBear::new(c0);
        row[CCC_C1] = BabyBear::new(c1);
        row[CCC_C2] = BabyBear::new(c2);
        row[CCC_D0] = BabyBear::new(dd0);
        row[CCC_D1] = BabyBear::new(dd1);
        row[CCC_D2] = BabyBear::new(dd2);
        row[CCC_KC0] = BabyBear::new(kc0);
        row[CCC_KC1] = BabyBear::new(kc1);
        row[CCC_KD0] = BabyBear::new(kd0);
        row[CCC_KD1] = BabyBear::new(kd1);

        // Range-check bit decompositions, in `CCC_RANGE_SPECS` order from `CCC_BIT_BASE`.
        let range_vals: [(u32, usize); 14] = [
            (cc0, 15),
            (cc1, 15),
            (dc0, 15),
            (dc1, 15),
            (c0, 15),
            (c1, 15),
            (c2, 15),
            (dd0, 15),
            (dd1, 15),
            (dd2, 15),
            (kc0, 1),
            (kc1, 1),
            (kd0, 1),
            (kd1, 1),
        ];
        let mut b = CCC_BIT_BASE;
        for (val, nbits) in range_vals {
            for j in 0..nbits {
                row[b + j] = BabyBear::new((val >> j) & 1);
            }
            b += nbits;
        }

        trace.push(row);
        pc0 = c0;
        pc1 = c1;
        pc2 = c2;
        pd0 = dd0;
        pd1 = dd1;
        pd2 = dd2;
    }

    let pi = vec![asset];
    (trace, pi)
}

/// Prove the cross-cell conservation through the Lean-emitted descriptor (law #1): the 5-col
/// trace satisfies `cross_cell_conservation_descriptor()` against the `[asset]` PI, via the
/// multi-table batch STARK. No tables/memory/maps are committed (the descriptor is pure row-window
/// arithmetic). Fail-closed on prove error.
pub fn prove_cross_cell_conservation(
    trace: &[Vec<BabyBear>],
    pi: &[BabyBear],
) -> Result<crate::descriptor_ir2::Ir2BatchProof<crate::descriptor_ir2::DreggStarkConfig>, String> {
    let desc = cross_cell_conservation_descriptor();
    crate::descriptor_ir2::prove_vm_descriptor2(
        &desc,
        trace,
        pi,
        &crate::descriptor_ir2::MemBoundaryWitness::default(),
        &[],
    )
}

/// Verify a cross-cell-conservation proof against the Lean descriptor + the `[asset]` PI.
/// Prover-free (`verifier` feature). Fail-closed on verify error.
pub fn verify_cross_cell_conservation(
    proof: &crate::descriptor_ir2::Ir2BatchProof<crate::descriptor_ir2::DreggStarkConfig>,
    pi: &[BabyBear],
) -> Result<(), String> {
    let desc = cross_cell_conservation_descriptor();
    crate::descriptor_ir2::verify_vm_descriptor2(&desc, proof, pi)
}

/// The signed last-row balance of a delta list (`Σ sign·mag`), as the verifier-side pre-flight the
/// trace builder's prefix sum forces. A turn conserves (for this asset) iff this is zero. The
/// live verifier would pre-flight this before proving (the debug batch prover panics on an
/// unsatisfiable trace), exactly as `prove_cross_side_existence` pre-flights the cross-side balance.
pub fn cross_cell_balance(deltas: &[CrossCellDelta]) -> i64 {
    deltas.iter().map(CrossCellDelta::signed).sum()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn delta(asset: u32, mag: u32, credit: bool) -> CrossCellDelta {
        CrossCellDelta {
            asset: BabyBear::new(asset),
            magnitude: mag,
            credit,
        }
    }

    /// The trace is UNSATISFIABLE iff proving rejects it (the debug batch prover panics or errors on
    /// an unsatisfiable trace, or a produced proof fails verify). Returns `true` when REJECTED.
    fn is_unsat(trace: &[Vec<BabyBear>], pi: &[BabyBear]) -> bool {
        let proved = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_cross_cell_conservation(trace, pi)
        }));
        match proved {
            Err(_) => true,
            Ok(Err(_)) => true,
            Ok(Ok(proof)) => verify_cross_cell_conservation(&proof, pi).is_err(),
        }
    }

    /// The byte-pinned descriptor parses and carries the v2 Lean-pinned shape (`#guard`s in
    /// `CrossCellConservation.lean`): width 172, PI 1, NO tables, an empty range carrier, SIX window
    /// gates (the 3+3 credit/debit limb transitions), NO chip lookups, name
    /// `dregg-cross-cell-conservation-v2`. Law-#1 tooth: a drift from the Lean golden is a hard failure.
    #[test]
    fn cross_cell_conservation_descriptor_matches_lean_pinned_shape() {
        use crate::descriptor_ir2::VmConstraint2;
        let d = cross_cell_conservation_descriptor();
        assert_eq!(d.name, CROSS_CELL_CONSERVATION_DESCRIPTOR_NAME);
        assert_eq!(d.trace_width, CCC_WIDTH);
        assert_eq!(d.trace_width, 172);
        assert_eq!(d.public_input_count, CCC_PI_COUNT);
        assert_eq!(d.public_input_count, 1);
        assert!(d.tables.is_empty(), "no committed tables");
        assert!(
            d.ranges.is_empty(),
            "v2 assembly requires the legacy range carrier empty (self-contained bit gates)"
        );
        assert_eq!(
            d.constraints.len(),
            201,
            "the Lean emission pins 201 constraints"
        );
        let window_gates = d
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
            .count();
        assert_eq!(
            window_gates, 6,
            "the 3 credit + 3 debit limb-transition window gates"
        );
        let chip_lookups = d
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Lookup(_)))
            .count();
        assert_eq!(
            chip_lookups, 0,
            "no chip lookups: self-contained bit-decomposition range gates"
        );
    }

    /// LIVENESS (end-to-end, law #1): an honest matched transfer (A −10, B +10) proves + verifies
    /// through the LEAN v2 descriptor batch prover; a tampered asset PI does NOT verify.
    #[test]
    fn honest_transfer_proves_rejects_wrong_asset() {
        let honest = vec![delta(7, 10, false), delta(7, 10, true)];
        assert_eq!(cross_cell_balance(&honest), 0);
        let (trace, pi) = build_cross_cell_conservation_trace(&honest);
        // final credit accumulator == final debit accumulator (conservation).
        let last = trace.last().unwrap();
        assert_eq!(last[CCC_C0], last[CCC_D0]);
        assert_eq!(last[CCC_C1], last[CCC_D1]);
        assert_eq!(last[CCC_C2], last[CCC_D2]);
        let proof = prove_cross_cell_conservation(&trace, &pi)
            .expect("honest conserving turn must prove through the v2 descriptor");
        verify_cross_cell_conservation(&proof, &pi)
            .expect("honest conserving turn proof must verify");

        let mut bad_pi = pi.clone();
        bad_pi[CCC_PI_ASSET] = bad_pi[CCC_PI_ASSET] + BabyBear::ONE;
        assert!(
            verify_cross_cell_conservation(&proof, &bad_pi).is_err(),
            "tampered asset PI must reject (the per-asset partition)"
        );
    }

    /// LIVENESS beyond `p`: a balanced turn whose per-asset credit / debit TOTAL is `2·(2^30−1) ≈
    /// 2^31 > p` — which the v1 single-felt sum WOULD HAVE WRAPPED — proves fine under the multi-limb
    /// accumulator (the `2^45` ceiling; no liveness degradation vs the old `~2^31` honest range).
    #[test]
    fn balanced_sum_exceeding_p_proves() {
        let big = 1_073_741_823u32; // 2^30 − 1
        let turn = vec![
            delta(7, big, true),
            delta(7, big, true),
            delta(7, big, false),
            delta(7, big, false),
        ];
        assert_eq!(cross_cell_balance(&turn), 0);
        let (trace, pi) = build_cross_cell_conservation_trace(&turn);
        let last = trace.last().unwrap();
        // the running credit total reached 2^31 > p, yet the limbs match debit's — no wrap.
        assert_eq!(last[CCC_C0], last[CCC_D0]);
        assert_eq!(last[CCC_C1], last[CCC_D1]);
        assert_eq!(last[CCC_C2], last[CCC_D2]);
        let proof = prove_cross_cell_conservation(&trace, &pi)
            .expect("balanced turn with total > p must prove (multi-limb, no wrap)");
        verify_cross_cell_conservation(&proof, &pi).expect("must verify");
    }

    /// SOUNDNESS — **THE `p`-SUM FORGERY (wrap-class #3) IS NOW UNSAT.** Two credit rows
    /// `mag₁ = 1006632961`, `mag₂ = 1006632960` (both `< 2^30`) whose true integer sum is EXACTLY
    /// `p = 2013265921`, with NO debit. Under the v1 single-felt design `balance[last] = p ≡ 0`
    /// accepted (minted ≈2·10⁹). Under v2 the credit accumulator reconstructs `p` in limbs
    /// `(1, 28672, 1)` — NONZERO — while the debit accumulator is `(0,0,0)`, so the `.last` equality
    /// boundary `C_k = D_k` is violated: the trace is UNSATISFIABLE. (Lean twin: `ccc_psum_forgery_unsat`.)
    #[test]
    fn psum_forgery_is_unsat() {
        let mag1 = 1_006_632_961u32;
        let mag2 = 1_006_632_960u32;
        assert!(
            mag1 < (1 << 30) && mag2 < (1 << 30),
            "both magnitudes are honest 30-bit values"
        );
        assert_eq!(
            mag1 as u64 + mag2 as u64,
            2_013_265_921,
            "they sum to EXACTLY p"
        );
        // the i64 pre-flight sees the true sum (no field wrap): a nonzero credit surplus.
        let forged = vec![delta(7, mag1, true), delta(7, mag2, true)];
        assert_eq!(cross_cell_balance(&forged), 2_013_265_921);

        let (trace, pi) = build_cross_cell_conservation_trace(&forged);
        let last = trace.last().unwrap();
        // the derived credit limbs reconstruct p (nonzero) while debit limbs are 0 — NOT equal.
        assert_eq!(last[CCC_C0], BabyBear::new(1));
        assert_eq!(last[CCC_C1], BabyBear::new(28672));
        assert_eq!(last[CCC_C2], BabyBear::new(1));
        assert_eq!(last[CCC_D0], BabyBear::ZERO);
        assert_ne!(
            last[CCC_C0], last[CCC_D0],
            "credit limbs ≠ debit limbs: no p-wrap masquerade"
        );

        assert!(
            is_unsat(&trace, &pi),
            "the p-sum forgery must be UNSATISFIABLE (the wrap the v1 single-felt sum admitted)"
        );

        // non-vacuity: the honest counterpart (both magnitudes matched by equal debits) proves.
        let honest = vec![
            delta(7, mag1, true),
            delta(7, mag2, true),
            delta(7, mag1, false),
            delta(7, mag2, false),
        ];
        let (htrace, hpi) = build_cross_cell_conservation_trace(&honest);
        let hproof =
            prove_cross_cell_conservation(&htrace, &hpi).expect("honest balanced turn must prove");
        verify_cross_cell_conservation(&hproof, &hpi).expect("must verify");
    }

    /// SOUNDNESS: an ordinary unbalanced turn (A −10, B +999, no declared mint) is UNSAT (credit 999
    /// ≠ debit 10); the disclosed-supply counterpart (A −10, B +999, supply −989) conserves + proves.
    #[test]
    fn unbalanced_unsat_disclosed_mint_proves() {
        let forged = vec![delta(7, 10, false), delta(7, 999, true)];
        assert_eq!(cross_cell_balance(&forged), 989);
        let (ft, fpi) = build_cross_cell_conservation_trace(&forged);
        assert!(is_unsat(&ft, &fpi), "unbalanced turn must be UNSAT");

        let disclosed = vec![
            delta(7, 10, false),
            delta(7, 999, true),
            delta(7, 989, false),
        ];
        assert_eq!(cross_cell_balance(&disclosed), 0);
        let (dt, dpi) = build_cross_cell_conservation_trace(&disclosed);
        let proof = prove_cross_cell_conservation(&dt, &dpi)
            .expect("disclosed-mint turn conserves + proves");
        verify_cross_cell_conservation(&proof, &dpi).expect("must verify");
    }
}
