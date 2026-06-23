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
//! The Lean twin is `metatheory/Dregg2/Circuit/CrossCellConservation.lean` (the descriptor + the
//! rejection teeth `ccc_rejects_unbalanced` / `ccc_forged_mint_unsat` / `ccc_rejects_wrong_asset`).

use crate::field::BabyBear;

// ---------------------------------------------------------------------------
// Lean-emitted descriptor (law #1): the cross-cell-conservation AIR, as a PROVED
// `EffectVmDescriptor2` (`Dregg2/Circuit/CrossCellConservation.lean`).
// ---------------------------------------------------------------------------

/// The byte-pinned Lean emission of the cross-cell-conservation descriptor
/// (`emitVmJson2 crossCellConservationDescriptor`). Width 5, ONE public input (the asset class),
/// NO declared tables (pure prefix-sum arithmetic — the signed delta IS the contribution), an empty
/// legacy range carrier (the magnitude bound is inherited from the per-cell proof). Re-emit via
/// `lake env lean --run EmitCrossCellConservation.lean`; the shape is pinned by
/// `cross_cell_conservation_descriptor_matches_lean_pinned_shape`.
pub const CROSS_CELL_CONSERVATION_DESCRIPTOR_JSON: &str =
    include_str!("../descriptors/dregg-cross-cell-conservation-v1.json");

/// The descriptor's wire identity (matches `crossCellConservationDescriptor.name`).
pub const CROSS_CELL_CONSERVATION_DESCRIPTOR_NAME: &str = "dregg-cross-cell-conservation-v1";

// ---------------------------------------------------------------------------
// Trace column + PI layout (mirrors the Lean `Ccc.*` constants).
// ---------------------------------------------------------------------------

/// Trace column: asset / issuer-cell class.
pub const CCC_ASSET_COL: usize = 0;
/// Trace column: the per-cell NET_DELTA magnitude `|δ|`.
pub const CCC_MAG_COL: usize = 1;
/// Trace column: the per-cell NET_DELTA sign (+1 / −1).
pub const CCC_SIGN_COL: usize = 2;
/// Trace column: 1 for a real contributing row, 0 for padding.
pub const CCC_PRESENT_COL: usize = 3;
/// Trace column: running signed prefix sum.
pub const CCC_BALANCE_COL: usize = 4;
/// Total trace width.
pub const CCC_WIDTH: usize = 5;

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
/// `[asset]` (the partition class — read from the first delta; all deltas must share it). Pads to
/// the next power of two with `present = 0` rows that carry the balance forward and mirror the
/// asset class (so the first/last asset `pi_binding`s hold). The off-AIR verifier re-derives the
/// identical `(trace, pi)` from the per-cell NET_DELTA PIs + the declared supply effects.
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
    let n_padded = n_active.max(2).next_power_of_two();
    let mut trace: Vec<Vec<BabyBear>> = Vec::with_capacity(n_padded);

    let mut balance = BabyBear::ZERO;
    for d in deltas {
        let mag = BabyBear::new(d.magnitude);
        let sign = sign_felt(d.credit);
        balance = balance + sign * mag;
        let mut row = vec![BabyBear::ZERO; CCC_WIDTH];
        row[CCC_ASSET_COL] = asset;
        row[CCC_MAG_COL] = mag;
        row[CCC_SIGN_COL] = sign;
        row[CCC_PRESENT_COL] = BabyBear::ONE;
        row[CCC_BALANCE_COL] = balance;
        trace.push(row);
    }

    // Padding: present = 0, sign = 0, mag = 0 → contribution `0·0 = 0`; balance carries forward; the
    // asset column mirrors the partition so the first/last asset `pi_binding`s hold.
    while trace.len() < n_padded {
        let mut row = vec![BabyBear::ZERO; CCC_WIDTH];
        row[CCC_ASSET_COL] = asset;
        row[CCC_BALANCE_COL] = balance;
        trace.push(row);
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

    /// The byte-pinned descriptor parses and carries the Lean-pinned shape (`#guard`s in
    /// `CrossCellConservation.lean`): width 5, PI 1, NO tables, EXACTLY one window gate, an empty
    /// range carrier, name `dregg-cross-cell-conservation-v1`. Law-#1 tooth: the Rust aggregation
    /// reads ONLY this descriptor; a drift from the Lean golden is a hard failure.
    #[test]
    fn cross_cell_conservation_descriptor_matches_lean_pinned_shape() {
        use crate::descriptor_ir2::VmConstraint2;
        let d = cross_cell_conservation_descriptor();
        assert_eq!(d.name, CROSS_CELL_CONSERVATION_DESCRIPTOR_NAME);
        assert_eq!(d.trace_width, CCC_WIDTH);
        assert_eq!(d.trace_width, 5);
        assert_eq!(d.public_input_count, CCC_PI_COUNT);
        assert_eq!(d.public_input_count, 1);
        assert!(d.tables.is_empty(), "pure row-window AIR: no committed tables");
        assert!(d.ranges.is_empty(), "v2 assembly requires the legacy range carrier empty");
        assert_eq!(d.constraints.len(), 8, "the Lean #guard pins 8 constraints");
        let window_gates = d
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
            .count();
        assert_eq!(window_gates, 1, "the single balance prefix-sum window gate");
        let chip_lookups = d
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Lookup(_)))
            .count();
        assert_eq!(chip_lookups, 0, "no chip lookups: the signed delta IS the contribution");
    }

    /// The signed-balance pre-flight: an honest transfer (A −10, B +10) balances to ZERO; the
    /// forged turn (A −10, B +999, no declared mint) leaves +989. This is the arithmetic the
    /// `build_cross_cell_conservation_trace` prefix sum forces into `balance[last]`.
    #[test]
    fn forged_turn_does_not_balance_honest_transfer_does() {
        let honest = vec![delta(7, 10, false), delta(7, 10, true)];
        assert_eq!(cross_cell_balance(&honest), 0, "honest A−10,B+10 conserves");

        let forged = vec![delta(7, 10, false), delta(7, 999, true)];
        assert_eq!(
            cross_cell_balance(&forged),
            989,
            "forged A−10,B+999 (no declared mint) leaves an uncancelled +989"
        );

        let (forged_trace, _pi) = build_cross_cell_conservation_trace(&forged);
        assert_ne!(
            forged_trace.last().unwrap()[CCC_BALANCE_COL],
            BabyBear::ZERO,
            "the forged turn's last-row balance is nonzero — the boundary balance[last]==0 rejects"
        );
    }

    /// A declared mint MAKES the forged-looking turn conserve: A −10, B +999, with a declared
    /// supply mint of −989 (the issuer's explicit supply-change row) balances to 0. This is the
    /// mint/burn discipline: non-conservation is only legal when DISCLOSED as a supply row.
    #[test]
    fn declared_mint_restores_conservation() {
        // B receives +999; A sends −10; the issuer declares a +989 mint as a credit and the supply
        // pool debits −989 — modeled here as the single declared supply row that pairs the +999.
        // The honest accounting: the +999 credit to B is matched by a −10 from A and a −989 supply
        // burn (the issuer's disclosed Annihilative row balancing the minted credit).
        let conserving = vec![delta(7, 10, false), delta(7, 999, true), delta(7, 989, false)];
        assert_eq!(
            cross_cell_balance(&conserving),
            0,
            "with the declared ±989 supply row the turn conserves"
        );
    }

    /// END-TO-END (law #1): an honest conserving turn proves + verifies through the LEAN descriptor
    /// batch prover; a tampered asset PI does NOT verify (the per-asset `pi_binding` partition).
    #[test]
    fn cross_cell_conservation_proves_honest_rejects_wrong_asset() {
        // Honest transfer A −10, B +10 over asset 7: balance[last] == 0, proves + verifies.
        let honest = vec![delta(7, 10, false), delta(7, 10, true)];
        let (trace, pi) = build_cross_cell_conservation_trace(&honest);
        assert_eq!(trace.last().unwrap()[CCC_BALANCE_COL], BabyBear::ZERO);
        let proof = prove_cross_cell_conservation(&trace, &pi)
            .expect("honest conserving turn must prove through the descriptor");
        verify_cross_cell_conservation(&proof, &pi)
            .expect("honest conserving turn proof must verify");

        // Tampered asset PI: the per-row `asset == pi[asset]` partition pin fails, so the same
        // proof no longer verifies — a delta of asset 7 cannot be relabeled to asset 8's sum.
        let mut bad_pi = pi.clone();
        bad_pi[CCC_PI_ASSET] = bad_pi[CCC_PI_ASSET] + BabyBear::ONE;
        assert!(
            verify_cross_cell_conservation(&proof, &bad_pi).is_err(),
            "tampered asset PI must reject (the per-asset partition)"
        );
    }

    /// THE FORGED-TURN UNSAT TOOTH (end-to-end). The forged turn A −10, B +999 (no declared mint)
    /// has a nonzero last-row balance, so the `balance[last] == 0` boundary is violated: the trace
    /// is UNSATISFIABLE. The honest transfer A −10, B +10 proves. This is the in-circuit
    /// realization of the Lean `ccc_forged_mint_unsat`.
    #[test]
    fn forged_mint_turn_is_unsat() {
        let forged = vec![delta(7, 10, false), delta(7, 999, true)];
        let (forged_trace, forged_pi) = build_cross_cell_conservation_trace(&forged);
        assert_ne!(forged_trace.last().unwrap()[CCC_BALANCE_COL], BabyBear::ZERO);

        // The unbalanced trace violates the `balance[last] == 0` boundary. The prover may reject up
        // front (the debug batch prover panics on an unsatisfiable trace) — caught here — or, if it
        // produces a proof, VERIFY must reject it. Either way the forgery does not pass.
        let proved = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_cross_cell_conservation(&forged_trace, &forged_pi)
        }));
        match proved {
            Err(_) => { /* prover panicked on the unsatisfiable trace — the forgery is rejected */ }
            Ok(Err(_)) => { /* prover returned Err — also a rejection */ }
            Ok(Ok(proof)) => {
                assert!(
                    verify_cross_cell_conservation(&proof, &forged_pi).is_err(),
                    "a forged non-conserving turn must NOT verify (balance[last]==0 boundary)"
                );
            }
        }

        // The honest counterpart proves + verifies (non-vacuity: the gate accepts honest turns).
        let honest = vec![delta(7, 10, false), delta(7, 10, true)];
        let (htrace, hpi) = build_cross_cell_conservation_trace(&honest);
        let hproof = prove_cross_cell_conservation(&htrace, &hpi)
            .expect("honest turn must prove");
        verify_cross_cell_conservation(&hproof, &hpi).expect("honest turn must verify");
    }
}
