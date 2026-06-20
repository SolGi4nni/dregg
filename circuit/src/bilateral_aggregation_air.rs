//! Stage 7-γ.2 Phase 2 — joint bilateral aggregation AIR.
//!
//! See `STAGE-7-GAMMA-2-PHASE-2-SKETCH.md` for the full design.
//!
//! This module collapses Phase 1's "N per-cell STARK proofs + Rust cross-cell
//! match loop" into a single outer AIR whose public input is the reduced
//! bundle-level summary. The outer trace has one row per inner per-cell proof
//! (padded to a power of two). Each row carries that proof's complete
//! active PI v3 vector (`inner_pi::ACTIVE_BASE_COUNT` felts) lifted into trace
//! columns, plus an identically-shaped "expected" projection derived from the
//! bilateral schedule (`turn::bilateral_schedule::ExpectedBilateral::roots_for/counts_for`
//! over the row's owner-cell). The AIR's constraints then enforce, in one
//! algebraic pass, every check the Rust loop performs today:
//!
//!   CG-2  turn-identity agreement
//!         per-row PI slots [TURN_HASH, EFFECTS_HASH_GLOBAL, ACTOR_NONCE,
//!         PREVIOUS_RECEIPT_HASH] equal the outer PI's matching slots.
//!
//!   CG-3  schedule replay
//!         per-row PI counts + roots equal the per-cell "expected" columns
//!         the prover populated from the schedule.
//!
//!   CG-4  IS_AGENT_CELL accounting
//!         running cumulative sum of IS_AGENT_CELL across rows. Boundary:
//!         last row's cumulative == 1. (When N_CELLS is the active prefix,
//!         padding rows carry IS_AGENT_CELL = 0 and contribute nothing.)
//!
//!   CG-5  cross-side existence
//!         expressed as a per-row "schedule-covered" indicator: a row's
//!         expected counts being nonzero must be matched by *another* row
//!         claiming the peer side. Today this is enforced *outside* the AIR
//!         by the prover's schedule-construction logic — the AIR's job is
//!         to confirm what the prover claims, not to discover unbundled
//!         peers. (CG-5 in Rust-shape is part of the prover-side wiring
//!         and the verifier's outer-PI cross-check, not an AIR constraint
//!         group of its own. The Phase-2 sketch flags it as the most
//!         delicate group; we land the matrix variant in a follow-up.)
//!
//!   BILATERAL_CONSISTENT
//!         outer PI slot, must equal 1; constrained to 1 at the last row.
//!
//! ## Inner-proof recursive verification (CG-1)
//!
//! Phase 2's headline win is *also* collapsing each inner STARK verify into
//! the outer AIR. With the now-paved `plonky3_recursion_impl` substrate, the
//! aggregation prover composes:
//!
//!   1. Phase-1 verify of each inner Effect VM proof (classical Rust call).
//!   2. The outer aggregation AIR proof over their PIs.
//!   3. (Optional) a recursive-layer proof of (2), produced via
//!      `prove_recursive_layer_for_air` — this is the constant-size
//!      verification artifact Phase 2 promises.
//!
//! Step (3) means the outer verifier never re-runs (1): the recursive layer
//! attests that the outer AIR accepted its inputs, and the outer AIR's CG-2
//! through CG-5 plus the row PIs *being the inner PIs* binds those inputs
//! to the per-cell proofs the prover ran in (1). A consumer downstream needs
//! only (3) + the outer PI to know the bundle is bilaterally consistent.
//!
//! ## Trace layout
//!
//! `width = AGG_WIDTH` columns. Per row:
//!
//! ```text
//!  [0  .. 74)   inner_pi_buffer       — the cell's full γ.2 PI vector
//!  [74 .. 81)   expected_counts       — 7 count fields from the schedule
//!  [81 ..109)   expected_roots        — 7 × 4-felt root fields
//!  [109]        is_agent_cumulative   — running sum of IS_AGENT_CELL
//!  [110]        consistent_indicator  — bool 1 = this row's checks pass
//!  [111]        n_cells_active        — running active-row counter
//! ```
//!
//! Boundary constraints:
//! - `is_agent_cumulative[last] == 1`
//! - `outer_pi[BILATERAL_CONSISTENT] == 1`
//!
//! ## Outer PI layout
//!
//! ```text
//!   0..4    OUTER_TURN_HASH
//!   4..8    OUTER_EFFECTS_HASH_GLOBAL
//!   8       OUTER_ACTOR_NONCE
//!   9..13   OUTER_PREVIOUS_RECEIPT_HASH
//!  13..21   OUTER_AGENT_CELL_ID   (8-felt cell-id decomposition)
//!  21       OUTER_N_CELLS         (number of active rows in the trace)
//!  22       OUTER_BILATERAL_CONSISTENT  (must == 1 for accept)
//! ```
//!
//! Fixed width: 23 felts, independent of N. This is the headline win for
//! verifier complexity vs. Phase 1's `N × 74` per-bundle PI.

#[cfg(feature = "plonky3")]
use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
#[cfg(feature = "plonky3")]
use p3_field::PrimeCharacteristicRing;

use crate::effect_vm::pi as inner_pi;
use crate::field::BabyBear;

// ---------------------------------------------------------------------------
// Lean-emitted descriptor (law #1): the bilateral aggregation AIR, as a PROVED
// `EffectVmDescriptor2` (`Dregg2/Circuit/Emit/EffectVmEmitBilateralAgg.lean`).
// ---------------------------------------------------------------------------

/// The byte-pinned Lean emission of the bilateral aggregation descriptor
/// (`emitVmJson2 bilateralAggDescriptor`). The schedule contract is DECOUPLED from the v1
/// `effect_vm::pi` buffer: the descriptor's main trace carries a standalone 49-felt schedule
/// block (`Sched.*`), 35 expected columns, and 3 accumulators (width 87); the outer PI is a
/// fixed 23 felts independent of N. The two cumulative-sum transitions are the new `windowGate`
/// (two-row) constraint kind. Re-emit via `lake env lean --run` over a driver printing
/// `emitVmJson2 bilateralAggDescriptor`; the SHA is pinned by
/// `bilateral_aggregation_descriptor_matches_lean_pin`.
#[cfg(any(feature = "prover", feature = "verifier"))]
pub const BILATERAL_AGGREGATION_DESCRIPTOR_JSON: &str =
    include_str!("../descriptors/dregg-bilateral-aggregation-v2.json");

/// The descriptor's wire identity (matches `bilateralAggDescriptor.name`).
pub const BILATERAL_AGGREGATION_DESCRIPTOR_NAME: &str = "dregg-bilateral-aggregation-v2";

/// Parse the byte-pinned Lean descriptor into an [`EffectVmDescriptor2`]. The aggregation
/// prover/verifier route through `descriptor_ir2::{prove,verify}_vm_descriptor2` against THIS
/// descriptor — no Rust-authored constraint semantics (law #1). Fail-closed on any parse error
/// (the pinned bytes are the Lean golden; a divergence is a hard refusal, never a warning).
#[cfg(any(feature = "prover", feature = "verifier"))]
pub fn bilateral_aggregation_descriptor() -> crate::descriptor_ir2::EffectVmDescriptor2 {
    crate::descriptor_ir2::parse_vm_descriptor2(BILATERAL_AGGREGATION_DESCRIPTOR_JSON)
        .expect("pinned bilateral-aggregation descriptor JSON must parse (Lean golden)")
}

// ===========================================================================
// The DECOUPLED v2 trace + outer-PI layout (Lean `Agg.*` / `Sched.*` / `OuterPi.*`).
//
// The descriptor's main trace carries a STANDALONE 49-felt bilateral-schedule block (no v1
// `effect_vm::pi` dependency), the 35 prover-derived `expected_*` columns, and 3 accumulators.
// These mirror `EffectVmEmitBilateralAgg.lean` 1:1 (pinned by the Lean `#guard`s + the Rust
// `agg_v2_layout_matches_lean` tooth). The aggregation reads the schedule block independently
// of the rotated effect-vm 38-PI.
// ===========================================================================

pub mod sched {
    //! The decoupled bilateral-schedule inner-row block (Lean `Sched.*`), offsets LOCAL to the
    //! aggregation main trace. The rotated witnessed-receipt carries this exact field order.
    /// 4-felt turn hash.
    pub const TURN_HASH_BASE: usize = 0;
    pub const TURN_HASH_LEN: usize = 4;
    /// 4-felt global effects hash.
    pub const EFFECTS_HASH_GLOBAL_BASE: usize = 4;
    pub const EFFECTS_HASH_GLOBAL_LEN: usize = 4;
    /// Actor nonce (1 felt).
    pub const ACTOR_NONCE: usize = 8;
    /// 4-felt previous-receipt hash.
    pub const PREVIOUS_RECEIPT_HASH_BASE: usize = 9;
    pub const PREVIOUS_RECEIPT_HASH_LEN: usize = 4;
    /// 7 bilateral counts.
    pub const COUNTS_BASE: usize = 13;
    pub const COUNTS_LEN: usize = 7;
    /// 7 × 4-felt bilateral roots.
    pub const ROOTS_BASE: usize = 20;
    pub const ROOTS_LEN: usize = 28;
    /// Agent-cell boolean (1 felt).
    pub const IS_AGENT_CELL: usize = 48;
    /// The schedule contract width (the standalone block the WR carries).
    pub const WIDTH: usize = 49;
}

/// The aggregation main trace: schedule block + expected cols + accumulators (Lean `Agg.*`).
pub mod agg {
    use super::sched;
    /// The schedule block occupies `[0, Sched::WIDTH)`.
    pub const SCHED_BASE: usize = 0;
    /// The per-cell EXPECTED counts (CG-3 replay target).
    pub const EXPECTED_COUNTS_BASE: usize = sched::WIDTH;
    pub const EXPECTED_COUNTS_LEN: usize = 7;
    /// The per-cell EXPECTED roots (7 × 4).
    pub const EXPECTED_ROOTS_BASE: usize = EXPECTED_COUNTS_BASE + EXPECTED_COUNTS_LEN;
    pub const EXPECTED_ROOTS_LEN: usize = 28;
    /// Running cumulative of `IS_AGENT_CELL`.
    pub const IS_AGENT_CUMULATIVE_COL: usize = EXPECTED_ROOTS_BASE + EXPECTED_ROOTS_LEN;
    /// Per-row "this row's checks passed" boolean.
    pub const CONSISTENT_INDICATOR_COL: usize = IS_AGENT_CUMULATIVE_COL + 1;
    /// Running active-row counter.
    pub const N_CELLS_ACTIVE_COL: usize = CONSISTENT_INDICATOR_COL + 1;
    /// Total main width.
    pub const WIDTH: usize = N_CELLS_ACTIVE_COL + 1;
    /// Absolute column of a schedule field.
    pub const fn sch_col(off: usize) -> usize {
        SCHED_BASE + off
    }
}

/// The aggregation outer public-input layout (Lean `OuterPi.*`; fixed width, independent of N).
pub mod outer_pi_v2 {
    pub const TURN_HASH_BASE: usize = 0;
    pub const TURN_HASH_LEN: usize = 4;
    pub const EFFECTS_HASH_GLOBAL_BASE: usize = 4;
    pub const EFFECTS_HASH_GLOBAL_LEN: usize = 4;
    pub const ACTOR_NONCE: usize = 8;
    pub const PREVIOUS_RECEIPT_HASH_BASE: usize = 9;
    pub const PREVIOUS_RECEIPT_HASH_LEN: usize = 4;
    pub const AGENT_CELL_ID_BASE: usize = 13;
    pub const AGENT_CELL_ID_LEN: usize = 8;
    pub const N_CELLS: usize = 21;
    pub const BILATERAL_CONSISTENT: usize = 22;
    /// Outer PI count (fixed at 23).
    pub const COUNT: usize = 23;
}

/// The v1 PI offsets of the bilateral-schedule contract — the 49-felt window `[33, 82)` inside
/// the legacy `effect_vm::pi` vector that the decoupled `sched` block re-bases to 0. The WR
/// carries the schedule independently; this is the ONE coupling to the v1 PI module, retired
/// when the WR is restructured to emit `sched` natively (see `schedule_block_from_inner_pi`).
#[cfg(any(feature = "prover", feature = "verifier"))]
pub const SCHEDULE_PI_BASE: usize = inner_pi::TURN_HASH_BASE; // == 33

/// Extract the 49-felt decoupled schedule block from a per-cell inner-PI vector. The block is
/// `inner_pi[SCHEDULE_PI_BASE .. SCHEDULE_PI_BASE + Sched::WIDTH)` — a pure projection (the
/// fields are contiguous in the v1 layout: turn-id 13 · counts 7 · roots 28 · is_agent 1). A
/// restructured rotated WR carries this block directly; until then the bundle derives it here.
#[cfg(any(feature = "prover", feature = "verifier"))]
pub fn schedule_block_from_inner_pi(inner_pi_vec: &[BabyBear]) -> [BabyBear; sched::WIDTH] {
    let mut block = [BabyBear::ZERO; sched::WIDTH];
    for (i, slot) in block.iter_mut().enumerate() {
        *slot = inner_pi_vec[SCHEDULE_PI_BASE + i];
    }
    block
}

// ---------------------------------------------------------------------------
// Outer-AIR column layout
// ---------------------------------------------------------------------------

/// Width of the inner PI buffer columns. Equal to the active per-cell PI v3
/// fixed count (`inner_pi::ACTIVE_BASE_COUNT`). We lift the entire vector into
/// the trace so every CG-2/CG-3 constraint is a simple column equality.
pub const PI_BUFFER_WIDTH: usize = inner_pi::ACTIVE_BASE_COUNT;

/// Offset of the inner PI buffer (column 0).
pub const PI_BUFFER_BASE: usize = 0;

/// Offset and width of the per-row expected counts block (7 felts).
pub const EXPECTED_COUNTS_BASE: usize = PI_BUFFER_BASE + PI_BUFFER_WIDTH;
pub const EXPECTED_COUNTS_WIDTH: usize = 7;

/// Offset and width of the per-row expected roots block (7 × 4 = 28 felts).
pub const EXPECTED_ROOTS_BASE: usize = EXPECTED_COUNTS_BASE + EXPECTED_COUNTS_WIDTH;
pub const EXPECTED_ROOTS_WIDTH: usize = 7 * 4;

/// Running cumulative of `IS_AGENT_CELL` (single felt).
pub const IS_AGENT_CUMULATIVE_COL: usize = EXPECTED_ROOTS_BASE + EXPECTED_ROOTS_WIDTH;

/// Per-row "this row's checks passed" boolean (single felt). Set to 1 by
/// the prover when the row corresponds to an actual inner proof and its
/// counts/roots/identity all match. Padding rows carry 0.
pub const CONSISTENT_INDICATOR_COL: usize = IS_AGENT_CUMULATIVE_COL + 1;

/// Running active-row counter (single felt). Padding rows do not increment.
pub const N_CELLS_ACTIVE_COL: usize = CONSISTENT_INDICATOR_COL + 1;

/// Total per-row width.
pub const AGG_WIDTH: usize = N_CELLS_ACTIVE_COL + 1;

// ---------------------------------------------------------------------------
// Outer-AIR public-input layout
// ---------------------------------------------------------------------------

/// Outer PI: 4-felt turn hash.
pub const OUTER_TURN_HASH_BASE: usize = 0;
pub const OUTER_TURN_HASH_LEN: usize = 4;

/// Outer PI: 4-felt global effects hash.
pub const OUTER_EFFECTS_HASH_GLOBAL_BASE: usize = OUTER_TURN_HASH_BASE + OUTER_TURN_HASH_LEN;
pub const OUTER_EFFECTS_HASH_GLOBAL_LEN: usize = 4;

/// Outer PI: actor nonce (single felt; matches the inner per-cell layout).
pub const OUTER_ACTOR_NONCE: usize = OUTER_EFFECTS_HASH_GLOBAL_BASE + OUTER_EFFECTS_HASH_GLOBAL_LEN;

/// Outer PI: 4-felt previous-receipt hash.
pub const OUTER_PREVIOUS_RECEIPT_HASH_BASE: usize = OUTER_ACTOR_NONCE + 1;
pub const OUTER_PREVIOUS_RECEIPT_HASH_LEN: usize = 4;

/// Outer PI: agent-cell id (8-felt canonical decomposition). The aggregation
/// verifier cross-checks this against the active row whose IS_AGENT_CELL is 1.
pub const OUTER_AGENT_CELL_ID_BASE: usize =
    OUTER_PREVIOUS_RECEIPT_HASH_BASE + OUTER_PREVIOUS_RECEIPT_HASH_LEN;
pub const OUTER_AGENT_CELL_ID_LEN: usize = 8;

/// Outer PI: number of active inner proofs in the bundle (single felt). The
/// AIR uses this only to constrain that the last active row's
/// `is_agent_cumulative == 1`; it does *not* gate constraints inside the
/// trace by index (Plonky3 doesn't support that pattern cleanly). Padding
/// rows are required to set IS_AGENT_CELL=0 and contribute zero to the
/// cumulative.
pub const OUTER_N_CELLS: usize = OUTER_AGENT_CELL_ID_BASE + OUTER_AGENT_CELL_ID_LEN;

/// Outer PI: bilateral-consistent flag (single felt; must be 1).
pub const OUTER_BILATERAL_CONSISTENT: usize = OUTER_N_CELLS + 1;

/// Outer PI base count.
pub const OUTER_BASE_COUNT: usize = OUTER_BILATERAL_CONSISTENT + 1;

// ---------------------------------------------------------------------------
// AIR shape
// ---------------------------------------------------------------------------

use crate::stark::{BoundaryConstraint, StarkAir};

// ---------------------------------------------------------------------------
// Witness construction
// ---------------------------------------------------------------------------

pub struct AggregationOuterPi {
    pub turn_hash: [BabyBear; 4],
    pub effects_hash_global: [BabyBear; 4],
    pub actor_nonce: BabyBear,
    pub previous_receipt_hash: [BabyBear; 4],
    pub agent_cell_id: [BabyBear; 8],
    pub n_cells: u32,
    pub bilateral_consistent: BabyBear,
}

impl AggregationOuterPi {
    /// Project to the flat outer-PI vector consumed by the AIR.
    pub fn to_vec(&self) -> Vec<BabyBear> {
        let mut pi = vec![BabyBear::ZERO; OUTER_BASE_COUNT];
        pi[OUTER_TURN_HASH_BASE..OUTER_TURN_HASH_BASE + OUTER_TURN_HASH_LEN]
            .copy_from_slice(&self.turn_hash[..OUTER_TURN_HASH_LEN]);
        pi[OUTER_EFFECTS_HASH_GLOBAL_BASE
            ..OUTER_EFFECTS_HASH_GLOBAL_BASE + OUTER_EFFECTS_HASH_GLOBAL_LEN]
            .copy_from_slice(&self.effects_hash_global[..OUTER_EFFECTS_HASH_GLOBAL_LEN]);
        pi[OUTER_ACTOR_NONCE] = self.actor_nonce;
        pi[OUTER_PREVIOUS_RECEIPT_HASH_BASE
            ..OUTER_PREVIOUS_RECEIPT_HASH_BASE + OUTER_PREVIOUS_RECEIPT_HASH_LEN]
            .copy_from_slice(&self.previous_receipt_hash[..OUTER_PREVIOUS_RECEIPT_HASH_LEN]);
        pi[OUTER_AGENT_CELL_ID_BASE..OUTER_AGENT_CELL_ID_BASE + OUTER_AGENT_CELL_ID_LEN]
            .copy_from_slice(&self.agent_cell_id[..OUTER_AGENT_CELL_ID_LEN]);
        pi[OUTER_N_CELLS] = BabyBear::new(self.n_cells);
        pi[OUTER_BILATERAL_CONSISTENT] = self.bilateral_consistent;
        pi
    }
}

pub struct AggregationInnerRowV2 {
    /// The decoupled bilateral-schedule block (`Sched::WIDTH` felts; see
    /// [`schedule_block_from_inner_pi`]).
    pub schedule: [BabyBear; sched::WIDTH],
    /// 7 expected counts, canonical order.
    pub expected_counts: [BabyBear; 7],
    /// 7 expected roots, each 4 felts, canonical order.
    pub expected_roots: [[BabyBear; 4]; 7],
}

/// Build the DECOUPLED v2 aggregation trace (width [`agg::WIDTH`] = 87) from an ordered list of
/// inner rows. Row layout mirrors Lean `Agg.*`: schedule block `[0, 49)`, expected counts
/// `[49, 56)`, expected roots `[56, 84)`, `is_agent_cumulative` 84, `consistent_indicator` 85,
/// `n_cells_active` 86. Active rows carry `consistent = 1`; padding rows (to the next power of
/// two) carry `0` and forward the cumulatives + the turn-identity slots (so CG-2's last-boundary
/// `pi_binding` holds when the last row is padding).
pub fn build_aggregation_trace_v2(rows: &[AggregationInnerRowV2]) -> Vec<Vec<BabyBear>> {
    assert!(!rows.is_empty(), "aggregation needs at least one inner row");
    let n_active = rows.len();
    let n_padded = n_active.max(2).next_power_of_two();

    let mut trace: Vec<Vec<BabyBear>> = Vec::with_capacity(n_padded);
    let mut cum_agent: u32 = 0;
    let mut n_cells_active: u32 = 0;

    for row in rows {
        let mut t = vec![BabyBear::ZERO; agg::WIDTH];
        for (j, &v) in row.schedule.iter().enumerate() {
            t[agg::sch_col(j)] = v;
        }
        t[agg::EXPECTED_COUNTS_BASE..agg::EXPECTED_COUNTS_BASE + 7]
            .copy_from_slice(&row.expected_counts);
        for k in 0..7 {
            for off in 0..4 {
                t[agg::EXPECTED_ROOTS_BASE + k * 4 + off] = row.expected_roots[k][off];
            }
        }
        let is_agent_u = row.schedule[sched::IS_AGENT_CELL].as_u32();
        cum_agent += is_agent_u;
        n_cells_active += 1;
        t[agg::IS_AGENT_CUMULATIVE_COL] = BabyBear::new(cum_agent);
        t[agg::CONSISTENT_INDICATOR_COL] = BabyBear::new(1);
        t[agg::N_CELLS_ACTIVE_COL] = BabyBear::new(n_cells_active);
        trace.push(t);
    }

    // Padding rows: cumulative + n_cells_active carry forward; the turn-identity schedule
    // fields mirror the first active row so the last-row CG-2 `pi_binding` is satisfied.
    while trace.len() < n_padded {
        let mut t = vec![BabyBear::ZERO; agg::WIDTH];
        t[agg::IS_AGENT_CUMULATIVE_COL] = BabyBear::new(cum_agent);
        t[agg::N_CELLS_ACTIVE_COL] = BabyBear::new(n_cells_active);
        if let Some(first) = rows.first() {
            for i in 0..sched::TURN_HASH_LEN {
                t[agg::sch_col(sched::TURN_HASH_BASE + i)] =
                    first.schedule[sched::TURN_HASH_BASE + i];
            }
            for i in 0..sched::EFFECTS_HASH_GLOBAL_LEN {
                t[agg::sch_col(sched::EFFECTS_HASH_GLOBAL_BASE + i)] =
                    first.schedule[sched::EFFECTS_HASH_GLOBAL_BASE + i];
            }
            t[agg::sch_col(sched::ACTOR_NONCE)] = first.schedule[sched::ACTOR_NONCE];
            for i in 0..sched::PREVIOUS_RECEIPT_HASH_LEN {
                t[agg::sch_col(sched::PREVIOUS_RECEIPT_HASH_BASE + i)] =
                    first.schedule[sched::PREVIOUS_RECEIPT_HASH_BASE + i];
            }
        }
        trace.push(t);
    }

    trace
}

/// Prove the DECOUPLED bilateral aggregation through the Lean-emitted descriptor (law #1): the
/// 87-col trace satisfies `bilateral_aggregation_descriptor()` against the 23-felt outer PI,
/// via the multi-table batch prover. No tables/memory/maps are committed (the descriptor is
/// pure row-window arithmetic). The caller serialises the returned `Ir2BatchProof` with
/// `postcard`, exactly as the rotated effect-vm leg does.
#[cfg(feature = "prover")]
pub fn prove_aggregation_v2(
    trace: &[Vec<BabyBear>],
    outer_pi: &[BabyBear],
) -> Result<crate::descriptor_ir2::Ir2BatchProof<crate::descriptor_ir2::DreggStarkConfig>, String> {
    let desc = bilateral_aggregation_descriptor();
    crate::descriptor_ir2::prove_vm_descriptor2(
        &desc,
        trace,
        outer_pi,
        &crate::descriptor_ir2::MemBoundaryWitness::default(),
        &[],
    )
}

/// Verify a DECOUPLED bilateral aggregation proof against the Lean descriptor + the 23-felt
/// outer PI. Prover-free (`verifier` feature). Fail-closed on verify error.
#[cfg(any(feature = "prover", feature = "verifier"))]
pub fn verify_aggregation_v2(
    proof: &crate::descriptor_ir2::Ir2BatchProof<crate::descriptor_ir2::DreggStarkConfig>,
    outer_pi: &[BabyBear],
) -> Result<(), String> {
    let desc = bilateral_aggregation_descriptor();
    crate::descriptor_ir2::verify_vm_descriptor2(&desc, proof, outer_pi)
}

// ---------------------------------------------------------------------------
// Lean-emitted descriptors (law #1) for the two bilateral-aggregation LEGS:
// the CROSS-SIDE EXISTENCE (CG-5) and BUNDLE-TREE FOLD AIRs. These retire the
// hand-authored `CrossSideExistenceAir`/`BundleTreeFoldAir` `StarkAir` impls on
// the live path (the hand-AIRs remain only as the layout-of-record + trace
// builders + tests until the C7 deletion). Each is a PROVED `EffectVmDescriptor2`
// (`Dregg2/Circuit/Emit/EffectVmEmit{CrossSide,BundleFold}.lean`).
// ---------------------------------------------------------------------------

/// The byte-pinned Lean emission of the cross-side-existence descriptor
/// (`emitVmJson2 crossSideDescriptor`). Width 8, no public inputs, a single Poseidon2 chip table:
/// the fingerprint `edge_fp = Poseidon2(edge_id)` is now a REAL in-circuit chip lookup (the
/// hand-AIR never constrained it), the balance prefix-sum is the `windowGate` two-row primitive,
/// and `balance[last] == 0` is the missing-peer boundary. Re-emit via
/// `lake env lean --run EmitBilateralLegs.lean`; the shape is pinned by
/// `cross_side_descriptor_parses_with_lean_pinned_shape`.
#[cfg(any(feature = "prover", feature = "verifier"))]
pub const CROSS_SIDE_EXISTENCE_DESCRIPTOR_JSON: &str =
    include_str!("../descriptors/dregg-cross-side-existence-v2.json");

/// The cross-side descriptor's wire identity (matches `crossSideDescriptor.name`).
pub const CROSS_SIDE_EXISTENCE_DESCRIPTOR_NAME: &str = "dregg-cross-side-existence-v2";

/// Parse the byte-pinned Lean cross-side descriptor. Fail-closed on parse error (the pinned bytes
/// are the Lean golden; a divergence is a hard refusal).
#[cfg(any(feature = "prover", feature = "verifier"))]
pub fn cross_side_existence_descriptor() -> crate::descriptor_ir2::EffectVmDescriptor2 {
    crate::descriptor_ir2::parse_vm_descriptor2(CROSS_SIDE_EXISTENCE_DESCRIPTOR_JSON)
        .expect("pinned cross-side-existence descriptor JSON must parse (Lean golden)")
}

/// The byte-pinned Lean emission of the bundle-tree-fold descriptor
/// (`emitVmJson2 bundleFoldDescriptor`). Width 3, public inputs `[initial, final]`, a single
/// Poseidon2 chip table: the compress `acc_out = Poseidon2(acc_in, digest)` is now a REAL
/// in-circuit chip lookup (RETIRING the hand-AIR's named residual that left the row-internal
/// Poseidon relation to the verifier's chain recompute), with chain continuity as the `windowGate`
/// primitive and the first/last accumulator pins as `pi_binding`s. Re-emit via
/// `lake env lean --run EmitBilateralLegs.lean`; shape pinned by
/// `bundle_fold_descriptor_parses_with_lean_pinned_shape`.
#[cfg(any(feature = "prover", feature = "verifier"))]
pub const BUNDLE_TREE_FOLD_DESCRIPTOR_JSON: &str =
    include_str!("../descriptors/dregg-bundle-tree-fold-v2.json");

/// The bundle-fold descriptor's wire identity (matches `bundleFoldDescriptor.name`).
pub const BUNDLE_TREE_FOLD_DESCRIPTOR_NAME: &str = "dregg-bundle-tree-fold-v2";

/// Parse the byte-pinned Lean bundle-fold descriptor. Fail-closed on parse error.
#[cfg(any(feature = "prover", feature = "verifier"))]
pub fn bundle_tree_fold_descriptor() -> crate::descriptor_ir2::EffectVmDescriptor2 {
    crate::descriptor_ir2::parse_vm_descriptor2(BUNDLE_TREE_FOLD_DESCRIPTOR_JSON)
        .expect("pinned bundle-tree-fold descriptor JSON must parse (Lean golden)")
}

/// Prove the cross-side-existence balance through the Lean-emitted descriptor (law #1): the 9-col
/// `build_cross_side_trace_v2` output satisfies `cross_side_existence_descriptor()` against the
/// `[commit_seed, edge_commit]` PI, via the multi-table batch STARK (the Poseidon2 chip table
/// commits both the fingerprints AND the rolling edge-sequence commitment). No Rust-authored
/// constraint semantics: every gate + the balance/commit `windowGate`s + the two chip lookups come
/// from the verified Lean module. The `pi` binds the proven trace to the canonical edge sequence
/// (the IR-v2 analog of the hand-AIR's `recompute_trace_commitment`).
#[cfg(feature = "prover")]
pub fn prove_cross_side_existence_v2(
    trace: &[Vec<BabyBear>],
    pi: &[BabyBear],
) -> Result<crate::descriptor_ir2::Ir2BatchProof<crate::descriptor_ir2::DreggStarkConfig>, String> {
    let desc = cross_side_existence_descriptor();
    crate::descriptor_ir2::prove_vm_descriptor2(
        &desc,
        trace,
        pi,
        &crate::descriptor_ir2::MemBoundaryWitness::default(),
        &[],
    )
}

/// Verify a cross-side-existence proof against the Lean descriptor + the `[commit_seed,
/// edge_commit]` PI. Prover-free.
#[cfg(any(feature = "prover", feature = "verifier"))]
pub fn verify_cross_side_existence_v2(
    proof: &crate::descriptor_ir2::Ir2BatchProof<crate::descriptor_ir2::DreggStarkConfig>,
    pi: &[BabyBear],
) -> Result<(), String> {
    let desc = cross_side_existence_descriptor();
    crate::descriptor_ir2::verify_vm_descriptor2(&desc, proof, pi)
}

/// Prove the bundle-tree fold through the Lean-emitted descriptor (law #1): the 3-col
/// `build_tree_fold_trace` output satisfies `bundle_tree_fold_descriptor()` against the
/// `[initial, final]` PI, via the multi-table batch STARK (the chip table commits the compress
/// chain). No Rust-authored constraint semantics.
#[cfg(feature = "prover")]
pub fn prove_tree_fold_v2(
    trace: &[Vec<BabyBear>],
    pi: &[BabyBear],
) -> Result<crate::descriptor_ir2::Ir2BatchProof<crate::descriptor_ir2::DreggStarkConfig>, String> {
    let desc = bundle_tree_fold_descriptor();
    crate::descriptor_ir2::prove_vm_descriptor2(
        &desc,
        trace,
        pi,
        &crate::descriptor_ir2::MemBoundaryWitness::default(),
        &[],
    )
}

/// Verify a bundle-tree-fold proof against the Lean descriptor + the `[initial, final]` PI.
/// Prover-free.
#[cfg(any(feature = "prover", feature = "verifier"))]
pub fn verify_tree_fold_v2(
    proof: &crate::descriptor_ir2::Ir2BatchProof<crate::descriptor_ir2::DreggStarkConfig>,
    pi: &[BabyBear],
) -> Result<(), String> {
    let desc = bundle_tree_fold_descriptor();
    crate::descriptor_ir2::verify_vm_descriptor2(&desc, proof, pi)
}

// ===========================================================================
// CG-5 IN-CIRCUIT — cross-side existence as an algebraic balance AIR
// ===========================================================================
//
// The original CG-5 ("every outgoing edge has its matching incoming peer in
// the bundle") was a Rust precondition (`verify_bilateral_chain`'s HashSet
// existence loop). This AIR makes it an *algebraic* constraint.
//
// ## The argument
//
// Walk every directed bilateral edge the canonical Turn schedule predicts
// (transfers + grants; introduces are handled as their pairwise role edges).
// For each edge `e = (from, to)` with canonical, direction-independent id
// `edge_id` we conceptually emit two half-edges:
//
//   * an OUTGOING half claimed by `from` (sign = +1)
//   * an INCOMING half claimed by `to`   (sign = -1)
//
// A half-edge is *materialised as a trace row only if its self-cell is a
// participant in the bundle*. The AIR maintains a running balance
//
//   balance[i] = balance[i-1] + sign[i] * edge_fp[i]
//
// where `edge_fp = Poseidon2(edge_id)` is a collision-resistant fingerprint
// of the canonical (direction-independent) edge id. The boundary constraint
// pins `balance[last] == 0`.
//
// ### Why sum-to-zero ⟺ no missing peer (soundness)
//
// If every edge that touches the bundle has BOTH endpoints in the bundle,
// then each `edge_fp` appears once with +1 and once with -1: every term
// cancels and the balance is 0. If some edge has exactly one endpoint in the
// bundle (the "missing peer" attack the brief flags), that edge contributes a
// single, uncancelled `± edge_fp` term. For the balance to still be 0, that
// surviving term must be cancelled by another edge's term — i.e. two distinct
// canonical edge ids must collide under Poseidon2 (`edge_fp_a == edge_fp_b`,
// `id_a != id_b`), or the prover must fabricate an `edge_id`/`sign` that
// disagrees with the canonical schedule.
//
// The first is a Poseidon2 collision (~124-bit hard). The second is closed by
// the verifier: it re-derives the *exact* multiset of canonical half-edges
// (id, sign, self-in-bundle) from the Turn and requires the proof-bound trace
// rows to equal it. So a malicious prover cannot drop a half-edge, flip a
// sign, or invent an edge id: the balance constraint then provably fails.
//
// This is a genuine in-circuit replacement for the Rust existence loop: the
// uncancelled-term detection is performed by the STARK over the committed
// trace (FRI + boundary opening), not by a Rust `HashSet`.
//
// ## Trace layout (`CSE_WIDTH` columns)
//
// ```text
//   [0..4)  edge_id           — canonical direction-independent 4-felt id
//   [4]     edge_fp           — Poseidon2(edge_id) fingerprint
//   [5]     sign              — +1 (outgoing) or p-1 (== -1, incoming)
//   [6]     present           — 1 for a real half-edge row, 0 for padding
//   [7]     balance           — running balance prefix sum (this row inclusive)
// ```
//
// Public inputs: none required for the algebraic core; the boundary pins
// `balance[last] == 0`. The verifier separately binds the trace to the Turn.

/// CG-5 trace column: canonical 4-felt edge id, base offset.
pub const CSE_EDGE_ID_BASE: usize = 0;
pub const CSE_EDGE_ID_LEN: usize = 4;
/// CG-5 trace column: Poseidon2 fingerprint of the edge id.
pub const CSE_EDGE_FP_COL: usize = CSE_EDGE_ID_BASE + CSE_EDGE_ID_LEN;
/// CG-5 trace column: edge direction sign (+1 outgoing / -1 incoming).
pub const CSE_SIGN_COL: usize = CSE_EDGE_FP_COL + 1;
/// CG-5 trace column: 1 for a real half-edge row, 0 for padding.
pub const CSE_PRESENT_COL: usize = CSE_SIGN_COL + 1;
/// CG-5 trace column: running balance prefix sum (this row inclusive).
pub const CSE_BALANCE_COL: usize = CSE_PRESENT_COL + 1;
/// CG-5 total trace width.
pub const CSE_WIDTH: usize = CSE_BALANCE_COL + 1;

/// Cross-side existence balance AIR (in-circuit CG-5). See module section.
#[derive(Clone, Debug)]
pub struct CrossSideExistenceAir;

impl CrossSideExistenceAir {
    pub const WIDTH: usize = CSE_WIDTH;
    pub const AIR_NAME: &'static str = "dregg-cross-side-existence-v1";

    /// Compute the per-edge fingerprint from a canonical 4-felt edge id.
    /// Direction-independent: both half-edges of the same canonical edge
    /// share this value, so a matched pair cancels in the balance.
    pub fn edge_fingerprint(edge_id: &[BabyBear; 4]) -> BabyBear {
        crate::poseidon2::hash_4_to_1(edge_id)
    }
}

#[cfg(feature = "plonky3")]
impl<F: PrimeCharacteristicRing + Sync> BaseAir<F> for CrossSideExistenceAir {
    fn width(&self) -> usize {
        Self::WIDTH
    }

    fn num_public_values(&self) -> usize {
        0
    }

    fn main_next_row_columns(&self) -> Vec<usize> {
        vec![
            CSE_BALANCE_COL,
            CSE_SIGN_COL,
            CSE_EDGE_FP_COL,
            CSE_PRESENT_COL,
        ]
    }
}

#[cfg(feature = "plonky3")]
impl<AB: AirBuilder> Air<AB> for CrossSideExistenceAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        let next = main.next_slice();

        let one = AB::Expr::ONE;
        let present: AB::Expr = local[CSE_PRESENT_COL].into();
        let sign: AB::Expr = local[CSE_SIGN_COL].into();
        let fp: AB::Expr = local[CSE_EDGE_FP_COL].into();
        let balance: AB::Expr = local[CSE_BALANCE_COL].into();

        // present ∈ {0,1}.
        builder.assert_zero(present.clone() * (present.clone() - one.clone()));
        // sign ∈ {+1,-1}: (sign-1)(sign+1) == sign^2 - 1 == 0 on present rows.
        // On padding rows we force sign == 0 so the contribution vanishes.
        // We express: present*(sign^2 - 1) == 0  AND  (1-present)*sign == 0.
        builder.assert_zero(present.clone() * (sign.clone() * sign.clone() - one.clone()));
        builder.assert_zero((one.clone() - present.clone()) * sign.clone());
        // Padding rows contribute nothing: (1-present)*fp == 0 is NOT required
        // (fp can be anything on padding), because the contribution is
        // sign*fp and sign==0 on padding. But to keep padding canonical we
        // also pin fp==0 on padding for a clean witness.
        builder.assert_zero((one.clone() - present.clone()) * fp.clone());

        // Balance prefix sum:
        //   balance[0]    == sign[0]*fp[0]              (first row seed)
        //   balance[i+1]  == balance[i] + sign[i+1]*fp[i+1]
        builder
            .when_first_row()
            .assert_zero(balance.clone() - sign.clone() * fp.clone());

        let bal_next: AB::Expr = next[CSE_BALANCE_COL].into();
        let sign_next: AB::Expr = next[CSE_SIGN_COL].into();
        let fp_next: AB::Expr = next[CSE_EDGE_FP_COL].into();
        builder
            .when_transition()
            .assert_zero(bal_next - (balance.clone() + sign_next * fp_next));

        // Boundary: the whole bundle balances — every present half-edge's
        // contribution cancels. Uncancelled (missing-peer) edges break this.
        builder.when_last_row().assert_zero(balance);
    }
}

impl StarkAir for CrossSideExistenceAir {
    fn width(&self) -> usize {
        CSE_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        // present*(sign^2 - 1) is degree 3.
        3
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn air_name(&self) -> &'static str {
        Self::AIR_NAME
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        next: &[BabyBear],
        _public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        let mut combined = BabyBear::ZERO;
        let mut pow = BabyBear::ONE;
        let mut add = |c: BabyBear| {
            combined = combined + pow * c;
            pow = pow * alpha;
        };

        let one = BabyBear::ONE;
        let present = local[CSE_PRESENT_COL];
        let sign = local[CSE_SIGN_COL];
        let fp = local[CSE_EDGE_FP_COL];
        let balance = local[CSE_BALANCE_COL];

        // present ∈ {0,1}.
        add(present * (present - one));
        // present*(sign^2 - 1) == 0.
        add(present * (sign * sign - one));
        // (1-present)*sign == 0.
        add((one - present) * sign);
        // (1-present)*fp == 0 (canonical padding).
        add((one - present) * fp);

        // Balance prefix-sum transition: balance[i+1] = balance[i] +
        // sign[i+1]*fp[i+1]. eval_constraints applies uniformly to rows
        // 0..n-2 (the transition vanishing polynomial excludes the last row),
        // so this expresses exactly the recurrence.
        let bal_next = next[CSE_BALANCE_COL];
        let sign_next = next[CSE_SIGN_COL];
        let fp_next = next[CSE_EDGE_FP_COL];
        add(bal_next - (balance + sign_next * fp_next));

        combined
    }

    fn boundary_constraints(
        &self,
        _public_inputs: &[BabyBear],
        trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        let mut cs = Vec::new();
        if trace_len < 2 {
            return cs;
        }
        // Row 0 seed: balance[0] == sign[0]*fp[0]. We cannot express the
        // product as a fixed boundary value (it depends on the witness), but
        // the verifier re-derives the canonical edge multiset and the row-0
        // values from it, so the seed is pinned externally. The algebraic
        // boundary we *can* fix is balance[last] == 0.
        cs.push(BoundaryConstraint {
            row: trace_len - 1,
            col: CSE_BALANCE_COL,
            value: BabyBear::ZERO,
        });
        cs
    }
}

/// One materialised half-edge row for the cross-side existence AIR.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CrossSideHalfEdge {
    /// Canonical, direction-independent 4-felt edge id.
    pub edge_id: [BabyBear; 4],
    /// `true` = outgoing (sign +1), `false` = incoming (sign -1).
    pub outgoing: bool,
}

/// Build the cross-side existence trace from an ordered list of half-edge
/// rows. Pads to the next power of two with `present = 0` rows that carry the
/// balance forward. Active rows compute `edge_fp = Poseidon2(edge_id)` and the
/// running balance.
pub fn build_cross_side_trace(half_edges: &[CrossSideHalfEdge]) -> Vec<Vec<BabyBear>> {
    let n_active = half_edges.len();
    let n_padded = n_active.max(2).next_power_of_two();
    let mut trace: Vec<Vec<BabyBear>> = Vec::with_capacity(n_padded);

    let mut balance = BabyBear::ZERO;
    for he in half_edges {
        let fp = CrossSideExistenceAir::edge_fingerprint(&he.edge_id);
        let sign = if he.outgoing {
            BabyBear::ONE
        } else {
            // p - 1 == -1 in BabyBear.
            BabyBear::ZERO - BabyBear::ONE
        };
        balance = balance + sign * fp;
        let mut row = vec![BabyBear::ZERO; CSE_WIDTH];
        row[CSE_EDGE_ID_BASE..CSE_EDGE_ID_BASE + 4].copy_from_slice(&he.edge_id);
        row[CSE_EDGE_FP_COL] = fp;
        row[CSE_SIGN_COL] = sign;
        row[CSE_PRESENT_COL] = BabyBear::ONE;
        row[CSE_BALANCE_COL] = balance;
        trace.push(row);
    }

    // Padding: present=0, sign=0, fp=0, balance carries forward.
    while trace.len() < n_padded {
        let mut row = vec![BabyBear::ZERO; CSE_WIDTH];
        row[CSE_BALANCE_COL] = balance;
        trace.push(row);
    }

    trace
}

// ---------------------------------------------------------------------------
// The DECOUPLED v2 cross-side trace (the LEAN-emitted descriptor layout, law #1).
//
// Adds the edge-sequence COMMITMENT columns the IR-v2 binding needs (see
// `EffectVmEmitCrossSide.lean` §"The trace↔proof binding"): a rolling
// `commit[i] = Poseidon2(commit_in[i], edge_fp[i])` whose final value is a public
// input the off-AIR verifier re-derives from the canonical Turn edges. The
// fingerprint AND the commitment are REAL chip lookups (the hand-AIR constrained
// neither in-circuit; it bound the whole trace via `recompute_trace_commitment`).
// ---------------------------------------------------------------------------

/// CG-5 v2 trace column: canonical 4-felt edge id (`Cse.EDGE_ID_BASE`).
pub const CSE2_EDGE_ID_BASE: usize = 0;
/// CG-5 v2 trace column: Poseidon2 fingerprint of the edge id.
pub const CSE2_EDGE_FP_COL: usize = CSE2_EDGE_ID_BASE + 4;
/// CG-5 v2 trace column: edge direction sign (+1 / -1).
pub const CSE2_SIGN_COL: usize = CSE2_EDGE_FP_COL + 1;
/// CG-5 v2 trace column: 1 for a real half-edge, 0 for padding.
pub const CSE2_PRESENT_COL: usize = CSE2_SIGN_COL + 1;
/// CG-5 v2 trace column: running balance prefix sum.
pub const CSE2_BALANCE_COL: usize = CSE2_PRESENT_COL + 1;
/// CG-5 v2 trace column: rolling edge-sequence commitment BEFORE this row (= prev `commit`).
pub const CSE2_COMMIT_IN_COL: usize = CSE2_BALANCE_COL + 1;
/// CG-5 v2 trace column: rolling edge-sequence commitment AFTER absorbing this row's fingerprint.
pub const CSE2_COMMIT_COL: usize = CSE2_COMMIT_IN_COL + 1;
/// Phase B-GATE: the fingerprint absorb's 7 exposed lanes 1..7 (`Cse.FP_LANE1_COL`).
pub const CSE2_FP_LANE1_COL: usize = CSE2_COMMIT_COL + 1;
/// Phase B-GATE: the commitment absorb's 7 exposed lanes 1..7 (`Cse.COMMIT_LANE1_COL`).
pub const CSE2_COMMIT_LANE1_COL: usize =
    CSE2_FP_LANE1_COL + (crate::descriptor_ir2::CHIP_OUT_LANES - 1);
/// CG-5 v2 total trace width (mirrors `Cse.WIDTH = 24`): chain cols + 2·7 chip lane cols.
pub const CSE2_WIDTH: usize =
    CSE2_COMMIT_LANE1_COL + (crate::descriptor_ir2::CHIP_OUT_LANES - 1);

/// CG-5 v2 public input: the commitment seed (`commit_in[0]`, fixed at 0).
pub const CSE2_PI_COMMIT_SEED: usize = 0;
/// CG-5 v2 public input: the final edge-sequence commitment (`commit[last]`).
pub const CSE2_PI_EDGE_COMMIT: usize = 1;
/// CG-5 v2 public input count (mirrors `Cse.PI_COUNT = 2`).
pub const CSE2_PI_COUNT: usize = 2;

/// Build the DECOUPLED v2 cross-side trace (width [`CSE2_WIDTH`] = 9) from an ordered list of
/// half-edge rows, returning `(trace, public_inputs)`. The rolling commitment
/// `commit[i] = Poseidon2(commit_in[i], edge_fp[i])` (seed 0) binds the ORDERED edge-fingerprint
/// sequence; its final value is `pi[CSE2_PI_EDGE_COMMIT]`. Padding rows carry the GENUINE
/// `edge_fp = Poseidon2(0,0,0,0)` and continue the commitment chain (so both chip lookups hold on
/// every row), with `present = sign = 0` so the balance is untouched. The off-AIR verifier
/// re-derives the identical `(trace, pi)` from the canonical Turn edges.
/// Phase B-GATE: fill a cross-side row's chip lane columns. The fingerprint absorb is arity-4 over
/// the 4-felt edge id; the commitment absorb is arity-2 over `[commit_in, fp]`. Lanes 1..7 are the
/// genuine permutation lanes (`chip_absorb_lanes`), so both 17-wide chip lookups match.
#[cfg(feature = "prover")]
fn cse2_fill_lanes(row: &mut [BabyBear], edge_id: &[BabyBear; 4], commit_in: BabyBear, fp: BabyBear) {
    let fp_lanes = crate::descriptor_ir2::chip_absorb_lanes(4, edge_id);
    let commit_lanes = crate::descriptor_ir2::chip_absorb_lanes(2, &[commit_in, fp]);
    let n = crate::descriptor_ir2::CHIP_OUT_LANES - 1;
    row[CSE2_FP_LANE1_COL..CSE2_FP_LANE1_COL + n].copy_from_slice(&fp_lanes);
    row[CSE2_COMMIT_LANE1_COL..CSE2_COMMIT_LANE1_COL + n].copy_from_slice(&commit_lanes);
}

#[cfg(feature = "prover")]
pub fn build_cross_side_trace_v2(
    half_edges: &[CrossSideHalfEdge],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let n_active = half_edges.len();
    let n_padded = n_active.max(2).next_power_of_two();
    let mut trace: Vec<Vec<BabyBear>> = Vec::with_capacity(n_padded);

    let mut balance = BabyBear::ZERO;
    let mut commit = BabyBear::ZERO; // the seed (== pi[CSE2_PI_COMMIT_SEED]).

    for he in half_edges {
        let fp = CrossSideExistenceAir::edge_fingerprint(&he.edge_id);
        let sign = if he.outgoing {
            BabyBear::ONE
        } else {
            BabyBear::ZERO - BabyBear::ONE
        };
        balance = balance + sign * fp;
        let commit_in = commit;
        let commit_out = crate::poseidon2::hash_2_to_1(commit_in, fp);
        commit = commit_out;
        let mut row = vec![BabyBear::ZERO; CSE2_WIDTH];
        row[CSE2_EDGE_ID_BASE..CSE2_EDGE_ID_BASE + 4].copy_from_slice(&he.edge_id);
        row[CSE2_EDGE_FP_COL] = fp;
        row[CSE2_SIGN_COL] = sign;
        row[CSE2_PRESENT_COL] = BabyBear::ONE;
        row[CSE2_BALANCE_COL] = balance;
        row[CSE2_COMMIT_IN_COL] = commit_in;
        row[CSE2_COMMIT_COL] = commit_out;
        cse2_fill_lanes(&mut row, &he.edge_id, commit_in, fp);
        trace.push(row);
    }

    // Padding: present=0, sign=0, balance carries forward; the fingerprint of the all-zero edge id
    // and the commitment chain continue (so both chip lookups hold on padding rows too).
    while trace.len() < n_padded {
        let edge_id = [BabyBear::ZERO; 4];
        let fp = CrossSideExistenceAir::edge_fingerprint(&edge_id);
        let commit_in = commit;
        let commit_out = crate::poseidon2::hash_2_to_1(commit_in, fp);
        commit = commit_out;
        let mut row = vec![BabyBear::ZERO; CSE2_WIDTH];
        row[CSE2_EDGE_FP_COL] = fp;
        row[CSE2_BALANCE_COL] = balance;
        row[CSE2_COMMIT_IN_COL] = commit_in;
        row[CSE2_COMMIT_COL] = commit_out;
        cse2_fill_lanes(&mut row, &edge_id, commit_in, fp);
        trace.push(row);
    }

    let pi = vec![BabyBear::ZERO, commit];
    (trace, pi)
}

// ===========================================================================
// PROOF-OF-PROOFS / TREE FOLD — BundleTreeFoldAir
// ===========================================================================
//
// The original aggregator produced a single, flat outer proof over one Turn's
// per-cell proofs. This AIR adds the recursive layer the brief asks for: an
// outer attestation over a *tree of child AggregatedBundles*. Each child
// bundle is reduced to a fixed digest (a Poseidon2 hash of its outer PI), and
// the fold AIR commits a hash chain over those digests:
//
//   acc[0]    = digest[0]
//   acc[i+1]  = Poseidon2( acc[i], digest[i+1] )   (2-to-1 compress)
//
// The final accumulator is the outer attestation's public input. Verifying
// the fold proof is O(1) in the number of children (the headline recursion
// win). The verifier separately re-checks each child bundle classically and
// recomputes the expected accumulator, so the fold proof binds the exact set
// of children it claims.
//
// ## Trace layout (`FOLD_WIDTH` columns)
//
// ```text
//   [0]  acc_in    — chain accumulator before absorbing this child
//   [1]  digest    — this child's bundle digest
//   [2]  acc_out   — Poseidon2(acc_in, digest)  (this row's chain output)
// ```
//
// Public inputs: `[initial_acc (==0 or digest[0] seed), final_acc]`.

/// Tree-fold trace column: incoming chain accumulator.
pub const FOLD_ACC_IN_COL: usize = 0;
/// Tree-fold trace column: this child's bundle digest.
pub const FOLD_DIGEST_COL: usize = 1;
/// Tree-fold trace column: outgoing chain accumulator (acc_in ⊕ digest).
pub const FOLD_ACC_OUT_COL: usize = 2;
/// Phase B-GATE: the compress absorb's 7 exposed lanes 1..7 (`Fold.LANE1_COL = 3`).
pub const FOLD_LANE1_COL: usize = 3;
/// Tree-fold total trace width: 3 chain cols + 7 chip lane cols (`Fold.WIDTH = 10`).
pub const FOLD_WIDTH: usize = 3 + (crate::descriptor_ir2::CHIP_OUT_LANES - 1);

/// Tree-fold public input: initial accumulator (seed).
pub const FOLD_PI_INITIAL: usize = 0;
/// Tree-fold public input: final accumulator (the outer attestation).
pub const FOLD_PI_FINAL: usize = 1;
/// Tree-fold public input count.
pub const FOLD_PI_COUNT: usize = 2;

/// Bundle-tree fold AIR (proof-of-proofs over child AggregatedBundles).
#[derive(Clone, Debug)]
pub struct BundleTreeFoldAir;

impl BundleTreeFoldAir {
    pub const WIDTH: usize = FOLD_WIDTH;
    pub const PUBLIC_INPUTS: usize = FOLD_PI_COUNT;
    pub const AIR_NAME: &'static str = "dregg-bundle-tree-fold-v1";

    /// Compress two chain elements into one (2-to-1 Poseidon2). The chain
    /// step the AIR's row-internal constraint mirrors.
    pub fn compress(acc: BabyBear, digest: BabyBear) -> BabyBear {
        crate::poseidon2::hash_2_to_1(acc, digest)
    }
}

#[cfg(feature = "plonky3")]
impl<F: PrimeCharacteristicRing + Sync> BaseAir<F> for BundleTreeFoldAir {
    fn width(&self) -> usize {
        Self::WIDTH
    }

    fn num_public_values(&self) -> usize {
        Self::PUBLIC_INPUTS
    }

    fn main_next_row_columns(&self) -> Vec<usize> {
        vec![FOLD_ACC_IN_COL]
    }
}

#[cfg(feature = "plonky3")]
impl<AB: AirBuilder> Air<AB> for BundleTreeFoldAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        let next = main.next_slice();

        let acc_in: AB::Expr = local[FOLD_ACC_IN_COL].into();
        let acc_out: AB::Expr = local[FOLD_ACC_OUT_COL].into();
        let next_acc_in: AB::Expr = next[FOLD_ACC_IN_COL].into();

        let pv = builder.public_values();
        let pv_initial: AB::Expr = pv[FOLD_PI_INITIAL].into();
        let pv_final: AB::Expr = pv[FOLD_PI_FINAL].into();

        // First row: acc_in == initial accumulator (public input).
        builder.when_first_row().assert_zero(acc_in - pv_initial);
        // Last row: acc_out == final accumulator (public input).
        builder
            .when_last_row()
            .assert_zero(acc_out.clone() - pv_final);
        // Chain continuity: acc_out[i] == acc_in[i+1].
        builder.when_transition().assert_zero(acc_out - next_acc_in);
        // NOTE: the row-internal Poseidon2 relation acc_out ==
        // compress(acc_in, digest) is enforced cryptographically by the
        // verifier recomputing the chain (custom-STARK has no in-AIR
        // Poseidon gadget). See the StarkAir impl docs for the residual.
    }
}

impl StarkAir for BundleTreeFoldAir {
    fn width(&self) -> usize {
        FOLD_WIDTH
    }

    fn constraint_degree(&self) -> usize {
        // All constraints are linear (degree 1) in the trace columns.
        2
    }

    fn has_chain_continuity(&self) -> bool {
        false
    }

    fn air_name(&self) -> &'static str {
        Self::AIR_NAME
    }

    fn eval_constraints(
        &self,
        local: &[BabyBear],
        next: &[BabyBear],
        _public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        let mut combined = BabyBear::ZERO;
        let mut pow = BabyBear::ONE;
        let mut add = |c: BabyBear| {
            combined = combined + pow * c;
            pow = pow * alpha;
        };
        // Chain continuity: acc_out[i] - acc_in[i+1] == 0 (rows 0..n-2).
        add(local[FOLD_ACC_OUT_COL] - next[FOLD_ACC_IN_COL]);
        combined
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        let mut cs = Vec::new();
        if public_inputs.len() != FOLD_PI_COUNT || trace_len < 2 {
            return cs;
        }
        // Row 0: acc_in == initial accumulator.
        cs.push(BoundaryConstraint {
            row: 0,
            col: FOLD_ACC_IN_COL,
            value: public_inputs[FOLD_PI_INITIAL],
        });
        // Last row: acc_out == final accumulator.
        cs.push(BoundaryConstraint {
            row: trace_len - 1,
            col: FOLD_ACC_OUT_COL,
            value: public_inputs[FOLD_PI_FINAL],
        });
        cs
    }
}

/// Build the tree-fold trace from an ordered list of child bundle digests.
/// Pads to the next power of two by continuing the compress chain over a
/// zero digest (so padding rows still satisfy continuity + the row-internal
/// compress relation the verifier recomputes). Returns `(trace, public_inputs)`.
/// Phase B-GATE: fill a tree-fold row's chip lane columns from the arity-2 compress absorb of
/// `[acc_in, digest]` — lanes 1..7 are the genuine permutation lanes so the 17-wide chip matches.
#[cfg(feature = "prover")]
fn fold_fill_lanes(row: &mut [BabyBear], acc_in: BabyBear, digest: BabyBear) {
    let lanes = crate::descriptor_ir2::chip_absorb_lanes(2, &[acc_in, digest]);
    let n = crate::descriptor_ir2::CHIP_OUT_LANES - 1;
    row[FOLD_LANE1_COL..FOLD_LANE1_COL + n].copy_from_slice(&lanes);
}

#[cfg(feature = "prover")]
pub fn build_tree_fold_trace(child_digests: &[BabyBear]) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    assert!(
        !child_digests.is_empty(),
        "tree fold needs at least one child digest"
    );
    let n = child_digests.len();
    let n_padded = n.max(2).next_power_of_two();
    let mut trace: Vec<Vec<BabyBear>> = Vec::with_capacity(n_padded);

    // Seed the chain with the first digest, then compress subsequent ones.
    let initial = child_digests[0];
    let mut acc = initial;
    for &digest in child_digests.iter() {
        let acc_in = acc;
        // Uniform recurrence: acc_out = compress(acc_in, digest). For the
        // seed row acc_in == digest[0], so the first child is double-folded;
        // this is deterministic and collision-resistant (Poseidon2), and the
        // verifier recomputes the identical chain.
        let acc_out = BundleTreeFoldAir::compress(acc_in, digest);
        let mut row = vec![BabyBear::ZERO; FOLD_WIDTH];
        row[FOLD_ACC_IN_COL] = acc_in;
        row[FOLD_DIGEST_COL] = digest;
        row[FOLD_ACC_OUT_COL] = acc_out;
        fold_fill_lanes(&mut row, acc_in, digest);
        trace.push(row);
        acc = acc_out;
    }
    // Padding rows: continue the chain over zero digests.
    while trace.len() < n_padded {
        let acc_in = acc;
        let acc_out = BundleTreeFoldAir::compress(acc_in, BabyBear::ZERO);
        let mut row = vec![BabyBear::ZERO; FOLD_WIDTH];
        row[FOLD_ACC_IN_COL] = acc_in;
        row[FOLD_DIGEST_COL] = BabyBear::ZERO;
        row[FOLD_ACC_OUT_COL] = acc_out;
        fold_fill_lanes(&mut row, acc_in, BabyBear::ZERO);
        trace.push(row);
        acc = acc_out;
    }

    let final_acc = trace.last().unwrap()[FOLD_ACC_OUT_COL];
    let public_inputs = vec![initial, final_acc];
    (trace, public_inputs)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// The byte-pinned descriptor parses and carries the Lean-pinned shape (`#guard`s in
    /// `EffectVmEmitBilateralAgg.lean`): width 87, PI 23, 70 constraints, EXACTLY two window
    /// gates, name `dregg-bilateral-aggregation-v2`. This is the law-#1 tooth — the Rust
    /// aggregation reads ONLY this descriptor; a drift from the Lean golden is a hard failure.
    #[cfg(any(feature = "prover", feature = "verifier"))]
    #[test]
    fn bilateral_descriptor_parses_with_lean_pinned_shape() {
        use crate::descriptor_ir2::VmConstraint2;
        let d = bilateral_aggregation_descriptor();
        assert_eq!(d.name, BILATERAL_AGGREGATION_DESCRIPTOR_NAME);
        assert_eq!(d.trace_width, agg::WIDTH);
        assert_eq!(d.trace_width, 87);
        assert_eq!(d.public_input_count, outer_pi_v2::COUNT);
        assert_eq!(d.public_input_count, 23);
        assert!(
            d.tables.is_empty(),
            "pure row-window AIR: no committed tables"
        );
        assert_eq!(
            d.constraints.len(),
            70,
            "the Lean #guard pins 70 constraints"
        );
        let window_gates = d
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
            .count();
        assert_eq!(
            window_gates, 2,
            "exactly the two cumulative-sum window gates"
        );
    }

    /// The cross-side-existence (CG-5) descriptor parses with the Lean-pinned shape
    /// (`EffectVmEmitCrossSide.lean` `#guard`s): width 10, 2 PI (commit seed + edge commitment),
    /// ONE Poseidon2 chip table, 11 constraints, EXACTLY two window gates (balance + commit
    /// continuity) + two chip lookups (the arity-4 fingerprint + the arity-2 commitment), name
    /// `dregg-cross-side-existence-v2`. Law-#1 tooth: the Rust CG-5 leg reads ONLY this descriptor.
    #[cfg(any(feature = "prover", feature = "verifier"))]
    #[test]
    fn cross_side_descriptor_parses_with_lean_pinned_shape() {
        use crate::descriptor_ir2::{TableSem, VmConstraint2};
        let d = cross_side_existence_descriptor();
        assert_eq!(d.name, CROSS_SIDE_EXISTENCE_DESCRIPTOR_NAME);
        assert_eq!(d.trace_width, CSE2_WIDTH);
        assert_eq!(d.trace_width, 24, "Phase B-GATE: 10 chain cols + 2·7 chip lane cols");
        assert_eq!(d.public_input_count, CSE2_PI_COUNT);
        assert_eq!(
            d.public_input_count, 2,
            "commit seed + edge-sequence commitment"
        );
        assert_eq!(d.tables.len(), 1, "one declared table");
        assert!(
            matches!(d.tables[0].sem, TableSem::Poseidon2Chip),
            "the fingerprint + commitment ride a real Poseidon2 chip table"
        );
        assert_eq!(
            d.constraints.len(),
            11,
            "the Lean #guard pins 11 constraints"
        );
        let window_gates = d
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
            .count();
        assert_eq!(
            window_gates, 2,
            "the balance + commitment-continuity window gates"
        );
        let chip_lookups = d
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Lookup(_)))
            .count();
        assert_eq!(chip_lookups, 2, "the fingerprint + commitment chip lookups");
    }

    /// The bundle-tree-fold descriptor parses with the Lean-pinned shape
    /// (`EffectVmEmitBundleFold.lean` `#guard`s): width 3, 2 PI, ONE Poseidon2 chip table, 4
    /// constraints, EXACTLY one window gate + one (arity-2) chip lookup, name
    /// `dregg-bundle-tree-fold-v2`. The chip lookup is the in-circuit compress that RETIRES the
    /// hand-AIR's verifier-side residual.
    #[cfg(any(feature = "prover", feature = "verifier"))]
    #[test]
    fn bundle_fold_descriptor_parses_with_lean_pinned_shape() {
        use crate::descriptor_ir2::{TableSem, VmConstraint2};
        let d = bundle_tree_fold_descriptor();
        assert_eq!(d.name, BUNDLE_TREE_FOLD_DESCRIPTOR_NAME);
        assert_eq!(d.trace_width, FOLD_WIDTH);
        assert_eq!(d.trace_width, 10, "Phase B-GATE: 3 chain cols + 7 chip lane cols");
        assert_eq!(d.public_input_count, FOLD_PI_COUNT);
        assert_eq!(d.public_input_count, 2);
        assert_eq!(d.tables.len(), 1, "one declared table");
        assert!(
            matches!(d.tables[0].sem, TableSem::Poseidon2Chip),
            "the compress rides a real Poseidon2 chip table"
        );
        assert_eq!(d.constraints.len(), 4, "the Lean #guard pins 4 constraints");
        let window_gates = d
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
            .count();
        assert_eq!(window_gates, 1, "the single chain-continuity window gate");
        let chip_lookups = d
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Lookup(_)))
            .count();
        assert_eq!(chip_lookups, 1, "the single compress chip lookup");
    }

    /// END-TO-END (law #1): the cross-side balance trace proves + verifies through the LEAN
    /// descriptor batch prover, and a TAMPERED edge-commitment PI does NOT verify (the
    /// edge-sequence binding that replaces the hand-AIR's `recompute_trace_commitment`). The
    /// missing-peer rejection is a property of the (unsatisfiable) unbalanced trace — the
    /// turn-side `prove_cross_side_existence` pre-flights the balance and returns `Err` BEFORE
    /// proving (the debug batch prover panics on an unsatisfiable trace), so we assert the
    /// nonzero-balance property here and leave the UNSAT rejection to the Lean tooth
    /// `cse_rejects_unbalanced` + the pre-flight.
    #[cfg(feature = "prover")]
    #[test]
    fn cross_side_descriptor_proves_balanced_rejects_missing_peer() {
        // Balanced: one edge, both halves present (+fp and -fp cancel).
        let (balanced, pi) = build_cross_side_trace_v2(&[he(1000, true), he(1000, false)]);
        assert_eq!(balanced.last().unwrap()[CSE2_BALANCE_COL], BabyBear::ZERO);
        let proof = prove_cross_side_existence_v2(&balanced, &pi)
            .expect("balanced cross-side trace must prove through the descriptor");
        verify_cross_side_existence_v2(&proof, &pi)
            .expect("balanced cross-side descriptor proof must verify");

        // Tampered edge-commitment PI: the `commit[last] == pi[edge_commit]` boundary fails, so the
        // same proof no longer verifies — this is the binding to the canonical edge sequence.
        let mut bad_pi = pi.clone();
        bad_pi[CSE2_PI_EDGE_COMMIT] = bad_pi[CSE2_PI_EDGE_COMMIT] + BabyBear::ONE;
        assert!(
            verify_cross_side_existence_v2(&proof, &bad_pi).is_err(),
            "tampered edge-commitment PI must reject (the edge-sequence binding)"
        );

        // Missing peer: the balance is nonzero — the turn-side pre-flight rejects this before
        // proving (the debug batch prover panics on an unsatisfiable trace). The `balance[last] ==
        // 0` boundary is the in-circuit detector, proved UNSAT by
        // `EffectVmEmitCrossSide.cse_rejects_unbalanced`.
        let (unbalanced, _upi) =
            build_cross_side_trace_v2(&[he(1000, true), he(2000, true), he(2000, false)]);
        assert_ne!(
            unbalanced.last().unwrap()[CSE2_BALANCE_COL],
            BabyBear::ZERO,
            "a missing-peer edge leaves a nonzero balance the boundary rejects"
        );
    }

    /// END-TO-END (law #1): the tree-fold trace proves + verifies through the LEAN descriptor batch
    /// prover, and a tampered final-accumulator PI does NOT verify (the `pi_binding` boundary). The
    /// compress is a REAL chip lookup, strictly stronger than the hand-AIR.
    #[cfg(feature = "prover")]
    #[test]
    fn tree_fold_descriptor_proves_rejects_tampered_final() {
        let (trace, pi) = build_tree_fold_trace(&[BabyBear::new(111), BabyBear::new(222)]);
        let proof =
            prove_tree_fold_v2(&trace, &pi).expect("tree fold must prove through the descriptor");
        verify_tree_fold_v2(&proof, &pi).expect("tree fold descriptor proof must verify");

        let mut bad_pi = pi.clone();
        bad_pi[FOLD_PI_FINAL] = bad_pi[FOLD_PI_FINAL] + BabyBear::ONE;
        assert!(
            verify_tree_fold_v2(&proof, &bad_pi).is_err(),
            "tampered final accumulator must reject"
        );
    }

    /// The decoupled `sched` block re-bases the v1 bilateral-schedule PI window `[33, 82)` to 0.
    /// Pin the contiguity assumption `schedule_block_from_inner_pi` relies on: every schedule
    /// field sits at `inner_pi::<field> == SCHEDULE_PI_BASE + sched::<field>`.
    #[cfg(any(feature = "prover", feature = "verifier"))]
    #[test]
    fn schedule_block_offsets_match_v1_pi_window() {
        assert_eq!(SCHEDULE_PI_BASE, 33);
        assert_eq!(sched::WIDTH, 49);
        assert_eq!(
            inner_pi::TURN_HASH_BASE,
            SCHEDULE_PI_BASE + sched::TURN_HASH_BASE
        );
        assert_eq!(
            inner_pi::EFFECTS_HASH_GLOBAL_BASE,
            SCHEDULE_PI_BASE + sched::EFFECTS_HASH_GLOBAL_BASE
        );
        assert_eq!(inner_pi::ACTOR_NONCE, SCHEDULE_PI_BASE + sched::ACTOR_NONCE);
        assert_eq!(
            inner_pi::PREVIOUS_RECEIPT_HASH_BASE,
            SCHEDULE_PI_BASE + sched::PREVIOUS_RECEIPT_HASH_BASE
        );
        assert_eq!(
            inner_pi::OUTBOUND_TRANSFER_COUNT,
            SCHEDULE_PI_BASE + sched::COUNTS_BASE
        );
        assert_eq!(
            inner_pi::OUTGOING_TRANSFER_ROOT_BASE,
            SCHEDULE_PI_BASE + sched::ROOTS_BASE
        );
        assert_eq!(
            inner_pi::IS_AGENT_CELL,
            SCHEDULE_PI_BASE + sched::IS_AGENT_CELL
        );
        // The window is exactly the 49 felts [33, 82) — nothing else lives in it.
        assert_eq!(SCHEDULE_PI_BASE + sched::WIDTH, inner_pi::IS_AGENT_CELL + 1);
    }

    // ---- CG-5 cross-side existence AIR ----

    fn he(id: u32, outgoing: bool) -> CrossSideHalfEdge {
        CrossSideHalfEdge {
            edge_id: [
                BabyBear::new(id),
                BabyBear::new(id + 1),
                BabyBear::new(id + 2),
                BabyBear::new(id + 3),
            ],
            outgoing,
        }
    }

    #[test]
    fn cross_side_balanced_pair_sums_to_zero_and_proves() {
        // One edge, both endpoints present: +fp and -fp cancel.
        let half_edges = vec![he(1000, true), he(1000, false)];
        let trace = build_cross_side_trace(&half_edges);
        assert_eq!(trace.last().unwrap()[CSE_BALANCE_COL], BabyBear::ZERO);

        let proof = crate::stark::try_prove(&CrossSideExistenceAir, &trace, &[])
            .expect("balanced cross-side trace must prove");
        crate::stark::verify(&CrossSideExistenceAir, &proof, &[])
            .expect("balanced cross-side proof must verify");
    }

    #[test]
    fn cross_side_two_edges_both_balanced_proves() {
        let half_edges = vec![
            he(1000, true),
            he(2000, true),
            he(1000, false),
            he(2000, false),
        ];
        let trace = build_cross_side_trace(&half_edges);
        assert_eq!(trace.last().unwrap()[CSE_BALANCE_COL], BabyBear::ZERO);
        let proof = crate::stark::try_prove(&CrossSideExistenceAir, &trace, &[]).expect("prove");
        crate::stark::verify(&CrossSideExistenceAir, &proof, &[]).expect("verify");
    }

    #[test]
    fn cross_side_missing_peer_does_not_balance() {
        // Edge 1000 has only its outgoing half present (peer missing). The
        // balance is the uncancelled fingerprint, which is nonzero with
        // overwhelming probability — so the boundary balance[last]==0 fails
        // and the trace is UNPROVABLE.
        let half_edges = vec![he(1000, true), he(2000, true), he(2000, false)];
        let trace = build_cross_side_trace(&half_edges);
        assert_ne!(
            trace.last().unwrap()[CSE_BALANCE_COL],
            BabyBear::ZERO,
            "missing-peer edge must leave a nonzero balance"
        );
        // The trace's transition constraints are internally consistent (the
        // prefix sum is honestly computed), so proving may succeed — but the
        // boundary constraint balance[last]==0 is violated, so VERIFY rejects.
        match crate::stark::try_prove(&CrossSideExistenceAir, &trace, &[]) {
            Err(_) => { /* prover rejected up front — also fine */ }
            Ok(proof) => {
                let res = crate::stark::verify(&CrossSideExistenceAir, &proof, &[]);
                assert!(
                    res.is_err(),
                    "missing-peer proof violates balance boundary and must not verify"
                );
            }
        }
    }

    #[test]
    fn cross_side_adversary_cannot_forge_zero_balance_boundary() {
        // Adversary builds a missing-peer trace, then hand-patches the last
        // balance cell to ZERO to try to satisfy the boundary. The internal
        // prefix-sum transition constraint then no longer holds, so the proof
        // still fails.
        let half_edges = vec![he(1000, true), he(2000, true), he(2000, false)];
        let mut trace = build_cross_side_trace(&half_edges);
        let last = trace.len() - 1;
        trace[last][CSE_BALANCE_COL] = BabyBear::ZERO;
        let res = crate::stark::try_prove(&CrossSideExistenceAir, &trace, &[]);
        assert!(
            res.is_err(),
            "patched balance breaks the prefix-sum transition; must not prove"
        );
    }

    // ---- Tree-fold AIR ----

    #[test]
    fn tree_fold_two_children_proves_and_verifies() {
        let digests = vec![BabyBear::new(111), BabyBear::new(222)];
        let (trace, pi) = build_tree_fold_trace(&digests);
        assert_eq!(pi.len(), FOLD_PI_COUNT);
        let proof =
            crate::stark::try_prove(&BundleTreeFoldAir, &trace, &pi).expect("tree fold must prove");
        crate::stark::verify(&BundleTreeFoldAir, &proof, &pi).expect("tree fold must verify");
    }

    #[test]
    fn tree_fold_rejects_tampered_final_acc() {
        let digests = vec![BabyBear::new(111), BabyBear::new(222), BabyBear::new(333)];
        let (trace, pi) = build_tree_fold_trace(&digests);
        let proof = crate::stark::try_prove(&BundleTreeFoldAir, &trace, &pi).expect("prove");
        // Tamper the final-acc public input: boundary opening now mismatches.
        let mut bad_pi = pi.clone();
        bad_pi[FOLD_PI_FINAL] = bad_pi[FOLD_PI_FINAL] + BabyBear::ONE;
        let res = crate::stark::verify(&BundleTreeFoldAir, &proof, &bad_pi);
        assert!(res.is_err(), "tampered final accumulator must reject");
    }

    #[test]
    fn tree_fold_distinct_child_sets_give_distinct_accumulators() {
        let (_, pi_a) = build_tree_fold_trace(&[BabyBear::new(1), BabyBear::new(2)]);
        let (_, pi_b) = build_tree_fold_trace(&[BabyBear::new(1), BabyBear::new(3)]);
        assert_ne!(
            pi_a[FOLD_PI_FINAL], pi_b[FOLD_PI_FINAL],
            "different child digest sets must fold to different accumulators"
        );
    }

    #[test]
    fn outer_pi_layout_round_trip() {
        let pi = AggregationOuterPi {
            turn_hash: [
                BabyBear::new(1),
                BabyBear::new(2),
                BabyBear::new(3),
                BabyBear::new(4),
            ],
            effects_hash_global: [
                BabyBear::new(5),
                BabyBear::new(6),
                BabyBear::new(7),
                BabyBear::new(8),
            ],
            actor_nonce: BabyBear::new(9),
            previous_receipt_hash: [
                BabyBear::new(10),
                BabyBear::new(11),
                BabyBear::new(12),
                BabyBear::new(13),
            ],
            agent_cell_id: [
                BabyBear::new(14),
                BabyBear::new(15),
                BabyBear::new(16),
                BabyBear::new(17),
                BabyBear::new(18),
                BabyBear::new(19),
                BabyBear::new(20),
                BabyBear::new(21),
            ],
            n_cells: 3,
            bilateral_consistent: BabyBear::new(1),
        };
        let v = pi.to_vec();
        assert_eq!(v.len(), OUTER_BASE_COUNT);
        assert_eq!(v[OUTER_TURN_HASH_BASE].as_u32(), 1);
        assert_eq!(v[OUTER_EFFECTS_HASH_GLOBAL_BASE].as_u32(), 5);
        assert_eq!(v[OUTER_ACTOR_NONCE].as_u32(), 9);
        assert_eq!(v[OUTER_PREVIOUS_RECEIPT_HASH_BASE].as_u32(), 10);
        assert_eq!(v[OUTER_AGENT_CELL_ID_BASE].as_u32(), 14);
        assert_eq!(v[OUTER_N_CELLS].as_u32(), 3);
        assert_eq!(v[OUTER_BILATERAL_CONSISTENT].as_u32(), 1);
    }
}
