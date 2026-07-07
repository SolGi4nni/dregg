//! # The emit-from-Lean EQUALITY GATE — the BILATERAL-BUNDLE AGGREGATION outer AIR (law #1).
//!
//! The aggregation descriptor is AUTHORED in Lean (`metatheory/Dregg2/Circuit/Emit/
//! EffectVmEmitBilateralAgg.lean`, `bilateralAggDescriptor`) and its wire string is byte-pinned
//! there (`metatheory/Dregg2/Circuit/Emit/BilateralAggregationEmit.lean`, the
//! `#guard emitVmJson2 bilateralAggDescriptor == GOLDEN`). This test embeds that EXACT string
//! ([`GOLDEN_JSON`], byte-identical to `circuit/descriptors/dregg-bilateral-aggregation-v2.json`,
//! which `bilateral_aggregation_air.rs` `include_str!`s), and:
//!
//!   1. DECODES it via [`parse_vm_descriptor2`] and asserts the decode equals an independently
//!      hand-built `EffectVmDescriptor2` (Lean emit ≡ Rust builder — a byte drift on either side
//!      breaks this OR the Lean `#guard`);
//!   2. proves an HONEST bundle witness (one agent cell + padding, the 87-column decoupled trace)
//!      through [`prove_vm_descriptor2`], asserts ACCEPT, and re-verifies the proof;
//!   3. the MUTATION CANARIES — each tampers the witness so exactly one hand-AIR constraint family
//!      bites, and asserts the prove-or-verify REFUSES (real UNSAT):
//!        (a) a forged outer turn-identity PI      → CG-2 `pi_binding`  (turn-identity agreement),
//!        (b) a carried count ≠ its expected column → CG-3 `gate`       (schedule replay),
//!        (c) TWO agent cells in one bundle         → CG-4 `boundary`   (`cum == 1`, the
//!            cross-federation double-spend rejection),
//!        (d) a forged running active-row counter   → the `window_gate` (the two-row cumulative
//!            primitive).
//!
//! The canaries are NON-VACUOUS by construction: each first asserts the honest witness is ACCEPTED
//! (so the negative pole is not spuriously green), then asserts the tampered witness is REJECTED.
//! These are the same rejections the Lean teeth prove over the emitted descriptor
//! (`agg_rejects_turn_mismatch` / `BilateralAggregationEmit.agg_rejects_count_mismatch` /
//! `agg_rejects_bad_agent_count`) and the `teasting/multi_cell_cross_fed_binding` gauntlet drives.

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, VmConstraint2, WindowExpr, WindowGateSpec,
    parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

/// The BYTE-IDENTICAL wire string Lean's `emitVmJson2 bilateralAggDescriptor` emits (pinned by the
/// `#guard` in `BilateralAggregationEmit.lean`, and equal to the `include_str!`ed golden). If Lean
/// drifts, that `#guard` fails; if this literal drifts, the `decoded == hand_built` assertion fails.
const GOLDEN_JSON: &str = r#"{"name":"dregg-bilateral-aggregation-v2","ir":2,"trace_width":87,"public_input_count":23,"tables":[],"constraints":[{"t":"pi_binding","row":"first","col":0,"pi_index":0},{"t":"pi_binding","row":"first","col":1,"pi_index":1},{"t":"pi_binding","row":"first","col":2,"pi_index":2},{"t":"pi_binding","row":"first","col":3,"pi_index":3},{"t":"pi_binding","row":"first","col":4,"pi_index":4},{"t":"pi_binding","row":"first","col":5,"pi_index":5},{"t":"pi_binding","row":"first","col":6,"pi_index":6},{"t":"pi_binding","row":"first","col":7,"pi_index":7},{"t":"pi_binding","row":"first","col":8,"pi_index":8},{"t":"pi_binding","row":"first","col":9,"pi_index":9},{"t":"pi_binding","row":"first","col":10,"pi_index":10},{"t":"pi_binding","row":"first","col":11,"pi_index":11},{"t":"pi_binding","row":"first","col":12,"pi_index":12},{"t":"pi_binding","row":"last","col":0,"pi_index":0},{"t":"pi_binding","row":"last","col":1,"pi_index":1},{"t":"pi_binding","row":"last","col":2,"pi_index":2},{"t":"pi_binding","row":"last","col":3,"pi_index":3},{"t":"pi_binding","row":"last","col":4,"pi_index":4},{"t":"pi_binding","row":"last","col":5,"pi_index":5},{"t":"pi_binding","row":"last","col":6,"pi_index":6},{"t":"pi_binding","row":"last","col":7,"pi_index":7},{"t":"pi_binding","row":"last","col":8,"pi_index":8},{"t":"pi_binding","row":"last","col":9,"pi_index":9},{"t":"pi_binding","row":"last","col":10,"pi_index":10},{"t":"pi_binding","row":"last","col":11,"pi_index":11},{"t":"pi_binding","row":"last","col":12,"pi_index":12},{"t":"gate","body":{"t":"add","l":{"t":"var","v":13},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":49}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":14},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":50}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":15},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":51}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":16},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":52}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":17},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":53}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":18},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":54}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":19},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":55}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":20},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":56}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":21},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":57}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":22},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":58}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":23},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":59}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":24},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":60}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":25},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":61}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":26},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":62}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":27},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":63}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":28},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":64}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":29},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":65}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":30},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":66}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":31},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":67}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":32},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":68}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":33},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":69}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":34},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":70}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":35},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":71}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":36},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":72}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":73}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":38},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":74}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":39},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":75}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":40},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":76}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":41},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":77}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":42},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":78}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":43},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":79}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":44},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":80}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":45},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":81}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":46},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":82}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":47},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":83}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":48},"r":{"t":"add","l":{"t":"var","v":48},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":85},"r":{"t":"add","l":{"t":"var","v":85},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":85}}},"r":{"t":"var","v":48}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":84},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":84}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"nxt","c":48}}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":86},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":86}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"nxt","c":85}}}}},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"var","v":84},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":48}}}},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"var","v":86},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":85}}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"var","v":84},"r":{"t":"const","v":-1}}},{"t":"pi_binding","row":"last","col":86,"pi_index":21}],"hash_sites":[],"ranges":[]}"#;

// --- Trace column layout (must match `EffectVmEmitBilateralAgg.lean` Sched.* / Agg.*). ---
const TURN_HASH_BASE: usize = 0;
const EFFECTS_HASH_GLOBAL_BASE: usize = 4;
const ACTOR_NONCE: usize = 8;
const PREVIOUS_RECEIPT_HASH_BASE: usize = 9;
const COUNTS_BASE: usize = 13;
const COUNTS_LEN: usize = 7;
const ROOTS_BASE: usize = 20;
const ROOTS_LEN: usize = 28;
const IS_AGENT_CELL: usize = 48;
const EXPECTED_COUNTS_BASE: usize = 49;
const EXPECTED_ROOTS_BASE: usize = 56;
const IS_AGENT_CUMULATIVE_COL: usize = 84;
const CONSISTENT_INDICATOR_COL: usize = 85;
const N_CELLS_ACTIVE_COL: usize = 86;
const AGG_WIDTH: usize = 87;

// --- Outer PI layout (Lean OuterPi.*). ---
const PI_N_CELLS: usize = 21;
const PI_BILATERAL_CONSISTENT: usize = 22;
const OUTER_PI_COUNT: usize = 23;

// ---------------------------------------------------------------------------
// The independently hand-built twin of the Lean descriptor (mirrors the Lean
// constraint builders 1:1, in the same order `aggConstraints` assembles them).
// ---------------------------------------------------------------------------

/// `colEqCol a b` — `gate (var a - var b)`.
fn col_eq_col(a: usize, b: usize) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::Gate(LeanExpr::add(
        LeanExpr::Var(a),
        LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(b)),
    )))
}

fn pi_bind(row: VmRow, col: usize, pi_index: usize) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index })
}

/// `boolGate c` — `gate (var c * (var c - 1))`.
fn bool_gate(c: usize) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::Gate(LeanExpr::mul(
        LeanExpr::Var(c),
        LeanExpr::add(LeanExpr::Var(c), LeanExpr::Const(-1)),
    )))
}

/// `paddingGate` — `gate ((1 - consistent) * is_agent)`.
fn padding_gate() -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::Gate(LeanExpr::mul(
        LeanExpr::add(
            LeanExpr::Const(1),
            LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(CONSISTENT_INDICATOR_COL)),
        ),
        LeanExpr::Var(IS_AGENT_CELL),
    )))
}

/// The cumulative `windowGate` (`onTransition`): `next[cum] - local[cum] - next[contribution]`.
fn cum_transition(cum: usize, contribution: usize) -> VmConstraint2 {
    VmConstraint2::WindowGate(WindowGateSpec {
        on_transition: true,
        body: WindowExpr::Add(
            Box::new(WindowExpr::Nxt(cum)),
            Box::new(WindowExpr::Add(
                Box::new(WindowExpr::Mul(
                    Box::new(WindowExpr::Const(-1)),
                    Box::new(WindowExpr::Loc(cum)),
                )),
                Box::new(WindowExpr::Mul(
                    Box::new(WindowExpr::Const(-1)),
                    Box::new(WindowExpr::Nxt(contribution)),
                )),
            )),
        ),
    })
}

fn boundary(row: VmRow, body: LeanExpr) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::Boundary { row, body })
}

/// `turnIdBindings row` — 13 PI bindings, schedule turn-identity cols 0..12 → outer PI 0..12.
fn turn_id_bindings(row: VmRow) -> Vec<VmConstraint2> {
    let mut v = Vec::new();
    for i in 0..4 {
        v.push(pi_bind(row, TURN_HASH_BASE + i, TURN_HASH_BASE + i));
    }
    for i in 0..4 {
        v.push(pi_bind(
            row,
            EFFECTS_HASH_GLOBAL_BASE + i,
            EFFECTS_HASH_GLOBAL_BASE + i,
        ));
    }
    v.push(pi_bind(row, ACTOR_NONCE, ACTOR_NONCE));
    for i in 0..4 {
        v.push(pi_bind(
            row,
            PREVIOUS_RECEIPT_HASH_BASE + i,
            PREVIOUS_RECEIPT_HASH_BASE + i,
        ));
    }
    v
}

/// `scheduleReplay` — 7 count + 28 root `col == expected` gates.
fn schedule_replay() -> Vec<VmConstraint2> {
    let mut v = Vec::new();
    for k in 0..COUNTS_LEN {
        v.push(col_eq_col(COUNTS_BASE + k, EXPECTED_COUNTS_BASE + k));
    }
    for k in 0..ROOTS_LEN {
        v.push(col_eq_col(ROOTS_BASE + k, EXPECTED_ROOTS_BASE + k));
    }
    v
}

fn hand_built_desc() -> EffectVmDescriptor2 {
    let mut constraints = Vec::new();
    // CG-2 (turn identity, first AND last rows).
    constraints.extend(turn_id_bindings(VmRow::First));
    constraints.extend(turn_id_bindings(VmRow::Last));
    // CG-3 (schedule replay).
    constraints.extend(schedule_replay());
    // CG-4 (agent accounting): booleans + padding + the two cumulative window transitions.
    constraints.push(bool_gate(IS_AGENT_CELL));
    constraints.push(bool_gate(CONSISTENT_INDICATOR_COL));
    constraints.push(padding_gate());
    constraints.push(cum_transition(IS_AGENT_CUMULATIVE_COL, IS_AGENT_CELL));
    constraints.push(cum_transition(N_CELLS_ACTIVE_COL, CONSISTENT_INDICATOR_COL));
    // Boundaries: row-0 seeds, last-row cum==1, last-row n==pi[N_CELLS].
    constraints.push(boundary(
        VmRow::First,
        LeanExpr::add(
            LeanExpr::Var(IS_AGENT_CUMULATIVE_COL),
            LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(IS_AGENT_CELL)),
        ),
    ));
    constraints.push(boundary(
        VmRow::First,
        LeanExpr::add(
            LeanExpr::Var(N_CELLS_ACTIVE_COL),
            LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(CONSISTENT_INDICATOR_COL)),
        ),
    ));
    constraints.push(boundary(
        VmRow::Last,
        LeanExpr::add(LeanExpr::Var(IS_AGENT_CUMULATIVE_COL), LeanExpr::Const(-1)),
    ));
    constraints.push(pi_bind(VmRow::Last, N_CELLS_ACTIVE_COL, PI_N_CELLS));

    EffectVmDescriptor2 {
        name: "dregg-bilateral-aggregation-v2".to_string(),
        trace_width: AGG_WIDTH,
        public_input_count: OUTER_PI_COUNT,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    }
}

// ---------------------------------------------------------------------------
// Honest witness construction (the 87-column decoupled trace).
// ---------------------------------------------------------------------------

fn turn_id_fixture() -> [BabyBear; 13] {
    let mut a = [BabyBear::ZERO; 13];
    for (i, s) in a.iter_mut().enumerate() {
        *s = BabyBear::new(100 + i as u32);
    }
    a
}
fn counts_fixture(base: u32) -> [BabyBear; 7] {
    let mut a = [BabyBear::ZERO; 7];
    for (i, s) in a.iter_mut().enumerate() {
        *s = BabyBear::new(base + i as u32);
    }
    a
}
fn roots_fixture(base: u32) -> [BabyBear; 28] {
    let mut a = [BabyBear::ZERO; 28];
    for (i, s) in a.iter_mut().enumerate() {
        *s = BabyBear::new(base + i as u32);
    }
    a
}

/// An ACTIVE inner row: schedule turn-id + counts + roots + is_agent, with the EXPECTED columns
/// equal to the carried counts/roots (CG-3 replay holds), consistent = 1, and the two running
/// cumulatives (`cum`, `n`) explicit.
fn active_row(
    turn_id: &[BabyBear; 13],
    counts: &[BabyBear; 7],
    roots: &[BabyBear; 28],
    is_agent: u32,
    cum: u32,
    n: u32,
) -> Vec<BabyBear> {
    let mut r = vec![BabyBear::ZERO; AGG_WIDTH];
    r[..13].copy_from_slice(&turn_id[..13]);
    for k in 0..COUNTS_LEN {
        r[COUNTS_BASE + k] = counts[k];
        r[EXPECTED_COUNTS_BASE + k] = counts[k];
    }
    for k in 0..ROOTS_LEN {
        r[ROOTS_BASE + k] = roots[k];
        r[EXPECTED_ROOTS_BASE + k] = roots[k];
    }
    r[IS_AGENT_CELL] = BabyBear::new(is_agent);
    r[IS_AGENT_CUMULATIVE_COL] = BabyBear::new(cum);
    r[CONSISTENT_INDICATOR_COL] = BabyBear::new(1);
    r[N_CELLS_ACTIVE_COL] = BabyBear::new(n);
    r
}

/// A PADDING row: mirrors the turn-identity fields (so the last-row CG-2 `pi_binding` holds), carries
/// the cumulatives forward, and sets consistent = 0 (so the padding `gate` and CG-4 booleans hold).
fn padding_row(turn_id: &[BabyBear; 13], cum: u32, n: u32) -> Vec<BabyBear> {
    let mut r = vec![BabyBear::ZERO; AGG_WIDTH];
    r[..13].copy_from_slice(&turn_id[..13]);
    r[IS_AGENT_CUMULATIVE_COL] = BabyBear::new(cum);
    r[CONSISTENT_INDICATOR_COL] = BabyBear::ZERO;
    r[N_CELLS_ACTIVE_COL] = BabyBear::new(n);
    r
}

/// The fixed 23-felt outer PI: turn-identity 0..12, an (off-AIR) agent-cell-id block, `n_cells`, and
/// the bilateral-consistent flag (= 1, the off-descriptor verifier check).
fn outer_pi(turn_id: &[BabyBear; 13], n_cells: u32) -> Vec<BabyBear> {
    let mut pi = vec![BabyBear::ZERO; OUTER_PI_COUNT];
    pi[..13].copy_from_slice(&turn_id[..13]);
    for (i, slot) in pi.iter_mut().enumerate().take(21).skip(13) {
        *slot = BabyBear::new(900 + i as u32);
    }
    pi[PI_N_CELLS] = BabyBear::new(n_cells);
    pi[PI_BILATERAL_CONSISTENT] = BabyBear::ONE;
    pi
}

/// The honest bundle: ONE agent cell (row 0) + three padding rows (height 4). Cumulative agent = 1
/// at the last row (the single-agent invariant); n_cells = 1.
fn honest_single_agent() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let turn_id = turn_id_fixture();
    let counts = counts_fixture(500);
    let roots = roots_fixture(600);
    let row0 = active_row(&turn_id, &counts, &roots, 1, 1, 1);
    let pad = padding_row(&turn_id, 1, 1);
    let trace = vec![row0, pad.clone(), pad.clone(), pad];
    let pi = outer_pi(&turn_id, 1);
    (trace, pi)
}

/// A DOUBLE-SPEND bundle: TWO agent cells (rows 0, 1, both `is_agent = 1`) + two padding rows. The
/// cumulative reaches 2 at the last row — `cum == 1` (CG-4 boundary) is violated. `n_cells = 2` so
/// the last-row `n == pi[N_CELLS]` binding still holds and the ONLY unsatisfied constraint is the
/// single-agent boundary.
fn two_agent_cells() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let turn_id = turn_id_fixture();
    let row0 = active_row(&turn_id, &counts_fixture(500), &roots_fixture(600), 1, 1, 1);
    let row1 = active_row(&turn_id, &counts_fixture(700), &roots_fixture(800), 1, 2, 2);
    let pad = padding_row(&turn_id, 2, 2);
    let trace = vec![row0, row1, pad.clone(), pad];
    let pi = outer_pi(&turn_id, 2);
    (trace, pi)
}

/// `true` iff this `(trace, pis)` is REJECTED end-to-end — proving refuses OR the produced proof
/// fails to VERIFY against `pis`. `false` iff it both proves AND verifies. (Prove-then-verify is the
/// faithful gate; `prove_vm_descriptor2` self-verifies only under `debug_assertions`, so the
/// consumer's `verify_vm_descriptor2` is the real check on the release path.)
fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }));
    match r {
        Err(_) => true,
        Ok(Err(_)) => true,
        Ok(Ok(())) => false,
    }
}

/// STEP 1 — the emitted descriptor decodes and equals the hand-built twin, with the Lean-pinned
/// shape (width 87, PI 23, 70 constraints, exactly two window gates, no tables).
#[test]
fn bilateral_aggregation_emit_decodes_to_hand_built() {
    let decoded = parse_vm_descriptor2(GOLDEN_JSON).expect("the Lean-emitted golden JSON decodes");
    let hand = hand_built_desc();
    assert_eq!(
        decoded, hand,
        "the Lean-emitted descriptor must equal the independently hand-built descriptor"
    );
    assert_eq!(decoded.name, "dregg-bilateral-aggregation-v2");
    assert_eq!(decoded.trace_width, AGG_WIDTH);
    assert_eq!(decoded.public_input_count, OUTER_PI_COUNT);
    assert!(decoded.tables.is_empty(), "pure row-window AIR: no tables");
    assert_eq!(
        decoded.constraints.len(),
        70,
        "the Lean #guard pins 70 constraints"
    );
    let window_gates = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
        .count();
    assert_eq!(
        window_gates, 2,
        "exactly the two cumulative-sum window gates"
    );
    let pins = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
        .count();
    assert_eq!(
        pins, 27,
        "13 first + 13 last turn-identity pins + the last-row n pin"
    );
}

/// STEP 2 — THE POSITIVE POLE: an honest single-agent bundle proves through the emitted descriptor
/// and re-verifies against the 23-felt outer PI.
#[test]
fn honest_aggregation_proves_and_verifies() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pi) = honest_single_agent();
    let proof = prove_vm_descriptor2(&desc, &trace, &pi, &MemBoundaryWitness::default(), &[])
        .expect("the honest bundle witness must prove");
    verify_vm_descriptor2(&desc, &proof, &pi).expect("the honest proof must re-verify");
}

/// STEP 3a — MUTATION CANARY (CG-2 turn identity): honest trace, but a FORGED outer turn-hash PI.
/// The first/last-row `pi_binding` (col 0 == pi[0]) is violated → UNSAT.
#[test]
fn forged_turn_identity_pi_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pi) = honest_single_agent();
    assert!(
        !rejects(&desc, &trace, &pi),
        "honest witness must be accepted — else the canary is vacuous"
    );
    let mut forged = pi.clone();
    forged[0] = forged[0] + BabyBear::ONE;
    assert!(
        rejects(&desc, &trace, &forged),
        "a forged turn-identity PI must be REJECTED (CG-2 agreement)"
    );
}

/// STEP 3b — MUTATION CANARY (CG-3 schedule replay): the active row's carried `counts[0]` is bumped
/// off its `expected_counts[0]` column → the replay `gate` (col 13 − col 49) is nonzero → UNSAT.
#[test]
fn schedule_count_mismatch_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pi) = honest_single_agent();
    assert!(
        !rejects(&desc, &trace, &pi),
        "honest witness must be accepted"
    );
    let mut bad = trace.clone();
    bad[0][COUNTS_BASE] = bad[0][COUNTS_BASE] + BabyBear::ONE; // carried count now ≠ expected
    assert!(
        rejects(&desc, &bad, &pi),
        "a carried count that disagrees with its expected column must be REJECTED (CG-3 replay)"
    );
}

/// STEP 3c — MUTATION CANARY (CG-4 single-agent boundary): TWO agent cells in one bundle drive the
/// cumulative to 2, violating the `cum == 1` last-row boundary → UNSAT. The cross-federation
/// double-spend rejection.
#[test]
fn two_agent_cells_refuse() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (honest, honest_pi) = honest_single_agent();
    assert!(
        !rejects(&desc, &honest, &honest_pi),
        "honest single-agent witness must be accepted"
    );
    let (double, double_pi) = two_agent_cells();
    assert!(
        rejects(&desc, &double, &double_pi),
        "two agent cells (cum == 2) must be REJECTED (single-agent boundary / double-spend)"
    );
}

/// STEP 3d — MUTATION CANARY (the two-row window gate): the last row's running active-row counter is
/// forged (and pi[N_CELLS] moved to match, so the `n == pi` binding still holds) — the
/// `cumActiveTransition` window gate (`next[n] − local[n] − next[consistent]`) no longer vanishes on
/// the last transition → UNSAT. The NEW two-row cumulative primitive genuinely gates.
#[test]
fn forged_active_counter_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pi) = honest_single_agent();
    assert!(
        !rejects(&desc, &trace, &pi),
        "honest witness must be accepted"
    );
    let mut bad = trace.clone();
    let last = bad.len() - 1;
    bad[last][N_CELLS_ACTIVE_COL] = BabyBear::new(7);
    let mut bad_pi = pi.clone();
    bad_pi[PI_N_CELLS] = BabyBear::new(7); // keep the last-row n == pi binding satisfied
    assert!(
        rejects(&desc, &bad, &bad_pi),
        "a forged running active-row counter must be REJECTED (the cumulative window gate)"
    );
}
