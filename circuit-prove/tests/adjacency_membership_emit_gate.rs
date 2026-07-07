//! # The emit-from-Lean EQUALITY GATE — sorted-set NEIGHBOR ADJACENCY (non-membership lift).
//!
//! The descriptor is AUTHORED in Lean
//! (`metatheory/Dregg2/Circuit/Emit/AdjacencyMembershipEmit.lean`, `adjacencyDesc`) and its wire
//! string is byte-pinned there (`emitVmJson2` `#guard`). This test embeds that EXACT string
//! ([`GOLDEN_JSON`]) and:
//!
//!   1. DECODES it via [`parse_vm_descriptor2`] and asserts the decode equals an independently
//!      hand-built `EffectVmDescriptor2` (Lean emit ≡ Rust builder — a byte drift on either side
//!      breaks this OR the Lean `#guard`);
//!   2. KATs the arity-2 chip mapping: `chip_absorb_all_lanes(2, [a,b])[0] == hash_2_to_1(a,b)`
//!      (a `TID_P2` lookup with arity tag 2 IS `hash_2_to_1`, the binary Merkle-node hash);
//!   3. proves an HONEST adjacency witness (two consecutive leaves, genuine dual authentication
//!      paths to a shared root, indices reconstructed in-circuit) through [`prove_vm_descriptor2`],
//!      asserts ACCEPT, and re-verifies;
//!   4. the MUTATION CANARY — four tampers (a forged claimed root; a leaf that does not sit under
//!      the claimed root; a forged co-path sibling; and — THE CATCH TOOTH — a NON-CONSECUTIVE
//!      wide-bracket pair) each force a real UNSAT. Every canary is NON-VACUOUS: the honest
//!      consecutive witness is asserted to ACCEPT first.
//!
//! ## The catch tooth this preserves
//!
//! `verify_adjacency` (`circuit/src/membership_adjacency_air.rs:627`) enforces
//! `idx_upper - idx_lower == 1` in the RUST VERIFIER WRAPPER — it is absent from
//! `adjacency_descriptor()`'s constraint list. The Lean emit INTERNALIZES it as a
//! `Base(Boundary{Last})` gate `u_idx_out - l_idx_out - 1 == 0` on the trace columns already
//! pinned to the index PIs, so the forge-closing consecutiveness relation lives IN the descriptor
//! and cannot be silently dropped. Test `nonconsecutive_wide_bracket_refuses` exercises exactly
//! that in-circuit tooth (a genuinely dual-authenticated pair at indices 5 and 7 is REJECTED).

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    CHIP_OUT_LANES, CHIP_RATE, CHIP_TUPLE_LEN, EffectVmDescriptor2, LookupSpec, MemBoundaryWitness,
    TID_P2, VmConstraint2, WindowExpr, WindowGateSpec, chip_absorb_all_lanes, parse_vm_descriptor2,
    prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};
use dregg_circuit::poseidon2::hash_2_to_1;

/// The BYTE-IDENTICAL wire string Lean's `emitVmJson2 adjacencyDesc` emits (pinned by the `#guard`
/// in `AdjacencyMembershipEmit.lean`). If Lean's emitter drifts that `#guard` fails; if this
/// literal drifts the `decoded == hand_built` assertion fails. Neither can silently diverge.
const GOLDEN_JSON: &str = r#"{"name":"dregg-membership-adjacency::poseidon2-v1","ir":2,"trace_width":32,"public_input_count":5,"tables":[],"constraints":[{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"var","v":2},"r":{"t":"var","v":2}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":2}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":3},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":0}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":2},"r":{"t":"var","v":1}}},"r":{"t":"mul","l":{"t":"var","v":2},"r":{"t":"var","v":0}}}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":4},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":1}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":2},"r":{"t":"var","v":0}}},"r":{"t":"mul","l":{"t":"var","v":2},"r":{"t":"var","v":1}}}}}},{"t":"lookup","table":1,"tuple":[{"t":"const","v":2},{"t":"var","v":3},{"t":"var","v":4},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":5},{"t":"var","v":18},{"t":"var","v":19},{"t":"var","v":20},{"t":"var","v":21},{"t":"var","v":22},{"t":"var","v":23},{"t":"var","v":24}]},{"t":"gate","body":{"t":"add","l":{"t":"var","v":7},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":6}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":2},"r":{"t":"var","v":16}}}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":5}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":6},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":7}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"var","v":10}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":10}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":11},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"var","v":9}}},"r":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"var","v":8}}}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":12},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"var","v":8}}},"r":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"var","v":9}}}}}},{"t":"lookup","table":1,"tuple":[{"t":"const","v":2},{"t":"var","v":11},{"t":"var","v":12},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":13},{"t":"var","v":25},{"t":"var","v":26},{"t":"var","v":27},{"t":"var","v":28},{"t":"var","v":29},{"t":"var","v":30},{"t":"var","v":31}]},{"t":"gate","body":{"t":"add","l":{"t":"var","v":15},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":14}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"var","v":16}}}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":8},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":13}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":14},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":15}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":17},"r":{"t":"mul","l":{"t":"const","v":-2},"r":{"t":"var","v":16}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":16},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":17}}}},{"t":"pi_binding","row":"first","col":0,"pi_index":1},{"t":"pi_binding","row":"first","col":8,"pi_index":2},{"t":"pi_binding","row":"last","col":5,"pi_index":0},{"t":"pi_binding","row":"last","col":13,"pi_index":0},{"t":"pi_binding","row":"last","col":7,"pi_index":3},{"t":"pi_binding","row":"last","col":15,"pi_index":4},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"var","v":16},"r":{"t":"const","v":-1}}},{"t":"boundary","row":"first","body":{"t":"var","v":6}},{"t":"boundary","row":"first","body":{"t":"var","v":14}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"var","v":15},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":7}},"r":{"t":"const","v":-1}}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"mul","l":{"t":"var","v":2},"r":{"t":"var","v":2}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":2}}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"var","v":3},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":0}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":2},"r":{"t":"var","v":1}}},"r":{"t":"mul","l":{"t":"var","v":2},"r":{"t":"var","v":0}}}}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"var","v":4},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":1}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":2},"r":{"t":"var","v":0}}},"r":{"t":"mul","l":{"t":"var","v":2},"r":{"t":"var","v":1}}}}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"var","v":10}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":10}}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"var","v":11},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"var","v":9}}},"r":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"var","v":8}}}}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"var","v":12},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"var","v":8}}},"r":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"var","v":9}}}}}}],"hash_sites":[],"ranges":[]}"#;

// --- Trace column layout (must match `AdjacencyMembershipEmit.lean` §1). ---
const L_CUR: usize = 0;
const L_SIB: usize = 1;
const L_DIR: usize = 2;
const L_LEFT: usize = 3;
const L_RIGHT: usize = 4;
const L_PAR: usize = 5;
const L_IDX_IN: usize = 6;
const L_IDX_OUT: usize = 7;
const U_CUR: usize = 8;
const U_SIB: usize = 9;
const U_DIR: usize = 10;
const U_LEFT: usize = 11;
const U_RIGHT: usize = 12;
const U_PAR: usize = 13;
const U_IDX_IN: usize = 14;
const U_IDX_OUT: usize = 15;
const POW: usize = 16;
const POW2: usize = 17;
const L_PAR_LANE_BASE: usize = 18;
const U_PAR_LANE_BASE: usize = 25;
const ADJ_WIDTH: usize = 32;

// --- PI indices (`adj_pi`). ---
const PI_ROOT: usize = 0;
const PI_LEAF_LOWER: usize = 1;
const PI_LEAF_UPPER: usize = 2;
const PI_IDX_LOWER: usize = 3;
const PI_IDX_UPPER: usize = 4;

// ─────────────────────────── the hand-built descriptor twin ───────────────────────────

fn neg(e: LeanExpr) -> LeanExpr {
    LeanExpr::mul(LeanExpr::Const(-1), e)
}

/// An arity-2 `TID_P2` chip lookup absorbing `[a, b]` (`hash_2_to_1`), binding out0 to `out_col`
/// and lanes 1..7 to `lane_base..lane_base+7`. Built EXACTLY as Lean's `chipLookupTuple` (arity
/// tag = 2, `CHIP_RATE` zero-padded inputs, then out0 :: 7 lanes).
fn chip2_lookup(a: usize, b: usize, out_col: usize, lane_base: usize) -> VmConstraint2 {
    let inputs = [a, b];
    let mut tuple: Vec<LeanExpr> = Vec::with_capacity(CHIP_TUPLE_LEN);
    tuple.push(LeanExpr::Const(2)); // arity tag (= ins.length in Lean's chipLookupTuple)
    for i in 0..CHIP_RATE {
        tuple.push(match inputs.get(i) {
            Some(&c) => LeanExpr::Var(c),
            None => LeanExpr::Const(0),
        });
    }
    tuple.push(LeanExpr::Var(out_col)); // out0 = the parent digest
    for j in 0..(CHIP_OUT_LANES - 1) {
        tuple.push(LeanExpr::Var(lane_base + j));
    }
    assert_eq!(tuple.len(), CHIP_TUPLE_LEN);
    VmConstraint2::Lookup(LookupSpec {
        table: TID_P2,
        tuple,
    })
}

/// `left - cur - dir*sib + dir*cur`.
fn left_order_body(cur: usize, sib: usize, dir: usize, left: usize) -> LeanExpr {
    LeanExpr::add(
        LeanExpr::Var(left),
        LeanExpr::add(
            neg(LeanExpr::Var(cur)),
            LeanExpr::add(
                neg(LeanExpr::mul(LeanExpr::Var(dir), LeanExpr::Var(sib))),
                LeanExpr::mul(LeanExpr::Var(dir), LeanExpr::Var(cur)),
            ),
        ),
    )
}

/// `right - sib - dir*cur + dir*sib`.
fn right_order_body(cur: usize, sib: usize, dir: usize, right: usize) -> LeanExpr {
    LeanExpr::add(
        LeanExpr::Var(right),
        LeanExpr::add(
            neg(LeanExpr::Var(sib)),
            LeanExpr::add(
                neg(LeanExpr::mul(LeanExpr::Var(dir), LeanExpr::Var(cur))),
                LeanExpr::mul(LeanExpr::Var(dir), LeanExpr::Var(sib)),
            ),
        ),
    )
}

/// `dir*dir - dir`.
fn dir_binary_body(dir: usize) -> LeanExpr {
    LeanExpr::add(
        LeanExpr::mul(LeanExpr::Var(dir), LeanExpr::Var(dir)),
        neg(LeanExpr::Var(dir)),
    )
}

/// `idx_out - idx_in - dir*pow`.
fn idx_step_body(dir: usize, idx_in: usize, idx_out: usize) -> LeanExpr {
    LeanExpr::add(
        LeanExpr::Var(idx_out),
        LeanExpr::add(
            neg(LeanExpr::Var(idx_in)),
            neg(LeanExpr::mul(LeanExpr::Var(dir), LeanExpr::Var(POW))),
        ),
    )
}

/// A transition `windowGate` for the cross-row copy `next[hi] == local[lo]` (`nxt hi - loc lo`).
fn copy_window(hi: usize, lo: usize) -> VmConstraint2 {
    VmConstraint2::WindowGate(WindowGateSpec {
        body: WindowExpr::Add(
            Box::new(WindowExpr::Nxt(hi)),
            Box::new(WindowExpr::Mul(
                Box::new(WindowExpr::Const(-1)),
                Box::new(WindowExpr::Loc(lo)),
            )),
        ),
        on_transition: true,
    })
}

#[allow(clippy::too_many_arguments)]
fn path_block(
    cur: usize,
    sib: usize,
    dir: usize,
    left: usize,
    right: usize,
    par: usize,
    idx_in: usize,
    idx_out: usize,
    lane_base: usize,
) -> Vec<VmConstraint2> {
    vec![
        VmConstraint2::Base(VmConstraint::Gate(dir_binary_body(dir))),
        VmConstraint2::Base(VmConstraint::Gate(left_order_body(cur, sib, dir, left))),
        VmConstraint2::Base(VmConstraint::Gate(right_order_body(cur, sib, dir, right))),
        chip2_lookup(left, right, par, lane_base),
        VmConstraint2::Base(VmConstraint::Gate(idx_step_body(dir, idx_in, idx_out))),
        copy_window(cur, par),
        copy_window(idx_in, idx_out),
    ]
}

/// The independently-hand-built twin of the Lean `adjacencyDesc`.
fn hand_built_desc() -> EffectVmDescriptor2 {
    let mut constraints = Vec::new();
    constraints.extend(path_block(
        L_CUR,
        L_SIB,
        L_DIR,
        L_LEFT,
        L_RIGHT,
        L_PAR,
        L_IDX_IN,
        L_IDX_OUT,
        L_PAR_LANE_BASE,
    ));
    constraints.extend(path_block(
        U_CUR,
        U_SIB,
        U_DIR,
        U_LEFT,
        U_RIGHT,
        U_PAR,
        U_IDX_IN,
        U_IDX_OUT,
        U_PAR_LANE_BASE,
    ));
    // pow2 - 2*pow
    constraints.push(VmConstraint2::Base(VmConstraint::Gate(LeanExpr::add(
        LeanExpr::Var(POW2),
        LeanExpr::mul(LeanExpr::Const(-2), LeanExpr::Var(POW)),
    ))));
    constraints.push(copy_window(POW, POW2));
    // leaf/root/index PI bindings
    for (row, col, pi) in [
        (VmRow::First, L_CUR, PI_LEAF_LOWER),
        (VmRow::First, U_CUR, PI_LEAF_UPPER),
        (VmRow::Last, L_PAR, PI_ROOT),
        (VmRow::Last, U_PAR, PI_ROOT),
        (VmRow::Last, L_IDX_OUT, PI_IDX_LOWER),
        (VmRow::Last, U_IDX_OUT, PI_IDX_UPPER),
    ] {
        constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
            row,
            col,
            pi_index: pi,
        }));
    }
    // row-0 anchors: pow - 1, l_idx_in, u_idx_in
    constraints.push(VmConstraint2::Base(VmConstraint::Boundary {
        row: VmRow::First,
        body: LeanExpr::add(LeanExpr::Var(POW), LeanExpr::Const(-1)),
    }));
    constraints.push(VmConstraint2::Base(VmConstraint::Boundary {
        row: VmRow::First,
        body: LeanExpr::Var(L_IDX_IN),
    }));
    constraints.push(VmConstraint2::Base(VmConstraint::Boundary {
        row: VmRow::First,
        body: LeanExpr::Var(U_IDX_IN),
    }));
    // THE CATCH TOOTH: u_idx_out - l_idx_out - 1 on the Last row.
    constraints.push(VmConstraint2::Base(VmConstraint::Boundary {
        row: VmRow::Last,
        body: LeanExpr::add(
            LeanExpr::Var(U_IDX_OUT),
            LeanExpr::add(neg(LeanExpr::Var(L_IDX_OUT)), LeanExpr::Const(-1)),
        ),
    }));
    // THE LAST-ROW ORDERING FIX (`adjLastOrderFix`): the six child-ordering bodies re-lowered as
    // Last-row boundaries (three per path). The transition `.gate` copies of these fire on rows
    // 0..n-2; these boundaries cover the last row, so the top Merkle level's ordering is enforced
    // on every row (the deployed every-row `assert_zero` semantics) and cannot be forged.
    for body in [
        dir_binary_body(L_DIR),
        left_order_body(L_CUR, L_SIB, L_DIR, L_LEFT),
        right_order_body(L_CUR, L_SIB, L_DIR, L_RIGHT),
        dir_binary_body(U_DIR),
        left_order_body(U_CUR, U_SIB, U_DIR, U_LEFT),
        right_order_body(U_CUR, U_SIB, U_DIR, U_RIGHT),
    ] {
        constraints.push(VmConstraint2::Base(VmConstraint::Boundary {
            row: VmRow::Last,
            body,
        }));
    }
    EffectVmDescriptor2 {
        name: "dregg-membership-adjacency::poseidon2-v1".to_string(),
        trace_width: ADJ_WIDTH,
        public_input_count: 5,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    }
}

// ─────────────────────────────── the witness producer ───────────────────────────────

/// One Merkle authentication step (mirrors `membership_adjacency_air::AdjStep`).
#[derive(Clone, Copy)]
struct Step {
    sibling: BabyBear,
    dir: bool,
}

fn bit(b: bool) -> BabyBear {
    if b { BabyBear::ONE } else { BabyBear::ZERO }
}

/// Walk a leaf→root path, returning `(root, reconstructed_index)` (mirrors the hand AIR's `walk`).
fn walk(leaf: BabyBear, path: &[Step]) -> (BabyBear, u64) {
    let mut cur = leaf;
    let mut idx: u64 = 0;
    for (level, step) in path.iter().enumerate() {
        let (l, r) = if step.dir {
            (step.sibling, cur)
        } else {
            (cur, step.sibling)
        };
        cur = hash_2_to_1(l, r);
        if step.dir {
            idx |= 1u64 << level;
        }
    }
    (cur, idx)
}

/// Build the IR2-layout adjacency trace (one binary-tree level per row) for two authentication
/// paths, leaving the 14 chip-lane columns zero (`prove_vm_descriptor2` fills them). Returns
/// `(trace, root_lower, idx_lower, root_upper, idx_upper)`. Does NOT enforce consecutiveness or
/// equal roots — the DESCRIPTOR (its Last-row boundaries) is the judge, so a non-adjacent or
/// wrong-root pair produces a well-formed but UNSATISFYING trace.
fn build_trace(
    leaf_lower: BabyBear,
    lower_path: &[Step],
    leaf_upper: BabyBear,
    upper_path: &[Step],
) -> (Vec<Vec<BabyBear>>, BabyBear, u64, BabyBear, u64) {
    let depth = lower_path.len();
    assert_eq!(depth, upper_path.len());
    assert!(depth.is_power_of_two() && depth >= 2);

    let mut trace: Vec<Vec<BabyBear>> = Vec::with_capacity(depth);
    let mut l_cur = leaf_lower;
    let mut u_cur = leaf_upper;
    let mut pow = BabyBear::ONE;
    let mut l_idx_in = BabyBear::ZERO;
    let mut u_idx_in = BabyBear::ZERO;

    for level in 0..depth {
        let ls = lower_path[level];
        let us = upper_path[level];

        let l_dir = bit(ls.dir);
        let (l_left, l_right) = if ls.dir {
            (ls.sibling, l_cur)
        } else {
            (l_cur, ls.sibling)
        };
        let l_par = hash_2_to_1(l_left, l_right);
        let l_idx_out = l_idx_in + l_dir * pow;

        let u_dir = bit(us.dir);
        let (u_left, u_right) = if us.dir {
            (us.sibling, u_cur)
        } else {
            (u_cur, us.sibling)
        };
        let u_par = hash_2_to_1(u_left, u_right);
        let u_idx_out = u_idx_in + u_dir * pow;

        let pow2 = pow + pow;

        let mut row = vec![BabyBear::ZERO; ADJ_WIDTH];
        row[L_CUR] = l_cur;
        row[L_SIB] = ls.sibling;
        row[L_DIR] = l_dir;
        row[L_LEFT] = l_left;
        row[L_RIGHT] = l_right;
        row[L_PAR] = l_par;
        row[L_IDX_IN] = l_idx_in;
        row[L_IDX_OUT] = l_idx_out;
        row[U_CUR] = u_cur;
        row[U_SIB] = us.sibling;
        row[U_DIR] = u_dir;
        row[U_LEFT] = u_left;
        row[U_RIGHT] = u_right;
        row[U_PAR] = u_par;
        row[U_IDX_IN] = u_idx_in;
        row[U_IDX_OUT] = u_idx_out;
        row[POW] = pow;
        row[POW2] = pow2;
        trace.push(row);

        l_cur = l_par;
        u_cur = u_par;
        l_idx_in = l_idx_out;
        u_idx_in = u_idx_out;
        pow = pow2;
    }
    let (root_l, idx_l) = walk(leaf_lower, lower_path);
    let (root_u, idx_u) = walk(leaf_upper, upper_path);
    (trace, root_l, idx_l, root_u, idx_u)
}

/// Assemble the PI vector `[root, leaf_lower, leaf_upper, idx_lower, idx_upper]`.
fn pis(root: BabyBear, ll: BabyBear, lu: BabyBear, il: u64, iu: u64) -> Vec<BabyBear> {
    vec![root, ll, lu, BabyBear::from_u64(il), BabyBear::from_u64(iu)]
}

// --- a concrete depth-4 sorted tree (16 leaves) fixture (mirrors the hand-AIR tests). ---

fn build_tree(leaves: &[BabyBear]) -> Vec<Vec<BabyBear>> {
    assert!(leaves.len().is_power_of_two());
    let mut levels = vec![leaves.to_vec()];
    while levels.last().unwrap().len() > 1 {
        let cur = levels.last().unwrap();
        let mut next = Vec::with_capacity(cur.len() / 2);
        for pair in cur.chunks(2) {
            next.push(hash_2_to_1(pair[0], pair[1]));
        }
        levels.push(next);
    }
    levels
}

fn auth_path(levels: &[Vec<BabyBear>], mut index: usize) -> Vec<Step> {
    let depth = levels.len() - 1;
    let mut path = Vec::with_capacity(depth);
    for level in &levels[..depth] {
        let is_right = index & 1 == 1;
        let sibling = if is_right {
            level[index - 1]
        } else {
            level[index + 1]
        };
        path.push(Step {
            sibling,
            dir: is_right,
        });
        index >>= 1;
    }
    path
}

fn sample_leaves(n: usize) -> Vec<BabyBear> {
    (0..n).map(|i| BabyBear::new((i as u32 + 1) * 10)).collect()
}

/// `true` iff `(trace, pis)` is REJECTED end-to-end — proving refuses OR the produced proof fails
/// to VERIFY against `pis`. Prove-THEN-verify is the faithful gate (self-verify is off in release,
/// so the CONSUMER's `verify_vm_descriptor2` is the real Last-row `PiBinding`/`Boundary` check).
fn rejects(
    desc: &EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(
            desc,
            trace,
            public_inputs,
            &MemBoundaryWitness::default(),
            &[],
        )?;
        verify_vm_descriptor2(desc, &proof, public_inputs)
    }));
    match r {
        Err(_) => true,
        Ok(Err(_)) => true,
        Ok(Ok(())) => false,
    }
}

// ─────────────────────────────────────── tests ───────────────────────────────────────────

/// STEP 1 — the emitted descriptor decodes and equals the hand-built twin (Lean emit ≡ Rust
/// semantics), and has exactly the expected shape.
#[test]
fn adjacency_emit_decodes_to_hand_built() {
    let decoded = parse_vm_descriptor2(GOLDEN_JSON).expect("the Lean-emitted golden JSON decodes");
    let hand = hand_built_desc();
    assert_eq!(
        decoded, hand,
        "the Lean-emitted descriptor must equal the independently hand-built descriptor"
    );
    assert_eq!(decoded.trace_width, ADJ_WIDTH);
    assert_eq!(decoded.public_input_count, 5);
    assert_eq!(decoded.constraints.len(), 32);
    let chip_lookups = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
        .count();
    assert_eq!(
        chip_lookups, 2,
        "two child→parent chip lookups (lower ‖ upper)"
    );
    let window_gates = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
        .count();
    assert_eq!(window_gates, 5, "cur/idx carries (×2 paths) + pow carry");
    // Seven Last-row Boundaries: the consecutiveness catch tooth + the six ordering-fix bodies
    // (`adjLastOrderFix`, three per path) that make the top Merkle level's child-ordering
    // non-forgeable on the last row.
    let last_boundaries = decoded
        .constraints
        .iter()
        .filter(|c| {
            matches!(
                c,
                VmConstraint2::Base(VmConstraint::Boundary {
                    row: VmRow::Last,
                    ..
                })
            )
        })
        .count();
    assert_eq!(
        last_boundaries, 7,
        "consecutiveness catch tooth + six last-row ordering-fix boundaries"
    );
}

/// STEP 2 — the family-wide chip mapping: an arity-2 `TID_P2` absorb IS `hash_2_to_1`, and both
/// children are load-bearing (perturbing either changes the digest AND every lane).
#[test]
fn arity2_chip_lookup_is_hash_2_to_1() {
    let a = BabyBear::new(12345);
    let b = BabyBear::new(67890);
    let lanes = chip_absorb_all_lanes(2, &[a, b]);
    assert_eq!(
        lanes[0],
        hash_2_to_1(a, b),
        "arity-2 chip out0 must equal hash_2_to_1 (the binary Merkle-node hash)"
    );
    for (j, base) in [a, b].into_iter().enumerate() {
        let mut inp = [a, b];
        inp[j] = base + BabyBear::ONE;
        let alt = chip_absorb_all_lanes(2, &inp);
        for i in 0..CHIP_OUT_LANES {
            assert_ne!(
                lanes[i], alt[i],
                "chip lane {i} unchanged after perturbing child {j} — that input is dead"
            );
        }
    }
}

/// STEP 3 — THE POSITIVE POLE: an honest consecutive pair (leaves 5 & 6 of a depth-4 tree, both
/// genuinely authenticating to the shared root, indices reconstructed to 5 and 6) proves through
/// the emitted descriptor and re-verifies.
#[test]
fn honest_adjacency_proves_and_verifies() {
    let leaves = sample_leaves(16);
    let levels = build_tree(&leaves);
    let root = levels.last().unwrap()[0];
    let lp = auth_path(&levels, 5);
    let up = auth_path(&levels, 6);
    let (trace, root_l, il, root_u, iu) = build_trace(leaves[5], &lp, leaves[6], &up);
    assert_eq!(root_l, root, "lower path authenticates to the tree root");
    assert_eq!(root_u, root, "upper path authenticates to the tree root");
    assert_eq!(
        (il, iu),
        (5, 6),
        "indices reconstruct in-circuit to 5 and 6"
    );

    let pi = pis(root, leaves[5], leaves[6], il, iu);
    let proof = prove_vm_descriptor2(
        parse_vm_descriptor2(GOLDEN_JSON).as_ref().unwrap(),
        &trace,
        &pi,
        &MemBoundaryWitness::default(),
        &[],
    )
    .expect("the honest consecutive witness must prove");
    verify_vm_descriptor2(
        parse_vm_descriptor2(GOLDEN_JSON).as_ref().unwrap(),
        &proof,
        &pi,
    )
    .expect("the honest proof must re-verify against the public inputs");
}

/// STEP 4a — MUTATION CANARY (claimed root): honest consecutive trace, FORGED public root. Both
/// Last-row root pins (`l_par`/`u_par == PI[root]`) are violated → UNSAT.
#[test]
fn forged_claimed_root_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let leaves = sample_leaves(16);
    let levels = build_tree(&leaves);
    let root = levels.last().unwrap()[0];
    let lp = auth_path(&levels, 5);
    let up = auth_path(&levels, 6);
    let (trace, _rl, il, _ru, iu) = build_trace(leaves[5], &lp, leaves[6], &up);
    let honest_pi = pis(root, leaves[5], leaves[6], il, iu);
    assert!(
        !rejects(&desc, &trace, &honest_pi),
        "honest witness must be accepted — else the canary is vacuous"
    );
    let forged_pi = pis(root + BabyBear::ONE, leaves[5], leaves[6], il, iu);
    assert!(
        rejects(&desc, &trace, &forged_pi),
        "a forged claimed root must be REJECTED (Last-row root pin)"
    );
}

/// STEP 4b — MUTATION CANARY (leaf): a tampered lower leaf, honestly walked to a DIFFERENT root,
/// but CLAIMING the original root. The lower Last-row root pin (`l_par == PI[root]`) is violated
/// → UNSAT. The leaf is bound to the root (the membership tooth).
#[test]
fn tampered_leaf_keeping_root_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let leaves = sample_leaves(16);
    let levels = build_tree(&leaves);
    let root = levels.last().unwrap()[0];
    let lp = auth_path(&levels, 5);
    let up = auth_path(&levels, 6);

    // sanity: the honest pair accepts (non-vacuity).
    let (h_trace, _rl, il, _ru, iu) = build_trace(leaves[5], &lp, leaves[6], &up);
    assert!(!rejects(
        &desc,
        &h_trace,
        &pis(root, leaves[5], leaves[6], il, iu)
    ));

    let tampered_leaf = leaves[5] + BabyBear::ONE;
    let (trace, root_l, til, _ru, tiu) = build_trace(tampered_leaf, &lp, leaves[6], &up);
    assert_ne!(
        root_l, root,
        "changing the leaf must change its authenticated root"
    );
    // claim the ORIGINAL root; the lower path no longer reaches it.
    let pi = pis(root, tampered_leaf, leaves[6], til, tiu);
    assert!(
        rejects(&desc, &trace, &pi),
        "a leaf that does not sit under the claimed root must be REJECTED"
    );
}

/// STEP 4c — MUTATION CANARY (sibling): a tampered lower co-path sibling, honestly walked to a
/// different root, claiming the original. The forged co-path breaks the Last-row root pin → UNSAT.
#[test]
fn tampered_sibling_keeping_root_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let leaves = sample_leaves(16);
    let levels = build_tree(&leaves);
    let root = levels.last().unwrap()[0];
    let mut lp = auth_path(&levels, 5);
    let up = auth_path(&levels, 6);

    let (h_trace, _rl, il, _ru, iu) = build_trace(leaves[5], &lp, leaves[6], &up);
    assert!(!rejects(
        &desc,
        &h_trace,
        &pis(root, leaves[5], leaves[6], il, iu)
    ));

    lp[0].sibling += BabyBear::ONE; // forge the level-0 co-path node
    let (trace, root_l, til, _ru, tiu) = build_trace(leaves[5], &lp, leaves[6], &up);
    assert_ne!(
        root_l, root,
        "changing a co-path sibling must change the root"
    );
    let pi = pis(root, leaves[5], leaves[6], til, tiu);
    assert!(
        rejects(&desc, &trace, &pi),
        "a forged co-path sibling must be REJECTED"
    );
}

/// STEP 4d — MUTATION CANARY (THE CATCH TOOTH): a genuinely dual-authenticated but NON-CONSECUTIVE
/// pair (leaves 5 & 7 of the same tree — both authenticate to the shared root, indices reconstruct
/// to 5 and 7). EVERY other constraint holds; ONLY the internalized consecutiveness Last-row
/// boundary (`u_idx_out - l_idx_out - 1 == 7 - 5 - 1 = 1 ≠ 0`) fails → UNSAT. This is the
/// wide-bracket forge `verify_adjacency:627` closes, now enforced IN the descriptor.
#[test]
fn nonconsecutive_wide_bracket_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let leaves = sample_leaves(16);
    let levels = build_tree(&leaves);
    let root = levels.last().unwrap()[0];

    // non-vacuity: the ADJACENT pair (5,6) accepts.
    let lp6 = auth_path(&levels, 5);
    let up6 = auth_path(&levels, 6);
    let (t_ok, _rl, il6, _ru, iu6) = build_trace(leaves[5], &lp6, leaves[6], &up6);
    assert!(!rejects(
        &desc,
        &t_ok,
        &pis(root, leaves[5], leaves[6], il6, iu6)
    ));

    // the wide bracket (5,7) — both real Merkle members, but NOT adjacent.
    let lp = auth_path(&levels, 5);
    let up = auth_path(&levels, 7);
    let (trace, root_l, il, root_u, iu) = build_trace(leaves[5], &lp, leaves[7], &up);
    assert_eq!(root_l, root, "leaf 5 still authenticates to the real root");
    assert_eq!(root_u, root, "leaf 7 still authenticates to the real root");
    assert_eq!(
        (il, iu),
        (5, 7),
        "indices reconstruct to a NON-adjacent 5 and 7"
    );
    let pi = pis(root, leaves[5], leaves[7], il, iu);
    assert!(
        rejects(&desc, &trace, &pi),
        "a non-consecutive wide-bracket pair must be REJECTED (the in-circuit consecutiveness tooth)"
    );
}

/// STEP 4e — THE CATCH TOOTH IS PRECISELY LOAD-BEARING (a descriptor-mutation canary that proves
/// STEP 4d is NON-VACUOUS). The very same wide-bracket (5,7) trace that STEP 4d REJECTS is ACCEPTED
/// by a descriptor identical to `adjacencyDesc` EXCEPT with the Last-row consecutiveness boundary
/// deleted. So the (5,7) trace satisfies every other constraint (both paths authenticate, indices
/// match their PIs, leaves match the First pins) — its rejection in STEP 4d is caused by the
/// internalized consecutiveness tooth and by nothing unrelated.
#[test]
fn catch_tooth_is_precisely_load_bearing() {
    let full = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    // The tooth-removed variant: drop ONLY the consecutiveness Last-row boundary (leaving the six
    // ordering-fix boundaries intact), so the (5,7) rejection is isolated to that one gate.
    let cons = VmConstraint2::Base(VmConstraint::Boundary {
        row: VmRow::Last,
        body: LeanExpr::add(
            LeanExpr::Var(U_IDX_OUT),
            LeanExpr::add(neg(LeanExpr::Var(L_IDX_OUT)), LeanExpr::Const(-1)),
        ),
    });
    let mut tooth_removed = full.clone();
    tooth_removed.constraints.retain(|c| c != &cons);
    assert_eq!(
        tooth_removed.constraints.len(),
        full.constraints.len() - 1,
        "exactly the one consecutiveness Last-row boundary was removed"
    );

    let leaves = sample_leaves(16);
    let levels = build_tree(&leaves);
    let root = levels.last().unwrap()[0];
    let lp = auth_path(&levels, 5);
    let up = auth_path(&levels, 7);
    let (trace, root_l, il, root_u, iu) = build_trace(leaves[5], &lp, leaves[7], &up);
    assert_eq!((root_l, root_u), (root, root));
    assert_eq!((il, iu), (5, 7));
    let pi = pis(root, leaves[5], leaves[7], il, iu);

    // REJECTED by the full descriptor (tooth present)…
    assert!(
        rejects(&full, &trace, &pi),
        "with the tooth, the wide bracket is rejected"
    );
    // …but ACCEPTED once the tooth is removed — the tooth, and only the tooth, is what bit.
    assert!(
        !rejects(&tooth_removed, &trace, &pi),
        "without the consecutiveness tooth the wide-bracket (5,7) trace is otherwise fully valid"
    );
}

/// STEP 4f — MUTATION CANARY (THE LAST-ROW ORDERING FIX): a genuinely dual-authenticated (5,6) pair
/// whose TOP Merkle level is FORGED. On the last row both paths' children are overwritten with an
/// unrelated pair `(x, y)` and the claimed root is `hash(x, y)`, so every hash/root/index/consecutive
/// constraint still holds — yet the top spine node `L_CUR[last]` is NOT a child of the disclosed root.
/// Under the transition-only ordering `.gate` (vacuous on the last row) this trace would satisfy the
/// descriptor; the landed `adjLastOrderFix` (six Last-row ordering boundaries) REJECTS it. Non-vacuity:
/// a descriptor with those six boundaries removed ACCEPTS the very same trace — so the ordering fix, and
/// only it, is what bit. This is exactly the forge the Lean refinement proof caught.
#[test]
fn forged_top_level_ordering_refuses() {
    let full = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let leaves = sample_leaves(16);
    let levels = build_tree(&leaves);
    let lp = auth_path(&levels, 5);
    let up = auth_path(&levels, 6);
    let (mut trace, _rl, il, _ru, iu) = build_trace(leaves[5], &lp, leaves[6], &up);
    assert_eq!((il, iu), (5, 6));

    // Forge the top (last) row's child pair for BOTH paths to an unrelated (x, y); claim hash(x, y).
    let x = BabyBear::new(777);
    let y = BabyBear::new(888);
    let forged_root = hash_2_to_1(x, y);
    let last = trace.len() - 1;
    trace[last][L_LEFT] = x;
    trace[last][L_RIGHT] = y;
    trace[last][L_PAR] = forged_root;
    trace[last][U_LEFT] = x;
    trace[last][U_RIGHT] = y;
    trace[last][U_PAR] = forged_root;
    let pi = pis(forged_root, leaves[5], leaves[6], il, iu);

    // REJECTED by the full descriptor: the last-row ordering boundary `L_LEFT - L_CUR ≠ 0` bites.
    assert!(
        rejects(&full, &trace, &pi),
        "a forged top-level child pair must be REJECTED (the last-row ordering fix)"
    );

    // Non-vacuity: drop the six ordering-fix boundaries (keep the consecutiveness tooth) — the same
    // forged trace is then ACCEPTED, so the ordering fix, and only it, is what rejected it.
    let cons = VmConstraint2::Base(VmConstraint::Boundary {
        row: VmRow::Last,
        body: LeanExpr::add(
            LeanExpr::Var(U_IDX_OUT),
            LeanExpr::add(neg(LeanExpr::Var(L_IDX_OUT)), LeanExpr::Const(-1)),
        ),
    });
    let mut ordering_removed = full.clone();
    ordering_removed.constraints.retain(|c| {
        !matches!(
            c,
            VmConstraint2::Base(VmConstraint::Boundary {
                row: VmRow::Last,
                ..
            })
        ) || c == &cons
    });
    assert_eq!(
        ordering_removed.constraints.len(),
        full.constraints.len() - 6,
        "exactly the six last-row ordering boundaries were removed"
    );
    assert!(
        !rejects(&ordering_removed, &trace, &pi),
        "without the ordering fix the forged top-level pair is otherwise fully valid"
    );
}
