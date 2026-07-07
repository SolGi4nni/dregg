//! # The emit-from-Lean EQUALITY GATE — alpha-batch NON-REVOCATION accumulator.
//!
//! The descriptor is AUTHORED in Lean
//! (`metatheory/Dregg2/Circuit/Emit/AccumulatorNonRevocationEmit.lean`, `accumulatorNonRevDesc`)
//! and its wire string is byte-pinned there (`emitVmJson2` `#guard`). This test embeds that EXACT
//! string ([`GOLDEN_JSON`]) and:
//!
//!   1. DECODES it via [`parse_vm_descriptor2`] and asserts the decode equals an independently
//!      hand-built `EffectVmDescriptor2` (Lean emit ≡ Rust semantics — a byte drift on either side
//!      breaks this OR the Lean `#guard`). The hand-built twin is transcribed directly from the
//!      DSL hand AIR `circuit/src/dsl/accumulator.rs::accumulator_circuit_descriptor` term-for-term.
//!   2. proves an HONEST non-revocation witness (the genuine DSL trace, `generate_accumulator_trace`)
//!      through [`prove_vm_descriptor2`], asserts ACCEPT, and re-verifies the proof;
//!   3. the MUTATION CANARIES — each tampers the witness/PIs and asserts the prove-or-verify REFUSES,
//!      with each rejection tied to a NAMED constraint (the accumulator binding, the `v ≠ 0` /
//!      non-membership `check`, the `alpha_aux` constancy soundness tooth, the last-row boundary,
//!      the public `Acc`/`alpha` bindings). Every canary is NON-VACUOUS: the honest witness is
//!      asserted ACCEPTED first.
//!
//! Mapping (see the Lean file's header for the full argument): C1..C4 + `sum==acc_aux` +
//! `check==(1,0,0,0)` → `.base (.gate)` on the transition domain (+ `.base (.boundary .last)` twins
//! for `sum`/`check`); `alpha_aux`/`acc_aux` → `.base (.piBinding .first)` + a `.windowGate`
//! CONSTANCY gate. The constancy gate is the IR-v2-native realization of "the aux carries the true
//! PI on every row"; it is a strict soundness strengthening over the DSL hand AIR (which pins
//! `alpha_aux` on row 0 only, leaving C1 vacuous on later rows).

use std::panic::AssertUnwindSafe;

use dregg_circuit::accumulator_types::{
    ACCUMULATOR_WIDTH, AccumulatorNonMembershipWitness, AccumulatorNonRevocationWitness, ExtElem,
    col, compute_accumulator, derive_alpha, pi,
};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, VmConstraint2, WindowExpr, WindowGateSpec,
    parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::dsl::accumulator::generate_accumulator_trace;
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};
use dregg_circuit::poseidon2::hash_many;

/// The BYTE-IDENTICAL wire string Lean's `emitVmJson2 accumulatorNonRevDesc` emits (pinned by the
/// `#guard` in `AccumulatorNonRevocationEmit.lean`). If Lean's emitter drifts, that `#guard` fails;
/// if this literal drifts, the `decoded == hand_built` assertion fails. Neither can silently diverge.
const GOLDEN_JSON: &str = r#"{"name":"dregg-accumulator-nonrev-emit-v2","ir":2,"trace_width":40,"public_input_count":9,"tables":[],"constraints":[{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":12}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":32}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":0}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":13}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":33}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":14}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":34}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":2}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":15}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":35}}},"r":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":3}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":16}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":4},"r":{"t":"var","v":12}}}},"r":{"t":"mul","l":{"t":"const","v":-11},"r":{"t":"mul","l":{"t":"var","v":5},"r":{"t":"var","v":15}}}},"r":{"t":"mul","l":{"t":"const","v":-11},"r":{"t":"mul","l":{"t":"var","v":6},"r":{"t":"var","v":14}}}},"r":{"t":"mul","l":{"t":"const","v":-11},"r":{"t":"mul","l":{"t":"var","v":7},"r":{"t":"var","v":13}}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":17}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":4},"r":{"t":"var","v":13}}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":5},"r":{"t":"var","v":12}}}},"r":{"t":"mul","l":{"t":"const","v":-11},"r":{"t":"mul","l":{"t":"var","v":6},"r":{"t":"var","v":15}}}},"r":{"t":"mul","l":{"t":"const","v":-11},"r":{"t":"mul","l":{"t":"var","v":7},"r":{"t":"var","v":14}}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":18}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":4},"r":{"t":"var","v":14}}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":5},"r":{"t":"var","v":13}}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":6},"r":{"t":"var","v":12}}}},"r":{"t":"mul","l":{"t":"const","v":-11},"r":{"t":"mul","l":{"t":"var","v":7},"r":{"t":"var","v":15}}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":19}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":4},"r":{"t":"var","v":15}}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":5},"r":{"t":"var","v":14}}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":6},"r":{"t":"var","v":13}}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":7},"r":{"t":"var","v":12}}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":20}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":21}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":17}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":22}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":18}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":10}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":23}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":19}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":11}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":28}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"var","v":24}}}},"r":{"t":"mul","l":{"t":"const","v":-11},"r":{"t":"mul","l":{"t":"var","v":9},"r":{"t":"var","v":27}}}},"r":{"t":"mul","l":{"t":"const","v":-11},"r":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"var","v":26}}}},"r":{"t":"mul","l":{"t":"const","v":-11},"r":{"t":"mul","l":{"t":"var","v":11},"r":{"t":"var","v":25}}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":29}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"var","v":25}}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":9},"r":{"t":"var","v":24}}}},"r":{"t":"mul","l":{"t":"const","v":-11},"r":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"var","v":27}}}},"r":{"t":"mul","l":{"t":"const","v":-11},"r":{"t":"mul","l":{"t":"var","v":11},"r":{"t":"var","v":26}}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":30}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"var","v":26}}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":9},"r":{"t":"var","v":25}}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"var","v":24}}}},"r":{"t":"mul","l":{"t":"const","v":-11},"r":{"t":"mul","l":{"t":"var","v":11},"r":{"t":"var","v":27}}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":31}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"var","v":27}}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":9},"r":{"t":"var","v":26}}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"var","v":25}}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"mul","l":{"t":"var","v":11},"r":{"t":"var","v":24}}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":20}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":36}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":21}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":37}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":22}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":38}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":23}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":39}}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":20}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":36}}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":21}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":37}}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":22}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":38}}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":23}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":39}}}},{"t":"gate","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":28}},"r":{"t":"const","v":-1}}},{"t":"gate","body":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":29}}},{"t":"gate","body":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":30}}},{"t":"gate","body":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":31}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":28}},"r":{"t":"const","v":-1}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":29}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":30}}},{"t":"boundary","row":"last","body":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":31}}},{"t":"pi_binding","row":"first","col":32,"pi_index":4},{"t":"pi_binding","row":"first","col":33,"pi_index":5},{"t":"pi_binding","row":"first","col":34,"pi_index":6},{"t":"pi_binding","row":"first","col":35,"pi_index":7},{"t":"pi_binding","row":"first","col":36,"pi_index":0},{"t":"pi_binding","row":"first","col":37,"pi_index":1},{"t":"pi_binding","row":"first","col":38,"pi_index":2},{"t":"pi_binding","row":"first","col":39,"pi_index":3},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":32},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":32}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":33},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":33}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":34},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":34}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":35},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":35}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":36},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":36}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":37},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":37}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":38},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":38}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":39},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":39}}}}],"hash_sites":[],"ranges":[]}"#;

// --- Trace column layout (must match `AccumulatorNonRevocationEmit.lean` §1 == `accumulator_types::col`). ---
const HASH: usize = 0;
const QUOTIENT: usize = 4;
const REMAINDER: usize = 8;
const DIFF: usize = 12;
const PRODUCT: usize = 16;
const SUM: usize = 20;
const V_INV: usize = 24;
const CHECK: usize = 28;
const ALPHA_AUX: usize = 32;
const ACC_AUX: usize = 36;
const WIDTH: usize = 40;
const PI_ACC: usize = 0;
const PI_ALPHA: usize = 4;
const PI_COUNT: usize = 9;
const W: i64 = 11;

// ---------------------------------------------------------------------------
// The hand-built descriptor twin (transcribed from `dsl/accumulator.rs`, byte-for-byte)
// ---------------------------------------------------------------------------

/// `coeff · col`.
fn coeff_var(k: i64, c: usize) -> LeanExpr {
    LeanExpr::mul(LeanExpr::Const(k), LeanExpr::Var(c))
}
/// `coeff · colA · colB` (the ext-field cross term).
fn coeff_mul(k: i64, c: usize, d: usize) -> LeanExpr {
    LeanExpr::mul(
        LeanExpr::Const(k),
        LeanExpr::mul(LeanExpr::Var(c), LeanExpr::Var(d)),
    )
}
/// Left-associated sum of terms (mirrors Lean's `.add (.add … )` nesting).
fn addl(terms: Vec<LeanExpr>) -> LeanExpr {
    terms
        .into_iter()
        .reduce(LeanExpr::add)
        .expect("non-empty term list")
}

/// C1 lane `i`: `diff[i] − alpha_aux[i] + h[i]`.
fn c1_body(i: usize) -> LeanExpr {
    addl(vec![
        coeff_var(1, DIFF + i),
        coeff_var(-1, ALPHA_AUX + i),
        coeff_var(1, HASH + i),
    ])
}
/// C3 lane `i`: `sum[i] − prod[i] − v[i]`.
fn c3_body(i: usize) -> LeanExpr {
    addl(vec![
        coeff_var(1, SUM + i),
        coeff_var(-1, PRODUCT + i),
        coeff_var(-1, REMAINDER + i),
    ])
}
/// `sum[i] − acc_aux[i]`.
fn sum_acc_body(i: usize) -> LeanExpr {
    addl(vec![coeff_var(1, SUM + i), coeff_var(-1, ACC_AUX + i)])
}
/// `check[i] − value_i`, `value = (1,0,0,0)`.
fn check_one_body(i: usize) -> LeanExpr {
    if i == 0 {
        LeanExpr::add(coeff_var(1, CHECK), LeanExpr::Const(-1))
    } else {
        coeff_var(1, CHECK + i)
    }
}
/// Ext-field multiply residual `o[lane] − (a·b)[lane]` over `BabyBear[X]/(X^4−11)`, matching the
/// `accumulator.rs` term lists byte-for-byte.
fn ext_mul_lane(o: usize, a: usize, b: usize, lane: usize) -> LeanExpr {
    match lane {
        0 => addl(vec![
            coeff_var(1, o),
            coeff_mul(-1, a, b),
            coeff_mul(-W, a + 1, b + 3),
            coeff_mul(-W, a + 2, b + 2),
            coeff_mul(-W, a + 3, b + 1),
        ]),
        1 => addl(vec![
            coeff_var(1, o + 1),
            coeff_mul(-1, a, b + 1),
            coeff_mul(-1, a + 1, b),
            coeff_mul(-W, a + 2, b + 3),
            coeff_mul(-W, a + 3, b + 2),
        ]),
        2 => addl(vec![
            coeff_var(1, o + 2),
            coeff_mul(-1, a, b + 2),
            coeff_mul(-1, a + 1, b + 1),
            coeff_mul(-1, a + 2, b),
            coeff_mul(-W, a + 3, b + 3),
        ]),
        _ => addl(vec![
            coeff_var(1, o + 3),
            coeff_mul(-1, a, b + 3),
            coeff_mul(-1, a + 1, b + 2),
            coeff_mul(-1, a + 2, b + 1),
            coeff_mul(-1, a + 3, b),
        ]),
    }
}
/// The constancy window body for column `c`: `next[c] − loc[c]`.
fn const_window(c: usize) -> WindowExpr {
    WindowExpr::Add(
        Box::new(WindowExpr::Nxt(c)),
        Box::new(WindowExpr::Mul(
            Box::new(WindowExpr::Const(-1)),
            Box::new(WindowExpr::Loc(c)),
        )),
    )
}

fn gate(body: LeanExpr) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::Gate(body))
}
fn last_boundary(body: LeanExpr) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::Boundary {
        row: VmRow::Last,
        body,
    })
}
fn first_pin(c: usize, p: usize) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::First,
        col: c,
        pi_index: p,
    })
}
fn win(body: WindowExpr) -> VmConstraint2 {
    VmConstraint2::WindowGate(WindowGateSpec {
        body,
        on_transition: true,
    })
}

/// The independently-hand-built twin of the Lean `accumulatorNonRevDesc`. The constraint ORDER
/// matches the Lean `constraints := c1Gates ++ c2Gates ++ … ++ accConst` concatenation exactly.
fn hand_built_desc() -> EffectVmDescriptor2 {
    let mut constraints: Vec<VmConstraint2> = Vec::new();
    // C1..C4 gates (transition domain).
    for i in 0..4 {
        constraints.push(gate(c1_body(i)));
    }
    for i in 0..4 {
        constraints.push(gate(ext_mul_lane(PRODUCT, QUOTIENT, DIFF, i)));
    }
    for i in 0..4 {
        constraints.push(gate(c3_body(i)));
    }
    for i in 0..4 {
        constraints.push(gate(ext_mul_lane(CHECK, REMAINDER, V_INV, i)));
    }
    // sum==acc_aux: gate + last-row boundary.
    for i in 0..4 {
        constraints.push(gate(sum_acc_body(i)));
    }
    for i in 0..4 {
        constraints.push(last_boundary(sum_acc_body(i)));
    }
    // check==(1,0,0,0): gate + last-row boundary.
    for i in 0..4 {
        constraints.push(gate(check_one_body(i)));
    }
    for i in 0..4 {
        constraints.push(last_boundary(check_one_body(i)));
    }
    // alpha_aux / acc_aux first-row pins.
    for i in 0..4 {
        constraints.push(first_pin(ALPHA_AUX + i, PI_ALPHA + i));
    }
    for i in 0..4 {
        constraints.push(first_pin(ACC_AUX + i, PI_ACC + i));
    }
    // alpha_aux / acc_aux constancy window gates.
    for i in 0..4 {
        constraints.push(win(const_window(ALPHA_AUX + i)));
    }
    for i in 0..4 {
        constraints.push(win(const_window(ACC_AUX + i)));
    }
    EffectVmDescriptor2 {
        name: "dregg-accumulator-nonrev-emit-v2".to_string(),
        trace_width: WIDTH,
        public_input_count: PI_COUNT,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    }
}

// ---------------------------------------------------------------------------
// Honest witness (the genuine DSL trace) + the accept/reject oracle
// ---------------------------------------------------------------------------

fn make_hash(seed: u32) -> BabyBear {
    hash_many(&[BabyBear::new(seed), BabyBear::new(0xCAFE)])
}

/// A genuine 8-row non-revocation trace (3 ancestors, none in the revocation set) + its 9 PIs,
/// built by the DEPLOYED DSL trace generator (`generate_accumulator_trace`). Returns
/// `(trace, pis, acc, alpha)`.
fn honest_fixture() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>, ExtElem, ExtElem) {
    let revocation_set: Vec<BabyBear> = (1..=5).map(|i| make_hash(i * 50)).collect();
    let alpha = derive_alpha(&revocation_set);
    let acc = compute_accumulator(&revocation_set, alpha);

    let ancestors: Vec<BabyBear> = (1..=3).map(|i| make_hash(i * 7777)).collect();
    let mut anc_w = Vec::new();
    for &h in &ancestors {
        assert!(
            !revocation_set.contains(&h),
            "ancestor must be a non-member"
        );
        let mut rem_base = BabyBear::ONE;
        for &rh in &revocation_set {
            rem_base = rem_base * (h - rh);
        }
        let remainder = ExtElem::from_base(rem_base);
        let diff = alpha.sub(ExtElem::from_base(h));
        let quotient = acc
            .sub(remainder)
            .mul(diff.inverse().expect("diff invertible"));
        anc_w.push(AccumulatorNonMembershipWitness {
            ancestor_hash: h,
            quotient,
            remainder,
        });
    }
    let witness = AccumulatorNonRevocationWitness { ancestors: anc_w };
    let (trace, pis) = generate_accumulator_trace(&witness, acc, alpha);
    assert_eq!(trace.len(), 8, "the fixture is an 8-row trace");
    assert_eq!(trace[0].len(), WIDTH);
    assert_eq!(pis.len(), PI_COUNT);
    (trace, pis, acc, alpha)
}

/// Write a self-consistent accumulator row for `(alpha_aux, h, v, acc)`: `diff = alpha_aux − h`,
/// `w = (acc − v)·diff⁻¹`, `prod = w·diff`, `sum = prod + v = acc`, `check = v·v⁻¹ = 1`. Every
/// per-row relation (C1..C4, `sum==acc_aux`, `check==(1,0,0,0)`) holds by construction; the ONLY
/// thing that can differ from an honest row is `alpha_aux` (constancy) — used to isolate the
/// constancy tooth in the drift canary.
fn self_consistent_row(alpha_aux: ExtElem, h: BabyBear, v: ExtElem, acc: ExtElem) -> Vec<BabyBear> {
    let mut row = vec![BabyBear::ZERO; WIDTH];
    let diff = alpha_aux.sub(ExtElem::from_base(h));
    let w = acc.sub(v).mul(diff.inverse().expect("diff invertible"));
    let prod = w.mul(diff);
    let sum = prod.add(v);
    let v_inv = v.inverse().expect("v nonzero");
    let check = v.mul(v_inv);
    ExtElem::from_base(h).write_to(&mut row, HASH);
    w.write_to(&mut row, QUOTIENT);
    v.write_to(&mut row, REMAINDER);
    diff.write_to(&mut row, DIFF);
    prod.write_to(&mut row, PRODUCT);
    sum.write_to(&mut row, SUM);
    v_inv.write_to(&mut row, V_INV);
    check.write_to(&mut row, CHECK);
    alpha_aux.write_to(&mut row, ALPHA_AUX);
    acc.write_to(&mut row, ACC_AUX);
    row
}

/// `true` iff this `(trace, pis)` is REJECTED end-to-end — proving refuses (the honest pre-flight
/// replay `Ir2Air::eval` catches a row-local violation) OR the produced proof fails to VERIFY. This
/// is the exact gate the merkle emit test uses.
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

// ---------------------------------------------------------------------------
// STEP 1 — Lean emit ≡ hand-built Rust semantics
// ---------------------------------------------------------------------------

#[test]
fn accumulator_nonrev_emit_decodes_to_hand_built() {
    let decoded = parse_vm_descriptor2(GOLDEN_JSON).expect("the Lean-emitted golden JSON decodes");
    let hand = hand_built_desc();
    assert_eq!(
        decoded, hand,
        "the Lean-emitted descriptor must equal the independently hand-built descriptor"
    );
    // shape pins
    assert_eq!(decoded.trace_width, WIDTH);
    assert_eq!(decoded.public_input_count, PI_COUNT);
    assert_eq!(decoded.constraints.len(), 48);
    assert!(
        decoded.tables.is_empty(),
        "pure arithmetic AIR — no declared tables"
    );
    let windows = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
        .count();
    assert_eq!(windows, 8, "4 alpha_aux + 4 acc_aux constancy window gates");
    let pins = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
        .count();
    assert_eq!(pins, 8, "4 alpha_aux + 4 acc_aux first-row pins");
    let lasts = decoded
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
    assert_eq!(lasts, 8, "4 sum + 4 check last-row boundaries");
    // The column layout the descriptor names is exactly the DSL hand AIR's.
    assert_eq!(HASH, col::HASH);
    assert_eq!(QUOTIENT, col::QUOTIENT);
    assert_eq!(REMAINDER, col::REMAINDER);
    assert_eq!(DIFF, col::DIFF);
    assert_eq!(PRODUCT, col::PRODUCT);
    assert_eq!(SUM, col::SUM);
    assert_eq!(V_INV, col::V_INV);
    assert_eq!(CHECK, col::CHECK);
    assert_eq!(ALPHA_AUX, ACCUMULATOR_WIDTH);
    assert_eq!(PI_ACC, pi::ACC_START);
    assert_eq!(PI_ALPHA, pi::ALPHA_START);
}

// ---------------------------------------------------------------------------
// STEP 2 — THE POSITIVE POLE
// ---------------------------------------------------------------------------

#[test]
fn honest_non_revocation_proves_and_verifies() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis, _acc, _alpha) = honest_fixture();
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the honest non-revocation witness must prove");
    verify_vm_descriptor2(&desc, &proof, &pis)
        .expect("the honest proof must re-verify against the public Acc/alpha");
}

// ---------------------------------------------------------------------------
// STEP 3 — THE MUTATION CANARIES (each tied to a named constraint)
// ---------------------------------------------------------------------------

/// CANARY (public accumulator binding): the claimed `Acc` PI is forged. The row-0 `acc_aux`
/// `PiBinding{First}` (`acc_aux[0] == pi[Acc]`) no longer holds → REJECTED.
#[test]
fn forged_accumulator_pi_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis, _acc, _alpha) = honest_fixture();
    assert!(
        !rejects(&desc, &trace, &pis),
        "honest witness must be accepted — else vacuous"
    );
    let mut forged = pis.clone();
    forged[PI_ACC] = forged[PI_ACC] + BabyBear::ONE; // wrong Acc lane 0
    assert!(
        rejects(&desc, &trace, &forged),
        "a forged public accumulator must be REJECTED (acc_aux first-row pin)"
    );
}

/// CANARY (public challenge binding): the claimed `alpha` PI is forged. The row-0 `alpha_aux`
/// `PiBinding{First}` no longer holds → REJECTED.
#[test]
fn forged_alpha_pi_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis, _acc, _alpha) = honest_fixture();
    assert!(
        !rejects(&desc, &trace, &pis),
        "honest witness must be accepted — else vacuous"
    );
    let mut forged = pis.clone();
    forged[PI_ALPHA] = forged[PI_ALPHA] + BabyBear::ONE; // wrong alpha lane 0
    assert!(
        rejects(&desc, &trace, &forged),
        "a forged public challenge must be REJECTED (alpha_aux first-row pin)"
    );
}

/// CANARY (THE SOUNDNESS STRENGTHENING — `alpha_aux` constancy): replace a MIDDLE row with a fully
/// self-consistent non-membership row (C1..C4 + `sum==acc_aux` + `check==(1,0,0,0)` all hold) whose
/// only deviation is a DRIFTED `alpha_aux = alpha + 1`. The DSL hand AIR — which pins `alpha_aux`
/// on row 0 only — would ACCEPT this (a free `alpha_aux` proves non-membership of anything). The
/// emitted descriptor's `.windowGate` constancy gate (`alpha_aux[next] − alpha_aux[loc] = 0`) is
/// the SOLE constraint that bites → REJECTED. Non-vacuity: the SAME row with `alpha_aux = alpha`
/// (no drift) is ACCEPTED, so the drift is precisely what the constancy tooth catches.
#[test]
fn tampered_alpha_aux_drift_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (base_trace, pis, acc, alpha) = honest_fixture();

    let h_pick = BabyBear::new(0x9E3779B9);
    let v_pick = ExtElem::from_base(BabyBear::new(7)); // any nonzero remainder
    let delta = ExtElem::from_base(BabyBear::ONE);

    // Non-vacuity: the self-consistent row with the TRUE alpha is accepted at row 1.
    let mut ok_trace = base_trace.clone();
    ok_trace[1] = self_consistent_row(alpha, h_pick, v_pick, acc);
    assert!(
        !rejects(&desc, &ok_trace, &pis),
        "a self-consistent row carrying the TRUE alpha must be accepted"
    );

    // The malicious row: identical construction, drifted alpha_aux. ONLY constancy can catch it.
    let mut bad_trace = base_trace.clone();
    bad_trace[1] = self_consistent_row(alpha.add(delta), h_pick, v_pick, acc);
    assert!(
        rejects(&desc, &bad_trace, &pis),
        "a drifted alpha_aux (free-challenge non-membership forgery) must be REJECTED \
         (the alpha_aux constancy window gate — the soundness strengthening over the hand AIR)"
    );
}

/// CANARY (`v ≠ 0` / genuine non-membership): zero the remainder `v` on a middle row. C3
/// (`sum − prod − v`) and C4 (`check − v·v_inv`) no longer hold (the honest `sum`/`check` were
/// computed with `v ≠ 0`) → REJECTED. A "member" (`v = 0`) cannot be laundered as a non-member.
#[test]
fn zero_remainder_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis, _acc, _alpha) = honest_fixture();
    assert!(
        !rejects(&desc, &trace, &pis),
        "honest witness must be accepted — else vacuous"
    );
    let mut bad = trace.clone();
    for k in 0..4 {
        bad[0][REMAINDER + k] = BabyBear::ZERO; // v := 0 on an active (non-last) row
    }
    assert!(
        rejects(&desc, &bad, &pis),
        "a zero remainder (claimed non-member that is a member) must be REJECTED (C3 / C4)"
    );
}

/// CANARY (accumulator equation `sum == Acc`): bump `sum` on a middle row. C3 (`sum − prod − v`)
/// and the `sum == acc_aux` gate no longer hold → REJECTED. The row's `sum` is pinned to the
/// committed accumulator.
#[test]
fn tampered_sum_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis, _acc, _alpha) = honest_fixture();
    assert!(
        !rejects(&desc, &trace, &pis),
        "honest witness must be accepted — else vacuous"
    );
    let mut bad = trace.clone();
    bad[0][SUM] = bad[0][SUM] + BabyBear::ONE;
    assert!(
        rejects(&desc, &bad, &pis),
        "a sum that does not equal Acc must be REJECTED (C3 + sum==acc_aux)"
    );
}

/// CANARY (last-row coverage): tamper `check[0]` on the LAST row only. The transition-domain gates
/// skip the last row, so ONLY the `.boundary .last` twin for `check==(1,0,0,0)` can bite → REJECTED.
/// This proves the last active ancestor row is genuinely constrained (the transition-domain gap the
/// last-row boundaries close).
#[test]
fn tampered_last_row_check_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis, _acc, _alpha) = honest_fixture();
    assert!(
        !rejects(&desc, &trace, &pis),
        "honest witness must be accepted — else vacuous"
    );
    let last = trace.len() - 1;
    let mut bad = trace.clone();
    bad[last][CHECK] = bad[last][CHECK] + BabyBear::ONE; // check[0] := 2 on the last row
    assert!(
        rejects(&desc, &bad, &pis),
        "a broken check on the last row must be REJECTED (the check last-row boundary)"
    );
}
