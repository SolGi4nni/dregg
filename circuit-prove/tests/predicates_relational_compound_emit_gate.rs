//! # The emit-from-Lean EQUALITY GATE — the `predicates-relational-compound` family.
//!
//! Two `EffectVmDescriptor2`s authored in Lean
//! (`metatheory/Dregg2/Circuit/Emit/PredicatesRelationalCompoundEmit.lean`) and byte-pinned there
//! (`emitVmJson2` `#guard`s). This test embeds both EXACT wire strings, and for each:
//!
//!   1. DECODES via [`parse_vm_descriptor2`] and asserts the decode equals an independently
//!      hand-built `EffectVmDescriptor2` (Lean emit ≡ Rust builder — a byte drift on either side
//!      breaks this OR the Lean `#guard`);
//!   2. proves an HONEST witness through the REAL [`prove_vm_descriptor2`], asserts ACCEPT, and
//!      re-verifies the proof against the public inputs;
//!   3. MUTATION CANARIES — each tampers ONE witness/PI coordinate and asserts prove-or-verify
//!      REFUSES, with the honest witness asserted accepted first (non-vacuity).
//!
//! The two circuits re-express the hand DSL predicate AIRs
//! (`circuit/src/dsl/predicates/{compound,relational}.rs`): the compound boolean gate tree
//! (pure `Base` gates + first-row `PiBinding`s) and the relational comparator, whose Poseidon2
//! commitment binding maps to arity-2 `TID_P2` chip lookups
//! (`chip_absorb_all_lanes(2, [v, r])[0] == hash_2_to_1(v, r)`) and whose 30-bit range proof stays
//! in its hand-AIR arithmetic (gated `Base`) form.

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    CHIP_OUT_LANES, CHIP_RATE, CHIP_TUPLE_LEN, EffectVmDescriptor2, LookupSpec, MemBoundaryWitness,
    TID_P2, VmConstraint2, chip_absorb_all_lanes, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};
use dregg_circuit::poseidon2::hash_2_to_1;

/// The BYTE-IDENTICAL wire string Lean's `emitVmJson2 compoundPredicateDesc` emits.
const COMPOUND_GOLDEN: &str = r#"{"name":"dregg-compound-predicate-ir2-v1","ir":2,"trace_width":39,"public_input_count":11,"tables":[],"constraints":[{"t":"gate","body":{"t":"mul","l":{"t":"var","v":0},"r":{"t":"add","l":{"t":"var","v":0},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":1},"r":{"t":"add","l":{"t":"var","v":1},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":2},"r":{"t":"add","l":{"t":"var","v":2},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":3},"r":{"t":"add","l":{"t":"var","v":3},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":4},"r":{"t":"add","l":{"t":"var","v":4},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":5},"r":{"t":"add","l":{"t":"var","v":5},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":6},"r":{"t":"add","l":{"t":"var","v":6},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":7},"r":{"t":"add","l":{"t":"var","v":7},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"add","l":{"t":"var","v":8},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":9},"r":{"t":"add","l":{"t":"var","v":9},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"add","l":{"t":"var","v":10},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":11},"r":{"t":"add","l":{"t":"var","v":11},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":12},"r":{"t":"add","l":{"t":"var","v":12},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}},"r":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}},"r":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":10}}},"r":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":11}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":12}}}}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":13},"r":{"t":"add","l":{"t":"var","v":13},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"add","l":{"t":"var","v":13},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":15}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":9},"r":{"t":"add","l":{"t":"var","v":13},"r":{"t":"add","l":{"t":"var","v":15},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"add","l":{"t":"var","v":13},"r":{"t":"add","l":{"t":"var","v":0},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":11},"r":{"t":"add","l":{"t":"var","v":13},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":15}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":12},"r":{"t":"add","l":{"t":"var","v":13},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":37}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"add","l":{"t":"var","v":37},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":18},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":26}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":19},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":27}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":20},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":28}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":21},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":29}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":22},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":30}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":23},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":31}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":24},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":32}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":25},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":33}}}},{"t":"pi_binding","row":"first","col":13,"pi_index":0},{"t":"pi_binding","row":"first","col":14,"pi_index":1},{"t":"pi_binding","row":"first","col":16,"pi_index":2},{"t":"pi_binding","row":"first","col":26,"pi_index":3},{"t":"pi_binding","row":"first","col":27,"pi_index":4},{"t":"pi_binding","row":"first","col":28,"pi_index":5},{"t":"pi_binding","row":"first","col":29,"pi_index":6},{"t":"pi_binding","row":"first","col":30,"pi_index":7},{"t":"pi_binding","row":"first","col":31,"pi_index":8},{"t":"pi_binding","row":"first","col":32,"pi_index":9},{"t":"pi_binding","row":"first","col":33,"pi_index":10}],"hash_sites":[],"ranges":[]}"#;

/// The BYTE-IDENTICAL wire string Lean's `emitVmJson2 relationalPredicateDesc` emits.
const RELATIONAL_GOLDEN: &str = r#"{"name":"dregg-relational-predicate-ir2-v1","ir":2,"trace_width":59,"public_input_count":3,"tables":[],"constraints":[{"t":"pi_binding","row":"first","col":36,"pi_index":2},{"t":"gate","body":{"t":"add","l":{"t":"var","v":36},"r":{"t":"const","v":-1}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"add","l":{"t":"var","v":37},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":38},"r":{"t":"add","l":{"t":"var","v":38},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":39},"r":{"t":"add","l":{"t":"var","v":39},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":37},"r":{"t":"add","l":{"t":"var","v":38},"r":{"t":"add","l":{"t":"var","v":39},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":37}}},"r":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":38}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":39}}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":5},"r":{"t":"add","l":{"t":"var","v":5},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":6},"r":{"t":"add","l":{"t":"var","v":6},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":7},"r":{"t":"add","l":{"t":"var","v":7},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"add","l":{"t":"var","v":8},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":9},"r":{"t":"add","l":{"t":"var","v":9},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"add","l":{"t":"var","v":10},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":11},"r":{"t":"add","l":{"t":"var","v":11},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":12},"r":{"t":"add","l":{"t":"var","v":12},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":13},"r":{"t":"add","l":{"t":"var","v":13},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":14},"r":{"t":"add","l":{"t":"var","v":14},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":15},"r":{"t":"add","l":{"t":"var","v":15},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":16},"r":{"t":"add","l":{"t":"var","v":16},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":17},"r":{"t":"add","l":{"t":"var","v":17},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":18},"r":{"t":"add","l":{"t":"var","v":18},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":19},"r":{"t":"add","l":{"t":"var","v":19},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":20},"r":{"t":"add","l":{"t":"var","v":20},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":21},"r":{"t":"add","l":{"t":"var","v":21},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":22},"r":{"t":"add","l":{"t":"var","v":22},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":23},"r":{"t":"add","l":{"t":"var","v":23},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":24},"r":{"t":"add","l":{"t":"var","v":24},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":25},"r":{"t":"add","l":{"t":"var","v":25},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":26},"r":{"t":"add","l":{"t":"var","v":26},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":27},"r":{"t":"add","l":{"t":"var","v":27},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":28},"r":{"t":"add","l":{"t":"var","v":28},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":29},"r":{"t":"add","l":{"t":"var","v":29},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":30},"r":{"t":"add","l":{"t":"var","v":30},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":31},"r":{"t":"add","l":{"t":"var","v":31},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":32},"r":{"t":"add","l":{"t":"var","v":32},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":33},"r":{"t":"add","l":{"t":"var","v":33},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"mul","l":{"t":"var","v":34},"r":{"t":"add","l":{"t":"var","v":34},"r":{"t":"const","v":-1}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":5}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":2},"r":{"t":"var","v":6}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":4},"r":{"t":"var","v":7}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":8},"r":{"t":"var","v":8}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":16},"r":{"t":"var","v":9}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":32},"r":{"t":"var","v":10}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":64},"r":{"t":"var","v":11}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":128},"r":{"t":"var","v":12}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":256},"r":{"t":"var","v":13}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":512},"r":{"t":"var","v":14}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1024},"r":{"t":"var","v":15}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":2048},"r":{"t":"var","v":16}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":4096},"r":{"t":"var","v":17}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":8192},"r":{"t":"var","v":18}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":16384},"r":{"t":"var","v":19}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":32768},"r":{"t":"var","v":20}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":65536},"r":{"t":"var","v":21}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":131072},"r":{"t":"var","v":22}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":262144},"r":{"t":"var","v":23}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":524288},"r":{"t":"var","v":24}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1048576},"r":{"t":"var","v":25}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":2097152},"r":{"t":"var","v":26}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":4194304},"r":{"t":"var","v":27}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":8388608},"r":{"t":"var","v":28}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":16777216},"r":{"t":"var","v":29}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":33554432},"r":{"t":"var","v":30}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":67108864},"r":{"t":"var","v":31}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":134217728},"r":{"t":"var","v":32}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":268435456},"r":{"t":"var","v":33}},"r":{"t":"mul","l":{"t":"const","v":536870912},"r":{"t":"var","v":34}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":4}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":37},"r":{"t":"var","v":34}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":38},"r":{"t":"var","v":4}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":39},"r":{"t":"add","l":{"t":"mul","l":{"t":"var","v":4},"r":{"t":"var","v":35}},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":43},"r":{"t":"add","l":{"t":"var","v":43},"r":{"t":"const","v":-1}}}},{"t":"pi_binding","row":"first","col":41,"pi_index":0},{"t":"pi_binding","row":"first","col":42,"pi_index":1},{"t":"lookup","table":1,"tuple":[{"t":"const","v":2},{"t":"var","v":0},{"t":"var","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":41},{"t":"var","v":45},{"t":"var","v":46},{"t":"var","v":47},{"t":"var","v":48},{"t":"var","v":49},{"t":"var","v":50},{"t":"var","v":51}]},{"t":"lookup","table":1,"tuple":[{"t":"const","v":2},{"t":"var","v":2},{"t":"var","v":3},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":42},{"t":"var","v":52},{"t":"var","v":53},{"t":"var","v":54},{"t":"var","v":55},{"t":"var","v":56},{"t":"var","v":57},{"t":"var","v":58}]},{"t":"gate","body":{"t":"var","v":44}}],"hash_sites":[],"ranges":[]}"#;

// ============================================================================
// EmittedExpr / VmConstraint2 builders — a faithful Rust mirror of the Lean §0 helpers.
// ============================================================================

fn v(c: usize) -> LeanExpr {
    LeanExpr::Var(c)
}
fn sub_c(a: LeanExpr, k: i64) -> LeanExpr {
    LeanExpr::add(a, LeanExpr::Const(-k))
}
fn sub_v(a: LeanExpr, col: usize) -> LeanExpr {
    LeanExpr::add(a, LeanExpr::mul(LeanExpr::Const(-1), v(col)))
}
fn bin_body(c: usize) -> LeanExpr {
    LeanExpr::mul(v(c), sub_c(v(c), 1))
}
fn one_minus(c: usize) -> LeanExpr {
    LeanExpr::add(LeanExpr::Const(1), LeanExpr::mul(LeanExpr::Const(-1), v(c)))
}
fn prod_e(xs: &[LeanExpr]) -> LeanExpr {
    match xs {
        [] => LeanExpr::Const(1),
        [x] => x.clone(),
        [x, rest @ ..] => LeanExpr::mul(x.clone(), prod_e(rest)),
    }
}
fn sum_e(xs: &[LeanExpr]) -> LeanExpr {
    match xs {
        [] => LeanExpr::Const(0),
        [x] => x.clone(),
        [x, rest @ ..] => LeanExpr::add(x.clone(), sum_e(rest)),
    }
}
fn at_least_one(cols: &[usize]) -> LeanExpr {
    let fs: Vec<LeanExpr> = cols.iter().map(|&c| one_minus(c)).collect();
    prod_e(&fs)
}
fn gate(body: LeanExpr) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::Gate(body))
}
fn pi_first(col: usize, pi_index: usize) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::First,
        col,
        pi_index,
    })
}

/// Arity-2 `TID_P2` chip lookup binding `digest` to `hash_2_to_1(in_a, in_b)`, exposing lanes 1..7
/// in `lanes` — mirrors Lean `commitLookup` / `chipLookupTuple [Var in_a, Var in_b] digest lanes`.
fn commit_lookup(in_a: usize, in_b: usize, digest: usize, lanes: &[usize]) -> VmConstraint2 {
    let ins = [in_a, in_b];
    let mut tuple: Vec<LeanExpr> = Vec::with_capacity(CHIP_TUPLE_LEN);
    tuple.push(LeanExpr::Const(2)); // arity tag = ins.length
    for i in 0..CHIP_RATE {
        tuple.push(match ins.get(i) {
            Some(&c) => LeanExpr::Var(c),
            None => LeanExpr::Const(0),
        });
    }
    tuple.push(LeanExpr::Var(digest)); // out0 = the commitment
    for &l in lanes {
        tuple.push(LeanExpr::Var(l));
    }
    assert_eq!(tuple.len(), CHIP_TUPLE_LEN);
    VmConstraint2::Lookup(LookupSpec {
        table: TID_P2,
        tuple,
    })
}

// ============================================================================
// Independent hand-built descriptors (the "hand-AIR semantics" twins).
// ============================================================================

/// The compound predicate descriptor twin (`compound.rs::compound_predicate_circuit_descriptor`).
fn compound_hand_built() -> EffectVmDescriptor2 {
    let mut c: Vec<VmConstraint2> = Vec::new();
    for i in 0..8 {
        c.push(gate(bin_body(i))); // C1–C8 sub_result binary
    }
    for &col in &[8usize, 9, 10, 11, 12] {
        c.push(gate(bin_body(col))); // C9–C13 op selectors binary
    }
    c.push(gate(at_least_one(&[8, 9, 10, 11, 12]))); // C14 at-least-one operator
    c.push(gate(bin_body(13))); // C15 composed binary
    c.push(gate(LeanExpr::mul(v(8), sub_v(v(13), 15)))); // C16 AND
    c.push(gate(LeanExpr::mul(
        v(9),
        sum_e(&[v(13), v(15), LeanExpr::Const(-1)]),
    ))); // C17 OR
    c.push(gate(LeanExpr::mul(
        v(10),
        sum_e(&[v(13), v(0), LeanExpr::Const(-1)]),
    ))); // C18 NOT
    c.push(gate(LeanExpr::mul(v(11), sub_v(v(13), 15)))); // C19 Threshold
    c.push(gate(LeanExpr::mul(v(12), sub_v(v(13), 37)))); // C20 Custom
    c.push(gate(bin_body(37))); // C21 gate_output binary
    for i in 0..8 {
        c.push(gate(sub_v(v(18 + i), 26 + i))); // C22–C29 subcommit == expected
    }
    c.push(pi_first(13, 0));
    c.push(pi_first(14, 1));
    c.push(pi_first(16, 2));
    for i in 0..8 {
        c.push(pi_first(26 + i, 3 + i));
    }
    EffectVmDescriptor2 {
        name: "dregg-compound-predicate-ir2-v1".to_string(),
        trace_width: 39,
        public_input_count: 11,
        tables: vec![],
        constraints: c,
        hash_sites: vec![],
        ranges: vec![],
    }
}

/// The relational predicate descriptor twin (`relational.rs::relational_predicate_descriptor`).
fn relational_hand_built() -> EffectVmDescriptor2 {
    let mut c: Vec<VmConstraint2> = Vec::new();
    c.push(pi_first(36, 2)); // C1 result_bit == pi[2]
    c.push(gate(sub_c(v(36), 1))); // C2 result_bit == 1
    c.push(gate(bin_body(37))); // C3 range_flag binary
    c.push(gate(bin_body(38))); // C3 eq_flag binary
    c.push(gate(bin_body(39))); // C3 neq_flag binary
    c.push(gate(sum_e(&[v(37), v(38), v(39), LeanExpr::Const(-1)]))); // C4 exactly one
    c.push(gate(at_least_one(&[37, 38, 39]))); // C5 at least one
    for i in 0..30 {
        c.push(gate(LeanExpr::mul(v(37), bin_body(5 + i)))); // C6 gated diff-bit binary
    }
    let terms: Vec<LeanExpr> = (0..30)
        .map(|i| LeanExpr::mul(LeanExpr::Const(1i64 << i), v(5 + i)))
        .collect();
    c.push(gate(LeanExpr::mul(v(37), sub_v(sum_e(&terms), 4)))); // C7 recompose
    c.push(gate(LeanExpr::mul(v(37), v(5 + 29)))); // C8 high bit zero
    c.push(gate(LeanExpr::mul(v(38), v(4)))); // C9 eq: diff == 0
    c.push(gate(LeanExpr::mul(
        v(39),
        sub_c(LeanExpr::mul(v(4), v(35)), 1),
    ))); // C10 neq: diff*inv == 1
    c.push(gate(bin_body(43))); // C11 commit_verify binary
    c.push(pi_first(41, 0)); // C12 commitment_a == pi[0]
    c.push(pi_first(42, 1)); // C13 commitment_b == pi[1]
    c.push(commit_lookup(0, 1, 41, &[45, 46, 47, 48, 49, 50, 51])); // C14 hashA
    c.push(commit_lookup(2, 3, 42, &[52, 53, 54, 55, 56, 57, 58])); // C15 hashB
    c.push(gate(v(44))); // C16 zero_pad == 0
    EffectVmDescriptor2 {
        name: "dregg-relational-predicate-ir2-v1".to_string(),
        trace_width: 59,
        public_input_count: 3,
        tables: vec![],
        constraints: c,
        hash_sites: vec![],
        ranges: vec![],
    }
}

// ============================================================================
// Prove/verify oracle.
// ============================================================================

/// `true` iff `(trace, pis)` is REJECTED end-to-end: proving refuses OR the proof fails to VERIFY.
/// Prove-THEN-verify is the faithful gate (in `--release` the self-verify is off, so the first-row
/// `PiBinding` is checked by the CONSUMER's `verify_vm_descriptor2` — the production posture).
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

// ============================================================================
// Compound witness fixtures: AND of sub_result[0], sub_result[1] (both true).
// ============================================================================

fn compound_row() -> Vec<BabyBear> {
    let mut r = vec![BabyBear::ZERO; 39];
    r[0] = BabyBear::ONE; // sub_result_0
    r[1] = BabyBear::ONE; // sub_result_1
    r[8] = BabyBear::ONE; // op_and
    r[13] = BabyBear::ONE; // composed_result
    r[14] = BabyBear::new(777); // tree_hash (off-circuit; PI-bound)
    r[15] = BabyBear::ONE; // and_intermediate = product(sub_0, sub_1)
    for i in 0..8 {
        let cm = BabyBear::new(100 + i as u32);
        r[18 + i] = cm; // sub_proof_commitment[i]
        r[26 + i] = cm; // expected_commitment[i]
    }
    r
}

fn compound_pis() -> Vec<BabyBear> {
    let mut p = vec![BabyBear::ZERO; 11];
    p[0] = BabyBear::ONE; // composed_result_expected
    p[1] = BabyBear::new(777); // tree_hash
    p[2] = BabyBear::ZERO; // threshold_k
    for i in 0..8 {
        p[3 + i] = BabyBear::new(100 + i as u32);
    }
    p
}

fn compound_trace() -> Vec<Vec<BabyBear>> {
    let r = compound_row();
    vec![r.clone(), r.clone(), r.clone(), r]
}

// ============================================================================
// Relational witness fixtures: value_a >= value_b (100 >= 40, diff = 60, range mode).
// ============================================================================

/// Fill diff-bit columns 5..35 with the low 30 bits of `diff`.
fn fill_diff_bits(row: &mut [BabyBear], diff: u32) {
    for i in 0..30 {
        row[5 + i] = BabyBear::new((diff >> i) & 1);
    }
}

fn relational_row() -> Vec<BabyBear> {
    let (va, ba, vb, bb) = (100u32, 7u32, 40u32, 9u32);
    let diff = va - vb; // 60, GreaterOrEqual
    let mut r = vec![BabyBear::ZERO; 59];
    r[0] = BabyBear::new(va);
    r[1] = BabyBear::new(ba);
    r[2] = BabyBear::new(vb);
    r[3] = BabyBear::new(bb);
    r[4] = BabyBear::new(diff);
    fill_diff_bits(&mut r, diff);
    r[36] = BabyBear::ONE; // result_bit
    r[37] = BabyBear::ONE; // range_flag
    r[41] = hash_2_to_1(BabyBear::new(va), BabyBear::new(ba)); // commitment_a
    r[42] = hash_2_to_1(BabyBear::new(vb), BabyBear::new(bb)); // commitment_b
    r[43] = BabyBear::ONE; // commit_verify_flag (deployed posture)
    r
}

fn relational_pis() -> Vec<BabyBear> {
    let r = relational_row();
    vec![r[41], r[42], BabyBear::ONE]
}

fn relational_trace() -> Vec<Vec<BabyBear>> {
    let r = relational_row();
    vec![r.clone(), r.clone(), r.clone(), r]
}

// ============================================================================
// STEP 1 — decode equals hand-built (Lean emit ≡ Rust builder).
// ============================================================================

#[test]
fn compound_emit_decodes_to_hand_built() {
    let decoded = parse_vm_descriptor2(COMPOUND_GOLDEN).expect("compound golden decodes");
    assert_eq!(
        decoded,
        compound_hand_built(),
        "Lean-emitted compound descriptor must equal the hand-built twin"
    );
    assert_eq!(decoded.trace_width, 39);
    assert_eq!(decoded.public_input_count, 11);
    assert_eq!(decoded.constraints.len(), 40);
    // pure Base + PiBinding: no lookups.
    assert!(
        decoded
            .constraints
            .iter()
            .all(|k| matches!(k, VmConstraint2::Base(_))),
        "the compound AIR has no in-circuit hash/range — all constraints are Base"
    );
}

#[test]
fn relational_emit_decodes_to_hand_built() {
    let decoded = parse_vm_descriptor2(RELATIONAL_GOLDEN).expect("relational golden decodes");
    assert_eq!(
        decoded,
        relational_hand_built(),
        "Lean-emitted relational descriptor must equal the hand-built twin"
    );
    assert_eq!(decoded.trace_width, 59);
    assert_eq!(decoded.public_input_count, 3);
    assert_eq!(decoded.constraints.len(), 47);
    let chip_lookups = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
        .count();
    assert_eq!(chip_lookups, 2, "two arity-2 commitment chip lookups");
}

// ============================================================================
// STEP 2 — the arity-2 chip mapping KAT (the relational commitment lookups' meaning).
// ============================================================================

#[test]
fn arity2_chip_lookup_is_hash_2_to_1() {
    let a = BabyBear::new(12345);
    let b = BabyBear::new(67890);
    let lanes = chip_absorb_all_lanes(2, &[a, b]);
    assert_eq!(
        lanes[0],
        hash_2_to_1(a, b),
        "arity-2 chip out0 must equal hash_2_to_1 (the Poseidon2 commitment)"
    );
    // both inputs are load-bearing: perturb each, out0 and every lane change.
    for j in 0..2 {
        let mut alt = [a, b];
        alt[j] += BabyBear::ONE;
        let lanes_alt = chip_absorb_all_lanes(2, &alt);
        for i in 0..CHIP_OUT_LANES {
            assert_ne!(
                lanes[i], lanes_alt[i],
                "chip lane {i} unchanged after perturbing input {j} — that input is dead"
            );
        }
    }
}

// ============================================================================
// STEP 3 — the POSITIVE POLE: honest witnesses prove and verify.
// ============================================================================

#[test]
fn compound_honest_proves_and_verifies() {
    let desc = parse_vm_descriptor2(COMPOUND_GOLDEN).expect("decode");
    let (trace, pis) = (compound_trace(), compound_pis());
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("honest compound witness must prove");
    verify_vm_descriptor2(&desc, &proof, &pis).expect("honest compound proof must verify");
}

#[test]
fn relational_honest_proves_and_verifies() {
    let desc = parse_vm_descriptor2(RELATIONAL_GOLDEN).expect("decode");
    let (trace, pis) = (relational_trace(), relational_pis());
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("honest relational witness must prove");
    verify_vm_descriptor2(&desc, &proof, &pis).expect("honest relational proof must verify");
}

// ============================================================================
// STEP 4 — MUTATION CANARIES (compound). Each bites a NAMED constraint.
// ============================================================================

/// C16 (AND gate) + the `composed == pi[0]` pin: composed forged to 0 while claiming pi[0] = 1.
#[test]
fn compound_forged_composed_refuses() {
    let desc = parse_vm_descriptor2(COMPOUND_GOLDEN).expect("decode");
    let (trace, pis) = (compound_trace(), compound_pis());
    assert!(!rejects(&desc, &trace, &pis), "honest must be accepted");
    let mut bad = trace.clone();
    for row in &mut bad {
        row[13] = BabyBear::ZERO; // composed_result := 0, but op_and=1 and and_intermediate=1
    }
    assert!(
        rejects(&desc, &bad, &pis),
        "composed=0 with op_and=1,and_int=1 violates the AND gate (and the pi[0] pin)"
    );
}

/// C1 (binary): sub_result_0 forged to a non-boolean 2.
#[test]
fn compound_nonbinary_subresult_refuses() {
    let desc = parse_vm_descriptor2(COMPOUND_GOLDEN).expect("decode");
    let (trace, pis) = (compound_trace(), compound_pis());
    let mut bad = trace.clone();
    for row in &mut bad {
        row[0] = BabyBear::new(2); // sub_result_0 := 2 -> 2*(2-1) = 2 != 0
    }
    assert!(
        rejects(&desc, &bad, &pis),
        "a non-boolean sub_result must violate its binary gate"
    );
}

/// C22 (sub-proof commitment binding): sub_proof_commitment[0] != expected_commitment[0].
#[test]
fn compound_broken_subproof_binding_refuses() {
    let desc = parse_vm_descriptor2(COMPOUND_GOLDEN).expect("decode");
    let (trace, pis) = (compound_trace(), compound_pis());
    let mut bad = trace.clone();
    for row in &mut bad {
        row[18] = BabyBear::new(999); // sub_proof_commitment[0] diverges from expected_commitment[0]
    }
    assert!(
        rejects(&desc, &bad, &pis),
        "a sub-result unbacked by its expected commitment must be REJECTED (C22 equality)"
    );
}

/// C14 (at-least-one operator): no operator selected.
#[test]
fn compound_no_operator_refuses() {
    let desc = parse_vm_descriptor2(COMPOUND_GOLDEN).expect("decode");
    let (trace, pis) = (compound_trace(), compound_pis());
    let mut bad = trace.clone();
    for row in &mut bad {
        row[8] = BabyBear::ZERO; // op_and := 0 -> all five selectors 0 -> product == 1 != 0
    }
    assert!(
        rejects(&desc, &bad, &pis),
        "a compound proof selecting no operator must be REJECTED (C14 at-least-one)"
    );
}

// ============================================================================
// STEP 4 — MUTATION CANARIES (relational). Each bites a NAMED constraint.
// ============================================================================

/// C14 (commitment chip lookup): commitment_a forged (leaf does not hash to it). The claimed
/// digest is served by no genuine permutation row -> the chip AIR refuses. `pi[0]` is set to the
/// forged value so the C12 pin is satisfied and ONLY the chip lookup bites.
#[test]
fn relational_forged_commitment_refuses() {
    let desc = parse_vm_descriptor2(RELATIONAL_GOLDEN).expect("decode");
    let (trace, pis) = (relational_trace(), relational_pis());
    assert!(!rejects(&desc, &trace, &pis), "honest must be accepted");
    let mut bad = trace.clone();
    let forged = bad[0][41] + BabyBear::ONE;
    for row in &mut bad {
        row[41] = forged; // commitment_a := genuine + 1
    }
    let bad_pis = vec![forged, pis[1], pis[2]]; // satisfy the C12 pin so only the lookup bites
    assert!(
        rejects(&desc, &bad, &bad_pis),
        "a commitment no (value,blinding) hashes to must be REJECTED (C14 chip lookup)"
    );
}

/// C8 (range high-bit): diff pushed OUT of range ([0, 2^29)) with a valid 30-bit decomposition
/// whose bit 29 is set. C7 (recompose) still holds; C6 (binary) still holds; ONLY C8 bites.
#[test]
fn relational_out_of_range_diff_refuses() {
    let desc = parse_vm_descriptor2(RELATIONAL_GOLDEN).expect("decode");
    let (trace, pis) = (relational_trace(), relational_pis());
    let mut bad = trace.clone();
    let big = 1u32 << 29; // 2^29: bit 29 set, in range [0, 2^30) but violates the < 2^29 tooth
    for row in &mut bad {
        row[4] = BabyBear::new(big); // diff := 2^29
        fill_diff_bits(row, big); // its genuine decomposition (bit 29 = 1)
    }
    assert!(
        rejects(&desc, &bad, &pis),
        "an out-of-range diff (high bit set) must be REJECTED (C8 range bound)"
    );
}

/// C1 (result_bit pin): the public result_bit forged to 0 while the trace asserts 1.
#[test]
fn relational_forged_result_bit_refuses() {
    let desc = parse_vm_descriptor2(RELATIONAL_GOLDEN).expect("decode");
    let (trace, pis) = (relational_trace(), relational_pis());
    let bad_pis = vec![pis[0], pis[1], BabyBear::ZERO]; // pi[2] := 0, trace result_bit = 1
    assert!(
        rejects(&desc, &trace, &bad_pis),
        "a forged public result_bit must be REJECTED (C1 first-row pin)"
    );
}
