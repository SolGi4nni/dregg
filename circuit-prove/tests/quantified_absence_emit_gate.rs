//! # The emit-from-Lean EQUALITY GATE — `quantified_absence` (Approach B, the quotient accumulator).
//!
//! The descriptor is AUTHORED in Lean (`metatheory/Dregg2/Circuit/Emit/QuantifiedAbsenceEmit.lean`,
//! `quantifiedAbsenceDesc`) and its wire string is byte-pinned there (`emitVmJson2` `#guard`). This
//! test embeds that EXACT string ([`GOLDEN_JSON`]) and:
//!
//!   1. DECODES it via [`parse_vm_descriptor2`] and asserts the decode equals an independently
//!      hand-built `EffectVmDescriptor2` (Lean emit ≡ Rust builder — a byte drift on either side
//!      breaks this OR the Lean `#guard`);
//!   2. proves an HONEST witness — one BabyBear⁴ element with its quotient/remainder cofactors,
//!      `diff = α − elem`, `prod = w·diff` (via the REAL `ExtElem::mul`), `sum = prod + v`, and the
//!      public `Acc_all = sum` — through [`prove_vm_descriptor2`], asserts ACCEPT, and re-verifies;
//!   3. the MUTATION CANARIES — each tampers ONE witness value / one public input and asserts the
//!      prove-or-verify REFUSES *by a specific emitted constraint*: the C1 `diff` gate (tamper
//!      `elem`), the C2 `w·diff` gate two ways (tamper the quotient `w`; and forge `prod` with the
//!      field-reduction `11·(…)` terms DROPPED — the X⁴−11 coupling tooth), the C3 `sum` gate
//!      (tamper the remainder `v`), the `sum == Acc_all` boundary pin (forge the `Acc_all` PI), and
//!      the α-materialization pin (forge the α PI).
//!
//! Every canary asserts the honest witness ACCEPTS first (non-vacuity), so a refusal is a genuine
//! constraint bite and not an unrelated prover error. This is the equality gate: the emitted
//! descriptor accepts EXACTLY the per-element quotient identity the hand AIR
//! (`circuit/src/quantified_absence.rs::QuotientAccumulatorAir`) checked — no more (the descriptor,
//! like the hand AIR, does not recompute the predicate or certify `Acc_all` is a genuine product;
//! those stay executor-verified carriers).

use std::panic::AssertUnwindSafe;

use dregg_circuit::accumulator_types::ExtElem;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, VmConstraint2, parse_vm_descriptor2,
    prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

/// The BYTE-IDENTICAL wire string Lean's `emitVmJson2 quantifiedAbsenceDesc` emits (pinned by the
/// `#guard` in `QuantifiedAbsenceEmit.lean`). If Lean's emitter drifts, that `#guard` fails; if this
/// literal drifts, the `decoded == hand_built` assertion fails. Neither can silently diverge.
const GOLDEN_JSON: &str = r#"{"name":"quantified-absence-quotient-accumulator::babybear4-v1","ir":2,"trace_width":28,"public_input_count":8,"tables":[],"constraints":[{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":12},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":24}}},"r":{"t":"var","v":0}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":13},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":25}}},"r":{"t":"var","v":1}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":14},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":26}}},"r":{"t":"var","v":2}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":15},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":27}}},"r":{"t":"var","v":3}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":16},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"add","l":{"t":"mul","l":{"t":"var","v":4},"r":{"t":"var","v":12}},"r":{"t":"mul","l":{"t":"const","v":11},"r":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"var","v":5},"r":{"t":"var","v":15}},"r":{"t":"mul","l":{"t":"var","v":6},"r":{"t":"var","v":14}}},"r":{"t":"mul","l":{"t":"var","v":7},"r":{"t":"var","v":13}}}}}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":17},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"var","v":4},"r":{"t":"var","v":13}},"r":{"t":"mul","l":{"t":"var","v":5},"r":{"t":"var","v":12}}},"r":{"t":"mul","l":{"t":"const","v":11},"r":{"t":"add","l":{"t":"mul","l":{"t":"var","v":6},"r":{"t":"var","v":15}},"r":{"t":"mul","l":{"t":"var","v":7},"r":{"t":"var","v":14}}}}}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":18},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"var","v":4},"r":{"t":"var","v":14}},"r":{"t":"mul","l":{"t":"var","v":5},"r":{"t":"var","v":13}}},"r":{"t":"mul","l":{"t":"var","v":6},"r":{"t":"var","v":12}}},"r":{"t":"mul","l":{"t":"const","v":11},"r":{"t":"mul","l":{"t":"var","v":7},"r":{"t":"var","v":15}}}}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":19},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"var","v":4},"r":{"t":"var","v":15}},"r":{"t":"mul","l":{"t":"var","v":5},"r":{"t":"var","v":14}}},"r":{"t":"mul","l":{"t":"var","v":6},"r":{"t":"var","v":13}}},"r":{"t":"mul","l":{"t":"var","v":7},"r":{"t":"var","v":12}}}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":20},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":16}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":21},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":17}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":22},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":18}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":10}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":23},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":19}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":11}}}},{"t":"pi_binding","row":"first","col":20,"pi_index":0},{"t":"pi_binding","row":"first","col":21,"pi_index":1},{"t":"pi_binding","row":"first","col":22,"pi_index":2},{"t":"pi_binding","row":"first","col":23,"pi_index":3},{"t":"pi_binding","row":"first","col":24,"pi_index":4},{"t":"pi_binding","row":"first","col":25,"pi_index":5},{"t":"pi_binding","row":"first","col":26,"pi_index":6},{"t":"pi_binding","row":"first","col":27,"pi_index":7}],"hash_sites":[],"ranges":[]}"#;

// --- Trace column layout (must match `QuantifiedAbsenceEmit.lean` §1). ---
const E0: usize = 0; // ELEMENT   0..3
const Q0: usize = 4; // QUOTIENT  4..7
const V0: usize = 8; // REMAINDER 8..11
const D0: usize = 12; // DIFF     12..15
const P0: usize = 16; // PRODUCT  16..19
const S0: usize = 20; // SUM      20..23
const A0: usize = 24; // ALPHA    24..27
const QACC_WIDTH: usize = 28;

// --- Public-input layout: Acc_all (0..3) then alpha (4..7). ---
const PI_ACC0: usize = 0;
const PI_ALPHA0: usize = 4;
const QACC_PI_COUNT: usize = 8;

fn var(i: usize) -> LeanExpr {
    LeanExpr::Var(i)
}
/// `(col a) − (col b)`.
fn sub_cols(a: usize, b: usize) -> LeanExpr {
    LeanExpr::add(var(a), LeanExpr::mul(LeanExpr::Const(-1), var(b)))
}
/// Product of two columns.
fn vv(a: usize, b: usize) -> LeanExpr {
    LeanExpr::mul(var(a), var(b))
}
/// Multiply by the BabyBear⁴ irreducible constant W = 11.
fn w11(e: LeanExpr) -> LeanExpr {
    LeanExpr::mul(LeanExpr::Const(11), e)
}

/// The independently-hand-built twin of the Lean `quantifiedAbsenceDesc`: four `diff` gates, four
/// `w·diff` (X⁴−11 mult) gates, four `sum` gates, the four `sum == Acc_all` pins, and the four
/// α-materialization pins — in that exact order.
fn hand_built_desc() -> EffectVmDescriptor2 {
    let mut constraints: Vec<VmConstraint2> = Vec::with_capacity(20);

    // C1: diff[i] = alpha[i] - elem[i]  →  (D_i - A_i) + E_i.
    for i in 0..4 {
        let body = LeanExpr::add(sub_cols(D0 + i, A0 + i), var(E0 + i));
        constraints.push(VmConstraint2::Base(VmConstraint::Gate(body)));
    }

    // C2: prod[i] = (w · diff)[i] over BabyBear⁴ (X⁴ − 11).  Body = P_i - c_i.
    let q = [Q0, Q0 + 1, Q0 + 2, Q0 + 3];
    let d = [D0, D0 + 1, D0 + 2, D0 + 3];
    let c0 = LeanExpr::add(
        vv(q[0], d[0]),
        w11(LeanExpr::add(
            LeanExpr::add(vv(q[1], d[3]), vv(q[2], d[2])),
            vv(q[3], d[1]),
        )),
    );
    let c1 = LeanExpr::add(
        LeanExpr::add(vv(q[0], d[1]), vv(q[1], d[0])),
        w11(LeanExpr::add(vv(q[2], d[3]), vv(q[3], d[2]))),
    );
    let c2 = LeanExpr::add(
        LeanExpr::add(
            LeanExpr::add(vv(q[0], d[2]), vv(q[1], d[1])),
            vv(q[2], d[0]),
        ),
        w11(vv(q[3], d[3])),
    );
    let c3 = LeanExpr::add(
        LeanExpr::add(
            LeanExpr::add(vv(q[0], d[3]), vv(q[1], d[2])),
            vv(q[2], d[1]),
        ),
        vv(q[3], d[0]),
    );
    for (i, c) in [c0, c1, c2, c3].into_iter().enumerate() {
        let body = LeanExpr::add(var(P0 + i), LeanExpr::mul(LeanExpr::Const(-1), c));
        constraints.push(VmConstraint2::Base(VmConstraint::Gate(body)));
    }

    // C3: sum[i] = prod[i] + v[i]  →  (S_i - P_i) - V_i.
    for i in 0..4 {
        let body = LeanExpr::add(
            sub_cols(S0 + i, P0 + i),
            LeanExpr::mul(LeanExpr::Const(-1), var(V0 + i)),
        );
        constraints.push(VmConstraint2::Base(VmConstraint::Gate(body)));
    }

    // boundary: sum == Acc_all (first-row pins).
    for i in 0..4 {
        constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
            row: VmRow::First,
            col: S0 + i,
            pi_index: PI_ACC0 + i,
        }));
    }
    // alpha materialization: ALPHA == alpha PIs (first-row pins).
    for i in 0..4 {
        constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
            row: VmRow::First,
            col: A0 + i,
            pi_index: PI_ALPHA0 + i,
        }));
    }

    EffectVmDescriptor2 {
        name: "quantified-absence-quotient-accumulator::babybear4-v1".to_string(),
        trace_width: QACC_WIDTH,
        public_input_count: QACC_PI_COUNT,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    }
}

fn limbs(e: ExtElem) -> [BabyBear; 4] {
    e.0
}

/// Write the four limbs of `e` into `row[off..off+4]`.
fn put(row: &mut [BabyBear], off: usize, e: ExtElem) {
    let l = limbs(e);
    row[off..off + 4].copy_from_slice(&l);
}

/// A single honest row from `(elem, w, v, alpha)`: `diff = α − elem`, `prod = w·diff` (REAL
/// `ExtElem::mul`), `sum = prod + v`. Returns `(row, sum)` — `sum` is the public `Acc_all`.
fn honest_row(elem: ExtElem, w: ExtElem, v: ExtElem, alpha: ExtElem) -> (Vec<BabyBear>, ExtElem) {
    let diff = alpha.sub(elem);
    let prod = w.mul(diff);
    let sum = prod.add(v);
    let mut row = vec![BabyBear::ZERO; QACC_WIDTH];
    put(&mut row, E0, elem);
    put(&mut row, Q0, w);
    put(&mut row, V0, v);
    put(&mut row, D0, diff);
    put(&mut row, P0, prod);
    put(&mut row, S0, sum);
    put(&mut row, A0, alpha);
    (row, sum)
}

/// The public inputs for `(acc_all, alpha)`: `Acc_all` limbs then α limbs.
fn pis(acc_all: ExtElem, alpha: ExtElem) -> Vec<BabyBear> {
    let mut p = Vec::with_capacity(QACC_PI_COUNT);
    p.extend_from_slice(&limbs(acc_all));
    p.extend_from_slice(&limbs(alpha));
    p
}

/// A 4-row (power-of-two) base trace of identical honest rows.
fn trace_of(row: &[BabyBear]) -> Vec<Vec<BabyBear>> {
    vec![row.to_vec(), row.to_vec(), row.to_vec(), row.to_vec()]
}

/// A witness fixture: a base-embedded element, a full-limb quotient, a full-limb remainder, and a
/// full-limb α (so `diff` and the ext-mult exercise all four limbs / every cross term).
fn fixture() -> (ExtElem, ExtElem, ExtElem, ExtElem) {
    let elem = ExtElem([
        BabyBear::new(1_000_003),
        BabyBear::ZERO,
        BabyBear::ZERO,
        BabyBear::ZERO,
    ]);
    let w = ExtElem([
        BabyBear::new(31),
        BabyBear::new(37),
        BabyBear::new(41),
        BabyBear::new(43),
    ]);
    let v = ExtElem([
        BabyBear::new(97),
        BabyBear::new(89),
        BabyBear::new(83),
        BabyBear::new(79),
    ]);
    let alpha = ExtElem([
        BabyBear::new(500_009),
        BabyBear::new(600_011),
        BabyBear::new(700_019),
        BabyBear::new(800_023),
    ]);
    (elem, w, v, alpha)
}

/// `true` iff this `(trace, pis)` is REJECTED end-to-end — proving refuses OR the produced proof
/// fails to VERIFY. `false` iff it both proves AND verifies. Prove-THEN-verify is the faithful gate:
/// `prove_vm_descriptor2` self-verifies only under `cfg!(debug_assertions)`, so in a `--release`
/// test the first-row `PiBinding` (and the transition gates) are checked by the CONSUMER's
/// `verify_vm_descriptor2` — exactly the production posture.
fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pv: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, pv, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pv)
    }));
    match r {
        Err(_) => true,      // panicked anywhere → rejected
        Ok(Err(_)) => true,  // prove OR verify returned Err → rejected
        Ok(Ok(())) => false, // proved AND verified → ACCEPTED
    }
}

/// STEP 1 — the emitted descriptor decodes and equals the hand-built twin (Lean emit ≡ Rust
/// semantics), with the expected shape.
#[test]
fn quantified_absence_emit_decodes_to_hand_built() {
    let decoded = parse_vm_descriptor2(GOLDEN_JSON).expect("the Lean-emitted golden JSON decodes");
    let hand = hand_built_desc();
    assert_eq!(
        decoded, hand,
        "the Lean-emitted descriptor must equal the independently hand-built descriptor"
    );
    assert_eq!(decoded.trace_width, QACC_WIDTH);
    assert_eq!(decoded.public_input_count, QACC_PI_COUNT);
    assert!(decoded.tables.is_empty(), "Approach B declares no tables");
    let gates = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::Gate(_))))
        .count();
    let pins = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
        .count();
    assert_eq!(gates, 12, "4 diff + 4 prod + 4 sum gates");
    assert_eq!(pins, 8, "4 Acc_all pins + 4 alpha pins");
}

/// STEP 2 — THE POSITIVE POLE: an honest quotient-accumulator witness proves through the emitted
/// descriptor, and the proof re-verifies against the public `(Acc_all, α)`.
#[test]
fn honest_witness_proves_and_verifies() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (elem, w, v, alpha) = fixture();
    let (row, acc_all) = honest_row(elem, w, v, alpha);
    let trace = trace_of(&row);
    let pv = pis(acc_all, alpha);
    let proof = prove_vm_descriptor2(&desc, &trace, &pv, &MemBoundaryWitness::default(), &[])
        .expect("the honest quotient-accumulator witness must prove");
    verify_vm_descriptor2(&desc, &proof, &pv)
        .expect("the honest proof must re-verify against the public (Acc_all, alpha)");
}

/// STEP 3a — CANARY (C1 `diff` gate): tamper `elem` in every row while keeping `diff` — now
/// `diff ≠ α − elem`, so the limb-0 diff gate is UNSAT. `elem` appears in NO other constraint, so
/// this bites C1 alone.
#[test]
fn tampered_elem_refuses_on_diff_gate() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (elem, w, v, alpha) = fixture();
    let (row, acc_all) = honest_row(elem, w, v, alpha);
    let pv = pis(acc_all, alpha);
    assert!(
        !rejects(&desc, &trace_of(&row), &pv),
        "honest witness must be accepted — else the canary is vacuous"
    );
    let mut bad = row.clone();
    bad[E0] = bad[E0] + BabyBear::ONE; // elem changes; diff column stays → diff ≠ α − elem
    assert!(
        rejects(&desc, &trace_of(&bad), &pv),
        "an elem inconsistent with diff must be REJECTED (C1 diff gate)"
    );
}

/// STEP 3b — CANARY (C2 `w·diff` gate, quotient): tamper the quotient `w` while keeping `prod` —
/// now `prod ≠ w·diff`, so the ext-mult gate is UNSAT. `w` appears in NO other constraint, so this
/// bites C2 alone.
#[test]
fn tampered_quotient_refuses_on_prod_gate() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (elem, w, v, alpha) = fixture();
    let (row, acc_all) = honest_row(elem, w, v, alpha);
    let pv = pis(acc_all, alpha);
    assert!(!rejects(&desc, &trace_of(&row), &pv), "non-vacuity");
    let mut bad = row.clone();
    bad[Q0] = bad[Q0] + BabyBear::ONE; // w changes; prod column stays → prod ≠ w·diff
    assert!(
        rejects(&desc, &trace_of(&bad), &pv),
        "a quotient inconsistent with the product must be REJECTED (C2 ext-mult gate)"
    );
}

/// STEP 3c — CANARY (C2 `w·diff` gate, the X⁴−11 coupling): forge `prod` with the field-reduction
/// `11·(…)` terms DROPPED (the truncated polynomial multiply), and set `sum = prod_wrong + v`,
/// `Acc_all = sum` so C3 and the boundary stay satisfied. The real C2 gate carries the `const 11`
/// coupling, so it REJECTS — proving the emitted bilinear form is the genuine BabyBear⁴ product,
/// not the naive one.
#[test]
fn forged_product_without_reduction_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (elem, w, v, alpha) = fixture();
    let diff = alpha.sub(elem);
    let prod_real = w.mul(diff);

    // The truncated (W = 0) product: the polynomial multiply WITHOUT the X⁴ ≡ 11 wraparound.
    let a = limbs(w);
    let b = limbs(diff);
    let wrong = ExtElem([
        a[0] * b[0],
        a[0] * b[1] + a[1] * b[0],
        a[0] * b[2] + a[1] * b[1] + a[2] * b[0],
        a[0] * b[3] + a[1] * b[2] + a[2] * b[1] + a[3] * b[0],
    ]);
    assert_ne!(
        limbs(prod_real),
        limbs(wrong),
        "the reduction terms must actually move the product — else the canary is vacuous"
    );

    let sum = wrong.add(v);
    let mut row = vec![BabyBear::ZERO; QACC_WIDTH];
    put(&mut row, E0, elem);
    put(&mut row, Q0, w);
    put(&mut row, V0, v);
    put(&mut row, D0, diff);
    put(&mut row, P0, wrong); // forged: no field reduction
    put(&mut row, S0, sum); // sum = wrong + v  (keeps C3 satisfied)
    put(&mut row, A0, alpha);
    let pv = pis(sum, alpha); // Acc_all = sum  (keeps the boundary satisfied)

    // sanity: the SAME layout with the REAL product is accepted (non-vacuity of the negative).
    let (good, acc_all) = honest_row(elem, w, v, alpha);
    assert!(
        !rejects(&desc, &trace_of(&good), &pis(acc_all, alpha)),
        "non-vacuity"
    );
    assert!(
        rejects(&desc, &trace_of(&row), &pv),
        "a product missing the X⁴−11 reduction must be REJECTED (C2 coupling tooth)"
    );
}

/// STEP 3d — CANARY (C3 `sum` gate): tamper the remainder `v` while keeping `sum` — now
/// `sum ≠ prod + v`, so the limb-0 sum gate is UNSAT. `v` appears in NO other constraint, so this
/// bites C3 alone.
#[test]
fn tampered_remainder_refuses_on_sum_gate() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (elem, w, v, alpha) = fixture();
    let (row, acc_all) = honest_row(elem, w, v, alpha);
    let pv = pis(acc_all, alpha);
    assert!(!rejects(&desc, &trace_of(&row), &pv), "non-vacuity");
    let mut bad = row.clone();
    bad[V0] = bad[V0] + BabyBear::ONE; // v changes; sum column stays → sum ≠ prod + v
    assert!(
        rejects(&desc, &trace_of(&bad), &pv),
        "a remainder inconsistent with the sum must be REJECTED (C3 sum gate)"
    );
}

/// STEP 3e — CANARY (boundary): honest trace, but a FORGED `Acc_all` PI. The first-row pin
/// `SUM == Acc_all` is violated → UNSAT. The public accumulator is bound to the witness sum.
#[test]
fn forged_acc_all_refuses_on_boundary() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (elem, w, v, alpha) = fixture();
    let (row, acc_all) = honest_row(elem, w, v, alpha);
    let trace = trace_of(&row);
    assert!(!rejects(&desc, &trace, &pis(acc_all, alpha)), "non-vacuity");
    let mut forged = pis(acc_all, alpha);
    forged[PI_ACC0] = forged[PI_ACC0] + BabyBear::ONE; // claim a different Acc_all
    assert!(
        rejects(&desc, &trace, &forged),
        "a forged Acc_all (sum does not equal it) must be REJECTED (boundary pin)"
    );
}

/// STEP 3f — CANARY (α materialization): honest trace, but a FORGED α PI. The first-row pin
/// `ALPHA == α` is violated → UNSAT. The challenge C1 reads is bound to the public α.
#[test]
fn forged_alpha_refuses_on_alpha_pin() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (elem, w, v, alpha) = fixture();
    let (row, acc_all) = honest_row(elem, w, v, alpha);
    let trace = trace_of(&row);
    assert!(!rejects(&desc, &trace, &pis(acc_all, alpha)), "non-vacuity");
    let mut forged = pis(acc_all, alpha);
    forged[PI_ALPHA0] = forged[PI_ALPHA0] + BabyBear::ONE; // claim a different α
    assert!(
        rejects(&desc, &trace, &forged),
        "a forged α (ALPHA column does not equal it) must be REJECTED (alpha pin)"
    );
}
