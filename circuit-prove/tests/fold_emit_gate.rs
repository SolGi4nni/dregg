//! # The emit-from-Lean EQUALITY GATE — the attenuation FOLD step (`dregg-fold-step-v2`).
//!
//! The descriptor is AUTHORED in Lean (`metatheory/Dregg2/Circuit/Emit/FoldEmit.lean`, `foldDesc`)
//! and its wire string byte-pinned there (`emitVmJson2` `#guard`). This test embeds that EXACT string
//! ([`GOLDEN_JSON`]) and:
//!
//!   1. DECODES it via [`parse_vm_descriptor2`] and asserts it equals an independently hand-built
//!      `EffectVmDescriptor2` (Lean emit ≡ Rust builder — a byte drift on either side breaks this OR
//!      the Lean `#guard`);
//!   2. KATs the ARITY-7 fact-hash mapping: `chip_absorb_all_lanes(7, [pred,t0,t1,t2,0,0xFACF,1])[0]
//!      == hash_fact(pred,[t0,t1,t2])` — the leaf the deployed `fact_hash_correct` binds;
//!   3. proves an HONEST fold witness (two removal rows + a summary row, genuine `hash_fact`
//!      commitments) through [`prove_vm_descriptor2`], asserts ACCEPT, re-verifies;
//!   4. the MUTATION CANARIES — each tampers ONE witness/PI coordinate and asserts the prove-or-verify
//!      REFUSES (real UNSAT), bitten by a NAMED constraint: the arity-7 chip lookup (fact-hash), the
//!      `membership_root_matches` gate, the `removal_count_increment` window, the summary root PI
//!      boundary, the `removal_hash_required` gate, and the pi4-carrier constancy window.
//!
//! The canaries are NON-VACUOUS by construction: each first asserts the honest witness is ACCEPTED,
//! then that the tampered one is REJECTED.
//!
//! This descriptor is the emitted twin of the deployed DSL fold AIR
//! (`circuit/src/dsl/fold.rs::fold_circuit_descriptor`, "dregg-fold-dsl-v2"). The Merkle-membership
//! of removed facts, the variable-length root-transition sponge, and the two host validation gates
//! (`delta_nonempty`, `checks_commitment_zero_when_no_checks`) ride OFF-descriptor exactly as the
//! deployed AIR leaves them.

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    CHIP_OUT_LANES, CHIP_RATE, CHIP_TUPLE_LEN, EffectVmDescriptor2, LookupSpec, MemBoundaryWitness,
    TID_P2, VmConstraint2, WindowExpr, WindowGateSpec, chip_absorb_all_lanes, parse_vm_descriptor2,
    prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};
use dregg_circuit::poseidon2::hash_fact;

/// The BYTE-IDENTICAL wire string Lean's `emitVmJson2 foldDesc` emits (pinned by the `#guard` in
/// `FoldEmit.lean`). If Lean's emitter drifts, that `#guard` fails; if this literal drifts, the
/// `decoded == hand_built` assertion fails. Neither can silently diverge.
const GOLDEN_JSON: &str = r#"{"name":"dregg-fold-step-v2","ir":2,"trace_width":21,"public_input_count":6,"tables":[],"constraints":[{"t":"gate","body":{"t":"mul","l":{"t":"var","v":0},"r":{"t":"add","l":{"t":"var","v":0},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":11},"r":{"t":"add","l":{"t":"var","v":11},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":0}}},"r":{"t":"add","l":{"t":"var","v":2},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":3}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":0}}},"r":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":11}}}}},{"t":"lookup","table":1,"tuple":[{"t":"const","v":7},{"t":"var","v":7},{"t":"var","v":8},{"t":"var","v":9},{"t":"var","v":10},{"t":"const","v":0},{"t":"const","v":64207},{"t":"const","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":1},{"t":"var","v":14},{"t":"var","v":15},{"t":"var","v":16},{"t":"var","v":17},{"t":"var","v":18},{"t":"var","v":19},{"t":"var","v":20}]},{"t":"pi_binding","row":"first","col":3,"pi_index":0},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"loc","c":3},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"nxt","c":3}}}},{"t":"pi_binding","row":"first","col":4,"pi_index":1},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"loc","c":4},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"nxt","c":4}}}},{"t":"window_gate","on_transition":true,"body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":0}}},"r":{"t":"add","l":{"t":"nxt","c":5},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":12}}}}},{"t":"pi_binding","row":"last","col":13,"pi_index":4},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"loc","c":13},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"nxt","c":13}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":0},"r":{"t":"add","l":{"t":"var","v":2},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":13}}}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"var","v":0},"r":{"t":"const","v":-1}}},{"t":"pi_binding","row":"last","col":5,"pi_index":2},{"t":"pi_binding","row":"last","col":6,"pi_index":3},{"t":"pi_binding","row":"last","col":2,"pi_index":4}],"hash_sites":[],"ranges":[]}"#;

// --- Trace column layout (must match `FoldEmit.lean` §1). ---
const ROW_TYPE: usize = 0;
const FACT_HASH: usize = 1;
const MEMBERSHIP_ROOT: usize = 2;
const OLD_ROOT: usize = 3;
const NEW_ROOT: usize = 4;
const REMOVAL_COUNT: usize = 5;
const CHECK_COUNT: usize = 6;
const FACT_PRED: usize = 7;
const FACT_TERM0: usize = 8;
const FACT_TERM1: usize = 9;
const FACT_TERM2: usize = 10;
const HASH_VALID: usize = 11;
const REMOVAL_COUNT_PLUS_ONE: usize = 12;
const PI4_CARRIER: usize = 13;
const FACT_LANE_BASE: usize = 14;
const FOLD_WIDTH: usize = 21;

const FACT_MARK: i64 = 0xFACF; // 64207

// --- WindowExpr helpers. ---
fn wloc(c: usize) -> WindowExpr {
    WindowExpr::Loc(c)
}
fn wnxt(c: usize) -> WindowExpr {
    WindowExpr::Nxt(c)
}
fn wadd(a: WindowExpr, b: WindowExpr) -> WindowExpr {
    WindowExpr::Add(Box::new(a), Box::new(b))
}
fn wmul(a: WindowExpr, b: WindowExpr) -> WindowExpr {
    WindowExpr::Mul(Box::new(a), Box::new(b))
}
fn wneg(a: WindowExpr) -> WindowExpr {
    wmul(WindowExpr::Const(-1), a)
}
/// `loc c - nxt c` — a column's cross-row constancy window body.
fn constancy(c: usize) -> WindowExpr {
    wadd(wloc(c), wneg(wnxt(c)))
}
fn wgate(body: WindowExpr) -> VmConstraint2 {
    VmConstraint2::WindowGate(WindowGateSpec {
        body,
        on_transition: true,
    })
}

// --- LeanExpr helpers. ---
fn one_minus(v: usize) -> LeanExpr {
    LeanExpr::add(
        LeanExpr::Const(1),
        LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(v)),
    )
}
fn gate(body: LeanExpr) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::Gate(body))
}
fn pib(row: VmRow, col: usize, pi_index: usize) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index })
}

/// The arity-7 `hash_fact` chip lookup: `[7, PRED,t0,t1,t2, 0, 0xFACF, 1, 0×9, FACT_HASH, lanes×7]`
/// — built EXACTLY as Lean's `chipLookupTuple` over the 7 inputs (`0/0xFACF/1` explicit constants).
fn fact_lookup() -> VmConstraint2 {
    let inputs = [
        LeanExpr::Var(FACT_PRED),
        LeanExpr::Var(FACT_TERM0),
        LeanExpr::Var(FACT_TERM1),
        LeanExpr::Var(FACT_TERM2),
        LeanExpr::Const(0),
        LeanExpr::Const(FACT_MARK),
        LeanExpr::Const(1),
    ];
    let mut tuple: Vec<LeanExpr> = Vec::with_capacity(CHIP_TUPLE_LEN);
    tuple.push(LeanExpr::Const(7)); // arity tag = ins.length
    for i in 0..CHIP_RATE {
        tuple.push(inputs.get(i).cloned().unwrap_or(LeanExpr::Const(0)));
    }
    tuple.push(LeanExpr::Var(FACT_HASH)); // out0 = the fact digest
    for j in 0..(CHIP_OUT_LANES - 1) {
        tuple.push(LeanExpr::Var(FACT_LANE_BASE + j));
    }
    assert_eq!(tuple.len(), CHIP_TUPLE_LEN);
    VmConstraint2::Lookup(LookupSpec {
        table: TID_P2,
        tuple,
    })
}

/// The independently-hand-built twin of Lean's `foldDesc` (the deployed DSL fold semantics in IR-v2).
fn hand_built_desc() -> EffectVmDescriptor2 {
    let constraints = vec![
        // row_type_binary, hash_valid_binary
        gate(LeanExpr::mul(
            LeanExpr::Var(ROW_TYPE),
            LeanExpr::add(LeanExpr::Var(ROW_TYPE), LeanExpr::Const(-1)),
        )),
        gate(LeanExpr::mul(
            LeanExpr::Var(HASH_VALID),
            LeanExpr::add(LeanExpr::Var(HASH_VALID), LeanExpr::Const(-1)),
        )),
        // membership_root_matches: (1-ROW_TYPE)*(MEMBERSHIP_ROOT-OLD_ROOT)
        gate(LeanExpr::mul(
            one_minus(ROW_TYPE),
            LeanExpr::add(
                LeanExpr::Var(MEMBERSHIP_ROOT),
                LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(OLD_ROOT)),
            ),
        )),
        // removal_hash_required: (1-ROW_TYPE)*(1-HASH_VALID)
        gate(LeanExpr::mul(one_minus(ROW_TYPE), one_minus(HASH_VALID))),
        // fact_hash_correct (arity-7 chip lookup)
        fact_lookup(),
        // old/new root: first pin + constancy
        pib(VmRow::First, OLD_ROOT, 0),
        wgate(constancy(OLD_ROOT)),
        pib(VmRow::First, NEW_ROOT, 1),
        wgate(constancy(NEW_ROOT)),
        // removal_count_increment: (1-loc ROW_TYPE)*(nxt RC - loc RC_PLUS_ONE)
        wgate(wmul(
            wadd(WindowExpr::Const(1), wneg(wloc(ROW_TYPE))),
            wadd(wnxt(REMOVAL_COUNT), wneg(wloc(REMOVAL_COUNT_PLUS_ONE))),
        )),
        // pi4 carrier: last pin + constancy, then the summary-gated root-transition binding
        pib(VmRow::Last, PI4_CARRIER, 4),
        wgate(constancy(PI4_CARRIER)),
        // root_transition_binding: ROW_TYPE*(MEMBERSHIP_ROOT-PI4_CARRIER)
        gate(LeanExpr::mul(
            LeanExpr::Var(ROW_TYPE),
            LeanExpr::add(
                LeanExpr::Var(MEMBERSHIP_ROOT),
                LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(PI4_CARRIER)),
            ),
        )),
        // last-row boundaries
        VmConstraint2::Base(VmConstraint::Boundary {
            row: VmRow::Last,
            body: LeanExpr::add(LeanExpr::Var(ROW_TYPE), LeanExpr::Const(-1)),
        }),
        pib(VmRow::Last, REMOVAL_COUNT, 2),
        pib(VmRow::Last, CHECK_COUNT, 3),
        pib(VmRow::Last, MEMBERSHIP_ROOT, 4),
    ];
    EffectVmDescriptor2 {
        name: "dregg-fold-step-v2".to_string(),
        trace_width: FOLD_WIDTH,
        public_input_count: 6,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    }
}

// --- The honest fold witness (2 removals + summary, padded to 4 rows). ---
const OLD_ROOT_V: u32 = 111_111;
const NEW_ROOT_V: u32 = 222_222;
const NUM_CHECKS: u32 = 3;
const CHECKS_NARROW: u32 = 777; // pi[5], unconstrained in-descriptor (host-gate coordinate)
/// The witnessed root-transition hash (`pi[4]`); the sponge that produces it rides OFF-descriptor.
const TRANSITION_HASH: u32 = 909_090;

/// The two removed facts (distinct predicates/terms so each fact hash is distinct).
fn facts() -> [(BabyBear, [BabyBear; 3]); 2] {
    [
        (
            BabyBear::new(10),
            [BabyBear::new(20), BabyBear::new(30), BabyBear::ZERO],
        ),
        (
            BabyBear::new(110),
            [BabyBear::new(120), BabyBear::new(130), BabyBear::ZERO],
        ),
    ]
}

/// One row, zero-initialised; `FACT_HASH` is ALWAYS the genuine `hash_fact` of the row's fact columns
/// (on the summary/pad rows PRED/terms are 0, so `FACT_HASH = hash_fact(0,[0,0,0])`) — the documented
/// completeness-narrowing that keeps the un-gated lookup satisfiable on every row.
fn honest_trace() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let facts = facts();
    let n = facts.len() as u32;
    let old_root = BabyBear::new(OLD_ROOT_V);
    let new_root = BabyBear::new(NEW_ROOT_V);
    let t = BabyBear::new(TRANSITION_HASH);
    let zero_fact_hash = hash_fact(
        BabyBear::ZERO,
        &[BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
    );

    let mut trace: Vec<Vec<BabyBear>> = Vec::new();
    for (i, (pred, terms)) in facts.iter().enumerate() {
        let mut row = vec![BabyBear::ZERO; FOLD_WIDTH];
        row[ROW_TYPE] = BabyBear::ZERO;
        row[FACT_HASH] = hash_fact(*pred, terms);
        row[MEMBERSHIP_ROOT] = old_root; // membership_root_matches: on removal rows MR == OLD_ROOT
        row[OLD_ROOT] = old_root;
        row[NEW_ROOT] = new_root;
        row[REMOVAL_COUNT] = BabyBear::new((i + 1) as u32);
        row[CHECK_COUNT] = BabyBear::new(NUM_CHECKS);
        row[FACT_PRED] = *pred;
        row[FACT_TERM0] = terms[0];
        row[FACT_TERM1] = terms[1];
        row[FACT_TERM2] = terms[2];
        row[HASH_VALID] = BabyBear::ONE;
        let is_last_removal = (i + 1) as u32 == n;
        row[REMOVAL_COUNT_PLUS_ONE] = if is_last_removal {
            BabyBear::new(n)
        } else {
            BabyBear::new((i + 2) as u32)
        };
        row[PI4_CARRIER] = t;
        trace.push(row);
    }
    // Summary row.
    let mut summary = vec![BabyBear::ZERO; FOLD_WIDTH];
    summary[ROW_TYPE] = BabyBear::ONE;
    summary[FACT_HASH] = zero_fact_hash;
    summary[MEMBERSHIP_ROOT] = t; // carries the root-transition hash (bound to pi[4])
    summary[OLD_ROOT] = old_root;
    summary[NEW_ROOT] = new_root;
    summary[REMOVAL_COUNT] = BabyBear::new(n);
    summary[CHECK_COUNT] = BabyBear::new(NUM_CHECKS);
    summary[HASH_VALID] = BabyBear::ONE;
    summary[REMOVAL_COUNT_PLUS_ONE] = BabyBear::new(n);
    summary[PI4_CARRIER] = t;
    trace.push(summary.clone());
    // Pad to a power of two with copies of the summary (ROW_TYPE = 1, so the row-local gates that
    // gate on `is_removal` stay off; the last-row boundaries bind against pi as on the summary).
    while !trace.len().is_power_of_two() {
        trace.push(summary.clone());
    }

    let pis = vec![
        old_root,
        new_root,
        BabyBear::new(n),
        BabyBear::new(NUM_CHECKS),
        t,
        BabyBear::new(CHECKS_NARROW),
    ];
    (trace, pis)
}

/// `true` iff `(trace, pis)` is REJECTED end-to-end (prove refuses OR the proof fails to verify).
/// `false` iff it both proves AND verifies. Prove-THEN-verify is the faithful gate (the first-row /
/// last-row PiBindings are checked against the public inputs by `verify_vm_descriptor2`).
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

/// STEP 1 — the emitted descriptor decodes and equals the hand-built twin.
#[test]
fn fold_emit_decodes_to_hand_built() {
    let decoded = parse_vm_descriptor2(GOLDEN_JSON).expect("the Lean-emitted golden JSON decodes");
    let hand = hand_built_desc();
    assert_eq!(
        decoded, hand,
        "the Lean-emitted descriptor must equal the independently hand-built descriptor"
    );
    assert_eq!(decoded.trace_width, FOLD_WIDTH);
    assert_eq!(decoded.public_input_count, 6);
    let chip_lookups = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
        .count();
    assert_eq!(chip_lookups, 1, "the single arity-7 fact-hash lookup");
    let windows = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
        .count();
    assert_eq!(
        windows, 4,
        "old/new-root + pi4 constancy, and removal-count increment"
    );
}

/// STEP 2 — the family signature: an arity-7 chip absorb of `[pred,t0,t1,t2,0,0xFACF,1]` IS
/// `hash_fact`, and every fact coordinate is load-bearing.
#[test]
fn arity7_chip_lookup_is_hash_fact() {
    let pred = BabyBear::new(10);
    let terms = [BabyBear::new(20), BabyBear::new(30), BabyBear::ZERO];
    let ins = [
        pred,
        terms[0],
        terms[1],
        terms[2],
        BabyBear::ZERO,
        BabyBear::new(FACT_MARK as u32),
        BabyBear::ONE,
    ];
    let lanes = chip_absorb_all_lanes(7, &ins);
    assert_eq!(
        lanes[0],
        hash_fact(pred, &terms),
        "arity-7 chip out0 must equal hash_fact (the removed-fact commitment)"
    );
    // Perturbing pred or any term changes the digest (the commitment binds the whole fact).
    for j in 0..4 {
        let mut alt = ins;
        alt[j] += BabyBear::ONE;
        assert_ne!(
            chip_absorb_all_lanes(7, &alt)[0],
            lanes[0],
            "fact coordinate {j} is dead — the commitment does not bind it"
        );
    }
}

/// STEP 3 — THE POSITIVE POLE: the honest fold witness proves and re-verifies.
#[test]
fn honest_fold_proves_and_verifies() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis) = honest_trace();
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the honest fold witness must prove");
    verify_vm_descriptor2(&desc, &proof, &pis).expect("the honest proof must re-verify");
}

/// STEP 4a — CANARY (fact-hash / arity-7 chip lookup): forge a removal row's `FACT_HASH`. No genuine
/// chip row serves the forged digest → UNSAT. THE FAMILY SIGNATURE TOOTH.
#[test]
fn forged_fact_hash_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis) = honest_trace();
    assert!(
        !rejects(&desc, &trace, &pis),
        "honest must be accepted — else vacuous"
    );
    let mut bad = trace.clone();
    bad[0][FACT_HASH] += BabyBear::ONE;
    assert!(
        rejects(&desc, &bad, &pis),
        "a forged fact commitment (no serving chip row) must be REJECTED"
    );
}

/// STEP 4b — CANARY (`membership_root_matches`): a removal row whose `MEMBERSHIP_ROOT ≠ OLD_ROOT`.
/// The gate `(1-ROW_TYPE)*(MR-OR)` is nonzero → UNSAT.
#[test]
fn membership_root_mismatch_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis) = honest_trace();
    let mut bad = trace.clone();
    bad[0][MEMBERSHIP_ROOT] += BabyBear::ONE;
    assert!(
        rejects(&desc, &bad, &pis),
        "a removal row with membership_root != old_root must be REJECTED"
    );
}

/// STEP 4c — CANARY (`removal_count_increment` window): forge a removal row's `REMOVAL_COUNT_PLUS_ONE`
/// so the next row's count no longer matches. The transition window is nonzero → UNSAT.
#[test]
fn broken_removal_increment_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis) = honest_trace();
    let mut bad = trace.clone();
    bad[0][REMOVAL_COUNT_PLUS_ONE] += BabyBear::new(3);
    assert!(
        rejects(&desc, &bad, &pis),
        "a broken removal-count increment must be REJECTED"
    );
}

/// STEP 4d — CANARY (summary root PI boundary): honest trace, but a FORGED `pi[4]` (root-transition
/// hash). The last-row `MEMBERSHIP_ROOT == pi[4]` boundary (and the pi4-carrier pin) fail → UNSAT.
#[test]
fn forged_transition_hash_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis) = honest_trace();
    let mut forged = pis.clone();
    forged[4] += BabyBear::ONE; // claim a different root-transition hash
    assert!(
        rejects(&desc, &trace, &forged),
        "a summary root-transition hash the trace does not publish must be REJECTED"
    );
}

/// STEP 4e — CANARY (`removal_hash_required`): a removal row with `HASH_VALID = 0`. The gate
/// `(1-ROW_TYPE)*(1-HASH_VALID)` is nonzero → UNSAT.
#[test]
fn removal_without_valid_hash_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis) = honest_trace();
    let mut bad = trace.clone();
    bad[0][HASH_VALID] = BabyBear::ZERO;
    assert!(
        rejects(&desc, &bad, &pis),
        "a removal row lacking a valid hash must be REJECTED"
    );
}

/// STEP 4f — CANARY (pi4-carrier constancy window): forge a NON-last row's `PI4_CARRIER`. The
/// constancy window `loc - nxt` breaks → UNSAT (this is the only tooth reading a removal row's
/// carrier, so the rejection is isolated to it).
#[test]
fn broken_pi4_carrier_constancy_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis) = honest_trace();
    let mut bad = trace.clone();
    bad[0][PI4_CARRIER] += BabyBear::ONE;
    assert!(
        rejects(&desc, &bad, &pis),
        "a non-constant pi4 carrier must be REJECTED"
    );
}
