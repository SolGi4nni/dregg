//! # The emit-from-Lean EQUALITY GATE — sorted-tree NON-MEMBERSHIP (the `revocation` family).
//!
//! Validates the historical depth-2 non-revocation descriptor emitted from Lean as an
//! `EffectVmDescriptor2` and gates green through the REAL
//! `prove_vm_descriptor2` / `verify_vm_descriptor2`.
//! The deployed depth-4 path is separately pinned by `non_revocation_adjacency_emit_gate`.
//!
//! The descriptor is AUTHORED in Lean (`metatheory/Dregg2/Circuit/Emit/NonRevocationEmit.lean`,
//! `nonRevocationDesc`) and its wire string is byte-pinned there (`emitVmJson2` `#guard`). This test
//! embeds that EXACT string ([`GOLDEN_JSON`]), and:
//!
//!   1. DECODES it via [`parse_vm_descriptor2`] and asserts the decode equals an independently
//!      hand-built `EffectVmDescriptor2` (Lean emit ≡ Rust builder — a byte drift on either side
//!      breaks this OR the Lean `#guard`);
//!   2. proves an HONEST freshness witness — an item `x` strictly bracketed by two ADJACENT
//!      committed sorted leaves `L < x < R`, both members of the public root — through
//!      [`prove_vm_descriptor2`], asserts ACCEPT, and re-verifies;
//!   3. the MUTATION CANARIES — each tamper forces a real UNSAT rejected BY A SPECIFIC CONSTRAINT:
//!      forged root PI (root pin), de-bracketed item (the 30-bit ORDERING RANGE — the non-membership
//!      tooth), non-adjacent neighbors (adjacency gate), forged bracketing leaf / forged sibling
//!      (Merkle-path membership pins), and a forged published queried item (the no-double-spend
//!      binding "b"). Each canary asserts the honest witness ACCEPTS first, so none is vacuous.

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    CHIP_OUT_LANES, CHIP_RATE, CHIP_TUPLE_LEN, EffectVmDescriptor2, LookupSpec, MemBoundaryWitness,
    TID_P2, TID_RANGE, TableDef2, TableSem, VmConstraint2, parse_vm_descriptor2,
    prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};
use dregg_circuit::poseidon2::hash_2_to_1;
use dregg_circuit::refusal::{Outcome, classify};

/// The BYTE-IDENTICAL wire string Lean's `emitVmJson2 nonRevocationDesc` emits (pinned by the
/// `#guard` in `NonRevocationEmit.lean`). If Lean's emitter drifts, that `#guard` fails; if this
/// literal drifts, the `decoded == hand_built` assertion fails. Neither can silently diverge.
const GOLDEN_JSON: &str = r#"{"name":"dregg-non-revocation-sorted-tree::poseidon2-v1","ir":2,"trace_width":27,"public_input_count":2,"tables":[{"id":2,"name":"range","arity":1,"sem":"range","bits":30}],"constraints":[{"t":"lookup","table":1,"tuple":[{"t":"const","v":2},{"t":"var","v":1},{"t":"var","v":2},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":9},{"t":"var","v":13},{"t":"var","v":14},{"t":"var","v":15},{"t":"var","v":16},{"t":"var","v":17},{"t":"var","v":18},{"t":"var","v":19}]},{"t":"lookup","table":1,"tuple":[{"t":"const","v":2},{"t":"var","v":10},{"t":"var","v":11},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":12},{"t":"var","v":20},{"t":"var","v":21},{"t":"var","v":22},{"t":"var","v":23},{"t":"var","v":24},{"t":"var","v":25},{"t":"var","v":26}]},{"t":"gate","body":{"t":"add","l":{"t":"var","v":10},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"var","v":5},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":0}}},"r":{"t":"var","v":1}},"r":{"t":"const","v":1}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"var","v":6},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":2}}},"r":{"t":"var","v":0}},"r":{"t":"const","v":1}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":7},"r":{"t":"var","v":5}},"r":{"t":"const","v":-1006632959}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":8},"r":{"t":"var","v":6}},"r":{"t":"const","v":-1006632959}}},{"t":"lookup","table":2,"tuple":[{"t":"var","v":7}]},{"t":"lookup","table":2,"tuple":[{"t":"var","v":8}]},{"t":"lookup","table":2,"tuple":[{"t":"var","v":5}]},{"t":"lookup","table":2,"tuple":[{"t":"var","v":6}]},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":4},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":3}}},"r":{"t":"const","v":-1}}},{"t":"pi_binding","row":"first","col":12,"pi_index":0},{"t":"pi_binding","row":"first","col":0,"pi_index":1},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"var","v":10},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"var","v":5},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":0}}},"r":{"t":"var","v":1}},"r":{"t":"const","v":1}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"add","l":{"t":"add","l":{"t":"var","v":6},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":2}}},"r":{"t":"var","v":0}},"r":{"t":"const","v":1}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":7},"r":{"t":"var","v":5}},"r":{"t":"const","v":-1006632959}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":8},"r":{"t":"var","v":6}},"r":{"t":"const","v":-1006632959}}},{"t":"boundary","row":"last","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":4},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":3}}},"r":{"t":"const","v":-1}}}],"hash_sites":[],"ranges":[]}"#;

// --- Trace column layout (must match `NonRevocationEmit.lean` §1). ---
const X: usize = 0;
const LEAF_L: usize = 1;
const LEAF_R: usize = 2;
const LPOS: usize = 3;
const RPOS: usize = 4;
const DIFF_L: usize = 5;
const DIFF_R: usize = 6;
const RL: usize = 7;
const RR: usize = 8;
const PAR0: usize = 9;
const CUR1: usize = 10;
const SIB1: usize = 11;
const PAR1: usize = 12;
const LEVEL0_LANE_BASE: usize = 13;
const LEVEL1_LANE_BASE: usize = 20;
const NONREV_WIDTH: usize = 27;

/// `(p−1)/2 − 1` for BabyBear — the deployed `revocation.rs::HALF_P_MINUS_1`.
const HALF_P_MINUS_1: u32 = 1_006_632_959;

// --- Expression builders (structurally IDENTICAL to the Lean `EmittedExpr` bodies §2). ---

/// `a − b` (Lean `subBody`).
fn sub(a: usize, b: usize) -> LeanExpr {
    LeanExpr::add(
        LeanExpr::Var(a),
        LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(b)),
    )
}

/// An arity-2 `TID_P2` chip lookup absorbing `[a, b]`, binding out0 to `out_col` and lanes 1..7 to
/// `lane_base..lane_base+7`. Built EXACTLY as Lean's `chipLookupTuple` (arity tag = 2 = ins.length,
/// `CHIP_RATE` zero-padded inputs, then out0 :: 7 lanes) — the `hash_2_to_1` binary-node hash.
fn chip2_lookup(a: usize, b: usize, out_col: usize, lane_base: usize) -> VmConstraint2 {
    let mut tuple: Vec<LeanExpr> = Vec::with_capacity(CHIP_TUPLE_LEN);
    tuple.push(LeanExpr::Const(2)); // arity tag (= ins.length in Lean's chipLookupTuple)
    let ins = [a, b];
    for i in 0..CHIP_RATE {
        tuple.push(match ins.get(i) {
            Some(&c) => LeanExpr::Var(c),
            None => LeanExpr::Const(0),
        });
    }
    tuple.push(LeanExpr::Var(out_col)); // out0 = the node digest
    for j in 0..(CHIP_OUT_LANES - 1) {
        tuple.push(LeanExpr::Var(lane_base + j));
    }
    assert_eq!(tuple.len(), CHIP_TUPLE_LEN);
    VmConstraint2::Lookup(LookupSpec {
        table: TID_P2,
        tuple,
    })
}

/// The independently-hand-built twin of the Lean `nonRevocationDesc`.
fn hand_built_desc() -> EffectVmDescriptor2 {
    let gate = |b: LeanExpr| VmConstraint2::Base(VmConstraint::Gate(b));
    // The LAST-ROW FIX: each semantic binding gate re-lowered as a `when_last_row` boundary so it
    // fires on the last row too (matching the deployed hand AIR's every-row binding).
    let boundary_last = |b: LeanExpr| {
        VmConstraint2::Base(VmConstraint::Boundary {
            row: VmRow::Last,
            body: b,
        })
    };
    let range_lookup = |w: usize| {
        VmConstraint2::Lookup(LookupSpec {
            table: TID_RANGE,
            tuple: vec![LeanExpr::Var(w)],
        })
    };
    // continuity: CUR1 − PAR0
    let cont = sub(CUR1, PAR0);
    // diff_left − x + L + 1
    let diff_l = LeanExpr::add(
        LeanExpr::add(
            LeanExpr::add(
                LeanExpr::Var(DIFF_L),
                LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(X)),
            ),
            LeanExpr::Var(LEAF_L),
        ),
        LeanExpr::Const(1),
    );
    // diff_right − R + x + 1
    let diff_r = LeanExpr::add(
        LeanExpr::add(
            LeanExpr::add(
                LeanExpr::Var(DIFF_R),
                LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(LEAF_R)),
            ),
            LeanExpr::Var(X),
        ),
        LeanExpr::Const(1),
    );
    // RL + diff_left − HALF_P_MINUS_1
    let range_l_bind = LeanExpr::add(
        LeanExpr::add(LeanExpr::Var(RL), LeanExpr::Var(DIFF_L)),
        LeanExpr::Const(-(HALF_P_MINUS_1 as i64)),
    );
    // RR + diff_right − HALF_P_MINUS_1
    let range_r_bind = LeanExpr::add(
        LeanExpr::add(LeanExpr::Var(RR), LeanExpr::Var(DIFF_R)),
        LeanExpr::Const(-(HALF_P_MINUS_1 as i64)),
    );
    // RPOS − LPOS − 1
    let adj = LeanExpr::add(
        LeanExpr::add(
            LeanExpr::Var(RPOS),
            LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(LPOS)),
        ),
        LeanExpr::Const(-1),
    );
    EffectVmDescriptor2 {
        name: "dregg-non-revocation-sorted-tree::poseidon2-v1".to_string(),
        trace_width: NONREV_WIDTH,
        public_input_count: 2,
        tables: vec![TableDef2 {
            id: TID_RANGE,
            name: "range".to_string(),
            arity: 1,
            sem: TableSem::Range { bits: 30 },
        }],
        constraints: vec![
            chip2_lookup(LEAF_L, LEAF_R, PAR0, LEVEL0_LANE_BASE),
            chip2_lookup(CUR1, SIB1, PAR1, LEVEL1_LANE_BASE),
            gate(cont.clone()),
            gate(diff_l.clone()),
            gate(diff_r.clone()),
            gate(range_l_bind.clone()),
            gate(range_r_bind.clone()),
            range_lookup(RL),
            range_lookup(RR),
            // LOWER-BOUND FIX: direct range-lookups on the diff wires pin diff ∈ [0,HALF]
            // (excludes the negative window that let a member be proven "fresh").
            range_lookup(DIFF_L),
            range_lookup(DIFF_R),
            gate(adj.clone()),
            VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::First,
                col: PAR1,
                pi_index: 0,
            }),
            VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::First,
                col: X,
                pi_index: 1,
            }),
            // LAST-ROW FIX: the six semantic binding bodies re-lowered as `when_last_row` boundaries
            // (same order as the gates) — a HEIGHT-1 / last-row trace can no longer free them.
            boundary_last(cont),
            boundary_last(diff_l),
            boundary_last(diff_r),
            boundary_last(range_l_bind),
            boundary_last(range_r_bind),
            boundary_last(adj),
        ],
        hash_sites: vec![],
        ranges: vec![],
    }
}

/// Build ONE fully-consistent active row for the given `(x, L, R, lpos, rpos, sib1)` — the two
/// adjacent bottom-sibling leaves `L, R` hashed to `PAR0 = hash_2_to_1(L, R)`, then up to
/// `root = hash_2_to_1(PAR0, sib1)`; the ordering witnesses `diff_left = x − L − 1`,
/// `diff_right = R − x − 1` and their range wires `HALF_P_MINUS_1 − diff` filled so EVERY base gate
/// is satisfied by construction. Chip LANE columns are left zero (the prover fills them from the
/// genuine permutation). Returns `(row, root)`.
fn consistent_row(
    x: BabyBear,
    l: BabyBear,
    r: BabyBear,
    lpos: u32,
    rpos: u32,
    sib1: BabyBear,
) -> (Vec<BabyBear>, BabyBear) {
    let par0 = hash_2_to_1(l, r);
    let root = hash_2_to_1(par0, sib1);
    let diff_l = x - l - BabyBear::ONE;
    let diff_r = r - x - BabyBear::ONE;
    let half = BabyBear::new(HALF_P_MINUS_1);
    let mut row = vec![BabyBear::ZERO; NONREV_WIDTH];
    row[X] = x;
    row[LEAF_L] = l;
    row[LEAF_R] = r;
    row[LPOS] = BabyBear::new(lpos);
    row[RPOS] = BabyBear::new(rpos);
    row[DIFF_L] = diff_l;
    row[DIFF_R] = diff_r;
    row[RL] = half - diff_l;
    row[RR] = half - diff_r;
    row[PAR0] = par0;
    row[CUR1] = par0; // continuity
    row[SIB1] = sib1;
    row[PAR1] = root;
    (row, root)
}

/// A 4-row (power-of-two) trace of IDENTICAL rows — the gates/lookups are ungated-per-row, so every
/// row must satisfy them (no zero padding; the honest row is repeated).
fn trace_of(row: &[BabyBear]) -> Vec<Vec<BabyBear>> {
    vec![row.to_vec(), row.to_vec(), row.to_vec(), row.to_vec()]
}

/// The honest freshness fixture: item `x = 200` bracketed by adjacent leaves `L = 100 < 200 < 300 = R`
/// at consecutive positions `0, 1`, with a level-1 sibling.
fn honest_row() -> (Vec<BabyBear>, BabyBear) {
    consistent_row(
        BabyBear::new(200),
        BabyBear::new(100),
        BabyBear::new(300),
        0,
        1,
        BabyBear::new(777_777),
    )
}

/// `true` iff this `(trace, pis)` is REJECTED end-to-end — proving refuses OR the produced proof
/// fails to VERIFY against `pis`. `false` iff it both proves AND verifies. Prove-THEN-verify is the
/// faithful gate (a `--release` prove does not self-check the first-row `PiBinding` against the PIs;
/// the consumer's `verify_vm_descriptor2` is the real check — the production posture).
fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    match classify("rejects", || {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }) {
        // The p3 debug prover's DOCUMENTED unsat verdict — a real refusal.
        // `classify` REDs on any other panic (a stray unwrap, a trace-assembly
        // debug_assert), which used to land here and read as "rejected".
        Outcome::UnsatPanic(_) => true,
        Outcome::Err(_) => true,
        Outcome::Accepted(_) => false,
    }
}

/// STEP 1 — the emitted descriptor decodes and equals the hand-built twin (Lean emit ≡ Rust
/// semantics), and has exactly the expected shape.
#[test]
fn non_revocation_emit_decodes_to_hand_built() {
    let decoded = parse_vm_descriptor2(GOLDEN_JSON).expect("the Lean-emitted golden JSON decodes");
    let hand = hand_built_desc();
    assert_eq!(
        decoded, hand,
        "the Lean-emitted descriptor must equal the independently hand-built descriptor"
    );
    assert_eq!(decoded.trace_width, NONREV_WIDTH);
    assert_eq!(decoded.public_input_count, 2);
    let chip_lookups = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
        .count();
    assert_eq!(
        chip_lookups, 2,
        "two child→parent chip lookups (depth-2 shared path)"
    );
    let range_lookups = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_RANGE))
        .count();
    assert_eq!(range_lookups, 2, "the two strict-ordering range lookups");
    let pins = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
        .count();
    assert_eq!(pins, 2, "the root pin + the queried-item pin");
}

/// STEP 2 — THE POSITIVE POLE: an honest freshness witness proves through the emitted descriptor and
/// re-verifies against `[root, queried_item]`.
#[test]
fn honest_non_revocation_proves_and_verifies() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (row, root) = honest_row();
    let x = row[X];
    let trace = trace_of(&row);
    let proof = prove_vm_descriptor2(
        &desc,
        &trace,
        &[root, x],
        &MemBoundaryWitness::default(),
        &[],
    )
    .expect("the honest freshness witness must prove (bracketed item under the committed root)");
    verify_vm_descriptor2(&desc, &proof, &[root, x])
        .expect("the honest proof must re-verify against [root, queried_item]");
}

/// STEP 3a — CANARY (forged root): honest trace, but a FORGED public root PI. The root pin
/// (`PAR1 == PI[0]`) is violated → UNSAT.
#[test]
fn forged_root_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (row, root) = honest_row();
    let x = row[X];
    let trace = trace_of(&row);
    assert!(
        !rejects(&desc, &trace, &[root, x]),
        "honest witness must be accepted — else vacuous"
    );
    assert!(
        rejects(&desc, &trace, &[root + BabyBear::ONE, x]),
        "a forged revocation root must be REJECTED (root pin)"
    );
}

/// STEP 3b — CANARY (de-bracketed item, THE NON-MEMBERSHIP TOOTH): the queried item is set far
/// above the left neighbor so `diff_left = x − L − 1` violates the strict half-field ordering bound
/// (`HALF_P_MINUS_1 − diff_left ≥ 2^30`). The 30-bit RANGE lookup on `RL` has no serving limb
/// decomposition → UNSAT. An item that is not strictly ordered just above its claimed left neighbor
/// cannot pass as bracketed. All other constraints stay satisfied (the row is rebuilt consistently),
/// so the bite is the RANGE constraint.
#[test]
fn de_bracketed_item_refuses_by_range() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (hrow, hroot) = honest_row();
    let hx = hrow[X];
    assert!(
        !rejects(&desc, &trace_of(&hrow), &[hroot, hx]),
        "honest witness must be accepted — else this canary is vacuous"
    );
    // x = L + 1 + 1_500_000_000 ⇒ diff_left = 1_500_000_000, inside the range REJECT window
    // [1006632960, 1946157056] ⇒ RL = HALF_P_MINUS_1 − diff_left wraps to ≥ 2^30.
    let l = BabyBear::new(100);
    let r = BabyBear::new(300);
    let x_bad = l + BabyBear::ONE + BabyBear::new(1_500_000_000);
    let (row, root) = consistent_row(x_bad, l, r, 0, 1, BabyBear::new(777_777));
    // sanity: the offending range wire genuinely exceeds 2^30 (so the tooth, not luck, rejects).
    assert!(
        row[RL].as_u32() >= (1u32 << 30),
        "the de-bracketed left range wire must exceed 2^30 for the range lookup to bite"
    );
    assert!(
        rejects(&desc, &trace_of(&row), &[root, x_bad]),
        "a de-bracketed item (ordering-bound violated) must be REJECTED by the range lookup"
    );
}

/// STEP 3c — CANARY (non-adjacent neighbors): honest bracket, but the two neighbor positions are NOT
/// consecutive (`RPOS = LPOS + 2`). The adjacency gate (`RPOS − LPOS − 1 = 0`) is violated → UNSAT.
/// If the bracketing leaves are not adjacent, something could sit between them — non-membership fails.
#[test]
fn non_adjacent_neighbors_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (row, root) = consistent_row(
        BabyBear::new(200),
        BabyBear::new(100),
        BabyBear::new(300),
        0,
        2, // NOT lpos + 1
        BabyBear::new(777_777),
    );
    let x = row[X];
    assert!(
        rejects(&desc, &trace_of(&row), &[root, x]),
        "non-adjacent bracketing positions must be REJECTED (adjacency gate)"
    );
}

/// STEP 3d — CANARY (forged bracketing leaf): the left neighbor value is changed and the tree is
/// honestly recomputed to a DIFFERENT root, but the proof CLAIMS the original root. The recomputed
/// `PAR1` no longer equals the claimed root → the root pin is UNSAT. The bracketing leaves are bound
/// to the committed root (a fabricated neighbor is refused).
#[test]
fn forged_bracketing_leaf_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (_, honest_root) = honest_row();
    // A different left neighbor (still < x): recomputes to a different root.
    let (row, tampered_root) = consistent_row(
        BabyBear::new(200),
        BabyBear::new(150), // was 100
        BabyBear::new(300),
        0,
        1,
        BabyBear::new(777_777),
    );
    assert_ne!(
        tampered_root, honest_root,
        "changing a bracketing leaf must change the root"
    );
    let x = row[X];
    assert!(
        rejects(&desc, &trace_of(&row), &[honest_root, x]),
        "a bracketing leaf not under the claimed root must be REJECTED (membership pin)"
    );
}

/// STEP 3e — CANARY (forged sibling): the level-1 sibling is changed and the tree is honestly
/// recomputed to a DIFFERENT root, but the proof claims the original root → the root pin is UNSAT.
/// The Merkle PATH to the committed root is load-bearing (a forged co-path is refused).
#[test]
fn forged_sibling_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (_, honest_root) = honest_row();
    let (row, tampered_root) = consistent_row(
        BabyBear::new(200),
        BabyBear::new(100),
        BabyBear::new(300),
        0,
        1,
        BabyBear::new(888_888), // was 777_777
    );
    assert_ne!(
        tampered_root, honest_root,
        "changing the sibling must change the root"
    );
    let x = row[X];
    assert!(
        rejects(&desc, &trace_of(&row), &[honest_root, x]),
        "a forged sibling (wrong co-path) must be REJECTED (membership pin)"
    );
}

/// STEP 3f — CANARY (forged queried item, the no-double-spend binding "b"): the honest freshness
/// witness for item `x`, but the verifier is handed a DIFFERENT expected item `x + 1` as `PI[1]`.
/// The queried-item pin (`X == PI[1]`) is violated → UNSAT. A freshness proof for one item does not
/// verify against a different expected item.
#[test]
fn forged_queried_item_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (row, root) = honest_row();
    let x = row[X];
    let trace = trace_of(&row);
    assert!(
        !rejects(&desc, &trace, &[root, x]),
        "honest witness must be accepted — else vacuous"
    );
    assert!(
        rejects(&desc, &trace, &[root, x + BabyBear::ONE]),
        "a freshness proof for one item must NOT verify against a different expected item"
    );
}
