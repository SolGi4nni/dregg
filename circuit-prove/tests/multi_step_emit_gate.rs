//! # The emit-from-Lean EQUALITY GATE — the MULTI-STEP derivation-chaining composition (family
//! `multi_step`).
//!
//! The descriptor is AUTHORED in Lean (`metatheory/Dregg2/Circuit/Emit/MultiStepChainEmit.lean`,
//! `multiStepChainDesc`) and its wire string is byte-pinned there (`emitVmJson2` `#guard`). It
//! emits the accumulated-hash CHAIN that composes K single-step derivations into one authorization:
//!
//!     prev₀ = initial_state_root
//!     accᵢ  = hash_2_to_1(prevᵢ, derived_hashᵢ)     -- MS1, an arity-2 Poseidon2Chip absorb
//!     prevᵢ₊₁ = accᵢ                                  -- MS2, a transition `window_gate`
//!     final_accumulated_hash = acc_last               -- MS3, a last-row `pi_binding`
//!
//! The chaining semantics are the authoritative producer
//! (`circuit/src/multi_step_air.rs::MultiStepWitness::compute_accumulated_hashes` +
//! `circuit/src/dsl/derivation.rs::generate_multi_step_trace_dsl`). ⚠ In the DEPLOYED tree those
//! chain columns are witness-computed but ENFORCED BY NOTHING (`MultiStepStarkAir::eval_constraints`
//! returns `ZERO`, `boundary_constraints` returns `[]`, `multi_step_air.rs:195-211`); this emitted
//! descriptor is the ENFORCED assurance twin (the `AccumulatorOpenEmit` posture).
//!
//! This test embeds the EXACT Lean-pinned string ([`GOLDEN_JSON`]) and:
//!
//!   1. DECODES it via [`parse_vm_descriptor2`] and asserts the decode equals an independently
//!      hand-built `EffectVmDescriptor2` (Lean emit ≡ Rust builder — a byte drift on either side
//!      breaks this OR the Lean `#guard`);
//!   2. proves an HONEST 4-step chain witness (genuine `hash_2_to_1` links) through
//!      [`prove_vm_descriptor2`], asserts ACCEPT, and re-verifies the proof;
//!   3. the MUTATION CANARIES — each tampers the witness so exactly one constraint family bites,
//!      and asserts the prove-or-verify REFUSES (real UNSAT):
//!        (a) a step's `derived_hash` bumped off its `ACC` digest  → MS1  `Poseidon2Chip` lookup,
//!        (b) a chain link broken (`prevᵢ₊₁ ≠ accᵢ`) with MS1/pins consistent → MS2 `window_gate`,
//!        (c) a forged initial-state-root PI                        → MS3a first-row `pi_binding`,
//!        (d) a forged final-accumulated-hash PI                    → MS3b last-row  `pi_binding`.
//!
//! The canaries are NON-VACUOUS by construction: each first asserts the honest witness is ACCEPTED,
//! then asserts the tampered witness is REJECTED.

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    CHIP_OUT_LANES, CHIP_RATE, CHIP_TUPLE_LEN, EffectVmDescriptor2, LookupSpec, MemBoundaryWitness,
    TID_P2, VmConstraint2, WindowExpr, WindowGateSpec, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};
use dregg_circuit::poseidon2::hash_2_to_1;

/// The BYTE-IDENTICAL wire string Lean's `emitVmJson2 multiStepChainDesc` emits (pinned by the
/// `#guard` in `MultiStepChainEmit.lean`). If Lean drifts, that `#guard` fails; if this literal
/// drifts, the `decoded == hand_built` assertion fails. Neither can silently diverge.
const GOLDEN_JSON: &str = r#"{"name":"multi-step-accumulated-hash-chain::poseidon2-v1","ir":2,"trace_width":10,"public_input_count":2,"tables":[],"constraints":[{"t":"lookup","table":1,"tuple":[{"t":"const","v":2},{"t":"var","v":0},{"t":"var","v":1},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"const","v":0},{"t":"var","v":2},{"t":"var","v":3},{"t":"var","v":4},{"t":"var","v":5},{"t":"var","v":6},{"t":"var","v":7},{"t":"var","v":8},{"t":"var","v":9}]},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":2}}}},{"t":"pi_binding","row":"first","col":0,"pi_index":0},{"t":"pi_binding","row":"last","col":2,"pi_index":1}],"hash_sites":[],"ranges":[]}"#;

// --- Trace column layout (must match `MultiStepChainEmit.lean` §1). ---
const PREV: usize = 0;
const DERIVED: usize = 1;
const ACC: usize = 2;
const LANE_BASE: usize = 3;
const CHAIN_WIDTH: usize = 10;

// --- PI layout. ---
const INITIAL_PI: usize = 0;
const FINAL_PI: usize = 1;

/// An arity-2 `TID_P2` chip lookup absorbing `[prev, derived]`, binding out0 to `ACC` and lanes 1..7
/// to `LANE_BASE..LANE_BASE+7`. Built EXACTLY as Lean's `chipLookupTuple` (arity tag = ins.length =
/// 2, `CHIP_RATE` zero-padded inputs, then out0 :: 7 lanes) — the `hash_2_to_1` shape
/// (`poseidon2.rs:365`).
fn chip2_lookup(prev: usize, derived: usize, out_col: usize, lane_base: usize) -> VmConstraint2 {
    let ins = [prev, derived];
    let mut tuple: Vec<LeanExpr> = Vec::with_capacity(CHIP_TUPLE_LEN);
    tuple.push(LeanExpr::Const(2)); // arity tag (= ins.length in Lean's chipLookupTuple)
    for i in 0..CHIP_RATE {
        tuple.push(match ins.get(i) {
            Some(&c) => LeanExpr::Var(c),
            None => LeanExpr::Const(0),
        });
    }
    tuple.push(LeanExpr::Var(out_col)); // out0 = the accumulated digest
    for j in 0..(CHIP_OUT_LANES - 1) {
        tuple.push(LeanExpr::Var(lane_base + j));
    }
    assert_eq!(tuple.len(), CHIP_TUPLE_LEN);
    VmConstraint2::Lookup(LookupSpec {
        table: TID_P2,
        tuple,
    })
}

/// The independently-hand-built twin of the Lean `multiStepChainDesc`: the arity-2 per-step chip
/// absorb (`ACC = hash_2_to_1(PREV, DERIVED)`), the transition continuity window
/// (`nxt[PREV] − loc[ACC]`), and the two boundary pins (first `PREV == pi[0]`, last `ACC == pi[1]`).
fn hand_built_desc() -> EffectVmDescriptor2 {
    let continuity = VmConstraint2::WindowGate(WindowGateSpec {
        on_transition: true,
        body: WindowExpr::Add(
            Box::new(WindowExpr::Nxt(PREV)),
            Box::new(WindowExpr::Mul(
                Box::new(WindowExpr::Const(-1)),
                Box::new(WindowExpr::Loc(ACC)),
            )),
        ),
    });
    let init_pin = VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::First,
        col: PREV,
        pi_index: INITIAL_PI,
    });
    let final_pin = VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::Last,
        col: ACC,
        pi_index: FINAL_PI,
    });
    EffectVmDescriptor2 {
        name: "multi-step-accumulated-hash-chain::poseidon2-v1".to_string(),
        trace_width: CHAIN_WIDTH,
        public_input_count: 2,
        tables: vec![],
        constraints: vec![
            chip2_lookup(PREV, DERIVED, ACC, LANE_BASE),
            continuity,
            init_pin,
            final_pin,
        ],
        hash_sites: vec![],
        ranges: vec![],
    }
}

// ---------------------------------------------------------------------------
// Honest witness construction (a genuine K-step accumulated-hash chain).
// ---------------------------------------------------------------------------

/// Build one chain row: `PREV`, `DERIVED`, and the genuine `ACC = hash_2_to_1(PREV, DERIVED)`. The
/// chip LANE columns (`LANE_BASE..`) are left zero — the prover's `trace_with_chip_lanes` fills them
/// from the genuine permutation.
fn chain_row(prev: BabyBear, derived: BabyBear) -> Vec<BabyBear> {
    let mut row = vec![BabyBear::ZERO; CHAIN_WIDTH];
    row[PREV] = prev;
    row[DERIVED] = derived;
    row[ACC] = hash_2_to_1(prev, derived);
    row
}

/// A genuine `deriveds.len()`-step chain seeded at `prev0`. Returns `(trace, initial, final)` where
/// `initial = prev0` and `final = acc_last`. Every link honestly chains (`prevᵢ₊₁ = accᵢ`).
fn honest_chain(
    prev0: BabyBear,
    deriveds: &[BabyBear],
) -> (Vec<Vec<BabyBear>>, BabyBear, BabyBear) {
    let mut trace = Vec::with_capacity(deriveds.len());
    let mut prev = prev0;
    for &d in deriveds {
        let row = chain_row(prev, d);
        prev = row[ACC]; // next step's entering hash = this step's leaving hash
        trace.push(row);
    }
    let final_acc = trace.last().unwrap()[ACC];
    (trace, prev0, final_acc)
}

/// A chain whose link into step 1 is BROKEN: `PREV[1]` is set to `bogus_prev1` (≠ `ACC[0]`) instead
/// of chaining honestly, but every per-step `ACC = hash_2_to_1(PREV, DERIVED)` is recomputed
/// consistently downstream and both boundary pins still hold. The ONLY unsatisfied constraint is the
/// transition continuity window at row 0 → row 1.
fn broken_link_chain(
    prev0: BabyBear,
    deriveds: &[BabyBear],
    bogus_prev1: BabyBear,
) -> (Vec<Vec<BabyBear>>, BabyBear, BabyBear) {
    let mut trace = Vec::with_capacity(deriveds.len());
    let mut prev = prev0;
    for (i, &d) in deriveds.iter().enumerate() {
        if i == 1 {
            prev = bogus_prev1; // BREAK: entering hash ≠ previous step's ACC
        }
        let row = chain_row(prev, d);
        prev = row[ACC];
        trace.push(row);
    }
    let final_acc = trace.last().unwrap()[ACC];
    (trace, prev0, final_acc)
}

/// The honest fixture: four distinct per-step derived hashes over a seeded initial state root.
fn fixture() -> (BabyBear, [BabyBear; 4]) {
    let prev0 = BabyBear::new(1001);
    let deriveds = [
        BabyBear::new(2002),
        BabyBear::new(3003),
        BabyBear::new(4004),
        BabyBear::new(5005),
    ];
    (prev0, deriveds)
}

/// `true` iff this `(trace, pis)` is REJECTED end-to-end — proving refuses OR the produced proof
/// fails to VERIFY against `pis`. `false` iff it both proves AND verifies. (Prove-then-verify is the
/// faithful gate; `prove_vm_descriptor2` self-verifies only under `debug_assertions`, so the
/// consumer's `verify_vm_descriptor2` is the real check on the release path — the boundary
/// `pi_binding`s are checked against the public inputs there.)
fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }));
    match r {
        Err(_) => true,      // panicked anywhere → rejected
        Ok(Err(_)) => true,  // prove OR verify returned Err → rejected
        Ok(Ok(())) => false, // proved AND verified → ACCEPTED
    }
}

/// STEP 1 — the emitted descriptor decodes and equals the hand-built twin (Lean emit ≡ Rust
/// semantics), with exactly the Lean-pinned shape.
#[test]
fn multi_step_emit_decodes_to_hand_built() {
    let decoded = parse_vm_descriptor2(GOLDEN_JSON).expect("the Lean-emitted golden JSON decodes");
    let hand = hand_built_desc();
    assert_eq!(
        decoded, hand,
        "the Lean-emitted descriptor must equal the independently hand-built descriptor"
    );
    // shape pins
    assert_eq!(
        decoded.name,
        "multi-step-accumulated-hash-chain::poseidon2-v1"
    );
    assert_eq!(decoded.trace_width, CHAIN_WIDTH);
    assert_eq!(decoded.public_input_count, 2);
    assert!(
        decoded.tables.is_empty(),
        "chip table is Presence-detected, not declared"
    );
    assert_eq!(decoded.constraints.len(), 4);
    let chip_lookups = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
        .count();
    assert_eq!(chip_lookups, 1, "the per-step arity-2 hash_2_to_1 absorb");
    let windows = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
        .count();
    assert_eq!(windows, 1, "the transition chain-continuity window");
    let pins = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
        .count();
    assert_eq!(
        pins, 2,
        "the first-row initial pin + the last-row final pin"
    );
}

/// STEP 2 — the family-wide chip mapping: an arity-2 `TID_P2` absorb IS `hash_2_to_1`. Constructing
/// the honest chain relies on this correspondence; assert it directly (each input load-bearing).
#[test]
fn arity2_chip_lookup_is_hash_2_to_1() {
    let a = BabyBear::new(111);
    let b = BabyBear::new(222);
    let d = hash_2_to_1(a, b);
    // both inputs are load-bearing: perturb either and the digest changes.
    assert_ne!(hash_2_to_1(a + BabyBear::ONE, b), d, "left input dead?");
    assert_ne!(hash_2_to_1(a, b + BabyBear::ONE), d, "right input dead?");
}

/// STEP 3 — THE POSITIVE POLE: an honest 4-step chain proves through the emitted descriptor and the
/// proof re-verifies against the `[initial, final]` public inputs.
#[test]
fn honest_chain_proves_and_verifies() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (prev0, deriveds) = fixture();
    let (trace, initial, final_acc) = honest_chain(prev0, &deriveds);
    let pis = [initial, final_acc];
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the honest accumulated-hash chain must prove");
    verify_vm_descriptor2(&desc, &proof, &pis)
        .expect("the honest proof must re-verify against [initial, final]");
}

/// STEP 4a — MUTATION CANARY (MS1 chip absorb): a step's carried `DERIVED` is bumped off the digest
/// its `ACC` column already commits to — the arity-2 chip lookup names a `(prev, derived)` whose
/// genuine `hash_2_to_1` no chip row serves as `ACC` → UNSAT. The per-step hash binding is
/// load-bearing (a step cannot claim a `derived_hash` its accumulated digest was not computed from).
/// Continuity (`prev₂ == acc₁` unchanged) and both pins still hold, so ONLY MS1 bites.
#[test]
fn tampered_derived_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (prev0, deriveds) = fixture();
    let (trace, initial, final_acc) = honest_chain(prev0, &deriveds);
    let pis = [initial, final_acc];
    assert!(
        !rejects(&desc, &trace, &pis),
        "honest witness must be accepted — else the canary is vacuous"
    );
    let mut bad = trace.clone();
    bad[1][DERIVED] = bad[1][DERIVED] + BabyBear::ONE; // ACC[1] no longer = hash_2_to_1(PREV[1], DERIVED)
    assert!(
        rejects(&desc, &bad, &pis),
        "a derived_hash that does not produce the committed accumulated digest must be REJECTED (MS1)"
    );
}

/// STEP 4b — MUTATION CANARY (MS2 continuity window): a chain whose entering hash into step 1 is
/// forged (`PREV[1] ≠ ACC[0]`), with every per-step `ACC = hash_2_to_1(PREV, DERIVED)` recomputed
/// consistently and both boundary pins re-pinned — so the ONLY unsatisfied constraint is the
/// transition `window_gate` (`nxt[PREV] − loc[ACC]`) at row 0 → row 1. The cross-step chain is
/// load-bearing (a spliced sub-chain is refused).
#[test]
fn broken_chain_link_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (prev0, deriveds) = fixture();
    // sanity: the honest chain is ACCEPTED (non-vacuity of the negative).
    let (honest, hi, hf) = honest_chain(prev0, &deriveds);
    assert!(
        !rejects(&desc, &honest, &[hi, hf]),
        "honest chain must be accepted"
    );
    // the honest ACC[0] the forged PREV[1] must differ from.
    let acc0 = honest[0][ACC];
    let bogus_prev1 = acc0 + BabyBear::ONE;
    let (bad, bi, bf) = broken_link_chain(prev0, &deriveds, bogus_prev1);
    // the broken chain's own pins are self-consistent (so ONLY continuity is unsatisfied).
    assert_ne!(
        bad[1][PREV], acc0,
        "the link into step 1 is genuinely broken"
    );
    assert!(
        rejects(&desc, &bad, &[bi, bf]),
        "a broken chain link (prev₁ ≠ acc₀) must be REJECTED (MS2 continuity window)"
    );
}

/// STEP 4c — MUTATION CANARY (MS3a initial pin): the honest chain, but a FORGED initial-state-root
/// PI. The first-row `pi_binding` (`PREV == pi[INITIAL]`) is violated → UNSAT. The chain is anchored
/// to the claimed initial state.
#[test]
fn forged_initial_root_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (prev0, deriveds) = fixture();
    let (trace, initial, final_acc) = honest_chain(prev0, &deriveds);
    assert!(
        !rejects(&desc, &trace, &[initial, final_acc]),
        "honest witness must be accepted"
    );
    let forged_initial = initial + BabyBear::ONE;
    assert!(
        rejects(&desc, &trace, &[forged_initial, final_acc]),
        "a forged initial-state-root PI must be REJECTED (MS3a first-row pin)"
    );
}

/// STEP 4d — MUTATION CANARY (MS3b final pin): the honest chain, but a FORGED final-accumulated-hash
/// PI. The last-row `pi_binding` (`ACC == pi[FINAL]`) is violated → UNSAT. The published tail is
/// bound to the chain's genuine terminal digest.
#[test]
fn forged_final_hash_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (prev0, deriveds) = fixture();
    let (trace, initial, final_acc) = honest_chain(prev0, &deriveds);
    assert!(
        !rejects(&desc, &trace, &[initial, final_acc]),
        "honest witness must be accepted"
    );
    let forged_final = final_acc + BabyBear::ONE;
    assert!(
        rejects(&desc, &trace, &[initial, forged_final]),
        "a forged final-accumulated-hash PI must be REJECTED (MS3b last-row pin)"
    );
}
