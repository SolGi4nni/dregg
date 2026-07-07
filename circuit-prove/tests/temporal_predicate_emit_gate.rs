//! # The emit-from-Lean EQUALITY GATE — the TEMPORAL predicate family (GTE continuous predicate).
//!
//! The descriptor is AUTHORED in Lean (`metatheory/Dregg2/Circuit/Emit/TemporalPredicateEmit.lean`,
//! `temporalPredicateDesc`) and its wire string is byte-pinned there (`emitVmJson2` `#guard`). This
//! test embeds that EXACT string ([`GOLDEN_JSON`]) and:
//!
//!   1. DECODES it via [`parse_vm_descriptor2`] and asserts the decode equals an independently
//!      hand-built `EffectVmDescriptor2` (Lean emit ≡ Rust builder — a byte drift on either side
//!      breaks this OR the Lean `#guard`);
//!   2. proves an HONEST GTE run (all values ≥ threshold) through [`prove_vm_descriptor2`], asserts
//!      ACCEPT, and re-verifies the proof;
//!   3. the MUTATION CANARIES — each tampers the witness / a public input and asserts the
//!      prove-or-verify REFUSES (real UNSAT), rejected BY A CONSTRAINT:
//!        * a below-threshold value → the bit-decomposition RANGE GADGET (C3 recompose + C4 high
//!          bit) is UNSAT (the non-negativity tooth: a value that fails the predicate has no valid
//!          in-range `diff` witness);
//!        * a forged threshold PI → the row-0 THRESHOLD `PiBinding` is UNSAT (audit-#3 anti-forge);
//!        * a forged final-state-root PI → the last-row STATE_ROOT `PiBinding` is UNSAT (audit-#3);
//!        * a forged padded_len PI → the last-row ACCUMULATOR `PiBinding` is UNSAT (the
//!          cannot-fabricate-duration tooth);
//!        * a broken accumulator counter → the C5 gate + T1 `WindowGate` are UNSAT;
//!        * a mutated last-row threshold → the T3 THRESHOLD-constancy `WindowGate` is UNSAT.
//!
//! Each canary is NON-VACUOUS: the honest witness proves (step 2), and the tampered witness is a
//! genuinely different statement whose constraint the emitted descriptor forces.
//!
//! This descriptor is the faithful IR-v2 twin of the hand AIR
//! `circuit/src/temporal_predicate_dsl.rs` (`TemporalPredicateDsl`, the deployed GTE variant): the
//! range gadget is emitted as the SAME in-line bit gates the hand AIR writes (NOT a Range-table
//! lookup), the cross-row counters + threshold constancy are `WindowGate`s, and the four PI
//! bindings are exactly the audit-`ce1e2def #3` anti-forge surface — no more (the interior
//! state-root gap is preserved, not laundered).

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, VmConstraint2, WindowExpr, WindowGateSpec,
    parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

/// The BYTE-IDENTICAL wire string Lean's `emitVmJson2 temporalPredicateDesc` emits (pinned by the
/// `#guard` in `TemporalPredicateEmit.lean`). If Lean's emitter drifts, that `#guard` fails; if
/// this literal drifts, the `decoded == hand_built` assertion fails. Neither can silently diverge.
const GOLDEN_JSON: &str = r#"{"name":"dregg-temporal-predicate-gte::dsl-v1","ir":2,"trace_width":38,"public_input_count":4,"tables":[],"constraints":[{"t":"gate","body":{"t":"add","l":{"t":"var","v":2},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":0}},"r":{"t":"var","v":1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":3},"r":{"t":"add","l":{"t":"var","v":3},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":4},"r":{"t":"add","l":{"t":"var","v":4},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":5},"r":{"t":"add","l":{"t":"var","v":5},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":6},"r":{"t":"add","l":{"t":"var","v":6},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":7},"r":{"t":"add","l":{"t":"var","v":7},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":8},"r":{"t":"add","l":{"t":"var","v":8},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":9},"r":{"t":"add","l":{"t":"var","v":9},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":10},"r":{"t":"add","l":{"t":"var","v":10},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":11},"r":{"t":"add","l":{"t":"var","v":11},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":12},"r":{"t":"add","l":{"t":"var","v":12},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":13},"r":{"t":"add","l":{"t":"var","v":13},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":14},"r":{"t":"add","l":{"t":"var","v":14},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":15},"r":{"t":"add","l":{"t":"var","v":15},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":16},"r":{"t":"add","l":{"t":"var","v":16},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":17},"r":{"t":"add","l":{"t":"var","v":17},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":18},"r":{"t":"add","l":{"t":"var","v":18},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":19},"r":{"t":"add","l":{"t":"var","v":19},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":20},"r":{"t":"add","l":{"t":"var","v":20},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":21},"r":{"t":"add","l":{"t":"var","v":21},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":22},"r":{"t":"add","l":{"t":"var","v":22},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":23},"r":{"t":"add","l":{"t":"var","v":23},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":24},"r":{"t":"add","l":{"t":"var","v":24},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":25},"r":{"t":"add","l":{"t":"var","v":25},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":26},"r":{"t":"add","l":{"t":"var","v":26},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":27},"r":{"t":"add","l":{"t":"var","v":27},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":28},"r":{"t":"add","l":{"t":"var","v":28},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":29},"r":{"t":"add","l":{"t":"var","v":29},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":30},"r":{"t":"add","l":{"t":"var","v":30},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":31},"r":{"t":"add","l":{"t":"var","v":31},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":32},"r":{"t":"add","l":{"t":"var","v":32},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1},"r":{"t":"var","v":3}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":2},"r":{"t":"var","v":4}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":4},"r":{"t":"var","v":5}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":8},"r":{"t":"var","v":6}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":16},"r":{"t":"var","v":7}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":32},"r":{"t":"var","v":8}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":64},"r":{"t":"var","v":9}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":128},"r":{"t":"var","v":10}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":256},"r":{"t":"var","v":11}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":512},"r":{"t":"var","v":12}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1024},"r":{"t":"var","v":13}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":2048},"r":{"t":"var","v":14}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":4096},"r":{"t":"var","v":15}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":8192},"r":{"t":"var","v":16}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":16384},"r":{"t":"var","v":17}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":32768},"r":{"t":"var","v":18}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":65536},"r":{"t":"var","v":19}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":131072},"r":{"t":"var","v":20}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":262144},"r":{"t":"var","v":21}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":524288},"r":{"t":"var","v":22}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":1048576},"r":{"t":"var","v":23}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":2097152},"r":{"t":"var","v":24}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":4194304},"r":{"t":"var","v":25}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":8388608},"r":{"t":"var","v":26}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":16777216},"r":{"t":"var","v":27}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":33554432},"r":{"t":"var","v":28}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":67108864},"r":{"t":"var","v":29}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":134217728},"r":{"t":"var","v":30}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":268435456},"r":{"t":"var","v":31}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":536870912},"r":{"t":"var","v":32}},"r":{"t":"const","v":0}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":2}}}},{"t":"gate","body":{"t":"var","v":32}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":35},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":33}},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":36},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":34}},"r":{"t":"const","v":-1}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":33},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":35}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":34},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":36}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":1}}}},{"t":"boundary","row":"first","body":{"t":"add","l":{"t":"var","v":33},"r":{"t":"const","v":-1}}},{"t":"boundary","row":"first","body":{"t":"var","v":34}},{"t":"pi_binding","row":"last","col":33,"pi_index":0},{"t":"pi_binding","row":"first","col":1,"pi_index":1},{"t":"pi_binding","row":"first","col":37,"pi_index":2},{"t":"pi_binding","row":"last","col":37,"pi_index":3}],"hash_sites":[],"ranges":[]}"#;

// --- Trace column layout (must match `TemporalPredicateEmit.lean` §1). ---
const VALUE: usize = 0;
const THRESHOLD: usize = 1;
const DIFF: usize = 2;
const DIFF_BITS_START: usize = 3;
const NUM_DIFF_BITS: usize = 30;
const ACCUMULATOR: usize = 33;
const STEP_INDEX: usize = 34;
const ACC_PLUS_ONE: usize = 35;
const STEP_PLUS_ONE: usize = 36;
const STATE_ROOT: usize = 37;
const TRACE_WIDTH: usize = 38;

// --- Public-input layout. ---
const PI_PADDED_LEN: usize = 0;
const PI_THRESHOLD: usize = 1;
const PI_INITIAL_STATE_ROOT: usize = 2;
const PI_FINAL_STATE_ROOT: usize = 3;

// ─────────────────────────────────────────────────────────────────────────────
// Independent hand-built twin of the Lean descriptor (byte-identical structure).
// ─────────────────────────────────────────────────────────────────────────────

fn wadd(a: WindowExpr, b: WindowExpr) -> WindowExpr {
    WindowExpr::Add(Box::new(a), Box::new(b))
}
fn wmul(a: WindowExpr, b: WindowExpr) -> WindowExpr {
    WindowExpr::Mul(Box::new(a), Box::new(b))
}

/// The `Σ_{i<30} 2^i · bit_i` reconstruction sum — the SAME right-fold nesting the Lean
/// `recomposeSum` produces (outermost term `i = 0`, innermost terminator `Const 0`).
fn recompose_sum() -> LeanExpr {
    let mut sum = LeanExpr::Const(0);
    for i in (0..NUM_DIFF_BITS).rev() {
        let term = LeanExpr::mul(
            LeanExpr::Const(1i64 << i),
            LeanExpr::Var(DIFF_BITS_START + i),
        );
        sum = LeanExpr::add(term, sum);
    }
    sum
}

fn gate(body: LeanExpr) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::Gate(body))
}

/// The independently-hand-built twin of the Lean `temporalPredicateDesc`.
fn hand_built_desc() -> EffectVmDescriptor2 {
    let mut constraints: Vec<VmConstraint2> = Vec::new();

    // C1: diff − (value − threshold).
    constraints.push(gate(LeanExpr::add(
        LeanExpr::Var(DIFF),
        LeanExpr::add(
            LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(VALUE)),
            LeanExpr::Var(THRESHOLD),
        ),
    )));
    // C2[i]: bit · (bit − 1), i in 0..30.
    for i in 0..NUM_DIFF_BITS {
        let b = DIFF_BITS_START + i;
        constraints.push(gate(LeanExpr::mul(
            LeanExpr::Var(b),
            LeanExpr::add(LeanExpr::Var(b), LeanExpr::Const(-1)),
        )));
    }
    // C3: Σ 2^i·bit_i − diff.
    constraints.push(gate(LeanExpr::add(
        recompose_sum(),
        LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(DIFF)),
    )));
    // C4: high bit zero.
    constraints.push(gate(LeanExpr::Var(DIFF_BITS_START + NUM_DIFF_BITS - 1)));
    // C5: acc_plus_one − accumulator − 1.
    constraints.push(gate(LeanExpr::add(
        LeanExpr::Var(ACC_PLUS_ONE),
        LeanExpr::add(
            LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(ACCUMULATOR)),
            LeanExpr::Const(-1),
        ),
    )));
    // C6: step_plus_one − step_index − 1.
    constraints.push(gate(LeanExpr::add(
        LeanExpr::Var(STEP_PLUS_ONE),
        LeanExpr::add(
            LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(STEP_INDEX)),
            LeanExpr::Const(-1),
        ),
    )));

    // T1/T2/T3 window gates (on_transition = true).
    let t1 = wadd(
        WindowExpr::Nxt(ACCUMULATOR),
        wmul(WindowExpr::Const(-1), WindowExpr::Loc(ACC_PLUS_ONE)),
    );
    let t2 = wadd(
        WindowExpr::Nxt(STEP_INDEX),
        wmul(WindowExpr::Const(-1), WindowExpr::Loc(STEP_PLUS_ONE)),
    );
    let t3 = wadd(
        WindowExpr::Nxt(THRESHOLD),
        wmul(WindowExpr::Const(-1), WindowExpr::Loc(THRESHOLD)),
    );
    for body in [t1, t2, t3] {
        constraints.push(VmConstraint2::WindowGate(WindowGateSpec {
            body,
            on_transition: true,
        }));
    }

    // Boundaries + PI bindings.
    constraints.push(VmConstraint2::Base(VmConstraint::Boundary {
        row: VmRow::First,
        body: LeanExpr::add(LeanExpr::Var(ACCUMULATOR), LeanExpr::Const(-1)),
    }));
    constraints.push(VmConstraint2::Base(VmConstraint::Boundary {
        row: VmRow::First,
        body: LeanExpr::Var(STEP_INDEX),
    }));
    constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::Last,
        col: ACCUMULATOR,
        pi_index: PI_PADDED_LEN,
    }));
    constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::First,
        col: THRESHOLD,
        pi_index: PI_THRESHOLD,
    }));
    constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::First,
        col: STATE_ROOT,
        pi_index: PI_INITIAL_STATE_ROOT,
    }));
    constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::Last,
        col: STATE_ROOT,
        pi_index: PI_FINAL_STATE_ROOT,
    }));

    EffectVmDescriptor2 {
        name: "dregg-temporal-predicate-gte::dsl-v1".to_string(),
        trace_width: TRACE_WIDTH,
        public_input_count: 4,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Witness / trace construction (mirrors `generate_dsl_trace`, fixed GTE fixture).
// ─────────────────────────────────────────────────────────────────────────────

/// Fill one trace row for a GTE step: `value ≥ threshold`, `diff = value − threshold`, honest bits.
fn make_row(value: u32, threshold: u32, step: usize, state_root: BabyBear) -> Vec<BabyBear> {
    let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];
    row[VALUE] = BabyBear::new(value);
    row[THRESHOLD] = BabyBear::new(threshold);
    let diff = BabyBear::new(value) - BabyBear::new(threshold);
    row[DIFF] = diff;
    let diff_u = diff.as_u32();
    for i in 0..NUM_DIFF_BITS {
        row[DIFF_BITS_START + i] = BabyBear::new((diff_u >> i) & 1);
    }
    let acc = (step + 1) as u32;
    row[ACCUMULATOR] = BabyBear::new(acc);
    row[STEP_INDEX] = BabyBear::new(step as u32);
    row[ACC_PLUS_ONE] = BabyBear::new(acc + 1);
    row[STEP_PLUS_ONE] = BabyBear::new(step as u32 + 1);
    row[STATE_ROOT] = state_root;
    row
}

/// The honest fixture: threshold 50, three real GTE steps (value 100), padded to a 4-row trace.
/// Returns `(trace, public_inputs)`.
fn honest_trace() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let threshold = 50u32;
    let values = [100u32, 100, 100];
    let state_roots = [
        BabyBear::new(1000),
        BabyBear::new(1001),
        BabyBear::new(1002),
    ];
    let num_steps = 3usize;
    let padded = 4usize; // next_power_of_two(3).max(2)
    let final_root = state_roots[num_steps - 1];

    let mut trace = Vec::with_capacity(padded);
    for step in 0..padded {
        let value = if step < num_steps {
            values[step]
        } else {
            values[num_steps - 1]
        };
        let sr = if step < num_steps {
            state_roots[step]
        } else {
            final_root
        };
        trace.push(make_row(value, threshold, step, sr));
    }
    let pis = vec![
        BabyBear::new(padded as u32),
        BabyBear::new(threshold),
        state_roots[0],
        final_root,
    ];
    (trace, pis)
}

/// `true` iff `(trace, pis)` is REJECTED end-to-end — proving refuses OR the proof fails to verify.
/// `false` iff it both proves AND verifies. Prove-THEN-verify is the faithful gate (the first-row /
/// last-row `PiBinding`s and boundaries are checked by `verify_vm_descriptor2` against the PIs).
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

// ─────────────────────────────────────────────────────────────────────────────
// STEP 1 — the emitted descriptor decodes and equals the hand-built twin.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn temporal_predicate_emit_decodes_to_hand_built() {
    let decoded = parse_vm_descriptor2(GOLDEN_JSON).expect("the Lean-emitted golden JSON decodes");
    let hand = hand_built_desc();
    assert_eq!(
        decoded, hand,
        "the Lean-emitted descriptor must equal the independently hand-built descriptor"
    );
    // shape pins
    assert_eq!(decoded.trace_width, TRACE_WIDTH);
    assert_eq!(decoded.public_input_count, 4);
    assert_eq!(
        decoded.constraints.len(),
        44,
        "1 (C1) + 30 (C2) + 4 (C3..C6) + 3 (T1..T3) + 6 (boundaries/pins)"
    );
    let windows = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
        .count();
    assert_eq!(windows, 3, "the three cross-row window gates (T1/T2/T3)");
    let pins = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
        .count();
    assert_eq!(pins, 4, "the four audit-#3 anti-forge PI bindings");
}

// ─────────────────────────────────────────────────────────────────────────────
// STEP 2 — THE POSITIVE POLE: an honest GTE run proves and re-verifies.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn honest_temporal_run_proves_and_verifies() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis) = honest_trace();
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the honest GTE run must prove (all values ≥ threshold, counters + bindings hold)");
    verify_vm_descriptor2(&desc, &proof, &pis)
        .expect("the honest proof must re-verify against the public inputs");
}

// ─────────────────────────────────────────────────────────────────────────────
// STEP 3 — MUTATION CANARIES (each rejected BY A CONSTRAINT; non-vacuous vs the honest anchor).
// ─────────────────────────────────────────────────────────────────────────────

/// 3a — the RANGE GADGET tooth: a below-threshold value at a non-last row. `diff = value −
/// threshold` wraps to a large field element; its 30 low bits cannot recompose it under a zero
/// high bit, so C3 (recompose) and C4 (high bit) are UNSAT. THE non-negativity / predicate tooth.
#[test]
fn below_threshold_value_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis) = honest_trace();
    // sanity: the honest trace is ACCEPTED (non-vacuity of the negative below).
    assert!(
        !rejects(&desc, &trace, &pis),
        "honest witness must be accepted — else every canary is vacuous"
    );
    // Tamper row 1 (a transition row, so per-row gates fire) to value 30 < threshold 50.
    let mut bad = trace.clone();
    let threshold = 50u32;
    bad[1] = make_row(30, threshold, 1, BabyBear::new(1001));
    // C1 still holds (diff IS value − threshold) and C2 still holds (bits binary), but the range
    // gadget C3/C4 cannot witness the wrapped negative diff.
    assert!(
        rejects(&desc, &bad, &pis),
        "a below-threshold value (out-of-range diff) must be REJECTED by the bit-recompose range gadget"
    );
}

/// 3b — the audit-#3 threshold anti-forge weld: a forged threshold PI. The row-0 THRESHOLD
/// `PiBinding` (`local[THRESHOLD] == pi[1]`) is UNSAT.
#[test]
fn forged_threshold_pi_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, mut pis) = honest_trace();
    assert!(!rejects(&desc, &trace, &pis), "honest anchor");
    pis[PI_THRESHOLD] = BabyBear::new(51); // claim a different threshold than the trace carries
    assert!(
        rejects(&desc, &trace, &pis),
        "a forged threshold PI must be REJECTED by the row-0 THRESHOLD PiBinding (audit-#3)"
    );
}

/// 3c — the audit-#3 state-root anti-forge weld: a forged final-state-root PI. The last-row
/// STATE_ROOT `PiBinding` (`local[STATE_ROOT] == pi[3]`) is UNSAT.
#[test]
fn forged_final_state_root_pi_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, mut pis) = honest_trace();
    assert!(!rejects(&desc, &trace, &pis), "honest anchor");
    pis[PI_FINAL_STATE_ROOT] = BabyBear::new(99999);
    assert!(
        rejects(&desc, &trace, &pis),
        "a forged final-state-root PI must be REJECTED by the last-row STATE_ROOT PiBinding (audit-#3)"
    );
}

/// 3d — the cannot-fabricate-duration tooth: a forged padded_len PI. The last-row ACCUMULATOR
/// `PiBinding` (`local[ACCUMULATOR] == pi[0]`) is UNSAT (the real trace's last accumulator is 4).
#[test]
fn forged_padded_len_pi_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, mut pis) = honest_trace();
    assert!(!rejects(&desc, &trace, &pis), "honest anchor");
    pis[PI_PADDED_LEN] = BabyBear::new(8); // claim 8 steps over a 4-row trace
    assert!(
        rejects(&desc, &trace, &pis),
        "a forged padded_len PI must be REJECTED by the last-row ACCUMULATOR PiBinding"
    );
}

/// 3e — the step-accumulator continuity: a broken counter at a middle row. The C5 gate
/// (`acc_plus_one − accumulator − 1`) AND the T1 `WindowGate` (`next.acc = local.acc_plus_one`)
/// are UNSAT.
#[test]
fn broken_accumulator_counter_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis) = honest_trace();
    assert!(!rejects(&desc, &trace, &pis), "honest anchor");
    let mut bad = trace.clone();
    bad[2][ACCUMULATOR] = BabyBear::new(9); // gap the counter chain at row 2 (a transition row)
    assert!(
        rejects(&desc, &bad, &pis),
        "a gapped accumulator must be REJECTED by the C5 gate + T1 window gate"
    );
}

/// 3f — the T3 THRESHOLD-constancy anti-forge weld (isolated): mutate the LAST row's threshold.
/// Per-row gates do not fire on the last row, but the T3 `WindowGate` on the `row2 → row3`
/// transition (`next.threshold − local.threshold`) is UNSAT.
#[test]
fn mutated_last_row_threshold_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis) = honest_trace();
    assert!(!rejects(&desc, &trace, &pis), "honest anchor");
    let mut bad = trace.clone();
    let last = bad.len() - 1;
    bad[last][THRESHOLD] = BabyBear::new(77); // break constancy across the last transition
    assert!(
        rejects(&desc, &bad, &pis),
        "a non-constant threshold must be REJECTED by the T3 constancy window gate (audit-#3)"
    );
}
