//! # The emit-from-Lean EQUALITY GATE — GARBLED-CIRCUIT EVALUATION (the 56-column DSL AIR).
//!
//! The descriptor is AUTHORED in Lean (`metatheory/Dregg2/Circuit/Emit/GarbledEvalEmit.lean`,
//! `garbledEvalDesc`) and its wire string is byte-pinned there (`emitVmJson2` `#guard`). It is the
//! emit-from-Lean twin of the hand-authored production garbled-evaluation DSL descriptor
//! (`circuit/src/dsl/garbled.rs::garbled_extended_descriptor`, which supersedes the deprecated
//! `circuit/src/garbled_air.rs::GarbledEvaluationAir`). This test embeds that EXACT string
//! ([`GOLDEN_JSON`]) and:
//!
//!   1. DECODES it via [`parse_vm_descriptor2`] and asserts the decode equals an independently
//!      hand-built `EffectVmDescriptor2` (Lean emit ≡ Rust builder — a byte drift on either side
//!      breaks this OR the Lean `#guard`);
//!   2. proves an HONEST evaluation witness (two chained garbled gates + two padding rows, the
//!      56-column trace) through [`prove_vm_descriptor2`], asserts ACCEPT, and re-verifies;
//!   3. the MUTATION CANARIES — each tampers the witness so exactly one hand-AIR constraint family
//!      bites, and asserts the prove-or-verify REFUSES (real UNSAT):
//!        (a) a forged commitment PI              → the first-row `pi_binding` (C1),
//!        (b) a forged garbled table ciphertext   → the DECRYPTION `gate` (C9, `output = table - hash`),
//!        (c) a non-boolean gate-type selector    → the `Binary` `gate` (C17),
//!        (d) two gate types set at once          → the EXCLUSIVITY `gate` (C23),
//!        (e) a broken output→left wire chain     → the `window_gate` (C24, cross-row chaining),
//!        (f) a nonzero first-row gate_index_delta → the `boundary` (`BoundaryDef::Fixed`).
//!
//! The canaries are NON-VACUOUS by construction: each first asserts the honest witness is ACCEPTED,
//! then asserts the tampered witness is REJECTED.
//!
//! ## The NAMED, executor-verified carrier (honest scope — the DECO-leaf posture)
//!
//! Faithful to the hand artifact, this descriptor does NOT constrain the Poseidon2 garbling hash:
//! `hash_out(i)` are FREE witness columns, and `hash_out == Poseidon2(left||right||gate_index)` /
//! `circuit_commitment == Poseidon2(tables)` / `output_label_hash == Poseidon2(output_label)` are
//! computed in Rust witness-gen (`circuit/src/garbled.rs`), NOT in-circuit. The AIR proves the
//! DECRYPTION algebra `output = table_entry - hash_out` over those digests; the garbling-hash
//! binding is the named executor-verified carrier (the Yao 2PC correctness/privacy floor is the
//! semantic twin in `metatheory/Dregg2/Crypto/GarbledJoint.lean`).
//!
//! ## The VERIFIER-WRAPPER tooth (named, not dropped)
//!
//! The DSL binds only the FIRST 4 felts of each 8-felt `WideHash` in-circuit (`public_input_count =
//! 8 = 4+4`). The FULL 8-felt (~124-bit) match is the verifier-side struct equality in
//! `circuit/src/dsl/garbled.rs::verify_garbled_evaluation_dsl` (`proof.circuit_commitment !=
//! *expected` → reject). It is off-descriptor by design; it is named here rather than emitted.

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, VmConstraint2, WindowExpr, WindowGateSpec,
    parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

/// The BYTE-IDENTICAL wire string Lean's `emitVmJson2 garbledEvalDesc` emits (pinned by the
/// `#guard` in `GarbledEvalEmit.lean`). If Lean drifts, that `#guard` fails; if this literal drifts,
/// the `decoded == hand_built` assertion fails. Neither can silently diverge.
const GOLDEN_JSON: &str = r#"{"name":"dregg-garbled-evaluation-extended-dsl-v1","ir":2,"trace_width":56,"public_input_count":8,"tables":[],"constraints":[{"t":"pi_binding","row":"first","col":41,"pi_index":0},{"t":"pi_binding","row":"first","col":42,"pi_index":1},{"t":"pi_binding","row":"first","col":43,"pi_index":2},{"t":"pi_binding","row":"first","col":44,"pi_index":3},{"t":"pi_binding","row":"first","col":45,"pi_index":4},{"t":"pi_binding","row":"first","col":46,"pi_index":5},{"t":"pi_binding","row":"first","col":47,"pi_index":6},{"t":"pi_binding","row":"first","col":48,"pi_index":7},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":55}}},"r":{"t":"add","l":{"t":"var","v":33},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":25}},"r":{"t":"var","v":17}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":55}}},"r":{"t":"add","l":{"t":"var","v":34},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":26}},"r":{"t":"var","v":18}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":55}}},"r":{"t":"add","l":{"t":"var","v":35},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":27}},"r":{"t":"var","v":19}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":55}}},"r":{"t":"add","l":{"t":"var","v":36},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":28}},"r":{"t":"var","v":20}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":55}}},"r":{"t":"add","l":{"t":"var","v":37},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":29}},"r":{"t":"var","v":21}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":55}}},"r":{"t":"add","l":{"t":"var","v":38},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":30}},"r":{"t":"var","v":22}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":55}}},"r":{"t":"add","l":{"t":"var","v":39},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":31}},"r":{"t":"var","v":23}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":55}}},"r":{"t":"add","l":{"t":"var","v":40},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":32}},"r":{"t":"var","v":24}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":49},"r":{"t":"add","l":{"t":"var","v":49},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":50},"r":{"t":"add","l":{"t":"var","v":50},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":51},"r":{"t":"add","l":{"t":"var","v":51},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":52},"r":{"t":"add","l":{"t":"var","v":52},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":53},"r":{"t":"add","l":{"t":"var","v":53},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":55},"r":{"t":"add","l":{"t":"var","v":55},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"mul","l":{"t":"add","l":{"t":"const","v":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":55}}},"r":{"t":"add","l":{"t":"var","v":49},"r":{"t":"add","l":{"t":"var","v":50},"r":{"t":"add","l":{"t":"var","v":51},"r":{"t":"add","l":{"t":"var","v":52},"r":{"t":"const","v":-1}}}}}}},{"t":"window_gate","on_transition":true,"body":{"t":"mul","l":{"t":"loc","c":53},"r":{"t":"add","l":{"t":"nxt","c":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":33}}}}},{"t":"window_gate","on_transition":true,"body":{"t":"mul","l":{"t":"loc","c":53},"r":{"t":"add","l":{"t":"nxt","c":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":34}}}}},{"t":"window_gate","on_transition":true,"body":{"t":"mul","l":{"t":"loc","c":53},"r":{"t":"add","l":{"t":"nxt","c":2},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":35}}}}},{"t":"window_gate","on_transition":true,"body":{"t":"mul","l":{"t":"loc","c":53},"r":{"t":"add","l":{"t":"nxt","c":3},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":36}}}}},{"t":"window_gate","on_transition":true,"body":{"t":"mul","l":{"t":"loc","c":53},"r":{"t":"add","l":{"t":"nxt","c":4},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":37}}}}},{"t":"window_gate","on_transition":true,"body":{"t":"mul","l":{"t":"loc","c":53},"r":{"t":"add","l":{"t":"nxt","c":5},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":38}}}}},{"t":"window_gate","on_transition":true,"body":{"t":"mul","l":{"t":"loc","c":53},"r":{"t":"add","l":{"t":"nxt","c":6},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":39}}}}},{"t":"window_gate","on_transition":true,"body":{"t":"mul","l":{"t":"loc","c":53},"r":{"t":"add","l":{"t":"nxt","c":7},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":40}}}}},{"t":"boundary","row":"first","body":{"t":"var","v":54}}],"hash_sites":[],"ranges":[]}"#;

// --- Trace column layout (must match `GarbledEvalEmit.lean` §1 / `garbled_air.rs::col`). ---
fn left(i: usize) -> usize {
    i
} // 0..7
fn right(i: usize) -> usize {
    8 + i
} // 8..15
#[allow(dead_code)]
const GATE_INDEX: usize = 16;
fn hash_out(i: usize) -> usize {
    17 + i
} // 17..24
fn table_entry(i: usize) -> usize {
    25 + i
} // 25..32
fn output(i: usize) -> usize {
    33 + i
} // 33..40
const CIRCUIT_COMMITMENT: usize = 41; // 41..44
const OUTPUT_LABEL_HASH: usize = 45; // 45..48
const IS_AND: usize = 49;
const IS_OR: usize = 50;
const IS_XOR: usize = 51;
const IS_NOT: usize = 52;
const CHAIN_FLAG: usize = 53;
const GATE_INDEX_DELTA: usize = 54;
const IS_PADDING: usize = 55;
const GARBLED_WIDTH: usize = 56;
const PI_COUNT: usize = 8;

// ---------------------------------------------------------------------------
// The independently hand-built twin of the Lean descriptor (mirrors the Lean
// constraint builders 1:1, in the same order `garbledEvalDesc` assembles them).
// ---------------------------------------------------------------------------

/// `(1 - is_padding)` — the `InvertedGated` selector factor.
fn not_padding() -> LeanExpr {
    LeanExpr::add(
        LeanExpr::Const(1),
        LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(IS_PADDING)),
    )
}

/// Decryption body lane `i`: `(1 - is_padding) * (output(i) - table_entry(i) + hash_out(i))`.
fn dec_gate(i: usize) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::Gate(LeanExpr::mul(
        not_padding(),
        LeanExpr::add(
            LeanExpr::Var(output(i)),
            LeanExpr::add(
                LeanExpr::mul(LeanExpr::Const(-1), LeanExpr::Var(table_entry(i))),
                LeanExpr::Var(hash_out(i)),
            ),
        ),
    )))
}

/// `Binary` gate for column `c`: `c * (c - 1)`.
fn bin_gate(c: usize) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::Gate(LeanExpr::mul(
        LeanExpr::Var(c),
        LeanExpr::add(LeanExpr::Var(c), LeanExpr::Const(-1)),
    )))
}

/// Exclusivity: `(1 - is_padding) * (is_and + is_or + is_xor + is_not - 1)`.
fn exclusivity_gate() -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::Gate(LeanExpr::mul(
        not_padding(),
        LeanExpr::add(
            LeanExpr::Var(IS_AND),
            LeanExpr::add(
                LeanExpr::Var(IS_OR),
                LeanExpr::add(
                    LeanExpr::Var(IS_XOR),
                    LeanExpr::add(LeanExpr::Var(IS_NOT), LeanExpr::Const(-1)),
                ),
            ),
        ),
    )))
}

/// Wire-chaining window gate lane `i`: `chain_flag * (next.left(i) - output(i))`, on the transition.
fn chain_gate(i: usize) -> VmConstraint2 {
    VmConstraint2::WindowGate(WindowGateSpec {
        on_transition: true,
        body: WindowExpr::Mul(
            Box::new(WindowExpr::Loc(CHAIN_FLAG)),
            Box::new(WindowExpr::Add(
                Box::new(WindowExpr::Nxt(left(i))),
                Box::new(WindowExpr::Mul(
                    Box::new(WindowExpr::Const(-1)),
                    Box::new(WindowExpr::Loc(output(i))),
                )),
            )),
        ),
    })
}

fn pi_bind(col: usize, pi_index: usize) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::First,
        col,
        pi_index,
    })
}

fn hand_built_desc() -> EffectVmDescriptor2 {
    let mut constraints = Vec::new();
    // C1-C4: circuit_commitment[0..4] first-row PI pins.
    for i in 0..4 {
        constraints.push(pi_bind(CIRCUIT_COMMITMENT + i, i));
    }
    // C5-C8: output_label_hash[0..4] first-row PI pins.
    for i in 0..4 {
        constraints.push(pi_bind(OUTPUT_LABEL_HASH + i, 4 + i));
    }
    // C9-C16: decryption correctness (gated on 1 - is_padding).
    for i in 0..8 {
        constraints.push(dec_gate(i));
    }
    // C17-C22: the six boolean selectors.
    constraints.push(bin_gate(IS_AND));
    constraints.push(bin_gate(IS_OR));
    constraints.push(bin_gate(IS_XOR));
    constraints.push(bin_gate(IS_NOT));
    constraints.push(bin_gate(CHAIN_FLAG));
    constraints.push(bin_gate(IS_PADDING));
    // C23: gate-type exclusivity.
    constraints.push(exclusivity_gate());
    // C24-C31: wire chaining (the two-row window gates).
    for i in 0..8 {
        constraints.push(chain_gate(i));
    }
    // Boundary: first-row gate_index_delta == 0.
    constraints.push(VmConstraint2::Base(VmConstraint::Boundary {
        row: VmRow::First,
        body: LeanExpr::Var(GATE_INDEX_DELTA),
    }));

    EffectVmDescriptor2 {
        name: "dregg-garbled-evaluation-extended-dsl-v1".to_string(),
        trace_width: GARBLED_WIDTH,
        public_input_count: PI_COUNT,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    }
}

// ---------------------------------------------------------------------------
// Honest witness construction (the 56-column decoupled trace).
// ---------------------------------------------------------------------------

/// The fixed 8-felt public input: `circuit_commitment[0..4]` then `output_label_hash[0..4]`.
fn pis() -> Vec<BabyBear> {
    (0..PI_COUNT)
        .map(|j| BabyBear::new(10 + j as u32))
        .collect()
}

/// A REAL garbled-gate row. The decryption columns satisfy `output = table_entry - hash_out`
/// (`table_entry = output + hash_out`); the commitment / output-label blocks carry the public
/// input; `left(i)` may be seeded to a predecessor's output (the wire chain). `hash_out` is a free
/// witness (the executor-verified Poseidon2 carrier).
#[allow(clippy::too_many_arguments)]
fn real_row(
    left_seed: &[u32; 8],
    right_base: u32,
    hash_base: u32,
    output_base: u32,
    is_and: u32,
    chain: u32,
    delta: u32,
) -> Vec<BabyBear> {
    let pi = pis();
    let mut r = vec![BabyBear::ZERO; GARBLED_WIDTH];
    for i in 0..8 {
        r[left(i)] = BabyBear::new(left_seed[i]);
        r[right(i)] = BabyBear::new(right_base + i as u32);
        let h = hash_base + i as u32;
        let o = output_base + i as u32;
        r[hash_out(i)] = BabyBear::new(h);
        r[output(i)] = BabyBear::new(o);
        r[table_entry(i)] = BabyBear::new(o + h); // output = table - hash
    }
    for j in 0..4 {
        r[CIRCUIT_COMMITMENT + j] = pi[j];
        r[OUTPUT_LABEL_HASH + j] = pi[4 + j];
    }
    r[IS_AND] = BabyBear::new(is_and);
    r[CHAIN_FLAG] = BabyBear::new(chain);
    r[GATE_INDEX_DELTA] = BabyBear::new(delta);
    r[IS_PADDING] = BabyBear::ZERO;
    r
}

/// A PADDING row: `is_padding = 1` (relaxes the gated decryption/exclusivity), all selectors and the
/// chain flag zero (the `Binary` gates hold), commitment/output-label mirrored for faithfulness.
fn padding_row() -> Vec<BabyBear> {
    let pi = pis();
    let mut r = vec![BabyBear::ZERO; GARBLED_WIDTH];
    for j in 0..4 {
        r[CIRCUIT_COMMITMENT + j] = pi[j];
        r[OUTPUT_LABEL_HASH + j] = pi[4 + j];
    }
    r[IS_PADDING] = BabyBear::ONE;
    r
}

/// The honest bundle: gate 0 (chains to gate 1) → gate 1 → two padding rows (height 4). The
/// wire chain is genuine: `row1.left(i) == row0.output(i)`.
fn honest_trace() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    // row 0 output = 400+i, chains to row 1's left.
    let row0 = real_row(
        &[100, 101, 102, 103, 104, 105, 106, 107],
        200,
        300,
        400,
        1,
        1,
        0,
    );
    let row0_out: [u32; 8] = std::array::from_fn(|i| 400 + i as u32);
    // row 1: left = row0's output (the chain), does not chain further (chain_flag = 0).
    let row1 = real_row(&row0_out, 250, 350, 500, 1, 0, 1);
    let trace = vec![row0, row1, padding_row(), padding_row()];
    (trace, pis())
}

/// `true` iff this `(trace, pis)` is REJECTED end-to-end — proving refuses OR the produced proof
/// fails to VERIFY against `pis`. `false` iff it both proves AND verifies. Prove-then-verify is the
/// faithful gate: `prove_vm_descriptor2` self-verifies only under `debug_assertions`, so the
/// consumer's `verify_vm_descriptor2` is the real check on the `--release` path.
fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], p: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, p, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, p)
    }));
    match r {
        Err(_) => true,
        Ok(Err(_)) => true,
        Ok(Ok(())) => false,
    }
}

/// STEP 1 — the emitted descriptor decodes and equals the hand-built twin (Lean emit ≡ Rust
/// semantics), with the Lean-pinned shape (width 56, PI 8, 32 constraints, 8 window gates, no tables).
#[test]
fn garbled_eval_emit_decodes_to_hand_built() {
    let decoded = parse_vm_descriptor2(GOLDEN_JSON).expect("the Lean-emitted golden JSON decodes");
    let hand = hand_built_desc();
    assert_eq!(
        decoded, hand,
        "the Lean-emitted descriptor must equal the independently hand-built descriptor"
    );
    assert_eq!(decoded.name, "dregg-garbled-evaluation-extended-dsl-v1");
    assert_eq!(decoded.trace_width, GARBLED_WIDTH);
    assert_eq!(decoded.public_input_count, PI_COUNT);
    assert!(decoded.tables.is_empty(), "pure row-window AIR: no tables");
    assert_eq!(
        decoded.constraints.len(),
        32,
        "the Lean #guard pins 32 constraints"
    );
    let window_gates = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::WindowGate(_)))
        .count();
    assert_eq!(window_gates, 8, "the eight wire-chaining window gates");
    let pins = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
        .count();
    assert_eq!(
        pins, 8,
        "the 4 commitment + 4 output-label first-row PI pins"
    );
}

/// STEP 2 — THE POSITIVE POLE: an honest two-gate evaluation proves through the emitted descriptor
/// and re-verifies against the 8-felt public input.
#[test]
fn honest_garbled_eval_proves_and_verifies() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, p) = honest_trace();
    let proof = prove_vm_descriptor2(&desc, &trace, &p, &MemBoundaryWitness::default(), &[])
        .expect("the honest garbled-evaluation witness must prove");
    verify_vm_descriptor2(&desc, &proof, &p).expect("the honest proof must re-verify");
}

/// STEP 3a — MUTATION CANARY (C1 PI binding): honest trace, a FORGED commitment PI. The first-row
/// `pi_binding` (col 41 == pi[0]) is violated → UNSAT.
#[test]
fn forged_commitment_pi_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, p) = honest_trace();
    assert!(
        !rejects(&desc, &trace, &p),
        "honest witness must be accepted — else the canary is vacuous"
    );
    let mut forged = p.clone();
    forged[0] = forged[0] + BabyBear::ONE;
    assert!(
        rejects(&desc, &trace, &forged),
        "a forged commitment PI must be REJECTED (the C1 first-row pi_binding)"
    );
}

/// STEP 3b — MUTATION CANARY (C9 decryption): the row-0 garbled table ciphertext `table_entry(0)` is
/// bumped off its `output = table - hash` relation → the decryption `gate` is nonzero → UNSAT. The
/// decryption-correctness tooth (`GarbledEvalEmit.decryption_body_zero_iff`).
#[test]
fn forged_table_entry_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, p) = honest_trace();
    assert!(
        !rejects(&desc, &trace, &p),
        "honest witness must be accepted"
    );
    let mut bad = trace.clone();
    bad[0][table_entry(0)] = bad[0][table_entry(0)] + BabyBear::ONE;
    assert!(
        rejects(&desc, &bad, &p),
        "a forged garbled ciphertext must be REJECTED (decryption correctness)"
    );
}

/// STEP 3c — MUTATION CANARY (C17 booleanity): the row-0 gate-type selector `is_and` is set to 2 —
/// the `Binary` gate `is_and·(is_and-1) = 2` is nonzero → UNSAT. A non-boolean selector is refused.
#[test]
fn non_boolean_selector_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, p) = honest_trace();
    assert!(
        !rejects(&desc, &trace, &p),
        "honest witness must be accepted"
    );
    let mut bad = trace.clone();
    bad[0][IS_AND] = BabyBear::new(2);
    assert!(
        rejects(&desc, &bad, &p),
        "a non-boolean gate-type selector must be REJECTED (the Binary gate)"
    );
}

/// STEP 3d — MUTATION CANARY (C23 exclusivity): row 0 sets BOTH `is_and` and `is_or` to 1 (each
/// individually boolean, so the `Binary` gates still hold), but the exclusivity gate
/// `(1-is_padding)·(is_and+is_or+is_xor+is_not-1) = 1` is nonzero → UNSAT. Exactly one gate type.
#[test]
fn ambiguous_gate_type_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, p) = honest_trace();
    assert!(
        !rejects(&desc, &trace, &p),
        "honest witness must be accepted"
    );
    let mut bad = trace.clone();
    bad[0][IS_OR] = BabyBear::ONE; // is_and already 1; two gate types now set
    assert!(
        rejects(&desc, &bad, &p),
        "two gate types set at once must be REJECTED (gate-type exclusivity)"
    );
}

/// STEP 3e — MUTATION CANARY (C24 wire chaining): row 1's left label `left(0)` is bumped off row 0's
/// output `output(0)`, while row 0's `chain_flag = 1` — the two-row `window_gate`
/// `chain_flag·(next.left(0) - output(0))` no longer vanishes on the row-0 transition → UNSAT. The
/// cross-row wire chaining genuinely gates.
#[test]
fn broken_wire_chaining_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, p) = honest_trace();
    assert!(
        !rejects(&desc, &trace, &p),
        "honest witness must be accepted"
    );
    let mut bad = trace.clone();
    bad[1][left(0)] = bad[1][left(0)] + BabyBear::ONE; // break the output→left chain
    assert!(
        rejects(&desc, &bad, &p),
        "a broken output→left wire chain must be REJECTED (the window gate)"
    );
}

/// STEP 3f — MUTATION CANARY (boundary): the first row's `gate_index_delta` is set nonzero → the
/// first-row `boundary` (`var 54 == 0`, `BoundaryDef::Fixed`) is violated → UNSAT.
#[test]
fn forged_gate_index_delta_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, p) = honest_trace();
    assert!(
        !rejects(&desc, &trace, &p),
        "honest witness must be accepted"
    );
    let mut bad = trace.clone();
    bad[0][GATE_INDEX_DELTA] = BabyBear::new(5);
    assert!(
        rejects(&desc, &bad, &p),
        "a nonzero first-row gate_index_delta must be REJECTED (the boundary)"
    );
}
