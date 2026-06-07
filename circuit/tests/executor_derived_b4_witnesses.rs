//! # B4 amplify: EXECUTOR-DERIVED witness `execute → prove → verify → anti-ghost`.
//!
//! For each effect in batch B4 (mint / noteCreate / noteSpend / pipelinedSend /
//! queueAllocate / queueAtomicTx / queueDequeue / queueEnqueue) this file drives the
//! REAL Plonky3 prover on a witness vector PRODUCED BY THE LEAN EXECUTOR — copied
//! verbatim from the `*WitnessJson` goldens of the corresponding
//! `Dregg2.Circuit.Witness.*` module (each of which runs the real `execFullA` arm and
//! lays out the full-state v2/v3 circuit's satisfying assignment with concrete
//! commitment-surface digest columns).
//!
//! The shape mirrors `lean_descriptor_air::lean_executor_derived_transfer`:
//!   1. the honest executor-derived witness proves+verifies (`execute → prove → verify`);
//!   2. a REAL forged post-state (a tampered THIRD ledger/side-table entry, a bystander
//!      mint, a wrong post-list) yields a witness the prover/verifier REJECTS — a real
//!      UNSAT on the bind / rest / log gate (the anti-ghost tooth, end-to-end).
//!
//! These are the validated reference's amplification: the SAME `execute→prove→verify`
//! gate the transfer beachhead established, now for eight more effects over the real
//! executor state.

use dregg_circuit::lean_descriptor_air::{
    parse_descriptor, prove_and_verify_descriptor, prove_descriptor, verify_descriptor,
};

/// A v2/v3 effect descriptor: a single guard bit at wire 0, then the rest/component/log
/// EQ gates at the fixed digest indices. (mint/noteCreate/noteSpend/queueAllocate are v2:
/// 72 wires, gates 66/67, 68/69, 70/71; the v3 queue effects extend the component wires.)
fn check_honest_proves_and_forged_rejects(
    descriptor_json: &str,
    expected_width: usize,
    expected_gates: usize,
    honest: &[i64],
    forged: &[i64],
    forged_gate_lhs: usize,
    forged_gate_rhs: usize,
    label: &str,
) {
    let desc = parse_descriptor(descriptor_json)
        .unwrap_or_else(|e| panic!("{label}: descriptor must parse: {e}"));
    assert_eq!(desc.trace_width, expected_width, "{label}: trace width");
    assert_eq!(desc.constraints.len(), expected_gates, "{label}: gate count");
    assert_eq!(honest.len(), expected_width, "{label}: honest witness width");
    assert_eq!(forged.len(), expected_width, "{label}: forged witness width");

    // The honest executor-derived witness MUST prove + verify.
    let proof = prove_and_verify_descriptor(&desc, honest)
        .unwrap_or_else(|e| panic!("{label}: honest executor-derived witness must prove+verify: {e}"));
    verify_descriptor(&desc, &proof)
        .unwrap_or_else(|e| panic!("{label}: re-verify of honest proof must succeed: {e}"));

    // The forgery's named gate pair MUST differ (the anti-ghost tooth shows up here).
    assert_ne!(
        forged[forged_gate_lhs], forged[forged_gate_rhs],
        "{label}: forged witness must break the bind/rest/log gate ({forged_gate_lhs} vs {forged_gate_rhs})"
    );

    // The forged witness MUST be rejected (prover panics on the broken gate in debug, or
    // verification rejects in release — either path means the forgery is NOT accepted).
    let tampered = std::panic::catch_unwind(|| {
        let p = prove_descriptor(&desc, forged)?;
        verify_descriptor(&desc, &p)
    });
    match tampered {
        Err(_) => {}
        Ok(verify_result) => assert!(
            verify_result.is_err(),
            "{label}: FORGED executor-derived witness MUST be rejected, but a proof verified — \
             the anti-ghost tooth failed"
        ),
    }
}

// ===========================================================================
// mintA — v2 (`Dregg2.Circuit.Witness.MintWitness`).
// Forgery: bystander ledger entry (2,0) minted 50 → 999 ⇒ component-bind gate (68 ≠ 69).
// ===========================================================================

const MINT_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-mint-v2","trace_width":72,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}}]}"#;

const MINT_HONEST: [i64; 72] = [
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    100000005000053, 130000006000083, 3, 3, 130000005000050, 130000005000050, 1000030, 1000030,
];

const MINT_FORGED: [i64; 72] = [
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    100000005000053, 130000006001032, 3, 3, 130000005000999, 130000005000050, 1000030, 1000030,
];

#[test]
fn b4_executor_derived_mint() {
    check_honest_proves_and_forged_rejects(
        MINT_DESCRIPTOR_JSON, 72, 4, &MINT_HONEST, &MINT_FORGED, 68, 69, "mintA",
    );
}

// ===========================================================================
// noteCreateA — v2 (`Dregg2.Circuit.Witness.NoteCreateWitness`).
// Forgery: bystander commitment 22 → 999 (tampered post-list) ⇒ bind gate (68 ≠ 69).
// ===========================================================================

const NOTECREATE_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-noteCreateA-v2","trace_width":72,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}}]}"#;

const NOTECREATE_HONEST: [i64; 72] = [
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    2000011000024, 3000077000012000024, 2, 2, 3000077000011000022, 3000077000011000022, 1000000, 1000000,
];

const NOTECREATE_FORGED: [i64; 72] = [
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    2000011000024, 3000077000012001001, 2, 2, 3000077000011000999, 3000077000011000022, 1000000, 1000000,
];

#[test]
fn b4_executor_derived_note_create() {
    check_honest_proves_and_forged_rejects(
        NOTECREATE_DESCRIPTOR_JSON, 72, 4, &NOTECREATE_HONEST, &NOTECREATE_FORGED, 68, 69, "noteCreateA",
    );
}

// ===========================================================================
// noteSpendA — v2 (`Dregg2.Circuit.Witness.NoteSpendWitness`).
// Forgery: bystander nullifier 22 silently dropped (double-spend laundering) ⇒ bind gate (68 ≠ 69).
// ===========================================================================

const NOTESPEND_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-noteSpendA-v2","trace_width":72,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}}]}"#;

const NOTESPEND_HONEST: [i64; 72] = [
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    2000011000024, 3000077000012000024, 2, 2, 3000077000011000022, 3000077000011000022, 1000000, 1000000,
];

const NOTESPEND_FORGED: [i64; 72] = [
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    2000011000024, 2000078000013, 2, 2, 2000077000011, 3000077000011000022, 1000000, 1000000,
];

#[test]
fn b4_executor_derived_note_spend() {
    check_honest_proves_and_forged_rejects(
        NOTESPEND_DESCRIPTOR_JSON, 72, 4, &NOTESPEND_HONEST, &NOTESPEND_FORGED, 68, 69, "noteSpendA",
    );
}

// ===========================================================================
// queueAllocateA — v2 (`Dregg2.Circuit.Witness.QueueAllocateWitness`).
// Forgery: bystander queue (id 5) capacity 4 → 999 (tampered side-table) ⇒ bind gate (68 ≠ 69).
// ===========================================================================

const QUEUEALLOCATE_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-queueAllocateA-v2","trace_width":72,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}}]}"#;

const QUEUEALLOCATE_HONEST: [i64; 72] = [
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1000000000501004002, 2501004000901008002, 2, 2, 2501004000900008000, 2501004000900008000, 1000000, 1000000,
];

const QUEUEALLOCATE_FORGED: [i64; 72] = [
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1000000000501004002, 2501999000901008002, 2, 2, 2501999000900008000, 2501004000900008000, 1000000, 1000000,
];

#[test]
fn b4_executor_derived_queue_allocate() {
    check_honest_proves_and_forged_rejects(
        QUEUEALLOCATE_DESCRIPTOR_JSON, 72, 4, &QUEUEALLOCATE_HONEST, &QUEUEALLOCATE_FORGED, 68, 69,
        "queueAllocateA",
    );
}

// ===========================================================================
// queueEnqueueA — v3 / triple (`Dregg2.Circuit.Witness.QueueEnqueueWitness`).
// 76 wires, 6 gates (rest 66/67; queues 68/69; bal 70/71; escrows 72/73; log 74/75).
// Forgery: parked escrow amount 30 → 999 (tampered escrow side-table) ⇒ escrow bind gate (72 ≠ 73).
// ===========================================================================

const QUEUEENQUEUE_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-queueEnqueueA-v2","trace_width":76,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}},{"lhs":{"t":"var","v":72},"rhs":{"t":"var","v":73}},{"lhs":{"t":"var","v":74},"rhs":{"t":"var","v":75}}]}"#;

const QUEUEENQUEUE_HONEST: [i64; 76] = [
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1000000000600004111, 2000000001271005240, 2, 2, 1000000000500004908, 1000000000500004908,
    70000000, 70000000, 1000000000700000300, 1000000000700000300, 1000030, 1000030,
];

const QUEUEENQUEUE_FORGED: [i64; 76] = [
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1000000000600004111, 2000000001271014930, 2, 2, 1000000000500004908, 1000000000500004908,
    70000000, 70000000, 1000000000700009990, 1000000000700000300, 1000030, 1000030,
];

#[test]
fn b4_executor_derived_queue_enqueue() {
    check_honest_proves_and_forged_rejects(
        QUEUEENQUEUE_DESCRIPTOR_JSON, 76, 6, &QUEUEENQUEUE_HONEST, &QUEUEENQUEUE_FORGED, 72, 73,
        "queueEnqueueA",
    );
}

// ===========================================================================
// queueDequeueA — v3 / triple (`Dregg2.Circuit.Witness.QueueDequeueWitness`).
// 76 wires, 6 gates. Forgery: refund ledger 100 → 999 (tampered bal) ⇒ bal bind gate (70 ≠ 71).
// ===========================================================================

const QUEUEDEQUEUE_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-queueDequeueA-v2","trace_width":76,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}},{"lhs":{"t":"var","v":72},"rhs":{"t":"var","v":73}},{"lhs":{"t":"var","v":74},"rhs":{"t":"var","v":75}}]}"#;

const QUEUEDEQUEUE_HONEST: [i64; 76] = [
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    2000000001270004490, 2000000001301004333, 2, 2, 1000000000500004000, 1000000000500004000,
    100000000, 100000000, 1000000000700000301, 1000000000700000301, 1000030, 1000030,
];

const QUEUEDEQUEUE_FORGED: [i64; 76] = [
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    2000000001270004490, 2000000002200004333, 2, 2, 1000000000500004000, 1000000000500004000,
    999000000, 100000000, 1000000000700000301, 1000000000700000301, 1000030, 1000030,
];

#[test]
fn b4_executor_derived_queue_dequeue() {
    check_honest_proves_and_forged_rejects(
        QUEUEDEQUEUE_DESCRIPTOR_JSON, 76, 6, &QUEUEDEQUEUE_HONEST, &QUEUEDEQUEUE_FORGED, 70, 71,
        "queueDequeueA",
    );
}

// ===========================================================================
// queueAtomicTxA — v3 / triple (`Dregg2.Circuit.Witness.QueueAtomicTxWitness`).
// 76 wires, 6 gates. Batch = one enqueue op. Forgery: enqueued buffer gets a bystander message
// appended (tampered FIFO) ⇒ queues bind gate (68 ≠ 69).
// ===========================================================================

const QUEUEATOMICTX_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-queueAtomicTxA-v2","trace_width":76,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}},{"lhs":{"t":"var","v":72},"rhs":{"t":"var","v":73}},{"lhs":{"t":"var","v":74},"rhs":{"t":"var","v":75}}]}"#;

const QUEUEATOMICTX_HONEST: [i64; 76] = [
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1000000000600004111, 2000002001270005240, 2, 2, 1000000000500004908, 1000000000500004908,
    70000000, 70000000, 1000000000700000300, 1000000000700000300, 2000000000030, 2000000000030,
];

const QUEUEATOMICTX_FORGED: [i64; 76] = [
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1000000000600004111, 2000002001270004909, 2, 2, 1000000000500004577, 1000000000500004908,
    70000000, 70000000, 1000000000700000300, 1000000000700000300, 2000000000030, 2000000000030,
];

#[test]
fn b4_executor_derived_queue_atomic_tx() {
    check_honest_proves_and_forged_rejects(
        QUEUEATOMICTX_DESCRIPTOR_JSON, 76, 6, &QUEUEATOMICTX_HONEST, &QUEUEATOMICTX_FORGED, 68, 69,
        "queueAtomicTxA",
    );
}

// ===========================================================================
// pipelinedSendA — v1 (`Dregg2.Circuit.Witness.PipelinedSendWitness`).
// 74 wires, 5 gates (rest 66/67; frame-reuse 68/69; touched 70/71; log 72/73). Kernel frozen,
// touched set = ∅. Forgery: bystander cell 2 minted 50 → 999 (tampered frozen frame) ⇒ frame
// gate (68 ≠ 69) — the "pale ghost" the projection circuit would miss.
// ===========================================================================

const PIPELINEDSEND_DESCRIPTOR_JSON: &str = r#"{"name":"dregg-pipelinedSendA-v1","trace_width":74,"constraints":[{"lhs":{"t":"var","v":0},"rhs":{"t":"const","v":1}},{"lhs":{"t":"var","v":66},"rhs":{"t":"var","v":67}},{"lhs":{"t":"var","v":68},"rhs":{"t":"var","v":69}},{"lhs":{"t":"var","v":70},"rhs":{"t":"var","v":71}},{"lhs":{"t":"var","v":72},"rhs":{"t":"var","v":73}}]}"#;

const PIPELINEDSEND_HONEST: [i64; 74] = [
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    980000348000459, 980000349000459, 3, 3, 3000100000005000050, 3000100000005000050, 0, 0, 1000000, 1000000,
];

const PIPELINEDSEND_FORGED: [i64; 74] = [
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    980000348000459, 1929006043009000, 3, 3, 3000100000005000050, 3000100000005000999, 0, 0, 1000000, 1000000,
];

#[test]
fn b4_executor_derived_pipelined_send() {
    check_honest_proves_and_forged_rejects(
        PIPELINEDSEND_DESCRIPTOR_JSON, 74, 5, &PIPELINEDSEND_HONEST, &PIPELINEDSEND_FORGED, 68, 69,
        "pipelinedSendA",
    );
}
