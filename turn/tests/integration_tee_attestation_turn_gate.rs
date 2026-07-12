//! R2 — a TEE attestation fact EXECUTOR-ENFORCED in a real turn.
//!
//! `cell/src/tee_attest.rs` gives the TEE fact its verifier shape
//! (`TeeWitnessedPredicateVerifier`, fail-closed until a host injects vendor
//! crypto), and `registry_with_real_verifiers()` — the registry every
//! `TurnExecutor` constructor installs by default — registers that fail-closed
//! verifier under `Custom { tee_predicate_vk() }`. Until now the fact was only
//! exercised registry-level / light-client-side. This test drives it through
//! the REAL turn path: `TurnExecutor::execute` → `execute_tree`'s touched-cell
//! program loop → `StateConstraint::Witnessed` dispatch through
//! `self.witnessed_registry` with the proof read from `Action::witness_blobs`.
//!
//! The gated cell is a grain turn-cell shape: its program requires the TEE
//! attestation predicate (pinned launch measurement; `report_data` bound to the
//! session commitment witnessed in state slot 8 — the same slot index as
//! `grain_turn::ATTESTATION_SLOT`, kept as a literal here so `dregg-turn`'s
//! test tree does not grow a `grain-turn` dev-dependency).
//!
//! What is proven, honestly:
//!
//! - REJECTED (fail-closed): with the PRODUCTION default registry and no host
//!   vendor crypto injected, a turn carrying a well-formed TEE proof blob is
//!   rejected as `TurnError::ProgramViolation`, and the rejection reason shows
//!   dispatch REACHED the tee-attestation verifier (not `KindNotRegistered`) —
//!   the fact is turn-enforced and closed by default.
//! - ADMITTED: with a host `TeeAttestationVerifier` injected (the documented
//!   `with_verifier` + `register_custom` upgrade path, same registry base) and
//!   the proof witnessed at `proof_witness_index` 0, the SAME turn commits.
//! - The admit is non-vacuous: with the verifier still injected, a wrong
//!   measurement, an unbound `report_data`, a forged vendor signature, and a
//!   stripped proof blob each still reject.
//!
//! Honest boundary: the injected `TestHostSnpVerifier` below is a TEST DOUBLE
//! for the host vendor-crypto seam. It authenticates a toy 8-byte trailer, NOT
//! an AMD KDS cert chain — real SEV-SNP/TDX/Nitro verification is host-side by
//! design (the cell crate must not link vendor crypto). What this file proves
//! is the executor weld: fail-closed default, registry dispatch in a real turn,
//! witness-blob binding, and the production `TeeWitnessedPredicateVerifier`'s
//! measurement/report_data/TCB checks (which are NOT reimplemented here).

use std::sync::Arc;

use dregg_cell::program::{CellProgram, StateConstraint};
use dregg_cell::tee_attest::{
    TeeAttestationVerifier, TeeQuoteKind, TeeReportClaims, TeeWitnessedPredicateVerifier,
    encode_tee_proof, tee_attestation_predicate, tee_predicate_vk,
};
use dregg_cell::{AuthRequired, Cell, CellId, Ledger, Permissions, field_from_u64};
use dregg_turn::action::WitnessBlob;
use dregg_turn::executor::registry_with_real_verifiers;
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Effect, TurnError,
    TurnExecutor, turn::Turn,
};

/// The pinned launch measurement of the ONE binary the cell program admits
/// (SNP launch measurement / TDX MRTD analog).
const MEASUREMENT: [u8; 32] = [0x4D; 32];

/// The turn/session commitment the quote's `report_data` must be bound to,
/// witnessed in the grain turn-cell's attestation slot.
const SESSION_COMMIT: [u8; 32] = [0x42; 32];

/// State slot carrying the bound commitment — the grain turn-cell's
/// attestation slot (`grain_turn::ATTESTATION_SLOT == 8`; STATE_SLOTS is 16).
const REPORT_DATA_SLOT: u8 = 8;

/// Slot the turn's action mutates (distinct from the attestation slot, so the
/// bound commitment survives into the post-state the predicate reads).
const MUTATED_SLOT: u8 = 1;

/// Toy vendor-signature trailer the injected test verifier authenticates.
const VENDOR_SIG: [u8; 8] = *b"SNPSIGOK";

/// Test double for the injected host vendor-crypto seam. Report layout:
/// `[measurement 32][report_data 32][vendor_sig 8]`. It refuses anything whose
/// trailer is not `VENDOR_SIG` — honoring the `TeeAttestationVerifier`
/// contract that claims are only returned for an AUTHENTICATED report — but
/// the "authentication" is a fixture, standing in for the real AMD-KDS /
/// DCAP / Nitro chain a production host installs.
struct TestHostSnpVerifier;

impl TeeAttestationVerifier for TestHostSnpVerifier {
    fn verify_report(
        &self,
        kind: TeeQuoteKind,
        report_bytes: &[u8],
    ) -> Result<TeeReportClaims, String> {
        if kind != TeeQuoteKind::SevSnp {
            return Err("test host verifier only speaks SEV-SNP".to_string());
        }
        if report_bytes.len() != 72 {
            return Err(format!(
                "malformed report: expected 72 bytes, got {}",
                report_bytes.len()
            ));
        }
        if report_bytes[64..72] != VENDOR_SIG {
            return Err("vendor signature verification failed".to_string());
        }
        let mut measurement = [0u8; 32];
        measurement.copy_from_slice(&report_bytes[0..32]);
        let mut report_data = [0u8; 32];
        report_data.copy_from_slice(&report_bytes[32..64]);
        Ok(TeeReportClaims {
            measurement,
            report_data,
            tcb_ok: true,
        })
    }
}

/// Build a vendor-signed (toy trailer) report for the test verifier.
fn signed_report(measurement: [u8; 32], report_data: [u8; 32]) -> Vec<u8> {
    let mut r = Vec::with_capacity(72);
    r.extend_from_slice(&measurement);
    r.extend_from_slice(&report_data);
    r.extend_from_slice(&VENDOR_SIG);
    r
}

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

/// A grain turn-cell gated by the TEE attestation predicate: its program
/// requires `Custom { tee_predicate_vk }` over every action, with the pinned
/// measurement as the predicate commitment and the session commitment bound
/// in the attestation slot.
fn make_tee_gated_grain_cell(seed: u8) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], 1000);
    cell.permissions = open_permissions();
    cell.state.fields[REPORT_DATA_SLOT as usize] = SESSION_COMMIT;
    cell.program = CellProgram::Predicate(vec![StateConstraint::Witnessed {
        wp: tee_attestation_predicate(MEASUREMENT, REPORT_DATA_SLOT),
    }]);
    cell
}

/// A real single-action turn on the gated cell: SetField on `MUTATED_SLOT`,
/// with the TEE proof carried in `Action::witness_blobs` (the predicate's
/// `proof_witness_index` is 0, so the proof is blob 0).
fn tee_gated_turn(cell: CellId, witness_blobs: Vec<WitnessBlob>) -> Turn {
    let mut forest = CallForest::new();
    let action = Action {
        target: cell,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell,
            index: MUTATED_SLOT as usize,
            value: field_from_u64(7),
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs,
    };
    forest.add_root(action);
    Turn {
        agent: cell,
        nonce: 0,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

/// An executor whose registry is the SAME production base
/// (`registry_with_real_verifiers`), upgraded via the documented host path:
/// re-register `Custom { tee_predicate_vk }` with a `TeeWitnessedPredicateVerifier`
/// carrying an injected vendor verifier.
fn executor_with_injected_host_tee() -> TurnExecutor {
    let mut reg = registry_with_real_verifiers();
    reg.register_custom(
        tee_predicate_vk(),
        Arc::new(TeeWitnessedPredicateVerifier::with_verifier(Arc::new(
            TestHostSnpVerifier,
        ))),
    );
    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_witnessed_registry(reg);
    executor
}

// ─────────────────────────────────────────────────────────────────────
// REJECTED: production default, no host crypto injected (fail-closed)
// ─────────────────────────────────────────────────────────────────────

/// A bare `TurnExecutor::new()` carries the production registry, whose TEE
/// verifier is fail-closed. A turn on the TEE-gated grain cell — carrying a
/// perfectly well-formed proof blob — is REJECTED, and the rejection reason
/// proves dispatch reached the tee-attestation verifier through the real turn
/// path (it is a verifier rejection, not `KindNotRegistered`).
#[test]
fn production_default_rejects_tee_gated_turn_fail_closed() {
    let cell = make_tee_gated_grain_cell(1);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    // The proof is well-formed and would satisfy the injected verifier; the
    // ONLY missing piece is host vendor crypto. Fail-closed must still refuse.
    let report = signed_report(MEASUREMENT, SESSION_COMMIT);
    let proof = encode_tee_proof(TeeQuoteKind::SevSnp, &report);
    let turn = tee_gated_turn(cell_id, vec![WitnessBlob::proof(proof)]);

    let executor = TurnExecutor::new(ComputronCosts::zero());
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        !result.is_committed(),
        "no host TEE crypto injected: the turn MUST be rejected (fail-closed); got {result:?}"
    );
    let (err, _at) = result.unwrap_rejected();
    match err {
        TurnError::ProgramViolation { cell: c, reason } => {
            assert_eq!(c, cell_id, "the violation must be on the gated cell");
            assert!(
                reason.contains("tee-attestation"),
                "dispatch must have REACHED the tee verifier (not KindNotRegistered): {reason}"
            );
            assert!(
                reason.contains("no TeeAttestationVerifier installed"),
                "the rejection must be the fail-closed default, not some other failure: {reason}"
            );
        }
        other => panic!("expected ProgramViolation on the gated cell, got: {other}"),
    }
    // Nothing landed.
    assert_eq!(
        ledger.get(&cell_id).unwrap().state.fields[MUTATED_SLOT as usize],
        [0u8; 32],
        "a rejected turn must not mutate the cell"
    );
}

// ─────────────────────────────────────────────────────────────────────
// ADMITTED: host verifier injected + proof witnessed
// ─────────────────────────────────────────────────────────────────────

/// With the host vendor verifier injected and the quote witnessed in the
/// action, the SAME turn commits: the attestation fact — "this turn ran the
/// pinned binary inside a genuine TEE, bound to this session commitment" —
/// is now enforced BY THE EXECUTOR as a condition of the turn landing.
#[test]
fn injected_host_verifier_and_witnessed_proof_admit_the_turn() {
    let cell = make_tee_gated_grain_cell(2);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let report = signed_report(MEASUREMENT, SESSION_COMMIT);
    let proof = encode_tee_proof(TeeQuoteKind::SevSnp, &report);
    let turn = tee_gated_turn(cell_id, vec![WitnessBlob::proof(proof)]);

    let executor = executor_with_injected_host_tee();
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "genuine measurement + bound report_data + injected verifier must commit; got {result:?}"
    );
    let landed = ledger.get(&cell_id).unwrap();
    assert_eq!(
        landed.state.fields[MUTATED_SLOT as usize],
        field_from_u64(7),
        "the admitted turn's effect must have landed"
    );
    assert_eq!(
        landed.state.fields[REPORT_DATA_SLOT as usize], SESSION_COMMIT,
        "the attestation slot's bound commitment must be untouched"
    );
}

// ─────────────────────────────────────────────────────────────────────
// Non-vacuity: with the verifier STILL injected, every broken binding
// rejects through the same real turn path.
// ─────────────────────────────────────────────────────────────────────

/// A genuine quote for a DIFFERENT binary (measurement != the program's pin)
/// is rejected — the measurement pin travels through the turn path.
#[test]
fn wrong_measurement_rejected_even_with_verifier_injected() {
    let cell = make_tee_gated_grain_cell(3);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let report = signed_report([0x55; 32], SESSION_COMMIT); // not MEASUREMENT
    let proof = encode_tee_proof(TeeQuoteKind::SevSnp, &report);
    let turn = tee_gated_turn(cell_id, vec![WitnessBlob::proof(proof)]);

    let executor = executor_with_injected_host_tee();
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        !result.is_committed(),
        "a quote for an unpinned binary must be rejected; got {result:?}"
    );
    let (err, _) = result.unwrap_rejected();
    match err {
        TurnError::ProgramViolation { reason, .. } => assert!(
            reason.contains("measurement does not match"),
            "expected the measurement-pin rejection: {reason}"
        ),
        other => panic!("expected ProgramViolation, got: {other}"),
    }
}

/// A genuine quote whose `report_data` is NOT the commitment bound in the
/// cell's attestation slot (a replayed / unbound quote) is rejected.
#[test]
fn unbound_report_data_rejected_even_with_verifier_injected() {
    let cell = make_tee_gated_grain_cell(4);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let report = signed_report(MEASUREMENT, [0xEE; 32]); // not SESSION_COMMIT
    let proof = encode_tee_proof(TeeQuoteKind::SevSnp, &report);
    let turn = tee_gated_turn(cell_id, vec![WitnessBlob::proof(proof)]);

    let executor = executor_with_injected_host_tee();
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        !result.is_committed(),
        "an unbound/replayed quote must be rejected; got {result:?}"
    );
    let (err, _) = result.unwrap_rejected();
    match err {
        TurnError::ProgramViolation { reason, .. } => assert!(
            reason.contains("not bound to the committed turn/session"),
            "expected the report_data binding rejection: {reason}"
        ),
        other => panic!("expected ProgramViolation, got: {other}"),
    }
}

/// A report the host verifier cannot authenticate (forged vendor signature)
/// is rejected — the injected seam's refusal surfaces as a turn rejection.
#[test]
fn forged_vendor_signature_rejected_even_with_verifier_injected() {
    let cell = make_tee_gated_grain_cell(5);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let mut report = signed_report(MEASUREMENT, SESSION_COMMIT);
    report[64] ^= 0xFF; // break the vendor signature trailer
    let proof = encode_tee_proof(TeeQuoteKind::SevSnp, &report);
    let turn = tee_gated_turn(cell_id, vec![WitnessBlob::proof(proof)]);

    let executor = executor_with_injected_host_tee();
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        !result.is_committed(),
        "an unauthenticated report must be rejected; got {result:?}"
    );
    let (err, _) = result.unwrap_rejected();
    match err {
        TurnError::ProgramViolation { reason, .. } => assert!(
            reason.contains("TEE report verification failed"),
            "expected the vendor-authentication rejection: {reason}"
        ),
        other => panic!("expected ProgramViolation, got: {other}"),
    }
}

/// Stripping the proof blob from the action closes the gate even with the
/// verifier injected — the anti-strip tooth on the witness carrier.
#[test]
fn stripped_proof_blob_rejected_even_with_verifier_injected() {
    let cell = make_tee_gated_grain_cell(6);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let turn = tee_gated_turn(cell_id, vec![]); // no witness blobs at all

    let executor = executor_with_injected_host_tee();
    let result = executor.execute(&turn, &mut ledger);
    assert!(
        !result.is_committed(),
        "a turn with the proof stripped must be rejected; got {result:?}"
    );
    let (err, _) = result.unwrap_rejected();
    match err {
        TurnError::ProgramViolation { reason, .. } => assert!(
            reason.contains("witness_blobs has no entry"),
            "expected the missing-proof-blob rejection: {reason}"
        ),
        other => panic!("expected ProgramViolation, got: {other}"),
    }
}
