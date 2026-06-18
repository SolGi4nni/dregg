//! # THE SELECTOR-GATE FORGERY BITE — the light-client unfoolability close for the gate-less
//! value-cohort family (setField / mint / attenuate / revokeCapability / grantCap).
//!
//! ## The forgery this closes
//!
//! The deployed sovereign verifier (`turn::executor::verify_and_commit_proof_rotated`) resolves ONE
//! rotated descriptor by `vm_effects.first()` and verifies ONE proof over a one-row-per-effect trace.
//! Before the fix, the per-slot setField descriptor (`setFieldVmDescriptor2-{0..7}R24`) and the mint /
//! attenuate / revokeCapability / grantCap members carried NO selector-binding gate. So a turn whose
//! LEAD is gate-less + a TAIL effect — e.g. `[SetField(slot0, v), Transfer(self→victim, A)]` — proved
//! under the gate-less setField LEAD descriptor while the TAIL (Transfer) row's transition was
//! UNFORCED: the prover set the tail row's balance FREELY, the commitment-integrity gates still
//! passed, and `verify_vm_descriptor2` ACCEPTED. A ledgerless light client was fooled (a silent
//! cross-effect transfer the descriptor never constrained).
//!
//! ## The close (Lean-emitted, law #1)
//!
//! Each gate-less member now appends `selectorGate <ownRuntimeSelector>` (`EffectVmEmit.§6½`,
//! `EffectVmEmitRotationV3.withSelectorGate`): the per-row body `(1 - sel[NOOP])·(1 - sel[s])` is
//! forced ZERO on every transition row, so a NON-pad row must carry the descriptor's OWN runtime
//! selector. The foreign-selector TAIL row (`sel[NOOP] = 0`, `sel[SET_FIELD] = 0`, `sel[TRANSFER] =
//! 1`) makes the body `1·1 = 1 ≠ 0` → UNSAT. The forgery is dead at `verify_vm_descriptor2` /
//! `prove_vm_descriptor2` ALONE — no ledger needed.
//!
//! ## The teeth
//!
//!   * NEGATIVE (the bite): a `[SetField(slot0, v), Transfer]` trace under the setField-0 LEAD
//!     descriptor, with the Transfer tail row's balance FORGED (a free debit with no honest source)
//!     — proving REFUSES (the appended `selectorGate SET_FIELD` rejects the foreign-selector row).
//!     Mirrored for mint (`[BridgeMint, Transfer]` under the mint descriptor).
//!   * POSITIVE (no downgrade): an HONEST single-cohort setField turn (the homogeneous shape the
//!     deployed sovereign verify path receives — heterogeneous turns split per cohort in
//!     PATH-PRESERVE / are rejected by the rotated prover) still proves+verifies GREEN.
//!
//! Gated on `prover` (compiles `descriptor_ir2`). Run with
//! `cargo test -p dregg-circuit --features prover selector_gate -- --nocapture`.

#![cfg(feature = "prover")]

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::columns::{PARAM_BASE, STATE_AFTER_BASE, param, sel, state};
use dregg_circuit::effect_vm::trace_rotated::{
    RotatedBlockWitness, empty_caveat_manifest, generate_rotated_effect_vm_trace,
    rotated_descriptor_name_for_effect,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_turn::rotation_witness as rw;

/// Resolve a rotated descriptor JSON by registry key from the committed staged TSV.
fn rotated_descriptor_json(name: &str) -> &'static str {
    V3_STAGED_REGISTRY_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some(name) {
                let _ = it.next();
                it.next()
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("{name} not in V3_STAGED_REGISTRY_TSV"))
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

fn producer_cell(balance: i64, nonce: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("31 pre-iroot limbs")
}

/// `true` iff `prove_vm_descriptor2` REFUSES (returns `Err` OR panics) on the given trace+PIs.
fn refused(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    dpis: &[BabyBear],
    mem_boundary: &MemBoundaryWitness,
    map_heaps: &[Vec<dregg_circuit::heap_root::HeapLeaf>],
) -> bool {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_vm_descriptor2(desc, trace, dpis, mem_boundary, map_heaps)
    }));
    match r {
        Err(_) => true,
        Ok(res) => res.is_err(),
    }
}

/// THE NEGATIVE TOOTH (setField LEAD): a `[SetField(slot0, v), Transfer]` trace under the setField-0
/// LEAD descriptor — with the Transfer tail row carrying a FORGED free balance debit — is UNSAT.
/// The appended `selectorGate SET_FIELD` rejects the foreign-selector (TRANSFER) tail row.
#[test]
fn setfield_lead_with_foreign_transfer_tail_is_unsat() {
    let name = "setFieldVmDescriptor2-0R24";
    let desc = parse_vm_descriptor2(rotated_descriptor_json(name))
        .expect("setField-0 rotated descriptor parses");

    let before_balance: i64 = 100_000;
    let field_val = BabyBear::new(0xABCD);
    let st = CellState::new(before_balance as u64, 0);

    // The heterogeneous LEAD = setField(slot 0), TAIL = an outgoing Transfer (the smuggled move).
    let effects = vec![
        Effect::SetField {
            field_idx: 0,
            value: field_val,
        },
        Effect::Transfer {
            amount: 50,
            direction: 1,
        },
    ];

    // The LIVE verify path resolves the descriptor by the LEAD effect — exactly setField-0.
    assert_eq!(
        rotated_descriptor_name_for_effect(&effects[0]),
        Some(name),
        "the lead effect resolves the gate-less setField-0 descriptor (the forgery's entry)"
    );

    // Build the rotated trace + PIs through the LIVE generator (the producer the adversary controls).
    let mut ledger = Ledger::new();
    let mut after_cell = producer_cell(before_balance, 0);
    assert!(after_cell.state.set_field(0, {
        let mut b = [0u8; 32];
        b[0..4].copy_from_slice(&0xABCDu32.to_le_bytes());
        b
    }));
    ledger.insert_cell(after_cell.clone()).unwrap();
    let before_cell = producer_cell(before_balance, 0);
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32]];
    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let caveat = empty_caveat_manifest();

    let (mut trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("generator builds the heterogeneous trace");

    // The TAIL (row 1) carries the foreign TRANSFER selector — the smoking gun the gate forbids.
    assert_eq!(
        trace[1][sel::TRANSFER],
        BabyBear::ONE,
        "row 1 carries the foreign TRANSFER selector"
    );
    assert_eq!(
        trace[1][sel::SET_FIELD],
        BabyBear::ZERO,
        "row 1 does NOT carry the setField selector (it is a foreign row)"
    );
    assert_eq!(
        trace[1][sel::NOOP],
        BabyBear::ZERO,
        "row 1 is NOT a NoOp pad (it is a real foreign effect)"
    );

    // The FORGERY: freely debit the tail row's after-balance (a transfer the descriptor never binds).
    trace[1][STATE_AFTER_BASE + state::BALANCE_LO] =
        trace[1][STATE_AFTER_BASE + state::BALANCE_LO] - BabyBear::new(50);
    trace[1][PARAM_BASE + param::AMOUNT] = BabyBear::new(50);
    trace[1][PARAM_BASE + param::DIRECTION] = BabyBear::ONE;

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    assert!(
        refused(&desc, &trace, &dpis, &mem_boundary, &map_heaps),
        "SOUNDNESS (light-client unfoolable): the foreign-TRANSFER tail row under the setField-0 \
         LEAD descriptor must be UNSAT — the appended `selectorGate SET_FIELD` rejects it"
    );

    eprintln!(
        "SELECTOR-GATE FORGERY BITE (setField lead): [SetField, Transfer] under setFieldVmDescriptor2-0R24 \
         is UNSAT — the foreign-selector tail row is rejected by the selector-binding gate."
    );
}

/// THE NEGATIVE TOOTH (mint LEAD): the same bite for the BridgeMint member — `[BridgeMint, Transfer]`
/// under the mint descriptor is UNSAT (the appended `selectorGate BRIDGE_MINT` rejects the tail row).
#[test]
fn mint_lead_with_foreign_transfer_tail_is_unsat() {
    let name = "mintVmDescriptor2R24";
    let desc =
        parse_vm_descriptor2(rotated_descriptor_json(name)).expect("mint rotated descriptor parses");

    let before_balance: i64 = 100_000;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![
        Effect::BridgeMint {
            value_lo: BabyBear::new(10),
            mint_hash: BabyBear::new(0x1234),
            value_full: 10,
        },
        Effect::Transfer {
            amount: 50,
            direction: 1,
        },
    ];
    assert_eq!(
        rotated_descriptor_name_for_effect(&effects[0]),
        Some(name),
        "the lead BridgeMint resolves the mint descriptor"
    );

    let mut ledger = Ledger::new();
    let after_cell = producer_cell(before_balance + 10, 0);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let before_cell = producer_cell(before_balance, 0);
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32]];
    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let caveat = empty_caveat_manifest();

    let (mut trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("generator builds the heterogeneous mint+transfer trace");

    assert_eq!(trace[1][sel::TRANSFER], BabyBear::ONE);
    assert_eq!(trace[1][sel::BRIDGE_MINT], BabyBear::ZERO);
    assert_eq!(trace[1][sel::NOOP], BabyBear::ZERO);

    // Forge the tail transfer's debit.
    trace[1][STATE_AFTER_BASE + state::BALANCE_LO] =
        trace[1][STATE_AFTER_BASE + state::BALANCE_LO] - BabyBear::new(50);
    trace[1][PARAM_BASE + param::AMOUNT] = BabyBear::new(50);
    trace[1][PARAM_BASE + param::DIRECTION] = BabyBear::ONE;

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    assert!(
        refused(&desc, &trace, &dpis, &mem_boundary, &map_heaps),
        "SOUNDNESS: [BridgeMint, Transfer] under the mint descriptor must be UNSAT — the appended \
         `selectorGate BRIDGE_MINT` rejects the foreign-TRANSFER tail row"
    );

    eprintln!(
        "SELECTOR-GATE FORGERY BITE (mint lead): [BridgeMint, Transfer] under mintVmDescriptor2R24 is UNSAT."
    );
}

/// THE POSITIVE TOOTH (no downgrade): an HONEST single-cohort setField turn — the homogeneous shape
/// the deployed sovereign verify path actually receives — still PROVES + VERIFIES green through the
/// gated setField-0 descriptor. The active row carries `sel[SET_FIELD] = 1` and the pads
/// `sel[NOOP] = 1`, both of which the appended gate admits.
#[test]
fn honest_homogeneous_setfield_still_proves_and_verifies() {
    let name = "setFieldVmDescriptor2-0R24";
    let desc = parse_vm_descriptor2(rotated_descriptor_json(name))
        .expect("setField-0 rotated descriptor parses");

    let before_balance: i64 = 100_000;
    let field_val = BabyBear::new(0xBEEF);
    let st = CellState::new(before_balance as u64, 0);

    // A single-cohort (homogeneous) setField turn — the ONLY shape the single-descriptor sovereign
    // verify path legitimately receives.
    let effects = vec![Effect::SetField {
        field_idx: 0,
        value: field_val,
    }];

    let mut ledger = Ledger::new();
    let mut after_cell = producer_cell(before_balance, 0);
    assert!(after_cell.state.set_field(0, {
        let mut b = [0u8; 32];
        b[0..4].copy_from_slice(&0xBEEFu32.to_le_bytes());
        b
    }));
    ledger.insert_cell(after_cell.clone()).unwrap();
    let before_cell = producer_cell(before_balance, 0);
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32]];
    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let caveat = empty_caveat_manifest();

    let (trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("generator builds the honest homogeneous setField trace");

    // The active row (0) carries the setField selector; all later rows are NoOp pads — both admitted.
    assert_eq!(trace[0][sel::SET_FIELD], BabyBear::ONE, "row 0 is the active setField row");
    for row in trace.iter().skip(1) {
        assert_eq!(row[sel::NOOP], BabyBear::ONE, "every pad row carries sel[NOOP] = 1");
    }

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
        .expect("NO DOWNGRADE: the honest homogeneous setField turn must still prove under the gate");
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .expect("NO DOWNGRADE: the honest setField proof must verify under the gate");

    eprintln!(
        "SELECTOR-GATE NO-DOWNGRADE (setField): an honest single-cohort setField turn still \
         proves+verifies green through the gated setFieldVmDescriptor2-0R24."
    );
}
