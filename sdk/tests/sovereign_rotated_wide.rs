//! # THE WIDE PRODUCER→EXECUTOR PIPELINE (STAGED — the faithful-commitment flip, de-risked).
//!
//! Proves the WHOLE flag-day pipeline end-to-end at the WIDE 8-felt geometry, ADDITIVELY (the live
//! 1-felt path in `sovereign_rotated_c1.rs` is UNTOUCHED). The flip is now a mechanical switch — this
//! test demonstrates each leg already coheres:
//!
//!   * **PRODUCER leg** (`full_turn_proof::prove_effect_vm_rotated_wide`): mints a real wide
//!     `Ir2BatchProof` over the WIDE descriptor (`WIDE_REGISTRY_STAGED_TSV` = the verified Lean
//!     `v3RegistryCapOpenWide`), publishing the 16 wide commit PIs (the 8-felt BEFORE/AFTER commits).
//!   * **EXECUTOR leg** (mirrored here): reconstructs the trusted before/after cell state, computes
//!     the chip-faithful 8-felt commit (`poseidon2::wire_commit_8_chip` — the byte-twin of the
//!     circuit's `fill_wide_block`) over each cell's `compute_rotated_pre_limbs`, OVERRIDES the 16
//!     wide PIs with those trusted commits, and `verify_vm_descriptor2` ACCEPTS — exactly the wide
//!     analog of the live executor's `dpis[42]/[43]` override (the 1-felt-retire the flip performs).
//!   * **THE FORGERY TOOTH**: a forged trusted commit (a state the kernel never produced) makes the
//!     anchored 16 wide PIs disagree with the proof's bound carrier ⇒ `verify_vm_descriptor2` UNSAT.
//!
//! So the flag-day = repoint the sovereign producer + executor onto these wide legs + re-emit/re-pin
//! the VK (atomic, ember-gated). This test proves the legs are green BEFORE that switch flips.
//!
//! Requires `prover` (the wide producer + verifier). Self-skips under `not(prover)`.

#![cfg(feature = "prover")]

use dregg_cell::commitment::{V9RotationContext, compute_rotated_pre_limbs};
use dregg_cell::{Cell, CellMode, Ledger};
use dregg_circuit::descriptor_ir2::{
    parse_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::{CellState, Effect as VmEffect};
use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::wire_commit_8_chip;
use dregg_sdk::full_turn_proof::prove_effect_vm_rotated_wide;
use dregg_turn::rotation_witness as rw;

/// Build a sovereign before/after cell pair for a transfer-out of `amount` from a `balance` cell.
fn sovereign_transfer_cells(balance: i64, amount: i64) -> (Cell, Cell) {
    let token_id = *blake3::hash(b"wide-pipeline-domain").as_bytes();
    let mut before = Cell::with_balance([7u8; 32], token_id, balance);
    before.mode = CellMode::Sovereign;
    let mut after = before.clone();
    after.state.set_balance(balance - amount);
    // The EffectVM transfer ticks the per-cell nonce (the deployed apply); the after-state the
    // producer proves carries the ticked nonce, so the AFTER 8-felt commit binds it.
    let _ = after.state.increment_nonce();
    (before, after)
}

/// Where the 16 wide PIs start (the wide descriptor's host piCount — 46 for the transfer-shape
/// cohort, the rotated `ROT_PI_COUNT`; PIs 46..53 = BEFORE 8-felt commit, 54..61 = AFTER 8-felt
/// commit). Post-Phase-C the v1 prefix grew 34→42, so the rotated prefix is 46 (= 42 + 4 commit
/// pins).
const WIDE_PI_BASE: usize = 46;

/// The chip-faithful 8-felt commit of a cell + turn-context (the executor's anchoring primitive).
fn cell_chip_commit8(cell: &Cell, ctx: &V9RotationContext) -> [BabyBear; 8] {
    let pre = compute_rotated_pre_limbs(cell, ctx);
    wire_commit_8_chip(&pre, ctx.iroot)
}

/// **CONTROL: the wide producer→executor pipeline PROVES + the anchored 16 wide PIs VERIFY.** The
/// sovereign transfer mints a wide proof; the executor anchors the 16 wide PIs to the trusted
/// before/after cell chip-commits and `verify_vm_descriptor2` accepts.
#[test]
fn wide_sovereign_pipeline_proves_and_anchored_verify_accepts() {
    let balance: i64 = 100_000;
    let amount: i64 = 100;
    let (before_cell, after_cell) = sovereign_transfer_cells(balance, amount);

    // The turn-context the rotated commitment absorbs (single-cell ledger, empty maps, empty
    // receipt-chain iroot) — the SAME context the sovereign producer supplies.
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_hashes: Vec<[u8; 32]> = vec![];
    let mut ctx_ledger = Ledger::new();
    let _ = ctx_ledger.insert_cell(before_cell.clone());

    let before_w = rw::produce(&before_cell, &ctx_ledger, &nullifier_root, &commitments_root, &receipt_hashes);
    let after_w = rw::produce(&after_cell, &ctx_ledger, &nullifier_root, &commitments_root, &receipt_hashes);

    let initial_vm_state = CellState::with_capability_root_and_record_digest(
        balance as u64,
        before_cell.state.nonce() as u32,
        dregg_cell::compute_canonical_capability_root_felt(&before_cell.capabilities),
        dregg_cell::compute_authority_digest_felt(&before_cell),
    );
    let effects = vec![VmEffect::Transfer { amount: amount as u64, direction: 1 }];
    let caveat = dregg_circuit::effect_vm::trace_rotated::transfer_caveat_manifest();

    // -- PRODUCER LEG: mint a real wide proof + the 16 published wide PIs. --
    let (proof, producer_dpis) =
        prove_effect_vm_rotated_wide(&initial_vm_state, &effects, &before_w, &after_w, &caveat, None)
            .expect("wide sovereign producer must mint a proof");

    // Resolve the wide descriptor (the executor pulls the same WIDE registry).
    let json = WIDE_REGISTRY_STAGED_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some("transferVmDescriptor2R24") {
                let _ = it.next();
                it.next()
            } else {
                None
            }
        })
        .expect("wide transfer member");
    let desc = parse_vm_descriptor2(json).expect("wide transfer descriptor parses");
    assert_eq!(producer_dpis.len(), desc.public_input_count, "wide PI count");

    // -- EXECUTOR LEG: anchor the 16 wide PIs to the TRUSTED before/after cell chip-commits (the wide
    //    analog of the live `dpis[42]/[43]` override — the 1-felt-retire the flip performs). --
    let before_ctx = V9RotationContext {
        cells_root: before_w.pre_limbs[0],
        nullifier_root,
        commitments_root,
        iroot: before_w.iroot,
    };
    let after_ctx = V9RotationContext {
        cells_root: after_w.pre_limbs[0],
        nullifier_root,
        commitments_root,
        iroot: after_w.iroot,
    };
    let trusted_before8 = cell_chip_commit8(&before_cell, &before_ctx);
    let trusted_after8 = cell_chip_commit8(&after_cell, &after_ctx);

    // The executor reconstructs the published 16 wide PIs from ITS trusted commits (NOT the
    // producer's claim) — a forged producer commit cannot survive this override.
    let mut anchored = producer_dpis.clone();
    for j in 0..8 {
        anchored[WIDE_PI_BASE + j] = trusted_before8[j];
        anchored[WIDE_PI_BASE + 8 + j] = trusted_after8[j];
    }

    // The trusted commits MUST equal the producer's published ones (the honest pipeline coheres):
    // BEFORE (the stored sovereign state) and AFTER (the EffectVM-applied post-state) both anchor.
    assert_eq!(
        anchored, producer_dpis,
        "the trusted chip-8-felt commits equal the producer's published 16 wide PIs (honest pipeline)"
    );
    verify_vm_descriptor2(&desc, &proof, &anchored)
        .expect("the wide proof VERIFIES against the executor-anchored 16 wide PIs");

    eprintln!(
        "WIDE PIPELINE GREEN: the sovereign producer minted an 8-felt wide proof, the executor \
         anchored the 16 wide PIs to the trusted cell chip-commits (wire_commit_8_chip), and \
         verify_vm_descriptor2 ACCEPTED — the flag-day legs cohere end-to-end."
    );
}

/// **THE FORGERY TOOTH: a forged trusted BEFORE commit is REJECTED.** If the executor anchors the
/// wide PIs to a commit the proof's bound carrier does NOT carry (a near-collision a 1-felt commit
/// could pass), `verify_vm_descriptor2` is UNSAT — the 8-felt commit binds, no executor reconstruction.
#[test]
fn wide_sovereign_forged_anchor_is_rejected() {
    let (before_cell, after_cell) = sovereign_transfer_cells(100_000, 100);
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let mut ctx_ledger = Ledger::new();
    let _ = ctx_ledger.insert_cell(before_cell.clone());
    let before_w = rw::produce(&before_cell, &ctx_ledger, &nullifier_root, &commitments_root, &[]);
    let after_w = rw::produce(&after_cell, &ctx_ledger, &nullifier_root, &commitments_root, &[]);

    let initial_vm_state = CellState::with_capability_root_and_record_digest(
        100_000u64,
        before_cell.state.nonce() as u32,
        dregg_cell::compute_canonical_capability_root_felt(&before_cell.capabilities),
        dregg_cell::compute_authority_digest_felt(&before_cell),
    );
    let effects = vec![VmEffect::Transfer { amount: 100, direction: 1 }];
    let caveat = dregg_circuit::effect_vm::trace_rotated::transfer_caveat_manifest();
    let (proof, producer_dpis) =
        prove_effect_vm_rotated_wide(&initial_vm_state, &effects, &before_w, &after_w, &caveat, None)
            .expect("wide sovereign producer must mint a proof");

    let json = WIDE_REGISTRY_STAGED_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some("transferVmDescriptor2R24") {
                let _ = it.next();
                it.next()
            } else {
                None
            }
        })
        .expect("wide transfer member");
    let desc = parse_vm_descriptor2(json).expect("wide transfer descriptor parses");

    // FORGE: bump one felt of the BEFORE commit (a state the proof's carrier does not carry).
    let mut forged = producer_dpis.clone();
    forged[WIDE_PI_BASE] = forged[WIDE_PI_BASE] + BabyBear::new(0x9999);
    assert!(
        verify_vm_descriptor2(&desc, &proof, &forged).is_err(),
        "a forged BEFORE 8-felt commit PI MUST be REJECTED — the wide commit binds the full state \
         (verify_vm_descriptor2 ALONE, no executor reconstruction)"
    );
    eprintln!("WIDE FORGERY TOOTH BITES: a forged 8-felt commit PI is UNSAT.");
}
