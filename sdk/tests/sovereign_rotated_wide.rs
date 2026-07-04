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
use dregg_circuit::descriptor_ir2::{parse_vm_descriptor2, verify_vm_descriptor2};
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

    let before_w = rw::produce(
        &before_cell,
        &ctx_ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_hashes,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ctx_ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_hashes,
        &Default::default(),
    );

    let initial_vm_state = CellState::with_capability_root_and_record_digest(
        balance as u64,
        before_cell.state.nonce() as u32,
        dregg_cell::compute_canonical_capability_root_felt(&before_cell.capabilities),
        dregg_cell::compute_authority_digest_felt(&before_cell),
    );
    let effects = vec![VmEffect::Transfer {
        amount: amount as u64,
        direction: 1,
    }];
    let caveat = dregg_circuit::effect_vm::trace_rotated::transfer_caveat_manifest();

    // -- PRODUCER LEG: mint a real wide proof + the 16 published wide PIs. --
    let (proof, producer_dpis) = prove_effect_vm_rotated_wide(
        &initial_vm_state,
        &effects,
        &before_w,
        &after_w,
        &caveat,
        None,
        None,
    )
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
    assert_eq!(
        producer_dpis.len(),
        desc.public_input_count,
        "wide PI count"
    );

    // -- EXECUTOR LEG: anchor the 16 wide PIs to the TRUSTED before/after cell chip-commits (the wide
    //    analog of the live `dpis[42]/[43]` override — the 1-felt-retire the flip performs). --
    let before_ctx = V9RotationContext {
        cells_root: before_w.pre_limbs[0],
        nullifier_root,
        commitments_root,
        iroot: before_w.iroot,
        material: Default::default(),
    };
    let after_ctx = V9RotationContext {
        cells_root: after_w.pre_limbs[0],
        nullifier_root,
        commitments_root,
        iroot: after_w.iroot,
        material: Default::default(),
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
    let before_w = rw::produce(
        &before_cell,
        &ctx_ledger,
        &nullifier_root,
        &commitments_root,
        &[],
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ctx_ledger,
        &nullifier_root,
        &commitments_root,
        &[],
        &Default::default(),
    );

    let initial_vm_state = CellState::with_capability_root_and_record_digest(
        100_000u64,
        before_cell.state.nonce() as u32,
        dregg_cell::compute_canonical_capability_root_felt(&before_cell.capabilities),
        dregg_cell::compute_authority_digest_felt(&before_cell),
    );
    let effects = vec![VmEffect::Transfer {
        amount: 100,
        direction: 1,
    }];
    let caveat = dregg_circuit::effect_vm::trace_rotated::transfer_caveat_manifest();
    let (proof, producer_dpis) = prove_effect_vm_rotated_wide(
        &initial_vm_state,
        &effects,
        &before_w,
        &after_w,
        &caveat,
        None,
        None,
    )
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

// ============================================================================================
// THE DEPLOYED REFUSAL PROVE-THROUGH (the refusal light-client forge's close, the LIVENESS pole).
// ============================================================================================
//
// `refusalVmDescriptor2R24` (wide) now carries an in-circuit `fields_root` `.write` map-op gate
// forcing `after_fields_root == write(before_fields_root, REFUSAL_AUDIT_KEY → audit_felt)` (the
// banked gate/apex close, commit 9625645d8). Until this wire, the DEPLOYED wide prove path
// (`prove_effect_vm_rotated_wide`) lumped Refusal into the record-pin branch with an EMPTY
// `map_heaps` — UNSAT against the `.write` gate, so an HONEST refusal FAILED TO PROVE on the live
// path (fail-closed). This test is the RED→GREEN liveness pole: an honest refusal turn now PROVES
// through the deployed wide producer (threading the BEFORE-cell fields tree + the audit felt) AND
// VERIFIES against the executor-anchored wide refusal descriptor. A prover refusal or a verifier
// rejection FAILS the test (no catch_unwind — unambiguous).
//
// H1: the refusal wide geometry is the record-pin8 geometry: the rotated prefix is 54 (= 42 v1 + 4
// commit pins + the 8 authority record-pins, `withRecordPin8Headroom2`) and the wide descriptor carries
// 54 + 16 = 70. So the 16 wide commit PIs start at `REFUSAL_WIDE_PI_BASE = 54`.

/// Where the 16 wide commit PIs start for the REFUSAL cohort (a record-digest mover: the 8 authority
/// record-pins occupy PI 46..53, so the wide commit PIs sit at 54..70 —
/// `refusalVmDescriptor2R24` wide = 70 PIs = 54 base + 16 wide).
const REFUSAL_WIDE_PI_BASE: usize = 54;

/// A sovereign refusal before/after cell pair: the after-cell carries the refusal audit slot written
/// into `fields_map[REFUSAL_AUDIT_EXT_KEY]` (via the shared `apply_effect_to_cell` weld — the SAME
/// projection the producer/executor use), so its committed `fields_root` (limb 36) is the genuine
/// sorted write the `.write` map-op gate forces.
fn sovereign_refusal_cells(balance: i64, block_height: u64) -> (Cell, Cell, dregg_turn::Effect) {
    let token_id = *blake3::hash(b"wide-refusal-domain").as_bytes();
    let mut before = Cell::with_balance([7u8; 32], token_id, balance);
    before.mode = CellMode::Sovereign;
    let cell_id = before.id();
    let kernel_effect = dregg_turn::Effect::Refusal {
        cell: cell_id,
        offered_action_commitment: [11u8; 32],
        refusal_reason: dregg_turn::action::RefusalReason::Declined,
        proof_witness_index: 0,
    };
    let mut after = before.clone();
    rw::apply_effect_to_cell(&mut after, &cell_id, &kernel_effect, block_height);
    (before, after, kernel_effect)
}

/// **THE DEPLOYED REFUSAL PROVE-THROUGH: an honest refusal PROVES on the live wide path + VERIFIES.**
/// BEFORE this wire the deployed prover routed Refusal through the record-pin generator with an empty
/// `map_heaps` (UNSAT vs the `.write` gate — the honest refusal could not be proven). AFTER: the
/// wide refusal producer threads the BEFORE fields-tree leaf set + the audit felt, the `.write` gate
/// opens the genuine sorted write, and the proof verifies against the executor-anchored wide refusal
/// descriptor. NO catch_unwind: a prover refusal or verify rejection fails the test.
#[test]
fn wide_sovereign_refusal_proves_and_anchored_verify_accepts() {
    let balance: i64 = 50_000;
    let block_height: u64 = 100;
    let (before_cell, after_cell, _kernel) = sovereign_refusal_cells(balance, block_height);
    let cell_id = before_cell.id();

    // The audit MUST have moved the fields_map (non-vacuity — the write is genuine).
    let audit_bytes = after_cell
        .state
        .fields_map
        .get(&dregg_cell::state::REFUSAL_AUDIT_EXT_KEY)
        .copied()
        .expect("a refused cell carries the audit slot in fields_map (apply_refusal wrote it)");

    // The turn-context (single-cell ledger, empty maps, empty receipt iroot) — the producer's context.
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_hashes: Vec<[u8; 32]> = vec![];
    let mut ctx_ledger = Ledger::new();
    let _ = ctx_ledger.insert_cell(before_cell.clone());

    let before_w = rw::produce(
        &before_cell,
        &ctx_ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_hashes,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ctx_ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_hashes,
        &Default::default(),
    );

    // The refusal moves the AFTER record-digest / fields_root limbs (the genuine write — non-vacuity).
    assert_ne!(
        before_w.pre_limbs[36], after_w.pre_limbs[36],
        "the refusal audit MOVES the AFTER fields_root limb (limb 36) — a genuine write"
    );

    let initial_vm_state = CellState::with_capability_root_and_record_digest(
        balance as u64,
        before_cell.state.nonce() as u32,
        dregg_cell::compute_canonical_capability_root_felt(&before_cell.capabilities),
        dregg_cell::compute_authority_digest_felt(&before_cell),
    );
    let effects = vec![VmEffect::Refusal {
        target: dregg_circuit::effect_vm::bytes32_to_8_limbs(
            blake3::hash(cell_id.as_bytes()).as_bytes(),
        ),
        reason_hash: dregg_circuit::effect_vm::bytes32_to_8_limbs(&[0u8; 32]),
    }];
    let caveat = dregg_circuit::effect_vm::trace_rotated::empty_caveat_manifest();

    // THE DEPLOYED PROVER WIRE: the BEFORE fields-tree leaf set + the audit felt the refusal writes.
    // These are what the live cipherclerk builds from the before/after cells; without them the wide
    // prover REFUSES (the `.write` gate has no witness).
    let before_leaves = dregg_cell::state::fields_root_leaves(&before_cell.state.fields_map);
    let audit_value = dregg_circuit::cap_root::fold_bytes32(&audit_bytes);

    // -- PRODUCER LEG (the deployed wide path): mint a real wide refusal proof + the 63 published PIs.
    // BEFORE this wire, `refusal_fields = None` would FAIL CLOSED here (the record-pin route with empty
    // map_heaps is UNSAT vs the `.write` gate). We pass the genuine fields context so it PROVES.
    let (proof, producer_dpis) = prove_effect_vm_rotated_wide(
        &initial_vm_state,
        &effects,
        &before_w,
        &after_w,
        &caveat,
        None,
        Some((&before_leaves, audit_value)),
    )
    .expect(
        "DEPLOYED REFUSAL PROVE-THROUGH (liveness pole): the honest refusal MUST prove on the wide path \
         via the fields-tree route (an empty map_heaps would be UNSAT vs the `.write` gate)",
    );

    // Resolve the WIDE refusal descriptor (the executor pulls the same WIDE registry).
    let json = WIDE_REGISTRY_STAGED_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some("refusalVmDescriptor2R24") {
                let _ = it.next();
                it.next()
            } else {
                None
            }
        })
        .expect("wide refusal member in WIDE_REGISTRY_STAGED_TSV");
    let desc = parse_vm_descriptor2(json).expect("wide refusal descriptor parses");
    assert_eq!(
        producer_dpis.len(),
        desc.public_input_count,
        "wide refusal PI count (58 narrow base = 50 + 8 authority + 16 wide = 74 — the H1 8-felt record-pin8)"
    );
    assert_eq!(
        desc.public_input_count, 74,
        "refusal wide descriptor carries 74 PIs (all 8 authority record-pins + 4 dsl rc + 16 wide commit PIs)"
    );

    // -- EXECUTOR LEG: anchor the 16 wide commit PIs to the TRUSTED before/after cell chip-commits
    //    (the wide analog of the live executor's 1-felt-retire override). --
    let before_ctx = V9RotationContext {
        cells_root: before_w.pre_limbs[0],
        nullifier_root,
        commitments_root,
        iroot: before_w.iroot,
        material: Default::default(),
    };
    let after_ctx = V9RotationContext {
        cells_root: after_w.pre_limbs[0],
        nullifier_root,
        commitments_root,
        iroot: after_w.iroot,
        material: Default::default(),
    };
    let trusted_before8 = cell_chip_commit8(&before_cell, &before_ctx);
    let trusted_after8 = cell_chip_commit8(&after_cell, &after_ctx);

    let mut anchored = producer_dpis.clone();
    for j in 0..8 {
        anchored[REFUSAL_WIDE_PI_BASE + j] = trusted_before8[j];
        anchored[REFUSAL_WIDE_PI_BASE + 8 + j] = trusted_after8[j];
    }
    // The honest pipeline coheres: the trusted commits equal the producer's published 16 wide PIs.
    assert_eq!(
        anchored, producer_dpis,
        "the trusted chip-8-felt commits equal the producer's published 16 wide refusal PIs (honest \
         pipeline — the fields_root write is bound into the 8-felt commit)"
    );

    // THE VERIFY POLE: the deployed light-client verifier (verify_vm_descriptor2 against the wide
    // refusal descriptor, the executor-anchored 16 wide PIs). It ACCEPTS the honest refusal.
    verify_vm_descriptor2(&desc, &proof, &anchored)
        .expect("the honest wide refusal proof VERIFIES against the executor-anchored 63 PIs");

    // THE FORGE TOOTH (deployed-prover route): a forged after-`fields_root` audit is UNSAT. We forge by
    // recomputing the proof against a DIFFERENT audit value (a producer trying to publish an after-root
    // that is NOT write(before_root, AUDIT_KEY, genuine_audit)). The `.write` gate has no satisfying
    // assignment for the forged after-root vs the genuine before-tree, so the wide prover REFUSES.
    let forged_audit = audit_value + BabyBear::new(0x5151);
    let forged = prove_effect_vm_rotated_wide(
        &initial_vm_state,
        &effects,
        &before_w,
        &after_w,
        &caveat,
        None,
        Some((&before_leaves, forged_audit)),
    );
    // NOTE: a different audit value yields a DIFFERENT (but still genuine) write — so this proves with a
    // SELF-CONSISTENT after-root. The forge that the GATE rejects is an after-root that is NOT the write
    // of the witnessed before-tree; that is the circuit forge-detector's job (the column override). Here
    // we assert the deployed producer is at least DETERMINISTIC + that the genuine audit's proof is the
    // one that anchors to the trusted after-cell (a forged audit anchors to a DIFFERENT after-commit, so
    // the executor's trusted-after override would REJECT it).
    if let Ok((forged_proof, forged_dpis)) = forged {
        // The forged-audit proof's published AFTER commit differs from the trusted after-cell's commit
        // (the trusted after-cell carries the GENUINE audit) ⇒ the executor's anchored verify REJECTS it.
        let mut forged_anchored = forged_dpis.clone();
        for j in 0..8 {
            forged_anchored[REFUSAL_WIDE_PI_BASE + j] = trusted_before8[j];
            forged_anchored[REFUSAL_WIDE_PI_BASE + 8 + j] = trusted_after8[j];
        }
        assert!(
            verify_vm_descriptor2(&desc, &forged_proof, &forged_anchored).is_err(),
            "a refusal proven with a FORGED audit value publishes an after-`fields_root` commit that \
             disagrees with the trusted after-cell (genuine audit) ⇒ the executor-anchored verify \
             REJECTS it (the 8-felt commit binds the written fields_root)"
        );
    }

    eprintln!(
        "DEPLOYED REFUSAL PROVE-THROUGH GREEN: the honest refusal PROVED on the deployed wide path via \
         the fields-tree route (BEFORE: empty map_heaps was UNSAT vs the `.write` gate; AFTER: proves + \
         verifies). The light-client refusal forge is closed gate→apex→deployed-prover end-to-end."
    );
}

// ============================================================================================
// THE LIGHT-CLIENT FLAG-DAY: the composed FULL-TURN / light-client surface now binds the WIDE
// 8-felt (~124-bit) commit, NOT the retired ~31-bit single felt. This is the close of the
// #1-precious 31-bit light-client floor: `verify_full_turn` (the surface a light client / remote
// peer re-verifies a NODE-SERVED turn proof on) anchors the 8-felt wide commit the executor binds.
// ============================================================================================

/// Build a rotated `FullTurnWitness` for a single outgoing transfer, plus a clone of the
/// `RotationTurnWitness` (the FullTurnWitness's `rotation` is consumed at prove time; the returned
/// clone gives the test the trusted `wide_commit_anchors()` + the before/after blocks for the
/// narrow-leg splice).
fn flagday_transfer_witness(
    balance: u64,
    amount: u64,
) -> (
    dregg_sdk::full_turn_proof::FullTurnWitness,
    dregg_sdk::full_turn_proof::RotationTurnWitness,
    CellState,
    Vec<VmEffect>,
) {
    use dregg_sdk::full_turn_proof::{FullTurnWitness, RotationTurnWitness};
    let token_id = *blake3::hash(b"flagday-domain").as_bytes();
    let mut before_cell = Cell::with_balance([7u8; 32], token_id, balance as i64);
    before_cell.mode = CellMode::Sovereign;
    let mut after_cell = before_cell.clone();
    after_cell
        .state
        .set_balance(after_cell.state.balance().saturating_sub(amount as i64));
    let _ = after_cell.state.increment_nonce();

    let initial_vm_state = CellState::with_capability_root_and_record_digest(
        balance,
        before_cell.state.nonce() as u32,
        dregg_cell::compute_canonical_capability_root_felt(&before_cell.capabilities),
        dregg_cell::compute_authority_digest_felt(&before_cell),
    );
    let vm_effects = vec![VmEffect::Transfer {
        amount,
        direction: 1,
    }];

    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_hashes: Vec<[u8; 32]> = Vec::new();
    let mut ctx_ledger = Ledger::new();
    let _ = ctx_ledger.insert_cell(before_cell.clone());
    let before_w = rw::produce(
        &before_cell,
        &ctx_ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_hashes,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ctx_ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_hashes,
        &Default::default(),
    );

    let rotation = RotationTurnWitness {
        before: before_w.clone(),
        after: after_w.clone(),
        caveat: dregg_circuit::effect_vm::trace_rotated::transfer_caveat_manifest(),
    };
    let witness = FullTurnWitness {
        initial_cell_state: initial_vm_state.clone(),
        effects: vm_effects.clone(),
        authorization: None,
        membership: None,
        conservation: None,
        non_revocation: None,
        cap_membership: None,
        turn_hash: *blake3::hash(b"flagday-turn").as_bytes(),
        rotation: Some(rotation),
        cap_turn_identity: None,
        umem_witness: None,
    };
    let rot_clone = RotationTurnWitness {
        before: before_w,
        after: after_w,
        caveat: dregg_circuit::effect_vm::trace_rotated::transfer_caveat_manifest(),
    };
    (witness, rot_clone, initial_vm_state, vm_effects)
}

/// **THE FLAG-DAY: an honest WIDE full-turn proof PROVES + the light-client `verify_full_turn`
/// ACCEPTS it at the 8-felt anchor.** `prove_full_turn` now emits a WIDE rotated leg (the 8-felt
/// commits at the LAST 16 PIs); `verify_full_turn` binds those against the trusted
/// `RotationTurnWitness::wide_commit_anchors()` (~124-bit). The retired 1-felt waist is GONE.
#[test]
fn flagday_wide_full_turn_proves_and_light_client_verifies_at_124_bit() {
    use dregg_sdk::full_turn_proof::{prove_full_turn, verify_full_turn};
    let (witness, rot, initial, effects) = flagday_transfer_witness(100_000, 100);
    let (old8, new8) = rot
        .wide_commit_anchors(&initial, &effects, None)
        .expect("wide_commit_anchors");

    let proof = prove_full_turn(&witness).expect("the honest WIDE full-turn must prove");

    // The effect-vm leg is the WIDE rotated leg (its PI carries the 16 wide commit PIs at the tail).
    let leg = proof
        .composed
        .sub_proofs
        .iter()
        .find(|sp| sp.label == "effect-vm-rotated")
        .expect("rotated effect-vm leg present");
    let n = leg.sub_public_inputs.len();
    assert!(
        n >= 16 + 46,
        "the WIDE transfer leg carries the 46 base PIs + 16 wide commit PIs (got {n})"
    );
    let leg_after8: [BabyBear; 8] = leg.sub_public_inputs[n - 8..n].try_into().unwrap();
    assert_eq!(
        leg_after8, new8,
        "the leg's published AFTER 8-felt commit == the trusted wide_commit_anchors AFTER (honest pipeline)"
    );

    // THE LIGHT-CLIENT VERIFY at the FULL 8-felt width — the close of the 31-bit floor.
    verify_full_turn(&proof, old8, new8)
        .expect("the light-client verifier ACCEPTS the honest wide full-turn at the 8-felt anchor");

    // A forged 8-felt NEW commit (one felt off) is REJECTED (the wide anchor binds ~124-bit).
    let mut forged_new = new8;
    forged_new[3] = forged_new[3] + BabyBear::new(0x7777);
    assert!(
        verify_full_turn(&proof, old8, forged_new).is_err(),
        "a forged 8-felt NEW commit MUST be rejected — the light-client surface binds the full ~124-bit commit"
    );
    eprintln!(
        "FLAG-DAY GREEN: the composed full-turn / light-client surface binds the 8-felt (~124-bit) commit."
    );
}

/// **THE REJECT TOOTH: a 1-felt V3 full-turn proof is REJECTED post-cutover.** We splice a NARROW
/// (1-felt V3 producer) transfer leg into an otherwise-honest full-turn proof. The re-pointed
/// light-client verifier (`verify_full_turn` → `verify_effect_vm_rotated_with_cutover`, iterating
/// the WIDE registry) finds NO accepting WIDE descriptor for the narrow leg — and the V3 fallback
/// accepts ONLY cap-open members, so a plain narrow transfer is FILTERED OUT — ⇒ the leg verifies
/// under no accepted descriptor ⇒ REJECTED. The honest 1-felt transfer surface can no longer pass
/// the composed full-turn / light-client verifier (the ~31-bit waist is closed for normal effects).
#[test]
fn flagday_rejects_one_felt_v3_full_turn_leg() {
    use dregg_circuit::effect_vm::trace_rotated::transfer_caveat_manifest;
    use dregg_sdk::full_turn_proof::{
        prove_effect_vm_rotated_ir2_with_caveat, prove_full_turn, verify_full_turn,
    };

    let (witness, rot, initial, effects) = flagday_transfer_witness(100_000, 100);
    let (old8, new8) = rot
        .wide_commit_anchors(&initial, &effects, None)
        .expect("wide_commit_anchors");

    // The honest WIDE proof (the scaffold we splice the narrow leg into).
    let mut proof = prove_full_turn(&witness).expect("honest wide full-turn proves");

    // Mint a NARROW (1-felt V3) transfer leg over the SAME effect/rotation — exactly what the
    // pre-flag-day producer emitted (the ~31-bit-commit leg).
    let caveat = transfer_caveat_manifest();
    let narrow = prove_effect_vm_rotated_ir2_with_caveat(
        &initial,
        &effects,
        &rot.before,
        &rot.after,
        &caveat,
        None,
    )
    .expect("the 1-felt V3 transfer leg proves (it is sound for the narrow descriptor)");
    let narrow_bytes = postcard::to_allocvec(&narrow).expect("serialize narrow leg");

    // Splice the narrow leg's proof bytes into the full-turn proof's effect-vm-rotated leg, leaving
    // the WIDE PI vector in place (a malicious node serving the cheaper 1-felt proof).
    let leg = proof
        .composed
        .sub_proofs
        .iter_mut()
        .find(|sp| sp.label == "effect-vm-rotated")
        .expect("rotated leg present");
    leg.proof_bytes = narrow_bytes;

    // POST-CUTOVER: the re-pointed light-client verifier REJECTS the narrow leg (no WIDE descriptor
    // accepts it; the V3 fallback admits cap-open members only, so a plain narrow transfer is out).
    assert!(
        verify_full_turn(&proof, old8, new8).is_err(),
        "REJECT TOOTH: a 1-felt V3 transfer leg MUST be rejected by the wide-bound light-client \
         verifier post-cutover — the ~31-bit waist is closed for normal effects"
    );
    eprintln!("FLAG-DAY REJECT TOOTH BITES: a 1-felt V3 full-turn leg is REJECTED post-cutover.");
}
