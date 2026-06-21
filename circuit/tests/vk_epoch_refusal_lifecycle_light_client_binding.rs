//! # THE VK-EPOCH FAMILY-2 DISCRIMINATOR — Refusal + the lifecycle PAYLOAD.
//!
//! ## What this measures (`docs/VK-EPOCH-PLAN.md`, STAGE B/C, families 2)
//!
//! Family 1 (`vk_epoch_perms_vk_light_client_binding.rs`, commit d58545a5f) PROVED that
//! setPermissions / setVK are FORCED-ON-WIRE: their in-circuit `permsVKWeldGate` welds the
//! committed AFTER perms/vk sub-limb to `param0`, AND `param0` is the post-value bound into the
//! PI-anchored `effects_hash` (a value a ledgerless light client independently knows from the
//! effect). So a perms-/vk-only forged post-cell is UNSAT through `verify_vm_descriptor2` ALONE,
//! NO off-cell `apply_effect_to_cell` re-derivation. The off-cell anchor became redundant for them.
//!
//! Family 2 — Refusal + the lifecycle PAYLOAD — is the HONEST CONTRAST. These effects ride a
//! DIFFERENT in-circuit primitive: the record-pin (`rotateV3WithRecordPin off d`), which welds the
//! committed AFTER limb (`B_RECORD_DIGEST = 24` for refusal's `fields_root` audit;
//! `B_LIFECYCLE = 29` for the lifecycle payload) to rotated PI 46. The decisive structural fact
//! (`trace_rotated.rs:388-391`, the in-code admission):
//!
//!     "We push the honest post value (read from the LAST row's AFTER block ...) so the honest
//!      trace satisfies it; the VERIFIER recomputes PI[46] from the committed pre-state + the
//!      effect, so a forgery cannot match it."
//!
//! That "verifier recomputes PI[46]" runs ONLY in the full-node off-cell anchor
//! (`turn::executor::proof_verify.rs` step 6b, `apply_effect_to_cell`). On the LIGHT-CLIENT path
//! (`verify_vm_descriptor2` ALONE — what `sdk::full_turn_proof::verify_effect_vm_rotated_with_cutover`
//! runs), PI 46 is a PRODUCER-SUPPLIED free PI; `generate_rotated_effect_vm_trace` fills it from the
//! producer's OWN after-witness AFTER limb (`dpis.push(last[AFTER_BASE + off])`,
//! `trace_rotated.rs:394`). So for ANY self-consistent forged post-cell, the record-pin is
//! satisfied vacuously: committed AFTER limb == PI 46 holds BY CONSTRUCTION.
//!
//! WHY there is no perms/VK-style weld for these: a weld needs an in-circuit DECLARED column that
//! equals the post-value AND is a light-client-known function of the effect. For refusal the
//! post-value is `fields_root_felt(fields_root')` — a Merkle-MAP root that depends on the
//! pre-`fields_root` (an insert, not a deterministic single felt); refusal's deployed params are
//! `param0 = target`, `param1 = reason_hash` — NEITHER is the post-`fields_root` (Lean `refusalV3`
//! doc-comment). For the lifecycle payload the post-value is `lifecycle_felt` folding the disc +
//! `reason_hash`/`death_certificate_hash` + `sealed_at`/`destroyed_at` — and `sealed_at` is the HOST
//! `block_height` (`rotation_witness.rs:570-575`), NOT carried by any effect param at all, so the
//! light client cannot reconstruct it from the effect. (The lifecycle DISC at limb 32 IS forced
//! in-circuit by `rotateV3WithDiscGate` — a frozen seal / resurrection IS light-client-rejected;
//! it is only the OPAQUE payload felt at limb 29 that rides the anchor.)
//!
//! ## The discriminator (both poles, GREEN = it asserts the CURRENT TRUTH)
//!
//! Run through `prove_vm_descriptor2` / `verify_vm_descriptor2` ALONE (the light-client path; no
//! `apply_effect_to_cell`). For each effect:
//!
//!   * POSITIVE (no downgrade): an HONEST refusal / cellSeal turn proves + verifies.
//!   * RESIDUAL (the contrast vs family 1): a post-cell forged to differ ONLY in the
//!     refusal-audit / lifecycle payload — a SELF-CONSISTENT post-cell whose own AFTER limb the
//!     producer also publishes as PI 46 — STILL proves + verifies through the light-client path
//!     ALONE. The record-pin does NOT bite (unlike family-1's weld), because PI 46 is
//!     producer-free here. This is the off-cell-anchor residual the VK-epoch must convert to a
//!     genuine in-circuit force (STAGE B/C — a verifier-anchored declared-payload column, the
//!     genuinely-new primitive, like the deleg-tree column was for refresh).
//!
//! This is the model-finds-the-bug artifact: it NAMES the residual precisely and guards against a
//! false "refusal/lifecycle-payload is forced-on-wire" claim. The full-node leg IS sound (the
//! off-cell anchor bites); these two are full-node-FORCED but NOT light-client-FORCED.
//!
//! Gated on `prover`. Run with
//! `cargo test -p dregg-circuit --features prover --test vk_epoch_refusal_lifecycle_light_client_binding -- --nocapture`.

#![cfg(feature = "prover")]

use dregg_cell::{Cell, Ledger};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::{
    AFTER_BASE, B_LIFECYCLE, B_RECORD_DIGEST, ROT_WIDTH, RotatedBlockWitness, empty_caveat_manifest,
    generate_rotated_effect_vm_trace, rotated_descriptor_name_for_effect,
};
use dregg_circuit::effect_vm::{CellState, Effect, bytes32_to_8_limbs};
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

/// The producer's before-cell (the pre-state the turn opens over).
fn producer_cell(balance: i64, nonce: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("37 pre-iroot limbs")
}

fn h8(b: &[u8; 32]) -> [BabyBear; 8] {
    bytes32_to_8_limbs(blake3::hash(b).as_bytes())
}

/// `true` iff `prove_vm_descriptor2` + `verify_vm_descriptor2` ACCEPT (the light-client path).
/// `false` iff `prove` refuses (Err/panic) or the proof fails to verify.
fn accepts(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    dpis: &[BabyBear],
    mem_boundary: &MemBoundaryWitness,
    map_heaps: &[Vec<dregg_circuit::heap_root::HeapLeaf>],
) -> bool {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, dpis, mem_boundary, map_heaps).ok()?;
        verify_vm_descriptor2(desc, &proof, dpis).ok()
    }));
    matches!(r, Ok(Some(())))
}

/// **REFUSAL is FULL-NODE-FORCED but NOT LIGHT-CLIENT-FORCED (the residual).** An honest refusal
/// proves + verifies; a post-cell forged to differ ONLY in the refusal-`fields_root` audit (a
/// self-consistent post-cell whose own AFTER record-digest limb the producer also publishes as PI
/// 46) STILL proves + verifies through `verify_vm_descriptor2` ALONE — the record-pin does NOT bite
/// on the light-client path (PI 46 is producer-free; the off-cell `apply_effect_to_cell` anchor that
/// recomputes it runs ONLY on the full node). This is the off-cell-anchor residual.
#[test]
fn refusal_is_full_node_forced_not_light_client_forced_anchor_disabled() {
    let balance: i64 = 50_000;

    // The HONEST refusal: the kernel effect writes the REFUSAL_AUDIT_EXT_KEY audit into the cell's
    // `fields_root` (which `compute_authority_digest_felt` folds into the AFTER record-digest limb).
    let before_cell = producer_cell(balance, 0);
    let cell_id = before_cell.id();
    let kernel_effect = dregg_turn::Effect::Refusal {
        cell: cell_id,
        offered_action_commitment: [11u8; 32],
        refusal_reason: dregg_turn::action::RefusalReason::Declined,
        proof_witness_index: 0,
    };

    // The rotated descriptor is the VM-effect refusal cohort member.
    let vm_effect = Effect::Refusal {
        target: h8(cell_id.as_bytes()),
        reason_hash: bytes32_to_8_limbs(&[0u8; 32]),
    };
    let name = rotated_descriptor_name_for_effect(&vm_effect)
        .expect("Refusal is a rotated cohort member");
    assert_eq!(name, "refusalVmDescriptor2R24");
    let desc =
        parse_vm_descriptor2(rotated_descriptor_json(name)).expect("rotated refusal descriptor parses");
    assert_eq!(
        desc.public_input_count, 47,
        "refusal carries the appended record-forcing pin (47 PIs)"
    );

    let st = CellState::new(balance as u64, 0);
    let effects = vec![vm_effect];

    let mut honest_after = producer_cell(balance, 0);
    rw::apply_effect_to_cell(&mut honest_after, &cell_id, &kernel_effect, 100);

    let mut ledger = Ledger::new();
    ledger.insert_cell(honest_after.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];

    let before_w =
        rw::produce(&before_cell, &Ledger::new(), &nullifier_root, &commitments_root, &receipt_log);
    let after_w =
        rw::produce(&honest_after, &ledger, &nullifier_root, &commitments_root, &receipt_log);

    // The refusal audit MOVED the AFTER record-digest limb (anti-vacuity).
    assert_ne!(
        before_w.pre_limbs[B_RECORD_DIGEST], after_w.pre_limbs[B_RECORD_DIGEST],
        "the refusal audit MOVES the AFTER record-digest limb (a genuine write)"
    );

    let caveat = empty_caveat_manifest();
    let (trace, dpis) =
        generate_rotated_effect_vm_trace(&st, &effects, &bridge(&before_w), &bridge(&after_w), &caveat)
            .expect("live rotated generator must produce a refusal trace + 47 PIs");
    assert_eq!(trace[0].len(), ROT_WIDTH, "rotated trace width");

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    // POSITIVE TOOTH (no downgrade): the honest refusal proves + verifies on the light-client path.
    assert!(
        accepts(&desc, &trace, &dpis, &mem_boundary, &map_heaps),
        "NO DOWNGRADE: the honest refusal must prove + verify through the light-client path"
    );

    // RESIDUAL TOOTH (the contrast vs family 1): a post-cell forged to differ ONLY in the refusal
    // audit. We build a SELF-CONSISTENT forged after-cell (a DIFFERENT audit payload), regenerate
    // its witness, and let the generator publish PI 46 from the forged AFTER limb (exactly as the
    // honest path does). The record-pin (committed AFTER == PI 46) is satisfied BY CONSTRUCTION, so
    // the light-client path ACCEPTS the forgery — the anchor that would recompute PI 46 from the
    // pre-cell + effect runs ONLY on the full node.
    let forged_kernel = dregg_turn::Effect::Refusal {
        cell: cell_id,
        offered_action_commitment: [99u8; 32], // a DIFFERENT audit input
        refusal_reason: dregg_turn::action::RefusalReason::NoAuthority,
        proof_witness_index: 0,
    };
    let mut forged_after = producer_cell(balance, 0);
    rw::apply_effect_to_cell(&mut forged_after, &cell_id, &forged_kernel, 100);
    let mut forged_ledger = Ledger::new();
    forged_ledger.insert_cell(forged_after.clone()).unwrap();
    let forged_after_w =
        rw::produce(&forged_after, &forged_ledger, &nullifier_root, &commitments_root, &receipt_log);

    assert_ne!(
        forged_after_w.pre_limbs[B_RECORD_DIGEST], after_w.pre_limbs[B_RECORD_DIGEST],
        "the forged audit folds to a DISTINCT AFTER record-digest limb (else the contrast is vacuous)"
    );

    let (forged_trace, forged_dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects, // SAME declared VM effect (params unchanged) — the forge is in the post-cell payload
        &bridge(&before_w),
        &bridge(&forged_after_w),
        &caveat,
    )
    .expect("generator builds the forged-audit trace");

    // The smoking gun: the committed AFTER record-digest limb is the FORGED value, AND the generator
    // publishes PI 46 from that SAME forged limb (producer-free) — so the record-pin holds vacuously.
    let last = &forged_trace[forged_trace.len() - 1];
    assert_eq!(
        last[AFTER_BASE + B_RECORD_DIGEST],
        forged_after_w.pre_limbs[B_RECORD_DIGEST],
        "the forged AFTER record-digest limb carries the forged audit"
    );

    assert!(
        accepts(&desc, &forged_trace, &forged_dpis, &mem_boundary, &map_heaps),
        "RESIDUAL (full-node-forced, NOT light-client-forced): a refusal forged to differ ONLY in \
         the `fields_root` audit — a self-consistent post-cell whose own AFTER record-digest the \
         producer publishes as PI 46 — STILL proves + verifies through verify_vm_descriptor2 ALONE. \
         The record-pin does NOT bite on the light-client path (contrast family-1's weld). The \
         off-cell apply_effect_to_cell anchor (full-node only) is the sole binding today. This is \
         the STAGE-B residual: refusal needs a verifier-anchored declared-payload column (a new \
         primitive) to become light-client-forced."
    );

    eprintln!(
        "VK-EPOCH FAMILY-2 refusal: FULL-NODE-FORCED (the off-cell anchor bites) but NOT \
         LIGHT-CLIENT-FORCED — a forged-audit post-cell is ACCEPTED through verify_vm_descriptor2 \
         ALONE; PI 46 is producer-free, the record-pin holds vacuously. The residual the epoch \
         must convert (STAGE B)."
    );
}

/// **The LIFECYCLE PAYLOAD is FULL-NODE-FORCED but NOT LIGHT-CLIENT-FORCED (the residual).** The
/// lifecycle DISC (limb 32) IS forced in-circuit (a frozen seal is rejected) — that is light-client
/// safe and NOT the subject here. This proves the OPAQUE payload felt (limb 29:
/// `reason_hash`/`sealed_at` for cellSeal, `death_certificate_hash`/`destroyed_at` for cellDestroy)
/// rides the off-cell anchor: a cellSeal forged to differ ONLY in the sealing payload STILL proves +
/// verifies through the light-client path ALONE.
#[test]
fn lifecycle_payload_is_full_node_forced_not_light_client_forced_anchor_disabled() {
    let balance: i64 = 50_000;

    let before_cell = producer_cell(balance, 0);
    let cell_id = before_cell.id();
    // The HONEST cellSeal: the kernel `c.seal(reason, block_height)` writes
    // `Sealed { reason_hash, sealed_at }` — `lifecycle_felt` folds both into the AFTER limb 29.
    let honest_reason = [22u8; 32];
    let honest_kernel = dregg_turn::Effect::CellSeal {
        target: cell_id,
        reason: honest_reason,
    };
    let vm_effect = Effect::CellSeal {
        target: h8(cell_id.as_bytes()),
        reason_hash: h8(&honest_reason),
    };
    let name = rotated_descriptor_name_for_effect(&vm_effect)
        .expect("CellSeal is a rotated cohort member");
    assert_eq!(name, "cellSealVmDescriptor2R24");
    let desc =
        parse_vm_descriptor2(rotated_descriptor_json(name)).expect("rotated cellSeal descriptor parses");
    assert_eq!(
        desc.public_input_count, 47,
        "cellSeal carries the appended lifecycle-forcing pin (47 PIs)"
    );

    let st = CellState::new(balance as u64, 0);
    let effects = vec![vm_effect];

    let mut honest_after = producer_cell(balance, 0);
    rw::apply_effect_to_cell(&mut honest_after, &cell_id, &honest_kernel, 100);

    let mut ledger = Ledger::new();
    ledger.insert_cell(honest_after.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];

    let before_w =
        rw::produce(&before_cell, &Ledger::new(), &nullifier_root, &commitments_root, &receipt_log);
    let after_w =
        rw::produce(&honest_after, &ledger, &nullifier_root, &commitments_root, &receipt_log);

    assert_ne!(
        before_w.pre_limbs[B_LIFECYCLE], after_w.pre_limbs[B_LIFECYCLE],
        "the seal MOVES the AFTER lifecycle limb (Live -> Sealed)"
    );

    let caveat = empty_caveat_manifest();
    let (trace, dpis) =
        generate_rotated_effect_vm_trace(&st, &effects, &bridge(&before_w), &bridge(&after_w), &caveat)
            .expect("live rotated generator must produce a cellSeal trace + 47 PIs");

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    // POSITIVE TOOTH (no downgrade).
    assert!(
        accepts(&desc, &trace, &dpis, &mem_boundary, &map_heaps),
        "NO DOWNGRADE: the honest cellSeal must prove + verify through the light-client path"
    );

    // RESIDUAL TOOTH: forge ONLY the sealing PAYLOAD (a different reason_hash; the DISC stays
    // Sealed, so the in-circuit disc gate is satisfied honestly — the forge is in the OPAQUE payload
    // felt the disc gate does NOT cover). A self-consistent forged post-cell whose own AFTER limb 29
    // the producer publishes as PI 46 STILL proves + verifies on the light-client path.
    let forged_reason = [44u8; 32]; // a DIFFERENT sealing rationale (same Sealed disc)
    let forged_kernel = dregg_turn::Effect::CellSeal {
        target: cell_id,
        reason: forged_reason,
    };
    let mut forged_after = producer_cell(balance, 0);
    rw::apply_effect_to_cell(&mut forged_after, &cell_id, &forged_kernel, 100);
    let mut forged_ledger = Ledger::new();
    forged_ledger.insert_cell(forged_after.clone()).unwrap();
    let forged_after_w =
        rw::produce(&forged_after, &forged_ledger, &nullifier_root, &commitments_root, &receipt_log);

    assert_ne!(
        forged_after_w.pre_limbs[B_LIFECYCLE], after_w.pre_limbs[B_LIFECYCLE],
        "the forged sealing payload folds to a DISTINCT AFTER lifecycle limb (else the contrast is vacuous)"
    );

    let (forged_trace, forged_dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&forged_after_w),
        &caveat,
    )
    .expect("generator builds the forged-payload trace");

    assert!(
        accepts(&desc, &forged_trace, &forged_dpis, &mem_boundary, &map_heaps),
        "RESIDUAL (full-node-forced, NOT light-client-forced): a cellSeal forged to differ ONLY in \
         the sealing PAYLOAD (reason_hash/sealed_at — the disc stays Sealed) STILL proves + verifies \
         through verify_vm_descriptor2 ALONE. The lifecycle DISC (limb 32) IS forced in-circuit, but \
         the OPAQUE payload felt (limb 29) rides the off-cell anchor (full-node only). This is the \
         STAGE-C residual: the payload (reason_hash/deathCert/sealed_at) needs a verifier-anchored \
         declared-payload column to become light-client-forced — and sealed_at = host block_height \
         is not even an effect param, so the new primitive must PI-anchor the host height."
    );

    eprintln!(
        "VK-EPOCH FAMILY-2 lifecycle payload: the DISC is light-client-forced, but the payload felt \
         (limb 29) is FULL-NODE-FORCED only — a forged-payload post-cell is ACCEPTED through \
         verify_vm_descriptor2 ALONE. The residual the epoch must convert (STAGE C)."
    );
}
