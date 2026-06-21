//! # THE VK-EPOCH FAMILY-2 DISCRIMINATOR — Refusal + the lifecycle PAYLOAD: the HONEST state.
//!
//! ## What this measures (`docs/VK-EPOCH-PLAN.md`, STAGE B/C, family 2 — STEP-0 ground truth)
//!
//! Family 1 (`vk_epoch_perms_vk_light_client_binding.rs`) is GENUINELY closed: setPermissions / setVK
//! carry an IN-CIRCUIT `permsVKWeldGate` welding the committed AFTER perms/vk sub-limb (limb 33/34) to
//! `param0`, and `param0` is the post-value bound into the PI-anchored `effects_hash` (a value a
//! ledgerless light client independently knows from the effect). So a perms-/vk-only forged post-cell is
//! UNSAT through `verify_vm_descriptor2` ALONE — NO verifier PI override, NO `apply_effect_to_cell`. The
//! deployed `setPermsVmDescriptor2R24` carries 107 constraints (the bare rotated 106 + the ONE weld);
//! the forge test rejects with `failed constraints = [the weld]`, the anchor not in the loop.
//!
//! Family 2 — Refusal + the lifecycle PAYLOAD — is the HONEST CONTRAST and is **STILL OPEN** for a
//! ledgerless light client. The deployed `refusalVmDescriptor2R24` carries 106 constraints — the bare
//! `rotateV3WithRecordPin B_RECORD_DIGEST` with NO force gate (one fewer than setPerms). The record pin
//! welds the committed AFTER record-digest limb (`B_RECORD_DIGEST = 24`) to the rotated PI slot
//! `ROT_PI_COUNT = 46`, but `generate_rotated_effect_vm_trace` fills that PI from the producer's OWN
//! AFTER limb (`trace_rotated.rs:393-395`). So on the LIGHT-CLIENT path — `verify_vm_descriptor2` over
//! the producer-published dpis, which is EXACTLY what the deployed SDK verifier
//! `full_turn_proof::verify_effect_vm_rotated_with_cutover` runs — the record pin holds VACUOUSLY: a
//! forged-but-self-consistent post-cell publishes its OWN forged limb as PI 46 and the pin is satisfied
//! by construction. ONLY the FULL-NODE off-cell anchor (`proof_verify.rs` step 6b,
//! `compute_authority_digest_felt(apply_effect_to_cell(trusted pre, effect))`) recomputes PI 46 from the
//! pre-cell and rejects the forge — and a ledgerless light client CANNOT run that re-derivation.
//!
//! ## WHY refusal cannot get the perms/VK-style weld (the obstruction, not a parking lot)
//!
//! perms/VK weld the AFTER sub-limb to `prmCol 0`, an IN-CIRCUIT declared-param column whose value is a
//! light-client-known function of the effect (`perms_digest_felt(P)` / `vk_digest_felt(VK)`, carried
//! verbatim by the effect's `permissions_hash` / `vk_hash` field, bound through `effects_hash`).
//!
//! Refusal's write is `fields_root' = map_insert(fields_root, REFUSAL_AUDIT_EXT_KEY, audit_felt(params))`
//! (`apply.rs::apply_refusal`). The audit VALUE `audit_felt = hash("dregg-refusal-audit-v1",
//! offered_action_commitment, reason)` IS effect-param-derivable. But the committed limb the light client
//! must bind is the `fields_root` ROOT (limb 36) / its fold into the authority residue (limb 24) — a
//! sorted-Poseidon2 MAP root that depends on the PRE-`fields_root`. There is NO single declared param
//! equal to it (`refusalVmDescriptor`'s params are `REFUSAL_TARGET` / `REFUSAL_REASON_HASH`, neither the
//! post-root), and committing `audit_felt` in a NEW dedicated sub-limb would DIVERGE the wire commitment
//! from the cell-side commitment (`compute_canonical_state_commitment`, which folds the audit INTO
//! `fields_root`), breaking the §1b faithfulness that makes ledger state need NO migration.
//!
//! The GENUINE in-circuit force is therefore a **`fields_root` map-op WRITE gate** (the noteSpend gold
//! standard: `after_root == sorted_insert(before_root, KEY, audit_felt(params))` checked in-circuit,
//! with a `fields_root` tree witness threaded into `map_heaps`). The `RotationWitness` carries only the
//! `fields_root` DIGEST limb (`pre_limbs[36]`), NOT the leaf-set; no prove path threads a `fields_root`
//! `map_heaps`. This is the SAME data-availability class as the cap-write §A gap — a witness-plumbing
//! task explicitly OUT of STAGE-B scope (logged: `HORIZONLOG.md`, `docs/VK-EPOCH-PLAN.md` STAGE B/D).
//!
//! The lifecycle PAYLOAD (cellSeal limb 29) has the SAME shape: the DISC (the safety-critical
//! transition) IS already in-circuit-forced (`rotateV3WithDiscGate`, cellSeal = 108 constraints, the +1
//! disc gate); only the OPAQUE payload felt `lifecycle_felt(reason_hash, sealed_at)` rides the record
//! pin. It is a hash of light-client-known inputs (`reason_hash` = effect param, `sealed_at = block_height`
//! = PI 44), so binding it needs an in-circuit HASH gate computing that felt — again NOT a single
//! declared-param weld. The disc close already rejects every lifecycle-STATE forgery (frozen seal /
//! resurrection / wrong-disc archive); the payload felt is a non-safety-critical residual.
//!
//! ## The discriminator (both poles — GREEN = it asserts the CURRENT TRUTH)
//!
//! Run through `prove_vm_descriptor2` / `verify_vm_descriptor2` ALONE (the light-client path; NO
//! `apply_effect_to_cell`, NO verifier PI override). For refusal:
//!
//!   * POSITIVE (no downgrade): an HONEST refusal turn proves + verifies.
//!   * OPEN RESIDUAL (the anchor-disabled discriminator): a post-cell forged to differ ONLY in the
//!     refusal-`fields_root` audit, with its OWN producer-free dpis, is STILL ACCEPTED through
//!     `verify_vm_descriptor2` ALONE. This is the LIGHT-CLIENT gap STAGE B must close via the map-op
//!     gate — the record pin alone is full-node-only (a verifier-anchored PI 46 is required to reject,
//!     and the deployed light-client verifier does not anchor it).
//!
//! This corrects the prior framing of this file (which manually anchored PI 46 with the honest value and
//! mislabeled the result "FORCED-ON-WIRE — residual CLOSED"): that anchor is the FULL-NODE step-6b
//! re-derivation, NOT an in-circuit gate, so it does not measure the light-client property. The honest
//! state is: refusal/lifecycle-payload ride the off-cell anchor and are NOT yet light-client-forced.
//!
//! Gated on `prover`. Run with
//! `cargo test -p dregg-circuit --features prover --test vk_epoch_refusal_lifecycle_light_client_binding -- --nocapture`.

#![cfg(feature = "prover")]

use dregg_cell::{Cell, Ledger};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::{
    AFTER_BASE, B_FIELDS_ROOT, B_LIFECYCLE, B_RECORD_DIGEST, BEFORE_BASE, ROT_PI_COUNT, ROT_WIDTH,
    RotatedBlockWitness, empty_caveat_manifest, generate_rotated_effect_vm_trace,
    generate_rotated_refusal_trace_with_fields_tree, rotated_descriptor_name_for_effect,
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

/// **THE FULL-NODE OFF-CELL ANCHOR (modelled).** The deployed full-node verifier (`proof_verify.rs`
/// step 6b) recomputes PI[46] from the TRUSTED pre-cell + the effect — it has the ledger. We model that
/// by overriding `dpis[ROT_PI_COUNT]` with the HONEST post-payload limb (the value the full node
/// recomputes by `apply_effect_to_cell(trusted pre, effect)` then `compute_authority_digest_felt(post)`
/// / `lifecycle_felt_cell(post)`). A LEDGERLESS LIGHT CLIENT CANNOT do this — it has no pre-cell — so
/// this anchor is the light-client-vs-full-node discriminator: with it the forge rejects (full node);
/// without it the forge is accepted (light client — the OPEN residual STAGE B must close).
fn full_node_anchor(dpis: &mut [BabyBear], honest_anchor: BabyBear) {
    dpis[ROT_PI_COUNT] = honest_anchor;
}

/// The folded audit-value felt the refusal writes at the reserved audit slot — the in-circuit map-op's
/// inserted VALUE, light-client-recomputable from the published refusal params. It is
/// `fold_bytes32(audit_bytes)` where `audit_bytes` is the deployed
/// `apply_refusal` audit fold (`blake3("dregg-refusal-audit-v1", offered_action_commitment, reason)`);
/// the post-cell carries it at `fields_map[REFUSAL_AUDIT_EXT_KEY]`.
fn refusal_audit_value(after_cell: &Cell) -> BabyBear {
    let bytes = after_cell
        .state
        .fields_map
        .get(&dregg_cell::state::REFUSAL_AUDIT_EXT_KEY)
        .copied()
        .expect("a refused cell carries the audit slot in fields_map");
    dregg_circuit::cap_root::fold_bytes32(&bytes)
}

/// **REFUSAL — the light-client residual is CLOSED (the in-circuit `fields_root` map-op WRITE gate).** An
/// honest refusal proves + verifies through `verify_vm_descriptor2` ALONE. A post-cell forged to differ in
/// the refusal-`fields_root` audit — publishing a forged after-`fields_root` limb (limb 36) — is now
/// REJECTED through `verify_vm_descriptor2` ALONE (the LIGHT-CLIENT path, NO `apply_effect_to_cell`, NO
/// verifier PI override): the in-circuit `.write` map-op forces `after_fields_root ==
/// write(before_fields_root, REFUSAL_AUDIT_KEY → audit_felt)`, so a forged after-root has no satisfying
/// assignment (the genuine sorted write is FUNCTIONAL — `writesTo_functional`). The deployed committed
/// limb 36 is now the OPENABLE sorted-Poseidon2 `fields_root` (`cell::state::compute_fields_root`), so the
/// map-op can open it; the BLAKE3-sponge `poseidon2(blake3(map))` it replaced was unbindable by any gate.
/// This is the LIVE realization of `EffectVmEmitRotationV3.refusalFieldsWriteV3_forces_write`, threaded to
/// the apex `lightclient_unfoolable_closed_final_genuine`.
#[test]
fn refusal_light_client_forge_rejected_by_fields_write_gate() {
    let balance: i64 = 50_000;

    let before_cell = producer_cell(balance, 0);
    let cell_id = before_cell.id();
    let kernel_effect = dregg_turn::Effect::Refusal {
        cell: cell_id,
        offered_action_commitment: [11u8; 32],
        refusal_reason: dregg_turn::action::RefusalReason::Declined,
        proof_witness_index: 0,
    };

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
        "refusal carries the appended record pin (47 PIs)"
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

    assert_ne!(
        before_w.pre_limbs[B_RECORD_DIGEST], after_w.pre_limbs[B_RECORD_DIGEST],
        "the refusal audit MOVES the AFTER record-digest limb (a genuine write — non-vacuity)"
    );

    let caveat = empty_caveat_manifest();

    // The cell's PRE-refusal overflow `fields_map` leaf set (the openable accumulator the limb-36 root
    // opens against) + the audit value the refusal writes (light-client-recomputable from the params).
    let before_leaves = dregg_cell::state::fields_root_leaves(&before_cell.state.fields_map);
    let audit_value = refusal_audit_value(&honest_after);

    // THE LIVE refusal trace WITH the fields-root write gate: limb 36 is the openable accumulator and the
    // `.write` map-op forces the after-root. `map_heaps` carries the BEFORE leaf set the prover threads.
    let (trace, dpis, map_heaps) = generate_rotated_refusal_trace_with_fields_tree(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
        &before_leaves,
        audit_value,
    )
    .expect("live rotated refusal generator must produce a fields-tree trace + 47 PIs");
    assert_eq!(trace[0].len(), ROT_WIDTH, "rotated trace width");

    let mem_boundary = MemBoundaryWitness::default();

    // The BEFORE/AFTER openable fields-roots the limb-36 columns now carry (non-vacuity: the genuine
    // write MOVES the root, so a forge to a different after-root is distinguishable in-circuit).
    let genuine_before_root = trace[0][BEFORE_BASE + B_FIELDS_ROOT];
    let genuine_after_root = trace[0][AFTER_BASE + B_FIELDS_ROOT];
    assert_ne!(
        genuine_before_root, genuine_after_root,
        "the refusal audit WRITE moves the openable fields_root (non-vacuity — a frozen root would be a \
         trivial accept)"
    );

    // POSITIVE TOOTH (no downgrade): the honest refusal proves + verifies on the light-client path,
    // threading the genuine fields tree.
    assert!(
        accepts(&desc, &trace, &dpis, &mem_boundary, &map_heaps),
        "NO DOWNGRADE: the honest refusal must prove + verify through the light-client path (the genuine \
         fields-root write satisfies the map-op gate)"
    );

    // THE FORGE (light-client, anchor-disabled): a post-cell forged to differ in the refusal audit
    // publishes a FORGED after-`fields_root` (limb 36) — committed ≠ the genuine sorted write. We forge
    // by overriding the published after-root limb on every row off the genuine write (and re-derive the
    // dependent commitment chain so the published commitment is self-consistent, exactly what a forging
    // producer would do). The `.write` map-op then has NO satisfying assignment: `new_root` (the forged
    // limb 36) ≠ `write(before_root, AUDIT_KEY, audit_value)`, so `prove_vm_descriptor2` REFUSES.
    let mut forged_trace = trace.clone();
    let forged_after_root = genuine_after_root + BabyBear::new(1);
    for row in forged_trace.iter_mut() {
        row[AFTER_BASE + B_FIELDS_ROOT] = forged_after_root;
    }
    // (We deliberately do NOT re-derive the commitment chain here: the map-op gate alone rejects the
    // forged after-root, independent of the commitment pins — the gate is the in-circuit force. The dpis
    // are the HONEST producer-free dpis; no full-node anchor is supplied or required.)

    // THE LIGHT-CLIENT CLOSE (anchor-disabled): with the producer-free dpis — exactly what the deployed
    // `verify_effect_vm_rotated_with_cutover` runs — the forged refusal is now REJECTED. The map-op
    // `.write` gate makes the forged after-`fields_root` UNSAT vs the genuine write. NO full-node anchor.
    assert!(
        !accepts(&desc, &forged_trace, &dpis, &mem_boundary, &map_heaps),
        "LIGHT-CLIENT CLOSE: a refusal forged to publish an after-`fields_root` that is NOT the genuine \
         write(before_root, REFUSAL_AUDIT_KEY, audit_felt) is REJECTED through verify_vm_descriptor2 \
         ALONE — the in-circuit `.write` map-op gate bites for a ledgerless client (NO off-cell anchor). \
         This is the residual the BLAKE3-sponge fields_root could NOT close; the openable sorted-Poseidon2 \
         realization makes limb 36 bindable."
    );

    // NON-VACUITY of the close: the SAME forged trace, were the map-op gate absent, would self-verify
    // (the limb is producer-free) — so the rejection above is the GATE biting, not a trace malformation.
    // We witness this by confirming the honest trace (genuine after-root) accepts while ONLY the after-root
    // changed: the rejection is keyed precisely on the after-`fields_root` write, not on any other column.
    assert!(
        forged_trace
            .iter()
            .zip(trace.iter())
            .all(|(f, h)| f
                .iter()
                .enumerate()
                .all(|(c, v)| c == AFTER_BASE + B_FIELDS_ROOT || *v == h[c])),
        "the forge perturbs ONLY the after-`fields_root` limb (36) — the rejection is the map-op gate \
         biting on the forged write, not an unrelated trace break"
    );

    eprintln!(
        "VK-EPOCH FAMILY-2 refusal: light-client forge REJECTED anchor-disabled by the in-circuit \
         fields_root `.write` map-op gate (limb 36 is now the openable sorted-Poseidon2 fields_root). The \
         record pin stays belt-and-suspenders; the map-op is the light-client force \
         (EffectVmEmitRotationV3.refusalFieldsWriteV3_forces_write → the apex)."
    );
}

/// **The lifecycle PAYLOAD — the light-client residual is OPEN, but the safety-critical DISC is CLOSED.**
/// The deployed `cellSealVmDescriptor2R24` carries the in-circuit `rotateV3WithDiscGate` (108 constraints
/// = the bare rotated + record pin + the ONE disc gate). So a cellSeal whose lifecycle STATE is forged
/// (a frozen seal: disc stays Live) is REJECTED through `verify_vm_descriptor2` ALONE — that close is
/// covered by the disc teeth (`cellSealV3_rejects_frozen` in Lean / the deployed disc gate). What stays
/// OPEN for a ledgerless client is the OPAQUE payload felt (limb 29: `lifecycle_felt(reason_hash,
/// sealed_at)`): a cellSeal forged to differ ONLY in the sealing payload (a DIFFERENT reason_hash, disc
/// still Sealed) is ACCEPTED anchor-disabled. Closing it needs an in-circuit hash gate over the
/// light-client-known `(reason_hash, block_height)`, not a single declared-param weld — STAGE C.
#[test]
fn lifecycle_payload_residual_open_disc_closed_anchor_disabled() {
    let balance: i64 = 50_000;

    let before_cell = producer_cell(balance, 0);
    let cell_id = before_cell.id();
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
        "cellSeal carries the appended record pin (47 PIs)"
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
        "the seal MOVES the AFTER lifecycle limb (Live -> Sealed) — non-vacuity"
    );

    let caveat = empty_caveat_manifest();
    let (trace, dpis) =
        generate_rotated_effect_vm_trace(&st, &effects, &bridge(&before_w), &bridge(&after_w), &caveat)
            .expect("live rotated generator must produce a cellSeal trace + 47 PIs");

    let honest_anchor = after_w.pre_limbs[B_LIFECYCLE];

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    // POSITIVE TOOTH (no downgrade).
    assert!(
        accepts(&desc, &trace, &dpis, &mem_boundary, &map_heaps),
        "NO DOWNGRADE: the honest cellSeal must prove + verify through the light-client path"
    );

    // Forge ONLY the sealing PAYLOAD (a different reason_hash; the DISC stays Sealed).
    let forged_reason = [44u8; 32];
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
        forged_after_w.pre_limbs[B_LIFECYCLE], honest_anchor,
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

    // THE LIGHT-CLIENT RESIDUAL (anchor-disabled): the payload-only forge is ACCEPTED with producer-free
    // dpis — the record pin on limb 29 holds vacuously. (The DISC is forced separately; a disc forgery —
    // a frozen seal — is rejected by the disc gate. Only the opaque payload felt stays open.)
    assert!(
        accepts(&desc, &forged_trace, &forged_dpis, &mem_boundary, &map_heaps),
        "STEP-0 GROUND TRUTH (lifecycle payload residual OPEN): a cellSeal forged to differ ONLY in the \
         sealing PAYLOAD (reason_hash; disc still Sealed) is ACCEPTED anchor-disabled. The safety-critical \
         DISC is in-circuit-forced; the opaque payload felt needs an in-circuit hash gate over \
         (reason_hash, block_height) — STAGE C."
    );

    // CONTRAST (the full-node leg is sound): the off-cell anchor rejects the payload forge.
    let mut anchored_forged_dpis = forged_dpis.clone();
    full_node_anchor(&mut anchored_forged_dpis, honest_anchor);
    assert!(
        !accepts(&desc, &forged_trace, &anchored_forged_dpis, &mem_boundary, &map_heaps),
        "FULL-NODE leg sound: with the off-cell anchor, the forged-payload cellSeal is REJECTED — the \
         forge IS distinguishable, so the light-client residual above is a genuine open gap"
    );

    eprintln!(
        "VK-EPOCH FAMILY-2 lifecycle payload: DISC closed (in-circuit disc gate), PAYLOAD residual OPEN \
         (forge accepted anchor-disabled). The payload close needs an in-circuit hash gate over \
         (reason_hash, block_height) — STAGE C."
    );
}
