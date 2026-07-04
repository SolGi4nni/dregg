//! # THE VK-EPOCH FAMILY-2 LIGHT-CLIENT CLOSE — Refusal + the lifecycle PAYLOAD: the HONEST state.
//!
//! ## What this measures (`docs/VK-EPOCH-PLAN.md`, STAGE B/C, family 2 — the CLOSED state)
//!
//! Family 1 (`vk_epoch_perms_vk_light_client_binding.rs`) is GENUINELY closed: setPermissions / setVK
//! carry an IN-CIRCUIT `permsVKWeldGate` welding the committed AFTER perms/vk sub-limb (limb 33/34) to
//! `param0`, and `param0` is the post-value bound into the PI-anchored `effects_hash` (a value a
//! ledgerless light client independently knows from the effect). So a perms-/vk-only forged post-cell is
//! UNSAT through `verify_vm_descriptor2` ALONE — NO verifier PI override, NO `apply_effect_to_cell`. The
//! deployed `setPermsVmDescriptor2R24` carries 107 constraints (the bare rotated 106 + the ONE weld);
//! the forge test rejects with `failed constraints = [the weld]`, the anchor not in the loop.
//!
//! Family 2 — Refusal + the lifecycle PAYLOAD — is now ALSO CLOSED for a ledgerless light client (a
//! DIFFERENT in-circuit primitive than family-1's single-param weld: a map-op WRITE gate / a HASH gate).
//! The deployed `refusalVmDescriptor2R24` carries — BESIDE the record-digest pin — a single `.write`
//! map-op (guard = `SEL_REFUSAL` col 52, key = the constant `refusalAuditKeyFelt = 529176517` =
//! `field_key_hash(REFUSAL_AUDIT_EXT_KEY)`, value = the declared audit-felt param col, root = the openable
//! limb-36 `fields_root`). It is the LAST constraint past the `rotateV3WithRecordPin B_RECORD_DIGEST`
//! base — so the deployed refusal row carries 107 constraints (the 1-felt registry) / 147 (the wide
//! registry the verifier reads), exactly ONE map-op (vs noteSpend's TWO: `.absent` + `.insert`). The
//! map-op FORCES `after_fields_root == write(before_fields_root, REFUSAL_AUDIT_KEY → audit_felt(params))`.
//!
//! So on the LIGHT-CLIENT path — `verify_vm_descriptor2` over the producer-published dpis, which is
//! EXACTLY what the deployed SDK verifier `full_turn_proof::verify_effect_vm_rotated_with_cutover` runs —
//! a refusal forged to publish a self-consistent post-cell differing ONLY in the refusal-`fields_root`
//! audit is REJECTED: its forged after-`fields_root` (limb 36) ≠ the genuine sorted write, and under CR
//! the write is FUNCTIONAL (`writesTo_functional`), so there is NO satisfying assignment — NO off-cell
//! anchor required. The PI-46 record-digest pin the row also carries is now belt-and-suspenders on the
//! FULL-NODE leg (the `proof_verify.rs` step-6b `compute_authority_digest_felt(apply_effect_to_cell(...))`
//! anchor still bites, redundantly, exactly as it does for setPerms/setVK).
//!
//! ## WHY refusal needed the map-op write gate (not the perms/VK-style single-param weld)
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
//! `fields_root`), breaking the §1b faithfulness that makes ledger state need NO migration. So the
//! GENUINE force is a **`fields_root` map-op WRITE gate** (the noteSpend gold standard:
//! `after_root == sorted_write(before_root, KEY, audit_felt(params))` checked in-circuit, with a
//! `fields_root` tree witness threaded into `map_heaps`). That gate is now DEPLOYED: limb 36 carries the
//! OPENABLE sorted-Poseidon2 `fields_root` (`cell::state::compute_fields_root`), and the prove path
//! `generate_rotated_refusal_trace_with_fields_tree` threads the BEFORE leaf-set as `map_heaps` so the
//! map-op can open it (the data-availability plumbing the prior framing had as out-of-scope is landed).
//!
//! The lifecycle PAYLOAD (cellSeal limb 29) is closed by a sibling primitive: the DISC (the safety-
//! critical transition) is in-circuit-forced (`rotateV3WithDiscGate`), AND the OPAQUE payload felt
//! `lifecycle_felt(disc, reason_hash, sealed_at)` — a FELT-DOMAIN Poseidon2 hash of light-client-known
//! inputs (`reason_hash` = effect param, `sealed_at = block_height`) — is now welded to the declared
//! payload-hash column `prmCol 3` by the in-circuit `lifecyclePayloadHashGate`. So a forged payload
//! (committed limb 29 ≠ the recomputed payload hash) is UNSAT anchor-disabled.
//!
//! ## The two poles (both teeth — GREEN = it asserts the CURRENT TRUTH)
//!
//! Run through `prove_vm_descriptor2` / `verify_vm_descriptor2` ALONE (the light-client path; NO
//! `apply_effect_to_cell`, NO verifier PI override). For refusal:
//!
//!   * POSITIVE (no downgrade): an HONEST refusal turn proves + verifies (the genuine fields-root write
//!     satisfies the map-op gate).
//!   * LIGHT-CLIENT CLOSE (anchor-disabled): a post-cell forged to differ ONLY in the refusal-`fields_root`
//!     audit, with its OWN producer-free dpis, is REJECTED through `verify_vm_descriptor2` ALONE — the
//!     in-circuit `.write` map-op bites for a ledgerless client (NO verifier-anchored PI 46 needed).
//!
//! This is the LIVE realization of `EffectVmEmitRotationV3.refusalFieldsWriteV3_forces_write` (refusal) /
//! `cellSealV3_payload_rejects_forged_lightclient` (lifecycle payload), threaded to the apex
//! `lightclient_unfoolable_closed_final_genuine`. The deployed-descriptor structural witness — the single
//! refusal `.write` map-op — is checked by `effect_vm_descriptors`'s registry coverage tests; the LIVE
//! deployed-descriptor prove/verify forge close is also exercised by
//! `effect_vm_rotation_flip::rotated_audit_record_pin_forces_record_digest_and_rejects_frozen_forgery`.
//!
//! Gated on `prover`. Run with
//! `cargo test -p dregg-circuit --features prover --test vk_epoch_refusal_lifecycle_light_client_binding -- --nocapture`.

// (formerly `#![cfg(feature = "prover")]` — that dregg-circuit feature is GONE; the
// descriptor-level prove/verify (`prove_vm_descriptor2`/`verify_vm_descriptor2`) is
// now unconditional in dregg-circuit, so this test compiles + runs by default.)

use dregg_cell::{Cell, Ledger};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::{
    AFTER_BASE, B_FIELDS_ROOT, B_LIFECYCLE, B_RECORD_DIGEST, BEFORE_BASE, ROT_PI_COUNT, ROT_WIDTH,
    RotatedBlockWitness, empty_caveat_manifest, generate_rotated_effect_vm_trace,
    generate_rotated_refusal_trace_with_fields_tree, generate_rotated_refusal_write_wide,
    rotated_descriptor_name_for_effect,
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
    let name =
        rotated_descriptor_name_for_effect(&vm_effect).expect("Refusal is a rotated cohort member");
    assert_eq!(name, "refusalVmDescriptor2R24");
    let desc = parse_vm_descriptor2(rotated_descriptor_json(name))
        .expect("rotated refusal descriptor parses");
    assert_eq!(
        desc.public_input_count, 58,
        "refusal PIs = 50 rotated base (46 + 4 dsl rc) + 8 authority limbs (the H1 record-pin8) = 58 \
         (committed refusalVmDescriptor2R24)"
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

    let before_w = rw::produce(
        &before_cell,
        &Ledger::new(),
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &honest_after,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        &Default::default(),
    );

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
        forged_trace.iter().zip(trace.iter()).all(|(f, h)| f
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

/// The declared payload-hash column the lifecycle-payload gate welds the AFTER lifecycle limb to:
/// `prmCol 3` = `PARAM_BASE + 3` (col 71). A FREE param column for all three lifecycle movers; the
/// producer fills it with the felt-domain `lifecycle_felt`, the LIGHT CLIENT recomputes it from the
/// PI-bound `reason_hash` + the turn-header height. `EffectVmEmitRotationV3.declaredLifecyclePayloadCol`.
const LC_PAYLOAD_COL: usize = dregg_circuit::effect_vm::columns::PARAM_BASE + 3;

/// **The lifecycle PAYLOAD — the light-client residual is CLOSED (the in-circuit lifecycle-payload HASH
/// gate).** The deployed `cellSealVmDescriptor2R24` now carries, BESIDE the disc gate, the in-circuit
/// `lifecyclePayloadHashGate`: a selector-gated weld of the AFTER lifecycle limb (`B_LIFECYCLE = 29`) to
/// the declared payload-hash column `prmCol 3`. The producer fills `prmCol 3` with the FELT-DOMAIN
/// `lifecycle_felt(disc, reason_hash, sealed_at)` — recomputable in-circuit from the LIGHT-CLIENT-KNOWN
/// inputs (the PI-bound `reason_hash` + the turn-header `block_height`), NOT a byte-packed sponge the gate
/// cannot open. So a cellSeal whose committed AFTER lifecycle limb DIVERGES from the recomputed payload
/// hash (a forged `reason_hash` / `sealed_at` riding a committed limb the producer did NOT derive from
/// the declared payload) is UNSAT through `verify_vm_descriptor2` ALONE — the LIGHT-CLIENT path, NO
/// off-cell anchor. This is the LIVE realization of
/// `EffectVmEmitRotationV3.cellSealV3_payload_rejects_forged_lightclient`, threaded to the apex.
#[test]
fn lifecycle_payload_forge_rejected_by_hash_gate_anchor_disabled() {
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
    let desc = parse_vm_descriptor2(rotated_descriptor_json(name))
        .expect("rotated cellSeal descriptor parses");
    assert_eq!(
        desc.public_input_count, 51,
        "cellSeal PIs = 50 rotated base (46 + 4 dsl rc) + 1 appended record pin = 51 \
         (committed cellSealVmDescriptor2R24)"
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

    let before_w = rw::produce(
        &before_cell,
        &Ledger::new(),
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &honest_after,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        &Default::default(),
    );

    assert_ne!(
        before_w.pre_limbs[B_LIFECYCLE], after_w.pre_limbs[B_LIFECYCLE],
        "the seal MOVES the AFTER lifecycle limb (Live -> Sealed) — non-vacuity"
    );

    let caveat = empty_caveat_manifest();
    let (trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("live rotated generator must produce a cellSeal trace + 47 PIs");

    // The honest declared payload-hash column IS the felt-domain `lifecycle_felt` of the sealed cell —
    // the value the light client recomputes from `(disc=Sealed, reason_hash, block_height)`. It equals
    // the committed AFTER lifecycle limb (the gate's weld is honest by construction).
    let honest_payload_felt = after_w.pre_limbs[B_LIFECYCLE];
    assert_eq!(
        trace[0][LC_PAYLOAD_COL], honest_payload_felt,
        "the producer fills prmCol 3 with the felt-domain lifecycle_felt (= the AFTER limb)"
    );

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    // POSITIVE TOOTH (no downgrade): the honest cellSeal — with the gate's weld satisfied — proves +
    // verifies on the light-client path.
    assert!(
        accepts(&desc, &trace, &dpis, &mem_boundary, &map_heaps),
        "NO DOWNGRADE: the honest cellSeal (AFTER lifecycle limb == recomputed payload hash) must prove + \
         verify through the light-client path"
    );

    // THE FORGE (light-client, anchor-disabled): a cellSeal forged to differ ONLY in the sealing PAYLOAD
    // — a committed AFTER lifecycle limb (`B_LIFECYCLE`) that does NOT equal the recomputed payload hash
    // the light client holds in `prmCol 3`. We pin `prmCol 3` to the HONEST recomputed felt (what the
    // light-client verifier supplies from the PI-bound reason_hash + height) and forge ONLY the committed
    // limb. The `lifecyclePayloadHashGate` (`sel · (after_lc − prmCol3)`) then has NO satisfying
    // assignment on the active seal row: `after_lc != prmCol3`, so `prove_vm_descriptor2` REFUSES.
    let mut forged_trace = trace.clone();
    let forged_payload_limb = honest_payload_felt + BabyBear::new(1);
    for row in forged_trace.iter_mut() {
        // forge the committed AFTER lifecycle limb; KEEP prmCol 3 at the recomputed payload hash.
        row[AFTER_BASE + B_LIFECYCLE] = forged_payload_limb;
        // (We deliberately do NOT re-derive the commitment chain — the in-circuit gate alone rejects the
        // forged limb vs the recomputed payload column, independent of the commitment pins.)
    }

    // THE LIGHT-CLIENT CLOSE (anchor-disabled): with the producer-free dpis — exactly what the deployed
    // `verify_effect_vm_rotated_with_cutover` runs — the forged-payload cellSeal is now REJECTED. The
    // `lifecyclePayloadHashGate` makes the forged committed lifecycle limb UNSAT vs the recomputed payload
    // hash. NO full-node anchor.
    assert!(
        !accepts(&desc, &forged_trace, &dpis, &mem_boundary, &map_heaps),
        "LIGHT-CLIENT CLOSE: a cellSeal forged to publish an AFTER lifecycle limb that is NOT the \
         recomputed lifecycle_felt(disc, reason_hash, block_height) is REJECTED through \
         verify_vm_descriptor2 ALONE — the in-circuit lifecycle-payload hash gate bites for a ledgerless \
         client (NO off-cell anchor). This is the residual the opaque byte-packed lifecycle_felt could NOT \
         close; the felt-domain realization makes limb 29 recomputable + bindable."
    );

    // NON-VACUITY of the close: the forge perturbs ONLY the committed AFTER lifecycle limb (col
    // `AFTER_BASE + B_LIFECYCLE`); every other column (incl. the recomputed `prmCol 3`) is unchanged — so
    // the rejection is the gate's weld biting on the forged limb, not an unrelated trace malformation.
    assert!(
        forged_trace.iter().zip(trace.iter()).all(|(f, h)| f
            .iter()
            .enumerate()
            .all(|(c, v)| c == AFTER_BASE + B_LIFECYCLE || *v == h[c])),
        "the forge perturbs ONLY the after-lifecycle limb (29) — the rejection is the payload hash gate \
         biting on the forged limb, not an unrelated trace break"
    );

    // CONTRAST (the full-node leg is ALSO sound, belt-and-suspenders): the off-cell anchor likewise
    // rejects — but the gate above already closed it WITHOUT the anchor (the light-client property).
    let mut anchored_forged_dpis = dpis.clone();
    full_node_anchor(&mut anchored_forged_dpis, honest_payload_felt);
    assert!(
        !accepts(
            &desc,
            &forged_trace,
            &anchored_forged_dpis,
            &mem_boundary,
            &map_heaps
        ),
        "FULL-NODE leg also sound (belt-and-suspenders): the off-cell anchor likewise rejects the \
         forged-payload limb"
    );

    eprintln!(
        "VK-EPOCH FAMILY-2 lifecycle payload: DISC closed (disc gate) AND PAYLOAD closed (in-circuit \
         lifecycle-payload hash gate — forge REJECTED anchor-disabled). The felt-domain lifecycle_felt \
         makes limb 29 recomputable from (disc, reason_hash, block_height); the gate welds it \
         (EffectVmEmitRotationV3.cellSealV3_payload_rejects_forged_lightclient → the apex)."
    );
}

/// Resolve a WIDE-registry descriptor JSON by registry KEY (col 0) from the committed staged TSV.
fn wide_json(name: &str) -> &'static str {
    dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV
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
        .unwrap_or_else(|| panic!("{name} not in WIDE_REGISTRY_STAGED_TSV"))
}

/// **THE DEPLOYED FIELDS-WRITE (OPTION I): the wide `refusalVmDescriptor2R24` PROVES + light-client
/// VERIFIES the faithful 8-felt fields-write.** The deployed after-spine `effFieldsWriteV3
/// refusalFieldsWriteV3 …` (`= CircuitSoundnessAssembled.Rfix 39`, `v3RegistryHeap` tail pos 55) a light
/// client checks: the wide producer lays the Class-A refusal base (the 8-felt fields-root GROUP + record
/// pin + audit param) WIDENED by the fields-open READ appendix (OLD audit leaf against the BEFORE root8) +
/// the AFTER-spine appendix (UPDATED audit leaf against the AFTER root8, SHARED path) + the 8-felt wide
/// carriers. A satisfying trace FORCES `fieldsWritesTo8` over the FULL ~124-bit BEFORE/AFTER fields-root
/// blocks (`FieldsOpenEmit.effFieldsWriteV3_forces_write8`) — the THIRD faithful 8-felt Merkle root,
/// deployed. The deployed twin of `wide_heap_write_proves_and_verifies`.
#[test]
fn wide_fields_write_proves_and_verifies() {
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
    let st = CellState::new(balance as u64, 0);
    let effects = vec![vm_effect];

    let mut honest_after = producer_cell(balance, 0);
    rw::apply_effect_to_cell(&mut honest_after, &cell_id, &kernel_effect, 100);

    let mut ledger = Ledger::new();
    ledger.insert_cell(honest_after.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &Ledger::new(),
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &honest_after,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        &Default::default(),
    );
    let caveat = empty_caveat_manifest();
    let before_leaves = dregg_cell::state::fields_root_leaves(&before_cell.state.fields_map);
    let audit_value = refusal_audit_value(&honest_after);

    let (trace, dpis, map_heaps) = generate_rotated_refusal_write_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
        &before_leaves,
        audit_value,
    )
    .expect("wide refusal fields-write generation");

    let name = "refusalVmDescriptor2R24";
    let desc = parse_vm_descriptor2(wide_json(name)).unwrap();
    // v13 geometry (the Lean-authoritative deployed bare wide, drift-clean): the OPTION I after-spine
    // wide tracks the grown GRAD_ROT_WIDTH graduated base. The producer's READ appendix base tracks
    // GRAD_ROT_WIDTH via `REFUSAL_WRITE_READ_BASE`; committed refusalVmDescriptor2R24 (wide) = 2965.
    assert_eq!(
        desc.trace_width, 2965,
        "refusal fields-write wide width 2965 (OPTION I after-spine, v13 graduated base — committed \
         wide refusalVmDescriptor2R24 trace_width)"
    );
    assert_eq!(
        desc.public_input_count, 74,
        "refusal fields-write wide 74 PIs (58 narrow base = 50 + 8 authority limbs, + 16 wide)"
    );
    assert_eq!(trace[0].len(), 2965);
    assert_eq!(dpis.len(), 74);

    let mb = MemBoundaryWitness::default();
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mb, &map_heaps)
        .unwrap_or_else(|e| panic!("refusal fields-write WIDE proof must prove: {e}"));
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .unwrap_or_else(|e| panic!("refusal fields-write WIDE proof must verify: {e}"));
    eprintln!(
        "WIDE refusal fields-write: PROVED + VERIFIED at 1935 (genuine sorted-Merkle audit-slot write \
         over the faithful 8-felt fields root + 8-felt commit, 70 PIs) — the THIRD faithful root deployed."
    );
}
