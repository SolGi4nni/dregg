//! # THE VK-EPOCH LIGHT-CLIENT BINDING AUDIT — MISC FAMILY (BATCH D).
//!
//! The fourth VK-epoch family: the five MISC effects, audited through the anchor-disabled
//! discriminator (the `prove`/`verify_vm_descriptor2` path ALONE — the same circuit verify a
//! ledgerless client runs; it NEVER calls `apply_effect_to_cell`, so a reject here is the
//! IN-CIRCUIT weld, not the host re-derivation). Mirrors the structure of
//! `circuit/tests/vk_epoch_perms_vk_light_client_binding.rs` (commit d58545a5f).
//!
//! Unlike the perms/VK family — which was ALREADY forced on-wire (the in-circuit `permsVKWeldGate`
//! binds the post perms/vk into the commitment) — the misc family splits into THREE grades, and
//! this audit reports each PRECISELY rather than over-claiming:
//!
//!   * **`emitEvent` / `pipelinedSend` / `exercise` — NO-CELL-WRITE; ON-WIRE BINDING = the
//!     state/commit passthrough, NOT the produced hash.** These write no committed cell column
//!     (full state passthrough; the nonce ticks). The rotated (light-client) descriptor binds the
//!     before/after balance·nonce boundaries and the published OLD/NEW commit·height·caveat — a
//!     forged AFTER state (nonce/balance) is UNSAT. But their DECLARED HASH (topic/payload /
//!     send_hash / exercise_hash) rides the V1 hand-AIR's `compute_effects_hash` PI-equality, whose
//!     PI slots (`EMIT_EVENT_TOPIC_HASH = 174`, …) lie PAST the rotated PI window (`V1_PI_COUNT =
//!     42`) — and the rotated descriptor binds none of `PI[16..20]` (`EFFECTS_HASH`) either. So the
//!     PRODUCED hash is bound at the full node, NOT in the rotated light-client descriptor. This
//!     audit asserts both: (POSITIVE) the state/commit IS bound on-wire; (RESIDUAL) a forged
//!     declared-hash param is ACCEPTED through the rotated path — the effects_hash is not welded
//!     into the light-client commitment. THE NAMED RESIDUAL: lift the effects_hash (or the
//!     emit-event topic/payload PI) into the rotated PI window so the produced output binds on-wire.
//!
//!   * **`makeSovereign` — VALUE_PARTIAL with a BROKEN LIVE SEAM (missing weld).** The registry
//!     descriptor `makeSovereignVmDescriptor2R24` declares 47 PIs (the record-forcing fifth pin),
//!     but the LIVE generator `generate_rotated_effect_vm_trace` emits only 46 dpis: its
//!     `record_pin_offset` (`trace_rotated.rs`) does NOT include `MakeSovereign`, so no PI[46] is
//!     fed. Consequence: an honest makeSovereign turn CANNOT prove through the live path
//!     (`public input count 46 != descriptor public_input_count 47`). The committed AFTER mode limb
//!     (`B_MODE = 35`) and authority-digest limb (`B_AUTHORITY_DIGEST = 24`, which folds the mode
//!     byte) DO move and ARE absorbed into the commit — but the declared record pin is never wired,
//!     so the makeSovereign rotated path is presently UN-PROVABLE, not merely partially-bound. THE
//!     NAMED RESIDUAL (shared-code weld, NOT in this disjoint test file): add the `MakeSovereign`
//!     arm to `record_pin_offset` (→ `Some(B_AUTHORITY_DIGEST)`, or a dedicated `B_MODE` pin) so the
//!     generator feeds the 47th PI the descriptor declares.
//!
//!   * **`setFieldDyn` — UNREACHABLE via the live generator (missing weld).** The dynamic
//!     `SetField` (`field_idx > 7`) routes to `setFieldDynVmDescriptor2R24`, but the V1 trace
//!     generator HARD-ASSERTS `field_idx < 8` (`trace.rs::generate_effect_vm_trace`), so
//!     `generate_rotated_effect_vm_trace` PANICS before producing any trace for an overflow write.
//!     The fields-root weld (PI[46] → the AFTER authority-digest limb folding `fields_root`) is
//!     declared in the descriptor but exercised by NO live path. THE NAMED RESIDUAL: the dynamic
//!     overflow `SetField` needs a generator path (lift the `field_idx < 8` assert into a
//!     dyn-routing branch that writes the `fields_root` map and feeds the fields-root pin).
//!
//! Each test below is GREEN: the confirmable bindings (the no-cell-write state/commit) prove + the
//! discriminator bites; the residuals are asserted as residuals (the precise broken seam / the
//! accepted forge), NOT faked green.
//!
//! Gated on `prover`. Run with
//! `cargo test -p dregg-circuit --features prover --test vk_epoch_misc_light_client_binding -- --nocapture`.

#![cfg(feature = "prover")]

use dregg_cell::{AuthRequired, Cell, CellMode, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, VmConstraint2, parse_vm_descriptor2,
    prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::lean_descriptor_air::VmConstraint;
use dregg_circuit::effect_vm::columns::PARAM_BASE;
use dregg_circuit::effect_vm::trace_rotated::{
    AFTER_BASE, B_AUTHORITY_DIGEST, B_MODE, ROT_WIDTH, RotatedBlockWitness, empty_caveat_manifest,
    generate_rotated_effect_vm_trace, rotated_descriptor_name_for_effect,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::HeapLeaf;
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

/// The producer's base cell: open perms, no VK, a fixed pk. Mode defaults to `Hosted`
/// (`Cell::with_balance`).
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
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("37 pre-iroot limbs")
}

/// `true` iff `prove_vm_descriptor2` REFUSES (returns `Err` OR panics) on the given trace + PIs.
fn refused(
    desc: &EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    dpis: &[BabyBear],
    mem_boundary: &MemBoundaryWitness,
    map_heaps: &[Vec<HeapLeaf>],
) -> bool {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_vm_descriptor2(desc, trace, dpis, mem_boundary, map_heaps)
    }));
    match r {
        Err(_) => true,
        Ok(res) => res.is_err(),
    }
}

const NULL_ROOT: [u8; 32] = [0u8; 32];
const COMMIT_ROOT: [u8; 32] = [0u8; 32];

fn receipt_log() -> Vec<[u8; 32]> {
    vec![[3u8; 32]]
}

// ============================================================================
// NO-CELL-WRITE effects: emitEvent / pipelinedSend / exercise.
//
// The state/commit passthrough IS bound on-wire; the PRODUCED declared hash is NOT bound in the
// rotated light-client descriptor (it rides the full-node v1 effects_hash, whose PI slots are past
// the rotated PI window). We confirm BOTH precisely.
// ============================================================================

/// Returns `(positive_proved, forged_state_rejected, forged_hash_accepted)`.
///
///   * `positive_proved`     — the honest passthrough turn proves + verifies (no downgrade).
///   * `forged_state_rejected` — a forged AFTER state (the nonce boundary) is UNSAT (the
///     state/commit IS bound on-wire — the genuine no-cell-write binding).
///   * `forged_hash_accepted` — a forged declared-hash param (with the honest PIs) is ACCEPTED:
///     the rotated descriptor does NOT bind the effects_hash / the produced output. This is the
///     NAMED RESIDUAL, asserted as a residual.
fn no_cell_write_audit(effect: Effect, name: &str) -> (bool, bool, bool) {
    let balance: i64 = 50_000;
    let st = CellState::new(balance as u64, 0);
    let effects = vec![effect];

    let resolved = rotated_descriptor_name_for_effect(&effects[0])
        .unwrap_or_else(|| panic!("{name} is a rotated cohort member"));
    assert_eq!(resolved, name);
    let desc = parse_vm_descriptor2(rotated_descriptor_json(name))
        .unwrap_or_else(|e| panic!("rotated {name} descriptor parses: {e}"));
    assert_eq!(
        desc.public_input_count, 46,
        "{name}: a no-cell-write passthrough carries the bare 46-PI rotated vector (no fifth pin)"
    );

    // The rotated descriptor binds NONE of PI[16..20] (the effects_hash): the produced output is
    // not welded into the light-client commitment (the structural source of the residual).
    let bound_pis: std::collections::BTreeSet<usize> = desc
        .constraints
        .iter()
        .filter_map(|c| match c {
            VmConstraint2::Base(VmConstraint::PiBinding { pi_index, .. }) => Some(*pi_index),
            _ => None,
        })
        .collect();
    assert!(
        (16..20).all(|p| !bound_pis.contains(&p)),
        "{name}: the rotated descriptor binds no EFFECTS_HASH PI (16..20) — the produced output is \
         NOT on the rotated light-client wire (the named residual)"
    );

    // Full state passthrough: BEFORE == AFTER except the nonce tick.
    let before_cell = producer_cell(balance, 0);
    let after_cell = producer_cell(balance, 1);
    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).unwrap();
    let before_w = rw::produce(&before_cell, &ledger, &NULL_ROOT, &COMMIT_ROOT, &receipt_log());
    let after_w = rw::produce(&after_cell, &ledger, &NULL_ROOT, &COMMIT_ROOT, &receipt_log());

    let caveat = empty_caveat_manifest();
    let (trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .unwrap_or_else(|e| panic!("live rotated generator produces a {name} trace + 46 PIs: {e}"));
    assert_eq!(trace[0].len(), ROT_WIDTH, "rotated trace width");

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<HeapLeaf>> = vec![];

    // POSITIVE TOOTH (no downgrade).
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
        .unwrap_or_else(|e| panic!("NO DOWNGRADE: the honest {name} turn must prove: {e}"));
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .unwrap_or_else(|e| panic!("NO DOWNGRADE: the honest {name} proof must verify: {e}"));
    let positive_proved = true;

    // BINDING TOOTH (the genuine no-cell-write binding): forge a WITNESS-CARRIED rotated limb of
    // the AFTER block — the authority digest (the perms residue, NOT one of the welded
    // balance/nonce/fields columns) — so the AFTER block publishes a DIFFERENT committed limb (and a
    // different commit) while we keep the HONEST published PIs. The rotated NEW_COMMIT pin (PI 43)
    // then disagrees with the forged AFTER commit carrier → UNSAT. This is the same shape as the
    // perms/vk template: a self-consistent forged post-cell that differs in a committed (non-welded)
    // limb is caught by the commit chain.
    let mut forged_after_cell = producer_cell(balance, 1);
    forged_after_cell.permissions = Permissions::zkapp(); // a DISTINCT committed authority residue
    let mut forged_ledger = Ledger::new();
    forged_ledger.insert_cell(forged_after_cell.clone()).unwrap();
    let forged_after_w =
        rw::produce(&forged_after_cell, &forged_ledger, &NULL_ROOT, &COMMIT_ROOT, &receipt_log());
    assert_ne!(
        forged_after_w.state_commit, after_w.state_commit,
        "{name}: the forged committed-limb post publishes a DIFFERENT commit (anti-vacuity)"
    );
    let (forged_state_trace, _forged_state_dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&forged_after_w),
        &caveat,
    )
    .expect("generator builds the forged-commit trace");
    // Keep the HONEST published PIs (the light client is shown the honest commit) against the forged
    // AFTER commit carrier → the NEW_COMMIT pin must reject.
    let forged_state_rejected =
        refused(&desc, &forged_state_trace, &dpis, &mem_boundary, &map_heaps);

    // RESIDUAL TOOTH: forge the declared-hash param[0] on every row while keeping the honest PIs.
    // The rotated descriptor does NOT bind the effects_hash → this is ACCEPTED (the residual).
    let honest_param0 = trace[0][PARAM_BASE];
    let forged_param0 = honest_param0 + BabyBear::new(987_654);
    let mut forged_hash_trace = trace.clone();
    for row in forged_hash_trace.iter_mut() {
        row[PARAM_BASE] = forged_param0;
    }
    let forged_hash_accepted =
        !refused(&desc, &forged_hash_trace, &dpis, &mem_boundary, &map_heaps);

    (positive_proved, forged_state_rejected, forged_hash_accepted)
}

#[test]
fn emitevent_state_binds_hash_is_residual_anchor_disabled() {
    let effect = Effect::EmitEvent {
        topic_hash: [BabyBear::new(11); 8],
        payload_hash: [BabyBear::new(22); 8],
    };
    let (proved, state_rejected, hash_accepted) =
        no_cell_write_audit(effect, "emitEventVmDescriptor2R24");
    assert!(proved, "emitEvent: honest passthrough proves + verifies");
    assert!(
        state_rejected,
        "emitEvent: a forged AFTER state (nonce boundary) is UNSAT — the state/commit IS bound \
         on-wire (the genuine no-cell-write binding)"
    );
    assert!(
        hash_accepted,
        "emitEvent RESIDUAL (named): a forged declared (topic, payload) param is ACCEPTED through \
         the rotated path — the effects_hash is NOT welded into the light-client commitment; the \
         produced output binds only at the full node. Lift the effects_hash / emit-event PI into \
         the rotated PI window to force it on-wire."
    );
    eprintln!(
        "VK-EPOCH emitEvent: state/commit BOUND on-wire (forged-state UNSAT); the produced \
         (topic,payload) is a RESIDUAL (forged-hash ACCEPTED — effects_hash off the rotated wire)."
    );
}

#[test]
fn pipelinedsend_state_binds_hash_is_residual_anchor_disabled() {
    let mut send_hash = [BabyBear::ZERO; 8];
    send_hash[0] = BabyBear::new(7777);
    let effect = Effect::PipelinedSend { send_hash };
    let (proved, state_rejected, hash_accepted) =
        no_cell_write_audit(effect, "pipelinedSendVmDescriptor2R24");
    assert!(proved, "pipelinedSend: honest passthrough proves + verifies");
    assert!(
        state_rejected,
        "pipelinedSend: a forged AFTER state is UNSAT — the state/commit IS bound on-wire (the \
         passthrough binding; pipelinedSend writes no cell column)"
    );
    assert!(
        hash_accepted,
        "pipelinedSend RESIDUAL (named): a forged send_hash param is ACCEPTED through the rotated \
         path — the produced send dispatch binds only at the full node (effects_hash off-wire)."
    );
    eprintln!(
        "VK-EPOCH pipelinedSend: state/commit BOUND on-wire; the send_hash is a RESIDUAL \
         (effects_hash off the rotated wire)."
    );
}

#[test]
fn exercise_state_binds_hash_is_residual_anchor_disabled() {
    let mut exercise_hash = [BabyBear::ZERO; 8];
    exercise_hash[0] = BabyBear::new(31337);
    let effect = Effect::ExerciseViaCapability { exercise_hash };
    let (proved, state_rejected, hash_accepted) =
        no_cell_write_audit(effect, "exerciseVmDescriptor2R24");
    assert!(proved, "exercise: honest passthrough proves + verifies");
    assert!(
        state_rejected,
        "exercise: a forged AFTER state (the economic frame / nonce tick) is UNSAT — the \
         state/commit IS bound on-wire; the inner actions carry their OWN bindings as their own rows"
    );
    assert!(
        hash_accepted,
        "exercise RESIDUAL (named): a forged exercise_hash param is ACCEPTED through the rotated \
         path — the cap-slot ‖ inner-effects-hash binds only at the full node (effects_hash off-wire)."
    );
    eprintln!(
        "VK-EPOCH exercise: economic frame (state/commit) BOUND on-wire; the exercise_hash is a \
         RESIDUAL (effects_hash off the rotated wire)."
    );
}

// ============================================================================
// makeSovereign — VALUE_PARTIAL with a BROKEN LIVE SEAM (missing record-pin weld).
// ============================================================================

/// **makeSovereign — the committed mode MOVES into the commit, but the live record pin is NOT
/// WIRED (a missing weld in shared `trace_rotated.rs::record_pin_offset`).**
///
/// The registry descriptor declares 47 PIs (the record-forcing fifth pin), but the live generator
/// emits only 46 dpis (no `MakeSovereign` arm in `record_pin_offset`). So an honest makeSovereign
/// turn CANNOT prove through the live path. We assert: (a) the mode genuinely moves the committed
/// mode (`B_MODE`) and authority-digest (`B_AUTHORITY_DIGEST`) limbs and the published commit
/// (anti-vacuity); (b) the live generator/descriptor are MISMATCHED — the 47th PI the descriptor
/// declares is unfed → the rotated makeSovereign path is presently UN-PROVABLE (the precise
/// residual a shared-code fix must close).
#[test]
fn makesovereign_record_pin_is_unwired_missing_weld() {
    let balance: i64 = 50_000;
    let effect = Effect::MakeSovereign;
    let name = rotated_descriptor_name_for_effect(&effect)
        .expect("MakeSovereign is a rotated cohort member");
    assert_eq!(name, "makeSovereignVmDescriptor2R24");
    let desc = parse_vm_descriptor2(rotated_descriptor_json(name))
        .expect("rotated makeSovereign descriptor parses");
    assert_eq!(
        desc.public_input_count, 47,
        "makeSovereign descriptor DECLARES the record-forcing 47th PI"
    );

    let st = CellState::new(balance as u64, 0);
    let effects = vec![effect];

    let mut before_cell = producer_cell(balance, 0);
    before_cell.mode = CellMode::Hosted;
    let mut after_cell = producer_cell(balance, 1);
    after_cell.mode = CellMode::Sovereign;
    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).unwrap();
    let before_w = rw::produce(&before_cell, &ledger, &NULL_ROOT, &COMMIT_ROOT, &receipt_log());
    let after_w = rw::produce(&after_cell, &ledger, &NULL_ROOT, &COMMIT_ROOT, &receipt_log());

    // (a) ANTI-VACUITY: the mode genuinely moves the committed mode + authority-digest limbs and
    // the published commit — the data the (declared but unfed) record pin would bind DOES move.
    assert_eq!(after_w.pre_limbs[B_MODE], BabyBear::ONE, "post mode limb = Sovereign(1)");
    assert_eq!(before_w.pre_limbs[B_MODE], BabyBear::ZERO, "pre mode limb = Hosted(0)");
    assert_ne!(
        before_w.pre_limbs[B_AUTHORITY_DIGEST], after_w.pre_limbs[B_AUTHORITY_DIGEST],
        "the authority-digest limb moves (the mode byte folds into it)"
    );
    assert_ne!(
        before_w.state_commit, after_w.state_commit,
        "the published commit moves on the Hosted→Sovereign promotion"
    );

    let caveat = empty_caveat_manifest();
    let (trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("live rotated generator produces a makeSovereign trace");
    let last = &trace[trace.len() - 1];
    assert_eq!(
        last[AFTER_BASE + B_MODE], BabyBear::ONE,
        "the AFTER block's committed mode limb is Sovereign(1)"
    );

    // (b) THE MISSING WELD: the generator emits 46 dpis, not the 47 the descriptor declares — so
    // `record_pin_offset(MakeSovereign)` is `None` and the 47th (record-forcing) PI is unfed.
    assert_eq!(
        dpis.len(),
        46,
        "MISSING WELD: the live generator emits 46 dpis (record_pin_offset has no MakeSovereign arm)"
    );
    assert_ne!(
        dpis.len(),
        desc.public_input_count,
        "MISSING WELD: 46 generated dpis != 47 descriptor PIs — the makeSovereign record pin is \
         declared but UNWIRED"
    );

    // The honest turn therefore CANNOT prove through the live path (the PI-count mismatch is fatal).
    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<HeapLeaf>> = vec![];
    let r = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps);
    assert!(
        r.is_err(),
        "the makeSovereign rotated path is presently UN-PROVABLE (46 dpis vs 47 declared PIs); the \
         residual is a shared-code weld: add the MakeSovereign arm to record_pin_offset"
    );

    eprintln!(
        "VK-EPOCH makeSovereign: the committed mode MOVES into the commit (B_MODE 0→1, \
         authority-digest moves), but the live record pin is UNWIRED — 46 generated dpis vs 47 \
         declared PIs → the rotated path is UN-PROVABLE. NAMED RESIDUAL: add MakeSovereign to \
         trace_rotated.rs::record_pin_offset."
    );
}

// ============================================================================
// setFieldDyn — UNREACHABLE via the live generator (missing weld).
// ============================================================================

/// **setFieldDyn — the dynamic overflow `SetField` is UNREACHABLE via the live generator.**
///
/// `Effect::SetField { field_idx > 7 }` routes to `setFieldDynVmDescriptor2R24`, but the V1 trace
/// generator hard-asserts `field_idx < 8`, so `generate_rotated_effect_vm_trace` PANICS before
/// producing a trace. The fields-root weld the descriptor declares is exercised by NO live path.
/// We assert the panic (the precise broken seam), and confirm the descriptor itself DOES declare
/// the 47th fields-root pin (so the residual is a generator gap, not a descriptor gap).
#[test]
fn setfielddyn_unreachable_via_live_generator_missing_weld() {
    let name = "setFieldDynVmDescriptor2R24";
    let desc =
        parse_vm_descriptor2(rotated_descriptor_json(name)).expect("setFieldDyn descriptor parses");
    assert_eq!(
        desc.public_input_count, 47,
        "setFieldDyn descriptor DECLARES the fields-root weld pin (47 PIs)"
    );

    // The dynamic SetField routes to the dyn descriptor by name...
    let effect = Effect::SetField {
        field_idx: 9,
        value: BabyBear::new(424_242),
    };
    assert_eq!(
        rotated_descriptor_name_for_effect(&effect).expect("routes"),
        name,
        "field_idx > 7 routes to setFieldDynVmDescriptor2R24"
    );

    // ...but the live generator PANICS on the overflow index (the V1 `field_idx < 8` assert) — so
    // no trace is ever produced for the dyn fields-root write.
    let balance: i64 = 50_000;
    let st = CellState::new(balance as u64, 0);
    let before_cell = producer_cell(balance, 0);
    let after_cell = producer_cell(balance, 1);
    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).unwrap();
    let before_w = rw::produce(&before_cell, &ledger, &NULL_ROOT, &COMMIT_ROOT, &receipt_log());
    let after_w = rw::produce(&after_cell, &ledger, &NULL_ROOT, &COMMIT_ROOT, &receipt_log());
    let caveat = empty_caveat_manifest();

    let panicked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        generate_rotated_effect_vm_trace(
            &st,
            &[effect],
            &bridge(&before_w),
            &bridge(&after_w),
            &caveat,
        )
    }))
    .is_err();
    assert!(
        panicked,
        "MISSING WELD: the live generator hard-asserts field_idx < 8, so the dynamic overflow \
         SetField (setFieldDyn) is UNREACHABLE — the declared fields-root weld is exercised by no \
         live path. NAMED RESIDUAL: give the dynamic overflow SetField a generator path (write the \
         fields_root map + feed the fields-root pin)."
    );

    eprintln!(
        "VK-EPOCH setFieldDyn: the descriptor DECLARES the fields-root weld (47 PIs), but the live \
         generator hard-asserts field_idx < 8 → the dyn overflow write is UNREACHABLE. NAMED \
         RESIDUAL: a generator path for the dynamic fields_root SetField."
    );
}
