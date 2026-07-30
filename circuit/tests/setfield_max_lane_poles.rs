//! # BOTH POLES of the EffectVM's `SetField` field-index bound (GitHub #61 / #62).
//!
//! The helm fleet reported `SetField field_idx out of bounds: 8` from the node's prover, on
//! turns that had already committed and receipted. The bound is CORRECT — the deployed AIR
//! carries `state::NUM_FIELDS` developer field lanes and the Lean that authors it types the
//! slot as `Fin 8` (pinned by `setfield_air_lane_bound_pin.rs`). What was wrong is that the
//! bound was enforced by `assert!` inside the prover, i.e. AFTER commit, as a panic.
//!
//! Two poles, and neither is satisfiable by the other's fix:
//!
//!   * **ACCEPT** — a write to the LAST slot the AIR does have a lane for (`NUM_FIELDS − 1`)
//!     PROVES and VERIFIES through the deployed per-slot descriptor, and the value LANDS in
//!     that slot's committed column. "No longer panics" is trivially satisfiable by deleting
//!     the check; this pole is not, because it asserts the write actually happened in the
//!     trace the proof is over.
//!   * **REFUSE** — a write to the FIRST slot with no lane (`NUM_FIELDS`, the exact index in
//!     #61's panic string) is refused BY TYPED VALUE at every door that a committed turn can
//!     reach: the executor's checked projection, the SDK's checked projection, and the trace
//!     generator itself. NOT by panic — the refusal has to survive being carried past the
//!     finalized path's durable commit-log write, which is what #62 is.
//!
//! Both indices are DERIVED from `state::NUM_FIELDS`, never written as `7`/`8`. If the AIR is
//! ever genuinely widened (a Lean edit, a full descriptor re-emit and a VK rotation), these
//! poles move with it instead of pinning a dead number.

use dregg_cell::{Cell, CellId, Ledger};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::{
    AFTER_BASE, empty_caveat_manifest, generate_rotated_effect_vm_trace,
    rotated_descriptor_name_for_effect,
};
use dregg_circuit::effect_vm::{
    CellState, Effect, EffectVmTraceError, field_limbs8, state, try_generate_effect_vm_trace,
};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_turn::rotation_witness as rw;

/// The LAST slot the deployed AIR carries a column for — the true maximum.
const MAX_PROVABLE_SLOT: usize = state::NUM_FIELDS - 1;
/// The FIRST slot it does not. This is the literal index in #61's panic text.
const FIRST_UNPROVABLE_SLOT: usize = state::NUM_FIELDS;

/// In-block offset of the AFTER rotated block's committed `fields[i]` lane-0 limb. The field
/// register `r(FIELD_BASE + i)` rides offset `CUSTOM_APP_FIELD_ROT_BASE + i` (Lean-emitted, in
/// `layout_generated`), so the written slot's committed value is readable off the trace.
fn after_field_limb0_offset(slot: usize) -> usize {
    dregg_circuit::effect_vm::layout_generated::CUSTOM_APP_FIELD_ROT_BASE + slot
}

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

fn producer_cell(balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    Cell::with_balance(pk, [0u8; 32], balance)
}

fn bridge(w: &rw::RotationWitness) -> dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness {
    dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot)
        .expect("pre-iroot limbs")
}

fn witness(cell: &Cell, ledger: &Ledger) -> rw::RotationWitness {
    rw::produce(
        cell,
        ledger,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &[[3u8; 32]],
        &Default::default(),
    )
}

// ═════════════════════════════════════════════════════════════════════════════════════
// POLE 1 — ACCEPT: the true maximum slot proves, verifies, and the write LANDS.
// ═════════════════════════════════════════════════════════════════════════════════════

/// A write to `NUM_FIELDS − 1` — the highest slot with a state-block column — must prove and
/// verify against the deployed `setFieldVmDescriptor2-{max}R24`, AND the written value must be
/// the one the AFTER block commits at that slot's lane-0 limb.
///
/// ANTI-VACUITY: the value check is the point. A "fix" that removed the bound entirely, or one
/// that clamped out-of-range indices onto slot 7 (which is what `trace.rs`'s deleted
/// `idx.min(7)` did), would still "not panic" — but it would not put THIS value in THIS slot
/// while leaving its neighbours untouched. So we assert the moved column and its bystanders.
#[test]
fn the_maximum_provable_slot_proves_verifies_and_the_write_lands() {
    let balance: i64 = 50_000;
    // A lane-0-only value (low 4 big-endian bytes) so the deployed completion-lane weld holds
    // for the honest write — the same shape `setfield_completion_lane_forge.rs` uses.
    let mut field_bytes = [0u8; 32];
    field_bytes[28..32].copy_from_slice(&0x0055_AA33u32.to_be_bytes());
    let lane0 = field_limbs8(&field_bytes)[0];

    let effect = Effect::SetField {
        field_idx: MAX_PROVABLE_SLOT as u32,
        value: lane0,
    };

    // The deployed per-slot member, resolved by the SAME router the live prover uses.
    let name = rotated_descriptor_name_for_effect(&effect).expect("setField is a cohort member");
    assert_eq!(
        name,
        format!("setFieldVmDescriptor2-{MAX_PROVABLE_SLOT}R24"),
        "the maximum provable slot must route to its OWN per-slot member, not to the dynamic \
         overflow descriptor"
    );
    let desc = parse_vm_descriptor2(rotated_descriptor_json(name)).expect("descriptor parses");

    let before_cell = producer_cell(balance);
    let mut after_cell = producer_cell(balance);
    assert!(
        after_cell.state.set_field(MAX_PROVABLE_SLOT, field_bytes),
        "slot {MAX_PROVABLE_SLOT} is inside STATE_SLOTS and must be settable on the cell"
    );

    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).unwrap();
    let before_w = witness(&before_cell, &ledger);
    let after_w = witness(&after_cell, &ledger);

    let st = CellState::new(balance as u64, 0);
    let (trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        std::slice::from_ref(&effect),
        &bridge(&before_w),
        &bridge(&after_w),
        &empty_caveat_manifest(),
    )
    .expect("the live rotated generator must produce a max-slot setField trace + PIs");

    // ── THE WRITE LANDED. The AFTER block's committed lane-0 limb for the written slot carries
    //    the value, and every OTHER field slot is untouched. This is what separates a real fix
    //    from "the assert is gone".
    let last = trace.last().expect("non-empty trace");
    let written = last[AFTER_BASE + after_field_limb0_offset(MAX_PROVABLE_SLOT)];
    assert_eq!(
        written, lane0,
        "the AFTER block must commit the written value at slot {MAX_PROVABLE_SLOT}'s lane-0 limb"
    );
    for other in 0..state::NUM_FIELDS {
        if other == MAX_PROVABLE_SLOT {
            continue;
        }
        assert_eq!(
            last[AFTER_BASE + after_field_limb0_offset(other)],
            BabyBear::ZERO,
            "slot {other} is a bystander of a write to {MAX_PROVABLE_SLOT} and must be frozen at \
             its pre-state — a value appearing here would mean the index was clamped or aliased"
        );
    }

    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &MemBoundaryWitness::default(), &[])
        .expect("an honest write to the MAXIMUM provable slot must prove on the deployed member");
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .expect("an honest max-slot setField proof must verify");

    eprintln!(
        "POLE 1 GREEN: slot {MAX_PROVABLE_SLOT} (= NUM_FIELDS-1) proves + verifies on \
         {name}, and the AFTER block commits the written value at that slot."
    );
}

/// The v1 trace generator — the one that used to `assert!` — must ACCEPT every slot the AIR
/// has a lane for and write each to its OWN column. Cheap (no prove), and it is the direct
/// non-vacuity companion to the refusal below: the checked generator is not simply refusing
/// everything.
#[test]
fn the_checked_generator_accepts_every_lane_and_writes_each_to_its_own_column() {
    let st = CellState::new(10_000, 0);
    for slot in 0..state::NUM_FIELDS {
        let value = BabyBear::new(0x1000 + slot as u32);
        let (trace, _pi) = try_generate_effect_vm_trace(
            &st,
            &[Effect::SetField {
                field_idx: slot as u32,
                value,
            }],
        )
        .unwrap_or_else(|e| panic!("slot {slot} has an AIR lane and must generate a trace: {e}"));

        let after = dregg_circuit::effect_vm::STATE_AFTER_BASE + state::FIELD_BASE;
        assert_eq!(
            trace[0][after + slot],
            value,
            "the write must land in slot {slot}'s OWN state_after column"
        );
        for other in 0..state::NUM_FIELDS {
            if other != slot {
                assert_eq!(
                    trace[0][after + other],
                    BabyBear::ZERO,
                    "writing slot {slot} must not disturb slot {other}"
                );
            }
        }
    }
}

// ═════════════════════════════════════════════════════════════════════════════════════
// POLE 2 — REFUSE: the first slot with no lane is refused by VALUE at every door.
// ═════════════════════════════════════════════════════════════════════════════════════

/// The prover's own door. `try_generate_effect_vm_trace` must RETURN the refusal, naming the
/// offending index and the lane count — never unwind.
///
/// ANTI-VACUITY: `catch_unwind` is wrapped around the call so a regression back to `assert!`
/// fails HERE rather than being reported as a passing `Err`. The old code panicked with
/// exactly `"SetField field_idx out of bounds: 8 (must be 0..7)"`, which is the string the
/// helm fleet pasted into #61.
#[test]
fn the_checked_generator_returns_the_refusal_and_does_not_unwind() {
    let st = CellState::new(10_000, 0);
    let effects = [Effect::SetField {
        field_idx: FIRST_UNPROVABLE_SLOT as u32,
        value: BabyBear::new(0xBEEF),
    }];

    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        try_generate_effect_vm_trace(&st, &effects)
    }))
    .expect(
        "the trace generator UNWOUND on an out-of-lane SetField. That is the #62 defect: on the \
         finalized path this call sits upstream of the durable commit-log write in the same \
         function, so an unwind here means the turn is receipted and never persisted.",
    );

    assert_eq!(
        outcome,
        Err(EffectVmTraceError::FieldIndexOutOfRange {
            field_idx: FIRST_UNPROVABLE_SLOT as u32,
            lanes: state::NUM_FIELDS,
        }),
        "the refusal must be the typed variant carrying BOTH the offending index and the lane \
         count, so a caller can log which slot and route around it"
    );

    // The message a node operator will actually see must name the index, the bound, and why —
    // the reporter was promised a measurement, not "invalid witness".
    let rendered = outcome.unwrap_err().to_string();
    for needle in [
        &FIRST_UNPROVABLE_SLOT.to_string()[..],
        "authority residue",
        "REFUSAL",
    ] {
        assert!(
            rendered.contains(needle),
            "the rendered refusal must contain {needle:?}; got: {rendered}"
        );
    }
}

/// The EXECUTOR's checked projection door — the one a committed turn passes through — must
/// refuse the same index by typed variant, before any prover is reached.
#[test]
fn the_executor_projection_refuses_the_first_unprovable_slot_by_variant() {
    use dregg_turn::executor::{EffectVmProjectionError, try_convert_turn_effects_to_vm};

    let cell = CellId([0x61; 32]);
    let turn = set_field_turn(cell, FIRST_UNPROVABLE_SLOT as u64);

    assert_eq!(
        try_convert_turn_effects_to_vm(&cell, &turn),
        Err(EffectVmProjectionError::UnprovableFieldIndex {
            index: FIRST_UNPROVABLE_SLOT as u64,
            lanes: state::NUM_FIELDS,
        }),
    );

    // And the door still ADMITS the maximum provable slot — the refusal is a bound, not a wall.
    assert!(
        try_convert_turn_effects_to_vm(&cell, &set_field_turn(cell, MAX_PROVABLE_SLOT as u64))
            .is_ok(),
        "slot {MAX_PROVABLE_SLOT} must still project"
    );
}

/// **THE ROUTING NOTE, PINNED.** `field_idx >= NUM_FIELDS` resolves to a DIFFERENT descriptor
/// (`setFieldDynVmDescriptor2R24`) — a distinct geometry with its own Blum linear-memory
/// witness. That member exists and proves in isolation, so it is easy to mistake for a real
/// answer for slots 8..15. It is NOT one on the node's path, and this pins the reason:
///
///   * its in-circuit address is `field_idx % NUM_FIELDS`, so slots 8 and 16 and 24 collapse to
///     the same memory cell — the raw index is not bound;
///   * its producer takes a SYNTHETIC in-bounds lead (`SetField { field_idx: slot, value: slot }`)
///     and then FORCES the AFTER `fields_root` limb to the slot number before recomputing the
///     block commitment, so the published NEW commit is over a fabricated fields_root rather
///     than the real cell's;
///   * it has no production call site outside the SDK's standalone sovereign precompute.
///
/// Routing the node at it would mint an attestation that disagrees with the committed cell —
/// strictly worse than the refusal. Recorded here so the next reader does not "just route it".
#[test]
fn the_overflow_index_routes_to_a_distinct_descriptor_not_a_wider_one() {
    let dyn_name = rotated_descriptor_name_for_effect(&Effect::SetField {
        field_idx: FIRST_UNPROVABLE_SLOT as u32,
        value: BabyBear::ZERO,
    })
    .expect("SetField always resolves a name");
    assert_eq!(dyn_name, "setFieldDynVmDescriptor2R24");

    // It is a DIFFERENT descriptor, not a wider per-slot one: its trace width and PI count
    // differ from the static member's, so a producer cannot swap one for the other.
    let stat = parse_vm_descriptor2(rotated_descriptor_json(&format!(
        "setFieldVmDescriptor2-{MAX_PROVABLE_SLOT}R24"
    )))
    .expect("static member parses");
    let dynd = parse_vm_descriptor2(rotated_descriptor_json(dyn_name)).expect("dyn member parses");
    assert_ne!(
        (stat.trace_width, stat.public_input_count),
        (dynd.trace_width, dynd.public_input_count),
        "the dyn member must remain a DISTINCT geometry; if these ever coincide, the claim that \
         it cannot substitute for a per-slot write needs re-measuring"
    );
}

fn set_field_turn(cell: CellId, index: u64) -> dregg_turn::Turn {
    use dregg_turn::action::{Action, Authorization, CommitmentMode, DelegationMode};
    use dregg_turn::forest::CallForest;

    let action = Action {
        target: cell,
        method: [0; 32],
        args: Vec::new(),
        authorization: Authorization::Unchecked,
        preconditions: dregg_cell::Preconditions::default(),
        effects: vec![dregg_turn::Effect::SetField {
            cell,
            index,
            value: [7; 32],
        }],
        may_delegate: DelegationMode::ParentsOwn,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: Vec::new(),
    };
    let mut call_forest = CallForest::new();
    call_forest.add_root(action);
    dregg_turn::Turn {
        agent: cell,
        nonce: 0,
        call_forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: Vec::new(),
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
