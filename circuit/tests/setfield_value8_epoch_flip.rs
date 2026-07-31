//! # The setField VALUE8 epoch — ADOPTED. The deployed member expresses an honest 32-byte write.
//!
//! The deployed `setFieldVmDescriptor2-{slot}R24` USED to ship the freeze-ALL wrap (`v3OfFrozen
//! (setFieldTickFace slot)`): every one of the written slot's 7 completion lanes — the high 224 bits
//! of the 32-byte value — was frozen BEFORE↔AFTER, so an honest LARGE-value `setField` was REJECTED.
//! The protocol could not express an honest 32-byte field write; a faithful per-trader settlement
//! allocation, a `pack_u64` above 2^32, a board coordinate outside the low lane — none could prove.
//!
//! The VALUE8 shape is now the DEPLOYED shape, in all three live registries. Lean `v3RegistryBare`
//! emits `withSetFieldCompletionPins slot (withSelectorGate SEL_SET_FIELD (setFieldV3 slot))`:
//! freeze-EXCEPT frees the written slot's 7 lanes and 7 `.piBinding .last` pins PUBLISH them as PIs
//! 46..=52 (rc rides 53..56; on the wide twins the 16 anchors ride 57..72). There is no longer a
//! parallel `setFieldValue8VmDescriptor2-*` staging registry — it was deleted with the flip.
//!
//! The teeth (all under the real `prove_vm_descriptor2` / `verify_vm_descriptor2`):
//!   * `honest_large_value_setfield_proves_under_value8` — the seam CLOSED on the 1-felt member.
//!   * `deployed_wide_member_accepts_the_honest_large_write` — ⚑ CONVERTED (see its doc): the
//!     assertion used to be that the deployed member REJECTS this write. It is now the LIVE-PATH
//!     pole: the honest write proves + verifies against the member the light client actually
//!     iterates (`WIDE_REGISTRY_STAGED_TSV`), through the live wide producer.
//!   * `forged_completion_lane_off_the_published_pi_is_unsat` — SOUNDNESS PRESERVED: forging a
//!     completion lane while keeping the honest published PI is UNSAT (the pin binds it).
//!   * `slot_i_value8_proof_binds_uniquely` — the slot-i proof verifies under descriptor-i but NOT
//!     under a sibling descriptor-j (the disjoint completion-pin columns give unique binding).

use dregg_cell::{Cell, Ledger};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::{
    AFTER_BASE, empty_caveat_manifest, generate_rotated_effect_vm_descriptor_and_trace_wide,
    generate_rotated_effect_vm_trace, rotated_descriptor_name_for_effect,
};
use dregg_circuit::effect_vm::{CellState, Effect, fold_bytes32_to_bb};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_turn::rotation_witness as rw;

const SLOT: usize = 3;
/// The written slot's first freed completion lane, absolute trace column (`AFTER_BASE + 113 + 7·slot`)
/// on the 1-felt member — the exact column Lean `withSetFieldCompletionPins` pins to PI 46.
const COMPLETION_COL: usize = AFTER_BASE + 113 + 7 * SLOT;
/// The value8 PI base (the 7 completion pins ride PI 46..=52; rc rides 53..56).
const VALUE8_PI_BASE: usize = 46;

fn tsv_json(tsv: &'static str, name: &str) -> &'static str {
    tsv.lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some(name) {
                let _ = it.next();
                it.next()
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("{name} not in tsv"))
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

struct Fixture {
    st: CellState,
    effects: Vec<Effect>,
    before_w: rw::RotationWitness,
    after_w: rw::RotationWitness,
}

/// An honest single-effect `setField` on `SLOT` whose value has NONZERO high bytes (a real 32-byte
/// `FieldElement` — a cleared amount, a large counter, a packed struct) — the case the deployed
/// freeze-ALL rejected outright.
fn honest_large_fixture() -> Fixture {
    let before: i64 = 50_000;
    let mut field_bytes = [0u8; 32];
    field_bytes[0] = 0xAB; // a high byte → nonzero completion lane
    field_bytes[1] = 0xCD;
    field_bytes[28..32].copy_from_slice(&1_000u32.to_be_bytes());
    let new_value = fold_bytes32_to_bb(&field_bytes);
    let effect = Effect::SetField {
        field_idx: SLOT as u32,
        value: new_value,
    };
    // Sanity: the live routing names the deployed member for this effect.
    assert_eq!(
        rotated_descriptor_name_for_effect(&effect).expect("setField cohort member"),
        "setFieldVmDescriptor2-3R24"
    );

    let mut after_cell = producer_cell(before);
    assert!(after_cell.state.set_field(SLOT, field_bytes), "set_field");
    let st = CellState::new(before as u64, 0);
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let z8 = dregg_circuit::heap_root::empty_heap_root_8();
    let rvk = dregg_turn::rotation_witness::empty_revoked_root_8();
    let rlog = vec![[3u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &z8,
        &z8,
        &rvk,
        &rlog,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &z8,
        &z8,
        &rvk,
        &rlog,
        &Default::default(),
    );
    Fixture {
        st,
        effects: vec![effect],
        before_w,
        after_w,
    }
}

/// The 1-felt (narrow) trace + the generator's own 57-PI vector.
fn build_narrow(f: &Fixture) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    generate_rotated_effect_vm_trace(
        &f.st,
        &f.effects,
        &bridge(&f.before_w),
        &bridge(&f.after_w),
        &empty_caveat_manifest(),
    )
    .expect("live rotated generator must produce a large-value setField trace + PIs")
}

fn deployed_desc(slot: usize) -> EffectVmDescriptor2 {
    let name = format!("setFieldVmDescriptor2-{slot}R24");
    parse_vm_descriptor2(tsv_json(V3_STAGED_REGISTRY_TSV, &name))
        .expect("deployed setField descriptor parses")
}

fn prove_verify(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], dpis: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, dpis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, dpis)
    }));
    matches!(r, Ok(Ok(())))
}

#[test]
fn honest_large_value_setfield_proves_under_value8() {
    let f = honest_large_fixture();
    let (trace, dpis) = build_narrow(&f);
    // Non-vacuity: the large value genuinely moved a written-slot completion lane off zero.
    let any_nonzero = (0..7).any(|k| trace[0][COMPLETION_COL + k] != BabyBear::ZERO);
    assert!(
        any_nonzero,
        "the large value must move a completion lane off zero"
    );

    let desc = deployed_desc(SLOT);
    // ⚑ 1692 → 1736, AND THE CLAIM ABOVE IS NOW FALSE BY DESIGN.
    //
    // This read "the VALUE8 weld adds no column — the deployed width is unmoved", which was true of
    // the seven-lane VALUE8 epoch: those lanes rode completion columns that already existed. The
    // NINE-LANE epoch (`e662ade32`) deliberately adds a column per slot — `fieldLaneCol` places slot
    // j's ninth lane at `176 + j`, consuming the two free pads plus 178..183 — so the width MUST move.
    //
    // Kept as a LITERAL on purpose: the other side is a committed descriptor byte, so re-typing it each
    // epoch IS the review. Verified against the emitted artifact rather than the failure message —
    // every setField member in both registries reads `trace_width: 1736`, so this is a consistent
    // emit, not a partial one.
    assert_eq!(
        desc.trace_width, 1736,
        "the NINE-LANE weld adds one column per slot — the deployed width moved 1692 → 1736"
    );
    // 57 → 58: the ninth lane publishes one more PI. `46 prefix + 8 value8 + 4 rc`, and the emitted
    // descriptor carries pi_binding indices 46..=53 on columns [569..575, 614] — the seventh contiguous
    // plus the ninth at 614, `fieldLaneCol`'s documented NON-CONTIGUOUS placement.
    assert_eq!(desc.public_input_count, 58);
    assert_eq!(
        dpis.len(),
        58,
        "the generator publishes the value8 block AND the ninth lane"
    );

    assert!(
        prove_verify(&desc, &trace, &dpis),
        "an HONEST large-value setField MUST prove + verify against the DEPLOYED 1-felt member \
         (its high 224 bits ride the freed lanes, published as PIs 46..=52)"
    );
    eprintln!("VALUE8: honest large-value setField proves+verifies on the deployed 1-felt member.");
}

/// **⚑ THIS TEST WAS CONVERTED, AND ITS OLD JOB WAS TO ASSERT THE WOUND.** It used to be
/// `deployed_freeze_all_still_rejects_the_large_write`, and it asserted that the SAME honest 32-byte
/// write STILL FAILED the deployed member — that was the point of staging the fix beside the live
/// wire instead of adopting it. Its green meant the live path was still unable to express an honest
/// field write.
///
/// It is now the LIVE-PATH pole, and it is the pole that matters: `verify_effect_vm_rotated_inner`
/// iterates the WIDE registries ONLY (the 1-felt leg was retired on 2026-07-19), so the member a
/// light client actually checks a setField turn against is the WIDE
/// `setFieldVmDescriptor2-{slot}R24` — 73 PIs, S2/E1-compacted columns. This drives the LIVE wide
/// producer end to end and requires the honest large write to prove + verify there.
#[test]
fn deployed_wide_member_accepts_the_honest_large_write() {
    let f = honest_large_fixture();
    let (desc, trace, dpis, map_heaps, mem_boundary) =
        generate_rotated_effect_vm_descriptor_and_trace_wide(
            &f.st,
            &f.effects,
            &bridge(&f.before_w),
            &bridge(&f.after_w),
            &empty_caveat_manifest(),
            None,
            None,
            None,
            None,
        )
        .expect("the LIVE wide producer must build a large-value setField leg");
    assert_eq!(
        desc.public_input_count, 74,
        "the deployed WIDE setField member is 46 prefix + 8 value8 + 4 rc + 16 wide anchors"
    );
    assert_eq!(
        dpis.len(),
        74,
        "the wide producer publishes the value8 block"
    );
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &map_heaps)
        .expect("HONEST 32-byte setField write must PROVE on the LIVE wide member");
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .expect("HONEST 32-byte setField write must VERIFY on the LIVE wide member");
    eprintln!(
        "VALUE8 LIVE POLE: an honest 32-byte setField write proves+verifies through the wide \
         producer against the member the light client iterates."
    );
}

#[test]
fn forged_completion_lane_off_the_published_pi_is_unsat() {
    // SOUNDNESS PRESERVED. Prove the honest baseline, then forge a completion lane in the trace while
    // keeping the honest published PI: the value8 pin (`.piBinding .last col pi`) forces after==pi, so
    // the forge is UNSAT — the high bytes are not an unconstrained free felt.
    let f = honest_large_fixture();
    let (trace, dpis) = build_narrow(&f);
    let desc = deployed_desc(SLOT);
    assert!(
        prove_verify(&desc, &trace, &dpis),
        "honest baseline must prove"
    );

    let mut ftrace = trace.clone();
    // Forge completion lane 0 (col COMPLETION_COL) on the LAST row (the pin reads `.last`) to a value
    // that differs from the published PI 46 (the honest completion). dpis stay honest.
    let last = ftrace.len() - 1;
    let honest = ftrace[last][COMPLETION_COL];
    ftrace[last][COMPLETION_COL] = honest + BabyBear::new(0x9999);
    assert_ne!(
        ftrace[last][COMPLETION_COL], dpis[VALUE8_PI_BASE],
        "forge must differ from the PI"
    );

    assert!(
        !prove_verify(&desc, &ftrace, &dpis),
        "a completion lane forged OFF the published value8 PI MUST be UNSAT (the pin binds the \
         declared value — soundness preserved, not weakened)"
    );
    eprintln!(
        "VALUE8: a completion-lane forge off the published PI is UNSAT — soundness preserved."
    );
}

#[test]
fn slot_i_value8_proof_binds_uniquely() {
    // UNIQUE BINDING. The slot-3 large-write proof (its completion lanes published at PI 46..=52)
    // verifies under descriptor-3 but NOT under a sibling descriptor (e.g. slot 0), which pins
    // slot-0's frozen completion lanes to the SAME PI slots — a mismatch the slot-3 trace violates.
    // This is the "selector binding ambiguous" reject the deployed freeze-ALL could not give the
    // light client.
    let f = honest_large_fixture();
    let (trace, dpis) = build_narrow(&f);

    assert!(
        prove_verify(&deployed_desc(SLOT), &trace, &dpis),
        "the slot-3 proof verifies under its OWN deployed descriptor"
    );
    for other in [0usize, 1, 2, 4] {
        assert!(
            !prove_verify(&deployed_desc(other), &trace, &dpis),
            "the slot-3 proof MUST NOT verify under the slot-{other} descriptor (unique binding)"
        );
    }
    eprintln!("VALUE8: the slot-3 proof binds UNIQUELY to descriptor-3 (disjoint pin columns).");
}
