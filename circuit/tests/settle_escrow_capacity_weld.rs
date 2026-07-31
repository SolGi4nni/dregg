//! # The sealed-escrow CAPACITY WELD exerciser — coverage ∧ satisfaction, against the DEPLOYED
//! carrier and the EMITTED welded descriptor (VK-EPOCH §6 BLOCKER 1, STAGED).
//!
//! This is the live capacity-caveat-bearing exerciser the prior VK-epoch pass found ABSENT ("no
//! deployed cell declares a capacity caveat, so even a flipped default has no exerciser"). It ties
//! the two halves of the sealed-escrow house-capacity light-client weld together for a turn that
//! DECLARES the escrow capacity (a `SlotCaveatEntry` with tag 17 over leg slots 0/1):
//!
//!  * **COVERAGE (PIECE 1, deployed):** the declared caveat projects onto the AIR-bound rotated
//!    carrier (`slot_caveats_to_rotated_manifest`); the carrier binds it into the ~124-bit wide
//!    commit, so a forger cannot OMIT it (`verify_rotated_caveat_coverage` rejects an omitting
//!    manifest). Lean: `CapacityCarrier.carrier_omission_impossible`.
//!  * **SATISFACTION (PIECE 2, staged):** the EMITTED `settleEscrowSatVmDescriptor2R24` carries the
//!    four selector-gated satisfaction gates over the rotated FIELD columns. An honest settle (both
//!    legs `Deposited` before, `Consumed` after, selector on) makes every welded gate vanish; a
//!    forged partial / phantom settle makes a gate body NON-zero — UNSAT in the welded path. Lean:
//!    `SettleEscrowSatDescriptor.settleEscrowSatV3_forces_settle_gate` + the partial/phantom UNSAT
//!    teeth.
//!
//! ## What this exercises and what it does NOT (no overclaim)
//!
//! It demonstrates the teeth biting at the EMITTED descriptor's CONSTRAINT level — the welded gates
//! pulled straight from the committed registry TSV, evaluated over honest and forged settle rows —
//! NOT a full STARK prove/verify of the welded descriptor. The remaining mechanical step to a
//! flippable escrow weld is a producer that emits a SATISFYING rotated trace for the welded
//! descriptor (the field-override + commit-recompute surgery the fee/nullifier producers do for
//! balance/nullifier limbs), then committing its VK and binding the selector to the committed
//! declaration in-AIR (`DeclCommitBinds`, §6 item 2). The descriptor + selector + refinement exist;
//! the satisfaction weld is STAGED, NOT flipped.

use dregg_circuit::descriptor_ir2::{VmConstraint2, eval_lean_expr, parse_vm_descriptor2};
use dregg_circuit::effect_vm::SlotCaveatEntry;
use dregg_circuit::effect_vm::pi;
use dregg_circuit::effect_vm::satisfaction_weld::{
    ESCROW_SEL_COL, after_field_col, before_field_col,
};
use dregg_circuit::effect_vm::trace_rotated::slot_caveats_to_rotated_manifest;
use dregg_circuit::effect_vm::verify_rotated_caveat_coverage;
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint};

const LEG_A: usize = 0;
const LEG_B: usize = 1;

/// A declared sealed-escrow capacity caveat (tag 17), legs in field slots 0/1 — exactly what the
/// executor's `project_slot_caveat_manifest` emits for `StateConstraint::SettleEscrow { 0, 1 }`.
fn escrow_caveat() -> SlotCaveatEntry {
    SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW,
        slot_index: LEG_A as u8,
        params: [
            BabyBear::new(LEG_B as u32),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
    }
}

#[test]
fn coverage_the_declared_escrow_caveat_cannot_be_omitted() {
    // The declared caveat projects onto the AIR-bound rotated carrier...
    let manifest =
        slot_caveats_to_rotated_manifest(&[escrow_caveat()]).expect("projects onto the carrier");
    assert!(
        manifest.covers_tag(pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW),
        "the projected manifest covers the declared escrow tag"
    );
    verify_rotated_caveat_coverage(&manifest, &[pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW])
        .expect("coverage holds for the declared escrow capacity (the carrier binds it)");

    // ...and an OMITTING (empty) manifest does NOT cover it — the omission tooth (PIECE 1).
    let empty = slot_caveats_to_rotated_manifest(&[]).expect("empty manifest projects");
    assert!(
        !empty.covers_tag(pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW),
        "the omitting manifest does not cover the escrow tag"
    );
    assert!(
        verify_rotated_caveat_coverage(&empty, &[pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW]).is_err(),
        "coverage REJECTS an omitting manifest — the forger cannot drop the declared capacity entry"
    );
}

/// Pull the EMITTED welded satisfaction gates (`.gate` bodies `mul(var ESCROW_SEL_COL, _)`) straight
/// from the committed registry TSV.
fn emitted_welded_gates() -> Vec<LeanExpr> {
    let json = V3_STAGED_REGISTRY_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some("settleEscrowSatVmDescriptor2R24") {
                let _name = it.next();
                it.next()
            } else {
                None
            }
        })
        .expect("settleEscrowSatVmDescriptor2R24 in the staged registry");
    let desc = parse_vm_descriptor2(json).expect("welded escrow descriptor parses");
    // Read the BODY through `row_local_body`, not the constraint KIND: the last-row hardening flag
    // day moved every row-local body from the transition-domain `Gate` onto a whole-domain
    // `windowGate`, and a kind-match here collected zero.
    desc.constraints
        .iter()
        .filter_map(|c| {
            let body = dregg_circuit::descriptor_ir2::row_local_body(c)?;
            match body.as_ref() {
                LeanExpr::Mul(l, _) if **l == LeanExpr::Var(ESCROW_SEL_COL) => {
                    Some(body.into_owned())
                }
                _ => None,
            }
        })
        .collect()
}

/// A 609-wide settle row: selector on/off, the four rotated leg field columns set.
fn settle_row(sel: u32, before_a: u32, before_b: u32, after_a: u32, after_b: u32) -> Vec<BabyBear> {
    let width = after_field_col(7).max(ESCROW_SEL_COL) + 1;
    let mut row = vec![BabyBear::ZERO; width.max(609)];
    row[ESCROW_SEL_COL] = BabyBear::new(sel);
    row[before_field_col(LEG_A)] = BabyBear::new(before_a);
    row[before_field_col(LEG_B)] = BabyBear::new(before_b);
    row[after_field_col(LEG_A)] = BabyBear::new(after_a);
    row[after_field_col(LEG_B)] = BabyBear::new(after_b);
    row
}

#[test]
fn satisfaction_emitted_descriptor_accepts_honest_rejects_forged() {
    let gates = emitted_welded_gates();
    assert_eq!(
        gates.len(),
        4,
        "the emitted descriptor carries four welded satisfaction gates"
    );

    let dep = pi::SETTLE_ESCROW_STATUS_DEPOSITED;
    let con = pi::SETTLE_ESCROW_STATUS_CONSUMED;
    let all_zero = |row: &[BabyBear]| {
        gates
            .iter()
            .all(|g| eval_lean_expr(g, row) == BabyBear::ZERO)
    };

    // HONEST settle: selector on, both legs Deposited→Consumed — accepted (every gate vanishes).
    assert!(
        all_zero(&settle_row(1, dep, dep, con, con)),
        "the honest settle satisfies every EMITTED welded gate"
    );
    // FORGED partial: leg B left Deposited after — a welded gate bites (UNSAT).
    assert!(
        !all_zero(&settle_row(1, dep, dep, con, dep)),
        "a partial settle (leg B unswapped) violates an EMITTED welded gate"
    );
    // FORGED phantom: leg A never Deposited before (Empty) — a welded gate bites (UNSAT).
    assert!(
        !all_zero(&settle_row(1, 0, dep, con, con)),
        "a phantom settle (leg A never locked) violates an EMITTED welded gate"
    );
    // SELECTOR OFF (non-capacity / padding row): the gates are inert even with arbitrary fields.
    assert!(
        all_zero(&settle_row(0, 7, 9, 3, 4)),
        "with the selector 0 the welded gates are inert (no false reject off a declared turn)"
    );
}
