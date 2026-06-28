//! PIECE 1 of the VK epoch — the CAPACITY CARRIER (STAGED).
//!
//! The capacity manifest (tags 17/18/19) projected onto the AIR-bound rotated caveat
//! carrier (`RotatedCaveatManifest`, whose `caveatCommit` is pinned to PI 45 on every
//! deployed R=24 cohort descriptor). These tests pin the producer projection
//! (`slot_caveats_to_rotated_manifest`) and the bound-leg coverage verifier
//! (`verify_rotated_caveat_coverage`) — the Rust shadow of the Lean
//! `Dregg2.Deos.CapacityCarrier.{carrier_omission_impossible, carrier_coverage_forced}`.
//! Omission on the bound leg is rejected; an honest covering manifest is accepted.

use dregg_circuit::effect_vm::trace_rotated::{
    RotatedCaveatManifest, slot_caveats_to_rotated_manifest,
};
use dregg_circuit::effect_vm::{SlotCaveatEntry, pi, verify_rotated_caveat_coverage};
use dregg_circuit::field::BabyBear;

const SETTLE: u32 = pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW; // 17
const DISCHARGE: u32 = pi::SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION; // 18
const VAULT: u32 = pi::SLOT_CAVEAT_TAG_VAULT_DEPOSIT; // 19

fn escrow_entry() -> SlotCaveatEntry {
    SlotCaveatEntry {
        type_tag: SETTLE,
        slot_index: 3,
        params: [
            BabyBear::new(4),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
    }
}

#[test]
fn projection_is_faithful_to_the_registers_domain() {
    use dregg_circuit::effect_vm::columns::rotation::caveat as cav;
    let m = slot_caveats_to_rotated_manifest(&[escrow_entry()]).unwrap();
    let e = &m.entries[0];
    assert_eq!(e.type_tag, SETTLE, "type tag preserved");
    assert_eq!(
        e.domain_tag,
        cav::DOMAIN_REGISTERS,
        "slot caveats land in the registers domain"
    );
    assert_eq!(e.key, BabyBear::new(3), "slot_index widens to the felt key");
    assert_eq!(
        e.params[0],
        BabyBear::new(4),
        "params preserved positionally"
    );
    // The remaining slots are the zero ("no caveat") padding.
    assert_eq!(m.entries[1].type_tag, 0);
}

#[test]
fn honest_manifest_covers_its_required_tag() {
    let m = slot_caveats_to_rotated_manifest(&[escrow_entry()]).unwrap();
    assert!(m.covers_tag(SETTLE));
    assert!(verify_rotated_caveat_coverage(&m, &[SETTLE]).is_ok());
}

#[test]
fn omission_on_the_bound_leg_is_rejected() {
    // The forger's count=0 dodge: the empty manifest does NOT cover the declared tag.
    let empty = RotatedCaveatManifest::default();
    assert!(!empty.covers_tag(SETTLE));
    assert!(
        verify_rotated_caveat_coverage(&empty, &[SETTLE]).is_err(),
        "a declared capacity tag absent from the bound rotated manifest must be rejected"
    );
}

#[test]
fn wrong_tag_does_not_cover() {
    // A manifest carrying a DIFFERENT capacity tag (vault) does not cover the required escrow tag.
    let m = slot_caveats_to_rotated_manifest(&[SlotCaveatEntry {
        type_tag: VAULT,
        slot_index: 0,
        params: [
            BabyBear::new(1),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
    }])
    .unwrap();
    assert!(!m.covers_tag(SETTLE));
    assert!(verify_rotated_caveat_coverage(&m, &[SETTLE]).is_err());
    // ...but it DOES cover its own tag.
    assert!(verify_rotated_caveat_coverage(&m, &[VAULT]).is_ok());
}

#[test]
fn multi_tag_coverage_demands_all() {
    let m = slot_caveats_to_rotated_manifest(&[
        escrow_entry(),
        SlotCaveatEntry {
            type_tag: DISCHARGE,
            slot_index: 1,
            params: [
                BabyBear::new(2),
                BabyBear::new(3),
                BabyBear::new(4),
                BabyBear::new(5),
            ],
        },
    ])
    .unwrap();
    assert!(verify_rotated_caveat_coverage(&m, &[SETTLE, DISCHARGE]).is_ok());
    // Dropping the discharge entry leaves a required tag uncovered.
    let only_escrow = slot_caveats_to_rotated_manifest(&[escrow_entry()]).unwrap();
    assert!(verify_rotated_caveat_coverage(&only_escrow, &[SETTLE, DISCHARGE]).is_err());
}

#[test]
fn overlong_manifest_fails_closed() {
    // More entries than the carrier width — REFUSED, never silently truncated (truncation could
    // drop a declared capacity gate).
    let many = vec![escrow_entry(); 5];
    assert!(slot_caveats_to_rotated_manifest(&many).is_err());
}

#[test]
fn empty_required_set_is_vacuously_ok() {
    let empty = RotatedCaveatManifest::default();
    assert!(verify_rotated_caveat_coverage(&empty, &[]).is_ok());
}
