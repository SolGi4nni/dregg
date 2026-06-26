//! # The 3 live-only WIDE members (the flip-coverage gap CLOSED).
//!
//! The WIDE registry (`WIDE_REGISTRY_STAGED_TSV`) is now a member-for-member, name-stable COVER of
//! the live V3 registry (`rotation-v3-staged-registry.tsv`, 57 members). Three members were live-only
//! before this slice — `transferCapOpenTBVmDescriptor2R24` / `heapWriteVmDescriptor2R24` /
//! `supplyMintVmDescriptor2R24`. Each is now present at its faithful `wideAppend` geometry, carrying
//! the 16 wide-commit PIs (the 8-felt ~124-bit before/after anchors). This test pins:
//!   * all 3 carry exactly 16 wide-commit PIs at the top of their PI vector (the anchors, NO narrowing);
//!   * `supplyMint` PROVES + light-client VERIFIES end-to-end at the wide geometry through the live
//!     wide dispatcher (`generate_rotated_effect_vm_descriptor_and_trace_wide`).
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::{
    RotatedBlockWitness, empty_caveat_manifest, generate_rotated_effect_vm_descriptor_and_trace_wide,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;
use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_turn::rotation_witness as rw;

fn wide_json(name: &str) -> &'static str {
    WIDE_REGISTRY_STAGED_TSV
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
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("pre-iroot limbs")
}

/// Every new member carries 16 wide-commit PiBindings (the 8-felt before/after anchors).
#[test]
fn new_wide_members_carry_16_commit_pis() {
    for (name, want_w, want_pi) in [
        ("transferCapOpenTBVmDescriptor2R24", 1029usize, 65usize),
        ("heapWriteVmDescriptor2R24", 803, 20),
        ("supplyMintVmDescriptor2R24", 817, 62),
    ] {
        let d = parse_vm_descriptor2(wide_json(name)).unwrap();
        assert_eq!(d.trace_width, want_w, "{name} wide width");
        assert_eq!(d.public_input_count, want_pi, "{name} wide PI count");
        // the top 16 PIs are the wide commit anchors: piCount-16 .. piCount must each be bound.
        let mut top_pis = std::collections::BTreeSet::new();
        for c in &d.constraints {
            if let Some(pi) = pi_index_of(c) {
                if pi >= want_pi - 16 {
                    top_pis.insert(pi);
                }
            }
        }
        assert_eq!(
            top_pis.len(),
            16,
            "{name}: the 8-felt before/after anchors = 16 wide-commit PIs bound at the top"
        );
        eprintln!("{name}: width {want_w}, {want_pi} PIs, 16 wide-commit anchors PRESENT.");
    }
}

fn pi_index_of(c: &dregg_circuit::descriptor_ir2::VmConstraint2) -> Option<usize> {
    use dregg_circuit::descriptor_ir2::VmConstraint2;
    use dregg_circuit::lean_descriptor_air::VmConstraint;
    match c {
        VmConstraint2::Base(VmConstraint::PiBinding { pi_index, .. }) => Some(*pi_index),
        _ => None,
    }
}

/// supplyMint (the dedicated sel::MINT mint) PROVES + VERIFIES at the wide geometry (817 / 62 PIs)
/// through the live wide dispatcher — the 8-felt anchors bind.
#[test]
fn wide_supply_mint_proves_and_verifies() {
    let name = "supplyMintVmDescriptor2R24";
    let before_balance: i64 = 100;
    let value: u64 = 30;
    let st = CellState::new(before_balance as u64, 5);
    let effects = vec![Effect::Mint {
        value_lo: dregg_circuit::field::BabyBear::new(value as u32),
        mint_hash: dregg_circuit::field::BabyBear::new(0),
        value_full: value,
    }];

    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 5);
    let after_cell = producer_cell(before_balance + value as i64, 6);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[11u8; 32]];
    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_log);

    let (desc, trace, dpis, map_heaps, _mb) = generate_rotated_effect_vm_descriptor_and_trace_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &empty_caveat_manifest(),
        None,
        None,
        None,
    )
    .expect("wide supply-mint dispatch");
    assert_eq!(desc.name, parse_vm_descriptor2(wide_json(name)).unwrap().name);
    assert_eq!(desc.trace_width, 817, "supplyMint wide width 817");
    assert_eq!(desc.public_input_count, 62, "supplyMint wide 62 PIs");
    assert_eq!(trace[0].len(), 817);
    assert_eq!(dpis.len(), 62);

    let mb = MemBoundaryWitness::default();
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mb, &map_heaps)
        .unwrap_or_else(|e| panic!("supplyMint WIDE proof must prove: {e}"));
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .unwrap_or_else(|e| panic!("supplyMint WIDE proof must verify: {e}"));
    eprintln!("WIDE supplyMint: PROVED + VERIFIED at width 817 (faithful 8-felt commit, 62 PIs).");
}
