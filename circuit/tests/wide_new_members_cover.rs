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
use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::chip_absorb_all_lanes;
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::{
    CAP_OPEN_TB_PI_ACTOR, CAP_OPEN_TB_PI_DST, CAP_OPEN_TB_PI_SRC, CapOpenWitness, FACET_MASK_HI,
    RotatedBlockWitness, SIGNATURE_AUTH_TAG, WRITE_MASK_LO, anchor_cap_open_turn_pins,
    empty_caveat_manifest, generate_rotated_effect_vm_descriptor_and_trace_wide,
    generate_rotated_heap_write_wide, generate_rotated_transfer_cap_open_tb_wide,
    transfer_caveat_manifest,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::HeapLeaf;
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
    // The committed post-v13-regen shapes (the registry drift pins): the TB host grew with the
    // v13 graduated base + membership columns (wide 2824), heapWrite carries the OPTION-I after-spine
    // host (wide 2951), supplyMint rides the transfer-shape host (wide 2493) at the UNWRAPPED 62 PIs
    // (never rc-wrapped, like cap-open). Widths read directly from the committed wide registry rows.
    for (name, want_w, want_pi) in [
        ("transferCapOpenTBVmDescriptor2R24", 2824usize, 65usize),
        ("heapWriteVmDescriptor2R24", 2951, 20),
        ("supplyMintVmDescriptor2R24", 2493, 62),
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
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        &Default::default(),
    );

    let (desc, trace, dpis, map_heaps, _mb) = generate_rotated_effect_vm_descriptor_and_trace_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &empty_caveat_manifest(),
        None,
        None,
        None,
        None,
    )
    .expect("wide supply-mint dispatch");
    assert_eq!(
        desc.name,
        parse_vm_descriptor2(wide_json(name)).unwrap().name
    );
    assert_eq!(
        desc.trace_width, 2493,
        "supplyMint wide width 2493 (committed wide supplyMintVmDescriptor2R24)"
    );
    assert_eq!(
        desc.public_input_count, 62,
        "supplyMint wide 62 PIs (unwrapped — no rc tail)"
    );
    assert_eq!(trace[0].len(), desc.trace_width);
    assert_eq!(dpis.len(), desc.public_input_count);

    let mb = MemBoundaryWitness::default();
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mb, &map_heaps)
        .unwrap_or_else(|e| panic!("supplyMint WIDE proof must prove: {e}"));
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .unwrap_or_else(|e| panic!("supplyMint WIDE proof must verify: {e}"));
    eprintln!("WIDE supplyMint: PROVED + VERIFIED at width 1197 (faithful 8-felt commit, 62 PIs).");
}

/// heapWrite (the Class-A heap-root recompute) PROVES + light-client VERIFIES at the wide geometry
/// (1183 / 20 PIs) through its dedicated per-family wide producer — the genuine sorted-Merkle splice
/// over the FAITHFUL 8-felt heap root forces the AFTER heap-root group and the 8-felt anchors bind.
/// Mirrors `wide_supply_mint_proves_and_verifies`.
#[test]
fn wide_heap_write_proves_and_verifies() {
    let name = "heapWriteVmDescriptor2R24";
    // A benign rotated lead lays the rotated block (heapWrite carries no economic gates); the heap
    // splice rides on top.
    let st = CellState::new(100, 5);
    let value_full: u64 = 30;
    let effects = vec![Effect::Mint {
        value_lo: BabyBear::new(value_full as u32),
        mint_hash: BabyBear::new(0),
        value_full,
    }];
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(100, 5);
    let after_cell = producer_cell(100 + value_full as i64, 6);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[11u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        &Default::default(),
    );

    // The splice's in-row recomputed address `chip-absorb(coll, key)`; seed the BEFORE heap with a leaf
    // there (the `.write` is an UPDATE of a present key).
    let coll = BabyBear::new(42);
    let key = BabyBear::new(7);
    let value = BabyBear::new(123);
    let mut absorb_in = [BabyBear::new(0); 11];
    absorb_in[0] = coll;
    absorb_in[1] = key;
    let addr = chip_absorb_all_lanes(2, &absorb_in)[0];
    let heap = vec![
        HeapLeaf {
            addr,
            value: BabyBear::new(9),
        },
        HeapLeaf {
            addr: BabyBear::new(999_983),
            value: BabyBear::new(1),
        },
    ];

    let (trace, dpis, map_heaps) = generate_rotated_heap_write_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &empty_caveat_manifest(),
        coll,
        key,
        value,
        &heap,
    )
    .expect("wide heap-write generation");

    let desc = parse_vm_descriptor2(wide_json(name)).unwrap();
    assert_eq!(
        desc.trace_width, 2951,
        "heapWrite wide width 2951 (OPTION I after-spine, v13 graduated base — committed wide heapWriteVmDescriptor2R24)"
    );
    assert_eq!(desc.public_input_count, 20, "heapWrite wide 20 PIs");
    assert_eq!(trace[0].len(), desc.trace_width);
    assert_eq!(dpis.len(), desc.public_input_count);

    let mb = MemBoundaryWitness::default();
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mb, &map_heaps)
        .unwrap_or_else(|e| panic!("heapWrite WIDE proof must prove: {e}"));
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .unwrap_or_else(|e| panic!("heapWrite WIDE proof must verify: {e}"));
    eprintln!(
        "WIDE heapWrite: PROVED + VERIFIED at width 1183 (genuine sorted-Merkle splice over the faithful 8-felt heap root + 8-felt commit, 20 PIs)."
    );
}

/// transferCapOpenTB (the #225 turn-identity weld) PROVES + light-client VERIFIES at the wide geometry
/// (1029 / 65 PIs) through its dedicated per-family wide producer: the verifier ANCHORS the three
/// turn-identity PIs (src/actor/dst) to the trusted turn, and the 8-felt anchors bind.
#[test]
fn wide_transfer_cap_open_tb_proves_and_verifies() {
    let name = "transferCapOpenTBVmDescriptor2R24";
    // The honest transfer base (a debit transfer — ticks the nonce, debits the balance).
    let before_balance: i64 = 100_000;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::Transfer {
        amount: 1_000,
        direction: 1,
    }];
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance - 1_000, 1);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32], [4u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_log,
        &Default::default(),
    );

    // The cap-membership witness: a transfer-conferring leaf (two-axis facet × tier) whose `target` IS
    // the turn's `src`. The owner arm publishes `actor == dst == src`.
    let src_felt: u32 = 7_777;
    let chosen: [BabyBear; 7] = [
        BabyBear::new(0xA11CE),
        BabyBear::new(src_felt),
        BabyBear::new(SIGNATURE_AUTH_TAG),
        BabyBear::new(WRITE_MASK_LO),
        BabyBear::new(FACET_MASK_HI),
        BabyBear::new(0x00FF_FFFF),
        BabyBear::new(42),
    ];
    let other: [BabyBear; 7] = [
        BabyBear::new(0xBEEF),
        BabyBear::new(123),
        BabyBear::new(1),
        BabyBear::new(1),
        BabyBear::new(0),
        BabyBear::new(9),
        BabyBear::new(0),
    ];
    let cap_open = CapOpenWitness::build(&[other, chosen], 1).expect("cap-open witness builds");
    let src = BabyBear::new(src_felt);
    let actor = src;
    let dst = src;

    let (trace, dpis) = generate_rotated_transfer_cap_open_tb_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &transfer_caveat_manifest(),
        &cap_open,
        src,
        actor,
        dst,
    )
    .expect("wide cap-open-TB generation");

    let desc = parse_vm_descriptor2(wide_json(name)).unwrap();
    assert_eq!(
        desc.trace_width, 2824,
        "transferCapOpenTB wide width 2824 (committed wide transferCapOpenTBVmDescriptor2R24)"
    );
    assert_eq!(desc.public_input_count, 65, "transferCapOpenTB wide 65 PIs");
    assert_eq!(trace[0].len(), desc.trace_width);
    assert_eq!(dpis.len(), desc.public_input_count);
    // The published turn identity rides the three TB PIs.
    assert_eq!(dpis[CAP_OPEN_TB_PI_SRC], src);
    assert_eq!(dpis[CAP_OPEN_TB_PI_ACTOR], actor);
    assert_eq!(dpis[CAP_OPEN_TB_PI_DST], dst);

    let mb = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<HeapLeaf>> = vec![];
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mb, &map_heaps)
        .unwrap_or_else(|e| panic!("transferCapOpenTB WIDE proof must prove: {e}"));

    // THE LIGHT-CLIENT ANCHOR: recompute the three turn-identity PIs from the TRUSTED turn and verify.
    let mut anchored = dpis.clone();
    anchor_cap_open_turn_pins(&mut anchored, src, actor, dst);
    verify_vm_descriptor2(&desc, &proof, &anchored).unwrap_or_else(|e| {
        panic!("transferCapOpenTB WIDE proof must verify under the trusted-turn anchor: {e}")
    });

    // THE NEGATIVE TOOTH: a forged published src (one the trusted turn does NOT carry) is rejected by
    // the verifier alone — the #225 gate stays load-bearing at the wide geometry.
    let mut forged = dpis.clone();
    anchor_cap_open_turn_pins(&mut forged, BabyBear::new(src_felt + 1), actor, dst);
    assert!(
        verify_vm_descriptor2(&desc, &proof, &forged).is_err(),
        "a published src that does NOT match the trusted turn MUST be rejected at the wide geometry"
    );
    eprintln!(
        "WIDE transferCapOpenTB: PROVED + VERIFIED at width 1029 (turn-identity anchor + faithful 8-felt commit, 65 PIs); forged-src tooth bites."
    );
}
