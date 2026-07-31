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
use dregg_circuit::effect_vm::bare_floor_refuse_weld as refuse;
use dregg_circuit::effect_vm::trace_rotated::{
    CAP_OPEN_TB_PI_COUNT, CAP_OPEN_TB_PI_SRC, CAP_OPEN_TB_WIDTH, CapOpenWitness, FACET_MASK_HI,
    GRAD_ROT_WIDTH, HEAP_WRITE_HOST_WIDTH, RotatedBlockWitness, SIGNATURE_AUTH_TAG,
    TRANSFER_AVAIL_PAD, V1_WIDTH, WIDE_CARRIER_APPENDIX, WRITE_MASK_LO, anchor_cap_open_turn_pins,
    avail_pad_for_descriptor_name, empty_caveat_manifest,
    generate_rotated_effect_vm_descriptor_and_trace_wide, generate_rotated_heap_write_wide,
    generate_rotated_transfer_cap_open_tb_wide, transfer_caveat_manifest,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;

/// The two membership-claim teeth columns the wide dispatcher splices onto a transfer leg's producer
/// row (paired 1:1 with the 2 claim PIs by the teeth-column exclusion).
const MEMBERSHIP_TEETH_COLS: usize = 2;
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

/// Total columns a member's OWN E1 kill-set (the Epoch-1 SECOND flag-day) deletes, summed from the
/// Lean-emitted single source `E1_COMPACT_TABLE` — exactly what `compact_e1_columns` drains.
fn e1_deleted_cols(key: &str) -> usize {
    dregg_circuit::effect_vm::e1_compact_generated::E1_COMPACT_TABLE
        .iter()
        .find(|(k, _)| *k == key)
        .map(|(_, runs)| runs.iter().map(|(a, b)| b - a).sum())
        .unwrap_or_else(|| panic!("{key} not in E1_COMPACT_TABLE"))
}

/// **THE COMMITTED WIDE WIDTH, DERIVED — never a transcribed pre-compaction literal.** A wide
/// member's committed `trace_width` is its pre-wide HOST width PLUS the wide-carrier appendix,
/// MINUS the S2 stratum (Epoch 1: the two rotated 1-felt Merkle–Damgård chain carrier bands and
/// their 840 graduated chip-lane columns) MINUS the member's own E1 kill-set. Both deletions are
/// read from the Lean-emitted tables `compact_s2_columns` / `compact_e1_columns` drain, so the next
/// compaction moves this pin WITH the bytes instead of rotting it into a dead gate. This is the
/// COMPACTED PRODUCER row — a gentian refuse-welded member carries a further prover-filled aux
/// block on top (see the two call sites that add it).
fn wide_width(key: &str, host: usize) -> usize {
    host + WIDE_CARRIER_APPENDIX
        - dregg_circuit::effect_vm::s2_compact_generated::S2_DELETED_COLS
        - e1_deleted_cols(key)
}

/// **THE BAND SELF-CHECK — count is not enough.** A member's S2 kill-set is not a column COUNT, it
/// is three named bands measured from that member's OWN block base `bb`; an availability-hardened
/// member is shifted by its weld pad, so the base cohort's bands and the avail cohort's bands are
/// DIFFERENT columns at the SAME count. Compacting the right number of columns from the wrong bands
/// leaves the honest proof UNSAT, so a table regen that moves a member's base must fail HERE — at
/// the assert that names it — rather than passing a width check while proving nothing.
fn assert_s2_bands_are_this_members_own(key: &str, desc_name: &str) {
    let bb = dregg_circuit::effect_vm::s2_compact_generated::S2_COMPACT_TABLE
        .iter()
        .find(|(k, _, _)| *k == key)
        .map(|(_, bb, _)| *bb)
        .unwrap_or_else(|| panic!("{key} not in S2_COMPACT_TABLE"));
    assert_eq!(
        bb,
        V1_WIDTH + avail_pad_for_descriptor_name(desc_name),
        "{key}: the S2 bands MUST be measured from this member's own availability-shifted block \
         base (V1_WIDTH + its avail pad) — compacting the avail-shifted bands off the base-cohort \
         row is the same column COUNT at the WRONG columns, which leaves the honest proof UNSAT"
    );
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
    // The committed post-v2-carrier-rotation shapes (the registry drift pins), each DERIVED from
    // its own pre-wide HOST width through `wide_width` rather than transcribed — the TB host is the
    // turn-bound cap-open width on the AVAIL-hardened transfer face, heapWrite carries the OPTION-I
    // after-spine host, and supplyMint rides the BARE graduated rotated host at the UNWRAPPED 62 PIs
    // (never rc-wrapped, like cap-open).
    for (name, host, want_pi) in [
        // The TB member's wide PI count is DERIVED, not transcribed: `CAP_OPEN_TB_PI_COUNT` (47 =
        // the rotated 46 + the ONE turn-identity `src` slot) + the 16 wide-commit anchors = 63.
        // It was 65 until 2026-07-31, when `CapOpenTurnPins` deleted the `actor`/`dst` pins and
        // their two PI slots — they named columns no other constraint read.
        (
            "transferCapOpenTBVmDescriptor2R24",
            CAP_OPEN_TB_WIDTH + TRANSFER_AVAIL_PAD,
            CAP_OPEN_TB_PI_COUNT + 16,
        ),
        ("heapWriteVmDescriptor2R24", HEAP_WRITE_HOST_WIDTH, 20),
        ("supplyMintVmDescriptor2R24", GRAD_ROT_WIDTH, 62),
    ] {
        let d = parse_vm_descriptor2(wide_json(name)).unwrap();
        let want_w = wide_width(name, host);
        assert_eq!(d.trace_width, want_w, "{name} wide width");
        // The width alone is a COUNT; pin the BANDS the count came from too.
        assert_s2_bands_are_this_members_own(name, &d.name);
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
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[11u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
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
        desc.trace_width,
        wide_width(name, GRAD_ROT_WIDTH),
        "supplyMint wide width = the BARE graduated rotated host + the wide-carrier appendix, \
         MINUS the S2 stratum and this member's own E1 kill-set (committed wide \
         supplyMintVmDescriptor2R24)"
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
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[11u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
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
        HeapLeaf::entry(addr, BabyBear::new(9)),
        HeapLeaf::entry(BabyBear::new(999_983), BabyBear::new(1)),
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
        desc.trace_width,
        wide_width(name, HEAP_WRITE_HOST_WIDTH),
        "heapWrite wide width = the OPTION-I after-spine host + the wide-carrier appendix, MINUS \
         the S2 stratum and this member's own E1 kill-set (committed wide \
         heapWriteVmDescriptor2R24)"
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

/// transferCapOpenTB (the #225 turn-identity weld) PROVES + light-client VERIFIES at the wide
/// geometry through its dedicated per-family wide producer: the verifier ANCHORS the ONE
/// turn-identity PI (`src`) to the trusted turn, and the 8-felt anchors bind. The weld adds no
/// column, so the wide host is the plain cap-open host on the avail-hardened face.
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
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32], [4u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );

    // The cap-membership witness: a transfer-conferring leaf (two-axis facet × tier) whose `target` IS
    // the turn's `src` — the column `targetBindGate` roots, and the only one the TB weld publishes.
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

    let (trace, dpis) = generate_rotated_transfer_cap_open_tb_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &transfer_caveat_manifest(),
        &cap_open,
        src,
    )
    .expect("wide cap-open-TB generation");

    let desc = parse_vm_descriptor2(wide_json(name)).unwrap();
    assert_eq!(
        desc.trace_width,
        wide_width(name, CAP_OPEN_TB_WIDTH + TRANSFER_AVAIL_PAD),
        "transferCapOpenTB wide width = the turn-bound cap-open host on the AVAIL-hardened transfer \
         face + the wide-carrier appendix, MINUS the S2 stratum and this member's own E1 kill-set \
         (committed wide transferCapOpenTBVmDescriptor2R24)"
    );
    assert_eq!(
        desc.public_input_count,
        CAP_OPEN_TB_PI_COUNT + 16,
        "transferCapOpenTB wide PIs = the TB member's {CAP_OPEN_TB_PI_COUNT} (46 rotated + the one \
         turn-identity `src`) + the 16 wide-commit anchors"
    );
    // PRODUCER ≡ DESCRIPTOR. A shortfall of exactly TRANSFER_AVAIL_PAD means the producer laid the
    // BARE transfer face and appended its wide carriers at `CAP_OPEN_TB_WIDTH`, while the COMMITTED
    // member is the AVAIL-hardened one (`…-transfer-v1-avail-…`) whose host is `CAP_OPEN_TB_WIDTH +
    // TRANSFER_AVAIL_PAD` and whose S2 block base is correspondingly shifted (`bb = 198`, not 188).
    // That is the avail-shift trap on the DEPLOYED producer, not a test pin: the same column COUNT
    // compacted from the WRONG bands.
    assert_eq!(
        trace[0].len(),
        desc.trace_width,
        "the cap-open-TB producer's compacted row must equal the committed member's width \
         (a shortfall of exactly TRANSFER_AVAIL_PAD = {TRANSFER_AVAIL_PAD} means the producer laid \
         the BARE transfer face for an AVAIL-hardened committed member)"
    );
    assert_eq!(dpis.len(), desc.public_input_count);
    // The published turn identity is `src`, and it is the ONE slot the TB weld adds.
    assert_eq!(dpis[CAP_OPEN_TB_PI_SRC], src);

    let mb = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<HeapLeaf>> = vec![];
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mb, &map_heaps)
        .unwrap_or_else(|e| panic!("transferCapOpenTB WIDE proof must prove: {e}"));

    // THE LIGHT-CLIENT ANCHOR: recompute the turn-identity PI from the TRUSTED turn and verify.
    let mut anchored = dpis.clone();
    anchor_cap_open_turn_pins(&mut anchored, src);
    verify_vm_descriptor2(&desc, &proof, &anchored).unwrap_or_else(|e| {
        panic!("transferCapOpenTB WIDE proof must verify under the trusted-turn anchor: {e}")
    });

    // THE NEGATIVE TOOTH: a forged published src (one the trusted turn does NOT carry) is rejected by
    // the verifier alone — the #225 gate stays load-bearing at the wide geometry.
    let mut forged = dpis.clone();
    anchor_cap_open_turn_pins(&mut forged, BabyBear::new(src_felt + 1));
    assert!(
        verify_vm_descriptor2(&desc, &proof, &forged).is_err(),
        "a published src that does NOT match the trusted turn MUST be rejected at the wide geometry"
    );
    eprintln!(
        "WIDE transferCapOpenTB: PROVED + VERIFIED (turn-identity anchor + faithful 8-felt commit, \
         {} PIs); forged-src tooth bites.",
        desc.public_input_count
    );
}

/// **THE GENTIAN REFUSE-WELD MINT TOOTH.** The fold participant leg mints a plain `Transfer`
/// through the FULL wide dispatcher onto the deployed availability-hardened, refuse-welded
/// `transferVmDescriptor2R24` (`…-v3-staged-gentian-deployed-bare-refuse`, trace_width 2664,
/// public_input_count 68 — the `pi_tail == 2` membership-teeth arm). The dispatcher's teeth-column
/// exclusion subtracts the WELD FOOTPRINT (`REFUSE_WELD_WIDEN = 45`) from the teeth-column tail
/// before the 1:1 exposure pairing; with the stale `3·REFUSE_STRIDE = 48` the tail (47 = 45 refuse +
/// 2 membership teeth) underflowed and the mint REFUSED — blocking every wide/fold proof regen. This
/// pins the mint SUCCEEDING with the correct geometry: `raw_col_tail 47 − 45 = 2 = pi_tail`.
#[test]
fn wide_transfer_membership_leg_mints_through_refuse_weld() {
    let before_balance: i64 = 100_000;
    let amount: u64 = 50;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance - amount as i64, 1);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
    let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
    let receipt_log: Vec<[u8; 32]> = vec![[5u8; 32], [6u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &nullifier_root,
        &commitments_root,
        &dregg_turn::rotation_witness::empty_revoked_root_8(),
        &receipt_log,
        &Default::default(),
    );

    // The producer-honest membership-teeth pair (any felts — the geometry check that was refusing is
    // independent of the teeth VALUES; it pairs the 2 teeth columns 1:1 with the 2 claim PIs).
    let membership_teeth = (BabyBear::new(0xA11CE), BabyBear::new(0xF00D));

    // THE FULL WIDE DISPATCH — the exact call `mint_rotated_participant_leg` makes for a transfer.
    let (desc, trace, dpis, _map_heaps, _mb) = generate_rotated_effect_vm_descriptor_and_trace_wide(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &transfer_caveat_manifest(),
        None,
        None,
        None,
        Some(membership_teeth),
    )
    .expect(
        "the refuse-welded wide transfer leg MUST mint (no refuse) — the teeth-column exclusion \
         subtracts the 45-column weld footprint, not 48, so raw_col_tail 47 − 45 = 2 = pi_tail",
    );

    assert!(
        desc.name.contains("-gentian-deployed-bare-refuse"),
        "the wide transfer dispatch resolves the deployed refuse-welded member ({})",
        desc.name
    );
    assert_eq!(
        desc.trace_width,
        wide_width(
            "transferVmDescriptor2R24",
            GRAD_ROT_WIDTH + TRANSFER_AVAIL_PAD
        ) + MEMBERSHIP_TEETH_COLS
            + refuse::REFUSE_WELD_WIDEN,
        "deployed avail-hardened refuse-welded transfer wide width = the COMPACTED PRODUCER row \
         (avail host + carriers − S2 − its own E1) + the 2 spliced membership teeth + the \
         refuse-weld footprint. This member's refuse block sits at the very TOP of the trace, so \
         its widen is REFUSE_WELD_WIDEN (the block span with the last stride-tail unallocated) — \
         NOT the full per-tag stride the teeth-less members carry"
    );
    // The geometry-CLASS self-check: assert the committed member really is the top-of-trace shape
    // whose widen the width above assumed, recovered from its OWN committed floor-refuse gates. A
    // regen that gives this member the dead stride-tail fails here instead of silently shifting the
    // refuse block under a width pin that still adds up.
    assert_eq!(
        refuse::refuse_weld_widen(&desc),
        refuse::REFUSE_WELD_WIDEN,
        "the avail-hardened transfer's refuse block rides at the TOP of the trace (no dead \
         stride-tail above it)"
    );
    assert_eq!(
        desc.public_input_count, 68,
        "66 producer PIs + 2 spliced membership claim PIs"
    );
    assert_eq!(
        dpis.len(),
        desc.public_input_count,
        "PIs mint to the descriptor count"
    );
    // The RETURNED trace row already carries the 2 spliced membership teeth (the dispatcher's
    // transfer arm pushed them onto every row); the ONLY columns still past it are the 45
    // refuse-weld aux cols that `fill_refuse_aux` populates at prove time. So `trace_width −
    // returned_row = 45`. The dispatcher's INTERNAL `raw_col_tail` (teeth NOT yet in the producer
    // row) is `45 + 2 = 47`, and the fixed exclusion computes `col_tail = 47 − REFUSE_WELD_WIDEN
    // (45) = 2 = pi_tail`. With the stale 48 this underflowed (47 < 48) and the mint refused.
    let post_teeth_tail = desc.trace_width - trace[0].len();
    assert_eq!(
        post_teeth_tail,
        refuse::REFUSE_WELD_WIDEN,
        "past the teeth-carrying producer row sit exactly the refuse-weld aux columns"
    );
    // pre-teeth raw_col_tail the exclusion sees
    let internal_raw_col_tail = post_teeth_tail + MEMBERSHIP_TEETH_COLS;
    assert_eq!(
        internal_raw_col_tail - refuse::REFUSE_WELD_WIDEN,
        MEMBERSHIP_TEETH_COLS,
        "the exclusion pairs the 2 teeth 1:1 with the 2 claim PIs (col_tail == pi_tail)"
    );
    // The 2 spliced teeth carry the honest pair (the exclusion's 1:1 pairing held).
    assert!(
        dpis.contains(&membership_teeth.0) && dpis.contains(&membership_teeth.1),
        "the membership teeth pair was spliced into the claim PIs"
    );
}

/// **THE FRESH-FOLD LEAF, BOTH POST-GAP-1-6 TURN BODIES.** The VK-epoch producer reconciliation:
/// a fresh full-turn leaf MINTS + PROVES + light-client VERIFIES through the FULL wide dispatcher
/// (the node's `prove_pool` route via `mint_rotated_participant_leg`) for BOTH representative bodies
/// on the regenerated deployed descriptors —
///   * **IncrementNonce** (`incrementNonceVmDescriptor2R24`, wide 2655 / 66 PIs, `pi_tail == 0`): the
///     teeth-less member whose refuse-weld widen is 48 (a 3-column dead stride-tail rides above the
///     decode block). The stale fixed exclusion (45) left `col_tail = 3 ≠ 0 = pi_tail` → "tail
///     mismatch"; the per-member `refuse_weld_widen` (= `trace_width − aux_base` = 48) restores
///     `col_tail = 0 = pi_tail` so the leg dispatches, then proves.
///   * **Transfer** (avail-hardened `transferVmDescriptor2R24`, wide 2664 / 68 PIs): the member whose
///     AAFI/avail epoch left the 15-bit borrow-limb range table (wire id 84 = `rangeTidW 15`)
///     un-declared in `tables`; the IR-v2 realizer now decodes its width from the committed tid and
///     realizes the byte-limb range relation, so the full prove no longer fails "custom table id 84
///     has no realized relation".
/// Together this is the whole make-it-real leaf: a fresh leaf proof exists for a teeth-less body AND
/// the avail transfer body on the post-flip descriptors.
#[test]
fn fresh_fold_leaf_mints_and_proves_both_bodies() {
    // --- Body 1: IncrementNonce (teeth-less, widen 48). ---
    {
        let st = CellState::new(100_000, 0);
        let effects = vec![Effect::IncrementNonce];
        let before_cell = producer_cell(100_000, 0);
        let after_cell = producer_cell(100_000, 1);
        let mut ledger = Ledger::new();
        ledger.insert_cell(after_cell.clone()).unwrap();
        let nr = dregg_circuit::heap_root::empty_heap_root_8();
        let cr = dregg_circuit::heap_root::empty_heap_root_8();
        let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];
        let before_w = rw::produce(
            &before_cell,
            &ledger,
            &nr,
            &cr,
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );
        let after_w = rw::produce(
            &after_cell,
            &ledger,
            &nr,
            &cr,
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );
        let (desc, trace, dpis, map_heaps, mb) =
            generate_rotated_effect_vm_descriptor_and_trace_wide(
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
            .expect(
                "IncrementNonce fresh leaf MUST dispatch (the per-member refuse widen 48 pairs \
                 raw_col_tail 48 − 48 = 0 = pi_tail; the stale fixed 45 gave 3 ≠ 0)",
            );
        assert!(desc.name.contains("incrementNonce"));
        assert_eq!(
            desc.trace_width,
            wide_width("incrementNonceVmDescriptor2R24", GRAD_ROT_WIDTH)
                + refuse::CAPACITY_TAGS.len() * refuse::REFUSE_STRIDE,
            "wide incrementNonce width = the COMPACTED PRODUCER row (bare graduated host + \
             carriers − S2 − its own E1) + the FULL per-tag refuse stride block. This teeth-less \
             member carries a 3-column dead stride-tail ABOVE the decode block, so its widen is the \
             whole CAPACITY_TAGS·REFUSE_STRIDE — not the top-of-trace REFUSE_WELD_WIDEN the \
             avail-hardened transfer/burn members get"
        );
        // The geometry-CLASS self-check, recovered from the member's OWN committed floor-refuse
        // gates: this is the dead-stride-tail shape, and the width above depends on that choice.
        assert_eq!(
            refuse::refuse_weld_widen(&desc),
            refuse::CAPACITY_TAGS.len() * refuse::REFUSE_STRIDE,
            "the teeth-less incrementNonce carries the dead stride-tail above its refuse block"
        );
        assert_eq!(desc.public_input_count, 66);
        assert_eq!(dpis.len(), desc.public_input_count);
        let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mb, &map_heaps)
            .unwrap_or_else(|e| panic!("IncrementNonce fresh leaf must PROVE: {e}"));
        verify_vm_descriptor2(&desc, &proof, &dpis)
            .unwrap_or_else(|e| panic!("IncrementNonce fresh leaf must VERIFY: {e}"));
        eprintln!("FRESH LEAF IncrementNonce: dispatch (widen 48) + PROVE + VERIFY.");
    }

    // --- Body 2: Transfer (avail-hardened, realizes custom range table 84). ---
    {
        let before_balance: i64 = 100_000;
        let amount: u64 = 50;
        let st = CellState::new(before_balance as u64, 0);
        let effects = vec![Effect::Transfer {
            amount,
            direction: 1,
        }];
        let before_cell = producer_cell(before_balance, 0);
        let after_cell = producer_cell(before_balance - amount as i64, 1);
        let mut ledger = Ledger::new();
        ledger.insert_cell(after_cell.clone()).unwrap();
        let nr = dregg_circuit::heap_root::empty_heap_root_8();
        let cr = dregg_circuit::heap_root::empty_heap_root_8();
        let receipt_log: Vec<[u8; 32]> = vec![[5u8; 32], [6u8; 32]];
        let before_w = rw::produce(
            &before_cell,
            &ledger,
            &nr,
            &cr,
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );
        let after_w = rw::produce(
            &after_cell,
            &ledger,
            &nr,
            &cr,
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        );
        let membership_teeth = (BabyBear::new(0xA11CE), BabyBear::new(0xF00D));
        let (desc, trace, dpis, map_heaps, mb) =
            generate_rotated_effect_vm_descriptor_and_trace_wide(
                &st,
                &effects,
                &bridge(&before_w),
                &bridge(&after_w),
                &transfer_caveat_manifest(),
                None,
                None,
                None,
                Some(membership_teeth),
            )
            .expect("Transfer avail fresh leaf MUST dispatch (widen 45 + 2 teeth)");
        assert!(desc.name.contains("transfer-v1-avail"));
        assert_eq!(
            desc.trace_width,
            wide_width(
                "transferVmDescriptor2R24",
                GRAD_ROT_WIDTH + TRANSFER_AVAIL_PAD
            ) + MEMBERSHIP_TEETH_COLS
                + refuse::REFUSE_WELD_WIDEN,
            "wide avail transfer width = the COMPACTED PRODUCER row + the 2 spliced membership \
             teeth + the top-of-trace refuse-weld footprint"
        );
        assert_eq!(
            refuse::refuse_weld_widen(&desc),
            refuse::REFUSE_WELD_WIDEN,
            "the avail-hardened transfer's refuse block rides at the TOP of the trace"
        );
        assert_eq!(desc.public_input_count, 68);
        assert_eq!(dpis.len(), desc.public_input_count);
        let proof =
            prove_vm_descriptor2(&desc, &trace, &dpis, &mb, &map_heaps).unwrap_or_else(|e| {
                panic!("Transfer avail fresh leaf must PROVE (custom range table 84 realized): {e}")
            });
        verify_vm_descriptor2(&desc, &proof, &dpis)
            .unwrap_or_else(|e| panic!("Transfer avail fresh leaf must VERIFY: {e}"));
        eprintln!(
            "FRESH LEAF Transfer(avail): dispatch + PROVE + VERIFY (table 84 = 15-bit range)."
        );
    }
}

/// **THE GEOMETRY VERSION BOUNDARY, POSITIVE ARM** — every committed wide member (the bare
/// wide registry AND the welded registry) rides the LIVE v2 wide-carrier geometry: the
/// structural detector measures its BEFORE→AFTER commit-carrier block span as 480 (60
/// carriers) and admits it at `WIDE_CARRIER_GEOMETRY_VERSION`.
#[test]
fn wide_registries_are_geometry_version_v2() {
    use dregg_circuit::effect_vm_descriptors::{
        WIDE_CARRIER_GEOMETRY_VERSION, WIDE_UMEM_WELD_REGISTRY_TSV, wide_carrier_geometry_version,
    };
    for (tsv, which) in [
        (WIDE_REGISTRY_STAGED_TSV, "bare wide"),
        (WIDE_UMEM_WELD_REGISTRY_TSV, "wide+umem welded"),
    ] {
        for line in tsv.lines().filter(|l| !l.is_empty()) {
            let mut it = line.splitn(3, '\t');
            let key = it.next().expect("key");
            let _name = it.next();
            let json = it.next().expect("json");
            let d = parse_vm_descriptor2(json).unwrap_or_else(|e| panic!("{key} parses: {e}"));
            assert_eq!(
                wide_carrier_geometry_version(&d),
                Ok(WIDE_CARRIER_GEOMETRY_VERSION),
                "{which} member {key} must ride the live v2 wide-carrier geometry"
            );
        }
    }
}

/// **THE GEOMETRY VERSION BOUNDARY, NEGATIVE ARM (the flag-day rejection tooth)** — an
/// artifact shaped like the RETIRED v1 registry/VK (57 carriers → 456-column block span →
/// 912-column appendix, commit carrier 56) is refused with the TYPED
/// `WideGeometryVersionError::RetiredV1`, and a nonsense span fails closed as
/// `UnknownGeometry` — never silently accepted, never silently widened.
#[test]
fn retired_v1_wide_geometry_is_version_refused() {
    use dregg_circuit::descriptor_ir2::{EffectVmDescriptor2, VmConstraint2};
    use dregg_circuit::effect_vm_descriptors::{
        WIDE_CARRIER_BLOCK_SPAN_RETIRED_V1, WideGeometryVersionError,
        require_wide_carrier_geometry_v2, wide_carrier_geometry_version,
    };
    use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};

    // Synthesize the v1 anchor-pin shape: host 1581 (the v13 rotated cohort), appendix 912,
    // BEFORE commit carrier at host + 8·56, AFTER at host + 456 + 8·56 (= width − 8).
    let v1_host = 1581usize;
    let v1_width = v1_host + 912;
    let pi = 62usize; // 46-PI host + 16 wide anchors
    let mk_pin = |row: VmRow, col: usize, pi_index: usize| {
        VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index })
    };
    let mut constraints = Vec::new();
    for j in 0..8usize {
        constraints.push(mk_pin(VmRow::First, v1_host + 8 * 56 + j, pi - 16 + j));
        constraints.push(mk_pin(VmRow::Last, v1_host + 456 + 8 * 56 + j, pi - 8 + j));
    }
    let legacy = EffectVmDescriptor2 {
        name: "transferVmDescriptor2R24Wide-legacy-v1".to_string(),
        trace_width: v1_width,
        public_input_count: pi,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    };
    assert_eq!(
        wide_carrier_geometry_version(&legacy),
        Err(WideGeometryVersionError::RetiredV1 {
            name: "transferVmDescriptor2R24Wide-legacy-v1".to_string(),
            block_span: WIDE_CARRIER_BLOCK_SPAN_RETIRED_V1,
        }),
        "the retired 57/56/912 shape gets the TYPED version refusal"
    );
    assert!(require_wide_carrier_geometry_v2(&legacy).is_err());

    // A nonsense block span (neither v2's 480 nor v1's 456) fails closed as UnknownGeometry.
    let mut weird = legacy.clone();
    weird.name = "weird-span".to_string();
    weird.constraints = (0..8usize)
        .flat_map(|j| {
            [
                mk_pin(VmRow::First, 100 + j, pi - 16 + j),
                mk_pin(VmRow::Last, 100 + 123 + j, pi - 8 + j),
            ]
        })
        .collect();
    assert_eq!(
        wide_carrier_geometry_version(&weird),
        Err(WideGeometryVersionError::UnknownGeometry {
            name: "weird-span".to_string(),
            block_span: 123,
        })
    );

    // Missing anchors fail closed too (a narrow artifact presented as wide).
    let mut anchorless = legacy.clone();
    anchorless.name = "anchorless".to_string();
    anchorless.constraints.clear();
    assert_eq!(
        wide_carrier_geometry_version(&anchorless),
        Err(WideGeometryVersionError::MissingAnchors {
            name: "anchorless".to_string(),
        })
    );
}
