//! THE CAP-OPEN AVAILABILITY-WELD LIVE ROUNDTRIP — the GAP #4 wrap class closed on the
//! cap-authorized transfer route (`transferCapOpenEffVmDescriptor2R24` + the TB twin).
//!
//! The Lean half (`Dregg2.Circuit.RotatedKernelRefinementCapOpenAvail`) re-hosts the LIVE cap-open
//! appendix / #225 turn-identity weld on the HARDENED rotated transfer base (`transferV3Avail` —
//! 15-bit borrow-limb decomposition + NO-FINAL-BORROW, availability circuit-forced) and the emit
//! (`EmitRotationV3.lean`) routes both keys to the hardened members at the ember-gated regen. This
//! file proves the producer side is REAL against whatever bytes the registry carries:
//!
//!   * PRE-regen (bare members): the pad derives to `0` and the roundtrip is the byte-identical
//!     live cap-open path — the fleet keeps proving;
//!   * POST-regen (hardened members): the pad derives to 10, the avail generator fills the
//!     availability witness limbs + borrow bits per row and lays the rotated appendix at the
//!     shifted bases, `widen_to_cap_open{,_tb}_avail` lays the cap-membership crown (and the two
//!     turn-identity columns) at the shifted appendix base, and the proof verifies;
//!   * THE AVAILABILITY TOOTH (hardened only): a forged NO-FINAL-BORROW bit on an honest
//!     cap-authorized trace is REFUSED — a cap-AUTHORIZED transfer still cannot over-debit;
//!   * THE AUTHORITY TOOTH (both): the #225 turn-identity anchor still bites — a published src the
//!     trusted turn does not carry is rejected by `verify_vm_descriptor2` alone (the cap-open
//!     authority facet is orthogonal to, and intact under, the availability weld).
//!
//! To exercise the hardened bytes BEFORE the regen installs them, point
//! `DREGG_AVAIL_REGISTRY_TSV` at a freshly-emitted registry TSV (the `scripts/emit-descriptors.sh`
//! stdout shape, `key\tname\tjson`); the default is the COMMITTED registry.

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::CellState;
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::Effect;
use dregg_circuit::effect_vm::trace_rotated::{
    CAP_OPEN_TB_PI_SRC, CAP_OPEN_TB_WIDTH, CAP_OPEN_WIDTH, CapOpenWitness, FACET_MASK_HI,
    ROT_PI_COUNT, RotatedBlockWitness, SIGNATURE_AUTH_TAG, WRITE_MASK_LO,
    anchor_cap_open_turn_pins, avail_pad_for_descriptor_name, cap_open_tb_dpis,
    generate_rotated_effect_vm_trace_avail, transfer_caveat_manifest, widen_to_cap_open_avail,
    widen_to_cap_open_tb_avail,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::HeapLeaf;
use dregg_turn::rotation_witness as rw;

/// The registry member JSON for `key`: the committed `V3_STAGED_REGISTRY_TSV` by default, or the
/// TSV at `DREGG_AVAIL_REGISTRY_TSV` (a freshly-emitted registry, for pre-regen validation of the
/// hardened bytes).
fn registry_json(key: &str) -> String {
    let owned;
    let tsv: &str = match std::env::var("DREGG_AVAIL_REGISTRY_TSV") {
        Ok(p) => {
            owned = std::fs::read_to_string(&p)
                .unwrap_or_else(|e| panic!("DREGG_AVAIL_REGISTRY_TSV {p} unreadable: {e}"));
            &owned
        }
        Err(_) => dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV,
    };
    for line in tsv.lines() {
        let mut parts = line.splitn(3, '\t');
        if parts.next() == Some(key) {
            let _name = parts.next();
            return parts
                .next()
                .expect("registry line has a json column")
                .to_string();
        }
    }
    panic!("{key} not in the registry TSV");
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
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("31 pre-iroot limbs")
}

/// Build the rotated TRANSFER base trace + PIs (a debit transfer, `direction = 1`) at the
/// descriptor-derived avail pad — the live rotated cohort path the transfer cap-open widens.
fn build_transfer_base_avail(avail_pad: usize) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
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

    let produce = |cell: &Cell| {
        rw::produce(
            cell,
            &ledger,
            &nullifier_root,
            &commitments_root,
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        )
    };
    let before_w = produce(&before_cell);
    let after_w = produce(&after_cell);

    let caveat = transfer_caveat_manifest();
    generate_rotated_effect_vm_trace_avail(
        avail_pad,
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("rotated Transfer base trace (avail-aware) must generate")
}

/// The cap-membership witness: a transfer-conferring leaf (`mask_lo == EFFECT_TRANSFER`,
/// `auth_tag == Signature`) whose `target` IS the turn's `src` felt.
const SRC_FELT: u32 = 7_777;

fn cap_open_witness() -> CapOpenWitness {
    let chosen: [BabyBear; 7] = [
        BabyBear::new(0xA11CE),            // slot_hash
        BabyBear::new(SRC_FELT),           // target (== src)
        BabyBear::new(SIGNATURE_AUTH_TAG), // auth_tag (== 1, Signature tier)
        BabyBear::new(WRITE_MASK_LO),      // mask_lo (== EFFECT_TRANSFER = 2)
        BabyBear::new(FACET_MASK_HI),      // mask_hi (== 0)
        BabyBear::new(0x00FF_FFFF),        // expiry
        BabyBear::new(42),                 // breadstuff
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
    CapOpenWitness::build(&[other, chosen], 1).expect("cap-open witness builds")
}

/// THE AVAILABILITY TOOTH: on a hardened (`avail_pad > 0`) member, forging the NO-FINAL-BORROW bit
/// (`BRW1` at `EFFECT_VM_WIDTH + 7` — claiming the debit under-borrowed) must refuse.
fn assert_forged_borrow_refused(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    dpis: &[BabyBear],
) {
    use dregg_circuit::effect_vm::EFFECT_VM_WIDTH;
    let mut forged: Vec<Vec<BabyBear>> = trace.to_vec();
    for row in forged.iter_mut() {
        row[EFFECT_VM_WIDTH + 7] = BabyBear::ONE; // BRW1 := 1 (forged final borrow)
    }
    let map_heaps: Vec<Vec<HeapLeaf>> = vec![];
    let refused = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_vm_descriptor2(
            desc,
            &forged,
            dpis,
            &MemBoundaryWitness::default(),
            &map_heaps,
        )
        .and_then(|p| verify_vm_descriptor2(desc, &p, dpis))
    }));
    assert!(
        match refused {
            Err(_) => true,
            Ok(res) => res.is_err(),
        },
        "{}: a forged final-borrow bit must not prove+verify on the hardened cap-open member",
        desc.name
    );
}

/// The LIVE turn-bound transfer cap-open key roundtrips (bare pre-regen; hardened + availability
/// tooth post-regen / under `DREGG_AVAIL_REGISTRY_TSV`), and the #225 turn-identity anchor keeps
/// biting on the hardened member — authority intact under the availability weld.
#[test]
fn cap_open_tb_member_roundtrips_live() {
    let json = registry_json("transferCapOpenTBVmDescriptor2R24");
    let desc = parse_vm_descriptor2(&json).expect("TB cap-open descriptor parses");
    let pad = avail_pad_for_descriptor_name(&desc.name);
    if desc.name.contains("-v1-avail") {
        assert!(pad > 0, "hardened TB member must derive a nonzero pad");
    }
    assert_eq!(
        desc.trace_width,
        CAP_OPEN_TB_WIDTH + pad,
        "TB width = bare TB width + avail pad"
    );
    assert_eq!(
        desc.public_input_count, 49,
        "TB carries 49 PIs regardless of the pad (columns shift, PI indices never)"
    );

    let trusted_src = BabyBear::new(SRC_FELT);
    let (mut trace, base_pis) = build_transfer_base_avail(pad);
    let w = cap_open_witness();
    widen_to_cap_open_tb_avail(&mut trace, &w, trusted_src, trusted_src, pad).expect("TB widen");
    let honest_pis = cap_open_tb_dpis(&base_pis, trusted_src, trusted_src, trusted_src);
    assert_eq!(honest_pis.len(), 49);

    let map_heaps: Vec<Vec<HeapLeaf>> = vec![];
    let proof = prove_vm_descriptor2(
        &desc,
        &trace,
        &honest_pis,
        &MemBoundaryWitness::default(),
        &map_heaps,
    )
    .expect("honest transfer TB cap-open proves");

    // (A) The verifier anchor — ACCEPT (trusted turn matches the published identity).
    let mut anchored = honest_pis.clone();
    anchor_cap_open_turn_pins(&mut anchored, trusted_src, trusted_src, trusted_src);
    verify_vm_descriptor2(&desc, &proof, &anchored)
        .expect("honest TB cap-open verifies under the trusted-turn anchor");

    // (B) THE AUTHORITY TOOTH — a published src the trusted turn does NOT carry is rejected by the
    // verifier alone (the #225 pin, intact at the avail-shifted geometry).
    {
        let mut forged = honest_pis.clone();
        anchor_cap_open_turn_pins(
            &mut forged,
            BabyBear::new(SRC_FELT + 1),
            trusted_src,
            trusted_src,
        );
        assert_ne!(forged[CAP_OPEN_TB_PI_SRC], honest_pis[CAP_OPEN_TB_PI_SRC]);
        assert!(
            verify_vm_descriptor2(&desc, &proof, &forged).is_err(),
            "a published src the trusted turn does not carry must be rejected"
        );
    }

    // (C) THE AVAILABILITY TOOTH (hardened bytes only).
    if pad > 0 {
        assert_forged_borrow_refused(&desc, &trace, &honest_pis);
        eprintln!(
            "CAP-OPEN TB AVAILABILITY TOOTH GREEN: forged final-borrow REFUSED on {}",
            desc.name
        );
    }
    eprintln!(
        "CAP-OPEN TB ROUNDTRIP GREEN ({}, pad {pad}): honest proves+verifies, forged identity rejected",
        desc.name
    );
}

/// The LIVE (non-TB) transfer cap-open key roundtrips (bare pre-regen; hardened + availability
/// tooth post-regen / under `DREGG_AVAIL_REGISTRY_TSV`).
#[test]
fn cap_open_eff_member_roundtrips_live() {
    let json = registry_json("transferCapOpenEffVmDescriptor2R24");
    let desc = parse_vm_descriptor2(&json).expect("eff cap-open descriptor parses");
    let pad = avail_pad_for_descriptor_name(&desc.name);
    if desc.name.contains("-v1-avail") {
        assert!(pad > 0, "hardened eff member must derive a nonzero pad");
    }
    assert_eq!(
        desc.trace_width,
        CAP_OPEN_WIDTH + pad,
        "eff width = bare cap-open width + avail pad"
    );
    assert_eq!(desc.public_input_count, 46, "eff carries the rotated 46 PIs");

    let (mut trace, base_pis) = build_transfer_base_avail(pad);
    let w = cap_open_witness();
    widen_to_cap_open_avail(&mut trace, &w, pad).expect("cap-open widen");
    // The eff member publishes the plain rotated 46-PI vector (no rc tail, no TB pins).
    let dpis: Vec<BabyBear> = base_pis[..ROT_PI_COUNT].to_vec();

    let map_heaps: Vec<Vec<HeapLeaf>> = vec![];
    let proof = prove_vm_descriptor2(
        &desc,
        &trace,
        &dpis,
        &MemBoundaryWitness::default(),
        &map_heaps,
    )
    .expect("honest transfer eff cap-open proves");
    verify_vm_descriptor2(&desc, &proof, &dpis).expect("honest eff cap-open verifies");

    if pad > 0 {
        assert_forged_borrow_refused(&desc, &trace, &dpis);
        eprintln!(
            "CAP-OPEN EFF AVAILABILITY TOOTH GREEN: forged final-borrow REFUSED on {}",
            desc.name
        );
    }
    eprintln!(
        "CAP-OPEN EFF ROUNDTRIP GREEN ({}, pad {pad}): honest proves+verifies",
        desc.name
    );
}
