//! THE AVAILABILITY-WELD LIVE ROUNDTRIP — the GAP #4 flip's producer↔descriptor agreement.
//!
//! The transfer/burn cohort members (`transferVmDescriptor2R24` / `burnVmDescriptor2R24`) route
//! to the HARDENED `…-v1-avail` descriptors at the ember-gated regen. This file proves the
//! producer side is REAL against whatever bytes the registry carries:
//!
//!   * PRE-regen (bare members): the pad derives to `0` and the roundtrip is the byte-identical
//!     live path — the fleet keeps proving;
//!   * POST-regen (hardened members): the pad derives to 10/8, the generator fills the
//!     availability witness limbs + borrow bits per row and lays the appendix at the shifted
//!     bases, the IR-2 assembly realizes the 15-bit range teeth, and the proof verifies;
//!   * THE TOOTH (hardened only): a forged NO-FINAL-BORROW bit on an honest trace is REFUSED.
//!
//! To exercise the hardened bytes BEFORE the regen installs them, point
//! `DREGG_AVAIL_REGISTRY_TSV` at a freshly-emitted registry TSV (the `scripts/emit-descriptors.sh`
//! stdout shape, `key\tname\tjson`); the default is the COMMITTED registry.

use dregg_circuit::CellState;
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::Effect;
use dregg_circuit::effect_vm::trace_rotated::{
    RotatedBlockWitness, avail_pad_for_descriptor_name, empty_caveat_manifest,
    generate_rotated_effect_vm_trace_avail, transfer_caveat_manifest,
};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_turn::rotation_witness as rw;

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};

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
        Err(_) => V3_STAGED_REGISTRY_TSV,
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

/// Build one honest rotated turn for `effects` over a 100_000-balance cell whose post balance is
/// `after_balance`, shaped for the descriptor whose name is `desc_name` (the avail pad derives
/// from it — the descriptor-driven producer contract).
fn honest_turn(
    desc_name: &str,
    effects: &[Effect],
    after_balance: i64,
    caveat: &dregg_circuit::effect_vm::trace_rotated::RotatedCaveatManifest,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let before_balance: i64 = 100_000;
    let st = CellState::new(before_balance as u64, 0);
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(after_balance, 0);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let produce = |cell: &Cell| {
        rw::produce(
            cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        )
    };
    let before_w = produce(&before_cell);
    let after_w = produce(&after_cell);
    let bridge = |w: &rw::RotationWitness| {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("pre-iroot limbs")
    };
    generate_rotated_effect_vm_trace_avail(
        avail_pad_for_descriptor_name(desc_name),
        &st,
        effects,
        &bridge(&before_w),
        &bridge(&after_w),
        caveat,
    )
    .expect("live rotated generator (avail-aware)")
}

fn roundtrip(key: &str, effects: &[Effect], after_balance: i64, transfer_shape: bool) {
    let json = registry_json(key);
    let desc = parse_vm_descriptor2(&json).unwrap_or_else(|e| panic!("{key} parses: {e}"));
    let pad = avail_pad_for_descriptor_name(&desc.name);
    if desc.name.contains("-v1-avail") {
        assert!(
            pad > 0,
            "{key}: a hardened member must derive a nonzero avail pad from its name"
        );
    }
    let caveat = if transfer_shape {
        transfer_caveat_manifest()
    } else {
        empty_caveat_manifest()
    };
    let (trace, dpis) = honest_turn(&desc.name, effects, after_balance, &caveat);
    assert_eq!(dpis.len(), desc.public_input_count, "{key}: PI shape");
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &MemBoundaryWitness::default(), &[])
        .unwrap_or_else(|e| panic!("{key}: honest turn must prove against the live member: {e}"));
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .unwrap_or_else(|e| panic!("{key}: honest proof verifies: {e}"));

    // THE TOOTH (bites only on the hardened member): forge the NO-FINAL-BORROW bit — claim the
    // debit under-borrowed. On the hardened member column `V1_WIDTH + 7` is the final borrow bit
    // `BRW1` and the (dir-gated / ungated) no-final-borrow gate demands 0; flipping it to 1 must
    // refuse. (On a bare member the column is part of the rotated appendix — skip.)
    if pad > 0 {
        use dregg_circuit::effect_vm::EFFECT_VM_WIDTH;
        let mut forged = trace.clone();
        for row in forged.iter_mut() {
            row[EFFECT_VM_WIDTH + 7] = BabyBear::ONE; // BRW1 := 1 (forged final borrow)
        }
        let refused = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_vm_descriptor2(&desc, &forged, &dpis, &MemBoundaryWitness::default(), &[])
                .and_then(|p| verify_vm_descriptor2(&desc, &p, &dpis))
        }));
        assert!(
            match refused {
                Err(_) => true,
                Ok(res) => res.is_err(),
            },
            "{key}: a forged final-borrow bit must not prove+verify on the hardened member"
        );
    }
}

/// The live transfer member roundtrips (bare pre-regen; hardened + 15-bit teeth post-regen).
#[test]
fn transfer_member_roundtrips_live() {
    roundtrip(
        "transferVmDescriptor2R24",
        &[Effect::Transfer {
            amount: 50,
            direction: 1,
        }],
        100_000 - 50,
        true,
    );
}

/// The live burn member roundtrips (bare pre-regen; hardened + 15-bit teeth post-regen).
#[test]
fn burn_member_roundtrips_live() {
    roundtrip(
        "burnVmDescriptor2R24",
        &[Effect::Burn {
            target_hash: BabyBear::new(1234),
            amount_lo: BabyBear::new(50),
            amount_full: 50,
        }],
        100_000 - 50,
        false,
    );
}

/// The live FEE'D transfer member roundtrips (bare pre-regen at pad 0, byte-identical to the
/// deployed fee path; hardened §11.8 fee-availability member + 15-bit MID/fee teeth post-regen).
/// THE FEE TOOTH (hardened only): a forged final FEE-BORROW bit — claiming the fee subtraction
/// under-borrowed, the fee-leg wrap-forgery's witness shape — is REFUSED.
#[test]
fn transfer_fee_member_roundtrips_live() {
    use dregg_circuit::effect_vm::trace_rotated::generate_rotated_effect_vm_trace_with_fee_avail;

    let key = "transferFeeVmDescriptor2R24";
    let json = registry_json(key);
    let desc = parse_vm_descriptor2(&json).unwrap_or_else(|e| panic!("{key} parses: {e}"));
    let pad = avail_pad_for_descriptor_name(&desc.name);
    if desc.name.contains("-v1-fee-avail") {
        assert_eq!(
            pad,
            dregg_circuit::effect_vm::trace_rotated::TRANSFER_FEE_AVAIL_PAD,
            "{key}: the hardened fee member derives the 16-col fee pad from its name"
        );
    }

    let before_balance: i64 = 100_000;
    let amount: u64 = 50;
    let fee: u64 = 7;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    // The producer's after-cell debits BOTH the transfer AND the fee (the proven post-fee state).
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance - amount as i64 - fee as i64, 0);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let produce = |cell: &Cell| {
        rw::produce(
            cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        )
    };
    let before_w = produce(&before_cell);
    let after_w = produce(&after_cell);
    let bridge = |w: &rw::RotationWitness| {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("pre-iroot limbs")
    };
    let caveat = transfer_caveat_manifest();
    let (trace, dpis) = generate_rotated_effect_vm_trace_with_fee_avail(
        pad,
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
        fee,
    )
    .expect("live fee'd rotated generator (avail-aware)");
    assert_eq!(dpis.len(), desc.public_input_count, "{key}: PI shape");
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &MemBoundaryWitness::default(), &[])
        .unwrap_or_else(|e| {
            panic!("{key}: honest fee'd turn must prove against the live member: {e}")
        });
    verify_vm_descriptor2(&desc, &proof, &dpis)
        .unwrap_or_else(|e| panic!("{key}: honest fee'd proof verifies: {e}"));

    // THE FEE TOOTH (bites only on the hardened member): forge the final FEE-borrow bit `FB1`
    // (col `V1_WIDTH + 15`) — claim `fee > mid`, the fee-leg wrap forgery's witness shape. The
    // UNGATED no-final-fee-borrow gate demands 0; flipping it to 1 must refuse.
    if pad > 0 {
        use dregg_circuit::effect_vm::EFFECT_VM_WIDTH;
        let mut forged = trace.clone();
        for row in forged.iter_mut() {
            row[EFFECT_VM_WIDTH + 15] = BabyBear::ONE; // FB1 := 1 (forged final fee borrow)
        }
        let refused = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_vm_descriptor2(&desc, &forged, &dpis, &MemBoundaryWitness::default(), &[])
                .and_then(|p| verify_vm_descriptor2(&desc, &p, &dpis))
        }));
        assert!(
            match refused {
                Err(_) => true,
                Ok(res) => res.is_err(),
            },
            "{key}: a forged final fee-borrow bit must not prove+verify on the hardened member"
        );
    }
}
