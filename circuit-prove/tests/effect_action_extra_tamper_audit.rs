//! ADVERSARIAL AUDIT (additive): one more isolating tamper the primary gate did not write.
//!
//! The primary gate (`effect_action_emit_gate.rs`) exercises the pi_binding, the limb-0 chain gate,
//! the forged borrow, the underflow, the `was_burn` limb-0 disclosure pin, and the continuity
//! window_gate. It leaves the was_burn limb-1 pin (`wb_1 == 0`, burn gate idx 59) UN-isolated. This
//! test bites exactly that tooth: a `was_burn_flag` of `65537` — limb 0 is still 1 (so the limb-0
//! pin is satisfied) and limb 1 is 1 (so the ONLY violated relation is the limb-1 pin) — with trace
//! AND PI moved together so every `pi_binding` still holds. Then it drops constraint idx 59 and
//! shows the SAME tamper flips REJECT -> ACCEPT.
//!
//! ⚑ Column/gate geometry moved on 2026-08-06 (`AMOUNT_LIMBS` 2 -> 4, 16-bit limbs): width 27,
//! pi 24, gates at 51..62. The 32-bit split it replaced could not be parsed by
//! `parse_vm_descriptor2` at all — its borrow coefficient `2^32` has no BabyBear felt.

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::effect_action_air::encode_amount;
use dregg_circuit::effect_vm::bytes32_to_8_limbs;
use dregg_circuit::field::BabyBear;

const BURN_GOLDEN: &str = include_str!("../../circuit/descriptors/by-name/effect-burn.json");

fn burn_row(target: &[u8; 32], old: u64, new: u64, amount: u64, was_burn: u64) -> Vec<BabyBear> {
    let mut row = vec![BabyBear::ZERO; 27];
    row[0..8].copy_from_slice(&bytes32_to_8_limbs(target));
    row[8..12].copy_from_slice(&encode_amount(old));
    row[12..16].copy_from_slice(&encode_amount(new));
    row[16..20].copy_from_slice(&encode_amount(amount));
    row[20..24].copy_from_slice(&encode_amount(was_burn));
    let mut borrow = 0u64;
    for i in 0..3u32 {
        let o = (old >> (i * 16)) & 0xFFFF;
        let a = ((amount >> (i * 16)) & 0xFFFF) + borrow;
        borrow = u64::from(o < a);
        row[24 + i as usize] = BabyBear::new(borrow as u32);
    }
    row
}

fn burn_pis(target: &[u8; 32], old: u64, new: u64, amount: u64, was_burn: u64) -> Vec<BabyBear> {
    burn_row(target, old, new, amount, was_burn)[0..24].to_vec()
}

fn rows4(row: Vec<BabyBear>) -> Vec<Vec<BabyBear>> {
    vec![row.clone(), row.clone(), row.clone(), row]
}

fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }));
    !matches!(r, Ok(Ok(())))
}

fn drop_at(desc: &EffectVmDescriptor2, idx: usize) -> EffectVmDescriptor2 {
    let mut d = desc.clone();
    d.constraints.remove(idx);
    d
}

/// `was_burn_flag`'s LIMB 1 is nonzero (`was_burn = 2^16 + 1` → limb0 = 1, limb1 = 1). The limb-0
/// pin (`var20 - 1`) is satisfied (1 - 1 = 0); the ONLY violated relation is the limb-1 pin
/// (`var21 == 0`, but 1 != 0). Trace + PI moved together so all 24 pins hold and the borrow chain
/// still closes.
#[test]
fn burn_wasburn_limb1_bites_its_own_pin() {
    let desc = parse_vm_descriptor2(BURN_GOLDEN).expect("decode");
    let target = [0x11u8; 32];

    // Honest baseline accepts (non-vacuity).
    assert!(!rejects(
        &desc,
        &rows4(burn_row(&target, 1000, 600, 400, 1)),
        &burn_pis(&target, 1000, 600, 400, 1)
    ));

    // Tamper: was_burn = 2^16 + 1 → limb0 = 1 (passes the limb-0 pin), limb1 = 1 (fails limb-1).
    let wb: u64 = 65_537;
    let t = rows4(burn_row(&target, 1000, 600, 400, wb));
    let p = burn_pis(&target, 1000, 600, 400, wb);
    // Confirm the encoding is what we think: limb0 = 1, limb1 = 1.
    assert_eq!(encode_amount(wb)[0], BabyBear::new(1));
    assert_eq!(encode_amount(wb)[1], BabyBear::new(1));

    assert!(
        rejects(&desc, &t, &p),
        "was_burn limb 1 != 0 must be REJECTED by its own pin"
    );

    // Attribution: drop EXACTLY the limb-1 pin (idx 59) → the same tamper now ACCEPTS.
    assert!(
        !rejects(&drop_at(&desc, 59), &t, &p),
        "dropping the was_burn limb-1 pin (idx 59) flips the tamper to ACCEPT — the sole biting tooth"
    );

    // Control: dropping an UNRELATED gate (the limb-0 chain gate, idx 51) leaves the tamper
    // REJECTED — proving the rejection is not a generic prover error but is bound to idx 59.
    assert!(
        rejects(&drop_at(&desc, 51), &t, &p),
        "dropping the limb-0 chain gate does NOT rescue the tamper — rejection is specific to 59"
    );
}
