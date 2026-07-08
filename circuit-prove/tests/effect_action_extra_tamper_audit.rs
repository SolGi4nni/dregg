//! ADVERSARIAL AUDIT (additive): one more isolating tamper the primary gate did not write.
//!
//! The primary gate (`effect_action_emit_gate.rs`) exercises the pi_binding, the low-limb
//! subtraction `cLo`, the `was_burn_lo` disclosure pin, and the continuity window_gate. It leaves
//! `cWasBurnHi` (`was_burn_hi == 0`, burn gate idx 37) UN-isolated. This test bites exactly that
//! tooth: a `was_burn_flag` whose HIGH limb is nonzero but whose LOW limb is still 1 (so `cWasBurnLo`
//! is satisfied and the ONLY violated relation is `cWasBurnHi`), with trace AND PI moved together so
//! every `pi_binding` still holds. Then it drops constraint idx 37 and shows the SAME tamper flips
//! REJECT -> ACCEPT, proving the rejection is attributable to `cWasBurnHi` alone.

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::effect_action_air::{encode_amount, encode_hash};
use dregg_circuit::field::BabyBear;

const BURN_GOLDEN: &str = r#"{"name":"dregg-effect-burn-v1","ir":2,"trace_width":17,"public_input_count":16,"tables":[],"constraints":[{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":0},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":0}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":1},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":1}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":2},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":2}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":3},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":3}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":4},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":4}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":5},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":5}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":6},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":6}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":7},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":7}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":8},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":8}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":9},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":9}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":10},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":10}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":11},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":11}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":12},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":12}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":13},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":13}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":14},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":14}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":15},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":15}}}},{"t":"window_gate","on_transition":true,"body":{"t":"add","l":{"t":"nxt","c":16},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"loc","c":16}}}},{"t":"pi_binding","row":"first","col":0,"pi_index":0},{"t":"pi_binding","row":"first","col":1,"pi_index":1},{"t":"pi_binding","row":"first","col":2,"pi_index":2},{"t":"pi_binding","row":"first","col":3,"pi_index":3},{"t":"pi_binding","row":"first","col":4,"pi_index":4},{"t":"pi_binding","row":"first","col":5,"pi_index":5},{"t":"pi_binding","row":"first","col":6,"pi_index":6},{"t":"pi_binding","row":"first","col":7,"pi_index":7},{"t":"pi_binding","row":"first","col":8,"pi_index":8},{"t":"pi_binding","row":"first","col":9,"pi_index":9},{"t":"pi_binding","row":"first","col":10,"pi_index":10},{"t":"pi_binding","row":"first","col":11,"pi_index":11},{"t":"pi_binding","row":"first","col":12,"pi_index":12},{"t":"pi_binding","row":"first","col":13,"pi_index":13},{"t":"pi_binding","row":"first","col":14,"pi_index":14},{"t":"pi_binding","row":"first","col":15,"pi_index":15},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":10},"r":{"t":"var","v":12}},"r":{"t":"add","l":{"t":"mul","l":{"t":"const","v":-4294967296},"r":{"t":"var","v":16}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":8}}}}},{"t":"gate","body":{"t":"add","l":{"t":"add","l":{"t":"var","v":11},"r":{"t":"var","v":13}},"r":{"t":"add","l":{"t":"var","v":16},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"var","v":9}}}}},{"t":"gate","body":{"t":"mul","l":{"t":"var","v":16},"r":{"t":"add","l":{"t":"var","v":16},"r":{"t":"const","v":-1}}}},{"t":"gate","body":{"t":"add","l":{"t":"var","v":14},"r":{"t":"const","v":-1}}},{"t":"gate","body":{"t":"var","v":15}}],"hash_sites":[],"ranges":[]}"#;

fn burn_row(target: &[u8; 32], old: u64, new: u64, amount: u64, was_burn: u64) -> Vec<BabyBear> {
    let mut row = vec![BabyBear::ZERO; 17];
    row[0..8].copy_from_slice(&encode_hash(target));
    let [o_lo, o_hi] = encode_amount(old);
    let [n_lo, n_hi] = encode_amount(new);
    let [a_lo, a_hi] = encode_amount(amount);
    let [w_lo, w_hi] = encode_amount(was_burn);
    row[8] = o_lo;
    row[9] = o_hi;
    row[10] = n_lo;
    row[11] = n_hi;
    row[12] = a_lo;
    row[13] = a_hi;
    row[14] = w_lo;
    row[15] = w_hi;
    let old_lo = old & 0xFFFF_FFFF;
    let amt_lo = amount & 0xFFFF_FFFF;
    row[16] = if old_lo < amt_lo {
        BabyBear::new(1)
    } else {
        BabyBear::ZERO
    };
    row
}

fn burn_pis(target: &[u8; 32], old: u64, new: u64, amount: u64, was_burn: u64) -> Vec<BabyBear> {
    burn_row(target, old, new, amount, was_burn)[0..16].to_vec()
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

/// `was_burn_flag`'s HIGH limb is nonzero (was_burn = 2^32 + 1 -> lo=1, hi=1). `cWasBurnLo`
/// (`var14 - 1`) is satisfied (1 - 1 = 0); the ONLY violated relation is `cWasBurnHi` (`var15 == 0`,
/// but 1 != 0). Trace + PI moved together so all 16 pins hold and the subtraction still balances.
#[test]
fn burn_wasburn_hi_limb_bites_cwasburnhi() {
    let desc = parse_vm_descriptor2(BURN_GOLDEN).expect("decode");
    let target = [0x11u8; 32];

    // Honest baseline accepts (non-vacuity).
    assert!(!rejects(
        &desc,
        &rows4(burn_row(&target, 1000, 600, 400, 1)),
        &burn_pis(&target, 1000, 600, 400, 1)
    ));

    // Tamper: was_burn = 2^32 + 1 -> lo limb 1 (passes cWasBurnLo), hi limb 1 (fails cWasBurnHi).
    let wb: u64 = 4_294_967_297;
    let t = rows4(burn_row(&target, 1000, 600, 400, wb));
    let p = burn_pis(&target, 1000, 600, 400, wb);
    // Confirm the encoding is what we think: lo=1, hi=1.
    assert_eq!(encode_amount(wb)[0], BabyBear::new(1));
    assert_eq!(encode_amount(wb)[1], BabyBear::new(1));

    assert!(
        rejects(&desc, &t, &p),
        "was_burn_hi != 0 must be REJECTED by cWasBurnHi"
    );

    // Attribution: drop EXACTLY cWasBurnHi (idx 37) -> the same tamper now ACCEPTS.
    assert!(
        !rejects(&drop_at(&desc, 37), &t, &p),
        "dropping cWasBurnHi (idx 37) flips the hi-limb tamper to ACCEPT — it is the sole biting tooth"
    );

    // Control: dropping an UNRELATED gate (cLo, idx 33) leaves the tamper REJECTED — proving the
    // rejection is not a generic prover error but is bound to idx 37 specifically.
    assert!(
        rejects(&drop_at(&desc, 33), &t, &p),
        "dropping cLo does NOT rescue the hi-limb tamper — rejection is specific to cWasBurnHi"
    );
}
