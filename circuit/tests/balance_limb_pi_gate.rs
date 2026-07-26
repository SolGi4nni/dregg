//! The balance-limb PI range gate — and the length precondition that made it
//! unreachable.
//!
//! `verify_balance_limb_pis` is the executor/verifier-side precondition under
//! Constraint Group 6. Group 6 binds `NET_DELTA = FINAL - INIT` over BabyBear,
//! and that algebra is satisfied just as happily by limbs OUTSIDE their declared
//! widths — the subtraction wraps mod p and a forged `NET_DELTA` is reachable.
//! The AIR does not range-check the limbs; this function is where that happens.
//!
//! It shipped with two holes at once, which is why it needs its own file:
//!
//!   1. **Nothing called it.** Defined in `effect_vm::verify`, re-exported from
//!      `effect_vm` AND from the crate root, and invoked by no production path
//!      and no test. The Group 6 precondition was satisfied by nothing.
//!   2. **Nothing COULD call it on the leg that ships.** Its length guard
//!      demanded `pi::BASE_COUNT` (201 felts) while its body reads six offsets,
//!      all `<= 25`. The deployed `"effect-vm-rotated"` leg publishes
//!      `V1_PI_COUNT` (42). So every live PI vector would have been turned away
//!      as "too short" *before a single limb was examined* — a range check that
//!      reports a length complaint about the proof it was meant to police.
//!
//! Hole 2 is the one a caller could not have discovered by reading the name, so
//! the first test below asserts the deployed length is DECIDED, not merely that
//! some long vector passes.

use dregg_circuit::BabyBear;
use dregg_circuit::effect_vm::trace_rotated::V1_PI_COUNT;
use dregg_circuit::effect_vm::{BALANCE_LIMB_PI_MIN_LEN, pi, verify_balance_limb_pis};

/// An honest PI vector at the DEPLOYED rotated width, with every balance limb
/// inside its declared range.
fn honest_rotated_pis() -> Vec<BabyBear> {
    let mut v = vec![BabyBear::ZERO; V1_PI_COUNT];
    // A plain, in-range transfer: 1000 -> 700, so NET_DELTA = 300 outgoing.
    v[pi::INIT_BAL_LO] = BabyBear::new(1000);
    v[pi::INIT_BAL_HI] = BabyBear::new(0);
    v[pi::FINAL_BAL_LO] = BabyBear::new(700);
    v[pi::FINAL_BAL_HI] = BabyBear::new(0);
    v[pi::NET_DELTA_MAG] = BabyBear::new(300);
    v[pi::NET_DELTA_SIGN] = BabyBear::new(1);
    v
}

/// THE REGRESSION. The offsets this function reads all live in the v1 PI prefix,
/// so the deployed rotated leg carries them in full. A `V1_PI_COUNT` vector must
/// be *decided*, not turned away on length — that rejection is what kept the
/// check off the live path.
#[test]
fn deployed_rotated_pi_width_is_decided_not_refused_on_length() {
    assert!(
        BALANCE_LIMB_PI_MIN_LEN <= V1_PI_COUNT,
        "the gate's own precondition ({BALANCE_LIMB_PI_MIN_LEN}) exceeds the width of the \
         deployed rotated leg ({V1_PI_COUNT}); it is unreachable on the only leg that ships"
    );
    // And the guard is derived from the reads, not written down beside them.
    assert_eq!(BALANCE_LIMB_PI_MIN_LEN, pi::NET_DELTA_SIGN + 1);
    // The old guard. Kept as a live number so the regression is legible: this is
    // the width that was demanded, against the width that exists.
    assert!(
        pi::BASE_COUNT > V1_PI_COUNT,
        "the historical BASE_COUNT guard is expected to be wider than the deployed leg"
    );

    verify_balance_limb_pis(&honest_rotated_pis())
        .expect("an honest rotated-width PI vector must pass");
}

/// Below the floor it genuinely needs, it still refuses — the fix narrowed the
/// precondition to the reads, it did not delete it.
#[test]
fn a_vector_too_short_for_the_reads_is_still_refused() {
    let short = vec![BabyBear::ZERO; BALANCE_LIMB_PI_MIN_LEN - 1];
    let err = verify_balance_limb_pis(&short).expect_err("must refuse below its own read floor");
    assert!(
        err.contains("too short"),
        "expected a length refusal, got: {err}"
    );
}

/// CAN IT GO RED. `balance_lo` is a 30-bit column and `balance_hi` a field-bounded
/// one; each poke must produce an error NAMING the limb it is about, so a red
/// points somewhere rather than just being red.
#[test]
fn each_balance_limb_is_individually_range_checked_and_names_itself() {
    let cases: [(&str, usize, u32); 4] = [
        ("INIT_BAL_LO", pi::INIT_BAL_LO, 1 << 30),
        ("FINAL_BAL_LO", pi::FINAL_BAL_LO, 1 << 30),
        ("INIT_BAL_HI", pi::INIT_BAL_HI, 1 << 31),
        ("FINAL_BAL_HI", pi::FINAL_BAL_HI, 1 << 31),
    ];
    for (label, idx, bad) in cases {
        let mut v = honest_rotated_pis();
        // The RAW tuple constructor, deliberately — not `BabyBear::new`, which reduces
        // mod p and would fold `2^31` back to `2^27 - 1` (in range, so the poke would
        // silently test nothing). A non-canonical felt is exactly the wire shape the HI
        // bound defends against: `sub_public_inputs` arrive by postcard decode, which
        // does not canonicalize. The `turn` verify floor canonicalizes first, so there
        // the HI arm is defence-in-depth; on the SDK leg it is load-bearing.
        v[idx] = BabyBear(bad);
        let err = verify_balance_limb_pis(&v)
            .expect_err("an out-of-width limb must be rejected, not accepted");
        assert!(
            err.contains(label),
            "the refusal for {label} must name it; got: {err}"
        );
    }
}

/// `NET_DELTA_SIGN` is a boolean. A non-boolean sign is the shape that lets a
/// forger pick which direction the Group 5 selector reads.
#[test]
fn a_non_boolean_net_delta_sign_is_rejected() {
    let mut v = honest_rotated_pis();
    v[pi::NET_DELTA_SIGN] = BabyBear::new(2);
    let err = verify_balance_limb_pis(&v).expect_err("sign must be 0 or 1");
    assert!(err.contains("NET_DELTA_SIGN"), "got: {err}");
}

/// `NET_DELTA_MAG` must stay inside the per-limb subtraction domain, or the
/// algebraic check can be satisfied by a wrap rather than by the real delta.
#[test]
fn an_out_of_domain_net_delta_magnitude_is_rejected() {
    let mut v = honest_rotated_pis();
    v[pi::NET_DELTA_MAG] = BabyBear::new(1 << 30);
    let err = verify_balance_limb_pis(&v).expect_err("magnitude must fit the 30-bit domain");
    assert!(err.contains("NET_DELTA_MAG"), "got: {err}");
}
