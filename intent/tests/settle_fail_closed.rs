//! FAIL-CLOSED proof for the intent per-leg settle twin (#10).
//!
//! `settle_ring_verified` was INVERTED: the verified Lean export `dregg_record_kernel_step` is now the
//! AUTHORITATIVE per-leg decider (the in-process `rec_exec_asset` is a cross-checked differential
//! sibling), and when NO verified gate is registered the ring is REFUSED — not silently settled by the
//! unverified in-process fold, as the old `ffi::cross_check_leg`-skipped-when-absent path did.
//!
//! This links `dregg-intent` as a NORMAL dependency (compiled WITHOUT `cfg(test)`, so the
//! release/consumer path runs, not the in-crate differential sibling that keeps native authoritative)
//! and registers NO verified gate, forcing the no-export branch. It asserts a legitimate, conserving,
//! funded ring — one the old native-authoritative path settled — is now REFUSED fail-closed.
//!
//! (The verified path deciding on a full-Lean target is exercised in `dregg-exec-lean`'s tests, which
//! register the real `register_distributed_gates()` gate over the linked archive.)

use dregg_intent::verified_settle::{
    VerifiedLeg, VerifiedSettleError, funded_ledger, settle_ring_verified,
};

fn asset(b: u8) -> [u8; 32] {
    let mut a = [0u8; 32];
    a[0] = b;
    a
}

#[test]
fn settle_ring_fails_closed_without_gate() {
    // A closed, conserving 2-leg ring: 1 -> 2 and 2 -> 1 of the same asset/amount (every asset
    // balanced). `funded_ledger` funds each sender, so the ring is structurally settleable — the old
    // native-authoritative fold settled it. With NO verified gate registered the INVERTED path must
    // REFUSE it (fail closed), never settle it in the unverified in-process fold.
    let a = asset(0xA1);
    let legs = vec![
        VerifiedLeg {
            from: 1,
            to: 2,
            asset: a,
            amount: 50,
        },
        VerifiedLeg {
            from: 2,
            to: 1,
            asset: a,
            amount: 50,
        },
    ];
    let k0 = funded_ledger(&legs);

    let result = settle_ring_verified(&k0, &legs);
    assert!(
        result.is_err(),
        "settle_ring_verified must FAIL CLOSED (refuse the ring) when the verified gate is absent — \
         it must not settle a ring in the unverified in-process fold; got {result:?}"
    );
    assert!(
        matches!(result, Err(VerifiedSettleError::FfiUnavailable(_))),
        "the fail-closed refusal must be FfiUnavailable (no verified executor gate registered); \
         got {result:?}"
    );
}
