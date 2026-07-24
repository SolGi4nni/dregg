//! FAIL-CLOSED proof for the strand-admission twin (#7, red-team F-4).
//!
//! `AdmissionRegistry::admitted` used to fall back to the NATIVE Rust `admitted_rust`
//! (`is_seed ∨ vouched_to_threshold ∨ has_valid_bond`) when the verified Lean gate was not
//! registered. That native decider has been removed from the live path: the verdict is now the
//! verified Lean `dregg_strand_admit` gate, or — when no gate is registered — a FAIL-CLOSED
//! seeds-only admission. This integration test links `dregg-federation` as a NORMAL dependency
//! (compiled WITHOUT `cfg(test)`, so the release/consumer path runs, not the in-crate differential
//! sibling `admitted_rust`) and registers NO verified gate, forcing the no-export branch. It asserts
//! a strand that `admitted_rust` WOULD admit (bonded / vouched-to-threshold) is REJECTED, while
//! genesis seeds still admit.
//!
//! (The verified path deciding on a full-Lean target is exercised in `dregg-exec-lean`'s tests, which
//! register the real `register_distributed_gates()` gate over the linked archive.)

use dregg_federation::admission::{AdmissionRegistry, Bond, Vouch};
use dregg_types::generate_keypair;

/// A bonded newcomer and a vouched-to-threshold candidate — both admitted by the native Rust twin —
/// are REJECTED fail-closed when the verified gate is absent; genesis seeds still admit.
#[test]
fn strand_admission_fails_closed_to_seeds_without_gate() {
    // seeds {a, b}, vouch threshold 2, min bond 100 (= the Lean `fedDemo` parameters).
    let (sk_a, a) = generate_keypair();
    let (sk_b, b) = generate_keypair();
    let mut reg = AdmissionRegistry::new([a, b], 2, 100);

    // A newcomer bonded AT the floor: the native twin `admitted_rust` admits it via the stake path.
    let (sk_bonded, bonded) = generate_keypair();
    assert!(reg.add_bond(Bond::post(&sk_bonded, 100)));

    // A candidate vouched by BOTH seeds (>= threshold 2): the native twin admits it via the vouch path.
    let (_, vouched) = generate_keypair();
    assert!(reg.add_vouch(Vouch::create(&sk_a, vouched)));
    assert!(reg.add_vouch(Vouch::create(&sk_b, vouched)));

    // A fresh Sybil with no standing at all.
    let (_, sybil) = generate_keypair();

    // ── The release/consumer path with NO verified gate registered: FAIL CLOSED to seeds-only. ──
    assert!(
        reg.admitted(&a) && reg.admitted(&b),
        "genesis seeds are admitted by construction even fail-closed"
    );
    assert!(
        !reg.admitted(&bonded),
        "F-4 fail-closed: a BONDED non-seed (which the native `admitted_rust` twin would admit) must \
         be REJECTED when the verified strand-admission gate is absent — never a silent native decision"
    );
    assert!(
        !reg.admitted(&vouched),
        "F-4 fail-closed: a VOUCHED-to-threshold non-seed (admitted by the native twin) must be \
         REJECTED when the verified gate is absent"
    );
    assert!(
        !reg.admitted(&sybil),
        "a fresh Sybil is rejected on every path"
    );

    // The participant projection the node hands to `tau` is likewise seeds-only fail-closed.
    let candidates = vec![a, b, bonded, vouched, sybil];
    let admitted = reg.admitted_participants(&candidates);
    assert_eq!(
        admitted,
        vec![a, b],
        "fail-closed admitted_participants is exactly the genesis seeds — no unverified non-seed anchors finality"
    );
    assert!(!reg.is_finalizable(&bonded) && !reg.is_finalizable(&vouched));
}
