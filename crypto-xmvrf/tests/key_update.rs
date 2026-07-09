//! KEY UPDATE — determinism of the ratchet, and forward security.
//!
//! The VRF is key-updatable (many-time): one key spans `2^height` epochs, and
//! `update` advances the epoch. This checks:
//!   * DETERMINISM: the whole schedule is a deterministic function of the seed —
//!     eval is stable across independent keygens and across the ratchet path.
//!   * FORWARD SECURITY: after ratcheting past an epoch, that epoch (and earlier)
//!     can no longer be evaluated — its chain state is destroyed.

use crypto_xmvrf::{keygen_from_seed, verify, EvalError};

/// The output at each epoch is deterministic in the seed: two independent keygens
/// from the same seed produce identical `(pk, y)` for every epoch.
#[test]
fn keygen_is_deterministic() {
    let (pk1, sk1) = keygen_from_seed(&[77u8; 32], 6);
    let (pk2, sk2) = keygen_from_seed(&[77u8; 32], 6);
    assert_eq!(pk1, pk2, "same seed ⇒ same public key");
    for epoch in 0..(1u64 << 6) {
        let (y1, _) = sk1.eval(epoch).unwrap();
        let (y2, _) = sk2.eval(epoch).unwrap();
        assert_eq!(y1, y2, "deterministic output at epoch {epoch}");
    }
}

/// Evaluating a future epoch directly equals ratcheting up to it and evaluating
/// the current epoch: the forward-walk in `eval` and the mutating `update` agree.
#[test]
fn ratchet_path_matches_direct_eval() {
    let (pk, mut sk_ratchet) = keygen_from_seed(&[5u8; 32], 6);
    let (_pk2, sk_direct) = keygen_from_seed(&[5u8; 32], 6);

    for target in 0..(1u64 << 6) {
        // Direct eval of `target` from a fresh (epoch-0) key.
        let (y_direct, p_direct) = sk_direct.eval(target).unwrap();

        // Ratchet the mutating key up to `target`, then eval the current epoch.
        while sk_ratchet.epoch() < target {
            assert!(sk_ratchet.update());
        }
        let (y_ratchet, p_ratchet) = sk_ratchet.eval(sk_ratchet.epoch()).unwrap();

        assert_eq!(
            y_direct, y_ratchet,
            "same output via ratchet at epoch {target}"
        );
        assert_eq!(p_direct.r, p_ratchet.r, "same opening at epoch {target}");
        assert!(verify(&pk, target, &y_ratchet, &p_ratchet));
    }
}

/// FORWARD SECURITY: once ratcheted past an epoch, evaluating it fails with
/// `EpochExpired` — the state needed to recompute its secrets is gone.
#[test]
fn past_epochs_become_unevaluable_after_update() {
    let (_pk, mut sk) = keygen_from_seed(&[13u8; 32], 5);

    // Advance to epoch 10.
    for _ in 0..10 {
        assert!(sk.update());
    }
    assert_eq!(sk.epoch(), 10);

    // Past epochs are expired.
    for past in 0..10u64 {
        assert_eq!(
            sk.eval(past),
            Err(EvalError::EpochExpired {
                current: 10,
                requested: past
            }),
            "epoch {past} must be expired after ratcheting to 10"
        );
    }
    // Current and future epochs still evaluate.
    assert!(sk.eval(10).is_ok());
    assert!(sk.eval(20).is_ok());
}

/// The key is finite: `update` refuses to advance past the last epoch, and eval
/// beyond capacity errors with `EpochOutOfRange`.
#[test]
fn key_lifetime_is_bounded() {
    let height = 4u8; // 16 epochs: 0..=15
    let (_pk, mut sk) = keygen_from_seed(&[99u8; 32], height);
    let capacity = 1u64 << height;

    // Ratchet to the last usable epoch (15); update then refuses.
    while sk.update() {}
    assert_eq!(sk.epoch(), capacity - 1, "stops at the last epoch");
    assert!(!sk.update(), "no update past the end");

    // Out-of-range eval errors.
    assert_eq!(
        sk.eval(capacity),
        Err(EvalError::EpochOutOfRange {
            requested: capacity,
            capacity
        })
    );
}

/// A different seed yields a different key schedule (sanity: the ratchet is keyed).
#[test]
fn distinct_seeds_give_distinct_schedules() {
    let (pk_a, sk_a) = keygen_from_seed(&[1u8; 32], 5);
    let (pk_b, sk_b) = keygen_from_seed(&[2u8; 32], 5);
    assert_ne!(pk_a.root, pk_b.root);
    let (ya, _) = sk_a.eval(0).unwrap();
    let (yb, _) = sk_b.eval(0).unwrap();
    assert_ne!(ya, yb);
}
