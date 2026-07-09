//! PROVABILITY (correctness): every honestly-evaluated `(y, π)` verifies.
//!
//! This is the Lean `provability` / `Correct` property (`Dregg2/Crypto/VRF.lean`)
//! at the executable level: for the honest key, `verify(pk, x, eval(sk, x)) = true`.

use crypto_xmvrf::{keygen_from_seed, verify};

/// Honest eval verifies across every epoch of the key's lifetime.
#[test]
fn honest_eval_verifies_all_epochs() {
    let height = 6u8; // 64 epochs
    let (pk, sk) = keygen_from_seed(&[7u8; 32], height);
    let capacity = 1u64 << height;
    for epoch in 0..capacity {
        let (y, proof) = sk.eval(epoch).expect("eval within lifetime");
        assert!(
            verify(&pk, epoch, &y, &proof),
            "honest output must verify at epoch {epoch}"
        );
    }
}

/// Provability still holds AFTER ratcheting: at each epoch, evaluate the current
/// epoch, verify, then update — the key-updatable usage pattern.
#[test]
fn provability_holds_along_the_ratchet() {
    let height = 5u8; // 32 epochs
    let (pk, mut sk) = keygen_from_seed(&[42u8; 32], height);
    loop {
        let epoch = sk.epoch();
        let (y, proof) = sk.eval(epoch).expect("current epoch is evaluable");
        assert!(
            verify(&pk, epoch, &y, &proof),
            "verifies at ratcheted epoch {epoch}"
        );
        if !sk.update() {
            break; // key exhausted
        }
    }
    assert_eq!(
        sk.epoch(),
        (1u64 << height) - 1,
        "ratcheted to the last epoch"
    );
}

/// A wrong output, a wrong epoch, or a tampered proof must NOT verify (soundness
/// of the verifier — the flip side of provability).
#[test]
fn tampered_pairs_do_not_verify() {
    let (pk, sk) = keygen_from_seed(&[9u8; 32], 4);
    let (y, proof) = sk.eval(3).unwrap();

    // Wrong output.
    let mut y_bad = y;
    y_bad[0] ^= 1;
    assert!(!verify(&pk, 3, &y_bad, &proof), "flipped output rejected");

    // Wrong epoch (right output, wrong position).
    assert!(
        !verify(&pk, 2, &y, &proof),
        "output presented at wrong epoch rejected"
    );

    // Tampered opening.
    let mut proof_bad = proof.clone();
    proof_bad.r[0] ^= 1;
    assert!(!verify(&pk, 3, &y, &proof_bad), "tampered opening rejected");

    // Tampered path.
    let mut proof_bad2 = proof.clone();
    proof_bad2.path[0][0] ^= 1;
    assert!(
        !verify(&pk, 3, &y, &proof_bad2),
        "tampered auth path rejected"
    );
}
