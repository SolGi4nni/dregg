//! UNIQUENESS — the critical property (`UniqueOutputs` in `Dregg2/Crypto/VRF.lean`).
//!
//! Two halves:
//!
//! 1. The XM-VRF Merkle construction: for a fixed `(pk, epoch)`, no second output
//!    verifies — a would-be equivocation is rejected, because the output is bound
//!    into the leaf by a collision-resistant hash. Holds even for a MALICIOUSLY
//!    chosen `pk` (the argument uses no honest-keygen assumption).
//!
//! 2. The X-VRF/WOTS+ PITFALL, made concrete: the naive chain "VRF" admits TWO
//!    distinct verifying outputs under one public key (the "Breaking X-VRF" shape,
//!    FC24) — and the analogous chain-shift attack, transplanted onto the Merkle
//!    VRF, produces a NON-verifying proof.

use crypto_xmvrf::naive_wots::{forge_two_outputs, NaiveWotsVrf};
use crypto_xmvrf::{keygen_from_seed, verify, PublicKey};

/// The honest output is the ONLY one that verifies at its epoch: sweeping many
/// candidate outputs, exactly the honest `y` passes.
#[test]
fn at_most_one_output_verifies_per_epoch() {
    let (pk, sk) = keygen_from_seed(&[3u8; 32], 5);
    let epoch = 11u64;
    let (y, proof) = sk.eval(epoch).unwrap();

    // The honest output verifies...
    assert!(verify(&pk, epoch, &y, &proof));

    // ...and NO altered output verifies with the same (honest) proof: changing y
    // changes the leaf hash, so the Merkle path no longer reaches the root.
    for byte in 0..32usize {
        for bit in 0..8u8 {
            let mut y2 = y;
            y2[byte] ^= 1 << bit;
            assert!(
                !verify(&pk, epoch, &y2, &proof),
                "a distinct output must not verify (byte {byte}, bit {bit})"
            );
        }
    }
}

/// Even with an ADVERSARIALLY chosen opening `r`, you cannot make a second output
/// verify: to hit the committed leaf you would need `H(epoch‖y2‖r2) = leaf` with
/// `y2 != y` — a blake3 collision. We assert the honest opening is forced (any
/// other opening for the honest `y` also fails), witnessing the leaf binding.
#[test]
fn opening_cannot_be_swapped_to_equivocate() {
    let (pk, sk) = keygen_from_seed(&[100u8; 32], 4);
    let epoch = 5u64;
    let (y, proof) = sk.eval(epoch).unwrap();
    assert!(verify(&pk, epoch, &y, &proof));

    // Try many alternative openings for a DIFFERENT output; none can reconstruct
    // the committed leaf (that would be a collision). Bounded search stands in for
    // the collision-resistance reduction proved in Lean / the papers.
    let y2 = {
        let mut t = y;
        t[0] ^= 0xff;
        t
    };
    for k in 0u64..4096 {
        let mut r2 = proof.r;
        r2[0..8].copy_from_slice(&k.to_le_bytes());
        let mut p2 = proof.clone();
        p2.r = r2;
        assert!(
            !verify(&pk, epoch, &y2, &p2),
            "no opening should let a distinct output verify (k={k})"
        );
    }
}

/// A maliciously chosen `pk` (arbitrary bytes) does not gain the attacker two
/// outputs: uniqueness is a property of the verify RELATION, independent of how
/// `pk` was produced. For a random-root `pk`, either nothing verifies or (with
/// negligible probability) one thing does — never a provable pair. We check that
/// the honest proof from one key does not verify under a different root, i.e. the
/// binding is to THIS root.
#[test]
fn uniqueness_is_relative_to_the_root_not_honest_keygen() {
    let (pk_a, sk_a) = keygen_from_seed(&[1u8; 32], 4);
    let (pk_b, _sk_b) = keygen_from_seed(&[2u8; 32], 4);
    assert_ne!(pk_a.root, pk_b.root);

    let (y, proof) = sk_a.eval(6).unwrap();
    assert!(verify(&pk_a, 6, &y, &proof));
    // The same (y, proof) cannot verify under an unrelated root.
    assert!(!verify(&pk_b, 6, &y, &proof));

    // A hand-crafted malicious root: the honest proof still will not verify (would
    // require a collision to match the crafted root at position 6).
    let malicious = PublicKey {
        root: [0x55u8; 32],
        height: 4,
    };
    assert!(!verify(&malicious, 6, &y, &proof));
}

// ---------------------------------------------------------------------------
// The X-VRF / WOTS+ pitfall, and the contrast.
// ---------------------------------------------------------------------------

/// THE PITFALL (Breaking X-VRF, FC24): the naive WOTS+-style chain VRF admits TWO
/// distinct outputs verifying under ONE public key. This is the `two_outputs_
/// break_uniqueness` / `badVRF` witness from the Lean framework, executable.
#[test]
fn naive_wots_vrf_breaks_uniqueness() {
    let scheme = NaiveWotsVrf { l: 16 };
    let sk = [0xABu8; 32];

    // Chain-shift equivocation at positions 3 and 9 under one pk.
    let two = forge_two_outputs(&scheme, &sk, 3, 9);
    let (b1, y1, sig1) = two.first;
    let (b2, y2, sig2) = two.second;

    // BOTH verify against the SAME public key...
    assert!(
        scheme.verify(&two.pk, b1, &y1, &sig1),
        "first output verifies"
    );
    assert!(
        scheme.verify(&two.pk, b2, &y2, &sig2),
        "second output verifies"
    );
    // ...yet the two outputs are DISTINCT: uniqueness is broken.
    assert_ne!(y1, y2, "two distinct outputs both verify — the X-VRF break");
}

/// THE CONTRAST: transplant the chain-shift idea onto the Merkle XM-VRF. There is
/// no chain to shift; to get a second verifying output you must present a
/// different `y` (or `r`) that reconstructs the SAME committed leaf — a blake3
/// collision. So the equivocation FAILS: no second output verifies.
#[test]
fn merkle_vrf_defeats_the_chain_shift() {
    let (pk, sk) = keygen_from_seed(&[0xCDu8; 32], 5);
    let epoch = 7u64;
    let (y, proof) = sk.eval(epoch).unwrap();
    assert!(verify(&pk, epoch, &y, &proof));

    // The analogue of the WOTS chain shift is "derive a related second output and
    // reuse the position/proof". Any y' != y reusing the same path fails, because
    // the leaf hash H(epoch‖y'‖r) differs and no longer authenticates to the root.
    let related = {
        // Deterministically derive a "shifted" candidate, mirroring c(sig).
        let mut h = blake3::Hasher::new();
        h.update(b"wots-chain");
        h.update(&y);
        *h.finalize().as_bytes()
    };
    assert_ne!(related, y);
    assert!(
        !verify(&pk, epoch, &related, &proof),
        "the shifted second output must NOT verify — Merkle CR binding holds"
    );
}
