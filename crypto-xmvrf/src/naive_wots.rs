//! The X-VRF pitfall, made concrete: a naive WOTS+-style chain "VRF" whose
//! `verify` relation admits TWO distinct outputs for one public key — a
//! UNIQUENESS break.
//!
//! # Why this exists
//!
//! X-VRF derives its VRF output from a WOTS+/XMSS one-time signature. The WOTS+
//! chaining function `c(·) = H(·)` iterated is only ONE-WAY / 2nd-preimage-resistant,
//! it is NOT collision-resistant, and — crucially — its verification accepts ANY
//! chain position whose forward-iteration reaches the public key. Given one valid
//! signature you can compute a valid signature at every LATER position by iterating
//! the chain. When the VRF output is a function of the signature, that is several
//! distinct valid outputs under one public key: uniqueness fails. A. Bodaghi et
//! al., *Breaking the X-VRF* (FC24), turns this into a full attack by crafting a
//! malicious public key that admits two checksum-valid messages.
//!
//! This module abstracts the ESSENTIAL flaw — a chain verify that is not a
//! collision-resistant commitment to the output — into the smallest faithful toy:
//! a single hash chain of length `L`, output `= H("out" ‖ sig)`, verify
//! `= (c^{L-b}(sig) == pk)`. [`forge_two_outputs`] then exhibits, for ONE public
//! key, two distinct signatures at two positions, hence two distinct verifying
//! outputs. That is exactly the Lean `two_outputs_break_uniqueness` witness / the
//! `badVRF` tooth.
//!
//! # Honest scope of this demonstration
//!
//! This reproduces the STRUCTURAL cause (a chain verify accepts a family of
//! `(position, sig)` pairs from one seed, so `output = f(sig)` is multi-valued
//! under the verify relation), not the byte-exact Bodaghi checksum/malicious-pk
//! cryptanalysis. blake3 is collision-resistant, so a fixed-position second
//! preimage is genuinely hard; the equivocation demonstrated here is the
//! cross-position chain-shift that WOTS-chain verification inherently permits — the
//! same weakness the FC24 attack exploits. The contrast test then shows the
//! [`crate::vrf`] Merkle construction rejects the analogous shift.

use crate::hash::Bytes32;

/// The WOTS+ chaining function, one step: `c(x) = blake3("wots-chain" ‖ x)`.
fn chain_step(x: &Bytes32) -> Bytes32 {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"wots-chain");
    hasher.update(x);
    *hasher.finalize().as_bytes()
}

/// Iterate the chain function `n` times: `c^n(x)`.
fn chain(x: &Bytes32, n: usize) -> Bytes32 {
    let mut acc = *x;
    for _ in 0..n {
        acc = chain_step(&acc);
    }
    acc
}

/// The naive output binder: `y = blake3("wots-out" ‖ sig)`.
fn output_of(sig: &Bytes32) -> Bytes32 {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"wots-out");
    hasher.update(sig);
    *hasher.finalize().as_bytes()
}

/// A naive single-chain WOTS+-style "VRF" over a chain of length `L`. UNSOUND on
/// purpose — a teaching counterexample, never a construction to use.
#[derive(Clone, Copy, Debug)]
pub struct NaiveWotsVrf {
    /// Chain length; valid signature positions are `0..=L`.
    pub l: usize,
}

/// A naive public key: the chain endpoint `c^L(sk)`.
pub type NaivePk = Bytes32;

impl NaiveWotsVrf {
    /// Derive the public key from a secret seed: `pk = c^L(sk)`.
    pub fn public_key(&self, sk: &Bytes32) -> NaivePk {
        chain(sk, self.l)
    }

    /// "Sign"/eval at chain position `b ∈ [0, L]`: signature `sig = c^b(sk)`,
    /// output `y = H("out" ‖ sig)`.
    pub fn eval_at(&self, sk: &Bytes32, b: usize) -> (Bytes32, Bytes32) {
        assert!(b <= self.l, "position out of range");
        let sig = chain(sk, b);
        (output_of(&sig), sig)
    }

    /// Verify a `(position b, sig, y)` triple against `pk`: the chain must reach
    /// `pk` from position `b` (`c^{L-b}(sig) == pk`) and `y` must bind `sig`.
    /// Note the verifier ACCEPTS the prover-supplied position — the structural
    /// hole the chain-shift attack drives through.
    pub fn verify(&self, pk: &NaivePk, b: usize, y: &Bytes32, sig: &Bytes32) -> bool {
        if b > self.l {
            return false;
        }
        &chain(sig, self.l - b) == pk && &output_of(sig) == y
    }
}

/// A pair of distinct outputs that BOTH verify under one naive public key — the
/// concrete uniqueness break.
pub struct TwoOutputs {
    /// The single public key both outputs verify against.
    pub pk: NaivePk,
    /// First `(position, output, signature)`.
    pub first: (usize, Bytes32, Bytes32),
    /// Second `(position, output, signature)`.
    pub second: (usize, Bytes32, Bytes32),
}

/// **The X-VRF-style uniqueness break.** From one seed and one public key, produce
/// two DISTINCT valid outputs at positions `b1 < b2` via the chain shift
/// `sig2 = c^{b2-b1}(sig1)` (so `c^{L-b2}(sig2) = c^{L-b1}(sig1) = pk`). Both
/// verify; the outputs differ because the signatures differ. This is the WOTS+
/// chain weakness that "Breaking X-VRF" (FC24) weaponises.
///
/// # Panics
/// If `b1 >= b2` or `b2 > scheme.l`.
pub fn forge_two_outputs(scheme: &NaiveWotsVrf, sk: &Bytes32, b1: usize, b2: usize) -> TwoOutputs {
    assert!(b1 < b2 && b2 <= scheme.l, "need b1 < b2 <= L");
    let pk = scheme.public_key(sk);

    let sig1 = chain(sk, b1);
    let y1 = output_of(&sig1);

    // The shift: a valid signature at the LATER position, derived from sig1 alone.
    let sig2 = chain(&sig1, b2 - b1); // == c^{b2}(sk)
    let y2 = output_of(&sig2);

    TwoOutputs {
        pk,
        first: (b1, y1, sig1),
        second: (b2, y2, sig2),
    }
}
