//! **THE WIDE DIGEST** — a native ~124-bit binding built from the one-site 8-felt
//! Poseidon2 compression the custom-leaf lowering now carries.
//!
//! # The construction (a `cap_node8` Merkle-Damgård chain)
//!
//! `dregg_circuit::cap_root::cap_node8` is the native arity-16 `node8` compression
//! `perm(L8 ‖ R8)[0..8]` — one Poseidon2 permutation carrying all 8 output lanes. The
//! custom-leaf lowering carries it as `ConstraintExpr::MerkleHash8`
//! (`circuit/src/custom_leaf_lowering.rs`): ONE `TID_P2` chip lookup whose 8 outputs are
//! PROGRAM-OWNED columns, so a full 8-felt (~124-bit) digest costs **one site and zero lane
//! columns**.
//!
//! The wide digest is a Merkle-Damgård chain over that compression. An 8-felt accumulator
//! is seeded with a domain-separated IV and absorbs the canonical stream 8 felts at a time:
//!
//! ```text
//!   acc8 := IV8(domain)
//!   for each 8-felt block B8 of the stream (zero-padded):  acc8 := cap_node8(acc8, B8)
//!   root := acc8                                            (8 felts, ~124-bit)
//! ```
//!
//! Modelling `cap_node8` as a random 16→8 compression, a stream that collides needs a full
//! 8-felt (~124-bit) collision — matching the deployed 8-felt `WideHash` /
//! `CellState::compute_commitment_8` and sitting above the ~112.6-bit FRI soundness floor.
//! The stream is a function of the shape (each stream is padded to the shape's maxima with
//! the canonical all-zero inactive encoding, so its LENGTH — and hence the block count — is
//! fixed per VK), and the four streams are domain-separated by their IVs.
//!
//! # What changed (was: 8 parallel Hash4to1 chains)
//!
//! This digest used to reach ~124 bits the only way the substrate then allowed: `W = 8`
//! parallel 4-ary (`Hash4to1`) absorb chains, because the custom-leaf lowering REFUSED
//! `MerkleHash8` (it carried single-output chip sites only). That refusal is gone. One
//! node8 site now binds all 8 felts, so the 8× site multiplier — and its per-site 7 lane
//! columns in the lowered leaf — are gone. See `crate::air::wide_chain` (the in-circuit
//! twin) and `tests/size.rs` (the before/after program+lane column census).
//!
//! Every function here is the HOST TWIN of the in-circuit chain in `crate::air`, which
//! rebuilds the identical `cap_node8` chain over witnessed columns with
//! `ConstraintExpr::MerkleHash8`. The two are pinned against each other by the PI-layout
//! and root tests in `tests/composition.rs`.

use dregg_circuit::cap_root::cap_node8;
use dregg_circuit::field::BabyBear;

use crate::field::fb;

/// Felts absorbed per node8 site (`cap_node8` compresses `acc8 ‖ block8`, so 8 fresh data
/// felts ride each site).
pub const ABSORB_RATE: usize = 8;

/// **THE BINDING WIDTH.** Felts in a committed root (`ruleset_root`, `subjects_root`,
/// `outcome_commitment`, `explanation_root`) — the native output width of `cap_node8`.
///
/// Each felt carries ~31 bits, so 8 felts give a ~248-bit digest with a ~124-bit collision
/// floor, matching the deployed 8-felt `WideHash` / `CellState::compute_commitment_8` and
/// sitting above the ~112.6-bit FRI soundness floor. It is not a knob: `cap_node8` outputs
/// exactly 8 lanes, and the digest binds all of them.
pub const DIGEST_FELTS: usize = 8;

/// Spacing between domain IV lanes, so `domain * LANE_STRIDE + lane` never collides across
/// domains for `lane < LANE_STRIDE`.
pub const LANE_STRIDE: u64 = 256;

/// Domain tag: the canonical subjects stream.
pub const DOMAIN_SUBJECTS: u64 = 0x9C01;
/// Domain tag: the canonical ruleset stream (THE COMPOSITION LAW).
pub const DOMAIN_RULESET: u64 = 0x9C02;
/// Domain tag: the outcome.
pub const DOMAIN_OUTCOME: u64 = 0x9C03;
/// Domain tag: the per-term explanation contributions.
pub const DOMAIN_EXPLANATION: u64 = 0x9C04;

/// The domain-separated 8-felt initial accumulator (`IV8`) for `domain`: lane `k` is
/// `domain * LANE_STRIDE + k`, so distinct domains seed the chain at distinct 8-felt
/// points and the four roots never coincide by construction.
pub fn iv8(domain: u64) -> [BabyBear; DIGEST_FELTS] {
    core::array::from_fn(|lane| fb((domain * LANE_STRIDE) as i128 + lane as i128))
}

/// The 8-felt digest of `data` under `domain`. Host twin of `crate::air::wide_chain`.
///
/// A `cap_node8` Merkle-Damgård chain: seed with `iv8(domain)`, then absorb `data` 8 felts
/// at a time (the final block zero-padded), returning the 8-felt accumulator.
pub fn wide_digest(domain: u64, data: &[BabyBear]) -> Vec<BabyBear> {
    let mut acc = iv8(domain);
    for block in data.chunks(ABSORB_RATE) {
        let mut b8 = [BabyBear::ZERO; DIGEST_FELTS];
        b8[..block.len()].copy_from_slice(block);
        acc = cap_node8(acc, b8);
    }
    acc.to_vec()
}
