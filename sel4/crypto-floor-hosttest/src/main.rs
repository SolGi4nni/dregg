//! Host witness for the executor PD's §2 byte-channel STARK verify.
//!
//! Includes the SAME carried STARK core the crypto-floor cross-compiles
//! (`crypto-floor/src/stark_core/{field,stark}.rs`) and replicates the
//! `dreggcf_stark_verify_bytes` + `dreggcf_stark_selftest` wiring from
//! `crypto-floor/src/lib.rs` verbatim, then RUNS the anti-ghost teeth natively on
//! the host: ACCEPT a sound proof, REJECT a tampered proof, REJECT a wrong public
//! input (the boundary tooth). The verify path here is byte-for-byte the path the
//! seL4 executor PD's crypto floor runs — this is the runnable proof that the
//! wiring bites, on a box with no user-mode qemu-aarch64.

// The carried stark_core exposes the FULL STARK API (prove_full/verify_with_config
// /replay_fri_betas/…); the floor uses a subset, so the rest is legitimately unused
// HERE. Allow dead_code crate-wide rather than editing the verbatim-carried file.
#![allow(dead_code)]

// std crate, but `alloc::` paths must resolve (the carried files `use alloc::...`).
// In a std crate `extern crate alloc;` aliases std's own alloc — one alloc, no dup.
extern crate alloc;

#[path = "../../dregg-pd/executor-pd/crypto-floor/src/stark_core/mod.rs"]
mod stark_core;

use stark_core::field::BabyBear;
use stark_core::stark::{prove, proof_from_bytes, proof_to_bytes, verify, BoundaryConstraint, StarkAir};

// ---- the carried AIR (byte-for-byte verifier-stark's CounterSquareAir) --------
struct CounterSquareAir;

impl StarkAir for CounterSquareAir {
    fn width(&self) -> usize {
        2
    }
    fn constraint_degree(&self) -> usize {
        2
    }
    fn air_name(&self) -> &'static str {
        "dregg-firmament-counter-square-v1"
    }
    fn has_chain_continuity(&self) -> bool {
        false
    }
    fn eval_constraints(
        &self,
        local: &[BabyBear],
        next: &[BabyBear],
        _public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        let c1 = next[0] - local[0] - BabyBear::ONE;
        let c2 = local[1] - local[0] * local[0];
        c1 + alpha * c2
    }
    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        _trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        if public_inputs.is_empty() {
            return vec![];
        }
        vec![BoundaryConstraint {
            row: 0,
            col: 0,
            value: public_inputs[0],
        }]
    }
}

fn air_by_name(name: &str) -> Option<&'static dyn StarkAir> {
    match name {
        "dregg-firmament-counter-square-v1" => Some(&CounterSquareAir),
        _ => None,
    }
}

/// VERBATIM the crypto-floor `dreggcf_stark_verify_bytes` wiring (lib.rs): decode
/// the proof bytes, resolve the carried AIR by `air_name`, decode the LE-u32 PI
/// limbs, run `verify`. Returns 1 iff verified, 0 on any failure (fail-closed).
fn stark_verify_bytes(proof: &[u8], pi_bytes: &[u8]) -> u8 {
    if proof.is_empty() {
        return 0;
    }
    let proof = match proof_from_bytes(proof) {
        Ok(p) => p,
        Err(_) => return 0,
    };
    let air = match air_by_name(&proof.air_name) {
        Some(a) => a,
        None => return 0,
    };
    let pi_elems: Vec<BabyBear> = pi_bytes
        .chunks_exact(4)
        .map(|c| BabyBear::from_u64(u32::from_le_bytes([c[0], c[1], c[2], c[3]]) as u64))
        .collect();
    match verify(air, &proof, &pi_elems) {
        Ok(()) => 1,
        Err(_) => 0,
    }
}

/// VERBATIM the crypto-floor `dreggcf_stark_selftest` (lib.rs): prove the carried
/// AIR, then drive the three teeth, returning a bitmask (0x7 = all bite).
fn stark_selftest() -> u8 {
    let air = CounterSquareAir;
    let pi = [BabyBear::new(0)];
    let pi_bytes: Vec<u8> = pi.iter().flat_map(|x| x.as_u32().to_le_bytes()).collect();
    let trace: Vec<Vec<BabyBear>> = (0u32..4)
        .map(|i| vec![BabyBear::new(i), BabyBear::new(i * i)])
        .collect();

    let proof = prove(&air, &trace, &pi);
    let bytes = proof_to_bytes(&proof);

    let mut mask = 0u8;

    if stark_verify_bytes(&bytes, &pi_bytes) == 1 {
        mask |= 0x1; // ACCEPTS a sound proof + correct PI
    }

    let mut tampered = bytes.clone();
    if !tampered.is_empty() {
        let mid = tampered.len() / 2;
        tampered[mid] ^= 0xff;
    }
    if stark_verify_bytes(&tampered, &pi_bytes) == 0 {
        mask |= 0x2; // REJECTS a tampered proof
    }

    let wrong_pi = [BabyBear::new(1)];
    let wrong_pi_bytes: Vec<u8> = wrong_pi.iter().flat_map(|x| x.as_u32().to_le_bytes()).collect();
    if stark_verify_bytes(&bytes, &wrong_pi_bytes) == 0 {
        mask |= 0x4; // REJECTS the good proof under a wrong PI (boundary tooth)
    }

    mask
}

use alloc::vec;
use alloc::vec::Vec;

fn main() {
    println!("== executor-PD §2 byte-channel STARK verify — host witness ==");
    let air = CounterSquareAir;
    let pi = [BabyBear::new(0)];
    let pi_bytes: Vec<u8> = pi.iter().flat_map(|x| x.as_u32().to_le_bytes()).collect();
    let trace: Vec<Vec<BabyBear>> = (0u32..4)
        .map(|i| vec![BabyBear::new(i), BabyBear::new(i * i)])
        .collect();
    let proof = prove(&air, &trace, &pi);
    let bytes = proof_to_bytes(&proof);
    println!("  proved the carried CounterSquareAir -> proof {} bytes", bytes.len());

    let good = stark_verify_bytes(&bytes, &pi_bytes);
    println!("  verify(good proof, correct PI)   -> {} ({})", good, if good == 1 { "ACCEPT" } else { "REJECT" });

    let mut tampered = bytes.clone();
    let mid = tampered.len() / 2;
    tampered[mid] ^= 0xff;
    let bad = stark_verify_bytes(&tampered, &pi_bytes);
    println!("  verify(tampered proof)           -> {} ({})", bad, if bad == 0 { "REJECT (anti-ghost tooth)" } else { "ACCEPT — UNSOUND!" });

    let wrong_pi = [BabyBear::new(1)];
    let wrong_pi_bytes: Vec<u8> = wrong_pi.iter().flat_map(|x| x.as_u32().to_le_bytes()).collect();
    let wrong = stark_verify_bytes(&bytes, &wrong_pi_bytes);
    println!("  verify(good proof, wrong PI)     -> {} ({})", wrong, if wrong == 0 { "REJECT (boundary tooth)" } else { "ACCEPT — UNSOUND!" });

    let mask = stark_selftest();
    println!("  dreggcf_stark_selftest() bitmask -> 0x{:x} (0x7 = all teeth bite)", mask);

    assert_eq!(mask, 0x7, "the byte-channel STARK verify teeth must all bite");
    assert_eq!(good, 1);
    assert_eq!(bad, 0);
    assert_eq!(wrong, 0);
    println!("\n== ALL teeth bite — the executor PD's real STARK verify is sound ( ◕‿◕ ) ==");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn byte_channel_verify_teeth_all_bite() {
        assert_eq!(stark_selftest(), 0x7);
    }

    #[test]
    fn accepts_sound_rejects_tampered_and_wrong_pi() {
        let air = CounterSquareAir;
        let pi = [BabyBear::new(0)];
        let pi_bytes: Vec<u8> = pi.iter().flat_map(|x| x.as_u32().to_le_bytes()).collect();
        let trace: Vec<Vec<BabyBear>> = (0u32..4)
            .map(|i| vec![BabyBear::new(i), BabyBear::new(i * i)])
            .collect();
        let proof = prove(&air, &trace, &pi);
        let bytes = proof_to_bytes(&proof);

        // ACCEPT a sound proof.
        assert_eq!(stark_verify_bytes(&bytes, &pi_bytes), 1);

        // REJECT a tampered proof.
        let mut tampered = bytes.clone();
        let mid = tampered.len() / 2;
        tampered[mid] ^= 0xff;
        assert_eq!(stark_verify_bytes(&tampered, &pi_bytes), 0);

        // REJECT a wrong public input (boundary binding).
        let wrong_pi = [BabyBear::new(1)];
        let wrong_pi_bytes: Vec<u8> = wrong_pi.iter().flat_map(|x| x.as_u32().to_le_bytes()).collect();
        assert_eq!(stark_verify_bytes(&bytes, &wrong_pi_bytes), 0);
    }

    #[test]
    fn garbage_and_empty_fail_closed() {
        let pi = 0u32.to_le_bytes();
        assert_eq!(stark_verify_bytes(&[0xABu8; 64], &pi), 0);
        assert_eq!(stark_verify_bytes(&[], &pi), 0);
    }

    #[test]
    fn unknown_air_fails_closed() {
        // A well-formed proof for a carried AIR, but if we relabel the AIR name to
        // one the floor does NOT carry, verification must fail closed. We can't
        // easily relabel a serialized proof here, so assert the resolver behavior.
        assert!(air_by_name("dregg-firmament-counter-square-v1").is_some());
        assert!(air_by_name("some-unknown-air").is_none());
    }
}
