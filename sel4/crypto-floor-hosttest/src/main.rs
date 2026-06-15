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

// The REAL elliptic-curve floor (§1 ed25519, §3 Pedersen, §7 AEAD) host witness —
// includes the SAME floor modules and runs their teeth + the interop checks
// (the floor's Pedersen == cell::commit_bytes; the floor opens a cell-sealed note).
mod crypto_extras;

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

// ---- LIVE proof-carrying-turn ADMISSION (the §2.1 wiring from lib.rs) ----------
//
// The selftest above MINTS a proof and verifies it in one breath. A LIVE turn is
// different: the producer ships the turn's proof bytes + PI OUT OF BAND in a wire
// envelope, the executor PD DECODES it and ADMITS the turn iff the carried proof
// verifies. The functions below mirror `dreggcf_admit_proof_carrying_turn` +
// `dreggcf_admit_selftest` from `crypto-floor/src/lib.rs` so the host runs the
// IDENTICAL admission path on a box with no user-mode qemu-aarch64.

/// The PCT1 proof-carrying-turn magic (matches lib.rs).
const PCT_MAGIC: &[u8; 4] = b"PCT1";

/// ENCODE a PCT1 turn wire from carried proof bytes + PI bytes (the PRODUCER side).
fn pct_encode(turn_id: u64, proof_bytes: &[u8], pi_bytes: &[u8]) -> Vec<u8> {
    let mut w = Vec::with_capacity(16 + proof_bytes.len() + 4 + pi_bytes.len());
    w.extend_from_slice(PCT_MAGIC);
    w.extend_from_slice(&turn_id.to_le_bytes());
    w.extend_from_slice(&(proof_bytes.len() as u32).to_le_bytes());
    w.extend_from_slice(proof_bytes);
    w.extend_from_slice(&(pi_bytes.len() as u32).to_le_bytes());
    w.extend_from_slice(pi_bytes);
    w
}

/// DECODE a PCT1 turn wire (the PD side) — VERBATIM the lib.rs `pct_decode`:
/// returns `(turn_id, proof_bytes, pi_bytes)` or `None` on any framing error.
fn pct_decode(wire: &[u8]) -> Option<(u64, &[u8], &[u8])> {
    if wire.len() < 16 || &wire[0..4] != PCT_MAGIC {
        return None;
    }
    let turn_id = u64::from_le_bytes([
        wire[4], wire[5], wire[6], wire[7], wire[8], wire[9], wire[10], wire[11],
    ]);
    let proof_len = u32::from_le_bytes([wire[12], wire[13], wire[14], wire[15]]) as usize;
    let proof_start: usize = 16;
    let proof_end = proof_start.checked_add(proof_len)?;
    if proof_end.checked_add(4)? > wire.len() {
        return None;
    }
    let proof_bytes = &wire[proof_start..proof_end];
    let pi_len = u32::from_le_bytes([
        wire[proof_end],
        wire[proof_end + 1],
        wire[proof_end + 2],
        wire[proof_end + 3],
    ]) as usize;
    let pi_start = proof_end + 4;
    let pi_end = pi_start.checked_add(pi_len)?;
    if pi_end > wire.len() {
        return None;
    }
    Some((turn_id, proof_bytes, &wire[pi_start..pi_end]))
}

/// ADMIT a LIVE proof-carrying turn — VERBATIM the lib.rs
/// `dreggcf_admit_proof_carrying_turn`: decode the wire, route the CARRIED proof +
/// PI through `stark_verify_bytes` (the one carried verifier), return the verdict
/// (1 = ADMIT, 0 = REFUSE, fail-closed). The verify input is the bytes the wire
/// carried — the live-turn path, not a re-mint.
fn admit_proof_carrying_turn(wire: &[u8]) -> u8 {
    if wire.is_empty() {
        return 0;
    }
    let (_turn_id, proof_bytes, pi_bytes) = match pct_decode(wire) {
        Some(parts) => parts,
        None => return 0,
    };
    stark_verify_bytes(proof_bytes, pi_bytes)
}

/// VERBATIM the crypto-floor `dreggcf_admit_selftest` (lib.rs): mint a proof on the
/// PRODUCER side, ENCODE three turn wires (genuine / tampered-proof / wrong-PI),
/// drive the ADMISSION path, return a bitmask (0x7 = ADMIT genuine, REFUSE both).
fn admit_selftest() -> u8 {
    let air = CounterSquareAir;
    let pi = [BabyBear::new(0)];
    let pi_bytes: Vec<u8> = pi.iter().flat_map(|x| x.as_u32().to_le_bytes()).collect();
    let trace: Vec<Vec<BabyBear>> = (0u32..4)
        .map(|i| vec![BabyBear::new(i), BabyBear::new(i * i)])
        .collect();
    let proof = prove(&air, &trace, &pi);
    let proof_bytes = proof_to_bytes(&proof);

    let mut mask = 0u8;

    // bit 0 — a GENUINE turn ADMITS.
    let genuine = pct_encode(0x7777, &proof_bytes, &pi_bytes);
    if admit_proof_carrying_turn(&genuine) == 1 {
        mask |= 0x1;
    }

    // bit 1 — a TAMPERED-proof turn REFUSES.
    let mut tampered_proof = proof_bytes.clone();
    if !tampered_proof.is_empty() {
        let mid = tampered_proof.len() / 2;
        tampered_proof[mid] ^= 0xff;
    }
    let tampered_turn = pct_encode(0x7777, &tampered_proof, &pi_bytes);
    if admit_proof_carrying_turn(&tampered_turn) == 0 {
        mask |= 0x2;
    }

    // bit 2 — a WRONG-PI turn REFUSES (the boundary tooth on the admission path).
    let wrong_pi = [BabyBear::new(1)];
    let wrong_pi_bytes: Vec<u8> = wrong_pi.iter().flat_map(|x| x.as_u32().to_le_bytes()).collect();
    let wrong_turn = pct_encode(0x7777, &proof_bytes, &wrong_pi_bytes);
    if admit_proof_carrying_turn(&wrong_turn) == 0 {
        mask |= 0x4;
    }

    mask
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
    println!("\n== byte channel: ALL teeth bite — the real STARK verify is sound ==");

    // ---- the LIVE proof-carrying-turn ADMISSION path (the §4 next step) --------
    // The producer ships a turn's proof bytes + PI in a PCT1 wire envelope; the
    // executor PD DECODES it and ADMITS the turn iff the carried proof verifies.
    // The proof bytes reach the verifier via the WIRE DECODE — not a re-mint.
    println!("\n== LIVE proof-carrying-turn ADMISSION (proof bytes routed from the turn wire) ==");
    let genuine = pct_encode(0x7777, &bytes, &pi_bytes);
    println!("  producer shipped a {}-byte turn wire (PCT1: turn_id + proof + PI)", genuine.len());
    let a_genuine = admit_proof_carrying_turn(&genuine);
    println!(
        "  admit(genuine turn)            -> {} ({})",
        a_genuine,
        if a_genuine == 1 { "ADMIT" } else { "REFUSE" }
    );

    let tampered_turn = pct_encode(0x7777, &tampered, &pi_bytes);
    let a_tampered = admit_proof_carrying_turn(&tampered_turn);
    println!(
        "  admit(turn w/ tampered proof)  -> {} ({})",
        a_tampered,
        if a_tampered == 0 { "REFUSE (anti-ghost tooth on the LIVE path)" } else { "ADMIT — UNSOUND!" }
    );

    let wrong_turn = pct_encode(0x7777, &bytes, &wrong_pi_bytes);
    let a_wrong = admit_proof_carrying_turn(&wrong_turn);
    println!(
        "  admit(turn w/ wrong PI)        -> {} ({})",
        a_wrong,
        if a_wrong == 0 { "REFUSE (boundary tooth on the LIVE path)" } else { "ADMIT — UNSOUND!" }
    );

    // a malformed turn envelope (bad magic) must REFUSE at decode — never admit.
    let malformed = vec![0u8; 32];
    let a_malformed = admit_proof_carrying_turn(&malformed);
    println!(
        "  admit(malformed turn wire)     -> {} ({})",
        a_malformed,
        if a_malformed == 0 { "REFUSE (fail-closed decode)" } else { "ADMIT — UNSOUND!" }
    );

    let admit_mask = admit_selftest();
    println!(
        "  dreggcf_admit_selftest() bitmask -> 0x{:x} (0x7 = ADMIT genuine, REFUSE tampered+wrong-PI)",
        admit_mask
    );

    assert_eq!(a_genuine, 1, "the genuine turn must ADMIT");
    assert_eq!(a_tampered, 0, "the tampered-proof turn must REFUSE");
    assert_eq!(a_wrong, 0, "the wrong-PI turn must REFUSE");
    assert_eq!(a_malformed, 0, "the malformed turn wire must REFUSE");
    assert_eq!(admit_mask, 0x7, "the LIVE-turn admission teeth must all bite");
    println!(
        "\n== LIVE-turn admission: a genuine turn is ADMITTED, a tampered/wrong-PI turn REFUSED ==\
         \n== the executor PD's proof-carrying turn routes its proof to the real verifier ( ◕‿◕ ) ==",
    );

    // ---- the REAL elliptic-curve floor: §1 ed25519, §3 Pedersen, §7 AEAD -------
    let crypto_ok = crypto_extras::run_report();
    assert!(crypto_ok, "the elliptic-curve crypto floor teeth must all bite");
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

    #[test]
    fn live_turn_admission_teeth_all_bite() {
        // The LIVE proof-carrying-turn admission path: ADMIT a genuine turn, REFUSE
        // a tampered-proof turn, REFUSE a wrong-PI turn — the anti-ghost teeth on
        // the ADMISSION entry (proof bytes routed from the turn wire).
        assert_eq!(admit_selftest(), 0x7);
    }

    #[test]
    fn live_turn_admits_genuine_refuses_tampered_and_wrong_pi() {
        let air = CounterSquareAir;
        let pi = [BabyBear::new(0)];
        let pi_bytes: Vec<u8> = pi.iter().flat_map(|x| x.as_u32().to_le_bytes()).collect();
        let trace: Vec<Vec<BabyBear>> = (0u32..4)
            .map(|i| vec![BabyBear::new(i), BabyBear::new(i * i)])
            .collect();
        let proof = prove(&air, &trace, &pi);
        let bytes = proof_to_bytes(&proof);

        // GENUINE turn -> ADMIT.
        let genuine = pct_encode(0x7777, &bytes, &pi_bytes);
        assert_eq!(admit_proof_carrying_turn(&genuine), 1, "genuine turn admits");

        // turn carrying a TAMPERED proof -> REFUSE.
        let mut tampered = bytes.clone();
        let mid = tampered.len() / 2;
        tampered[mid] ^= 0xff;
        let tampered_turn = pct_encode(0x7777, &tampered, &pi_bytes);
        assert_eq!(admit_proof_carrying_turn(&tampered_turn), 0, "tampered turn refuses");

        // turn carrying the good proof but a WRONG PI -> REFUSE (boundary tooth).
        let wrong_pi = [BabyBear::new(1)];
        let wrong_pi_bytes: Vec<u8> =
            wrong_pi.iter().flat_map(|x| x.as_u32().to_le_bytes()).collect();
        let wrong_turn = pct_encode(0x7777, &bytes, &wrong_pi_bytes);
        assert_eq!(admit_proof_carrying_turn(&wrong_turn), 0, "wrong-PI turn refuses");
    }

    #[test]
    fn live_turn_malformed_wire_fails_closed() {
        // Empty, bad-magic, and overrun-length turn envelopes must all REFUSE at
        // decode — never admit, never panic.
        assert_eq!(admit_proof_carrying_turn(&[]), 0, "empty turn refuses");
        assert_eq!(admit_proof_carrying_turn(&[0u8; 32]), 0, "bad-magic turn refuses");
        let mut overrun = Vec::new();
        overrun.extend_from_slice(PCT_MAGIC);
        overrun.extend_from_slice(&0u64.to_le_bytes());
        overrun.extend_from_slice(&0xFFFF_FFFFu32.to_le_bytes()); // proof_len >> buffer
        assert_eq!(admit_proof_carrying_turn(&overrun), 0, "overrun-len turn refuses");
    }

    #[test]
    fn live_turn_decode_binds_carried_proof() {
        // The decode binds back the exact carried proof + PI + turn_id, and the
        // admission verdict equals the bare byte-channel verdict (framing adds no
        // verdict change — the carried proof is load-bearing, not re-minted).
        let air = CounterSquareAir;
        let pi = [BabyBear::new(0)];
        let pi_bytes: Vec<u8> = pi.iter().flat_map(|x| x.as_u32().to_le_bytes()).collect();
        let trace: Vec<Vec<BabyBear>> = (0u32..4)
            .map(|i| vec![BabyBear::new(i), BabyBear::new(i * i)])
            .collect();
        let proof = prove(&air, &trace, &pi);
        let bytes = proof_to_bytes(&proof);

        let wire = pct_encode(42, &bytes, &pi_bytes);
        let (tid, dp, dpi) = pct_decode(&wire).expect("well-formed wire decodes");
        assert_eq!(tid, 42);
        assert_eq!(dp, &bytes[..]);
        assert_eq!(dpi, &pi_bytes[..]);
        assert_eq!(
            admit_proof_carrying_turn(&wire),
            stark_verify_bytes(&bytes, &pi_bytes),
            "admission verdict == byte-channel verdict"
        );
    }
}
