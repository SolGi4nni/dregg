//! # `cap_reshape_descriptor` — the OPENABLE `capability_root` descriptor loader (the ARGUS linchpin).
//!
//! The cap-reshape crown (#103): the Lean-verified `EffectVmDescriptor` that checks, IN-CIRCUIT, the
//! two capability-security openings a light client must trust WITHOUT re-running history:
//!
//!   * **non-amplification** — a granted cap is `≤` a held cap (the in-row submask gates
//!     `granted_bit ≤ held_bit` per bit, over the opened held leaf);
//!   * **production-authority** — a mint is gated on OPENING the issuer cap from the producer's held-set
//!     root (the held `target` binds the minted-asset PI + the control/mint bit is set).
//!
//! ## Provenance (anti-drift, the LAW#1 way)
//!
//! `dregg-effectvm-capreshape-v1.json` is the **byte-exact** output of the verified Lean emit
//! `Dregg2.Circuit.Emit.EffectVmEmitCapReshape.capReshapeJson` (`emitVmJson capReshapeVmDescriptor`).
//! The Rust prover INTERPRETS this descriptor via `parse_vm_descriptor` (it AUTHORS NO CONSTRAINT — the
//! constraints are emitted from the proved Lean module). The `CAPRESHAPE_V1_FP` SHA-256 pins the bytes;
//! the test below re-hashes + re-parses, so any Lean→Rust drift fails CI.
//!
//! This is a STANDALONE loader (its own module + test), NOT registered in the locked
//! `effect_vm_descriptors` registry (whose count assertions would otherwise break). The descriptor is
//! the openable-`capability_root` check the sdk authority-binding (the Phase-D payoff) routes to; this
//! module proves it parses + carries the anti-amplify + anti-unauthorized-mint teeth.
//!
//! ## The carried hypothesis (honest seam)
//!
//! The descriptor checks the SUBMASK shadow of non-amplification (`granted_bit ≤ held_bit`, bit by bit)
//! and binds the rights digest into the opened held leaf; the bridge to the genuine `Finset Auth`
//! lattice is the Lean `entryEncodes` correspondence (`EffectVmEmitCapReshape` §2′). The turn-level
//! binding of the opened `cap_root` to the producer's authenticated cell-root is the sdk
//! authority-binding (`full_turn_proof.rs`), cited not duplicated here.

use crate::lean_descriptor_air::{EffectVmDescriptor, LeanExpr, VmConstraint, parse_vm_descriptor};

/// The byte-exact verified-Lean JSON for the openable-`capability_root` descriptor.
pub const CAPRESHAPE_V1_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-capreshape-v1.json");

/// The SHA-256 of the committed bytes (the anti-drift fingerprint).
pub const CAPRESHAPE_V1_FP: &str =
    "69a443b58a65e9f47e37d856ceb4a0a269c9bfb00992441df55482e881d88e56";

/// The descriptor name (the canonical wire identity).
pub const CAPRESHAPE_V1_NAME: &str = "dregg-effectvm-capreshape-v1";

/// The `Auth` rights-mask bit width (8 atoms ⇒ 8 bits): mirrors Lean `EffectVmEmitCapReshape.MASK_BITS`.
pub const MASK_BITS: usize = 8;

/// The held-mask bit columns (aux block, `[104, 112)` on the 186-col layout). Mirrors Lean
/// `col.heldBit i = 104 + i`.
pub const HELD_BIT_BASE: usize = 104;

/// The granted-mask bit columns (`[112, 120)`). Mirrors Lean `col.grantedBit i = 112 + i`.
pub const GRANTED_BIT_BASE: usize = 112;

/// The control-bit position (`authBit control = 64 = 2^6`). Mirrors Lean `CONTROL_BIT_POS`.
pub const CONTROL_BIT_POS: usize = 6;

/// Parse the openable-`capability_root` descriptor through the running EffectVM interpreter.
/// (The same `parse_vm_descriptor` the cutover dispatcher uses; the descriptor drives the verified
/// circuit for the cap-reshape row.)
pub fn cap_reshape_descriptor() -> Result<EffectVmDescriptor, String> {
    parse_vm_descriptor(CAPRESHAPE_V1_JSON)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Self-contained SHA-256 (FIPS 180-4), no external dep (mirrors the registry test's
    /// `sha256_hex`), so the drift fingerprint is reproducible from this file alone.
    fn sha256_hex(data: &[u8]) -> String {
        const K: [u32; 64] = [
            0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
            0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
            0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
            0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
            0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
            0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
            0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
            0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
            0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
            0xc67178f2,
        ];
        let mut h: [u32; 8] = [
            0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
            0x5be0cd19,
        ];
        let mut msg = data.to_vec();
        let bitlen = (data.len() as u64) * 8;
        msg.push(0x80);
        while msg.len() % 64 != 56 {
            msg.push(0);
        }
        msg.extend_from_slice(&bitlen.to_be_bytes());
        for chunk in msg.chunks(64) {
            let mut w = [0u32; 64];
            for i in 0..16 {
                w[i] = u32::from_be_bytes([
                    chunk[4 * i],
                    chunk[4 * i + 1],
                    chunk[4 * i + 2],
                    chunk[4 * i + 3],
                ]);
            }
            for i in 16..64 {
                let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
                let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
                w[i] = w[i - 16]
                    .wrapping_add(s0)
                    .wrapping_add(w[i - 7])
                    .wrapping_add(s1);
            }
            let (mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh) =
                (h[0], h[1], h[2], h[3], h[4], h[5], h[6], h[7]);
            for i in 0..64 {
                let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
                let ch = (e & f) ^ ((!e) & g);
                let t1 = hh
                    .wrapping_add(s1)
                    .wrapping_add(ch)
                    .wrapping_add(K[i])
                    .wrapping_add(w[i]);
                let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
                let maj = (a & b) ^ (a & c) ^ (b & c);
                let t2 = s0.wrapping_add(maj);
                hh = g;
                g = f;
                f = e;
                e = d.wrapping_add(t1);
                d = c;
                c = b;
                b = a;
                a = t1.wrapping_add(t2);
            }
            h[0] = h[0].wrapping_add(a);
            h[1] = h[1].wrapping_add(b);
            h[2] = h[2].wrapping_add(c);
            h[3] = h[3].wrapping_add(d);
            h[4] = h[4].wrapping_add(e);
            h[5] = h[5].wrapping_add(f);
            h[6] = h[6].wrapping_add(g);
            h[7] = h[7].wrapping_add(hh);
        }
        let mut out = String::with_capacity(64);
        for word in h {
            for byte in word.to_be_bytes() {
                out.push_str(&format!("{byte:02x}"));
            }
        }
        out
    }

    /// The committed JSON re-hashes to its fingerprint AND re-parses through the interpreter — the
    /// Lean→Rust anti-drift tooth (a re-emit that changes a gate, or a stale committed JSON, fails).
    #[test]
    fn capreshape_parses_and_matches_fingerprint() {
        let fp = sha256_hex(CAPRESHAPE_V1_JSON.as_bytes());
        assert_eq!(
            fp, CAPRESHAPE_V1_FP,
            "cap-reshape descriptor fingerprint drift: re-run EmitAllJson + update CAPRESHAPE_V1_FP"
        );

        let d =
            cap_reshape_descriptor().expect("cap-reshape descriptor must parse via interpreter");
        assert_eq!(d.name, CAPRESHAPE_V1_NAME, "parsed name != wire identity");
        assert_eq!(
            d.trace_width, 186,
            "cap-reshape shares the 186-col EffectVM base trace"
        );
        assert_eq!(d.public_input_count, 1, "the minted-asset PI");
        // 8 held-bool + 8 granted-bool + 8 submask + 2 recon + 1 PI binding + 1 control gate = 28.
        assert_eq!(d.constraints.len(), 3 * MASK_BITS + 2 + 2);
        // one held-leaf recompute site (`hash[slot, target, held_mask, 0]`, arity 4).
        assert_eq!(d.hash_sites.len(), 1);
        assert_eq!(d.hash_sites[0].inputs.len(), 4);
        assert_eq!(d.hash_sites[0].arity, 4);
    }

    /// Helper: does the gate body `g·(1 − h)` (a `mul` of `var(g)` with `add(const 1, mul(const -1,
    /// var(h)))`) appear in the constraint list for the given (granted, held) bit columns? This is the
    /// per-bit NON-AMP submask tooth; finding it for every bit confirms `granted ⊑ held` is enforced.
    fn has_submask_gate(d: &EffectVmDescriptor, granted_col: usize, held_col: usize) -> bool {
        d.constraints.iter().any(|c| match c {
            VmConstraint::Gate(LeanExpr::Mul(l, r)) => {
                let lhs_is_granted = matches!(**l, LeanExpr::Var(v) if v == granted_col);
                // r = add(const 1, mul(const -1, var held))
                let rhs_is_one_minus_held = match &**r {
                    LeanExpr::Add(a, b) => {
                        let a_is_one = matches!(**a, LeanExpr::Const(1));
                        let b_is_neg_held = matches!(&**b, LeanExpr::Mul(x, y)
                            if matches!(**x, LeanExpr::Const(-1))
                                && matches!(**y, LeanExpr::Var(v) if v == held_col));
                        a_is_one && b_is_neg_held
                    }
                    _ => false,
                };
                lhs_is_granted && rhs_is_one_minus_held
            }
            _ => false,
        })
    }

    /// THE ANTI-AMPLIFY TOOTH is present in the circuit: for EVERY mask bit, the descriptor carries the
    /// submask gate `granted_bit·(1 − held_bit) = 0` (a granted bit may be set only where the held bit
    /// is). So the interpreted circuit ENFORCES `granted ⊑ held` bitwise — non-amplification in-circuit,
    /// not an executor-trusted side-check.
    #[test]
    fn capreshape_carries_anti_amplify_teeth() {
        let d = cap_reshape_descriptor().unwrap();
        for i in 0..MASK_BITS {
            assert!(
                has_submask_gate(&d, GRANTED_BIT_BASE + i, HELD_BIT_BASE + i),
                "non-amp submask gate missing for bit {i} (granted {} ≤ held {})",
                GRANTED_BIT_BASE + i,
                HELD_BIT_BASE + i
            );
        }
    }

    /// THE ANTI-UNAUTHORIZED-MINT TOOTH is present: the descriptor carries (a) a first-row PI binding
    /// pinning the held cap's `target` param (col 71) to the minted-asset PI (index 0) — the opened
    /// issuer cap must target the asset — and (b) the control-bit gate `held_bit[6] − 1 = 0` forcing the
    /// mint right. So a mint WITHOUT the held issuer cap is rejected in-circuit.
    #[test]
    fn capreshape_carries_production_authority_teeth() {
        let d = cap_reshape_descriptor().unwrap();
        // (a) the asset-binding PI: target param (col 71) == PI[0] on the first row.
        let has_asset_pi = d.constraints.iter().any(|c| {
            matches!(c, VmConstraint::PiBinding { col, pi_index, .. } if *col == 71 && *pi_index == 0)
        });
        assert!(
            has_asset_pi,
            "production-authority asset PI binding missing"
        );
        // (b) the control-bit gate: add(var held_bit[6], mul(const -1, const 1)) = 0, i.e. h6 = 1.
        let has_control_gate = d.constraints.iter().any(|c| match c {
            VmConstraint::Gate(LeanExpr::Add(l, r)) => {
                matches!(**l, LeanExpr::Var(v) if v == HELD_BIT_BASE + CONTROL_BIT_POS)
                    && matches!(&**r, LeanExpr::Mul(x, y)
                        if matches!(**x, LeanExpr::Const(-1)) && matches!(**y, LeanExpr::Const(1)))
            }
            _ => false,
        });
        assert!(
            has_control_gate,
            "production-authority control-bit gate (held_bit[6] = 1) missing"
        );
    }
}
