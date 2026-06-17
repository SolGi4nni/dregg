//! # `cap_delegation_nonamp_descriptor` — the GENUINE-NON-AMP cap-graph descriptor loader.
//!
//! The ARGUS linchpin on the DELEGATION family (`delegate`, `delegateAtten`, `attenuate`, `introduce`,
//! `revoke`, `refresh`). One Lean-verified `EffectVmDescriptor` that, on a cap-graph row, enforces BOTH:
//!
//!   * **genuine cap-root recompute** — `new_cap_root = hash[edge_leaf, old_cap_root]` with
//!     `edge_leaf = hash[holder, target, rights, op]` (the §G prepend-accumulator advance, op-tagged), so
//!     the post `cap_root` is a FORCED function of the bound cap-edge mutation, not an opaque digest
//!     parameter — and the recomputed root is absorbed into `state_commit` (tamper ⇒ UNSAT);
//!   * **in-circuit non-amplification** — the per-bit submask gates `granted_bit ≤ held_bit` over the
//!     SAME `rights` felt the recompute hashes into the edge leaf, so the granted edge's conferred rights
//!     are `⊑` the delegator's held mask. An over-grant (a granted bit set where the held bit is clear)
//!     fails the submask gate. `granted ⊑ held` is now IN-CIRCUIT on the whole cap-graph family.
//!
//! The two legs INTERLOCK on one `rights` felt: tamper it to dodge the submask gate and the recomputed
//! `cap_root` moves ⇒ `state_commit` moves ⇒ UNSAT (the §G `capRoot_binds_edge` anti-ghost). This is the
//! delegation-family counterpart of the mint-flavour `cap_reshape_descriptor` (`granted ⊑ held` PLUS
//! production-authority); here it is `granted ⊑ held` PLUS the cap-root recompute (no production gate —
//! a delegation is not a mint).
//!
//! ## Provenance (anti-drift, the LAW#1 way)
//!
//! `dregg-effectvm-attenuateA-v1-genuine-nonamp.json` is the **byte-exact** output of the verified Lean
//! emit `Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.attenuateVmDescriptorGenuineNonAmp` (via
//! `emitVmJson`, the `EmitAllJson` registry line). The Rust prover INTERPRETS this descriptor via
//! `parse_vm_descriptor` (it AUTHORS NO CONSTRAINT — the gates are emitted from the proved Lean module:
//! `capDeleg_nonAmp_in_circuit` / `capDeleg_rejects_amplify` are the in-circuit teeth, both polarities).
//! The `GENUINE_NONAMP_FP` SHA-256 pins the bytes; the test below re-hashes + re-parses, so any Lean→Rust
//! drift fails CI. ONE descriptor object backs all six effects (the `op` tag distinguishes the mutation,
//! so the JSON is shared — selector→JSON fan-out, like the v1 cap-graph face).
//!
//! This is a STANDALONE loader (its own module + test), NOT registered in the locked
//! `effect_vm_descriptors` registry (whose count assertions would otherwise break) — exactly as
//! `cap_reshape_descriptor` is standalone. The sdk authority-binding routes cap-graph rows to it by name.

use crate::lean_descriptor_air::{EffectVmDescriptor, parse_vm_descriptor};

/// The byte-exact verified-Lean JSON for the genuine-non-amp cap-graph descriptor.
pub const GENUINE_NONAMP_JSON: &str =
    include_str!("../descriptors/dregg-effectvm-attenuateA-v1-genuine-nonamp.json");

/// The SHA-256 of the committed bytes (the anti-drift fingerprint).
pub const GENUINE_NONAMP_FP: &str =
    "61b1cabb55a5f396f91dbca604c9a59a1e5d9bdca4d76bfd578bf8350e305cf4";

/// The descriptor name (the canonical wire identity — shared across the six cap-graph effects).
pub const GENUINE_NONAMP_NAME: &str = "dregg-effectvm-attenuateA-v1-genuine-nonamp";

/// The `Auth` rights-mask bit width (8 atoms ⇒ 8 bits): mirrors Lean `EffectVmEmitCapReshape.MASK_BITS`.
pub const MASK_BITS: usize = 8;

/// The DELEGATION held-mask bit columns. Mirrors Lean `dcol.heldBit i = 120 + i`
/// (`col.GRANTED_BIT_BASE + MASK_BITS = 112 + 8 = 120`), past the mint-flavour bit block.
pub const DELEG_HELD_BIT_BASE: usize = 120;

/// The DELEGATION granted-mask bit columns. Mirrors Lean `dcol.grantedBit i = 128 + i`
/// (`col.GRANTED_BIT_BASE + 2·MASK_BITS = 112 + 16 = 128`). These reconstruct `cp.RIGHTS` (param 4,
/// col 72) — the SAME `rights` felt the cap-root edge-leaf site hashes.
pub const DELEG_GRANTED_BIT_BASE: usize = 128;

/// Parse the genuine-non-amp cap-graph descriptor through the running EffectVM interpreter.
/// (The same `parse_vm_descriptor` the cutover dispatcher uses; the descriptor drives the verified
/// circuit for the delegation-family row.)
pub fn cap_delegation_nonamp_descriptor() -> Result<EffectVmDescriptor, String> {
    parse_vm_descriptor(GENUINE_NONAMP_JSON)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lean_descriptor_air::{LeanExpr, VmConstraint};

    /// Self-contained SHA-256 (FIPS 180-4), no external dep (mirrors `cap_reshape_descriptor`'s
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
    fn genuine_nonamp_parses_and_matches_fingerprint() {
        let fp = sha256_hex(GENUINE_NONAMP_JSON.as_bytes());
        assert_eq!(
            fp, GENUINE_NONAMP_FP,
            "genuine-non-amp descriptor fingerprint drift: run scripts/emit-descriptors.sh and commit"
        );

        let d = cap_delegation_nonamp_descriptor()
            .expect("genuine-non-amp descriptor must parse via interpreter");
        assert_eq!(d.name, GENUINE_NONAMP_NAME, "parsed name != wire identity");
        assert_eq!(
            d.trace_width, 187,
            "the genuine-non-amp cap-graph row shares the 187-col EffectVM base trace (P0-2 record-digest)"
        );
        // 30 genuine (12 frame freeze + 14 transition + 4 boundary) + 26 non-amp
        // (8 held-bool + 8 granted-bool + 8 submask + 2 recon) = 56.
        assert_eq!(d.constraints.len(), (12 + 14 + 4) + (3 * MASK_BITS + 2));
        // 6 hash sites: 2 cap-root recompute (edge-leaf + advance) + 4 GROUP-4 state-commitment.
        assert_eq!(d.hash_sites.len(), 6);
    }

    /// Helper: does the per-bit NON-AMP submask gate body `g·(1 − h)` (a `mul` of `var(g)` with
    /// `add(const 1, mul(const -1, var(h)))`) appear in the constraint list for the given (granted,
    /// held) bit columns? Finding it for every bit confirms `granted ⊑ held` is enforced in-circuit.
    fn has_submask_gate(d: &EffectVmDescriptor, granted_col: usize, held_col: usize) -> bool {
        d.constraints.iter().any(|c| match c {
            VmConstraint::Gate(LeanExpr::Mul(l, r)) => {
                let lhs_is_granted = matches!(**l, LeanExpr::Var(v) if v == granted_col);
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

    /// THE ANTI-AMPLIFY TOOTH is present on the cap-graph family: for EVERY mask bit, the descriptor
    /// carries the submask gate `granted_bit·(1 − held_bit) = 0` over the DELEGATION bit columns
    /// (held `[120,128)`, granted `[128,136)`). So the interpreted circuit ENFORCES `granted ⊑ held`
    /// bitwise — in-circuit non-amplification on every delegation effect, not an executor side-check.
    #[test]
    fn genuine_nonamp_carries_anti_amplify_teeth() {
        let d = cap_delegation_nonamp_descriptor().unwrap();
        for i in 0..MASK_BITS {
            assert!(
                has_submask_gate(&d, DELEG_GRANTED_BIT_BASE + i, DELEG_HELD_BIT_BASE + i),
                "non-amp submask gate missing for bit {i} (granted {} ≤ held {})",
                DELEG_GRANTED_BIT_BASE + i,
                DELEG_HELD_BIT_BASE + i
            );
        }
    }

    /// THE GENUINE CAP-ROOT RECOMPUTE is present (NOT an opaque digest): the descriptor carries the two
    /// recompute hash-sites — the edge leaf `hash[holder, target, rights, op]` (arity 4) into the leaf
    /// carrier (col 102) and the advance `hash[edge_leaf, old_cap_root]` (arity 2) into the cap-root
    /// after-column (col 87). So the post `cap_root` is FORCED by the bound edge mutation, interlocking
    /// with the non-amp gate on the same `rights` felt (col 72).
    #[test]
    fn genuine_nonamp_carries_caproot_recompute() {
        let d = cap_delegation_nonamp_descriptor().unwrap();
        // the edge-leaf recompute site: arity 4, digest into col 102 (CAP_EDGE_LEAF), reading params
        // holder/target/rights/op (cols 70/71/72/73).
        let leaf_site = d
            .hash_sites
            .iter()
            .find(|s| s.digest_col == 102)
            .expect("cap-edge-leaf recompute site (digest col 102) missing");
        assert_eq!(leaf_site.arity, 4, "edge leaf is hash[holder,target,rights,op]");
        assert_eq!(leaf_site.inputs.len(), 4);
        // the advance site: arity 2, digest into col 87 (saCol CAP_ROOT), reading the leaf (102) + the
        // old cap-root column (65 = sbCol CAP_ROOT).
        let adv_site = d
            .hash_sites
            .iter()
            .find(|s| s.digest_col == 87)
            .expect("cap-root advance site (digest col 87 = saCol CAP_ROOT) missing");
        assert_eq!(adv_site.arity, 2, "advance is hash[edge_leaf, old_cap_root]");
        assert_eq!(adv_site.inputs.len(), 2);
    }
}
