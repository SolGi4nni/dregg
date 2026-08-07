//! Bridge action binding AIR (sibling to `note_spending_witness`).
//!
//! # Why a sibling AIR?
//!
//! `note_spending_witness` (and its DSL twin `dsl::note_spending`) already prove
//! knowledge of a spending key + Merkle membership of the note, and pin
//! `nullifier`, `merkle_root`, `value`, `asset_type`, `destination_federation`
//! as public inputs. **However**, each of those PIs is a **single** BabyBear
//! field element (~31 bits). To squeeze a 32-byte hash into one felt the
//! prover/verifier compresses via `bytes_to_babybear` (Poseidon2 hash of 8
//! limbs to one element). That compression is one-way, so it works for
//! soundness, but it has two consequences this AIR fixes:
//!
//! 1. **The full 32 bytes never appear directly in any PI vector**, only their
//!    Poseidon2 digest. A verifier that wants to attribute a bridge mint to a
//!    specific 32-byte recipient commitment (the "who got minted to") cannot
//!    cryptographically check against the recipient bytes — it can only check
//!    against the digest. For a bridge that mints a *new note* on the
//!    destination, the destination wants the proof to say "I am minting to
//!    commitment 0xABCD…", not "I am minting to something that hashes to a
//!    BabyBear felt 0x12345678".
//!
//! 2. **The amount is currently truncated to 30 bits** (`v & ((1<<30)-1)`,
//!    see `turn/src/executor.rs` BridgeMint closure, CAVEAT-LAYER-COVERAGE.md
//!    §6.5, and `circuit/src/effect_vm.rs::BridgeMint::value_lo`). Above
//!    2^30 (~10⁹) the high bits are unrecoverable from the proof — a prover
//!    above that ceiling can claim any high-bit collision. The substrate
//!    AIR is out of this lane's write surface, but the bridge-side proof
//!    can and must carry the full 64 bits.
//!
//! # ⚑ THE FLAG DAY THIS FILE IS (2026-08-06): two felts cannot carry a u64
//!
//! Until this commit the amount rode **two 32-bit limbs**, `BabyBear::new(lo)` /
//! `BabyBear::new(hi)`. `BabyBear::new` REDUCES, `p = 2013265921 < 2^32`, and so
//! `lo = 0` and `lo = p` were the same cell: `encode_amount(0) ==
//! encode_amount(2_013_265_921)`. A "full-fidelity binding" that collides on the
//! amount is not full fidelity, and the collision is **one addition away**, not a
//! search.
//!
//! ⚑ **No coefficient or reduction change could have fixed it, and that is a
//! theorem, not a judgement.** Two felts carry `p² = 4_053_239_737_456_637_441`
//! distinct pairs and a u64 has `2^64 = 18_446_744_073_709_551_616` values, so by
//! pigeonhole EVERY 2-felt encoding of a u64 collides — on average 4.55 amounts per
//! pair. `two_felts_cannot_carry_a_u64` is that count, asserted. The only repair is
//! to widen, and the width the tree already uses for exactly this fact is
//! **`AMOUNT_LIMBS = 4` at `AMOUNT_LIMB_BITS = 16`**: `4·16 = 64` exactly, every
//! limb `< 2^16 ≪ p` so `BabyBear::new` never reduces, and the encoding is
//! injective with a total inverse (`decode_amount`). This is the same repair
//! `effect_action_air.rs` took in the same flag day, and the same width
//! `EffectVmEmitBurn` / `CrossCellConservation` / `vault_weld.rs::borrow_compare`
//! already run their borrow chains on.
//!
//! ⚠ **What re-emits / refuses to load.** `BRIDGE_ACTION_WIDTH` 26 → 28, so
//! `bridge-action-leaf::bridge_action_air_v1` grows to 28 PI slots and 56
//! constraints. The Lean author (`Dregg2/Circuit/Emit/BridgeActionEmit.lean`) and
//! its checked-in artifact `circuit/descriptors/by-name/bridge-action.json` are
//! re-emitted; `scripts/descriptor-anchor-inertness-baseline.txt`'s row moves
//! 26 → 28. Every previously-minted `PortableActionBinding` fails
//! `verify_vm_descriptor2` on the PI count — it cannot be reinterpreted, only
//! rejected. Nothing on a deployed path produced one: the executor's
//! `verify_bridge_action` was deleted, and the only `src/` consumer chain
//! (`bridge::midnight_verified` → `bridge::midnight_gateway`) has no caller.
//!
//! # What this AIR binds
//!
//! Public inputs (all bytes / amount carried at full fidelity):
//!
//! ```text
//! pi[ 0.. 8) = nullifier_limbs[8]              (8 × 4-byte BabyBear limbs)
//! pi[ 8..16) = recipient_limbs[8]              (8 × 4-byte BabyBear limbs)
//! pi[16..24) = destination_federation_limbs[8] (8 × 4-byte BabyBear limbs)
//! pi[24..28) = amount_limbs[4]                 (u64 as 4 × 16-bit limbs, LSB first)
//! ```
//!
//! Total = 28 PI slots, ~248 bits of binding strength per 32-byte field, and the
//! full 64 bits of amount — INJECTIVELY (`encode_amount_is_injective`,
//! `amount_round_trips`).
//!
//! Trace layout (1 row, padded to 4 to satisfy STARK power-of-2 requirements):
//!
//! ```text
//! col  0.. 8) nullifier_limbs[8]
//! col  8..16) recipient_limbs[8]
//! col 16..24) destination_federation_limbs[8]
//! col 24..28) amount_limbs[4]
//! ```
//!
//! Boundary constraints pin each trace column at row 0 to the corresponding
//! PI slot. The verifier passes the exact same 28 BabyBears it received from
//! the executor; any mismatch on any column fails STARK verification.
//!
//! # What this AIR does NOT do
//!
//! It does NOT re-prove the underlying spend (that's `note_spending`'s
//! job). It is a *binding-only* AIR: it carries the typed bridge-action
//! parameters at full fidelity inside a STARK so the executor can check
//! that the bridge mint it is about to apply matches the proof's bytes
//! algebraically, not just by ad-hoc structural comparison in plaintext.
//!
//! ⚑ **And the tuple it binds is PROVER-CHOSEN.** Nothing here attests that the
//! bound `(nullifier, recipient, destination_federation, amount)` corresponds to a
//! spend that happened; anyone can mint a verifying binding for any tuple.
//! `Dregg2/Circuit/BridgeBindingFromFold.lean` REFUSES this AIR as a bridge-mint
//! backing for exactly that reason, and the sound deployed backing is the
//! note-spend leaf folded to the published `mint_hash`
//! (`circuit-prove/src/note_spend_leaf_adapter.rs`). Do not read a verifying
//! `PortableActionBinding` as evidence that a burn occurred.
//!
//! Combined with `note_spending`'s Merkle/nullifier/key proof, the pair of
//! AIRs (spend + action) gives the executor algebraic guarantees on:
//! - Knowledge of the spending key (spending AIR)
//! - Merkle membership of the spent note (spending AIR)
//! - 248-bit-strength binding to nullifier / recipient / destination_federation
//!   (this AIR)
//! - Full, INJECTIVE 64-bit amount binding (this AIR)

use crate::field::BabyBear;

/// Number of BabyBear limbs used to represent a 32-byte value.
pub const HASH_LIMBS: usize = 8;

/// Bits per amount limb. ⚑ `16`, not `32`: every limb is then `< 2^16 ≪ p`, so
/// `BabyBear::new` never reduces. Mirrors
/// `effect_action_air::AMOUNT_LIMB_BITS` and Lean's
/// `EffectActionBindingEmit.LIMB_BITS`.
pub const AMOUNT_LIMB_BITS: u32 = 16;

/// Limbs per u64 amount: `4 · 16 = 64`, exact — no truncation, no wasted capacity.
pub const AMOUNT_LIMBS: usize = 4;

/// Trace width: 8 + 8 + 8 + 4 = 28 columns.
pub const BRIDGE_ACTION_WIDTH: usize = 3 * HASH_LIMBS + AMOUNT_LIMBS;

/// Number of public-input slots. Each 32-byte field uses 8 limbs; the amount uses
/// [`AMOUNT_LIMBS`]. The PI layout mirrors the column layout exactly.
pub const BRIDGE_ACTION_PI_COUNT: usize = BRIDGE_ACTION_WIDTH;

/// Column ranges. (Const fn would be cleaner; explicit names are clearer.)
pub mod col {
    /// Column range \[0, 8\): nullifier limbs.
    pub const NULLIFIER_START: usize = 0;
    /// Column range \[8, 16\): recipient (destination_commitment) limbs.
    pub const RECIPIENT_START: usize = 8;
    /// Column range \[16, 24\): destination_federation limbs.
    pub const DESTINATION_FEDERATION_START: usize = 16;
    /// Column range \[24, 28\): the four 16-bit amount limbs, LSB first.
    pub const AMOUNT_START: usize = 24;
}

/// Public input layout matches the column layout exactly.
pub mod pi {
    /// PI range \[0, 8\): nullifier limbs.
    pub const NULLIFIER_START: usize = 0;
    /// PI range \[8, 16\): recipient limbs.
    pub const RECIPIENT_START: usize = 8;
    /// PI range \[16, 24\): destination_federation limbs.
    pub const DESTINATION_FEDERATION_START: usize = 16;
    /// PI range \[24, 28\): the four 16-bit amount limbs, LSB first.
    pub const AMOUNT_START: usize = 24;
}

/// Encode a u64 amount as [`AMOUNT_LIMBS`] BabyBear limbs of
/// [`AMOUNT_LIMB_BITS`] bits, least-significant first.
///
/// ⚑ INJECTIVE, unlike the 2 × 32-bit split this replaced: every limb is
/// `< 2^16 ≪ p`, so `BabyBear::new` never reduces and two distinct u64s never
/// share a limb vector. [`decode_amount`] is the total inverse;
/// `encode_amount_is_injective` and `amount_round_trips` are the teeth.
pub fn encode_amount(amount: u64) -> [BabyBear; AMOUNT_LIMBS] {
    let mut out = [BabyBear::ZERO; AMOUNT_LIMBS];
    for (i, slot) in out.iter_mut().enumerate() {
        *slot = BabyBear::new(((amount >> (i as u32 * AMOUNT_LIMB_BITS)) & 0xFFFF) as u32);
    }
    out
}

/// Recover the u64 an [`encode_amount`] limb vector came from.
///
/// Returns `None` for a limb that is not `< 2^16` — i.e. for a felt vector that is
/// NOT in `encode_amount`'s image. That refusal is the point: it makes the claim
/// "these four felts denote this u64" checkable rather than assumed, which is what
/// the retired 2-limb shape could not offer at any assignment.
pub fn decode_amount(limbs: &[BabyBear; AMOUNT_LIMBS]) -> Option<u64> {
    let mut out = 0u64;
    for (i, l) in limbs.iter().enumerate() {
        let v = u64::from(l.canonical_val());
        if v >= 1u64 << AMOUNT_LIMB_BITS {
            return None;
        }
        out |= v << (i as u32 * AMOUNT_LIMB_BITS);
    }
    Some(out)
}

/// A bridge-action witness: the typed parameters the prover and verifier
/// will algebraically agree on.
#[derive(Clone, Debug)]
pub struct BridgeActionWitness {
    /// The 32-byte spent-note nullifier.
    pub nullifier: [u8; 32],
    /// The 32-byte destination-side commitment (recipient note commitment).
    pub recipient: [u8; 32],
    /// The 32-byte destination federation identity.
    pub destination_federation: [u8; 32],
    /// The full u64 amount (no truncation).
    pub amount: u64,
}

impl BridgeActionWitness {
    /// Compute the canonical public-input vector this witness commits to.
    pub fn public_inputs(&self) -> Vec<BabyBear> {
        let n = crate::effect_vm::bytes32_to_8_limbs(&self.nullifier);
        let r = crate::effect_vm::bytes32_to_8_limbs(&self.recipient);
        let d = crate::effect_vm::bytes32_to_8_limbs(&self.destination_federation);
        let a = encode_amount(self.amount);
        let mut pi = Vec::with_capacity(BRIDGE_ACTION_PI_COUNT);
        pi.extend_from_slice(&n);
        pi.extend_from_slice(&r);
        pi.extend_from_slice(&d);
        pi.extend_from_slice(&a);
        pi
    }
}

/// The Bridge Action AIR's shape descriptor (VK v2; see
/// `circuit::air_descriptor`). Captures the externally visible shape
/// of [`BridgeActionAir`] so callers can fingerprint it into VK v2's
/// layered hash.
///
/// The PI vector mirrors the column layout exactly (8-limb nullifier,
/// 8-limb recipient, 8-limb destination_federation, 4-limb amount).
pub const AIR_DESCRIPTOR: crate::air_descriptor::AirDescriptor =
    crate::air_descriptor::AirDescriptor {
        air_id: "bridge_action_air_v1",
        column_count: BRIDGE_ACTION_WIDTH,
        public_input_layout: &[
            crate::air_descriptor::PiSlot {
                name: "nullifier",
                offset: pi::NULLIFIER_START,
                length_in_felts: HASH_LIMBS,
            },
            crate::air_descriptor::PiSlot {
                name: "recipient",
                offset: pi::RECIPIENT_START,
                length_in_felts: HASH_LIMBS,
            },
            crate::air_descriptor::PiSlot {
                name: "destination_federation",
                offset: pi::DESTINATION_FEDERATION_START,
                length_in_felts: HASH_LIMBS,
            },
            crate::air_descriptor::PiSlot {
                name: "amount",
                offset: pi::AMOUNT_START,
                length_in_felts: AMOUNT_LIMBS,
            },
        ],
        // Linear transition constraints across the 28 columns, plus per-
        // column boundary bindings at row 0.
        constraint_polynomial_count: BRIDGE_ACTION_WIDTH,
        boundary_constraint_count: BRIDGE_ACTION_WIDTH,
        max_degree: 2,
        source_hash: None,
    };

/// The bridge-action binding AIR.
///
/// One real row of typed data; padded to 4 to satisfy STARK power-of-2
/// requirements (FRI requires a power-of-2 trace length).
pub struct BridgeActionAir;

impl BridgeActionAir {
    /// Generate the execution trace and public inputs from a witness.
    pub fn generate_trace(witness: &BridgeActionWitness) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let n = crate::effect_vm::bytes32_to_8_limbs(&witness.nullifier);
        let r = crate::effect_vm::bytes32_to_8_limbs(&witness.recipient);
        let d = crate::effect_vm::bytes32_to_8_limbs(&witness.destination_federation);
        let a = encode_amount(witness.amount);

        // Row 0: the full typed binding.
        let mut row0 = vec![BabyBear::ZERO; BRIDGE_ACTION_WIDTH];
        row0[col::NULLIFIER_START..col::NULLIFIER_START + HASH_LIMBS].copy_from_slice(&n);
        row0[col::RECIPIENT_START..col::RECIPIENT_START + HASH_LIMBS].copy_from_slice(&r);
        row0[col::DESTINATION_FEDERATION_START..col::DESTINATION_FEDERATION_START + HASH_LIMBS]
            .copy_from_slice(&d);
        row0[col::AMOUNT_START..col::AMOUNT_START + AMOUNT_LIMBS].copy_from_slice(&a);

        // Pad to length 4 (smallest power of 2 ≥ 1).
        let mut trace = Vec::with_capacity(4);
        trace.push(row0.clone());
        for _ in 1..4 {
            // Padding rows replicate row 0 so the boundary constraints at
            // (row 0, col X) are unambiguous and the transition continuity
            // (next == local for all cols) holds trivially.
            trace.push(row0.clone());
        }

        let public_inputs = witness.public_inputs();
        (trace, public_inputs)
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn make_witness() -> BridgeActionWitness {
        BridgeActionWitness {
            nullifier: [0x10; 32],
            recipient: [0x20; 32],
            destination_federation: [0x30; 32],
            amount: 0xDEAD_BEEF_CAFE_F00D,
        }
    }

    #[test]
    fn hash_limbs_roundtrip_deterministic() {
        let a = crate::effect_vm::bytes32_to_8_limbs(&[0x42; 32]);
        let b = crate::effect_vm::bytes32_to_8_limbs(&[0x42; 32]);
        assert_eq!(a, b, "bytes32_to_8_limbs must be deterministic");
    }

    #[test]
    fn hash_limbs_distinguish_distinct_bytes() {
        let a = crate::effect_vm::bytes32_to_8_limbs(&[0x42; 32]);
        let mut bytes = [0x42u8; 32];
        bytes[0] = 0x43;
        let b = crate::effect_vm::bytes32_to_8_limbs(&bytes);
        assert_ne!(a, b, "one byte change must change the limb encoding");
    }

    #[test]
    fn encode_amount_full_64_bits() {
        let l = encode_amount(0xDEAD_BEEF_CAFE_F00D);
        assert_eq!(l[0], BabyBear::new(0xF00D));
        assert_eq!(l[1], BabyBear::new(0xCAFE));
        assert_eq!(l[2], BabyBear::new(0xBEEF));
        assert_eq!(l[3], BabyBear::new(0xDEAD));
    }

    /// ⚑ THE REGRESSION POLE OF THE FLAG DAY. Under the retired 2 × 32-bit split,
    /// `lo` was `BabyBear::new(0)` for BOTH of these and the whole PI vector
    /// collided; a proof minted for one verified against the other. One addition,
    /// no search.
    #[test]
    fn encode_amount_is_injective_across_the_reduction_boundary() {
        assert_ne!(
            encode_amount(0),
            encode_amount(2_013_265_921),
            "amount and amount + p must not share a limb vector"
        );
        assert_ne!(
            encode_amount(1),
            encode_amount(1 + 2_013_265_921),
            "the collision is one addition away under the retired 32-bit split"
        );
        // Every limb is strictly below the felt modulus, so `BabyBear::new` cannot
        // have reduced — the structural reason injectivity holds at all.
        for a in [0u64, 1, u64::MAX, 2_013_265_921, 0xDEAD_BEEF_CAFE_F00D] {
            for limb in encode_amount(a) {
                assert!(
                    limb.0 < (1u32 << AMOUNT_LIMB_BITS),
                    "limb {limb:?} of {a} must be < 2^16 so no reduction occurs"
                );
            }
        }
    }

    /// ⚠ ANTI-VACUITY: the u64 comes BACK OUT of the limbs. A binding that cannot
    /// be decoded is a binding to felts, not to an amount.
    #[test]
    fn amount_round_trips() {
        for a in [
            0u64,
            1,
            0xFFFF,
            0x1_0000,
            2_013_265_921,
            (1u64 << 32) - 1,
            1u64 << 32,
            0xDEAD_BEEF_CAFE_F00D,
            u64::MAX,
        ] {
            assert_eq!(decode_amount(&encode_amount(a)), Some(a), "round-trip {a}");
        }
    }

    /// `decode_amount` REFUSES a felt vector outside `encode_amount`'s image — the
    /// check the retired shape had no way to express.
    #[test]
    fn decode_amount_refuses_an_out_of_image_limb() {
        let mut limbs = encode_amount(7);
        limbs[0] = BabyBear::new(1u32 << AMOUNT_LIMB_BITS);
        assert_eq!(decode_amount(&limbs), None);
    }

    /// ⚑ THE PIGEONHOLE, ASSERTED. Two felts hold `p²` pairs; a u64 has `2^64`
    /// values. `p² < 2^64`, so EVERY 2-felt encoding of a u64 collides — the
    /// retired shape was not merely badly chosen, it was impossible. Four 16-bit
    /// limbs are exactly enough and not more.
    #[test]
    fn two_felts_cannot_carry_a_u64() {
        let p = u128::from(crate::field::BABYBEAR_P);
        assert!(
            p * p < 1u128 << 64,
            "p^2 = {} must be < 2^64 = {} — the pigeonhole that makes any 2-felt \
             u64 encoding non-injective",
            p * p,
            1u128 << 64
        );
        assert_eq!(AMOUNT_LIMBS as u32 * AMOUNT_LIMB_BITS, 64);
        assert!(
            (1u128 << AMOUNT_LIMB_BITS) <= p,
            "each 16-bit limb must fit a felt without reduction"
        );
    }

    #[test]
    fn encode_amount_distinguishes_high_bits() {
        // Two amounts that share low 30 bits but differ in high bits must
        // produce distinct encodings — proving we don't have the 30-bit
        // truncation bug.
        let a = encode_amount((1u64 << 30) | 1); // low bit set, bit 30 set
        let b = encode_amount(1); // only low bit set
        assert_ne!(
            a, b,
            "amounts differing only in high bits must produce distinct PIs"
        );
    }

    #[test]
    fn witness_public_inputs_layout() {
        let w = make_witness();
        let pi = w.public_inputs();
        assert_eq!(pi.len(), BRIDGE_ACTION_PI_COUNT);
        let n = crate::effect_vm::bytes32_to_8_limbs(&w.nullifier);
        let r = crate::effect_vm::bytes32_to_8_limbs(&w.recipient);
        let d = crate::effect_vm::bytes32_to_8_limbs(&w.destination_federation);
        let a = encode_amount(w.amount);
        for i in 0..HASH_LIMBS {
            assert_eq!(pi[pi::NULLIFIER_START + i], n[i]);
            assert_eq!(pi[pi::RECIPIENT_START + i], r[i]);
            assert_eq!(pi[pi::DESTINATION_FEDERATION_START + i], d[i]);
        }
        for i in 0..AMOUNT_LIMBS {
            assert_eq!(pi[pi::AMOUNT_START + i], a[i]);
        }
        // …and the amount is recoverable from the PI vector alone.
        let mut back = [BabyBear::ZERO; AMOUNT_LIMBS];
        back.copy_from_slice(&pi[pi::AMOUNT_START..pi::AMOUNT_START + AMOUNT_LIMBS]);
        assert_eq!(decode_amount(&back), Some(w.amount));
    }

    #[test]
    fn trace_generation_shape() {
        let w = make_witness();
        let (trace, pi) = BridgeActionAir::generate_trace(&w);
        assert_eq!(trace.len(), 4, "padded to power of 2 (smallest = 4)");
        for row in &trace {
            assert_eq!(row.len(), BRIDGE_ACTION_WIDTH);
        }
        assert_eq!(pi.len(), BRIDGE_ACTION_PI_COUNT);
    }
}
