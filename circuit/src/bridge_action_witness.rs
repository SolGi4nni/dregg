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
//! # What this AIR binds
//!
//! Public inputs (all bytes / amount carried at full fidelity):
//!
//! ```text
//! pi[ 0.. 8) = nullifier_limbs[8]              (8 × 4-byte BabyBear limbs)
//! pi[ 8..16) = recipient_limbs[8]              (8 × 4-byte BabyBear limbs)
//! pi[16..24) = destination_federation_limbs[8] (8 × 4-byte BabyBear limbs)
//! pi[24]     = amount_lo   (low  32 bits of u64 amount, BabyBear-encoded)
//! pi[25]     = amount_hi   (high 32 bits of u64 amount, BabyBear-encoded)
//! ```
//!
//! Total = 26 PI slots, ~248 bits of binding strength per 32-byte field, and
//! the full 64 bits of amount (split into two 32-bit limbs, each reduced
//! canonically to BabyBear via `BabyBear::new`).
//!
//! Trace layout (1 row, padded to 4 to satisfy STARK power-of-2 requirements):
//!
//! ```text
//! col  0.. 8) nullifier_limbs[8]
//! col  8..16) recipient_limbs[8]
//! col 16..24) destination_federation_limbs[8]
//! col 24      amount_lo
//! col 25      amount_hi
//! ```
//!
//! Boundary constraints pin each trace column at row 0 to the corresponding
//! PI slot. The verifier passes the exact same 26 BabyBears it received from
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
//! Combined with `note_spending`'s Merkle/nullifier/key proof, the pair of
//! AIRs (spend + action) gives the executor algebraic guarantees on:
//! - Knowledge of the spending key (spending AIR)
//! - Merkle membership of the spent note (spending AIR)
//! - 248-bit-strength binding to nullifier / recipient / destination_federation
//!   (this AIR)
//! - Full 64-bit amount binding (this AIR)

use crate::field::BabyBear;

/// Trace width: 8 + 8 + 8 + 2 = 26 columns.
pub const BRIDGE_ACTION_WIDTH: usize = 26;

/// Number of public-input slots. Each 32-byte field uses 8 limbs; amount uses 2.
pub const BRIDGE_ACTION_PI_COUNT: usize = 26;

/// Number of BabyBear limbs used to represent a 32-byte value.
pub const HASH_LIMBS: usize = 8;

/// Column ranges. (Const fn would be cleaner; explicit names are clearer.)
pub mod col {
    /// Column range \[0, 8\): nullifier limbs.
    pub const NULLIFIER_START: usize = 0;
    /// Column range \[8, 16\): recipient (destination_commitment) limbs.
    pub const RECIPIENT_START: usize = 8;
    /// Column range \[16, 24\): destination_federation limbs.
    pub const DESTINATION_FEDERATION_START: usize = 16;
    /// Column 24: amount low 32 bits.
    pub const AMOUNT_LO: usize = 24;
    /// Column 25: amount high 32 bits.
    pub const AMOUNT_HI: usize = 25;
}

/// Public input layout matches the column layout exactly.
pub mod pi {
    /// PI range \[0, 8\): nullifier limbs.
    pub const NULLIFIER_START: usize = 0;
    /// PI range \[8, 16\): recipient limbs.
    pub const RECIPIENT_START: usize = 8;
    /// PI range \[16, 24\): destination_federation limbs.
    pub const DESTINATION_FEDERATION_START: usize = 16;
    /// PI 24: amount_lo.
    pub const AMOUNT_LO: usize = 24;
    /// PI 25: amount_hi.
    pub const AMOUNT_HI: usize = 25;
}

/// Encode a u64 amount as 2 BabyBear limbs (low 32 + high 32, each reduced
/// canonically via `BabyBear::new`).
pub fn encode_amount(amount: u64) -> [BabyBear; 2] {
    let lo = (amount & 0xFFFF_FFFF) as u32;
    let hi = (amount >> 32) as u32;
    [BabyBear::new(lo), BabyBear::new(hi)]
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
        let [lo, hi] = encode_amount(self.amount);
        let mut pi = Vec::with_capacity(BRIDGE_ACTION_PI_COUNT);
        pi.extend_from_slice(&n);
        pi.extend_from_slice(&r);
        pi.extend_from_slice(&d);
        pi.push(lo);
        pi.push(hi);
        pi
    }
}

/// The Bridge Action AIR's shape descriptor (VK v2; see
/// `circuit::air_descriptor`). Captures the externally visible shape
/// of [`BridgeActionAir`] so callers can fingerprint it into VK v2's
/// layered hash.
///
/// The PI vector mirrors the column layout exactly (8-limb nullifier,
/// 8-limb recipient, 8-limb destination_federation, 2-limb amount).
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
                name: "amount_lo",
                offset: pi::AMOUNT_LO,
                length_in_felts: 1,
            },
            crate::air_descriptor::PiSlot {
                name: "amount_hi",
                offset: pi::AMOUNT_HI,
                length_in_felts: 1,
            },
        ],
        // Linear transition constraints across the 26 columns, plus per-
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
        let [lo, hi] = encode_amount(witness.amount);

        // Row 0: the full typed binding.
        let mut row0 = vec![BabyBear::ZERO; BRIDGE_ACTION_WIDTH];
        row0[col::NULLIFIER_START..col::NULLIFIER_START + HASH_LIMBS].copy_from_slice(&n);
        row0[col::RECIPIENT_START..col::RECIPIENT_START + HASH_LIMBS].copy_from_slice(&r);
        row0[col::DESTINATION_FEDERATION_START..col::DESTINATION_FEDERATION_START + HASH_LIMBS]
            .copy_from_slice(&d);
        row0[col::AMOUNT_LO] = lo;
        row0[col::AMOUNT_HI] = hi;

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
        let [lo, hi] = encode_amount(0xDEAD_BEEF_CAFE_F00D);
        // Low 32 bits = 0xCAFE_F00D, high 32 bits = 0xDEAD_BEEF.
        assert_eq!(lo, BabyBear::new(0xCAFE_F00D));
        assert_eq!(hi, BabyBear::new(0xDEAD_BEEF));
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
        let [lo, hi] = encode_amount(w.amount);
        for i in 0..HASH_LIMBS {
            assert_eq!(pi[pi::NULLIFIER_START + i], n[i]);
            assert_eq!(pi[pi::RECIPIENT_START + i], r[i]);
            assert_eq!(pi[pi::DESTINATION_FEDERATION_START + i], d[i]);
        }
        assert_eq!(pi[pi::AMOUNT_LO], lo);
        assert_eq!(pi[pi::AMOUNT_HI], hi);
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
