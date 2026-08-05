//! Verifying a recursive batch proof, and fingerprinting the circuit it is a proof OF.
//!
//! Two operations, and they are load-bearing in that order:
//!
//! 1. [`recursion_vk_fingerprint`] — **which circuit is this**. Without it, "the root verifies"
//!    means only "*some* circuit's proof verifies", and a from-scratch prover could aggregate a
//!    different circuit's proofs and present a root this verifier accepts.
//! 2. [`verify_recursive_batch_proof_with_config`] — **does it verify**.
//!
//! A consumer that runs (2) without (1) has checked nothing about the statement.

use p3_recursion::{RecursionOutput, ops::Poseidon2Config};

use crate::config::{D, DreggRecursionConfig, create_recursion_config};

/// A fingerprint of a recursive batch proof's **verifier-reconstruction inputs** — the closest
/// thing the fork's proof format has to a verifying key.
/// [`verify_recursive_batch_proof`] reconstructs the circuit table AIRs and the preprocessed
/// binding **from the proof itself** (`table_packing`, `rows`, `alu_variant`, `ext_degree`,
/// `w_binomial`, the non-primitive table manifest, and `stark_common` — whose
/// `preprocessed.commitment` is the Merkle binding of the verifier circuit's static op-list).
///
/// The fingerprint hashes exactly those reconstruction inputs (shape + preprocessed binding;
/// runtime values are excluded), so an accepted proof whose fingerprint equals a trusted anchor
/// is — under blake3 collision resistance and the MMCS commitment binding — a proof of the SAME
/// verifier-circuit structure the anchor was extracted from.
///
/// ## What this does and does NOT pin (be precise)
///
/// PINS: the root layer's circuit structure — its op-list (via the preprocessed commitment),
/// table shapes, packing, lookups (derived from the rebuilt AIRs), and the non-primitive table
/// manifest shape.
///
/// ⚑ 2026-07-30: fork rev `fc3c6df` made a constant's VALUE a PREPROCESSED column of `ConstAir`
/// (`[ext_mult, out_idx, value[0..D]]`) constrained equal to the main-trace copy, so the
/// `into_recursion_input_pinned` `connect`-to-`alloc_const` pin of a child's Merkle cap now
/// REACHES this fingerprint. Two probes that previously measured the pin to pin nothing
/// (`const_pin_probe.rs`, `vk_pin_lever_a_probe.rs`) are inverted. What is UNCHANGED: a child's
/// cap also rides as a runtime PUBLIC input and `PublicAir`'s value columns are still main-trace
/// only — deliberately, since a public input's value is per-execution data and must stay out of
/// circuit identity. The single-layer step is MEASURED; transitivity to the root is READ off the
/// call graph. See `dregg_circuit_prove::ivc_turn_chain`'s module docs for the two-horn analysis
/// and the residual.
///
/// ⚑ **DETERMINISM IS A SHIPPED PROPERTY.** An honest re-fold of the same chain must mint the
/// SAME fingerprint or the light client's distributed trust anchor cannot be reproduced;
/// `circuit-prove/tests/recursion_vk_determinism.rs` folds one fixed chain four times (three
/// in-process, one in a child process) and requires all four to agree.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct RecursionVk(pub [u8; 32]);

impl RecursionVk {
    /// Hex rendering for error messages and anchor pinning.
    pub fn to_hex(&self) -> String {
        self.0.iter().map(|b| format!("{b:02x}")).collect()
    }

    /// Parse a 64-character lowercase-hex fingerprint. Returns `None` on any other shape — an
    /// operator-supplied anchor that does not parse must not silently become a zero anchor.
    pub fn from_hex(s: &str) -> Option<Self> {
        if s.len() != 64 {
            return None;
        }
        let mut out = [0u8; 32];
        for (i, byte) in out.iter_mut().enumerate() {
            *byte = u8::from_str_radix(s.get(2 * i..2 * i + 2)?, 16).ok()?;
        }
        Some(Self(out))
    }
}

/// Compute the [`RecursionVk`] fingerprint of a recursive batch proof's verifier-reconstruction
/// inputs. Deterministic in the circuit structure; independent of the witness content (two
/// proofs of the same circuit shape over different data fingerprint identically — that is what
/// makes it usable as a trust anchor).
pub fn recursion_vk_fingerprint(
    proof: &p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>,
) -> RecursionVk {
    fn ser<T: serde::Serialize>(h: &mut blake3::Hasher, label: &str, v: &T) {
        let bytes = postcard::to_allocvec(v)
            .expect("VK-material field must postcard-serialize (alloc serializer is infallible)");
        h.update(label.as_bytes());
        h.update(&(bytes.len() as u64).to_le_bytes());
        h.update(&bytes);
    }

    let mut h = blake3::Hasher::new();
    h.update(b"dregg-recursion-vk-v1");

    // The shape fields verify_all_tables rebuilds the table AIRs from.
    ser(&mut h, "table_packing", &proof.table_packing);
    ser(&mut h, "rows", &proof.rows);
    ser(&mut h, "alu_variant", &proof.alu_variant);
    h.update(&[proof.alu_quintic_trinomial as u8]);
    h.update(&(proof.ext_degree as u64).to_le_bytes());
    ser(&mut h, "w_binomial", &proof.w_binomial);

    // Per-table degree bits (the FRI domain shape the verifier trusts).
    ser(&mut h, "degree_bits", &proof.proof.degree_bits);

    // Non-primitive table manifest SHAPE (op_type / rows / lanes / variant).
    // `entry.public_values` are runtime values the host verifier passes through to
    // `verify_batch` — excluded so the fingerprint stays content-independent.
    h.update(&(proof.non_primitives.len() as u64).to_le_bytes());
    for entry in &proof.non_primitives {
        ser(&mut h, "npo_op_type", &entry.op_type);
        h.update(&(entry.rows as u64).to_le_bytes());
        h.update(&(entry.lanes as u64).to_le_bytes());
        ser(&mut h, "npo_air_variant", &entry.air_variant);
    }

    // The preprocessed binding — THE verifying-key core: the Merkle commitment to the verifier
    // circuit's static op-list columns, plus the per-instance metadata the verifier interprets
    // it with.
    match &proof.stark_common.preprocessed {
        None => {
            h.update(&[0u8]);
        }
        Some(gp) => {
            h.update(&[1u8]);
            ser(&mut h, "preprocessed_commitment", &gp.commitment);
            h.update(&(gp.instances.len() as u64).to_le_bytes());
            for inst in &gp.instances {
                match inst {
                    None => {
                        h.update(&[0u8]);
                    }
                    Some(m) => {
                        h.update(&[1u8]);
                        h.update(&(m.matrix_index as u64).to_le_bytes());
                        h.update(&(m.width as u64).to_le_bytes());
                        h.update(&(m.degree_bits as u64).to_le_bytes());
                    }
                }
            }
            ser(&mut h, "matrix_to_instance", &gp.matrix_to_instance);
        }
    }

    RecursionVk(*h.finalize().as_bytes())
}

/// Verify a recursive proof output (the in-memory `RecursionOutput` a fold produces).
pub fn verify_recursive_layer(
    output: &RecursionOutput<DreggRecursionConfig>,
) -> Result<(), String> {
    verify_recursive_batch_proof(&output.0)
}

/// Verify a recursive proof from just the inner `BatchStarkProof`.
///
/// The `Rc<CircuitProverData<SC>>` half of `RecursionOutput` is only needed for *chaining* the
/// proof into another recursion layer, not for verifying it — which is exactly why a verify-only
/// consumer never needs the prover's data structures.
pub fn verify_recursive_batch_proof(
    proof: &p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>,
) -> Result<(), String> {
    verify_recursive_batch_proof_with_config(proof, &create_recursion_config())
}

/// [`verify_recursive_batch_proof`] under an explicit recursion config — the proof must have
/// been PRODUCED under the same config's FRI engine. The IR-v2 leaf-wrap / chain-fold tower runs
/// at [`crate::config::ir2_leaf_wrap_config`] (log_blowup 6), not the default recursion knobs
/// (log_blowup 3).
pub fn verify_recursive_batch_proof_with_config(
    proof: &p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
) -> Result<(), String> {
    let mut prover = p3_circuit_prover::BatchStarkProver::new(config.clone());
    // Register the NPO table provers that were used to produce the recursive proof. The verifier
    // needs these to interpret the non-primitive ops in the proof.
    prover.register_poseidon2_table::<D>(Poseidon2Config::BABY_BEAR_D4_W16);
    // The ISOLATED segment-digest permutation table (`baby_bear_d4_w24`): a distinct Poseidon2
    // op-type the IVC/chain segment-digest sponge runs over, so its rows never share the W16
    // challenger's chain-state / CTL bus / connect graph.
    prover.register_poseidon2_table::<D>(Poseidon2Config::BABY_BEAR_D4_W24);
    // split_coeff_tables = false because Poseidon2Config::D (4) == extension degree D (4)
    prover.register_recompose_table::<D>(false);
    // The exposed-claim channel: a fold root carries an `expose_claim` table.
    prover.register_expose_claim_table::<D>();
    prover
        .verify_all_tables(proof)
        .map_err(|e| format!("Recursive proof verification failed: {:?}", e))
}

/// Decode a postcard-serialised `BatchStarkProof` at the given config's type.
///
/// ⚑ Kept separate from verification so a caller can fingerprint a decoded proof BEFORE deciding
/// to spend the verify: a root whose circuit identity is already wrong should be refused without
/// running FRI.
pub fn decode_recursive_batch_proof(
    bytes: &[u8],
) -> Result<p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>, String> {
    postcard::from_bytes(bytes).map_err(|e| format!("Recursive proof postcard decode failed: {e}"))
}

/// Verify a recursive proof from postcard-serialised bytes, at the DEFAULT recursion knobs.
pub fn verify_recursive_layer_bytes(bytes: &[u8]) -> Result<(), String> {
    verify_recursive_batch_proof(&decode_recursive_batch_proof(bytes)?)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The hex round-trip is exact, and a malformed anchor is `None` rather than a zero anchor —
    /// an operator typo must not silently become "pin nothing".
    #[test]
    fn vk_hex_round_trips_and_refuses_malformed() {
        let vk = RecursionVk([0xABu8; 32]);
        assert_eq!(RecursionVk::from_hex(&vk.to_hex()), Some(vk));
        assert_eq!(RecursionVk::from_hex(""), None);
        assert_eq!(RecursionVk::from_hex(&"ab".repeat(31)), None);
        assert_eq!(RecursionVk::from_hex(&"zz".repeat(32)), None);
    }

    /// A garbage byte string does not decode into a proof — the decode seam is a refusal, not a
    /// panic, so a caller can treat "unparseable root" the same as "wrong root".
    #[test]
    fn garbage_bytes_do_not_decode_into_a_root() {
        assert!(decode_recursive_batch_proof(&[0xAAu8; 96]).is_err());
    }
}
