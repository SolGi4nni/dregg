//! Golden-Vision recursive witness compression — the PRODUCER half (Group C of
//! the turn-prover extraction).
//!
//! `dregg_turn::witnessed_receipt` keeps the TYPES (`WitnessedReceipt`,
//! `WitnessBundle`, `RecursiveProofVariant`) because every verify path and every
//! on-disk artifact needs them unconditionally. Producing a recursive variant
//! needs `dregg_circuit_prove::recursive_witness_bundle::RecursiveProofProducer`,
//! so it lives here, and reaches core two ways:
//!
//! * [`CircuitRecursiveWitnessProducer`] implements core's
//!   [`RecursiveWitnessProducer`](dregg_turn::recursive_witness_producer::RecursiveWitnessProducer)
//!   and is installed once at startup by
//!   [`crate::install_recursive_witness_producer`]. That is what lights up the
//!   best-effort `recursive_compress` flag on
//!   `WitnessedReceipt::from_components_with_compression`. Nothing installed ⇒ no
//!   variant attached (fail-closed by absence, the old
//!   `#[cfg(not(feature = "prover"))]` behavior).
//! * [`from_components_strict_recursive`] is the HARD-FAIL constructor: it calls
//!   the producer directly and returns `Err` if compression cannot be produced.
//!   It needs no installation because reaching it already means the caller linked
//!   this crate.

use dregg_circuit::field::BabyBear;
use dregg_turn::recursive_witness_producer::RecursiveWitnessProducer;
use dregg_turn::turn::TurnReceipt;
use dregg_turn::witnessed_receipt::{RecursiveProofVariant, WitnessBundle, WitnessedReceipt};

/// Produce a [`RecursiveProofVariant`] from an inline scope-2 trace + the
/// receipt's public inputs.
///
/// Thin wrapper around
/// [`dregg_circuit_prove::recursive_witness_bundle::RecursiveProofProducer::produce`]
/// so the receipt constructors do not have to thread `BabyBear` through their
/// signatures. Returns the compressed variant on success; on failure returns the
/// error string from the recursion library (e.g. AIR build failure, postcard
/// encode error).
///
/// Relies on the `recursion` feature being enabled in `dregg-circuit` (which is
/// in its default feature set). If the host disables the feature, this entry
/// point becomes a link-time error — which is the honest signal: opt-in recursive
/// compression requires the recursion substrate.
pub fn produce_recursive_variant(
    trace: &[Vec<BabyBear>],
    public_inputs_u32: &[u32],
) -> Result<RecursiveProofVariant, String> {
    use dregg_circuit_prove::recursive_witness_bundle::RecursiveProofProducer;

    let pi: Vec<BabyBear> = public_inputs_u32
        .iter()
        .map(|&v| BabyBear::new_canonical(v))
        .collect();

    let out = RecursiveProofProducer::produce(trace, &pi)?;
    Ok(RecursiveProofVariant {
        proof_bytes: out.proof_bytes,
        public_inputs: public_inputs_u32.to_vec(),
        recursive_vk_hash: out.recursive_vk_hash,
    })
}

/// The injectable producer core `dregg-turn` calls through.
#[derive(Clone, Copy, Debug, Default)]
pub struct CircuitRecursiveWitnessProducer;

impl CircuitRecursiveWitnessProducer {
    pub fn new() -> Self {
        Self
    }
}

impl RecursiveWitnessProducer for CircuitRecursiveWitnessProducer {
    fn produce(
        &self,
        trace: &[Vec<BabyBear>],
        public_inputs_u32: &[u32],
    ) -> Result<RecursiveProofVariant, String> {
        produce_recursive_variant(trace, public_inputs_u32)
    }
}

/// Like `WitnessedReceipt::from_components_with_compression` but hard-fails if
/// recursive compression cannot be produced. Use when the caller requires the
/// Golden Vision form.
///
/// Was `WitnessedReceipt::from_components_strict_recursive` behind
/// `dregg-turn`'s `prover` feature; it is a free function here because the
/// receipt TYPE stays in core and only the producer moved.
pub fn from_components_strict_recursive(
    receipt: TurnReceipt,
    proof_bytes: Vec<u8>,
    public_inputs: Vec<u32>,
    trace: &[Vec<BabyBear>],
) -> Result<WitnessedReceipt, String> {
    let rp = produce_recursive_variant(trace, &public_inputs)?;
    let wb = WitnessBundle::inline_with_recursive(trace, rp);
    let h = wb.witness_hash();
    Ok(WitnessedReceipt {
        receipt,
        proof_bytes,
        public_inputs,
        witness_bundle: Some(wb),
        witness_hash: h,
        aggregate_membership: None,
        bilateral_schedule: None,
    })
}
