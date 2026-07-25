//! The recursive-witness-compression seam (Golden Vision, Group C of the
//! turn-prover extraction).
//!
//! A [`crate::witnessed_receipt::WitnessBundle`] may carry a
//! [`RecursiveProofVariant`] — a single small recursive STARK attesting "I re-ran
//! the AIR over this inline trace and accepted", so a replayer verifies ~KB
//! instead of re-running the whole trace. PRODUCING that variant needs
//! `dregg_circuit_prove::recursive_witness_bundle::RecursiveProofProducer`, i.e.
//! the recursion substrate; VERIFYING and CARRYING it needs only the wire types.
//!
//! So the split is: the `WitnessedReceipt` / `WitnessBundle` /
//! `RecursiveProofVariant` **types stay here** (the verify path and every on-disk
//! artifact need them, unconditionally), and the **producer** lives in
//! `dregg-turn-prover`, reaching this crate through the trait below.
//!
//! ## Fail-closed by absence
//!
//! [`crate::witnessed_receipt::WitnessedReceipt::from_components_with_compression`]
//! consults [`recursive_witness_producer`]. With nothing installed it attaches no
//! recursive variant and returns the Silver-Vision (inline-trace) receipt — the
//! identical behavior to the deleted `#[cfg(not(feature = "prover"))]` build, and
//! identical to the already-documented best-effort behavior when the producer
//! errors. Nothing is fabricated: absent the prover there is simply no Golden
//! Vision proof, and a consumer that REQUIRES one calls
//! `dregg_turn_prover::recursive_bundle::from_components_strict_recursive`, which
//! cannot be reached without linking the prover crate at all.
//!
//! Installation is **once, irreversible** (`OnceLock`), the same posture as the
//! exact-FNSP-v3 proof authority: no later crate can swap the compression
//! producer after the node has begun emitting receipts.

use core::fmt;
use std::error::Error;
use std::sync::{Arc, OnceLock};

use crate::witnessed_receipt::RecursiveProofVariant;

/// The injected Golden-Vision recursive-compression producer.
///
/// Implemented by `dregg_turn_prover::recursive_bundle::CircuitRecursiveWitnessProducer`
/// over `dregg_circuit_prove::recursive_witness_bundle::RecursiveProofProducer`.
pub trait RecursiveWitnessProducer: Send + Sync {
    /// Produce the recursive variant for `trace` + `public_inputs_u32` (canonical
    /// BabyBear `u32` cells), or the error string from the recursion library.
    ///
    /// Must be side-effect free: this is called from a receipt constructor.
    fn produce(
        &self,
        trace: &[Vec<dregg_circuit::field::BabyBear>],
        public_inputs_u32: &[u32],
    ) -> Result<RecursiveProofVariant, String>;
}

static RECURSIVE_WITNESS_PRODUCER: OnceLock<Arc<dyn RecursiveWitnessProducer>> = OnceLock::new();

/// Install the process-wide recursive-compression producer.
///
/// `dregg_turn_prover::install_recursive_witness_producer` is the production
/// caller. Returns `Err` if one is already installed — install-once by design.
pub fn install_recursive_witness_producer(
    producer: Arc<dyn RecursiveWitnessProducer>,
) -> Result<(), RecursiveWitnessProducerAlreadyInstalled> {
    RECURSIVE_WITNESS_PRODUCER
        .set(producer)
        .map_err(|_| RecursiveWitnessProducerAlreadyInstalled)
}

/// The installed producer, if any. `None` ⇒ no Golden-Vision compression is
/// available in this process (fail-closed: the receipt keeps its inline trace).
pub fn recursive_witness_producer() -> Option<&'static Arc<dyn RecursiveWitnessProducer>> {
    RECURSIVE_WITNESS_PRODUCER.get()
}

/// Whether a recursive-compression producer has been installed in this process.
pub fn recursive_witness_producer_installed() -> bool {
    RECURSIVE_WITNESS_PRODUCER.get().is_some()
}

/// Refusal of a second [`install_recursive_witness_producer`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RecursiveWitnessProducerAlreadyInstalled;

impl fmt::Display for RecursiveWitnessProducerAlreadyInstalled {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("a recursive witness producer is already installed")
    }
}

impl Error for RecursiveWitnessProducerAlreadyInstalled {}
