use p3_field::{Field, PackedValue, PrimeField, PrimeField32, PrimeField64};
use p3_maybe_rayon::prelude::*;
use p3_symmetric::CryptographicPermutation;
use tracing::instrument;

use crate::{
    CanObserve, CanSampleBits, CanSampleUniformBits, DuplexChallenger, MultiField32Challenger,
    UniformSamplingField,
};

// ═════════════════════════════════════════════════════════════════════════════════════════════
// ⚑ DREGG DELTA vs Plonky3 82cfad73 — the ONLY edit in this vendored crate.
//
// Upstream grinds with rayon's UNORDERED finders: `find_map_any` (`DuplexChallenger::grind`) and
// `find_any` (`grind_generic`, `MultiField32Challenger::grind`, and both
// `SerializingChallenger{32,64}::grind` in the sibling module). Those return whichever chunk a
// worker thread happened to finish first, so two runs of the same binary on the same transcript
// pick DIFFERENT valid PoW witnesses.
//
// That is sound — the verifier checks VALIDITY (`check_witness`: the low `bits` sampled bits are
// zero), never a canonical value, and every valid witness verifies — but it is not
// REPRODUCIBLE, because the witness is absorbed into the Fiat-Shamir transcript BEFORE the query
// indices are drawn. A different witness ⇒ different query indices ⇒ different opened values ⇒
// a different (postcard varint-encoded) proof, byte-for-byte and length included.
//
// MEASURED in this tree (`GOAL-MINA-SEMANTIC-LIGHTCLIENTS.md`, 2026-07-31): three rayon runs of
// one binary produced three distinct apex/terminal/shrink proof lengths, while the serial
// fallback — whose shim implements `find_any` as `Iterator::find`, i.e. min-index — reproduced
// its own bytes exactly. The VK is unaffected either way (`recursion_vk_fingerprint` hashes
// circuit SHAPE and explicitly excludes `public_values`, opened values, query proofs and the pow
// witness), so this is NOT a flag day; what it broke was every byte-parity gate in the tree.
//
// The fix is to search in parallel and take the SEQUENTIALLY FIRST match:
//   `find_any`      -> `find_first`
//   `find_map_any`  -> `find_map_first`
// which is exactly the serial fallback's answer, so rayon-on and rayon-off now agree, and two
// rayon runs agree with each other. It is also independent of `F::Packing::WIDTH`: the batched
// `DuplexChallenger` path scans lanes with `Iterator::find` inside a batch, so the lowest
// matching BATCH's lowest matching LANE is the global minimum candidate whatever the SIMD width.
//
// ⚑ NOT A SOUNDNESS CHANGE, and deliberately so. `query_proof_of_work_bits` /
// `commit_proof_of_work_bits` are untouched; the work an honest prover performs and the
// predicate the verifier checks are identical. Only WHICH of the many valid witnesses is
// returned changes. A "determinism fix" that lowered a PoW knob would be the opposite of this.
// ═════════════════════════════════════════════════════════════════════════════════════════════

/// Trait for challengers that support proof-of-work (PoW) grinding.
///
/// A `GrindingChallenger` can:
/// - Absorb a candidate witness into the transcript
/// - Sample random bitstrings to check the PoW condition
/// - Brute-force search for a valid witness that satisfies the PoW
///
/// This trait is typically used in protocols requiring computational effort
/// from the prover.
pub trait GrindingChallenger:
    CanObserve<Self::Witness> + CanSampleBits<usize> + Sync + Clone
{
    /// The underlying field element type used as the witness.
    type Witness: Field;

    /// Perform a brute-force search to find a valid PoW witness.
    ///
    /// Given a `bits` parameter, this function searches for a field element
    /// `witness` such that after observing it, the next `bits` bits that challenger outputs
    /// are all `0`.
    fn grind(&mut self, bits: usize) -> Self::Witness;

    /// Check whether a given `witness` satisfies the PoW condition.
    ///
    /// After absorbing the witness, the challenger samples `bits` random bits
    /// and verifies that all bits sampled are zero.
    ///
    /// Returns `true` if the witness passes the PoW check, `false` otherwise.
    #[must_use]
    fn check_witness(&mut self, bits: usize, witness: Self::Witness) -> bool {
        if bits == 0 {
            return true;
        }
        self.observe(witness);
        self.sample_bits(bits) == 0
    }
}

/// Trait for challengers that support proof-of-work (PoW) grinding with
/// guaranteed uniformly sampled bits.
pub trait UniformGrindingChallenger:
    GrindingChallenger + CanSampleUniformBits<Self::Witness>
{
    /// Grinds based on *uniformly sampled bits*. This variant is allowed to do rejection
    /// sampling if a value is sampled that would violate our uniformity requirement
    /// (chance of about 1/P).
    ///
    /// Use this together with `check_witness_uniform`.
    fn grind_uniform(&mut self, bits: usize) -> Self::Witness;

    /// Grinds based on *uniformly sampled bits*. This variant errors if a value is
    /// sampled, which would violate our uniformity requirement (chance of about 1/P).
    /// See the `UniformSamplingField` trait implemented for each field for details.
    ///
    /// Use this together with `check_witness_uniform_may_error`.
    fn grind_uniform_may_error(&mut self, bits: usize) -> Self::Witness;

    /// Check whether a given `witness` satisfies the PoW condition.
    ///
    /// After absorbing the witness, the challenger samples `bits` random bits
    /// *uniformly* and verifies that all bits sampled are zero. The uniform
    /// sampling implies we do rejection sampling in about ~1/P cases.
    ///
    /// Returns `true` if the witness passes the PoW check, `false` otherwise.
    fn check_witness_uniform(&mut self, bits: usize, witness: Self::Witness) -> bool {
        self.observe(witness);
        self.sample_uniform_bits::<true>(bits)
            .expect("Error impossible here due to resampling strategy")
            == 0
    }

    /// Check whether a given `witness` satisfies the PoW condition.
    ///
    /// After absorbing the witness, the challenger samples `bits` random bits
    /// *uniformly* and verifies that all bits sampled are zero. In about ~1/P
    /// cases this function may error if a sampled value lies outside a range
    /// in which we can guarantee uniform bits.
    ///
    /// Returns `true` if the witness passes the PoW check, `false` otherwise.
    fn check_witness_uniform_may_error(&mut self, bits: usize, witness: Self::Witness) -> bool {
        self.observe(witness);
        self.sample_uniform_bits::<false>(bits)
            .is_ok_and(|v| v == 0)
    }
}

impl<F, P, const WIDTH: usize, const RATE: usize> GrindingChallenger
    for DuplexChallenger<F, P, WIDTH, RATE>
where
    F: PrimeField64,
    P: CryptographicPermutation<[F; WIDTH]>
        + CryptographicPermutation<[<F as Field>::Packing; WIDTH]>,
{
    type Witness = F;

    #[instrument(name = "grind for proof-of-work witness", skip_all)]
    fn grind(&mut self, bits: usize) -> Self::Witness {
        // Ensure `bits` is small enough to be used in a shift.
        assert!(bits < 64, "bit count must be valid");

        // Ensure the PoW target 2^bits is smaller than the field order.
        // Otherwise, the probability analysis for grinding would break.
        assert!((1u64 << bits) < F::ORDER_U64);

        // Trivial case: 0 bits mean no PoW is required and any witness is valid.
        if bits == 0 {
            return F::ZERO;
        }

        // SIMD width: number of field elements processed in parallel.
        // Each SIMD lane corresponds to one candidate witness.
        let lanes = F::Packing::WIDTH;

        // Total number of batches needed to cover all field elements.
        // Each batch tests `lanes` witnesses in parallel.
        let num_batches = F::ORDER_U64.div_ceil(lanes as u64);

        // Cache the field order.
        let order = F::ORDER_U64;

        // Bitmask used to check the PoW condition. eg. bits = 3 => mask = 0b111
        // We accept a witness if (sample & mask) == 0. This verifies 'bits' trailing zeros.
        let mask = (1u64 << bits) - 1;

        // In a duplex sponge, new inputs are absorbed sequentially at indices [0, 1, 2, ...].
        // The grinding witness is therefore absorbed at the next available position.
        let witness_idx = self.input_buffer.len();

        // Build the sponge state as packed field elements (SIMD vectors).
        //
        // The current transcript is split across:
        // - `input_buffer`: recently observed transcript elements that have not yet been permuted
        // - `sponge_state`: the internal sponge state after previous permutations
        //
        // Logically, the next permutation would act on:
        //   [input_buffer || sponge_state]
        //
        // This is invariant across batches, so we compute it once.
        let base_packed_state: [_; WIDTH] = core::array::from_fn(|i| {
            if i < self.input_buffer.len() {
                // Broadcast buffered transcript elements (input_buffer) to all SIMD lanes.
                F::Packing::from(self.input_buffer[i])
            } else {
                // Broadcast existing sponge state (sponge_state) to all SIMD lanes.
                F::Packing::from(self.sponge_state[i])
            }
        });

        // Grinding is implemented via parallel brute-force search over candidate witnesses.
        //
        // For efficiency, the search is vectorized using SIMD:
        // It is semantically equivalent to serially trying witnesses until the PoW condition is met.
        //
        // - Each SIMD lane corresponds to a distinct candidate witness
        // - All lanes share the same transcript prefix
        // - A single permutation evaluates multiple candidates in parallel
        // DREGG DELTA: `find_map_first`, not upstream's `find_map_any` — the lowest matching
        // batch, whose inner `Iterator::find` already takes the lowest matching lane, so the
        // witness is the global minimum candidate and does not depend on thread scheduling or on
        // `F::Packing::WIDTH`.
        let witness = (0..num_batches)
            .into_par_iter()
            .find_map_first(|batch| {
                // Compute the starting candidate for this batch.
                //
                // Each batch processes `F::Packing::WIDTH` candidates:
                //   - Batch 0 -> candidates [0, 1, ..., F::Packing::WIDTH - 1]
                //   - Batch 1 -> candidates [F::Packing::WIDTH, ..., 2 * F::Packing::WIDTH - 1]
                //   - Batch k -> candidates [k * F::Packing::WIDTH, ..., (k+1) * F::Packing::WIDTH - 1]
                let base = batch * lanes as u64;

                // Start with a copy of the precomputed base state.
                let mut packed_state = base_packed_state;

                // Generate SIMD-packed candidate witnesses.
                // Each lane receives a distinct field element.
                //   [base + 0, base + 1, ..., base + F::Packing::WIDTH - 1]
                let packed_witnesses = F::Packing::from_fn(|lane| {
                    let candidate = base + lane as u64;
                    if candidate < order {
                        // SAFETY: candidate < field order, so this is a valid canonical field element.
                        unsafe { F::from_canonical_unchecked(candidate) }
                    } else {
                        // Values outside the field order can never satisfy PoW, so we repeat the last potential witness
                        F::NEG_ONE
                    }
                });

                // Insert the candidate witnesses at the next absorption position.
                //
                // This simulates absorbing `transcript || witness` before the Fiat–Shamir challenge is derived.
                packed_state[witness_idx] = packed_witnesses;

                // Apply the cryptographic permutation (SIMD version)
                //
                // This permutes all `lanes` candidates simultaneously.
                self.permutation.permute_mut(&mut packed_state);

                // Check each lane for the PoW condition
                //
                // - In a duplex sponge, output is read from position [RATE-1] (last rate element).
                // - We check if the low `bits` of each sample are all zeros.
                //
                // We scan SIMD lanes to find the first candidate whose output satisfies the PoW condition.
                packed_state[RATE - 1]
                    .as_slice()
                    .iter()
                    .zip(packed_witnesses.as_slice())
                    .find(|(sample, _)| {
                        // Accept if the low `bits` bits are all zero.
                        (sample.as_canonical_u64() & mask) == 0
                    })
                    .map(|(_, &witness)| witness)
            })
            .expect("failed to find proof-of-work witness");

        // Double-check the witness using the standard verifier logic and update the challenger state.
        assert!(self.check_witness(bits, witness));

        witness
    }
}

impl<F, P, const WIDTH: usize, const RATE: usize> UniformGrindingChallenger
    for DuplexChallenger<F, P, WIDTH, RATE>
where
    F: UniformSamplingField + PrimeField64,
    P: CryptographicPermutation<[F; WIDTH]>
        + CryptographicPermutation<[<F as Field>::Packing; WIDTH]>,
{
    #[instrument(name = "grind uniform for proof-of-work witness", skip_all)]
    fn grind_uniform(&mut self, bits: usize) -> Self::Witness {
        // Call the generic grinder with the "resample" checking logic.
        self.grind_generic(bits, |challenger, witness| {
            challenger.check_witness_uniform(bits, witness)
        })
    }
    #[instrument(name = "grind uniform may error for proof-of-work witness", skip_all)]
    fn grind_uniform_may_error(&mut self, bits: usize) -> Self::Witness {
        // Call the generic grinder with the "error" checking logic.
        self.grind_generic(bits, |challenger, witness| {
            challenger.check_witness_uniform_may_error(bits, witness)
        })
    }
}
impl<F, P, const WIDTH: usize, const RATE: usize> DuplexChallenger<F, P, WIDTH, RATE>
where
    F: PrimeField64,
    P: CryptographicPermutation<[F; WIDTH]>,
{
    /// A generic, private helper for PoW grinding, parameterized by the checking function.
    fn grind_generic<CHECK>(&mut self, bits: usize, check_fn: CHECK) -> F
    where
        CHECK: Fn(&mut Self, F) -> bool + Sync + Send,
    {
        // Maybe check that bits is greater than 0?
        assert!(bits < (usize::BITS as usize), "bit count must be valid");
        assert!(
            (1u64 << bits) < F::ORDER_U64,
            "bit count exceeds field order"
        );
        // The core parallel brute-force search logic.
        let witness = (0..F::ORDER_U64)
            .into_par_iter()
            .map(|i| unsafe {
                // This is safe as i is always in range.
                F::from_canonical_unchecked(i)
            })
            // DREGG DELTA: `find_first`, not upstream's `find_any`.
            .find_first(|&witness| check_fn(&mut self.clone(), witness))
            .expect("failed to find proof-of-work witness");
        // Run the check one last time on the *original* challenger to update its state
        // and confirm the witness is valid.
        assert!(check_fn(self, witness));
        witness
    }
}

impl<F, PF, P, const WIDTH: usize, const RATE: usize> GrindingChallenger
    for MultiField32Challenger<F, PF, P, WIDTH, RATE>
where
    F: PrimeField32,
    PF: PrimeField,
    P: CryptographicPermutation<[PF; WIDTH]>,
{
    type Witness = F;

    #[instrument(name = "grind for proof-of-work witness", skip_all)]
    fn grind(&mut self, bits: usize) -> Self::Witness {
        assert!(bits < (usize::BITS as usize), "bit count must be valid");
        assert!((1 << bits) < F::ORDER_U32);

        // Trivial case: 0 bits mean no PoW is required and any witness is valid.
        if bits == 0 {
            return F::ZERO;
        }

        let witness = (0..F::ORDER_U32)
            .into_par_iter()
            .map(|i| unsafe {
                // i < F::ORDER_U32 by construction so this is safe.
                F::from_canonical_unchecked(i)
            })
            // DREGG DELTA: `find_first`, not upstream's `find_any`. This is the OUTER (BN254)
            // config's challenger, so it is the one the apex/shrink byte-parity gates ride on.
            .find_first(|witness| self.clone().check_witness(bits, *witness))
            .expect("failed to find witness");
        assert!(self.check_witness(bits, witness));
        witness
    }
}
