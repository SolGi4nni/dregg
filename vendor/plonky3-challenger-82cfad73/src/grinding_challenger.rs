use p3_field::{Field, PackedValue, PrimeField, PrimeField32, PrimeField64};
use p3_maybe_rayon::prelude::*;
use p3_symmetric::CryptographicPermutation;
use tracing::instrument;

use crate::{
    CanObserve, CanSampleBits, CanSampleUniformBits, DuplexChallenger, MultiField32Challenger,
    UniformSamplingField,
};

// ═════════════════════════════════════════════════════════════════════════════════════════════
// ⚑ DREGG DELTA vs Plonky3 82cfad73 — the only edits in this vendored crate, both in the PoW
// grind and neither of them touching what the verifier checks. DELTA 1 (2026-08-02) fixed WHICH
// valid witness is returned; DELTA 2 (2026-08-14) fixed the SCHEDULE that finds it, and returns
// DELTA 1's witness exactly.
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
//
// ─────────────────────────────────────────────────────────────────────────────────────────────
// ⚑ DELTA 2 (2026-08-14) — THE SCHEDULE. `find_first` KEPT ITS ANSWER AND LOST ITS PARALLELISM.
//
// `find_first` must prove NO LOWER candidate exists, so rayon's `full()` fires only for a worker
// whose lower bound already exceeds the best index found. The answer lives at candidate
// `w ≈ 2^bits`, i.e. in the first ~0.003% of a `2^31`-wide range, and rayon's splitter is
// thief-driven: the other workers are never idle (each is grinding its own multi-million-batch
// subrange and will not abort until a LOWER match is published), so nobody steals into the low
// chunk. The worker that owns index 0 walks `0 -> w` essentially alone.
//
// MEASURED (`breadstuffs/circuit/tests/grind_phase_measure.rs` §G3, 2026-08-13, one fixed
// transcript, `crit` = max batches scanned by any ONE worker = the permutations on the critical
// path, a contention-free instrument): **20,766 batches at 1 thread and 20,766 at 12 threads.
// Scale 1.00.** Wall clock got WORSE (24.4 -> 28.9 ms) while total work rose 5.9x, because the
// eleven other workers contend for memory bandwidth and every match they publish loses the `min`.
//
// The fix is a WINDOWED PARALLEL MIN, and it is a pure scheduling change:
//
//     scan `0..span` in contiguous ascending windows; inside a window take the match with the
//     LOWEST unit index (a complete scan, no early exit, so it splits perfectly across T
//     threads); return on the first non-empty window.
//
// ⚑ WHY THE WITNESS IS BYTE-FOR-BYTE THE SAME, and it is an equality, not an approximation.
// Windows are contiguous and ascending, so every unit before the first non-empty window produced
// `None`. `find_map_first` returns the value of the lowest unit producing `Some`; that unit lies
// in the first non-empty window; and `min_by_key(unit)` over that window returns exactly that
// unit's value. So `windowed(span, w) == find_map_first(0..span)` FOR EVERY WINDOW SIZE `w >= 1`
// — the window is a schedule parameter that cannot reach the answer. Same predicate, same
// witness, same Fiat-Shamir transcript, same query indices, same proof bytes, same VK.
// `dregg-circuit`'s `grind_windowed_min_is_byte_identical` sweeps eleven window sizes against the
// deployed `grind` and `grind_proof_bytes_are_identical_under_the_windowed_schedule` asserts the
// SERIALIZED PROOFS are equal, rather than arguing it.
//
// The price is the tunable part: a window covering `c * 2^bits` candidates is empty with
// probability `e^(-c)`, so expected total work is `c / (1 - e^(-c))` times the mean draw
// (`c = 1/4` => 1.13x) while the critical path falls by ~T. See `GRIND_WINDOW_C_NUM/DEN`.
// ═════════════════════════════════════════════════════════════════════════════════════════════

/// Window size as a fraction of the expected draw `2^bits`: `c = NUM / DEN`.
///
/// A window covers `c * 2^bits` candidates, so it is empty with probability `e^(-c)` and the
/// expected number of windows is `1 / (1 - e^(-c))`. The two effects pull opposite ways:
///
/// * **small `c`** — less wasted work (`c / (1 - e^(-c))` -> 1 as `c -> 0`) and a shorter critical
///   path, but more rayon joins (`~1/c` of them), so the per-window barrier eventually dominates;
/// * **large `c`** — fewer joins and, at `c = 8`, literally fixed work (one window over 64 draws,
///   measured), but a proportionally larger constant cost.
///
/// ⚑ **Every EXACT column says smaller `c` is better, monotonically** — over 512 draws at `T = 12`
/// the mean critical path is `0.087 / 0.089 / 0.094 / 0.106` of the old path's at
/// `c = 1/16, 1/8, 1/4, 1/2`, and total work is `1.032 / 1.063 / 1.126 / 1.267`. The only thing
/// opposing `c -> 0` is the per-window rayon barrier, and a barrier is **invisible to an operation
/// count**, so it was measured on its own (96 tasks on 12 threads, no work in them, min of 4096:
/// **7.1 us**) and the latency derived from the exact counts rather than benchmarked.
///
/// `c = 1/4` is the **minimax** choice across the uncertainty in that one measured constant, not
/// the argmin at its measured value: `c = 1/8` wins by 3% if a barrier really costs 7.1 us, and
/// loses everywhere above ~2x that, while `c = 1/4` is within 6% of the best across a 10x range.
/// It costs **1.126x** the expected total work (so a serial/1-thread grind regresses ~13%), holds
/// the barrier to **3.1%** of a window, and puts the window at `2^bits / 4` candidates = 4,096
/// batches at the deployed `bits = 16`.
///
/// ⚠ A whole-grind wall clock cannot pick this parameter on a contended box and was not allowed to:
/// across two runs at load 24 and load 62 the timed column moved its own minimum from `c = 1/4` to
/// `c = 2`. `grind_phase_measure.rs` §G3 ⑤ prints both so the disagreement stays visible.
const GRIND_WINDOW_C_NUM: u64 = 1;
const GRIND_WINDOW_C_DEN: u64 = 4;

/// Never window below this many units. Only binds for tiny `bits` (where the whole grind is
/// microseconds anyway) and keeps a window from degenerating into a barrier per handful of work.
const GRIND_WINDOW_MIN_UNITS: u64 = 64;

/// How many rayon tasks each worker should have available per window. Splitting a window into
/// `threads * this` chunks up front is what turns "a complete parallel scan" from an aspiration
/// into a division of labour — see `windowed_find_map_first`.
const GRIND_TASKS_PER_WORKER: u64 = 8;

/// The default window, in *units* (a unit is one SIMD batch for `DuplexChallenger`, one candidate
/// for every other grinder), for a grind of `bits` bits at `candidates_per_unit` candidates a unit.
#[inline]
pub const fn default_grind_window(bits: usize, candidates_per_unit: u64) -> u64 {
    // `bits < 64` is asserted by every caller before this point.
    let expected = 1u64 << bits;
    let per_unit = if candidates_per_unit == 0 {
        1
    } else {
        candidates_per_unit
    };
    let units = expected.saturating_mul(GRIND_WINDOW_C_NUM) / (GRIND_WINDOW_C_DEN * per_unit);
    if units < GRIND_WINDOW_MIN_UNITS {
        GRIND_WINDOW_MIN_UNITS
    } else {
        units
    }
}

/// Scan `0..span` in contiguous ascending windows of `window` units and return the value produced
/// by the **lowest** unit that produces one — i.e. exactly `find_map_first(0..span)`, on a
/// schedule that parallelises.
///
/// Each window is a COMPLETE parallel scan with no early exit, reduced by minimum unit index, so
/// it saturates the pool; the search stops at the first non-empty window. See this module's
/// `DELTA 2` block for why the result is independent of `window`.
///
/// ⚑ **The window is split EAGERLY, and it has to be.** `rayon::range` gives `Range<u64>` an
/// **unindexed** producer (`u64`/`i64`/`u128`/`i128` all are), which halves only when a worker goes
/// idle and steals. On a loaded box the steal does not arrive, one worker walks a long contiguous
/// run of the window, and the critical path stops falling with `T` — MEASURED here at **9,942 of
/// 24,576 batches on a single worker at `T = 12`**, against 2,048 for an even division. Iterating
/// the window as a `usize` range makes it **indexed**, which is what `with_max_len` needs in order
/// to force the split up front instead of hoping for it. That is a schedule detail and, like the
/// window itself, cannot reach the answer.
#[inline]
pub fn windowed_find_map_first<T, S>(span: u64, window: u64, scan: S) -> Option<T>
where
    T: Send,
    S: Fn(u64) -> Option<T> + Sync + Send,
{
    // A zero window would not advance; a window wider than the span is just one window.
    //
    // ⚑ The `usize` clamp is load-bearing on a 32-bit target and a no-op on a 64-bit one. The
    // window is iterated as a `usize` range (that is what makes it INDEXED, see above), so a
    // window wider than `usize::MAX` would TRUNCATE, silently skip candidates, and could return a
    // non-minimal witness — the one way this schedule could reach the answer. `default_grind_window`
    // returns up to `2^61` for a 64-bit field, so the bound is reachable in principle.
    let window = window.max(1).min(span.max(1)).min(usize::MAX as u64);
    let threads = current_num_threads().max(1) as u64;
    let mut lo = 0u64;
    while lo < span {
        let hi = (lo + window).min(span);
        let len = hi - lo;
        // Enough tasks that every worker has slack to steal from, without the per-task overhead
        // mattering: a chunk here is thousands of permutations even at the deployed window.
        let chunk = len
            .div_ceil(threads.saturating_mul(GRIND_TASKS_PER_WORKER).max(1))
            .max(1)
            .min(usize::MAX as u64) as usize;
        let hit = (0..len as usize)
            .into_par_iter()
            .with_max_len(chunk)
            .filter_map(|k| {
                let unit = lo + k as u64;
                scan(unit).map(|found| (unit, found))
            })
            .min_by_key(|&(unit, _)| unit);
        if let Some((_, found)) = hit {
            return Some(found);
        }
        lo = hi;
    }
    None
}

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
        self.grind_with_window(
            bits,
            default_grind_window(bits.min(63), F::Packing::WIDTH as u64),
        )
    }
}

impl<F, P, const WIDTH: usize, const RATE: usize> DuplexChallenger<F, P, WIDTH, RATE>
where
    F: PrimeField64,
    P: CryptographicPermutation<[F; WIDTH]>
        + CryptographicPermutation<[<F as Field>::Packing; WIDTH]>,
{
    /// [`GrindingChallenger::grind`] with the search window stated explicitly, in SIMD batches.
    ///
    /// ⚑ **The window is a SCHEDULE parameter and cannot reach the answer**: this returns the
    /// globally minimal valid witness for every `window >= 1`, identically to upstream's
    /// `find_map_first`. It is public so that a test can sweep windows against the deployed
    /// `grind` and assert the equality on real proof bytes, rather than a paraphrase of this
    /// function doing so beside it.
    pub fn grind_with_window(&mut self, bits: usize, window: u64) -> F {
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
        //
        // DREGG DELTA 1: the LOWEST matching batch wins, whose inner `Iterator::find` already
        // takes the lowest matching lane, so the witness is the global minimum candidate and does
        // not depend on thread scheduling or on `F::Packing::WIDTH`.
        //
        // DREGG DELTA 2: that minimum is computed by a WINDOWED PARALLEL MIN rather than by
        // rayon's `find_map_first`, which was measured at scale 1.00 across 12 threads. Same
        // witness, same bytes; see the module's `DELTA 2` block.
        let witness = windowed_find_map_first(num_batches, window, |batch| {
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
        //
        // DREGG DELTA 1: the LOWEST valid candidate, not upstream's `find_any`.
        // DREGG DELTA 2: computed by a windowed parallel min, so the search actually divides
        // across the pool. Identical answer for every window; see the module's `DELTA 2` block.
        let witness = windowed_find_map_first(F::ORDER_U64, default_grind_window(bits, 1), |i| {
            // SAFETY: `i < F::ORDER_U64` by construction.
            let witness = unsafe { F::from_canonical_unchecked(i) };
            check_fn(&mut self.clone(), witness).then_some(witness)
        })
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
        self.grind_with_window(bits, default_grind_window(bits.min(63), 1))
    }
}

impl<F, PF, P, const WIDTH: usize, const RATE: usize> MultiField32Challenger<F, PF, P, WIDTH, RATE>
where
    F: PrimeField32,
    PF: PrimeField,
    P: CryptographicPermutation<[PF; WIDTH]>,
{
    /// [`GrindingChallenger::grind`] with the search window stated explicitly, in candidates.
    ///
    /// ⚑ This is the OUTER (BN254) path, and it is where the absolute milliseconds are largest:
    /// it is neither SIMD-packed nor batched, so **one candidate costs one whole BN254 Poseidon2
    /// duplex** — roughly two orders of magnitude more than a BabyBear packed permutation ÷ 4
    /// lanes. It carried exactly the same `find_first` pathology as the inner grind.
    ///
    /// The window is a schedule parameter and cannot reach the answer: the returned witness is the
    /// globally minimal valid one for every `window >= 1`.
    pub fn grind_with_window(&mut self, bits: usize, window: u64) -> F {
        assert!(bits < (usize::BITS as usize), "bit count must be valid");
        assert!((1 << bits) < F::ORDER_U32);

        // Trivial case: 0 bits mean no PoW is required and any witness is valid.
        if bits == 0 {
            return F::ZERO;
        }

        // DREGG DELTA 1: the LOWEST valid candidate, not upstream's `find_any` — this is the
        // challenger the apex/shrink byte-parity gates ride on.
        // DREGG DELTA 2: found by a windowed parallel min, so the search divides across the pool.
        let witness = windowed_find_map_first(u64::from(F::ORDER_U32), window, |i| {
            // SAFETY: `i < F::ORDER_U32` by construction.
            let witness = unsafe { F::from_canonical_unchecked(i as u32) };
            self.clone().check_witness(bits, witness).then_some(witness)
        })
        .expect("failed to find witness");
        assert!(self.check_witness(bits, witness));
        witness
    }
}
