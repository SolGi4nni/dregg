//! # §G — EXACT FIELD-OPERATION COUNTS FOR THE IR-v2 PROVER — the missing half of the instrument.
//!
//! `ir2_phase_profile.rs` §D counts Poseidon2 permutations exactly. It has no counterpart on the
//! arithmetic side, so `docs/COST-MODEL.md`'s central claim — *"the prover is hash-bound at every
//! feasible blowup"* — rests on comparing an EXACT count against a CONTENDED wall clock. That
//! comparison is not sound: hash work is a large-buffer traversal (memory-bound) and field
//! arithmetic is cache-resident (compute-bound), so the two degrade at DIFFERENT rates under load,
//! and `hash/arith` is precisely the quantity a busy box corrupts most. This file supplies the
//! arithmetic count so the comparison can be made in one contention-immune unit.
//!
//! ## ⚑ WHY THE OBVIOUS INSTRUMENT DOES NOT WORK, and what replaces it
//!
//! The obvious move — mirror §D by wrapping `BabyBear` in a counting newtype and proving under a
//! config over it — **cannot reach this prover.** `prove_vm_descriptor2_for_config` carries
//! `Domain<SC>: PolynomialSpace<Val = P3BabyBear>`, and its trace argument is `&[Vec<BabyBear>]`
//! produced by monomorphic witness generation (`generate_effect_vm_trace`, the Poseidon2 chip
//! lanes, the heap-root and mem-boundary builders). The AIR itself IS field-generic
//! (`impl<AB> Air<AB> for Ir2Air where AB::F: PrimeField32`); the *witness* is not. Making it
//! generic is a real refactor of deployed code, and this lane does not move deployed types — for
//! the same reason §D did not.
//!
//! What IS substitutable, at zero cost to deployed types, is the **`Dft` type parameter of
//! `TwoAdicFriPcs<Val, Dft, InputMmcs, FriMmcs, Fold>`**. It is a free parameter over
//! `TwoAdicSubgroupDft<Val>`, exactly as the permutation was a free parameter of the hash/compress
//! types. So the same sidestep applies one seam over: a caller-supplied config whose ONLY
//! difference is a **recording** DFT.
//!
//! That matters more than it sounds, because of where the arithmetic is. From the §A per-phase
//! table at b=6, the arithmetic phases are
//!
//! | phase | ms | share of arith |
//! |---|---:|---:|
//! | LDE quotient-eval | 12.925 | 50% |
//! | LDE commit | 7.710 | 30% |
//! | open arith (quotient reduce) | 3.545 | 14% |
//! | quotient eval | 1.283 | 5% |
//! | lookup perm | 0.246 | 1% |
//! | FRI fold | 0.072 | 0.3% |
//!
//! **80% of the prover's arithmetic is DFT**, and the DFT is reached entirely through the `Dft`
//! seam. So the plan is: count the DFT exactly, and derive the remainder from source with the
//! derivation checked against a counted case.
//!
//! ## The method, in three parts
//!
//! 1. **Record.** [`RecordingDft`] implements `TwoAdicSubgroupDft<P3BabyBear>` by delegating every
//!    method to a real `Radix2DitParallel<P3BabyBear>`, logging `(method, height, width,
//!    added_bits, shift)` for each call. The proof produced is bit-identical to the deployed one;
//!    the recorder adds a `Vec::push` per DFT call (call counts are in the dozens).
//! 2. **Replay.** The recorded call sequence is replayed IN ORDER against a
//!    `Radix2DitParallel<CountedBabyBear>` — [`CountedBabyBear`] being a `repr(transparent)`
//!    newtype over `BabyBear` whose `Add`/`Sub`/`Mul`/`Neg`/`try_inverse` bump global counters.
//!    Replay order is preserved because the DFT memoises twiddle tables: replaying out of order,
//!    or with a fresh instance per call, would charge twiddle construction repeatedly and
//!    over-count. One `Radix2DitParallel<CountedBabyBear>` per configuration point, same as the
//!    prover has one per config.
//! 3. **Derive** the non-DFT arithmetic from the (vendored, readable) source, and check the
//!    derivation shape against counted DFT cases — see [`dft_derivation_check`].
//!
//! ### Why replay is sound: the DFT has no data-dependent branch
//!
//! Replay uses matrices of the recorded DIMENSIONS filled with an arbitrary pattern, not the real
//! values. That is exact because `Radix2DitParallel`'s op count is a function of `(h, w,
//! added_bits)` alone: every branch in `first_half`/`second_half`/`coset_dft` is on a layer index
//! or a twiddle POSITION (`dit_layer_twiddle_free` fires at layer 0 and at the first row-pair of
//! each block — structural, not a value test), never on a trace value. The one value-dependent
//! path in the whole file is `try_inverse`'s zero check, which the DFT reaches only with
//! `shift.inverse()` and `F::from_int(h).try_inverse()` — both non-zero constants that replay
//! reproduces exactly, since the shift is recorded as its canonical `u32`.
//!
//! ## ⚑⚑ SCALAR-EQUIVALENT, NOT INSTRUCTIONS — the choice, and what it costs
//!
//! **Every count in this file is a SCALAR-EQUIVALENT operation count: the number of BabyBear
//! multiplications/additions the ALGORITHM performs, independent of how many the machine issues
//! per instruction.**
//!
//! It is scalar-equivalent *by construction*, not by convention: `CountedBabyBear::Packing` is
//! `Self` (via plonky3's `unsafe impl<T: Packable> PackedValue for T`, WIDTH = 1), so the packed
//! paths in `p3-dft`'s butterflies — `F::Packing::pack_slice_with_suffix_mut(row)` — degrade to
//! width-1 packs and every lane is counted individually. Crucially this does NOT change the
//! algorithm: a butterfly is applied to every element of every row-pair either way, so the
//! width-1 replay and the NEON width-4 deployed run do the *same* scalar-equivalent work.
//!
//! This is the same unit §D already reports for permutations ("scalar-equivalent; a packed
//! `permute_mut` adds `Packing::WIDTH`"). **The two instruments therefore compose in one unit,
//! which is the entire point.**
//!
//! **The consequence, stated because it is the whole reason wall clock and op count diverge:** a
//! scalar-equivalent count is a measure of WORK, not of instructions and not of latency. On this
//! box `<BabyBear as Field>::Packing` is `PackedMontyField31Neon` (WIDTH = 4), so the deployed
//! prover issues roughly one instruction per 4 counted multiplies wherever the path vectorises —
//! and the FRI/Merkle side vectorises too (§D: the Merkle build and the PoW grind are both packed;
//! only the challenger's duplexing is scalar). **A count in this file may NOT be converted to
//! milliseconds by multiplying by a scalar-latency rate.** The conversion constant that is allowed
//! is the packed-path *lane* rate, and [`conversion_rate_microbenchmark`] measures both sides of
//! the exchange in exactly that unit so the ratio is apples-to-apples.
//!
//! The instruction-count question is a different question, and it has a different answer: divide
//! each phase's scalar-equivalent count by the SIMD width of the path that executes it. Both are
//! reported. The work count is the one that is hardware-free and reproducible; the instruction
//! count is a property of this box's NEON width.
//!
//! ## Runs
//!
//! ```text
//! cargo test -p dregg-circuit --release --test ir2_field_op_counts -- --nocapture --test-threads=1
//! ```
//! Release only. The counters are relaxed `fetch_add`s on shared cache lines, so **this run's
//! timings are meaningless and none are reported** — same discipline as §D.

use std::cell::RefCell;
use std::fmt::{self, Debug, Display, Formatter};
use std::iter::{Product, Sum};
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

use p3_baby_bear::{BabyBear as P3BabyBear, default_babybear_poseidon2_16};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::{Radix2DitParallel, TwoAdicSubgroupDft};
use p3_field::extension::BinomialExtensionField;
use p3_field::{
    BasedVectorSpace, Field, Packable, PackedValue, PrimeCharacteristicRing, PrimeField32,
    PrimeField64, RawDataSerializable, TwoAdicField,
};
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_matrix::Matrix;
use p3_matrix::bitrev::BitReversedMatrixView;
use p3_matrix::dense::{RowMajorMatrix, RowMajorMatrixViewMut};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::StarkConfig;
use serde::{Deserialize, Serialize};

use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, UMemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2_for_config,
};
use dregg_circuit::effect_vm::{CellState, Effect, generate_effect_vm_trace};
use dregg_circuit::effect_vm_descriptors::descriptor2_for_key;
use dregg_circuit::field::BabyBear;

// ─────────────────────────────────────────────────────────────────────────────
// THE COUNTERS
// ─────────────────────────────────────────────────────────────────────────────

/// Scalar-equivalent BabyBear multiplications. Bumped by `Mul`, `MulAssign` and `Div` (a division
/// is one inverse plus one multiply and is charged as both).
static MULS: AtomicU64 = AtomicU64::new(0);
/// Scalar-equivalent additions.
static ADDS: AtomicU64 = AtomicU64::new(0);
/// Scalar-equivalent subtractions. Kept apart from `ADDS` because a BabyBear subtract and add are
/// the same cost but a reader deriving a butterfly count needs to see them separately.
static SUBS: AtomicU64 = AtomicU64::new(0);
/// Negations.
static NEGS: AtomicU64 = AtomicU64::new(0);
/// `try_inverse` calls. NOT decomposed into multiplies: BabyBear's inverse is a hand-written
/// addition chain, so it is counted as an event and priced separately in
/// [`conversion_rate_microbenchmark`]. Batch inversion's Montgomery-trick multiplies DO go through
/// `Mul` and are counted there, so this stays small by construction.
static INVS: AtomicU64 = AtomicU64::new(0);

fn reset_counters() {
    MULS.store(0, Ordering::Relaxed);
    ADDS.store(0, Ordering::Relaxed);
    SUBS.store(0, Ordering::Relaxed);
    NEGS.store(0, Ordering::Relaxed);
    INVS.store(0, Ordering::Relaxed);
}

#[derive(Default, Clone, Copy, PartialEq, Eq, Debug)]
struct OpCounts {
    mul: u64,
    add: u64,
    sub: u64,
    neg: u64,
    inv: u64,
}

impl OpCounts {
    fn read() -> Self {
        Self {
            mul: MULS.load(Ordering::Relaxed),
            add: ADDS.load(Ordering::Relaxed),
            sub: SUBS.load(Ordering::Relaxed),
            neg: NEGS.load(Ordering::Relaxed),
            inv: INVS.load(Ordering::Relaxed),
        }
    }
    fn since(base: Self) -> Self {
        let now = Self::read();
        Self {
            mul: now.mul - base.mul,
            add: now.add - base.add,
            sub: now.sub - base.sub,
            neg: now.neg - base.neg,
            inv: now.inv - base.inv,
        }
    }
    fn add_in(&mut self, o: Self) {
        self.mul += o.mul;
        self.add += o.add;
        self.sub += o.sub;
        self.neg += o.neg;
        self.inv += o.inv;
    }
    /// Total scalar-equivalent field operations, inverses excluded (they are priced separately).
    fn total_linear(&self) -> u64 {
        self.mul + self.add + self.sub + self.neg
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE COUNTING FIELD
//
// `repr(transparent)` over `BabyBear`. Every trait method that plonky3 provides a DEFAULT for is
// LEFT at its default on purpose: the defaults decompose into `Add`/`Sub`/`Mul`/`Neg`, which are
// the counted primitives. Delegating e.g. `square` or `double` to the inner BabyBear would make
// them cost zero, which is exactly the blindness this file exists to remove.
// ─────────────────────────────────────────────────────────────────────────────

#[derive(
    Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize, Deserialize,
)]
#[repr(transparent)]
struct CountedBabyBear(P3BabyBear);

impl Display for CountedBabyBear {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl Add for CountedBabyBear {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        ADDS.fetch_add(1, Ordering::Relaxed);
        Self(self.0 + rhs.0)
    }
}
impl AddAssign for CountedBabyBear {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}
impl Sub for CountedBabyBear {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        SUBS.fetch_add(1, Ordering::Relaxed);
        Self(self.0 - rhs.0)
    }
}
impl SubAssign for CountedBabyBear {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}
impl Neg for CountedBabyBear {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        NEGS.fetch_add(1, Ordering::Relaxed);
        Self(-self.0)
    }
}
impl Mul for CountedBabyBear {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        MULS.fetch_add(1, Ordering::Relaxed);
        Self(self.0 * rhs.0)
    }
}
impl MulAssign for CountedBabyBear {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}
impl Div for CountedBabyBear {
    type Output = Self;
    #[inline]
    fn div(self, rhs: Self) -> Self {
        // One inverse plus one multiply; both are charged.
        self * rhs.inverse()
    }
}
impl DivAssign for CountedBabyBear {
    #[inline]
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}
impl Sum for CountedBabyBear {
    #[inline]
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        // `reduce`, not `fold(ZERO)`: an n-term sum is n-1 additions, not n.
        iter.reduce(|a, b| a + b).unwrap_or(Self::ZERO)
    }
}
impl Product for CountedBabyBear {
    #[inline]
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|a, b| a * b).unwrap_or(Self::ONE)
    }
}

impl PrimeCharacteristicRing for CountedBabyBear {
    // The prime subfield is the REAL BabyBear, not `Self`. That is what lets this type skip
    // `PrimeField`/`QuotientMap` entirely: integer injections land in the subfield (uncounted, as
    // they are in the deployed prover — they are compile-time constants or index arithmetic, not
    // field multiplications) and are lifted by `from_prime_subfield`.
    type PrimeSubfield = P3BabyBear;

    const ZERO: Self = Self(P3BabyBear::ZERO);
    const ONE: Self = Self(P3BabyBear::ONE);
    const TWO: Self = Self(P3BabyBear::TWO);
    const NEG_ONE: Self = Self(P3BabyBear::NEG_ONE);

    #[inline]
    fn from_prime_subfield(f: Self::PrimeSubfield) -> Self {
        Self(f)
    }
}

impl Packable for CountedBabyBear {}

impl RawDataSerializable for CountedBabyBear {
    const NUM_BYTES: usize = <P3BabyBear as RawDataSerializable>::NUM_BYTES;
    #[inline]
    fn into_bytes(self) -> impl IntoIterator<Item = u8> {
        self.0.into_bytes()
    }
}

impl Field for CountedBabyBear {
    // WIDTH = 1 via plonky3's blanket `unsafe impl<T: Packable> PackedValue for T`. This is what
    // makes every count in this file scalar-equivalent by construction — see the module header.
    type Packing = Self;

    const GENERATOR: Self = Self(P3BabyBear::GENERATOR);

    #[inline]
    fn try_inverse(&self) -> Option<Self> {
        INVS.fetch_add(1, Ordering::Relaxed);
        self.0.try_inverse().map(Self)
    }

    fn order() -> num_bigint::BigUint {
        P3BabyBear::order()
    }
}

impl TwoAdicField for CountedBabyBear {
    const TWO_ADICITY: usize = <P3BabyBear as TwoAdicField>::TWO_ADICITY;
    #[inline]
    fn two_adic_generator(bits: usize) -> Self {
        Self(P3BabyBear::two_adic_generator(bits))
    }
}

// The degree-4 binomial extension over the counting field, so §G4 can count the EXTENSION
// arithmetic — the FRI fold and the open phase run entirely in `BinomialExtensionField<_, 4>`, and
// their cost in BASE multiplies is what has to be added to the DFT count.
//
// ⚠ ONE FIDELITY GAP, MEASURED AND STATED. `MontyField31` overrides
// `BinomiallyExtendableAlgebra::binomial_mul` with `quartic_mul_packed` (`monty-31/src/
// extension.rs`), which precomputes `w·b` (4 multiplies by W) and then does one 4×4 packed dot
// product (16 multiplies) = 20. `CountedBabyBear` has no such override, so it takes the generic
// `quartic_mul`, which shares more subterms: 5+5+5+4 = 19 multiplies. **The counting extension is
// therefore ~5% CHEAPER per extension multiply than the deployed one.** That is the conservative
// direction for a hash-bound claim (it under-states arithmetic), and §G4 prints both so the
// correction is applicable.
impl p3_field::extension::BinomiallyExtendableAlgebra<Self, 4> for CountedBabyBear {}

impl p3_field::extension::BinomiallyExtendable<4> for CountedBabyBear {
    const W: Self = Self(<P3BabyBear as p3_field::extension::BinomiallyExtendable<4>>::W);
    const DTH_ROOT: Self =
        Self(<P3BabyBear as p3_field::extension::BinomiallyExtendable<4>>::DTH_ROOT);
    const EXT_GENERATOR: [Self; 4] = {
        let g = <P3BabyBear as p3_field::extension::BinomiallyExtendable<4>>::EXT_GENERATOR;
        [Self(g[0]), Self(g[1]), Self(g[2]), Self(g[3])]
    };
}

impl p3_field::extension::HasTwoAdicBinomialExtension<4> for CountedBabyBear {
    const EXT_TWO_ADICITY: usize =
        <P3BabyBear as p3_field::extension::HasTwoAdicBinomialExtension<4>>::EXT_TWO_ADICITY;
    fn ext_two_adic_generator(bits: usize) -> [Self; 4] {
        let g = <P3BabyBear as p3_field::extension::HasTwoAdicBinomialExtension<4>>::ext_two_adic_generator(bits);
        [Self(g[0]), Self(g[1]), Self(g[2]), Self(g[3])]
    }
}

/// The counting extension field: what FRI and the open phase actually compute in.
type EfC = BinomialExtensionField<CountedBabyBear, 4>;

// ─────────────────────────────────────────────────────────────────────────────
// THE RECORDING DFT — the substitutable seam
// ─────────────────────────────────────────────────────────────────────────────

/// Which `TwoAdicSubgroupDft` entry point the prover called. Recorded for the record, **not** used
/// as the phase classifier — [`phase_of`] does that from the span path, because the entry point
/// turned out not to distinguish the phases at all:
///
/// - `Pcs::commit` AND `Pcs::get_quotient_ldes` both call `coset_lde_batch`, so the entry point
///   cannot tell a trace commit from a quotient-chunk commit; only the enclosing span can.
/// - `Pcs::get_evaluations_on_domain`'s slow path would call `coset_idft_batch` then
///   `coset_dft_batch` — and **§G1 measures ZERO of both at every blowup.** The fast truncation
///   branch fires every time, so these two variants are never constructed in this workload. They
///   are kept because their absence is the evidence for §G1's finding 1, and a variant that stops
///   being unreachable is something a reader should be able to see.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum DftCall {
    DftBatch,
    CosetDftBatch,
    CosetIdftBatch,
    CosetLdeBatch,
}

/// **The phase label, computed by `ir2_phase_profile.rs`'s OWN predicate** applied to the span path
/// captured at the call — not by a re-derivation of it. That file's classifier reads:
///
/// ```ignore
/// if path.contains("coset_lde_batch") || path.contains("coset_dft") || path.contains("idft") {
///     return Some(if path.contains("compute quotient") {
///         "LDE quotient-eval (arith)"
///     } else {
///         "LDE commit (arith)"
///     });
/// }
/// ```
///
/// so the split is *entirely* on whether the call sits under a `compute quotient` span. Both LDE
/// rows in §A's table are therefore `coset_lde_batch_with_transform` spans; neither is a coset
/// DFT of a re-evaluated trace. See §G1's finding.
fn phase_of(path: &str) -> &'static str {
    if path.contains("compute quotient") {
        "LDE quotient-eval (arith)"
    } else {
        "LDE commit (arith)"
    }
}

#[derive(Clone, Debug)]
struct DftEvent {
    call: DftCall,
    height: usize,
    width: usize,
    added_bits: usize,
    /// Canonical `u32` of the coset shift, so replay reproduces the exact same twiddle tables (and
    /// therefore the exact same memoisation hits) as the recorded run.
    shift: u32,
    /// ⚑ THE ENCLOSING SPAN PATH at the moment of the call, captured by [`PathLayer`]. This is what
    /// makes this file's phase split COMPARABLE to `ir2_phase_profile.rs`'s rather than merely
    /// plausible: that file classifies a DFT span as "LDE quotient-eval" iff its path contains
    /// `compute quotient`, and this records the same predicate at the same call.
    path: String,
}

// ── A minimal span-path tracker. `ir2_phase_profile.rs` needs self-TIME so it carries a full
// frame stack; this needs only the path, so it keeps a `Vec<String>` and reads the top. Same
// mechanism, a tenth of the machinery, and no timing is taken from it.
thread_local! {
    static PATH: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) };
}

struct PathLayer;

impl<S> tracing_subscriber::Layer<S> for PathLayer
where
    S: tracing::Subscriber + for<'a> tracing_subscriber::registry::LookupSpan<'a>,
{
    fn on_enter(&self, id: &tracing::span::Id, ctx: tracing_subscriber::layer::Context<'_, S>) {
        let name = ctx
            .span(id)
            .map(|s| s.name().to_string())
            .unwrap_or_default();
        PATH.with(|p| {
            let mut st = p.borrow_mut();
            let next = match st.last() {
                Some(prev) => format!("{prev}>{name}"),
                None => name,
            };
            st.push(next);
        });
    }
    fn on_exit(&self, _id: &tracing::span::Id, _ctx: tracing_subscriber::layer::Context<'_, S>) {
        PATH.with(|p| {
            p.borrow_mut().pop();
        });
    }
}

fn install_path_layer() {
    use tracing_subscriber::layer::SubscriberExt;
    static ONCE: std::sync::OnceLock<()> = std::sync::OnceLock::new();
    ONCE.get_or_init(|| {
        let sub = tracing_subscriber::registry().with(PathLayer);
        tracing::subscriber::set_global_default(sub).expect("global subscriber");
    });
}

fn current_path() -> String {
    PATH.with(|p| p.borrow().last().cloned().unwrap_or_default())
}

fn dft_log() -> &'static Mutex<Vec<DftEvent>> {
    static L: std::sync::OnceLock<Mutex<Vec<DftEvent>>> = std::sync::OnceLock::new();
    L.get_or_init(|| Mutex::new(Vec::new()))
}

fn record(call: DftCall, height: usize, width: usize, added_bits: usize, shift: P3BabyBear) {
    dft_log().lock().unwrap().push(DftEvent {
        call,
        height,
        width,
        added_bits,
        shift: shift.as_canonical_u32(),
        path: current_path(),
    });
}

/// A `TwoAdicSubgroupDft<P3BabyBear>` that delegates every call to the real
/// `Radix2DitParallel<P3BabyBear>` and logs its shape. The proof it produces is bit-identical to
/// the deployed one — the only added work is a `Vec::push` per call, and DFT calls number in the
/// dozens per proof.
#[derive(Clone, Default, Debug)]
struct RecordingDft {
    inner: Radix2DitParallel<P3BabyBear>,
}

impl TwoAdicSubgroupDft<P3BabyBear> for RecordingDft {
    type Evaluations = BitReversedMatrixView<RowMajorMatrix<P3BabyBear>>;

    fn dft_batch(&self, mat: RowMajorMatrix<P3BabyBear>) -> Self::Evaluations {
        record(
            DftCall::DftBatch,
            mat.height(),
            mat.width(),
            0,
            P3BabyBear::ONE,
        );
        self.inner.dft_batch(mat)
    }

    fn coset_dft_batch(
        &self,
        mat: RowMajorMatrix<P3BabyBear>,
        shift: P3BabyBear,
    ) -> Self::Evaluations {
        record(DftCall::CosetDftBatch, mat.height(), mat.width(), 0, shift);
        self.inner.coset_dft_batch(mat, shift)
    }

    fn coset_idft_batch(
        &self,
        mat: RowMajorMatrix<P3BabyBear>,
        shift: P3BabyBear,
    ) -> RowMajorMatrix<P3BabyBear> {
        record(DftCall::CosetIdftBatch, mat.height(), mat.width(), 0, shift);
        self.inner.coset_idft_batch(mat, shift)
    }

    fn coset_lde_batch_with_transform<T>(
        &self,
        mat: RowMajorMatrix<P3BabyBear>,
        added_bits: usize,
        shift: P3BabyBear,
        transform: T,
    ) -> Self::Evaluations
    where
        T: FnOnce(&mut RowMajorMatrixViewMut<'_, P3BabyBear>, p3_dft::Layout),
    {
        record(
            DftCall::CosetLdeBatch,
            mat.height(),
            mat.width(),
            added_bits,
            shift,
        );
        self.inner
            .coset_lde_batch_with_transform(mat, added_bits, shift, transform)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE REPLAY
// ─────────────────────────────────────────────────────────────────────────────

fn filler_matrix(height: usize, width: usize) -> RowMajorMatrix<CountedBabyBear> {
    // Arbitrary non-zero pattern. The DFT's op count is data-independent (module header), so the
    // values are irrelevant; they are made non-zero and non-constant anyway so that any accidental
    // value-dependent short-circuit would show up as a discrepancy rather than hide.
    let values = (0..height * width)
        .map(|i| {
            CountedBabyBear(P3BabyBear::from_u32(
                (i as u32).wrapping_mul(2_654_435_761) | 1,
            ))
        })
        .collect();
    RowMajorMatrix::new(values, width)
}

/// Replay the recorded call sequence over the counting field, **in order and against a single
/// `Radix2DitParallel<CountedBabyBear>`**, so twiddle-table construction is amortised exactly the
/// way the deployed prover amortises it (one memo map per config, shared across every call).
fn replay(events: &[DftEvent]) -> Vec<(DftEvent, OpCounts)> {
    let dft: Radix2DitParallel<CountedBabyBear> = Radix2DitParallel::default();
    let mut out = Vec::with_capacity(events.len());
    for ev in events {
        let mat = filler_matrix(ev.height, ev.width);
        let shift = CountedBabyBear(P3BabyBear::from_u32(ev.shift));
        let base = OpCounts::read();
        match ev.call {
            DftCall::DftBatch => {
                std::hint::black_box(dft.dft_batch(mat));
            }
            DftCall::CosetDftBatch => {
                std::hint::black_box(dft.coset_dft_batch(mat, shift));
            }
            DftCall::CosetIdftBatch => {
                std::hint::black_box(dft.coset_idft_batch(mat, shift));
            }
            DftCall::CosetLdeBatch => {
                std::hint::black_box(dft.coset_lde_batch(mat, ev.added_bits, shift));
            }
        }
        out.push((ev.clone(), OpCounts::since(base)));
    }
    out
}

// ─────────────────────────────────────────────────────────────────────────────
// THE CONFIG — deployed everything, except the Dft
// ─────────────────────────────────────────────────────────────────────────────

type Pack = <P3BabyBear as Field>::Packing;
type Ef = BinomialExtensionField<P3BabyBear, 4>;
type Perm = p3_baby_bear::Poseidon2BabyBear<16>;
type Hash = PaddingFreeSponge<Perm, 16, 8, 8>;
type Compress = TruncatedPermutation<Perm, 2, 8, 16>;
type ValMmcs = MerkleTreeMmcs<Pack, Pack, Hash, Compress, 2, 8>;
type ChallengeMmcs = ExtensionMmcs<P3BabyBear, Ef, ValMmcs>;
type RecPcs = TwoAdicFriPcs<P3BabyBear, RecordingDft, ValMmcs, ChallengeMmcs>;
type Challenger = DuplexChallenger<P3BabyBear, Perm, 16, 8>;
type RecordingConfig = StarkConfig<RecPcs, Ef, Challenger>;

fn recording_config(log_blowup: usize, num_queries: usize, pow: usize) -> RecordingConfig {
    let perm = default_babybear_poseidon2_16();
    let hash = Hash::new(perm.clone());
    let compress = Compress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress, 0);
    let fri_params = FriParameters {
        log_blowup,
        log_final_poly_len: 0,
        max_log_arity: 3,
        num_queries,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: pow,
        mmcs: ChallengeMmcs::new(val_mmcs.clone()),
    };
    let pcs = TwoAdicFriPcs::new(RecordingDft::default(), val_mmcs, fri_params);
    StarkConfig::new(pcs, Challenger::new(perm))
}

// ─────────────────────────────────────────────────────────────────────────────
// THE WORKLOAD — the SAME real transfer effect §D counted permutations on
// ─────────────────────────────────────────────────────────────────────────────

struct Workload {
    desc: dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    base_trace: Vec<Vec<BabyBear>>,
    pis: Vec<BabyBear>,
}

fn transfer_workload() -> Workload {
    let state = CellState::new(100_000, 0);
    let effects = vec![Effect::Transfer {
        amount: 50,
        direction: 1,
    }];
    let (base_trace, pis) = generate_effect_vm_trace(&state, &effects);
    let v2_json = descriptor2_for_key("transferVmDescriptor2").expect("v2 transfer descriptor");
    let desc = parse_vm_descriptor2(v2_json).expect("v2 transfer descriptor parses");
    let dpis: Vec<BabyBear> = pis[..desc.public_input_count].to_vec();
    Workload {
        desc,
        base_trace,
        pis: dpis,
    }
}

/// Prove once under the recording config and return the DFT call log.
fn record_one(w: &Workload, lb: usize, q: usize, pow: usize) -> Vec<DftEvent> {
    let config = recording_config(lb, q, pow);
    dft_log().lock().unwrap().clear();
    let proof = prove_vm_descriptor2_for_config(
        &w.desc,
        &w.base_trace,
        &w.pis,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &config,
    )
    .expect("recording config proves");
    // Self-verify happens inside; keep the proof alive so nothing is optimised away.
    std::hint::black_box(&proof);
    dft_log().lock().unwrap().clone()
}

// ─────────────────────────────────────────────────────────────────────────────
// §G1 — THE MEASUREMENT
// ─────────────────────────────────────────────────────────────────────────────

/// **§G1 — exact scalar-equivalent field-op counts per phase, per blowup.**
#[test]
fn field_op_counts_per_phase() {
    install_path_layer();
    let w = transfer_workload();
    println!(
        "\n═══ §G1 EXACT SCALAR-EQUIVALENT FIELD-OP COUNTS (deployed SIMD lane width = {}) ═══\n\
         Counting field `Packing = Self` (WIDTH 1) ⇒ every count below is SCALAR-EQUIVALENT WORK,\n\
         the same unit §D reports permutations in. Divide by {} for the NEON instruction count\n\
         wherever the path vectorises. No timings are reported from this run.",
        Pack::WIDTH,
        Pack::WIDTH
    );

    let mut table: Vec<(usize, Vec<(&'static str, OpCounts, u64)>)> = Vec::new();

    for lb in [3usize, 4, 5, 6, 7] {
        let events = record_one(&w, lb, 19, 0);
        reset_counters();
        let per_call = replay(&events);

        // Aggregate by phase, using ir2_phase_profile's own predicate on the captured span path.
        let mut per_phase: std::collections::BTreeMap<&'static str, (OpCounts, u64)> =
            Default::default();
        for (ev, c) in &per_call {
            let e = per_phase.entry(phase_of(&ev.path)).or_default();
            e.0.add_in(*c);
            e.1 += 1;
        }

        println!("\n── lb={lb} (blowup {}×) q=19 pow=0", 1usize << lb);
        println!(
            "   {:<28} {:>7} {:>14} {:>14} {:>14} {:>8} {:>14}",
            "phase", "calls", "MUL", "ADD", "SUB", "INV", "total (M+A+S)"
        );
        let mut rows = Vec::new();
        for (ph, (c, n)) in &per_phase {
            println!(
                "   {:<28} {:>7} {:>14} {:>14} {:>14} {:>8} {:>14}",
                ph,
                n,
                c.mul,
                c.add,
                c.sub,
                c.inv,
                c.total_linear()
            );
            rows.push((*ph, *c, *n));
        }
        let mut tot = OpCounts::default();
        for (_, (c, _)) in &per_phase {
            tot.add_in(*c);
        }
        println!(
            "   {:<28} {:>7} {:>14} {:>14} {:>14} {:>8} {:>14}",
            "— DFT TOTAL",
            per_call.len(),
            tot.mul,
            tot.add,
            tot.sub,
            tot.inv,
            tot.total_linear()
        );

        // ⚑ EVERY CALL, IN ORDER, WITH ITS SPAN PATH. The order is the prover's commit sequence
        // (preprocessed → main trace → permutation → per-AIR quotient chunks), so a reader can see
        // exactly which matrix is which rather than inferring it from a width.
        println!("\n   every DFT call, in call order (counts are for THAT call alone):");
        println!(
            "   {:>3} {:>8} {:>6} {:>4} {:>12} {:>12} {:>12}  {}",
            "#", "h", "w", "+b", "MUL", "ADD", "SUB", "span path"
        );
        for (i, (ev, c)) in per_call.iter().enumerate() {
            println!(
                "   {:>3} {:>8} {:>6} {:>4} {:>12} {:>12} {:>12}  {}",
                i,
                ev.height,
                ev.width,
                ev.added_bits,
                c.mul,
                c.add,
                c.sub,
                if ev.path.is_empty() {
                    "<no span>"
                } else {
                    &ev.path
                }
            );
        }

        table.push((lb, rows));
    }

    // The composed table, alongside §D's permutation counts so the two instruments can be read
    // together. §D values are quoted from `ir2_phase_profile.rs`'s recorded output at q=19, pow=0.
    println!("\n── §G1 SUMMARY: scalar-equivalent field ops (DFT phases only) by blowup");
    println!(
        "   {:>3} {:>16} {:>16} {:>16}",
        "lb", "LDE commit", "LDE quot-eval", "DFT total (M+A+S)"
    );
    for (lb, rows) in &table {
        let commit = rows
            .iter()
            .find(|(p, _, _)| *p == "LDE commit (arith)")
            .map(|(_, c, _)| c.total_linear())
            .unwrap_or(0);
        let quot = rows
            .iter()
            .find(|(p, _, _)| *p == "LDE quotient-eval (arith)")
            .map(|(_, c, _)| c.total_linear())
            .unwrap_or(0);
        println!("   {lb:>3} {commit:>16} {quot:>16} {:>16}", commit + quot);
    }
    println!("\n   MULTIPLIES only (the term that prices against a Poseidon2 permutation):");
    println!(
        "   {:>3} {:>16} {:>16} {:>16}",
        "lb", "LDE commit", "LDE quot-eval", "DFT MUL total"
    );
    for (lb, rows) in &table {
        let commit = rows
            .iter()
            .find(|(p, _, _)| *p == "LDE commit (arith)")
            .map(|(_, c, _)| c.mul)
            .unwrap_or(0);
        let quot = rows
            .iter()
            .find(|(p, _, _)| *p == "LDE quotient-eval (arith)")
            .map(|(_, c, _)| c.mul)
            .unwrap_or(0);
        println!("   {lb:>3} {commit:>16} {quot:>16} {:>16}", commit + quot);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// §G2 — THE DERIVATION CHECK
//
// The brief's option 2: an LDE of `w` columns at height `h` and blowup `2^b` is a known number of
// butterflies. Deriving it and checking the derivation against the counted case is what makes the
// count auditable — and it is what catches the two places a hand derivation goes wrong.
// ─────────────────────────────────────────────────────────────────────────────

/// Textbook radix-2 DIT: `log2(h)` layers of `h/2` butterflies per column, each butterfly one
/// multiply + one add + one sub. Plonky3 shaves the multiply on every twiddle equal to one.
fn textbook_dft_ops(h: usize, w: usize) -> (u64, u64, u64) {
    let log_h = h.trailing_zeros() as u64;
    let butterflies = (h as u64 / 2) * (w as u64) * log_h;
    (butterflies, butterflies, butterflies)
}

/// **§G2 — check the closed form against counted reality on the shapes the prover actually uses.**
#[test]
fn dft_derivation_check() {
    reset_counters();
    let dft: Radix2DitParallel<CountedBabyBear> = Radix2DitParallel::default();
    println!(
        "\n═══ §G2 DERIVED vs COUNTED — plain `dft_batch`, no coset, no blowup ═══\n\
         textbook = (h/2)·w·log₂h butterflies, each 1 MUL + 1 ADD + 1 SUB."
    );
    println!(
        "   {:>8} {:>6} {:>14} {:>14} {:>8} {:>14} {:>8}",
        "h", "w", "MUL counted", "MUL textbook", "ratio", "ADD counted", "A/txt"
    );
    for (h, w) in [
        (64usize, 8usize),
        (256, 8),
        (1024, 8),
        (4096, 8),
        (1024, 64),
    ] {
        let base = OpCounts::read();
        std::hint::black_box(dft.dft_batch(filler_matrix(h, w)));
        let c = OpCounts::since(base);
        let (tm, ta, _) = textbook_dft_ops(h, w);
        println!(
            "   {:>8} {:>6} {:>14} {:>14} {:>8.3} {:>14} {:>8.3}",
            h,
            w,
            c.mul,
            tm,
            c.mul as f64 / tm as f64,
            c.add,
            c.add as f64 / ta as f64
        );
    }
    println!(
        "\n   ⚑ The MUL ratio is BELOW 1 and the ADD ratio is 1: `dit_layer_twiddle_free` and\n   \
         `dit_layer_first_one` skip the multiply wherever the twiddle is one — layer 0 entirely,\n   \
         and the first row-pair of every block thereafter. A hand-derived butterfly count\n   \
         OVER-CHARGES the multiplies and gets the adds right. This is the reason the count is\n   \
         taken rather than derived."
    );

    println!("\n═══ §G2b coset LDE — the shape the prover actually calls ═══");
    println!(
        "   {:>8} {:>6} {:>4} {:>16} {:>16} {:>16}",
        "h", "w", "+b", "MUL", "ADD", "SUB"
    );
    for (h, w, b) in [
        (64usize, 8usize, 3usize),
        (64, 8, 6),
        (256, 8, 3),
        (256, 8, 6),
    ] {
        let base = OpCounts::read();
        std::hint::black_box(dft.coset_lde_batch(
            filler_matrix(h, w),
            b,
            CountedBabyBear::GENERATOR,
        ));
        let c = OpCounts::since(base);
        println!(
            "   {h:>8} {w:>6} {b:>4} {:>16} {:>16} {:>16}",
            c.mul, c.add, c.sub
        );
    }
    println!(
        "\n   An `h → h·2^b` coset LDE is one iDFT of size h plus 2^b coset DFTs of size h, so the\n   \
         MUL term is Θ(2^b · h · log h) — LINEAR in the blowup with a log-h coefficient, which is\n   \
         why the LDE phases double per rung in the §A timing table."
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// §G5 — WHERE THE LDE'S TIME ACTUALLY GOES
//
// ⚑ §G1 and `ir2_phase_profile.rs` §A disagree GROSSLY about the LDE, and the disagreement is a
// finding, not a discrepancy to average away. At b=6:
//
//   phase                     counted ops   §A measured ms
//   LDE commit (6 calls)       12,513,091            7.710
//   LDE quotient-eval (12)        457,424           12.925
//
// The phase carrying **3.5% of the arithmetic** is measured at **63% of the time**. Both cannot
// be a statement about arithmetic. This section settles it WITHOUT a whole-prover clock: each
// recorded geometry is replayed as a STANDALONE kernel against the real
// `Radix2DitParallel<P3BabyBear>`, min-of-N, with no prover and no tracing in the loop. A single
// coset LDE at these shapes is tens of microseconds to a few milliseconds, so min-of-N is a
// legitimate estimator where a min-of-N over an 80 ms prove is not.
//
// The quantity of interest is **ns per COUNTED field operation**, per geometry. If it is roughly
// constant, the LDE's time is arithmetic. If it varies by orders of magnitude, the LDE's time is
// something else — and the op count is what makes "something else" visible at all.
// ─────────────────────────────────────────────────────────────────────────────

/// **§G5 — ns per counted field operation, per real committed geometry.**
#[test]
fn lde_time_per_counted_operation() {
    install_path_layer();
    let w = transfer_workload();
    let lb = 6usize;
    let events = record_one(&w, lb, 19, 0);
    reset_counters();
    let per_call = replay(&events);

    // Collapse to distinct geometries, keeping the per-call op count and the phase.
    let mut geoms: Vec<(usize, usize, usize, &'static str, OpCounts)> = Vec::new();
    for (ev, c) in &per_call {
        if !geoms
            .iter()
            .any(|g| g.0 == ev.height && g.1 == ev.width && g.2 == ev.added_bits)
        {
            geoms.push((ev.height, ev.width, ev.added_bits, phase_of(&ev.path), *c));
        }
    }

    let dft: Radix2DitParallel<P3BabyBear> = Radix2DitParallel::default();
    println!(
        "\n═══ §G5 STANDALONE COSET-LDE KERNEL at every real geometry, lb={lb} \
         (min of N=25 calls) ═══\n   \
         Real `Radix2DitParallel<P3BabyBear>`, no prover, no tracing. `ns/op` divides the min\n   \
         wall time by the EXACT counted scalar-equivalent field ops for that same call."
    );
    println!(
        "   {:>6} {:>6} {:>4} {:>26} {:>12} {:>10} {:>9}",
        "h", "w", "+b", "phase", "counted ops", "min µs", "ns/op"
    );
    for (h, wd, ab, phase, c) in &geoms {
        let ops = c.total_linear();
        let mut best = f64::INFINITY;
        for _ in 0..25 {
            let m = RowMajorMatrix::new(
                (0..(h * wd))
                    .map(|i| P3BabyBear::from_u32((i as u32).wrapping_mul(2_654_435_761) | 1))
                    .collect(),
                *wd,
            );
            let t = Instant::now();
            let out = dft.coset_lde_batch(m, *ab, P3BabyBear::GENERATOR);
            let e = t.elapsed().as_secs_f64();
            std::hint::black_box(&out);
            if e < best {
                best = e;
            }
        }
        println!(
            "   {:>6} {:>6} {:>4} {:>26} {:>12} {:>10.1} {:>9.2}",
            h,
            wd,
            ab,
            phase,
            ops,
            best * 1e6,
            best * 1e9 / ops as f64
        );
    }
    println!(
        "\n   ⚑ Read the `ns/op` column. A constant there would mean the LDE's time IS its\n   \
         arithmetic. A spread means it is not — and the width-4 quotient-chunk geometries are\n   \
         where to look, because a width-4 matrix is ONE NEON vector per row, so every per-row\n   \
         cost (twiddle load, bit-reversal index, bounds check) is paid against 4 lanes instead\n   \
         of amortised across a wide row."
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// §G4 — THE NON-DFT ARITHMETIC, as COUNTED KERNELS at the real geometry
//
// The DFT is 80% of the prover's arithmetic at b=6 but only ~46% at b=3 — and b=3 is where the
// crossover sits, so the remainder cannot be waved away. It is reached through `p3-fri`'s `open`
// and `p3-batch-stark`'s quotient loop, neither of which is behind a substitutable type parameter.
//
// What IS reachable: the KERNELS those phases are built from are public generic functions, so each
// one is CALLED over the counting field at the geometry the recorder observed. Every number below
// is a real count of a real kernel; only the MULTIPLICITY (how many matrices, at how many points)
// is derived, and it is derived UPWARD — see `open_phase_upper_bound`.
//
// ⚑ The direction of every approximation in this section is stated, and they all point the same
// way: they OVER-state arithmetic. That is the conservative direction for a "hash-bound" claim,
// so a hash-bound verdict computed against this bound is a verdict that survives the slack.
// ─────────────────────────────────────────────────────────────────────────────

/// Cost of the extension-field primitives, counted rather than assumed.
#[derive(Default, Clone, Copy, Debug)]
struct ExtPrimitives {
    ext_mul: OpCounts,
    ext_mul_base: OpCounts,
    ext_add: OpCounts,
    ext_sub: OpCounts,
    ext_inv: OpCounts,
}

fn count_ext_primitives() -> ExtPrimitives {
    const N: u64 = 4096;
    let a =
        EfC::from_basis_coefficients_fn(|i| CountedBabyBear(P3BabyBear::from_u32(7 + i as u32)));
    let b =
        EfC::from_basis_coefficients_fn(|i| CountedBabyBear(P3BabyBear::from_u32(3 + i as u32)));
    let s = CountedBabyBear(P3BabyBear::from_u32(5));

    let mut p = ExtPrimitives::default();
    macro_rules! kernel {
        ($slot:ident, $body:expr) => {{
            let base = OpCounts::read();
            for _ in 0..N {
                std::hint::black_box($body);
            }
            let c = OpCounts::since(base);
            p.$slot = OpCounts {
                mul: c.mul / N,
                add: c.add / N,
                sub: c.sub / N,
                neg: c.neg / N,
                inv: c.inv / N,
            };
        }};
    }
    kernel!(ext_mul, a * b);
    kernel!(ext_mul_base, a * s);
    kernel!(ext_add, a + b);
    kernel!(ext_sub, a - b);
    kernel!(ext_inv, a.inverse());
    p
}

/// The committed-matrix geometry, recovered from the recorder's `coset_lde_batch` events. Every
/// matrix the PCS commits to reaches the DFT through exactly that entry point, so this IS the
/// committed set — nothing is guessed about which matrices exist.
#[derive(Clone, Copy, Debug)]
struct CommittedMat {
    /// LDE height = input height × 2^added_bits.
    lde_height: usize,
    width: usize,
}

fn committed_mats(events: &[DftEvent]) -> Vec<CommittedMat> {
    events
        .iter()
        .filter(|e| e.call == DftCall::CosetLdeBatch)
        .map(|e| CommittedMat {
            lde_height: e.height << e.added_bits,
            width: e.width,
        })
        .collect()
}

/// **The open phase, counted kernel by kernel, at an UPPER-BOUND multiplicity.**
///
/// From `vendor/plonky3-fri-82cfad73/src/two_adic_pcs.rs::open`, per committed matrix `M` of LDE
/// height `H` and width `w`, opened at `P` points:
///
/// 1. `compress mat` — `M.rowwise_packed_dot_product::<Challenge>(&alpha_powers)`: `H·w`
///    base×extension multiplies plus `H·(w−1)` extension adds. **Once per matrix**, reused across
///    that matrix's points.
/// 2. `reduce matrix quotient` — per point, per row:
///    `*ro += alpha_pow_offset * (reduced_openings − reduced_row) * inv_denom`, i.e. one extension
///    sub, two extension muls and one extension add. `H·P` times.
/// 3. `compute_inverse_denominators` — per distinct point, a `batch_multiplicative_inverse` over
///    `2^max_log_height` extension elements.
/// 4. `evaluate matrix` (barycentric) — `low_coset.columnwise_dot_product(weights)` over the
///    TRUNCATED matrix (`h = H >> log_blowup` rows), once per (matrix, point).
///
/// **`P = 2` is used for every matrix. That is an over-count**: `p3-batch-stark` opens the main
/// trace, permutation and preprocessed matrices at `{zeta, zeta_next}` but the quotient chunks at
/// `{zeta}` only. Over-counting arithmetic is the conservative direction here.
fn open_phase_upper_bound(mats: &[CommittedMat], log_blowup: usize, p: ExtPrimitives) -> OpCounts {
    let mut total = OpCounts::default();
    const POINTS: u64 = 2;

    for m in mats {
        let h = m.lde_height as u64;
        let w = m.width as u64;

        // 1. compress mat — once per matrix.
        for _ in 0..1 {
            let mut c = OpCounts::default();
            for _ in 0..h {
                for _ in 0..w {
                    c.add_in(p.ext_mul_base);
                }
                for _ in 0..w.saturating_sub(1) {
                    c.add_in(p.ext_add);
                }
            }
            total.add_in(c);
        }

        // 2. reduce matrix quotient — H rows × P points.
        let mut per_row = OpCounts::default();
        per_row.add_in(p.ext_sub);
        per_row.add_in(p.ext_mul);
        per_row.add_in(p.ext_mul);
        per_row.add_in(p.ext_add);
        for _ in 0..(h * POINTS) {
            total.add_in(per_row);
        }

        // 4. evaluate matrix — the truncated low coset, per (matrix, point).
        let low_h = h >> log_blowup;
        for _ in 0..POINTS {
            for _ in 0..(low_h * w) {
                total.add_in(p.ext_mul);
            }
            for _ in 0..(low_h.saturating_sub(1) * w) {
                total.add_in(p.ext_add);
            }
        }
    }

    // 3. compute_inverse_denominators — one batch inverse per distinct point at the max height.
    // Montgomery's trick over n elements: 3(n−1) multiplies + 1 inverse.
    let max_h = mats.iter().map(|m| m.lde_height).max().unwrap_or(0) as u64;
    for _ in 0..POINTS {
        for _ in 0..max_h {
            total.add_in(p.ext_sub);
        }
        for _ in 0..(3 * max_h.saturating_sub(1)) {
            total.add_in(p.ext_mul);
        }
        total.add_in(p.ext_inv);
    }

    total
}

/// **§G4 — extension primitives counted, and the open phase bounded from them.**
#[test]
fn open_phase_and_extension_primitives() {
    install_path_layer();
    reset_counters();
    let p = count_ext_primitives();
    println!("\n═══ §G4a EXTENSION PRIMITIVES, COUNTED (degree-4 binomial over BabyBear) ═══");
    println!(
        "   {:<24} {:>8} {:>8} {:>8} {:>6}",
        "kernel", "MUL", "ADD", "SUB", "INV"
    );
    for (n, c) in [
        ("ext × ext", p.ext_mul),
        ("ext × base", p.ext_mul_base),
        ("ext + ext", p.ext_add),
        ("ext − ext", p.ext_sub),
        ("ext inverse", p.ext_inv),
    ] {
        println!(
            "   {:<24} {:>8} {:>8} {:>8} {:>6}",
            n, c.mul, c.add, c.sub, c.inv
        );
    }
    println!(
        "\n   ⚠ `ext × ext` here is the GENERIC `quartic_mul`. The deployed `MontyField31`\n   \
         overrides it with `quartic_mul_packed` (4 multiplies by W + a 4×4 dot product = 20\n   \
         multiplies) where the generic path shares subterms down to 19. The counting extension is\n   \
         therefore ~5% CHEAPER per extension multiply than the deployed one — it UNDER-states\n   \
         arithmetic by that much, which is the conservative direction for a hash-bound claim."
    );

    // The FRI fold, counted directly: `CpuTwoAdicFriFold` is public and generic over (F, EF).
    println!("\n═══ §G4b FRI FOLD, COUNTED (arity 2, the deployed path) ═══");
    println!(
        "   {:>10} {:>14} {:>14} {:>14}",
        "rows in", "MUL", "ADD", "SUB"
    );
    for log_h in [8usize, 10, 12] {
        let h = 1usize << log_h;
        let vals: Vec<EfC> = (0..h * 2)
            .map(|i| {
                EfC::from_basis_coefficients_fn(|j| {
                    CountedBabyBear(P3BabyBear::from_u32((i * 4 + j) as u32 | 1))
                })
            })
            .collect();
        let m = RowMajorMatrix::new(vals, 2);
        let beta = EfC::from_basis_coefficients_fn(|j| {
            CountedBabyBear(P3BabyBear::from_u32(j as u32 + 11))
        });
        let base = OpCounts::read();
        let folded = <p3_fri::CpuTwoAdicFriFold as p3_fri::TwoAdicFriFoldBackend<
            CountedBabyBear,
            EfC,
        >>::fold_matrix(&p3_fri::CpuTwoAdicFriFold, beta, 1, m);
        let c = OpCounts::since(base);
        std::hint::black_box(&folded);
        println!(
            "   {:>10} {:>14} {:>14} {:>14}   ({:.1} MUL per folded row)",
            h * 2,
            c.mul,
            c.add,
            c.sub,
            c.mul as f64 / h as f64
        );
    }

    // The open phase, bounded, at each blowup, on the recorded committed geometry.
    let w = transfer_workload();
    println!(
        "\n═══ §G4c OPEN-PHASE UPPER BOUND from the recorded committed geometry ═══\n   \
         P = 2 opening points assumed for EVERY committed matrix (an over-count: quotient chunks\n   \
         are opened at zeta only). Kernels counted, multiplicities derived UPWARD."
    );
    println!(
        "   {:>3} {:>7} {:>16} {:>16} {:>16}",
        "lb", "mats", "open MUL", "open ADD+SUB", "open total"
    );
    for lb in [3usize, 4, 5, 6, 7] {
        let events = record_one(&w, lb, 19, 0);
        let mats = committed_mats(&events);
        let c = open_phase_upper_bound(&mats, lb, p);
        println!(
            "   {:>3} {:>7} {:>16} {:>16} {:>16}",
            lb,
            mats.len(),
            c.mul,
            c.add + c.sub,
            c.total_linear()
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// §G3 — THE CONVERSION RATE
//
// With both sides exact, the ONLY remaining unknown separating "counted work" from "which side is
// bigger in seconds" is the exchange rate between one Poseidon2 permutation and one BabyBear
// multiply. That is a single constant, and unlike a whole-prover timing it fits in L1 and runs in
// microseconds — so it survives a contended box in a way an 80 ms prove does not.
// ─────────────────────────────────────────────────────────────────────────────

/// Minimum over `windows` short windows of `per_window` operations each; returns ns per operation.
/// Short windows, many of them: a window that fits between two preemptions is a clean sample, and
/// the minimum over thousands of them finds one. A single long window cannot escape preemption.
fn min_ns<F: FnMut()>(windows: usize, per_window: u64, mut f: F) -> f64 {
    let mut best = f64::INFINITY;
    for _ in 0..windows {
        let t = Instant::now();
        f();
        let e = t.elapsed().as_secs_f64() / per_window as f64;
        if e < best {
            best = e;
        }
    }
    best * 1e9
}

/// **§G3 — the exchange rate, measured on both sides in the SAME unit (scalar-equivalent, packed
/// path, throughput-bound).**
#[test]
fn conversion_rate_microbenchmark() {
    use p3_symmetric::Permutation as _;

    const WINDOWS: usize = 4_000;
    const PER: usize = 4_096;

    // ── Multiply, packed path, throughput-bound. `PER` independent packed multiplies per window;
    // dividing by `Pack::WIDTH` gives ns per scalar-equivalent multiply, which is the unit §G1
    // counts in.
    let mut a: Vec<Pack> = (0..PER)
        .map(|i| Pack::from(P3BabyBear::from_u32(i as u32 | 1)))
        .collect();
    let b: Vec<Pack> = (0..PER)
        .map(|i| Pack::from(P3BabyBear::from_u32((i as u32).wrapping_mul(7) | 3)))
        .collect();
    // warm
    for _ in 0..50 {
        for (x, y) in a.iter_mut().zip(b.iter()) {
            *x = std::hint::black_box(*x * *y);
        }
    }
    let mul_packed_call = min_ns(WINDOWS, PER as u64, || {
        for (x, y) in a.iter_mut().zip(b.iter()) {
            *x = std::hint::black_box(*x * *y);
        }
    });
    let mul_lane = mul_packed_call / Pack::WIDTH as f64;

    // Scalar multiply, throughput-bound, for the SIMD factor on the arithmetic side.
    let mut sa: Vec<P3BabyBear> = (0..PER)
        .map(|i| P3BabyBear::from_u32(i as u32 | 1))
        .collect();
    let sb: Vec<P3BabyBear> = (0..PER)
        .map(|i| P3BabyBear::from_u32((i as u32).wrapping_mul(7) | 3))
        .collect();
    for _ in 0..50 {
        for (x, y) in sa.iter_mut().zip(sb.iter()) {
            *x = std::hint::black_box(*x * *y);
        }
    }
    let mul_scalar = min_ns(WINDOWS, PER as u64, || {
        for (x, y) in sa.iter_mut().zip(sb.iter()) {
            *x = std::hint::black_box(*x * *y);
        }
    });

    // Additions, same unit, for completeness — an LDE does as many adds as multiplies.
    let mut aa: Vec<Pack> = (0..PER)
        .map(|i| Pack::from(P3BabyBear::from_u32(i as u32 | 1)))
        .collect();
    for _ in 0..50 {
        for (x, y) in aa.iter_mut().zip(b.iter()) {
            *x = std::hint::black_box(*x + *y);
        }
    }
    let add_packed_call = min_ns(WINDOWS, PER as u64, || {
        for (x, y) in aa.iter_mut().zip(b.iter()) {
            *x = std::hint::black_box(*x + *y);
        }
    });
    let add_lane = add_packed_call / Pack::WIDTH as f64;

    // ── Poseidon2, packed path, throughput-bound. Same estimator, same unit.
    let perm = default_babybear_poseidon2_16();
    let mut pbank: Vec<[Pack; 16]> = (0..512)
        .map(|i| {
            let mut s = [Pack::from(P3BabyBear::ONE); 16];
            s[0] = Pack::from(P3BabyBear::from_u32(i as u32));
            s
        })
        .collect();
    for _ in 0..100 {
        for s in pbank.iter_mut() {
            perm.permute_mut(std::hint::black_box(s));
        }
    }
    let perm_packed_call = min_ns(WINDOWS, 512, || {
        for s in pbank.iter_mut() {
            perm.permute_mut(std::hint::black_box(s));
        }
    });
    let perm_lane = perm_packed_call / Pack::WIDTH as f64;

    // ── An inverse, priced as an event (see the `INVS` doc comment).
    let mut inv_in: Vec<P3BabyBear> = (0..PER)
        .map(|i| P3BabyBear::from_u32(i as u32 | 1))
        .collect();
    for _ in 0..20 {
        for x in inv_in.iter_mut() {
            *x = std::hint::black_box(x.inverse());
        }
    }
    let inv_scalar = min_ns(400, PER as u64, || {
        for x in inv_in.iter_mut() {
            *x = std::hint::black_box(x.inverse());
        }
    });

    println!(
        "\n═══ §G3 CONVERSION RATE — min of N={WINDOWS} windows × {PER} ops, ONE thread, \
         SIMD width {} ═══",
        Pack::WIDTH
    );
    println!(
        "   packed MUL      : {mul_packed_call:8.3} ns/call = {mul_lane:7.4} ns per scalar-equivalent multiply"
    );
    println!(
        "   scalar MUL      : {mul_scalar:8.3} ns          (SIMD factor {:.2}×)",
        mul_scalar / mul_lane
    );
    println!(
        "   packed ADD      : {add_packed_call:8.3} ns/call = {add_lane:7.4} ns per scalar-equivalent add"
    );
    println!(
        "   packed POSEIDON2: {perm_packed_call:8.3} ns/call = {perm_lane:7.4} ns per scalar-equivalent permutation"
    );
    println!(
        "   scalar inverse  : {inv_scalar:8.3} ns/inverse  ({:.1} multiplies' worth)",
        inv_scalar / mul_lane
    );
    println!(
        "\n   ⚑ THE EXCHANGE RATE  Y = (ns per permutation) / (ns per multiply) = {:.1}\n   \
         Both numerators are packed-path, throughput-bound, scalar-equivalent lane rates — the\n   \
         SAME unit on both sides. Comparing a packed permutation against a SCALAR multiply would\n   \
         inflate Y by the SIMD factor and is the error this measurement exists to avoid.",
        perm_lane / mul_lane
    );
    println!(
        "   Y_add = (ns per permutation) / (ns per add) = {:.1}",
        perm_lane / add_lane
    );
    println!(
        "\n   Contention robustness: each window is {} packed ops ≈ {:.1} µs and stays resident.\n   \
         The estimator is the minimum over {WINDOWS} of them, so a clean sample only needs ONE\n   \
         un-preempted window. An 80 ms whole-prover timing has no such escape.",
        PER,
        PER as f64 * mul_packed_call / 1000.0
    );

    // ── §G3b — ⚑ THE RATE IS A FUNCTION OF THE WORKING SET, AND THE PHASES HAVE DIFFERENT ONES.
    //
    // `COST-MODEL.md`'s retraction says hash work is memory-bound and field arithmetic is
    // cache-resident. **At the deployed geometry that is not true of the arithmetic either.** The
    // committed LDE at b=6 is 4096 × 386 × 4 B = 6.3 MB, and the DFT streams it; a multiply rate
    // taken on a resident buffer therefore OVER-states the arithmetic side's throughput, i.e.
    // UNDER-states its time. So the exchange rate is measured across working sets and the verdict
    // is reported against the range, not against one number.
    println!(
        "\n═══ §G3b THE EXCHANGE RATE ACROSS WORKING SETS (min of 200 windows each) ═══\n   \
         The deployed LDE buffer is ~{:.1} MB at b=6 and ~{:.1} MB at b=7. Both the DFT and the\n   \
         Merkle build stream a buffer that size, so neither runs at its resident rate.",
        4096.0 * 386.0 * 4.0 / 1e6,
        8192.0 * 386.0 * 4.0 / 1e6
    );
    println!(
        "   {:>12} {:>16} {:>18} {:>10}",
        "buffer", "ns / mul (lane)", "ns / perm (lane)", "Y"
    );
    for bytes in [32usize << 10, 512 << 10, 4 << 20, 16 << 20] {
        // Multiply: one pass over `n` packed elements, multiplying in place.
        let n = bytes / std::mem::size_of::<Pack>();
        let mut buf: Vec<Pack> = (0..n)
            .map(|i| Pack::from(P3BabyBear::from_u32(i as u32 | 1)))
            .collect();
        let k = Pack::from(P3BabyBear::from_u32(1_234_567));
        for _ in 0..3 {
            for x in buf.iter_mut() {
                *x = std::hint::black_box(*x * k);
            }
        }
        let mul_ns = min_ns(200, n as u64, || {
            for x in buf.iter_mut() {
                *x = std::hint::black_box(*x * k);
            }
        }) / Pack::WIDTH as f64;

        // Poseidon2: one pass over a bank of the same total size.
        let states = (bytes / std::mem::size_of::<[Pack; 16]>()).max(1);
        let mut bank: Vec<[Pack; 16]> = (0..states)
            .map(|i| {
                let mut s = [Pack::from(P3BabyBear::ONE); 16];
                s[0] = Pack::from(P3BabyBear::from_u32(i as u32));
                s
            })
            .collect();
        for _ in 0..3 {
            for s in bank.iter_mut() {
                perm.permute_mut(std::hint::black_box(s));
            }
        }
        let perm_ns = min_ns(200, states as u64, || {
            for s in bank.iter_mut() {
                perm.permute_mut(std::hint::black_box(s));
            }
        }) / Pack::WIDTH as f64;

        println!(
            "   {:>10} KB {:>16.4} {:>18.2} {:>10.1}",
            bytes >> 10,
            mul_ns,
            perm_ns,
            perm_ns / mul_ns
        );
    }
    println!(
        "\n   ⚑ Read the LAST rows. Y falls as the working set grows, because the multiply is a\n   \
         one-op-per-element stream (bandwidth-bound the moment it leaves cache) while a Poseidon2\n   \
         permutation does ~560 multiplies per 64-byte state (compute-bound at every size). The\n   \
         SMALLEST Y in this table is the one a hash-bound claim must clear."
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// §G6 — THE MECHANISM behind Finding 3: what a NARROW `coset_lde_batch` pays for
//
// §G1 Finding 3 established the *shape* of the anomaly — twelve width-4 quotient-chunk LDE calls
// carrying 3.5% of the LDE's arithmetic and (per §A) 63% of its time — and named a layout fix
// without naming a mechanism. A layout change justified by "it was slow" does not generalise, and
// it cannot tell you WHICH widths to batch into. §G6 names the mechanism in exact counts.
//
// `Radix2DitParallel::coset_lde_batch_with_transform` runs one iDFT and then `2^added_bits`
// separate `coset_dft_oop` calls, one per coset, each at a DISTINCT shift `g_big^j · shift`. The
// sections below take the candidates in order and let the measurements eliminate them:
//
//   §G6b  the coset-twiddle tables — width-independent in COUNTS (confirmed) …
//   §G6c  … and ~zero on a CLOCK. ⚑ HYPOTHESIS REFUTED; the counted term is not the cost.
//   §G6d  the cost tracks the COSET COUNT, not the work: at fixed output size the work falls
//         while the clock rises 34×. A per-coset constant of ~10–15 µs, independent of h AND w.
//   §G6e  that constant IS rayon's cold hand-off — 11–27× when the caller is a pool worker.
//   §G6f  the same question asked of the whole prover: 1.2–2.5×. ⚑ NOT TAKEN by this lane.
// ─────────────────────────────────────────────────────────────────────────────

/// The quotient-chunk geometry the real prover produces, read off §G1's call log (stable at every
/// blowup): `(chunk height, number of chunks)`, one entry per AIR. Chunk height IS trace height —
/// `quotient_domain.size() = trace_size · n_chunks` and `split_evals` cuts it into `n_chunks`
/// pieces — so the chunk counts read directly as the AIRs' quotient degrees: 2, 8, 2.
const QUOTIENT_CHUNK_GEOMETRY: [(usize, usize); 3] = [(64, 2), (8, 8), (16, 2)];

/// The per-chunk LDE shift the prover passes, DERIVED from `p3-batch-stark`'s construction and
/// CHECKED against the recorded log in [`quotient_chunk_shifts_are_omega_powers`].
///
/// `quotient_domain = trace_domain.create_disjoint_domain(h·n)` gives shift `1 · GENERATOR` and
/// size `h·n`; `split_domains(n)` gives chunk `i` the shift `GENERATOR · ω^i` where
/// `ω = two_adic_generator(log2(h·n))`; and `two_adic_pcs.rs` passes
/// `GENERATOR / chunk_shift = ω^{-i}`.
fn chunk_lde_shifts(h: usize, n: usize) -> Vec<P3BabyBear> {
    let log_q = p3_util::log2_strict_usize(h * n);
    let omega = P3BabyBear::two_adic_generator(log_q);
    let omega_inv = omega.inverse();
    (0..n).map(|i| omega_inv.exp_u64(i as u64)).collect()
}

/// **§G6a — the premise, checked through the prover's OWN domain API, and the after-picture.**
///
/// Part 1 rebuilds the chunk domains with the same calls `p3-batch-stark` makes
/// (`natural_domain_for_degree` → `create_disjoint_domain(h·n)` → `split_domains(n)`) and takes
/// `GENERATOR / shift` exactly as `two_adic_pcs.rs` does, then checks [`chunk_lde_shifts`] against
/// it. Nothing here is re-derived by hand; the check is against the real objects.
///
/// Part 2 records a real prove and asserts what the DFT seam now sees. **Before DELTA 3 this was
/// twelve width-4 calls** (the §G1 log in `field-op-counts.md`, reproduced on this box on
/// 2026-08-14); after it, three batched calls at widths 8 / 32 / 8, all at shift `ONE`.
#[test]
fn quotient_chunk_shifts_are_omega_powers() {
    use p3_commit::PolynomialSpace;
    use p3_field::coset::TwoAdicMultiplicativeCoset;

    println!("\n═══ §G6a THE CHUNK SHIFTS, through the prover's own domain API ═══");
    for (h, n) in QUOTIENT_CHUNK_GEOMETRY {
        let trace = TwoAdicMultiplicativeCoset::new(P3BabyBear::ONE, p3_util::log2_strict_usize(h))
            .expect("trace domain");
        let quotient = trace.create_disjoint_domain(h * n);
        assert_eq!(quotient.size(), h * n, "quotient domain size h·n");
        let real: Vec<P3BabyBear> = quotient
            .split_domains(n)
            .into_iter()
            .map(|d| P3BabyBear::GENERATOR / d.shift())
            .collect();
        assert_eq!(
            real,
            chunk_lde_shifts(h, n),
            "h={h} n={n}: derived ω^-i must equal the shift `get_quotient_ldes` computes"
        );
        println!(
            "   h={h:>3} n={n}  shifts = {:?}",
            real.iter()
                .map(|s| s.as_canonical_u32())
                .collect::<Vec<_>>()
        );
    }
    println!(
        "   ⚑ CHECKED at source: chunk `i` of every AIR is LDE'd at `ω^-i` for\n   \
         `ω = two_adic_generator(log2(h·n))`, and chunk 0 is always ONE."
    );

    install_path_layer();
    let w = transfer_workload();
    let events = record_one(&w, 6, 19, 0);
    let quot: Vec<&DftEvent> = events
        .iter()
        .filter(|e| e.path.contains("compute quotient"))
        .collect();

    println!("\n═══ §G6a AFTER DELTA 3 — what the DFT seam sees in a real prove (b=6) ═══");
    for (k, ev) in quot.iter().enumerate() {
        println!(
            "   call {k}: h={:>3} w={:>3} +b={} shift={}",
            ev.height, ev.width, ev.added_bits, ev.shift
        );
    }
    let shape: Vec<(usize, usize)> = quot.iter().map(|e| (e.height, e.width)).collect();
    assert_eq!(
        shape,
        vec![(64, 8), (8, 32), (16, 8)],
        "DELTA 3: one batched LDE per AIR, at width n·D — was twelve width-4 calls"
    );
    assert!(
        quot.iter().all(|e| e.shift == 1),
        "DELTA 3 folds every chunk shift into the coefficients and LDEs at shift ONE"
    );
    println!(
        "   ⚑ 12 width-4 calls → 3 calls at widths 8 / 32 / 8. The six `prove_batch` commits\n   \
         (widths 236, 386, 2, 72, 12, 4) are untouched."
    );
}

/// Ops charged by one `coset_lde_batch(h, w, added_bits, shift)` on a **cold** memo (fresh `Dft`)
/// minus the same call on a **warm** memo (same instance, same key). The difference is exactly the
/// twiddle-table construction for the `2^added_bits` distinct coset shifts.
fn cold_warm_split(h: usize, w: usize, added_bits: usize, shift: u32) -> (OpCounts, OpCounts) {
    let s = CountedBabyBear(P3BabyBear::from_u32(shift));

    let dft: Radix2DitParallel<CountedBabyBear> = Radix2DitParallel::default();
    let base = OpCounts::read();
    std::hint::black_box(dft.coset_lde_batch(filler_matrix(h, w), added_bits, s));
    let cold = OpCounts::since(base);

    let base = OpCounts::read();
    std::hint::black_box(dft.coset_lde_batch(filler_matrix(h, w), added_bits, s));
    let warm = OpCounts::since(base);

    (cold, warm)
}

/// **§G6b — the width-independent term, isolated in exact counts.**
///
/// Sweeps width at fixed `(h, added_bits)` and reports the cold−warm difference. If the mechanism
/// is the per-coset twiddle table, that difference is a CONSTANT in `w` while the call's total
/// grows linearly in `w` — so its SHARE falls as `1/w`, which is the whole asymmetry between a
/// width-236 trace commit and a width-4 quotient chunk.
#[test]
fn narrow_call_overhead_mechanism() {
    reset_counters();
    let added_bits = 6usize;

    println!(
        "\n═══ §G6b THE WIDTH-INDEPENDENT TERM — cold-memo minus warm-memo `coset_lde_batch` ═══\n   \
         added_bits={added_bits} (blowup {}×). `cold` builds {} coset-twiddle tables; `warm` reuses them.\n   \
         Counts are scalar-equivalent BabyBear ops.\n",
        1 << added_bits,
        1 << added_bits
    );
    println!(
        "   {:>4} {:>5} {:>12} {:>12} {:>12} {:>9} {:>12}",
        "h", "w", "cold M+A+S", "warm M+A+S", "twiddle term", "share", "twid/coset"
    );
    for h in [8usize, 16, 64] {
        for w in [4usize, 8, 16, 32, 64, 236] {
            let (cold, warm) = cold_warm_split(h, w, added_bits, 1);
            let c = cold.mul + cold.add + cold.sub;
            let wm = warm.mul + warm.add + warm.sub;
            let t = c - wm;
            println!(
                "   {h:>4} {w:>5} {c:>12} {wm:>12} {t:>12} {:>8.2}% {:>12.2}",
                100.0 * t as f64 / c as f64,
                t as f64 / (1u64 << added_bits) as f64
            );
        }
    }
    println!(
        "\n   ⚑ READ THE `twiddle term` COLUMN DOWN EACH `h` BLOCK: it does not move with `w`, so\n   \
         its SHARE falls as 1/w — 9.1% of a width-4 call at h=64 against 0.17% of a width-236 one.\n   \
         ⚠ THAT IS A COUNT, AND THE COUNT IS NOT THE COST: §G6c measures the same cold-vs-warm\n   \
         split on a CLOCK and finds it is noise. The width-independent TIME is elsewhere (§G6d/e).\n   \
         Kept because a plausible width-independent term that turns out not to be the mechanism is\n   \
         the thing a reader most needs to see eliminated.\n   \
         (⚠ the h=64 rows are ~2.5× the closed form 63+2·15=93: `Powers::collect_n` takes a\n   \
         PARALLEL path at n ≥ 16, so those cells are thread-count dependent. h=8 and h=16 match\n   \
         13 and 27 exactly.)"
    );

    // The claim the column makes, asserted rather than left to the reader.
    for h in [8usize, 16, 64] {
        let terms: Vec<u64> = [4usize, 8, 16, 32, 64, 236]
            .into_iter()
            .map(|w| {
                let (c, wm) = cold_warm_split(h, w, added_bits, 1);
                (c.mul + c.add + c.sub) - (wm.mul + wm.add + wm.sub)
            })
            .collect();
        assert!(
            terms.iter().all(|t| *t == terms[0]),
            "h={h}: the cold−warm term must be identical at every width (it is width-independent); got {terms:?}"
        );
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// §G7 — THE BATCHING: correctness first, then counts, then a labelled clock
//
// §G6 says the per-coset overhead is a function of `(h, added_bits)` and not of `w`. That names
// the fix AND its grouping: batch every chunk that shares a height, because those are exactly the
// calls that would otherwise rebuild the same `2^added_bits` tables. The IR-v2 prover's chunks
// group by AIR and an AIR's chunks all have one height, so the grouping is "one call per AIR" —
// widths 8, 32, 8 for the three AIRs, which is the shape `field-op-counts.md` §G1 Finding 3 named.
//
// `p3_fri::batched_chunk_ldes` is the deployed implementation; these tests call THAT function, not
// a re-derivation of it, so a divergence between instrument and prover is not possible here.
// ─────────────────────────────────────────────────────────────────────────────

fn filler_matrix_p3(height: usize, width: usize) -> RowMajorMatrix<P3BabyBear> {
    let values = (0..height * width)
        .map(|i| P3BabyBear::from_u32((i as u32).wrapping_mul(2_654_435_761) | 1))
        .collect();
    RowMajorMatrix::new(values, width)
}

/// The unbatched path, verbatim from `two_adic_pcs.rs`'s pre-DELTA-3 `get_quotient_ldes` body.
fn per_chunk_ldes<F: TwoAdicField + Ord>(
    dft: &Radix2DitParallel<F>,
    added_bits: usize,
    shifts: &[F],
    mats: Vec<RowMajorMatrix<F>>,
) -> Vec<RowMajorMatrix<F>> {
    use p3_matrix::bitrev::BitReversibleMatrix;
    shifts
        .iter()
        .zip(mats)
        .map(|(s, m)| {
            dft.coset_lde_batch(m, added_bits, *s)
                .bit_reverse_rows()
                .to_row_major_matrix()
        })
        .collect()
}

/// **§G7a — THE CORRECTNESS OBLIGATION: the batch returns the same matrices, element for element.**
///
/// The quotient chunks are committed as separate matrices because the verifier opens them
/// separately, so a batching that changed what those matrices ARE would be a wire change. This
/// asserts it does not: at the prover's real geometry and its real `ω^-i` shifts, at every blowup
/// in range, the batched result equals the per-chunk result exactly. Deployed types
/// (`P3BabyBear`, `Radix2DitParallel`), no counting newtype, nothing generic left free.
#[test]
fn batched_chunk_ldes_are_bit_identical() {
    for added_bits in 3..=7usize {
        for (h, n) in QUOTIENT_CHUNK_GEOMETRY {
            let shifts = chunk_lde_shifts(h, n);
            let mats: Vec<_> = (0..n)
                .map(|c| filler_matrix_p3(h, 4).clone_with_offset(c))
                .collect();

            let dft_a: Radix2DitParallel<P3BabyBear> = Radix2DitParallel::default();
            let want = per_chunk_ldes(&dft_a, added_bits, &shifts, mats.clone());

            let dft_b: Radix2DitParallel<P3BabyBear> = Radix2DitParallel::default();
            let got = p3_fri::batched_chunk_ldes(&dft_b, added_bits, &shifts, mats);

            assert_eq!(want.len(), got.len(), "chunk count preserved");
            for (i, (a, b)) in want.iter().zip(&got).enumerate() {
                assert_eq!(a.width, b.width, "b={added_bits} h={h} chunk {i} width");
                assert_eq!(
                    a.values, b.values,
                    "b={added_bits} h={h} chunk {i}: batched LDE differs from per-chunk LDE"
                );
            }
        }
    }
    println!(
        "\n═══ §G7a BATCHED == PER-CHUNK, element for element ═══\n   \
         Checked at added_bits 3..=7 × the three real chunk geometries (h=64 n=2, h=8 n=8,\n   \
         h=16 n=2) with the prover's real `ω^-i` shifts, over deployed `P3BabyBear` /\n   \
         `Radix2DitParallel`. ⇒ the MMCS batch, the opening rounds and the verifier see an\n   \
         IDENTICAL object. No wire change, no VK change, no flag day."
    );
}

/// A distinct filler per chunk, so an equality test cannot pass by every chunk being the same.
trait CloneWithOffset {
    fn clone_with_offset(self, k: usize) -> Self;
}
impl CloneWithOffset for RowMajorMatrix<P3BabyBear> {
    fn clone_with_offset(mut self, k: usize) -> Self {
        for (i, v) in self.values.iter_mut().enumerate() {
            *v += P3BabyBear::from_u32((k as u32 + 1).wrapping_mul(i as u32 | 7));
        }
        self
    }
}

/// **§G7b — the batching in EXACT COUNTS.** Both paths run over the counting field, on one fresh
/// `Radix2DitParallel<CountedBabyBear>` each (a prover builds a fresh `Pcs` per proof, so the
/// twiddle memo really does start cold), in the real call order. The batched column INCLUDES the
/// coefficient prescale, because the counted run calls the deployed `batched_chunk_ldes` itself.
#[test]
fn batched_chunk_ldes_op_counts() {
    println!(
        "\n═══ §G7b QUOTIENT-CHUNK LDE, PER-CHUNK vs BATCHED — scalar-equivalent ops ═══\n   \
         Geometry per proof: 2×(h=64,w=4) + 8×(h=8,w=4) + 2×(h=16,w=4) ⇒ batched widths 8 / 32 / 8."
    );
    println!(
        "\n   {:>3} {:>7} {:>14} {:>14} {:>10} {:>9}",
        "b", "calls", "per-chunk M+A+S", "batched M+A+S", "saved", "saved %"
    );
    let mut rows = Vec::new();
    for added_bits in 3..=7usize {
        let mut narrow = OpCounts::default();
        let mut batched = OpCounts::default();
        let mut narrow_calls = 0usize;
        let mut batched_calls = 0usize;

        // One `Dft` per path per proof, exactly as the prover has one per config.
        let dft_a: Radix2DitParallel<CountedBabyBear> = Radix2DitParallel::default();
        let dft_b: Radix2DitParallel<CountedBabyBear> = Radix2DitParallel::default();

        for (h, n) in QUOTIENT_CHUNK_GEOMETRY {
            let shifts: Vec<CountedBabyBear> = chunk_lde_shifts(h, n)
                .into_iter()
                .map(CountedBabyBear)
                .collect();
            let mats: Vec<_> = (0..n).map(|_| filler_matrix(h, 4)).collect();

            let base = OpCounts::read();
            std::hint::black_box(per_chunk_ldes(&dft_a, added_bits, &shifts, mats.clone()));
            narrow.add_in(OpCounts::since(base));
            narrow_calls += n;

            let base = OpCounts::read();
            std::hint::black_box(p3_fri::batched_chunk_ldes(
                &dft_b, added_bits, &shifts, mats,
            ));
            batched.add_in(OpCounts::since(base));
            batched_calls += 1;
        }

        let nt = narrow.mul + narrow.add + narrow.sub;
        let bt = batched.mul + batched.add + batched.sub;
        println!(
            "   {added_bits:>3} {:>7} {nt:>14} {bt:>14} {:>10} {:>8.1}%",
            format!("{narrow_calls}→{batched_calls}"),
            nt as i64 - bt as i64,
            100.0 * (nt as f64 - bt as f64) / nt as f64
        );
        rows.push((added_bits, nt, bt));
    }
    println!(
        "\n   ⚑ The arithmetic saving is REAL but SMALL — it is `n-1` iDFTs and the duplicated\n   \
         coset-twiddle tables, minus the prescale. That is the point of §G6: the 27× per-call\n   \
         asymmetry §G1 Finding 2 measured was never in the op count, so an arithmetic optimisation\n   \
         aimed here would have bought nothing. What the batch removes is the per-CALL, per-COSET\n   \
         overhead a counter cannot see — see §G7c."
    );
    for (b, nt, bt) in rows {
        assert!(
            bt <= nt,
            "b={b}: batched must not do more arithmetic ({bt} > {nt})"
        );
    }
}

/// **§G7c — the wall-clock upper bound, labelled.** ⚠ This box is contended; the estimator is
/// min-of-N, which finds one un-preempted window if there is one, and a MINIMUM under load is an
/// UPPER BOUND on the true time. Both paths pay the same contention, so the RATIO is the durable
/// quantity; the absolute ms are not.
#[test]
fn batched_chunk_ldes_wallclock() {
    const N: usize = 40;
    println!(
        "\n═══ §G7c QUOTIENT-CHUNK LDE WALL CLOCK — min of {N}, fresh `Dft` per iteration ═══\n   \
         ⚠ UPPER BOUND on a contended box. RAYON_NUM_THREADS={}. Deployed `P3BabyBear`.\n",
        std::env::var("RAYON_NUM_THREADS").unwrap_or_else(|_| "default".into())
    );
    println!(
        "   {:>3} {:>12} {:>12} {:>9} {:>14}",
        "b", "per-chunk ms", "batched ms", "speedup", "saved ms"
    );
    for added_bits in 3..=7usize {
        let work: Vec<(Vec<P3BabyBear>, Vec<RowMajorMatrix<P3BabyBear>>)> = QUOTIENT_CHUNK_GEOMETRY
            .iter()
            .map(|&(h, n)| {
                (
                    chunk_lde_shifts(h, n),
                    (0..n).map(|_| filler_matrix_p3(h, 4)).collect(),
                )
            })
            .collect();

        let narrow_ns = min_ns(N, 1, || {
            let dft: Radix2DitParallel<P3BabyBear> = Radix2DitParallel::default();
            for (shifts, mats) in &work {
                std::hint::black_box(per_chunk_ldes(&dft, added_bits, shifts, mats.clone()));
            }
        });
        let batched_ns = min_ns(N, 1, || {
            let dft: Radix2DitParallel<P3BabyBear> = Radix2DitParallel::default();
            for (shifts, mats) in &work {
                std::hint::black_box(p3_fri::batched_chunk_ldes(
                    &dft,
                    added_bits,
                    shifts,
                    mats.clone(),
                ));
            }
        });
        println!(
            "   {added_bits:>3} {:>12.3} {:>12.3} {:>8.2}× {:>14.3}",
            narrow_ns / 1e6,
            batched_ns / 1e6,
            narrow_ns / batched_ns,
            (narrow_ns - batched_ns) / 1e6
        );
    }
}

/// **§G6c — the per-coset constant, in wall clock, split into twiddle-table and butterfly.**
///
/// §G6b isolates the width-independent term in *counts*; counts cannot see allocation, a
/// `spin::RwLock` write, a `BTreeMap` insert or a rayon dispatch, and §G1 Finding 2 is precisely a
/// phase whose time is not its count. This measures the same split on a clock: one
/// `coset_lde_batch` on a **cold** memo against the identical call on a **warm** one, **one call
/// per timing window in both arms** so the two windows differ only by the `2^added_bits`
/// coset-twiddle tables.
///
/// ⚠ The first cut of this test timed `cold` against a window containing *two* calls and
/// subtracted — and reported NEGATIVE twiddle costs at 11 of 14 geometries, because the second
/// call in a window allocates its output while the first is still live and pays for that, not for
/// the memo. A min-of-mins over differently-shaped windows is not a difference. Recorded because
/// the broken version looked plausible and printed a full table.
///
/// ⚠ Run with `RAYON_NUM_THREADS=1`. §G5 failed on this box because rayon dispatch under load
/// swamped every geometry at a flat 2.7–6.0 ms floor; one thread removes that term and the numbers
/// become monotone in the work — which is what §G5 said the next measurement needed.
#[test]
fn per_coset_constant_wallclock() {
    const N: usize = 60;
    println!(
        "\n═══ §G6c THE PER-COSET CONSTANT ON A CLOCK — cold memo vs warm memo ═══\n   \
         ⚠ min of {N}, UPPER BOUND on a contended box. RAYON_NUM_THREADS={}.\n   \
         Both arms: ONE `coset_lde_batch` per window. `cold` builds 2^b coset-twiddle tables.\n",
        std::env::var("RAYON_NUM_THREADS").unwrap_or_else(|_| "default".into())
    );
    println!(
        "   {:>4} {:>5} {:>4} {:>11} {:>11} {:>12} {:>13} {:>10}",
        "h", "w", "+b", "cold µs", "warm µs", "twiddle µs", "twid/coset µs", "twid %"
    );
    for added_bits in [3usize, 6] {
        for (h, w) in [
            (64usize, 4usize),
            (64, 8),
            (8, 4),
            (8, 32),
            (16, 4),
            (16, 8),
            (64, 236),
        ] {
            let cold = min_ns(N, 1, || {
                let dft: Radix2DitParallel<P3BabyBear> = Radix2DitParallel::default();
                std::hint::black_box(dft.coset_lde_batch(
                    filler_matrix_p3(h, w),
                    added_bits,
                    P3BabyBear::ONE,
                ));
            });
            let dft_warm: Radix2DitParallel<P3BabyBear> = Radix2DitParallel::default();
            std::hint::black_box(dft_warm.coset_lde_batch(
                filler_matrix_p3(h, w),
                added_bits,
                P3BabyBear::ONE,
            ));
            let warm = min_ns(N, 1, || {
                std::hint::black_box(dft_warm.coset_lde_batch(
                    filler_matrix_p3(h, w),
                    added_bits,
                    P3BabyBear::ONE,
                ));
            });
            let twid = cold - warm;
            println!(
                "   {h:>4} {w:>5} {added_bits:>4} {:>11.1} {:>11.1} {:>12.1} {:>13.3} {:>9.1}%",
                cold / 1e3,
                warm / 1e3,
                twid / 1e3,
                twid / 1e3 / (1u64 << added_bits) as f64,
                100.0 * twid / cold
            );
        }
    }
    println!(
        "\n   ⚑ `twid/coset` is the width-independent per-coset constant a NARROW call cannot\n   \
         amortise. Compare the `w` pairs at one `h`: the µs stay put while the work multiplies.\n   \
         That constant, times (calls × 2^b), is what the batching removes."
    );
}

/// **§G6d — THE MECHANISM, isolated: the cost tracks the COSET COUNT, not the output size.**
///
/// §G6c refuted the twiddle-table hypothesis on a clock (cold−warm is sign-random noise). What is
/// left in `coset_lde_batch_with_transform` that is paid `2^added_bits` times and depends on
/// neither `w` nor `h` is the **per-coset `coset_dft_oop` call itself** — a `first_half_general_oop`
/// and a `second_half_general`, each a `p3_maybe_rayon` parallel dispatch, plus a
/// `reverse_matrix_index_bits`, on a matrix that at `w = 4` is 256 elements.
///
/// This holds the OUTPUT SIZE fixed at `h · 2^added_bits = 4096` and slides the split. Total
/// butterfly work is `Θ(4096 · w · log h)` — it *falls* as `added_bits` rises. If the cost tracked
/// work, the last row would be the cheapest. If it tracks the coset count, it doubles per rung.
#[test]
fn cost_tracks_coset_count_not_work() {
    const N: usize = 40;
    const OUT: usize = 4096;
    println!(
        "\n═══ §G6d FIXED OUTPUT SIZE h·2^b = {OUT}, SLIDING THE SPLIT ═══\n   \
         ⚠ min of {N}, RAYON_NUM_THREADS={}. Output is {OUT}×w in EVERY row.\n",
        std::env::var("RAYON_NUM_THREADS").unwrap_or_else(|_| "default".into())
    );
    for w in [4usize, 64] {
        println!("   ── w = {w}");
        println!(
            "   {:>6} {:>7} {:>7} {:>11} {:>14} {:>16}",
            "h", "+b", "cosets", "µs", "µs/coset", "rel. work Θ(log h)"
        );
        let mut prev = f64::NAN;
        for added_bits in 0..=9usize {
            let h = OUT >> added_bits;
            let ns = min_ns(N, 1, || {
                let dft: Radix2DitParallel<P3BabyBear> = Radix2DitParallel::default();
                std::hint::black_box(dft.coset_lde_batch(
                    filler_matrix_p3(h, w),
                    added_bits,
                    P3BabyBear::ONE,
                ));
            });
            println!(
                "   {h:>6} {added_bits:>7} {:>7} {:>11.1} {:>14.3} {:>16.2}  {}",
                1usize << added_bits,
                ns / 1e3,
                ns / 1e3 / (1usize << added_bits) as f64,
                p3_util::log2_strict_usize(h) as f64 / 12.0,
                if prev.is_nan() {
                    String::new()
                } else {
                    format!("{:.2}× prev", ns / prev)
                }
            );
            prev = ns;
        }
    }
    println!(
        "\n   ⚑ Work FALLS monotonically down each block (the `log h` column) while the clock\n   \
         RISES with the coset count. The cost of a `coset_lde_batch` is `2^added_bits` × a\n   \
         constant that depends on neither the width nor the height — a per-coset CALL constant.\n   \
         ⇒ batching `k` same-height calls into one divides that term by exactly `k`, and nothing\n   \
         about the arithmetic changes. That is why §G7c measures ~4× on a 12→3 batch."
    );
}

/// **§G6e — WHAT the per-coset constant IS: a cold rayon hand-off, and a second free win.**
///
/// §G6d pins the constant at ~10–15 µs per coset, independent of `h` and `w`. The only thing in
/// `coset_dft_oop` with that shape is its `p3_maybe_rayon` parallel dispatches
/// (`first_half_general_oop`, `second_half_general`, `reverse_matrix_index_bits`). Rayon's
/// `par_*` from a thread that is **not itself a pool worker** takes `Registry::in_worker_cold`:
/// the caller parks on a latch while a worker picks the job up — a full cross-thread round trip,
/// paid per dispatch, per coset, per call, and utterly independent of how much work the job does.
///
/// The test: run the identical workload from the calling thread and again inside
/// `ThreadPool::install`, which makes the caller a worker so every nested dispatch is warm.
///
/// ⚠ If this shows a large gap, it is a SECOND optimisation of the same kind, available to the
/// whole prover for the price of one `install` at the top — and it is NOT taken by this lane.
#[test]
fn per_coset_constant_is_a_cold_rayon_handoff() {
    const N: usize = 30;
    let threads: usize = std::env::var("RAYON_NUM_THREADS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(rayon::current_num_threads);
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(threads)
        .build()
        .expect("pool");

    println!(
        "\n═══ §G6e THE PER-COSET CONSTANT — caller-thread vs INSIDE the rayon pool ═══\n   \
         ⚠ min of {N}, {threads} rayon thread(s). Workload: the real quotient-chunk LDEs,\n   \
         both layouts × both call sites, so the two optimisations can be read against each other.\n"
    );
    println!(
        "   {:>3} {:>13} {:>13} {:>13} {:>13} {:>10} {:>10}",
        "b", "12× caller", "3× caller", "12× pool", "3× pool", "batch gain", "pool gain"
    );
    for added_bits in [3usize, 6] {
        let work: Vec<(Vec<P3BabyBear>, Vec<RowMajorMatrix<P3BabyBear>>)> = QUOTIENT_CHUNK_GEOMETRY
            .iter()
            .map(|&(h, n)| {
                (
                    chunk_lde_shifts(h, n),
                    (0..n).map(|_| filler_matrix_p3(h, 4)).collect(),
                )
            })
            .collect();
        let narrow = || {
            let dft: Radix2DitParallel<P3BabyBear> = Radix2DitParallel::default();
            for (shifts, mats) in &work {
                std::hint::black_box(per_chunk_ldes(&dft, added_bits, shifts, mats.clone()));
            }
        };
        let batched = || {
            let dft: Radix2DitParallel<P3BabyBear> = Radix2DitParallel::default();
            for (shifts, mats) in &work {
                std::hint::black_box(p3_fri::batched_chunk_ldes(
                    &dft,
                    added_bits,
                    shifts,
                    mats.clone(),
                ));
            }
        };
        let n_out = min_ns(N, 1, narrow);
        let b_out = min_ns(N, 1, batched);
        let n_in = pool.install(|| min_ns(N, 1, narrow));
        let b_in = pool.install(|| min_ns(N, 1, batched));
        println!(
            "   {added_bits:>3} {:>13.3} {:>13.3} {:>13.3} {:>13.3} {:>9.2}× {:>9.2}×",
            n_out / 1e6,
            b_out / 1e6,
            n_in / 1e6,
            b_in / 1e6,
            n_out / b_out,
            n_out / n_in
        );
    }
    println!(
        "\n   ⚑ READ THE LAST TWO COLUMNS TOGETHER. Both optimisations attack the SAME per-coset\n   \
         constant: the batch divides the number of times it is paid, the pool makes each one\n   \
         cheap. They therefore DO NOT COMPOSE MULTIPLICATIVELY — compare `3× pool` against\n   \
         `12× pool` to see what the batching is still worth once the hand-off is warm."
    );
}

type PlainPcs = TwoAdicFriPcs<P3BabyBear, Radix2DitParallel<P3BabyBear>, ValMmcs, ChallengeMmcs>;
type PlainConfig = StarkConfig<PlainPcs, Ef, Challenger>;

fn plain_config(log_blowup: usize, num_queries: usize, pow: usize) -> PlainConfig {
    let perm = default_babybear_poseidon2_16();
    let hash = Hash::new(perm.clone());
    let compress = Compress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress, 0);
    let fri_params = FriParameters {
        log_blowup,
        log_final_poly_len: 0,
        max_log_arity: 3,
        num_queries,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: pow,
        mmcs: ChallengeMmcs::new(val_mmcs.clone()),
    };
    StarkConfig::new(
        TwoAdicFriPcs::new(Radix2DitParallel::default(), val_mmcs, fri_params),
        Challenger::new(perm),
    )
}

/// **§G6f — the same cold-hand-off question, asked of the WHOLE prover.**
///
/// §G6e prices it on the quotient-chunk LDEs alone, where the matrices are 256 elements and a
/// cross-thread hand-off has nothing to amortise against. A whole prove is mostly big matrices and
/// a Merkle build, so the honest question is what fraction of the *prover* this reaches. Same
/// workload, same config, deployed `Radix2DitParallel`; the only difference is whether the calling
/// thread is a rayon worker.
///
/// ⚠ NOT TAKEN BY THIS LANE. It is a one-line change at the prover entry point and it belongs to
/// whoever owns that entry point, with its own before/after. Recorded here because the number is
/// the reason to do it.
#[test]
fn whole_prove_inside_the_rayon_pool() {
    const N: usize = 5;
    let threads: usize = std::env::var("RAYON_NUM_THREADS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(rayon::current_num_threads);
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(threads)
        .build()
        .expect("pool");
    let w = transfer_workload();

    println!(
        "\n═══ §G6f WHOLE PROVE — caller-thread vs INSIDE the rayon pool ═══\n   \
         ⚠ min of {N}, {threads} rayon thread(s), q=19 pow=0, contended box (UPPER BOUNDS).\n"
    );
    println!(
        "   {:>3} {:>16} {:>16} {:>10}",
        "b", "from caller ms", "inside pool ms", "speedup"
    );
    for lb in [3usize, 6] {
        let run = || {
            let config = plain_config(lb, 19, 0);
            let proof = prove_vm_descriptor2_for_config(
                &w.desc,
                &w.base_trace,
                &w.pis,
                &MemBoundaryWitness::default(),
                &[],
                &UMemBoundaryWitness::default(),
                &config,
            )
            .expect("proves");
            std::hint::black_box(&proof);
        };
        let outside = min_ns(N, 1, run);
        let inside = pool.install(|| min_ns(N, 1, run));
        println!(
            "   {lb:>3} {:>16.3} {:>16.3} {:>9.2}×",
            outside / 1e6,
            inside / 1e6,
            outside / inside
        );
    }
}
