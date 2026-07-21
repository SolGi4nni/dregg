//! The CARRY-FREE ADDITIVE fold — codex Round-3 Q1's Tier-0 speed lever, MEASURED.
//!
//! The exact-integer TFHE clear (`crate::fhe_clear`) folds the per-order unary
//! price-bucket increments with `FheUint32::sum`, and the MEASURED envelope
//! (`MEASURED-ENVELOPE.md`, `HBOX-24CORE-ENVELOPE.md`) showed the load-bearing
//! finding: a multi-block radix add **carry-propagates**, and carry propagation
//! is PBS-class (~13 ms/element even in the deferred-carry tree-sum), so the
//! aggregation DOMINATES the clear (up to 45× the O(K) crossing). The estimates'
//! "addition ≈ µs, the cheap primitive" is only true for an ADDITIVE scheme.
//!
//! This module builds that additive scheme for real and measures it. The carrier
//! is **BFV** (`fhe.rs`) — an exact-quantized `R_q = Z_q[X]/(X^n+1)` ring scheme,
//! SIMD-batched into `n` plaintext slots, whose ciphertext addition is a native
//! modular polynomial add: **no carry propagation, no bootstrap, no PBS**. This
//! is exactly the "exact quantized BFV/BGV for the carry-free fold" of
//! `docs/deos/FHEGG-CODEX-ROUND3.md` §B/Q1 (CKKS is the approximate cousin, not
//! available in tfhe-rs; BFV is the exact additive path and the one codex named
//! for the *auction* fold specifically — CKKS is for the T-step PDHG search).
//!
//! The SIMD packing is the structural win over TFHE. TFHE packs one integer per
//! `FheUint32` and must sum each of the K buckets separately: 2·K bucket-sums,
//! each over ~N/2 carry-propagating adds → O(N·K) PBS-class work. BFV packs the
//! WHOLE K-bucket increment vector of one order into a SINGLE ciphertext (K ≤ n
//! slots), so folding N orders is just **N ciphertext additions total** from
//! zero accumulators (one running sum for demand, one for supply), each a
//! carry-free poly add that updates all K buckets at once. O(N) carry-free adds
//! vs O(N·K) PBS adds.
//!
//! The crossing is a comparison, and there is no comparison from additive
//! homomorphism alone. It is deliberately NOT done here. The production-shaped
//! path returns strict [`LeanCiphertext`] curves from [`CollectiveOrderFoldEngine`]
//! and feeds them to `crate::boundary`: the parties mask and threshold-open only
//! a one-time-padded value, locally derive shares, and run the boolean MPC crossing.
//! No scheme switch or clear curve is required. The older [`bfv_fold`] harness
//! below still recovers p*/V* from decrypted curves solely as a single-key oracle;
//! that clear-domain crossing is not part of the additive protocol cost.
//!
//! Mint-safety: the fold's quantization is the deployable floor/ceil quantizer
//! proven mint-safe in `metatheory/Market/MintSafeQuantization.lean`
//! (`mint_safe_floor_ceil`: floor inputs, ceil outputs, at step Δ; the integer
//! gate `Σ⌈vout/Δ⌉ ≤ Σ⌊vin/Δ⌋` provably forbids `Σvout > Σvin`). See `mint_safe`.

use std::sync::Arc;
use std::time::{Duration, Instant};
use std::{fmt, mem};

use fhe::bfv::{BfvParameters, Ciphertext, Encoding, Plaintext, PublicKey, SecretKey};
use fhe_traits::{FheDecoder, FheDecrypter, FheEncoder, FheEncrypter, Serialize as FheSerialize};
use rand_09::rngs::StdRng as StdRng09;
use rand_09::SeedableRng as SeedableRng09;

use crate::bfv_lean::{BfvLeanError, LeanCiphertext};
use crate::gpu_arena::{FoldBackend, FoldCapacity, FoldEngine, ResidentFoldPlan};
use crate::threshold::{BfvParams, CollectivePublicKey};
use crate::{order_increment, Order, Side};

/// Fail-closed errors from the collective-key order-fold consumer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CollectiveFoldError {
    InvalidBucketCount { k: usize, degree: usize },
    EmptySide(&'static str),
    Crypto(&'static str),
    Fold(BfvLeanError),
}

impl fmt::Display for CollectiveFoldError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidBucketCount { k, degree } => {
                write!(f, "K={k} is outside the BFV SIMD degree 1..={degree}")
            }
            Self::EmptySide(side) => write!(f, "collective order row batch has no {side} row"),
            Self::Crypto(phase) => write!(f, "fhe.rs failed during collective-key {phase}"),
            Self::Fold(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for CollectiveFoldError {}

impl From<BfvLeanError> for CollectiveFoldError {
    fn from(value: BfvLeanError) -> Self {
        Self::Fold(value)
    }
}

pub type CollectiveFoldResult<T> = std::result::Result<T, CollectiveFoldError>;

/// One encrypted unary order row accepted by the collective-key fold.
///
/// [`encrypt_collective_order_rows`] constructs these under a [`CollectivePublicKey`].
/// [`CollectiveOrderRow::from_lean`] is the transport ingress for an already parsed row: it checks
/// slot capacity, while [`CollectiveOrderFoldEngine::fold_rows`] validates the complete batch shape.
/// BFV ciphertexts do not carry a verifiable public-key identity or a range proof. Authenticating the
/// submitting party and binding `plain_bound` to the encrypted row remain host/range-proof obligations.
#[derive(Clone, Debug)]
pub struct CollectiveOrderRow {
    side: Side,
    ciphertext: LeanCiphertext,
}

impl CollectiveOrderRow {
    pub fn from_lean(
        side: Side,
        ciphertext: LeanCiphertext,
        k: usize,
    ) -> CollectiveFoldResult<Self> {
        if k == 0 || k > ciphertext.degree {
            return Err(CollectiveFoldError::InvalidBucketCount {
                k,
                degree: ciphertext.degree,
            });
        }
        validate_collective_lean(&ciphertext)?;
        Ok(Self { side, ciphertext })
    }

    pub fn side(&self) -> Side {
        self.side
    }

    pub fn ciphertext(&self) -> &LeanCiphertext {
        &self.ciphertext
    }

    pub fn into_ciphertext(self) -> LeanCiphertext {
        self.ciphertext
    }
}

/// Costs paid once while turning plaintext trader-side unary rows into strict `LeanCiphertext` ingress.
///
/// The serialization bridge is explicit because `fhe.rs::Ciphertext` keeps its coefficient storage
/// crate-private. Its public API offers no coefficient-row borrow from which `LeanCiphertext` could be
/// built zero-copy. `wire_ingress` therefore measures `Ciphertext::to_bytes` plus the strict canonical
/// [`LeanCiphertext::from_fhe_bytes`] parse; it is not folded into the GPU timing.
#[derive(Clone, Copy, Debug, Default)]
pub struct CollectiveIngressTiming {
    pub rows: usize,
    pub encode: Duration,
    pub encrypt: Duration,
    pub wire_ingress: Duration,
}

/// Backend, adapter-capacity, execution-plan, and wall-clock metadata for one side of the book.
#[derive(Clone, Copy, Debug)]
pub struct CollectiveFoldPhase {
    pub input_ciphertexts: usize,
    /// Raw resident payload bytes per ciphertext (2 polys × RNS rows × degree × 8).
    pub ciphertext_bytes: u64,
    /// Exact adapter capacity for this ciphertext shape when GPU ran; `None` on a labelled CPU fallback.
    pub capacity: Option<FoldCapacity>,
    /// Exact upload/reduction plan when GPU ran; `None` on a labelled CPU fallback.
    pub plan: Option<ResidentFoldPlan>,
    pub backend: FoldBackend,
    /// Whole paired FoldEngine call: validation + both folds + one shared GPU readback/device wait, or
    /// both CPU folds on fallback. Demand and supply report the same shared wall time intentionally.
    pub elapsed: Duration,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct CollectiveFoldTiming {
    pub n_rows: usize,
    pub k: usize,
    /// Host-only vector partitioning. Ciphertext row allocations are moved, not cloned.
    pub partition: Duration,
}

/// Collective-key folded curves, still encrypted and directly consumable by
/// [`crate::boundary::MaskedDecryptSession`]. No joint [`SecretKey`] is constructed or returned.
#[derive(Debug)]
pub struct CollectiveFoldedBook {
    pub d_ct: LeanCiphertext,
    pub s_ct: LeanCiphertext,
    pub timing: CollectiveFoldTiming,
    pub demand: CollectiveFoldPhase,
    pub supply: CollectiveFoldPhase,
}

/// Retained order-fold consumer. Its [`FoldEngine`] owns/reuses one wgpu device and pipeline; repeated
/// books therefore do not pay adapter/pipeline initialization on every call.
pub struct CollectiveOrderFoldEngine {
    fold_engine: FoldEngine,
}

impl CollectiveOrderFoldEngine {
    pub fn new() -> Self {
        Self {
            fold_engine: FoldEngine::new(),
        }
    }

    /// Explicit policy/headless path whose output is still byte-identical to the CPU fold oracle.
    pub fn cpu_only() -> Self {
        Self {
            fold_engine: FoldEngine::cpu_only(),
        }
    }

    pub fn has_gpu_arena(&self) -> bool {
        self.fold_engine.has_gpu_arena()
    }

    /// Fold already-ingressed rows. Ownership is consumed so the demand/supply partition moves each
    /// `LeanCiphertext`; it does not clone the large RNS row allocations.
    pub fn fold_rows(
        &self,
        rows: Vec<CollectiveOrderRow>,
        k: usize,
        plaintext_modulus: u64,
    ) -> CollectiveFoldResult<CollectiveFoldedBook> {
        let n_rows = rows.len();
        let t0 = Instant::now();
        let mut demand_rows = Vec::new();
        let mut supply_rows = Vec::new();
        for row in rows {
            if k == 0 || k > row.ciphertext.degree {
                return Err(CollectiveFoldError::InvalidBucketCount {
                    k,
                    degree: row.ciphertext.degree,
                });
            }
            match row.side {
                Side::Bid => demand_rows.push(row.ciphertext),
                Side::Ask => supply_rows.push(row.ciphertext),
            }
        }
        let partition = t0.elapsed();
        if demand_rows.is_empty() {
            return Err(CollectiveFoldError::EmptySide("demand"));
        }
        if supply_rows.is_empty() {
            return Err(CollectiveFoldError::EmptySide("supply"));
        }

        // Demand and supply have the same BFV shape. Folding them as a pair keeps their kernels
        // independent but concatenates the two resident outputs for one MAP_READ and one device wait.
        let fold_started = Instant::now();
        let (demand_execution, supply_execution) =
            self.fold_engine
                .fold_pair(&demand_rows, &supply_rows, plaintext_modulus)?;
        let paired_elapsed = fold_started.elapsed();
        let (d_ct, demand) = fold_phase(
            &self.fold_engine,
            &demand_rows,
            demand_execution,
            paired_elapsed,
        )?;
        let (s_ct, supply) = fold_phase(
            &self.fold_engine,
            &supply_rows,
            supply_execution,
            paired_elapsed,
        )?;
        Ok(CollectiveFoldedBook {
            d_ct,
            s_ct,
            timing: CollectiveFoldTiming {
                n_rows,
                k,
                partition,
            },
            demand,
            supply,
        })
    }

    /// Complete producer/consumer call: collective-key encryption → one strict wire parse at ingress →
    /// retained resident GPU fold (or explicitly reported CPU fallback). The output contains no secret key.
    pub fn fold_orders(
        &self,
        orders: &[Order],
        k: usize,
        params: &BfvParams,
        public_key: &CollectivePublicKey,
    ) -> CollectiveFoldResult<(CollectiveFoldedBook, CollectiveIngressTiming)> {
        let (rows, ingress) = encrypt_collective_order_rows(orders, k, params, public_key)?;
        let folded = self.fold_rows(rows, k, params.plaintext_modulus())?;
        Ok((folded, ingress))
    }
}

impl Default for CollectiveOrderFoldEngine {
    fn default() -> Self {
        Self::new()
    }
}

fn ciphertext_bytes(ct: &LeanCiphertext) -> CollectiveFoldResult<u64> {
    let lanes = ct
        .polys
        .len()
        .checked_mul(ct.moduli.len())
        .and_then(|n| n.checked_mul(ct.degree))
        .and_then(|n| n.checked_mul(mem::size_of::<u64>()))
        .ok_or(BfvLeanError::Incompatible(
            "collective fold: ciphertext shape byte count overflows host address space",
        ))?;
    u64::try_from(lanes)
        .map_err(|_| {
            BfvLeanError::Incompatible("collective fold: ciphertext shape byte count exceeds u64")
        })
        .map_err(CollectiveFoldError::from)
}

fn validate_collective_lean(ct: &LeanCiphertext) -> CollectiveFoldResult<()> {
    if ct.moduli.is_empty() || ct.degree == 0 || ct.polys.len() != 2 {
        return Err(BfvLeanError::Incompatible(
            "collective fold: ciphertext is not a nonempty two-polynomial fold shape",
        )
        .into());
    }
    for poly in &ct.polys {
        if poly.rows.len() != ct.moduli.len() {
            return Err(BfvLeanError::Incompatible(
                "collective fold: polynomial RNS row count differs from modulus count",
            )
            .into());
        }
        for (modulus_index, (row, &modulus)) in poly.rows.iter().zip(ct.moduli.iter()).enumerate() {
            if modulus == 0 || row.len() != ct.degree {
                return Err(BfvLeanError::Incompatible(
                    "collective fold: invalid modulus or RNS row length",
                )
                .into());
            }
            if row.iter().any(|&coefficient| coefficient >= modulus) {
                return Err(BfvLeanError::NonCanonical { modulus_index }.into());
            }
        }
    }
    Ok(())
}

fn fold_phase(
    engine: &FoldEngine,
    rows: &[LeanCiphertext],
    execution: crate::gpu_arena::FoldExecution,
    paired_elapsed: Duration,
) -> CollectiveFoldResult<(LeanCiphertext, CollectiveFoldPhase)> {
    let bytes = ciphertext_bytes(&rows[0])?;
    let (capacity, plan) = match execution.backend {
        FoldBackend::GpuResident(plan) => {
            let capacity = engine
                .capacity(&rows[0])
                .expect("GPU execution implies retained arena")?;
            debug_assert_eq!(capacity.ciphertexts_per_chunk, plan.ciphertexts_per_chunk);
            (Some(capacity), Some(plan))
        }
        FoldBackend::CpuNoArena | FoldBackend::CpuUnsupportedShape => (None, None),
    };
    let phase = CollectiveFoldPhase {
        input_ciphertexts: rows.len(),
        ciphertext_bytes: bytes,
        capacity,
        plan,
        backend: execution.backend,
        elapsed: paired_elapsed,
    };
    Ok((execution.ciphertext, phase))
}

/// Encrypt trader-side unary order rows under the n-of-n collective public key.
///
/// A zero row is inserted only for an otherwise empty side so both encrypted aggregate curves remain
/// representable without a secret key. The row has `plain_bound = 0`, so it consumes no wrap budget.
pub fn encrypt_collective_order_rows(
    orders: &[Order],
    k: usize,
    params: &BfvParams,
    public_key: &CollectivePublicKey,
) -> CollectiveFoldResult<(Vec<CollectiveOrderRow>, CollectiveIngressTiming)> {
    if k == 0 || k > params.degree() {
        return Err(CollectiveFoldError::InvalidBucketCount {
            k,
            degree: params.degree(),
        });
    }

    let mut timing = CollectiveIngressTiming::default();
    let mut rng = rand_09::rng();
    let mut rows = Vec::with_capacity(orders.len() + 2);
    let mut have_demand = false;
    let mut have_supply = false;

    for order in orders {
        match order.side {
            Side::Bid => have_demand = true,
            Side::Ask => have_supply = true,
        }
        let slots = order_increment(order, k)
            .into_iter()
            .map(u64::from)
            .collect::<Vec<_>>();
        rows.push(encrypt_collective_row(
            order.side,
            &slots,
            u64::from(order.qty),
            params,
            public_key,
            &mut rng,
            &mut timing,
        )?);
    }
    let zero = vec![0u64; k];
    if !have_demand {
        rows.push(encrypt_collective_row(
            Side::Bid,
            &zero,
            0,
            params,
            public_key,
            &mut rng,
            &mut timing,
        )?);
    }
    if !have_supply {
        rows.push(encrypt_collective_row(
            Side::Ask,
            &zero,
            0,
            params,
            public_key,
            &mut rng,
            &mut timing,
        )?);
    }
    timing.rows = rows.len();
    Ok((rows, timing))
}

/// Encrypt one trader-owned order under the collective public key.
///
/// This is the deployment-shaped sibling of [`encrypt_collective_order_rows`]:
/// it can be called inside the trader's process so an order aggregator receives
/// only a [`CollectiveOrderRow`], never the plaintext [`Order`].  The returned
/// timing covers exactly one row.  As with every BFV ingress in this crate, the
/// ciphertext does not itself prove that its hidden slots are the unary encoding
/// of the declared bound; malicious-input validity still requires a range/
/// well-formedness proof or an authenticated honest-client policy.
pub fn encrypt_collective_order(
    order: &Order,
    k: usize,
    params: &BfvParams,
    public_key: &CollectivePublicKey,
) -> CollectiveFoldResult<(CollectiveOrderRow, CollectiveIngressTiming)> {
    if k == 0 || k > params.degree() {
        return Err(CollectiveFoldError::InvalidBucketCount {
            k,
            degree: params.degree(),
        });
    }
    let slots = order_increment(order, k)
        .into_iter()
        .map(u64::from)
        .collect::<Vec<_>>();
    let mut timing = CollectiveIngressTiming::default();
    let mut rng = rand_09::rng();
    let row = encrypt_collective_row(
        order.side,
        &slots,
        u64::from(order.qty),
        params,
        public_key,
        &mut rng,
        &mut timing,
    )?;
    timing.rows = 1;
    Ok((row, timing))
}

/// Deterministic sibling used only by the authenticated-ingress opening
/// verifier.  The seed is an encryption-randomness opening: disclosing it
/// together with a guessed plaintext lets a verifier reproduce the exact BFV
/// ciphertext, so callers must treat it as secret until they intentionally use
/// the operator-visible verification tier.
pub(crate) fn encrypt_collective_order_with_seed(
    order: &Order,
    k: usize,
    params: &BfvParams,
    public_key: &CollectivePublicKey,
    seed: [u8; 32],
) -> CollectiveFoldResult<(CollectiveOrderRow, CollectiveIngressTiming)> {
    if k == 0 || k > params.degree() {
        return Err(CollectiveFoldError::InvalidBucketCount {
            k,
            degree: params.degree(),
        });
    }
    let slots = order_increment(order, k)
        .into_iter()
        .map(u64::from)
        .collect::<Vec<_>>();
    let mut timing = CollectiveIngressTiming::default();
    let mut rng = StdRng09::from_seed(seed);
    let row = encrypt_collective_row(
        order.side,
        &slots,
        u64::from(order.qty),
        params,
        public_key,
        &mut rng,
        &mut timing,
    )?;
    timing.rows = 1;
    Ok((row, timing))
}

fn encrypt_collective_row(
    side: Side,
    live_slots: &[u64],
    plain_bound: u64,
    params: &BfvParams,
    public_key: &CollectivePublicKey,
    rng: &mut impl rand_09::CryptoRng,
    timing: &mut CollectiveIngressTiming,
) -> CollectiveFoldResult<CollectiveOrderRow> {
    let mut slots = vec![0u64; params.degree()];
    slots[..live_slots.len()].copy_from_slice(live_slots);
    let t0 = Instant::now();
    let plaintext = Plaintext::try_encode(&slots, Encoding::simd(), params.arc())
        .map_err(|_| CollectiveFoldError::Crypto("SIMD encode"))?;
    timing.encode += t0.elapsed();

    let t0 = Instant::now();
    let ciphertext: Ciphertext = public_key
        .pk
        .try_encrypt(&plaintext, rng)
        .map_err(|_| CollectiveFoldError::Crypto("encryption"))?;
    timing.encrypt += t0.elapsed();

    // Necessary one-time representation bridge. `fhe.rs::Ciphertext` exposes no public coefficient-row
    // borrow; the strict parser also checks canonical residues, fresh two-poly shape, and degree.
    let t0 = Instant::now();
    let wire = ciphertext.to_bytes();
    let ciphertext =
        LeanCiphertext::from_fhe_bytes(&wire, params.moduli(), params.degree(), plain_bound)?;
    timing.wire_ingress += t0.elapsed();
    CollectiveOrderRow::from_lean(side, ciphertext, live_slots.len())
}

/// Per-phase timing + op counts from one BFV additive fold (the honest envelope,
/// apples-to-apples with `crate::FheTiming` for the TFHE clear).
#[derive(Clone, Debug, Default)]
pub struct BfvFoldTiming {
    pub n: usize,
    pub k: usize,
    /// BFV ring degree n (= number of SIMD slots; must be ≥ K).
    pub degree: usize,
    /// BFV plaintext modulus t (bucket sums must stay < t: no wrap).
    pub plaintext_modulus: u64,
    /// wall time to generate the BFV keypair (one-time network setup).
    pub keygen: Duration,
    /// wall time to encrypt all N packed order increments (N ciphertexts total —
    /// each packs the FULL K-bucket vector, vs TFHE's N·K scalar ciphertexts).
    pub encrypt: Duration,
    /// wall time for the additive fold itself (the carry-free part under test).
    pub fold: Duration,
    /// number of homomorphic ciphertext ADDs in the fold. Each add folds ALL K
    /// buckets at once (SIMD), so this is ~N, NOT N·K.
    pub add_ops: usize,
    /// wall time to decrypt the two aggregate curve ciphertexts.
    pub decrypt: Duration,
    /// clearing price bucket p* recovered from the decrypted curves (clear-domain
    /// crossing — NOT part of the additive cost; the real crossing stays TFHE).
    pub p_star: usize,
    pub v_star: u32,
}

/// Pick a real 128-bit BFV parameter set: degree ≥ K slots, plaintext modulus t
/// with headroom over the largest bucket sum (no wrap), ample noise budget for an
/// N-deep additive fold (BFV additions grow noise ~linearly; no multiplications,
/// so no relin/bootstrap is needed). `fhe.rs`'s `default_parameters_128` yields
/// 128-bit sets at degrees 1024,2048,4096,8192,16384; we take the degree-4096
/// set (nth 2): 4096 slots (≥ any tested K), a ~109-bit ciphertext modulus q
/// (noise budget for millions of adds), plaintext modulus ≈ 2^plaintext_nbits.
pub fn pick_params(plaintext_nbits: usize) -> Arc<BfvParameters> {
    BfvParameters::default_parameters_128(plaintext_nbits)
        .expect("128-bit BFV params")
        .nth(2)
        .expect("degree-4096 parameter set")
}

/// Legacy single-key folded book with its curves still encrypted. `bfv_fold`
/// decrypts this to check against the plaintext reference, and the legacy
/// `crate::boundary::masked_decrypt_to_shares` benchmark can mask it first.
/// Production callers use [`CollectiveFoldedBook`], which carries no secret key
/// and feeds the party-owned `crate::boundary::MaskedDecryptSession` path.
pub struct BfvFoldedBook {
    /// Encrypted aggregate demand curve (K slots live, rest zero).
    pub d_ct: Ciphertext,
    /// Encrypted aggregate supply curve.
    pub s_ct: Ciphertext,
    /// The keypair. PoC-only convenience: in production the secret key is the
    /// network/threshold key and never exists in one place.
    pub sk: SecretKey,
    pub pk: PublicKey,
    /// keygen/encrypt/fold/add_ops filled; decrypt & p*/V* belong to the caller.
    pub timing: BfvFoldTiming,
}

/// The encrypted-output core of the BFV additive fold: keygen → encrypt each
/// order's packed K-bucket increment as ONE SIMD ciphertext → carry-free fold
/// into the demand/supply curve ciphertexts. Identical phases (and identical
/// fixed rng seed, hence identical bytes) to [`bfv_fold`], which is now a thin
/// decrypt-and-check wrapper around this.
pub fn bfv_fold_encrypted(
    orders: &[Order],
    k: usize,
    params: &Arc<BfvParameters>,
) -> BfvFoldedBook {
    let mut t = BfvFoldTiming {
        n: orders.len(),
        k,
        degree: params.degree(),
        plaintext_modulus: params.plaintext(),
        ..Default::default()
    };
    assert!(
        k <= params.degree(),
        "K={k} exceeds SIMD slot count {}",
        params.degree()
    );

    // Deterministic rng for the BFV randomness (keygen + encryption). The measured
    // fold cost is independent of the seed; a fixed seed keeps the run reproducible.
    let mut rng = StdRng09::seed_from_u64(0xB_F_74_C0DE);

    let t0 = Instant::now();
    let sk = SecretKey::random(params, &mut rng);
    let pk = PublicKey::new(&sk, &mut rng);
    t.keygen = t0.elapsed();

    // (0) Encrypt each order's packed K-bucket increment as ONE SIMD ciphertext.
    let t0 = Instant::now();
    let mut bid_cts: Vec<Ciphertext> = Vec::new();
    let mut ask_cts: Vec<Ciphertext> = Vec::new();
    for o in orders {
        let inc: Vec<u64> = order_increment(o, k)
            .into_iter()
            .map(|q| q as u64)
            .collect();
        let pt = Plaintext::try_encode(&inc, Encoding::simd(), params).expect("simd encode");
        let ct: Ciphertext = pk.try_encrypt(&pt, &mut rng).expect("encrypt");
        match o.side {
            Side::Bid => bid_cts.push(ct),
            Side::Ask => ask_cts.push(ct),
        }
    }
    t.encrypt = t0.elapsed();

    // (a) THE ADDITIVE FOLD — the carry-free part under test. D = Σ_bids, S =
    //     Σ_asks, each a running sum of packed ciphertexts. Every `+=` folds all K
    //     buckets at once via native modular poly-add: no carry, no PBS. This is
    //     N ciphertext adds total from zero accumulators, vs TFHE's 2·K
    //     deferred-carry bucket-sums over N/2 carry-propagating elements each.
    let t0 = Instant::now();
    let mut d_ct = Ciphertext::zero(params);
    for ct in &bid_cts {
        d_ct += ct;
    }
    let mut s_ct = Ciphertext::zero(params);
    for ct in &ask_cts {
        s_ct += ct;
    }
    t.fold = t0.elapsed();
    t.add_ops = bid_cts.len() + ask_cts.len();

    BfvFoldedBook {
        d_ct,
        s_ct,
        sk,
        pk,
        timing: t,
    }
}

/// The BFV additive fold. Each order is expanded (locally, trader-side) into its
/// K-bucket unary increment vector, packed into ONE SIMD ciphertext, and summed
/// homomorphically into the running demand/supply curve ciphertexts. Returns the
/// decrypted `(demand, supply)` curves (length K) and the timing. The keypair is
/// generated fresh here; in production it is the network/threshold key.
pub fn bfv_fold(
    orders: &[Order],
    k: usize,
    params: &Arc<BfvParameters>,
) -> (Vec<u64>, Vec<u64>, BfvFoldTiming) {
    let folded = bfv_fold_encrypted(orders, k, params);
    let BfvFoldedBook {
        d_ct,
        s_ct,
        sk,
        pk: _,
        timing: mut t,
    } = folded;

    // (b) Decrypt the two aggregate curve ciphertexts (K slots each). In the
    //     no-viewer deployment the curves are NEVER opened — the crossing runs
    //     homomorphically on TFHE and only p*/V* are threshold-decrypted. Here we
    //     decrypt them ONLY to check the fold against the plaintext reference.
    let t0 = Instant::now();
    let d_pt = sk.try_decrypt(&d_ct).expect("decrypt D");
    let s_pt = sk.try_decrypt(&s_ct).expect("decrypt S");
    let d_full = Vec::<u64>::try_decode(&d_pt, Encoding::simd()).expect("decode D");
    let s_full = Vec::<u64>::try_decode(&s_pt, Encoding::simd()).expect("decode S");
    let demand: Vec<u64> = d_full[..k].to_vec();
    let supply: Vec<u64> = s_full[..k].to_vec();
    t.decrypt = t0.elapsed();

    // (c) CLEAR-DOMAIN crossing (NOT additive, NOT part of the measured cost — the
    //     real crossing stays TFHE, ~10 s O(K)). Recover p*/V* to CHECK the fold,
    //     under the uniform-price rule p* = argmax_p min(D[p],S[p]) (ties to the
    //     lowest p). V*==0 (usize::MAX sentinel) => the book never clears.
    let mut p_star = usize::MAX;
    let mut v_star = 0u32;
    for p in 0..k {
        let v = demand[p].min(supply[p]) as u32;
        if v > v_star {
            v_star = v;
            p_star = p;
        }
    }
    t.p_star = p_star;
    t.v_star = v_star;

    (demand, supply, t)
}

/// The mint-safe quantizer — the deployable floor/ceil rounding proven no-mint in
/// `metatheory/Market/MintSafeQuantization.lean`.
///
/// The additive fold's soundness discipline is NOT the fold's approximation
/// quality (that is COMPLETENESS / parameter sizing) but conservation: the
/// quantized settlement must never MINT the true (rational-valued) totals. The
/// Lean theorem `mint_safe_floor_ceil` (Δ > 0) proves the deployable rule:
///
///   floor the INPUTS  `qin_i  = ⌊vin_i  / Δ⌋`   (under-approximate),
///   ceil  the OUTPUTS  `qout_j = ⌈vout_j / Δ⌉`   (over-approximate),
///
/// then the cheap INTEGER gate `Σ qout ≤ Σ qin` — checked on the exact-integer
/// grid the BFV fold operates over — PROVABLY forbids a mint of the true values:
/// `Σ vout ≤ Σ vin`. The directionality is load-bearing (the Lean file's
/// `wrong_direction_admits_mint` shows flipping it lets a mint pass). The
/// companion `sufficient_surplus_passes_gate` bounds the completeness reserve at
/// `Δ·(n_in + n_out)`: an honest clearing whose true surplus exceeds that is
/// accepted, so Δ is the tunable precision/tolerance knob.
///
/// Values are carried as fixed-point integers (micro-units): `v` denotes `v/DEN`
/// of a unit and Δ is `delta` micro-units, so the ℚ arithmetic of the Lean is
/// reproduced exactly on `i128` with no float. Values are non-negative (market
/// value flows), so floor/ceil are the standard non-negative integer divisions.
pub mod mint_safe {
    /// `⌊v / Δ⌋` for the mint-safe INPUT direction (v ≥ 0, Δ > 0).
    #[inline]
    pub fn floor_div(v: i128, delta: i128) -> i128 {
        assert!(delta > 0 && v >= 0);
        v / delta
    }

    /// `⌈v / Δ⌉` for the mint-safe OUTPUT direction (v ≥ 0, Δ > 0).
    #[inline]
    pub fn ceil_div(v: i128, delta: i128) -> i128 {
        assert!(delta > 0 && v >= 0);
        (v + delta - 1) / delta
    }

    /// The cheap integer gate `Σ ⌈vout/Δ⌉ ≤ Σ ⌊vin/Δ⌋` — floor the inputs, ceil
    /// the outputs, at step Δ. Returns `(gate_passes, sum_qout, sum_qin)`. When it
    /// passes, `mint_safe_floor_ceil` (Lean) certifies `Σ vout ≤ Σ vin` — no mint
    /// of the true rational values within the quantization tolerance.
    pub fn floor_ceil_gate(vin: &[i128], vout: &[i128], delta: i128) -> (bool, i128, i128) {
        let sum_qin: i128 = vin.iter().map(|&v| floor_div(v, delta)).sum();
        let sum_qout: i128 = vout.iter().map(|&v| ceil_div(v, delta)).sum();
        (sum_qout <= sum_qin, sum_qout, sum_qin)
    }

    /// Direct check that the TRUE (rational, i.e. micro-unit) totals do not mint:
    /// `Σ vout ≤ Σ vin`. The gate is a SUFFICIENT cheap witness for this; this is
    /// the ground truth the gate is trusted to imply (via the Lean theorem).
    pub fn true_no_mint(vin: &[i128], vout: &[i128]) -> bool {
        let s_in: i128 = vin.iter().sum();
        let s_out: i128 = vout.iter().sum();
        s_out <= s_in
    }
}
