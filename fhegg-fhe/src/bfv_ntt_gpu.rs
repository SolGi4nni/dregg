//! Portable, bit-exact GPU negacyclic polynomial multiplication for the BFV
//! RNS representation already used by [`crate::bfv_lean`] and the private-book
//! proof.
//!
//! `LeanCiphertext` serialization exposes power-basis residue rows.  This
//! module multiplies two such [`RnsPoly`] values in
//! `Z_q[X]/(X^n + 1)`: twist by a primitive `2n`-th root, cyclic radix-2 NTT,
//! pointwise multiply, inverse NTT, and untwist. The deployed 36--37-bit
//! moduli use an exact three-limb radix-2^16 Montgomery kernel: public tables
//! enter Montgomery form at upload, input conversion is fused into the first
//! GPU pass, every butterfly stays there, and the final boundary returns
//! canonical residues. It requires
//! no CUDA, HIP, native `u64`, or vendor extension.
//!
//! The scope is deliberately below full BFV ciphertext multiplication.  It
//! does not perform BFV's extended-basis scaling, tensor assembly, or
//! relinearization; [`crate::bfv_mul`] remains the semantic ct×ct oracle.  This
//! is the first portable arithmetic organ needed underneath that operation.
//!
//! [`RnsNttEngine`] reports whether the result came from wgpu or an explicit
//! CPU capability fallback.  Invalid shapes, composite/non-NTT moduli,
//! non-canonical residues, and GPU execution failures never fall back and are
//! never relabeled as a successful GPU computation.

use std::fmt;
use std::sync::{mpsc, Arc, Mutex, OnceLock};

use fhe_math::rq::Context;

use crate::bfv_lean::RnsPoly;

const WORKGROUP_SIZE: u32 = 64;
const MAX_DEGREE: usize = 1 << 16;
const MAX_RNS_ROWS: usize = 16;
/// Three radix-2^16 limbs. Larger valid CPU families take a labelled adapter-
/// limits fallback instead of entering an unsupported GPU reduction.
const GPU_MONTGOMERY_RADIX: u64 = 1u64 << 48;

type Result<T> = std::result::Result<T, BfvNttError>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BfvNttError {
    InvalidShape(&'static str),
    InvalidSchedule(String),
    UnsupportedParameters(String),
    NonCanonical {
        operand: &'static str,
        row: usize,
        coefficient: usize,
        value: u64,
        modulus: u64,
    },
    /// A fail-closed caller requested actual portable-wgpu execution, but the
    /// adapter/device or its advertised limits could not run the validated
    /// shape. This is distinct from a shader/queue failure after dispatch.
    WgpuRequired(String),
    GpuExecution(String),
    OutputMismatch {
        row: usize,
        coefficient: usize,
        expected: u64,
        actual: u64,
    },
}

impl fmt::Display for BfvNttError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidShape(what) => write!(f, "invalid RNS polynomial shape: {what}"),
            Self::InvalidSchedule(what) => write!(f, "invalid odd-NTT schedule: {what}"),
            Self::UnsupportedParameters(what) => {
                write!(f, "unsupported RNS NTT parameters: {what}")
            }
            Self::NonCanonical {
                operand,
                row,
                coefficient,
                value,
                modulus,
            } => write!(
                f,
                "non-canonical {operand} residue at row {row}, coefficient {coefficient}: \
                 {value} >= q = {modulus}"
            ),
            Self::WgpuRequired(what) => write!(f, "portable wgpu RNS NTT required: {what}"),
            Self::GpuExecution(what) => write!(f, "wgpu RNS NTT failed: {what}"),
            Self::OutputMismatch {
                row,
                coefficient,
                expected,
                actual,
            } => write!(
                f,
                "odd-NTT output mismatch at row {row}, coefficient {coefficient}: \
                 expected {expected}, got {actual}"
            ),
        }
    }
}

impl std::error::Error for BfvNttError {}

/// The arithmetic backend that actually produced a polynomial product.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RnsNttBackend {
    Wgpu {
        adapter: String,
    },
    /// Deterministic caller policy (from [`RnsNttEngine::cpu_only`]).
    CpuPolicy,
    /// No adapter/device could be acquired. The reason is retained rather
    /// than turning a CPU result into an apparent GPU green.
    CpuUnavailable {
        reason: String,
    },
    /// An adapter exists but its advertised buffer/dispatch limits cannot run
    /// this preflighted shape.
    CpuAdapterLimits {
        reason: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RnsNttExecution {
    pub polynomial: RnsPoly,
    pub backend: RnsNttBackend,
}

/// Auditable execution shape for a same-parameter batch of independent exact
/// negacyclic products.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RnsNttBatchPlan {
    pub input_pairs: usize,
    pub rns_rows_per_polynomial: usize,
    pub total_rns_rows: usize,
    pub degree: usize,
    pub host_plan_cache_hit: bool,
    pub gpu_dispatches: usize,
    pub gpu_coefficient_uploads: usize,
    pub gpu_static_table_uploads: usize,
    pub gpu_queue_submissions: usize,
    pub gpu_readbacks: usize,
}

/// One exact same-parameter multiplication batch. A GPU result represents one
/// submission and one readback across all pairs, not a loop over single-call
/// [`RnsNttExecution`] values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RnsNttBatchExecution {
    pub polynomials: Vec<RnsPoly>,
    pub backend: RnsNttBackend,
    pub plan: RnsNttBatchPlan,
}

/// Direction of the exact odd-domain transform used by the BFV family proof.
///
/// `Forward` evaluates a power-basis polynomial at `psi^(2k+1)`. `Inverse`
/// performs the corresponding interpolation, including both `n^-1` and the
/// inverse negacyclic twist. The names describe semantic transforms, not just
/// the cyclic radix-2 core dispatched by the shader.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OddNttDirection {
    Forward,
    Inverse,
}

/// One radix-2 stage shared by every RNS row in an odd-NTT dispatch.
///
/// This is deliberately explicit proof-witness metadata. `root_table_offset`
/// selects the forward or inverse half of the packed root table; the two flags
/// identify the stage boundaries at which the negacyclic twist and inverse
/// normalization must be constrained by the AIR.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OddNttStage {
    pub direction: OddNttDirection,
    pub stage_index: usize,
    pub len: usize,
    pub half: usize,
    pub root_stride: usize,
    pub root_table_offset: usize,
    pub consumes_twisted_input: bool,
    pub produces_normalized_output: bool,
}

/// Complete deterministic identity of one batched odd-NTT transform.
///
/// The schedule contains no prover-chosen root data. For the deployed
/// degree-4096/q0-q1-q2 family, `psi` is pinned byte-for-byte to the roots in
/// `Market.PrivateBookBfvNttFamily`; [`OddNttSchedule::validate`] rebuilds and
/// checks that identity. This prevents two extensionally equivalent polynomial
/// multipliers with differently ordered spectra from silently producing
/// incompatible proof witnesses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OddNttSchedule {
    pub direction: OddNttDirection,
    pub degree: usize,
    pub moduli: Vec<u64>,
    pub psi: Vec<u64>,
    pub stages: Vec<OddNttStage>,
}

impl OddNttSchedule {
    /// Number of AIR butterfly rows emitted by this batched transform.
    pub fn butterfly_rows(&self) -> usize {
        self.moduli.len() * (self.degree / 2) * self.stages.len()
    }

    /// Fail closed if any root, direction, stage, stride, or boundary flag was
    /// changed after the schedule was produced.
    pub fn validate(&self) -> Result<()> {
        let plan = NttPlan::from_shape(self.degree, &self.moduli)?;
        let expected = Self::from_plan(&plan, self.direction);
        if *self == expected {
            Ok(())
        } else {
            Err(BfvNttError::InvalidSchedule(
                "root or radix-2 stage metadata differs from the canonical plan".to_owned(),
            ))
        }
    }

    fn from_plan(plan: &NttPlan, direction: OddNttDirection) -> Self {
        let mut stages = Vec::with_capacity(plan.log_degree as usize);
        let mut len = 2usize;
        let mut stage_index = 0usize;
        while len <= plan.degree {
            stages.push(OddNttStage {
                direction,
                stage_index,
                len,
                half: len / 2,
                root_stride: plan.degree / len,
                root_table_offset: match direction {
                    OddNttDirection::Forward => 0,
                    OddNttDirection::Inverse => plan.degree,
                },
                consumes_twisted_input: direction == OddNttDirection::Forward && stage_index == 0,
                produces_normalized_output: direction == OddNttDirection::Inverse
                    && stage_index + 1 == plan.log_degree as usize,
            });
            stage_index += 1;
            len *= 2;
        }
        Self {
            direction,
            degree: plan.degree,
            moduli: plan.moduli.clone(),
            psi: plan.rows.iter().map(|row| row.psi).collect(),
            stages,
        }
    }
}

/// Result of one standalone odd forward or inverse transform.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OddNttExecution {
    pub polynomial: RnsPoly,
    pub schedule: OddNttSchedule,
    pub backend: RnsNttBackend,
}

/// Auditable execution shape for one same-parameter batch of independent
/// odd-domain transforms. The GPU counts describe actual queue/buffer traffic;
/// they are zero on a labelled CPU policy/capability path.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OddNttBatchPlan {
    pub input_polynomials: usize,
    pub rns_rows_per_polynomial: usize,
    pub total_rns_rows: usize,
    pub degree: usize,
    /// Whether the validated root/twist host plan was reused rather than
    /// rebuilt for this call. The cache is bounded to the engine's most
    /// recently used parameter family.
    pub host_plan_cache_hit: bool,
    pub gpu_dispatches: usize,
    pub gpu_input_uploads: usize,
    pub gpu_static_table_uploads: usize,
    pub gpu_queue_submissions: usize,
    pub gpu_readbacks: usize,
}

/// One batched transform result. Every polynomial follows the same canonical
/// [`OddNttSchedule`]; the backend and plan make a one-submission batch
/// distinguishable from four sequential calls that happened to return the
/// same residues.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OddNttBatchExecution {
    pub polynomials: Vec<RnsPoly>,
    pub schedule: OddNttSchedule,
    pub backend: RnsNttBackend,
    pub plan: OddNttBatchPlan,
}

/// One exact butterfly row suitable for streaming into the six-residue portion
/// of the planned 48-column AIR. The host does not have to allocate a giant
/// transcript: [`visit_odd_ntt_cpu`] emits rows in canonical
/// `(modulus, stage, butterfly)` order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OddNttButterfly {
    pub direction: OddNttDirection,
    pub modulus_row: usize,
    pub stage_index: usize,
    pub butterfly_index: usize,
    pub left_index: usize,
    pub right_index: usize,
    pub twiddle_index: usize,
    pub modulus: u64,
    pub left_input: u64,
    pub right_input: u64,
    pub twiddle: u64,
    pub twiddled_right: u64,
    pub left_output: u64,
    pub right_output: u64,
}

/// Roots fixed by `Market.PrivateBookBfvNttFamily.lean` for the deployed BFV
/// basis. q2 intentionally differs from the first primitive root found by a
/// generic search; pinning it is required for spectrum/witness identity.
pub const DEPLOYED_ODD_NTT_PSI: [u64; 3] = [5_546_991_020, 41_019_061_109, 93_693_982_103];

pub const PRIVATE_BOOK_ORDER_COUNT: usize = 4;
pub const PRIVATE_BOOK_CIPHER_POLY_COUNT: usize = 2;
pub const PRIVATE_BOOK_RNS_MODULUS_COUNT: usize = 3;
pub const PRIVATE_BOOK_DEGREE: usize = 4096;
pub const PRIVATE_BOOK_LOG_DEGREE: usize = 12;
pub const PRIVATE_BOOK_NTT_TRACE_WIDTH: usize = 48;
pub const PRIVATE_BOOK_LIVE_FAMILY_ROWS: usize = 1_032_192;
pub const PRIVATE_BOOK_PADDED_FAMILY_ROWS: usize = 1 << 20;

/// Address of one row in the production private-book NTT-family matrix.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrivateBookNttFamilyRow {
    ForwardU {
        order: usize,
        modulus: usize,
        stage: usize,
        butterfly: usize,
    },
    Pointwise {
        order: usize,
        ciphertext_poly: usize,
        modulus: usize,
        coefficient: usize,
    },
    InverseProduct {
        order: usize,
        ciphertext_poly: usize,
        modulus: usize,
        stage: usize,
        butterfly: usize,
    },
    Terminal {
        order: usize,
        ciphertext_poly: usize,
        modulus: usize,
        coefficient_pair: usize,
    },
    Padding {
        padding_row: usize,
    },
}

/// Decode a physical row of the exact `2^20 × 48` production family schedule.
/// Every live transform butterfly, spectral product, and terminal coefficient
/// pair occurs exactly once; padding occupies only the final 16,384 rows.
pub fn private_book_ntt_family_row(row: usize) -> Result<PrivateBookNttFamilyRow> {
    if row >= PRIVATE_BOOK_PADDED_FAMILY_ROWS {
        return Err(BfvNttError::InvalidSchedule(format!(
            "family row {row} exceeds the 2^20 matrix"
        )));
    }
    let butterflies_per_stage = PRIVATE_BOOK_DEGREE / 2;
    let butterflies_per_transform = butterflies_per_stage * PRIVATE_BOOK_LOG_DEGREE;
    let forward_rows =
        PRIVATE_BOOK_ORDER_COUNT * PRIVATE_BOOK_RNS_MODULUS_COUNT * butterflies_per_transform;
    let pointwise_rows = PRIVATE_BOOK_ORDER_COUNT
        * PRIVATE_BOOK_CIPHER_POLY_COUNT
        * PRIVATE_BOOK_RNS_MODULUS_COUNT
        * PRIVATE_BOOK_DEGREE;
    let inverse_rows = PRIVATE_BOOK_ORDER_COUNT
        * PRIVATE_BOOK_CIPHER_POLY_COUNT
        * PRIVATE_BOOK_RNS_MODULUS_COUNT
        * butterflies_per_transform;

    if row < forward_rows {
        let transform = row / butterflies_per_transform;
        let within = row % butterflies_per_transform;
        return Ok(PrivateBookNttFamilyRow::ForwardU {
            order: transform / PRIVATE_BOOK_RNS_MODULUS_COUNT,
            modulus: transform % PRIVATE_BOOK_RNS_MODULUS_COUNT,
            stage: within / butterflies_per_stage,
            butterfly: within % butterflies_per_stage,
        });
    }
    let row = row - forward_rows;
    if row < pointwise_rows {
        let equation = row / PRIVATE_BOOK_DEGREE;
        return Ok(PrivateBookNttFamilyRow::Pointwise {
            order: equation / (PRIVATE_BOOK_CIPHER_POLY_COUNT * PRIVATE_BOOK_RNS_MODULUS_COUNT),
            ciphertext_poly: (equation / PRIVATE_BOOK_RNS_MODULUS_COUNT)
                % PRIVATE_BOOK_CIPHER_POLY_COUNT,
            modulus: equation % PRIVATE_BOOK_RNS_MODULUS_COUNT,
            coefficient: row % PRIVATE_BOOK_DEGREE,
        });
    }
    let row = row - pointwise_rows;
    if row < inverse_rows {
        let transform = row / butterflies_per_transform;
        let within = row % butterflies_per_transform;
        return Ok(PrivateBookNttFamilyRow::InverseProduct {
            order: transform / (PRIVATE_BOOK_CIPHER_POLY_COUNT * PRIVATE_BOOK_RNS_MODULUS_COUNT),
            ciphertext_poly: (transform / PRIVATE_BOOK_RNS_MODULUS_COUNT)
                % PRIVATE_BOOK_CIPHER_POLY_COUNT,
            modulus: transform % PRIVATE_BOOK_RNS_MODULUS_COUNT,
            stage: within / butterflies_per_stage,
            butterfly: within % butterflies_per_stage,
        });
    }
    let row = row - inverse_rows;
    let terminal_rows = PRIVATE_BOOK_ORDER_COUNT
        * PRIVATE_BOOK_CIPHER_POLY_COUNT
        * PRIVATE_BOOK_RNS_MODULUS_COUNT
        * (PRIVATE_BOOK_DEGREE / 2);
    if row < terminal_rows {
        let equation_pair = row / (PRIVATE_BOOK_DEGREE / 2);
        return Ok(PrivateBookNttFamilyRow::Terminal {
            order: equation_pair
                / (PRIVATE_BOOK_CIPHER_POLY_COUNT * PRIVATE_BOOK_RNS_MODULUS_COUNT),
            ciphertext_poly: (equation_pair / PRIVATE_BOOK_RNS_MODULUS_COUNT)
                % PRIVATE_BOOK_CIPHER_POLY_COUNT,
            modulus: equation_pair % PRIVATE_BOOK_RNS_MODULUS_COUNT,
            coefficient_pair: row % (PRIVATE_BOOK_DEGREE / 2),
        });
    }
    let live_row = forward_rows + pointwise_rows + inverse_rows + terminal_rows;
    debug_assert_eq!(live_row, PRIVATE_BOOK_LIVE_FAMILY_ROWS);
    Ok(PrivateBookNttFamilyRow::Padding {
        padding_row: row - terminal_rows,
    })
}

/// Backend policy for exact RNS transforms. `RequireWgpu` is the fail-closed
/// qualification/deployment setting: capability absence is an error rather
/// than a CPU result carrying an optimistic GPU label.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum RnsNttPolicy {
    #[default]
    Auto,
    CpuOnly,
    RequireWgpu,
}

/// Reusable dispatch policy. GPU initialization is process-wide and lazy.
pub struct RnsNttEngine {
    policy: RnsNttPolicy,
    /// One bounded prepared parameter family. A map keyed by caller-supplied
    /// parameters would let untrusted shapes grow process memory without
    /// bound; the private-book workload needs one hot family at a time.
    plan_cache: Mutex<Option<Arc<NttPlan>>>,
}

impl RnsNttEngine {
    pub fn new() -> Self {
        Self {
            policy: RnsNttPolicy::Auto,
            plan_cache: Mutex::new(None),
        }
    }

    /// Force the exact CPU reference and label it as policy-selected. This is
    /// useful both for deployments that forbid accelerators and for a
    /// deterministic fallback/parity gate.
    pub fn cpu_only() -> Self {
        Self {
            policy: RnsNttPolicy::CpuOnly,
            plan_cache: Mutex::new(None),
        }
    }

    /// Require one real portable-wgpu execution. This constructor never
    /// permits an unavailable/adapter-limits result to become a CPU green.
    pub fn require_wgpu() -> Self {
        Self {
            policy: RnsNttPolicy::RequireWgpu,
            plan_cache: Mutex::new(None),
        }
    }

    pub const fn policy(&self) -> RnsNttPolicy {
        self.policy
    }

    pub fn has_gpu(&self) -> bool {
        self.policy != RnsNttPolicy::CpuOnly && matches!(gpu_state(), GpuState::Ready(_))
    }

    pub fn multiply(
        &self,
        lhs: &RnsPoly,
        rhs: &RnsPoly,
        moduli: &[u64],
    ) -> Result<RnsNttExecution> {
        let lhs_degree = validate_poly(lhs, moduli, "lhs")?;
        let rhs_degree = validate_poly(rhs, moduli, "rhs")?;
        if lhs_degree != rhs_degree {
            return Err(BfvNttError::InvalidShape(
                "operand polynomial degrees differ",
            ));
        }
        let (plan, _) = self.cached_plan(lhs_degree, moduli)?;
        if self.policy == RnsNttPolicy::CpuOnly {
            return Ok(RnsNttExecution {
                polynomial: multiply_cpu_with_plan(lhs, rhs, plan.as_ref()),
                backend: RnsNttBackend::CpuPolicy,
            });
        }
        match gpu_state() {
            GpuState::Unavailable(reason) if self.policy == RnsNttPolicy::RequireWgpu => {
                Err(BfvNttError::WgpuRequired(reason.clone()))
            }
            GpuState::Unavailable(reason) => Ok(RnsNttExecution {
                polynomial: multiply_cpu_with_plan(lhs, rhs, plan.as_ref()),
                backend: RnsNttBackend::CpuUnavailable {
                    reason: reason.clone(),
                },
            }),
            GpuState::Broken(reason) => Err(BfvNttError::GpuExecution(reason.clone())),
            GpuState::Ready(gpu) => {
                if let Err(reason) = gpu.supports(plan.as_ref(), 1) {
                    if self.policy == RnsNttPolicy::RequireWgpu {
                        return Err(BfvNttError::WgpuRequired(reason));
                    }
                    return Ok(RnsNttExecution {
                        polynomial: multiply_cpu_with_plan(lhs, rhs, plan.as_ref()),
                        backend: RnsNttBackend::CpuAdapterLimits { reason },
                    });
                }
                Ok(RnsNttExecution {
                    polynomial: gpu.multiply(lhs, rhs, plan.as_ref())?,
                    backend: RnsNttBackend::Wgpu {
                        adapter: gpu.adapter.clone(),
                    },
                })
            }
        }
    }

    /// Multiply a nonempty same-parameter family in one GPU submission. This
    /// is the production private-book shape: four `u` polynomials paired with
    /// both collective-public-key rows (eight independent products).
    pub fn multiply_batch(
        &self,
        lhs: &[RnsPoly],
        rhs: &[RnsPoly],
        moduli: &[u64],
    ) -> Result<RnsNttBatchExecution> {
        if lhs.is_empty() || lhs.len() != rhs.len() {
            return Err(BfvNttError::InvalidShape(
                "multiplication batch is empty or operand batch lengths differ",
            ));
        }
        let degree = validate_poly(&lhs[0], moduli, "lhs")?;
        let rhs_degree = validate_poly(&rhs[0], moduli, "rhs")?;
        if rhs_degree != degree {
            return Err(BfvNttError::InvalidShape(
                "operand polynomial degrees differ",
            ));
        }
        for (left, right) in lhs[1..].iter().zip(&rhs[1..]) {
            if validate_poly(left, moduli, "lhs")? != degree
                || validate_poly(right, moduli, "rhs")? != degree
            {
                return Err(BfvNttError::InvalidShape(
                    "multiplication batch polynomials have different degrees",
                ));
            }
        }
        let (plan, host_plan_cache_hit) = self.cached_plan(degree, moduli)?;
        let total_rns_rows =
            lhs.len()
                .checked_mul(plan.moduli.len())
                .ok_or(BfvNttError::InvalidShape(
                    "multiplication batch row count overflows usize",
                ))?;
        let report = |gpu: bool, gpu_static_table_uploads: usize| RnsNttBatchPlan {
            input_pairs: lhs.len(),
            rns_rows_per_polynomial: plan.moduli.len(),
            total_rns_rows,
            degree: plan.degree,
            host_plan_cache_hit,
            gpu_dispatches: if gpu {
                plan.log_degree as usize * 2 + 5
            } else {
                0
            },
            gpu_coefficient_uploads: if gpu { 2 } else { 0 },
            gpu_static_table_uploads,
            gpu_queue_submissions: usize::from(gpu),
            gpu_readbacks: usize::from(gpu),
        };
        let cpu = |backend| RnsNttBatchExecution {
            polynomials: lhs
                .iter()
                .zip(rhs)
                .map(|(left, right)| multiply_cpu_with_plan(left, right, plan.as_ref()))
                .collect(),
            backend,
            plan: report(false, 0),
        };
        if self.policy == RnsNttPolicy::CpuOnly {
            return Ok(cpu(RnsNttBackend::CpuPolicy));
        }
        match gpu_state() {
            GpuState::Unavailable(reason) if self.policy == RnsNttPolicy::RequireWgpu => {
                Err(BfvNttError::WgpuRequired(reason.clone()))
            }
            GpuState::Unavailable(reason) => Ok(cpu(RnsNttBackend::CpuUnavailable {
                reason: reason.clone(),
            })),
            GpuState::Broken(reason) => Err(BfvNttError::GpuExecution(reason.clone())),
            GpuState::Ready(gpu) => {
                if let Err(reason) = gpu.supports(plan.as_ref(), lhs.len()) {
                    if self.policy == RnsNttPolicy::RequireWgpu {
                        return Err(BfvNttError::WgpuRequired(reason));
                    }
                    return Ok(cpu(RnsNttBackend::CpuAdapterLimits { reason }));
                }
                let (polynomials, gpu_static_table_uploads) =
                    gpu.multiply_batch(lhs, rhs, plan.as_ref())?;
                Ok(RnsNttBatchExecution {
                    polynomials,
                    backend: RnsNttBackend::Wgpu {
                        adapter: gpu.adapter.clone(),
                    },
                    plan: report(true, gpu_static_table_uploads),
                })
            }
        }
    }

    /// Execute the exact standalone odd-domain forward transform. This is the
    /// transform used for the twelve shared-u and six reusable public-key
    /// spectra in the private-book family, rather than a multiplication-only
    /// API that hides the spectral boundary.
    pub fn forward_odd(&self, input: &RnsPoly, moduli: &[u64]) -> Result<OddNttExecution> {
        self.transform_odd(input, moduli, OddNttDirection::Forward)
    }

    /// Execute the exact standalone odd-domain inverse transform, including
    /// inverse twist and `n^-1` normalization.
    pub fn inverse_odd(&self, input: &RnsPoly, moduli: &[u64]) -> Result<OddNttExecution> {
        self.transform_odd(input, moduli, OddNttDirection::Inverse)
    }

    /// Batch the four owner-local `u` spectra of the N4K4 private book (or any
    /// nonempty same-parameter family) into one coefficient upload, one queue
    /// submission, and one readback. RNS rows are flattened as
    /// `[polynomial][modulus][coefficient]`; the shader reuses the exact same
    /// pinned modulus/root/twist tables for every polynomial.
    pub fn forward_odd_batch(
        &self,
        inputs: &[RnsPoly],
        moduli: &[u64],
    ) -> Result<OddNttBatchExecution> {
        self.transform_odd_batch(inputs, moduli, OddNttDirection::Forward)
    }

    /// Batched exact inverse transform, including inverse twist and `n^-1`
    /// normalization independently for every polynomial.
    pub fn inverse_odd_batch(
        &self,
        inputs: &[RnsPoly],
        moduli: &[u64],
    ) -> Result<OddNttBatchExecution> {
        self.transform_odd_batch(inputs, moduli, OddNttDirection::Inverse)
    }

    fn transform_odd(
        &self,
        input: &RnsPoly,
        moduli: &[u64],
        direction: OddNttDirection,
    ) -> Result<OddNttExecution> {
        let mut batch = self.transform_odd_batch(std::slice::from_ref(input), moduli, direction)?;
        Ok(OddNttExecution {
            polynomial: batch
                .polynomials
                .pop()
                .expect("one-input transform batch returns one polynomial"),
            schedule: batch.schedule,
            backend: batch.backend,
        })
    }

    fn transform_odd_batch(
        &self,
        inputs: &[RnsPoly],
        moduli: &[u64],
        direction: OddNttDirection,
    ) -> Result<OddNttBatchExecution> {
        let first = inputs
            .first()
            .ok_or(BfvNttError::InvalidShape("odd-NTT batch is empty"))?;
        let degree = validate_poly(first, moduli, "input")?;
        for input in &inputs[1..] {
            let input_degree = validate_poly(input, moduli, "input")?;
            if input_degree != degree {
                return Err(BfvNttError::InvalidShape(
                    "odd-NTT batch polynomials have different degrees",
                ));
            }
        }
        let (plan, host_plan_cache_hit) = self.cached_plan(degree, moduli)?;
        let total_rns_rows =
            inputs
                .len()
                .checked_mul(plan.moduli.len())
                .ok_or(BfvNttError::InvalidShape(
                    "odd-NTT batch row count overflows usize",
                ))?;
        let schedule = OddNttSchedule::from_plan(plan.as_ref(), direction);
        let report = |gpu: bool, gpu_static_table_uploads: usize| OddNttBatchPlan {
            input_polynomials: inputs.len(),
            rns_rows_per_polynomial: plan.moduli.len(),
            total_rns_rows,
            degree: plan.degree,
            host_plan_cache_hit,
            gpu_dispatches: if gpu { plan.log_degree as usize + 2 } else { 0 },
            gpu_input_uploads: usize::from(gpu),
            gpu_static_table_uploads,
            gpu_queue_submissions: usize::from(gpu),
            gpu_readbacks: usize::from(gpu),
        };
        let cpu = |backend| OddNttBatchExecution {
            polynomials: inputs
                .iter()
                .map(|input| transform_cpu_with_plan(input, plan.as_ref(), direction))
                .collect(),
            schedule: schedule.clone(),
            backend,
            plan: report(false, 0),
        };
        if self.policy == RnsNttPolicy::CpuOnly {
            return Ok(cpu(RnsNttBackend::CpuPolicy));
        }
        match gpu_state() {
            GpuState::Unavailable(reason) if self.policy == RnsNttPolicy::RequireWgpu => {
                Err(BfvNttError::WgpuRequired(reason.clone()))
            }
            GpuState::Unavailable(reason) => Ok(cpu(RnsNttBackend::CpuUnavailable {
                reason: reason.clone(),
            })),
            GpuState::Broken(reason) => Err(BfvNttError::GpuExecution(reason.clone())),
            GpuState::Ready(gpu) => {
                if let Err(reason) = gpu.supports(plan.as_ref(), inputs.len()) {
                    if self.policy == RnsNttPolicy::RequireWgpu {
                        return Err(BfvNttError::WgpuRequired(reason));
                    }
                    return Ok(cpu(RnsNttBackend::CpuAdapterLimits { reason }));
                }
                let (polynomials, gpu_static_table_uploads) =
                    gpu.transform_odd_batch(inputs, plan.as_ref(), direction)?;
                Ok(OddNttBatchExecution {
                    polynomials,
                    schedule,
                    backend: RnsNttBackend::Wgpu {
                        adapter: gpu.adapter.clone(),
                    },
                    plan: report(true, gpu_static_table_uploads),
                })
            }
        }
    }

    fn cached_plan(&self, degree: usize, moduli: &[u64]) -> Result<(Arc<NttPlan>, bool)> {
        let mut cache = self
            .plan_cache
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if let Some(plan) = cache.as_ref().filter(|plan| plan.matches(degree, moduli)) {
            return Ok((Arc::clone(plan), true));
        }
        // Serialize the rare miss so two concurrent callers cannot both build
        // a plan while one is inaccurately reported as a cache hit.
        let prepared = Arc::new(NttPlan::from_shape(degree, moduli)?);
        *cache = Some(Arc::clone(&prepared));
        Ok((prepared, false))
    }
}

impl Default for RnsNttEngine {
    fn default() -> Self {
        Self::new()
    }
}

/// One-call convenience. Retain an [`RnsNttEngine`] when backend observation
/// or repeated calls matter.
pub fn multiply_rns_gpu_or_cpu(
    lhs: &RnsPoly,
    rhs: &RnsPoly,
    moduli: &[u64],
) -> Result<RnsNttExecution> {
    RnsNttEngine::new().multiply(lhs, rhs, moduli)
}

/// Exact CPU reference/fallback for negacyclic RNS multiplication.
pub fn multiply_rns_cpu(lhs: &RnsPoly, rhs: &RnsPoly, moduli: &[u64]) -> Result<RnsPoly> {
    let plan = NttPlan::new(lhs, rhs, moduli)?;
    Ok(multiply_cpu_with_plan(lhs, rhs, &plan))
}

/// Exact CPU reference for one standalone odd-domain transform.
pub fn transform_odd_rns_cpu(
    input: &RnsPoly,
    moduli: &[u64],
    direction: OddNttDirection,
) -> Result<RnsPoly> {
    let plan = NttPlan::for_poly(input, moduli, "input")?;
    Ok(transform_cpu_with_plan(input, &plan, direction))
}

/// Stream the exact CPU butterfly witness in canonical schedule order while
/// returning the transformed polynomial. This is the bounded-memory bridge for
/// filling family AIR rows; callers may encode each callback immediately.
pub fn visit_odd_ntt_cpu<F>(
    input: &RnsPoly,
    moduli: &[u64],
    direction: OddNttDirection,
    mut visitor: F,
) -> Result<RnsPoly>
where
    F: FnMut(OddNttButterfly),
{
    let plan = NttPlan::for_poly(input, moduli, "input")?;
    Ok(transform_cpu_with_plan_and_visitor(
        input,
        &plan,
        direction,
        &mut visitor,
    ))
}

/// Recompute and compare every residue against the canonical CPU transform.
/// Schedule identity is checked first, so root/stage mutations are distinct
/// from output mutations and never accepted as a different valid transform.
pub fn verify_odd_ntt_execution(
    input: &RnsPoly,
    moduli: &[u64],
    execution: &OddNttExecution,
) -> Result<()> {
    execution.schedule.validate()?;
    let plan = NttPlan::for_poly(input, moduli, "input")?;
    let expected_schedule = OddNttSchedule::from_plan(&plan, execution.schedule.direction);
    if execution.schedule != expected_schedule {
        return Err(BfvNttError::InvalidSchedule(
            "execution schedule does not match the input modulus family".to_owned(),
        ));
    }
    let expected = transform_cpu_with_plan(input, &plan, execution.schedule.direction);
    if execution.polynomial.rows.len() != expected.rows.len()
        || execution
            .polynomial
            .rows
            .iter()
            .zip(&expected.rows)
            .any(|(actual, expected)| actual.len() != expected.len())
    {
        return Err(BfvNttError::InvalidShape(
            "claimed odd-NTT output shape differs from the canonical transform",
        ));
    }
    for (row, (actual, expected)) in execution
        .polynomial
        .rows
        .iter()
        .zip(&expected.rows)
        .enumerate()
    {
        for (coefficient, (&actual, &expected)) in actual.iter().zip(expected).enumerate() {
            if actual != expected {
                return Err(BfvNttError::OutputMismatch {
                    row,
                    coefficient,
                    expected,
                    actual,
                });
            }
        }
    }
    Ok(())
}

#[derive(Clone)]
struct RowPlan {
    psi: u64,
    montgomery_r: u64,
    roots: Vec<u64>,
    inverse_roots: Vec<u64>,
    twists: Vec<u64>,
    inverse_twists_times_n_inv: Vec<u64>,
}

struct NttPlan {
    degree: usize,
    log_degree: u32,
    moduli: Vec<u64>,
    rows: Vec<RowPlan>,
}

impl NttPlan {
    fn matches(&self, degree: usize, moduli: &[u64]) -> bool {
        self.degree == degree && self.moduli == moduli
    }

    fn new(lhs: &RnsPoly, rhs: &RnsPoly, moduli: &[u64]) -> Result<Self> {
        let degree = validate_poly(lhs, moduli, "lhs")?;
        let rhs_degree = validate_poly(rhs, moduli, "rhs")?;
        if degree != rhs_degree {
            return Err(BfvNttError::InvalidShape(
                "operand polynomial degrees differ",
            ));
        }
        Self::from_shape(degree, moduli)
    }

    fn for_poly(poly: &RnsPoly, moduli: &[u64], operand: &'static str) -> Result<Self> {
        let degree = validate_poly(poly, moduli, operand)?;
        Self::from_shape(degree, moduli)
    }

    fn from_shape(degree: usize, moduli: &[u64]) -> Result<Self> {
        if moduli.is_empty() {
            return Err(BfvNttError::InvalidShape("modulus set is empty"));
        }
        if moduli.len() > MAX_RNS_ROWS {
            return Err(BfvNttError::InvalidShape(
                "RNS row count exceeds the bounded GPU/CPU plan",
            ));
        }
        if degree < 8 || !degree.is_power_of_two() {
            return Err(BfvNttError::InvalidShape(
                "degree must be a power of two at least 8",
            ));
        }
        if degree > MAX_DEGREE {
            return Err(BfvNttError::InvalidShape(
                "degree exceeds the bounded NTT implementation",
            ));
        }
        if moduli.iter().any(|&q| q >= (1u64 << 62)) {
            return Err(BfvNttError::UnsupportedParameters(
                "moduli must be below 2^62 so every split-u32 add stays below 2^63".to_owned(),
            ));
        }
        // This is the same prime/2n-root/coprimality constructor fhe.rs uses.
        // It is a fail-closed parameter guard, not merely a root-search guess.
        Context::new(moduli, degree).map_err(|error| {
            BfvNttError::UnsupportedParameters(format!(
                "fhe-math rejected the modulus set/degree: {error}"
            ))
        })?;

        let mut rows = Vec::with_capacity(moduli.len());
        for &q in moduli {
            rows.push(build_row_plan(q, degree)?);
        }
        Ok(Self {
            degree,
            log_degree: degree.trailing_zeros(),
            moduli: moduli.to_vec(),
            rows,
        })
    }
}

fn validate_poly(poly: &RnsPoly, moduli: &[u64], operand: &'static str) -> Result<usize> {
    if moduli.is_empty() {
        return Err(BfvNttError::InvalidShape("modulus set is empty"));
    }
    if poly.rows.len() != moduli.len() {
        return Err(BfvNttError::InvalidShape(
            "operand row count differs from modulus count",
        ));
    }
    let degree = poly.rows[0].len();
    if poly.rows.iter().any(|row| row.len() != degree) {
        return Err(BfvNttError::InvalidShape(
            "all operand rows must have the same degree",
        ));
    }
    for (row, (&q, coefficients)) in moduli.iter().zip(&poly.rows).enumerate() {
        for (coefficient, &value) in coefficients.iter().enumerate() {
            if value >= q {
                return Err(BfvNttError::NonCanonical {
                    operand,
                    row,
                    coefficient,
                    value,
                    modulus: q,
                });
            }
        }
    }
    Ok(degree)
}

fn build_row_plan(q: u64, degree: usize) -> Result<RowPlan> {
    let order = (degree as u64)
        .checked_mul(2)
        .ok_or(BfvNttError::InvalidShape("2*degree overflows u64"))?;
    let exponent = (q - 1) / order;
    let deployed_moduli = crate::bfv_lean::FOLD_MODULI;
    let prescribed = if degree == PRIVATE_BOOK_DEGREE {
        deployed_moduli
            .iter()
            .position(|candidate| *candidate == q)
            .map(|row| DEPLOYED_ODD_NTT_PSI[row])
    } else {
        None
    };
    let psi = match prescribed {
        Some(root) => Some(root),
        None => {
            let mut found = None;
            for candidate in 2u64..=1_000_000 {
                let root = mod_pow(candidate, exponent, q);
                if mod_pow(root, degree as u64, q) == q - 1 {
                    found = Some(root);
                    break;
                }
            }
            found
        }
    };
    let psi = psi.ok_or_else(|| {
        BfvNttError::UnsupportedParameters(format!("no primitive {order}-th root found modulo {q}"))
    })?;
    if mod_pow(psi, degree as u64, q) != q - 1 {
        return Err(BfvNttError::UnsupportedParameters(format!(
            "prescribed psi={psi} is not a primitive {order}-th negacyclic root modulo {q}"
        )));
    }
    let psi_inv = mod_pow(psi, q - 2, q);
    let omega = mod_mul(psi, psi, q);
    let omega_inv = mod_pow(omega, q - 2, q);
    let n_inv = mod_pow((degree as u64) % q, q - 2, q);
    let montgomery_r = (u128::from(GPU_MONTGOMERY_RADIX) % u128::from(q)) as u64;

    let roots = powers(omega, degree, q);
    let inverse_roots = powers(omega_inv, degree, q);
    let twists = powers(psi, degree, q);
    let inverse_twists_times_n_inv = powers(psi_inv, degree, q)
        .into_iter()
        .map(|value| mod_mul(value, n_inv, q))
        .collect();
    Ok(RowPlan {
        psi,
        montgomery_r,
        roots,
        inverse_roots,
        twists,
        inverse_twists_times_n_inv,
    })
}

fn powers(base: u64, count: usize, modulus: u64) -> Vec<u64> {
    let mut out = Vec::with_capacity(count);
    let mut value = 1u64;
    for _ in 0..count {
        out.push(value);
        value = mod_mul(value, base, modulus);
    }
    out
}

fn inverse_mod_2_16(odd: u16) -> u16 {
    // Newton iteration doubles the number of correct low bits each round.
    let mut inverse = odd;
    for _ in 0..4 {
        inverse = inverse.wrapping_mul(2u16.wrapping_sub(odd.wrapping_mul(inverse)));
    }
    inverse
}

fn validate_gpu_montgomery_moduli(moduli: &[u64]) -> std::result::Result<(), String> {
    if let Some(&modulus) = moduli
        .iter()
        .find(|&&modulus| modulus >= GPU_MONTGOMERY_RADIX)
    {
        return Err(format!(
            "modulus {modulus} exceeds the exact three-limb radix-2^16 GPU carrier"
        ));
    }
    Ok(())
}

fn mod_mul(a: u64, b: u64, modulus: u64) -> u64 {
    ((u128::from(a) * u128::from(b)) % u128::from(modulus)) as u64
}

fn mod_pow(mut base: u64, mut exponent: u64, modulus: u64) -> u64 {
    let mut out = 1u64;
    while exponent != 0 {
        if exponent & 1 != 0 {
            out = mod_mul(out, base, modulus);
        }
        exponent >>= 1;
        if exponent != 0 {
            base = mod_mul(base, base, modulus);
        }
    }
    out
}

fn add_mod(a: u64, b: u64, modulus: u64) -> u64 {
    let sum = a + b;
    if sum >= modulus {
        sum - modulus
    } else {
        sum
    }
}

fn sub_mod(a: u64, b: u64, modulus: u64) -> u64 {
    if a >= b {
        a - b
    } else {
        modulus - (b - a)
    }
}

fn bit_reverse_permute(values: &mut [u64]) {
    let bits = values.len().trailing_zeros();
    for i in 0..values.len() {
        let j = i.reverse_bits() >> (usize::BITS - bits);
        if i < j {
            values.swap(i, j);
        }
    }
}

fn cyclic_ntt(values: &mut [u64], roots: &[u64], modulus: u64) {
    bit_reverse_permute(values);
    let degree = values.len();
    let mut len = 2usize;
    while len <= degree {
        let half = len / 2;
        let step = degree / len;
        for block in (0..degree).step_by(len) {
            for j in 0..half {
                let u = values[block + j];
                let v = mod_mul(values[block + j + half], roots[j * step], modulus);
                values[block + j] = add_mod(u, v, modulus);
                values[block + j + half] = sub_mod(u, v, modulus);
            }
        }
        len *= 2;
    }
}

fn cyclic_ntt_with_visitor<F>(
    values: &mut [u64],
    roots: &[u64],
    modulus: u64,
    modulus_row: usize,
    direction: OddNttDirection,
    visitor: &mut F,
) where
    F: FnMut(OddNttButterfly),
{
    bit_reverse_permute(values);
    let degree = values.len();
    let mut len = 2usize;
    let mut stage_index = 0usize;
    while len <= degree {
        let half = len / 2;
        let step = degree / len;
        let mut butterfly_index = 0usize;
        for block in (0..degree).step_by(len) {
            for j in 0..half {
                let left_index = block + j;
                let right_index = left_index + half;
                let twiddle_index = j * step;
                let left_input = values[left_index];
                let right_input = values[right_index];
                let twiddle = roots[twiddle_index];
                let twiddled_right = mod_mul(right_input, twiddle, modulus);
                let left_output = add_mod(left_input, twiddled_right, modulus);
                let right_output = sub_mod(left_input, twiddled_right, modulus);
                values[left_index] = left_output;
                values[right_index] = right_output;
                visitor(OddNttButterfly {
                    direction,
                    modulus_row,
                    stage_index,
                    butterfly_index,
                    left_index,
                    right_index,
                    twiddle_index,
                    modulus,
                    left_input,
                    right_input,
                    twiddle,
                    twiddled_right,
                    left_output,
                    right_output,
                });
                butterfly_index += 1;
            }
        }
        debug_assert_eq!(butterfly_index, degree / 2);
        stage_index += 1;
        len *= 2;
    }
}

fn transform_cpu_with_plan(input: &RnsPoly, plan: &NttPlan, direction: OddNttDirection) -> RnsPoly {
    transform_cpu_with_plan_and_visitor(input, plan, direction, &mut |_| {})
}

fn transform_cpu_with_plan_and_visitor<F>(
    input: &RnsPoly,
    plan: &NttPlan,
    direction: OddNttDirection,
    visitor: &mut F,
) -> RnsPoly
where
    F: FnMut(OddNttButterfly),
{
    let mut rows = Vec::with_capacity(plan.moduli.len());
    for (modulus_row, ((input_row, &q), row_plan)) in input
        .rows
        .iter()
        .zip(&plan.moduli)
        .zip(&plan.rows)
        .enumerate()
    {
        let mut values = match direction {
            OddNttDirection::Forward => input_row
                .iter()
                .zip(&row_plan.twists)
                .map(|(&value, &twist)| mod_mul(value, twist, q))
                .collect(),
            OddNttDirection::Inverse => input_row.clone(),
        };
        let roots = match direction {
            OddNttDirection::Forward => &row_plan.roots,
            OddNttDirection::Inverse => &row_plan.inverse_roots,
        };
        cyclic_ntt_with_visitor(&mut values, roots, q, modulus_row, direction, visitor);
        if direction == OddNttDirection::Inverse {
            for (value, &scale) in values.iter_mut().zip(&row_plan.inverse_twists_times_n_inv) {
                *value = mod_mul(*value, scale, q);
            }
        }
        rows.push(values);
    }
    RnsPoly { rows }
}

fn multiply_cpu_with_plan(lhs: &RnsPoly, rhs: &RnsPoly, plan: &NttPlan) -> RnsPoly {
    let mut rows = Vec::with_capacity(plan.moduli.len());
    for (row, ((left, right), &q)) in lhs.rows.iter().zip(&rhs.rows).zip(&plan.moduli).enumerate() {
        let row_plan = &plan.rows[row];
        let mut a: Vec<u64> = left
            .iter()
            .zip(&row_plan.twists)
            .map(|(&value, &twist)| mod_mul(value, twist, q))
            .collect();
        let mut b: Vec<u64> = right
            .iter()
            .zip(&row_plan.twists)
            .map(|(&value, &twist)| mod_mul(value, twist, q))
            .collect();
        cyclic_ntt(&mut a, &row_plan.roots, q);
        cyclic_ntt(&mut b, &row_plan.roots, q);
        for (value, &other) in a.iter_mut().zip(&b) {
            *value = mod_mul(*value, other, q);
        }
        cyclic_ntt(&mut a, &row_plan.inverse_roots, q);
        for (value, &scale) in a.iter_mut().zip(&row_plan.inverse_twists_times_n_inv) {
            *value = mod_mul(*value, scale, q);
        }
        rows.push(a);
    }
    RnsPoly { rows }
}

enum GpuState {
    Ready(GpuCtx),
    Unavailable(String),
    /// Adapter initialization reached our shader, so a validation failure is
    /// an implementation bug rather than a capability fallback.
    Broken(String),
}

#[derive(Clone, Copy)]
enum GpuNttOperation {
    Multiply,
    Transform(OddNttDirection),
}

fn dispatch_stages<F>(
    dispatch: &mut F,
    pipeline: &wgpu::ComputePipeline,
    degree: u32,
    log_degree: u32,
    rows: u32,
    modulus_rows: u32,
    roots_offset: u32,
) where
    F: FnMut(&wgpu::ComputePipeline, [u32; 8], u32),
{
    let mut len = 2u32;
    while len <= degree {
        let half = len / 2;
        let step = degree / len;
        dispatch(
            pipeline,
            [
                degree,
                log_degree,
                half,
                step,
                roots_offset,
                rows,
                modulus_rows,
                0,
            ],
            degree / 2,
        );
        len *= 2;
    }
}

fn gpu_state() -> &'static GpuState {
    static GPU: OnceLock<GpuState> = OnceLock::new();
    GPU.get_or_init(GpuCtx::initialize)
}

struct GpuCtx {
    _instance: wgpu::Instance,
    device: wgpu::Device,
    queue: wgpu::Queue,
    adapter: String,
    limits: wgpu::Limits,
    bgl: wgpu::BindGroupLayout,
    twist_both: wgpu::ComputePipeline,
    twist_lhs: wgpu::ComputePipeline,
    bit_reverse_both: wgpu::ComputePipeline,
    stage_both: wgpu::ComputePipeline,
    pointwise: wgpu::ComputePipeline,
    bit_reverse_lhs: wgpu::ComputePipeline,
    bit_reverse_lhs_mont: wgpu::ComputePipeline,
    stage_lhs: wgpu::ComputePipeline,
    finalize_lhs: wgpu::ComputePipeline,
    /// One bounded resident immutable table family. Coefficient buffers stay
    /// per-call, while public moduli/roots/twists survive repeated private-book
    /// transforms on the same adapter.
    static_tables: Mutex<Option<GpuStaticTableCache>>,
}

struct GpuStaticTableCache {
    degree: usize,
    moduli: Vec<u64>,
    tables: Arc<GpuStaticTables>,
}

struct GpuStaticTables {
    moduli: wgpu::Buffer,
    roots: wgpu::Buffer,
    twists: wgpu::Buffer,
}

impl GpuCtx {
    fn initialize() -> GpuState {
        let instance = wgpu::Instance::default();
        let Some(adapter) =
            pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
                power_preference: wgpu::PowerPreference::HighPerformance,
                ..Default::default()
            }))
        else {
            return GpuState::Unavailable("no wgpu adapter".to_owned());
        };
        let info = adapter.get_info();
        let limits = adapter.limits();
        let (device, queue) = match pollster::block_on(adapter.request_device(
            &wgpu::DeviceDescriptor {
                label: Some("bfv-rns-ntt"),
                required_features: wgpu::Features::empty(),
                required_limits: limits.clone(),
                memory_hints: Default::default(),
            },
            None,
        )) {
            Ok(pair) => pair,
            Err(error) => {
                return GpuState::Unavailable(format!("wgpu device request failed: {error}"));
            }
        };

        device.push_error_scope(wgpu::ErrorFilter::Validation);
        let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("bfv_ntt.wgsl"),
            source: wgpu::ShaderSource::Wgsl(include_str!("shaders/bfv_ntt.wgsl").into()),
        });
        let bgl = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: Some("bfv-rns-ntt-bindings"),
            entries: &[
                buffer_entry(0, wgpu::BufferBindingType::Uniform),
                buffer_entry(1, wgpu::BufferBindingType::Storage { read_only: false }),
                buffer_entry(2, wgpu::BufferBindingType::Storage { read_only: false }),
                buffer_entry(3, wgpu::BufferBindingType::Storage { read_only: true }),
                buffer_entry(4, wgpu::BufferBindingType::Storage { read_only: true }),
                buffer_entry(5, wgpu::BufferBindingType::Storage { read_only: true }),
            ],
        });
        let layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: Some("bfv-rns-ntt-layout"),
            bind_group_layouts: &[&bgl],
            push_constant_ranges: &[],
        });
        let make_pipeline = |entry: &'static str| {
            device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                label: Some(entry),
                layout: Some(&layout),
                module: &shader,
                entry_point: Some(entry),
                compilation_options: Default::default(),
                cache: None,
            })
        };
        let twist_both = make_pipeline("twist_both");
        let twist_lhs = make_pipeline("twist_lhs");
        let bit_reverse_both = make_pipeline("bit_reverse_both");
        let stage_both = make_pipeline("stage_both");
        let pointwise = make_pipeline("pointwise");
        let bit_reverse_lhs = make_pipeline("bit_reverse_lhs");
        let bit_reverse_lhs_mont = make_pipeline("bit_reverse_lhs_mont");
        let stage_lhs = make_pipeline("stage_lhs");
        let finalize_lhs = make_pipeline("finalize_lhs");
        if let Some(error) = pollster::block_on(device.pop_error_scope()) {
            return GpuState::Broken(format!("BFV NTT shader validation failed: {error}"));
        }
        GpuState::Ready(Self {
            _instance: instance,
            device,
            queue,
            adapter: format!("{} ({:?})", info.name, info.backend),
            limits,
            bgl,
            twist_both,
            twist_lhs,
            bit_reverse_both,
            stage_both,
            pointwise,
            bit_reverse_lhs,
            bit_reverse_lhs_mont,
            stage_lhs,
            finalize_lhs,
            static_tables: Mutex::new(None),
        })
    }

    fn supports(&self, plan: &NttPlan, batch_size: usize) -> std::result::Result<(), String> {
        if batch_size == 0 {
            return Err("odd-NTT GPU batch is empty".to_owned());
        }
        validate_gpu_montgomery_moduli(&plan.moduli)?;
        if self.limits.max_storage_buffers_per_shader_stage < 5 {
            return Err(format!(
                "adapter exposes {} storage buffers per compute stage; 5 required",
                self.limits.max_storage_buffers_per_shader_stage
            ));
        }
        let rows = plan.moduli.len() as u64;
        let degree = plan.degree as u64;
        let coefficient_bytes_per_polynomial = rows
            .checked_mul(degree)
            .and_then(|count| count.checked_mul(8))
            .ok_or_else(|| "coefficient buffer size overflow".to_owned())?;
        let coefficient_bytes = coefficient_bytes_per_polynomial
            .checked_mul(batch_size as u64)
            .ok_or_else(|| "batched coefficient buffer size overflow".to_owned())?;
        let table_bytes = coefficient_bytes_per_polynomial
            .checked_mul(2)
            .ok_or_else(|| "root/twist table size overflow".to_owned())?;
        let max_storage = self
            .limits
            .max_buffer_size
            .min(u64::from(self.limits.max_storage_buffer_binding_size));
        if coefficient_bytes > max_storage || table_bytes > max_storage {
            return Err(format!(
                "shape needs {coefficient_bytes}-byte coefficient and {table_bytes}-byte table \
                 bindings, adapter limit is {max_storage}"
            ));
        }
        let workgroups_x = (plan.degree as u32).div_ceil(WORKGROUP_SIZE);
        let total_rows = plan
            .moduli
            .len()
            .checked_mul(batch_size)
            .and_then(|rows| u32::try_from(rows).ok())
            .ok_or_else(|| "batched RNS row count exceeds u32".to_owned())?;
        if workgroups_x > self.limits.max_compute_workgroups_per_dimension
            || total_rows > self.limits.max_compute_workgroups_per_dimension
        {
            return Err("dispatch dimensions exceed adapter limits".to_owned());
        }
        Ok(())
    }

    fn multiply(&self, lhs: &RnsPoly, rhs: &RnsPoly, plan: &NttPlan) -> Result<RnsPoly> {
        let (mut outputs, _) = self.execute_batch(
            std::slice::from_ref(lhs),
            Some(std::slice::from_ref(rhs)),
            plan,
            GpuNttOperation::Multiply,
        )?;
        Ok(outputs
            .pop()
            .expect("one-pair multiply batch returns one polynomial"))
    }

    fn multiply_batch(
        &self,
        lhs: &[RnsPoly],
        rhs: &[RnsPoly],
        plan: &NttPlan,
    ) -> Result<(Vec<RnsPoly>, usize)> {
        self.execute_batch(lhs, Some(rhs), plan, GpuNttOperation::Multiply)
    }

    fn transform_odd_batch(
        &self,
        inputs: &[RnsPoly],
        plan: &NttPlan,
        direction: OddNttDirection,
    ) -> Result<(Vec<RnsPoly>, usize)> {
        self.execute_batch(inputs, None, plan, GpuNttOperation::Transform(direction))
    }

    fn static_tables(&self, plan: &NttPlan) -> (Arc<GpuStaticTables>, usize) {
        use wgpu::util::DeviceExt;

        let mut cache = self
            .static_tables
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if let Some(cache) = cache
            .as_ref()
            .filter(|cache| cache.degree == plan.degree && cache.moduli == plan.moduli)
        {
            return (Arc::clone(&cache.tables), 0);
        }

        // Serialize the rare miss so reported upload counts remain actual;
        // speculative losing allocations would otherwise upload three buffers
        // but return the winning cache entry as a zero-upload hit.
        let mut qdata = Vec::with_capacity(plan.moduli.len() * 8);
        let mut roots = Vec::with_capacity(plan.moduli.len() * plan.degree * 4);
        let mut twists = Vec::with_capacity(plan.moduli.len() * plan.degree * 4);
        for (&q, row) in plan.moduli.iter().zip(&plan.rows) {
            let q_inverse = inverse_mod_2_16(q as u16).wrapping_neg();
            let r_squared = mod_mul(row.montgomery_r, row.montgomery_r, q);
            qdata.extend_from_slice(&[
                q as u32,
                (q >> 32) as u32,
                u32::from(q_inverse),
                0,
                r_squared as u32,
                (r_squared >> 32) as u32,
                0,
                0,
            ]);
            for &value in row.roots.iter().chain(&row.inverse_roots) {
                let value = mod_mul(value, row.montgomery_r, q);
                roots.extend_from_slice(&[value as u32, (value >> 32) as u32]);
            }
            // A forward twist converts the canonical uploaded coefficient at
            // the same time: REDC(value * twist*R^2) = value*twist*R.
            for &value in &row.twists {
                let value = mod_mul(value, r_squared, q);
                twists.extend_from_slice(&[value as u32, (value >> 32) as u32]);
            }
            // Inverse scales consume an already-Montgomery butterfly value,
            // so these carry the ordinary single R factor.
            for &value in &row.inverse_twists_times_n_inv {
                let value = mod_mul(value, row.montgomery_r, q);
                twists.extend_from_slice(&[value as u32, (value >> 32) as u32]);
            }
        }
        let prepared = Arc::new(GpuStaticTables {
            moduli: self
                .device
                .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                    label: Some("bfv-ntt-moduli"),
                    contents: bytemuck::cast_slice(&qdata),
                    usage: wgpu::BufferUsages::STORAGE,
                }),
            roots: self
                .device
                .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                    label: Some("bfv-ntt-roots"),
                    contents: bytemuck::cast_slice(&roots),
                    usage: wgpu::BufferUsages::STORAGE,
                }),
            twists: self
                .device
                .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                    label: Some("bfv-ntt-twists"),
                    contents: bytemuck::cast_slice(&twists),
                    usage: wgpu::BufferUsages::STORAGE,
                }),
        });

        *cache = Some(GpuStaticTableCache {
            degree: plan.degree,
            moduli: plan.moduli.clone(),
            tables: Arc::clone(&prepared),
        });
        (prepared, 3)
    }

    fn execute_batch(
        &self,
        lhs: &[RnsPoly],
        rhs: Option<&[RnsPoly]>,
        plan: &NttPlan,
        operation: GpuNttOperation,
    ) -> Result<(Vec<RnsPoly>, usize)> {
        use wgpu::util::DeviceExt;

        if lhs.is_empty() || rhs.is_some_and(|rhs| rhs.len() != lhs.len()) {
            return Err(BfvNttError::InvalidShape(
                "GPU NTT batch is empty or operand batch lengths differ",
            ));
        }

        // Any buffer/bind/dispatch validation failure is a kernel error. It
        // must not escape as an uncaptured panic or be converted into a CPU
        // capability fallback.
        self.device.push_error_scope(wgpu::ErrorFilter::Validation);

        let pack = |polynomials: &[RnsPoly]| -> Vec<u32> {
            let mut words =
                Vec::with_capacity(polynomials.len() * plan.moduli.len() * plan.degree * 2);
            for polynomial in polynomials {
                for row in &polynomial.rows {
                    for &value in row {
                        words.push(value as u32);
                        words.push((value >> 32) as u32);
                    }
                }
            }
            words
        };
        let lhs_words = pack(lhs);
        // The manual bind-group layout is shared by all entry points. A
        // standalone transform binds one inert coefficient in the unused RHS
        // slot; no duplicate polynomial upload is performed.
        let rhs_words = rhs.map(pack).unwrap_or_else(|| vec![0u32; 2]);
        let lhs_buf = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("bfv-ntt-lhs"),
                contents: bytemuck::cast_slice(&lhs_words),
                usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC,
            });
        let rhs_buf = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some("bfv-ntt-rhs"),
                contents: bytemuck::cast_slice(&rhs_words),
                usage: wgpu::BufferUsages::STORAGE,
            });
        let (static_tables, gpu_static_table_uploads) = self.static_tables(plan);

        let output_bytes = (lhs_words.len() * std::mem::size_of::<u32>()) as u64;
        let read_buf = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("bfv-ntt-readback"),
            size: output_bytes,
            usage: wgpu::BufferUsages::COPY_DST | wgpu::BufferUsages::MAP_READ,
            mapped_at_creation: false,
        });

        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("bfv-rns-ntt"),
            });
        let mut metadata_buffers = Vec::new();
        let mut bind_groups = Vec::new();
        let modulus_rows = plan.moduli.len() as u32;
        let rows = u32::try_from(plan.moduli.len() * lhs.len())
            .expect("GpuCtx::supports bounded the batched RNS row count");
        let degree = plan.degree as u32;
        let log_degree = plan.log_degree;
        let mut dispatch =
            |pipeline: &wgpu::ComputePipeline, meta: [u32; 8], invocations_x: u32| {
                let meta_buf = self
                    .device
                    .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                        label: Some("bfv-ntt-meta"),
                        contents: bytemuck::cast_slice(&meta),
                        usage: wgpu::BufferUsages::UNIFORM,
                    });
                let bind = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
                    label: Some("bfv-ntt-bind"),
                    layout: &self.bgl,
                    entries: &[
                        wgpu::BindGroupEntry {
                            binding: 0,
                            resource: meta_buf.as_entire_binding(),
                        },
                        wgpu::BindGroupEntry {
                            binding: 1,
                            resource: lhs_buf.as_entire_binding(),
                        },
                        wgpu::BindGroupEntry {
                            binding: 2,
                            resource: rhs_buf.as_entire_binding(),
                        },
                        wgpu::BindGroupEntry {
                            binding: 3,
                            resource: static_tables.moduli.as_entire_binding(),
                        },
                        wgpu::BindGroupEntry {
                            binding: 4,
                            resource: static_tables.roots.as_entire_binding(),
                        },
                        wgpu::BindGroupEntry {
                            binding: 5,
                            resource: static_tables.twists.as_entire_binding(),
                        },
                    ],
                });
                {
                    let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                        label: Some("bfv-ntt-dispatch"),
                        timestamp_writes: None,
                    });
                    pass.set_pipeline(pipeline);
                    pass.set_bind_group(0, &bind, &[]);
                    pass.dispatch_workgroups(invocations_x.div_ceil(WORKGROUP_SIZE), rows, 1);
                }
                metadata_buffers.push(meta_buf);
                bind_groups.push(bind);
            };

        let base_meta = [degree, log_degree, 0, 0, 0, rows, modulus_rows, 0];
        match operation {
            GpuNttOperation::Multiply => {
                dispatch(&self.twist_both, base_meta, degree);
                dispatch(&self.bit_reverse_both, base_meta, degree);
                dispatch_stages(
                    &mut dispatch,
                    &self.stage_both,
                    degree,
                    log_degree,
                    rows,
                    modulus_rows,
                    0,
                );
                dispatch(&self.pointwise, base_meta, degree);
                dispatch(&self.bit_reverse_lhs, base_meta, degree);
                dispatch_stages(
                    &mut dispatch,
                    &self.stage_lhs,
                    degree,
                    log_degree,
                    rows,
                    modulus_rows,
                    degree,
                );
                dispatch(&self.finalize_lhs, base_meta, degree);
            }
            GpuNttOperation::Transform(OddNttDirection::Forward) => {
                dispatch(&self.twist_lhs, base_meta, degree);
                dispatch(&self.bit_reverse_lhs, base_meta, degree);
                dispatch_stages(
                    &mut dispatch,
                    &self.stage_lhs,
                    degree,
                    log_degree,
                    rows,
                    modulus_rows,
                    0,
                );
            }
            GpuNttOperation::Transform(OddNttDirection::Inverse) => {
                dispatch(&self.bit_reverse_lhs_mont, base_meta, degree);
                dispatch_stages(
                    &mut dispatch,
                    &self.stage_lhs,
                    degree,
                    log_degree,
                    rows,
                    modulus_rows,
                    degree,
                );
                dispatch(&self.finalize_lhs, base_meta, degree);
            }
        }
        drop(dispatch);
        encoder.copy_buffer_to_buffer(&lhs_buf, 0, &read_buf, 0, output_bytes);

        self.queue.submit([encoder.finish()]);
        self.device.poll(wgpu::Maintain::Wait);
        if let Some(error) = pollster::block_on(self.device.pop_error_scope()) {
            return Err(BfvNttError::GpuExecution(format!(
                "buffer/bind/dispatch validation failed: {error}"
            )));
        }
        let slice = read_buf.slice(..);
        let (sender, receiver) = mpsc::sync_channel(1);
        slice.map_async(wgpu::MapMode::Read, move |status| {
            let _ = sender.send(status);
        });
        self.device.poll(wgpu::Maintain::Wait);
        receiver
            .recv()
            .map_err(|error| BfvNttError::GpuExecution(error.to_string()))?
            .map_err(|error| BfvNttError::GpuExecution(error.to_string()))?;
        let mapped = slice.get_mapped_range();
        let words: &[u32] = bytemuck::cast_slice(&mapped);
        let output = if words.len() == lhs_words.len() {
            let mut output_polynomials = Vec::with_capacity(lhs.len());
            let mut cursor = 0usize;
            for _ in lhs {
                let mut output_rows = Vec::with_capacity(plan.moduli.len());
                for _ in &plan.moduli {
                    let mut row = Vec::with_capacity(plan.degree);
                    for _ in 0..plan.degree {
                        row.push(u64::from(words[cursor]) | (u64::from(words[cursor + 1]) << 32));
                        cursor += 2;
                    }
                    output_rows.push(row);
                }
                output_polynomials.push(RnsPoly { rows: output_rows });
            }
            Some(output_polynomials)
        } else {
            None
        };
        drop(mapped);
        read_buf.unmap();
        let output_polynomials = output.ok_or_else(|| {
            BfvNttError::GpuExecution(
                "readback word count differs from the preflighted shape".to_owned(),
            )
        })?;
        for (polynomial, output) in output_polynomials.iter().enumerate() {
            for (row, (&q, coefficients)) in plan.moduli.iter().zip(&output.rows).enumerate() {
                if let Some((coefficient, &value)) = coefficients
                    .iter()
                    .enumerate()
                    .find(|(_, value)| **value >= q)
                {
                    return Err(BfvNttError::GpuExecution(format!(
                        "shader emitted non-canonical residue at polynomial {polynomial}, row {row}, \
                         coefficient {coefficient}: {value} >= {q}"
                    )));
                }
            }
        }
        Ok((output_polynomials, gpu_static_table_uploads))
    }
}

fn buffer_entry(binding: u32, ty: wgpu::BufferBindingType) -> wgpu::BindGroupLayoutEntry {
    wgpu::BindGroupLayoutEntry {
        binding,
        visibility: wgpu::ShaderStages::COMPUTE,
        ty: wgpu::BindingType::Buffer {
            ty,
            has_dynamic_offset: false,
            min_binding_size: None,
        },
        count: None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bfv_lean::{FOLD_DEGREE, FOLD_MODULI};
    use fhe_math::rq::{traits::TryConvertFrom, Poly, Representation};
    use std::time::Instant;

    fn schoolbook(lhs: &[u64], rhs: &[u64], q: u64) -> Vec<u64> {
        let degree = lhs.len();
        let mut out = vec![0u64; degree];
        for (i, &a) in lhs.iter().enumerate() {
            for (j, &b) in rhs.iter().enumerate() {
                let product = mod_mul(a, b, q);
                let index = i + j;
                if index < degree {
                    out[index] = add_mod(out[index], product, q);
                } else {
                    out[index - degree] = sub_mod(out[index - degree], product, q);
                }
            }
        }
        out
    }

    /// Integer twin of the fixed-loop WGSL REDC, checked against the u128
    /// oracle below. Deliberately uses u32 accumulators so a violated limb
    /// bound panics in debug tests instead of being hidden by a wider host sum.
    fn montgomery_mul_radix16_reference(a: u64, b: u64, q: u64) -> u64 {
        const MASK: u32 = 0xffff;
        let digits = |value: u64| {
            [
                value as u32 & MASK,
                (value >> 16) as u32 & MASK,
                (value >> 32) as u32 & MASK,
            ]
        };
        let a = digits(a);
        let b = digits(b);
        let q_digits = digits(q);
        let q_inverse = u32::from(inverse_mod_2_16(q as u16).wrapping_neg());
        let mut t = [0u32; 7];

        for i in 0..3 {
            let mut carry = 0u32;
            for j in 0..3 {
                let index = i + j;
                let uv = t[index]
                    .checked_add(a[j].checked_mul(b[i]).expect("16-bit product"))
                    .and_then(|uv| uv.checked_add(carry))
                    .expect("radix-2^16 product accumulator fits u32");
                t[index] = uv & MASK;
                carry = uv >> 16;
            }
            for digit in &mut t[i + 3..] {
                let uv = digit
                    .checked_add(carry)
                    .expect("product carry propagation fits u32");
                *digit = uv & MASK;
                carry = uv >> 16;
            }
            assert_eq!(carry, 0, "seven limbs carry the complete product");

            let multiplier = t[i].wrapping_mul(q_inverse) & MASK;
            carry = 0;
            for j in 0..3 {
                let index = i + j;
                let uv = t[index]
                    .checked_add(
                        multiplier
                            .checked_mul(q_digits[j])
                            .expect("16-bit reduction product"),
                    )
                    .and_then(|uv| uv.checked_add(carry))
                    .expect("radix-2^16 reduction accumulator fits u32");
                t[index] = uv & MASK;
                carry = uv >> 16;
            }
            for digit in &mut t[i + 3..] {
                let uv = digit
                    .checked_add(carry)
                    .expect("reduction carry propagation fits u32");
                *digit = uv & MASK;
                carry = uv >> 16;
            }
            assert_eq!(carry, 0, "seven limbs carry the complete reduction");
            assert_eq!(t[i], 0, "Montgomery reduction cancels the low limb");
        }

        let mut reduced = u64::from(t[3])
            | (u64::from(t[4]) << 16)
            | (u64::from(t[5]) << 32)
            | (u64::from(t[6]) << 48);
        if reduced >= q {
            reduced -= q;
        }
        assert!(reduced < q);
        reduced
    }

    fn deployed_poly(seed: u64) -> RnsPoly {
        let mut state = seed;
        RnsPoly {
            rows: FOLD_MODULI
                .iter()
                .enumerate()
                .map(|(row, &q)| {
                    (0..FOLD_DEGREE)
                        .map(|i| {
                            state = state
                                .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                                .rotate_left(17)
                                .wrapping_add((row + i + 1) as u64);
                            match i {
                                0 => q - 1,
                                1 => 0,
                                _ => state % q,
                            }
                        })
                        .collect()
                })
                .collect(),
        }
    }

    #[test]
    fn cpu_reference_matches_independent_schoolbook_negacyclic_product() {
        let q = 97u64; // prime and 1 mod 2*8
        let lhs = RnsPoly {
            rows: vec![vec![96, 0, 1, 2, 33, 71, 95, 4]],
        };
        let rhs = RnsPoly {
            rows: vec![vec![5, 96, 0, 19, 88, 1, 2, 3]],
        };
        let got = multiply_rns_cpu(&lhs, &rhs, &[q]).expect("CPU NTT product");
        assert_eq!(got.rows[0], schoolbook(&lhs.rows[0], &rhs.rows[0], q));

        let identity = RnsPoly {
            rows: vec![vec![1, 0, 0, 0, 0, 0, 0, 0]],
        };
        assert_eq!(
            multiply_rns_cpu(&lhs, &identity, &[q]).expect("NTT round trip"),
            lhs,
            "forward + inverse negacyclic NTT must recover every exact coefficient"
        );
    }

    #[test]
    fn radix16_montgomery_reduction_matches_u128_oracle_at_deployed_boundaries() {
        for &q in &FOLD_MODULI {
            assert!(q < GPU_MONTGOMERY_RADIX);
            let q_inverse = inverse_mod_2_16(q as u16).wrapping_neg();
            assert_eq!((q as u16).wrapping_mul(q_inverse), u16::MAX);
            let r = (u128::from(GPU_MONTGOMERY_RADIX) % u128::from(q)) as u64;
            let boundaries = [
                0,
                1,
                q / 2,
                u64::from(u32::MAX),
                u64::from(u32::MAX) + 1,
                q - 1,
            ];
            for &a in &boundaries {
                for &b in &boundaries {
                    let a_r = mod_mul(a, r, q);
                    let b_r = mod_mul(b, r, q);
                    let product_r = montgomery_mul_radix16_reference(a_r, b_r, q);
                    assert_eq!(product_r, mod_mul(mod_mul(a, b, q), r, q));
                    assert_eq!(
                        montgomery_mul_radix16_reference(product_r, 1, q),
                        mod_mul(a, b, q)
                    );
                }
            }

            let mut state = q ^ 0x6750_4e54_545f_4d4f;
            for _ in 0..16_384 {
                state = state
                    .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                    .rotate_left(17)
                    .wrapping_add(0xda94_2042_e4dd_58b5);
                let a = state % q;
                state = state
                    .wrapping_mul(0xd134_2543_de82_ef95)
                    .rotate_left(29)
                    .wrapping_add(0x94d0_49bb_1331_11eb);
                let b = state % q;
                let a_r = mod_mul(a, r, q);
                let b_r = mod_mul(b, r, q);
                let product_r = montgomery_mul_radix16_reference(a_r, b_r, q);
                assert_eq!(product_r, mod_mul(mod_mul(a, b, q), r, q));
                assert_eq!(
                    montgomery_mul_radix16_reference(product_r, 1, q),
                    mod_mul(a, b, q)
                );
            }
        }
    }

    #[test]
    fn radix16_gpu_carrier_accepts_deployed_moduli_and_refuses_wider_families() {
        validate_gpu_montgomery_moduli(&FOLD_MODULI).expect("deployed q0/q1/q2 fit 48 bits");
        let error = validate_gpu_montgomery_moduli(&[FOLD_MODULI[0], GPU_MONTGOMERY_RADIX])
            .expect_err("a 48-bit modulus does not fit the three-limb carrier");
        assert!(error.contains("exceeds the exact three-limb radix-2^16 GPU carrier"));
    }

    #[test]
    fn hostile_shape_modulus_and_residue_inputs_fail_before_dispatch() {
        let valid = RnsPoly {
            rows: vec![vec![0; 8]],
        };
        let short = RnsPoly {
            rows: vec![vec![0; 7]],
        };
        assert!(matches!(
            multiply_rns_cpu(&short, &short, &[97]),
            Err(BfvNttError::InvalidShape(_))
        ));
        assert!(matches!(
            multiply_rns_cpu(&valid, &RnsPoly { rows: vec![] }, &[97]),
            Err(BfvNttError::InvalidShape(_))
        ));
        assert!(matches!(
            multiply_rns_cpu(&valid, &valid, &[91]),
            Err(BfvNttError::UnsupportedParameters(_))
        )); // composite
        let noncanonical = RnsPoly {
            rows: vec![vec![97, 0, 0, 0, 0, 0, 0, 0]],
        };
        assert!(matches!(
            multiply_rns_cpu(&noncanonical, &valid, &[97]),
            Err(BfvNttError::NonCanonical {
                operand: "lhs",
                row: 0,
                coefficient: 0,
                value: 97,
                modulus: 97,
            })
        ));
    }

    #[test]
    fn explicit_cpu_fallback_is_labelled_and_bit_exact() {
        let q = 97u64;
        let lhs = RnsPoly {
            rows: vec![vec![96, 3, 1, 2, 33, 71, 95, 4]],
        };
        let rhs = RnsPoly {
            rows: vec![vec![5, 96, 7, 19, 88, 1, 2, 3]],
        };
        let expected = multiply_rns_cpu(&lhs, &rhs, &[q]).expect("CPU reference");
        let execution = RnsNttEngine::cpu_only()
            .multiply(&lhs, &rhs, &[q])
            .expect("explicit CPU policy");
        assert_eq!(execution.polynomial, expected);
        assert_eq!(execution.backend, RnsNttBackend::CpuPolicy);
    }

    #[test]
    fn deployed_rows_match_fhe_math_and_gpu_roundtrip_is_bit_exact() {
        let lhs = deployed_poly(0x6750_0001);
        let rhs = deployed_poly(0x6750_0002);
        let cpu = multiply_rns_cpu(&lhs, &rhs, &FOLD_MODULI).expect("CPU NTT reference");

        // Independent oracle: fhe-math is the arithmetic layer used by fhe.rs.
        let context = Context::new_arc(&FOLD_MODULI, FOLD_DEGREE).expect("fhe-math context");
        let flatten = |poly: &RnsPoly| poly.rows.iter().flatten().copied().collect::<Vec<_>>();
        let mut oracle_lhs =
            Poly::try_convert_from(flatten(&lhs), &context, false, Representation::PowerBasis)
                .expect("oracle lhs");
        let mut oracle_rhs =
            Poly::try_convert_from(flatten(&rhs), &context, false, Representation::PowerBasis)
                .expect("oracle rhs");
        oracle_lhs.change_representation(Representation::Ntt);
        oracle_rhs.change_representation(Representation::Ntt);
        let mut oracle = &oracle_lhs * &oracle_rhs;
        oracle.change_representation(Representation::PowerBasis);
        let oracle_rows: Vec<Vec<u64>> = oracle
            .coefficients()
            .outer_iter()
            .map(|row| row.to_vec())
            .collect();
        assert_eq!(
            cpu.rows, oracle_rows,
            "CPU reference diverged from fhe-math"
        );

        let require_wgpu = std::env::var_os("DREGG_REQUIRE_WGPU").is_some();
        let engine = if require_wgpu {
            RnsNttEngine::require_wgpu()
        } else {
            RnsNttEngine::new()
        };
        let execution = engine
            .multiply(&lhs, &rhs, &FOLD_MODULI)
            .expect("GPU or explicit capability fallback");
        assert_eq!(
            execution.polynomial, cpu,
            "portable WGSL product diverged at an exact deployed coefficient"
        );

        // Multiplication by one forces the same twist -> forward NTT ->
        // inverse NTT -> untwist path and must recover every input coefficient.
        let identity = RnsPoly {
            rows: FOLD_MODULI
                .iter()
                .map(|_| {
                    let mut row = vec![0; FOLD_DEGREE];
                    row[0] = 1;
                    row
                })
                .collect(),
        };
        let roundtrip = engine
            .multiply(&lhs, &identity, &FOLD_MODULI)
            .expect("GPU NTT round trip");
        assert_eq!(
            roundtrip.polynomial, lhs,
            "NTT round trip changed coefficients"
        );
        match execution.backend {
            RnsNttBackend::Wgpu { adapter } => {
                eprintln!("portable BFV RNS NTT parity + roundtrip GREEN on {adapter}");
                assert!(matches!(roundtrip.backend, RnsNttBackend::Wgpu { .. }));
            }
            fallback => {
                assert!(
                    std::env::var_os("DREGG_REQUIRE_WGPU").is_none(),
                    "DREGG_REQUIRE_WGPU is set but BFV RNS NTT used {fallback:?}"
                );
                eprintln!(
                    "portable BFV RNS NTT GPU parity SKIPPED explicitly; exact CPU fallback used: {fallback:?}"
                );
            }
        }
    }

    fn direct_odd_forward_at(input: &[u64], frequency: usize, psi: u64, q: u64) -> u64 {
        input
            .iter()
            .enumerate()
            .fold(0u64, |acc, (coefficient, &value)| {
                let exponent = ((2 * frequency + 1) * coefficient) as u64;
                add_mod(acc, mod_mul(value, mod_pow(psi, exponent, q), q), q)
            })
    }

    fn direct_odd_inverse_at(spectrum: &[u64], coefficient: usize, psi: u64, q: u64) -> u64 {
        let psi_inverse = mod_pow(psi, q - 2, q);
        let n_inverse = mod_pow((spectrum.len() as u64) % q, q - 2, q);
        let sum = spectrum
            .iter()
            .enumerate()
            .fold(0u64, |acc, (frequency, &value)| {
                let exponent = ((2 * frequency + 1) * coefficient) as u64;
                add_mod(acc, mod_mul(value, mod_pow(psi_inverse, exponent, q), q), q)
            });
        mod_mul(sum, n_inverse, q)
    }

    #[test]
    fn production_family_row_decoder_is_total_exact_and_boundary_pinned() {
        let butterflies_per_transform = (PRIVATE_BOOK_DEGREE / 2) * PRIVATE_BOOK_LOG_DEGREE;
        let forward_rows =
            PRIVATE_BOOK_ORDER_COUNT * PRIVATE_BOOK_RNS_MODULUS_COUNT * butterflies_per_transform;
        let pointwise_rows = PRIVATE_BOOK_ORDER_COUNT
            * PRIVATE_BOOK_CIPHER_POLY_COUNT
            * PRIVATE_BOOK_RNS_MODULUS_COUNT
            * PRIVATE_BOOK_DEGREE;
        let inverse_rows = PRIVATE_BOOK_ORDER_COUNT
            * PRIVATE_BOOK_CIPHER_POLY_COUNT
            * PRIVATE_BOOK_RNS_MODULUS_COUNT
            * butterflies_per_transform;

        assert_eq!(PRIVATE_BOOK_NTT_TRACE_WIDTH, 48);
        assert_eq!(PRIVATE_BOOK_LIVE_FAMILY_ROWS, 1_032_192);
        assert_eq!(PRIVATE_BOOK_PADDED_FAMILY_ROWS, 1_048_576);
        assert_eq!(
            private_book_ntt_family_row(0).unwrap(),
            PrivateBookNttFamilyRow::ForwardU {
                order: 0,
                modulus: 0,
                stage: 0,
                butterfly: 0,
            }
        );
        assert_eq!(
            private_book_ntt_family_row(forward_rows - 1).unwrap(),
            PrivateBookNttFamilyRow::ForwardU {
                order: 3,
                modulus: 2,
                stage: 11,
                butterfly: 2047,
            }
        );
        assert_eq!(
            private_book_ntt_family_row(forward_rows).unwrap(),
            PrivateBookNttFamilyRow::Pointwise {
                order: 0,
                ciphertext_poly: 0,
                modulus: 0,
                coefficient: 0,
            }
        );
        assert_eq!(
            private_book_ntt_family_row(forward_rows + pointwise_rows).unwrap(),
            PrivateBookNttFamilyRow::InverseProduct {
                order: 0,
                ciphertext_poly: 0,
                modulus: 0,
                stage: 0,
                butterfly: 0,
            }
        );
        assert_eq!(
            private_book_ntt_family_row(forward_rows + pointwise_rows + inverse_rows).unwrap(),
            PrivateBookNttFamilyRow::Terminal {
                order: 0,
                ciphertext_poly: 0,
                modulus: 0,
                coefficient_pair: 0,
            }
        );
        assert_eq!(
            private_book_ntt_family_row(PRIVATE_BOOK_LIVE_FAMILY_ROWS - 1).unwrap(),
            PrivateBookNttFamilyRow::Terminal {
                order: 3,
                ciphertext_poly: 1,
                modulus: 2,
                coefficient_pair: 2047,
            }
        );
        assert_eq!(
            private_book_ntt_family_row(PRIVATE_BOOK_LIVE_FAMILY_ROWS).unwrap(),
            PrivateBookNttFamilyRow::Padding { padding_row: 0 }
        );
        assert_eq!(
            private_book_ntt_family_row(PRIVATE_BOOK_PADDED_FAMILY_ROWS - 1).unwrap(),
            PrivateBookNttFamilyRow::Padding {
                padding_row: 16_383,
            }
        );
        assert!(matches!(
            private_book_ntt_family_row(PRIVATE_BOOK_PADDED_FAMILY_ROWS),
            Err(BfvNttError::InvalidSchedule(_))
        ));

        // Exhaust the complete physical matrix and invert every decoded
        // address. This is stronger than checking section endpoints: no live
        // row can alias another semantic operation or disappear into padding.
        let mut counts = [0usize; 5];
        for physical_row in 0..PRIVATE_BOOK_PADDED_FAMILY_ROWS {
            let recomposed = match private_book_ntt_family_row(physical_row).unwrap() {
                PrivateBookNttFamilyRow::ForwardU {
                    order,
                    modulus,
                    stage,
                    butterfly,
                } => {
                    counts[0] += 1;
                    assert!(order < PRIVATE_BOOK_ORDER_COUNT);
                    assert!(modulus < PRIVATE_BOOK_RNS_MODULUS_COUNT);
                    assert!(stage < PRIVATE_BOOK_LOG_DEGREE);
                    assert!(butterfly < PRIVATE_BOOK_DEGREE / 2);
                    (order * PRIVATE_BOOK_RNS_MODULUS_COUNT + modulus) * butterflies_per_transform
                        + stage * (PRIVATE_BOOK_DEGREE / 2)
                        + butterfly
                }
                PrivateBookNttFamilyRow::Pointwise {
                    order,
                    ciphertext_poly,
                    modulus,
                    coefficient,
                } => {
                    counts[1] += 1;
                    assert!(order < PRIVATE_BOOK_ORDER_COUNT);
                    assert!(ciphertext_poly < PRIVATE_BOOK_CIPHER_POLY_COUNT);
                    assert!(modulus < PRIVATE_BOOK_RNS_MODULUS_COUNT);
                    assert!(coefficient < PRIVATE_BOOK_DEGREE);
                    forward_rows
                        + ((order * PRIVATE_BOOK_CIPHER_POLY_COUNT + ciphertext_poly)
                            * PRIVATE_BOOK_RNS_MODULUS_COUNT
                            + modulus)
                            * PRIVATE_BOOK_DEGREE
                        + coefficient
                }
                PrivateBookNttFamilyRow::InverseProduct {
                    order,
                    ciphertext_poly,
                    modulus,
                    stage,
                    butterfly,
                } => {
                    counts[2] += 1;
                    assert!(order < PRIVATE_BOOK_ORDER_COUNT);
                    assert!(ciphertext_poly < PRIVATE_BOOK_CIPHER_POLY_COUNT);
                    assert!(modulus < PRIVATE_BOOK_RNS_MODULUS_COUNT);
                    assert!(stage < PRIVATE_BOOK_LOG_DEGREE);
                    assert!(butterfly < PRIVATE_BOOK_DEGREE / 2);
                    forward_rows
                        + pointwise_rows
                        + ((order * PRIVATE_BOOK_CIPHER_POLY_COUNT + ciphertext_poly)
                            * PRIVATE_BOOK_RNS_MODULUS_COUNT
                            + modulus)
                            * butterflies_per_transform
                        + stage * (PRIVATE_BOOK_DEGREE / 2)
                        + butterfly
                }
                PrivateBookNttFamilyRow::Terminal {
                    order,
                    ciphertext_poly,
                    modulus,
                    coefficient_pair,
                } => {
                    counts[3] += 1;
                    assert!(order < PRIVATE_BOOK_ORDER_COUNT);
                    assert!(ciphertext_poly < PRIVATE_BOOK_CIPHER_POLY_COUNT);
                    assert!(modulus < PRIVATE_BOOK_RNS_MODULUS_COUNT);
                    assert!(coefficient_pair < PRIVATE_BOOK_DEGREE / 2);
                    forward_rows
                        + pointwise_rows
                        + inverse_rows
                        + ((order * PRIVATE_BOOK_CIPHER_POLY_COUNT + ciphertext_poly)
                            * PRIVATE_BOOK_RNS_MODULUS_COUNT
                            + modulus)
                            * (PRIVATE_BOOK_DEGREE / 2)
                        + coefficient_pair
                }
                PrivateBookNttFamilyRow::Padding { padding_row } => {
                    counts[4] += 1;
                    PRIVATE_BOOK_LIVE_FAMILY_ROWS + padding_row
                }
            };
            assert_eq!(recomposed, physical_row);
        }
        assert_eq!(counts, [294_912, 98_304, 589_824, 49_152, 16_384]);
    }

    #[test]
    fn deployed_scheduled_odd_ntt_is_lean_pinned_streamable_and_mutation_strict() {
        let input = deployed_poly(0x6750_4e54_5401);
        let cpu_engine = RnsNttEngine::cpu_only();
        let forward = cpu_engine
            .forward_odd(&input, &FOLD_MODULI)
            .expect("production CPU odd forward NTT");
        assert_eq!(forward.backend, RnsNttBackend::CpuPolicy);
        assert_eq!(forward.schedule.psi, DEPLOYED_ODD_NTT_PSI);
        assert_eq!(forward.schedule.stages.len(), PRIVATE_BOOK_LOG_DEGREE);
        assert_eq!(forward.schedule.butterfly_rows(), 3 * 24_576);
        forward
            .schedule
            .validate()
            .expect("canonical forward schedule");

        // Anchor the staged radix-2 implementation to Lean's direct
        // sum_j a_j*psi^((2k+1)j) definition at spread frequencies in every
        // deployed modulus, including the separately pinned q2 root.
        for (row, (&q, &psi)) in FOLD_MODULI.iter().zip(&DEPLOYED_ODD_NTT_PSI).enumerate() {
            for frequency in [0usize, 1, 17, 255, 2048, 4095] {
                assert_eq!(
                    forward.polynomial.rows[row][frequency],
                    direct_odd_forward_at(&input.rows[row], frequency, psi, q),
                    "direct odd-forward mismatch at row={row}, frequency={frequency}"
                );
            }
        }

        let mut butterfly_count = 0usize;
        let streamed = visit_odd_ntt_cpu(
            &input,
            &FOLD_MODULI,
            OddNttDirection::Forward,
            |butterfly| {
                assert_eq!(
                    butterfly.twiddled_right,
                    mod_mul(butterfly.right_input, butterfly.twiddle, butterfly.modulus)
                );
                assert_eq!(
                    butterfly.left_output,
                    add_mod(
                        butterfly.left_input,
                        butterfly.twiddled_right,
                        butterfly.modulus
                    )
                );
                assert_eq!(
                    butterfly.right_output,
                    sub_mod(
                        butterfly.left_input,
                        butterfly.twiddled_right,
                        butterfly.modulus
                    )
                );
                butterfly_count += 1;
            },
        )
        .expect("streaming CPU witness");
        assert_eq!(streamed, forward.polynomial);
        assert_eq!(butterfly_count, forward.schedule.butterfly_rows());

        let inverse = cpu_engine
            .inverse_odd(&forward.polynomial, &FOLD_MODULI)
            .expect("production CPU odd inverse NTT");
        assert_eq!(inverse.polynomial, input, "odd NTT round trip");
        inverse
            .schedule
            .validate()
            .expect("canonical inverse schedule");
        for (row, (&q, &psi)) in FOLD_MODULI.iter().zip(&DEPLOYED_ODD_NTT_PSI).enumerate() {
            for coefficient in [0usize, 3, 31, 511, 2049, 4095] {
                assert_eq!(
                    inverse.polynomial.rows[row][coefficient],
                    direct_odd_inverse_at(&forward.polynomial.rows[row], coefficient, psi, q),
                    "direct odd-inverse mismatch at row={row}, coefficient={coefficient}"
                );
            }
        }
        verify_odd_ntt_execution(&input, &FOLD_MODULI, &forward)
            .expect("honest execution verifies");

        let mut wrong_coefficient = forward.clone();
        wrong_coefficient.polynomial.rows[2][2049] = add_mod(
            wrong_coefficient.polynomial.rows[2][2049],
            1,
            FOLD_MODULI[2],
        );
        assert!(matches!(
            verify_odd_ntt_execution(&input, &FOLD_MODULI, &wrong_coefficient),
            Err(BfvNttError::OutputMismatch {
                row: 2,
                coefficient: 2049,
                ..
            })
        ));

        let mut wrong_stage = forward.clone();
        wrong_stage.schedule.stages[7].root_stride += 1;
        assert!(matches!(
            verify_odd_ntt_execution(&input, &FOLD_MODULI, &wrong_stage),
            Err(BfvNttError::InvalidSchedule(_))
        ));
        let mut wrong_root = forward.clone();
        wrong_root.schedule.psi[2] = 61_409_057_737; // another valid q2 root, wrong spectrum identity
        assert!(matches!(
            verify_odd_ntt_execution(&input, &FOLD_MODULI, &wrong_root),
            Err(BfvNttError::InvalidSchedule(_))
        ));
        let mut wrong_modulus = forward.clone();
        wrong_modulus.schedule.moduli.swap(0, 1);
        assert!(matches!(
            verify_odd_ntt_execution(&input, &FOLD_MODULI, &wrong_modulus),
            Err(BfvNttError::InvalidSchedule(_))
        ));
        let mut changed_input = input.clone();
        changed_input.rows[1][997] = add_mod(changed_input.rows[1][997], 1, FOLD_MODULI[1]);
        assert!(matches!(
            verify_odd_ntt_execution(&changed_input, &FOLD_MODULI, &forward),
            Err(BfvNttError::OutputMismatch { .. })
        ));
    }

    #[test]
    fn deployed_scheduled_odd_ntt_wgpu_matches_every_cpu_residue() {
        let input = deployed_poly(0x6750_4e54_5402);
        let cpu_forward = transform_odd_rns_cpu(&input, &FOLD_MODULI, OddNttDirection::Forward)
            .expect("CPU forward reference");
        let engine = RnsNttEngine::new();
        let gpu_forward = engine
            .forward_odd(&input, &FOLD_MODULI)
            .expect("GPU or explicit capability fallback forward transform");
        assert_eq!(gpu_forward.polynomial, cpu_forward);
        verify_odd_ntt_execution(&input, &FOLD_MODULI, &gpu_forward)
            .expect("forward execution verifies");

        let cpu_inverse =
            transform_odd_rns_cpu(&cpu_forward, &FOLD_MODULI, OddNttDirection::Inverse)
                .expect("CPU inverse reference");
        let gpu_inverse = engine
            .inverse_odd(&gpu_forward.polynomial, &FOLD_MODULI)
            .expect("GPU or explicit capability fallback inverse transform");
        assert_eq!(gpu_inverse.polynomial, cpu_inverse);
        assert_eq!(gpu_inverse.polynomial, input);
        verify_odd_ntt_execution(&gpu_forward.polynomial, &FOLD_MODULI, &gpu_inverse)
            .expect("inverse execution verifies");

        match (&gpu_forward.backend, &gpu_inverse.backend) {
            (
                RnsNttBackend::Wgpu { adapter: forward },
                RnsNttBackend::Wgpu { adapter: inverse },
            ) => {
                assert_eq!(forward, inverse);
                eprintln!(
                    "scheduled BFV odd forward/inverse parity GREEN on {forward}: \
                     2 transforms × 3 moduli × 4096 residues"
                );
            }
            (forward, inverse) => {
                assert!(
                    std::env::var_os("DREGG_REQUIRE_WGPU").is_none(),
                    "DREGG_REQUIRE_WGPU is set but odd NTT used {forward:?}/{inverse:?}"
                );
                eprintln!(
                    "scheduled BFV odd NTT GPU parity SKIPPED explicitly: {forward:?}/{inverse:?}"
                );
            }
        }
    }

    #[test]
    fn deployed_private_book_four_order_forward_batch_is_exact_and_profiled() {
        let inputs = [
            deployed_poly(0x6750_4e54_54b0),
            deployed_poly(0x6750_4e54_54b1),
            deployed_poly(0x6750_4e54_54b2),
            deployed_poly(0x6750_4e54_54b3),
        ];
        let expected = inputs
            .iter()
            .map(|input| {
                transform_odd_rns_cpu(input, &FOLD_MODULI, OddNttDirection::Forward)
                    .expect("CPU private-book forward oracle")
            })
            .collect::<Vec<_>>();
        let require_wgpu = std::env::var_os("DREGG_REQUIRE_WGPU").is_some();
        let engine = if require_wgpu {
            RnsNttEngine::require_wgpu()
        } else {
            RnsNttEngine::new()
        };

        // Warm adapter/pipeline initialization outside the deployed four-order timing.
        let warm = engine
            .forward_odd(&inputs[0], &FOLD_MODULI)
            .expect("warm exact odd NTT");
        assert_eq!(warm.polynomial, expected[0]);

        let sequential_started = Instant::now();
        let executions = inputs
            .iter()
            .map(|input| {
                engine
                    .forward_odd(input, &FOLD_MODULI)
                    .expect("private-book exact odd NTT")
            })
            .collect::<Vec<_>>();
        let sequential_elapsed = sequential_started.elapsed();
        for (execution, expected) in executions.iter().zip(&expected) {
            assert_eq!(&execution.polynomial, expected);
        }

        let batch_started = Instant::now();
        let batch = engine
            .forward_odd_batch(&inputs, &FOLD_MODULI)
            .expect("one-submission private-book odd-NTT batch");
        let batch_elapsed = batch_started.elapsed();
        assert_eq!(batch.polynomials, expected);
        assert_eq!(batch.schedule.psi, DEPLOYED_ODD_NTT_PSI);
        assert_eq!(batch.plan.input_polynomials, 4);
        assert_eq!(batch.plan.rns_rows_per_polynomial, 3);
        assert_eq!(batch.plan.total_rns_rows, 12);
        assert_eq!(batch.plan.degree, FOLD_DEGREE);
        assert!(batch.plan.host_plan_cache_hit);

        let inverse_batch = engine
            .inverse_odd_batch(&batch.polynomials, &FOLD_MODULI)
            .expect("one-submission private-book inverse odd-NTT batch");
        assert_eq!(inverse_batch.polynomials, inputs);
        assert_eq!(inverse_batch.plan.input_polynomials, 4);
        assert_eq!(inverse_batch.plan.total_rns_rows, 12);
        assert!(inverse_batch.plan.host_plan_cache_hit);
        assert_eq!(
            inverse_batch.plan.gpu_queue_submissions,
            batch.plan.gpu_queue_submissions
        );
        assert_eq!(inverse_batch.plan.gpu_readbacks, batch.plan.gpu_readbacks);

        match (&executions[0].backend, &batch.backend) {
            (
                RnsNttBackend::Wgpu { adapter },
                RnsNttBackend::Wgpu {
                    adapter: batch_adapter,
                },
            ) => {
                assert_eq!(batch_adapter, adapter);
                assert!(matches!(
                    &inverse_batch.backend,
                    RnsNttBackend::Wgpu { adapter: inverse_adapter } if inverse_adapter == adapter
                ));
                assert_eq!(batch.plan.gpu_dispatches, PRIVATE_BOOK_LOG_DEGREE + 2);
                assert_eq!(batch.plan.gpu_input_uploads, 1);
                assert_eq!(batch.plan.gpu_static_table_uploads, 0);
                assert_eq!(batch.plan.gpu_queue_submissions, 1);
                assert_eq!(batch.plan.gpu_readbacks, 1);
                assert_eq!(inverse_batch.plan.gpu_static_table_uploads, 0);
                assert!(executions.iter().all(
                    |execution| matches!(&execution.backend, RnsNttBackend::Wgpu { adapter: actual } if actual == adapter)
                ));
                eprintln!(
                    "private-book odd-NTT four-order batch GREEN on {adapter}: sequential={:.3}ms, batched={:.3}ms, ratio={:.3}x; metadata=cached host+GPU tables/1 input upload/1 submission/1 readback",
                    sequential_elapsed.as_secs_f64() * 1e3,
                    batch_elapsed.as_secs_f64() * 1e3,
                    sequential_elapsed.as_secs_f64() / batch_elapsed.as_secs_f64(),
                );
            }
            (fallback, batch_fallback) => {
                assert!(
                    !require_wgpu,
                    "RequireWgpu accepted non-GPU private-book batch {fallback:?}/{batch_fallback:?}"
                );
                assert_eq!(batch.plan.gpu_dispatches, 0);
                assert_eq!(batch.plan.gpu_input_uploads, 0);
                assert_eq!(batch.plan.gpu_static_table_uploads, 0);
                assert_eq!(batch.plan.gpu_queue_submissions, 0);
                assert_eq!(batch.plan.gpu_readbacks, 0);
                eprintln!(
                    "private-book odd-NTT four-order GPU profile SKIPPED explicitly: {fallback:?}/{batch_fallback:?}"
                );
            }
        }

        assert!(matches!(
            engine.forward_odd_batch(&[], &FOLD_MODULI),
            Err(BfvNttError::InvalidShape("odd-NTT batch is empty"))
        ));
        let mut wrong_shape = inputs[0].clone();
        wrong_shape.rows.pop();
        assert!(matches!(
            engine.forward_odd_batch(&[inputs[0].clone(), wrong_shape], &FOLD_MODULI),
            Err(BfvNttError::InvalidShape(_))
        ));
    }
}
