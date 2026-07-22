//! Ring-aware exact zero observation for the eight-equality residual.
//!
//! The generic bounded product computes `prod(i-r), i=1..=8` with seven
//! ciphertext-by-ciphertext multiplications. Pairing roots `i` and `9-i` and
//! sharing powers gives the exact identity
//!
//! ```text
//! u = r^2 - 9r
//! prod(i-r) = (u^2 + 28u + 160)(u^2 + 32u + 252).
//! ```
//!
//! This schedule uses three ciphertext multiplications at the same depth as
//! the balanced factor tree. It is exact only because the residual certificate
//! pins every live slot to `0..=8`; it is not a whole-field shortcut and the
//! runtime measurements below do not constitute a BFV noise theorem.

use std::fmt;
use std::sync::Arc;
use std::time::{Duration, Instant};

use fhe::bfv::{BfvParameters, Ciphertext, Encoding, Multiplicator, Plaintext, RelinearizationKey};
use fhe_traits::FheEncoder;
use serde::Serialize;

use super::logic_schedule::{
    BfvCostManifest, BfvLogicEngine, CompiledResidualEqualityPlan, DeclaredEncryptedNat,
    LogicBfvError,
};
use super::logic_zero_observation::{
    residual_statement_digest, SameOpeningReceipt, ZERO_OBSERVATION_VERSION,
};

pub const SYMMETRIC_EIGHT_BOUND: u64 = 8;
pub const SYMMETRIC_EIGHT_TRUE_SCALE: u64 = 40_320;

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SymmetricEightZeroCost {
    pub plaintext_constant_encodes: usize,
    pub ciphertext_multiplications: usize,
    pub relinearizations: usize,
    pub ciphertext_plaintext_multiplications: usize,
    pub ciphertext_additions: usize,
    pub ciphertext_subtractions: usize,
    pub ciphertext_plaintext_additions: usize,
    pub input_multiplicative_depth: usize,
    pub output_multiplicative_depth: usize,
}

impl SymmetricEightZeroCost {
    pub fn from_input_depth(input_multiplicative_depth: usize) -> Self {
        Self {
            plaintext_constant_encodes: 5,
            ciphertext_multiplications: 3,
            relinearizations: 3,
            ciphertext_plaintext_multiplications: 3,
            ciphertext_additions: 2,
            ciphertext_subtractions: 1,
            ciphertext_plaintext_additions: 2,
            input_multiplicative_depth,
            output_multiplicative_depth: input_multiplicative_depth + 3,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SymmetricEightZeroManifest {
    pub version: u32,
    pub strategy: &'static str,
    pub plaintext_modulus: u64,
    pub live_slots: usize,
    pub maximum_residual: u64,
    pub true_scale: u64,
    pub residual_computation_cost: BfvCostManifest,
    pub zero_conversion_cost: SymmetricEightZeroCost,
    pub same_opening: SameOpeningReceipt,
    pub output: &'static str,
    pub leakage: &'static str,
    pub trust_and_noise_boundary: Vec<&'static str>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SymmetricEightZeroPlan {
    manifest: SymmetricEightZeroManifest,
}

impl SymmetricEightZeroPlan {
    pub fn manifest(&self) -> &SymmetricEightZeroManifest {
        &self.manifest
    }
}

#[derive(Debug)]
pub struct SymmetricEightZeroExecution {
    pub manifest: SymmetricEightZeroManifest,
    pub output: Ciphertext,
    pub residual_evaluation_elapsed: Duration,
    pub zero_conversion_elapsed: Duration,
}

pub struct SymmetricEightZeroEngine {
    params: Arc<BfvParameters>,
    multiplicator: Multiplicator,
    plaintext_modulus: u64,
}

impl SymmetricEightZeroEngine {
    pub fn new(
        relinearization_key: &RelinearizationKey,
        params: Arc<BfvParameters>,
    ) -> Result<Self, SymmetricEightZeroError> {
        let plaintext_modulus = params.plaintext();
        if plaintext_modulus != 1_032_193 {
            return Err(SymmetricEightZeroError::UnsupportedPlaintextModulus { plaintext_modulus });
        }
        let multiplicator = Multiplicator::default(relinearization_key)
            .map_err(|error| SymmetricEightZeroError::Bfv(error.to_string()))?;
        Ok(Self {
            params,
            multiplicator,
            plaintext_modulus,
        })
    }

    pub fn compile(
        &self,
        compiled: &CompiledResidualEqualityPlan,
        inputs: &[DeclaredEncryptedNat],
        same_opening: SameOpeningReceipt,
        live_slots: usize,
    ) -> Result<SymmetricEightZeroPlan, SymmetricEightZeroError> {
        if live_slots == 0 {
            return Err(SymmetricEightZeroError::InvalidLiveSlots);
        }
        let maximum_residual = u64::try_from(compiled.certificate().maximum_residual_sum)
            .map_err(|_| SymmetricEightZeroError::WrongResidualBound { got: u64::MAX })?;
        if maximum_residual != SYMMETRIC_EIGHT_BOUND {
            return Err(SymmetricEightZeroError::WrongResidualBound {
                got: maximum_residual,
            });
        }
        let expected = residual_statement_digest(compiled, inputs, same_opening.opening_commitment);
        if same_opening.version != ZERO_OBSERVATION_VERSION
            || same_opening.statement_digest != expected
        {
            return Err(SymmetricEightZeroError::SameOpeningStatementMismatch);
        }
        let input_depth = compiled.cost().maximum_multiplicative_depth;
        Ok(SymmetricEightZeroPlan {
            manifest: SymmetricEightZeroManifest {
                version: ZERO_OBSERVATION_VERSION,
                strategy: "exact bound-eight symmetric root pairing with shared u and u^2",
                plaintext_modulus: self.plaintext_modulus,
                live_slots,
                maximum_residual,
                true_scale: SYMMETRIC_EIGHT_TRUE_SCALE,
                residual_computation_cost: compiled.cost().clone(),
                zero_conversion_cost: SymmetricEightZeroCost::from_input_depth(input_depth),
                same_opening,
                output: "encrypted scaled bit; 8! exactly when residual is zero and zero otherwise",
                leakage: "no residual or internal truth is opened by the conversion itself",
                trust_and_noise_boundary: vec![
                    "an external verifier must establish the same-opening receipt",
                    "the residual certificate must bound every live slot in 0..=8",
                    "the formal identity proves plaintext semantics, not BFV noise correctness",
                    "large plaintext coefficients can cost more noise than the multiplication count suggests",
                    "threshold or single-key executions are measurements, not a general depth theorem",
                ],
            },
        })
    }

    pub fn execute(
        &self,
        logic_engine: &BfvLogicEngine,
        compiled: &CompiledResidualEqualityPlan,
        inputs: &[DeclaredEncryptedNat],
        plan: &SymmetricEightZeroPlan,
    ) -> Result<SymmetricEightZeroExecution, SymmetricEightZeroError> {
        let expected = residual_statement_digest(
            compiled,
            inputs,
            plan.manifest.same_opening.opening_commitment,
        );
        if expected != plan.manifest.same_opening.statement_digest
            || compiled.cost() != &plan.manifest.residual_computation_cost
            || compiled.certificate().maximum_residual_sum
                != u128::from(plan.manifest.maximum_residual)
            || plan.manifest.maximum_residual != SYMMETRIC_EIGHT_BOUND
        {
            return Err(SymmetricEightZeroError::ManifestDrift);
        }

        let residual = logic_engine
            .execute_residual_equalities(compiled, inputs)
            .map_err(SymmetricEightZeroError::Logic)?;
        let started = Instant::now();
        let live_slots = plan.manifest.live_slots;

        let encode = |value: u64| {
            Plaintext::try_encode(&vec![value; live_slots], Encoding::simd(), &self.params)
                .map_err(|error| SymmetricEightZeroError::Bfv(error.to_string()))
        };
        let nine = encode(9)?;
        let twenty_eight = encode(28)?;
        let thirty_two = encode(32)?;
        let one_sixty = encode(160)?;
        let two_fifty_two = encode(252)?;

        // u = r^2 - 9r
        let r_squared = self
            .multiplicator
            .multiply(&residual.ciphertext, &residual.ciphertext)
            .map_err(|error| SymmetricEightZeroError::Bfv(error.to_string()))?;
        let nine_r = &residual.ciphertext * &nine;
        let u = &r_squared - &nine_r;

        // Both quadratic blocks share the only u^2 ciphertext.
        let u_squared = self
            .multiplicator
            .multiply(&u, &u)
            .map_err(|error| SymmetricEightZeroError::Bfv(error.to_string()))?;
        let twenty_eight_u = &u * &twenty_eight;
        let mut left = &u_squared + &twenty_eight_u;
        left += &one_sixty;
        let thirty_two_u = &u * &thirty_two;
        let mut right = &u_squared + &thirty_two_u;
        right += &two_fifty_two;

        let output = self
            .multiplicator
            .multiply(&left, &right)
            .map_err(|error| SymmetricEightZeroError::Bfv(error.to_string()))?;

        Ok(SymmetricEightZeroExecution {
            manifest: plan.manifest.clone(),
            output,
            residual_evaluation_elapsed: residual.elapsed,
            zero_conversion_elapsed: started.elapsed(),
        })
    }
}

#[derive(Debug)]
pub enum SymmetricEightZeroError {
    UnsupportedPlaintextModulus { plaintext_modulus: u64 },
    InvalidLiveSlots,
    WrongResidualBound { got: u64 },
    SameOpeningStatementMismatch,
    ManifestDrift,
    Bfv(String),
    Logic(LogicBfvError),
}

impl fmt::Display for SymmetricEightZeroError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsupportedPlaintextModulus { plaintext_modulus } => write!(
                f,
                "symmetric zero test supports plaintext modulus 1032193, got {plaintext_modulus}"
            ),
            Self::InvalidLiveSlots => {
                f.write_str("symmetric zero test needs at least one live slot")
            }
            Self::WrongResidualBound { got } => write!(
                f,
                "symmetric zero test is specialized to residual bound 8, got {got}"
            ),
            Self::SameOpeningStatementMismatch => {
                f.write_str("same-opening receipt does not bind this symmetric-zero statement")
            }
            Self::ManifestDrift => {
                f.write_str("symmetric-zero execution drifted from its checked manifest")
            }
            Self::Bfv(error) => write!(f, "symmetric-zero BFV operation failed: {error}"),
            Self::Logic(error) => write!(f, "symmetric-zero residual failed: {error}"),
        }
    }
}

impl std::error::Error for SymmetricEightZeroError {}
