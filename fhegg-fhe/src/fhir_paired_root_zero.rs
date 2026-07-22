//! Certified complementary-root lowering for bounded encrypted zero tests.
//!
//! The generic fhIR zero conversion evaluates
//! `P_B(r) = product_(i=1..B) (i-r)`.  Its plaintext semantics are exact on a
//! residual certified to lie in `0..=B`, but it needs `B-1`
//! ciphertext-by-ciphertext multiplications.  Pairing root `i` with
//! `B+1-i` gives
//!
//! ```text
//! (i-r)(B+1-i-r) = u + i(B+1-i),
//! u = r^2 - (B+1)r.
//! ```
//!
//! All pairs share the single ciphertext `u`.  A balanced product therefore
//! needs `ceil(B/2)` ciphertext multiplications for `B >= 2`, at the same
//! multiplicative depth as the generic balanced product.  Odd `B` contributes
//! the unpaired middle factor `(B+1)/2-r`.
//!
//! This module validates an existing residual no-wrap and same-opening
//! certificate; it does not infer either one.  The algebraic identity and
//! primitive-call ledger are exact.  The existing boundary remains explicit:
//! a successful BFV execution is not a general noise theorem, and an external
//! verifier must establish the same-opening receipt.

use std::fmt;
use std::sync::Arc;
use std::time::{Duration, Instant};

use fhe::bfv::{BfvParameters, Ciphertext, Encoding, Multiplicator, Plaintext, RelinearizationKey};
use fhe_traits::FheEncoder;
use serde::Serialize;

use crate::fhir::logic_schedule::{
    BfvCostManifest, BfvLogicEngine, CompiledResidualEqualityPlan, DeclaredEncryptedNat,
    LogicBfvError,
};
use crate::fhir::logic_zero_observation::{
    residual_statement_digest, SameOpeningReceipt, ZERO_OBSERVATION_VERSION,
};

pub const PAIRED_ROOT_ZERO_VERSION: u32 = 1;
pub const PAIRED_ROOT_MIN_BOUND: u64 = 4;
pub const PAIRED_ROOT_MAX_BOUND: u64 = 4_096;
pub const PAIRED_ROOT_PLAINTEXT_MODULUS: u64 = 1_032_193;

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct PairedRootCost {
    pub plaintext_constant_encodes: usize,
    pub ciphertext_multiplications: usize,
    pub relinearizations: usize,
    pub ciphertext_plaintext_multiplications: usize,
    pub ciphertext_plaintext_additions: usize,
    pub ciphertext_subtractions: usize,
    pub plaintext_ciphertext_subtractions: usize,
    pub input_multiplicative_depth: usize,
    pub output_multiplicative_depth: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct PairedRootCertificate {
    pub maximum_residual: u64,
    pub root_pair_count: usize,
    pub unpaired_middle_root: Option<u64>,
    pub covered_root_count: usize,
    pub generic_ciphertext_multiplications: usize,
    pub paired_ciphertext_multiplications: usize,
    pub saved_ciphertext_multiplications: usize,
    pub depth_preserved: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct PairedRootZeroManifest {
    pub version: u32,
    pub strategy: &'static str,
    pub plaintext_modulus: u64,
    pub live_slots: usize,
    pub maximum_residual: u64,
    pub true_scale: u64,
    pub residual_computation_cost: BfvCostManifest,
    pub zero_conversion_cost: PairedRootCost,
    pub certificate: PairedRootCertificate,
    pub same_opening: SameOpeningReceipt,
    pub output: &'static str,
    pub leakage: &'static str,
    pub trust_and_noise_boundary: Vec<&'static str>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairedRootZeroPlan {
    manifest: PairedRootZeroManifest,
}

impl PairedRootZeroPlan {
    pub fn manifest(&self) -> &PairedRootZeroManifest {
        &self.manifest
    }
}

#[derive(Debug)]
pub struct PairedRootZeroExecution {
    pub manifest: PairedRootZeroManifest,
    pub output: Ciphertext,
    pub residual_evaluation_elapsed: Duration,
    pub zero_conversion_elapsed: Duration,
}

pub struct PairedRootZeroEngine {
    params: Arc<BfvParameters>,
    multiplicator: Multiplicator,
    plaintext_modulus: u64,
}

fn ceil_log2(value: usize) -> usize {
    if value <= 1 {
        0
    } else {
        usize::BITS as usize - (value - 1).leading_zeros() as usize
    }
}

fn factorial_mod(bound: u64, modulus: u64) -> u64 {
    (1..=bound).fold(1, |acc, value| {
        ((u128::from(acc) * u128::from(value)) % u128::from(modulus)) as u64
    })
}

fn expected_parts(
    bound: u64,
    input_depth: usize,
) -> Result<(PairedRootCost, PairedRootCertificate), PairedRootZeroError> {
    if !(PAIRED_ROOT_MIN_BOUND..=PAIRED_ROOT_MAX_BOUND).contains(&bound) {
        return Err(PairedRootZeroError::UnsupportedResidualBound { bound });
    }
    let root_pair_count = usize::try_from(bound / 2)
        .map_err(|_| PairedRootZeroError::UnsupportedResidualBound { bound })?;
    let unpaired_middle_root = (bound % 2 == 1).then_some((bound + 1) / 2);
    let factor_count = root_pair_count + usize::from(unpaired_middle_root.is_some());
    let paired_ciphertext_multiplications = factor_count;
    let generic_ciphertext_multiplications = usize::try_from(bound - 1)
        .map_err(|_| PairedRootZeroError::UnsupportedResidualBound { bound })?;
    let saved_ciphertext_multiplications = generic_ciphertext_multiplications
        .checked_sub(paired_ciphertext_multiplications)
        .ok_or(PairedRootZeroError::NoStrictSaving { bound })?;
    if saved_ciphertext_multiplications == 0 {
        return Err(PairedRootZeroError::NoStrictSaving { bound });
    }
    let generic_output_depth = input_depth + ceil_log2(bound as usize);
    let paired_output_depth = input_depth + 1 + ceil_log2(factor_count);
    let cost = PairedRootCost {
        // B+1, one constant per root pair, and the odd middle root if present.
        plaintext_constant_encodes: 1 + factor_count,
        // One shared r^2 plus factor_count-1 balanced factor products.
        ciphertext_multiplications: paired_ciphertext_multiplications,
        relinearizations: paired_ciphertext_multiplications,
        ciphertext_plaintext_multiplications: 1,
        ciphertext_plaintext_additions: root_pair_count,
        ciphertext_subtractions: 1,
        plaintext_ciphertext_subtractions: usize::from(unpaired_middle_root.is_some()),
        input_multiplicative_depth: input_depth,
        output_multiplicative_depth: paired_output_depth,
    };
    let certificate = PairedRootCertificate {
        maximum_residual: bound,
        root_pair_count,
        unpaired_middle_root,
        covered_root_count: 2 * root_pair_count + usize::from(unpaired_middle_root.is_some()),
        generic_ciphertext_multiplications,
        paired_ciphertext_multiplications,
        saved_ciphertext_multiplications,
        depth_preserved: paired_output_depth == generic_output_depth,
    };
    if certificate.covered_root_count != bound as usize || !certificate.depth_preserved {
        return Err(PairedRootZeroError::InternalCertificateFailure);
    }
    Ok((cost, certificate))
}

/// Transparent scalar evaluator for differential/falsifier tooling.
///
/// Its result must equal `product_(i=1..B) (i-r) mod modulus`; execution is
/// accepted only for `r <= B`, the domain certified by the residual compiler.
pub fn paired_root_indicator_mod(
    residual: u64,
    bound: u64,
    modulus: u64,
) -> Result<u64, PairedRootZeroError> {
    if modulus < 2 || residual > bound {
        return Err(PairedRootZeroError::ScalarDomainViolation {
            residual,
            bound,
            modulus,
        });
    }
    let _ = expected_parts(bound, 0)?;
    let modulus = u128::from(modulus);
    let r = u128::from(residual);
    let sum = u128::from(bound + 1);
    let u = (r * r + modulus - ((sum * r) % modulus)) % modulus;
    let mut result = 1u128;
    for i in 1..=bound / 2 {
        let constant = u128::from(i) * u128::from(bound + 1 - i);
        result = (result * ((u + constant) % modulus)) % modulus;
    }
    if bound % 2 == 1 {
        let middle = u128::from((bound + 1) / 2);
        result = (result * ((middle + modulus - r) % modulus)) % modulus;
    }
    Ok(result as u64)
}

impl PairedRootZeroEngine {
    pub fn new(
        relinearization_key: &RelinearizationKey,
        params: Arc<BfvParameters>,
    ) -> Result<Self, PairedRootZeroError> {
        let plaintext_modulus = params.plaintext();
        if plaintext_modulus != PAIRED_ROOT_PLAINTEXT_MODULUS {
            return Err(PairedRootZeroError::UnsupportedPlaintextModulus { plaintext_modulus });
        }
        let multiplicator = Multiplicator::default(relinearization_key)
            .map_err(|error| PairedRootZeroError::Bfv(error.to_string()))?;
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
    ) -> Result<PairedRootZeroPlan, PairedRootZeroError> {
        if live_slots == 0 {
            return Err(PairedRootZeroError::InvalidLiveSlots);
        }
        let maximum_residual = u64::try_from(compiled.certificate().maximum_residual_sum)
            .map_err(|_| PairedRootZeroError::ResidualBoundTooLarge)?;
        let (zero_conversion_cost, certificate) = expected_parts(
            maximum_residual,
            compiled.cost().maximum_multiplicative_depth,
        )?;
        let expected = residual_statement_digest(compiled, inputs, same_opening.opening_commitment);
        if same_opening.version != ZERO_OBSERVATION_VERSION
            || same_opening.statement_digest != expected
        {
            return Err(PairedRootZeroError::SameOpeningStatementMismatch);
        }
        Ok(PairedRootZeroPlan {
            manifest: PairedRootZeroManifest {
                version: PAIRED_ROOT_ZERO_VERSION,
                strategy: "exact complementary-root product with shared r^2-(B+1)r",
                plaintext_modulus: self.plaintext_modulus,
                live_slots,
                maximum_residual,
                true_scale: factorial_mod(maximum_residual, self.plaintext_modulus),
                residual_computation_cost: compiled.cost().clone(),
                zero_conversion_cost,
                certificate,
                same_opening,
                output: "encrypted scaled bit; B! exactly at residual zero and zero on 1..=B",
                leakage: "no residual or truth bit is opened by this conversion",
                trust_and_noise_boundary: vec![
                    "an external verifier must establish the exact same-opening receipt",
                    "the residual compiler must certify every live slot in 0..=B",
                    "the paired-root algebra and operation count do not constitute a BFV noise theorem",
                    "successful oracle execution is a measurement, not a general depth guarantee",
                ],
            },
        })
    }

    pub fn execute(
        &self,
        logic_engine: &BfvLogicEngine,
        compiled: &CompiledResidualEqualityPlan,
        inputs: &[DeclaredEncryptedNat],
        plan: &PairedRootZeroPlan,
    ) -> Result<PairedRootZeroExecution, PairedRootZeroError> {
        let expected_statement = residual_statement_digest(
            compiled,
            inputs,
            plan.manifest.same_opening.opening_commitment,
        );
        let (expected_cost, expected_certificate) = expected_parts(
            plan.manifest.maximum_residual,
            compiled.cost().maximum_multiplicative_depth,
        )?;
        if plan.manifest.version != PAIRED_ROOT_ZERO_VERSION
            || plan.manifest.plaintext_modulus != self.plaintext_modulus
            || expected_statement != plan.manifest.same_opening.statement_digest
            || compiled.cost() != &plan.manifest.residual_computation_cost
            || compiled.certificate().maximum_residual_sum
                != u128::from(plan.manifest.maximum_residual)
            || plan.manifest.zero_conversion_cost != expected_cost
            || plan.manifest.certificate != expected_certificate
            || plan.manifest.true_scale
                != factorial_mod(plan.manifest.maximum_residual, self.plaintext_modulus)
        {
            return Err(PairedRootZeroError::ManifestDrift);
        }

        let residual = logic_engine
            .execute_residual_equalities(compiled, inputs)
            .map_err(PairedRootZeroError::Logic)?;
        let started = Instant::now();
        let live_slots = plan.manifest.live_slots;
        let encode = |value: u64| {
            Plaintext::try_encode(&vec![value; live_slots], Encoding::simd(), &self.params)
                .map_err(|error| PairedRootZeroError::Bfv(error.to_string()))
        };

        let sum = encode(plan.manifest.maximum_residual + 1)?;
        let mut observed_cost = PairedRootCost {
            plaintext_constant_encodes: 1,
            ciphertext_multiplications: 1,
            relinearizations: 1,
            ciphertext_plaintext_multiplications: 1,
            ciphertext_plaintext_additions: 0,
            ciphertext_subtractions: 1,
            plaintext_ciphertext_subtractions: 0,
            input_multiplicative_depth: compiled.cost().maximum_multiplicative_depth,
            output_multiplicative_depth: expected_cost.output_multiplicative_depth,
        };
        let r_squared = self
            .multiplicator
            .multiply(&residual.ciphertext, &residual.ciphertext)
            .map_err(|error| PairedRootZeroError::Bfv(error.to_string()))?;
        let sum_r = &residual.ciphertext * &sum;
        let u = &r_squared - &sum_r;

        let mut factors = Vec::with_capacity(
            plan.manifest.certificate.root_pair_count
                + usize::from(plan.manifest.certificate.unpaired_middle_root.is_some()),
        );
        for i in 1..=plan.manifest.maximum_residual / 2 {
            let constant = (i * (plan.manifest.maximum_residual + 1 - i)) % self.plaintext_modulus;
            factors.push(&u + &encode(constant)?);
            observed_cost.plaintext_constant_encodes += 1;
            observed_cost.ciphertext_plaintext_additions += 1;
        }
        if let Some(middle) = plan.manifest.certificate.unpaired_middle_root {
            factors.push(&encode(middle)? - &residual.ciphertext);
            observed_cost.plaintext_constant_encodes += 1;
            observed_cost.plaintext_ciphertext_subtractions += 1;
        }

        let mut balanced_multiplications = 0usize;
        while factors.len() > 1 {
            let mut next = Vec::with_capacity(factors.len().div_ceil(2));
            let mut iter = factors.into_iter();
            while let Some(left) = iter.next() {
                if let Some(right) = iter.next() {
                    balanced_multiplications += 1;
                    next.push(
                        self.multiplicator
                            .multiply(&left, &right)
                            .map_err(|error| PairedRootZeroError::Bfv(error.to_string()))?,
                    );
                } else {
                    next.push(left);
                }
            }
            factors = next;
        }
        observed_cost.ciphertext_multiplications += balanced_multiplications;
        observed_cost.relinearizations += balanced_multiplications;
        if observed_cost != plan.manifest.zero_conversion_cost {
            return Err(PairedRootZeroError::ManifestDrift);
        }
        let output = factors
            .pop()
            .ok_or(PairedRootZeroError::InternalCertificateFailure)?;
        Ok(PairedRootZeroExecution {
            manifest: plan.manifest.clone(),
            output,
            residual_evaluation_elapsed: residual.elapsed,
            zero_conversion_elapsed: started.elapsed(),
        })
    }
}

#[derive(Debug)]
pub enum PairedRootZeroError {
    UnsupportedPlaintextModulus {
        plaintext_modulus: u64,
    },
    UnsupportedResidualBound {
        bound: u64,
    },
    NoStrictSaving {
        bound: u64,
    },
    InvalidLiveSlots,
    ResidualBoundTooLarge,
    SameOpeningStatementMismatch,
    ManifestDrift,
    InternalCertificateFailure,
    ScalarDomainViolation {
        residual: u64,
        bound: u64,
        modulus: u64,
    },
    Bfv(String),
    Logic(LogicBfvError),
}

impl fmt::Display for PairedRootZeroError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsupportedPlaintextModulus { plaintext_modulus } => write!(
                f,
                "paired-root zero supports plaintext modulus {PAIRED_ROOT_PLAINTEXT_MODULUS}, got {plaintext_modulus}"
            ),
            Self::UnsupportedResidualBound { bound } => write!(
                f,
                "paired-root optimization requires residual bound {PAIRED_ROOT_MIN_BOUND}..={PAIRED_ROOT_MAX_BOUND}, got {bound}"
            ),
            Self::NoStrictSaving { bound } => {
                write!(f, "paired-root schedule does not strictly improve bound {bound}")
            }
            Self::InvalidLiveSlots => f.write_str("paired-root zero requires a live SIMD slot"),
            Self::ResidualBoundTooLarge => {
                f.write_str("residual no-wrap bound does not fit the paired-root boundary")
            }
            Self::SameOpeningStatementMismatch => {
                f.write_str("same-opening receipt does not bind this paired-root statement")
            }
            Self::ManifestDrift => {
                f.write_str("paired-root execution drifted from its exact manifest")
            }
            Self::InternalCertificateFailure => {
                f.write_str("paired-root coverage/depth certificate failed internally")
            }
            Self::ScalarDomainViolation { residual, bound, modulus } => write!(
                f,
                "scalar paired-root evaluator requires modulus >= 2 and residual {residual} in 0..={bound}; modulus={modulus}"
            ),
            Self::Bfv(error) => write!(f, "paired-root BFV operation failed: {error}"),
            Self::Logic(error) => write!(f, "paired-root residual failed: {error}"),
        }
    }
}

impl std::error::Error for PairedRootZeroError {}
