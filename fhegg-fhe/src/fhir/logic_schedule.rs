//! Executable BFV backends for the finite logic schedule.
//!
//! This module is a deliberately small fhIR sibling to the convex-product
//! grammar.  It realizes two useful fragments of
//! `Dregg2.Logic.FheLogicSchedule` with the deployed `fhe.rs` BFV carrier:
//!
//! * [`BooleanProgram`] evaluates canonical encrypted bits with the exact
//!   arithmetic identities
//!   `not x = 1-x`, `x and y = xy`, `x or y = x+y-xy`, and
//!   `x == y = 1-x-y+2xy`;
//! * [`ResidualEqualityPlan`] evaluates a conjunction of equalities as the
//!   nonnegative residual `sum_i (x_i-y_i)^2`.  A checked centered-plaintext
//!   certificate makes finite-field cancellation impossible: the largest
//!   possible sum is strictly below the centered BFV window.
//!
//! Both paths execute real ciphertext additions/subtractions and real BFV
//! ciphertext-by-ciphertext multiplication with relinearization.  Their
//! [`BfvCostManifest`] values count exactly the primitive calls made by this
//! interpreter.  They are symbolic instruction counts, not latency, noise, or
//! security theorems.  In particular:
//!
//! * callers must bind every declared bit/bound to the encrypted plaintext
//!   (for example with a range/same-opening proof);
//! * all ciphertexts and the relinearization key must use the same parameters
//!   and key epoch;
//! * `maximum_multiplicative_depth` is reported but not admitted against a
//!   proved BFV noise budget;
//! * the residual path intentionally stops before the final secret zero test.
//!   Threshold opening-to-shares plus PartyMPC equality is the existing fhEgg
//!   boundary for that decision.
//!
//! The Rust implementation is oracle-tested by decrypting concrete workloads.
//! It is not itself a Rust-to-Lean refinement proof.

use std::fmt;
use std::sync::Arc;
use std::time::{Duration, Instant};

use fhe::bfv::{BfvParameters, Ciphertext, Multiplicator, RelinearizationKey};
use serde::Serialize;

/// Version of the machine-readable operation and certificate manifests.
pub const BFV_LOGIC_MANIFEST_VERSION: u32 = 1;

/// Exact primitive-call ledger for this interpreter.
///
/// Encryption, decryption, key generation, parameter setup, and the residual
/// zero decision are deliberately outside the ledger.  No field is a runtime
/// or noise estimate.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct BfvCostManifest {
    pub logical_input_reads: usize,
    pub encrypted_constant_reads: usize,
    pub ciphertext_additions: usize,
    pub ciphertext_subtractions: usize,
    pub ciphertext_multiplications: usize,
    pub relinearizations: usize,
    pub maximum_multiplicative_depth: usize,
    pub boundary_zero_decisions: usize,
}

impl BfvCostManifest {
    fn merge(&mut self, rhs: &Self) {
        self.logical_input_reads += rhs.logical_input_reads;
        self.encrypted_constant_reads += rhs.encrypted_constant_reads;
        self.ciphertext_additions += rhs.ciphertext_additions;
        self.ciphertext_subtractions += rhs.ciphertext_subtractions;
        self.ciphertext_multiplications += rhs.ciphertext_multiplications;
        self.relinearizations += rhs.relinearizations;
        self.maximum_multiplicative_depth = self
            .maximum_multiplicative_depth
            .max(rhs.maximum_multiplicative_depth);
        self.boundary_zero_decisions += rhs.boundary_zero_decisions;
    }
}

/// Backend contract emitted beside a compiled plan.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct BfvLogicManifest {
    pub version: u32,
    pub carrier: &'static str,
    pub workload: &'static str,
    pub plaintext_modulus: u64,
    pub centered_window: u64,
    pub cost: BfvCostManifest,
    pub final_decision: &'static str,
    pub assumptions: Vec<&'static str>,
}

impl BfvLogicManifest {
    /// Deterministic JSON field order follows the structure declaration.
    pub fn canonical_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }
}

/// Boolean-valued terms accepted by the first executable backend.
///
/// `Input(i)` corresponds to a Boolean-valued source variable.  `Eq` is the
/// bit-valued specialization of `FiniteLogicPlan.Term` equality.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BooleanProgram {
    Constant(bool),
    Input(usize),
    Eq(Box<BooleanProgram>, Box<BooleanProgram>),
    Not(Box<BooleanProgram>),
    And(Box<BooleanProgram>, Box<BooleanProgram>),
    Or(Box<BooleanProgram>, Box<BooleanProgram>),
}

impl BooleanProgram {
    /// Transparent source semantics used by the differential tests.
    pub fn evaluate_plain(&self, inputs: &[bool]) -> Result<bool, LogicBfvError> {
        match self {
            Self::Constant(value) => Ok(*value),
            Self::Input(index) => {
                inputs
                    .get(*index)
                    .copied()
                    .ok_or(LogicBfvError::InputOutOfRange {
                        index: *index,
                        available: inputs.len(),
                    })
            }
            Self::Eq(left, right) => {
                Ok(left.evaluate_plain(inputs)? == right.evaluate_plain(inputs)?)
            }
            Self::Not(input) => Ok(!input.evaluate_plain(inputs)?),
            Self::And(left, right) => {
                Ok(left.evaluate_plain(inputs)? && right.evaluate_plain(inputs)?)
            }
            Self::Or(left, right) => {
                Ok(left.evaluate_plain(inputs)? || right.evaluate_plain(inputs)?)
            }
        }
    }

    fn profile(&self) -> Profile {
        match self {
            Self::Constant(_) => Profile {
                cost: BfvCostManifest {
                    encrypted_constant_reads: 1,
                    ..BfvCostManifest::default()
                },
                depth: 0,
            },
            Self::Input(_) => Profile {
                cost: BfvCostManifest {
                    logical_input_reads: 1,
                    ..BfvCostManifest::default()
                },
                depth: 0,
            },
            Self::Not(input) => {
                let mut profile = input.profile();
                profile.cost.encrypted_constant_reads += 1;
                profile.cost.ciphertext_subtractions += 1;
                profile
            }
            Self::And(left, right) => Profile::binary(left.profile(), right.profile(), 0, 0, 1),
            Self::Or(left, right) => Profile::binary(left.profile(), right.profile(), 1, 1, 1),
            Self::Eq(left, right) => {
                let mut profile = Profile::binary(left.profile(), right.profile(), 2, 2, 1);
                profile.cost.encrypted_constant_reads += 1;
                profile
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Profile {
    cost: BfvCostManifest,
    depth: usize,
}

impl Profile {
    fn binary(
        left: Self,
        right: Self,
        additions: usize,
        subtractions: usize,
        multiplications: usize,
    ) -> Self {
        let input_depth = left.depth.max(right.depth);
        let mut cost = left.cost;
        cost.merge(&right.cost);
        cost.ciphertext_additions += additions;
        cost.ciphertext_subtractions += subtractions;
        cost.ciphertext_multiplications += multiplications;
        cost.relinearizations += multiplications;
        let depth = input_depth + usize::from(multiplications != 0);
        cost.maximum_multiplicative_depth = cost.maximum_multiplicative_depth.max(depth);
        Self { cost, depth }
    }
}

/// A program paired with the exact static operation ledger used at execution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompiledBooleanProgram {
    program: BooleanProgram,
    cost: BfvCostManifest,
}

impl CompiledBooleanProgram {
    pub fn program(&self) -> &BooleanProgram {
        &self.program
    }

    pub fn cost(&self) -> &BfvCostManifest {
        &self.cost
    }
}

/// Compile the Boolean fragment.  This is structural and cannot silently
/// select a LUT, rotation, or high-fan-in primitive.
pub fn compile_boolean(program: BooleanProgram) -> CompiledBooleanProgram {
    let cost = program.profile().cost;
    CompiledBooleanProgram { program, cost }
}

/// Ciphertext declared to encrypt a canonical bit.
///
/// The declaration is an ingress obligation, not a check that can be recovered
/// from a BFV ciphertext.  The constructor name is intentionally explicit.
#[derive(Clone, Debug)]
pub struct DeclaredEncryptedBit {
    ciphertext: Ciphertext,
    multiplicative_depth: usize,
}

impl DeclaredEncryptedBit {
    pub fn from_declared_canonical(ciphertext: Ciphertext) -> Self {
        Self {
            ciphertext,
            multiplicative_depth: 0,
        }
    }

    pub fn ciphertext(&self) -> &Ciphertext {
        &self.ciphertext
    }

    pub fn multiplicative_depth(&self) -> usize {
        self.multiplicative_depth
    }
}

/// Encrypted constants required by the Boolean arithmetic identities.
#[derive(Clone, Debug)]
pub struct BooleanConstants {
    zero: DeclaredEncryptedBit,
    one: DeclaredEncryptedBit,
}

impl BooleanConstants {
    /// `zero` and `one` must encrypt those canonical values under the same BFV
    /// key and parameters as every input.
    pub fn from_declared_constants(zero: Ciphertext, one: Ciphertext) -> Self {
        Self {
            zero: DeclaredEncryptedBit::from_declared_canonical(zero),
            one: DeclaredEncryptedBit::from_declared_canonical(one),
        }
    }
}

/// One measured execution.  `elapsed` is wall-clock observation for this run;
/// the exact cost ledger remains separate.
#[derive(Debug)]
pub struct BooleanExecution {
    pub output: DeclaredEncryptedBit,
    pub observed_cost: BfvCostManifest,
    pub elapsed: Duration,
}

/// Variable terms for the corrected additive equality-residual fragment.
#[derive(Clone, Debug)]
pub struct DeclaredEncryptedNat {
    ciphertext: Ciphertext,
    declared_upper_bound: u64,
}

impl DeclaredEncryptedNat {
    /// The plaintext is declared to be in `0..=declared_upper_bound`.
    pub fn from_declared_bound(ciphertext: Ciphertext, declared_upper_bound: u64) -> Self {
        Self {
            ciphertext,
            declared_upper_bound,
        }
    }

    pub fn ciphertext(&self) -> &Ciphertext {
        &self.ciphertext
    }

    pub fn declared_upper_bound(&self) -> u64 {
        self.declared_upper_bound
    }
}

/// `all_i inputs[lhs_i] == inputs[rhs_i]`, lowered to one nonnegative sum.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResidualEqualityPlan {
    pub pairs: Vec<(usize, usize)>,
    pub input_bound: u64,
}

impl ResidualEqualityPlan {
    pub fn evaluate_plain(&self, inputs: &[u64]) -> Result<u128, LogicBfvError> {
        let mut sum = 0u128;
        for &(lhs_index, rhs_index) in &self.pairs {
            let lhs = *inputs
                .get(lhs_index)
                .ok_or(LogicBfvError::InputOutOfRange {
                    index: lhs_index,
                    available: inputs.len(),
                })?;
            let rhs = *inputs
                .get(rhs_index)
                .ok_or(LogicBfvError::InputOutOfRange {
                    index: rhs_index,
                    available: inputs.len(),
                })?;
            if lhs > self.input_bound {
                return Err(LogicBfvError::PlainInputBoundExceeded {
                    index: lhs_index,
                    value: lhs,
                    admitted: self.input_bound,
                });
            }
            if rhs > self.input_bound {
                return Err(LogicBfvError::PlainInputBoundExceeded {
                    index: rhs_index,
                    value: rhs,
                    admitted: self.input_bound,
                });
            }
            let distance = u128::from(lhs.abs_diff(rhs));
            sum = sum
                .checked_add(distance * distance)
                .ok_or(LogicBfvError::BoundArithmeticOverflow)?;
        }
        Ok(sum)
    }

    pub fn evaluate_plain_truth(&self, inputs: &[u64]) -> Result<bool, LogicBfvError> {
        Ok(self.evaluate_plain(inputs)? == 0)
    }
}

/// Exact public range certificate for the residual program.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ResidualNoWrapCertificate {
    pub plaintext_modulus: u64,
    pub centered_window: u64,
    pub pair_count: usize,
    pub input_bound: u64,
    pub maximum_single_residual: u128,
    pub maximum_residual_sum: u128,
}

/// A checked residual plan.  Construction fails unless every possible sum is
/// a nonnegative integer strictly inside the centered plaintext window.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompiledResidualEqualityPlan {
    plan: ResidualEqualityPlan,
    cost: BfvCostManifest,
    certificate: ResidualNoWrapCertificate,
}

impl CompiledResidualEqualityPlan {
    pub fn plan(&self) -> &ResidualEqualityPlan {
        &self.plan
    }

    pub fn cost(&self) -> &BfvCostManifest {
        &self.cost
    }

    pub fn certificate(&self) -> &ResidualNoWrapCertificate {
        &self.certificate
    }
}

/// Encrypted residual.  Observing truth still requires an external zero
/// decision; decrypting directly is only an oracle/testing action.
#[derive(Debug)]
pub struct ResidualExecution {
    pub ciphertext: Ciphertext,
    pub maximum_residual: u128,
    pub observed_cost: BfvCostManifest,
    pub elapsed: Duration,
}

/// Real `fhe.rs` BFV execution engine for both fragments.
pub struct BfvLogicEngine {
    params: Arc<BfvParameters>,
    multiplicator: Multiplicator,
    plaintext_modulus: u64,
    centered_window: u64,
}

impl BfvLogicEngine {
    pub fn new(
        relinearization_key: &RelinearizationKey,
        params: Arc<BfvParameters>,
    ) -> Result<Self, LogicBfvError> {
        let plaintext_modulus = params.plaintext();
        if plaintext_modulus <= 2 {
            return Err(LogicBfvError::PlaintextModulusTooSmall { plaintext_modulus });
        }
        let multiplicator = Multiplicator::default(relinearization_key)
            .map_err(|error| LogicBfvError::Bfv(error.to_string()))?;
        Ok(Self {
            params,
            multiplicator,
            plaintext_modulus,
            centered_window: (plaintext_modulus - 1) / 2,
        })
    }

    pub fn plaintext_modulus(&self) -> u64 {
        self.plaintext_modulus
    }

    pub fn centered_window(&self) -> u64 {
        self.centered_window
    }

    pub fn boolean_manifest(&self, compiled: &CompiledBooleanProgram) -> BfvLogicManifest {
        BfvLogicManifest {
            version: BFV_LOGIC_MANIFEST_VERSION,
            carrier: "fhe.rs/BFV exact modular SIMD",
            workload: "canonical encrypted Boolean formula",
            plaintext_modulus: self.plaintext_modulus,
            centered_window: self.centered_window,
            cost: compiled.cost.clone(),
            final_decision: "encrypted canonical bit (no opening included)",
            assumptions: vec![
                "inputs and constants encrypt canonical bits under one parameter/key epoch",
                "the relinearization key matches every input ciphertext",
                "input declarations are bound by an external range/same-opening authority",
                "multiplicative depth is symbolic here; no BFV noise theorem is claimed",
            ],
        }
    }

    /// Execute a structurally compiled Boolean program with real BFV
    /// arithmetic, checking that the dynamic primitive ledger equals the
    /// compiler's static ledger.
    pub fn execute_boolean(
        &self,
        compiled: &CompiledBooleanProgram,
        inputs: &[DeclaredEncryptedBit],
        constants: &BooleanConstants,
    ) -> Result<BooleanExecution, LogicBfvError> {
        let started = Instant::now();
        let mut observed_cost = BfvCostManifest::default();
        let output =
            self.eval_boolean(compiled.program(), inputs, constants, &mut observed_cost)?;
        let elapsed = started.elapsed();
        if observed_cost != compiled.cost {
            return Err(LogicBfvError::ManifestDrift {
                expected: compiled.cost.clone(),
                observed: observed_cost,
            });
        }
        Ok(BooleanExecution {
            output,
            observed_cost: compiled.cost.clone(),
            elapsed,
        })
    }

    fn eval_boolean(
        &self,
        program: &BooleanProgram,
        inputs: &[DeclaredEncryptedBit],
        constants: &BooleanConstants,
        cost: &mut BfvCostManifest,
    ) -> Result<DeclaredEncryptedBit, LogicBfvError> {
        match program {
            BooleanProgram::Constant(value) => {
                cost.encrypted_constant_reads += 1;
                Ok(if *value {
                    constants.one.clone()
                } else {
                    constants.zero.clone()
                })
            }
            BooleanProgram::Input(index) => {
                cost.logical_input_reads += 1;
                inputs
                    .get(*index)
                    .cloned()
                    .ok_or(LogicBfvError::InputOutOfRange {
                        index: *index,
                        available: inputs.len(),
                    })
            }
            BooleanProgram::Not(input) => {
                let input = self.eval_boolean(input, inputs, constants, cost)?;
                cost.encrypted_constant_reads += 1;
                cost.ciphertext_subtractions += 1;
                Ok(DeclaredEncryptedBit {
                    ciphertext: &constants.one.ciphertext - &input.ciphertext,
                    multiplicative_depth: input.multiplicative_depth,
                })
            }
            BooleanProgram::And(left, right) => {
                let left = self.eval_boolean(left, inputs, constants, cost)?;
                let right = self.eval_boolean(right, inputs, constants, cost)?;
                self.multiply_bits(left, right, cost)
            }
            BooleanProgram::Or(left, right) => {
                let left = self.eval_boolean(left, inputs, constants, cost)?;
                let right = self.eval_boolean(right, inputs, constants, cost)?;
                cost.ciphertext_additions += 1;
                let sum = &left.ciphertext + &right.ciphertext;
                let product = self.multiply_bits(left, right, cost)?;
                cost.ciphertext_subtractions += 1;
                Ok(DeclaredEncryptedBit {
                    ciphertext: &sum - &product.ciphertext,
                    multiplicative_depth: product.multiplicative_depth,
                })
            }
            BooleanProgram::Eq(left, right) => {
                let left = self.eval_boolean(left, inputs, constants, cost)?;
                let right = self.eval_boolean(right, inputs, constants, cost)?;
                let product = self.multiply_bits(left.clone(), right.clone(), cost)?;
                cost.ciphertext_additions += 1;
                let doubled_product = &product.ciphertext + &product.ciphertext;
                cost.encrypted_constant_reads += 1;
                cost.ciphertext_subtractions += 1;
                let one_minus_left = &constants.one.ciphertext - &left.ciphertext;
                cost.ciphertext_subtractions += 1;
                let one_minus_both = &one_minus_left - &right.ciphertext;
                cost.ciphertext_additions += 1;
                Ok(DeclaredEncryptedBit {
                    ciphertext: &one_minus_both + &doubled_product,
                    multiplicative_depth: product.multiplicative_depth,
                })
            }
        }
    }

    fn multiply_bits(
        &self,
        left: DeclaredEncryptedBit,
        right: DeclaredEncryptedBit,
        cost: &mut BfvCostManifest,
    ) -> Result<DeclaredEncryptedBit, LogicBfvError> {
        cost.ciphertext_multiplications += 1;
        cost.relinearizations += 1;
        let multiplicative_depth = left.multiplicative_depth.max(right.multiplicative_depth) + 1;
        cost.maximum_multiplicative_depth =
            cost.maximum_multiplicative_depth.max(multiplicative_depth);
        let ciphertext = self
            .multiplicator
            .multiply(&left.ciphertext, &right.ciphertext)
            .map_err(|error| LogicBfvError::Bfv(error.to_string()))?;
        Ok(DeclaredEncryptedBit {
            ciphertext,
            multiplicative_depth,
        })
    }

    /// Check the positive/no-wrap certificate and produce an executable plan.
    pub fn compile_residual_equalities(
        &self,
        plan: ResidualEqualityPlan,
    ) -> Result<CompiledResidualEqualityPlan, LogicBfvError> {
        let maximum_single_residual = u128::from(plan.input_bound)
            .checked_mul(u128::from(plan.input_bound))
            .ok_or(LogicBfvError::BoundArithmeticOverflow)?;
        let maximum_residual_sum = maximum_single_residual
            .checked_mul(plan.pairs.len() as u128)
            .ok_or(LogicBfvError::BoundArithmeticOverflow)?;
        if maximum_residual_sum >= u128::from(self.centered_window) {
            return Err(LogicBfvError::ResidualNoWrapRefused {
                maximum_residual_sum,
                centered_window: self.centered_window,
            });
        }
        let pair_count = plan.pairs.len();
        let cost = BfvCostManifest {
            logical_input_reads: 2 * pair_count,
            ciphertext_additions: pair_count.saturating_sub(1),
            ciphertext_subtractions: pair_count,
            ciphertext_multiplications: pair_count,
            relinearizations: pair_count,
            maximum_multiplicative_depth: usize::from(pair_count != 0),
            // One is REQUIRED at the boundary but deliberately not executed here.
            boundary_zero_decisions: 0,
            ..BfvCostManifest::default()
        };
        let certificate = ResidualNoWrapCertificate {
            plaintext_modulus: self.plaintext_modulus,
            centered_window: self.centered_window,
            pair_count,
            input_bound: plan.input_bound,
            maximum_single_residual,
            maximum_residual_sum,
        };
        Ok(CompiledResidualEqualityPlan {
            plan,
            cost,
            certificate,
        })
    }

    pub fn residual_manifest(&self, compiled: &CompiledResidualEqualityPlan) -> BfvLogicManifest {
        BfvLogicManifest {
            version: BFV_LOGIC_MANIFEST_VERSION,
            carrier: "fhe.rs/BFV exact centered-integer SIMD",
            workload: "bounded conjunction of encrypted natural equalities",
            plaintext_modulus: self.plaintext_modulus,
            centered_window: self.centered_window,
            cost: compiled.cost.clone(),
            final_decision: "encrypted nonnegative residual; external zero decision required",
            assumptions: vec![
                "every plaintext is in its declared public natural-number bound",
                "the relinearization key matches every input ciphertext",
                "the checked residual sum remains strictly inside the centered plaintext window",
                "input declarations are bound by an external range/same-opening authority",
                "the final equality-to-zero decision is not part of this BFV execution",
                "depth one is symbolic here; no BFV noise theorem is claimed",
            ],
        }
    }

    /// Execute the corrected additive equality-residual lowering.  Every
    /// equality uses one subtraction and one squaring; all squares are added.
    pub fn execute_residual_equalities(
        &self,
        compiled: &CompiledResidualEqualityPlan,
        inputs: &[DeclaredEncryptedNat],
    ) -> Result<ResidualExecution, LogicBfvError> {
        let started = Instant::now();
        let mut observed_cost = BfvCostManifest::default();
        let mut residuals = Vec::with_capacity(compiled.plan.pairs.len());
        for &(lhs_index, rhs_index) in &compiled.plan.pairs {
            let lhs = inputs
                .get(lhs_index)
                .ok_or(LogicBfvError::InputOutOfRange {
                    index: lhs_index,
                    available: inputs.len(),
                })?;
            let rhs = inputs
                .get(rhs_index)
                .ok_or(LogicBfvError::InputOutOfRange {
                    index: rhs_index,
                    available: inputs.len(),
                })?;
            observed_cost.logical_input_reads += 2;
            if lhs.declared_upper_bound > compiled.plan.input_bound {
                return Err(LogicBfvError::EncryptedInputBoundExceeded {
                    index: lhs_index,
                    declared: lhs.declared_upper_bound,
                    admitted: compiled.plan.input_bound,
                });
            }
            if rhs.declared_upper_bound > compiled.plan.input_bound {
                return Err(LogicBfvError::EncryptedInputBoundExceeded {
                    index: rhs_index,
                    declared: rhs.declared_upper_bound,
                    admitted: compiled.plan.input_bound,
                });
            }
            observed_cost.ciphertext_subtractions += 1;
            let difference = &lhs.ciphertext - &rhs.ciphertext;
            observed_cost.ciphertext_multiplications += 1;
            observed_cost.relinearizations += 1;
            observed_cost.maximum_multiplicative_depth = 1;
            let square = self
                .multiplicator
                .multiply(&difference, &difference)
                .map_err(|error| LogicBfvError::Bfv(error.to_string()))?;
            residuals.push(square);
        }

        let ciphertext = if residuals.is_empty() {
            Ciphertext::zero(&self.params)
        } else {
            let mut iter = residuals.into_iter();
            let mut sum = iter.next().expect("nonempty by branch");
            for residual in iter {
                observed_cost.ciphertext_additions += 1;
                sum += &residual;
            }
            sum
        };
        let elapsed = started.elapsed();
        if observed_cost != compiled.cost {
            return Err(LogicBfvError::ManifestDrift {
                expected: compiled.cost.clone(),
                observed: observed_cost,
            });
        }
        Ok(ResidualExecution {
            ciphertext,
            maximum_residual: compiled.certificate.maximum_residual_sum,
            observed_cost: compiled.cost.clone(),
            elapsed,
        })
    }
}

#[derive(Debug)]
pub enum LogicBfvError {
    PlaintextModulusTooSmall {
        plaintext_modulus: u64,
    },
    InputOutOfRange {
        index: usize,
        available: usize,
    },
    PlainInputBoundExceeded {
        index: usize,
        value: u64,
        admitted: u64,
    },
    EncryptedInputBoundExceeded {
        index: usize,
        declared: u64,
        admitted: u64,
    },
    BoundArithmeticOverflow,
    ResidualNoWrapRefused {
        maximum_residual_sum: u128,
        centered_window: u64,
    },
    ManifestDrift {
        expected: BfvCostManifest,
        observed: BfvCostManifest,
    },
    Bfv(String),
}

impl fmt::Display for LogicBfvError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::PlaintextModulusTooSmall { plaintext_modulus } => write!(
                f,
                "BFV plaintext modulus {plaintext_modulus} cannot carry canonical Boolean arithmetic"
            ),
            Self::InputOutOfRange { index, available } => {
                write!(
                    f,
                    "logic input {index} is outside the {available}-input environment"
                )
            }
            Self::PlainInputBoundExceeded {
                index,
                value,
                admitted,
            } => write!(
                f,
                "plain logic input {index} value {value} exceeds admitted bound {admitted}"
            ),
            Self::EncryptedInputBoundExceeded {
                index,
                declared,
                admitted,
            } => write!(
                f,
                "encrypted logic input {index} declares bound {declared}, above admitted {admitted}"
            ),
            Self::BoundArithmeticOverflow => f.write_str("logic bound arithmetic overflow"),
            Self::ResidualNoWrapRefused {
                maximum_residual_sum,
                centered_window,
            } => write!(
                f,
                "residual no-wrap refused: maximum sum {maximum_residual_sum} is not below centered BFV window {centered_window}"
            ),
            Self::ManifestDrift { expected, observed } => write!(
                f,
                "BFV logic operation manifest drift: expected {expected:?}, observed {observed:?}"
            ),
            Self::Bfv(error) => write!(f, "fhe.rs BFV operation failed: {error}"),
        }
    }
}

impl std::error::Error for LogicBfvError {}
