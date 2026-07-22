//! Explicit zero-observation boundary for corrected BFV logic residuals.
//!
//! `logic_schedule` intentionally ends with an encrypted, nonnegative
//! residual.  This module supplies the strongest boundary currently executable
//! in fhEgg without pretending that ordinary BFV arithmetic has a free exact
//! zero-test.  There are two explicit strategies:
//!
//! * an encrypted bounded-domain scaled indicator
//!   `product_(i=1..B) (i-r)`, enabled by the residual no-wrap bound; and
//! * an n-of-n, Lean-pinned, smudged threshold opening of the residual.
//!
//! The bounded product is `B!` when the residual is zero and zero at every
//! other certified residual.  Normalizing it to a canonical one requires a
//! large modular inverse; that normalization exhausted the deployed noise
//! envelope in oracle tests, so the API does not hide it.  A final threshold
//! observation can compare the two scaled values while revealing only truth.
//! An internal hybrid continuation remains unsupported.
//!
//! The boundary is deliberately expensive and deliberately leaky:
//!
//! * every party emits one public decryption-share message;
//! * the coordinator performs one threshold combine;
//! * every live SIMD residual is revealed in full and compared with zero;
//! * an internal residual-to-bit conversion would additionally reveal an
//!   internal subformula and require re-encryption before encrypted evaluation
//!   can continue.  That continuation is priced but refused here because the
//!   current Rust executor has no hybrid continuation machine.
//!
//! A [`SameOpeningReceipt`] binds an external opening commitment and verifier
//! receipt to the exact residual plan and exact input ciphertext bytes.  This
//! module checks that binding, but it does **not** implement the external
//! same-opening proof verifier.  That trust boundary is represented in both the
//! types and the manifest instead of being smuggled into a performance claim.
//!
//! The returned coverage marks only encrypted evaluation and zero observation
//! as measured.  Key setup, input encryption, and external same-opening proof
//! verification are outside the timed function, so [`PhaseCoverage::complete`]
//! is false and this receipt cannot be labelled an end-to-end benchmark.

use std::fmt;
use std::time::{Duration, Instant};

use fhe::bfv::{BfvParameters, Ciphertext, Encoding, Multiplicator, Plaintext, RelinearizationKey};
use fhe_traits::{FheEncoder, Serialize as FheSerialize};
use serde::Serialize;
use sha2::{Digest, Sha256};

use crate::bfv_lean::LeanCiphertext;
use crate::threshold::{combine, BfvParams, ThresholdError, ThresholdParty, MIN_SMUDGE_BITS};

use super::logic_schedule::{
    BfvCostManifest, BfvLogicEngine, CompiledResidualEqualityPlan, DeclaredEncryptedNat,
    LogicBfvError,
};

/// Canonical statement/receipt format version.
pub const ZERO_OBSERVATION_VERSION: u32 = 1;

const STATEMENT_DOMAIN: &[u8] = b"dregg/fhir/residual-zero-observation-statement/v1";

/// Receipt emitted by an external same-opening verifier.
///
/// The external verifier must establish that the ciphertexts committed by
/// `statement_digest` encrypt the opening committed by `opening_commitment`.
/// This module checks exact statement binding and refuses zero/empty receipt
/// fields, but cannot derive that semantic fact from BFV ciphertext bytes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SameOpeningReceipt {
    pub version: u32,
    pub statement_digest: [u8; 32],
    pub opening_commitment: [u8; 32],
    pub verifier_receipt_digest: [u8; 32],
    pub verifier_id: String,
}

impl SameOpeningReceipt {
    /// Construct a receipt after an external verifier has accepted the exact
    /// statement digest returned by [`residual_statement_digest`].
    pub fn from_external_verifier(
        statement_digest: [u8; 32],
        opening_commitment: [u8; 32],
        verifier_receipt_digest: [u8; 32],
        verifier_id: impl Into<String>,
    ) -> Result<Self, ZeroObservationError> {
        let verifier_id = verifier_id.into();
        if statement_digest == [0; 32]
            || opening_commitment == [0; 32]
            || verifier_receipt_digest == [0; 32]
            || verifier_id.is_empty()
        {
            return Err(ZeroObservationError::MalformedSameOpeningReceipt);
        }
        Ok(Self {
            version: ZERO_OBSERVATION_VERSION,
            statement_digest,
            opening_commitment,
            verifier_receipt_digest,
            verifier_id,
        })
    }
}

/// Exact symbolic price of one threshold-opened residual ciphertext.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ThresholdBoundaryCost {
    pub decryption_share_messages: usize,
    pub threshold_combines: usize,
    pub opened_residual_slots: usize,
    pub clear_zero_comparisons: usize,
    pub ciphertext_reencryptions: usize,
}

/// Which phases are represented by measured execution in a receipt.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct PhaseCoverage {
    pub key_setup_measured: bool,
    pub input_encryption_measured: bool,
    pub same_opening_verification_measured: bool,
    pub encrypted_evaluation_measured: bool,
    pub every_zero_observation_measured: bool,
    pub output_observation_measured: bool,
}

impl PhaseCoverage {
    /// The fail-closed gate for the phrase "end-to-end".
    pub fn complete(&self) -> bool {
        self.key_setup_measured
            && self.input_encryption_measured
            && self.same_opening_verification_measured
            && self.encrypted_evaluation_measured
            && self.every_zero_observation_measured
            && self.output_observation_measured
    }
}

/// Machine-readable boundary statement emitted before execution.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ThresholdZeroObservationManifest {
    pub version: u32,
    pub strategy: &'static str,
    pub plaintext_modulus: u64,
    pub party_count: usize,
    pub smudge_bits: u32,
    pub live_slots: usize,
    pub continuation_required: bool,
    pub encrypted_computation_cost: BfvCostManifest,
    pub boundary_cost: ThresholdBoundaryCost,
    pub maximum_residual: u128,
    pub same_opening: SameOpeningReceipt,
    pub leakage: &'static str,
    pub trust_and_noise_boundary: Vec<&'static str>,
}

impl ThresholdZeroObservationManifest {
    pub fn canonical_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }
}

/// A checked request to open one residual ciphertext.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ThresholdZeroObservationPlan {
    manifest: ThresholdZeroObservationManifest,
}

impl ThresholdZeroObservationPlan {
    pub fn manifest(&self) -> &ThresholdZeroObservationManifest {
        &self.manifest
    }
}

/// Concrete measured receipt.  The residual values are present because they
/// really are the values revealed to the coordinator.
#[derive(Debug, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ThresholdZeroObservationExecution {
    pub manifest: ThresholdZeroObservationManifest,
    pub residual_ciphertext_digest: [u8; 32],
    pub opened_residuals: Vec<u64>,
    pub truth_bits: Vec<bool>,
    pub encrypted_evaluation_elapsed_ns: u128,
    pub threshold_observation_elapsed_ns: u128,
    pub decryption_share_wire_bytes: usize,
    pub coverage: PhaseCoverage,
}

/// Primitive-call ledger for the exact bounded-domain encrypted zero test
///
/// `product_{i=1..B} (i-r)` is `B!` at `r=0` and zero at every certified
/// residual `r in 1..=B`.  Plaintext operations are listed explicitly rather
/// than being conflated with ciphertext-by-ciphertext multiplication.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct BoundedEncryptedZeroCost {
    pub plaintext_constant_encodes: usize,
    pub ciphertext_plaintext_subtractions: usize,
    pub ciphertext_multiplications: usize,
    pub relinearizations: usize,
    pub ciphertext_plaintext_multiplications: usize,
    pub input_multiplicative_depth: usize,
    pub output_multiplicative_depth: usize,
}

/// Checked statement for an exact encrypted zero conversion on a finite
/// no-wrap interval.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct BoundedEncryptedZeroManifest {
    pub version: u32,
    pub strategy: &'static str,
    pub plaintext_modulus: u64,
    pub live_slots: usize,
    pub maximum_residual: u64,
    pub true_scale: u64,
    pub residual_computation_cost: BfvCostManifest,
    pub zero_conversion_cost: BoundedEncryptedZeroCost,
    pub same_opening: SameOpeningReceipt,
    pub output: &'static str,
    pub leakage: &'static str,
    pub trust_and_noise_boundary: Vec<&'static str>,
}

/// Executable bounded-domain zero-test plan.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoundedEncryptedZeroPlan {
    manifest: BoundedEncryptedZeroManifest,
}

impl BoundedEncryptedZeroPlan {
    pub fn manifest(&self) -> &BoundedEncryptedZeroManifest {
        &self.manifest
    }
}

/// Encrypted scaled-bit output of the real bounded zero test.
#[derive(Debug)]
pub struct BoundedEncryptedZeroExecution {
    pub manifest: BoundedEncryptedZeroManifest,
    pub output: Ciphertext,
    pub residual_evaluation_elapsed: Duration,
    pub zero_conversion_elapsed: Duration,
}

/// Threshold observation of an already-encrypted canonical result bit.
#[derive(Debug, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ThresholdBitObservation {
    pub opened_bits: Vec<bool>,
    pub elapsed_ns: u128,
    pub decryption_share_messages: usize,
    pub decryption_share_wire_bytes: usize,
    pub threshold_combines: usize,
    pub leakage: &'static str,
    pub noise_boundary: &'static str,
}

/// Real BFV multiplication engine for the finite-domain product zero test.
pub struct BoundedEncryptedZeroEngine {
    params: std::sync::Arc<BfvParameters>,
    multiplicator: Multiplicator,
    plaintext_modulus: u64,
}

impl BoundedEncryptedZeroEngine {
    pub fn new(
        relinearization_key: &RelinearizationKey,
        params: std::sync::Arc<BfvParameters>,
    ) -> Result<Self, ZeroObservationError> {
        let plaintext_modulus = params.plaintext();
        if plaintext_modulus != 1_032_193 {
            return Err(ZeroObservationError::UnsupportedBoundedZeroField { plaintext_modulus });
        }
        let multiplicator = Multiplicator::default(relinearization_key)
            .map_err(|error| ZeroObservationError::Bfv(error.to_string()))?;
        Ok(Self {
            params,
            multiplicator,
            plaintext_modulus,
        })
    }

    /// Compile the product indicator.  This implementation deliberately caps
    /// the interval to keep manifest construction and execution bounded; a
    /// larger interval should select threshold opening or a different carrier.
    pub fn compile(
        &self,
        compiled: &CompiledResidualEqualityPlan,
        inputs: &[DeclaredEncryptedNat],
        same_opening: SameOpeningReceipt,
        live_slots: usize,
    ) -> Result<BoundedEncryptedZeroPlan, ZeroObservationError> {
        let maximum_residual = u64::try_from(compiled.certificate().maximum_residual_sum)
            .map_err(|_| ZeroObservationError::ResidualBoundTooLarge)?;
        if maximum_residual == 0 || maximum_residual > 4_096 || live_slots == 0 {
            return Err(ZeroObservationError::BoundedZeroIntervalRefused { maximum_residual });
        }
        if maximum_residual >= self.plaintext_modulus {
            return Err(ZeroObservationError::BoundedZeroIntervalRefused { maximum_residual });
        }
        let expected = residual_statement_digest(compiled, inputs, same_opening.opening_commitment);
        if same_opening.version != ZERO_OBSERVATION_VERSION
            || same_opening.statement_digest != expected
        {
            return Err(ZeroObservationError::SameOpeningStatementMismatch);
        }
        let factor_count = maximum_residual as usize;
        let input_depth = compiled.cost().maximum_multiplicative_depth;
        let product_depth =
            usize::BITS as usize - (factor_count.saturating_sub(1)).leading_zeros() as usize;
        let zero_conversion_cost = BoundedEncryptedZeroCost {
            plaintext_constant_encodes: factor_count,
            ciphertext_plaintext_subtractions: factor_count,
            ciphertext_multiplications: factor_count.saturating_sub(1),
            relinearizations: factor_count.saturating_sub(1),
            ciphertext_plaintext_multiplications: 0,
            input_multiplicative_depth: input_depth,
            output_multiplicative_depth: input_depth + product_depth,
        };
        Ok(BoundedEncryptedZeroPlan {
            manifest: BoundedEncryptedZeroManifest {
                version: ZERO_OBSERVATION_VERSION,
                strategy: "exact encrypted bounded scaled product: product(i-r) for i=1..B",
                plaintext_modulus: self.plaintext_modulus,
                live_slots,
                maximum_residual,
                true_scale: factorial_mod(maximum_residual, self.plaintext_modulus),
                residual_computation_cost: compiled.cost().clone(),
                zero_conversion_cost,
                same_opening,
                output: "encrypted scaled bit; B! exactly when residual is zero and zero otherwise",
                leakage: "no residual or internal truth is opened by the conversion itself",
                trust_and_noise_boundary: vec![
                    "the same-opening receipt is produced by an external verifier",
                    "the residual no-wrap certificate must bound every live slot in 0..=B",
                    "exact bounded-domain polynomial semantics do not constitute a BFV noise theorem",
                    "successful oracle executions are measurements, not a general depth guarantee",
                ],
            },
        })
    }

    /// Execute the corrected residual and the exact bounded product indicator.
    pub fn execute(
        &self,
        logic_engine: &BfvLogicEngine,
        compiled: &CompiledResidualEqualityPlan,
        inputs: &[DeclaredEncryptedNat],
        plan: &BoundedEncryptedZeroPlan,
    ) -> Result<BoundedEncryptedZeroExecution, ZeroObservationError> {
        let expected_statement = residual_statement_digest(
            compiled,
            inputs,
            plan.manifest.same_opening.opening_commitment,
        );
        if expected_statement != plan.manifest.same_opening.statement_digest
            || compiled.cost() != &plan.manifest.residual_computation_cost
            || compiled.certificate().maximum_residual_sum
                != u128::from(plan.manifest.maximum_residual)
        {
            return Err(ZeroObservationError::ManifestDrift);
        }
        let residual = logic_engine
            .execute_residual_equalities(compiled, inputs)
            .map_err(ZeroObservationError::Logic)?;
        let started = Instant::now();
        let live_slots = plan.manifest.live_slots;
        let mut factors = Vec::with_capacity(plan.manifest.maximum_residual as usize);
        for integer in 1..=plan.manifest.maximum_residual {
            let constant =
                Plaintext::try_encode(&vec![integer; live_slots], Encoding::simd(), &self.params)
                    .map_err(|error| ZeroObservationError::Bfv(error.to_string()))?;
            factors.push(&constant - &residual.ciphertext);
        }
        let mut multiplications = 0usize;
        while factors.len() > 1 {
            let mut next = Vec::with_capacity(factors.len().div_ceil(2));
            let mut iter = factors.into_iter();
            while let Some(left) = iter.next() {
                if let Some(right) = iter.next() {
                    multiplications += 1;
                    next.push(
                        self.multiplicator
                            .multiply(&left, &right)
                            .map_err(|error| ZeroObservationError::Bfv(error.to_string()))?,
                    );
                } else {
                    next.push(left);
                }
            }
            factors = next;
        }
        if multiplications
            != plan
                .manifest
                .zero_conversion_cost
                .ciphertext_multiplications
        {
            return Err(ZeroObservationError::ManifestDrift);
        }
        let output = factors
            .pop()
            .ok_or(ZeroObservationError::BoundedZeroIntervalRefused {
                maximum_residual: 0,
            })?;
        Ok(BoundedEncryptedZeroExecution {
            manifest: plan.manifest.clone(),
            output,
            residual_evaluation_elapsed: residual.elapsed,
            zero_conversion_elapsed: started.elapsed(),
        })
    }
}

fn factorial_mod(bound: u64, modulus: u64) -> u64 {
    let mut result = 1u64;
    for value in 1..=bound {
        result = ((u128::from(result) * u128::from(value)) % u128::from(modulus)) as u64;
    }
    result
}

/// Open only the final encrypted canonical bit through the same n-of-n
/// threshold carrier.  This reveals one bit per live slot, not the residual.
pub fn execute_threshold_bit_observation(
    ciphertext: &Ciphertext,
    parties: &[ThresholdParty],
    params: &BfvParams,
    live_slots: usize,
) -> Result<ThresholdBitObservation, ZeroObservationError> {
    execute_threshold_scaled_bit_observation(ciphertext, 1, parties, params, live_slots)
}

/// Open a two-valued encrypted result: zero is false and `true_scale` is true.
/// Any third value fails closed, turning exhausted BFV noise into refusal
/// rather than a silently wrong logical decision.
pub fn execute_threshold_scaled_bit_observation(
    ciphertext: &Ciphertext,
    true_scale: u64,
    parties: &[ThresholdParty],
    params: &BfvParams,
    live_slots: usize,
) -> Result<ThresholdBitObservation, ZeroObservationError> {
    if parties.is_empty() || live_slots == 0 {
        return Err(ZeroObservationError::InvalidBoundaryShape);
    }
    let bytes = ciphertext.to_bytes();
    let lean = LeanCiphertext::from_fhe_bytes(&bytes, params.moduli(), params.degree(), true_scale)
        .map_err(|error| ZeroObservationError::CiphertextBoundary(error.to_string()))?;
    let started = Instant::now();
    let shares = parties
        .iter()
        .map(|party| party.partial_decrypt(&lean, MIN_SMUDGE_BITS))
        .collect::<Result<Vec<_>, _>>()
        .map_err(ZeroObservationError::Threshold)?;
    let decryption_share_wire_bytes = shares.iter().map(|share| share.to_wire_bytes().len()).sum();
    let opened = combine(&shares, params).map_err(ZeroObservationError::Threshold)?;
    if opened.len() < live_slots {
        return Err(ZeroObservationError::OpenedSlotsTooShort {
            have: opened.len(),
            need: live_slots,
        });
    }
    let mut opened_bits = Vec::with_capacity(live_slots);
    for &value in &opened[..live_slots] {
        match value {
            0 => opened_bits.push(false),
            value if value == true_scale => opened_bits.push(true),
            _ => return Err(ZeroObservationError::OpenedBitNonCanonical { value }),
        }
    }
    Ok(ThresholdBitObservation {
        opened_bits,
        elapsed_ns: started.elapsed().as_nanos(),
        decryption_share_messages: shares.len(),
        decryption_share_wire_bytes,
        threshold_combines: 1,
        leakage: "one final truth bit per live SIMD slot; the two-valued scaled carrier is opened",
        noise_boundary: "the fold-noise smudging theorem does not prove correctness for this multiplied depth; this execution is an oracle measurement",
    })
}

impl ThresholdZeroObservationExecution {
    pub fn end_to_end_comparable(&self) -> bool {
        self.coverage.complete()
    }

    pub fn encrypted_evaluation_elapsed(&self) -> Duration {
        Duration::from_nanos(
            u64::try_from(self.encrypted_evaluation_elapsed_ns).unwrap_or(u64::MAX),
        )
    }

    pub fn threshold_observation_elapsed(&self) -> Duration {
        Duration::from_nanos(
            u64::try_from(self.threshold_observation_elapsed_ns).unwrap_or(u64::MAX),
        )
    }
}

fn put_u64(hash: &mut Sha256, value: u64) {
    hash.update(value.to_le_bytes());
}

fn put_u128(hash: &mut Sha256, value: u128) {
    hash.update(value.to_le_bytes());
}

fn put_cost(hash: &mut Sha256, cost: &BfvCostManifest) {
    for value in [
        cost.logical_input_reads,
        cost.encrypted_constant_reads,
        cost.ciphertext_additions,
        cost.ciphertext_subtractions,
        cost.ciphertext_multiplications,
        cost.relinearizations,
        cost.maximum_multiplicative_depth,
        cost.boundary_zero_decisions,
    ] {
        put_u64(hash, value as u64);
    }
}

fn ciphertext_digest(ciphertext: &fhe::bfv::Ciphertext) -> [u8; 32] {
    Sha256::digest(ciphertext.to_bytes()).into()
}

/// Digest the exact residual plan, no-wrap certificate, opening commitment,
/// and exact input ciphertext bytes.  Reordering inputs, changing one pair, or
/// changing a declared bound changes the statement consumed by the external
/// same-opening verifier.
pub fn residual_statement_digest(
    compiled: &CompiledResidualEqualityPlan,
    inputs: &[DeclaredEncryptedNat],
    opening_commitment: [u8; 32],
) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(STATEMENT_DOMAIN);
    hash.update(ZERO_OBSERVATION_VERSION.to_le_bytes());
    hash.update(opening_commitment);
    put_u64(&mut hash, compiled.plan().pairs.len() as u64);
    for &(left, right) in &compiled.plan().pairs {
        put_u64(&mut hash, left as u64);
        put_u64(&mut hash, right as u64);
    }
    put_u64(&mut hash, compiled.plan().input_bound);
    let certificate = compiled.certificate();
    put_u64(&mut hash, certificate.plaintext_modulus);
    put_u64(&mut hash, certificate.centered_window);
    put_u64(&mut hash, certificate.pair_count as u64);
    put_u64(&mut hash, certificate.input_bound);
    put_u128(&mut hash, certificate.maximum_single_residual);
    put_u128(&mut hash, certificate.maximum_residual_sum);
    put_cost(&mut hash, compiled.cost());
    put_u64(&mut hash, inputs.len() as u64);
    for input in inputs {
        put_u64(&mut hash, input.declared_upper_bound());
        hash.update(ciphertext_digest(input.ciphertext()));
    }
    hash.finalize().into()
}

/// Compile a fully priced opening request.  `continuation_required` marks an
/// internal hybrid residual-to-bit conversion.  It is priced here, but the
/// executor refuses it until a real re-encrypt-and-resume machine exists.
pub fn compile_threshold_zero_observation(
    engine: &BfvLogicEngine,
    compiled: &CompiledResidualEqualityPlan,
    inputs: &[DeclaredEncryptedNat],
    same_opening: SameOpeningReceipt,
    party_count: usize,
    live_slots: usize,
    continuation_required: bool,
) -> Result<ThresholdZeroObservationPlan, ZeroObservationError> {
    if party_count == 0 || live_slots == 0 {
        return Err(ZeroObservationError::InvalidBoundaryShape);
    }
    if same_opening.version != ZERO_OBSERVATION_VERSION {
        return Err(ZeroObservationError::WrongVersion {
            got: same_opening.version,
        });
    }
    let expected = residual_statement_digest(compiled, inputs, same_opening.opening_commitment);
    if same_opening.statement_digest != expected {
        return Err(ZeroObservationError::SameOpeningStatementMismatch);
    }
    let boundary_cost = ThresholdBoundaryCost {
        decryption_share_messages: party_count,
        threshold_combines: 1,
        opened_residual_slots: live_slots,
        clear_zero_comparisons: live_slots,
        ciphertext_reencryptions: usize::from(continuation_required),
    };
    Ok(ThresholdZeroObservationPlan {
        manifest: ThresholdZeroObservationManifest {
            version: ZERO_OBSERVATION_VERSION,
            strategy: "n-of-n smudged threshold opening of complete residual",
            plaintext_modulus: engine.plaintext_modulus(),
            party_count,
            smudge_bits: MIN_SMUDGE_BITS,
            live_slots,
            continuation_required,
            encrypted_computation_cost: compiled.cost().clone(),
            boundary_cost,
            maximum_residual: compiled.certificate().maximum_residual_sum,
            same_opening,
            leakage: if continuation_required {
                "all live internal residual values and internal truth bits become public to the opening coordinator"
            } else {
                "all live final residual values and final truth bits become public to the opening coordinator"
            },
            trust_and_noise_boundary: vec![
                "external verifier must prove the committed opening matches every bound ciphertext",
                "n-of-n party custody and authenticated transport are deployment obligations",
                "the existing smudging theorem assumes the deployed fold-noise envelope; it is not a noise proof for multiplied logic ciphertexts",
                "successful oracle executions are measurements, not a general BFV correctness or security theorem",
                "key setup, input encryption, and external proof verification are outside this timed executor",
            ],
        },
    })
}

/// Execute the encrypted residual and its complete n-of-n threshold opening.
/// The output is a clear truth vector, but the receipt also records the larger
/// residual-value leakage actually incurred.
pub fn execute_final_threshold_zero_observation(
    engine: &BfvLogicEngine,
    compiled: &CompiledResidualEqualityPlan,
    inputs: &[DeclaredEncryptedNat],
    plan: &ThresholdZeroObservationPlan,
    parties: &[ThresholdParty],
    params: &BfvParams,
) -> Result<ThresholdZeroObservationExecution, ZeroObservationError> {
    if plan.manifest.continuation_required {
        return Err(ZeroObservationError::HybridContinuationNotImplemented);
    }
    if parties.len() != plan.manifest.party_count {
        return Err(ZeroObservationError::PartyCountMismatch {
            expected: plan.manifest.party_count,
            got: parties.len(),
        });
    }
    if params.plaintext_modulus() != plan.manifest.plaintext_modulus {
        return Err(ZeroObservationError::ParameterMismatch);
    }
    let expected_statement = residual_statement_digest(
        compiled,
        inputs,
        plan.manifest.same_opening.opening_commitment,
    );
    if expected_statement != plan.manifest.same_opening.statement_digest {
        return Err(ZeroObservationError::SameOpeningStatementMismatch);
    }

    let residual = engine
        .execute_residual_equalities(compiled, inputs)
        .map_err(ZeroObservationError::Logic)?;
    if residual.maximum_residual != plan.manifest.maximum_residual
        || residual.observed_cost != plan.manifest.encrypted_computation_cost
    {
        return Err(ZeroObservationError::ManifestDrift);
    }
    let residual_bytes = residual.ciphertext.to_bytes();
    let residual_ciphertext_digest = Sha256::digest(&residual_bytes).into();
    let maximum_residual = u64::try_from(residual.maximum_residual)
        .map_err(|_| ZeroObservationError::ResidualBoundTooLarge)?;
    let lean = LeanCiphertext::from_fhe_bytes(
        &residual_bytes,
        params.moduli(),
        params.degree(),
        maximum_residual,
    )
    .map_err(|error| ZeroObservationError::CiphertextBoundary(error.to_string()))?;

    let boundary_started = Instant::now();
    let shares = parties
        .iter()
        .map(|party| party.partial_decrypt(&lean, MIN_SMUDGE_BITS))
        .collect::<Result<Vec<_>, _>>()
        .map_err(ZeroObservationError::Threshold)?;
    let decryption_share_wire_bytes = shares.iter().map(|share| share.to_wire_bytes().len()).sum();
    let opened = combine(&shares, params).map_err(ZeroObservationError::Threshold)?;
    let threshold_observation_elapsed = boundary_started.elapsed();
    if opened.len() < plan.manifest.live_slots {
        return Err(ZeroObservationError::OpenedSlotsTooShort {
            have: opened.len(),
            need: plan.manifest.live_slots,
        });
    }
    let opened_residuals = opened[..plan.manifest.live_slots].to_vec();
    if opened_residuals
        .iter()
        .any(|&value| u128::from(value) > plan.manifest.maximum_residual)
    {
        return Err(ZeroObservationError::OpenedResidualOutOfRange);
    }
    let truth_bits = opened_residuals.iter().map(|value| *value == 0).collect();

    Ok(ThresholdZeroObservationExecution {
        manifest: plan.manifest.clone(),
        residual_ciphertext_digest,
        opened_residuals,
        truth_bits,
        encrypted_evaluation_elapsed_ns: residual.elapsed.as_nanos(),
        threshold_observation_elapsed_ns: threshold_observation_elapsed.as_nanos(),
        decryption_share_wire_bytes,
        coverage: PhaseCoverage {
            key_setup_measured: false,
            input_encryption_measured: false,
            same_opening_verification_measured: false,
            encrypted_evaluation_measured: true,
            every_zero_observation_measured: true,
            output_observation_measured: true,
        },
    })
}

#[derive(Debug)]
pub enum ZeroObservationError {
    WrongVersion { got: u32 },
    MalformedSameOpeningReceipt,
    SameOpeningStatementMismatch,
    InvalidBoundaryShape,
    PartyCountMismatch { expected: usize, got: usize },
    ParameterMismatch,
    HybridContinuationNotImplemented,
    UnsupportedBoundedZeroField { plaintext_modulus: u64 },
    BoundedZeroIntervalRefused { maximum_residual: u64 },
    ManifestDrift,
    ResidualBoundTooLarge,
    OpenedSlotsTooShort { have: usize, need: usize },
    OpenedResidualOutOfRange,
    OpenedBitNonCanonical { value: u64 },
    CiphertextBoundary(String),
    Bfv(String),
    Logic(LogicBfvError),
    Threshold(ThresholdError),
}

impl fmt::Display for ZeroObservationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WrongVersion { got } => write!(f, "zero-observation version {got} is unsupported"),
            Self::MalformedSameOpeningReceipt => {
                f.write_str("same-opening verifier receipt is empty or malformed")
            }
            Self::SameOpeningStatementMismatch => {
                f.write_str("same-opening receipt does not bind the exact plan and ciphertexts")
            }
            Self::InvalidBoundaryShape => {
                f.write_str("zero-observation party count and live-slot count must be nonzero")
            }
            Self::PartyCountMismatch { expected, got } => {
                write!(f, "zero-observation expected {expected} parties, got {got}")
            }
            Self::ParameterMismatch => f.write_str("zero-observation BFV parameters differ"),
            Self::HybridContinuationNotImplemented => f.write_str(
                "internal residual observation is priced, but re-encrypt-and-resume is not implemented",
            ),
            Self::UnsupportedBoundedZeroField { plaintext_modulus } => write!(
                f,
                "bounded encrypted zero test supports only pinned prime field 1032193, got {plaintext_modulus}"
            ),
            Self::BoundedZeroIntervalRefused { maximum_residual } => write!(
                f,
                "bounded encrypted zero interval 0..={maximum_residual} is empty or exceeds the 4096-point execution cap"
            ),
            Self::ManifestDrift => {
                f.write_str("zero-observation execution drifted from its computation manifest")
            }
            Self::ResidualBoundTooLarge => {
                f.write_str("residual bound does not fit the threshold ciphertext boundary")
            }
            Self::OpenedSlotsTooShort { have, need } => {
                write!(f, "threshold opening returned {have} slots, need {need}")
            }
            Self::OpenedResidualOutOfRange => {
                f.write_str("threshold-opened residual exceeds the certified no-wrap bound")
            }
            Self::OpenedBitNonCanonical { value } => {
                write!(f, "threshold-opened zero-test output {value} is not a canonical bit")
            }
            Self::CiphertextBoundary(error) => write!(f, "ciphertext boundary refused: {error}"),
            Self::Bfv(error) => write!(f, "BFV zero-observation operation failed: {error}"),
            Self::Logic(error) => write!(f, "logic execution failed: {error}"),
            Self::Threshold(error) => write!(f, "threshold observation failed: {error:?}"),
        }
    }
}

impl std::error::Error for ZeroObservationError {}
