//! Fail-closed Cert-F translation validation for clearing receipts.
//!
//! [`fhegg_solver::cert::CertF`] is a useful translation certificate: it checks
//! a primal/dual witness against the public flow program `(A, w, c, epsilon)`
//! carried by the certificate.  That check does **not** say where the program
//! came from.  In particular, a claim digest prefixed to a certificate does not
//! prove that `(A, w, c)` was derived from the ciphertext digests in
//! [`ClearingClaim::ordered_inputs`], and Cert-F has no intrinsic meaning for
//! the clearing bucket `p*`.
//!
//! This module therefore separates two types:
//!
//! * [`CertFTranslationChecker`] checks the evidence carrier and its numeric
//!   primal/dual relation.  It deliberately does not implement
//!   [`ComputationIntegrityVerifier`].
//! * [`CertFClearingVerifier`] implements [`ComputationIntegrityVerifier`] only
//!   when constructed with an explicit [`CertFProgramBinder`].  The binder is
//!   the semantic authority that must derive (or otherwise independently bind)
//!   every public program field and the output meaning from the claim's real
//!   sources.  There is no permissive/default binder.
//!
//! # What remains for a dark/no-viewer binder
//!
//! An operator-visible reveal boundary can implement the binder from a
//! canonical list of verified `OrderSourceCertificate`s: verify the configured
//! source key, join every certificate to the BFV session, match its exact
//! message/ciphertext pair to a typed order-input segment, reconstruct the
//! canonical program, and recompute `(p*, V*)` including the public tie rule.
//! Such certificates reveal the plaintext order tuple and trust the configured
//! source verifier.  They are therefore **not** the true no-viewer binder.  That
//! stronger rung still needs a lattice/FHE same-opening and well-formedness
//! proof (or an equivalent malicious-secure MPC proof) from committed
//! ciphertexts to the canonical program and exact output.

use fhegg_solver::cert::CertF;

use crate::attestation::{
    ClearingClaim, ComputationIntegrityEvidence, ComputationIntegrityVerifier, Digest32,
};

const VERIFIER_DOMAIN: &[u8] = b"fhegg.CertFClearingVerifier.v2";
const BINDER_AND_DOMAIN: &[u8] = b"fhegg.CertFProgramBinder.all-of.v1";
const INTEGRITY_AND_DOMAIN: &[u8] = b"fhegg.ComputationIntegrityVerifier.all-of.v1";
const CERTF_EVIDENCE_VERSION: u8 = 2;
const INTEGRITY_AND_EVIDENCE_VERSION: u8 = 1;
const MAX_EVIDENCE_BYTES: usize = 4 * 1024 * 1024;
const MAX_COMPOSED_EVIDENCE_BYTES: usize = 8 * 1024 * 1024;

/// Largest accepted integer-valued objective. Larger values are rejected
/// before conversion, so no two accepted `u64` values can alias as `f64`.
pub const MAX_EXACT_F64_INTEGER: u64 = 1u64 << 53;

/// Numeric policy selected by the relying party, never by the proof producer.
///
/// The policy fixes the optimality and feasibility tolerances and bounds the
/// evidence-controlled program shape/coefficient scale.  A semantic binder may
/// (and normally should) impose substantially tighter, product-specific bounds.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct CertFVerifierPolicy {
    pub max_epsilon: f64,
    pub feasibility_tolerance: f64,
    pub volume_tolerance: f64,
    pub max_capacity: f64,
    pub max_abs_weight: f64,
    pub max_nodes: usize,
    pub max_edges: usize,
}

impl CertFVerifierPolicy {
    /// A small reveal-boundary policy suitable for exact/projected test
    /// certificates.  A deployment should construct its product-specific
    /// policy explicitly and commit it through the verifier id.
    pub const fn reveal_boundary() -> Self {
        Self {
            max_epsilon: 0.1,
            feasibility_tolerance: 1e-6,
            volume_tolerance: 1e-2,
            max_capacity: 1_000_000.0,
            max_abs_weight: 1_000_000.0,
            max_nodes: 65_536,
            max_edges: 1_000_000,
        }
    }

    fn valid(self) -> bool {
        self.max_epsilon.is_finite()
            && self.max_epsilon >= 0.0
            && self.feasibility_tolerance.is_finite()
            && self.feasibility_tolerance >= 0.0
            && self.volume_tolerance.is_finite()
            && self.volume_tolerance >= 0.0
            && self.volume_tolerance < 0.5
            && self.max_capacity.is_finite()
            && self.max_capacity >= 0.0
            && self.max_abs_weight.is_finite()
            && self.max_abs_weight >= 0.0
            && self.max_nodes > 0
            && self.max_edges > 0
    }

    fn digest(self) -> Digest32 {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"fhegg.CertFVerifierPolicy.v1");
        for value in [
            self.max_epsilon,
            self.feasibility_tolerance,
            self.volume_tolerance,
            self.max_capacity,
            self.max_abs_weight,
        ] {
            hasher.update(&value.to_bits().to_be_bytes());
        }
        hasher.update(&(self.max_nodes as u64).to_be_bytes());
        hasher.update(&(self.max_edges as u64).to_be_bytes());
        *hasher.finalize().as_bytes()
    }
}

/// Construction failure for a relying-party numeric policy.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CertFVerifierConfigError {
    InvalidNumericPolicy,
}

impl std::fmt::Display for CertFVerifierConfigError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "invalid Cert-F relying-party numeric policy")
    }
}

impl std::error::Error for CertFVerifierConfigError {}

/// Failure to assemble a bounded conjunction-evidence envelope.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntegrityCompositionError {
    EvidenceTooLarge,
}

impl std::fmt::Display for IntegrityCompositionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "composed computation-integrity evidence is too large")
    }
}

impl std::error::Error for IntegrityCompositionError {}

/// The semantic link missing from a standalone Cert-F carrier.
///
/// `binds` must fail unless the certificate's complete public program
/// (`n_nodes`, `m_edges`, `edges`, `w`, `c`, and `epsilon`) is the canonical
/// program derived from independently authenticated sources committed by
/// `claim.ordered_inputs`.  It must also bind the program's output meaning to
/// `claim.outcome`, including `p_star` and the public tie rule when the product
/// has a price bucket.  Merely checking `claim.digest()` is not an
/// implementation of this contract.
pub trait CertFProgramBinder {
    /// Stable identity of the derivation/source-authentication policy.  A
    /// configured key, program version, and input-layout version belong here.
    fn binding_id(&self) -> Digest32;

    /// Verify the semantic source -> program -> output relation.
    fn binds(&self, claim: &ClearingClaim, cert: &CertF) -> bool;
}

/// Conjunction of two independently useful binders (for example an exact
/// source/program binder AND an authenticated computation-roster binder).
#[derive(Clone, Debug)]
pub struct AllOfProgramBinder<A, B> {
    first: A,
    second: B,
}

impl<A, B> AllOfProgramBinder<A, B> {
    pub fn new(first: A, second: B) -> Self {
        Self { first, second }
    }
}

impl<A: CertFProgramBinder, B: CertFProgramBinder> CertFProgramBinder for AllOfProgramBinder<A, B> {
    fn binding_id(&self) -> Digest32 {
        let mut hasher = blake3::Hasher::new();
        hasher.update(BINDER_AND_DOMAIN);
        hasher.update(&self.first.binding_id());
        hasher.update(&self.second.binding_id());
        *hasher.finalize().as_bytes()
    }

    fn binds(&self, claim: &ClearingClaim, cert: &CertF) -> bool {
        self.first.binds(claim, cert) && self.second.binds(claim, cert)
    }
}

/// Conjunction of two complete integrity verifiers over one receipt field.
///
/// This closes the envelope-composition seam: a Cert-F verifier can be paired
/// with the existing authenticated-quorum verifier (or another independently
/// configured source verifier) without replacing either obligation. The
/// combined verifier id commits both component verifier ids and ordered roles.
#[derive(Clone, Debug)]
pub struct AllOfIntegrityVerifier<A, B> {
    first: A,
    second: B,
    verifier_id: Digest32,
}

impl<A: ComputationIntegrityVerifier, B: ComputationIntegrityVerifier>
    AllOfIntegrityVerifier<A, B>
{
    pub fn new(first: A, second: B) -> Self {
        let mut hasher = blake3::Hasher::new();
        hasher.update(INTEGRITY_AND_DOMAIN);
        hasher.update(&first.verifier_id());
        hasher.update(&second.verifier_id());
        let verifier_id = *hasher.finalize().as_bytes();
        Self {
            first,
            second,
            verifier_id,
        }
    }

    /// Assemble one bounded outer envelope. Component evidence remains in its
    /// native format and is checked only by its configured component verifier.
    pub fn assemble_evidence(
        &self,
        first_evidence: &[u8],
        second_evidence: &[u8],
    ) -> Result<ComputationIntegrityEvidence, IntegrityCompositionError> {
        let first_len = u32::try_from(first_evidence.len())
            .map_err(|_| IntegrityCompositionError::EvidenceTooLarge)?;
        let total_len = 1usize
            .checked_add(4)
            .and_then(|length| length.checked_add(first_evidence.len()))
            .and_then(|length| length.checked_add(second_evidence.len()))
            .ok_or(IntegrityCompositionError::EvidenceTooLarge)?;
        if total_len > MAX_COMPOSED_EVIDENCE_BYTES {
            return Err(IntegrityCompositionError::EvidenceTooLarge);
        }
        let mut evidence = Vec::with_capacity(total_len);
        evidence.push(INTEGRITY_AND_EVIDENCE_VERSION);
        evidence.extend_from_slice(&first_len.to_be_bytes());
        evidence.extend_from_slice(first_evidence);
        evidence.extend_from_slice(second_evidence);
        Ok(ComputationIntegrityEvidence::External {
            verifier_id: self.verifier_id,
            evidence,
        })
    }
}

impl<A: ComputationIntegrityVerifier, B: ComputationIntegrityVerifier> ComputationIntegrityVerifier
    for AllOfIntegrityVerifier<A, B>
{
    fn verifier_id(&self) -> Digest32 {
        self.verifier_id
    }

    fn verify(&self, claim_digest: &Digest32, evidence: &[u8]) -> bool {
        let Some((first, second)) = decode_composed(evidence) else {
            return false;
        };
        self.first.verify(claim_digest, first) && self.second.verify(claim_digest, second)
    }

    fn verify_claim(&self, claim: &ClearingClaim, evidence: &[u8]) -> bool {
        let Some((first, second)) = decode_composed(evidence) else {
            return false;
        };
        self.first.verify_claim(claim, first) && self.second.verify_claim(claim, second)
    }
}

/// Result of the useful, but deliberately non-semantic, translation check.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct CertFTranslationReport {
    pub primal: f64,
    pub dual: f64,
    pub volume_consistent: bool,
}

/// Standalone checker for a Cert-F carrier.  This type intentionally does not
/// implement [`ComputationIntegrityVerifier`].
#[derive(Clone, Copy, Debug)]
pub struct CertFTranslationChecker {
    policy: CertFVerifierPolicy,
}

impl CertFTranslationChecker {
    pub fn new(policy: CertFVerifierPolicy) -> Result<Self, CertFVerifierConfigError> {
        if !policy.valid() {
            return Err(CertFVerifierConfigError::InvalidNumericPolicy);
        }
        Ok(Self { policy })
    }

    /// Check carrier validity, fixed relying-party tolerances, and the numeric
    /// relation between its achieved objective and the claim's `V*`.
    /// No source/program semantics are inferred by this method.
    pub fn check_claim(
        &self,
        claim: &ClearingClaim,
        evidence: &[u8],
    ) -> Option<CertFTranslationReport> {
        let (bound, cert) = decode(evidence)?;
        if bound != claim.digest() || !program_within_policy(&cert, self.policy) {
            return None;
        }
        let checked = cert.check_with(self.policy.feasibility_tolerance);
        if !checked.valid {
            return None;
        }
        let (primal, dual) = recomputed_objectives(&cert)?;
        if dual + self.policy.volume_tolerance < primal {
            return None;
        }
        if claim.outcome.v_star > MAX_EXACT_F64_INTEGER {
            return None;
        }
        let v_star = claim.outcome.v_star as f64;
        // Bind the published value to the achieved primal objective, not merely
        // to an arbitrarily wide primal/dual interval.  The dual supplies the
        // separately policy-bounded epsilon-optimality statement.
        let volume_consistent = (primal - v_star).abs() <= self.policy.volume_tolerance
            && v_star <= dual + self.policy.volume_tolerance
            && dual - primal <= self.policy.max_epsilon + self.policy.volume_tolerance;
        volume_consistent.then_some(CertFTranslationReport {
            primal,
            dual,
            volume_consistent,
        })
    }
}

/// Full receipt verifier, available only with an explicit semantic binder.
#[derive(Clone, Debug)]
pub struct CertFClearingVerifier<B> {
    binder: B,
    checker: CertFTranslationChecker,
    verifier_id: Digest32,
}

impl<B: CertFProgramBinder> CertFClearingVerifier<B> {
    pub fn new(binder: B, policy: CertFVerifierPolicy) -> Result<Self, CertFVerifierConfigError> {
        let checker = CertFTranslationChecker::new(policy)?;
        let mut hasher = blake3::Hasher::new();
        hasher.update(VERIFIER_DOMAIN);
        hasher.update(&binder.binding_id());
        hasher.update(&policy.digest());
        let verifier_id = *hasher.finalize().as_bytes();
        Ok(Self {
            binder,
            checker,
            verifier_id,
        })
    }

    pub fn policy(&self) -> CertFVerifierPolicy {
        self.checker.policy
    }
}

impl<B: CertFProgramBinder> ComputationIntegrityVerifier for CertFClearingVerifier<B> {
    fn verifier_id(&self) -> Digest32 {
        self.verifier_id
    }

    /// A digest alone cannot drive the semantic binder.  Fail closed; receipt
    /// verification calls the overridden full-claim method below.
    fn verify(&self, _claim_digest: &Digest32, _evidence: &[u8]) -> bool {
        false
    }

    fn verify_claim(&self, claim: &ClearingClaim, evidence: &[u8]) -> bool {
        let Some((_bound, cert)) = decode(evidence) else {
            return false;
        };
        self.checker.check_claim(claim, evidence).is_some() && self.binder.binds(claim, &cert)
    }
}

/// Canonical v2 evidence: `version || bound_claim_digest || cert_json`.
///
/// The digest prevents accidental/stale cross-claim reuse.  It is not a
/// signature and is not the semantic program binding; that is the binder's job.
pub fn assemble_evidence(claim_digest: &Digest32, cert: &CertF) -> Vec<u8> {
    let json = cert.to_json();
    let mut out = Vec::with_capacity(1 + 32 + json.len());
    out.push(CERTF_EVIDENCE_VERSION);
    out.extend_from_slice(claim_digest);
    out.extend_from_slice(json.as_bytes());
    out
}

fn decode(evidence: &[u8]) -> Option<(Digest32, CertF)> {
    if evidence.len() < 1 + 32
        || evidence.len() > MAX_EVIDENCE_BYTES
        || evidence[0] != CERTF_EVIDENCE_VERSION
    {
        return None;
    }
    let mut bound = [0u8; 32];
    bound.copy_from_slice(&evidence[1..33]);
    let cert: CertF = serde_json::from_slice(&evidence[33..]).ok()?;
    Some((bound, cert))
}

fn decode_composed(evidence: &[u8]) -> Option<(&[u8], &[u8])> {
    const HEADER_LEN: usize = 1 + 4;
    if evidence.len() < HEADER_LEN
        || evidence.len() > MAX_COMPOSED_EVIDENCE_BYTES
        || evidence[0] != INTEGRITY_AND_EVIDENCE_VERSION
    {
        return None;
    }
    let first_len = u32::from_be_bytes(evidence[1..5].try_into().ok()?) as usize;
    let first_end = HEADER_LEN.checked_add(first_len)?;
    if first_end > evidence.len() {
        return None;
    }
    Some((&evidence[HEADER_LEN..first_end], &evidence[first_end..]))
}

fn program_within_policy(cert: &CertF, policy: CertFVerifierPolicy) -> bool {
    cert.n_nodes <= policy.max_nodes
        && cert.m_edges <= policy.max_edges
        && cert.epsilon.is_finite()
        && cert.epsilon >= 0.0
        && cert.epsilon <= policy.max_epsilon
        && cert
            .c
            .iter()
            .all(|value| value.is_finite() && *value >= 0.0 && *value <= policy.max_capacity)
        && cert
            .w
            .iter()
            .all(|value| value.is_finite() && value.abs() <= policy.max_abs_weight)
}

fn recomputed_objectives(cert: &CertF) -> Option<(f64, f64)> {
    if cert.w.len() != cert.f.len() || cert.c.len() != cert.s.len() {
        return None;
    }
    let primal: f64 = cert.w.iter().zip(&cert.f).map(|(w, f)| w * f).sum();
    let dual: f64 = cert.c.iter().zip(&cert.s).map(|(c, s)| c * s).sum();
    (primal.is_finite() && dual.is_finite()).then_some((primal, dual))
}
