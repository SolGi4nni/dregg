//! Transport and frontend-neutral operation boundary for fhEgg settlement.
//!
//! [`FheggSettlementBundle`] owns the public objects needed to reconstruct an
//! [`ExpectedClearingContext`] plus the computation-integrity evidence covering
//! that exact context. It deliberately contains no plaintext [`fhegg_fhe::Order`],
//! BFV secret key, decryption share, mask, Beaver triple, or party input share.
//! A web, Telegram, Discord, or native host may accept the strict canonical wire
//! form, decode it with bounded allocations, and hand the resulting operation to
//! [`DarkBazaarOffering`] without learning a trader's order.
//!
//! The attestation claim itself is not duplicated on the wire: it is a
//! deterministic function of the independently carried public context and is
//! reconstructed with [`AttestedClearingReceipt::issue`]. External evidence is
//! then checked against that reconstructed claim by the relying party's verifier.
//!
//! # Security disclosure
//!
//! This is an authenticated deployment seam, not a new lattice proof. The
//! public bundle contains ciphertext/source digests, masked Beaver openings,
//! public shape, and `(p*, V*)`; the live replayed market state separately
//! carries source-verifier certificates for the exact encrypted seller ask,
//! concrete asset, and bids. Settlement joins every exact message/ciphertext
//! pair to its WriteOnce board seal and common BFV identity. That same-opening
//! boundary is operator-visible and trusted-verifier based, not house-blind ZK.
//! The computation-integrity and MPC assumptions named by
//! [`crate::fhegg_settlement`] remain unchanged.

use std::fmt;
use std::time::Duration;

use dreggnet_offerings::BinaryOperationDescriptor;
use fhegg_fhe::attestation::{
    AttestationError, AttestedClearingReceipt, BfvPublicIdentity, ComputationIntegrityEvidence,
    ComputationIntegrityResidual, ComputationIntegrityVerifier, Digest32, ExpectedClearingContext,
    InputDigest, InputDigestKind, PartyIdentity, ReplayGuard,
};
use fhegg_fhe::mpc::Crossing;
use fhegg_fhe::mpc_party::{
    DistributedTranscript, MaskedOpening, PartyMpcError, PartyMpcSession,
    TripleFormationCertificate,
};

use crate::fhegg_settlement::{FheggSettlementError, FheggSettlementReceipt};
use crate::{DarkBazaarOffering, DarkBazaarSession};

const WIRE_MAGIC: &[u8; 8] = b"FHDBv002";

/// Stable operation name for HTTP routes, bot command adapters, queues, and
/// native dispatchers. The operation body is [`FheggSettlementBundle::to_wire_bytes`].
pub const FHEGG_SETTLEMENT_OPERATION: &str = "dark-bazaar.settle-fhegg.v2";

/// Exact content type accepted by HTTP and message-adapter upload boundaries.
pub const FHEGG_SETTLEMENT_MEDIA_TYPE: &str = "application/vnd.dregg.fhegg-settlement.v2";

/// Text a host can expose beside an upload/submit affordance without overstating
/// the current privacy or computation-integrity boundary.
pub const FHEGG_SETTLEMENT_DISCLOSURE: &str = "Authenticated fhEgg result: trader plaintext is absent from this request. The exact encrypted seller ask and concrete asset are frozen into a reserved WriteOnce listing-source slot before bids; every accepted bid seal likewise includes an exact signed-message/ciphertext binding certified after the configured ingress verifier reproduced that operator-visible BFV encryption. Substituting the asset, ask, bid, ciphertext, actor, certificate, BFV domain, or seal fails. This is a source-verifier trust boundary, not a house-blind lattice ZK proof. FHTRI004 adds roster/session-bound binary sacrifice and two-lane authenticated openings, while its setup authority still sees the candidate bits and MAC keys; it is not dealer-free malicious MPC or a PQ-completeness claim. A durable host retains this canonical public bundle for restart verification: the full hybrid-signed preprocessing certificate, exact timeout, ciphertext/source digests, masked openings, computation-integrity evidence, and public result. The fhEgg replay sidecar never stores order plaintext, an FHE secret key, encryption randomness, a decryption share, a MAC key share, a Beaver triple, or a party input share. The current CRAWL move log separately replays its operator-visible order values and public source certificates; this does not make CRAWL Tier0 house-blind.";

/// Hard transport limits are deliberately below `usize` and independent of
/// attacker-controlled declared lengths. The current N=2,K=4 demo is tiny.
pub const MAX_FHEGG_BUNDLE_BYTES: usize = 64 * 1024 * 1024;
const MAX_PARTIES: usize = 4_096;
const MAX_INPUTS: usize = 262_144;
const MAX_MASKED_OPENINGS: usize = 4_000_000;
const MAX_EVIDENCE_BYTES: usize = 8 * 1024 * 1024;
const MAX_PREPROCESSING_CERTIFICATE_BYTES: usize = 1024 * 1024;
const MAX_BIT_BYTES: usize = 64;

#[derive(Clone, Debug)]
pub struct FheggSettlementBundle {
    session: PartyMpcSession,
    ordered_roster: Vec<PartyIdentity>,
    bfv: BfvPublicIdentity,
    ordered_inputs: Vec<InputDigest>,
    transcript: DistributedTranscript,
    crossing: Crossing,
    receipt: AttestedClearingReceipt,
}

impl FheggSettlementBundle {
    /// Own an independently reconstructed public verification context and its
    /// exact attestation. Binding-only evidence can be transported but will be
    /// refused by the settlement operation's mandatory full verification.
    pub fn new(
        expected: &ExpectedClearingContext<'_>,
        receipt: &AttestedClearingReceipt,
    ) -> Result<Self, FheggTransportError> {
        if expected.session.preprocessing_binding().is_some() {
            expected.session.require_certified_preprocessing()?;
        }
        check_limits(
            expected.ordered_roster.len(),
            expected.ordered_inputs.len(),
            expected.transcript.masked.len(),
            evidence_len(&receipt.computation_integrity),
        )?;
        receipt.verify_binding(expected)?;
        Ok(Self {
            session: expected.session.clone(),
            ordered_roster: expected.ordered_roster.to_vec(),
            bfv: expected.bfv.clone(),
            ordered_inputs: expected.ordered_inputs.to_vec(),
            transcript: expected.transcript.clone(),
            crossing: expected.crossing.clone(),
            receipt: receipt.clone(),
        })
    }

    pub fn expected_context(&self) -> ExpectedClearingContext<'_> {
        ExpectedClearingContext {
            session: &self.session,
            ordered_roster: &self.ordered_roster,
            bfv: &self.bfv,
            ordered_inputs: &self.ordered_inputs,
            transcript: &self.transcript,
            crossing: &self.crossing,
        }
    }

    pub fn receipt(&self) -> &AttestedClearingReceipt {
        &self.receipt
    }

    pub fn claim_digest(&self) -> Digest32 {
        self.receipt.claim_digest()
    }

    pub fn source_inputs(&self) -> &[InputDigest] {
        &self.ordered_inputs
    }

    pub fn crossing(&self) -> &Crossing {
        &self.crossing
    }

    /// Strict, versioned, length-delimited encoding. Integer widths, option and
    /// enum tags, vector order, and all allocation limits are fixed here.
    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = Encoder::default();
        out.raw(WIRE_MAGIC);
        out.digest(&self.session.nonce());
        out.usize(self.session.n_parties());
        out.usize(self.session.buckets());
        out.usize(self.session.value_bits());
        out.u64(self.session.plaintext_modulus());
        out.u64(self.session.quorum_timeout().as_secs());
        out.u32(self.session.quorum_timeout().subsec_nanos());
        match self.session.preprocessing_certificate() {
            None => out.u8(0),
            Some(certificate) => {
                out.u8(1);
                out.bytes(&certificate.canonical_bytes());
            }
        }

        out.usize(self.ordered_roster.len());
        for party in &self.ordered_roster {
            out.digest(&party.0);
        }

        out.u64(self.bfv.n_parties);
        out.u64(self.bfv.opening_threshold);
        out.u64(self.bfv.degree);
        out.digest(&self.bfv.moduli_digest);
        out.u64(self.bfv.plaintext_modulus);
        out.digest(&self.bfv.crp_seed);
        out.digest(&self.bfv.collective_public_key_digest);

        out.usize(self.ordered_inputs.len());
        for input in &self.ordered_inputs {
            out.u8(match input.kind {
                InputDigestKind::Ciphertext => 0,
                InputDigestKind::Commitment => 1,
            });
            out.digest(&input.digest);
        }

        out.usize(self.transcript.masked.len());
        for opening in &self.transcript.masked {
            out.usize(opening.gate);
            out.u8(opening.d);
            out.u8(opening.e);
        }
        out.bytes(&self.transcript.revealed_pstar);
        out.bytes(&self.transcript.revealed_vstar);
        out.usize(self.transcript.and_gates);
        out.usize(self.transcript.scalar_opening_rounds);
        out.usize(self.transcript.modeled_batched_rounds);
        out.usize(self.transcript.gate_share_messages);
        out.usize(self.transcript.output_share_messages);

        match self.crossing.p_star {
            Some(price) => {
                out.u8(1);
                out.usize(price);
            }
            None => out.u8(0),
        }
        out.u64(self.crossing.v_star);

        match &self.receipt.computation_integrity {
            ComputationIntegrityEvidence::BindingOnly(
                ComputationIntegrityResidual::OutputOnlySelfAssertion,
            ) => {
                out.u8(0);
                out.u8(0);
            }
            ComputationIntegrityEvidence::External {
                verifier_id,
                evidence,
            } => {
                out.u8(1);
                out.digest(verifier_id);
                out.bytes(evidence);
            }
        }
        out.0
    }

    /// Decode with bounded allocations, reconstruct the canonical attestation
    /// claim from the owned public context, and validate the entire binding.
    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self, FheggTransportError> {
        if bytes.len() > MAX_FHEGG_BUNDLE_BYTES {
            return Err(FheggTransportError::BundleTooLarge(bytes.len()));
        }
        let mut input = Decoder::new(bytes);
        if input.raw::<8>()? != *WIRE_MAGIC {
            return Err(FheggTransportError::Malformed("wrong fhEgg bundle magic"));
        }
        let nonce = input.digest()?;
        let n_parties = input.usize()?;
        let buckets = input.usize()?;
        let value_bits = input.usize()?;
        let plaintext_modulus = input.u64()?;
        let timeout_secs = input.u64()?;
        let timeout_nanos = input.u32()?;
        if timeout_nanos >= 1_000_000_000 {
            return Err(FheggTransportError::Malformed(
                "invalid session timeout nanoseconds",
            ));
        }
        let preprocessing_certificate = match input.u8()? {
            0 => None,
            1 => Some(TripleFormationCertificate::from_canonical_bytes(
                &input.bounded_bytes(MAX_PREPROCESSING_CERTIFICATE_BYTES)?,
            )?),
            _ => {
                return Err(FheggTransportError::Malformed(
                    "invalid preprocessing binding tag",
                ));
            }
        };
        if n_parties > MAX_PARTIES || value_bits > 63 {
            return Err(FheggTransportError::DeclaredLimitExceeded);
        }
        let mut session = PartyMpcSession::new(
            nonce,
            n_parties,
            buckets,
            value_bits,
            plaintext_modulus,
            Duration::new(timeout_secs, timeout_nanos),
        )?;
        if let Some(certificate) = preprocessing_certificate {
            session = session.with_public_preprocessing_certificate(certificate)?;
        }

        let roster_len = input.bounded_len(MAX_PARTIES)?;
        let mut ordered_roster = Vec::with_capacity(roster_len);
        for _ in 0..roster_len {
            ordered_roster.push(PartyIdentity(input.digest()?));
        }

        let bfv = BfvPublicIdentity {
            n_parties: input.u64()?,
            opening_threshold: input.u64()?,
            degree: input.u64()?,
            moduli_digest: input.digest()?,
            plaintext_modulus: input.u64()?,
            crp_seed: input.digest()?,
            collective_public_key_digest: input.digest()?,
        };

        let inputs_len = input.bounded_len(MAX_INPUTS)?;
        let mut ordered_inputs = Vec::with_capacity(inputs_len);
        for _ in 0..inputs_len {
            let kind = match input.u8()? {
                0 => InputDigestKind::Ciphertext,
                1 => InputDigestKind::Commitment,
                _ => return Err(FheggTransportError::Malformed("invalid input digest kind")),
            };
            ordered_inputs.push(InputDigest {
                kind,
                digest: input.digest()?,
            });
        }

        let masked_len = input.bounded_len(MAX_MASKED_OPENINGS)?;
        let mut masked = Vec::with_capacity(masked_len);
        for _ in 0..masked_len {
            masked.push(MaskedOpening {
                gate: input.usize()?,
                d: input.u8()?,
                e: input.u8()?,
            });
        }
        let transcript = DistributedTranscript {
            masked,
            revealed_pstar: input.bounded_bytes(MAX_BIT_BYTES)?,
            revealed_vstar: input.bounded_bytes(MAX_BIT_BYTES)?,
            and_gates: input.usize()?,
            scalar_opening_rounds: input.usize()?,
            modeled_batched_rounds: input.usize()?,
            gate_share_messages: input.usize()?,
            output_share_messages: input.usize()?,
        };

        let p_star = match input.u8()? {
            0 => None,
            1 => Some(input.usize()?),
            _ => return Err(FheggTransportError::Malformed("invalid p* option tag")),
        };
        let crossing = Crossing {
            p_star,
            v_star: input.u64()?,
        };

        let computation_integrity = match input.u8()? {
            0 => {
                if input.u8()? != 0 {
                    return Err(FheggTransportError::Malformed(
                        "invalid binding-only residual tag",
                    ));
                }
                ComputationIntegrityEvidence::BindingOnly(
                    ComputationIntegrityResidual::OutputOnlySelfAssertion,
                )
            }
            1 => ComputationIntegrityEvidence::External {
                verifier_id: input.digest()?,
                evidence: input.bounded_bytes(MAX_EVIDENCE_BYTES)?,
            },
            _ => {
                return Err(FheggTransportError::Malformed(
                    "invalid computation-integrity tag",
                ));
            }
        };
        if !input.is_finished() {
            return Err(FheggTransportError::TrailingBytes);
        }
        check_limits(
            ordered_roster.len(),
            ordered_inputs.len(),
            transcript.masked.len(),
            evidence_len(&computation_integrity),
        )?;

        let context = ExpectedClearingContext {
            session: &session,
            ordered_roster: &ordered_roster,
            bfv: &bfv,
            ordered_inputs: &ordered_inputs,
            transcript: &transcript,
            crossing: &crossing,
        };
        let receipt = AttestedClearingReceipt::issue(&context, computation_integrity)?;
        Self::new(&context, &receipt)
    }
}

/// A frontend-neutral one-shot operation. Surface adapters only need to cap and
/// decode the byte body; the operation owns everything until host dispatch.
#[derive(Clone, Debug)]
pub struct FheggSettlementOperation {
    bundle: FheggSettlementBundle,
}

impl FheggSettlementOperation {
    pub const NAME: &'static str = FHEGG_SETTLEMENT_OPERATION;

    pub fn from_bundle(bundle: FheggSettlementBundle) -> Self {
        Self { bundle }
    }

    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self, FheggTransportError> {
        FheggSettlementBundle::from_wire_bytes(bytes).map(Self::from_bundle)
    }

    pub fn disclosure(&self) -> &'static str {
        FHEGG_SETTLEMENT_DISCLOSURE
    }

    /// The one frontend-neutral deos operation descriptor. Every adapter
    /// renders this value rather than copying names, limits, or disclosure text.
    pub fn descriptor() -> BinaryOperationDescriptor {
        BinaryOperationDescriptor {
            name: FHEGG_SETTLEMENT_OPERATION.to_string(),
            title: "Upload authenticated fhEgg settlement".to_string(),
            input_media_type: FHEGG_SETTLEMENT_MEDIA_TYPE.to_string(),
            max_input_bytes: MAX_FHEGG_BUNDLE_BYTES,
            disclosure: FHEGG_SETTLEMENT_DISCLOSURE.to_string(),
        }
    }

    pub fn execute<V: ComputationIntegrityVerifier, R: ReplayGuard>(
        self,
        offering: &DarkBazaarOffering,
        session: &mut DarkBazaarSession,
        verifier: &V,
        replay_guard: &mut R,
    ) -> Result<FheggSettlementReceipt, FheggSettlementError> {
        let expected = self.bundle.expected_context();
        offering.settle_fhegg_verified(
            session,
            self.bundle.receipt(),
            &expected,
            verifier,
            replay_guard,
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FheggTransportError {
    BundleTooLarge(usize),
    DeclaredLimitExceeded,
    Malformed(&'static str),
    TrailingBytes,
    Session(PartyMpcError),
    Binding(AttestationError),
}

impl fmt::Display for FheggTransportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BundleTooLarge(size) => write!(f, "fhEgg bundle is too large: {size} bytes"),
            Self::DeclaredLimitExceeded => write!(
                f,
                "fhEgg bundle declared a vector over its deployment limit"
            ),
            Self::Malformed(why) => write!(f, "malformed fhEgg settlement bundle: {why}"),
            Self::TrailingBytes => write!(f, "fhEgg settlement bundle has trailing bytes"),
            Self::Session(error) => error.fmt(f),
            Self::Binding(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for FheggTransportError {}

impl From<PartyMpcError> for FheggTransportError {
    fn from(error: PartyMpcError) -> Self {
        Self::Session(error)
    }
}

impl From<AttestationError> for FheggTransportError {
    fn from(error: AttestationError) -> Self {
        Self::Binding(error)
    }
}

fn evidence_len(evidence: &ComputationIntegrityEvidence) -> usize {
    match evidence {
        ComputationIntegrityEvidence::BindingOnly(_) => 0,
        ComputationIntegrityEvidence::External { evidence, .. } => evidence.len(),
    }
}

fn check_limits(
    roster: usize,
    inputs: usize,
    openings: usize,
    evidence: usize,
) -> Result<(), FheggTransportError> {
    if roster > MAX_PARTIES
        || inputs > MAX_INPUTS
        || openings > MAX_MASKED_OPENINGS
        || evidence > MAX_EVIDENCE_BYTES
    {
        return Err(FheggTransportError::DeclaredLimitExceeded);
    }
    Ok(())
}

#[derive(Default)]
struct Encoder(Vec<u8>);

impl Encoder {
    fn raw(&mut self, bytes: &[u8]) {
        self.0.extend_from_slice(bytes);
    }

    fn u8(&mut self, value: u8) {
        self.0.push(value);
    }

    fn u64(&mut self, value: u64) {
        self.raw(&value.to_be_bytes());
    }

    fn u32(&mut self, value: u32) {
        self.raw(&value.to_be_bytes());
    }

    fn usize(&mut self, value: usize) {
        self.u64(value as u64);
    }

    fn digest(&mut self, value: &Digest32) {
        self.raw(value);
    }

    fn bytes(&mut self, value: &[u8]) {
        self.usize(value.len());
        self.raw(value);
    }
}

struct Decoder<'a> {
    bytes: &'a [u8],
    cursor: usize,
}

impl<'a> Decoder<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, cursor: 0 }
    }

    fn raw<const N: usize>(&mut self) -> Result<[u8; N], FheggTransportError> {
        let end = self
            .cursor
            .checked_add(N)
            .filter(|&end| end <= self.bytes.len())
            .ok_or(FheggTransportError::Malformed(
                "truncated fixed-width field",
            ))?;
        let value = self.bytes[self.cursor..end]
            .try_into()
            .map_err(|_| FheggTransportError::Malformed("truncated fixed-width field"))?;
        self.cursor = end;
        Ok(value)
    }

    fn u8(&mut self) -> Result<u8, FheggTransportError> {
        Ok(self.raw::<1>()?[0])
    }

    fn u64(&mut self) -> Result<u64, FheggTransportError> {
        Ok(u64::from_be_bytes(self.raw::<8>()?))
    }

    fn u32(&mut self) -> Result<u32, FheggTransportError> {
        Ok(u32::from_be_bytes(self.raw::<4>()?))
    }

    fn usize(&mut self) -> Result<usize, FheggTransportError> {
        usize::try_from(self.u64()?).map_err(|_| FheggTransportError::DeclaredLimitExceeded)
    }

    fn digest(&mut self) -> Result<Digest32, FheggTransportError> {
        self.raw::<32>()
    }

    fn bounded_len(&mut self, max: usize) -> Result<usize, FheggTransportError> {
        let len = self.usize()?;
        if len > max {
            return Err(FheggTransportError::DeclaredLimitExceeded);
        }
        Ok(len)
    }

    fn bounded_bytes(&mut self, max: usize) -> Result<Vec<u8>, FheggTransportError> {
        let len = self.bounded_len(max)?;
        let end = self
            .cursor
            .checked_add(len)
            .filter(|&end| end <= self.bytes.len())
            .ok_or(FheggTransportError::Malformed("truncated byte vector"))?;
        let value = self.bytes[self.cursor..end].to_vec();
        self.cursor = end;
        Ok(value)
    }

    fn is_finished(&self) -> bool {
        self.cursor == self.bytes.len()
    }
}
