//! Typed `FHTRI005` dealerless preprocessing composition.
//!
//! One threshold-BFV batch supplies exactly `129 = 1 kept + 128 sacrificed`
//! private candidates per kept gate. Each party retains its BFV output, emits a
//! public sacrifice-row commitment, and later retains its own candidate/MAC-bit
//! custody. The ceremony requires the depth-three degree-8192 correlation
//! parameter profile: the additive degree-4096 profile cannot decrypt a full
//! 129-candidate row reliably. The coordinator sees only public BFV, candidate,
//! MAC-key, and beacon artifacts.
//!
//! State transitions consume their predecessor. There is no partial-roster
//! fallback and no method that calls `mpc_distributed_mac`'s test-only ideal OT
//! adapter. The present production path deliberately terminates at
//! [`AwaitingCrossTermProvider`]; a future malicious-secure PQ OT/VOLE or
//! threshold-BFV provider must add the next typed transition.
//!
//! The remaining security boundary is exact: BFV contribution bitness and
//! decryption-share correctness still lack transferable lattice proofs; compact
//! ceremony identities and the BFV ML-DSA roster still need an enrollment
//! mapping; reliable broadcast/signatures are external; and commit-reveal keeps
//! last-revealer abort bias. No authenticated candidate is released here.

use std::fmt;

use sha2::{Digest, Sha512};

use crate::distributed_bfv_correlation::{
    CorrelationError, CorrelationPartyOutput, CorrelationSession, CorrelationTranscript,
    OpenedCorrelation, PartyOutputCommitment, DISTRIBUTED_BFV_PARTIES, MAX_DISTRIBUTED_BFV_TRIPLES,
};
use crate::joint_beacon::{
    finalize_beacon, seal_commitments as seal_beacon_set, JointBeaconCommitment,
    JointBeaconCommitmentSet, JointBeaconContext, JointBeaconError, JointBeaconReveal,
    JointBeaconTranscript,
};
use crate::mpc_distributed_mac::{
    DistributedMacCertificate, DistributedMacError, DistributedMacManifest, KeyContribution,
    MacKeyShareCustody, PartyBitShares, PartyTagBuilder, DISTRIBUTED_MAC_LANES,
};
use crate::mpc_party::sacrifice::{
    ensure_same_candidate_manifest, prepare_candidate_commitment, seal_candidate_commitments,
    BinarySacrificeError, BinaryTripleShare, CandidateCommitmentMessage, CommittedSacrificeBatch,
    PartySacrificeMaterial, PendingCandidateCommitment, SacrificeCandidateRow,
    SacrificeCommitmentBinding, BINARY_SACRIFICE_SECURITY_BITS,
};
use crate::threshold::BfvParams;

pub const FHTRI005_CANDIDATES_PER_GATE: usize = BINARY_SACRIFICE_SECURITY_BITS + 1;
pub const FHTRI005_BITS_PER_CANDIDATE: usize = 3;
const PLAN_DOMAIN: &[u8] = b"fhegg/fhtri005/dealerless-plan/v1";
const CANDIDATE_CONTEXT_DOMAIN: &[u8] = b"fhegg/fhtri005/candidate-context/v1";
const MAC_BINDING_DOMAIN: &[u8] = b"fhegg/fhtri005/mac-binding/v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DealerlessPreprocessingError {
    InvalidParameters(&'static str),
    ArithmeticOverflow,
    UnsupportedPartyCount { have: usize, required: usize },
    Correlation(CorrelationError),
    Sacrifice(BinarySacrificeError),
    DistributedMac(DistributedMacError),
    JointBeacon(JointBeaconError),
    CeremonyMismatch,
    CandidateUndersupply { have: usize, need: usize },
}

impl fmt::Display for DealerlessPreprocessingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FHTRI005 dealerless ceremony refused: {self:?}")
    }
}
impl std::error::Error for DealerlessPreprocessingError {}
impl From<CorrelationError> for DealerlessPreprocessingError {
    fn from(value: CorrelationError) -> Self {
        Self::Correlation(value)
    }
}
impl From<BinarySacrificeError> for DealerlessPreprocessingError {
    fn from(value: BinarySacrificeError) -> Self {
        Self::Sacrifice(value)
    }
}
impl From<DistributedMacError> for DealerlessPreprocessingError {
    fn from(value: DistributedMacError) -> Self {
        Self::DistributedMac(value)
    }
}
impl From<JointBeaconError> for DealerlessPreprocessingError {
    fn from(value: JointBeaconError) -> Self {
        Self::JointBeacon(value)
    }
}
pub type Result<T> = std::result::Result<T, DealerlessPreprocessingError>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DealerlessCeremonyPlan {
    session_digest: [u8; 32],
    roster: Vec<[u8; 32]>,
    kept_gates: usize,
    candidate_count: usize,
    mac_values: u32,
    batch_binding: [u8; 64],
    digest: [u8; 64],
}

impl DealerlessCeremonyPlan {
    fn build(
        session_digest: [u8; 32],
        roster: Vec<[u8; 32]>,
        kept_gates: usize,
        batch_binding: [u8; 64],
        correlation_triples: usize,
    ) -> Result<Self> {
        if session_digest == [0; 32] || batch_binding == [0; 64] || kept_gates == 0 {
            return Err(DealerlessPreprocessingError::InvalidParameters(
                "session, batch, and kept-gate count must be nonzero",
            ));
        }
        if roster.len() != DISTRIBUTED_BFV_PARTIES {
            return Err(DealerlessPreprocessingError::UnsupportedPartyCount {
                have: roster.len(),
                required: DISTRIBUTED_BFV_PARTIES,
            });
        }
        for (party, id) in roster.iter().enumerate() {
            if *id == [0; 32] || roster[..party].contains(id) {
                return Err(DealerlessPreprocessingError::InvalidParameters(
                    "roster identities must be nonzero and unique",
                ));
            }
        }
        let candidate_count = kept_gates
            .checked_mul(FHTRI005_CANDIDATES_PER_GATE)
            .ok_or(DealerlessPreprocessingError::ArithmeticOverflow)?;
        if candidate_count > MAX_DISTRIBUTED_BFV_TRIPLES {
            return Err(DealerlessPreprocessingError::InvalidParameters(
                "candidate batch exceeds threshold-BFV SIMD capacity",
            ));
        }
        if correlation_triples != candidate_count {
            return Err(DealerlessPreprocessingError::CandidateUndersupply {
                have: correlation_triples,
                need: candidate_count,
            });
        }
        let mac_values = u32::try_from(
            candidate_count
                .checked_mul(FHTRI005_BITS_PER_CANDIDATE)
                .ok_or(DealerlessPreprocessingError::ArithmeticOverflow)?,
        )
        .map_err(|_| DealerlessPreprocessingError::ArithmeticOverflow)?;
        let digest = plan_digest(
            session_digest,
            &roster,
            kept_gates,
            candidate_count,
            mac_values,
            batch_binding,
        )?;
        Ok(Self {
            session_digest,
            roster,
            kept_gates,
            candidate_count,
            mac_values,
            batch_binding,
            digest,
        })
    }

    pub fn session_digest(&self) -> [u8; 32] {
        self.session_digest
    }
    pub fn roster(&self) -> &[[u8; 32]] {
        &self.roster
    }
    pub fn kept_gates(&self) -> usize {
        self.kept_gates
    }
    pub fn candidate_count(&self) -> usize {
        self.candidate_count
    }
    pub fn mac_values(&self) -> u32 {
        self.mac_values
    }
    pub fn batch_binding(&self) -> [u8; 64] {
        self.batch_binding
    }
    pub fn digest(&self) -> [u8; 64] {
        self.digest
    }
}

pub struct AwaitingCorrelationOpening {
    plan: DealerlessCeremonyPlan,
}

impl AwaitingCorrelationOpening {
    /// The only production constructor accepts the real BFV session and its
    /// exact candidate count.
    pub fn new(
        correlation: &CorrelationSession,
        params: &BfvParams,
        roster: Vec<[u8; 32]>,
        kept_gates: usize,
        batch_binding: [u8; 64],
    ) -> Result<Self> {
        if !params.is_correlation_set() || !correlation.matches_parameters(params) {
            return Err(DealerlessPreprocessingError::InvalidParameters(
                "session must use the exact depth-three correlation parameter set",
            ));
        }
        Ok(Self {
            plan: DealerlessCeremonyPlan::build(
                correlation.digest(),
                roster,
                kept_gates,
                batch_binding,
                correlation.triples(),
            )?,
        })
    }

    pub fn plan(&self) -> &DealerlessCeremonyPlan {
        &self.plan
    }

    pub fn seal_correlation(
        self,
        correlation: &CorrelationSession,
        opened: OpenedCorrelation,
        commitments: [PartyOutputCommitment; DISTRIBUTED_BFV_PARTIES],
    ) -> Result<(CorrelationCandidatesCommitted, CorrelationTranscript)> {
        if correlation.digest() != self.plan.session_digest
            || correlation.triples() != self.plan.candidate_count
        {
            return Err(DealerlessPreprocessingError::CeremonyMismatch);
        }
        let (transcript, certificate) = opened.seal(&commitments)?;
        certificate.validate(correlation)?;
        let certificate_wire = certificate.to_wire_bytes()?;
        let binding = SacrificeCommitmentBinding::new(
            candidate_context(&self.plan, &certificate_wire),
            self.plan.roster.clone(),
            self.plan.kept_gates,
            self.plan.batch_binding,
        )?;
        Ok((
            CorrelationCandidatesCommitted {
                round: CandidateCommitmentRound {
                    plan: self.plan,
                    binding,
                    correlation_certificate: certificate_wire,
                },
                output_commitments: commitments,
            },
            transcript,
        ))
    }
}

pub struct CorrelationCandidatesCommitted {
    round: CandidateCommitmentRound,
    output_commitments: [PartyOutputCommitment; DISTRIBUTED_BFV_PARTIES],
}

impl CorrelationCandidatesCommitted {
    pub fn plan(&self) -> &DealerlessCeremonyPlan {
        &self.round.plan
    }

    /// Consumes exactly one party's retained BFV output locally.
    pub fn prepare_party_candidates(
        &self,
        party: usize,
        output: CorrelationPartyOutput,
    ) -> Result<DealerlessPartyCandidates> {
        if party >= DISTRIBUTED_BFV_PARTIES || output.commitment() != self.output_commitments[party]
        {
            return Err(DealerlessPreprocessingError::CeremonyMismatch);
        }
        let (salt, triples) = output.into_candidate_parts();
        self.round.prepare_from_parts(party, salt, triples)
    }

    pub fn seal_candidate_messages(
        self,
        messages: Vec<CandidateCommitmentMessage>,
    ) -> Result<CandidatesCommitted> {
        self.round.seal_messages(messages)
    }
}

struct CandidateCommitmentRound {
    plan: DealerlessCeremonyPlan,
    binding: SacrificeCommitmentBinding,
    correlation_certificate: Vec<u8>,
}

impl CandidateCommitmentRound {
    fn prepare_from_parts(
        &self,
        party: usize,
        salt: [u8; 32],
        triples: Vec<BinaryTripleShare>,
    ) -> Result<DealerlessPartyCandidates> {
        if party >= self.plan.roster.len() {
            return Err(DealerlessPreprocessingError::UnsupportedPartyCount {
                have: party + 1,
                required: self.plan.roster.len(),
            });
        }
        let bits = flatten_candidate_bits(&self.plan, &triples)?;
        let row = partition_candidate_row(&self.plan, party, triples)?;
        let (message, pending) = prepare_candidate_commitment(&self.binding, row, salt)?;
        Ok(DealerlessPartyCandidates {
            plan_digest: self.plan.digest,
            party,
            message,
            pending,
            bits,
        })
    }

    fn seal_messages(
        self,
        messages: Vec<CandidateCommitmentMessage>,
    ) -> Result<CandidatesCommitted> {
        let candidate_manifest = seal_candidate_commitments(&self.binding, &messages)?;
        let mac_manifest = DistributedMacManifest::new(
            self.plan.session_digest,
            candidate_manifest.root(),
            self.plan.roster.clone(),
            self.plan.mac_values,
        )?;
        Ok(CandidatesCommitted {
            plan: self.plan,
            sacrifice_binding: self.binding,
            candidate_manifest,
            correlation_certificate: self.correlation_certificate,
            mac_manifest,
        })
    }
}

pub struct DealerlessPartyCandidates {
    plan_digest: [u8; 64],
    party: usize,
    message: CandidateCommitmentMessage,
    pending: PendingCandidateCommitment,
    bits: Vec<u8>,
}

impl DealerlessPartyCandidates {
    pub fn party(&self) -> usize {
        self.party
    }
    pub fn commitment(&self) -> CandidateCommitmentMessage {
        self.message.clone()
    }

    pub fn bind_awaiting_cross_terms(
        self,
        public: &AwaitingCrossTermProvider,
        key: MacKeyShareCustody,
    ) -> Result<DealerlessPartyAwaitingCrossTerms> {
        if self.plan_digest != public.plan.digest
            || self.party >= public.plan.roster.len()
            || self.message.commitment() != public.candidate_manifest.row_commitments()[self.party]
            || self.bits.len() != public.plan.mac_values as usize
        {
            return Err(DealerlessPreprocessingError::CeremonyMismatch);
        }
        let material = self
            .pending
            .bind_to_manifest(&public.sacrifice_binding, &public.candidate_manifest)?;
        let bit_shares = PartyBitShares::new(
            &public.mac_certificate,
            u32::try_from(self.party)
                .map_err(|_| DealerlessPreprocessingError::ArithmeticOverflow)?,
            self.bits,
        )?;
        // This is also the only way into the terminal party-local state: it
        // validates that the retained secret key is the exact contribution
        // committed by this party in the public MAC certificate.  Keeping a
        // raw, unchecked `(key, bits)` pair here would merely move a
        // coordinator-substitution failure into the future VOLE transition.
        let tag_builder = PartyTagBuilder::new(&public.mac_certificate, &key, bit_shares)?;
        Ok(DealerlessPartyAwaitingCrossTerms {
            party: self.party,
            material,
            key,
            tag_builder,
        })
    }
}

pub struct CandidatesCommitted {
    plan: DealerlessCeremonyPlan,
    sacrifice_binding: SacrificeCommitmentBinding,
    candidate_manifest: CommittedSacrificeBatch,
    correlation_certificate: Vec<u8>,
    mac_manifest: DistributedMacManifest,
}

impl CandidatesCommitted {
    pub fn candidate_manifest(&self) -> &CommittedSacrificeBatch {
        &self.candidate_manifest
    }
    pub fn mac_manifest(&self) -> &DistributedMacManifest {
        &self.mac_manifest
    }
    pub fn ensure_same_view(&self, other: &Self) -> Result<()> {
        if self.plan != other.plan || self.sacrifice_binding != other.sacrifice_binding {
            return Err(DealerlessPreprocessingError::CeremonyMismatch);
        }
        ensure_same_candidate_manifest(
            &self.sacrifice_binding,
            &self.candidate_manifest,
            &other.candidate_manifest,
        )?;
        Ok(())
    }

    pub fn seal_mac_keys(self, contributions: Vec<KeyContribution>) -> Result<MacKeysCommitted> {
        let mac_certificate =
            DistributedMacCertificate::seal(self.mac_manifest.clone(), contributions)?;
        let beacon_context = JointBeaconContext::new(
            self.plan.session_digest,
            self.plan.roster.clone(),
            self.candidate_manifest.root(),
            mac_binding(&self.mac_manifest, &mac_certificate),
        )?;
        Ok(MacKeysCommitted {
            plan: self.plan,
            sacrifice_binding: self.sacrifice_binding,
            candidate_manifest: self.candidate_manifest,
            correlation_certificate: self.correlation_certificate,
            mac_certificate,
            beacon_context,
        })
    }
}

pub struct MacKeysCommitted {
    plan: DealerlessCeremonyPlan,
    sacrifice_binding: SacrificeCommitmentBinding,
    candidate_manifest: CommittedSacrificeBatch,
    correlation_certificate: Vec<u8>,
    mac_certificate: DistributedMacCertificate,
    beacon_context: JointBeaconContext,
}

impl MacKeysCommitted {
    pub fn beacon_context(&self) -> &JointBeaconContext {
        &self.beacon_context
    }
    pub fn seal_beacon_commitments(
        self,
        commitments: Vec<JointBeaconCommitment>,
    ) -> Result<BeaconCommitmentsCommitted> {
        let set = seal_beacon_set(&self.beacon_context, &commitments)?;
        Ok(BeaconCommitmentsCommitted { public: self, set })
    }
}

pub struct BeaconCommitmentsCommitted {
    public: MacKeysCommitted,
    set: JointBeaconCommitmentSet,
}

impl BeaconCommitmentsCommitted {
    pub fn commitment_set(&self) -> &JointBeaconCommitmentSet {
        &self.set
    }
    pub fn finalize_beacon(
        self,
        reveals: Vec<JointBeaconReveal>,
    ) -> Result<AwaitingCrossTermProvider> {
        let beacon = finalize_beacon(&self.public.beacon_context, &self.set, &reveals)?;
        Ok(AwaitingCrossTermProvider {
            plan: self.public.plan,
            sacrifice_binding: self.public.sacrifice_binding,
            candidate_manifest: self.public.candidate_manifest,
            correlation_certificate: self.public.correlation_certificate,
            mac_certificate: self.public.mac_certificate,
            beacon,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CrossTermRequirement {
    pub ceremony_digest: [u8; 64],
    pub setup_root: [u8; 64],
    pub parties: u32,
    pub values_per_party: u32,
    pub mac_lanes: usize,
    pub ordered_pair_batches: usize,
}

/// Intentional terminal production state. There is no ideal-transfer or
/// `finish` method.
pub struct AwaitingCrossTermProvider {
    plan: DealerlessCeremonyPlan,
    sacrifice_binding: SacrificeCommitmentBinding,
    candidate_manifest: CommittedSacrificeBatch,
    correlation_certificate: Vec<u8>,
    mac_certificate: DistributedMacCertificate,
    beacon: JointBeaconTranscript,
}

impl AwaitingCrossTermProvider {
    pub fn plan(&self) -> &DealerlessCeremonyPlan {
        &self.plan
    }
    pub fn candidate_manifest(&self) -> &CommittedSacrificeBatch {
        &self.candidate_manifest
    }
    pub fn mac_certificate(&self) -> &DistributedMacCertificate {
        &self.mac_certificate
    }
    pub fn beacon(&self) -> &JointBeaconTranscript {
        &self.beacon
    }
    pub fn correlation_certificate_wire(&self) -> &[u8] {
        &self.correlation_certificate
    }
    pub fn cross_term_requirement(&self) -> CrossTermRequirement {
        let parties = self.mac_certificate.manifest().parties();
        CrossTermRequirement {
            ceremony_digest: self.plan.digest,
            setup_root: self.mac_certificate.setup_root(),
            parties,
            values_per_party: self.mac_certificate.manifest().values(),
            mac_lanes: DISTRIBUTED_MAC_LANES,
            ordered_pair_batches: parties as usize * (parties as usize - 1),
        }
    }
}

pub struct DealerlessPartyAwaitingCrossTerms {
    party: usize,
    material: PartySacrificeMaterial,
    key: MacKeyShareCustody,
    tag_builder: PartyTagBuilder,
}

impl DealerlessPartyAwaitingCrossTerms {
    pub fn party(&self) -> usize {
        self.party
    }
    pub fn into_parts(self) -> (PartySacrificeMaterial, MacKeyShareCustody, PartyTagBuilder) {
        (self.material, self.key, self.tag_builder)
    }
}

fn partition_candidate_row(
    plan: &DealerlessCeremonyPlan,
    party: usize,
    triples: Vec<BinaryTripleShare>,
) -> Result<SacrificeCandidateRow> {
    if triples.len() != plan.candidate_count {
        return Err(DealerlessPreprocessingError::CandidateUndersupply {
            have: triples.len(),
            need: plan.candidate_count,
        });
    }
    let mut kept = Vec::with_capacity(plan.kept_gates);
    let mut sacrificed = Vec::with_capacity(plan.kept_gates * BINARY_SACRIFICE_SECURITY_BITS);
    let mut iter = triples.into_iter();
    for _ in 0..plan.kept_gates {
        kept.push(
            iter.next()
                .ok_or(DealerlessPreprocessingError::CandidateUndersupply {
                    have: 0,
                    need: plan.candidate_count,
                })?,
        );
        sacrificed.extend(iter.by_ref().take(BINARY_SACRIFICE_SECURITY_BITS));
    }
    if iter.next().is_some()
        || kept.len() != plan.kept_gates
        || sacrificed.len() != plan.kept_gates * BINARY_SACRIFICE_SECURITY_BITS
    {
        return Err(DealerlessPreprocessingError::CandidateUndersupply {
            have: kept.len() + sacrificed.len(),
            need: plan.candidate_count,
        });
    }
    Ok(SacrificeCandidateRow::new(party, kept, sacrificed)?)
}

fn flatten_candidate_bits(
    plan: &DealerlessCeremonyPlan,
    triples: &[BinaryTripleShare],
) -> Result<Vec<u8>> {
    if triples.len() != plan.candidate_count {
        return Err(DealerlessPreprocessingError::CandidateUndersupply {
            have: triples.len(),
            need: plan.candidate_count,
        });
    }
    let mut bits = Vec::with_capacity(plan.mac_values as usize);
    for triple in triples.iter().copied() {
        bits.extend_from_slice(&triple.into_bits());
    }
    Ok(bits)
}

fn plan_digest(
    session: [u8; 32],
    roster: &[[u8; 32]],
    kept: usize,
    candidates: usize,
    mac_values: u32,
    batch: [u8; 64],
) -> Result<[u8; 64]> {
    let mut hash = domain_hash(PLAN_DOMAIN);
    hash.update(session);
    hash.update(batch);
    hash.update(checked_u64(roster.len())?.to_be_bytes());
    hash.update(checked_u64(kept)?.to_be_bytes());
    hash.update(checked_u64(candidates)?.to_be_bytes());
    hash.update(mac_values.to_be_bytes());
    for (party, id) in roster.iter().enumerate() {
        hash.update(checked_u64(party)?.to_be_bytes());
        hash.update(id);
    }
    Ok(hash.finalize().into())
}

fn candidate_context(plan: &DealerlessCeremonyPlan, certificate: &[u8]) -> [u8; 64] {
    let mut hash = domain_hash(CANDIDATE_CONTEXT_DOMAIN);
    hash.update(plan.digest);
    hash.update((certificate.len() as u64).to_be_bytes());
    hash.update(certificate);
    hash.finalize().into()
}

fn mac_binding(
    manifest: &DistributedMacManifest,
    certificate: &DistributedMacCertificate,
) -> [u8; 64] {
    let mut hash = domain_hash(MAC_BINDING_DOMAIN);
    hash.update(manifest.digest());
    hash.update(certificate.setup_root());
    hash.finalize().into()
}

fn checked_u64(value: usize) -> Result<u64> {
    u64::try_from(value).map_err(|_| DealerlessPreprocessingError::ArithmeticOverflow)
}
fn domain_hash(domain: &[u8]) -> Sha512 {
    let mut hash = Sha512::new();
    hash.update((domain.len() as u64).to_be_bytes());
    hash.update(domain);
    hash
}

#[cfg(test)]
mod tests {
    use std::process::Command;
    use std::time::Duration;

    use dregg_pq::MlDsaKey;
    use fhe::bfv::RelinearizationKey;
    use rand::{rngs::StdRng, SeedableRng};

    use super::*;
    use crate::distributed_bfv_correlation::{CorrelationCoordinator, EncryptedBitContribution};
    use crate::joint_beacon::prepare_commitment as prepare_beacon;
    use crate::mpc_distributed_mac::{generate_key_share, MacKeyShareCustody};
    use crate::threshold::relin::{generate_relinearization_key, RelinKeySession};
    use crate::threshold::{
        BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, ThresholdParty,
    };

    const BFV_CHILD_ENV: &str = "DREGG_FHTRI005_DEALERLESS_CHILD";

    struct BfvFixture {
        params: BfvParams,
        keygen: KeygenSession,
        dkg_wires: Vec<Vec<u8>>,
        collective: CollectivePublicKey,
        threshold_parties: Vec<ThresholdParty>,
        relin_session: RelinKeySession,
        relin_key: RelinearizationKey,
        signing_keys: Vec<MlDsaKey>,
    }

    fn bfv_fixture() -> BfvFixture {
        let params = BfvParams::correlation_set();
        let keygen = KeygenSession::from_seed(DISTRIBUTED_BFV_PARTIES, [0xa1; 32]).unwrap();
        let mut dkg_wires = Vec::new();
        let mut threshold_parties = Vec::new();
        let mut keygen_coordinator = KeygenCoordinator::new(keygen.clone(), params.clone());
        for party in 0..DISTRIBUTED_BFV_PARTIES {
            let (state, contribution) =
                ThresholdParty::join_seeded(&keygen, party, &params, &[0xb1 + party as u8; 32])
                    .unwrap();
            dkg_wires.push(contribution.to_wire_bytes());
            keygen_coordinator.accept(contribution).unwrap();
            threshold_parties.push(state);
        }
        let collective = keygen_coordinator.finish().unwrap();
        let relin_session = RelinKeySession::from_public_entropy(
            &keygen,
            &collective,
            [0xc1; 32],
            Duration::from_secs(120),
        )
        .unwrap();
        let relin_key =
            generate_relinearization_key(&relin_session, &params, &collective, &threshold_parties)
                .unwrap();
        let signing_keys = (0..DISTRIBUTED_BFV_PARTIES)
            .map(|party| MlDsaKey::from_ed25519_seed(&[0xd1 + party as u8; 32]))
            .collect();
        BfvFixture {
            params,
            keygen,
            dkg_wires,
            collective,
            threshold_parties,
            relin_session,
            relin_key,
            signing_keys,
        }
    }

    fn bfv_session(fx: &BfvFixture) -> CorrelationSession {
        CorrelationSession::new(
            [0xe1; 32],
            &fx.keygen,
            &fx.dkg_wires,
            &fx.collective,
            &fx.relin_session,
            &fx.relin_key,
            fx.signing_keys.iter().map(MlDsaKey::public_bytes).collect(),
            FHTRI005_CANDIDATES_PER_GATE,
            &fx.params,
        )
        .unwrap()
    }

    fn plan(tag: u8, triples: usize) -> Result<DealerlessCeremonyPlan> {
        DealerlessCeremonyPlan::build(
            [tag; 32],
            vec![[0x21; 32], [0x22; 32]],
            1,
            [0x31; 64],
            triples,
        )
    }
    fn round(tag: u8) -> CandidateCommitmentRound {
        let plan = plan(tag, FHTRI005_CANDIDATES_PER_GATE).unwrap();
        let cert = vec![tag; 401];
        let binding = SacrificeCommitmentBinding::new(
            candidate_context(&plan, &cert),
            plan.roster.clone(),
            1,
            plan.batch_binding,
        )
        .unwrap();
        CandidateCommitmentRound {
            plan,
            binding,
            correlation_certificate: cert,
        }
    }
    fn triples(party: usize, count: usize) -> Vec<BinaryTripleShare> {
        (0..count)
            .map(|i| {
                BinaryTripleShare::new(
                    ((i + party) & 1) as u8,
                    ((i / 2 + party) & 1) as u8,
                    ((i / 4 + party) & 1) as u8,
                )
                .unwrap()
            })
            .collect()
    }
    fn prepared(
        tag: u8,
    ) -> (
        CandidateCommitmentRound,
        DealerlessPartyCandidates,
        DealerlessPartyCandidates,
    ) {
        let round = round(tag);
        let p0 = round
            .prepare_from_parts(0, [0x41; 32], triples(0, 129))
            .unwrap();
        let p1 = round
            .prepare_from_parts(1, [0x42; 32], triples(1, 129))
            .unwrap();
        (round, p0, p1)
    }
    fn candidates(tag: u8) -> CandidatesCommitted {
        let (round, p0, p1) = prepared(tag);
        round
            .seal_messages(vec![p0.commitment(), p1.commitment()])
            .unwrap()
    }
    fn mac_keys(tag: u8) -> (MacKeysCommitted, Vec<MacKeyShareCustody>) {
        let candidates = candidates(tag);
        let mut rng = StdRng::seed_from_u64(tag as u64 + 1);
        let (k0, s0) = generate_key_share(candidates.mac_manifest(), 0, &mut rng).unwrap();
        let (k1, s1) = generate_key_share(candidates.mac_manifest(), 1, &mut rng).unwrap();
        (
            candidates.seal_mac_keys(vec![k0, k1]).unwrap(),
            vec![s0, s1],
        )
    }

    fn complete(
        tag: u8,
    ) -> (
        AwaitingCrossTermProvider,
        DealerlessPartyCandidates,
        DealerlessPartyCandidates,
        Vec<MacKeyShareCustody>,
    ) {
        let (round, p0, p1) = prepared(tag);
        let candidates = round
            .seal_messages(vec![p0.commitment(), p1.commitment()])
            .unwrap();
        let mut rng = StdRng::seed_from_u64(tag as u64 + 1);
        let (k0, s0) = generate_key_share(candidates.mac_manifest(), 0, &mut rng).unwrap();
        let (k1, s1) = generate_key_share(candidates.mac_manifest(), 1, &mut rng).unwrap();
        let public = candidates.seal_mac_keys(vec![k0, k1]).unwrap();
        let context = public.beacon_context().clone();
        let (c0, r0) = prepare_beacon(&context, 0, [0x61; 64]).unwrap();
        let (c1, r1) = prepare_beacon(&context, 1, [0x62; 64]).unwrap();
        let committed = public.seal_beacon_commitments(vec![c0, c1]).unwrap();
        let set = committed.commitment_set().clone();
        let final_state = committed
            .finalize_beacon(vec![r0.reveal(&set).unwrap(), r1.reveal(&set).unwrap()])
            .unwrap();
        (final_state, p0, p1, vec![s0, s1])
    }

    /// Exercise the production-only constructor and the real threshold-BFV
    /// output boundary in an isolated process.  The environment override is
    /// only the repository's explicit test acknowledgement for the fallback
    /// ML-DSA core; production still follows its verified-core install policy.
    #[test]
    fn real_threshold_bfv_batch_reaches_only_party_local_candidate_custody() {
        let status = Command::new(std::env::current_exe().unwrap())
            .arg("--exact")
            .arg("dealerless_preprocessing::tests::real_threshold_bfv_batch_dealerless_worker")
            .arg("--nocapture")
            .env(BFV_CHILD_ENV, "1")
            .env("DREGG_ALLOW_UNAUDITED_PQ", "1")
            .status()
            .unwrap();
        assert!(status.success(), "dealerless threshold-BFV worker failed");
    }

    #[test]
    fn real_threshold_bfv_batch_dealerless_worker() {
        if std::env::var_os(BFV_CHILD_ENV).is_none() {
            return;
        }
        assert_eq!(
            std::env::var_os("DREGG_ALLOW_UNAUDITED_PQ").as_deref(),
            Some(std::ffi::OsStr::new("1"))
        );
        let fx = bfv_fixture();
        let session = bfv_session(&fx);
        assert!(matches!(
            AwaitingCorrelationOpening::new(
                &session,
                &BfvParams::fold_set(),
                vec![[0xf1; 32], [0xf2; 32]],
                1,
                [0xf3; 64],
            ),
            Err(DealerlessPreprocessingError::InvalidParameters(_))
        ));
        let awaiting = AwaitingCorrelationOpening::new(
            &session,
            &fx.params,
            vec![[0xf1; 32], [0xf2; 32]],
            1,
            [0xf3; 64],
        )
        .unwrap();
        let n = FHTRI005_CANDIDATES_PER_GATE;
        let expand = |prefix: &[u8]| {
            let mut values = vec![0; n];
            values[..prefix.len()].copy_from_slice(prefix);
            values
        };
        let (state0, contribution0) = EncryptedBitContribution::prepare(
            &session,
            0,
            expand(&[0, 0, 1, 1, 0, 1, 0, 1]),
            expand(&[0, 1, 0, 1, 1, 0, 0, 1]),
            expand(&[0, 0, 1, 0, 1, 0, 1, 1]),
            &fx.params,
            &fx.collective,
            &fx.signing_keys[0],
        )
        .unwrap();
        let (state1, contribution1) = EncryptedBitContribution::prepare(
            &session,
            1,
            expand(&[0, 1, 0, 1, 1, 0, 1, 0]),
            expand(&[0, 0, 1, 1, 0, 1, 1, 0]),
            expand(&[0, 1, 0, 0, 1, 1, 0, 1]),
            &fx.params,
            &fx.collective,
            &fx.signing_keys[1],
        )
        .unwrap();
        let mut coordinator = CorrelationCoordinator::new(session.clone(), fx.params.clone());
        coordinator
            .accept_wire(contribution0.to_wire_bytes().unwrap())
            .unwrap();
        coordinator
            .accept_wire(contribution1.to_wire_bytes().unwrap())
            .unwrap();
        let pending = coordinator.finish(&fx.relin_key).unwrap();
        let shares = fx
            .threshold_parties
            .iter()
            .map(|party| pending.decryption_share(party).unwrap())
            .collect();
        let opened = pending.open(shares).unwrap();
        let output0 = state0.derive_output(&opened, [0x91; 32]).unwrap();
        let output1 = state1.derive_output(&opened, [0x92; 32]).unwrap();
        let commitments = [output0.commitment(), output1.commitment()];
        let (correlated, transcript) = awaiting
            .seal_correlation(&session, opened, commitments)
            .unwrap();
        transcript
            .verify(&session, &fx.params, &fx.relin_key)
            .unwrap();

        // These calls are the party-process boundary in production.  The
        // public coordinator receives only the two returned commitments.
        let local0 = correlated.prepare_party_candidates(0, output0).unwrap();
        let local1 = correlated.prepare_party_candidates(1, output1).unwrap();
        let candidates = correlated
            .seal_candidate_messages(vec![local0.commitment(), local1.commitment()])
            .unwrap();
        assert_eq!(candidates.candidate_manifest().gates(), 1);
        assert_eq!(
            candidates.candidate_manifest().rounds(),
            BINARY_SACRIFICE_SECURITY_BITS
        );
        assert_eq!(
            candidates.mac_manifest().values(),
            (FHTRI005_CANDIDATES_PER_GATE * FHTRI005_BITS_PER_CANDIDATE) as u32
        );
    }

    #[test]
    fn exact_129_geometry_refuses_undersupply() {
        assert!(matches!(
            plan(0x11, 128),
            Err(DealerlessPreprocessingError::CandidateUndersupply {
                have: 128,
                need: 129
            })
        ));
        assert!(matches!(
            round(0x11).prepare_from_parts(0, [0x41; 32], triples(0, 128)),
            Err(DealerlessPreprocessingError::CandidateUndersupply { .. })
        ));
    }

    #[test]
    fn candidate_barrier_refuses_omission_reorder_and_replay() {
        let (active_round, p0, p1) = prepared(0x11);
        assert!(matches!(
            round(0x11).seal_messages(vec![p0.commitment()]),
            Err(DealerlessPreprocessingError::Sacrifice(
                BinarySacrificeError::IncompleteRoster { have: 1, need: 2 }
            ))
        ));
        assert!(matches!(
            round(0x11).seal_messages(vec![p1.commitment(), p0.commitment()]),
            Err(DealerlessPreprocessingError::Sacrifice(
                BinarySacrificeError::ReorderedParty { .. }
            ))
        ));
        let replay = round(0x12)
            .prepare_from_parts(0, [0x41; 32], triples(0, 129))
            .unwrap();
        assert!(matches!(
            active_round.seal_messages(vec![replay.commitment(), p1.commitment()]),
            Err(DealerlessPreprocessingError::Sacrifice(
                BinarySacrificeError::ManifestMismatch
            ))
        ));
    }

    #[test]
    fn conflicting_complete_views_are_equivocation() {
        let (round, p0, p1) = prepared(0x11);
        let alt0 = round
            .prepare_from_parts(0, [0x51; 32], triples(0, 129))
            .unwrap();
        let first = CandidateCommitmentRound {
            plan: round.plan.clone(),
            binding: round.binding.clone(),
            correlation_certificate: round.correlation_certificate.clone(),
        }
        .seal_messages(vec![p0.commitment(), p1.commitment()])
        .unwrap();
        let second = round
            .seal_messages(vec![alt0.commitment(), p1.commitment()])
            .unwrap();
        assert!(matches!(
            first.ensure_same_view(&second),
            Err(DealerlessPreprocessingError::Sacrifice(
                BinarySacrificeError::Equivocation
            ))
        ));
    }

    #[test]
    fn mac_and_beacon_barriers_refuse_omission_and_reorder() {
        let candidates = candidates(0x11);
        let mut rng = StdRng::seed_from_u64(9);
        let (k0, _s0) = generate_key_share(candidates.mac_manifest(), 0, &mut rng).unwrap();
        assert!(matches!(
            candidates.seal_mac_keys(vec![k0]),
            Err(DealerlessPreprocessingError::DistributedMac(
                DistributedMacError::ShapeMismatch
            ))
        ));

        let (public, _keys) = mac_keys(0x12);
        let context = public.beacon_context().clone();
        let (c0, _) = prepare_beacon(&context, 0, [0x61; 64]).unwrap();
        assert!(matches!(
            public.seal_beacon_commitments(vec![c0]),
            Err(DealerlessPreprocessingError::JointBeacon(
                JointBeaconError::IncompleteRoster { have: 1, need: 2 }
            ))
        ));

        let (public, _keys) = mac_keys(0x13);
        let context = public.beacon_context().clone();
        let (c0, _) = prepare_beacon(&context, 0, [0x61; 64]).unwrap();
        let (c1, _) = prepare_beacon(&context, 1, [0x62; 64]).unwrap();
        assert!(matches!(
            public.seal_beacon_commitments(vec![c1, c0]),
            Err(DealerlessPreprocessingError::JointBeacon(
                JointBeaconError::ReorderedParty { .. }
            ))
        ));

        let (public, _keys) = mac_keys(0x14);
        let context = public.beacon_context().clone();
        let (c0, r0) = prepare_beacon(&context, 0, [0x61; 64]).unwrap();
        let (c1, _r1) = prepare_beacon(&context, 1, [0x62; 64]).unwrap();
        let committed = public.seal_beacon_commitments(vec![c0, c1]).unwrap();
        let set = committed.commitment_set().clone();
        assert!(matches!(
            committed.finalize_beacon(vec![r0.reveal(&set).unwrap()]),
            Err(DealerlessPreprocessingError::JointBeacon(
                JointBeaconError::IncompleteRoster { have: 1, need: 2 }
            ))
        ));
    }

    #[test]
    fn complete_state_stops_at_exact_cross_term_requirement() {
        let (final_state, _p0, _p1, _keys) = complete(0x15);
        let need = final_state.cross_term_requirement();
        assert_eq!(need.parties, 2);
        assert_eq!(need.values_per_party, 129 * 3);
        assert_eq!(need.mac_lanes, 2);
        assert_eq!(need.ordered_pair_batches, 2);
        assert_ne!(final_state.beacon().beacon(), [0; 64]);
    }

    #[test]
    fn party_local_rows_and_committed_mac_keys_rejoin_only_at_the_typed_seam() {
        let (final_state, p0, p1, mut keys) = complete(0x16);
        let key0 = keys.remove(0);
        let key1 = keys.remove(0);
        let local0 = p0.bind_awaiting_cross_terms(&final_state, key0).unwrap();
        let local1 = p1.bind_awaiting_cross_terms(&final_state, key1).unwrap();
        assert_eq!(local0.party(), 0);
        assert_eq!(local1.party(), 1);
        let (_row0, _key0, _builder0) = local0.into_parts();
        let (_row1, _key1, _builder1) = local1.into_parts();
    }

    #[test]
    fn party_local_seam_refuses_an_uncommitted_mac_key() {
        let (final_state, p0, _p1, _keys) = complete(0x17);
        let mut rng = StdRng::seed_from_u64(0xdead_beef);
        let (_wrong_public, wrong_key) =
            generate_key_share(final_state.mac_certificate().manifest(), 0, &mut rng).unwrap();
        assert!(matches!(
            p0.bind_awaiting_cross_terms(&final_state, wrong_key),
            Err(DealerlessPreprocessingError::DistributedMac(
                DistributedMacError::ContextMismatch
            ))
        ));
    }
}
