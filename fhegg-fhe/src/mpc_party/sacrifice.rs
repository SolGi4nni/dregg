//! Committed-candidate sacrifice for binary Beaver triples.
//!
//! The bare protocol remains available as an algebraic reference.  The live
//! `FHTRI004` custody path composes it with [`super::authenticated_bits`] before
//! releasing a kept row.  The two layers intentionally remain separate so the
//! unauthenticated failure mode stays executable rather than disappearing
//! behind the hardened adapter.
//!
//! 1. each party locally commits its kept and sacrificial GF(2) share row and
//!    sends only a public [`CandidateCommitmentMessage`];
//! 2. derive 128 challenge bits per kept gate from a beacon supplied only after
//!    the commitment is fixed;
//! 3. open `rho = r*a + f` and `sigma = b + g`;
//! 4. open check shares whose XOR, plus `rho*sigma`, is exactly
//!    `r*(c+a*b) + (h+f*g)`.
//!
//! All arithmetic is GF(2), so one sacrifice contributes exactly one bit of
//! soundness. The fixed 128 rounds are deliberate; a single binary challenge
//! is not a meaningful malicious-preprocessing check. SHA-512 binds rows and
//! the manifest. Challenge expansion is SHA-512 in a counter mode and is
//! modeled as unpredictable only when the beacon is unpredictable after the
//! manifest root exists.
//!
//! # Exact trust boundary
//!
//! The commitment barrier is genuinely party-local: [`prepare_candidate_commitment`]
//! consumes one secret row into an opaque pending value, while
//! [`seal_candidate_commitments`] receives only fixed-width public commitments.
//! [`VerifiedSacrificeBatch::release_party`] likewise consumes one material at
//! its owning party. No coordinator API in that path accepts a collection of
//! secret candidate rows. The older
//! [`commit_candidate_rows`] helper remains as a clearly labeled compatibility
//! delegator for tests and the not-yet-cut-over FHTRI004 ceremony.
//!
//! This protects against malformed, precommitted candidate correlations when
//! the party response code is honest. It is not malicious MPC yet. Response
//! shares are not authenticated shares/MACs and carry no ZK proof that a party
//! computed them from its committed row. A lying party can therefore forge a
//! check share and force acceptance; `lying_check_share_can_force_acceptance_without_authentication`
//! keeps that residual executable. The live cutover must compose a MAC/ZK
//! response-authority layer, an independently authenticated post-commit beacon,
//! and one-time custody before `SacrificedPartyRow` can feed PartyMPC gates.

use std::fmt;

use sha2::{Digest, Sha512};

use super::authenticated_bits::VerifiedAuthenticatedOpening;

/// Statistical soundness target for binary sacrifice. Each round contributes
/// one bit under an unpredictable post-commit challenge.
pub const BINARY_SACRIFICE_SECURITY_BITS: usize = 128;

/// Allocation ceiling across kept and sacrificial triples in one committed
/// batch. This is a preprocessing DoS bound, not a cryptographic parameter.
pub const MAX_BINARY_SACRIFICE_TRIPLES: usize = 16 * 1024 * 1024;

const BINDING_DOMAIN: &[u8] = b"fhegg/party-mpc/binary-sacrifice-binding/v2";
const ROSTER_DOMAIN: &[u8] = b"fhegg/party-mpc/binary-sacrifice-roster/v2";
const ROW_DOMAIN: &[u8] = b"fhegg/party-mpc/binary-sacrifice-row/v2";
const MANIFEST_DOMAIN: &[u8] = b"fhegg/party-mpc/binary-sacrifice-manifest/v2";
const LEGACY_IDENTITY_DOMAIN: &[u8] = b"fhegg/party-mpc/binary-sacrifice-legacy-identity/v2";
const LEGACY_BATCH_DOMAIN: &[u8] = b"fhegg/party-mpc/binary-sacrifice-legacy-batch/v2";
const CHALLENGE_DOMAIN: &[u8] = b"fhegg/party-mpc/binary-sacrifice-challenge/v1";
const CHALLENGE_DIGEST_DOMAIN: &[u8] = b"fhegg/party-mpc/binary-sacrifice-challenge-digest/v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BinarySacrificeError {
    InvalidParameters(&'static str),
    ShapeMismatch,
    InvalidParty { party: usize, n_parties: usize },
    IncompleteRoster { have: usize, need: usize },
    DuplicateParty { party: usize },
    ReorderedParty { position: usize, party: usize },
    Equivocation,
    CommitmentMismatch { party: usize },
    ManifestMismatch,
    ChallengeMismatch,
    AuthenticationMismatch,
    CheckRejected { gate: usize, round: usize },
    ArithmeticOverflow,
}

impl fmt::Display for BinarySacrificeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "binary triple sacrifice error: {self:?}")
    }
}

impl std::error::Error for BinarySacrificeError {}

pub type Result<T> = std::result::Result<T, BinarySacrificeError>;

/// One party's additive share of a binary Beaver candidate. Fields stay
/// private so ordinary logs cannot accidentally disclose preprocessing.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct BinaryTripleShare {
    a: u8,
    b: u8,
    c: u8,
}

impl BinaryTripleShare {
    pub fn new(a: u8, b: u8, c: u8) -> Result<Self> {
        if a > 1 || b > 1 || c > 1 {
            return Err(BinarySacrificeError::InvalidParameters(
                "binary triple shares must be canonical bits",
            ));
        }
        Ok(Self { a, b, c })
    }

    /// Consume the row-owned value at the future party-local adapter boundary.
    /// These are secret shares, never coordinator/public transcript material.
    pub fn into_bits(self) -> [u8; 3] {
        [self.a, self.b, self.c]
    }
}

/// One party's pre-challenge row: one kept candidate per gate and exactly 128
/// sacrificial candidates per kept candidate, stored gate-major.
pub struct SacrificeCandidateRow {
    party: usize,
    kept: Vec<BinaryTripleShare>,
    sacrificed: Vec<BinaryTripleShare>,
}

impl SacrificeCandidateRow {
    pub fn new(
        party: usize,
        kept: Vec<BinaryTripleShare>,
        sacrificed: Vec<BinaryTripleShare>,
    ) -> Result<Self> {
        if kept.is_empty() {
            return Err(BinarySacrificeError::InvalidParameters(
                "sacrifice requires at least one kept gate",
            ));
        }
        let expected = kept
            .len()
            .checked_mul(BINARY_SACRIFICE_SECURITY_BITS)
            .ok_or(BinarySacrificeError::ArithmeticOverflow)?;
        if sacrificed.len() != expected {
            return Err(BinarySacrificeError::ShapeMismatch);
        }
        Ok(Self {
            party,
            kept,
            sacrificed,
        })
    }

    pub fn party(&self) -> usize {
        self.party
    }

    pub fn gates(&self) -> usize {
        self.kept.len()
    }
}

/// Exact public definition of one candidate-commitment ceremony.
///
/// The ordered roster is retained, not merely its digest. `batch_binding` must
/// name the one preprocessing batch/session attempt; callers must not reuse it
/// to reroll after a beacon abort.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SacrificeCommitmentBinding {
    context: [u8; 64],
    roster: Vec<[u8; 32]>,
    roster_digest: [u8; 64],
    gates: usize,
    batch_binding: [u8; 64],
    digest: [u8; 64],
}

impl SacrificeCommitmentBinding {
    pub fn new(
        context: [u8; 64],
        roster: Vec<[u8; 32]>,
        gates: usize,
        batch_binding: [u8; 64],
    ) -> Result<Self> {
        validate_commitment_shape(context, &roster, gates, batch_binding)?;
        let roster_digest = sacrifice_roster_digest(&roster)?;
        let digest =
            sacrifice_binding_digest(context, &roster, roster_digest, gates, batch_binding)?;
        Ok(Self {
            context,
            roster,
            roster_digest,
            gates,
            batch_binding,
            digest,
        })
    }

    pub fn context(&self) -> [u8; 64] {
        self.context
    }

    pub fn roster(&self) -> &[[u8; 32]] {
        &self.roster
    }

    pub fn roster_digest(&self) -> [u8; 64] {
        self.roster_digest
    }

    pub fn n_parties(&self) -> usize {
        self.roster.len()
    }

    pub fn gates(&self) -> usize {
        self.gates
    }

    pub fn batch_binding(&self) -> [u8; 64] {
        self.batch_binding
    }

    pub fn digest(&self) -> [u8; 64] {
        self.digest
    }
}

/// Public fixed-shape message emitted by one party after its secret candidate
/// row has entered local pending custody.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CandidateCommitmentMessage {
    binding_digest: [u8; 64],
    roster_digest: [u8; 64],
    batch_binding: [u8; 64],
    party: usize,
    identity: [u8; 32],
    gates: usize,
    rounds: usize,
    commitment: [u8; 64],
}

impl CandidateCommitmentMessage {
    pub fn binding_digest(&self) -> [u8; 64] {
        self.binding_digest
    }

    pub fn party(&self) -> usize {
        self.party
    }

    pub fn identity(&self) -> [u8; 32] {
        self.identity
    }

    pub fn gates(&self) -> usize {
        self.gates
    }

    pub fn commitment(&self) -> [u8; 64] {
        self.commitment
    }
}

/// Party-local secret row waiting for a complete public commitment barrier.
/// It intentionally implements neither `Clone` nor `Debug`.
pub struct PendingCandidateCommitment {
    binding_digest: [u8; 64],
    roster_digest: [u8; 64],
    batch_binding: [u8; 64],
    identity: [u8; 32],
    commitment: [u8; 64],
    row_salt: [u8; 32],
    row: SacrificeCandidateRow,
}

/// Public binding of all candidate rows before the beacon is sampled.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommittedSacrificeBatch {
    context: [u8; 64],
    binding_digest: [u8; 64],
    roster: Vec<[u8; 32]>,
    roster_digest: [u8; 64],
    batch_binding: [u8; 64],
    n_parties: usize,
    gates: usize,
    row_commitments: Vec<[u8; 64]>,
    root: [u8; 64],
}

impl CommittedSacrificeBatch {
    pub fn context(&self) -> [u8; 64] {
        self.context
    }

    pub fn binding_digest(&self) -> [u8; 64] {
        self.binding_digest
    }

    pub fn roster(&self) -> &[[u8; 32]] {
        &self.roster
    }

    pub fn roster_digest(&self) -> [u8; 64] {
        self.roster_digest
    }

    pub fn batch_binding(&self) -> [u8; 64] {
        self.batch_binding
    }

    pub fn n_parties(&self) -> usize {
        self.n_parties
    }

    pub fn gates(&self) -> usize {
        self.gates
    }

    pub fn rounds(&self) -> usize {
        BINARY_SACRIFICE_SECURITY_BITS
    }

    pub fn row_commitments(&self) -> &[[u8; 64]] {
        &self.row_commitments
    }

    pub fn root(&self) -> [u8; 64] {
        self.root
    }
}

/// Opaque party custody for one committed candidate row.
pub struct PartySacrificeMaterial {
    manifest_root: [u8; 64],
    context: [u8; 64],
    binding_digest: [u8; 64],
    roster_digest: [u8; 64],
    batch_binding: [u8; 64],
    identity: [u8; 32],
    row_salt: [u8; 32],
    row: SacrificeCandidateRow,
}

/// Challenge vector bound to one manifest and one post-commit beacon.
#[derive(Clone, PartialEq, Eq)]
pub struct SacrificeChallenge {
    manifest_root: [u8; 64],
    digest: [u8; 64],
    bits: Vec<u8>,
}

impl SacrificeChallenge {
    pub fn derive(manifest: &CommittedSacrificeBatch, beacon: [u8; 64]) -> Result<Self> {
        if beacon == [0; 64] {
            return Err(BinarySacrificeError::InvalidParameters(
                "post-commit beacon must be nonzero",
            ));
        }
        let bit_count = manifest
            .gates
            .checked_mul(BINARY_SACRIFICE_SECURITY_BITS)
            .ok_or(BinarySacrificeError::ArithmeticOverflow)?;
        let mut bits = Vec::with_capacity(bit_count);
        let mut counter = 0u64;
        while bits.len() < bit_count {
            let mut hash = Sha512::new();
            hash.update(canonical_domain(CHALLENGE_DOMAIN));
            hash.update(manifest.context);
            hash.update(manifest.root);
            hash.update(beacon);
            hash.update(counter.to_be_bytes());
            for byte in hash.finalize() {
                for shift in 0..8 {
                    if bits.len() == bit_count {
                        break;
                    }
                    bits.push((byte >> shift) & 1);
                }
            }
            counter = counter
                .checked_add(1)
                .ok_or(BinarySacrificeError::ArithmeticOverflow)?;
        }
        let mut digest = Sha512::new();
        digest.update(canonical_domain(CHALLENGE_DIGEST_DOMAIN));
        digest.update(manifest.root);
        digest.update(beacon);
        digest.update(checked_u64(bit_count)?.to_be_bytes());
        digest.update(&bits);
        Ok(Self {
            manifest_root: manifest.root,
            digest: digest.finalize().into(),
            bits,
        })
    }

    pub fn digest(&self) -> [u8; 64] {
        self.digest
    }

    pub fn soundness_bits(&self) -> usize {
        BINARY_SACRIFICE_SECURITY_BITS
    }

    /// Public challenge bit used by the authenticated-response adapter.  The
    /// manifest dimensions remain part of validation; callers cannot index a
    /// challenge under another batch shape.
    pub fn bit_at(
        &self,
        manifest: &CommittedSacrificeBatch,
        gate: usize,
        round: usize,
    ) -> Result<u8> {
        validate_challenge(manifest, self)?;
        self.bit(gate, round, manifest.gates)
    }

    fn bit(&self, gate: usize, round: usize, gates: usize) -> Result<u8> {
        let expected = gates
            .checked_mul(BINARY_SACRIFICE_SECURITY_BITS)
            .ok_or(BinarySacrificeError::ArithmeticOverflow)?;
        if self.bits.len() != expected || gate >= gates || round >= BINARY_SACRIFICE_SECURITY_BITS {
            return Err(BinarySacrificeError::ShapeMismatch);
        }
        Ok(self.bits[flat_index(gate, round)?])
    }
}

/// Unauthenticated first-round message. A production network must authenticate
/// both its sender and its derivation from committed shares.
pub struct SacrificeOpeningShare {
    manifest_root: [u8; 64],
    challenge_digest: [u8; 64],
    party: usize,
    rho: Vec<u8>,
    sigma: Vec<u8>,
}

/// Reconstructed masked values after an exact full-party first round.
pub struct OpenedSacrificeMasks {
    manifest_root: [u8; 64],
    challenge_digest: [u8; 64],
    rho: Vec<u8>,
    sigma: Vec<u8>,
}

/// Unauthenticated second-round message. This is the remaining active-security
/// seam: algebra alone cannot prove that a peer computed this from its row.
pub struct SacrificeCheckShare {
    manifest_root: [u8; 64],
    challenge_digest: [u8; 64],
    party: usize,
    tau: Vec<u8>,
}

/// Opaque capability issued only after every amplified check accepts.
pub struct VerifiedSacrificeBatch {
    manifest_root: [u8; 64],
    context: [u8; 64],
    n_parties: usize,
    gates: usize,
}

impl VerifiedSacrificeBatch {
    pub fn manifest_root(&self) -> [u8; 64] {
        self.manifest_root
    }

    pub fn soundness_bits(&self) -> usize {
        BINARY_SACRIFICE_SECURITY_BITS
    }

    /// Release one party's kept row at that party. The verified capability is
    /// public ceremony state; the secret material is consumed locally and is
    /// never gathered into a coordinator vector on this path.
    pub fn release_party(
        &self,
        manifest: &CommittedSacrificeBatch,
        material: PartySacrificeMaterial,
    ) -> Result<SacrificedPartyRow> {
        validate_manifest_capability(
            manifest,
            self.manifest_root,
            self.context,
            self.n_parties,
            self.gates,
        )?;
        let party = material.row.party;
        validate_material(manifest, &material, party)?;
        Ok(SacrificedPartyRow {
            manifest_root: manifest.root,
            party,
            triples: material.row.kept,
        })
    }

    /// Legacy centralized compatibility release. Distributed callers should
    /// call [`Self::release_party`] independently at every party instead of
    /// collecting secret material in one process.
    pub fn release(
        self,
        manifest: &CommittedSacrificeBatch,
        materials: Vec<PartySacrificeMaterial>,
    ) -> Result<Vec<SacrificedPartyRow>> {
        validate_manifest_capability(
            manifest,
            self.manifest_root,
            self.context,
            self.n_parties,
            self.gates,
        )?;
        if materials.len() != manifest.n_parties {
            return Err(BinarySacrificeError::ShapeMismatch);
        }
        let mut survivors = Vec::with_capacity(materials.len());
        for material in materials {
            survivors.push(self.release_party(manifest, material)?);
            // `material.row.sacrificed` and the salt are dropped here.
        }
        Ok(survivors)
    }
}

/// Party-owned surviving kept row. It deliberately implements neither `Clone`
/// nor `Debug`; conversion consumes the wrapper at a local custody boundary.
pub struct SacrificedPartyRow {
    manifest_root: [u8; 64],
    party: usize,
    triples: Vec<BinaryTripleShare>,
}

impl SacrificedPartyRow {
    pub fn manifest_root(&self) -> [u8; 64] {
        self.manifest_root
    }

    pub fn party(&self) -> usize {
        self.party
    }

    pub fn gates(&self) -> usize {
        self.triples.len()
    }

    pub fn into_triples(self) -> Vec<BinaryTripleShare> {
        self.triples
    }
}

/// Commit one party's candidate row without disclosing it to the coordinator.
/// The returned pending value remains at that party until a complete manifest
/// has been sealed from public messages only.
pub fn prepare_candidate_commitment(
    binding: &SacrificeCommitmentBinding,
    row: SacrificeCandidateRow,
    row_salt: [u8; 32],
) -> Result<(CandidateCommitmentMessage, PendingCandidateCommitment)> {
    if row.party >= binding.n_parties() {
        return Err(BinarySacrificeError::InvalidParty {
            party: row.party,
            n_parties: binding.n_parties(),
        });
    }
    if row.gates() != binding.gates || row_salt == [0; 32] {
        return Err(BinarySacrificeError::ShapeMismatch);
    }
    let identity = binding.roster[row.party];
    let commitment = candidate_row_commitment(binding, &row, row_salt)?;
    let message = CandidateCommitmentMessage {
        binding_digest: binding.digest,
        roster_digest: binding.roster_digest,
        batch_binding: binding.batch_binding,
        party: row.party,
        identity,
        gates: binding.gates,
        rounds: BINARY_SACRIFICE_SECURITY_BITS,
        commitment,
    };
    let pending = PendingCandidateCommitment {
        binding_digest: binding.digest,
        roster_digest: binding.roster_digest,
        batch_binding: binding.batch_binding,
        identity,
        commitment,
        row_salt,
        row,
    };
    Ok((message, pending))
}

/// Seal exactly one public commitment from every roster member, in exact roster
/// order. This function has no parameter through which secret candidate rows
/// can enter the coordinator.
pub fn seal_candidate_commitments(
    binding: &SacrificeCommitmentBinding,
    messages: &[CandidateCommitmentMessage],
) -> Result<CommittedSacrificeBatch> {
    validate_commitment_message_order(binding.n_parties(), messages)?;
    let mut row_commitments = Vec::with_capacity(binding.n_parties());
    for (party, message) in messages.iter().enumerate() {
        if message.binding_digest != binding.digest
            || message.roster_digest != binding.roster_digest
            || message.batch_binding != binding.batch_binding
            || message.identity != binding.roster[party]
            || message.gates != binding.gates
            || message.rounds != BINARY_SACRIFICE_SECURITY_BITS
            || message.commitment == [0; 64]
        {
            return Err(BinarySacrificeError::ManifestMismatch);
        }
        row_commitments.push(message.commitment);
    }
    let root = manifest_root(binding, &row_commitments)?;
    Ok(CommittedSacrificeBatch {
        context: binding.context,
        binding_digest: binding.digest,
        roster: binding.roster.clone(),
        roster_digest: binding.roster_digest,
        batch_binding: binding.batch_binding,
        n_parties: binding.n_parties(),
        gates: binding.gates,
        row_commitments,
        root,
    })
}

/// Refuse conflicting complete public views for one exact commitment context.
/// Authenticated reliable broadcast remains the caller's responsibility.
pub fn ensure_same_candidate_manifest(
    binding: &SacrificeCommitmentBinding,
    left: &CommittedSacrificeBatch,
    right: &CommittedSacrificeBatch,
) -> Result<()> {
    validate_manifest_binding(binding, left)?;
    validate_manifest_binding(binding, right)?;
    if left != right {
        return Err(BinarySacrificeError::Equivocation);
    }
    Ok(())
}

impl PendingCandidateCommitment {
    /// Consume party-local pending custody into the exact complete manifest
    /// that contains its public commitment.
    pub fn bind_to_manifest(
        self,
        binding: &SacrificeCommitmentBinding,
        manifest: &CommittedSacrificeBatch,
    ) -> Result<PartySacrificeMaterial> {
        validate_manifest_binding(binding, manifest)?;
        let party = self.row.party;
        if party >= manifest.n_parties
            || self.binding_digest != binding.digest
            || self.roster_digest != binding.roster_digest
            || self.batch_binding != binding.batch_binding
            || self.identity != binding.roster[party]
            || self.commitment != manifest.row_commitments[party]
        {
            return Err(BinarySacrificeError::CommitmentMismatch { party });
        }
        let expected = candidate_row_commitment(binding, &self.row, self.row_salt)?;
        if expected != self.commitment {
            return Err(BinarySacrificeError::CommitmentMismatch { party });
        }
        Ok(PartySacrificeMaterial {
            manifest_root: manifest.root,
            context: binding.context,
            binding_digest: binding.digest,
            roster_digest: binding.roster_digest,
            batch_binding: binding.batch_binding,
            identity: self.identity,
            row_salt: self.row_salt,
            row: self.row,
        })
    }
}

/// Legacy centralized compatibility helper. New distributed callers must use
/// [`prepare_candidate_commitment`] at each party and send only
/// [`CandidateCommitmentMessage`] to [`seal_candidate_commitments`].
pub fn commit_candidate_rows(
    context: [u8; 64],
    rows: Vec<SacrificeCandidateRow>,
    salts: Vec<[u8; 32]>,
) -> Result<(CommittedSacrificeBatch, Vec<PartySacrificeMaterial>)> {
    if rows.len() < 2 || rows.len() != salts.len() {
        return Err(BinarySacrificeError::ShapeMismatch);
    }
    let gates = rows[0].gates();
    let roster = legacy_roster(context, rows.len())?;
    let batch_binding = legacy_batch_binding(context, rows.len(), gates)?;
    let binding = SacrificeCommitmentBinding::new(context, roster, gates, batch_binding)?;
    let mut messages = Vec::with_capacity(rows.len());
    let mut pending = Vec::with_capacity(rows.len());
    for (row, salt) in rows.into_iter().zip(salts) {
        let (message, local) = prepare_candidate_commitment(&binding, row, salt)?;
        messages.push(message);
        pending.push(local);
    }
    let manifest = seal_candidate_commitments(&binding, &messages)?;
    let materials = pending
        .into_iter()
        .map(|local| local.bind_to_manifest(&binding, &manifest))
        .collect::<Result<Vec<_>>>()?;
    Ok((manifest, materials))
}

impl PartySacrificeMaterial {
    pub fn opening_share(
        &self,
        manifest: &CommittedSacrificeBatch,
        challenge: &SacrificeChallenge,
    ) -> Result<SacrificeOpeningShare> {
        validate_material(manifest, self, self.row.party)?;
        validate_challenge(manifest, challenge)?;
        let entries = manifest
            .gates
            .checked_mul(BINARY_SACRIFICE_SECURITY_BITS)
            .ok_or(BinarySacrificeError::ArithmeticOverflow)?;
        let mut rho = Vec::with_capacity(entries);
        let mut sigma = Vec::with_capacity(entries);
        for gate in 0..manifest.gates {
            let kept = self.row.kept[gate];
            for round in 0..BINARY_SACRIFICE_SECURITY_BITS {
                let sacrificial = self.row.sacrificed[flat_index(gate, round)?];
                let r = challenge.bit(gate, round, manifest.gates)?;
                rho.push((r & kept.a) ^ sacrificial.a);
                sigma.push(kept.b ^ sacrificial.b);
            }
        }
        Ok(SacrificeOpeningShare {
            manifest_root: manifest.root,
            challenge_digest: challenge.digest,
            party: self.row.party,
            rho,
            sigma,
        })
    }

    pub fn check_share(
        &self,
        manifest: &CommittedSacrificeBatch,
        challenge: &SacrificeChallenge,
        opened: &OpenedSacrificeMasks,
    ) -> Result<SacrificeCheckShare> {
        validate_material(manifest, self, self.row.party)?;
        validate_challenge(manifest, challenge)?;
        validate_opened(manifest, challenge, opened)?;
        let mut tau = Vec::with_capacity(opened.rho.len());
        for gate in 0..manifest.gates {
            let kept = self.row.kept[gate];
            for round in 0..BINARY_SACRIFICE_SECURITY_BITS {
                let index = flat_index(gate, round)?;
                let sacrificial = self.row.sacrificed[index];
                let r = challenge.bit(gate, round, manifest.gates)?;
                tau.push(
                    (r & kept.c)
                        ^ sacrificial.c
                        ^ (opened.sigma[index] & sacrificial.a)
                        ^ (opened.rho[index] & sacrificial.b),
                );
            }
        }
        Ok(SacrificeCheckShare {
            manifest_root: manifest.root,
            challenge_digest: challenge.digest,
            party: self.row.party,
            tau,
        })
    }
}

/// Reconstruct exact first-round masked openings from every party.
pub fn aggregate_openings(
    manifest: &CommittedSacrificeBatch,
    challenge: &SacrificeChallenge,
    openings: &[SacrificeOpeningShare],
) -> Result<OpenedSacrificeMasks> {
    validate_challenge(manifest, challenge)?;
    if openings.len() != manifest.n_parties {
        return Err(BinarySacrificeError::ShapeMismatch);
    }
    let entries = manifest
        .gates
        .checked_mul(BINARY_SACRIFICE_SECURITY_BITS)
        .ok_or(BinarySacrificeError::ArithmeticOverflow)?;
    let mut rho = vec![0u8; entries];
    let mut sigma = vec![0u8; entries];
    for (party, opening) in openings.iter().enumerate() {
        if opening.party != party {
            return Err(BinarySacrificeError::InvalidParty {
                party: opening.party,
                n_parties: manifest.n_parties,
            });
        }
        if opening.manifest_root != manifest.root
            || opening.challenge_digest != challenge.digest
            || opening.rho.len() != entries
            || opening.sigma.len() != entries
            || opening.rho.iter().chain(&opening.sigma).any(|bit| *bit > 1)
        {
            return Err(BinarySacrificeError::ManifestMismatch);
        }
        for index in 0..entries {
            rho[index] ^= opening.rho[index];
            sigma[index] ^= opening.sigma[index];
        }
    }
    Ok(OpenedSacrificeMasks {
        manifest_root: manifest.root,
        challenge_digest: challenge.digest,
        rho,
        sigma,
    })
}

/// Verify every amplified equation and issue an opaque release capability.
pub fn verify_check_shares(
    manifest: &CommittedSacrificeBatch,
    challenge: &SacrificeChallenge,
    opened: &OpenedSacrificeMasks,
    checks: &[SacrificeCheckShare],
) -> Result<VerifiedSacrificeBatch> {
    validate_challenge(manifest, challenge)?;
    validate_opened(manifest, challenge, opened)?;
    if checks.len() != manifest.n_parties {
        return Err(BinarySacrificeError::ShapeMismatch);
    }
    let entries = opened.rho.len();
    let mut tau = vec![0u8; entries];
    for (party, check) in checks.iter().enumerate() {
        if check.party != party {
            return Err(BinarySacrificeError::InvalidParty {
                party: check.party,
                n_parties: manifest.n_parties,
            });
        }
        if check.manifest_root != manifest.root
            || check.challenge_digest != challenge.digest
            || check.tau.len() != entries
            || check.tau.iter().any(|bit| *bit > 1)
        {
            return Err(BinarySacrificeError::ManifestMismatch);
        }
        for (aggregate, share) in tau.iter_mut().zip(&check.tau) {
            *aggregate ^= *share;
        }
    }
    for gate in 0..manifest.gates {
        for round in 0..BINARY_SACRIFICE_SECURITY_BITS {
            let index = flat_index(gate, round)?;
            let reconstructed = tau[index] ^ (opened.rho[index] & opened.sigma[index]);
            if reconstructed != 0 {
                return Err(BinarySacrificeError::CheckRejected { gate, round });
            }
        }
    }
    Ok(VerifiedSacrificeBatch {
        manifest_root: manifest.root,
        context: manifest.context,
        n_parties: manifest.n_parties,
        gates: manifest.gates,
    })
}

/// Verify the sacrifice equations from two already-MAC-verified public
/// openings.  `masks` is exactly `rho || sigma`; `checks` is exactly `tau`.
/// Both must descend from the same authenticated candidate setup.
///
/// This closes the executable lying-check-share hole in the live adapter under
/// the authenticated-opening module's explicit trusted-setup and one-honest-
/// party premises.  It does not turn the bare [`SacrificeCheckShare`] API into
/// a malicious-secure protocol and does not claim dealer-free preprocessing.
pub fn verify_authenticated_openings(
    manifest: &CommittedSacrificeBatch,
    challenge: &SacrificeChallenge,
    masks: &VerifiedAuthenticatedOpening,
    checks: &VerifiedAuthenticatedOpening,
) -> Result<VerifiedSacrificeBatch> {
    validate_challenge(manifest, challenge)?;
    if masks.setup_root() != checks.setup_root() {
        return Err(BinarySacrificeError::AuthenticationMismatch);
    }
    let entries = manifest
        .gates
        .checked_mul(BINARY_SACRIFICE_SECURITY_BITS)
        .ok_or(BinarySacrificeError::ArithmeticOverflow)?;
    let mask_values = masks.values();
    if mask_values.len()
        != entries
            .checked_mul(2)
            .ok_or(BinarySacrificeError::ArithmeticOverflow)?
        || checks.values().len() != entries
    {
        return Err(BinarySacrificeError::ShapeMismatch);
    }
    let (rho, sigma) = mask_values.split_at(entries);
    for gate in 0..manifest.gates {
        for round in 0..BINARY_SACRIFICE_SECURITY_BITS {
            let index = flat_index(gate, round)?;
            if checks.values()[index] ^ (rho[index] & sigma[index]) != 0 {
                return Err(BinarySacrificeError::CheckRejected { gate, round });
            }
        }
    }
    Ok(VerifiedSacrificeBatch {
        manifest_root: manifest.root,
        context: manifest.context,
        n_parties: manifest.n_parties,
        gates: manifest.gates,
    })
}

fn validate_material(
    manifest: &CommittedSacrificeBatch,
    material: &PartySacrificeMaterial,
    expected_party: usize,
) -> Result<()> {
    if material.manifest_root != manifest.root
        || material.context != manifest.context
        || material.binding_digest != manifest.binding_digest
        || material.roster_digest != manifest.roster_digest
        || material.batch_binding != manifest.batch_binding
        || material.row.party != expected_party
        || expected_party >= manifest.n_parties
        || material.identity != manifest.roster[expected_party]
        || material.row.gates() != manifest.gates
    {
        return Err(BinarySacrificeError::ManifestMismatch);
    }
    let commitment = candidate_row_commitment_fields(
        manifest.binding_digest,
        manifest.roster_digest,
        manifest.batch_binding,
        material.identity,
        &material.row,
        material.row_salt,
    )?;
    if commitment != manifest.row_commitments[expected_party] {
        return Err(BinarySacrificeError::CommitmentMismatch {
            party: expected_party,
        });
    }
    Ok(())
}

fn validate_challenge(
    manifest: &CommittedSacrificeBatch,
    challenge: &SacrificeChallenge,
) -> Result<()> {
    let expected = manifest
        .gates
        .checked_mul(BINARY_SACRIFICE_SECURITY_BITS)
        .ok_or(BinarySacrificeError::ArithmeticOverflow)?;
    if challenge.manifest_root != manifest.root
        || challenge.bits.len() != expected
        || challenge.bits.iter().any(|bit| *bit > 1)
    {
        return Err(BinarySacrificeError::ChallengeMismatch);
    }
    Ok(())
}

fn validate_opened(
    manifest: &CommittedSacrificeBatch,
    challenge: &SacrificeChallenge,
    opened: &OpenedSacrificeMasks,
) -> Result<()> {
    let expected = manifest
        .gates
        .checked_mul(BINARY_SACRIFICE_SECURITY_BITS)
        .ok_or(BinarySacrificeError::ArithmeticOverflow)?;
    if opened.manifest_root != manifest.root
        || opened.challenge_digest != challenge.digest
        || opened.rho.len() != expected
        || opened.sigma.len() != expected
        || opened.rho.iter().chain(&opened.sigma).any(|bit| *bit > 1)
    {
        return Err(BinarySacrificeError::ManifestMismatch);
    }
    Ok(())
}

fn validate_manifest_capability(
    manifest: &CommittedSacrificeBatch,
    root: [u8; 64],
    context: [u8; 64],
    n_parties: usize,
    gates: usize,
) -> Result<()> {
    if manifest.root != root
        || manifest.context != context
        || manifest.n_parties != n_parties
        || manifest.gates != gates
    {
        return Err(BinarySacrificeError::ManifestMismatch);
    }
    Ok(())
}

fn candidate_row_commitment(
    binding: &SacrificeCommitmentBinding,
    row: &SacrificeCandidateRow,
    salt: [u8; 32],
) -> Result<[u8; 64]> {
    let identity =
        binding
            .roster
            .get(row.party)
            .copied()
            .ok_or(BinarySacrificeError::InvalidParty {
                party: row.party,
                n_parties: binding.n_parties(),
            })?;
    candidate_row_commitment_fields(
        binding.digest,
        binding.roster_digest,
        binding.batch_binding,
        identity,
        row,
        salt,
    )
}

fn candidate_row_commitment_fields(
    binding_digest: [u8; 64],
    roster_digest: [u8; 64],
    batch_binding: [u8; 64],
    identity: [u8; 32],
    row: &SacrificeCandidateRow,
    salt: [u8; 32],
) -> Result<[u8; 64]> {
    let mut hash = Sha512::new();
    hash.update(canonical_domain(ROW_DOMAIN));
    hash.update(binding_digest);
    hash.update(roster_digest);
    hash.update(batch_binding);
    hash.update(checked_u64(row.party)?.to_be_bytes());
    hash.update(identity);
    hash.update(checked_u64(row.kept.len())?.to_be_bytes());
    hash.update(checked_u64(BINARY_SACRIFICE_SECURITY_BITS)?.to_be_bytes());
    hash.update(salt);
    for triple in row.kept.iter().chain(&row.sacrificed) {
        hash.update([triple.a, triple.b, triple.c]);
    }
    Ok(hash.finalize().into())
}

fn manifest_root(
    binding: &SacrificeCommitmentBinding,
    row_commitments: &[[u8; 64]],
) -> Result<[u8; 64]> {
    if row_commitments.len() != binding.n_parties() {
        return Err(BinarySacrificeError::IncompleteRoster {
            have: row_commitments.len(),
            need: binding.n_parties(),
        });
    }
    let mut hash = Sha512::new();
    hash.update(canonical_domain(MANIFEST_DOMAIN));
    hash.update(binding.digest);
    hash.update(binding.context);
    hash.update(binding.roster_digest);
    hash.update(binding.batch_binding);
    hash.update(checked_u64(binding.n_parties())?.to_be_bytes());
    hash.update(checked_u64(binding.gates)?.to_be_bytes());
    hash.update(checked_u64(BINARY_SACRIFICE_SECURITY_BITS)?.to_be_bytes());
    for (party, (identity, commitment)) in binding.roster.iter().zip(row_commitments).enumerate() {
        hash.update(checked_u64(party)?.to_be_bytes());
        hash.update(identity);
        hash.update(commitment);
    }
    Ok(hash.finalize().into())
}

fn validate_commitment_shape(
    context: [u8; 64],
    roster: &[[u8; 32]],
    gates: usize,
    batch_binding: [u8; 64],
) -> Result<()> {
    if context == [0; 64] || batch_binding == [0; 64] || gates == 0 {
        return Err(BinarySacrificeError::InvalidParameters(
            "commitment context, batch, and gate count must be nonzero",
        ));
    }
    if roster.len() < 2 {
        return Err(BinarySacrificeError::IncompleteRoster {
            have: roster.len(),
            need: 2,
        });
    }
    for (party, identity) in roster.iter().enumerate() {
        if *identity == [0; 32] {
            return Err(BinarySacrificeError::InvalidParty {
                party,
                n_parties: roster.len(),
            });
        }
        if roster[..party].contains(identity) {
            return Err(BinarySacrificeError::DuplicateParty { party });
        }
    }
    let total_candidates = gates
        .checked_mul(BINARY_SACRIFICE_SECURITY_BITS + 1)
        .and_then(|per_party| per_party.checked_mul(roster.len()))
        .ok_or(BinarySacrificeError::ArithmeticOverflow)?;
    if total_candidates > MAX_BINARY_SACRIFICE_TRIPLES {
        return Err(BinarySacrificeError::InvalidParameters(
            "binary sacrifice batch exceeds allocation ceiling",
        ));
    }
    Ok(())
}

fn validate_commitment_message_order(
    n_parties: usize,
    messages: &[CandidateCommitmentMessage],
) -> Result<()> {
    let mut seen = vec![false; n_parties];
    for message in messages {
        if message.party >= n_parties {
            return Err(BinarySacrificeError::InvalidParty {
                party: message.party,
                n_parties,
            });
        }
        if seen[message.party] {
            return Err(BinarySacrificeError::DuplicateParty {
                party: message.party,
            });
        }
        seen[message.party] = true;
    }
    if messages.len() != n_parties {
        return Err(BinarySacrificeError::IncompleteRoster {
            have: messages.len(),
            need: n_parties,
        });
    }
    for (position, message) in messages.iter().enumerate() {
        if message.party != position {
            return Err(BinarySacrificeError::ReorderedParty {
                position,
                party: message.party,
            });
        }
    }
    Ok(())
}

fn validate_manifest_binding(
    binding: &SacrificeCommitmentBinding,
    manifest: &CommittedSacrificeBatch,
) -> Result<()> {
    if manifest.context != binding.context
        || manifest.binding_digest != binding.digest
        || manifest.roster != binding.roster
        || manifest.roster_digest != binding.roster_digest
        || manifest.batch_binding != binding.batch_binding
        || manifest.n_parties != binding.n_parties()
        || manifest.gates != binding.gates
        || manifest.row_commitments.len() != binding.n_parties()
        || manifest.root != manifest_root(binding, &manifest.row_commitments)?
    {
        return Err(BinarySacrificeError::ManifestMismatch);
    }
    Ok(())
}

fn sacrifice_roster_digest(roster: &[[u8; 32]]) -> Result<[u8; 64]> {
    let mut hash = Sha512::new();
    hash.update(canonical_domain(ROSTER_DOMAIN));
    hash.update(checked_u64(roster.len())?.to_be_bytes());
    for (party, identity) in roster.iter().enumerate() {
        hash.update(checked_u64(party)?.to_be_bytes());
        hash.update(identity);
    }
    Ok(hash.finalize().into())
}

fn sacrifice_binding_digest(
    context: [u8; 64],
    roster: &[[u8; 32]],
    roster_digest: [u8; 64],
    gates: usize,
    batch_binding: [u8; 64],
) -> Result<[u8; 64]> {
    let mut hash = Sha512::new();
    hash.update(canonical_domain(BINDING_DOMAIN));
    hash.update(context);
    hash.update(roster_digest);
    hash.update(batch_binding);
    hash.update(checked_u64(roster.len())?.to_be_bytes());
    hash.update(checked_u64(gates)?.to_be_bytes());
    hash.update(checked_u64(BINARY_SACRIFICE_SECURITY_BITS)?.to_be_bytes());
    for (party, identity) in roster.iter().enumerate() {
        hash.update(checked_u64(party)?.to_be_bytes());
        hash.update(identity);
    }
    Ok(hash.finalize().into())
}

fn legacy_roster(context: [u8; 64], n_parties: usize) -> Result<Vec<[u8; 32]>> {
    let mut roster = Vec::with_capacity(n_parties);
    for party in 0..n_parties {
        let mut hash = Sha512::new();
        hash.update(canonical_domain(LEGACY_IDENTITY_DOMAIN));
        hash.update(context);
        hash.update(checked_u64(n_parties)?.to_be_bytes());
        hash.update(checked_u64(party)?.to_be_bytes());
        let digest: [u8; 64] = hash.finalize().into();
        let mut identity = [0u8; 32];
        identity.copy_from_slice(&digest[..32]);
        roster.push(identity);
    }
    Ok(roster)
}

fn legacy_batch_binding(context: [u8; 64], n_parties: usize, gates: usize) -> Result<[u8; 64]> {
    let mut hash = Sha512::new();
    hash.update(canonical_domain(LEGACY_BATCH_DOMAIN));
    hash.update(context);
    hash.update(checked_u64(n_parties)?.to_be_bytes());
    hash.update(checked_u64(gates)?.to_be_bytes());
    Ok(hash.finalize().into())
}

fn flat_index(gate: usize, round: usize) -> Result<usize> {
    gate.checked_mul(BINARY_SACRIFICE_SECURITY_BITS)
        .and_then(|base| base.checked_add(round))
        .ok_or(BinarySacrificeError::ArithmeticOverflow)
}

fn checked_u64(value: usize) -> Result<u64> {
    u64::try_from(value).map_err(|_| BinarySacrificeError::ArithmeticOverflow)
}

fn canonical_domain(domain: &[u8]) -> Vec<u8> {
    let mut encoded = Vec::with_capacity(8 + domain.len());
    encoded.extend_from_slice(&(domain.len() as u64).to_be_bytes());
    encoded.extend_from_slice(domain);
    encoded
}

#[cfg(test)]
mod tests {
    use super::*;

    fn triple(a: u8, b: u8, c: u8) -> BinaryTripleShare {
        BinaryTripleShare::new(a, b, c).unwrap()
    }

    fn split(global: [u8; 3], party_zero: [u8; 3]) -> [BinaryTripleShare; 2] {
        [
            triple(party_zero[0], party_zero[1], party_zero[2]),
            triple(
                global[0] ^ party_zero[0],
                global[1] ^ party_zero[1],
                global[2] ^ party_zero[2],
            ),
        ]
    }

    fn candidate_rows(
        kept_global: [u8; 3],
        sacrificed_global: [u8; 3],
    ) -> Vec<SacrificeCandidateRow> {
        let kept = split(kept_global, [1, 0, 1]);
        let mut sacrificed = [Vec::new(), Vec::new()];
        for round in 0..BINARY_SACRIFICE_SECURITY_BITS {
            let party_zero = [
                (round & 1) as u8,
                ((round >> 1) & 1) as u8,
                ((round >> 2) & 1) as u8,
            ];
            let shares = split(sacrificed_global, party_zero);
            sacrificed[0].push(shares[0]);
            sacrificed[1].push(shares[1]);
        }
        vec![
            SacrificeCandidateRow::new(0, vec![kept[0]], std::mem::take(&mut sacrificed[0]))
                .unwrap(),
            SacrificeCandidateRow::new(1, vec![kept[1]], std::mem::take(&mut sacrificed[1]))
                .unwrap(),
        ]
    }

    fn commit(
        kept_global: [u8; 3],
        sacrificed_global: [u8; 3],
    ) -> (CommittedSacrificeBatch, Vec<PartySacrificeMaterial>) {
        commit_candidate_rows(
            [0x42; 64],
            candidate_rows(kept_global, sacrificed_global),
            vec![[0x51; 32], [0x52; 32]],
        )
        .unwrap()
    }

    fn distributed_prepared(
        kept_global: [u8; 3],
        sacrificed_global: [u8; 3],
    ) -> (
        SacrificeCommitmentBinding,
        Vec<CandidateCommitmentMessage>,
        Vec<PendingCandidateCommitment>,
    ) {
        let binding = SacrificeCommitmentBinding::new(
            [0x42; 64],
            vec![[0x71; 32], [0x72; 32]],
            1,
            [0x43; 64],
        )
        .unwrap();
        let mut messages = Vec::new();
        let mut pending = Vec::new();
        for (row, salt) in candidate_rows(kept_global, sacrificed_global)
            .into_iter()
            .zip([[0x51; 32], [0x52; 32]])
        {
            let (message, local) = prepare_candidate_commitment(&binding, row, salt).unwrap();
            messages.push(message);
            pending.push(local);
        }
        (binding, messages, pending)
    }

    fn honest_messages(
        manifest: &CommittedSacrificeBatch,
        challenge: &SacrificeChallenge,
        materials: &[PartySacrificeMaterial],
    ) -> (OpenedSacrificeMasks, Vec<SacrificeCheckShare>) {
        let openings = materials
            .iter()
            .map(|material| material.opening_share(manifest, challenge).unwrap())
            .collect::<Vec<_>>();
        let opened = aggregate_openings(manifest, challenge, &openings).unwrap();
        let checks = materials
            .iter()
            .map(|material| material.check_share(manifest, challenge, &opened).unwrap())
            .collect();
        (opened, checks)
    }

    #[test]
    fn honest_amplified_sacrifice_releases_only_kept_rows() {
        let (manifest, materials) = commit([1, 1, 1], [1, 0, 0]);
        let challenge = SacrificeChallenge::derive(&manifest, [0x61; 64]).unwrap();
        let (opened, checks) = honest_messages(&manifest, &challenge, &materials);
        let verified = verify_check_shares(&manifest, &challenge, &opened, &checks).unwrap();
        assert_eq!(verified.soundness_bits(), 128);
        let survivors = verified.release(&manifest, materials).unwrap();
        assert_eq!(survivors.len(), 2);
        assert!(survivors.iter().all(|row| row.gates() == 1));
    }

    #[test]
    fn party_local_commitment_barrier_releases_material_only_after_complete_seal() {
        let (binding, messages, pending) = distributed_prepared([1, 1, 1], [1, 0, 0]);
        let manifest = seal_candidate_commitments(&binding, &messages).unwrap();
        assert_eq!(manifest.context(), binding.context());
        assert_eq!(manifest.roster(), binding.roster());
        assert_eq!(manifest.roster_digest(), binding.roster_digest());
        assert_eq!(manifest.batch_binding(), binding.batch_binding());
        assert_eq!(
            manifest.row_commitments(),
            &[messages[0].commitment(), messages[1].commitment()]
        );

        let materials = pending
            .into_iter()
            .map(|local| local.bind_to_manifest(&binding, &manifest).unwrap())
            .collect::<Vec<_>>();
        let challenge = SacrificeChallenge::derive(&manifest, [0x61; 64]).unwrap();
        let (opened, checks) = honest_messages(&manifest, &challenge, &materials);
        let verified = verify_check_shares(&manifest, &challenge, &opened, &checks).unwrap();
        let survivors = materials
            .into_iter()
            .map(|material| verified.release_party(&manifest, material).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(survivors.len(), binding.n_parties());
        assert!(survivors.iter().all(|row| row.gates() == 1));
    }

    #[test]
    fn public_commitment_barrier_refuses_omission_duplicate_and_reorder() {
        let (binding, messages, _) = distributed_prepared([1, 1, 1], [1, 0, 0]);
        assert!(matches!(
            seal_candidate_commitments(&binding, &messages[..1]),
            Err(BinarySacrificeError::IncompleteRoster { have: 1, need: 2 })
        ));
        assert!(matches!(
            seal_candidate_commitments(&binding, &[messages[0].clone(), messages[0].clone()]),
            Err(BinarySacrificeError::DuplicateParty { party: 0 })
        ));
        assert!(matches!(
            seal_candidate_commitments(&binding, &[messages[1].clone(), messages[0].clone()]),
            Err(BinarySacrificeError::ReorderedParty { .. })
        ));
    }

    #[test]
    fn conflicting_complete_commitment_views_are_equivocation() {
        let (binding, honest_messages, _) = distributed_prepared([1, 1, 1], [1, 0, 0]);
        let honest = seal_candidate_commitments(&binding, &honest_messages).unwrap();

        let mut alternate_rows = candidate_rows([1, 1, 1], [1, 0, 0]).into_iter();
        let alternate_row0 = alternate_rows.next().unwrap();
        let (alternate0, _) =
            prepare_candidate_commitment(&binding, alternate_row0, [0x61; 32]).unwrap();
        let conflicting =
            seal_candidate_commitments(&binding, &[alternate0, honest_messages[1].clone()])
                .unwrap();
        assert!(matches!(
            ensure_same_candidate_manifest(&binding, &honest, &conflicting),
            Err(BinarySacrificeError::Equivocation)
        ));
    }

    #[test]
    fn context_roster_and_batch_replay_are_refused() {
        let (binding, messages, pending) = distributed_prepared([1, 1, 1], [1, 0, 0]);
        let changed_context = SacrificeCommitmentBinding::new(
            [0x44; 64],
            binding.roster().to_vec(),
            binding.gates(),
            binding.batch_binding(),
        )
        .unwrap();
        assert!(matches!(
            seal_candidate_commitments(&changed_context, &messages),
            Err(BinarySacrificeError::ManifestMismatch)
        ));

        let changed_roster = SacrificeCommitmentBinding::new(
            binding.context(),
            vec![[0x71; 32], [0x73; 32]],
            binding.gates(),
            binding.batch_binding(),
        )
        .unwrap();
        assert!(seal_candidate_commitments(&changed_roster, &messages).is_err());

        let changed_batch = SacrificeCommitmentBinding::new(
            binding.context(),
            binding.roster().to_vec(),
            binding.gates(),
            [0x45; 64],
        )
        .unwrap();
        assert!(seal_candidate_commitments(&changed_batch, &messages).is_err());

        let manifest = seal_candidate_commitments(&binding, &messages).unwrap();
        let other_manifest = {
            let mut alternate_rows = candidate_rows([1, 1, 1], [1, 0, 0]).into_iter();
            let alternate_row0 = alternate_rows.next().unwrap();
            let (alternate0, _) =
                prepare_candidate_commitment(&binding, alternate_row0, [0x61; 32]).unwrap();
            seal_candidate_commitments(&binding, &[alternate0, messages[1].clone()]).unwrap()
        };
        let mut pending = pending.into_iter();
        assert!(matches!(
            pending
                .next()
                .unwrap()
                .bind_to_manifest(&binding, &other_manifest),
            Err(BinarySacrificeError::CommitmentMismatch { party: 0 })
        ));
        pending
            .next()
            .unwrap()
            .bind_to_manifest(&binding, &manifest)
            .unwrap();
    }

    #[test]
    fn malformed_kept_candidate_is_rejected_by_honest_responses() {
        let (manifest, materials) = commit([1, 1, 0], [1, 0, 0]);
        let challenge = SacrificeChallenge::derive(&manifest, [0x62; 64]).unwrap();
        assert!(challenge.bits.iter().any(|bit| *bit == 1));
        let (opened, checks) = honest_messages(&manifest, &challenge, &materials);
        assert!(matches!(
            verify_check_shares(&manifest, &challenge, &opened, &checks),
            Err(BinarySacrificeError::CheckRejected { .. })
        ));
    }

    #[test]
    fn malformed_sacrificial_candidate_is_rejected_for_every_challenge() {
        let (manifest, materials) = commit([1, 1, 1], [0, 0, 1]);
        let challenge = SacrificeChallenge::derive(&manifest, [0x63; 64]).unwrap();
        let (opened, checks) = honest_messages(&manifest, &challenge, &materials);
        assert!(matches!(
            verify_check_shares(&manifest, &challenge, &opened, &checks),
            Err(BinarySacrificeError::CheckRejected { gate: 0, round: 0 })
        ));
    }

    #[test]
    fn committed_row_mutation_is_refused_before_an_opening() {
        let (manifest, mut materials) = commit([1, 1, 1], [1, 0, 0]);
        materials[1].row.kept[0].c ^= 1;
        let challenge = SacrificeChallenge::derive(&manifest, [0x64; 64]).unwrap();
        assert!(matches!(
            materials[1].opening_share(&manifest, &challenge),
            Err(BinarySacrificeError::CommitmentMismatch { party: 1 })
        ));
    }

    #[test]
    fn reordered_or_cross_manifest_messages_are_refused() {
        let (manifest, materials) = commit([1, 1, 1], [1, 0, 0]);
        let challenge = SacrificeChallenge::derive(&manifest, [0x65; 64]).unwrap();
        let mut openings = materials
            .iter()
            .map(|material| material.opening_share(&manifest, &challenge).unwrap())
            .collect::<Vec<_>>();
        let other_challenge = SacrificeChallenge::derive(&manifest, [0x66; 64]).unwrap();
        assert!(matches!(
            aggregate_openings(&manifest, &other_challenge, &openings),
            Err(BinarySacrificeError::ManifestMismatch)
        ));

        openings.swap(0, 1);
        assert!(matches!(
            aggregate_openings(&manifest, &challenge, &openings),
            Err(BinarySacrificeError::InvalidParty { .. })
        ));
    }

    /// EXPECTED RESIDUAL TOOTH: without authenticated-share/MAC/ZK response
    /// validity, one lying party can cancel the public residual and make a bad
    /// kept candidate pass. This test must stay green until that future layer
    /// changes the message type and makes the forgery unconstructible.
    #[test]
    fn lying_check_share_can_force_acceptance_without_authentication() {
        let (manifest, materials) = commit([1, 1, 0], [1, 0, 0]);
        let challenge = SacrificeChallenge::derive(&manifest, [0x67; 64]).unwrap();
        assert!(challenge.bits.iter().any(|bit| *bit == 1));
        let (opened, mut checks) = honest_messages(&manifest, &challenge, &materials);
        assert!(verify_check_shares(&manifest, &challenge, &opened, &checks).is_err());

        for index in 0..checks[0].tau.len() {
            let aggregate_tau = checks.iter().fold(0, |acc, check| acc ^ check.tau[index]);
            let residual = aggregate_tau ^ (opened.rho[index] & opened.sigma[index]);
            checks[0].tau[index] ^= residual;
        }
        let forged = verify_check_shares(&manifest, &challenge, &opened, &checks)
            .expect("unauthenticated response shares cannot establish malicious security");
        assert_eq!(forged.manifest_root(), manifest.root());
    }
}
