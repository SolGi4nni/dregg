//! Committed-candidate sacrifice for binary Beaver triples.
//!
//! The bare protocol remains available as an algebraic reference.  The live
//! `FHTRI004` custody path composes it with [`super::authenticated_bits`] before
//! releasing a kept row.  The two layers intentionally remain separate so the
//! unauthenticated failure mode stays executable rather than disappearing
//! behind the hardened adapter.
//!
//! 1. commit every party's kept and sacrificial GF(2) share row;
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

const ROW_DOMAIN: &[u8] = b"fhegg/party-mpc/binary-sacrifice-row/v1";
const MANIFEST_DOMAIN: &[u8] = b"fhegg/party-mpc/binary-sacrifice-manifest/v1";
const CHALLENGE_DOMAIN: &[u8] = b"fhegg/party-mpc/binary-sacrifice-challenge/v1";
const CHALLENGE_DIGEST_DOMAIN: &[u8] = b"fhegg/party-mpc/binary-sacrifice-challenge-digest/v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BinarySacrificeError {
    InvalidParameters(&'static str),
    ShapeMismatch,
    InvalidParty { party: usize, n_parties: usize },
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

/// Public binding of all candidate rows before the beacon is sampled.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommittedSacrificeBatch {
    context: [u8; 64],
    n_parties: usize,
    gates: usize,
    row_commitments: Vec<[u8; 64]>,
    root: [u8; 64],
}

impl CommittedSacrificeBatch {
    pub fn context(&self) -> [u8; 64] {
        self.context
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

    /// Consume the verification capability and exact committed custody rows,
    /// destroying all sacrificial material and releasing only the kept shares.
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
        for (party, material) in materials.into_iter().enumerate() {
            validate_material(manifest, &material, party)?;
            survivors.push(SacrificedPartyRow {
                manifest_root: manifest.root,
                party,
                triples: material.row.kept,
            });
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

/// Bind exact rows before challenge derivation. Rows must arrive in canonical
/// party order `0..n`; reordering is refused rather than silently normalized.
pub fn commit_candidate_rows(
    context: [u8; 64],
    rows: Vec<SacrificeCandidateRow>,
    salts: Vec<[u8; 32]>,
) -> Result<(CommittedSacrificeBatch, Vec<PartySacrificeMaterial>)> {
    if context == [0; 64] {
        return Err(BinarySacrificeError::InvalidParameters(
            "sacrifice context must be nonzero",
        ));
    }
    if rows.len() < 2 || rows.len() != salts.len() {
        return Err(BinarySacrificeError::ShapeMismatch);
    }
    let gates = rows[0].gates();
    let candidates_per_party = gates
        .checked_mul(BINARY_SACRIFICE_SECURITY_BITS + 1)
        .ok_or(BinarySacrificeError::ArithmeticOverflow)?;
    let total_candidates = candidates_per_party
        .checked_mul(rows.len())
        .ok_or(BinarySacrificeError::ArithmeticOverflow)?;
    if total_candidates > MAX_BINARY_SACRIFICE_TRIPLES {
        return Err(BinarySacrificeError::InvalidParameters(
            "binary sacrifice batch exceeds allocation ceiling",
        ));
    }
    let mut row_commitments = Vec::with_capacity(rows.len());
    for (party, (row, salt)) in rows.iter().zip(&salts).enumerate() {
        if row.party != party {
            return Err(BinarySacrificeError::InvalidParty {
                party: row.party,
                n_parties: rows.len(),
            });
        }
        if row.gates() != gates || *salt == [0; 32] {
            return Err(BinarySacrificeError::ShapeMismatch);
        }
        row_commitments.push(row_commitment(context, row, *salt)?);
    }
    let root = manifest_root(context, rows.len(), gates, &row_commitments)?;
    let manifest = CommittedSacrificeBatch {
        context,
        n_parties: rows.len(),
        gates,
        row_commitments,
        root,
    };
    let materials = rows
        .into_iter()
        .zip(salts)
        .map(|(row, row_salt)| PartySacrificeMaterial {
            manifest_root: root,
            context,
            row_salt,
            row,
        })
        .collect();
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
        || material.row.party != expected_party
        || expected_party >= manifest.n_parties
        || material.row.gates() != manifest.gates
    {
        return Err(BinarySacrificeError::ManifestMismatch);
    }
    let commitment = row_commitment(manifest.context, &material.row, material.row_salt)?;
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

fn row_commitment(
    context: [u8; 64],
    row: &SacrificeCandidateRow,
    salt: [u8; 32],
) -> Result<[u8; 64]> {
    let mut hash = Sha512::new();
    hash.update(canonical_domain(ROW_DOMAIN));
    hash.update(context);
    hash.update(checked_u64(row.party)?.to_be_bytes());
    hash.update(checked_u64(row.kept.len())?.to_be_bytes());
    hash.update(checked_u64(BINARY_SACRIFICE_SECURITY_BITS)?.to_be_bytes());
    hash.update(salt);
    for triple in row.kept.iter().chain(&row.sacrificed) {
        hash.update([triple.a, triple.b, triple.c]);
    }
    Ok(hash.finalize().into())
}

fn manifest_root(
    context: [u8; 64],
    n_parties: usize,
    gates: usize,
    row_commitments: &[[u8; 64]],
) -> Result<[u8; 64]> {
    let mut hash = Sha512::new();
    hash.update(canonical_domain(MANIFEST_DOMAIN));
    hash.update(context);
    hash.update(checked_u64(n_parties)?.to_be_bytes());
    hash.update(checked_u64(gates)?.to_be_bytes());
    hash.update(checked_u64(BINARY_SACRIFICE_SECURITY_BITS)?.to_be_bytes());
    for commitment in row_commitments {
        hash.update(commitment);
    }
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
