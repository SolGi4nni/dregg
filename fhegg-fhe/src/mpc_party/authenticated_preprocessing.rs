//! Live authenticated sacrifice ceremony for `FHTRI004` Beaver custody.
//!
//! This module composes the binary sacrifice algebra with the two-lane
//! `GF(2^128)` authenticated-opening layer.  Candidate rows and their MAC setup
//! are fixed before the sacrifice beacon; `rho || sigma` and `tau` are then
//! opened through separate value-commit and MAC-check-commit barriers.  Only an
//! opaque successful sacrifice capability can release the kept rows.
//!
//! The ceremony is roster-, base-session-, and invocation-bound.  It is still
//! an explicit trusted-dealer construction: the dealer sees every candidate,
//! the reconstructed values, and both global MAC keys, and presently supplies
//! the post-commit beacon from its RNG.  The transcript prevents custody/router
//! substitution and makes party-response forgery fail under the one-honest-
//! party MAC premise; it is not dealer-free preprocessing, persistent replay
//! storage, or a quantified joint soundness reduction.

use rand::{CryptoRng, Rng, RngCore};
use sha2::{Digest, Sha512};

use super::authenticated_bits::{
    prepare_mac_check, reconstruct_opened_bits, seal_mac_check_commitments,
    seal_opening_commitments, trusted_mac_setup_for_bits, verify_mac_check,
    AuthenticatedBitManifest, AuthenticatedBitRow, MacBatchChallenge, MacKeyShare,
    VerifiedAuthenticatedOpening, AUTHENTICATED_BIT_MAC_LANES, MAX_AUTHENTICATED_BITS,
};
use super::sacrifice::{
    commit_candidate_rows, verify_authenticated_openings, BinaryTripleShare,
    CommittedSacrificeBatch, SacrificeCandidateRow, SacrificeChallenge,
    BINARY_SACRIFICE_SECURITY_BITS, MAX_BINARY_SACRIFICE_TRIPLES,
};
use super::{LocalTriple, PartyMpcError, Result};

pub const AUTHENTICATED_SACRIFICE_RECEIPT_BYTES: usize = 713;
const RECEIPT_MAGIC: &[u8; 8] = b"FHAPS001";
const RECEIPT_VERSION: u8 = 1;
const CONTEXT_DOMAIN: &[u8] = b"fhegg/party-mpc/authenticated-sacrifice/context/v1";
const AUTH_CONTEXT_DOMAIN: &[u8] = b"fhegg/party-mpc/authenticated-sacrifice/mac-context/v1";
const SACRIFICE_BEACON_DOMAIN: &[u8] = b"fhegg/party-mpc/authenticated-sacrifice/beacon/v1";
const RECEIPT_DOMAIN: &[u8] = b"fhegg/party-mpc/authenticated-sacrifice/receipt/v1";

/// Public, fixed-width authority-signed summary of the authenticated sacrifice
/// ceremony that released one kept Beaver row per party. It binds the phase
/// digests but is not an independently replayable public ceremony transcript.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AuthenticatedSacrificeReceipt {
    base_session_digest: [u8; 32],
    roster_digest: [u8; 64],
    ceremony_nonce: [u8; 64],
    candidate_manifest_root: [u8; 64],
    sacrifice_challenge_digest: [u8; 64],
    mac_setup_root: [u8; 64],
    mask_opening_digest: [u8; 64],
    mask_mac_challenge_digest: [u8; 64],
    tau_opening_digest: [u8; 64],
    tau_mac_challenge_digest: [u8; 64],
    n_parties: usize,
    gates: usize,
    sacrifice_rounds: usize,
    mac_lanes: usize,
    transcript_digest: [u8; 64],
}

impl AuthenticatedSacrificeReceipt {
    pub fn base_session_digest(&self) -> [u8; 32] {
        self.base_session_digest
    }

    pub fn roster_digest(&self) -> [u8; 64] {
        self.roster_digest
    }

    pub fn ceremony_nonce(&self) -> [u8; 64] {
        self.ceremony_nonce
    }

    pub fn candidate_manifest_root(&self) -> [u8; 64] {
        self.candidate_manifest_root
    }

    pub fn mac_setup_root(&self) -> [u8; 64] {
        self.mac_setup_root
    }

    pub fn transcript_digest(&self) -> [u8; 64] {
        self.transcript_digest
    }

    pub fn sacrifice_rounds(&self) -> usize {
        self.sacrifice_rounds
    }

    pub fn mac_lanes(&self) -> usize {
        self.mac_lanes
    }

    pub(crate) fn validate_binding(
        &self,
        base_session_digest: [u8; 32],
        roster_digest: [u8; 64],
        n_parties: usize,
        gates: usize,
    ) -> Result<()> {
        if self.base_session_digest != base_session_digest
            || base_session_digest == [0; 32]
            || self.roster_digest != roster_digest
            || roster_digest == [0; 64]
            || self.ceremony_nonce == [0; 64]
            || self.candidate_manifest_root == [0; 64]
            || self.sacrifice_challenge_digest == [0; 64]
            || self.mac_setup_root == [0; 64]
            || self.mask_opening_digest == [0; 64]
            || self.mask_mac_challenge_digest == [0; 64]
            || self.tau_opening_digest == [0; 64]
            || self.tau_mac_challenge_digest == [0; 64]
            || self.n_parties != n_parties
            || n_parties < 2
            || self.gates != gates
            || gates == 0
            || self.sacrifice_rounds != BINARY_SACRIFICE_SECURITY_BITS
            || self.mac_lanes != AUTHENTICATED_BIT_MAC_LANES
            || self.transcript_digest != receipt_digest(self)?
        {
            return Err(PartyMpcError::InvalidAuthenticatedPreprocessing);
        }
        Ok(())
    }

    pub(crate) fn to_canonical_bytes(&self) -> Result<Vec<u8>> {
        let mut out = encode_receipt_without_digest(self)?;
        out.extend_from_slice(&self.transcript_digest);
        if out.len() != AUTHENTICATED_SACRIFICE_RECEIPT_BYTES {
            return Err(PartyMpcError::ArithmeticOverflow);
        }
        Ok(out)
    }

    pub(crate) fn from_canonical_bytes(bytes: &[u8]) -> Result<Self> {
        if bytes.len() != AUTHENTICATED_SACRIFICE_RECEIPT_BYTES
            || bytes.get(..8) != Some(RECEIPT_MAGIC)
            || bytes.get(8) != Some(&RECEIPT_VERSION)
        {
            return Err(PartyMpcError::InvalidAuthenticatedPreprocessing);
        }
        let mut input = ReceiptReader::new(&bytes[9..]);
        let receipt = Self {
            base_session_digest: input.array::<32>()?,
            roster_digest: input.array::<64>()?,
            ceremony_nonce: input.array::<64>()?,
            candidate_manifest_root: input.array::<64>()?,
            sacrifice_challenge_digest: input.array::<64>()?,
            mac_setup_root: input.array::<64>()?,
            mask_opening_digest: input.array::<64>()?,
            mask_mac_challenge_digest: input.array::<64>()?,
            tau_opening_digest: input.array::<64>()?,
            tau_mac_challenge_digest: input.array::<64>()?,
            n_parties: input.usize()?,
            gates: input.usize()?,
            sacrifice_rounds: input.usize()?,
            mac_lanes: input.usize()?,
            transcript_digest: input.array::<64>()?,
        };
        input.finish()?;
        receipt.validate_binding(
            receipt.base_session_digest,
            receipt.roster_digest,
            receipt.n_parties,
            receipt.gates,
        )?;
        Ok(receipt)
    }
}

pub(super) struct GeneratedAuthenticatedPreprocessing {
    pub kept_rows: Vec<Vec<LocalTriple>>,
    pub receipt: AuthenticatedSacrificeReceipt,
}

/// Generate and release a live authenticated-sacrifice batch.  The caller must
/// subsequently include the returned receipt in the authority-signed FHTRI004
/// certificate; an unsigned receipt is not deployable custody evidence.
pub(super) fn generate_authenticated_sacrificed_rows<R: Rng + CryptoRng>(
    base_session_digest: [u8; 32],
    roster_digest: [u8; 64],
    n_parties: usize,
    gates: usize,
    rng: &mut R,
) -> Result<GeneratedAuthenticatedPreprocessing> {
    if base_session_digest == [0; 32] || roster_digest == [0; 64] || n_parties < 2 || gates == 0 {
        return Err(PartyMpcError::InvalidAuthenticatedPreprocessing);
    }
    validate_allocation_shape(n_parties, gates)?;
    let ceremony_nonce = random_nonzero::<64, _>(rng);
    let context = ceremony_context(
        base_session_digest,
        roster_digest,
        ceremony_nonce,
        n_parties,
        gates,
    )?;
    let (candidate_rows, source_value_shares) = candidate_rows(n_parties, gates, rng)?;
    let salts = (0..n_parties)
        .map(|_| random_nonzero::<32, _>(rng))
        .collect::<Vec<_>>();
    let (manifest, materials) =
        commit_candidate_rows(context, candidate_rows, salts).map_err(map_sacrifice)?;

    // Candidate authentication is fixed before the sacrifice beacon.  This
    // link is trusted-dealer local today; the receipt names it explicitly.
    let auth_context = authenticated_context(context, manifest.root())?;
    let authenticated = trusted_mac_setup_for_bits(auth_context, source_value_shares, rng)
        .map_err(map_authenticated)?;
    let (auth_manifest, source_rows, key_shares) = authenticated.into_parts();

    let raw_beacon = random_nonzero::<64, _>(rng);
    let sacrifice_beacon = bound_sacrifice_beacon(
        raw_beacon,
        manifest.root(),
        auth_manifest.setup_root(),
        roster_digest,
    );
    let challenge =
        SacrificeChallenge::derive(&manifest, sacrifice_beacon).map_err(map_sacrifice)?;

    let mask_rows = derive_mask_rows(&manifest, &challenge, &source_rows)?;
    let mask_manifest = auth_manifest
        .linear_view(
            gates
                .checked_mul(BINARY_SACRIFICE_SECURITY_BITS)
                .and_then(|entries| entries.checked_mul(2))
                .ok_or(PartyMpcError::ArithmeticOverflow)?,
        )
        .map_err(map_authenticated)?;
    let (verified_masks, mask_mac_challenge_digest) =
        authenticated_open(&mask_manifest, &mask_rows, &key_shares, rng)?;

    let tau_rows = derive_tau_rows(&manifest, &challenge, &source_rows, verified_masks.values())?;
    let tau_manifest = auth_manifest
        .linear_view(
            gates
                .checked_mul(BINARY_SACRIFICE_SECURITY_BITS)
                .ok_or(PartyMpcError::ArithmeticOverflow)?,
        )
        .map_err(map_authenticated)?;
    let (verified_tau, tau_mac_challenge_digest) =
        authenticated_open(&tau_manifest, &tau_rows, &key_shares, rng)?;

    let mask_opening_digest = verified_masks.opened_digest();
    let tau_opening_digest = verified_tau.opened_digest();
    let verified =
        verify_authenticated_openings(&manifest, &challenge, &verified_masks, &verified_tau)
            .map_err(map_sacrifice)?;
    let survivors = verified
        .release(&manifest, materials)
        .map_err(map_sacrifice)?;
    let kept_rows = survivors
        .into_iter()
        .map(|row| {
            row.into_triples()
                .into_iter()
                .map(|triple| {
                    let [a, b, c] = triple.into_bits();
                    LocalTriple { a, b, c }
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    let mut receipt = AuthenticatedSacrificeReceipt {
        base_session_digest,
        roster_digest,
        ceremony_nonce,
        candidate_manifest_root: manifest.root(),
        sacrifice_challenge_digest: challenge.digest(),
        mac_setup_root: auth_manifest.setup_root(),
        mask_opening_digest,
        mask_mac_challenge_digest,
        tau_opening_digest,
        tau_mac_challenge_digest,
        n_parties,
        gates,
        sacrifice_rounds: BINARY_SACRIFICE_SECURITY_BITS,
        mac_lanes: AUTHENTICATED_BIT_MAC_LANES,
        transcript_digest: [0; 64],
    };
    receipt.transcript_digest = receipt_digest(&receipt)?;
    receipt.validate_binding(base_session_digest, roster_digest, n_parties, gates)?;
    Ok(GeneratedAuthenticatedPreprocessing { kept_rows, receipt })
}

fn candidate_rows<R: Rng>(
    n_parties: usize,
    gates: usize,
    rng: &mut R,
) -> Result<(Vec<SacrificeCandidateRow>, Vec<Vec<u8>>)> {
    let sacrificial = gates
        .checked_mul(BINARY_SACRIFICE_SECURITY_BITS)
        .ok_or(PartyMpcError::ArithmeticOverflow)?;
    let mut kept_rows = allocate_party_rows(n_parties, gates)?;
    let mut sacrificed_rows = allocate_party_rows(n_parties, sacrificial)?;
    for _ in 0..gates {
        let shares = random_valid_triple_shares(n_parties, rng)?;
        for (party, share) in shares.into_iter().enumerate() {
            kept_rows[party].push(share);
        }
        for _ in 0..BINARY_SACRIFICE_SECURITY_BITS {
            let shares = random_valid_triple_shares(n_parties, rng)?;
            for (party, share) in shares.into_iter().enumerate() {
                sacrificed_rows[party].push(share);
            }
        }
    }
    let source_values = gates
        .checked_add(sacrificial)
        .and_then(|candidates| candidates.checked_mul(3))
        .ok_or(PartyMpcError::ArithmeticOverflow)?;
    let mut source_value_shares = Vec::new();
    source_value_shares
        .try_reserve_exact(n_parties)
        .map_err(|_| PartyMpcError::InvalidAuthenticatedPreprocessing)?;
    for party in 0..n_parties {
        let mut values = Vec::new();
        values
            .try_reserve_exact(source_values)
            .map_err(|_| PartyMpcError::InvalidAuthenticatedPreprocessing)?;
        values.extend(
            kept_rows[party]
                .iter()
                .chain(&sacrificed_rows[party])
                .flat_map(|triple| triple.into_bits()),
        );
        source_value_shares.push(values);
    }
    let rows = kept_rows
        .into_iter()
        .zip(sacrificed_rows)
        .enumerate()
        .map(|(party, (kept, sacrificed))| {
            SacrificeCandidateRow::new(party, kept, sacrificed).map_err(map_sacrifice)
        })
        .collect::<Result<Vec<_>>>()?;
    Ok((rows, source_value_shares))
}

fn validate_allocation_shape(n_parties: usize, gates: usize) -> Result<()> {
    let candidates_per_party = gates
        .checked_mul(BINARY_SACRIFICE_SECURITY_BITS + 1)
        .ok_or(PartyMpcError::ArithmeticOverflow)?;
    let total_candidates = candidates_per_party
        .checked_mul(n_parties)
        .ok_or(PartyMpcError::ArithmeticOverflow)?;
    let total_authenticated_bits = total_candidates
        .checked_mul(3)
        .ok_or(PartyMpcError::ArithmeticOverflow)?;
    if total_candidates > MAX_BINARY_SACRIFICE_TRIPLES
        || total_authenticated_bits > MAX_AUTHENTICATED_BITS
    {
        return Err(PartyMpcError::InvalidAuthenticatedPreprocessing);
    }
    Ok(())
}

fn allocate_party_rows(n_parties: usize, capacity: usize) -> Result<Vec<Vec<BinaryTripleShare>>> {
    let mut rows = Vec::new();
    rows.try_reserve_exact(n_parties)
        .map_err(|_| PartyMpcError::InvalidAuthenticatedPreprocessing)?;
    for _ in 0..n_parties {
        let mut row = Vec::new();
        row.try_reserve_exact(capacity)
            .map_err(|_| PartyMpcError::InvalidAuthenticatedPreprocessing)?;
        rows.push(row);
    }
    Ok(rows)
}

fn random_valid_triple_shares<R: Rng>(
    n_parties: usize,
    rng: &mut R,
) -> Result<Vec<BinaryTripleShare>> {
    let a = rng.gen_range(0..=1);
    let b = rng.gen_range(0..=1);
    let a_shares = split_bit(a, n_parties, rng);
    let b_shares = split_bit(b, n_parties, rng);
    let c_shares = split_bit(a & b, n_parties, rng);
    (0..n_parties)
        .map(|party| {
            BinaryTripleShare::new(a_shares[party], b_shares[party], c_shares[party])
                .map_err(map_sacrifice)
        })
        .collect()
}

fn split_bit<R: Rng>(value: u8, n_parties: usize, rng: &mut R) -> Vec<u8> {
    let mut shares = Vec::with_capacity(n_parties);
    let mut aggregate = value;
    for _ in 0..n_parties - 1 {
        let share = rng.gen_range(0..=1);
        aggregate ^= share;
        shares.push(share);
    }
    shares.push(aggregate);
    shares
}

fn derive_mask_rows(
    manifest: &CommittedSacrificeBatch,
    challenge: &SacrificeChallenge,
    source_rows: &[AuthenticatedBitRow],
) -> Result<Vec<AuthenticatedBitRow>> {
    let entries = manifest
        .gates()
        .checked_mul(BINARY_SACRIFICE_SECURITY_BITS)
        .ok_or(PartyMpcError::ArithmeticOverflow)?;
    source_rows
        .iter()
        .map(|row| {
            let mut rho = Vec::with_capacity(entries);
            let mut sigma = Vec::with_capacity(entries);
            for gate in 0..manifest.gates() {
                for round in 0..BINARY_SACRIFICE_SECURITY_BITS {
                    let r = challenge
                        .bit_at(manifest, gate, round)
                        .map_err(map_sacrifice)?;
                    let a = source_share(row, kept_index(gate, 0)?)?;
                    let b = source_share(row, kept_index(gate, 1)?)?;
                    let f = source_share(row, sacrifice_index(manifest.gates(), gate, round, 0)?)?;
                    let g = source_share(row, sacrifice_index(manifest.gates(), gate, round, 1)?)?;
                    rho.push(
                        a.scale_public(r)
                            .map_err(map_authenticated)?
                            .xor(f)
                            .map_err(map_authenticated)?,
                    );
                    sigma.push(b.xor(g).map_err(map_authenticated)?);
                }
            }
            rho.extend(sigma);
            AuthenticatedBitRow::from_linear_shares(rho).map_err(map_authenticated)
        })
        .collect()
}

fn derive_tau_rows(
    manifest: &CommittedSacrificeBatch,
    challenge: &SacrificeChallenge,
    source_rows: &[AuthenticatedBitRow],
    masks: &[u8],
) -> Result<Vec<AuthenticatedBitRow>> {
    let entries = manifest
        .gates()
        .checked_mul(BINARY_SACRIFICE_SECURITY_BITS)
        .ok_or(PartyMpcError::ArithmeticOverflow)?;
    if masks.len()
        != entries
            .checked_mul(2)
            .ok_or(PartyMpcError::ArithmeticOverflow)?
    {
        return Err(PartyMpcError::InvalidAuthenticatedPreprocessing);
    }
    let (rho, sigma) = masks.split_at(entries);
    source_rows
        .iter()
        .map(|row| {
            let mut tau = Vec::with_capacity(entries);
            for gate in 0..manifest.gates() {
                for round in 0..BINARY_SACRIFICE_SECURITY_BITS {
                    let index = gate
                        .checked_mul(BINARY_SACRIFICE_SECURITY_BITS)
                        .and_then(|base| base.checked_add(round))
                        .ok_or(PartyMpcError::ArithmeticOverflow)?;
                    let r = challenge
                        .bit_at(manifest, gate, round)
                        .map_err(map_sacrifice)?;
                    let c = source_share(row, kept_index(gate, 2)?)?;
                    let f = source_share(row, sacrifice_index(manifest.gates(), gate, round, 0)?)?;
                    let g = source_share(row, sacrifice_index(manifest.gates(), gate, round, 1)?)?;
                    let h = source_share(row, sacrifice_index(manifest.gates(), gate, round, 2)?)?;
                    let value = c
                        .scale_public(r)
                        .map_err(map_authenticated)?
                        .xor(h)
                        .map_err(map_authenticated)?
                        .xor(f.scale_public(sigma[index]).map_err(map_authenticated)?)
                        .map_err(map_authenticated)?
                        .xor(g.scale_public(rho[index]).map_err(map_authenticated)?)
                        .map_err(map_authenticated)?;
                    tau.push(value);
                }
            }
            AuthenticatedBitRow::from_linear_shares(tau).map_err(map_authenticated)
        })
        .collect()
}

fn source_share(
    row: &AuthenticatedBitRow,
    index: usize,
) -> Result<super::authenticated_bits::AuthenticatedBitShare> {
    row.share(index)
        .ok_or(PartyMpcError::InvalidAuthenticatedPreprocessing)
}

fn kept_index(gate: usize, component: usize) -> Result<usize> {
    gate.checked_mul(3)
        .and_then(|base| base.checked_add(component))
        .ok_or(PartyMpcError::ArithmeticOverflow)
}

fn sacrifice_index(gates: usize, gate: usize, round: usize, component: usize) -> Result<usize> {
    gates
        .checked_mul(3)
        .and_then(|base| {
            gate.checked_mul(BINARY_SACRIFICE_SECURITY_BITS)
                .and_then(|offset| offset.checked_add(round))
                .and_then(|candidate| candidate.checked_mul(3))
                .and_then(|candidate| base.checked_add(candidate))
        })
        .and_then(|base| base.checked_add(component))
        .ok_or(PartyMpcError::ArithmeticOverflow)
}

fn authenticated_open<R: Rng + CryptoRng>(
    manifest: &AuthenticatedBitManifest,
    rows: &[AuthenticatedBitRow],
    keys: &[MacKeyShare],
    rng: &mut R,
) -> Result<(VerifiedAuthenticatedOpening, [u8; 64])> {
    if rows.len() != manifest.n_parties() || keys.len() != manifest.n_parties() {
        return Err(PartyMpcError::InvalidAuthenticatedPreprocessing);
    }
    let prepared = rows
        .iter()
        .map(|row| {
            row.prepare_opening(manifest, random_nonzero::<32, _>(rng))
                .map_err(map_authenticated)
        })
        .collect::<Result<Vec<_>>>()?;
    let commitments = prepared
        .iter()
        .map(|(commitment, _)| commitment.clone())
        .collect::<Vec<_>>();
    let set = seal_opening_commitments(manifest, &commitments).map_err(map_authenticated)?;
    let reveals = prepared
        .into_iter()
        .map(|(_, pending)| pending.reveal(&set).map_err(map_authenticated))
        .collect::<Result<Vec<_>>>()?;
    let opened = reconstruct_opened_bits(manifest, &set, &reveals).map_err(map_authenticated)?;
    let challenge = MacBatchChallenge::derive(manifest, &opened, random_nonzero::<64, _>(rng))
        .map_err(map_authenticated)?;
    let challenge_digest = challenge.digest();
    let prepared_checks = rows
        .iter()
        .zip(keys)
        .map(|(row, key)| {
            prepare_mac_check(
                manifest,
                row,
                key,
                &opened,
                &challenge,
                random_nonzero::<32, _>(rng),
            )
            .map_err(map_authenticated)
        })
        .collect::<Result<Vec<_>>>()?;
    let commitments = prepared_checks
        .iter()
        .map(|(commitment, _)| commitment.clone())
        .collect::<Vec<_>>();
    let set = seal_mac_check_commitments(manifest, &challenge, &commitments)
        .map_err(map_authenticated)?;
    let reveals = prepared_checks
        .into_iter()
        .map(|(_, pending)| pending.reveal(&set).map_err(map_authenticated))
        .collect::<Result<Vec<_>>>()?;
    let verified = verify_mac_check(manifest, &opened, &challenge, &set, &reveals)
        .map_err(map_authenticated)?;
    Ok((verified, challenge_digest))
}

fn ceremony_context(
    base_session_digest: [u8; 32],
    roster_digest: [u8; 64],
    ceremony_nonce: [u8; 64],
    n_parties: usize,
    gates: usize,
) -> Result<[u8; 64]> {
    let mut hash = Sha512::new();
    hash.update(canonical_domain(CONTEXT_DOMAIN));
    hash.update(base_session_digest);
    hash.update(roster_digest);
    hash.update(ceremony_nonce);
    hash.update(checked_u64(n_parties)?.to_be_bytes());
    hash.update(checked_u64(gates)?.to_be_bytes());
    Ok(hash.finalize().into())
}

fn authenticated_context(context: [u8; 64], manifest_root: [u8; 64]) -> Result<[u8; 64]> {
    let mut hash = Sha512::new();
    hash.update(canonical_domain(AUTH_CONTEXT_DOMAIN));
    hash.update(context);
    hash.update(manifest_root);
    let result: [u8; 64] = hash.finalize().into();
    if result == [0; 64] {
        return Err(PartyMpcError::InvalidAuthenticatedPreprocessing);
    }
    Ok(result)
}

fn bound_sacrifice_beacon(
    raw: [u8; 64],
    manifest_root: [u8; 64],
    setup_root: [u8; 64],
    roster_digest: [u8; 64],
) -> [u8; 64] {
    let mut hash = Sha512::new();
    hash.update(canonical_domain(SACRIFICE_BEACON_DOMAIN));
    hash.update(raw);
    hash.update(manifest_root);
    hash.update(setup_root);
    hash.update(roster_digest);
    hash.finalize().into()
}

fn receipt_digest(receipt: &AuthenticatedSacrificeReceipt) -> Result<[u8; 64]> {
    let mut hash = Sha512::new();
    hash.update(canonical_domain(RECEIPT_DOMAIN));
    hash.update(encode_receipt_without_digest(receipt)?);
    Ok(hash.finalize().into())
}

fn encode_receipt_without_digest(receipt: &AuthenticatedSacrificeReceipt) -> Result<Vec<u8>> {
    let mut out = Vec::with_capacity(AUTHENTICATED_SACRIFICE_RECEIPT_BYTES - 64);
    out.extend_from_slice(RECEIPT_MAGIC);
    out.push(RECEIPT_VERSION);
    out.extend_from_slice(&receipt.base_session_digest);
    out.extend_from_slice(&receipt.roster_digest);
    out.extend_from_slice(&receipt.ceremony_nonce);
    out.extend_from_slice(&receipt.candidate_manifest_root);
    out.extend_from_slice(&receipt.sacrifice_challenge_digest);
    out.extend_from_slice(&receipt.mac_setup_root);
    out.extend_from_slice(&receipt.mask_opening_digest);
    out.extend_from_slice(&receipt.mask_mac_challenge_digest);
    out.extend_from_slice(&receipt.tau_opening_digest);
    out.extend_from_slice(&receipt.tau_mac_challenge_digest);
    out.extend_from_slice(&checked_u64(receipt.n_parties)?.to_be_bytes());
    out.extend_from_slice(&checked_u64(receipt.gates)?.to_be_bytes());
    out.extend_from_slice(&checked_u64(receipt.sacrifice_rounds)?.to_be_bytes());
    out.extend_from_slice(&checked_u64(receipt.mac_lanes)?.to_be_bytes());
    Ok(out)
}

fn checked_u64(value: usize) -> Result<u64> {
    u64::try_from(value).map_err(|_| PartyMpcError::ArithmeticOverflow)
}

fn canonical_domain(domain: &[u8]) -> Vec<u8> {
    let mut encoded = Vec::with_capacity(8 + domain.len());
    encoded.extend_from_slice(&(domain.len() as u64).to_be_bytes());
    encoded.extend_from_slice(domain);
    encoded
}

fn random_nonzero<const N: usize, R: RngCore + CryptoRng>(rng: &mut R) -> [u8; N] {
    loop {
        let mut bytes = [0u8; N];
        rng.fill_bytes(&mut bytes);
        if bytes != [0; N] {
            return bytes;
        }
    }
}

fn map_authenticated(_: super::authenticated_bits::AuthenticatedBitError) -> PartyMpcError {
    PartyMpcError::InvalidAuthenticatedPreprocessing
}

fn map_sacrifice(_: super::sacrifice::BinarySacrificeError) -> PartyMpcError {
    PartyMpcError::InvalidAuthenticatedPreprocessing
}

struct ReceiptReader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> ReceiptReader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn take(&mut self, len: usize) -> Result<&'a [u8]> {
        let end = self
            .offset
            .checked_add(len)
            .filter(|end| *end <= self.bytes.len())
            .ok_or(PartyMpcError::InvalidAuthenticatedPreprocessing)?;
        let value = &self.bytes[self.offset..end];
        self.offset = end;
        Ok(value)
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N]> {
        self.take(N)?
            .try_into()
            .map_err(|_| PartyMpcError::InvalidAuthenticatedPreprocessing)
    }

    fn usize(&mut self) -> Result<usize> {
        usize::try_from(u64::from_be_bytes(self.array::<8>()?))
            .map_err(|_| PartyMpcError::InvalidAuthenticatedPreprocessing)
    }

    fn finish(self) -> Result<()> {
        if self.offset == self.bytes.len() {
            Ok(())
        } else {
            Err(PartyMpcError::InvalidAuthenticatedPreprocessing)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{rngs::StdRng, SeedableRng};

    #[test]
    fn live_ceremony_releases_only_valid_kept_rows() {
        let generated = generate_authenticated_sacrificed_rows(
            [0x11; 32],
            [0x22; 64],
            3,
            2,
            &mut StdRng::seed_from_u64(0x3344),
        )
        .unwrap();
        generated
            .receipt
            .validate_binding([0x11; 32], [0x22; 64], 3, 2)
            .unwrap();
        assert_eq!(generated.kept_rows.len(), 3);
        for gate in 0..2 {
            let a = generated
                .kept_rows
                .iter()
                .fold(0, |acc, row| acc ^ row[gate].a);
            let b = generated
                .kept_rows
                .iter()
                .fold(0, |acc, row| acc ^ row[gate].b);
            let c = generated
                .kept_rows
                .iter()
                .fold(0, |acc, row| acc ^ row[gate].c);
            assert_eq!(c, a & b);
        }
    }

    #[test]
    fn receipt_roundtrip_and_binding_refuse_mutation_roster_and_replay() {
        let first = generate_authenticated_sacrificed_rows(
            [0x41; 32],
            [0x42; 64],
            2,
            1,
            &mut StdRng::seed_from_u64(0x4344),
        )
        .unwrap();
        let second = generate_authenticated_sacrificed_rows(
            [0x41; 32],
            [0x42; 64],
            2,
            1,
            &mut StdRng::seed_from_u64(0x4546),
        )
        .unwrap();
        assert_ne!(
            first.receipt.transcript_digest(),
            second.receipt.transcript_digest(),
            "same-session retries must be invocation-separated"
        );
        assert!(first
            .receipt
            .validate_binding([0x41; 32], [0x43; 64], 2, 1)
            .is_err());
        let bytes = first.receipt.to_canonical_bytes().unwrap();
        let decoded = AuthenticatedSacrificeReceipt::from_canonical_bytes(&bytes).unwrap();
        assert_eq!(decoded, first.receipt);
        let mut mutated = bytes;
        mutated[200] ^= 1;
        assert!(AuthenticatedSacrificeReceipt::from_canonical_bytes(&mutated).is_err());
    }

    #[test]
    fn hostile_shape_refuses_before_candidate_allocation() {
        let n_parties = 2;
        let gates =
            MAX_AUTHENTICATED_BITS / (n_parties * 3 * (BINARY_SACRIFICE_SECURITY_BITS + 1)) + 1;
        assert!(matches!(
            generate_authenticated_sacrificed_rows(
                [0x51; 32],
                [0x52; 64],
                n_parties,
                gates,
                &mut StdRng::seed_from_u64(0x5354),
            ),
            Err(PartyMpcError::InvalidAuthenticatedPreprocessing)
        ));
    }
}
