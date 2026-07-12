//! # eth-lightclient — inbound Ethereum Altair sync-committee light-client verify core
//!
//! This crate lets dregg act as a *real* Ethereum light client (inbound): rather
//! than trusting an RPC node's `finalized` tag, it verifies the BLS12-381
//! aggregate signature that the Altair sync committee places over a beacon block
//! header, and it verifies the SSZ Merkle branch that rotates the trusted
//! committee forward. Both are the actual cryptographic gates a light client runs.
//!
//! It is an INBOUND FOREIGN-CHAIN verifier (verifying Ethereum), NOT part of
//! dregg's own soundness TCB, so it builds on `blst` — the audited BLS12-381
//! library used by every ETH consensus client.
//!
//! ## The Altair sync-committee scheme (ground truth)
//!
//! * `SYNC_COMMITTEE_SIZE = 512` validators. Each slot they BLS-sign the block
//!   header. A [`SyncAggregate`] carries a 512-bit participation bitfield plus one
//!   aggregate G2 signature.
//! * BLS scheme: BLS12-381 **min-pubkey** (G1 public keys, G2 signatures),
//!   ciphersuite `BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_` (see [`DST`]).
//! * Signing root: `compute_signing_root(header, domain)` where
//!   `domain = compute_domain(DOMAIN_SYNC_COMMITTEE, fork_version, genesis_validators_root)`.
//! * Safe-update participation threshold: `participants * 3 >= 512 * 2` (>= 2/3).
//!
//! ## Domain / signing-root computation (spec constants)
//!
//! * `DOMAIN_SYNC_COMMITTEE = 0x07000000` (a `DomainType`, 4 bytes).
//! * `compute_fork_data_root(fork_version, gvr) = hash_tree_root(ForkData{ current_version: fork_version (bytes4), genesis_validators_root: gvr (Root) })`
//!   = `SHA-256( (fork_version ++ 28 zeros) || gvr )`.
//! * `compute_domain = DOMAIN_SYNC_COMMITTEE(4 bytes) ++ fork_data_root[0..28]`.
//! * `compute_signing_root(header, domain) = hash_tree_root(SigningData{ object_root: hash_tree_root(header), domain })`
//!   = `SHA-256( hash_tree_root(header) || domain )`.

pub mod ssz;

pub mod base;
pub mod base_fault_proof;
pub mod evm;
pub mod execution;
pub mod finality;

use blst::min_pk::{AggregatePublicKey, PublicKey, Signature};
use blst::BLST_ERROR;

/// Number of validators in an Altair sync committee (`SYNC_COMMITTEE_SIZE`).
pub const SYNC_COMMITTEE_SIZE: usize = 512;

/// `DOMAIN_SYNC_COMMITTEE` domain type (`0x07000000`).
pub const DOMAIN_SYNC_COMMITTEE: [u8; 4] = [0x07, 0x00, 0x00, 0x00];

/// The ETH2 BLS ciphersuite domain-separation tag (min-pubkey, proof-of-possession).
/// Ciphersuite `BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_` — note the trailing
/// underscore; this exact string is the hash-to-curve DST every ETH client uses.
pub const DST: &[u8] = b"BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_";

/// Generalized index of `next_sync_committee` within `BeaconState` in Altair..Deneb
/// (`NEXT_SYNC_COMMITTEE_GINDEX = 55`).
pub const NEXT_SYNC_COMMITTEE_GINDEX: u64 = 55;
/// Merkle-branch depth for `next_sync_committee` in Altair..Deneb = `floor(log2(55)) = 5`.
pub const NEXT_SYNC_COMMITTEE_DEPTH: usize = 5;
/// `NEXT_SYNC_COMMITTEE_GINDEX` in Electra+ (the deepened `BeaconState`): 87
/// (consensus-specs `NEXT_SYNC_COMMITTEE_GINDEX_ELECTRA`).
pub const NEXT_SYNC_COMMITTEE_GINDEX_ELECTRA: u64 = 87;
/// Merkle-branch depth for the Electra+ `next_sync_committee` = `floor(log2(87)) = 6`.
pub const NEXT_SYNC_COMMITTEE_DEPTH_ELECTRA: usize = 6;
/// Subtree index used by `is_valid_merkle_branch` = `55 % 2^5 = 87 % 2^6 = 23`.
/// Identical across the fork boundary (the committee keeps the same left/right walk,
/// one level deeper) — only the branch LENGTH differs, exactly like the finalized-root
/// dual-depth in [`finality`].
pub const NEXT_SYNC_COMMITTEE_SUBTREE_INDEX: u64 =
    NEXT_SYNC_COMMITTEE_GINDEX % (1 << NEXT_SYNC_COMMITTEE_DEPTH);

/// Errors are fail-closed: every path that is not a fully valid verification
/// returns an error rather than silently accepting.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// The trusted committee is not exactly `SYNC_COMMITTEE_SIZE` pubkeys
    /// (an empty committee lands here — it can never verify).
    WrongCommitteeSize { got: usize },
    /// Zero participants in the sync aggregate (the NOMAD-LAW floor).
    NoParticipants,
    /// Participation below the 2/3 safe-update threshold.
    InsufficientParticipation {
        participants: usize,
        required: usize,
    },
    /// A committee pubkey (or the aggregate) failed to deserialize / validate.
    BadPubkey,
    /// The aggregate signature failed to deserialize or failed BLS verification.
    BadSignature,
    /// The committee-rotation Merkle branch did not reconstruct the state root.
    BadMerkleBranch,
    /// The finality branch did not reconstruct the attested state root (the finalized
    /// header is not proven final).
    BadFinalityBranch,
    /// The execution branch did not reconstruct the beacon body root (the execution
    /// payload header — and its state root — is not proven under the finalized header).
    BadExecutionBranch,
    /// A Merkle branch of the wrong depth was supplied.
    WrongBranchLength { got: usize, expected: usize },
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for Error {}

/// An Altair `BeaconBlockHeader` (a fixed 5-field SSZ container). Field order
/// (phase0/beacon-chain.md `BeaconBlockHeader`) is load-bearing for the root:
/// `slot, proposer_index, parent_root, state_root, body_root`.
#[derive(Debug, Clone)]
pub struct BeaconBlockHeader {
    pub slot: u64,
    pub proposer_index: u64,
    pub parent_root: [u8; 32],
    pub state_root: [u8; 32],
    pub body_root: [u8; 32],
}

impl BeaconBlockHeader {
    /// SSZ `hash_tree_root` of the header: merkleize the five field roots
    /// (padded to 8 chunks).
    pub fn hash_tree_root(&self) -> [u8; 32] {
        let chunks = vec![
            ssz::htr_u64(self.slot),
            ssz::htr_u64(self.proposer_index),
            self.parent_root,
            self.state_root,
            self.body_root,
        ];
        ssz::merkleize(chunks)
    }
}

/// An Altair `SyncCommittee` container: 512 pubkeys + an aggregate pubkey.
#[derive(Debug, Clone)]
pub struct SyncCommittee {
    pub pubkeys: Vec<[u8; 48]>,
    pub aggregate_pubkey: [u8; 48],
}

impl SyncCommittee {
    /// SSZ `hash_tree_root`: merkleize([htr(Vector[pubkeys,512]), htr(aggregate_pubkey)]).
    pub fn hash_tree_root(&self) -> [u8; 32] {
        let pubkey_roots: Vec<[u8; 32]> = self.pubkeys.iter().map(ssz::htr_bytes48).collect();
        let pubkeys_root = ssz::merkleize(pubkey_roots);
        let agg_root = ssz::htr_bytes48(&self.aggregate_pubkey);
        ssz::merkleize(vec![pubkeys_root, agg_root])
    }
}

/// The `SyncAggregate`: a 512-bit participation bitfield (64 bytes, little-endian
/// bit order) and one aggregate G2 signature (96 compressed bytes).
#[derive(Debug, Clone)]
pub struct SyncAggregate {
    pub sync_committee_bits: [u8; SYNC_COMMITTEE_SIZE / 8],
    pub sync_committee_signature: [u8; 96],
}

impl SyncAggregate {
    /// Whether committee member `i` participated.
    #[inline]
    pub fn participated(&self, i: usize) -> bool {
        (self.sync_committee_bits[i / 8] >> (i % 8)) & 1 == 1
    }
    /// Number of participating members.
    pub fn count(&self) -> usize {
        self.sync_committee_bits
            .iter()
            .map(|b| b.count_ones() as usize)
            .sum()
    }
}

// ---------------------------------------------------------------------------
// Domain / signing root
// ---------------------------------------------------------------------------

/// `compute_fork_data_root(fork_version, genesis_validators_root)`.
pub fn compute_fork_data_root(
    fork_version: [u8; 4],
    genesis_validators_root: [u8; 32],
) -> [u8; 32] {
    let mut version_chunk = [0u8; 32];
    version_chunk[..4].copy_from_slice(&fork_version);
    // ForkData is a 2-field container → merkleize 2 chunks = hash(c0 || c1).
    ssz::hash_pair(&version_chunk, &genesis_validators_root)
}

/// `compute_domain(DOMAIN_SYNC_COMMITTEE, fork_version, genesis_validators_root)`.
pub fn compute_domain(fork_version: [u8; 4], genesis_validators_root: [u8; 32]) -> [u8; 32] {
    let fdr = compute_fork_data_root(fork_version, genesis_validators_root);
    let mut domain = [0u8; 32];
    domain[..4].copy_from_slice(&DOMAIN_SYNC_COMMITTEE);
    domain[4..].copy_from_slice(&fdr[..28]);
    domain
}

/// `compute_signing_root(header, domain)` — the 32-byte message the sync
/// committee actually signs.
pub fn compute_signing_root(
    header: &BeaconBlockHeader,
    fork_version: [u8; 4],
    genesis_validators_root: [u8; 32],
) -> [u8; 32] {
    let domain = compute_domain(fork_version, genesis_validators_root);
    let object_root = header.hash_tree_root();
    // SigningData is a 2-field container → hash(object_root || domain).
    ssz::hash_pair(&object_root, &domain)
}

// ---------------------------------------------------------------------------
// BLS verification primitives (shared by the KATs and by verify_sync_aggregate)
// ---------------------------------------------------------------------------

/// Verify a single BLS signature (G1 pubkey, G2 sig) over `message` under [`DST`].
/// This is the exact ciphersuite path used inside [`verify_sync_aggregate`]; the
/// external ethereum/bls12-381-tests KATs exercise it directly.
pub fn bls_verify(pubkey: &[u8; 48], message: &[u8], signature: &[u8; 96]) -> Result<(), Error> {
    let pk = PublicKey::from_bytes(pubkey).map_err(|_| Error::BadPubkey)?;
    let sig = Signature::from_bytes(signature).map_err(|_| Error::BadSignature)?;
    // sig_groupcheck=true (subgroup check), pk_validate=true (rejects infinity /
    // off-curve). Fail-closed on anything but BLST_SUCCESS.
    match sig.verify(true, message, DST, &[], &pk, true) {
        BLST_ERROR::BLST_SUCCESS => Ok(()),
        _ => Err(Error::BadSignature),
    }
}

/// Byte-level convenience wrapper over [`bls_aggregate_verify_same_message`]:
/// parse a set of compressed pubkeys + a compressed signature and verify the
/// aggregate over one shared `message`. This is the `fast_aggregate_verify`
/// operation from the consensus spec (used by the external KATs).
pub fn bls_fast_aggregate_verify(
    pubkeys: &[[u8; 48]],
    message: &[u8],
    signature: &[u8; 96],
) -> Result<(), Error> {
    if pubkeys.is_empty() {
        return Err(Error::NoParticipants);
    }
    let pks: Vec<PublicKey> = pubkeys
        .iter()
        .map(|p| PublicKey::from_bytes(p))
        .collect::<Result<_, _>>()
        .map_err(|_| Error::BadPubkey)?;
    let pk_refs: Vec<&PublicKey> = pks.iter().collect();
    let sig = Signature::from_bytes(signature).map_err(|_| Error::BadSignature)?;
    bls_aggregate_verify_same_message(&pk_refs, message, &sig)
}

/// Verify an aggregate signature where every `pubkey` signed the SAME `message`
/// (the sync-committee case). Aggregates the participating G1 pubkeys and BLS-verifies.
/// Fails closed on an empty pubkey set.
pub fn bls_aggregate_verify_same_message(
    pubkeys: &[&PublicKey],
    message: &[u8],
    signature: &Signature,
) -> Result<(), Error> {
    if pubkeys.is_empty() {
        return Err(Error::NoParticipants);
    }
    let apk = AggregatePublicKey::aggregate(pubkeys, true)
        .map_err(|_| Error::BadPubkey)?
        .to_public_key();
    match signature.verify(true, message, DST, &[], &apk, true) {
        BLST_ERROR::BLST_SUCCESS => Ok(()),
        _ => Err(Error::BadSignature),
    }
}

// ---------------------------------------------------------------------------
// The two light-client gates
// ---------------------------------------------------------------------------

/// Verify a sync-committee signature over a beacon header.
///
/// Aggregates the participating committee pubkeys, computes the signing root with
/// the correct sync-committee domain, and BLS-verifies the aggregate signature —
/// enforcing the 2/3 participation threshold.
///
/// Fail-closed on: an empty / wrong-size committee, zero participants,
/// sub-threshold participation, an undecodable pubkey/signature, a wrong
/// domain/fork (wrong signing root → signature mismatch), or a bad signature.
pub fn verify_sync_aggregate(
    header: &BeaconBlockHeader,
    sync_aggregate: &SyncAggregate,
    committee_pubkeys: &[[u8; 48]],
    fork_version: [u8; 4],
    genesis_validators_root: [u8; 32],
) -> Result<(), Error> {
    if committee_pubkeys.len() != SYNC_COMMITTEE_SIZE {
        return Err(Error::WrongCommitteeSize {
            got: committee_pubkeys.len(),
        });
    }

    // Participating subset (bit set in the aggregate).
    let participants: Vec<&[u8; 48]> = committee_pubkeys
        .iter()
        .enumerate()
        .filter(|(i, _)| sync_aggregate.participated(*i))
        .map(|(_, pk)| pk)
        .collect();

    let count = participants.len();
    if count == 0 {
        return Err(Error::NoParticipants);
    }
    // Safe-update threshold: participants * 3 >= SYNC_COMMITTEE_SIZE * 2 (>= 2/3).
    // The multiply form avoids the rounding trap of `count >= 2*512/3`.
    let required = (SYNC_COMMITTEE_SIZE * 2).div_ceil(3); // = 342
    if count * 3 < SYNC_COMMITTEE_SIZE * 2 {
        return Err(Error::InsufficientParticipation {
            participants: count,
            required,
        });
    }

    // Deserialize + subgroup-validate each participating pubkey.
    let pks: Vec<PublicKey> = participants
        .iter()
        .map(|b| PublicKey::from_bytes(b.as_slice()))
        .collect::<Result<_, _>>()
        .map_err(|_| Error::BadPubkey)?;
    let pk_refs: Vec<&PublicKey> = pks.iter().collect();

    let signing_root = compute_signing_root(header, fork_version, genesis_validators_root);
    let sig = Signature::from_bytes(&sync_aggregate.sync_committee_signature)
        .map_err(|_| Error::BadSignature)?;

    bls_aggregate_verify_same_message(&pk_refs, &signing_root, &sig)
}

/// Verify the committee-rotation Merkle branch: prove `next_sync_committee`
/// against a finalized/attested header's `state_root`, so the trusted committee
/// can advance one sync-period. Fail-closed on a bad branch.
///
/// This models the SSZ inclusion proof at generalized index
/// `NEXT_SYNC_COMMITTEE_GINDEX = 55` (Altair..Deneb: depth 5) or
/// `NEXT_SYNC_COMMITTEE_GINDEX_ELECTRA = 87` (Electra+: depth 6) — subtree index 23
/// in BOTH, so the only observable fork difference is the branch LENGTH. Real
/// post-Electra updates carry a 6-node branch; we accept either depth and fail
/// closed on any other length (the same dual-depth treatment
/// [`finality::verify_finality_branch`] gives the finalized root).
pub fn verify_committee_update(
    next_sync_committee: &SyncCommittee,
    next_sync_committee_branch: &[[u8; 32]],
    attested_state_root: &[u8; 32],
) -> Result<(), Error> {
    if next_sync_committee_branch.len() != NEXT_SYNC_COMMITTEE_DEPTH
        && next_sync_committee_branch.len() != NEXT_SYNC_COMMITTEE_DEPTH_ELECTRA
    {
        return Err(Error::WrongBranchLength {
            got: next_sync_committee_branch.len(),
            expected: NEXT_SYNC_COMMITTEE_DEPTH_ELECTRA,
        });
    }
    // Sanity: the subtree index is invariant across the fork boundary.
    debug_assert_eq!(
        NEXT_SYNC_COMMITTEE_GINDEX % (1 << NEXT_SYNC_COMMITTEE_DEPTH),
        NEXT_SYNC_COMMITTEE_GINDEX_ELECTRA % (1 << NEXT_SYNC_COMMITTEE_DEPTH_ELECTRA)
    );
    let leaf = next_sync_committee.hash_tree_root();
    if ssz::is_valid_merkle_branch(
        &leaf,
        next_sync_committee_branch,
        NEXT_SYNC_COMMITTEE_SUBTREE_INDEX,
        attested_state_root,
    ) {
        Ok(())
    } else {
        Err(Error::BadMerkleBranch)
    }
}
