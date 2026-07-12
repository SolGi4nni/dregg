//! `cosmos-lightclient`: the **inbound Cosmos/IBC socket** — dregg VERIFYING a
//! Cosmos chain by proof, never by trusting an RPC tag or a committee.
//!
//! This is the Cosmos analog of the ETH sync-committee verifier
//! ([`eth-lightclient`]) and the Solana Tower-BFT verifier
//! ([`dregg-bridge::solana_consensus`]). It has two accept paths, both
//! fail-closed:
//!
//! 1. [`verify_cosmos_header`] — advance a trusted Tendermint state to an
//!    untrusted [`SignedHeader`] via the audited informalsystems
//!    light-client verifier ([`tendermint_light_client_verifier`]). It enforces
//!    the whole Tendermint rule set: the validator-set hash binds the header, a
//!    stake-weighted **>= 2/3** of the voting power signed the commit (real
//!    Ed25519 verification), the header is within the trusting period, its time
//!    is monotonic and not from the future, and (for an adjacent block) the
//!    trusted `next_validators_hash` matches the untrusted validator set. On
//!    success it yields an unforgeable [`VerifiedHeader`] token — the only way to
//!    obtain one is to pass verification (its fields are private; there is no
//!    other constructor). The header's `app_hash` is the commitment the
//!    membership path opens into.
//!
//! 2. [`verify_cosmos_membership`] — verify a two-op ICS-23 proof (an `iavl`
//!    module-store exist proof + a `tendermint`/`simple` multistore exist proof)
//!    that `key -> value` is committed under a verified `app_hash`, via the
//!    audited [`ics23`] crate. This is exactly the chained verification ibc-rs
//!    performs: the iavl proof computes the module sub-root, the tendermint proof
//!    proves that sub-root under the app_hash, and the top root must equal the
//!    app_hash. Any tamper (a forged leaf, a wrong value, a swapped sub-root)
//!    breaks the chain and is refused.
//!
//! 3. [`ProvenCosmosFact`] — the bound result: `(chain_id, height, store_key,
//!    key, value)` proven at a [`VerifiedHeader`]. It is the Cosmos analog of
//!    `dregg-bridge::solana_holdings::ProvenHolding`, ready for a
//!    governance/holdings binding (e.g. an account balance in the `bank` store,
//!    or an IBC packet commitment). That wire is a named followup; so is the
//!    OUTBOUND direction (dregg as a CosmWasm client Cosmos verifies), which
//!    waits on the wrap.
//!
//! # Trust boundary (honest)
//!
//! The consensus arithmetic, the Ed25519 commit-signature verification, the
//! validator-set hashing, and the ICS-23 proof hashing are all real (delegated to
//! the audited reference libraries, not hand-rolled). What is *assumed* is the
//! weak-subjectivity anchor: the caller must supply a genuinely trusted starting
//! [`TrustedCosmosState`] (a header + validator set the operator has verified out
//! of band). From there each advance is trustless. This is the same
//! weak-subjectivity posture every Tendermint light client (Hermes, ibc-rs) has.

use core::time::Duration;

use ics23::commitment_proof::Proof as Ics23Proof;
use ics23::{
    calculate_existence_root, iavl_spec, tendermint_spec, CommitmentProof, ExistenceProof,
    HostFunctionsManager,
};
use tendermint::block::signed_header::SignedHeader;
use tendermint::block::Height;
use tendermint::chain::Id as ChainId;
use tendermint::validator::Set as ValidatorSet;
use tendermint::{Hash, Time};
use tendermint_light_client_verifier::options::Options;
use tendermint_light_client_verifier::types::{
    TrustThreshold, TrustedBlockState, UntrustedBlockState,
};
use tendermint_light_client_verifier::{ProdVerifier, Verdict, Verifier};

// ============================================================================
// Header verification (accept path 1)
// ============================================================================

/// The trusted starting point for a light-client advance: a header + validator
/// set the caller has verified out of band (the weak-subjectivity anchor), or a
/// previously [`VerifiedHeader`] advanced to. `next_validators` / `next_validators_hash`
/// describe the validator set that signs the *next* block — for an adjacent-block
/// advance the verifier binds `next_validators_hash` to the untrusted validator set.
#[derive(Clone, Debug)]
pub struct TrustedCosmosState {
    /// The chain id the untrusted header must also carry (a header from another
    /// chain is refused — cross-chain replay defense).
    pub chain_id: ChainId,
    /// The trusted header's block time (anchors the trusting-period + monotonic-time checks).
    pub header_time: Time,
    /// The trusted header's height.
    pub height: Height,
    /// The validator set that signs `height + 1` (its hash is `next_validators_hash`).
    pub next_validators: ValidatorSet,
    /// The trusted header's `next_validators_hash` commitment.
    pub next_validators_hash: Hash,
}

/// Default clock-drift tolerance (the local clock may lag a blockchain timestamp
/// by at most this). Matches Hermes/ibc-rs defaults.
pub const DEFAULT_CLOCK_DRIFT: Duration = Duration::from_secs(5);

/// Why a header advance was refused. A refusal NEVER yields a [`VerifiedHeader`]
/// (fail closed).
#[derive(Clone, Debug)]
pub enum HeaderVerifyError {
    /// The signed commit did not reach the required voting-power threshold
    /// (sub-2/3, or a forged/invalid signature contributed no power). Carries the
    /// verifier's tally description.
    NotEnoughVotingPower(String),
    /// The header failed a validity check: validators-hash mismatch, a bad
    /// signature, an expired header (outside the trusting period), non-monotonic
    /// or future time, a chain-id mismatch, or a malformed commit. Carries the
    /// verifier's detail.
    Invalid(String),
}

impl core::fmt::Display for HeaderVerifyError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            HeaderVerifyError::NotEnoughVotingPower(d) => {
                write!(f, "insufficient voting power: {d}")
            }
            HeaderVerifyError::Invalid(d) => write!(f, "invalid header: {d}"),
        }
    }
}

impl std::error::Error for HeaderVerifyError {}

/// An unforgeable proof-carrying token: a Cosmos header that PASSED full
/// Tendermint light-client verification (>= 2/3 voting power signed the commit,
/// the validator-set hash bound the header, within the trusting period). Its
/// fields are private and it has no public constructor other than
/// [`verify_cosmos_header`] — you cannot fabricate one. Its `app_hash` is the
/// commitment [`verify_cosmos_membership`] opens state into.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedHeader {
    chain_id: String,
    height: u64,
    time: Time,
    app_hash: Vec<u8>,
}

impl VerifiedHeader {
    /// The chain id proven (bound to the trusted state's chain id).
    pub fn chain_id(&self) -> &str {
        &self.chain_id
    }
    /// The verified block height.
    pub fn height(&self) -> u64 {
        self.height
    }
    /// The verified block time.
    pub fn time(&self) -> Time {
        self.time
    }
    /// The verified application state root — the ICS-23 membership commitment.
    pub fn app_hash(&self) -> &[u8] {
        &self.app_hash
    }
}

/// Verify an untrusted [`SignedHeader`] + validator set advances a
/// [`TrustedCosmosState`], via the audited informalsystems light-client verifier.
///
/// Enforces (all fail-closed): the validator-set hash binds the header; a
/// stake-weighted **>= 2/3** of the voting power signed the commit (real Ed25519
/// verification of the canonical vote sign-bytes); the trusted header is within
/// `trusting_period` of `now`; the untrusted time is monotonic (after the trusted
/// time) and not from the future (beyond `now + clock_drift`); the chain ids
/// match; and — for an adjacent block — the trusted `next_validators_hash` equals
/// the untrusted validator set's hash.
///
/// `untrusted_next_validators` is the set that signs `height + 1`; pass `None` if
/// unavailable (the next-validators-hash cross-check is then skipped, exactly as
/// the underlying verifier documents).
///
/// On success returns a [`VerifiedHeader`] carrying the verified `app_hash`.
#[allow(clippy::too_many_arguments)]
pub fn verify_cosmos_header(
    trusted: &TrustedCosmosState,
    untrusted_signed_header: &SignedHeader,
    untrusted_validators: &ValidatorSet,
    untrusted_next_validators: Option<&ValidatorSet>,
    trust_threshold: TrustThreshold,
    trusting_period: Duration,
    now: Time,
) -> Result<VerifiedHeader, HeaderVerifyError> {
    let options = Options {
        trust_threshold,
        trusting_period,
        clock_drift: DEFAULT_CLOCK_DRIFT,
    };

    let untrusted = UntrustedBlockState {
        signed_header: untrusted_signed_header,
        validators: untrusted_validators,
        next_validators: untrusted_next_validators,
    };
    let trusted_state = TrustedBlockState {
        chain_id: &trusted.chain_id,
        header_time: trusted.header_time,
        height: trusted.height,
        next_validators: &trusted.next_validators,
        next_validators_hash: trusted.next_validators_hash,
    };

    let verifier = ProdVerifier::default();
    match verifier.verify_update_header(untrusted, trusted_state, &options, now) {
        Verdict::Success => {
            let h = &untrusted_signed_header.header;
            Ok(VerifiedHeader {
                chain_id: h.chain_id.as_str().to_string(),
                height: h.height.value(),
                time: h.time,
                app_hash: h.app_hash.as_bytes().to_vec(),
            })
        }
        Verdict::NotEnoughTrust(tally) => Err(HeaderVerifyError::NotEnoughVotingPower(format!(
            "{tally:?}"
        ))),
        Verdict::Invalid(detail) => Err(HeaderVerifyError::Invalid(format!("{detail:?}"))),
    }
}

// ============================================================================
// ICS-23 membership verification (accept path 2)
// ============================================================================

/// A Cosmos state-membership proof: the two-op ICS-23 proof an ABCI query with
/// `prove=true` returns for a `/store/<module>/key` path. `iavl_proof` proves
/// `key -> value` in the module's IAVL store (the module sub-root);
/// `store_proof` proves `store_key -> module_sub_root` in the Tendermint simple
/// multistore Merkle tree (whose root is the block `app_hash`).
#[derive(Clone, Debug)]
pub struct CosmosMembershipProof {
    /// The module store name (e.g. `b"bank"`), the key of the outer `tendermint`
    /// proof op.
    pub store_key: Vec<u8>,
    /// The inner `ics23:iavl` exist proof: `key -> value` under the module sub-root.
    pub iavl_proof: CommitmentProof,
    /// The outer `ics23:simple` (tendermint) exist proof: `store_key -> sub-root`
    /// under the `app_hash`.
    pub store_proof: CommitmentProof,
}

/// Why a membership proof was refused. A refusal NEVER counts as membership
/// (fail closed).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MembershipError {
    /// A proof op was not an existence proof (a non-existence / batch / compressed
    /// op cannot prove membership).
    NotExistenceProof,
    /// Could not compute the sub-root from an existence proof (malformed proof).
    RootComputationFailed,
    /// The inner IAVL exist proof did not prove `key -> value` under its sub-root
    /// (wrong key/value, tampered leaf, or spec violation).
    IavlProofInvalid,
    /// The outer tendermint exist proof did not prove `store_key -> sub-root` under
    /// its root (tampered proof, or the sub-root did not match).
    StoreProofInvalid,
    /// The proof's top root did not equal the verified `app_hash` — the proof does
    /// not open into THIS block's state.
    AppHashMismatch,
}

impl core::fmt::Display for MembershipError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let s = match self {
            MembershipError::NotExistenceProof => "proof op is not an existence proof",
            MembershipError::RootComputationFailed => "could not compute sub-root from proof",
            MembershipError::IavlProofInvalid => "iavl membership proof invalid",
            MembershipError::StoreProofInvalid => "tendermint store proof invalid",
            MembershipError::AppHashMismatch => "proof root does not match app_hash",
        };
        f.write_str(s)
    }
}

impl std::error::Error for MembershipError {}

fn exist_proof(cp: &CommitmentProof) -> Result<&ExistenceProof, MembershipError> {
    match &cp.proof {
        Some(Ics23Proof::Exist(ex)) => Ok(ex),
        _ => Err(MembershipError::NotExistenceProof),
    }
}

/// Verify a two-op ICS-23 membership proof that `key -> value` is committed under
/// `app_hash`, via the audited [`ics23`] crate — the same chained verification
/// ibc-rs performs.
///
/// Steps (each fail-closed):
/// 1. Compute the module sub-root from the IAVL exist proof, and verify it proves
///    `key -> value` under that sub-root (the IAVL spec: leaf/inner hash ops,
///    ordering, prefixes).
/// 2. Compute the top root from the tendermint exist proof, and verify it proves
///    `store_key -> sub_root` under that top root (the tendermint spec).
/// 3. Require the top root to equal `app_hash`.
///
/// A tampered value changes the IAVL leaf hash (step 1 fails); a tampered IAVL
/// proof changes the sub-root, which then mismatches the tendermint proof's
/// committed value (step 2 fails); a tampered tendermint proof makes the top root
/// differ from `app_hash` (step 3 fails). Non-membership passed here is refused
/// in step 1 (it is not an existence proof).
pub fn verify_cosmos_membership(
    app_hash: &[u8],
    proof: &CosmosMembershipProof,
    key: &[u8],
    value: &[u8],
) -> Result<(), MembershipError> {
    // ---- Level 0: IAVL module store: key -> value under sub_root ----
    let iavl_ex = exist_proof(&proof.iavl_proof)?;
    let sub_root = calculate_existence_root::<HostFunctionsManager>(iavl_ex)
        .map_err(|_| MembershipError::RootComputationFailed)?;
    if !ics23::verify_membership::<HostFunctionsManager>(
        &proof.iavl_proof,
        &iavl_spec(),
        &sub_root,
        key,
        value,
    ) {
        return Err(MembershipError::IavlProofInvalid);
    }

    // ---- Level 1: tendermint multistore: store_key -> sub_root under top_root ----
    let store_ex = exist_proof(&proof.store_proof)?;
    let top_root = calculate_existence_root::<HostFunctionsManager>(store_ex)
        .map_err(|_| MembershipError::RootComputationFailed)?;
    if !ics23::verify_membership::<HostFunctionsManager>(
        &proof.store_proof,
        &tendermint_spec(),
        &top_root,
        &proof.store_key,
        &sub_root,
    ) {
        return Err(MembershipError::StoreProofInvalid);
    }

    // ---- Anchor: the top root MUST be the verified app_hash ----
    if top_root != app_hash {
        return Err(MembershipError::AppHashMismatch);
    }
    Ok(())
}

// ============================================================================
// ProvenCosmosFact (bound result — accept path 3)
// ============================================================================

/// A proven Cosmos state fact: at verified `(chain_id, height)`, the module store
/// `store_key` committed `key -> value`. Produced ONLY by [`prove_cosmos_fact`],
/// which requires a [`VerifiedHeader`] (an unforgeable, fully-verified header) AND
/// a valid ICS-23 membership proof under that header's `app_hash`. Its fields are
/// private with no other constructor — it cannot be fabricated. This is the
/// Cosmos analog of `ProvenHolding`; a governance/holdings binding consumes it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProvenCosmosFact {
    chain_id: String,
    height: u64,
    store_key: Vec<u8>,
    key: Vec<u8>,
    value: Vec<u8>,
}

impl ProvenCosmosFact {
    /// The chain the fact was proven on.
    pub fn chain_id(&self) -> &str {
        &self.chain_id
    }
    /// The verified height the fact holds at.
    pub fn height(&self) -> u64 {
        self.height
    }
    /// The module store the key lives in (e.g. `b"bank"`).
    pub fn store_key(&self) -> &[u8] {
        &self.store_key
    }
    /// The proven key.
    pub fn key(&self) -> &[u8] {
        &self.key
    }
    /// The proven value.
    pub fn value(&self) -> &[u8] {
        &self.value
    }
}

/// Bind a [`ProvenCosmosFact`] from a [`VerifiedHeader`] + an ICS-23 membership
/// proof: verify `key -> value` under the header's verified `app_hash`, and on
/// success return the fact bound to the header's `(chain_id, height)`.
///
/// Fail-closed: a [`VerifiedHeader`] can only exist if it passed
/// [`verify_cosmos_header`], and this refuses (returns the [`MembershipError`])
/// unless the membership proof also verifies. So a `ProvenCosmosFact` is a genuine
/// end-to-end proof — a >= 2/3-signed header AND a valid state proof under it.
pub fn prove_cosmos_fact(
    header: &VerifiedHeader,
    proof: &CosmosMembershipProof,
    key: &[u8],
    value: &[u8],
) -> Result<ProvenCosmosFact, MembershipError> {
    verify_cosmos_membership(header.app_hash(), proof, key, value)?;
    Ok(ProvenCosmosFact {
        chain_id: header.chain_id().to_string(),
        height: header.height(),
        store_key: proof.store_key.clone(),
        key: key.to_vec(),
        value: value.to_vec(),
    })
}

/// Decode a raw ABCI-query proof-op payload (protobuf `CommitmentProof` bytes)
/// into an [`ics23::CommitmentProof`]. A malformed payload is refused.
pub fn decode_commitment_proof(bytes: &[u8]) -> Result<CommitmentProof, prost::DecodeError> {
    <CommitmentProof as prost::Message>::decode(bytes)
}
