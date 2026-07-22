//! Joint roster commit-reveal beacon for `FHTRI005` preprocessing.
//!
//! `FHTRI004` currently lets its preprocessing authority sample the sacrifice
//! challenge.  This module removes that particular choice from one process:
//!
//! 1. fix the exact session, ordered roster, candidate manifest, and MAC
//!    manifest;
//! 2. every roster member commits a private 64-byte contribution;
//! 3. seal exactly one commitment from every member, in roster order;
//! 4. reveal exactly one matching contribution from every member;
//! 5. derive the 64-byte beacon from the complete canonical transcript.
//!
//! A verifier never sorts messages or fills missing entries. Omission,
//! duplicate party numbers, reordered messages, conflicting commitment-set
//! roots, reveal substitution, unknown versions, truncation, trailing bytes,
//! and allocation-ceiling violations all fail closed. The transcript binds the
//! complete ordered roster rather than only a caller-supplied roster digest.
//!
//! # Exact security boundary
//!
//! If one contribution is sampled uniformly and remains hidden until the full
//! commitment set is fixed, no participant can choose the resulting beacon.
//! SHA-512 is used both as the hiding/binding commitment and transcript hash.
//! This module does not authenticate party identities or provide reliable
//! broadcast: deployments must carry its messages over the authenticated
//! roster/session transport and must compare the sealed set root. Observing two
//! distinct set roots for one context is an equivocation and [`ensure_same_set`]
//! refuses it.
//!
//! Commit-reveal does **not** remove last-revealer abort bias. A final party may
//! see all earlier contributions and withhold its reveal. The only safe local
//! result is then no beacon; callers must not fall back to a partial transcript.
//! Retry, timeout, exclusion, or bond/slash policy is a higher-level protocol
//! decision and must bind a fresh candidate/MAC manifest rather than silently
//! rerolling this context. The transcript also is not a threshold signature,
//! consensus certificate, distributed triple factory, or proof that a revealed
//! contribution was generated with adequate entropy.

use std::fmt;

use sha2::{Digest, Sha512};

/// Hard allocation ceiling for one preprocessing roster.
pub const MAX_JOINT_BEACON_PARTIES: usize = 1024;

const TRANSCRIPT_MAGIC: &[u8; 8] = b"FHTBC005";
const COMMITMENT_MAGIC: &[u8; 8] = b"FHTBCM05";
const REVEAL_MAGIC: &[u8; 8] = b"FHTBRV05";
const WIRE_VERSION: u8 = 1;
const COMMITMENT_WIRE_BYTES: usize = 8 + 1 + 64 + 8 + 32 + 64;
const REVEAL_WIRE_BYTES: usize = 8 + 1 + 64 + 64 + 8 + 32 + 64;
const TRANSCRIPT_FIXED_BYTES: usize = 8 + 1 + 32 + 64 + 64 + 8 + 64 + 8 + 64 + 8 + 64 + 64;
/// Maximum canonical transcript accepted at a process boundary.
pub const MAX_JOINT_BEACON_WIRE_BYTES: usize =
    TRANSCRIPT_FIXED_BYTES + MAX_JOINT_BEACON_PARTIES * (32 + 64 + 64);

const CONTEXT_DOMAIN: &[u8] = b"fhegg/fhtri005/joint-beacon/context/v1";
const COMMITMENT_DOMAIN: &[u8] = b"fhegg/fhtri005/joint-beacon/commitment/v1";
const SET_DOMAIN: &[u8] = b"fhegg/fhtri005/joint-beacon/commitment-set/v1";
const BEACON_DOMAIN: &[u8] = b"fhegg/fhtri005/joint-beacon/output/v1";
const TRANSCRIPT_DOMAIN: &[u8] = b"fhegg/fhtri005/joint-beacon/transcript/v1";

/// Fail-closed joint-beacon errors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JointBeaconError {
    InvalidParameters(&'static str),
    AllocationCeiling,
    IncompleteRoster { have: usize, need: usize },
    InvalidParty { party: usize, n_parties: usize },
    DuplicateParty { party: usize },
    ReorderedParty { position: usize, party: usize },
    ContextMismatch,
    CommitmentMismatch { party: usize },
    CommitmentSetMismatch,
    Equivocation,
    BeaconMismatch,
    MalformedWire(&'static str),
    ArithmeticOverflow,
}

impl fmt::Display for JointBeaconError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FHTRI005 joint-beacon error: {self:?}")
    }
}

impl std::error::Error for JointBeaconError {}

pub type Result<T> = std::result::Result<T, JointBeaconError>;

/// Immutable public context fixed before any contribution is committed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JointBeaconContext {
    session_digest: [u8; 32],
    roster: Vec<[u8; 32]>,
    candidate_manifest: [u8; 64],
    mac_manifest: [u8; 64],
    digest: [u8; 64],
}

impl JointBeaconContext {
    pub fn new(
        session_digest: [u8; 32],
        roster: Vec<[u8; 32]>,
        candidate_manifest: [u8; 64],
        mac_manifest: [u8; 64],
    ) -> Result<Self> {
        validate_context_inputs(session_digest, &roster, candidate_manifest, mac_manifest)?;
        let digest = context_digest(session_digest, &roster, candidate_manifest, mac_manifest)?;
        Ok(Self {
            session_digest,
            roster,
            candidate_manifest,
            mac_manifest,
            digest,
        })
    }

    pub fn session_digest(&self) -> [u8; 32] {
        self.session_digest
    }

    pub fn roster(&self) -> &[[u8; 32]] {
        &self.roster
    }

    pub fn candidate_manifest(&self) -> [u8; 64] {
        self.candidate_manifest
    }

    pub fn mac_manifest(&self) -> [u8; 64] {
        self.mac_manifest
    }

    pub fn digest(&self) -> [u8; 64] {
        self.digest
    }

    pub fn n_parties(&self) -> usize {
        self.roster.len()
    }
}

/// One roster member's pre-reveal commitment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JointBeaconCommitment {
    context_digest: [u8; 64],
    party: usize,
    identity: [u8; 32],
    commitment: [u8; 64],
}

impl JointBeaconCommitment {
    pub fn party(&self) -> usize {
        self.party
    }

    pub fn commitment(&self) -> [u8; 64] {
        self.commitment
    }

    pub fn to_canonical_bytes(&self) -> Result<Vec<u8>> {
        let mut out = Vec::with_capacity(COMMITMENT_WIRE_BYTES);
        out.extend_from_slice(COMMITMENT_MAGIC);
        out.push(WIRE_VERSION);
        out.extend_from_slice(&self.context_digest);
        put_usize(&mut out, self.party)?;
        out.extend_from_slice(&self.identity);
        out.extend_from_slice(&self.commitment);
        debug_assert_eq!(out.len(), COMMITMENT_WIRE_BYTES);
        Ok(out)
    }

    pub fn from_canonical_bytes(bytes: &[u8]) -> Result<Self> {
        if bytes.len() != COMMITMENT_WIRE_BYTES {
            return Err(JointBeaconError::MalformedWire(
                "commitment wire has wrong length",
            ));
        }
        let mut input = Reader::new(bytes);
        if input.array::<8>()? != *COMMITMENT_MAGIC || input.byte()? != WIRE_VERSION {
            return Err(JointBeaconError::MalformedWire(
                "unsupported commitment wire",
            ));
        }
        let commitment = Self {
            context_digest: input.array()?,
            party: input.usize()?,
            identity: input.array()?,
            commitment: input.array()?,
        };
        input.finish()?;
        if commitment.context_digest == [0; 64]
            || commitment.identity == [0; 32]
            || commitment.commitment == [0; 64]
        {
            return Err(JointBeaconError::MalformedWire("zero commitment field"));
        }
        Ok(commitment)
    }
}

/// Party-local contribution retained until the complete commitment set exists.
/// It intentionally implements neither `Clone` nor `Debug`.
pub struct PendingJointBeaconReveal {
    context_digest: [u8; 64],
    party: usize,
    identity: [u8; 32],
    contribution: [u8; 64],
    commitment: [u8; 64],
}

/// Commit a caller-generated contribution. At least one honest caller must use
/// an unpredictable 64-byte value for the resulting beacon to be unpredictable.
pub fn prepare_commitment(
    context: &JointBeaconContext,
    party: usize,
    contribution: [u8; 64],
) -> Result<(JointBeaconCommitment, PendingJointBeaconReveal)> {
    let identity = party_identity(context, party)?;
    if contribution == [0; 64] {
        return Err(JointBeaconError::InvalidParameters(
            "beacon contribution must be nonzero",
        ));
    }
    let commitment = contribution_commitment(context.digest, party, identity, contribution)?;
    let public = JointBeaconCommitment {
        context_digest: context.digest,
        party,
        identity,
        commitment,
    };
    let pending = PendingJointBeaconReveal {
        context_digest: context.digest,
        party,
        identity,
        contribution,
        commitment,
    };
    Ok((public, pending))
}

/// Complete, ordered commitment barrier. No canonicalization by sorting occurs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JointBeaconCommitmentSet {
    context_digest: [u8; 64],
    root: [u8; 64],
    commitments: Vec<[u8; 64]>,
}

impl JointBeaconCommitmentSet {
    pub fn root(&self) -> [u8; 64] {
        self.root
    }

    pub fn commitments(&self) -> &[[u8; 64]] {
        &self.commitments
    }
}

pub fn seal_commitments(
    context: &JointBeaconContext,
    commitments: &[JointBeaconCommitment],
) -> Result<JointBeaconCommitmentSet> {
    validate_ordered_parties(
        context.n_parties(),
        commitments.iter().map(|commitment| commitment.party),
    )?;
    let mut ordered = Vec::with_capacity(context.n_parties());
    for (party, commitment) in commitments.iter().enumerate() {
        if commitment.context_digest != context.digest
            || commitment.identity != context.roster[party]
            || commitment.commitment == [0; 64]
        {
            return Err(JointBeaconError::ContextMismatch);
        }
        ordered.push(commitment.commitment);
    }
    let root = commitment_set_root(context, &ordered)?;
    Ok(JointBeaconCommitmentSet {
        context_digest: context.digest,
        root,
        commitments: ordered,
    })
}

/// Refuse two authenticated-broadcast views that sealed different commitments
/// for the same context. A caller must abort the ceremony on this error.
pub fn ensure_same_set(
    context: &JointBeaconContext,
    left: &JointBeaconCommitmentSet,
    right: &JointBeaconCommitmentSet,
) -> Result<()> {
    validate_set(context, left)?;
    validate_set(context, right)?;
    if left != right {
        return Err(JointBeaconError::Equivocation);
    }
    Ok(())
}

/// One public contribution reveal, bound to the complete commitment-set root.
#[derive(Clone, PartialEq, Eq)]
pub struct JointBeaconReveal {
    context_digest: [u8; 64],
    commitment_set_root: [u8; 64],
    party: usize,
    identity: [u8; 32],
    contribution: [u8; 64],
}

impl fmt::Debug for JointBeaconReveal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("JointBeaconReveal")
            .field("context_digest", &self.context_digest)
            .field("commitment_set_root", &self.commitment_set_root)
            .field("party", &self.party)
            .field("identity", &self.identity)
            .field("contribution", &"<public after reveal>")
            .finish()
    }
}

impl JointBeaconReveal {
    pub fn party(&self) -> usize {
        self.party
    }

    pub fn contribution(&self) -> [u8; 64] {
        self.contribution
    }

    pub fn to_canonical_bytes(&self) -> Result<Vec<u8>> {
        let mut out = Vec::with_capacity(REVEAL_WIRE_BYTES);
        out.extend_from_slice(REVEAL_MAGIC);
        out.push(WIRE_VERSION);
        out.extend_from_slice(&self.context_digest);
        out.extend_from_slice(&self.commitment_set_root);
        put_usize(&mut out, self.party)?;
        out.extend_from_slice(&self.identity);
        out.extend_from_slice(&self.contribution);
        debug_assert_eq!(out.len(), REVEAL_WIRE_BYTES);
        Ok(out)
    }

    pub fn from_canonical_bytes(bytes: &[u8]) -> Result<Self> {
        if bytes.len() != REVEAL_WIRE_BYTES {
            return Err(JointBeaconError::MalformedWire(
                "reveal wire has wrong length",
            ));
        }
        let mut input = Reader::new(bytes);
        if input.array::<8>()? != *REVEAL_MAGIC || input.byte()? != WIRE_VERSION {
            return Err(JointBeaconError::MalformedWire("unsupported reveal wire"));
        }
        let reveal = Self {
            context_digest: input.array()?,
            commitment_set_root: input.array()?,
            party: input.usize()?,
            identity: input.array()?,
            contribution: input.array()?,
        };
        input.finish()?;
        if reveal.context_digest == [0; 64]
            || reveal.commitment_set_root == [0; 64]
            || reveal.identity == [0; 32]
            || reveal.contribution == [0; 64]
        {
            return Err(JointBeaconError::MalformedWire("zero reveal field"));
        }
        Ok(reveal)
    }
}

impl PendingJointBeaconReveal {
    /// Consume the party-local contribution only after the exact complete set
    /// containing its commitment has been sealed.
    pub fn reveal(self, set: &JointBeaconCommitmentSet) -> Result<JointBeaconReveal> {
        if self.context_digest != set.context_digest
            || self.party >= set.commitments.len()
            || set.commitments[self.party] != self.commitment
        {
            return Err(JointBeaconError::CommitmentSetMismatch);
        }
        Ok(JointBeaconReveal {
            context_digest: self.context_digest,
            commitment_set_root: set.root,
            party: self.party,
            identity: self.identity,
            contribution: self.contribution,
        })
    }
}

/// Complete public ceremony transcript and deterministic beacon.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JointBeaconTranscript {
    context: JointBeaconContext,
    commitment_set_root: [u8; 64],
    commitments: Vec<[u8; 64]>,
    contributions: Vec<[u8; 64]>,
    beacon: [u8; 64],
    transcript_digest: [u8; 64],
}

impl JointBeaconTranscript {
    pub fn context(&self) -> &JointBeaconContext {
        &self.context
    }

    pub fn commitment_set_root(&self) -> [u8; 64] {
        self.commitment_set_root
    }

    /// This 64-byte value can replace the authority-sampled raw beacon at the
    /// existing FHTRI004 sacrifice challenge boundary.
    pub fn beacon(&self) -> [u8; 64] {
        self.beacon
    }

    pub fn transcript_digest(&self) -> [u8; 64] {
        self.transcript_digest
    }

    pub fn verify(&self) -> Result<()> {
        let commitments = rebuild_commitments(&self.context, &self.commitments);
        let set = seal_commitments(&self.context, &commitments)?;
        if set.root != self.commitment_set_root {
            return Err(JointBeaconError::CommitmentSetMismatch);
        }
        let reveals = rebuild_reveals(&self.context, &set, &self.contributions);
        let rebuilt = finalize_beacon(&self.context, &set, &reveals)?;
        if rebuilt.beacon != self.beacon || rebuilt.transcript_digest != self.transcript_digest {
            return Err(JointBeaconError::BeaconMismatch);
        }
        Ok(())
    }

    pub fn to_canonical_bytes(&self) -> Result<Vec<u8>> {
        self.verify()?;
        let n = self.context.n_parties();
        let expected = transcript_wire_len(n)?;
        let mut out = Vec::with_capacity(expected);
        out.extend_from_slice(TRANSCRIPT_MAGIC);
        out.push(WIRE_VERSION);
        out.extend_from_slice(&self.context.session_digest);
        out.extend_from_slice(&self.context.candidate_manifest);
        out.extend_from_slice(&self.context.mac_manifest);
        put_usize(&mut out, n)?;
        for identity in &self.context.roster {
            out.extend_from_slice(identity);
        }
        out.extend_from_slice(&self.context.digest);
        put_usize(&mut out, self.commitments.len())?;
        for commitment in &self.commitments {
            out.extend_from_slice(commitment);
        }
        out.extend_from_slice(&self.commitment_set_root);
        put_usize(&mut out, self.contributions.len())?;
        for contribution in &self.contributions {
            out.extend_from_slice(contribution);
        }
        out.extend_from_slice(&self.beacon);
        out.extend_from_slice(&self.transcript_digest);
        if out.len() != expected {
            return Err(JointBeaconError::ArithmeticOverflow);
        }
        Ok(out)
    }

    pub fn from_canonical_bytes(bytes: &[u8]) -> Result<Self> {
        if bytes.len() > MAX_JOINT_BEACON_WIRE_BYTES {
            return Err(JointBeaconError::AllocationCeiling);
        }
        let mut input = Reader::new(bytes);
        if input.array::<8>()? != *TRANSCRIPT_MAGIC || input.byte()? != WIRE_VERSION {
            return Err(JointBeaconError::MalformedWire(
                "unsupported joint-beacon transcript",
            ));
        }
        let session_digest = input.array()?;
        let candidate_manifest = input.array()?;
        let mac_manifest = input.array()?;
        let n = input.usize()?;
        if n > MAX_JOINT_BEACON_PARTIES {
            return Err(JointBeaconError::AllocationCeiling);
        }
        // Check the exact length before allocating from an untrusted count.
        if bytes.len() != transcript_wire_len(n)? {
            return Err(JointBeaconError::MalformedWire(
                "transcript length does not match roster count",
            ));
        }
        let mut roster = Vec::with_capacity(n);
        for _ in 0..n {
            roster.push(input.array()?);
        }
        let context =
            JointBeaconContext::new(session_digest, roster, candidate_manifest, mac_manifest)?;
        if input.array::<64>()? != context.digest {
            return Err(JointBeaconError::ContextMismatch);
        }
        let commitment_count = input.usize()?;
        if commitment_count != n {
            return Err(JointBeaconError::IncompleteRoster {
                have: commitment_count,
                need: n,
            });
        }
        let mut commitment_values = Vec::with_capacity(n);
        for _ in 0..n {
            commitment_values.push(input.array()?);
        }
        let set_root = input.array()?;
        let reveal_count = input.usize()?;
        if reveal_count != n {
            return Err(JointBeaconError::IncompleteRoster {
                have: reveal_count,
                need: n,
            });
        }
        let mut contributions = Vec::with_capacity(n);
        for _ in 0..n {
            contributions.push(input.array()?);
        }
        let encoded_beacon = input.array()?;
        let encoded_transcript_digest = input.array()?;
        input.finish()?;

        let commitments = rebuild_commitments(&context, &commitment_values);
        let set = seal_commitments(&context, &commitments)?;
        if set.root != set_root {
            return Err(JointBeaconError::CommitmentSetMismatch);
        }
        let reveals = rebuild_reveals(&context, &set, &contributions);
        let transcript = finalize_beacon(&context, &set, &reveals)?;
        if transcript.beacon != encoded_beacon
            || transcript.transcript_digest != encoded_transcript_digest
        {
            return Err(JointBeaconError::BeaconMismatch);
        }
        Ok(transcript)
    }
}

/// Finalize only from a complete ordered roster of valid reveals.
pub fn finalize_beacon(
    context: &JointBeaconContext,
    set: &JointBeaconCommitmentSet,
    reveals: &[JointBeaconReveal],
) -> Result<JointBeaconTranscript> {
    validate_set(context, set)?;
    validate_ordered_parties(
        context.n_parties(),
        reveals.iter().map(|reveal| reveal.party),
    )?;
    let mut contributions = Vec::with_capacity(context.n_parties());
    for (party, reveal) in reveals.iter().enumerate() {
        if reveal.context_digest != context.digest
            || reveal.commitment_set_root != set.root
            || reveal.identity != context.roster[party]
            || reveal.contribution == [0; 64]
        {
            return Err(JointBeaconError::ContextMismatch);
        }
        let commitment = contribution_commitment(
            context.digest,
            party,
            context.roster[party],
            reveal.contribution,
        )?;
        if commitment != set.commitments[party] {
            return Err(JointBeaconError::CommitmentMismatch { party });
        }
        contributions.push(reveal.contribution);
    }
    let beacon = derive_beacon(context, set, &contributions)?;
    let transcript_digest = derive_transcript_digest(context, set, &contributions, beacon)?;
    Ok(JointBeaconTranscript {
        context: context.clone(),
        commitment_set_root: set.root,
        commitments: set.commitments.clone(),
        contributions,
        beacon,
        transcript_digest,
    })
}

fn validate_context_inputs(
    session_digest: [u8; 32],
    roster: &[[u8; 32]],
    candidate_manifest: [u8; 64],
    mac_manifest: [u8; 64],
) -> Result<()> {
    if session_digest == [0; 32] || candidate_manifest == [0; 64] || mac_manifest == [0; 64] {
        return Err(JointBeaconError::InvalidParameters(
            "session and manifests must be nonzero",
        ));
    }
    if roster.len() < 2 {
        return Err(JointBeaconError::InvalidParameters(
            "joint beacon requires at least two parties",
        ));
    }
    if roster.len() > MAX_JOINT_BEACON_PARTIES {
        return Err(JointBeaconError::AllocationCeiling);
    }
    for (party, identity) in roster.iter().enumerate() {
        if *identity == [0; 32] {
            return Err(JointBeaconError::InvalidParty {
                party,
                n_parties: roster.len(),
            });
        }
        if roster[..party].contains(identity) {
            return Err(JointBeaconError::DuplicateParty { party });
        }
    }
    Ok(())
}

fn validate_ordered_parties(n_parties: usize, parties: impl Iterator<Item = usize>) -> Result<()> {
    let parties = parties.collect::<Vec<_>>();
    for party in &parties {
        if *party >= n_parties {
            return Err(JointBeaconError::InvalidParty {
                party: *party,
                n_parties,
            });
        }
    }
    let mut seen = vec![false; n_parties];
    for party in &parties {
        if seen[*party] {
            return Err(JointBeaconError::DuplicateParty { party: *party });
        }
        seen[*party] = true;
    }
    if parties.len() != n_parties {
        return Err(JointBeaconError::IncompleteRoster {
            have: parties.len(),
            need: n_parties,
        });
    }
    for (position, party) in parties.into_iter().enumerate() {
        if party != position {
            return Err(JointBeaconError::ReorderedParty { position, party });
        }
    }
    Ok(())
}

fn validate_set(context: &JointBeaconContext, set: &JointBeaconCommitmentSet) -> Result<()> {
    if set.context_digest != context.digest || set.commitments.len() != context.n_parties() {
        return Err(JointBeaconError::CommitmentSetMismatch);
    }
    let expected = commitment_set_root(context, &set.commitments)?;
    if expected != set.root {
        return Err(JointBeaconError::CommitmentSetMismatch);
    }
    Ok(())
}

fn party_identity(context: &JointBeaconContext, party: usize) -> Result<[u8; 32]> {
    context
        .roster
        .get(party)
        .copied()
        .ok_or(JointBeaconError::InvalidParty {
            party,
            n_parties: context.n_parties(),
        })
}

fn context_digest(
    session_digest: [u8; 32],
    roster: &[[u8; 32]],
    candidate_manifest: [u8; 64],
    mac_manifest: [u8; 64],
) -> Result<[u8; 64]> {
    let mut hash = domain_hash(CONTEXT_DOMAIN);
    hash.update(session_digest);
    hash.update(candidate_manifest);
    hash.update(mac_manifest);
    hash.update(checked_u64(roster.len())?.to_be_bytes());
    for (party, identity) in roster.iter().enumerate() {
        hash.update(checked_u64(party)?.to_be_bytes());
        hash.update(identity);
    }
    Ok(hash.finalize().into())
}

fn contribution_commitment(
    context_digest: [u8; 64],
    party: usize,
    identity: [u8; 32],
    contribution: [u8; 64],
) -> Result<[u8; 64]> {
    let mut hash = domain_hash(COMMITMENT_DOMAIN);
    hash.update(context_digest);
    hash.update(checked_u64(party)?.to_be_bytes());
    hash.update(identity);
    hash.update(contribution);
    Ok(hash.finalize().into())
}

fn commitment_set_root(context: &JointBeaconContext, commitments: &[[u8; 64]]) -> Result<[u8; 64]> {
    if commitments.len() != context.n_parties() {
        return Err(JointBeaconError::IncompleteRoster {
            have: commitments.len(),
            need: context.n_parties(),
        });
    }
    let mut hash = domain_hash(SET_DOMAIN);
    hash.update(context.digest);
    hash.update(checked_u64(commitments.len())?.to_be_bytes());
    for (party, (identity, commitment)) in context.roster.iter().zip(commitments).enumerate() {
        hash.update(checked_u64(party)?.to_be_bytes());
        hash.update(identity);
        hash.update(commitment);
    }
    Ok(hash.finalize().into())
}

fn derive_beacon(
    context: &JointBeaconContext,
    set: &JointBeaconCommitmentSet,
    contributions: &[[u8; 64]],
) -> Result<[u8; 64]> {
    let mut hash = domain_hash(BEACON_DOMAIN);
    hash.update(context.digest);
    hash.update(set.root);
    hash.update(checked_u64(contributions.len())?.to_be_bytes());
    for (party, ((identity, commitment), contribution)) in context
        .roster
        .iter()
        .zip(&set.commitments)
        .zip(contributions)
        .enumerate()
    {
        hash.update(checked_u64(party)?.to_be_bytes());
        hash.update(identity);
        hash.update(commitment);
        hash.update(contribution);
    }
    let beacon: [u8; 64] = hash.finalize().into();
    if beacon == [0; 64] {
        return Err(JointBeaconError::BeaconMismatch);
    }
    Ok(beacon)
}

fn derive_transcript_digest(
    context: &JointBeaconContext,
    set: &JointBeaconCommitmentSet,
    contributions: &[[u8; 64]],
    beacon: [u8; 64],
) -> Result<[u8; 64]> {
    let mut hash = domain_hash(TRANSCRIPT_DOMAIN);
    hash.update(context.digest);
    hash.update(set.root);
    hash.update(checked_u64(context.n_parties())?.to_be_bytes());
    for (party, ((identity, commitment), contribution)) in context
        .roster
        .iter()
        .zip(&set.commitments)
        .zip(contributions)
        .enumerate()
    {
        hash.update(checked_u64(party)?.to_be_bytes());
        hash.update(identity);
        hash.update(commitment);
        hash.update(contribution);
    }
    hash.update(beacon);
    Ok(hash.finalize().into())
}

fn rebuild_commitments(
    context: &JointBeaconContext,
    values: &[[u8; 64]],
) -> Vec<JointBeaconCommitment> {
    values
        .iter()
        .enumerate()
        .map(|(party, commitment)| JointBeaconCommitment {
            context_digest: context.digest,
            party,
            identity: context.roster[party],
            commitment: *commitment,
        })
        .collect()
}

fn rebuild_reveals(
    context: &JointBeaconContext,
    set: &JointBeaconCommitmentSet,
    values: &[[u8; 64]],
) -> Vec<JointBeaconReveal> {
    values
        .iter()
        .enumerate()
        .map(|(party, contribution)| JointBeaconReveal {
            context_digest: context.digest,
            commitment_set_root: set.root,
            party,
            identity: context.roster[party],
            contribution: *contribution,
        })
        .collect()
}

fn transcript_wire_len(n_parties: usize) -> Result<usize> {
    if n_parties > MAX_JOINT_BEACON_PARTIES {
        return Err(JointBeaconError::AllocationCeiling);
    }
    n_parties
        .checked_mul(32 + 64 + 64)
        .and_then(|variable| TRANSCRIPT_FIXED_BYTES.checked_add(variable))
        .ok_or(JointBeaconError::ArithmeticOverflow)
}

fn checked_u64(value: usize) -> Result<u64> {
    u64::try_from(value).map_err(|_| JointBeaconError::ArithmeticOverflow)
}

fn put_usize(out: &mut Vec<u8>, value: usize) -> Result<()> {
    out.extend_from_slice(&checked_u64(value)?.to_be_bytes());
    Ok(())
}

fn domain_hash(domain: &[u8]) -> Sha512 {
    let mut hash = Sha512::new();
    hash.update((domain.len() as u64).to_be_bytes());
    hash.update(domain);
    hash
}

struct Reader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> Reader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn take(&mut self, len: usize) -> Result<&'a [u8]> {
        let end = self
            .offset
            .checked_add(len)
            .filter(|end| *end <= self.bytes.len())
            .ok_or(JointBeaconError::MalformedWire("truncated field"))?;
        let value = &self.bytes[self.offset..end];
        self.offset = end;
        Ok(value)
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N]> {
        self.take(N)?
            .try_into()
            .map_err(|_| JointBeaconError::MalformedWire("invalid fixed-width field"))
    }

    fn byte(&mut self) -> Result<u8> {
        Ok(self.take(1)?[0])
    }

    fn usize(&mut self) -> Result<usize> {
        usize::try_from(u64::from_be_bytes(self.array()?))
            .map_err(|_| JointBeaconError::MalformedWire("value does not fit usize"))
    }

    fn finish(self) -> Result<()> {
        if self.offset == self.bytes.len() {
            Ok(())
        } else {
            Err(JointBeaconError::MalformedWire("trailing bytes"))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn context() -> JointBeaconContext {
        JointBeaconContext::new(
            [0x11; 32],
            vec![[0x21; 32], [0x22; 32], [0x23; 32]],
            [0x31; 64],
            [0x41; 64],
        )
        .unwrap()
    }

    fn ceremony() -> (
        JointBeaconContext,
        JointBeaconCommitmentSet,
        Vec<JointBeaconReveal>,
        JointBeaconTranscript,
    ) {
        let context = context();
        let mut commitments = Vec::new();
        let mut pending = Vec::new();
        for party in 0..context.n_parties() {
            let (commitment, reveal) =
                prepare_commitment(&context, party, [0x51 + party as u8; 64]).unwrap();
            commitments.push(commitment);
            pending.push(reveal);
        }
        let set = seal_commitments(&context, &commitments).unwrap();
        let reveals = pending
            .into_iter()
            .map(|pending| pending.reveal(&set).unwrap())
            .collect::<Vec<_>>();
        let transcript = finalize_beacon(&context, &set, &reveals).unwrap();
        (context, set, reveals, transcript)
    }

    #[test]
    fn complete_roster_is_deterministic_and_round_trips_strictly() {
        let (_, _, _, transcript) = ceremony();
        transcript.verify().unwrap();
        let bytes = transcript.to_canonical_bytes().unwrap();
        assert_eq!(bytes.len(), transcript_wire_len(3).unwrap());
        let decoded = JointBeaconTranscript::from_canonical_bytes(&bytes).unwrap();
        assert_eq!(decoded, transcript);
        assert_eq!(decoded.beacon(), transcript.beacon());

        let (context, _, _, second) = ceremony();
        assert_eq!(second.context(), &context);
        assert_eq!(second.beacon(), transcript.beacon());
    }

    #[test]
    fn omission_duplicate_and_reorder_fail_closed() {
        let (context, set, reveals, _) = ceremony();
        assert!(matches!(
            finalize_beacon(&context, &set, &reveals[..2]),
            Err(JointBeaconError::IncompleteRoster { have: 2, need: 3 })
        ));

        let duplicate = vec![reveals[0].clone(), reveals[0].clone(), reveals[2].clone()];
        assert!(matches!(
            finalize_beacon(&context, &set, &duplicate),
            Err(JointBeaconError::DuplicateParty { party: 0 })
        ));

        let reordered = vec![reveals[1].clone(), reveals[0].clone(), reveals[2].clone()];
        assert!(matches!(
            finalize_beacon(&context, &set, &reordered),
            Err(JointBeaconError::ReorderedParty { .. })
        ));

        let (c0, _) = prepare_commitment(&context, 0, [0x51; 64]).unwrap();
        let (c1, _) = prepare_commitment(&context, 1, [0x52; 64]).unwrap();
        let (c2, _) = prepare_commitment(&context, 2, [0x53; 64]).unwrap();
        assert!(matches!(
            seal_commitments(&context, &[c0.clone(), c1.clone()]),
            Err(JointBeaconError::IncompleteRoster { have: 2, need: 3 })
        ));
        assert!(matches!(
            seal_commitments(&context, &[c0.clone(), c0.clone(), c2.clone()]),
            Err(JointBeaconError::DuplicateParty { party: 0 })
        ));
        assert!(matches!(
            seal_commitments(&context, &[c1, c0, c2]),
            Err(JointBeaconError::ReorderedParty { .. })
        ));
    }

    #[test]
    fn contribution_context_and_manifest_substitution_fail() {
        let (context, set, reveals, transcript) = ceremony();

        let mut substituted = reveals.clone();
        substituted[1].contribution[0] ^= 1;
        assert!(matches!(
            finalize_beacon(&context, &set, &substituted),
            Err(JointBeaconError::CommitmentMismatch { party: 1 })
        ));

        let other_context = JointBeaconContext::new(
            context.session_digest(),
            context.roster().to_vec(),
            [0x32; 64],
            context.mac_manifest(),
        )
        .unwrap();
        assert!(finalize_beacon(&other_context, &set, &reveals).is_err());

        let mut bytes = transcript.to_canonical_bytes().unwrap();
        // Candidate manifest begins after magic, version, and session.
        bytes[8 + 1 + 32] ^= 1;
        assert!(JointBeaconTranscript::from_canonical_bytes(&bytes).is_err());
    }

    #[test]
    fn commitment_set_equivocation_is_explicitly_refused() {
        let context = context();
        let (c0, _) = prepare_commitment(&context, 0, [0x51; 64]).unwrap();
        let (c1, _) = prepare_commitment(&context, 1, [0x52; 64]).unwrap();
        let (c2, _) = prepare_commitment(&context, 2, [0x53; 64]).unwrap();
        let honest = seal_commitments(&context, &[c0.clone(), c1.clone(), c2.clone()]).unwrap();
        let (other_c1, _) = prepare_commitment(&context, 1, [0x62; 64]).unwrap();
        let conflicting = seal_commitments(&context, &[c0, other_c1, c2]).unwrap();
        assert!(matches!(
            ensure_same_set(&context, &honest, &conflicting),
            Err(JointBeaconError::Equivocation)
        ));
    }

    #[test]
    fn strict_message_wires_reject_downgrade_and_trailing_bytes() {
        let context = context();
        let (commitment, pending) = prepare_commitment(&context, 0, [0x51; 64]).unwrap();
        let commitment_bytes = commitment.to_canonical_bytes().unwrap();
        assert_eq!(
            JointBeaconCommitment::from_canonical_bytes(&commitment_bytes).unwrap(),
            commitment
        );
        let mut downgraded = commitment_bytes.clone();
        downgraded[8] = 0;
        assert!(JointBeaconCommitment::from_canonical_bytes(&downgraded).is_err());
        let mut trailing = commitment_bytes;
        trailing.push(0);
        assert!(JointBeaconCommitment::from_canonical_bytes(&trailing).is_err());

        let (c1, _) = prepare_commitment(&context, 1, [0x52; 64]).unwrap();
        let (c2, _) = prepare_commitment(&context, 2, [0x53; 64]).unwrap();
        let set = seal_commitments(&context, &[commitment, c1, c2]).unwrap();
        let reveal = pending.reveal(&set).unwrap();
        let reveal_bytes = reveal.to_canonical_bytes().unwrap();
        assert_eq!(
            JointBeaconReveal::from_canonical_bytes(&reveal_bytes).unwrap(),
            reveal
        );
        let mut downgrade_reveal = reveal_bytes.clone();
        downgrade_reveal[8] = 0;
        assert!(JointBeaconReveal::from_canonical_bytes(&downgrade_reveal).is_err());
        let mut trailing_reveal = reveal_bytes;
        trailing_reveal.push(0);
        assert!(JointBeaconReveal::from_canonical_bytes(&trailing_reveal).is_err());
    }

    #[test]
    fn transcript_wire_rejects_downgrade_trailing_and_length_ceiling() {
        let (_, _, _, transcript) = ceremony();
        let bytes = transcript.to_canonical_bytes().unwrap();

        let mut downgrade = bytes.clone();
        downgrade[8] = 0;
        assert!(JointBeaconTranscript::from_canonical_bytes(&downgrade).is_err());

        let mut trailing = bytes;
        trailing.push(0);
        assert!(JointBeaconTranscript::from_canonical_bytes(&trailing).is_err());

        let oversized = vec![0u8; MAX_JOINT_BEACON_WIRE_BYTES + 1];
        assert!(matches!(
            JointBeaconTranscript::from_canonical_bytes(&oversized),
            Err(JointBeaconError::AllocationCeiling)
        ));

        let roster = vec![[0x77; 32]; MAX_JOINT_BEACON_PARTIES + 1];
        assert!(matches!(
            JointBeaconContext::new([1; 32], roster, [2; 64], [3; 64]),
            Err(JointBeaconError::AllocationCeiling)
        ));
    }

    #[test]
    fn exact_roster_and_nonzero_fields_are_required() {
        assert!(JointBeaconContext::new(
            [0x11; 32],
            vec![[0x21; 32], [0x21; 32]],
            [0x31; 64],
            [0x41; 64],
        )
        .is_err());
        assert!(JointBeaconContext::new(
            [0; 32],
            vec![[0x21; 32], [0x22; 32]],
            [0x31; 64],
            [0x41; 64],
        )
        .is_err());
        assert!(prepare_commitment(&context(), 0, [0; 64]).is_err());
    }
}
