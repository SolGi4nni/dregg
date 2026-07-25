//! A `t`-of-`n` custody committee whose parties are SEPARATE PROCESSES.
//!
//! # The gap this closes
//!
//! [`super::quorum`] has a real bivariate-VSS DKG and a real threshold opening,
//! and `dreggnet_market::threshold_committee` has a real `n`-of-`n` committee —
//! and every party in both of them is a thread in one address space. Both say so
//! in their own doc comments. One process holding every share is one compromise
//! away from all of them, whatever the combiner checks, so the threshold property
//! of a co-located committee is worth exactly the integrity of that one process.
//!
//! This module is the wiring that makes the parties separate. It invents no
//! cryptography: the sharing, the commitments, the openings and the combiner are
//! [`super::quorum`]'s, and the confidentiality/authentication is the enrolled
//! native-PQ transport identity in [`crate::mpc_party::transport`]. What it adds
//! is the three things a distributed deployment needs and an in-process ceremony
//! never had to have:
//!
//!   1. a way to move a private dealer row to exactly ONE named recipient
//!      ([`DistributedDkg::deal`] seals it; there is still no public plaintext
//!      codec for a row anywhere);
//!   2. the RECIPIENT-side half of the VSS check
//!      ([`super::quorum::verify_received_dealer_row`]), because a recipient
//!      holds one row and cannot run the all-rows `DealerBundle::verify`; and
//!   3. the pairwise cross-evaluation as an actual message
//!      ([`DealerRowCrossEvaluation`]) instead of a nested loop over rows one
//!      process happened to have.
//!
//! # What is authenticated, and what still trusts the peer
//!
//! The model is SEMI-HONEST, unchanged from the parent module. Precisely:
//!
//! * **Authenticated.** Every DKG message is sealed in one dual-signed
//!   (Ed25519 + ML-DSA-65) hybrid (X25519 + ML-KEM-768) envelope addressed to one
//!   enrolled roster slot, binding the complete roster digest, the DKG domain,
//!   the route and the sequence. A router cannot read a row, substitute a dealing,
//!   re-address one party's row to another, replay a phase-1 message as phase 2,
//!   or splice a message from another committee. Decryption shares are
//!   additionally signed under [`super::quorum::AuthenticatedQuorumRoster`] with
//!   the SAME enrolled Ed25519 identity, and the combiner verifies every one.
//! * **Checked, not trusted.** A dealer's public commitment against its public key
//!   contribution (`C_00 == p0`); each recipient's own row against that commitment
//!   AND against the public BFV image; each PAIR's rows against each other. A
//!   dealer that lies to a recipient, or to a pair, is refused by that recipient
//!   or that pair — this is the tampered-row refusal, and it fires.
//! * **Still trusted.** That a dealer sampled a SHORT (ternary/CBD) secret — the
//!   keygen range-proof seam named in the parent module — and that a party's
//!   decryption share was honestly computed from its custody row. Distributed
//!   openings here carry NO zero-knowledge share certificate; see
//!   [`super::quorum::assemble_distributed_party`] for why that is architectural
//!   and not a shortcut. A malicious party can therefore make an opening produce
//!   garbage. It cannot make it produce a plaintext of its choosing, and it cannot
//!   learn the plaintext with fewer than `t` parties.
//! * **Not addressed at all.** Availability. `n - t` parties may be offline for an
//!   OPENING; all `n` must be live for the SETUP.
//!
//! # What a coalition of `t-1` parties actually learns
//!
//! Stated plainly, because "threshold" is a word people round up. A coalition of
//! `t-1` custody parties holds: its own members' DEALT secrets `s_d` in full (each
//! party is also a dealer, and a dealer knows what it dealt); one bivariate ROW
//! `F_d(i+1, y)` of every other dealer's polynomial per member; and everything
//! public — the collective key, every dealer's commitment and BFV linear images,
//! and every decryption share ever published.
//!
//! For each HONEST dealer that is `t-1` evaluations of a degree-`t-1` sharing, so
//! that dealer's constant stays information-theoretically undetermined, and
//! `s = sum_d s_d` with it. The guarantee is therefore exactly "at least one
//! honest dealer", not "at least one honest party" — a coalition holding every
//! dealer's secret holds `s` by construction, which is what `n`-of-`n` dealing
//! means.
//!
//! What `t-1` parties CAN do: refuse to open (availability), and publish garbage
//! shares that make an opening return garbage — with no share proof on this path,
//! that is detectable only as "the plaintext is wrong", not attributable.
//!
//! One sharper edge, inherited and worth naming in a DISTRIBUTED setting because
//! restarts are normal here: a party refuses to partially decrypt the same
//! ciphertext twice, which is what stops smudge-averaging, and that replay state
//! is IN MEMORY. A restarted party will answer the same ciphertext again.
//!
//! # The collective secret
//!
//! `s = sum_d s_d` is never materialized. Each dealer knows only its own `s_d`;
//! each party holds only `sum_d F_d(i+1, 0)`, one Shamir evaluation. No API in
//! this module, in [`super::quorum`], or in the worker binary reconstructs `s`,
//! and the opening path never needs it: each party applies its own Lagrange
//! coefficient locally and publishes a smudged masked value.

use std::fmt;

use fhe_traits::Serialize as FheSerialize;
use sha2::{Digest, Sha256};

use crate::mpc_party::transport::{
    EqualityTransportError, EqualityTransportRoster, NativePqTransportIdentity,
    NativePqTransportPublicIdentity, TransportSecurityProfile,
};
use crate::threshold::quorum::{
    assemble_distributed_party, deal as deal_contribution, finish_public_key,
    verify_received_dealer_row, DealerRowCrossEvaluation, DealerVssCommitment, PrivateDealerShare,
    QuorumError, QuorumKeygenSession, QuorumParty, VerifiedPrivateDealerShare,
};
use crate::threshold::{BfvParams, CollectivePublicKey, PublicKeyContribution, ThresholdError};

const DKG_DOMAIN: &[u8] = b"fhegg/distributed-threshold-committee/v1";
const DKG_CRP_DOMAIN: &[u8] = b"fhegg/distributed-threshold-committee-crp/v1";
const DKG_SETUP_DIGEST_DOMAIN: &[u8] = b"fhegg/distributed-threshold-committee-setup/v1";
const DEALING_MAGIC: &[u8; 8] = b"FHDKv001";
const CROSS_ROUND_MAGIC: &[u8; 8] = b"FHDXv001";

/// Sequence number of the dealing round on every `dealer -> recipient` route.
pub const SEQUENCE_DEALING: u64 = 1;
/// Sequence number of the cross-evaluation round on every `party -> peer` route.
pub const SEQUENCE_CROSS_EVALUATION: u64 = 2;
/// Sequence number of a relying party's opening request.
pub const SEQUENCE_OPEN_REQUEST: u64 = 3;
/// Sequence number of a custody party's opening response.
pub const SEQUENCE_OPEN_RESPONSE: u64 = 4;
/// Sequence number of a custody party's collective-public-key response.
pub const SEQUENCE_PUBLIC_KEY_RESPONSE: u64 = 5;

/// Canonical enrollment record for one slot: the public half of a native-PQ
/// transport identity.
///
/// ONE codec, used by every participant. Two spellings of "the enrolled bytes"
/// is how a roster ends up meaning different things to different processes, and
/// the roster digest is what the whole DKG domain is derived from.
pub fn encode_enrollment(identity: &NativePqTransportPublicIdentity) -> Vec<u8> {
    let mut encoded = Vec::new();
    encoded.extend_from_slice(&identity.ed25519());
    encoded.extend_from_slice(&(identity.ml_dsa().len() as u64).to_le_bytes());
    encoded.extend_from_slice(identity.ml_dsa());
    encoded.extend_from_slice(&(identity.ml_kem_encapsulation_key().len() as u64).to_le_bytes());
    encoded.extend_from_slice(identity.ml_kem_encapsulation_key());
    encoded
}

/// Parse one enrollment record. Deployed key lengths are checked by
/// [`NativePqTransportPublicIdentity::from_parts`].
pub fn decode_enrollment(bytes: &[u8]) -> Result<NativePqTransportPublicIdentity> {
    let mut cursor = Cursor::new(bytes);
    let ed25519: [u8; 32] = cursor
        .take(32)?
        .try_into()
        .map_err(|_| DistributedCommitteeError::Message("enrollment ed25519"))?;
    let ml_dsa = cursor.length_prefixed()?.to_vec();
    let ml_kem = cursor.length_prefixed()?.to_vec();
    if !cursor.finished() {
        return Err(DistributedCommitteeError::Message(
            "trailing enrollment bytes",
        ));
    }
    Ok(NativePqTransportPublicIdentity::from_parts(
        ed25519, ml_dsa, ml_kem,
    )?)
}

/// Why a distributed committee could not be stood up or could not answer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DistributedCommitteeError {
    /// The roster, profile or `(n, t)` shape was refused before any crypto ran.
    Configuration(&'static str),
    /// A sealed envelope failed to authenticate, decrypt, or matched the wrong
    /// route/sequence/roster.
    Transport(EqualityTransportError),
    /// A DKG message was malformed or belonged to another session.
    Message(&'static str),
    /// A VSS/quorum check refused. THIS is where a tampered row lands.
    Quorum(QuorumError),
    /// A public-key aggregation refused.
    Threshold(ThresholdError),
}

impl fmt::Display for DistributedCommitteeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Configuration(why) => write!(f, "distributed committee configuration: {why}"),
            Self::Transport(error) => write!(f, "sealed DKG envelope refused: {error}"),
            Self::Message(why) => write!(f, "malformed DKG message: {why}"),
            Self::Quorum(error) => write!(f, "VSS/quorum refusal: {error}"),
            Self::Threshold(error) => write!(f, "threshold refusal: {error:?}"),
        }
    }
}

impl std::error::Error for DistributedCommitteeError {}

impl From<EqualityTransportError> for DistributedCommitteeError {
    fn from(error: EqualityTransportError) -> Self {
        Self::Transport(error)
    }
}

impl From<QuorumError> for DistributedCommitteeError {
    fn from(error: QuorumError) -> Self {
        Self::Quorum(error)
    }
}

impl From<ThresholdError> for DistributedCommitteeError {
    fn from(error: ThresholdError) -> Self {
        Self::Threshold(error)
    }
}

type Result<T> = std::result::Result<T, DistributedCommitteeError>;

/// The public parameters every party process derives INDEPENDENTLY from the
/// enrolled roster.
///
/// The CRP seed is derived from the roster digest rather than chosen by anyone:
/// a party that picks the public randomness is a party with a lever on it, and
/// there is no coordinator here to be trusted with the choice. Two committees
/// with different enrollments therefore cannot collide, and a party cannot move
/// the committee to a session of its choosing without changing the roster every
/// other party independently hashed.
#[derive(Clone)]
pub struct DistributedDkg {
    session: QuorumKeygenSession,
    params: BfvParams,
    roster: EqualityTransportRoster,
    domain: [u8; 32],
}

impl DistributedDkg {
    /// `roster` must be a native-PQ roster of exactly `n` parties plus the
    /// relying-party (coordinator) slot at index `n`.
    pub fn new(
        roster: EqualityTransportRoster,
        threshold: usize,
        params: BfvParams,
    ) -> Result<Self> {
        if roster.security_profile() != TransportSecurityProfile::NativePostQuantum {
            return Err(DistributedCommitteeError::Configuration(
                "a distributed committee runs only on the native-PQ transport profile",
            ));
        }
        let n_parties = roster.n_parties();
        let roster_digest = roster.preprocessing_roster_digest();
        let mut crp = Sha256::new();
        crp.update(DKG_CRP_DOMAIN);
        crp.update(roster_digest);
        crp.update((n_parties as u64).to_le_bytes());
        crp.update((threshold as u64).to_le_bytes());
        let crp_seed: [u8; 32] = crp.finalize().into();
        let session = QuorumKeygenSession::from_seed(n_parties, threshold, crp_seed)?;

        let mut domain = Sha256::new();
        domain.update(DKG_DOMAIN);
        domain.update(roster_digest);
        domain.update(crp_seed);
        domain.update((n_parties as u64).to_le_bytes());
        domain.update((threshold as u64).to_le_bytes());
        domain.update((params.degree() as u64).to_le_bytes());
        for &modulus in params.moduli() {
            domain.update(modulus.to_le_bytes());
        }
        domain.update(params.plaintext_modulus().to_le_bytes());
        Ok(Self {
            session,
            params,
            roster,
            domain: domain.finalize().into(),
        })
    }

    pub fn session(&self) -> &QuorumKeygenSession {
        &self.session
    }

    pub fn params(&self) -> &BfvParams {
        &self.params
    }

    pub fn roster(&self) -> &EqualityTransportRoster {
        &self.roster
    }

    /// Every sealed envelope in this committee binds this value, so a message
    /// from another committee — same processes, same keys, different enrollment
    /// or parameters — cannot be replayed into this one.
    pub fn domain(&self) -> [u8; 32] {
        self.domain
    }

    pub fn n_parties(&self) -> usize {
        self.session.n_parties()
    }

    pub fn threshold(&self) -> usize {
        self.session.threshold()
    }

    /// The relying party's slot. It holds NO share and never appears in an
    /// opening roster; it is enrolled only so its requests and the parties'
    /// responses are on the same authenticated transport as everything else.
    pub fn relying_party(&self) -> usize {
        self.roster.coordinator()
    }

    pub fn seal(
        &self,
        identity: &NativePqTransportIdentity,
        sender: usize,
        recipient: usize,
        sequence: u64,
        payload: &[u8],
    ) -> Result<Vec<u8>> {
        Ok(self.roster.seal_native_pq_auxiliary(
            identity,
            sender,
            recipient,
            &self.domain,
            sequence,
            payload,
        )?)
    }

    pub fn open(
        &self,
        identity: &NativePqTransportIdentity,
        sender: usize,
        recipient: usize,
        sequence: u64,
        sealed: &[u8],
    ) -> Result<Vec<u8>> {
        Ok(self.roster.open_native_pq_auxiliary(
            identity,
            sender,
            recipient,
            &self.domain,
            sequence,
            sealed,
        )?)
    }

    /// PHASE 1, dealer side: sample this dealer's contribution, verify the whole
    /// dealing against itself, and seal one addressed message per other party.
    ///
    /// The self-check is the real [`super::quorum::DealerBundle::verify`] over all
    /// `n` rows — the ONE participant that legitimately holds every row of this
    /// dealing is the dealer that just sampled them, so an honest dealer refuses
    /// to publish a dealing that would fail its recipients' checks. It is not a
    /// substitute for those checks: a MALICIOUS dealer simply would not run it,
    /// which is exactly why each recipient runs its own.
    pub fn deal(&self, identity: &NativePqTransportIdentity, dealer: usize) -> Result<Dealing> {
        self.deal_inner(identity, dealer, None)
    }

    /// HOSTILE TEST ENTRY POINT, debug builds only: deal honestly, commit
    /// honestly, then corrupt the private row addressed to `victim` before
    /// sealing it.
    ///
    /// This is a DEALER THAT LIES TO ONE RECIPIENT — the exact adversary the
    /// recipient-side commitment opening exists to catch — and it is here so that
    /// refusal can be observed firing between real processes instead of asserted
    /// in a doc comment. It is compiled out of release builds, and there is no
    /// runtime switch that reaches it.
    #[cfg(debug_assertions)]
    pub fn deal_with_hostile_row_corruption(
        &self,
        identity: &NativePqTransportIdentity,
        dealer: usize,
        victim: usize,
    ) -> Result<Dealing> {
        self.deal_inner(identity, dealer, Some(victim))
    }

    fn deal_inner(
        &self,
        identity: &NativePqTransportIdentity,
        dealer: usize,
        corrupt_row_for: Option<usize>,
    ) -> Result<Dealing> {
        if dealer >= self.n_parties() {
            return Err(DistributedCommitteeError::Configuration(
                "dealer index is outside the roster",
            ));
        }
        let bundle = deal_contribution(&self.session, dealer, &self.params)?;
        let (contribution, commitment, rows) =
            bundle.verify(&self.params)?.into_distributed_parts();

        let contribution_wire = contribution.to_wire_bytes();
        let commitment_wire = commitment.to_wire_bytes();
        let mut own_row = None;
        let mut sealed = Vec::with_capacity(self.n_parties().saturating_sub(1));
        for row in rows {
            let recipient = row.recipient();
            if recipient == dealer {
                own_row = Some(row);
                continue;
            }
            let message = encode_dealing(
                &contribution_wire,
                &commitment_wire,
                &row,
                corrupt_row_for == Some(recipient),
            );
            sealed.push((
                recipient,
                self.seal(identity, dealer, recipient, SEQUENCE_DEALING, &message)?,
            ));
        }
        let own_row = own_row.ok_or(DistributedCommitteeError::Message(
            "the dealing carried no row for its own dealer",
        ))?;
        Ok(Dealing {
            accepted: AcceptedDealing {
                dealer,
                contribution,
                commitment,
                row: own_row,
            },
            sealed,
        })
    }

    /// PHASE 1, recipient side: authenticate, open, and VERIFY.
    ///
    /// Refusal here is the tampered-row tooth. A row whose bytes were altered in
    /// flight cannot even be opened (the AEAD is over the sealed carrier); a row a
    /// malicious dealer altered BEFORE committing fails the commitment opening; a
    /// row it recommitted fails the public BFV image or, at the latest, the peer
    /// cross-evaluation in phase 2.
    pub fn accept_dealing(
        &self,
        identity: &NativePqTransportIdentity,
        recipient: usize,
        dealer: usize,
        sealed: &[u8],
    ) -> Result<AcceptedDealing> {
        if recipient >= self.n_parties() || dealer >= self.n_parties() || recipient == dealer {
            return Err(DistributedCommitteeError::Configuration(
                "a dealing route is outside the roster",
            ));
        }
        let message = self.open(identity, dealer, recipient, SEQUENCE_DEALING, sealed)?;
        let (contribution_wire, commitment_wire, row_wire) = decode_dealing(&message)?;
        let contribution = PublicKeyContribution::from_wire_bytes(contribution_wire)?;
        let commitment = DealerVssCommitment::from_wire_bytes(commitment_wire, &self.params)?;
        let row = PrivateDealerShare::from_confidential_bytes(row_wire, &self.params)?;
        // A self-consistent dealing for ANOTHER (n, t, crp_seed) parses fine, so
        // the session is compared before any acceptance.
        if *commitment.session() != self.session || commitment.dealer() != dealer {
            return Err(DistributedCommitteeError::Message(
                "the dealing does not belong to this committee session",
            ));
        }
        let row =
            verify_received_dealer_row(&commitment, &contribution, row, recipient, &self.params)?;
        Ok(AcceptedDealing {
            dealer,
            contribution,
            commitment,
            row,
        })
    }

    /// PHASE 2, sender side: this party's cross-evaluation of EVERY dealer's row
    /// at one peer's point, as a single message.
    pub fn cross_evaluation_message(
        &self,
        accepted: &[AcceptedDealing],
        peer: usize,
    ) -> Result<Vec<u8>> {
        let mut evaluations = Vec::with_capacity(accepted.len());
        for dealing in accepted {
            evaluations.push(dealing.row.cross_evaluation(peer, &self.params)?);
        }
        Ok(encode_cross_round(&evaluations))
    }

    /// PHASE 2, receiver side: check the peer's evaluations against this party's
    /// own rows, for every dealer, refusing on the first disagreement.
    pub fn check_cross_evaluation_message(
        &self,
        accepted: &[AcceptedDealing],
        peer: usize,
        message: &[u8],
    ) -> Result<()> {
        let received = decode_cross_round(message, &self.params)?;
        if received.len() != accepted.len() {
            return Err(DistributedCommitteeError::Message(
                "the cross-evaluation round does not cover every dealer",
            ));
        }
        for (dealing, evaluation) in accepted.iter().zip(&received) {
            if evaluation.dealer() != dealing.dealer || evaluation.from() != peer {
                return Err(DistributedCommitteeError::Message(
                    "a cross-evaluation is attributed to the wrong dealer or peer",
                ));
            }
            dealing
                .row
                .check_cross_evaluation(evaluation, &self.params)?;
        }
        Ok(())
    }

    /// PHASE 3: this party's custody state, the collective public key it
    /// independently aggregates, and the public setup digest every honest party
    /// computes identically.
    pub fn finish(
        &self,
        party: usize,
        accepted: Vec<AcceptedDealing>,
    ) -> Result<DistributedCustody> {
        if accepted.len() != self.n_parties() {
            return Err(DistributedCommitteeError::Message(
                "custody needs exactly one accepted dealing per dealer",
            ));
        }
        for (dealer, dealing) in accepted.iter().enumerate() {
            if dealing.dealer != dealer {
                return Err(DistributedCommitteeError::Message(
                    "accepted dealings are not in canonical dealer order",
                ));
            }
        }
        let contributions = accepted
            .iter()
            .map(|dealing| dealing.contribution.clone())
            .collect::<Vec<_>>();
        let collective = finish_public_key(&self.session, &contributions, &self.params)?;

        let mut digest = Sha256::new();
        digest.update(DKG_SETUP_DIGEST_DOMAIN);
        digest.update(self.domain);
        for dealing in &accepted {
            digest.update(dealing.commitment.digest());
        }
        digest.update(Sha256::digest(collective.pk.to_bytes()));
        let setup_digest: [u8; 32] = digest.finalize().into();

        let rows = accepted.into_iter().map(|dealing| dealing.row).collect();
        let custody = assemble_distributed_party(&self.session, party, rows, &self.params)?;
        Ok(DistributedCustody {
            party: custody,
            collective,
            setup_digest,
        })
    }
}

/// One dealer's complete phase-1 output: its own row (which never leaves the
/// process) and one sealed message per other party.
pub struct Dealing {
    accepted: AcceptedDealing,
    sealed: Vec<(usize, Vec<u8>)>,
}

impl Dealing {
    /// The dealer's own accepted dealing, ready to sit alongside the ones it
    /// receives.
    pub fn own(self) -> (AcceptedDealing, Vec<(usize, Vec<u8>)>) {
        (self.accepted, self.sealed)
    }
}

/// One dealer's dealing, as accepted by ONE recipient after its own checks.
pub struct AcceptedDealing {
    dealer: usize,
    contribution: PublicKeyContribution,
    commitment: DealerVssCommitment,
    row: VerifiedPrivateDealerShare,
}

impl AcceptedDealing {
    pub fn dealer(&self) -> usize {
        self.dealer
    }

    pub fn commitment_digest(&self) -> [u8; 32] {
        self.commitment.digest()
    }
}

/// What one party process holds after a successful distributed setup.
///
/// `party` is the custody state. It has no secret accessor, and there is no path
/// from a `DistributedCustody` to the collective secret: the only thing it can do
/// with its row is produce a Lagrange-weighted, smudged decryption share for a
/// named opening.
pub struct DistributedCustody {
    pub party: QuorumParty,
    pub collective: CollectivePublicKey,
    pub setup_digest: [u8; 32],
}

/// Byte offset of the first RNS coefficient inside a confidential row encoding:
/// magic, `n`, `t`, CRP seed, dealer, recipient, salt, and the degree count.
const CONFIDENTIAL_ROW_FIRST_COEFFICIENT: usize = 8 + 8 + 8 + 32 + 8 + 8 + 32 + 8;

fn encode_dealing(
    contribution: &[u8],
    commitment: &[u8],
    row: &VerifiedPrivateDealerShare,
    corrupt: bool,
) -> Vec<u8> {
    let mut row = row.confidential_bytes();
    if corrupt {
        // One bit of one committed coefficient. The dealer's public commitment
        // still opens to the ORIGINAL row, so the recipient's opening check must
        // refuse this one.
        row[CONFIDENTIAL_ROW_FIRST_COEFFICIENT] ^= 1;
    }
    let mut out = Vec::with_capacity(8 + 24 + contribution.len() + commitment.len() + row.len());
    out.extend_from_slice(DEALING_MAGIC);
    for part in [contribution, commitment, row.as_slice()] {
        out.extend_from_slice(&(part.len() as u64).to_le_bytes());
        out.extend_from_slice(part);
    }
    out
}

fn decode_dealing(message: &[u8]) -> Result<(&[u8], &[u8], &[u8])> {
    let mut cursor = Cursor::new(message);
    if cursor.take(8)? != DEALING_MAGIC {
        return Err(DistributedCommitteeError::Message("dealing magic"));
    }
    let contribution = cursor.length_prefixed()?;
    let commitment = cursor.length_prefixed()?;
    let row = cursor.length_prefixed()?;
    if !cursor.finished() {
        return Err(DistributedCommitteeError::Message("trailing dealing bytes"));
    }
    Ok((contribution, commitment, row))
}

fn encode_cross_round(evaluations: &[DealerRowCrossEvaluation]) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(CROSS_ROUND_MAGIC);
    out.extend_from_slice(&(evaluations.len() as u64).to_le_bytes());
    for evaluation in evaluations {
        let wire = evaluation.to_wire_bytes();
        out.extend_from_slice(&(wire.len() as u64).to_le_bytes());
        out.extend_from_slice(&wire);
    }
    out
}

fn decode_cross_round(message: &[u8], params: &BfvParams) -> Result<Vec<DealerRowCrossEvaluation>> {
    let mut cursor = Cursor::new(message);
    if cursor.take(8)? != CROSS_ROUND_MAGIC {
        return Err(DistributedCommitteeError::Message("cross-round magic"));
    }
    let count = cursor.length()?;
    if count > 1024 {
        return Err(DistributedCommitteeError::Message("cross-round arity"));
    }
    let mut evaluations = Vec::with_capacity(count);
    for _ in 0..count {
        let wire = cursor.length_prefixed()?;
        evaluations.push(DealerRowCrossEvaluation::from_wire_bytes(wire, params)?);
    }
    if !cursor.finished() {
        return Err(DistributedCommitteeError::Message(
            "trailing cross-round bytes",
        ));
    }
    Ok(evaluations)
}

struct Cursor<'a> {
    bytes: &'a [u8],
    position: usize,
}

impl<'a> Cursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, position: 0 }
    }

    fn take(&mut self, length: usize) -> Result<&'a [u8]> {
        let end = self
            .position
            .checked_add(length)
            .filter(|&end| end <= self.bytes.len())
            .ok_or(DistributedCommitteeError::Message("message truncated"))?;
        let output = &self.bytes[self.position..end];
        self.position = end;
        Ok(output)
    }

    fn length(&mut self) -> Result<usize> {
        let bytes: [u8; 8] = self
            .take(8)?
            .try_into()
            .map_err(|_| DistributedCommitteeError::Message("length field"))?;
        usize::try_from(u64::from_le_bytes(bytes))
            .map_err(|_| DistributedCommitteeError::Message("length overflow"))
    }

    fn length_prefixed(&mut self) -> Result<&'a [u8]> {
        let length = self.length()?;
        self.take(length)
    }

    fn finished(&self) -> bool {
        self.position == self.bytes.len()
    }
}
