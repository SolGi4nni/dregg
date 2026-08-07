//! The PRODUCTION relying-party caller for the distributed threshold committee.
//!
//! [`super::distributed`] is the party-side substrate: `n` separate processes run
//! a sealed native-PQ ceremony and hold one custody share each. Until now the only
//! thing that DROVE them was a test — the relying-party half (agree the collective
//! key, run the verified commit round, ask `t` parties for shares, verify the
//! certificates, combine) lived inline in `tests/distributed_threshold_committee.rs`
//! and nowhere a product could call it. This module is that half, as a reusable
//! object a market or a bin constructs and calls.
//!
//! It holds NO share and never learns one. Its transport identity is enrolled at
//! the committee's relying-party slot (roster index `n`), so its requests and the
//! parties' responses ride the SAME dual-signed hybrid-PQ envelopes as the DKG did.
//!
//! # The custody boundary of a dark clearing
//!
//! A dark clearing's no-single-viewer step is exactly this: a masked aggregate is
//! encrypted to the committee's collective key, and only a `t`-party threshold
//! opening reveals the masked value — no party, and not this caller, sees a curve
//! coefficient. [`DistributedCommitteeClient::open_verified`] is that opening, and
//! it now REFUSES any share that does not carry a valid zero-knowledge decrypt-share
//! certificate, because it combines under
//! [`AuthenticatedQuorumRoster::new_verified`].
//!
//! # Honest scope
//!
//! - The parties are separate PROCESSES over real TCP with the enrolled native-PQ
//!   transport. What remains single-host is deployment: the party binary binds
//!   `LOCALHOST` and rendezvous is a shared filesystem directory. Genuinely-separate
//!   hosting / WAN is the remaining ops item, not a change to this protocol.
//! - The verified rounds are MALICIOUS-party-sound on the commitment surface: the
//!   commit round refuses any party whose published commitment does not carry a
//!   valid [`AggregateRowBindingProof`] tying it to the sum of its dealt rows
//!   ([`super::quorum::assemble_distributed_transcript`] verifies every proof
//!   here, in this caller), and the verified opening refuses any share without a
//!   valid decrypt-share certificate against that commitment. What remains
//!   semi-honest is inherited from [`super::distributed`]: dealer secret
//!   SHORTNESS is unproven (the keygen range-proof seam), and availability is
//!   out of scope.

use std::io::{self, Read, Write};
use std::net::{SocketAddr, TcpStream};
use std::time::Duration;

use fhe::bfv::PublicKey;
use fhe_traits::DeserializeParametrized;

use crate::bfv_lean::LeanCiphertext;
use crate::mpc_party::transport::NativePqTransportIdentity;
use crate::threshold::distributed::{
    decode_commit_response, encode_finalize_request, DistributedCommitteeError, DistributedDkg,
    SEQUENCE_COMMIT_RESPONSE, SEQUENCE_FINALIZE_REQUEST, SEQUENCE_FINALIZE_RESPONSE,
    SEQUENCE_OPEN_REQUEST, SEQUENCE_OPEN_RESPONSE, SEQUENCE_PUBLIC_KEY_RESPONSE,
};
use crate::threshold::quorum::{
    assemble_distributed_transcript, AggregateRowBindingProof, AuthenticatedQuorumCombiner,
    AuthenticatedQuorumRoster, DealerVssCommitment, QuorumError, QuorumOpeningSession,
    VerifiedDkgTranscript,
};
use crate::threshold::{BfvParams, CollectivePublicKey};

/// The public frame kinds a party process answers. The header is public routing
/// only; the sealed envelope inside re-binds route/sequence/roster, so a lying
/// header makes the open fail rather than the party act on the wrong thing. These
/// are the ONE definition the party binary imports, so the two never drift.
pub const KIND_DEALING: u8 = 1;
pub const KIND_CROSS: u8 = 2;
pub const KIND_OPEN_REQUEST: u8 = 3;
pub const KIND_PUBLIC_KEY_REQUEST: u8 = 4;
pub const KIND_SHUTDOWN: u8 = 5;
pub const KIND_COMMIT_REQUEST: u8 = 6;
pub const KIND_FINALIZE_REQUEST: u8 = 7;

/// The largest frame either side will send or accept.
pub const MAX_MESSAGE_BYTES: usize = 16 * 1024 * 1024;

/// Write one length-prefixed frame: `kind(1) | sender(4 BE) | len(4 BE) | payload`.
pub fn write_frame(
    stream: &mut TcpStream,
    kind: u8,
    sender: u32,
    payload: &[u8],
) -> io::Result<()> {
    if payload.len() > MAX_MESSAGE_BYTES {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "outbound message exceeds its allocation limit",
        ));
    }
    let mut header = [0u8; 9];
    header[0] = kind;
    header[1..5].copy_from_slice(&sender.to_be_bytes());
    header[5..].copy_from_slice(&(payload.len() as u32).to_be_bytes());
    stream.write_all(&header)?;
    stream.write_all(payload)?;
    stream.flush()
}

/// Read one frame written by [`write_frame`].
pub fn read_frame(stream: &mut TcpStream) -> io::Result<(u8, u32, Vec<u8>)> {
    let mut header = [0u8; 9];
    stream.read_exact(&mut header)?;
    let sender = u32::from_be_bytes(header[1..5].try_into().expect("4 bytes"));
    let length = u32::from_be_bytes(header[5..].try_into().expect("4 bytes")) as usize;
    if length > MAX_MESSAGE_BYTES {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "inbound message exceeds its allocation limit",
        ));
    }
    let mut payload = vec![0u8; length];
    stream.read_exact(&mut payload)?;
    Ok((header[0], sender, payload))
}

/// Why the relying-party caller could not complete a step.
#[derive(Debug)]
pub enum RelyingPartyError {
    /// The client was built with a roster/key/address shape that cannot address
    /// the committee.
    Configuration(&'static str),
    /// A TCP request to a party failed, or a party returned an empty/refusing
    /// answer to something that must succeed.
    Transport(String),
    /// A party's answer disagreed with another party's — the value it named is not
    /// unanimous, so it is refused rather than picked.
    Disagreement(&'static str),
    /// A sealed-envelope, DKG, or transcript-shape refusal from the committee layer.
    Committee(DistributedCommitteeError),
    /// A quorum/opening/certificate refusal. THIS is where a share missing or
    /// carrying an invalid decrypt-share certificate lands.
    Quorum(QuorumError),
}

impl std::fmt::Display for RelyingPartyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Configuration(why) => write!(f, "relying-party configuration: {why}"),
            Self::Transport(why) => write!(f, "committee transport: {why}"),
            Self::Disagreement(why) => write!(f, "committee parties disagreed: {why}"),
            Self::Committee(error) => write!(f, "committee refusal: {error}"),
            Self::Quorum(error) => write!(f, "quorum/opening refusal: {error:?}"),
        }
    }
}

impl std::error::Error for RelyingPartyError {}

impl From<DistributedCommitteeError> for RelyingPartyError {
    fn from(error: DistributedCommitteeError) -> Self {
        Self::Committee(error)
    }
}

impl From<QuorumError> for RelyingPartyError {
    fn from(error: QuorumError) -> Self {
        Self::Quorum(error)
    }
}

type Result<T> = std::result::Result<T, RelyingPartyError>;

/// Drives the landed distributed committee over its authenticated transport. It is
/// the caller a dark clearing (or any threshold-decrypt consumer) constructs; the
/// `n` custody parties are separate processes it talks to by address.
pub struct DistributedCommitteeClient {
    identity: NativePqTransportIdentity,
    dkg: DistributedDkg,
    party_addresses: Vec<SocketAddr>,
    party_keys: Vec<[u8; 32]>,
    io_timeout: Duration,
}

impl DistributedCommitteeClient {
    /// `identity` is this caller's enrolled relying-party transport identity;
    /// `party_addresses` and `party_keys` are the `n` custody parties' listen
    /// addresses and enrolled Ed25519 custody keys, both indexed by party.
    pub fn new(
        identity: NativePqTransportIdentity,
        dkg: DistributedDkg,
        party_addresses: Vec<SocketAddr>,
        party_keys: Vec<[u8; 32]>,
    ) -> Result<Self> {
        let n = dkg.n_parties();
        if party_addresses.len() != n || party_keys.len() != n {
            return Err(RelyingPartyError::Configuration(
                "one address and one custody key per party are required",
            ));
        }
        Ok(Self {
            identity,
            dkg,
            party_addresses,
            party_keys,
            io_timeout: Duration::from_secs(300),
        })
    }

    pub fn with_io_timeout(mut self, io_timeout: Duration) -> Self {
        self.io_timeout = io_timeout;
        self
    }

    pub fn dkg(&self) -> &DistributedDkg {
        &self.dkg
    }

    pub fn params(&self) -> &BfvParams {
        self.dkg.params()
    }

    /// Send one frame to a party and return its reply payload. The relying party's
    /// roster index is the frame sender, as the party expects.
    fn request(&self, party: usize, kind: u8, payload: &[u8]) -> Result<Vec<u8>> {
        let address = *self
            .party_addresses
            .get(party)
            .ok_or(RelyingPartyError::Configuration("party index out of range"))?;
        let sender = self.dkg.relying_party() as u32;
        let mut stream = TcpStream::connect_timeout(&address, self.io_timeout)
            .map_err(|error| RelyingPartyError::Transport(format!("connect {address}: {error}")))?;
        stream
            .set_read_timeout(Some(self.io_timeout))
            .and_then(|()| stream.set_write_timeout(Some(self.io_timeout)))
            .map_err(|error| RelyingPartyError::Transport(format!("timeouts: {error}")))?;
        write_frame(&mut stream, kind, sender, payload)
            .map_err(|error| RelyingPartyError::Transport(format!("write to {party}: {error}")))?;
        let (_, _, reply) = read_frame(&mut stream)
            .map_err(|error| RelyingPartyError::Transport(format!("read from {party}: {error}")))?;
        Ok(reply)
    }

    /// Ask every party for the collective public key it independently aggregated,
    /// and return it only if all `n` agree. Encrypting to it needs no quorum.
    pub fn collective_public_key(&self) -> Result<CollectivePublicKey> {
        let mut collective_bytes: Option<Vec<u8>> = None;
        for party in 0..self.dkg.n_parties() {
            let sealed = self.request(party, KIND_PUBLIC_KEY_REQUEST, &[])?;
            if sealed.is_empty() {
                return Err(RelyingPartyError::Transport(format!(
                    "party {party} is not ready to publish the collective key"
                )));
            }
            let answer = self.dkg.open(
                &self.identity,
                party,
                self.dkg.relying_party(),
                SEQUENCE_PUBLIC_KEY_RESPONSE,
                &sealed,
            )?;
            if answer.len() < 32 {
                return Err(RelyingPartyError::Transport(format!(
                    "party {party} returned a malformed collective-key answer"
                )));
            }
            let key_bytes = answer[32..].to_vec();
            match &collective_bytes {
                None => collective_bytes = Some(key_bytes),
                Some(expected) if expected != &key_bytes => {
                    return Err(RelyingPartyError::Disagreement(
                        "two parties reported different collective public keys",
                    ));
                }
                Some(_) => {}
            }
        }
        let key_bytes =
            collective_bytes.ok_or(RelyingPartyError::Configuration("no custody parties"))?;
        let pk = PublicKey::from_bytes(&key_bytes, self.dkg.params().arc()).map_err(|_| {
            RelyingPartyError::Transport("collective public key did not parse".into())
        })?;
        Ok(CollectivePublicKey { pk })
    }

    /// Run the verified commit round and return the shared transcript the decrypt-
    /// share certificates anchor to.
    ///
    /// Two rounds, both request/response: (1) collect every party's public
    /// aggregate-row commitment vector, its [`AggregateRowBindingProof`], and the
    /// FULL dealer commitments it accepted, refusing unless every party names the
    /// SAME dealings and refusing ANY party whose commitment does not prove equal
    /// to the sum of its dealt rows ([`QuorumError::PartyCommitmentUnbound`]);
    /// (2) hand the assembled ordered commitment+proof set back to every party so
    /// each completes its certificate-capable custody. The transcript is then
    /// usable for [`open_verified`](Self::open_verified).
    pub fn verified_transcript(
        &self,
        collective: &CollectivePublicKey,
    ) -> Result<VerifiedDkgTranscript> {
        let n = self.dkg.n_parties();
        let mut dealer_commitments: Option<Vec<DealerVssCommitment>> = None;
        let mut party_secret_commitments: Vec<Vec<[u8; 32]>> = Vec::with_capacity(n);
        let mut binding_proofs: Vec<AggregateRowBindingProof> = Vec::with_capacity(n);
        for party in 0..n {
            let sealed = self.request(party, KIND_COMMIT_REQUEST, &[])?;
            if sealed.is_empty() {
                return Err(RelyingPartyError::Transport(format!(
                    "party {party} is not ready to publish its secret-share commitment"
                )));
            }
            let message = self.dkg.open(
                &self.identity,
                party,
                self.dkg.relying_party(),
                SEQUENCE_COMMIT_RESPONSE,
                &sealed,
            )?;
            let (dealers, commitments, proof) =
                decode_commit_response(&message, self.dkg.session(), self.dkg.params())?;
            match &dealer_commitments {
                None => dealer_commitments = Some(dealers),
                Some(expected) if expected != &dealers => {
                    return Err(RelyingPartyError::Disagreement(
                        "two parties accepted different dealer commitment sets",
                    ));
                }
                Some(_) => {}
            }
            party_secret_commitments.push(commitments);
            binding_proofs.push(proof);
        }
        let dealer_commitments =
            dealer_commitments.ok_or(RelyingPartyError::Configuration("no custody parties"))?;
        let transcript = assemble_distributed_transcript(
            self.dkg.session(),
            &dealer_commitments,
            party_secret_commitments.clone(),
            &binding_proofs,
            collective,
            self.dkg.params(),
        )
        .map_err(RelyingPartyError::Quorum)?;

        let finalize_body = encode_finalize_request(&party_secret_commitments, &binding_proofs);
        for party in 0..n {
            let sealed = self.dkg.seal(
                &self.identity,
                self.dkg.relying_party(),
                party,
                SEQUENCE_FINALIZE_REQUEST,
                &finalize_body,
            )?;
            let sealed_ack = self.request(party, KIND_FINALIZE_REQUEST, &sealed)?;
            if sealed_ack.is_empty() {
                return Err(RelyingPartyError::Transport(format!(
                    "party {party} refused to finalize its verified custody"
                )));
            }
            // The ack is sealed and route-bound like everything else; opening it is
            // the proof the answer came from the enrolled party, not a router.
            self.dkg.open(
                &self.identity,
                party,
                self.dkg.relying_party(),
                SEQUENCE_FINALIZE_RESPONSE,
                &sealed_ack,
            )?;
        }
        Ok(transcript)
    }

    /// Open one ciphertext under a `t`-party quorum, REFUSING any share without a
    /// valid decrypt-share certificate.
    ///
    /// `roster` names exactly `t` live custody parties in increasing order. Each
    /// produces a certificate-carrying signed share in its own process; the
    /// verified combiner authenticates every one, then verifies every certificate
    /// against `transcript`, before combining. A share with no certificate is
    /// refused as [`QuorumError::MissingDecryptShareProof`]; one whose certificate
    /// does not verify, as [`QuorumError::InvalidDecryptShareProof`].
    pub fn open_verified(
        &self,
        transcript: &VerifiedDkgTranscript,
        ciphertext_bytes: &[u8],
        plain_bound: u64,
        roster: &[usize],
        nonce: [u8; 32],
    ) -> Result<Vec<u64>> {
        let params = self.dkg.params();
        let opening = QuorumOpeningSession::new_verified(
            self.dkg.session().clone(),
            transcript,
            nonce,
            roster.to_vec(),
        )
        .map_err(RelyingPartyError::Quorum)?;
        let lean = LeanCiphertext::from_fhe_bytes(
            ciphertext_bytes,
            params.moduli(),
            params.degree(),
            plain_bound,
        )
        .map_err(|_| RelyingPartyError::Transport("ciphertext did not parse".into()))?;
        let request_body = encode_open_request(nonce, roster, plain_bound, ciphertext_bytes);

        let mut framed = Vec::with_capacity(roster.len());
        for &party in roster {
            let sealed_request = self.dkg.seal(
                &self.identity,
                self.dkg.relying_party(),
                party,
                SEQUENCE_OPEN_REQUEST,
                &request_body,
            )?;
            let sealed_answer = self.request(party, KIND_OPEN_REQUEST, &sealed_request)?;
            if sealed_answer.is_empty() {
                return Err(RelyingPartyError::Transport(format!(
                    "party {party} refused to answer the opening"
                )));
            }
            framed.push(self.dkg.open(
                &self.identity,
                party,
                self.dkg.relying_party(),
                SEQUENCE_OPEN_RESPONSE,
                &sealed_answer,
            )?);
        }

        let quorum_roster = AuthenticatedQuorumRoster::new_verified(
            self.dkg.session().clone(),
            transcript,
            self.party_keys.clone(),
        )
        .map_err(RelyingPartyError::Quorum)?;
        AuthenticatedQuorumCombiner::new(quorum_roster)
            .combine_framed(&opening, &lean, &framed, params)
            .map_err(RelyingPartyError::Quorum)
    }

    /// Send the fire-and-forget shutdown frame to a party.
    pub fn shutdown(&self, party: usize) {
        let Some(&address) = self.party_addresses.get(party) else {
            return;
        };
        let Ok(mut stream) = TcpStream::connect_timeout(&address, self.io_timeout) else {
            return;
        };
        let _ = write_frame(
            &mut stream,
            KIND_SHUTDOWN,
            self.dkg.relying_party() as u32,
            &[],
        );
    }
}

/// The opening-request body, shared by this caller and the party binary so the two
/// never grow divergent framings: `nonce(32) | roster_len | roster | plain_bound |
/// ct_len | ciphertext`.
pub fn encode_open_request(
    nonce: [u8; 32],
    roster: &[usize],
    plain_bound: u64,
    ciphertext: &[u8],
) -> Vec<u8> {
    let mut out = Vec::with_capacity(56 + roster.len() * 8 + ciphertext.len());
    out.extend_from_slice(&nonce);
    out.extend_from_slice(&(roster.len() as u64).to_le_bytes());
    for &party in roster {
        out.extend_from_slice(&(party as u64).to_le_bytes());
    }
    out.extend_from_slice(&plain_bound.to_le_bytes());
    out.extend_from_slice(&(ciphertext.len() as u64).to_le_bytes());
    out.extend_from_slice(ciphertext);
    out
}

/// Parse an opening-request body. Returns `(nonce, roster, plain_bound,
/// ciphertext)`.
pub fn decode_open_request(
    bytes: &[u8],
) -> std::result::Result<([u8; 32], Vec<usize>, u64, Vec<u8>), &'static str> {
    let mut position = 0usize;
    let mut take = |length: usize| -> std::result::Result<&[u8], &'static str> {
        let end = position
            .checked_add(length)
            .filter(|&end| end <= bytes.len())
            .ok_or("truncated opening request")?;
        let output = &bytes[position..end];
        position = end;
        Ok(output)
    };
    let nonce: [u8; 32] = take(32)?.try_into().map_err(|_| "nonce")?;
    let count = u64::from_le_bytes(take(8)?.try_into().map_err(|_| "count")?) as usize;
    if count > 1024 {
        return Err("opening roster arity");
    }
    let mut roster = Vec::with_capacity(count);
    for _ in 0..count {
        roster.push(u64::from_le_bytes(take(8)?.try_into().map_err(|_| "party")?) as usize);
    }
    let plain_bound = u64::from_le_bytes(take(8)?.try_into().map_err(|_| "bound")?);
    let length = u64::from_le_bytes(take(8)?.try_into().map_err(|_| "length")?) as usize;
    let ciphertext = take(length)?.to_vec();
    Ok((nonce, roster, plain_bound, ciphertext))
}
