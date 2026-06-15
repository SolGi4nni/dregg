//! The DKG **ceremony** — the transport + agreement layer for [`crate::dkg`]
//! (the ceremony-as-cell-app lane the dkg.rs NOTES name).
//!
//! [`crate::dkg`] is the pure protocol: Feldman rounds, Ack/Complaint, QUAL,
//! [`DkgOutput`] → `BeaconShare`. It deliberately models transport as "bytes
//! that arrived" and assumes a COMMON VIEW. This module supplies what that
//! leaves open, mapped onto the organs (docs/ORGANS.md):
//!
//! * **Authenticated broadcast** — every round message rides as a
//!   [`SignedCeremonyMsg`]: an ed25519 signature over a domain-tagged
//!   transcript binding `(ceremony id ‖ signer index ‖ message bytes)`. The
//!   blocklace (or the hosted node service) carries the signed bytes; the
//!   signature is what makes a dealing/complaint/reveal ATTRIBUTABLE — the
//!   precondition for slashing.
//! * **The common view** — [`CeremonyView`]: the deterministic accumulator
//!   every party feeds the same agreed message sequence. Its per-round
//!   canonical roots ([`CeremonyView::dealings_root`] /
//!   [`responses_root`](CeremonyView::responses_root) /
//!   [`reveals_root`](CeremonyView::reveals_root)) are the values the
//!   ceremony CELL pins on each round-closing turn
//!   (`dregg_cell::blueprint` DKG section) — so "we computed QUAL over the
//!   same view" is checkable against the chain, not asserted.
//! * **Private shares** — [`SealedShare`]: the seal-pair shape
//!   (ephemeral X25519 → HKDF → ChaCha20-Poly1305, the captp
//!   `store_forward` primitives), with the ceremony id, dealer, and
//!   recipient bound into the sealed payload so a share cannot be replayed
//!   into another ceremony or re-addressed.
//! * **Equivocation evidence** — two DIFFERENT signed dealings from one
//!   dealer in one ceremony are kept as an [`EquivocationEvidence`] pair
//!   (both signed, hence self-certifying). Per the dkg.rs stance, the FIRST
//!   dealing in the agreed order stays operative (every honest party adopts
//!   the same one, so the run is consistent); the evidence is what the
//!   court/obligation lane slashes on.
//! * **Slash attribution** — [`CeremonyView::offenses`]: the witness-first
//!   reading of the complaint round (ORGANS §5). A complaint answered by a
//!   verifying reveal convicts the COMPLAINER ([`Offense::FalseComplaint`] —
//!   the dealer exhibited the witness); an unanswered (or failing-reveal)
//!   complaint convicts the DEALER ([`Offense::BadDealing`]). Deterministic
//!   in the agreed view, like `compute_qual` — every honest party computes
//!   the same slash set. The slash itself is an obligation-cell move
//!   (`dregg_cell::blueprint::obligation_factory_descriptor`), not done here.
//!
//! # Honest residues (named, loud)
//!
//! * The bond posting/slashing pipe (participants post obligation cells at
//!   enrollment; an [`Offense`] becomes the slash leg's justification) is the
//!   adjudication lane's composition — this module produces the attributable
//!   evidence, the court executes the move.
//! * In the HOSTED node service the node relays the signed messages; the
//!   agreed-order property is the node's sequencing plus the on-cell round
//!   roots (auditable, equivocation-detectable, not yet BFT-agreed). Full
//!   blocklace carriage replaces the relay without touching this module:
//!   everything here is already deterministic in the message sequence.

use std::collections::{BTreeMap, BTreeSet};

use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};
use serde::{Deserialize, Serialize};

use dregg_captp::store_forward::{decrypt_from_sender, encrypt_for_destination};

use crate::dkg::{
    Complaint, ComplaintReveal, Dealing, DkgError, DkgOutput, DkgParams, DkgParticipant,
    PrivateShare, ShareResponse, compute_qual,
};

/// Domain tag for the signed-message transcript.
const CEREMONY_SIG_DOMAIN: &str = "dregg-dkg-ceremony-sig-v1";
/// Domain tag for the sealed private-share payload.
const CEREMONY_SHARE_DOMAIN: &str = "dregg-dkg-ceremony-share-v1";
/// Domain tags for the per-round canonical roots (the on-cell commitments).
const DEALINGS_ROOT_DOMAIN: &str = "dregg-dkg-dealings-root-v1";
const RESPONSES_ROOT_DOMAIN: &str = "dregg-dkg-responses-root-v1";
const REVEALS_ROOT_DOMAIN: &str = "dregg-dkg-reveals-root-v1";
/// Domain tag for the finalize output commitment (the on-cell output slot).
const OUTPUT_COMMIT_DOMAIN: &str = "dregg-dkg-output-commit-v1";

// =============================================================================
// Errors
// =============================================================================

/// Every way the ceremony layer refuses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CeremonyError {
    /// Underlying DKG-protocol error.
    Dkg(DkgError),
    /// A signature did not verify (or the signer index has no roster key).
    BadSignature {
        /// The claimed signer index.
        signer: usize,
    },
    /// The message's claimed author index does not match the signer index
    /// (e.g. a dealing for dealer 3 signed by participant 2).
    AuthorMismatch {
        /// The signing participant.
        signer: usize,
        /// The index the message body claims to be from.
        claimed: usize,
    },
    /// A sealed share whose bound ceremony id is not this ceremony.
    WrongCeremony,
    /// A sealed share addressed to someone else (or whose inner binding
    /// disagrees with its envelope).
    NotForMe {
        /// Our index.
        expected: usize,
        /// The envelope's recipient.
        got: usize,
    },
    /// The sealed payload failed to open (wrong key, tampered ciphertext).
    SealFailure,
    /// Byte-level decode failure.
    Serialization,
}

impl From<DkgError> for CeremonyError {
    fn from(e: DkgError) -> Self {
        CeremonyError::Dkg(e)
    }
}

impl std::fmt::Display for CeremonyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CeremonyError::Dkg(e) => write!(f, "dkg: {e}"),
            CeremonyError::BadSignature { signer } => {
                write!(f, "signature from participant {signer} did not verify")
            }
            CeremonyError::AuthorMismatch { signer, claimed } => {
                write!(
                    f,
                    "participant {signer} signed a message claiming author {claimed}"
                )
            }
            CeremonyError::WrongCeremony => write!(f, "sealed share bound to another ceremony"),
            CeremonyError::NotForMe { expected, got } => {
                write!(f, "sealed share for participant {got} opened by {expected}")
            }
            CeremonyError::SealFailure => write!(f, "sealed share failed to open"),
            CeremonyError::Serialization => write!(f, "ceremony serialization error"),
        }
    }
}

impl std::error::Error for CeremonyError {}

// =============================================================================
// Roster — who is in the ceremony (the cell pins its commitment)
// =============================================================================

/// One ceremony participant's public identity: DKG index, cell id, the
/// X25519 seal key private shares are sealed to, and the ed25519 key round
/// messages are signed with. The ceremony cell's roster slot commits to the
/// full sorted leaf set (`dregg_cell::blueprint::dkg_participant_leaf` /
/// `dkg_roster_root`), so the descriptor content-addresses the EXACT
/// participant set — a ceremony IS its roster.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RosterEntry {
    /// 1-based DKG participant index.
    pub index: usize,
    /// The participant's cell id (raw 32 bytes — kept curve/crate-agnostic).
    pub cell: [u8; 32],
    /// X25519 public key private shares are sealed to.
    pub seal_pk: [u8; 32],
    /// ed25519 public key round messages are verified against.
    pub auth_pk: [u8; 32],
}

/// The ceremony roster: index → entry, every index in `1..=n` present.
pub type CeremonyRoster = BTreeMap<usize, RosterEntry>;

/// Validate a roster against `params`: exactly the indices `1..=n`, each
/// entry self-consistent.
pub fn validate_roster(params: &DkgParams, roster: &CeremonyRoster) -> Result<(), CeremonyError> {
    if roster.len() != params.n {
        return Err(CeremonyError::Dkg(DkgError::InvalidParameters));
    }
    for (i, entry) in roster {
        if *i == 0 || *i > params.n || entry.index != *i {
            return Err(CeremonyError::Dkg(DkgError::IndexOutOfRange { index: *i }));
        }
    }
    Ok(())
}

// =============================================================================
// Round messages on the wire
// =============================================================================

/// One broadcast round message (the union [`crate::dkg`] rounds 1–3 speak).
/// Private shares are NOT here — they ride [`SealedShare`]s.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CeremonyMsg {
    /// Round 1: a dealer's Feldman commitments.
    Dealing(Dealing),
    /// Round 2: a recipient's typed Ack/Complaint.
    Response(ShareResponse),
    /// Round 3: a complained-against dealer's public reveal.
    Reveal(ComplaintReveal),
}

impl CeremonyMsg {
    /// The participant index this message claims to be authored by — the
    /// index the SIGNATURE must come from ([`SignedCeremonyMsg::verify`]).
    pub fn author(&self) -> usize {
        match self {
            CeremonyMsg::Dealing(d) => d.dealer,
            CeremonyMsg::Response(ShareResponse::Ack { member, .. }) => *member,
            CeremonyMsg::Response(ShareResponse::Complaint(c)) => c.complainer,
            CeremonyMsg::Reveal(r) => r.dealer,
        }
    }

    /// Canonical bytes (postcard — every inner type is serde with canonical
    /// byte codecs for the point-carrying ones).
    pub fn to_bytes(&self) -> Vec<u8> {
        postcard::to_allocvec(self).expect("serialization cannot fail")
    }

    /// Decode canonical bytes (validates curve points on the way in via the
    /// inner byte codecs).
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, CeremonyError> {
        postcard::from_bytes(bytes).map_err(|_| CeremonyError::Serialization)
    }
}

/// The signed transcript bytes for one message in one ceremony.
fn signing_transcript(ceremony: &[u8; 32], signer: usize, msg_bytes: &[u8]) -> Vec<u8> {
    let mut t = Vec::with_capacity(CEREMONY_SIG_DOMAIN.len() + 32 + 8 + msg_bytes.len());
    t.extend_from_slice(CEREMONY_SIG_DOMAIN.as_bytes());
    t.extend_from_slice(ceremony);
    t.extend_from_slice(&(signer as u64).to_le_bytes());
    t.extend_from_slice(msg_bytes);
    t
}

/// A round message + its authenticated-broadcast envelope: who signed it,
/// for which ceremony, with what signature. THIS is the wire unit (it rides
/// a turn payload / the blocklace / the node relay).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SignedCeremonyMsg {
    /// The ceremony (cell id raw bytes) this message belongs to.
    pub ceremony: [u8; 32],
    /// The signing participant's 1-based index.
    pub signer: usize,
    /// The message.
    pub msg: CeremonyMsg,
    /// ed25519 signature over [`signing_transcript`].
    #[serde(with = "serde_sig64")]
    pub signature: [u8; 64],
}

/// serde for the 64-byte signature ([`serde`] derives only auto-cover arrays
/// up to length 32). Mirrors `dregg_types`'s own `serde_64` (length-checked
/// on the way in), kept local since that helper is crate-private.
mod serde_sig64 {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer>(bytes: &[u8; 64], serializer: S) -> Result<S::Ok, S::Error> {
        bytes.as_ref().serialize(serializer)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<[u8; 64], D::Error> {
        let v: Vec<u8> = Deserialize::deserialize(deserializer)?;
        v.try_into()
            .map_err(|_| serde::de::Error::custom("expected 64 bytes"))
    }
}

impl SignedCeremonyMsg {
    /// Sign `msg` for `ceremony` as participant `signer`.
    pub fn sign(
        ceremony: [u8; 32],
        signer: usize,
        msg: CeremonyMsg,
        signing_key: &[u8; 32],
    ) -> Self {
        let sk = SigningKey::from_bytes(signing_key);
        let transcript = signing_transcript(&ceremony, signer, &msg.to_bytes());
        let signature = sk.sign(&transcript).to_bytes();
        SignedCeremonyMsg {
            ceremony,
            signer,
            msg,
            signature,
        }
    }

    /// Verify against the roster: the signature must check under the
    /// SIGNER's roster key, AND the signer must BE the message's claimed
    /// author (a participant cannot forge rounds for another index).
    pub fn verify(
        &self,
        ceremony: &[u8; 32],
        roster: &CeremonyRoster,
    ) -> Result<(), CeremonyError> {
        if &self.ceremony != ceremony {
            return Err(CeremonyError::WrongCeremony);
        }
        let claimed = self.msg.author();
        if claimed != self.signer {
            return Err(CeremonyError::AuthorMismatch {
                signer: self.signer,
                claimed,
            });
        }
        let entry = roster
            .get(&self.signer)
            .ok_or(CeremonyError::BadSignature {
                signer: self.signer,
            })?;
        let vk =
            VerifyingKey::from_bytes(&entry.auth_pk).map_err(|_| CeremonyError::BadSignature {
                signer: self.signer,
            })?;
        let transcript = signing_transcript(&self.ceremony, self.signer, &self.msg.to_bytes());
        vk.verify(&transcript, &Signature::from_bytes(&self.signature))
            .map_err(|_| CeremonyError::BadSignature {
                signer: self.signer,
            })
    }

    /// Canonical wire bytes.
    pub fn to_bytes(&self) -> Vec<u8> {
        postcard::to_allocvec(self).expect("serialization cannot fail")
    }

    /// Decode wire bytes.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, CeremonyError> {
        postcard::from_bytes(bytes).map_err(|_| CeremonyError::Serialization)
    }
}

// =============================================================================
// Sealed private shares (the seal-pair leg)
// =============================================================================

/// A private share sealed to its recipient: ephemeral X25519 → HKDF →
/// ChaCha20-Poly1305 (the captp `store_forward` seal-pair). The payload
/// binds `(domain ‖ ceremony ‖ dealer ‖ recipient ‖ share bytes)`, so a
/// sealed share replayed into another ceremony — or re-addressed to another
/// participant — fails to open coherently and is refused.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SealedShare {
    /// The ceremony (cell id raw bytes).
    pub ceremony: [u8; 32],
    /// The dealing participant.
    pub dealer: usize,
    /// The participant this share is sealed to.
    pub recipient: usize,
    /// Sender's ephemeral X25519 public key.
    pub ephemeral_pk: [u8; 32],
    /// The sealed payload.
    pub ciphertext: Vec<u8>,
}

fn share_payload(ceremony: &[u8; 32], share: &PrivateShare) -> Vec<u8> {
    let mut p = Vec::with_capacity(CEREMONY_SHARE_DOMAIN.len() + 32 + 16 + share.share_bytes.len());
    p.extend_from_slice(CEREMONY_SHARE_DOMAIN.as_bytes());
    p.extend_from_slice(ceremony);
    p.extend_from_slice(&(share.dealer as u64).to_le_bytes());
    p.extend_from_slice(&(share.recipient as u64).to_le_bytes());
    p.extend_from_slice(&share.share_bytes);
    p
}

/// Seal one private share to `recipient_seal_pk`.
pub fn seal_share(
    ceremony: &[u8; 32],
    share: &PrivateShare,
    recipient_seal_pk: &[u8; 32],
) -> SealedShare {
    let payload = share_payload(ceremony, share);
    let (ephemeral_pk, ciphertext) =
        encrypt_for_destination(&payload, recipient_seal_pk, &[0u8; 32]);
    SealedShare {
        ceremony: *ceremony,
        dealer: share.dealer,
        recipient: share.recipient,
        ephemeral_pk,
        ciphertext,
    }
}

/// Open a sealed share as participant `my_index` of `ceremony`, checking
/// every binding fail-closed: envelope ceremony/recipient, AEAD opening, and
/// the INNER bindings (domain, ceremony, dealer, recipient) against the
/// envelope — a mismatch anywhere refuses.
pub fn open_share(
    sealed: &SealedShare,
    ceremony: &[u8; 32],
    my_index: usize,
    my_seal_secret: &[u8; 32],
) -> Result<PrivateShare, CeremonyError> {
    if &sealed.ceremony != ceremony {
        return Err(CeremonyError::WrongCeremony);
    }
    if sealed.recipient != my_index {
        return Err(CeremonyError::NotForMe {
            expected: my_index,
            got: sealed.recipient,
        });
    }
    let payload = decrypt_from_sender(&sealed.ciphertext, &sealed.ephemeral_pk, my_seal_secret)
        .map_err(|_| CeremonyError::SealFailure)?;
    let prefix_len = CEREMONY_SHARE_DOMAIN.len() + 32 + 16;
    if payload.len() < prefix_len {
        return Err(CeremonyError::SealFailure);
    }
    let (head, share_bytes) = payload.split_at(prefix_len);
    let (domain, rest) = head.split_at(CEREMONY_SHARE_DOMAIN.len());
    let (cid, idx) = rest.split_at(32);
    let dealer = u64::from_le_bytes(idx[0..8].try_into().expect("8 bytes")) as usize;
    let recipient = u64::from_le_bytes(idx[8..16].try_into().expect("8 bytes")) as usize;
    if domain != CEREMONY_SHARE_DOMAIN.as_bytes() || cid != ceremony {
        return Err(CeremonyError::WrongCeremony);
    }
    if dealer != sealed.dealer || recipient != sealed.recipient {
        return Err(CeremonyError::SealFailure);
    }
    Ok(PrivateShare {
        dealer,
        recipient,
        share_bytes: share_bytes.to_vec(),
    })
}

// =============================================================================
// Equivocation evidence + offense attribution (the slashable record)
// =============================================================================

/// Two DIFFERENT signed dealings from one dealer in one ceremony —
/// self-certifying (both signatures verify under the dealer's roster key
/// over conflicting bodies), retained for the court/obligation lane.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EquivocationEvidence {
    /// The equivocating dealer.
    pub dealer: usize,
    /// The first signed dealing (the operative one — first in agreed order).
    pub first: SignedCeremonyMsg,
    /// The conflicting second.
    pub second: SignedCeremonyMsg,
}

impl EquivocationEvidence {
    /// Re-check the evidence from scratch: both messages verify under the
    /// roster, both are dealings from `dealer`, and the bodies DIFFER.
    /// Anyone holding the roster can convict — no trust in the reporter.
    pub fn verify(&self, ceremony: &[u8; 32], roster: &CeremonyRoster) -> bool {
        self.first.verify(ceremony, roster).is_ok()
            && self.second.verify(ceremony, roster).is_ok()
            && matches!(&self.first.msg, CeremonyMsg::Dealing(d) if d.dealer == self.dealer)
            && matches!(&self.second.msg, CeremonyMsg::Dealing(d) if d.dealer == self.dealer)
            && self.first.msg != self.second.msg
    }
}

/// An attributable ceremony offense — what the adjudication lane slashes a
/// participant's obligation bond over. Deterministic in the agreed view
/// ([`CeremonyView::offenses`]), so every honest party computes the same
/// slash set; each variant names the WITNESS that convicts.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Offense {
    /// Two conflicting signed dealings (witness: the evidence pair itself).
    Equivocation(EquivocationEvidence),
    /// A complaint the dealer answered with a VERIFYING reveal — the
    /// complaint was unjustified (witness-first: the exhibit decides).
    FalseComplaint {
        /// The convicted complainer.
        complainer: usize,
        /// The dealer who exhibited the verifying reveal.
        dealer: usize,
    },
    /// A complaint left unanswered (silence) or answered with a reveal that
    /// FAILS against the dealer's own commitments — the dealer's fault
    /// either way; QUAL already excludes them ([`compute_qual`]).
    BadDealing {
        /// The convicted dealer.
        dealer: usize,
        /// The complainer whose complaint stands.
        complainer: usize,
    },
}

impl Offense {
    /// The participant the offense convicts (the bond to slash).
    pub fn offender(&self) -> usize {
        match self {
            Offense::Equivocation(e) => e.dealer,
            Offense::FalseComplaint { complainer, .. } => *complainer,
            Offense::BadDealing { dealer, .. } => *dealer,
        }
    }
}

// =============================================================================
// The common view
// =============================================================================

/// The deterministic agreed-view accumulator. Feed every party the same
/// signed-message sequence (the blocklace order / the hosted relay's
/// sequence) and every derived value here — roots, QUAL, offenses, the
/// public output — is identical across parties, which is exactly the
/// agreement [`compute_qual`]'s docs require the ceremony lane to supply.
///
/// Verification discipline: [`CeremonyView::record`] VERIFIES the signature
/// and author binding before accepting anything, so an unauthenticated or
/// cross-signed message can never enter the view (and therefore never enter
/// a root the cell pins).
#[derive(Clone, Debug)]
pub struct CeremonyView {
    ceremony: [u8; 32],
    params: DkgParams,
    roster: CeremonyRoster,
    /// dealer → the FIRST verified signed dealing (the operative one).
    dealings: BTreeMap<usize, SignedCeremonyMsg>,
    /// Conflicting-dealing evidence, in detection order.
    equivocations: Vec<EquivocationEvidence>,
    /// Verified acks, deduped: (dealer, member).
    acks: BTreeSet<(usize, usize)>,
    /// Verified complaints, deduped: (dealer, complainer).
    complaints: BTreeSet<(usize, usize)>,
    /// Verified reveals, deduped by canonical bytes, keyed
    /// (dealer, recipient) → reveal. A dealer answering twice with
    /// different bytes keeps the FIRST (same first-wins stance as dealings).
    reveals: BTreeMap<(usize, usize), ComplaintReveal>,
}

/// What [`CeremonyView::record`] did with a verified message.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Recorded {
    /// Entered the view (first occurrence).
    Fresh,
    /// Byte-identical duplicate — idempotent, ignored.
    Duplicate,
    /// A CONFLICTING dealing: evidence retained, first dealing operative.
    Equivocation(EquivocationEvidence),
}

impl CeremonyView {
    /// An empty view for one ceremony. Fails if the roster does not match
    /// the params.
    pub fn new(
        ceremony: [u8; 32],
        params: DkgParams,
        roster: CeremonyRoster,
    ) -> Result<Self, CeremonyError> {
        validate_roster(&params, &roster)?;
        Ok(CeremonyView {
            ceremony,
            params,
            roster,
            dealings: BTreeMap::new(),
            equivocations: Vec::new(),
            acks: BTreeSet::new(),
            complaints: BTreeSet::new(),
            reveals: BTreeMap::new(),
        })
    }

    /// The ceremony id.
    pub fn ceremony(&self) -> &[u8; 32] {
        &self.ceremony
    }

    /// The params.
    pub fn params(&self) -> &DkgParams {
        &self.params
    }

    /// The roster.
    pub fn roster(&self) -> &CeremonyRoster {
        &self.roster
    }

    /// Number of operative dealings.
    pub fn dealing_count(&self) -> usize {
        self.dealings.len()
    }

    /// The operative (first) dealing of `dealer`, if any.
    pub fn dealing_of(&self, dealer: usize) -> Option<&Dealing> {
        self.dealings.get(&dealer).map(|s| match &s.msg {
            CeremonyMsg::Dealing(d) => d,
            _ => unreachable!("dealings map holds only Dealing messages"),
        })
    }

    /// All verified complaints (sorted by (dealer, complainer)).
    pub fn complaints(&self) -> Vec<Complaint> {
        self.complaints
            .iter()
            .map(|&(dealer, complainer)| Complaint { dealer, complainer })
            .collect()
    }

    /// All verified reveals (sorted by (dealer, recipient)).
    pub fn reveals(&self) -> Vec<ComplaintReveal> {
        self.reveals.values().cloned().collect()
    }

    /// Acks recorded (sorted).
    pub fn acks(&self) -> &BTreeSet<(usize, usize)> {
        &self.acks
    }

    /// Equivocation evidence retained so far.
    pub fn equivocations(&self) -> &[EquivocationEvidence] {
        &self.equivocations
    }

    /// Record one signed message. Verifies the signature + author binding
    /// FIRST (fail-closed: nothing unverified enters the view), then files
    /// it; well-formedness of a dealing (commitment length, valid points)
    /// is also checked here so a malformed dealing never becomes operative
    /// (its dealer simply has no stored dealing — out of QUAL, exactly the
    /// `DkgParticipant::receive_dealing` stance).
    pub fn record(&mut self, signed: &SignedCeremonyMsg) -> Result<Recorded, CeremonyError> {
        signed.verify(&self.ceremony, &self.roster)?;
        match &signed.msg {
            CeremonyMsg::Dealing(d) => {
                if d.commitments().len() != self.params.t {
                    return Err(CeremonyError::Dkg(DkgError::MalformedDealing {
                        dealer: d.dealer,
                    }));
                }
                match self.dealings.get(&d.dealer) {
                    None => {
                        self.dealings.insert(d.dealer, signed.clone());
                        Ok(Recorded::Fresh)
                    }
                    Some(first) if first.msg == signed.msg => Ok(Recorded::Duplicate),
                    Some(first) => {
                        let evidence = EquivocationEvidence {
                            dealer: d.dealer,
                            first: first.clone(),
                            second: signed.clone(),
                        };
                        // Retain each distinct conflicting pair once.
                        if !self.equivocations.contains(&evidence) {
                            self.equivocations.push(evidence.clone());
                        }
                        Ok(Recorded::Equivocation(evidence))
                    }
                }
            }
            CeremonyMsg::Response(ShareResponse::Ack { dealer, member }) => {
                Ok(if self.acks.insert((*dealer, *member)) {
                    Recorded::Fresh
                } else {
                    Recorded::Duplicate
                })
            }
            CeremonyMsg::Response(ShareResponse::Complaint(c)) => {
                Ok(if self.complaints.insert((c.dealer, c.complainer)) {
                    Recorded::Fresh
                } else {
                    Recorded::Duplicate
                })
            }
            CeremonyMsg::Reveal(r) => match self.reveals.get(&(r.dealer, r.recipient)) {
                None => {
                    self.reveals.insert((r.dealer, r.recipient), r.clone());
                    Ok(Recorded::Fresh)
                }
                Some(first) if first == r => Ok(Recorded::Duplicate),
                Some(_) => Ok(Recorded::Duplicate), // first answer stands
            },
        }
    }

    fn root_over(domain: &str, items: impl Iterator<Item = Vec<u8>>) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key(domain);
        let collected: Vec<Vec<u8>> = items.collect();
        hasher.update(&(collected.len() as u64).to_le_bytes());
        for item in collected {
            hasher.update(&(item.len() as u64).to_le_bytes());
            hasher.update(&item);
        }
        *hasher.finalize().as_bytes()
    }

    /// Canonical root over the operative dealing set (sorted by dealer) —
    /// what the cell's dealings-root slot pins at the round close. Order-
    /// independent in the message arrival order (modulo equivocation
    /// first-wins, which the agreed sequence makes identical for everyone).
    pub fn dealings_root(&self) -> [u8; 32] {
        Self::root_over(
            DEALINGS_ROOT_DOMAIN,
            self.dealings.values().map(|s| s.to_bytes()),
        )
    }

    /// Canonical root over the response round: sorted acks then sorted
    /// complaints.
    pub fn responses_root(&self) -> [u8; 32] {
        let acks = self
            .acks
            .iter()
            .map(|&(d, m)| postcard::to_allocvec(&("ack", d as u64, m as u64)).expect("serde"));
        let complaints = self.complaints.iter().map(|&(d, c)| {
            postcard::to_allocvec(&("complaint", d as u64, c as u64)).expect("serde")
        });
        Self::root_over(RESPONSES_ROOT_DOMAIN, acks.chain(complaints))
    }

    /// Canonical root over the reveal round (sorted by (dealer, recipient)).
    pub fn reveals_root(&self) -> [u8; 32] {
        Self::root_over(
            REVEALS_ROOT_DOMAIN,
            self.reveals
                .values()
                .map(|r| postcard::to_allocvec(r).expect("serde")),
        )
    }

    /// QUAL over this view — [`compute_qual`] verbatim (deterministic given
    /// the agreed view; equivocators keep their FIRST dealing operative per
    /// the dkg.rs stance — the slash, not exclusion, is the deterrent).
    pub fn qual(&self) -> BTreeSet<usize> {
        let dealings: BTreeMap<usize, Dealing> = self
            .dealings
            .iter()
            .map(|(&i, s)| match &s.msg {
                CeremonyMsg::Dealing(d) => (i, d.clone()),
                _ => unreachable!("dealings map holds only Dealing messages"),
            })
            .collect();
        compute_qual(&self.params, &dealings, &self.complaints(), &self.reveals())
    }

    /// The deterministic offense attribution over the agreed view —
    /// witness-first (ORGANS §5): for each complaint against a dealer with
    /// an operative dealing, a VERIFYING reveal convicts the complainer
    /// ([`Offense::FalseComplaint`]); no verifying reveal convicts the
    /// dealer ([`Offense::BadDealing`]). Plus every equivocation pair.
    /// Complaints naming a dealer who never dealt convict nobody beyond
    /// what QUAL already does (no dealing ⇒ already disqualified; there is
    /// no on-record artifact to weigh a bond against).
    pub fn offenses(&self) -> Vec<Offense> {
        let mut out: Vec<Offense> = self
            .equivocations
            .iter()
            .cloned()
            .map(Offense::Equivocation)
            .collect();
        let dealings: BTreeMap<usize, Dealing> = self
            .dealings
            .iter()
            .map(|(&i, s)| match &s.msg {
                CeremonyMsg::Dealing(d) => (i, d.clone()),
                _ => unreachable!(),
            })
            .collect();
        for &(dealer, complainer) in &self.complaints {
            let Some(dealing) = dealings.get(&dealer) else {
                continue; // never dealt: already out of QUAL, nothing to weigh
            };
            let answered = self.reveals.get(&(dealer, complainer)).is_some_and(|r| {
                crate::dkg::compute_qual(
                    &DkgParams {
                        n: self.params.n,
                        t: self.params.t,
                    },
                    &BTreeMap::from([(dealer, dealing.clone())]),
                    &[Complaint { dealer, complainer }],
                    std::slice::from_ref(r),
                )
                .contains(&dealer)
            });
            if answered {
                out.push(Offense::FalseComplaint { complainer, dealer });
            } else {
                out.push(Offense::BadDealing { dealer, complainer });
            }
        }
        out
    }

    /// The PUBLIC finalize: QUAL + group public key + per-member share
    /// publics, derived from broadcast commitments alone — no secret shares
    /// needed, so a coordinator (or any auditor) can compute and commit the
    /// output without being a participant. Aborts loudly below threshold,
    /// exactly like [`DkgParticipant::finalize`].
    pub fn public_output(&self) -> Result<CeremonyPublicOutput, CeremonyError> {
        let qual = self.qual();
        if qual.len() < self.params.t {
            return Err(CeremonyError::Dkg(DkgError::InsufficientQual {
                got: qual.len(),
                need: self.params.t,
            }));
        }
        // Pure commitment arithmetic — no secret shares enter.
        use ark_ec::CurveGroup;
        use ark_ff::Zero;
        use hints::G1;
        type G1P = <hints::snark::Curve as ark_ec::pairing::Pairing>::G1;
        let dealing = |i: usize| self.dealing_of(i).expect("qual ⊆ stored dealings");
        let mut group = G1P::zero();
        for &i in &qual {
            group += dealing(i).commitments()[0];
        }
        let share_publics: Vec<G1> = (1..=self.params.n)
            .map(|j| {
                let mut pk = G1P::zero();
                for &i in &qual {
                    pk += eval_commitments_pub(dealing(i).commitments(), j as u64);
                }
                pk.into_affine()
            })
            .collect();
        Ok(CeremonyPublicOutput {
            threshold: self.params.t,
            qual: qual.into_iter().collect(),
            group_public: group.into_affine(),
            share_publics,
        })
    }
}

/// Public Horner evaluation `Σ_k C_k · jᵏ` (the [`crate::dkg`] commitment
/// evaluation, reproduced here over the public wire types).
fn eval_commitments_pub(
    commitments: &[hints::G1],
    j: u64,
) -> <hints::snark::Curve as ark_ec::pairing::Pairing>::G1 {
    use ark_ff::Zero;
    type G1P = <hints::snark::Curve as ark_ec::pairing::Pairing>::G1;
    let x = hints::F::from(j);
    commitments
        .iter()
        .rev()
        .fold(G1P::zero(), |acc, c| acc * x + *c)
}

/// The ceremony's public result — what the coordinator commits on-cell and
/// what any verifier needs: QUAL, the group public key, the per-member
/// share publics. Byte-encoding of the `(threshold, group, share_publics)`
/// tail is the [`crate::dkg::DkgPublicView`] / `BeaconCommittee` tuple
/// encoding, so [`CeremonyPublicOutput::public_view_bytes`] feeds
/// `DkgPublicView::from_bytes` / committee bootstrap directly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CeremonyPublicOutput {
    /// The threshold t.
    pub threshold: usize,
    /// The qualified dealer set (sorted).
    pub qual: Vec<usize>,
    /// The group public key `g₁·f(0)`.
    pub group_public: hints::G1,
    /// Per-member share publics (index 1..=n at positions 0..n).
    pub share_publics: Vec<hints::G1>,
}

impl CeremonyPublicOutput {
    /// The `DkgPublicView`-compatible byte encoding of the public surface.
    pub fn public_view_bytes(&self) -> Vec<u8> {
        use ark_serialize::CanonicalSerialize;
        let mut buf = Vec::new();
        (
            self.threshold as u64,
            self.group_public,
            &self.share_publics,
        )
            .serialize_compressed(&mut buf)
            .expect("serialization cannot fail");
        buf
    }

    /// The 32-byte output commitment the ceremony cell's output slot pins:
    /// BLAKE3(domain, qual ‖ public-view bytes). Anyone holding the agreed
    /// view recomputes and checks it against the chain.
    pub fn commitment(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key(OUTPUT_COMMIT_DOMAIN);
        hasher.update(&(self.qual.len() as u64).to_le_bytes());
        for &i in &self.qual {
            hasher.update(&(i as u64).to_le_bytes());
        }
        let view = self.public_view_bytes();
        hasher.update(&(view.len() as u64).to_le_bytes());
        hasher.update(&view);
        *hasher.finalize().as_bytes()
    }
}

// =============================================================================
// The participant driver
// =============================================================================

/// One participant's ceremony driver: wraps a [`DkgParticipant`] + a
/// [`CeremonyView`] and speaks ONLY wire types ([`SignedCeremonyMsg`] /
/// [`SealedShare`]). Construction deals; [`CeremonyDriver::observe`]
/// consumes broadcasts; [`CeremonyDriver::accept_share`] opens sealed
/// shares and produces the signed Ack/Complaint response;
/// [`CeremonyDriver::finalize`] yields the [`DkgOutput`] (secret share +
/// committee surface) once the view is closed.
pub struct CeremonyDriver {
    ceremony: [u8; 32],
    index: usize,
    signing_key: [u8; 32],
    seal_secret: [u8; 32],
    participant: DkgParticipant,
    view: CeremonyView,
}

impl std::fmt::Debug for CeremonyDriver {
    /// Secrets redacted.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CeremonyDriver")
            .field("ceremony", &hex::encode(self.ceremony))
            .field("index", &self.index)
            .finish_non_exhaustive()
    }
}

impl CeremonyDriver {
    /// Deal as participant `index`: returns the driver, the SIGNED dealing
    /// to broadcast, and the sealed shares to deliver (one per roster
    /// member, including self — process it like any other for uniformity).
    pub fn new(
        ceremony: [u8; 32],
        params: DkgParams,
        index: usize,
        signing_key: [u8; 32],
        seal_secret: [u8; 32],
        roster: CeremonyRoster,
    ) -> Result<(Self, SignedCeremonyMsg, Vec<SealedShare>), CeremonyError> {
        let view = CeremonyView::new(ceremony, params, roster)?;
        let (participant, dealing, shares) = DkgParticipant::new(params, index)?;
        let signed =
            SignedCeremonyMsg::sign(ceremony, index, CeremonyMsg::Dealing(dealing), &signing_key);
        let sealed = shares
            .iter()
            .map(|s| {
                let entry = view
                    .roster()
                    .get(&s.recipient)
                    .expect("roster validated complete");
                seal_share(&ceremony, s, &entry.seal_pk)
            })
            .collect();
        let mut driver = CeremonyDriver {
            ceremony,
            index,
            signing_key,
            seal_secret,
            participant,
            view,
        };
        // Self-observe the own dealing (everyone's view includes it).
        driver.observe(&signed)?;
        Ok((driver, signed, sealed))
    }

    /// This driver's index.
    pub fn index(&self) -> usize {
        self.index
    }

    /// The accumulated view (read access — roots, QUAL, offenses).
    pub fn view(&self) -> &CeremonyView {
        &self.view
    }

    /// Consume one broadcast message: verify, file into the view, and feed
    /// dealings to the inner participant (first-wins; an equivocating
    /// second dealing is evidence, not state).
    pub fn observe(&mut self, signed: &SignedCeremonyMsg) -> Result<Recorded, CeremonyError> {
        let recorded = self.view.record(signed)?;
        if recorded == Recorded::Fresh {
            if let CeremonyMsg::Dealing(d) = &signed.msg {
                self.participant.receive_dealing(d)?;
            }
        }
        Ok(recorded)
    }

    /// Open a sealed share addressed to me, verify it against the dealer's
    /// commitments, and return the SIGNED response to broadcast (Ack when
    /// it verifies, Complaint when it does not — the dealer's fault either
    /// way). The response is also self-observed into the view.
    pub fn accept_share(
        &mut self,
        sealed: &SealedShare,
    ) -> Result<SignedCeremonyMsg, CeremonyError> {
        let share = open_share(sealed, &self.ceremony, self.index, &self.seal_secret)?;
        let response = self.participant.receive_share(&share)?;
        let signed = SignedCeremonyMsg::sign(
            self.ceremony,
            self.index,
            CeremonyMsg::Response(response),
            &self.signing_key,
        );
        self.observe(&signed)?;
        Ok(signed)
    }

    /// A sealed share that never ARRIVED is also the dealer's fault: the
    /// signed complaints to broadcast for every dealer with an operative
    /// dealing from whom I hold no verified share (call at the dealing
    /// deadline).
    pub fn missing_share_complaints(&self) -> Vec<SignedCeremonyMsg> {
        let mut out = Vec::new();
        for (&dealer, _) in self.view.dealings.iter() {
            let acked = self.view.acks.contains(&(dealer, self.index));
            let complained = self.view.complaints.contains(&(dealer, self.index));
            if !acked && !complained {
                out.push(SignedCeremonyMsg::sign(
                    self.ceremony,
                    self.index,
                    CeremonyMsg::Response(ShareResponse::Complaint(Complaint {
                        dealer,
                        complainer: self.index,
                    })),
                    &self.signing_key,
                ));
            }
        }
        out
    }

    /// Answer a complaint against ME with the signed public reveal.
    pub fn answer(&mut self, complaint: &Complaint) -> Result<SignedCeremonyMsg, CeremonyError> {
        let reveal = self.participant.reveal(complaint)?;
        let signed = SignedCeremonyMsg::sign(
            self.ceremony,
            self.index,
            CeremonyMsg::Reveal(reveal),
            &self.signing_key,
        );
        self.observe(&signed)?;
        Ok(signed)
    }

    /// Finalize over the agreed view: my secret share + the full committee
    /// surface ([`DkgOutput`] → `BeaconShare`/`BeaconCommittee`).
    pub fn finalize(&self) -> Result<DkgOutput, CeremonyError> {
        Ok(self
            .participant
            .finalize(&self.view.complaints(), &self.view.reveals())?)
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn make_roster(n: usize) -> (CeremonyRoster, Vec<([u8; 32], [u8; 32])>) {
        // Returns roster + per-index (sign_sk, seal_sk). Signing keys are
        // deterministic per index (so two "dealers 1" in the equivocation
        // test share an identity); seal keys ride the captp keypair helper.
        let mut roster = CeremonyRoster::new();
        let mut secrets = Vec::new();
        for i in 1..=n {
            let sign_sk = [0x10 + i as u8; 32];
            let auth_pk = SigningKey::from_bytes(&sign_sk).verifying_key().to_bytes();
            let (seal_sk, seal_pk) = dregg_captp::store_forward::generate_x25519_keypair();
            roster.insert(
                i,
                RosterEntry {
                    index: i,
                    cell: [i as u8; 32],
                    seal_pk,
                    auth_pk,
                },
            );
            secrets.push((sign_sk, seal_sk));
        }
        (roster, secrets)
    }

    fn run_ceremony(
        n: usize,
        t: usize,
        ceremony: [u8; 32],
    ) -> (Vec<CeremonyDriver>, Vec<SignedCeremonyMsg>) {
        let params = DkgParams { n, t };
        let (roster, secrets) = make_roster(n);
        let mut drivers = Vec::new();
        let mut dealings = Vec::new();
        let mut sealed_all = Vec::new();
        for i in 1..=n {
            let (sign_sk, seal_sk) = secrets[i - 1];
            let (d, signed, sealed) =
                CeremonyDriver::new(ceremony, params, i, sign_sk, seal_sk, roster.clone()).unwrap();
            drivers.push(d);
            dealings.push(signed);
            sealed_all.extend(sealed);
        }
        // Broadcast every dealing to every OTHER driver (wire bytes).
        for signed in &dealings {
            let bytes = signed.to_bytes();
            let decoded = SignedCeremonyMsg::from_bytes(&bytes).unwrap();
            for d in drivers.iter_mut() {
                if d.index() != decoded.signer {
                    assert_eq!(d.observe(&decoded).unwrap(), Recorded::Fresh);
                }
            }
        }
        // Deliver every sealed share; broadcast every response.
        let mut responses = Vec::new();
        for sealed in &sealed_all {
            let resp = drivers[sealed.recipient - 1].accept_share(sealed).unwrap();
            responses.push(resp);
        }
        for resp in &responses {
            for d in drivers.iter_mut() {
                if d.index() != resp.signer {
                    d.observe(resp).unwrap();
                }
            }
        }
        (drivers, dealings)
    }

    #[test]
    fn full_ceremony_over_the_wire_agrees() {
        let ceremony = [7u8; 32];
        let (drivers, _) = run_ceremony(4, 2, ceremony);

        // Every driver computes the same roots and full QUAL.
        let r0 = drivers[0].view().dealings_root();
        let q0 = drivers[0].view().qual();
        assert_eq!(q0, (1..=4).collect());
        for d in &drivers {
            assert_eq!(d.view().dealings_root(), r0);
            assert_eq!(
                d.view().responses_root(),
                drivers[0].view().responses_root()
            );
            assert_eq!(d.view().qual(), q0);
            assert!(d.view().offenses().is_empty());
        }

        // Finalize: identical group key everywhere; the coordinator's
        // PUBLIC output matches the participants' (and commits stably).
        let outs: Vec<DkgOutput> = drivers.iter().map(|d| d.finalize().unwrap()).collect();
        for o in &outs[1..] {
            assert_eq!(o.group_public(), outs[0].group_public());
        }
        let public = drivers[0].view().public_output().unwrap();
        assert_eq!(&public.group_public, outs[0].group_public());
        assert_eq!(public.qual, vec![1, 2, 3, 4]);
        assert_eq!(
            public.commitment(),
            drivers[1].view().public_output().unwrap().commitment()
        );
        // The public-view bytes bootstrap a DkgPublicView (reshare anchor).
        let view = crate::dkg::DkgPublicView::from_bytes(&public.public_view_bytes()).unwrap();
        assert_eq!(view.threshold(), 2);
        assert_eq!(view.num_members(), 4);
    }

    #[test]
    fn unauthenticated_and_cross_signed_messages_refused() {
        let params = DkgParams { n: 3, t: 2 };
        let ceremony = [9u8; 32];
        let (roster, secrets) = make_roster(3);
        let (_d1, signed1, _) = CeremonyDriver::new(
            ceremony,
            params,
            1,
            secrets[0].0,
            secrets[0].1,
            roster.clone(),
        )
        .unwrap();
        let mut view = CeremonyView::new(ceremony, params, roster.clone()).unwrap();

        // Tampered signature refused.
        let mut bad = signed1.clone();
        bad.signature[0] ^= 1;
        assert!(matches!(
            view.record(&bad),
            Err(CeremonyError::BadSignature { signer: 1 })
        ));

        // Participant 2 signing a dealing CLAIMING dealer 1 refused.
        let cross = SignedCeremonyMsg::sign(ceremony, 2, signed1.msg.clone(), &secrets[1].0);
        let cross = SignedCeremonyMsg { signer: 2, ..cross };
        assert!(matches!(
            view.record(&cross),
            Err(CeremonyError::AuthorMismatch {
                signer: 2,
                claimed: 1
            })
        ));

        // The genuine one records.
        assert_eq!(view.record(&signed1).unwrap(), Recorded::Fresh);
    }

    #[test]
    fn equivocation_keeps_first_dealing_and_retains_verifiable_evidence() {
        let params = DkgParams { n: 3, t: 2 };
        let ceremony = [11u8; 32];
        let (roster, secrets) = make_roster(3);
        let mut view = CeremonyView::new(ceremony, params, roster.clone()).unwrap();

        // Dealer 1 deals TWICE (two fresh participants, same index/keys).
        let (_p, first, _) = CeremonyDriver::new(
            ceremony,
            params,
            1,
            secrets[0].0,
            secrets[0].1,
            roster.clone(),
        )
        .unwrap();
        let (_p2, second, _) = CeremonyDriver::new(
            ceremony,
            params,
            1,
            secrets[0].0,
            secrets[0].1,
            roster.clone(),
        )
        .unwrap();
        assert_eq!(view.record(&first).unwrap(), Recorded::Fresh);
        let rec = view.record(&second).unwrap();
        let Recorded::Equivocation(evidence) = rec else {
            panic!("conflicting dealing must yield evidence, got {rec:?}");
        };
        // Self-certifying: anyone with the roster convicts.
        assert!(evidence.verify(&ceremony, &roster));
        assert_eq!(evidence.dealer, 1);
        // Tampered evidence does not convict.
        let mut forged = evidence.clone();
        forged.second.signature[0] ^= 1;
        assert!(!forged.verify(&ceremony, &roster));
        // First dealing stays operative; the offense is on record.
        assert_eq!(
            view.dealing_of(1).unwrap(),
            match &first.msg {
                CeremonyMsg::Dealing(d) => d,
                _ => unreachable!(),
            }
        );
        assert_eq!(view.offenses().len(), 1);
        assert_eq!(view.offenses()[0].offender(), 1);
    }

    #[test]
    fn sealed_share_bindings_fail_closed() {
        let params = DkgParams { n: 3, t: 2 };
        let ceremony = [13u8; 32];
        let other = [14u8; 32];
        let (roster, secrets) = make_roster(3);
        let (_d, _signed, sealed) = CeremonyDriver::new(
            ceremony,
            params,
            1,
            secrets[0].0,
            secrets[0].1,
            roster.clone(),
        )
        .unwrap();
        let to_two = sealed.iter().find(|s| s.recipient == 2).unwrap();

        // Opens for its recipient.
        let share = open_share(to_two, &ceremony, 2, &secrets[1].1).unwrap();
        assert_eq!(share.dealer, 1);
        assert_eq!(share.recipient, 2);

        // Cross-ceremony replay refused (envelope and inner binding).
        assert_eq!(
            open_share(to_two, &other, 2, &secrets[1].1).unwrap_err(),
            CeremonyError::WrongCeremony
        );
        let mut relabeled = to_two.clone();
        relabeled.ceremony = other;
        assert!(open_share(&relabeled, &other, 2, &secrets[1].1).is_err());

        // Re-addressing refused: claiming it is for 3 (envelope edit) fails
        // the inner binding even with 3's key... it fails the AEAD first
        // (sealed to 2's pk), and a same-key relabel fails the binding.
        let mut readdressed = to_two.clone();
        readdressed.recipient = 3;
        assert!(open_share(&readdressed, &ceremony, 3, &secrets[2].1).is_err());
        let mut relabeled_recipient = to_two.clone();
        relabeled_recipient.recipient = 3;
        assert!(open_share(&relabeled_recipient, &ceremony, 3, &secrets[1].1).is_err());

        // Wrong key refused.
        assert!(open_share(to_two, &ceremony, 2, &secrets[2].1).is_err());
    }

    #[test]
    fn corrupted_share_yields_complaint_and_witness_first_attribution() {
        let params = DkgParams { n: 3, t: 2 };
        let ceremony = [17u8; 32];
        let (roster, secrets) = make_roster(3);
        let mut drivers = Vec::new();
        let mut dealings = Vec::new();
        let mut sealed_all = Vec::new();
        for i in 1..=3usize {
            let (d, signed, sealed) = CeremonyDriver::new(
                ceremony,
                params,
                i,
                secrets[i - 1].0,
                secrets[i - 1].1,
                roster.clone(),
            )
            .unwrap();
            drivers.push(d);
            dealings.push(signed);
            sealed_all.extend(sealed);
        }
        for signed in &dealings {
            for d in drivers.iter_mut() {
                if d.index() != signed.signer {
                    d.observe(signed).unwrap();
                }
            }
        }
        // Corrupt dealer 2's share to member 3 IN TRANSIT: re-seal garbage.
        // (The seal is authenticated, so in-transit tamper = replace with a
        // validly-sealed WRONG share — model the cheating dealer directly.)
        let bad_share = PrivateShare {
            dealer: 2,
            recipient: 3,
            share_bytes: vec![0xAB; 32],
        };
        let bad_sealed = seal_share(&ceremony, &bad_share, &roster.get(&3).unwrap().seal_pk);
        let mut responses = Vec::new();
        for sealed in sealed_all
            .iter()
            .filter(|s| !(s.dealer == 2 && s.recipient == 3))
            .chain(std::iter::once(&bad_sealed))
        {
            responses.push(drivers[sealed.recipient - 1].accept_share(sealed).unwrap());
        }
        for resp in &responses {
            for d in drivers.iter_mut() {
                if d.index() != resp.signer {
                    d.observe(resp).unwrap();
                }
            }
        }
        // The complaint is on record everywhere.
        for d in &drivers {
            assert_eq!(
                d.view().complaints(),
                vec![Complaint {
                    dealer: 2,
                    complainer: 3
                }]
            );
        }
        // Dealer 2 ANSWERS honestly: the reveal verifies, defeating the
        // complaint — full QUAL, and the COMPLAINER is the convict
        // (witness-first; here the complaint was justified against the
        // transit share but the dealer's actual polynomial answers it).
        let complaint = Complaint {
            dealer: 2,
            complainer: 3,
        };
        let reveal = drivers[1].answer(&complaint).unwrap();
        for d in drivers.iter_mut() {
            if d.index() != 2 {
                d.observe(&reveal).unwrap();
            }
        }
        for d in &drivers {
            assert_eq!(d.view().qual(), (1..=3).collect());
            assert_eq!(
                d.view().offenses(),
                vec![Offense::FalseComplaint {
                    complainer: 3,
                    dealer: 2
                }]
            );
        }
        // WITHOUT the reveal the attribution flips to the dealer — pin that
        // on a forked view.
        let mut forked = CeremonyView::new(ceremony, params, roster.clone()).unwrap();
        for signed in &dealings {
            forked.record(signed).unwrap();
        }
        for resp in &responses {
            forked.record(resp).unwrap();
        }
        assert_eq!(
            forked.offenses(),
            vec![Offense::BadDealing {
                dealer: 2,
                complainer: 3
            }]
        );
        assert_eq!(forked.qual(), [1usize, 3].into_iter().collect());
    }

    #[test]
    fn missing_share_complaints_name_silent_dealers() {
        let params = DkgParams { n: 3, t: 2 };
        let ceremony = [19u8; 32];
        let (roster, secrets) = make_roster(3);
        let mut drivers = Vec::new();
        let mut dealings = Vec::new();
        let mut sealed_all = Vec::new();
        for i in 1..=3usize {
            let (d, signed, sealed) = CeremonyDriver::new(
                ceremony,
                params,
                i,
                secrets[i - 1].0,
                secrets[i - 1].1,
                roster.clone(),
            )
            .unwrap();
            drivers.push(d);
            dealings.push(signed);
            sealed_all.extend(sealed);
        }
        for signed in &dealings {
            for d in drivers.iter_mut() {
                if d.index() != signed.signer {
                    d.observe(signed).unwrap();
                }
            }
        }
        // Dealer 2 never delivers to member 3 (everything else flows).
        for sealed in sealed_all
            .iter()
            .filter(|s| !(s.dealer == 2 && s.recipient == 3))
        {
            let resp = drivers[sealed.recipient - 1].accept_share(sealed).unwrap();
            for d in drivers.iter_mut() {
                if d.index() != resp.signer {
                    d.observe(&resp).unwrap();
                }
            }
        }
        let complaints = drivers[2].missing_share_complaints();
        assert_eq!(complaints.len(), 1);
        assert!(matches!(
            &complaints[0].msg,
            CeremonyMsg::Response(ShareResponse::Complaint(Complaint {
                dealer: 2,
                complainer: 3
            }))
        ));
    }

    #[test]
    fn roots_are_arrival_order_insensitive() {
        let ceremony = [23u8; 32];
        let params = DkgParams { n: 3, t: 2 };
        let (roster, secrets) = make_roster(3);
        let mut dealings = Vec::new();
        for i in 1..=3usize {
            let (_d, signed, _) = CeremonyDriver::new(
                ceremony,
                params,
                i,
                secrets[i - 1].0,
                secrets[i - 1].1,
                roster.clone(),
            )
            .unwrap();
            dealings.push(signed);
        }
        let mut forward = CeremonyView::new(ceremony, params, roster.clone()).unwrap();
        let mut reverse = CeremonyView::new(ceremony, params, roster).unwrap();
        for signed in &dealings {
            forward.record(signed).unwrap();
        }
        for signed in dealings.iter().rev() {
            reverse.record(signed).unwrap();
        }
        assert_eq!(forward.dealings_root(), reverse.dealings_root());
        assert_eq!(forward.responses_root(), reverse.responses_root());
        assert_eq!(forward.reveals_root(), reverse.reveals_root());
    }
}
