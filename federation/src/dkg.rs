//! Distributed key generation (Feldman / JF-DKG) + proactive resharing for
//! the beacon committee — the upgrade [`crate::beacon`]'s NOTES §1 names:
//! share issuance with NO party ever holding `f(0)`. The dealer in
//! [`crate::beacon::BeaconCommittee::deal`] transiently knows the group
//! secret; here the group secret is `f(0) = Σ_{i∈QUAL} f_i(0)`, a sum of
//! per-participant secrets that exists only as a mathematical object.
//!
//! # The protocol (joint-Feldman, GJKR's JF-DKG)
//!
//! Participants are indexed `1..=n` with threshold `t`.
//!
//! 1. **Deal** ([`DkgParticipant::new`]): participant `i` samples a secret
//!    polynomial `f_i` of degree `t−1`, BROADCASTS the Feldman commitments
//!    `C_ik = g₁·a_ik` ([`Dealing`] — in **G1**, matching the beacon's key
//!    group: `group_public`/`share_publics` live in G1, signatures in G2),
//!    and produces one PRIVATE share `f_i(j)` per participant `j`
//!    ([`PrivateShare`] — modeled as bytes-to-deliver; see "transport" below).
//! 2. **Verify** ([`DkgParticipant::receive_share`]): `j` checks
//!    `g₁·f_i(j) == Σ_k C_ik·jᵏ` and answers with a typed
//!    [`ShareResponse::Ack`] or [`ShareResponse::Complaint`].
//! 3. **Complaints** ([`DkgParticipant::reveal`], [`compute_qual`]): a
//!    complained-against dealer publicly reveals the disputed share
//!    ([`ComplaintReveal`]). A complaint is ANSWERED iff some reveal for that
//!    (dealer, complainer) pair verifies against the dealer's commitments;
//!    a dealer with any unanswered complaint (including silence) is
//!    disqualified. `QUAL` = dealers with a well-formed dealing and no
//!    unanswered complaint — computed by the pure function [`compute_qual`],
//!    deterministic in the view `(dealings, complaints, reveals)`.
//! 4. **Finalize** ([`DkgParticipant::finalize`]): aborts loudly if
//!    `|QUAL| < t`; otherwise `s_j = Σ_{i∈QUAL} f_i(j)`, group public key
//!    `= Σ_{i∈QUAL} C_i0`, and per-member share publics
//!    `pk_j = Σ_{i∈QUAL} Σ_k C_ik·jᵏ`. The [`DkgOutput`] converts straight
//!    into [`BeaconShare`] + [`BeaconCommittee`], so
//!    [`crate::beacon::beacon_at`] / [`crate::beacon::verify_beacon`] work
//!    unchanged over DKG-derived keys.
//!
//! # Agreement assumption (what the cell-app ceremony supplies later)
//!
//! `QUAL` is deterministic GIVEN a common view: every honest party must feed
//! [`compute_qual`] the same `(dealings, complaints, reveals)` sets. This
//! module does NOT build that agreement — the ceremony-as-cell-app lane rides
//! the blocklace's authenticated agreed broadcast for it. Until then the
//! caller is responsible for delivering identical message sets to every
//! participant (the tests do exactly that).
//!
//! # Transport is modeled, not built
//!
//! [`PrivateShare::share_bytes`] is the canonical encoding of the field
//! element — a PLACEHOLDER for a ciphertext. Confidentiality and sender
//! authentication of the private channel (e.g. HPKE to the recipient's
//! strand key) belong to the ceremony lane; nothing here assumes more than
//! "these bytes reached `recipient` and allegedly came from `dealer`".
//!
//! # Why JF-DKG's key-distribution bias is harmless HERE
//!
//! Gennaro–Jarecki–Krawczyk–Rabin showed an adversary can bias the
//! DISTRIBUTION of the JF-DKG public key (decide after seeing others'
//! commitments whether its own dealers get disqualified, steering
//! `Σ_{i∈QUAL} f_i(0)` by a few bits). For the beacon this is irrelevant:
//! the security properties consumed are (a) unforgeability — no `<t`
//! coalition computes `H(m)^{f(0)}` — and (b) UNIQUENESS of the BLS
//! signature, which holds for EVERY fixed key; neither needs the key to be
//! uniformly distributed. This is the same argument GJKR later made for
//! threshold Schnorr ("Secure Applications of Pedersen's DKG", CT-RSA 2003):
//! the reduction embeds its challenge whatever the (slightly biased) key is.
//! If a future application ever uses the GROUP KEY ITSELF as randomness,
//! upgrade to the full Pedersen-committed New-DKG with an extraction round —
//! the round structures here are the skeleton for that too.
//!
//! # Resharing — what it does and does NOT do
//!
//! [`reshare_deal`] + [`ReshareParticipant`] re-share the SAME `f(0)` to a
//! new committee (possibly new size `n'` and threshold `t'`): each old
//! member `j` deals sub-shares of THEIR share `s_j` with a degree-`(t'−1)`
//! polynomial `g_j` anchored by `g_j(0) = s_j` (the dealing's constant
//! commitment must equal the OLD committee's `pk_j` — that anchor is
//! verified on receipt). New members Lagrange-combine sub-shares from a
//! deterministic set `R` of `t` old dealers into `s'_m = Σ_{j∈R} λ_j g_j(m)`
//! — fresh shares of the unchanged secret, so the group public key (and any
//! already-issued beacon!) is preserved across the committee change.
//!
//! HONESTY: resharing does NOT revoke old shares. They remain valid Shamir
//! points of the same `f(0)` forever; any old `t`-subset can still compute
//! the (unique, hence identical) group signature OUTSIDE the new committee's
//! surface. What rotation buys: the NEW committee's verification surface
//! (`share_publics`) accepts only new shares, and — under the PROACTIVE
//! assumption that old members ERASE their old shares (deletion is a
//! party-local act no protocol can force; it also needs memory hygiene /
//! zeroization at the holder) — an adversary must corrupt `t` members within
//! ONE epoch window rather than across the committee's whole lifetime.
//!
//! # NOTES — what the ceremony-as-cell-app lane adds
//!
//! 1. Authenticated broadcast + common view = the blocklace (each round's
//!    messages ride turns; `compute_qual` then runs over an AGREED view).
//! 2. Equivocation evidence: two different [`Dealing`]s from one dealer in
//!    one ceremony are blocklace-detectable and slashable (here the second
//!    one is merely rejected with [`DkgError::DuplicateDealing`]).
//! 3. Slashable complaints: a complaint and its answering reveal are both
//!    on-record, so a FALSE complaint (reveal verifies) and a bad dealing
//!    (reveal fails) are each attributable — admission-bond slashing hooks
//!    onto exactly these, in the admission lane, not here.
//! 4. Proactive deletion: epoch transitions trigger [`reshare_deal`]; the
//!    erase-old-share obligation becomes a cell-app attestation.

use std::collections::{BTreeMap, BTreeSet};

use ark_ec::{AffineRepr, CurveGroup, pairing::Pairing};
use ark_ff::{Field, UniformRand, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::{RngCore, SeedableRng, rngs::StdRng};
use serde::{Deserialize, Serialize};

use hints::snark::Curve;
use hints::{F, G1};

use crate::beacon::{BeaconCommittee, BeaconShare};

type G1P = <Curve as Pairing>::G1;

// =============================================================================
// Errors
// =============================================================================

/// Errors from the DKG / resharing layer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DkgError {
    /// n == 0, t == 0, or t > n.
    InvalidParameters,
    /// A participant/dealer index outside `1..=n`.
    IndexOutOfRange {
        /// The offending index.
        index: usize,
    },
    /// A second dealing from the same dealer (equivocation at the transport
    /// layer; the blocklace makes this slashable evidence later).
    DuplicateDealing {
        /// The equivocating dealer.
        dealer: usize,
    },
    /// A dealing that is not a well-formed degree-(t−1) Feldman commitment
    /// vector (wrong length, bad point, or — for resharing — a constant term
    /// that does not anchor to the old committee's share public key).
    MalformedDealing {
        /// The dealer whose dealing was rejected.
        dealer: usize,
    },
    /// A private share addressed to someone else reached this participant.
    WrongRecipient {
        /// This participant's index.
        expected: usize,
        /// The share's recipient field.
        got: usize,
    },
    /// A share (or reveal/complaint) referencing a dealer whose dealing this
    /// participant has not received — rounds are ordered: dealings first.
    UnknownDealer {
        /// The unknown dealer index.
        dealer: usize,
    },
    /// |QUAL| < t: not enough qualified dealers to anchor the threshold.
    /// The ceremony MUST abort — finishing with a sub-threshold QUAL would
    /// let a smaller coalition reconstruct f(0).
    InsufficientQual {
        /// Qualified dealers.
        got: usize,
        /// The threshold t.
        need: usize,
    },
    /// Fewer than `need` valid reshare dealings to interpolate the old
    /// secret through.
    InsufficientDealers {
        /// Valid reshare dealings seen.
        got: usize,
        /// The OLD committee threshold.
        need: usize,
    },
    /// Finalization needs a verified share from this QUAL/R dealer and none
    /// was ever received (nor supplied by a verifying reveal).
    MissingShare {
        /// The dealer whose share is missing.
        dealer: usize,
    },
    /// The reshared key did not reproduce the old group public key (should
    /// be unreachable given the per-dealing anchor check; belt and braces).
    GroupKeyMismatch,
    /// Byte-level decode failure.
    SerializationError,
}

impl std::fmt::Display for DkgError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DkgError::InvalidParameters => write!(f, "invalid DKG parameters"),
            DkgError::IndexOutOfRange { index } => {
                write!(f, "participant index {index} out of range")
            }
            DkgError::DuplicateDealing { dealer } => {
                write!(f, "duplicate dealing from dealer {dealer}")
            }
            DkgError::MalformedDealing { dealer } => {
                write!(f, "malformed dealing from dealer {dealer}")
            }
            DkgError::WrongRecipient { expected, got } => {
                write!(f, "share for participant {got} delivered to {expected}")
            }
            DkgError::UnknownDealer { dealer } => {
                write!(f, "no dealing received from dealer {dealer}")
            }
            DkgError::InsufficientQual { got, need } => {
                write!(f, "insufficient QUAL: {got} < {need} — ceremony aborts")
            }
            DkgError::InsufficientDealers { got, need } => {
                write!(f, "insufficient reshare dealers: {got} < {need}")
            }
            DkgError::MissingShare { dealer } => {
                write!(f, "missing verified share from dealer {dealer}")
            }
            DkgError::GroupKeyMismatch => {
                write!(f, "reshared key does not match the old group public key")
            }
            DkgError::SerializationError => write!(f, "DKG serialization error"),
        }
    }
}

impl std::error::Error for DkgError {}

// =============================================================================
// Parameters + field/point helpers
// =============================================================================

/// Ceremony parameters: `n` participants (indices `1..=n`), threshold `t`
/// (any `t` final shares reconstruct; no `t−1` coalition learns anything).
///
/// Robustness note: complaint resolution can only disqualify dealers, so a
/// run with `c` corrupt dealers completes iff `n − c ≥ t`. The classical
/// robust setting is `n ≥ 2t−1`; this module permits any `t ≤ n` (the beacon
/// does too) and simply aborts loudly when QUAL falls below `t`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DkgParams {
    /// Committee size.
    pub n: usize,
    /// Threshold.
    pub t: usize,
}

impl DkgParams {
    fn validate(&self) -> Result<(), DkgError> {
        if self.n == 0 || self.t == 0 || self.t > self.n {
            return Err(DkgError::InvalidParameters);
        }
        Ok(())
    }
}

/// Horner evaluation of a secret polynomial (coeffs low-to-high) at `x`.
fn eval_poly(coeffs: &[F], x: F) -> F {
    coeffs.iter().rev().fold(F::zero(), |acc, c| acc * x + c)
}

/// Horner evaluation of a Feldman commitment vector at `x`:
/// `Σ_k C_k · xᵏ` — the public image `g₁·f(x)` of the committed polynomial.
fn eval_commitments(commitments: &[G1], x: F) -> G1P {
    commitments
        .iter()
        .rev()
        .fold(G1P::zero(), |acc, c| acc * x + *c)
}

/// Lagrange coefficients at 0 for the (distinct, nonzero) points `xs`.
fn lagrange_at_zero(xs: &[F]) -> Vec<F> {
    let mut out = Vec::with_capacity(xs.len());
    for (k, xk) in xs.iter().enumerate() {
        let mut lambda = F::from(1u64);
        for (j, xj) in xs.iter().enumerate() {
            if j == k {
                continue;
            }
            let denom = (*xj - *xk)
                .inverse()
                .expect("distinct 1-based indices, nonzero denominator");
            lambda *= *xj * denom;
        }
        out.push(lambda);
    }
    out
}

fn share_to_bytes(s: &F) -> Vec<u8> {
    let mut buf = Vec::new();
    s.serialize_compressed(&mut buf)
        .expect("field serialization cannot fail");
    buf
}

fn share_from_bytes(bytes: &[u8]) -> Result<F, DkgError> {
    F::deserialize_compressed(bytes).map_err(|_| DkgError::SerializationError)
}

/// Parse + verify a (revealed or privately delivered) share for `recipient`
/// against a dealer's commitments. `Some(s)` iff it parses AND
/// `g₁·s == Σ_k C_k·recipientᵏ`.
fn verified_share(commitments: &[G1], recipient: usize, share_bytes: &[u8]) -> Option<F> {
    let s = share_from_bytes(share_bytes).ok()?;
    let expected = eval_commitments(commitments, F::from(recipient as u64));
    if G1::generator() * s == expected {
        Some(s)
    } else {
        None
    }
}

fn point_ok(p: &G1) -> bool {
    p.is_in_correct_subgroup_assuming_on_curve()
}

// =============================================================================
// Round messages (all serde — they ride turns later)
// =============================================================================

/// Round-1 BROADCAST: dealer `i`'s Feldman commitments `C_ik = g₁·a_ik`,
/// `k = 0..t−1`, to its secret polynomial `f_i`. `C_i0` commits the dealer's
/// contribution to the group secret.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Dealing {
    /// The dealing participant's 1-based index.
    pub dealer: usize,
    commitments: Vec<G1>,
}

impl Dealing {
    /// The commitment vector (length t, points in G1 — the beacon key group).
    pub fn commitments(&self) -> &[G1] {
        &self.commitments
    }

    /// Serialize: dealer ‖ commitments (compressed).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        (self.dealer as u64, &self.commitments)
            .serialize_compressed(&mut buf)
            .expect("serialization cannot fail");
        buf
    }

    /// Deserialize (validates curve points — compressed arkworks
    /// deserialization checks subgroup membership).
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, DkgError> {
        let (dealer, commitments): (u64, Vec<G1>) =
            CanonicalDeserialize::deserialize_compressed(bytes)
                .map_err(|_| DkgError::SerializationError)?;
        Ok(Self {
            dealer: dealer as usize,
            commitments,
        })
    }
}

/// Round-1 PRIVATE message: dealer's evaluation `f_dealer(recipient)`,
/// canonically encoded. The bytes are a CIPHERTEXT PLACEHOLDER — the
/// ceremony lane wraps them in an authenticated private channel; this
/// module only models "bytes to deliver".
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrivateShare {
    /// The dealing participant.
    pub dealer: usize,
    /// The participant this share is for.
    pub recipient: usize,
    /// Canonical encoding of `f_dealer(recipient)`.
    pub share_bytes: Vec<u8>,
}

/// A complaint: `complainer` states that `dealer`'s private share failed
/// verification against the broadcast commitments (or never arrived /
/// failed to parse).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Complaint {
    /// The accused dealer.
    pub dealer: usize,
    /// The complaining recipient.
    pub complainer: usize,
}

/// Round-2 response from a recipient about one dealer's share.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ShareResponse {
    /// The share verified against the dealer's commitments.
    Ack {
        /// The dealer whose share verified.
        dealer: usize,
        /// The acknowledging recipient.
        member: usize,
    },
    /// The share failed verification — broadcast for round 3.
    Complaint(Complaint),
}

/// Round-3 BROADCAST: a complained-against dealer publicly reveals the
/// disputed share. If it verifies, the complaint was unjustified (and the
/// complainer adopts the revealed value); if not — or if the dealer stays
/// silent — the dealer is disqualified.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ComplaintReveal {
    /// The revealing dealer.
    pub dealer: usize,
    /// The complainer the share was for.
    pub recipient: usize,
    /// Canonical encoding of `f_dealer(recipient)`, now public.
    pub share_bytes: Vec<u8>,
}

/// Reshare BROADCAST: old member `dealer` (OLD index) commits a
/// degree-(t'−1) polynomial `g_dealer` with `g_dealer(0) = s_dealer`.
/// `commitments[0]` MUST equal the old committee's `pk_dealer` — verified
/// on receipt; that anchor is what makes resharing preserve `f(0)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReshareDealing {
    /// The dealing OLD-committee member's 1-based index.
    pub dealer: usize,
    commitments: Vec<G1>,
}

impl ReshareDealing {
    /// The commitment vector (length t', constant term anchored to the old
    /// committee's share public key).
    pub fn commitments(&self) -> &[G1] {
        &self.commitments
    }

    /// Serialize: dealer ‖ commitments (compressed).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::new();
        (self.dealer as u64, &self.commitments)
            .serialize_compressed(&mut buf)
            .expect("serialization cannot fail");
        buf
    }

    /// Deserialize (validates curve points).
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, DkgError> {
        let (dealer, commitments): (u64, Vec<G1>) =
            CanonicalDeserialize::deserialize_compressed(bytes)
                .map_err(|_| DkgError::SerializationError)?;
        Ok(Self {
            dealer: dealer as usize,
            commitments,
        })
    }
}

/// Reshare PRIVATE message: `g_dealer(recipient)` where `recipient` is a
/// NEW-committee index. Same ciphertext-placeholder caveat as
/// [`PrivateShare`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResharePrivateShare {
    /// The OLD-committee dealer.
    pub dealer: usize,
    /// The NEW-committee recipient.
    pub recipient: usize,
    /// Canonical encoding of `g_dealer(recipient)`.
    pub share_bytes: Vec<u8>,
}

// Serde-via-bytes for the point-carrying messages (same pattern as
// `BeaconOutput` — postcard/serde_json both ride the byte string).
macro_rules! impl_bytes_serde {
    ($ty:ty) => {
        impl Serialize for $ty {
            fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                serializer.serialize_bytes(&self.to_bytes())
            }
        }
        impl<'de> Deserialize<'de> for $ty {
            fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
                let bytes: Vec<u8> = Deserialize::deserialize(deserializer)?;
                Self::from_bytes(&bytes).map_err(serde::de::Error::custom)
            }
        }
    };
}

impl_bytes_serde!(Dealing);
impl_bytes_serde!(ReshareDealing);

// =============================================================================
// QUAL — pure, deterministic in the common view
// =============================================================================

/// Compute the qualified-dealer set from the (assumed-common) view.
///
/// A dealer is in QUAL iff it has a stored (hence well-formed) dealing and
/// every complaint against it is ANSWERED by some reveal for the same
/// `(dealer, complainer)` pair that verifies against its commitments.
/// Complaints from indices outside `1..=n` are ignored (the ceremony lane
/// authenticates senders; an unauthenticated index is not a member).
///
/// Deterministic: same `(dealings, complaints, reveals)` ⇒ same QUAL.
/// AGREEMENT on that view is the blocklace's job later (module docs).
pub fn compute_qual(
    params: &DkgParams,
    dealings: &BTreeMap<usize, Dealing>,
    complaints: &[Complaint],
    reveals: &[ComplaintReveal],
) -> BTreeSet<usize> {
    let mut qual = BTreeSet::new();
    'dealers: for (&dealer, dealing) in dealings {
        for c in complaints {
            if c.dealer != dealer || c.complainer == 0 || c.complainer > params.n {
                continue;
            }
            let answered = reveals.iter().any(|r| {
                r.dealer == dealer
                    && r.recipient == c.complainer
                    && verified_share(&dealing.commitments, r.recipient, &r.share_bytes).is_some()
            });
            if !answered {
                continue 'dealers; // unanswered complaint ⇒ disqualified
            }
        }
        qual.insert(dealer);
    }
    qual
}

// =============================================================================
// Participant state machine
// =============================================================================

/// One participant's DKG state. Construction performs the deal (round 1);
/// the receive methods drive rounds 2–3; [`DkgParticipant::finalize`]
/// produces the [`DkgOutput`].
pub struct DkgParticipant {
    params: DkgParams,
    index: usize,
    /// My secret polynomial — needed to answer complaints; never broadcast.
    poly: Vec<F>,
    dealings: BTreeMap<usize, Dealing>,
    /// dealer → my VERIFIED share f_dealer(index).
    shares: BTreeMap<usize, F>,
}

impl std::fmt::Debug for DkgParticipant {
    /// Secrets redacted: the polynomial and received shares never print.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DkgParticipant")
            .field("params", &self.params)
            .field("index", &self.index)
            .field("dealings", &self.dealings.keys().collect::<Vec<_>>())
            .field("shares_from", &self.shares.keys().collect::<Vec<_>>())
            .finish_non_exhaustive()
    }
}

impl DkgParticipant {
    /// Deal with OS entropy: sample `f_index`, return the participant state,
    /// the broadcast [`Dealing`], and the `n` private shares to deliver
    /// (including one to self — process it like any other for uniformity).
    pub fn new(
        params: DkgParams,
        index: usize,
    ) -> Result<(Self, Dealing, Vec<PrivateShare>), DkgError> {
        Self::new_with_rng(params, index, &mut ark_std::rand::rngs::OsRng)
    }

    /// Deal from a caller-supplied seed. Reproducible — tests/differentials.
    pub fn new_with_seed(
        params: DkgParams,
        index: usize,
        seed: [u8; 32],
    ) -> Result<(Self, Dealing, Vec<PrivateShare>), DkgError> {
        let mut rng = StdRng::from_seed(seed);
        Self::new_with_rng(params, index, &mut rng)
    }

    /// Deal from a caller-supplied RNG.
    pub fn new_with_rng(
        params: DkgParams,
        index: usize,
        rng: &mut impl RngCore,
    ) -> Result<(Self, Dealing, Vec<PrivateShare>), DkgError> {
        params.validate()?;
        if index == 0 || index > params.n {
            return Err(DkgError::IndexOutOfRange { index });
        }
        let poly: Vec<F> = (0..params.t).map(|_| F::rand(rng)).collect();
        let g1 = G1::generator();
        let commitments: Vec<G1> = poly.iter().map(|a| (g1 * a).into_affine()).collect();
        let dealing = Dealing {
            dealer: index,
            commitments,
        };
        let shares = (1..=params.n)
            .map(|j| PrivateShare {
                dealer: index,
                recipient: j,
                share_bytes: share_to_bytes(&eval_poly(&poly, F::from(j as u64))),
            })
            .collect();
        Ok((
            Self {
                params,
                index,
                poly,
                dealings: BTreeMap::new(),
                shares: BTreeMap::new(),
            },
            dealing,
            shares,
        ))
    }

    /// This participant's 1-based index.
    pub fn index(&self) -> usize {
        self.index
    }

    /// Record a broadcast dealing. Fail-closed: out-of-range dealer, wrong
    /// commitment length, or a bad point rejects (and the dealer, having no
    /// stored dealing, can never enter QUAL); a SECOND dealing from the same
    /// dealer is equivocation and rejects.
    pub fn receive_dealing(&mut self, dealing: &Dealing) -> Result<(), DkgError> {
        if dealing.dealer == 0 || dealing.dealer > self.params.n {
            return Err(DkgError::IndexOutOfRange {
                index: dealing.dealer,
            });
        }
        if dealing.commitments.len() != self.params.t || !dealing.commitments.iter().all(point_ok) {
            return Err(DkgError::MalformedDealing {
                dealer: dealing.dealer,
            });
        }
        if self.dealings.contains_key(&dealing.dealer) {
            return Err(DkgError::DuplicateDealing {
                dealer: dealing.dealer,
            });
        }
        self.dealings.insert(dealing.dealer, dealing.clone());
        Ok(())
    }

    /// Verify a private share against the dealer's stored commitments.
    /// A share that fails to parse or verify yields a typed
    /// [`ShareResponse::Complaint`] (the DEALER's fault — broadcast it);
    /// misdelivery and missing-dealing are caller errors instead.
    pub fn receive_share(&mut self, share: &PrivateShare) -> Result<ShareResponse, DkgError> {
        if share.recipient != self.index {
            return Err(DkgError::WrongRecipient {
                expected: self.index,
                got: share.recipient,
            });
        }
        let dealing = self
            .dealings
            .get(&share.dealer)
            .ok_or(DkgError::UnknownDealer {
                dealer: share.dealer,
            })?;
        match verified_share(&dealing.commitments, self.index, &share.share_bytes) {
            Some(s) => {
                self.shares.insert(share.dealer, s);
                Ok(ShareResponse::Ack {
                    dealer: share.dealer,
                    member: self.index,
                })
            }
            None => Ok(ShareResponse::Complaint(Complaint {
                dealer: share.dealer,
                complainer: self.index,
            })),
        }
    }

    /// Answer a complaint against ME by publicly revealing the complainer's
    /// share. (An honest dealer's reveal verifies, defeating the complaint;
    /// a cheater either stays silent or reveals something that fails.)
    pub fn reveal(&self, complaint: &Complaint) -> Result<ComplaintReveal, DkgError> {
        if complaint.dealer != self.index {
            return Err(DkgError::WrongRecipient {
                expected: self.index,
                got: complaint.dealer,
            });
        }
        if complaint.complainer == 0 || complaint.complainer > self.params.n {
            return Err(DkgError::IndexOutOfRange {
                index: complaint.complainer,
            });
        }
        Ok(ComplaintReveal {
            dealer: self.index,
            recipient: complaint.complainer,
            share_bytes: share_to_bytes(&eval_poly(
                &self.poly,
                F::from(complaint.complainer as u64),
            )),
        })
    }

    /// Finalize: compute QUAL from the common view, abort loudly if
    /// `|QUAL| < t`, adopt any verifying reveals addressed to me (a justified
    /// complainer gets its share from the reveal round), and combine:
    /// `s_index = Σ_{i∈QUAL} f_i(index)`, plus the full public surface.
    pub fn finalize(
        &self,
        complaints: &[Complaint],
        reveals: &[ComplaintReveal],
    ) -> Result<DkgOutput, DkgError> {
        let qual = compute_qual(&self.params, &self.dealings, complaints, reveals);
        if qual.len() < self.params.t {
            return Err(DkgError::InsufficientQual {
                got: qual.len(),
                need: self.params.t,
            });
        }

        // Adopt verifying reveals addressed to me (round-3 share delivery).
        let mut my_shares = self.shares.clone();
        for r in reveals {
            if r.recipient != self.index {
                continue;
            }
            if let Some(dealing) = self.dealings.get(&r.dealer) {
                if let Some(s) = verified_share(&dealing.commitments, self.index, &r.share_bytes) {
                    my_shares.insert(r.dealer, s);
                }
            }
        }

        let mut secret_share = F::zero();
        for &i in &qual {
            secret_share += my_shares
                .get(&i)
                .ok_or(DkgError::MissingShare { dealer: i })?;
        }

        let mut group = G1P::zero();
        for &i in &qual {
            group += self.dealings[&i].commitments[0];
        }
        let share_publics: Vec<G1> = (1..=self.params.n)
            .map(|j| {
                let mut pk = G1P::zero();
                for &i in &qual {
                    pk += eval_commitments(&self.dealings[&i].commitments, F::from(j as u64));
                }
                pk.into_affine()
            })
            .collect();

        // Belt and braces: my combined secret must match my own public image.
        if G1::generator() * secret_share != share_publics[self.index - 1].into_group() {
            return Err(DkgError::GroupKeyMismatch);
        }

        Ok(DkgOutput {
            n: self.params.n,
            t: self.params.t,
            qual: qual.into_iter().collect(),
            group_public: group.into_affine(),
            share_publics,
            index: self.index,
            secret_share,
        })
    }
}

// =============================================================================
// Output — the drop-in for crate::beacon
// =============================================================================

/// One participant's DKG result: its secret share `f(index)` plus the full
/// public committee surface. Converts directly into the beacon types —
/// `BeaconCommittee::from(&out)` / `BeaconShare::from(&out)` — so
/// [`crate::beacon::beacon_at`] and [`crate::beacon::verify_beacon`] run
/// unchanged over DKG-derived keys.
#[derive(Clone)]
pub struct DkgOutput {
    n: usize,
    t: usize,
    qual: Vec<usize>,
    group_public: G1,
    share_publics: Vec<G1>,
    index: usize,
    secret_share: F,
}

impl std::fmt::Debug for DkgOutput {
    /// Secret share redacted.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DkgOutput")
            .field("n", &self.n)
            .field("t", &self.t)
            .field("qual", &self.qual)
            .field("index", &self.index)
            .finish_non_exhaustive()
    }
}

impl DkgOutput {
    /// This holder's 1-based share index.
    pub fn index(&self) -> usize {
        self.index
    }

    /// Committee size n.
    pub fn num_members(&self) -> usize {
        self.n
    }

    /// Threshold t.
    pub fn threshold(&self) -> usize {
        self.t
    }

    /// The qualified dealer set (sorted) the key was combined over.
    pub fn qual(&self) -> &[usize] {
        &self.qual
    }

    /// The group public key `g₁·f(0)`.
    pub fn group_public(&self) -> &G1 {
        &self.group_public
    }

    /// The public committee surface — what new members of a LATER reshare
    /// ceremony need (they hold no [`DkgOutput`] yet).
    pub fn public_view(&self) -> DkgPublicView {
        DkgPublicView {
            threshold: self.t,
            group_public: self.group_public,
            share_publics: self.share_publics.clone(),
        }
    }

    /// The beacon committee over these keys (identical for every honest
    /// participant of the same ceremony).
    pub fn beacon_committee(&self) -> BeaconCommittee {
        BeaconCommittee::from_parts(self.group_public, self.share_publics.clone(), self.t)
    }

    /// This holder's beacon share.
    pub fn beacon_share(&self) -> BeaconShare {
        BeaconShare::from_parts(self.index, self.secret_share)
    }
}

impl From<&DkgOutput> for BeaconCommittee {
    fn from(out: &DkgOutput) -> Self {
        out.beacon_committee()
    }
}

impl From<&DkgOutput> for BeaconShare {
    fn from(out: &DkgOutput) -> Self {
        out.beacon_share()
    }
}

/// The PUBLIC surface of a finished ceremony: old threshold, group key, and
/// per-member share publics — exactly what a reshare verifier anchors to.
/// Byte-compatible with [`BeaconCommittee::to_bytes`] (same tuple encoding),
/// so a new member can bootstrap the view from a published committee.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DkgPublicView {
    threshold: usize,
    group_public: G1,
    share_publics: Vec<G1>,
}

impl DkgPublicView {
    /// The committee threshold t.
    pub fn threshold(&self) -> usize {
        self.threshold
    }

    /// The group public key.
    pub fn group_public(&self) -> &G1 {
        &self.group_public
    }

    /// Committee size n.
    pub fn num_members(&self) -> usize {
        self.share_publics.len()
    }

    /// Serialize (same encoding as `BeaconCommittee::to_bytes`).
    pub fn to_bytes(&self) -> Vec<u8> {
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

    /// Deserialize (validates curve points; accepts `BeaconCommittee::to_bytes`
    /// output).
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, DkgError> {
        let (threshold, group_public, share_publics): (u64, G1, Vec<G1>) =
            CanonicalDeserialize::deserialize_compressed(bytes)
                .map_err(|_| DkgError::SerializationError)?;
        let threshold = threshold as usize;
        if threshold == 0 || threshold > share_publics.len() {
            return Err(DkgError::InvalidParameters);
        }
        Ok(Self {
            threshold,
            group_public,
            share_publics,
        })
    }
}

// =============================================================================
// Resharing (proactive refresh / committee change, same f(0))
// =============================================================================

/// Old member: deal sub-shares of YOUR share `s_index` to the new committee
/// with a fresh degree-(t'−1) polynomial `g(0) = s_index`. OS entropy.
pub fn reshare_deal(
    old: &DkgOutput,
    new_params: DkgParams,
) -> Result<(ReshareDealing, Vec<ResharePrivateShare>), DkgError> {
    reshare_deal_with_rng(old, new_params, &mut ark_std::rand::rngs::OsRng)
}

/// [`reshare_deal`] from a caller-supplied seed (tests/differentials).
pub fn reshare_deal_with_seed(
    old: &DkgOutput,
    new_params: DkgParams,
    seed: [u8; 32],
) -> Result<(ReshareDealing, Vec<ResharePrivateShare>), DkgError> {
    let mut rng = StdRng::from_seed(seed);
    reshare_deal_with_rng(old, new_params, &mut rng)
}

/// [`reshare_deal`] from a caller-supplied RNG.
pub fn reshare_deal_with_rng(
    old: &DkgOutput,
    new_params: DkgParams,
    rng: &mut impl RngCore,
) -> Result<(ReshareDealing, Vec<ResharePrivateShare>), DkgError> {
    new_params.validate()?;
    let mut coeffs = Vec::with_capacity(new_params.t);
    coeffs.push(old.secret_share);
    coeffs.extend((1..new_params.t).map(|_| F::rand(rng)));
    let g1 = G1::generator();
    let commitments: Vec<G1> = coeffs.iter().map(|a| (g1 * a).into_affine()).collect();
    let dealing = ReshareDealing {
        dealer: old.index,
        commitments,
    };
    let shares = (1..=new_params.n)
        .map(|m| ResharePrivateShare {
            dealer: old.index,
            recipient: m,
            share_bytes: share_to_bytes(&eval_poly(&coeffs, F::from(m as u64))),
        })
        .collect();
    Ok((dealing, shares))
}

/// A NEW-committee member's reshare state. Anchored to the OLD committee's
/// public view; finalizes to a [`DkgOutput`] for the new committee with the
/// SAME group public key.
pub struct ReshareParticipant {
    old: DkgPublicView,
    new_params: DkgParams,
    index: usize,
    dealings: BTreeMap<usize, ReshareDealing>,
    /// old dealer → my VERIFIED sub-share g_dealer(index).
    sub_shares: BTreeMap<usize, F>,
}

impl ReshareParticipant {
    /// New member `index` (1-based in the NEW committee) joining a reshare
    /// from the old committee described by `old`.
    pub fn new(old: DkgPublicView, new_params: DkgParams, index: usize) -> Result<Self, DkgError> {
        new_params.validate()?;
        if index == 0 || index > new_params.n {
            return Err(DkgError::IndexOutOfRange { index });
        }
        Ok(Self {
            old,
            new_params,
            index,
            dealings: BTreeMap::new(),
            sub_shares: BTreeMap::new(),
        })
    }

    /// Record a reshare dealing. Beyond the [`DkgParticipant::receive_dealing`]
    /// checks, the constant commitment MUST equal the old committee's
    /// `pk_dealer` — the anchor that forces `g_dealer(0) = s_dealer`, hence
    /// preservation of `f(0)`. A dealer substituting a fresh secret is
    /// rejected here, fail-closed.
    pub fn receive_dealing(&mut self, dealing: &ReshareDealing) -> Result<(), DkgError> {
        if dealing.dealer == 0 || dealing.dealer > self.old.share_publics.len() {
            return Err(DkgError::IndexOutOfRange {
                index: dealing.dealer,
            });
        }
        if dealing.commitments.len() != self.new_params.t
            || !dealing.commitments.iter().all(point_ok)
            || dealing.commitments[0] != self.old.share_publics[dealing.dealer - 1]
        {
            return Err(DkgError::MalformedDealing {
                dealer: dealing.dealer,
            });
        }
        if self.dealings.contains_key(&dealing.dealer) {
            return Err(DkgError::DuplicateDealing {
                dealer: dealing.dealer,
            });
        }
        self.dealings.insert(dealing.dealer, dealing.clone());
        Ok(())
    }

    /// Verify a private sub-share against the dealer's anchored commitments.
    /// Same typed Ack/Complaint surface as the DKG round.
    pub fn receive_share(
        &mut self,
        share: &ResharePrivateShare,
    ) -> Result<ShareResponse, DkgError> {
        if share.recipient != self.index {
            return Err(DkgError::WrongRecipient {
                expected: self.index,
                got: share.recipient,
            });
        }
        let dealing = self
            .dealings
            .get(&share.dealer)
            .ok_or(DkgError::UnknownDealer {
                dealer: share.dealer,
            })?;
        match verified_share(&dealing.commitments, self.index, &share.share_bytes) {
            Some(s) => {
                self.sub_shares.insert(share.dealer, s);
                Ok(ShareResponse::Ack {
                    dealer: share.dealer,
                    member: self.index,
                })
            }
            None => Ok(ShareResponse::Complaint(Complaint {
                dealer: share.dealer,
                complainer: self.index,
            })),
        }
    }

    /// Combine: pick the DETERMINISTIC dealer set `R` = the lowest `old.t`
    /// old indices with valid (anchored) dealings — every honest new member
    /// computes the same `R` from the same broadcast view, which is what
    /// makes the new shares consistent points of ONE polynomial
    /// `f'(x) = Σ_{j∈R} λ_j·g_j(x)` with `f'(0) = f(0)`. A member holding a
    /// valid dealing from `j∈R` but no verified sub-share fails loudly
    /// ([`DkgError::MissingShare`]) — in the full ceremony that complaint is
    /// resolved by a reveal round exactly like the DKG's.
    pub fn finalize(&self) -> Result<DkgOutput, DkgError> {
        let need = self.old.threshold;
        if self.dealings.len() < need {
            return Err(DkgError::InsufficientDealers {
                got: self.dealings.len(),
                need,
            });
        }
        let r: Vec<usize> = self.dealings.keys().copied().take(need).collect();
        let xs: Vec<F> = r.iter().map(|&j| F::from(j as u64)).collect();
        let lambdas = lagrange_at_zero(&xs);

        let mut secret_share = F::zero();
        for (&j, lambda) in r.iter().zip(&lambdas) {
            let s = self
                .sub_shares
                .get(&j)
                .ok_or(DkgError::MissingShare { dealer: j })?;
            secret_share += *s * lambda;
        }

        // Public surface of the NEW committee, derived from the broadcast
        // commitments alone (every member computes the same values).
        let mut group = G1P::zero();
        for (&j, lambda) in r.iter().zip(&lambdas) {
            group += self.dealings[&j].commitments[0] * *lambda;
        }
        // The anchor check on receipt makes this equality structural; keep
        // the loud check anyway (belt and braces, like beacon aggregation).
        if group.into_affine() != self.old.group_public {
            return Err(DkgError::GroupKeyMismatch);
        }
        let share_publics: Vec<G1> = (1..=self.new_params.n)
            .map(|m| {
                let mut pk = G1P::zero();
                for (&j, lambda) in r.iter().zip(&lambdas) {
                    pk += eval_commitments(&self.dealings[&j].commitments, F::from(m as u64))
                        * *lambda;
                }
                pk.into_affine()
            })
            .collect();

        if G1::generator() * secret_share != share_publics[self.index - 1].into_group() {
            return Err(DkgError::GroupKeyMismatch);
        }

        Ok(DkgOutput {
            n: self.new_params.n,
            t: self.new_params.t,
            qual: r,
            group_public: self.old.group_public,
            share_publics,
            index: self.index,
            secret_share,
        })
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::beacon::{BeaconError, beacon_at, verify_beacon};

    /// Drive a fully honest ceremony, delivering every broadcast and every
    /// private share to every participant — the "same view" the blocklace
    /// guarantees later.
    fn run_dkg(n: usize, t: usize, seed_base: u8) -> Vec<DkgOutput> {
        let params = DkgParams { n, t };
        let mut parts = Vec::new();
        let mut dealings = Vec::new();
        let mut priv_shares = Vec::new();
        for i in 1..=n {
            let (p, d, ss) =
                DkgParticipant::new_with_seed(params, i, [seed_base.wrapping_add(i as u8); 32])
                    .unwrap();
            parts.push(p);
            dealings.push(d);
            priv_shares.extend(ss);
        }
        for p in parts.iter_mut() {
            for d in &dealings {
                p.receive_dealing(d).unwrap();
            }
        }
        for ps in &priv_shares {
            let resp = parts[ps.recipient - 1].receive_share(ps).unwrap();
            assert!(
                matches!(resp, ShareResponse::Ack { .. }),
                "honest share must ack"
            );
        }
        parts
            .iter()
            .map(|p| p.finalize(&[], &[]).unwrap())
            .collect()
    }

    // ── The full honest ceremony: drop-in for the beacon ─────────────────

    #[test]
    fn honest_ceremony_yields_a_working_unique_beacon() {
        let outs = run_dkg(5, 3, 10);
        let (epoch, height) = (4, 1042);

        // Every participant derives the IDENTICAL committee, full QUAL.
        let committee = BeaconCommittee::from(&outs[0]);
        for out in &outs {
            assert_eq!(BeaconCommittee::from(out), committee);
            assert_eq!(out.qual(), &[1, 2, 3, 4, 5]);
        }
        assert_eq!(committee.threshold(), 3);
        assert_eq!(committee.num_members(), 5);

        // The beacon.rs uniqueness tooth, over DKG-derived keys: every
        // quorum subset produces THE SAME output.
        let shares: Vec<BeaconShare> = outs.iter().map(BeaconShare::from).collect();
        let subsets: &[&[usize]] = &[&[0, 1, 2], &[2, 3, 4], &[0, 2, 4], &[1, 3, 4]];
        let mut outputs = Vec::new();
        for subset in subsets {
            let picked: Vec<BeaconShare> = subset.iter().map(|&i| shares[i].clone()).collect();
            outputs.push(beacon_at(&committee, &picked, epoch, height).unwrap());
        }
        for out in &outputs[1..] {
            assert_eq!(outputs[0], *out, "quorum subsets must agree (uniqueness)");
        }
        // Light verification with the group key only — verify_beacon
        // unchanged over DKG keys.
        assert!(verify_beacon(committee.group_public(), &outputs[0]));
        // And below threshold still cannot produce it.
        assert_eq!(
            beacon_at(&committee, &shares[0..2], epoch, height).unwrap_err(),
            BeaconError::InsufficientPartials { got: 2, need: 3 }
        );
    }

    // ── Cheating dealer: complained out, ceremony completes ──────────────

    #[test]
    fn cheating_dealer_is_disqualified_and_ceremony_completes() {
        let (n, t) = (5, 3);
        let params = DkgParams { n, t };
        let mut parts = Vec::new();
        let mut dealings = Vec::new();
        let mut priv_shares = Vec::new();
        for i in 1..=n {
            let (p, d, ss) = DkgParticipant::new_with_seed(params, i, [40 + i as u8; 32]).unwrap();
            parts.push(p);
            dealings.push(d);
            priv_shares.extend(ss);
        }
        // Dealer 2 corrupts the share addressed to member 4.
        let bad_idx = priv_shares
            .iter()
            .position(|ps| ps.dealer == 2 && ps.recipient == 4)
            .unwrap();
        priv_shares[bad_idx].share_bytes[0] ^= 0x01;
        let bad_reveal_bytes = priv_shares[bad_idx].share_bytes.clone();

        for p in parts.iter_mut() {
            for d in &dealings {
                p.receive_dealing(d).unwrap();
            }
        }
        let mut complaints = Vec::new();
        for ps in &priv_shares {
            match parts[ps.recipient - 1].receive_share(ps).unwrap() {
                ShareResponse::Ack { .. } => {}
                ShareResponse::Complaint(c) => complaints.push(c),
            }
        }
        assert_eq!(
            complaints,
            vec![Complaint {
                dealer: 2,
                complainer: 4
            }]
        );

        // The dealer "answers" with the SAME bad share — the reveal fails
        // verification, so the complaint stands and dealer 2 is out.
        let bad_reveal = ComplaintReveal {
            dealer: 2,
            recipient: 4,
            share_bytes: bad_reveal_bytes,
        };
        let outs: Vec<DkgOutput> = parts
            .iter()
            .map(|p| {
                p.finalize(&complaints, std::slice::from_ref(&bad_reveal))
                    .unwrap()
            })
            .collect();
        // Staying SILENT disqualifies identically (same QUAL, same key).
        let outs_silent: Vec<DkgOutput> = parts
            .iter()
            .map(|p| p.finalize(&complaints, &[]).unwrap())
            .collect();

        let committee = BeaconCommittee::from(&outs[0]);
        for (a, b) in outs.iter().zip(&outs_silent) {
            assert_eq!(a.qual(), &[1, 3, 4, 5], "dealer 2 must be disqualified");
            assert_eq!(BeaconCommittee::from(a), committee);
            assert_eq!(BeaconCommittee::from(b), committee);
        }

        // The ceremony output works as a beacon WITHOUT the cheater's
        // contribution — all 5 members (incl. the disqualified DEALER, who
        // is still a fine RECIPIENT) hold usable shares.
        let shares: Vec<BeaconShare> = outs.iter().map(BeaconShare::from).collect();
        let out_a = beacon_at(&committee, &shares[0..3], 7, 7).unwrap();
        let out_b = beacon_at(&committee, &shares[2..5], 7, 7).unwrap();
        assert_eq!(out_a, out_b);
        assert!(committee.verify_beacon(&out_a));
    }

    #[test]
    fn unjustified_complaint_is_defeated_by_a_valid_reveal() {
        let (n, t) = (5, 3);
        let params = DkgParams { n, t };
        let mut parts = Vec::new();
        let mut dealings = Vec::new();
        let mut priv_shares = Vec::new();
        for i in 1..=n {
            let (p, d, ss) = DkgParticipant::new_with_seed(params, i, [70 + i as u8; 32]).unwrap();
            parts.push(p);
            dealings.push(d);
            priv_shares.extend(ss);
        }
        for p in parts.iter_mut() {
            for d in &dealings {
                p.receive_dealing(d).unwrap();
            }
        }
        for ps in &priv_shares {
            parts[ps.recipient - 1].receive_share(ps).unwrap();
        }
        // Member 3 FALSELY complains about honest dealer 1.
        let complaint = Complaint {
            dealer: 1,
            complainer: 3,
        };
        // Dealer 1 answers; the reveal verifies, defeating the complaint.
        let reveal = parts[0].reveal(&complaint).unwrap();
        let outs: Vec<DkgOutput> = parts
            .iter()
            .map(|p| {
                p.finalize(&[complaint], std::slice::from_ref(&reveal))
                    .unwrap()
            })
            .collect();
        // Full QUAL — identical to the run with no complaints at all.
        let honest: Vec<DkgOutput> = parts
            .iter()
            .map(|p| p.finalize(&[], &[]).unwrap())
            .collect();
        for (a, b) in outs.iter().zip(&honest) {
            assert_eq!(a.qual(), &[1, 2, 3, 4, 5]);
            assert_eq!(BeaconCommittee::from(a), BeaconCommittee::from(b));
        }
        // WITHOUT the reveal, the false complaint would have ejected the
        // honest dealer — the reveal round is load-bearing.
        let ejected = parts[0].finalize(&[complaint], &[]).unwrap();
        assert_eq!(ejected.qual(), &[2, 3, 4, 5]);
    }

    // ── Below-t QUAL aborts loudly ────────────────────────────────────────

    #[test]
    fn below_threshold_qual_aborts() {
        let (n, t) = (5, 3);
        let params = DkgParams { n, t };
        let mut parts = Vec::new();
        let mut dealings = Vec::new();
        let mut priv_shares = Vec::new();
        for i in 1..=n {
            let (p, d, ss) = DkgParticipant::new_with_seed(params, i, [90 + i as u8; 32]).unwrap();
            parts.push(p);
            dealings.push(d);
            priv_shares.extend(ss);
        }
        // Dealers 1..=3 corrupt every share they send to OTHERS.
        for ps in priv_shares.iter_mut() {
            if ps.dealer <= 3 && ps.recipient != ps.dealer {
                ps.share_bytes[0] ^= 0x01;
            }
        }
        for p in parts.iter_mut() {
            for d in &dealings {
                p.receive_dealing(d).unwrap();
            }
        }
        let mut complaints = Vec::new();
        for ps in &priv_shares {
            if let ShareResponse::Complaint(c) = parts[ps.recipient - 1].receive_share(ps).unwrap()
            {
                complaints.push(c);
            }
        }
        // No reveals: dealers 1-3 are out, QUAL = {4, 5} < t = 3.
        for p in &parts {
            assert_eq!(
                p.finalize(&complaints, &[]).unwrap_err(),
                DkgError::InsufficientQual { got: 2, need: 3 }
            );
        }
    }

    #[test]
    fn degenerate_parameters_are_rejected() {
        assert_eq!(
            DkgParticipant::new_with_seed(DkgParams { n: 0, t: 0 }, 1, [1; 32]).unwrap_err(),
            DkgError::InvalidParameters
        );
        assert_eq!(
            DkgParticipant::new_with_seed(DkgParams { n: 3, t: 4 }, 1, [1; 32]).unwrap_err(),
            DkgError::InvalidParameters
        );
        assert_eq!(
            DkgParticipant::new_with_seed(DkgParams { n: 3, t: 2 }, 4, [1; 32]).unwrap_err(),
            DkgError::IndexOutOfRange { index: 4 }
        );
    }

    #[test]
    fn equivocating_dealing_is_rejected() {
        let params = DkgParams { n: 3, t: 2 };
        let (mut p, _d1, _) = DkgParticipant::new_with_seed(params, 1, [3; 32]).unwrap();
        let (_, d2a, _) = DkgParticipant::new_with_seed(params, 2, [4; 32]).unwrap();
        let (_, d2b, _) = DkgParticipant::new_with_seed(params, 2, [5; 32]).unwrap();
        p.receive_dealing(&d2a).unwrap();
        assert_eq!(
            p.receive_dealing(&d2b).unwrap_err(),
            DkgError::DuplicateDealing { dealer: 2 }
        );
    }

    // ── Resharing: same f(0), fresh shares, new committee ────────────────

    #[test]
    fn reshare_preserves_the_group_key_and_the_beacon() {
        let old_outs = run_dkg(5, 3, 20);
        let old_committee = BeaconCommittee::from(&old_outs[0]);
        let old_shares: Vec<BeaconShare> = old_outs.iter().map(BeaconShare::from).collect();
        let (epoch, height) = (9, 99);
        let old_beacon = beacon_at(&old_committee, &old_shares, epoch, height).unwrap();

        // Rotate to a new committee: n'=4, t'=2. All 5 old members deal.
        let new_params = DkgParams { n: 4, t: 2 };
        let mut reshare_dealings = Vec::new();
        let mut reshare_shares = Vec::new();
        for (k, old) in old_outs.iter().enumerate() {
            let (d, ss) = reshare_deal_with_seed(old, new_params, [120 + k as u8; 32]).unwrap();
            reshare_dealings.push(d);
            reshare_shares.extend(ss);
        }
        let view = old_outs[0].public_view();
        let mut new_parts: Vec<ReshareParticipant> = (1..=4)
            .map(|m| ReshareParticipant::new(view.clone(), new_params, m).unwrap())
            .collect();
        for p in new_parts.iter_mut() {
            for d in &reshare_dealings {
                p.receive_dealing(d).unwrap();
            }
        }
        for ps in &reshare_shares {
            let resp = new_parts[ps.recipient - 1].receive_share(ps).unwrap();
            assert!(matches!(resp, ShareResponse::Ack { .. }));
        }
        let new_outs: Vec<DkgOutput> = new_parts.iter().map(|p| p.finalize().unwrap()).collect();

        // SAME group public key; identical committee across new members;
        // deterministic dealer set R = lowest old-t indices.
        let new_committee = BeaconCommittee::from(&new_outs[0]);
        for out in &new_outs {
            assert_eq!(out.group_public(), old_outs[0].group_public());
            assert_eq!(BeaconCommittee::from(out), new_committee);
            assert_eq!(out.qual(), &[1, 2, 3], "deterministic reshare set R");
        }
        assert_eq!(new_committee.group_public(), old_committee.group_public());

        // The reshared shares interpolate the SAME f(0): the new committee's
        // beacon for the same (epoch, height) is BYTE-IDENTICAL to the old
        // one, and verifies under the unchanged group key — this is what
        // anchors committee rotation across epoch transitions.
        let new_shares: Vec<BeaconShare> = new_outs.iter().map(BeaconShare::from).collect();
        let new_beacon = beacon_at(&new_committee, &new_shares, epoch, height).unwrap();
        assert_eq!(new_beacon.to_bytes(), old_beacon.to_bytes());
        assert!(verify_beacon(new_committee.group_public(), &new_beacon));
        // Quorum subsets of the NEW committee agree too (t'=2).
        let sub = beacon_at(&new_committee, &new_shares[2..4], epoch, height).unwrap();
        assert_eq!(sub, new_beacon);

        // What rotation does enforce: the NEW committee's verification
        // surface rejects OLD shares' partials (fresh share publics)...
        let old_partial = old_shares[1].sign(epoch, height); // old index 2, in range for n'=4
        assert!(!new_committee.verify_partial(&old_partial, epoch, height));
        let old_partials: Vec<_> = old_shares.iter().map(|s| s.sign(epoch, height)).collect();
        assert_eq!(
            new_committee
                .aggregate(&old_partials, epoch, height)
                .unwrap_err(),
            BeaconError::InsufficientPartials { got: 0, need: 2 }
        );
        // ...and HONESTLY does not revoke them: old shares remain valid
        // points of the same f(0) under the OLD surface. Without proactive
        // DELETION, a t-subset of un-erased old shares still computes the
        // (identical) group signature.
        assert!(old_committee.verify_partial(&old_partial, epoch, height));
        let ghost = beacon_at(&old_committee, &old_shares[0..3], epoch, height).unwrap();
        assert_eq!(ghost.to_bytes(), new_beacon.to_bytes());
    }

    #[test]
    fn reshare_rejects_unanchored_dealings_and_thin_dealer_sets() {
        let old_outs = run_dkg(5, 3, 60);
        let new_params = DkgParams { n: 3, t: 2 };
        let view = old_outs[0].public_view();

        // A dealer trying to substitute a FRESH secret (commitments not
        // anchored to its old share public) is rejected fail-closed: build
        // a dealing from old member 1's secret but claim it is member 2's.
        let (mut forged, _) = reshare_deal_with_seed(&old_outs[0], new_params, [200; 32]).unwrap();
        forged.dealer = 2;
        let mut p = ReshareParticipant::new(view.clone(), new_params, 1).unwrap();
        assert_eq!(
            p.receive_dealing(&forged).unwrap_err(),
            DkgError::MalformedDealing { dealer: 2 }
        );

        // Fewer than old-t valid dealings cannot finalize.
        let (d1, ss1) = reshare_deal_with_seed(&old_outs[0], new_params, [201; 32]).unwrap();
        let (d2, ss2) = reshare_deal_with_seed(&old_outs[1], new_params, [202; 32]).unwrap();
        p.receive_dealing(&d1).unwrap();
        p.receive_dealing(&d2).unwrap();
        for ps in ss1.iter().chain(&ss2).filter(|ps| ps.recipient == 1) {
            p.receive_share(ps).unwrap();
        }
        assert_eq!(
            p.finalize().unwrap_err(),
            DkgError::InsufficientDealers { got: 2, need: 3 }
        );
    }

    // ── Serde: every round message rides turns later ──────────────────────

    #[test]
    fn round_messages_roundtrip_through_serde() {
        let params = DkgParams { n: 4, t: 2 };
        let (p1, dealing, priv_shares) =
            DkgParticipant::new_with_seed(params, 1, [33; 32]).unwrap();

        let complaint = Complaint {
            dealer: 1,
            complainer: 3,
        };
        let ack = ShareResponse::Ack {
            dealer: 1,
            member: 2,
        };
        let reveal = p1.reveal(&complaint).unwrap();

        let outs = run_dkg(4, 2, 110);
        let (reshare_dealing, reshare_shares) =
            reshare_deal_with_seed(&outs[0], DkgParams { n: 3, t: 2 }, [111; 32]).unwrap();

        macro_rules! roundtrip {
            ($v:expr, $ty:ty) => {{
                let bytes = postcard::to_allocvec(&$v).unwrap();
                let back: $ty = postcard::from_bytes(&bytes).unwrap();
                assert_eq!($v, back);
            }};
        }
        roundtrip!(params, DkgParams);
        roundtrip!(dealing, Dealing);
        roundtrip!(priv_shares[2].clone(), PrivateShare);
        roundtrip!(complaint, Complaint);
        roundtrip!(ack, ShareResponse);
        roundtrip!(ShareResponse::Complaint(complaint), ShareResponse);
        roundtrip!(reveal, ComplaintReveal);
        roundtrip!(reshare_dealing, ReshareDealing);
        roundtrip!(reshare_shares[1].clone(), ResharePrivateShare);

        // The byte codecs validate points on the way in.
        assert_eq!(Dealing::from_bytes(&dealing.to_bytes()).unwrap(), dealing);
        assert!(Dealing::from_bytes(b"junk").is_err());

        // Public view: byte-compatible with BeaconCommittee::to_bytes.
        let committee = BeaconCommittee::from(&outs[0]);
        let view = DkgPublicView::from_bytes(&committee.to_bytes()).unwrap();
        assert_eq!(view, outs[0].public_view());
    }
}
