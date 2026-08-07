//! Relinearization for the DISTRIBUTED `t < n` committee.
//!
//! # Why the custody rows cannot carry this, and what does
//!
//! The committee has two secret-sharing structures over the same collective
//! secret, and only one of them supports relinearization.
//!
//! * **Lagrange (custody).** Party `i` holds `s_i = sum_d S_d(i+1, 0)` and any
//!   `t` parties recover `s` by `sum_i lambda_i s_i`. This is what
//!   [`super::quorum::QuorumParty::partial_decrypt`] uses: each party applies
//!   its own `lambda_i` locally and publishes a smudged share.
//! * **Additive over dealers.** `s = sum_d s_d`, where each dealer's `s_d` is
//!   the ternary contribution it sampled in [`super::quorum::deal`]. This is the
//!   structure the collective public key is aggregated over in the first place
//!   (`p0 = sum_d (-a s_d + e_d)`).
//!
//! **Relinearization runs on the second one. It cannot run on the first**, and
//! this is not a matter of finding the right coefficients — it is the noise
//! budget. fhe.rs's mbfv `RelinKeyGen` (Mouchet et al., Protocol 2) has each
//! party emit `h0_i = -a u_i + w s_i + e0_i` and `h1_i = a s_i + e1_i` in round
//! 1, aggregate by PLAIN SUM, and then in round 2 multiply the round-1 aggregate
//! by its own secret again — the step that puts `w s^2` into the key. Three
//! things break under a Lagrange combination, each independently fatal:
//!
//! 1. **Round-1 noise is amplified by secret material in round 2.** Lagrange
//!    coefficients are full-width mod `q`, so `sum_i lambda_i e0_i` is uniform
//!    rather than short, and round 2 multiplies that aggregate by `s`. The
//!    relinearization key's error term must be SHORT for the key to be correct;
//!    here it is uniform, and the key relinearizes to garbage. This is the
//!    quadratic amplification, and it already kills the scheme at round 1.
//! 2. **The ephemeral `u` must be short and stops being short.** fhe.rs samples
//!    it with `Poly::small` and it survives into round 2 as `(u - s) h1`;
//!    `sum_i lambda_i u_i` is uniform.
//! 3. **Dropping the fresh per-party noise is not an escape.** Round 2 publishes
//!    `s_i * h0` with `h0` public, which reveals `s_i` outright.
//!
//! The honest alternative — reshare to a degree-`2(t-1)` sharing, collect
//! `2t-1` points and run a degree-reduction round — is a protocol this
//! repository does not have and would need its own malicious-security argument.
//! The additive-of-shorts structure is already present, already `n`-of-`n`, and
//! is exactly the shape upstream was written for, so this module uses it.
//!
//! # What that costs, stated plainly
//!
//! This ceremony is `n`-of-`n` over dealers: **every** party must be live for
//! it. That is the same availability requirement the DKG SETUP already has
//! ("all `n` must be live for the setup" — [`super::distributed`]), and it does
//! not touch the `t`-of-`n` OPENING property, which still tolerates `n - t`
//! offline parties. A party that dies during relin means the relin ceremony
//! restarts; the custody it already established survives untouched.
//!
//! It does not lower the corruption threshold either — see
//! [`super::quorum::DealerRelinSecret`] for that argument.
//!
//! # Security boundary
//!
//! Narrowly: this is upstream fhe.rs's HONEST `n`-of-`n` mbfv relin protocol,
//! run between processes over the committee's authenticated transport, with the
//! same "aggregation checks no well-formedness proof" hole the in-process path
//! has ([`super::relin`]). A malformed or biased party contribution corrupts the
//! collective relin key and is caught only by the acceptance gate
//! ([`crate::threshold::relying_party::DistributedCommitteeClient::relin_key`]),
//! which is DETECTION under an honest coordinator, not attribution. There is no
//! per-share ZK proof here, and none of it is formalized in Lean. What the
//! transport does add over the in-process path is that every share travels
//! inside a sealed, route-bound, dually-signed envelope, so a share cannot be
//! injected, replayed onto another route, or attributed to a party that did not
//! send it.

use fhe::bfv::RelinearizationKey;
use fhe::mbfv::{
    round::{R1Aggregated, R1, R2},
    Aggregate, CommonRandomPoly, RelinKeyGenerator, RelinKeyShare,
};
use rand_09::rngs::StdRng;
use rand_09::{RngCore, SeedableRng};
use std::collections::BTreeSet;

use super::quorum::DealerRelinSecret;
use super::relin::{RelinError, RelinKeySession, Result};
use super::BfvParams;

/// Wire magic for one relin share message. The payload shape below is bound to
/// it; a change here is a flag day and old wires refuse to parse.
const RELIN_MESSAGE_MAGIC: &[u8; 8] = b"FHDRv001";

const ROUND_1: u8 = 1;
const ROUND_1_AGGREGATE: u8 = 2;
const ROUND_2: u8 = 3;

/// One dealer's relinearization party state, held across BOTH rounds.
///
/// The protocol requires the SAME ephemeral `u` in round 1 and round 2. Upstream
/// keeps that inside a borrowing `RelinKeyGenerator`, which an event-driven
/// party process cannot store between two socket round-trips. This holds the
/// seed `u` is drawn from instead and rebuilds the generator per round, so `u`
/// is identical across rounds while every round's smoothing noise stays fresh
/// from the OS.
///
/// No `Clone`, `Debug` or serializer: it owns the dealer's short secret.
pub struct RelinDealerParty {
    session: RelinKeySession,
    dealer: usize,
    params: BfvParams,
    secret_key: fhe::bfv::SecretKey,
    crp: Vec<CommonRandomPoly>,
    /// Seed for the ephemeral `u` ONLY. Secret: `u` is secret material.
    u_seed: [u8; 32],
}

impl RelinDealerParty {
    /// Bind a dealer's retained short secret to one exact relin ceremony.
    pub fn new(
        session: &RelinKeySession,
        params: &BfvParams,
        secret: &DealerRelinSecret,
    ) -> Result<Self> {
        let dealer = secret.dealer();
        let n_parties = session.keygen_session().n_parties();
        if dealer >= n_parties {
            return Err(RelinError::InvalidParty {
                party: dealer,
                n_parties,
            });
        }
        if secret.session().public_key_session() != session.keygen_session() {
            return Err(RelinError::SessionMismatch { party: dealer });
        }
        let mut u_seed = [0u8; 32];
        rand_09::rng().fill_bytes(&mut u_seed);
        Ok(Self {
            session: session.clone(),
            dealer,
            params: params.clone(),
            secret_key: secret.secret_key(params),
            crp: session.common_random_polys(params)?,
            u_seed,
        })
    }

    pub fn dealer(&self) -> usize {
        self.dealer
    }

    /// Rebuild the generator with the SAME `u` as every other round.
    ///
    /// `u_rng` is seeded, so `u` is reproduced exactly; the smoothing noise each
    /// round adds comes from a separate fresh OS rng at the call site.
    fn generator(&self) -> Result<RelinKeyGenerator<'_, '_>> {
        let mut u_rng = StdRng::from_seed(self.u_seed);
        RelinKeyGenerator::new(&self.secret_key, &self.crp, &mut u_rng).map_err(|_| {
            RelinError::Fhe {
                phase: "party setup",
            }
        })
    }

    /// This party's round-1 share, as a sealed-transport-ready message.
    pub fn round_1(&self) -> Result<Vec<u8>> {
        let share = self
            .generator()?
            .round_1(&mut rand_09::rng())
            .map_err(|_| RelinError::Fhe { phase: "round 1" })?;
        Ok(encode_message(
            ROUND_1,
            self.session.session_id(),
            self.dealer,
            &share.to_canonical_bytes(),
        ))
    }

    /// This party's round-2 share, computed against the coordinator's round-1
    /// aggregate.
    ///
    /// The aggregate is re-parsed under this party's OWN session id, so an
    /// aggregate from a different ceremony is refused rather than folded in.
    pub fn round_2(&self, round_1_aggregate: &[u8]) -> Result<Vec<u8>> {
        let aggregate = decode_round_1_aggregate(round_1_aggregate, &self.session, &self.params)?;
        let share = self
            .generator()?
            .round_2(&aggregate, &mut rand_09::rng())
            .map_err(|_| RelinError::Fhe { phase: "round 2" })?;
        Ok(encode_message(
            ROUND_2,
            self.session.session_id(),
            self.dealer,
            &share.to_canonical_bytes(),
        ))
    }
}

fn encode_message(round: u8, session_id: [u8; 32], party: usize, share: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(share.len() + 57);
    out.extend_from_slice(RELIN_MESSAGE_MAGIC);
    out.push(round);
    out.extend_from_slice(&session_id);
    out.extend_from_slice(&(party as u64).to_le_bytes());
    out.extend_from_slice(&(share.len() as u64).to_le_bytes());
    out.extend_from_slice(share);
    out
}

/// Strictly parse one relin message and return `(party, share bytes)`.
///
/// Refuses a wrong magic, the wrong round, a share from a DIFFERENT ceremony
/// (the session id is covered), a party index outside the roster, a truncated
/// body, and any trailing byte.
fn decode_message<'a>(
    bytes: &'a [u8],
    round: u8,
    session: &RelinKeySession,
) -> Result<(usize, &'a [u8])> {
    let malformed = || RelinError::Fhe {
        phase: "share message",
    };
    if bytes.len() < 57 || &bytes[..8] != RELIN_MESSAGE_MAGIC.as_slice() {
        return Err(malformed());
    }
    if bytes[8] != round {
        return Err(RelinError::PhaseMismatch);
    }
    if bytes[9..41] != session.session_id() {
        return Err(RelinError::SessionMismatch { party: usize::MAX });
    }
    let party = u64::from_le_bytes(bytes[41..49].try_into().map_err(|_| malformed())?);
    let party = usize::try_from(party).map_err(|_| malformed())?;
    let n_parties = session.keygen_session().n_parties();
    if party >= n_parties {
        return Err(RelinError::InvalidParty { party, n_parties });
    }
    let len = u64::from_le_bytes(bytes[49..57].try_into().map_err(|_| malformed())?);
    let len = usize::try_from(len).map_err(|_| malformed())?;
    let end = 57usize.checked_add(len).ok_or_else(malformed)?;
    if end != bytes.len() {
        return Err(malformed());
    }
    Ok((party, &bytes[57..end]))
}

/// Check that a set of received messages is EXACTLY the full roster, once each.
///
/// Relin is `n`-of-`n`: a missing party is not a smaller quorum, it is a key
/// that decrypts to garbage. A duplicate is a party counted twice.
fn check_full_roster(parties: &BTreeSet<usize>, session: &RelinKeySession) -> Result<()> {
    let n = session.keygen_session().n_parties();
    if *parties != (0..n).collect::<BTreeSet<_>>() {
        return Err(RelinError::QuorumTooSmall {
            have: parties.len(),
            need: n,
        });
    }
    Ok(())
}

/// COORDINATOR: fold every party's round-1 share into the aggregate that round 2
/// is computed against.
pub fn aggregate_round_1(
    session: &RelinKeySession,
    params: &BfvParams,
    messages: &[Vec<u8>],
) -> Result<Vec<u8>> {
    let mut seen = BTreeSet::new();
    let mut shares = Vec::with_capacity(messages.len());
    for message in messages {
        let (party, share_bytes) = decode_message(message, ROUND_1, session)?;
        if !seen.insert(party) {
            return Err(RelinError::DuplicateParty { party });
        }
        shares.push(
            RelinKeyShare::<R1>::from_canonical_bytes(share_bytes, params.arc()).map_err(|_| {
                RelinError::Fhe {
                    phase: "round 1 share decode",
                }
            })?,
        );
    }
    check_full_roster(&seen, session)?;
    let aggregated =
        RelinKeyShare::<R1Aggregated>::from_shares(shares).map_err(|_| RelinError::Fhe {
            phase: "round 1 aggregation",
        })?;
    Ok(encode_message(
        ROUND_1_AGGREGATE,
        session.session_id(),
        0,
        &aggregated.to_canonical_bytes(),
    ))
}

fn decode_round_1_aggregate(
    bytes: &[u8],
    session: &RelinKeySession,
    params: &BfvParams,
) -> Result<std::sync::Arc<RelinKeyShare<R1Aggregated>>> {
    let (_, share_bytes) = decode_message(bytes, ROUND_1_AGGREGATE, session)?;
    let share = RelinKeyShare::<R1Aggregated>::from_canonical_bytes(share_bytes, params.arc())
        .map_err(|_| RelinError::Fhe {
            phase: "round 1 aggregate decode",
        })?;
    Ok(std::sync::Arc::new(share))
}

/// COORDINATOR: assemble the collective relinearization key from every party's
/// round-2 share.
///
/// Every share must carry the SAME round-1 aggregate the coordinator published;
/// upstream's assembler silently takes the aggregate from whichever share it
/// happens to see first, so a party that answered against a different aggregate
/// would otherwise be folded in unnoticed. That is checked here.
pub fn assemble_relin_key(
    session: &RelinKeySession,
    params: &BfvParams,
    round_1_aggregate: &[u8],
    messages: &[Vec<u8>],
) -> Result<RelinearizationKey> {
    let (_, published_aggregate) = decode_message(round_1_aggregate, ROUND_1_AGGREGATE, session)?;
    let mut seen = BTreeSet::new();
    let mut shares = Vec::with_capacity(messages.len());
    for message in messages {
        let (party, share_bytes) = decode_message(message, ROUND_2, session)?;
        if !seen.insert(party) {
            return Err(RelinError::DuplicateParty { party });
        }
        let share =
            RelinKeyShare::<R2>::from_canonical_bytes(share_bytes, params.arc()).map_err(|_| {
                RelinError::Fhe {
                    phase: "round 2 share decode",
                }
            })?;
        if share.carried_round_1_canonical_bytes() != Some(published_aggregate.to_vec()) {
            return Err(RelinError::RoundOneAggregateMismatch { party });
        }
        shares.push(share);
    }
    check_full_roster(&seen, session)?;
    RelinearizationKey::from_shares(shares).map_err(|_| RelinError::Fhe {
        phase: "key assembly",
    })
}

/// The mandatory acceptance gate for a DISTRIBUTED relin key.
///
/// # Why assembly alone cannot be the gate
///
/// [`assemble_relin_key`] refuses everything STRUCTURAL — a wrong round, a
/// foreign ceremony, a short or duplicated roster, an unpublished round-1
/// aggregate, a share that does not parse. It cannot refuse a share that is
/// well-formed and WRONG, because aggregation checks no well-formedness proof:
/// a malformed or biased contribution is a valid-looking poly vector, and the
/// only place the fault becomes visible is at multiply time, unattributably.
/// Byte-flipping a round-2 share deep in its payload lands exactly here — it was
/// measured doing so while writing these teeth.
///
/// This gate closes that, fail-closed: it runs `trials` (at least 8) FRESH
/// random `ct x ct` products through the candidate key and requires every one to
/// decrypt to the EXACT plaintext product. A corrupt key produces a mismatch and
/// is refused, so it is never cached or used. Fresh per-call randomness means a
/// corrupt key cannot be tuned to pass a fixed vector.
///
/// It is DETECTION under an honest coordinator, not ATTRIBUTION: it says the key
/// is bad, never which party made it bad. `open` is supplied by the caller so
/// the same gate serves an in-process quorum and a real distributed committee
/// opening; whatever it is, it must be a genuine `t`-of-`n` open, because a gate
/// that decrypts with a locally-held secret would be checking nothing.
pub fn relin_acceptance_gate<F>(
    key: &RelinearizationKey,
    params: &BfvParams,
    collective: &super::CollectivePublicKey,
    trials: usize,
    mut open: F,
) -> Result<()>
where
    F: FnMut(&crate::bfv_mul::BoundedCiphertext) -> Result<u64>,
{
    use fhe::bfv::{Encoding, Plaintext};
    use fhe_traits::{FheEncoder, FheEncrypter};

    let trials = trials.max(8);
    let engine =
        crate::bfv_mul::MulEngine::new(key, params.arc()).map_err(|_| RelinError::Fhe {
            phase: "acceptance multiplicator",
        })?;
    // Keep the product well inside the plaintext modulus so a refusal can only
    // mean a bad key, never the wrap guard.
    let bound = 64u64;
    let mut rng = rand_09::rng();

    for trial in 0..trials {
        let left = rng.next_u64() % (bound + 1);
        let right = rng.next_u64() % (bound + 1);
        let encrypt =
            |value: u64| -> Result<fhe::bfv::Ciphertext> {
                let mut slots = vec![0u64; params.degree()];
                slots[0] = value;
                let plaintext = Plaintext::try_encode(&slots, Encoding::simd(), params.arc())
                    .map_err(|_| RelinError::Fhe {
                        phase: "acceptance encode",
                    })?;
                collective
                    .pk
                    .try_encrypt(&plaintext, &mut rand_09::rng())
                    .map_err(|_| RelinError::Fhe {
                        phase: "acceptance encrypt",
                    })
            };
        let product = engine
            .multiply(
                &crate::bfv_mul::BoundedCiphertext::new(encrypt(left)?, bound),
                &crate::bfv_mul::BoundedCiphertext::new(encrypt(right)?, bound),
            )
            .map_err(|_| RelinError::Fhe {
                phase: "acceptance multiply",
            })?;
        if open(&product)? != left * right {
            return Err(RelinError::AcceptanceFailed { trial });
        }
    }
    Ok(())
}
