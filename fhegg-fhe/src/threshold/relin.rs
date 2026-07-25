//! Party-owned multiparty BFV relinearization-key generation.
//!
//! A BFV ciphertext×ciphertext multiplication needs a relinearization key.
//! Constructing it with `RelinearizationKey::new(&assembled_secret, ...)`
//! would silently undo threshold custody even if encryption and decryption
//! were otherwise collective.  This module instead runs fhe.rs's multiparty
//! BFV `RelinKeyGen` protocol over the exact [`ThresholdParty`] shares that
//! produced the collective public key.
//!
//! Each scoped party worker reconstructs only its own fhe.rs `SecretKey`,
//! retains the secret-dependent `RelinKeyGenerator` (including its private
//! ephemeral `u`) across both rounds, and emits only typed fhe.rs R1/R2
//! shares.  The coordinator enforces the exact keygen session, public-key
//! digest, roster, phase, and deadline before aggregating the public
//! `RelinearizationKey`.  There is no API that returns a party secret or an
//! assembled secret key.
//!
//! [`transport`] authenticates a strict canonical public control envelope for
//! each round and provides a bounded, restart-safe coordinator snapshot.  The
//! algebraic `RelinKeyShare<R1/R2>` payload itself remains an opaque fhe.rs
//! type with no public codec, however: after coordinator recovery the live
//! party must resend the typed public share under the exact recorded envelope.
//! The manifest ID cannot yet cryptographically commit to that opaque value.
//!
//! Security boundary, stated narrowly: this is fhe.rs's honest n-of-n mbfv
//! protocol.  There is no malicious-share proof, party restart during the
//! secret-dependent two-round generator, dropout recovery or `t < n` relin
//! ceremony, and the construction has not yet been formalized in Lean.  It
//! removes the assembled-secret-key generation seam from the legacy n-of-n
//! Dark AMM; it does not by itself upgrade that lane to a malicious-secure
//! network ceremony.

use std::collections::BTreeSet;
use std::sync::{mpsc, Arc};
use std::thread;
use std::time::{Duration, Instant};

use fhe::bfv::RelinearizationKey;
use fhe::mbfv::{
    round::{R1Aggregated, R1, R2},
    Aggregate, CommonRandomPoly, RelinKeyGenerator, RelinKeyShare,
};
use fhe_traits::Serialize as FheSerialize;
use rand_09::rngs::StdRng;
use rand_09::{RngCore, SeedableRng};
use sha2::{Digest, Sha256};

use super::{sk_from_coeffs, BfvParams, CollectivePublicKey, KeygenSession, ThresholdParty};

/// Authenticated canonical control envelopes and restart-safe coordinator
/// state for this ceremony.  See the module-level boundary before treating an
/// envelope as a proof of the opaque upstream algebraic share.
pub mod transport;

const CRP_DOMAIN: &[u8] = b"fhegg/threshold/relin-crp/v1";
const SESSION_DOMAIN: &[u8] = b"fhegg/threshold/relin-session/v1";
const PUBLIC_KEY_DOMAIN: &[u8] = b"fhegg/threshold/relin-public-key/v1";

pub type Result<T> = std::result::Result<T, RelinError>;

/// Fail-closed errors from the n-of-n relinearization ceremony.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RelinError {
    EmptyRoster,
    QuorumTooSmall {
        have: usize,
        need: usize,
    },
    DuplicateParty {
        party: usize,
    },
    InvalidParty {
        party: usize,
        n_parties: usize,
    },
    SessionMismatch {
        party: usize,
    },
    PublicKeyMismatch,
    ZeroTimeout,
    Timeout {
        phase: &'static str,
    },
    ChannelClosed {
        phase: &'static str,
    },
    PhaseMismatch,
    Fhe {
        phase: &'static str,
    },
    PartyPanicked,
    /// The candidate n-of-n relin key failed its mandatory acceptance gate: a FRESH random trial ct×ct
    /// product did not decrypt to the exact plaintext product under the full threshold quorum. Fail closed —
    /// a silently-corrupt relin key (a malformed/biased party contribution slips past aggregation, which
    /// checks no well-formedness proof) is refused here and never cached or used.
    AcceptanceFailed {
        trial: usize,
    },
}

impl std::fmt::Display for RelinError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptyRoster => write!(f, "relinearization roster is empty"),
            Self::QuorumTooSmall { have, need } => {
                write!(f, "relinearization needs {need} parties, received {have}")
            }
            Self::DuplicateParty { party } => {
                write!(f, "duplicate relinearization party {party}")
            }
            Self::InvalidParty { party, n_parties } => write!(
                f,
                "relinearization party {party} is outside roster 0..{n_parties}"
            ),
            Self::SessionMismatch { party } => {
                write!(f, "party {party} belongs to a different keygen session")
            }
            Self::PublicKeyMismatch => {
                write!(f, "collective public key differs from the bound session")
            }
            Self::ZeroTimeout => write!(f, "relinearization timeout must be nonzero"),
            Self::Timeout { phase } => write!(f, "relinearization timed out during {phase}"),
            Self::ChannelClosed { phase } => {
                write!(f, "relinearization channel closed during {phase}")
            }
            Self::PhaseMismatch => write!(f, "relinearization message has the wrong phase"),
            Self::Fhe { phase } => write!(f, "fhe.rs rejected relinearization {phase}"),
            Self::PartyPanicked => write!(f, "a relinearization party worker panicked"),
            Self::AcceptanceFailed { trial } => write!(
                f,
                "relin key failed the acceptance gate at trial {trial}: a fresh ct×ct product did not \
                 decrypt to the exact plaintext product under the quorum (candidate key refused)"
            ),
        }
    }
}

impl std::error::Error for RelinError {}

/// Public identity and deadline of one exact relinearization ceremony.
///
/// `public_entropy` is not consumed directly as polynomial randomness.  It is
/// domain-separated from the keygen CRP and bound to the collective public
/// key before expansion into fhe.rs's relinearization CRP vector.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelinKeySession {
    keygen: KeygenSession,
    collective_public_key_digest: [u8; 32],
    crp_seed: [u8; 32],
    session_id: [u8; 32],
    timeout: Duration,
}

impl RelinKeySession {
    /// Begin a ceremony with fresh public entropy.
    pub fn random(
        keygen: &KeygenSession,
        collective: &CollectivePublicKey,
        timeout: Duration,
    ) -> Result<Self> {
        let mut public_entropy = [0u8; 32];
        rand_09::rng().fill_bytes(&mut public_entropy);
        Self::from_public_entropy(keygen, collective, public_entropy, timeout)
    }

    /// Deterministically reconstruct a public ceremony identity.
    pub fn from_public_entropy(
        keygen: &KeygenSession,
        collective: &CollectivePublicKey,
        public_entropy: [u8; 32],
        timeout: Duration,
    ) -> Result<Self> {
        if keygen.n_parties() == 0 {
            return Err(RelinError::EmptyRoster);
        }
        if timeout.is_zero() {
            return Err(RelinError::ZeroTimeout);
        }
        let collective_public_key_digest = public_key_digest(collective);

        let mut crp = Sha256::new();
        crp.update(CRP_DOMAIN);
        bind_keygen(&mut crp, keygen);
        crp.update(collective_public_key_digest);
        crp.update(public_entropy);
        let crp_seed: [u8; 32] = crp.finalize().into();

        let mut identity = Sha256::new();
        identity.update(SESSION_DOMAIN);
        bind_keygen(&mut identity, keygen);
        identity.update(collective_public_key_digest);
        identity.update(crp_seed);
        identity.update(timeout.as_nanos().to_le_bytes());
        let session_id = identity.finalize().into();

        Ok(Self {
            keygen: keygen.clone(),
            collective_public_key_digest,
            crp_seed,
            session_id,
            timeout,
        })
    }

    pub fn keygen_session(&self) -> &KeygenSession {
        &self.keygen
    }

    pub fn collective_public_key_digest(&self) -> [u8; 32] {
        self.collective_public_key_digest
    }

    pub fn crp_seed(&self) -> [u8; 32] {
        self.crp_seed
    }

    pub fn session_id(&self) -> [u8; 32] {
        self.session_id
    }

    pub fn timeout(&self) -> Duration {
        self.timeout
    }

    fn common_random_polys(&self, params: &BfvParams) -> Result<Vec<CommonRandomPoly>> {
        let mut rng = StdRng::from_seed(self.crp_seed);
        CommonRandomPoly::new_vec(params.arc(), &mut rng).map_err(|_| RelinError::Fhe {
            phase: "CRP expansion",
        })
    }
}

fn bind_keygen(hasher: &mut Sha256, keygen: &KeygenSession) {
    hasher.update((keygen.n_parties() as u64).to_le_bytes());
    hasher.update(keygen.crp_seed());
}

fn public_key_digest(collective: &CollectivePublicKey) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(PUBLIC_KEY_DOMAIN);
    hasher.update(collective.pk.to_bytes());
    hasher.finalize().into()
}

struct R1Envelope {
    session_id: [u8; 32],
    party: usize,
    share: RelinKeyShare<R1>,
}

struct R2Envelope {
    session_id: [u8; 32],
    party: usize,
    share: RelinKeyShare<R2>,
}

enum PartyMessage {
    R1(R1Envelope),
    R2(R2Envelope),
    Failed(RelinError),
}

struct R1Broadcast {
    session_id: [u8; 32],
    share: Arc<RelinKeyShare<R1Aggregated>>,
}

fn remaining(deadline: Instant, phase: &'static str) -> Result<Duration> {
    deadline
        .checked_duration_since(Instant::now())
        .filter(|duration| !duration.is_zero())
        .ok_or(RelinError::Timeout { phase })
}

fn receive(
    receiver: &mpsc::Receiver<PartyMessage>,
    deadline: Instant,
    phase: &'static str,
) -> Result<PartyMessage> {
    match receiver.recv_timeout(remaining(deadline, phase)?) {
        Ok(message) => Ok(message),
        Err(mpsc::RecvTimeoutError::Timeout) => Err(RelinError::Timeout { phase }),
        Err(mpsc::RecvTimeoutError::Disconnected) => Err(RelinError::ChannelClosed { phase }),
    }
}

fn run_relin_party(
    party: &ThresholdParty,
    params: &BfvParams,
    session: &RelinKeySession,
    messages: mpsc::Sender<PartyMessage>,
    r1_broadcast: mpsc::Receiver<R1Broadcast>,
    deadline: Instant,
) -> Result<()> {
    let party_index = party.party();
    if party.keygen_session != session.keygen {
        return Err(RelinError::SessionMismatch { party: party_index });
    }

    // `sk`, `crp`, and the generator's secret-dependent ephemeral `u` all
    // remain in this party worker across both rounds.
    let sk = sk_from_coeffs(&party.key_share.coeffs, params.arc());
    let crp = session.common_random_polys(params)?;
    let mut rng = rand_09::rng();
    let generator = RelinKeyGenerator::new(&sk, &crp, &mut rng).map_err(|_| RelinError::Fhe {
        phase: "party setup",
    })?;
    let r1 = generator
        .round_1(&mut rng)
        .map_err(|_| RelinError::Fhe { phase: "round 1" })?;
    messages
        .send(PartyMessage::R1(R1Envelope {
            session_id: session.session_id,
            party: party_index,
            share: r1,
        }))
        .map_err(|_| RelinError::ChannelClosed {
            phase: "round 1 send",
        })?;

    let broadcast = match r1_broadcast.recv_timeout(remaining(deadline, "round 1 broadcast")?) {
        Ok(broadcast) => broadcast,
        Err(mpsc::RecvTimeoutError::Timeout) => {
            return Err(RelinError::Timeout {
                phase: "round 1 broadcast",
            });
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            return Err(RelinError::ChannelClosed {
                phase: "round 1 broadcast",
            });
        }
    };
    if broadcast.session_id != session.session_id {
        return Err(RelinError::SessionMismatch { party: party_index });
    }

    let r2 = generator
        .round_2(&broadcast.share, &mut rng)
        .map_err(|_| RelinError::Fhe { phase: "round 2" })?;
    messages
        .send(PartyMessage::R2(R2Envelope {
            session_id: session.session_id,
            party: party_index,
            share: r2,
        }))
        .map_err(|_| RelinError::ChannelClosed {
            phase: "round 2 send",
        })?;
    Ok(())
}

/// Run one complete n-of-n multiparty relinearization ceremony.
///
/// Party workers borrow opaque [`ThresholdParty`] values and the coordinator
/// receives only the two upstream public protocol shares.  The returned key is
/// directly consumable by fhe.rs `Multiplicator` / fhEgg `MulEngine`.
pub fn generate_relinearization_key(
    session: &RelinKeySession,
    params: &BfvParams,
    collective: &CollectivePublicKey,
    parties: &[ThresholdParty],
) -> Result<RelinearizationKey> {
    let n = session.keygen.n_parties();
    if parties.len() < n {
        return Err(RelinError::QuorumTooSmall {
            have: parties.len(),
            need: n,
        });
    }
    if public_key_digest(collective) != session.collective_public_key_digest {
        return Err(RelinError::PublicKeyMismatch);
    }

    let mut roster = BTreeSet::new();
    for party in parties {
        let party_index = party.party();
        if party_index >= n {
            return Err(RelinError::InvalidParty {
                party: party_index,
                n_parties: n,
            });
        }
        if !roster.insert(party_index) {
            return Err(RelinError::DuplicateParty { party: party_index });
        }
        if party.keygen_session != session.keygen {
            return Err(RelinError::SessionMismatch { party: party_index });
        }
    }
    if roster != (0..n).collect() {
        return Err(RelinError::QuorumTooSmall {
            have: roster.len(),
            need: n,
        });
    }

    let deadline = Instant::now()
        .checked_add(session.timeout)
        .ok_or(RelinError::Timeout {
            phase: "session setup",
        })?;
    thread::scope(|scope| {
        let (messages_tx, messages_rx) = mpsc::channel::<PartyMessage>();
        let mut broadcasts = Vec::with_capacity(n);
        let mut workers = Vec::with_capacity(n);
        for party in parties {
            let (broadcast_tx, broadcast_rx) = mpsc::channel::<R1Broadcast>();
            broadcasts.push(broadcast_tx);
            let messages_tx = messages_tx.clone();
            workers.push(scope.spawn(move || {
                let result = run_relin_party(
                    party,
                    params,
                    session,
                    messages_tx.clone(),
                    broadcast_rx,
                    deadline,
                );
                if let Err(error) = result {
                    let _ = messages_tx.send(PartyMessage::Failed(error));
                }
            }));
        }
        drop(messages_tx);

        let mut seen_r1 = BTreeSet::new();
        let mut r1_shares = Vec::with_capacity(n);
        while r1_shares.len() < n {
            match receive(&messages_rx, deadline, "round 1 collection")? {
                PartyMessage::R1(envelope) => {
                    if envelope.session_id != session.session_id {
                        return Err(RelinError::SessionMismatch {
                            party: envelope.party,
                        });
                    }
                    if envelope.party >= n {
                        return Err(RelinError::InvalidParty {
                            party: envelope.party,
                            n_parties: n,
                        });
                    }
                    if !seen_r1.insert(envelope.party) {
                        return Err(RelinError::DuplicateParty {
                            party: envelope.party,
                        });
                    }
                    r1_shares.push(envelope.share);
                }
                PartyMessage::R2(_) => return Err(RelinError::PhaseMismatch),
                PartyMessage::Failed(error) => return Err(error),
            }
        }
        let r1 = Arc::new(
            RelinKeyShare::<R1Aggregated>::from_shares(r1_shares).map_err(|_| RelinError::Fhe {
                phase: "round 1 aggregation",
            })?,
        );
        for broadcast in broadcasts {
            broadcast
                .send(R1Broadcast {
                    session_id: session.session_id,
                    share: Arc::clone(&r1),
                })
                .map_err(|_| RelinError::ChannelClosed {
                    phase: "round 1 broadcast",
                })?;
        }

        let mut seen_r2 = BTreeSet::new();
        let mut r2_shares = Vec::with_capacity(n);
        while r2_shares.len() < n {
            match receive(&messages_rx, deadline, "round 2 collection")? {
                PartyMessage::R2(envelope) => {
                    if envelope.session_id != session.session_id {
                        return Err(RelinError::SessionMismatch {
                            party: envelope.party,
                        });
                    }
                    if envelope.party >= n {
                        return Err(RelinError::InvalidParty {
                            party: envelope.party,
                            n_parties: n,
                        });
                    }
                    if !seen_r2.insert(envelope.party) {
                        return Err(RelinError::DuplicateParty {
                            party: envelope.party,
                        });
                    }
                    r2_shares.push(envelope.share);
                }
                PartyMessage::R1(_) => return Err(RelinError::PhaseMismatch),
                PartyMessage::Failed(error) => return Err(error),
            }
        }

        for worker in workers {
            worker.join().map_err(|_| RelinError::PartyPanicked)?;
        }
        RelinearizationKey::from_shares(r2_shares).map_err(|_| RelinError::Fhe {
            phase: "round 2 aggregation",
        })
    })
}

/// **The mandatory relin acceptance gate (roadmap Build 4 — Tier-0 malicious-security detection).**
///
/// Aggregation of the n-of-n relin shares checks NO well-formedness proof, so a malformed/biased party
/// contribution can silently corrupt the collective relin key (the fault surfaces only as garbage at
/// multiply-time, unattributably). This gate catches that fail-closed: it runs `trials` (at least 8) FRESH
/// random ct×ct products through the candidate key and requires each to decrypt — via the full threshold
/// quorum — to the EXACT plaintext product. A corrupt key produces a mismatch and is refused with
/// [`RelinError::AcceptanceFailed`], so it is never cached or used.
///
/// This is DETECTION under an honest coordinator, NOT attribution — an honest stopgap subsumed once the
/// decrypt-share validity certificate (roadmap Build 6) attributes a bad share to its party. It adds no new
/// crypto: it reuses [`MulEngine`], the collective encrypt, and the in-tree threshold `partial_decrypt`/
/// `combine`. Fresh per-call randomness means a corrupt key cannot be tuned to pass a fixed vector.
pub fn relin_acceptance_gate(
    relin: &RelinearizationKey,
    params: &BfvParams,
    collective: &super::CollectivePublicKey,
    parties: &[super::ThresholdParty],
    trials: usize,
) -> Result<()> {
    use crate::bfv_lean::LeanCiphertext;
    use crate::bfv_mul::{BoundedCiphertext, MulEngine};
    use fhe::bfv::{Encoding, Plaintext};
    use fhe_traits::{FheEncoder, FheEncrypter, Serialize as _};
    use rand_09::Rng;

    let t = params.plaintext_modulus();
    let engine = MulEngine::new(relin, params.arc()).map_err(|_| RelinError::Fhe {
        phase: "acceptance-gate engine",
    })?;
    let mut rng = rand_09::rng();
    // Keep m1*m2 < t so the exact product is representable (deployed t ~ 2^20).
    const BOUND: u64 = 1000;
    for trial in 0..trials.max(8) {
        let m1 = rng.random_range(0..BOUND);
        let m2 = rng.random_range(0..BOUND);
        let encrypt = |m: u64| -> std::result::Result<fhe::bfv::Ciphertext, RelinError> {
            let pt = Plaintext::try_encode(&[m], Encoding::simd(), params.arc()).map_err(|_| {
                RelinError::Fhe {
                    phase: "acceptance-gate encode",
                }
            })?;
            collective
                .pk
                .try_encrypt(&pt, &mut rand_09::rng())
                .map_err(|_| RelinError::Fhe {
                    phase: "acceptance-gate encrypt",
                })
        };
        let product = engine
            .multiply(
                &BoundedCiphertext::new(encrypt(m1)?, m1),
                &BoundedCiphertext::new(encrypt(m2)?, m2),
            )
            .map_err(|_| RelinError::Fhe {
                phase: "acceptance-gate multiply",
            })?;
        let lean = LeanCiphertext::from_fhe_bytes(
            &product.ct.to_bytes(),
            params.moduli(),
            params.degree(),
            product.plain_bound,
        )
        .map_err(|_| RelinError::Fhe {
            phase: "acceptance-gate lean boundary",
        })?;
        let shares = parties
            .iter()
            .map(|p| p.partial_decrypt(&lean, super::MIN_SMUDGE_BITS))
            .collect::<std::result::Result<Vec<_>, _>>()
            .map_err(|_| RelinError::Fhe {
                phase: "acceptance-gate partial decrypt",
            })?;
        let opened = super::combine(&shares, params).map_err(|_| RelinError::Fhe {
            phase: "acceptance-gate combine",
        })?;
        if opened.first().copied() != Some((m1 * m2) % t) {
            return Err(RelinError::AcceptanceFailed { trial });
        }
    }
    Ok(())
}

/// [`generate_relinearization_key`] followed by the mandatory [`relin_acceptance_gate`]. Any caller that
/// CACHES or USES a relin key should call this, never the bare generator — a corrupt key never escapes.
pub fn generate_relinearization_key_verified(
    session: &RelinKeySession,
    params: &BfvParams,
    collective: &super::CollectivePublicKey,
    parties: &[super::ThresholdParty],
) -> Result<RelinearizationKey> {
    let relin = generate_relinearization_key(session, params, collective, parties)?;
    relin_acceptance_gate(&relin, params, collective, parties, 8)?;
    Ok(relin)
}
