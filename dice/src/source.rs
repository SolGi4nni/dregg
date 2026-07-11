//! The pluggable [`RandomnessSource`] trait and its implementations.
//!
//! A source has two halves that must agree:
//! - a **producer** ([`RandomnessSource::evidence`]) that, given a request,
//!   emits the [`RandomnessEvidence`] a receipt would carry, and
//! - a pure **verifier** ([`RandomnessSource::seed`]) that re-derives the
//!   [`Seed`] from `(request, evidence)` and checks the evidence, returning the
//!   seed or a [`VerifyError`].
//!
//! The verifier is the trust surface: it is a pure function of public data and is
//! the same regardless of who produced the evidence.

use std::cell::RefCell;

use crate::draw::{DrawStream, Seed};
use crate::error::VerifyError;
use crate::event::EventId;
use crate::request::{
    BeaconEvidence, BeaconKind, BeaconParams, DERIVATION_VERSION, EvidenceKind, Finalization,
    RandomnessEvidence, RandomnessRequest,
};
use crate::util::absorb_len_prefixed;

/// Domain tag for the seed derivation.
pub const DOMAIN_SEED: &[u8] = b"dregg-dice/seed/v1";
/// Domain tag for the commit-reveal commitment.
pub const DOMAIN_COMMIT: &[u8] = b"dregg-dice/commit-reveal/commit/v1";
/// Domain tag for the [`Hybrid`] genesis binding (key-chain root + beacon params).
pub const DOMAIN_HYBRID_GENESIS: &[u8] = b"dregg-dice/hybrid/genesis/v1";
/// Domain tag separating the two halves of the hybrid seed mix.
pub const DOMAIN_HYBRID_MIX: &[u8] = b"dregg-dice/hybrid/mix/v1";
/// Domain tag for a hash-chain beacon forward step.
pub const DOMAIN_BEACON_CHAIN: &[u8] = b"dregg-dice/beacon/hashchain/v1";
/// Domain tag for a key-chain Merkle leaf (`H(tag ‖ pk_bytes)`).
pub const DOMAIN_KEYCHAIN_LEAF: &[u8] = b"dregg-dice/keychain/leaf/v1";
/// Domain tag for a key-chain Merkle interior node (`H(tag ‖ left ‖ right)`).
pub const DOMAIN_KEYCHAIN_NODE: &[u8] = b"dregg-dice/keychain/node/v1";
/// Domain tag for deriving a key-chain epoch's LB-VRF key seed from the master seed.
pub const DOMAIN_KEYCHAIN_EPOCH_SEED: &[u8] = b"dregg-dice/keychain/epoch-seed/v1";

/// Derive a seed from the event id and a source output, domain-separated by a
/// per-source tag. Because the event id binds `draw_count`/`event_kind`/action,
/// the seed is unique to the finalized context.
fn derive_seed(event_id: &EventId, source_tag: &[u8], source_output: &[u8]) -> Seed {
    let mut h = blake3::Hasher::new();
    absorb_len_prefixed(&mut h, DOMAIN_SEED);
    absorb_len_prefixed(&mut h, source_tag);
    h.update(event_id.as_bytes());
    absorb_len_prefixed(&mut h, source_output);
    Seed::from_bytes(*h.finalize().as_bytes())
}

/// Recompute the transcript commitment for a seed under a request's draw count
/// and compare against the evidence. This is the shared grinding tooth every
/// verifier ends with.
fn check_transcript(
    seed: Seed,
    req: &RandomnessRequest,
    ev: &RandomnessEvidence,
) -> Result<Seed, VerifyError> {
    let stream = DrawStream::new(seed, req.draw_count);
    if stream.transcript_commitment() != ev.draw_transcript_commitment {
        return Err(VerifyError::TranscriptMismatch);
    }
    Ok(seed)
}

fn check_version(ev: &RandomnessEvidence) -> Result<(), VerifyError> {
    if ev.derivation_version != DERIVATION_VERSION {
        return Err(VerifyError::UnsupportedVersion {
            expected: DERIVATION_VERSION,
            found: ev.derivation_version,
        });
    }
    Ok(())
}

/// A pluggable source of verifiable randomness.
///
/// `evidence` produces; `seed` verifies. `seed` takes no `self` — verification is
/// a pure function of public data, so a light client checks a source it never
/// instantiated.
pub trait RandomnessSource {
    /// Produce the evidence a receipt would record for `req`.
    fn evidence(&self, req: &RandomnessRequest) -> RandomnessEvidence;

    /// Re-derive and verify the seed from `(req, ev)`.
    fn seed(req: &RandomnessRequest, ev: &RandomnessEvidence) -> Result<Seed, VerifyError>
    where
        Self: Sized;
}

// ─────────────────────────────────────────────────────────────────────────────
// Deterministic — the pure test/offline source.
// ─────────────────────────────────────────────────────────────────────────────

/// A deterministic source keyed on a caller-supplied 32-byte context. Fully
/// reproducible; used for tests and for offline sessions where no external
/// unpredictability source is available. Provides **no** unpredictability
/// guarantee on its own — whoever knows the context knows the seed.
#[derive(Clone, Debug)]
pub struct Deterministic {
    /// Context folded into the seed.
    pub context: [u8; 32],
}

impl Deterministic {
    /// The seed-derivation source tag for this source.
    const TAG: &'static [u8] = b"deterministic";
}

impl RandomnessSource for Deterministic {
    fn evidence(&self, req: &RandomnessRequest) -> RandomnessEvidence {
        let seed = derive_seed(&req.event_id(), Self::TAG, &self.context);
        let commitment = DrawStream::new(seed, req.draw_count).transcript_commitment();
        RandomnessEvidence {
            derivation_version: DERIVATION_VERSION,
            source: EvidenceKind::Deterministic {
                context: self.context,
            },
            draw_transcript_commitment: commitment,
        }
    }

    fn seed(req: &RandomnessRequest, ev: &RandomnessEvidence) -> Result<Seed, VerifyError> {
        check_version(ev)?;
        let EvidenceKind::Deterministic { context } = &ev.source else {
            return Err(VerifyError::SourceMismatch);
        };
        let seed = derive_seed(&req.event_id(), Self::TAG, context);
        check_transcript(seed, req, ev)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// CommitReveal — two-party, deterministic and testable.
// ─────────────────────────────────────────────────────────────────────────────

/// Two-party commit-reveal.
///
/// The server publishes `commit(server_reveal)` before the player's contribution
/// is bound; the seed folds both contributions with the event id. This prevents
/// either party from *unilaterally choosing* the outcome (the server is bound to
/// its committed reveal; the player cannot bias it without a matching change to
/// the server's committed value). It does **not** prevent a last-revealer
/// **selective abort** — see the crate docs.
#[derive(Clone, Debug)]
pub struct CommitReveal {
    /// The server's secret contribution (opened at reveal time).
    pub server_reveal: [u8; 32],
    /// The player's contribution.
    pub player_contribution: [u8; 32],
}

impl CommitReveal {
    /// The seed-derivation source tag for this source.
    const TAG: &'static [u8] = b"commit-reveal";

    /// The commitment the server publishes before revealing: `H(DOMAIN || reveal)`.
    pub fn commit(server_reveal: &[u8; 32]) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        absorb_len_prefixed(&mut h, DOMAIN_COMMIT);
        h.update(server_reveal);
        *h.finalize().as_bytes()
    }

    /// The source output feeding the seed: both contributions, length-prefixed.
    fn source_output(server_reveal: &[u8; 32], player_contribution: &[u8; 32]) -> [u8; 64] {
        let mut out = [0u8; 64];
        out[..32].copy_from_slice(server_reveal);
        out[32..].copy_from_slice(player_contribution);
        out
    }
}

impl RandomnessSource for CommitReveal {
    fn evidence(&self, req: &RandomnessRequest) -> RandomnessEvidence {
        let output = Self::source_output(&self.server_reveal, &self.player_contribution);
        let seed = derive_seed(&req.event_id(), Self::TAG, &output);
        let commitment = DrawStream::new(seed, req.draw_count).transcript_commitment();
        RandomnessEvidence {
            derivation_version: DERIVATION_VERSION,
            source: EvidenceKind::CommitReveal {
                server_commitment: Self::commit(&self.server_reveal),
                server_reveal: self.server_reveal,
                player_contribution: self.player_contribution,
            },
            draw_transcript_commitment: commitment,
        }
    }

    fn seed(req: &RandomnessRequest, ev: &RandomnessEvidence) -> Result<Seed, VerifyError> {
        check_version(ev)?;
        let EvidenceKind::CommitReveal {
            server_commitment,
            server_reveal,
            player_contribution,
        } = &ev.source
        else {
            return Err(VerifyError::SourceMismatch);
        };
        // The reveal must open the commitment: a tampered reveal is rejected here.
        if Self::commit(server_reveal) != *server_commitment {
            return Err(VerifyError::CommitmentMismatch);
        }
        let output = Self::source_output(server_reveal, player_contribution);
        let seed = derive_seed(&req.event_id(), Self::TAG, &output);
        check_transcript(seed, req, ev)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// MockBeacon — a stand-in for a public randomness beacon (no signature check).
// ─────────────────────────────────────────────────────────────────────────────

/// A mock public-beacon source. Folds a caller-supplied beacon `output` into the
/// seed and round-trips through [`EvidenceKind::Beacon`]. It does **not** verify
/// the beacon's signature/finality — that needs the real beacon infra — so it is
/// suitable for tests and wiring, not for a non-grindability guarantee.
#[derive(Clone, Debug)]
pub struct MockBeacon {
    /// Beacon identity.
    pub beacon_id: Vec<u8>,
    /// The future round fixed by the request acknowledgement.
    pub round: u64,
    /// The beacon output for that round.
    pub output: [u8; 32],
}

impl MockBeacon {
    /// The seed-derivation source tag for this source.
    const TAG: &'static [u8] = b"beacon";

    fn source_output(beacon_id: &[u8], round: u64, output: &[u8; 32]) -> Vec<u8> {
        let mut out = Vec::with_capacity(beacon_id.len() + 8 + 32);
        out.extend_from_slice(&(beacon_id.len() as u64).to_le_bytes());
        out.extend_from_slice(beacon_id);
        out.extend_from_slice(&round.to_le_bytes());
        out.extend_from_slice(output);
        out
    }
}

impl RandomnessSource for MockBeacon {
    fn evidence(&self, req: &RandomnessRequest) -> RandomnessEvidence {
        let output = Self::source_output(&self.beacon_id, self.round, &self.output);
        let seed = derive_seed(&req.event_id(), Self::TAG, &output);
        let commitment = DrawStream::new(seed, req.draw_count).transcript_commitment();
        RandomnessEvidence {
            derivation_version: DERIVATION_VERSION,
            source: EvidenceKind::Beacon {
                beacon_id: self.beacon_id.clone(),
                round: self.round,
                output: self.output,
            },
            draw_transcript_commitment: commitment,
        }
    }

    fn seed(req: &RandomnessRequest, ev: &RandomnessEvidence) -> Result<Seed, VerifyError> {
        check_version(ev)?;
        let EvidenceKind::Beacon {
            beacon_id,
            round,
            output,
        } = &ev.source
        else {
            return Err(VerifyError::SourceMismatch);
        };
        let src = Self::source_output(beacon_id, *round, output);
        let seed = derive_seed(&req.event_id(), Self::TAG, &src);
        check_transcript(seed, req, ev)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// ServerVrf — the real post-quantum LB-VRF source (`pqvrf`, Esgin et al. Set I).
// ─────────────────────────────────────────────────────────────────────────────

/// Domain tag for the per-event LB-VRF key commitment (the request-binding model).
pub const DOMAIN_LB_VRF_KEY_COMMITMENT: &[u8] = b"dregg-dice/lb-vrf/key-commitment/v1";

/// A producer-side error from [`ServerVrf::try_evidence`].
///
/// The trait's infallible [`RandomnessSource::evidence`] panics on these; real
/// producers call [`ServerVrf::try_evidence`] to handle them. Both are load-bearing
/// for the **one-time** discipline: Set I permits exactly one evaluation per key.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VrfEvalError {
    /// This `ServerVrf`'s one-time key was already consumed by a prior evaluation.
    /// Set I is one-time; mint a fresh [`ServerVrf`] (a new key epoch) per event.
    KeyConsumed,
    /// The underlying `pqvrf::eval` failed (its one-time budget, or a sampling abort).
    Backend(pqvrf::EvalError),
}

impl core::fmt::Display for VrfEvalError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::KeyConsumed => f.write_str(
                "LB-VRF key already consumed — Set I is one-time; mint a fresh ServerVrf per event",
            ),
            Self::Backend(e) => write!(f, "LB-VRF eval failed: {e}"),
        }
    }
}

impl std::error::Error for VrfEvalError {}

/// A server randomness source backed by the one-time post-quantum **LB-VRF**
/// (`pqvrf`, Esgin et al. FC 2021, Set I).
///
/// # What it wraps
///
/// The VRF input is the draw's [`EventId`] bytes (which already bind
/// game/seq/pre-state/action/purpose/draw-count). Producing evidence runs one
/// `pqvrf::eval` over that input, yielding `(output, proof)`; the recorded
/// [`EvidenceKind::LbVrf`] carries the public key, output, and proof. The pure
/// [`RandomnessSource::seed`] verifier re-runs `pqvrf::verify(&pk, event_id,
/// &output, &proof)` and, only on success, derives the [`Seed`] over the
/// **verified** output via the same domain-separated [`derive_seed`] every source
/// ends with. A forged output or proof — one the LB-VRF secret never produced for
/// this input — fails `pqvrf::verify`; its uniqueness reduces to Module-SIS. That
/// is escape-hatch #4 (one-output-per-input) closed with a lattice primitive, in
/// place of the rejected classical ECVRF.
///
/// # The one-time key model (per-event key committed in the request)
///
/// Set I permits **one** evaluation per key ([`pqvrf::MAX_EVALUATIONS`] = 1), so
/// each random event needs its own key epoch. This crate uses the simpler of the
/// two correct models: a **per-event key committed in the request**. The event's
/// public key (or its [`ServerVrf::key_commitment`]) is bound into the request
/// *before the draw* — the request commitment is stored first — so a verifier
/// checks the proof under the key the request committed to and the server cannot
/// swap in a fresh, favourable key after seeing the outcome. It is simpler than a
/// genesis-committed key-chain (which needs a Merkle root + per-epoch membership
/// proof, indexed by `seq`) and needs no extra committed state: the existing
/// request/[`EventId`] binding carries the key. `ServerVrf` enforces the one-eval
/// rule two ways — `pqvrf::SecretKey`'s own budget counter, and by *burning* its
/// key on first use ([`ServerVrf::try_evidence`] returns [`VrfEvalError::KeyConsumed`]
/// on a second call).
///
/// **Assurance.** Output pseudorandomness rests on MLWE (assumed; `pqvrf`'s
/// undischarged `Pseudorandom` obligation). Uniqueness (the one-output tooth this
/// source uses) reduces to Module-SIS. Genesis key binding, a real delayed beacon,
/// and timeout-no-reroll (hatches #1/#2/#5) remain the [`Hybrid`] follow-up.
pub struct ServerVrf {
    /// The one-time LB-VRF secret key for this event epoch — consumed on first eval.
    key: RefCell<Option<pqvrf::SecretKey>>,
    /// The corresponding public key (the verification anchor recorded in evidence).
    public_key: pqvrf::PublicKey,
}

impl core::fmt::Debug for ServerVrf {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ServerVrf")
            .field("public_key", &self.public_key)
            .field("key_consumed", &self.key.borrow().is_none())
            .finish()
    }
}

impl ServerVrf {
    /// The seed-derivation source tag for this source.
    const TAG: &'static [u8] = b"lb-vrf";

    /// Mint a fresh one-time key epoch from a 32-byte key seed (via `pqvrf::keygen`).
    ///
    /// Each event MUST use a distinct `ServerVrf` (a distinct key seed): Set I is
    /// one-time, and evaluating a key on a second input would break the scheme.
    pub fn from_key_seed(seed: &[u8; 32]) -> ServerVrf {
        let (public_key, secret_key) = pqvrf::keygen(seed);
        ServerVrf {
            key: RefCell::new(Some(secret_key)),
            public_key,
        }
    }

    /// This epoch's LB-VRF public key.
    pub fn public_key(&self) -> &pqvrf::PublicKey {
        &self.public_key
    }

    /// This epoch's LB-VRF public key in canonical bytes (as recorded in evidence).
    pub fn public_key_bytes(&self) -> Vec<u8> {
        encode_public_key(&self.public_key)
    }

    /// Whether this source's one-time key has already been consumed.
    pub fn key_consumed(&self) -> bool {
        self.key.borrow().is_none()
    }

    /// The domain-separated commitment to a public key, `H(DOMAIN || pk_bytes)` — the
    /// value a request binds (e.g. into `game_binding`) to pin THIS key epoch before
    /// the draw. A verifier that recomputes it from the evidence's public key and
    /// compares it to the request's committed value detects a swapped key.
    pub fn key_commitment(public_key_bytes: &[u8]) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        absorb_len_prefixed(&mut h, DOMAIN_LB_VRF_KEY_COMMITMENT);
        absorb_len_prefixed(&mut h, public_key_bytes);
        *h.finalize().as_bytes()
    }

    /// Produce LB-VRF evidence for `req`, consuming this epoch's one-time key.
    ///
    /// Runs a single `pqvrf::eval` with VRF input = the request's [`EventId`] bytes,
    /// then derives the seed over the verified output and records the draw transcript.
    /// A second call returns [`VrfEvalError::KeyConsumed`] — the one-time guarantee.
    pub fn try_evidence(
        &self,
        req: &RandomnessRequest,
    ) -> Result<RandomnessEvidence, VrfEvalError> {
        let mut slot = self.key.borrow_mut();
        let secret_key = slot.as_mut().ok_or(VrfEvalError::KeyConsumed)?;
        let event_id = req.event_id();
        let (output, proof) =
            pqvrf::eval(secret_key, event_id.as_bytes()).map_err(VrfEvalError::Backend)?;
        // Burn the key: Set I is one-time. (pqvrf's own budget counter also refuses a
        // second eval; this additionally drops the secret and yields a crisp error.)
        *slot = None;

        let output_bytes = encode_output(&output);
        let seed = derive_seed(&event_id, Self::TAG, &output_bytes);
        let commitment = DrawStream::new(seed, req.draw_count).transcript_commitment();
        Ok(RandomnessEvidence {
            derivation_version: DERIVATION_VERSION,
            source: EvidenceKind::LbVrf {
                public_key: encode_public_key(&self.public_key),
                output: output_bytes,
                proof: encode_proof(&proof),
            },
            draw_transcript_commitment: commitment,
        })
    }
}

impl RandomnessSource for ServerVrf {
    fn evidence(&self, req: &RandomnessRequest) -> RandomnessEvidence {
        self.try_evidence(req).expect(
            "ServerVrf::evidence: the one-time LB-VRF key is exhausted or eval aborted — \
             use ServerVrf::try_evidence to handle one-time exhaustion",
        )
    }

    fn seed(req: &RandomnessRequest, ev: &RandomnessEvidence) -> Result<Seed, VerifyError> {
        check_version(ev)?;
        let EvidenceKind::LbVrf {
            public_key,
            output,
            proof,
        } = &ev.source
        else {
            return Err(VerifyError::SourceMismatch);
        };
        // Decode the untrusted byte fields into pqvrf structures (canonical lengths).
        let public_key = decode_public_key(public_key)?;
        let output = decode_output(output)?;
        let proof = decode_proof(proof)?;
        // THE ONE-OUTPUT TOOTH: re-run pqvrf::verify under the recorded key and the
        // request's event id. A forged output/proof (not the LB-VRF value for this
        // input) is rejected here — uniqueness reduces to Module-SIS.
        let event_id = req.event_id();
        if !pqvrf::verify(&public_key, event_id.as_bytes(), &output, &proof) {
            return Err(VerifyError::VrfProofInvalid);
        }
        // Only now — over the VERIFIED output — derive the seed and check the transcript.
        let seed = derive_seed(&event_id, Self::TAG, &encode_output(&output));
        check_transcript(seed, req, ev)
    }
}

// ── LB-VRF ⇄ bytes codec. pqvrf ships no wire format; these are canonical
//    little-endian encodings of its public structs, with strict length checks on
//    decode so a malformed evidence field is rejected before the proof check. ──

fn encode_public_key(pk: &pqvrf::PublicKey) -> Vec<u8> {
    let mut out = Vec::with_capacity(pqvrf::MSIS_RANK * pqvrf::DEGREE * 4);
    for poly in &pk.t {
        for &c in &poly.coefficients {
            out.extend_from_slice(&c.to_le_bytes());
        }
    }
    out
}

fn decode_public_key(bytes: &[u8]) -> Result<pqvrf::PublicKey, VerifyError> {
    let expected = pqvrf::MSIS_RANK * pqvrf::DEGREE * 4;
    if bytes.len() != expected {
        return Err(VerifyError::MalformedVrfEvidence(
            "LB-VRF public key has the wrong byte length",
        ));
    }
    let mut it = bytes.chunks_exact(4);
    let t = core::array::from_fn(|_| {
        let coefficients = core::array::from_fn(|_| {
            let c = it.next().expect("length checked above");
            u32::from_le_bytes([c[0], c[1], c[2], c[3]])
        });
        pqvrf::PublicPolynomial { coefficients }
    });
    Ok(pqvrf::PublicKey { t })
}

fn encode_output(output: &pqvrf::Output) -> Vec<u8> {
    let mut out = Vec::with_capacity(pqvrf::OUTPUT_DEGREE * 4);
    for &c in &output.coefficients {
        out.extend_from_slice(&c.to_le_bytes());
    }
    out
}

fn decode_output(bytes: &[u8]) -> Result<pqvrf::Output, VerifyError> {
    if bytes.len() != pqvrf::OUTPUT_DEGREE * 4 {
        return Err(VerifyError::MalformedVrfEvidence(
            "LB-VRF output has the wrong byte length",
        ));
    }
    let mut it = bytes.chunks_exact(4);
    let coefficients = core::array::from_fn(|_| {
        let c = it.next().expect("length checked above");
        u32::from_le_bytes([c[0], c[1], c[2], c[3]])
    });
    Ok(pqvrf::Output { coefficients })
}

fn encode_proof(proof: &pqvrf::Proof) -> Vec<u8> {
    let mut out = Vec::with_capacity(pqvrf::SECRET_WIDTH * pqvrf::DEGREE * 4 + pqvrf::DEGREE);
    for poly in &proof.response {
        for &c in &poly.coefficients {
            out.extend_from_slice(&c.to_le_bytes());
        }
    }
    for &c in &proof.challenge.coefficients {
        out.extend_from_slice(&c.to_le_bytes());
    }
    out
}

fn decode_proof(bytes: &[u8]) -> Result<pqvrf::Proof, VerifyError> {
    let response_len = pqvrf::SECRET_WIDTH * pqvrf::DEGREE * 4;
    let expected = response_len + pqvrf::DEGREE;
    if bytes.len() != expected {
        return Err(VerifyError::MalformedVrfEvidence(
            "LB-VRF proof has the wrong byte length",
        ));
    }
    let (response_bytes, challenge_bytes) = bytes.split_at(response_len);
    let mut it = response_bytes.chunks_exact(4);
    let response = core::array::from_fn(|_| {
        let coefficients = core::array::from_fn(|_| {
            let c = it.next().expect("length checked above");
            i32::from_le_bytes([c[0], c[1], c[2], c[3]])
        });
        pqvrf::ResponsePolynomial { coefficients }
    });
    let challenge = pqvrf::ChallengePolynomial {
        coefficients: core::array::from_fn(|i| challenge_bytes[i] as i8),
    };
    Ok(pqvrf::Proof {
        response,
        challenge,
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// Beacon — a pluggable public randomness beacon behind a pure, source-free verifier.
// ─────────────────────────────────────────────────────────────────────────────

/// A public randomness beacon.
///
/// The producer half ([`Beacon::round_output`]) may know operator secrets; the
/// verifier half is the **pure, source-free** [`verify_beacon_round`], which
/// checks a round output against the genesis-pinned [`BeaconParams`] with only
/// public data — so a light client verifies a beacon it never instantiated.
pub trait Beacon {
    /// The genesis-pinned parameters (committed into the hybrid `game_binding`).
    fn params(&self) -> BeaconParams;

    /// The beacon's output for a matured `round` (operator side).
    fn round_output(&self, round: u64) -> [u8; 32];
}

/// One forward step of a hash-chain beacon: `H(DOMAIN_BEACON_CHAIN || v)`.
fn beacon_step(v: &[u8; 32]) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    absorb_len_prefixed(&mut h, DOMAIN_BEACON_CHAIN);
    h.update(v);
    *h.finalize().as_bytes()
}

/// `H^steps(root)` under [`beacon_step`].
fn beacon_hash_n(root: &[u8; 32], steps: u64) -> [u8; 32] {
    let mut v = *root;
    for _ in 0..steps {
        v = beacon_step(&v);
    }
    v
}

/// A forward-secure hash-chain beacon (the shipped, testable beacon model).
///
/// The operator picks a secret `root` and a chain `length`, publishing
/// `anchor = H^length(root)` at genesis. Round `R` (for `1 <= R <= length`)
/// reveals `H^(length-R)(root)`; a verifier accepts iff `H^R(output) == anchor`.
/// Preimage resistance makes a future round unpredictable at commit time, and the
/// anchor is genesis-pinned, so the operator cannot reschedule to a favourable
/// round.
///
/// **Trust level (honest):** this is a single-operator, forward-secure beacon, not
/// a threshold construction. It trusts the operator not to have chosen a `root`
/// whose chain lands a favourable value at the target round (it cannot do so
/// *after* seeing the event, since the anchor is committed first, but a
/// precomputing operator colluding on `root` is not excluded — that is what a
/// threshold [`BeaconKind::Drand`] beacon buys, and wiring live drand is the
/// remaining gap for escape hatch #2).
#[derive(Clone, Debug)]
pub struct HashChainBeacon {
    root: [u8; 32],
    length: u64,
    beacon_id: Vec<u8>,
    schedule: crate::request::BeaconSchedule,
}

impl HashChainBeacon {
    /// Build a hash-chain beacon from a secret `root`, a chain `length`, an
    /// identity, and the round schedule.
    pub fn new(
        root: [u8; 32],
        length: u64,
        beacon_id: impl Into<Vec<u8>>,
        schedule: crate::request::BeaconSchedule,
    ) -> HashChainBeacon {
        HashChainBeacon {
            root,
            length,
            beacon_id: beacon_id.into(),
            schedule,
        }
    }

    /// The genesis-pinned anchor `H^length(root)`.
    pub fn anchor(&self) -> [u8; 32] {
        beacon_hash_n(&self.root, self.length)
    }
}

impl Beacon for HashChainBeacon {
    fn params(&self) -> BeaconParams {
        BeaconParams {
            beacon_id: self.beacon_id.clone(),
            kind: BeaconKind::HashChain {
                anchor: self.anchor(),
                length: self.length,
            },
            schedule: self.schedule.clone(),
        }
    }

    fn round_output(&self, round: u64) -> [u8; 32] {
        // o_R = H^(length-R)(root), so H^R(o_R) = H^length(root) = anchor.
        assert!(
            round >= 1 && round <= self.length,
            "hash-chain round {round} out of range 1..={}",
            self.length
        );
        beacon_hash_n(&self.root, self.length - round)
    }
}

/// Pure, source-free verification of a beacon round output against genesis-pinned
/// parameters. A light client calls this with only public data.
///
/// - [`BeaconKind::HashChain`]: accepts iff `1 <= round <= length` and
///   `H^round(output) == anchor`.
/// - [`BeaconKind::Drand`]: fails closed — real drand round verification is a BLS
///   pairing check against the pinned group key, the remaining gap for hatch #2.
pub fn verify_beacon_round(
    params: &BeaconParams,
    round: u64,
    output: &[u8; 32],
) -> Result<(), VerifyError> {
    match &params.kind {
        BeaconKind::HashChain { anchor, length } => {
            if round == 0 || round > *length {
                return Err(VerifyError::BeaconVerifyFailed);
            }
            if beacon_hash_n(output, round) != *anchor {
                return Err(VerifyError::BeaconVerifyFailed);
            }
            Ok(())
        }
        BeaconKind::Drand { .. } => Err(VerifyError::BackendUnavailable(
            "real drand-BLS round verification (pairing check vs the pinned group key) \
             is the remaining gap for escape hatch #2",
        )),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// KeyChain — a genesis-committed chain of one-time LB-VRF keys, epoch = seq (#1).
// ─────────────────────────────────────────────────────────────────────────────

/// A key-chain Merkle leaf: `H(DOMAIN_KEYCHAIN_LEAF || pk_bytes)`.
fn keychain_leaf(pk_bytes: &[u8]) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    absorb_len_prefixed(&mut h, DOMAIN_KEYCHAIN_LEAF);
    absorb_len_prefixed(&mut h, pk_bytes);
    *h.finalize().as_bytes()
}

/// A key-chain Merkle interior node: `H(DOMAIN_KEYCHAIN_NODE || left || right)`.
fn keychain_node(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    absorb_len_prefixed(&mut h, DOMAIN_KEYCHAIN_NODE);
    h.update(left);
    h.update(right);
    *h.finalize().as_bytes()
}

/// Build the full Merkle layer stack from a power-of-two leaf vector (`layers[0]`
/// is the leaves; the last layer is the single root).
fn build_layers(leaves: Vec<[u8; 32]>) -> Vec<Vec<[u8; 32]>> {
    let mut layers = vec![leaves];
    while layers.last().expect("non-empty").len() > 1 {
        let cur = layers.last().expect("non-empty");
        let mut next = Vec::with_capacity(cur.len() / 2);
        for pair in cur.chunks(2) {
            next.push(keychain_node(&pair[0], &pair[1]));
        }
        layers.push(next);
    }
    layers
}

/// The Merkle membership path (sibling per level) for `index`.
fn merkle_proof(layers: &[Vec<[u8; 32]>], index: usize) -> Vec<[u8; 32]> {
    let mut proof = Vec::with_capacity(layers.len().saturating_sub(1));
    let mut idx = index;
    for level in &layers[..layers.len().saturating_sub(1)] {
        proof.push(level[idx ^ 1]);
        idx >>= 1;
    }
    proof
}

/// Pure, source-free verification that `pk_bytes` is the LB-VRF public key committed
/// at leaf `epoch` of a genesis key-chain `root`. A light client calls this with
/// only public data. Rejects a key from a different (or fresh) epoch (hatch #1).
pub fn verify_epoch_membership(
    root: &[u8; 32],
    epoch: u64,
    pk_bytes: &[u8],
    proof: &[[u8; 32]],
) -> bool {
    let mut node = keychain_leaf(pk_bytes);
    let mut idx = epoch;
    for sib in proof {
        node = if idx & 1 == 0 {
            keychain_node(&node, sib)
        } else {
            keychain_node(sib, &node)
        };
        idx >>= 1;
    }
    // `idx == 0` rejects an epoch index beyond the committed tree (a too-large seq).
    idx == 0 && node == *root
}

/// A **genesis-committed chain of one-time LB-VRF keys**, one per epoch, indexed by
/// the transition `seq` (epoch = `seq`).
///
/// Set I LB-VRF keys are one-time ([`pqvrf::MAX_EVALUATIONS`] = 1), so each random
/// event needs its own key epoch. Rather than mint a *fresh* key at turn time
/// (which the server could choose favourably after seeing the outcome — escape
/// hatch #1), a `KeyChain` derives all epoch keys deterministically from a master
/// seed and commits their public keys in a **Merkle root** published at genesis.
/// The request pins that root (via [`Hybrid::genesis_binding`]) and the transition
/// `seq` selects the leaf; the verifier checks the eval key's membership at leaf
/// `seq` ([`verify_epoch_membership`]). A server that swaps in any other key fails,
/// because that key is not the committed leaf for this `seq`.
pub struct KeyChain {
    /// Per-epoch one-time secret keys, interior-mutable so a `&self` producer can
    /// burn a key on first use (Set I is one-time).
    secrets: Vec<RefCell<Option<pqvrf::SecretKey>>>,
    /// Per-epoch public keys (the verification anchors, committed as leaves).
    public_keys: Vec<pqvrf::PublicKey>,
    /// The Merkle layer stack over the (pow2-padded) public-key leaves.
    layers: Vec<Vec<[u8; 32]>>,
    /// Number of real epochs (leaves before padding).
    num_epochs: usize,
}

impl core::fmt::Debug for KeyChain {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("KeyChain")
            .field("num_epochs", &self.num_epochs)
            .field("root", &hex4(&self.root()))
            .finish()
    }
}

fn hex4(b: &[u8; 32]) -> String {
    let mut s = String::new();
    for x in &b[..4] {
        s.push_str(&format!("{x:02x}"));
    }
    s.push('…');
    s
}

impl KeyChain {
    /// Deterministically derive a key-chain of `num_epochs` one-time LB-VRF keys
    /// from a 32-byte master seed. Epoch `e`'s key seed is
    /// `H(DOMAIN_KEYCHAIN_EPOCH_SEED || master || e)`.
    ///
    /// Panics if `num_epochs == 0`.
    pub fn from_master_seed(master: &[u8; 32], num_epochs: usize) -> KeyChain {
        assert!(num_epochs >= 1, "a key-chain needs at least one epoch");
        let mut secrets = Vec::with_capacity(num_epochs);
        let mut public_keys = Vec::with_capacity(num_epochs);
        let mut leaves = Vec::with_capacity(num_epochs);
        for epoch in 0..num_epochs {
            let mut h = blake3::Hasher::new();
            absorb_len_prefixed(&mut h, DOMAIN_KEYCHAIN_EPOCH_SEED);
            h.update(master);
            h.update(&(epoch as u64).to_le_bytes());
            let seed = *h.finalize().as_bytes();
            let (pk, sk) = pqvrf::keygen(&seed);
            leaves.push(keychain_leaf(&encode_public_key(&pk)));
            public_keys.push(pk);
            secrets.push(RefCell::new(Some(sk)));
        }
        // Pad to a power of two with a domain-separated empty leaf (a real key's
        // encoded bytes are never empty, so the pad never collides with a leaf).
        let padded = num_epochs.next_power_of_two();
        let empty = keychain_leaf(&[]);
        let mut padded_leaves = leaves;
        padded_leaves.resize(padded, empty);
        let layers = build_layers(padded_leaves);
        KeyChain {
            secrets,
            public_keys,
            layers,
            num_epochs,
        }
    }

    /// The genesis-committed key-chain Merkle root.
    pub fn root(&self) -> [u8; 32] {
        self.layers.last().expect("non-empty layers")[0]
    }

    /// Number of real (non-padded) epochs.
    pub fn num_epochs(&self) -> usize {
        self.num_epochs
    }

    /// Epoch `epoch`'s LB-VRF public key in canonical bytes (the committed leaf).
    pub fn public_key_bytes(&self, epoch: usize) -> Vec<u8> {
        encode_public_key(&self.public_keys[epoch])
    }

    /// The Merkle membership path for epoch `epoch`.
    pub fn epoch_proof(&self, epoch: usize) -> Vec<[u8; 32]> {
        merkle_proof(&self.layers, epoch)
    }

    /// Evaluate epoch `epoch`'s one-time key over `event_id`, burning the key.
    ///
    /// A second call for the same epoch returns [`VrfEvalError::KeyConsumed`] (Set I
    /// is one-time). Epochs are independent, so distinct events (distinct `seq`) use
    /// distinct keys.
    pub fn eval_epoch(
        &self,
        epoch: usize,
        event_id: &EventId,
    ) -> Result<(pqvrf::Output, pqvrf::Proof), VrfEvalError> {
        let mut slot = self.secrets[epoch].borrow_mut();
        let sk = slot.as_mut().ok_or(VrfEvalError::KeyConsumed)?;
        let (output, proof) =
            pqvrf::eval(sk, event_id.as_bytes()).map_err(VrfEvalError::Backend)?;
        *slot = None; // burn: Set I is one-time.
        Ok((output, proof))
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Hybrid — genesis-committed LB-VRF key-chain ∧ delayed schedule-bound beacon,
// with timeout finalization. Closes hatches #1, #2 (schedule layer), #4, #5.
// ─────────────────────────────────────────────────────────────────────────────

/// Whether a [`Hybrid`] producer emits the normal (VRF-provided) evidence or the
/// timeout (`ServerMissed`) evidence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FinalizeMode {
    /// Normal path: the server publishes its LB-VRF proof for this epoch.
    Normal,
    /// Timeout path: model a server that withheld its LB-VRF proof past the deadline;
    /// any finalizer produces the beacon-only evidence.
    SimulateServerMissed,
}

/// The recommended endpoint: a **genesis-committed LB-VRF key-chain** mixed with a
/// **delayed, schedule-bound public beacon**, with timeout finalization so
/// withholding cannot reroll.
///
/// The seed mixes two independent contributions, domain-separated and
/// length-prefixed so changing **either** changes the seed:
/// - the epoch (`= seq`) LB-VRF output over the [`EventId`] (a one-time key
///   committed in the genesis key-chain root — the server has no freedom in it once
///   the action is bound, and cannot swap the key: hatches #1, #4), and
/// - a **future** beacon round output whose round is fixed by the schedule from the
///   receipt `seq` (the server cannot pick a favourable already-published round:
///   hatch #2 at the schedule layer).
///
/// **Timeout finalization (hatch #5).** If the server withholds its LB-VRF proof
/// past the deadline, anyone finalizes from the beacon alone with a recorded
/// [`Finalization::ServerMissed`] marker. The resulting seed is a pure function of
/// the (unpredictable-at-commit) beacon output and the event id — it is
/// **determined, not chooseable**, and there is exactly one such seed, so
/// withholding yields no reroll and no alternative outcome; the fault is visible in
/// the evidence. Because the beacon round matures *after* the reveal deadline, the
/// server's decision to withhold is made without knowing the beacon output, so a
/// selective abort buys nothing. (The reveal-deadline-before-beacon-maturity
/// ordering is a scheduling obligation of the receipt layer; this crate encodes the
/// round as a future, schedule-bound round and records the fault.)
///
/// **Assurance.** LB-VRF output pseudorandomness rests on MLWE (assumed; `pqvrf`'s
/// undischarged `Pseudorandom` obligation); uniqueness (one output per input)
/// reduces to Module-SIS. The shipped beacon is a single-operator forward-secure
/// hash chain; a real threshold **drand-BLS** beacon ([`BeaconKind::Drand`]) is the
/// remaining production gap for hatch #2.
pub struct Hybrid {
    key_chain: KeyChain,
    beacon: Box<dyn Beacon>,
    mode: FinalizeMode,
}

impl Hybrid {
    /// The seed-derivation source tag.
    const TAG: &'static [u8] = b"hybrid";

    /// Build a hybrid producer over a genesis key-chain and a beacon (normal path).
    pub fn new(key_chain: KeyChain, beacon: Box<dyn Beacon>) -> Hybrid {
        Hybrid {
            key_chain,
            beacon,
            mode: FinalizeMode::Normal,
        }
    }

    /// Set the finalization mode (use [`FinalizeMode::SimulateServerMissed`] to model
    /// the timeout path a would-be finalizer produces).
    pub fn with_mode(mut self, mode: FinalizeMode) -> Hybrid {
        self.mode = mode;
        self
    }

    /// The genesis binding a hybrid game commits so a verifier can pin the LB-VRF
    /// key-chain root, the beacon parameters, and the round schedule together:
    /// `H(DOMAIN_HYBRID_GENESIS || key_chain_root || beacon_params)`. Set a request's
    /// `game_binding` to this. A per-turn key-chain swap (hatch #1), a beacon swap, or
    /// a schedule change (hatch #2) all fail the verifier's re-derivation.
    pub fn genesis_binding(key_chain_root: &[u8; 32], beacon: &BeaconParams) -> Vec<u8> {
        let mut h = blake3::Hasher::new();
        absorb_len_prefixed(&mut h, DOMAIN_HYBRID_GENESIS);
        h.update(key_chain_root);
        absorb_beacon_params(&mut h, beacon);
        h.finalize().as_bytes().to_vec()
    }
}

/// Absorb beacon params injectively into a hasher (for the genesis binding).
fn absorb_beacon_params(h: &mut blake3::Hasher, p: &BeaconParams) {
    absorb_len_prefixed(h, &p.beacon_id);
    match &p.kind {
        BeaconKind::HashChain { anchor, length } => {
            h.update(&[0x01]);
            h.update(anchor);
            h.update(&length.to_le_bytes());
        }
        BeaconKind::Drand {
            group_public_key,
            scheme,
        } => {
            h.update(&[0x02]);
            absorb_len_prefixed(h, group_public_key);
            absorb_len_prefixed(h, scheme.as_bytes());
        }
    }
    h.update(&p.schedule.base_round.to_le_bytes());
    h.update(&p.schedule.stride.to_le_bytes());
}

/// The source output fed to the seed for a hybrid finalization: a domain tag, a
/// marker byte, the (possibly empty) VRF output, and the beacon output — each
/// length-prefixed so the encoding is injective and the two finalization paths are
/// domain-separated (a `ServerProvided` seed can never equal a `ServerMissed` one).
fn hybrid_source_output(
    finalization: Finalization,
    vrf_output: &[u8],
    beacon_output: &[u8; 32],
) -> Vec<u8> {
    let marker: u8 = match finalization {
        Finalization::ServerProvided => 0x01,
        Finalization::ServerMissed => 0x00,
    };
    let mut out = Vec::with_capacity(DOMAIN_HYBRID_MIX.len() + 1 + 8 + vrf_output.len() + 8 + 32);
    out.extend_from_slice(DOMAIN_HYBRID_MIX);
    out.push(marker);
    out.extend_from_slice(&(vrf_output.len() as u64).to_le_bytes());
    out.extend_from_slice(vrf_output);
    out.extend_from_slice(&32u64.to_le_bytes());
    out.extend_from_slice(beacon_output);
    out
}

impl RandomnessSource for Hybrid {
    fn evidence(&self, req: &RandomnessRequest) -> RandomnessEvidence {
        let event_id = req.event_id();
        let params = self.beacon.params();
        let round = params.schedule.expected_round(req.seq);
        let beacon_output = self.beacon.round_output(round);
        let epoch = req.seq as usize;
        let key_chain_root = self.key_chain.root();

        let (finalization, vrf_public_key, vrf_output, vrf_proof, epoch_proof) = match self.mode {
            FinalizeMode::Normal => {
                let (output, proof) = self.key_chain.eval_epoch(epoch, &event_id).expect(
                    "Hybrid::evidence: the epoch's one-time LB-VRF key is exhausted or eval aborted",
                );
                (
                    Finalization::ServerProvided,
                    self.key_chain.public_key_bytes(epoch),
                    encode_output(&output),
                    encode_proof(&proof),
                    self.key_chain.epoch_proof(epoch),
                )
            }
            FinalizeMode::SimulateServerMissed => (
                Finalization::ServerMissed,
                Vec::new(),
                Vec::new(),
                Vec::new(),
                Vec::new(),
            ),
        };

        let so = hybrid_source_output(finalization, &vrf_output, &beacon_output);
        let seed = derive_seed(&event_id, Self::TAG, &so);
        let commitment = DrawStream::new(seed, req.draw_count).transcript_commitment();
        RandomnessEvidence {
            derivation_version: DERIVATION_VERSION,
            source: EvidenceKind::Hybrid {
                finalization,
                key_chain_root,
                vrf_public_key,
                vrf_output,
                vrf_proof,
                epoch_proof,
                beacon: BeaconEvidence {
                    params,
                    round,
                    output: beacon_output,
                },
            },
            draw_transcript_commitment: commitment,
        }
    }

    fn seed(req: &RandomnessRequest, ev: &RandomnessEvidence) -> Result<Seed, VerifyError> {
        check_version(ev)?;
        let EvidenceKind::Hybrid {
            finalization,
            key_chain_root,
            vrf_public_key,
            vrf_output,
            vrf_proof,
            epoch_proof,
            beacon,
        } = &ev.source
        else {
            return Err(VerifyError::SourceMismatch);
        };

        // Hatches #1 + #2: the key-chain root, beacon params, and schedule must all
        // reproduce the genesis binding fixed in the request.
        if Hybrid::genesis_binding(key_chain_root, &beacon.params) != req.game_binding {
            return Err(VerifyError::GenesisBindingMismatch);
        }

        // Hatch #2 (schedule layer): the round is the schedule-bound one for this
        // seq — no picking a favourable already-published round.
        if beacon.round != beacon.params.schedule.expected_round(req.seq) {
            return Err(VerifyError::BeaconRoundMismatch);
        }
        // The beacon output verifies against the pinned params (a wrong or
        // rescheduled output is rejected). Checked independently of the round
        // binding above, so a rescheduled-but-chain-valid output still fails there.
        verify_beacon_round(&beacon.params, beacon.round, &beacon.output)?;

        let event_id = req.event_id();
        let seed = match finalization {
            Finalization::ServerProvided => {
                // Hatch #1: the eval key must be the genesis-committed key for this
                // epoch (= seq). A swapped or fresh key fails Merkle membership.
                if !verify_epoch_membership(key_chain_root, req.seq, vrf_public_key, epoch_proof) {
                    return Err(VerifyError::EpochKeyMismatch);
                }
                // Hatch #4: the LB-VRF output/proof must verify under that key (one
                // output per (key, input); a forgery reduces to Module-SIS).
                let pk = decode_public_key(vrf_public_key)?;
                let output = decode_output(vrf_output)?;
                let proof = decode_proof(vrf_proof)?;
                if !pqvrf::verify(&pk, event_id.as_bytes(), &output, &proof) {
                    return Err(VerifyError::VrfProofInvalid);
                }
                let so = hybrid_source_output(
                    Finalization::ServerProvided,
                    &encode_output(&output),
                    &beacon.output,
                );
                derive_seed(&event_id, Hybrid::TAG, &so)
            }
            Finalization::ServerMissed => {
                // Hatch #5: no VRF; the seed is determined by the beacon alone. There
                // is exactly one such seed — no reroll, no alternative — and the fault
                // is recorded in `finalization`. The VRF fields are ignored, so nothing
                // a withholding server stuffs into them can bias the outcome.
                let so = hybrid_source_output(Finalization::ServerMissed, &[], &beacon.output);
                derive_seed(&event_id, Hybrid::TAG, &so)
            }
        };
        check_transcript(seed, req, ev)
    }
}
