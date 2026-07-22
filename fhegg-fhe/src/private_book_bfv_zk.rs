//! Transferable zero-knowledge proof of the private-book/BFV same opening.
//!
//! This is the deliberately heavy, fixed-shape `N=4,K=4,n=4096` apex
//! relation.  It is separate from the ordinary fold path and must only be
//! wired by the `amm-input-binding` proof feature.
//!
//! One Bulletproof R1CS proof establishes that:
//!
//! * eight one-hot private order-kind selectors and four private quantities
//!   form the exact packed book opened by the deployed arity-16 Poseidon2
//!   private root;
//! * the same finite order choice selects the exact fhe.rs SIMD plaintext
//!   polynomial (all 128 legal rows are derived through fhe.rs's encoder,
//!   never a hand-written slot-to-coefficient approximation); and
//! * all four supplied ciphertexts satisfy public-key BFV
//!   `c0=u*pk0+e1+m, c1=u*pk1+e2` over every pinned RNS modulus, for shared
//!   coefficient vectors `u,e1,e2` in `[-32,31]`, which contains fhe-util's
//!   complete variance-10 CBD support `[-20,20]`.
//!
//! The 4096 coefficient equations are compressed only after Bulletproofs has
//! committed the complete phase-one witness.  For each RNS modulus, 128
//! independent transcript-derived Rademacher combinations are constrained in
//! phase two.  The `2^-128` claim therefore applies **only** to this randomized
//! equation compression; overall security additionally relies on Bulletproofs'
//! discrete-log/Fiat-Shamir assumptions, BLAKE3 collision resistance and XOF
//! pseudorandomness, and the deployed Poseidon2 commitment.
//!
//! # Production note
//!
//! This construction is intentionally conservative and large (roughly 445k
//! multipliers and roughly 25M linear-combination terms).  The R1CS backend is
//! the upstream `yoloproofs` experimental API and is a prototype/reference
//! backend, not a deployment-supported proving system.  Greco
//! (ePrint 2024/594) is the natural Halo2/RLWE-specialized successor, but its
//! published implementation currently realizes the secret-key circuit.  This
//! module does not relabel that code as public-key BFV: it proves the exact
//! public-key equations itself.
//! It does not replace the existing HidingFRI Dark Bazaar proof: a receipt must
//! verify both against the identical `PublicStatement`.  HidingFRI proves the
//! clearing semantics and `(p*,V*)`; this proof supplies the missing encrypted
//! input/root join.
//!
//! [`prove_private_book_bfv_native_slice_zk`] is the migration off this
//! classical relation.  Its Lean-emitted HidingFRI AIR fuses the Dark Bazaar
//! statement with one *complete* 4,096-term production BFV equation and a
//! faithful eight-lane commitment to the public-key row.  It is native-PQ and
//! uncompressed, but remains one of 98,304 exact equations; callers must not
//! treat that first slice as the complete BFV opening until the indexed family
//! is materialized.
//!
//! # Exact residual
//!
//! Verification proves existence of bounded-short encryption witnesses, not
//! exact membership in the deployed seeded sampler image, ideal entropy, seed
//! distinctness, or the exact CBD probability mass function;
//! a submitter can always choose weak randomness for its own ciphertext.  It
//! also treats the supplied collective key as the statement key: authenticated
//! DKG/key-well-formedness remains the threshold layer's job.  Finally, this is
//! explicitly **Tier 1**: it is zero knowledge to proof consumers, but the
//! present proving API receives the complete book and seeds in one process.
//! The `private_book_distributed_prover` boundary is the separate integration
//! seam required by a future Tier-0 backend; this monolithic function must not
//! be relabeled or called after reconstructing its shares at a coordinator.

use std::fmt;
use std::sync::LazyLock;
use std::time::{Duration, Instant};

use bulletproofs_r1cs::r1cs::{
    ConstraintSystem, LinearCombination, R1CSError, R1CSProof, RandomizableConstraintSystem,
    RandomizedConstraintSystem, Variable,
};
use bulletproofs_r1cs::{BulletproofGens, PedersenGens};
use curve25519_dalek::scalar::Scalar;
use dregg_circuit_prove::dark_bazaar_private::{
    self, PrivateBookWitness, PublicStatement, DIGEST_WIDTH, ORDER_COUNT, PRICE_COUNT,
    ROOT_DOMAIN_TAG, RULE_ID,
};
use dregg_circuit_prove::private_book_bfv_slice as native_slice;
use fhe_math::rq::{traits::TryConvertFrom, Poly, Representation};
use merlin::Transcript;
use rand_09::rngs::StdRng;
use rand_09::{RngCore, SeedableRng};

use crate::bfv_lean::{RnsPoly, FOLD_DEGREE, FOLD_MODULI};
use crate::bfv_ntt_gpu::{RnsNttBackend, RnsNttBatchExecution, RnsNttEngine};
#[cfg(test)]
use crate::private_book_bfv_exact::derive_exact_message_table;
use crate::private_book_bfv_exact::{
    derive_signs, negacyclic_correlation, parse_public_key, signed_dot, ExactBfvError,
    ExactBfvPublicRelation as PublicRelation, COMPRESSION_ROUNDS, MAX_ABS_BATCH_QUOTIENT,
    QUOTIENT_BITS,
};
use crate::private_book_relation::{
    private_book_relation_digest, verify_private_book_opening, PrivateBookCiphertexts,
    PrivateBookEncryptionOpening, PRIVATE_BOOK_BFV_CODEC_ID, PRIVATE_BOOK_PUBLIC_BOUND,
};
use crate::threshold::{BfvParams, CollectivePublicKey};

const PROOF_TRANSCRIPT: &[u8] = b"fhegg/private-book-bfv-bulletproof/n4k4/v1";
const PROOF_MAGIC: &[u8; 8] = b"FHPZK001";
const PROOF_VERSION: u16 = 1;
const FOLD_PLAINTEXT_MODULUS: u64 = 1_032_193;
const BFV_VARIANCE: usize = 10;
// fhe-util's variance-10 CBD consumes two 20-bit popcounts, so its true support
// is [-20, 20] (not [-10, 10]).  A six-bit shifted range is the smallest cheap
// Bulletproof gadget containing every honest coefficient.  The transferable
// relation consequently proves bounded-short [-32, 31] BFV noise; exact seeded
// sampler-image membership remains a host preflight, not an R1CS claim.
const SHORT_SHIFT: i64 = 32;
const SHORT_BITS: usize = 6;
const BP_GENS_CAPACITY: usize = 1 << 19;
const MAX_PROOF_BYTES: usize = 64 * 1024;
const POSEIDON_WIDTH: usize = 16;
const BABYBEAR_MODULUS: u32 = 2_013_265_921;
const QUANTITY_COUNT: usize = dark_bazaar_private::MAX_QTY as usize + 1;
const PRIVATE_BOOK_OPTION_COUNT: usize = 2 * PRICE_COUNT * QUANTITY_COUNT;

/// Opt-in, secret-free wall-clock attribution for the deliberately heavy
/// private-book relation. The default path performs no clock reads and emits
/// nothing. When `DREGG_PRIVATE_BOOK_BFV_TIMING=1`, each invocation prints one
/// line containing fixed phase names and elapsed times only; no statement,
/// witness, key, ciphertext, transcript, or proof bytes are logged.
const TIMING_ENV: &str = "DREGG_PRIVATE_BOOK_BFV_TIMING";

struct PhaseTimings {
    operation: &'static str,
    started: Option<Instant>,
    current_started: Option<Instant>,
    current: &'static str,
    phases: Vec<(&'static str, Duration)>,
    aggregates: Vec<(&'static str, Duration)>,
    emitted: bool,
}

impl PhaseTimings {
    fn new(operation: &'static str, first_phase: &'static str) -> Self {
        let enabled = matches!(
            std::env::var(TIMING_ENV).as_deref(),
            Ok("1" | "true" | "yes" | "on")
        );
        let now = enabled.then(Instant::now);
        Self {
            operation,
            started: now,
            current_started: now,
            current: first_phase,
            phases: Vec::new(),
            aggregates: Vec::new(),
            emitted: false,
        }
    }

    fn enabled(&self) -> bool {
        self.started.is_some()
    }

    fn next(&mut self, next_phase: &'static str) {
        let Some(previous) = self.current_started else {
            self.current = next_phase;
            return;
        };
        let now = Instant::now();
        self.phases
            .push((self.current, now.duration_since(previous)));
        self.current = next_phase;
        self.current_started = Some(now);
    }

    fn add_aggregate(&mut self, name: &'static str, duration: Duration) {
        if self.enabled() {
            self.aggregates.push((name, duration));
        }
    }

    fn finish(&mut self) {
        self.emit("ok");
    }

    fn emit(&mut self, outcome: &'static str) {
        let (Some(started), Some(previous)) = (self.started, self.current_started) else {
            return;
        };
        let now = Instant::now();
        self.phases
            .push((self.current, now.duration_since(previous)));
        let phases = self
            .phases
            .iter()
            .map(|(name, duration)| format!("{name}={:.3}ms", duration.as_secs_f64() * 1e3))
            .collect::<Vec<_>>()
            .join(",");
        let aggregates = self
            .aggregates
            .iter()
            .map(|(name, duration)| format!("{name}={:.3}ms", duration.as_secs_f64() * 1e3))
            .collect::<Vec<_>>()
            .join(",");
        eprintln!(
            "private-book-bfv-timing operation={} outcome={} total={:.3}ms phases=[{}] aggregates=[{}]",
            self.operation,
            outcome,
            now.duration_since(started).as_secs_f64() * 1e3,
            phases,
            aggregates,
        );
        self.emitted = true;
    }
}

impl Drop for PhaseTimings {
    fn drop(&mut self) {
        if !self.emitted {
            self.emit("error-or-early-return");
        }
    }
}

static BP_GENS: LazyLock<BulletproofGens> =
    LazyLock::new(|| BulletproofGens::new(BP_GENS_CAPACITY, 1));

// A deliberately loose, integer (not field) bound for one phase-two equation.
// Per modulus there are eight polynomial families.  Each contributes at most
// n*(32q + 32 + q) from u, e and c.  Each of the four exact c0 message
// polynomials has every RNS coefficient below q, so messages add at most
// 4*n*q.  After division by q:
//   8*n*(32+1+1) + 4*n = 1,130,496 < 2^21.
// QUOTIENT_BITS=24 represents [-2^23,2^23), leaving more than a factor-two
// margin.  Before division the absolute integer is < 2^59 for the largest
// pinned q, far below the ~2^252 Curve25519 scalar order, so Scalar wrap cannot
// satisfy a false integer equation.
type Result<T> = std::result::Result<T, PrivateBookBfvZkError>;

#[derive(Debug)]
pub enum PrivateBookBfvZkError {
    WrongParameters,
    InvalidStatement,
    InvalidOpening(String),
    PublicKeyWire,
    Encoder(String),
    Arithmetic(String),
    ProofWire,
    ProofSystem(String),
}

impl fmt::Display for PrivateBookBfvZkError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WrongParameters => write!(f, "private-book ZK requires the exact BFV fold set"),
            Self::InvalidStatement => write!(f, "invalid fixed Dark Bazaar public statement"),
            Self::InvalidOpening(error) => write!(f, "invalid private BFV opening: {error}"),
            Self::PublicKeyWire => write!(f, "collective public key is not a canonical BFV key"),
            Self::Encoder(error) => write!(f, "fhe.rs SIMD basis derivation failed: {error}"),
            Self::Arithmetic(error) => {
                write!(f, "private-book relation arithmetic failed: {error}")
            }
            Self::ProofWire => write!(f, "invalid private-book BFV proof wire"),
            Self::ProofSystem(error) => write!(f, "private-book Bulletproof failed: {error}"),
        }
    }
}

impl std::error::Error for PrivateBookBfvZkError {}

impl From<ExactBfvError> for PrivateBookBfvZkError {
    fn from(error: ExactBfvError) -> Self {
        match error {
            ExactBfvError::WrongParameters | ExactBfvError::InvalidOwner => Self::WrongParameters,
            ExactBfvError::InvalidStatement => Self::InvalidStatement,
            ExactBfvError::PublicKeyWire => Self::PublicKeyWire,
            ExactBfvError::Encoder(reason) => Self::Encoder(reason),
            ExactBfvError::Arithmetic(reason) => Self::Arithmetic(reason),
        }
    }
}

impl From<R1CSError> for PrivateBookBfvZkError {
    fn from(error: R1CSError) -> Self {
        Self::ProofSystem(error.to_string())
    }
}

/// Canonical transferable proof body.  The public statement, key, parameters,
/// and ciphertexts are deliberately supplied independently to verification.
#[derive(Clone, PartialEq, Eq)]
pub struct PrivateBookBfvZkProof {
    proof: Vec<u8>,
}

/// HidingFRI proof of one complete, exact native-field BFV equation: order 0,
/// ciphertext polynomial 0, modulus 0, coefficient 0.  This is the executable
/// first member of the mechanically extensible 98,304-equation family.  It is
/// post-quantum at the proof-system layer and has no Ristretto relation.
pub struct PrivateBookBfvNativeSliceProof {
    proof: native_slice::PrivateBookBfvSliceProof,
}

impl PrivateBookBfvNativeSliceProof {
    pub fn to_postcard(&self) -> Result<Vec<u8>> {
        self.proof
            .to_postcard()
            .map_err(PrivateBookBfvZkError::ProofSystem)
    }

    pub fn from_postcard(bytes: &[u8]) -> Result<Self> {
        let proof = native_slice::PrivateBookBfvSliceProof::from_postcard(bytes)
            .map_err(|_| PrivateBookBfvZkError::ProofWire)?;
        Ok(Self { proof })
    }
}

impl PrivateBookBfvZkProof {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(8 + 2 + 4 + self.proof.len());
        out.extend_from_slice(PROOF_MAGIC);
        out.extend_from_slice(&PROOF_VERSION.to_be_bytes());
        out.extend_from_slice(&(self.proof.len() as u32).to_be_bytes());
        out.extend_from_slice(&self.proof);
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
        if bytes.len() < 14 || &bytes[..8] != PROOF_MAGIC {
            return Err(PrivateBookBfvZkError::ProofWire);
        }
        let version = u16::from_be_bytes([bytes[8], bytes[9]]);
        let len = u32::from_be_bytes([bytes[10], bytes[11], bytes[12], bytes[13]]) as usize;
        if version != PROOF_VERSION
            || len > MAX_PROOF_BYTES
            || bytes.len().checked_sub(14) != Some(len)
        {
            return Err(PrivateBookBfvZkError::ProofWire);
        }
        R1CSProof::from_bytes(&bytes[14..]).map_err(|_| PrivateBookBfvZkError::ProofWire)?;
        Ok(Self {
            proof: bytes[14..].to_vec(),
        })
    }
}

/// Prove the exact four-ciphertext/private-root same-opening relation in one
/// explicit Tier-1 process that sees the complete private witness and opening.
///
/// The exact deterministic reencryption checker runs first.  This is
/// load-bearing: the R1CS short witnesses are extracted from those same seeds,
/// and are refused if the seeded ciphertext equality does not hold.
pub fn prove_private_book_bfv_zk(
    statement: PublicStatement,
    witness: &PrivateBookWitness,
    ciphertexts: &PrivateBookCiphertexts,
    opening: &PrivateBookEncryptionOpening,
    params: &BfvParams,
    public_key: &CollectivePublicKey,
) -> Result<PrivateBookBfvZkProof> {
    let mut timing = PhaseTimings::new("prove", "validate-public");
    validate_public(statement, ciphertexts, params)?;
    timing.next("opening-reencryption-check");
    verify_private_book_opening(statement, witness, ciphertexts, opening, params, public_key)
        .map_err(|error| PrivateBookBfvZkError::InvalidOpening(error.to_string()))?;

    timing.next("canonical-public-relation");
    let public = PublicRelation::derive(statement, ciphertexts, params, public_key)?;
    timing.next("secret-witness-extract");
    let secret = SecretRelation::extract(witness, opening)?;
    timing.next("seeded-ring-validation");
    secret.validate_seeded_equations(&public)?;

    timing.next("r1cs-phase1-synthesis");
    let pc_gens = PedersenGens::default();
    let transcript = relation_transcript(statement, ciphertexts, params, public_key);
    let mut prover = bulletproofs_r1cs::r1cs::Prover::new(&pc_gens, transcript);
    build_relation(&mut prover, statement, &public, Some(&secret))?;
    timing.next("r1cs-prove-including-phase2-synthesis");
    let proof = prover.prove(&BP_GENS)?;
    timing.next("proof-serialize");
    let result = PrivateBookBfvZkProof {
        proof: proof.to_bytes(),
    };
    timing.finish();
    Ok(result)
}

/// Verify transferable same-opening evidence.  The proof contains no trusted
/// copy of any public value; wrong key, ciphertext, root, session, modulus, or
/// layout changes the transcript and/or constraints and must fail.
pub fn verify_private_book_bfv_zk(
    proof: &PrivateBookBfvZkProof,
    statement: PublicStatement,
    ciphertexts: &PrivateBookCiphertexts,
    params: &BfvParams,
    public_key: &CollectivePublicKey,
) -> Result<()> {
    let mut timing = PhaseTimings::new("verify", "validate-public");
    validate_public(statement, ciphertexts, params)?;
    timing.next("canonical-public-relation");
    let public = PublicRelation::derive(statement, ciphertexts, params, public_key)?;
    timing.next("proof-parse-and-transcript");
    let r1cs = R1CSProof::from_bytes(&proof.proof).map_err(|_| PrivateBookBfvZkError::ProofWire)?;
    let transcript = relation_transcript(statement, ciphertexts, params, public_key);
    let mut verifier = bulletproofs_r1cs::r1cs::Verifier::new(transcript);
    timing.next("r1cs-phase1-rebuild");
    build_relation(&mut verifier, statement, &public, None)?;
    timing.next("r1cs-verify-including-phase2-rebuild");
    verifier.verify(&r1cs, &PedersenGens::default(), &BP_GENS)?;
    timing.finish();
    Ok(())
}

/// Prove the first exact native-PQ member of the private-book/BFV same-opening
/// family through the Lean-emitted descriptor and HidingFRI backend.
///
/// Unlike the legacy Bulletproof relation, this slice uses no transcript-
/// randomized compression: all 4,096 `u` coefficients occur in the exact
/// coefficient-zero negacyclic equation.  The host still validates every
/// production BFV equation before entering the prover, so the slice cannot be
/// used to bless a malformed ciphertext outside its presently materialized
/// geometry.
pub fn prove_private_book_bfv_native_slice_zk(
    statement: PublicStatement,
    witness: &PrivateBookWitness,
    ciphertexts: &PrivateBookCiphertexts,
    opening: &PrivateBookEncryptionOpening,
    params: &BfvParams,
    public_key: &CollectivePublicKey,
) -> Result<PrivateBookBfvNativeSliceProof> {
    validate_public(statement, ciphertexts, params)?;
    verify_private_book_opening(statement, witness, ciphertexts, opening, params, public_key)
        .map_err(|error| PrivateBookBfvZkError::InvalidOpening(error.to_string()))?;

    let mut timing = PhaseTimings::new("native-slice-prove", "public-relation");
    let public = PublicRelation::derive(statement, ciphertexts, params, public_key)?;
    let secret = SecretRelation::extract(witness, opening)?;
    secret.validate_seeded_equations(&public)?;

    let message = message_coefficient(secret.witness.orders[0], &public.message_table, 0, 0);
    let slice_opening = native_slice::PrivateBookBfvSliceOpening {
        public_key_coefficients: public.pk.polys[0].rows[0].clone(),
        u_coefficients: secret.randomness[0].u.clone(),
        error_coefficient: secret.randomness[0].e1[0],
        message_coefficient: message,
        ciphertext_coefficient: public.ciphertexts[0].polys[0].rows[0][0],
    };
    native_slice::audit_row_local_constraints(statement.session, witness, &slice_opening)
        .map_err(PrivateBookBfvZkError::ProofSystem)?;
    let (proof, native_public) = native_slice::prove_zk(statement.session, witness, &slice_opening)
        .map_err(PrivateBookBfvZkError::ProofSystem)?;
    if native_public.book != statement {
        return Err(PrivateBookBfvZkError::Arithmetic(
            "Lean-emitted slice statement disagreed with the supplied Dark Bazaar statement"
                .to_owned(),
        ));
    }
    timing.finish();
    Ok(PrivateBookBfvNativeSliceProof { proof })
}

/// Verify the exact native-PQ slice against independently supplied public key,
/// ciphertext, parameters, and Dark Bazaar statement.  The public-key root is
/// recomputed from all 4,096 coefficients; no prover-carried key identity is
/// trusted.
pub fn verify_private_book_bfv_native_slice_zk(
    proof: &PrivateBookBfvNativeSliceProof,
    statement: PublicStatement,
    ciphertexts: &PrivateBookCiphertexts,
    params: &BfvParams,
    public_key: &CollectivePublicKey,
) -> Result<()> {
    validate_public(statement, ciphertexts, params)?;
    let parsed_key = parse_public_key(public_key, params)?;
    let pk_row = &parsed_key.polys[0].rows[0];
    let key_root =
        native_slice::public_key_root(pk_row).map_err(PrivateBookBfvZkError::Arithmetic)?;
    let ciphertext = ciphertexts.rows()[0].polys[0].rows[0][0];
    let native_public = native_slice::PrivateBookBfvSlicePublic {
        book: statement,
        public_key_root: key_root,
        ciphertext_limbs: split_native_slice_residue(ciphertext),
    };
    native_slice::verify_zk(&proof.proof, native_public).map_err(PrivateBookBfvZkError::ProofSystem)
}

fn split_native_slice_residue(mut value: u64) -> [u32; 3] {
    core::array::from_fn(|_| {
        let limb = (value & 0x7fff) as u32;
        value >>= 15;
        limb
    })
}

fn validate_public(
    statement: PublicStatement,
    ciphertexts: &PrivateBookCiphertexts,
    params: &BfvParams,
) -> Result<()> {
    if params.degree() != FOLD_DEGREE
        || params.moduli() != FOLD_MODULI.as_slice()
        || params.plaintext_modulus() != FOLD_PLAINTEXT_MODULUS
    {
        return Err(PrivateBookBfvZkError::WrongParameters);
    }
    if statement.session >= BABYBEAR_MODULUS
        || statement.rule != RULE_ID
        || statement.p_star as usize >= PRICE_COUNT
        || statement.v_star > (ORDER_COUNT as u32) * u32::from(dark_bazaar_private::MAX_QTY)
        || statement
            .order_root
            .iter()
            .any(|&lane| lane >= BABYBEAR_MODULUS)
    {
        return Err(PrivateBookBfvZkError::InvalidStatement);
    }
    if ciphertexts.rows().iter().any(|row| {
        row.degree != FOLD_DEGREE
            || row.moduli.as_slice() != FOLD_MODULI.as_slice()
            || row.level != 0
            || !row.variable_time
            || row.polys.len() != 2
            || row.plain_bound != PRIVATE_BOOK_PUBLIC_BOUND
            || row.polys.iter().any(|poly| {
                poly.rows.len() != FOLD_MODULI.len()
                    || poly.rows.iter().any(|coeffs| coeffs.len() != FOLD_DEGREE)
            })
    }) {
        return Err(PrivateBookBfvZkError::WrongParameters);
    }
    Ok(())
}

fn relation_transcript(
    statement: PublicStatement,
    ciphertexts: &PrivateBookCiphertexts,
    params: &BfvParams,
    public_key: &CollectivePublicKey,
) -> Transcript {
    let mut transcript = Transcript::new(PROOF_TRANSCRIPT);
    transcript.append_message(b"codec", PRIVATE_BOOK_BFV_CODEC_ID);
    transcript.append_u64(b"version", u64::from(PROOF_VERSION));
    transcript.append_u64(b"compression-rounds", COMPRESSION_ROUNDS as u64);
    transcript.append_u64(b"short-bits", SHORT_BITS as u64);
    transcript.append_u64(b"quotient-bits", QUOTIENT_BITS as u64);
    transcript.append_message(
        b"relation",
        &private_book_relation_digest(statement, ciphertexts, params, public_key),
    );
    transcript
}

#[derive(Clone, Debug)]
struct OrderRandomness {
    u: Vec<i64>,
    e1: Vec<i64>,
    e2: Vec<i64>,
}

#[derive(Clone)]
struct SecretRelation {
    witness: PrivateBookWitness,
    randomness: [OrderRandomness; ORDER_COUNT],
}

impl SecretRelation {
    fn extract(
        witness: &PrivateBookWitness,
        opening: &PrivateBookEncryptionOpening,
    ) -> Result<Self> {
        let randomness = opening
            .prover_seeds()
            .iter()
            .map(|seed| {
                let mut rng = StdRng::from_seed(*seed);
                let u = sample_cbd(FOLD_DEGREE, BFV_VARIANCE, &mut rng)?;
                let e1 = sample_cbd(FOLD_DEGREE, BFV_VARIANCE, &mut rng)?;
                let e2 = sample_cbd(FOLD_DEGREE, BFV_VARIANCE, &mut rng)?;
                if u.iter().chain(e1.iter()).chain(e2.iter()).any(|value| {
                    !(-2 * BFV_VARIANCE as i64..=2 * BFV_VARIANCE as i64).contains(value)
                }) {
                    return Err(PrivateBookBfvZkError::InvalidOpening(
                        "CBD extraction exceeded the pinned variance bound".to_owned(),
                    ));
                }
                Ok(OrderRandomness { u, e1, e2 })
            })
            .collect::<Result<Vec<_>>>()?
            .try_into()
            .expect("exactly four encryption seeds");
        Ok(Self {
            witness: witness.clone(),
            randomness,
        })
    }

    /// Independently re-evaluate every exact public-key ring equation from the
    /// extracted short coefficients.  This catches RNG/sampling drift before a
    /// proof can turn a host-side extraction mistake into an asserted witness.
    fn validate_seeded_equations(&self, public: &PublicRelation) -> Result<()> {
        if crate::private_book_bfv_wgpu::requested_by_environment() {
            // The same opt-in that requests the large signed-dot kernel also
            // requests the exact eight seeded u×pk products. It is fail-closed:
            // adapter absence or limits are errors, never CPU work carrying a
            // GPU label. The no-environment path below remains the independent
            // fhe-math reference used since the relation was introduced.
            self.validate_seeded_equations_with_engine(public, &RnsNttEngine::require_wgpu())?;
            Ok(())
        } else {
            self.validate_seeded_equations_reference(public)
        }
    }

    fn validate_seeded_equations_reference(&self, public: &PublicRelation) -> Result<()> {
        self.validate_seeded_products(public, |order, poly| {
            let mut u = Poly::try_convert_from(
                self.randomness[order].u.as_slice(),
                &public.context,
                false,
                Representation::PowerBasis,
            )
            .map_err(|error| PrivateBookBfvZkError::Arithmetic(error.to_string()))?;
            let mut pk = Poly::try_convert_from(
                public.pk.polys[poly]
                    .rows
                    .iter()
                    .flatten()
                    .copied()
                    .collect::<Vec<_>>(),
                &public.context,
                false,
                Representation::PowerBasis,
            )
            .map_err(|error| PrivateBookBfvZkError::Arithmetic(error.to_string()))?;
            u.change_representation(Representation::Ntt);
            pk.change_representation(Representation::Ntt);
            u *= &pk;
            u.change_representation(Representation::PowerBasis);
            Ok(Vec::<u64>::from(&u))
        })
    }

    /// Production portable-wgpu seam for the exact seeded ring preflight.
    /// Returning the observed backend lets the qualification canary prove that
    /// the real relation caller—not only an isolated kernel test—selected the
    /// requested adapter.
    fn validate_seeded_equations_with_engine(
        &self,
        public: &PublicRelation,
        engine: &RnsNttEngine,
    ) -> Result<RnsNttBatchExecution> {
        let mut lhs = Vec::with_capacity(ORDER_COUNT * 2);
        let mut rhs = Vec::with_capacity(ORDER_COUNT * 2);
        for order in 0..ORDER_COUNT {
            let u = RnsPoly {
                rows: FOLD_MODULI
                    .iter()
                    .map(|&q| {
                        self.randomness[order]
                            .u
                            .iter()
                            .map(|&value| i128::from(value).rem_euclid(i128::from(q)) as u64)
                            .collect()
                    })
                    .collect(),
            };
            for poly in 0..2 {
                lhs.push(u.clone());
                rhs.push(public.pk.polys[poly].clone());
            }
        }
        let execution = engine
            .multiply_batch(&lhs, &rhs, &FOLD_MODULI)
            .map_err(|error| PrivateBookBfvZkError::Arithmetic(error.to_string()))?;
        self.validate_seeded_products(public, |order, poly| {
            Ok(execution.polynomials[order * 2 + poly]
                .rows
                .iter()
                .flatten()
                .copied()
                .collect())
        })?;
        Ok(execution)
    }

    fn validate_seeded_products<F>(&self, public: &PublicRelation, mut product: F) -> Result<()>
    where
        F: FnMut(usize, usize) -> Result<Vec<u64>>,
    {
        for order in 0..ORDER_COUNT {
            for poly in 0..2 {
                let product = product(order, poly)?;
                if product.len() != FOLD_MODULI.len() * FOLD_DEGREE {
                    return Err(PrivateBookBfvZkError::Arithmetic(
                        "seeded ring product has the wrong exact shape".to_owned(),
                    ));
                }
                for (qi, &q) in FOLD_MODULI.iter().enumerate() {
                    for coefficient in 0..FOLD_DEGREE {
                        let mut rhs = product[qi * FOLD_DEGREE + coefficient] as i128;
                        rhs += if poly == 0 {
                            self.randomness[order].e1[coefficient] as i128
                        } else {
                            self.randomness[order].e2[coefficient] as i128
                        };
                        if poly == 0 {
                            rhs += message_coefficient(
                                self.witness.orders[order],
                                &public.message_table,
                                qi,
                                coefficient,
                            ) as i128;
                        }
                        let actual = public.ciphertexts[order].polys[poly].rows[qi][coefficient];
                        if rhs.rem_euclid(q as i128) != actual as i128 {
                            let error = if poly == 0 {
                                self.randomness[order].e1[coefficient]
                            } else {
                                self.randomness[order].e2[coefficient]
                            };
                            let message = if poly == 0 {
                                message_coefficient(
                                    self.witness.orders[order],
                                    &public.message_table,
                                    qi,
                                    coefficient,
                                )
                            } else {
                                0
                            };
                            return Err(PrivateBookBfvZkError::InvalidOpening(format!(
                                "extracted short witness disagrees at order {order}, poly {poly}, modulus {qi}, coefficient {coefficient}: product={}, error={error}, message={message}, rhs={}, actual={actual}",
                                product[qi * FOLD_DEGREE + coefficient],
                                rhs.rem_euclid(q as i128),
                            )));
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

#[derive(Clone)]
struct OrderVars {
    options: Vec<Variable>,
}

#[derive(Clone)]
struct RandomnessVars {
    u: Vec<Variable>,
    e1: Vec<Variable>,
    e2: Vec<Variable>,
}

fn build_relation<CS: RandomizableConstraintSystem>(
    cs: &mut CS,
    statement: PublicStatement,
    public: &PublicRelation,
    secret: Option<&SecretRelation>,
) -> std::result::Result<(), R1CSError> {
    let mut order_vars = Vec::with_capacity(ORDER_COUNT);
    let mut packed_book = LinearCombination::from(Scalar::ZERO);
    let mut packed_value = 0u64;

    for order_index in 0..ORDER_COUNT {
        let order = secret.map(|secret| secret.witness.orders[order_index]);
        let option_value = order.map(order_option_index);
        let mut options = Vec::with_capacity(PRIVATE_BOOK_OPTION_COUNT);
        let mut one_hot = LinearCombination::from(-Scalar::ONE);
        let mut code = LinearCombination::from(Scalar::ZERO);
        for kind in 0..2 * PRICE_COUNT {
            for qty in 0..QUANTITY_COUNT {
                let option_index = kind * QUANTITY_COUNT + qty;
                let selected = option_value.map(|actual| u64::from(actual == option_index));
                let option = bit(cs, selected)?;
                one_hot = one_hot + option;
                code = code + option * Scalar::from((kind + 8 * qty) as u64);
                options.push(option);
            }
        }
        cs.constrain(one_hot);

        let place = 128u64.pow(order_index as u32);
        packed_book = packed_book + code * Scalar::from(place);
        if let Some(order) = order {
            let kind = order_kind(order) as u64;
            packed_value += (kind + 8 * u64::from(order.qty)) * place;
        }
        order_vars.push(OrderVars { options });
    }

    constrain_poseidon_root(
        cs,
        statement,
        packed_book,
        secret.map(|_| packed_value),
        secret.map(|secret| secret.witness.blinding),
    )?;

    let mut randomness_vars = Vec::with_capacity(ORDER_COUNT);
    for order in 0..ORDER_COUNT {
        let values = secret.map(|secret| &secret.randomness[order]);
        let u = allocate_short_vector(cs, values.map(|values| values.u.as_slice()))?;
        let e1 = allocate_short_vector(cs, values.map(|values| values.e1.as_slice()))?;
        let e2 = allocate_short_vector(cs, values.map(|values| values.e2.as_slice()))?;
        randomness_vars.push(RandomnessVars { u, e1, e2 });
    }

    let phase_public = public.clone();
    let phase_orders = order_vars;
    let phase_randomness = randomness_vars;
    let phase_secret = secret.cloned();
    // `specify_randomized_constraints` stores this callback until the prover's
    // complete phase-one assignment (orders, blindings, and all u/e vectors)
    // has been committed into A_I1/A_O1/S1.  `challenge_scalar` is unavailable
    // before that transition, so neither prover nor caller can choose the
    // compression signs before committing the witness.
    cs.specify_randomized_constraints(move |phase2| {
        constrain_bfv_equations(
            phase2,
            &phase_public,
            &phase_orders,
            &phase_randomness,
            phase_secret.as_ref(),
        )
    })?;
    Ok(())
}

fn allocate_short_vector<CS: ConstraintSystem>(
    cs: &mut CS,
    values: Option<&[i64]>,
) -> std::result::Result<Vec<Variable>, R1CSError> {
    let mut variables = Vec::with_capacity(FOLD_DEGREE);
    for coefficient in 0..FOLD_DEGREE {
        let value = values.map(|values| values[coefficient]);
        let variable = cs.allocate(value.map(|value| scalar_i128(i128::from(value))))?;
        range_lc(
            cs,
            variable + Scalar::from(SHORT_SHIFT as u64),
            value.map(|value| (value + SHORT_SHIFT) as u64),
            SHORT_BITS,
        )?;
        variables.push(variable);
    }
    Ok(variables)
}

fn constrain_bfv_equations<CS: RandomizedConstraintSystem>(
    cs: &mut CS,
    public: &PublicRelation,
    orders: &[OrderVars],
    randomness: &[RandomnessVars],
    secret: Option<&SecretRelation>,
) -> std::result::Result<(), R1CSError> {
    let mut timing = PhaseTimings::new(
        if secret.is_some() {
            "prove-phase2-relation"
        } else {
            "verify-phase2-relation"
        },
        "rademacher-ntt-and-lc-synthesis",
    );
    let mut correlation_ntt = Duration::ZERO;
    let challenge = cs.challenge_scalar(b"bfv-coefficient-compression");
    let challenge_bytes = challenge.to_bytes();
    // Prover-only, explicit opt-in. Verification deliberately keeps deriving
    // these public coefficients through `signed_dot`, so a GPU-produced proof
    // is checked by the unchanged CPU relation.
    let message_dot_started = timing.enabled().then(Instant::now);
    let message_dot_cache =
        if secret.is_some() && crate::private_book_bfv_wgpu::requested_by_environment() {
            Some(precompute_message_dots_wgpu(
                &challenge_bytes,
                &public.message_table,
            )?)
        } else {
            None
        };
    if message_dot_cache.is_some() {
        if let Some(started) = message_dot_started {
            timing.add_aggregate("wgpu-message-dots", started.elapsed());
        }
    }
    for qi in 0..FOLD_MODULI.len() {
        let q = FOLD_MODULI[qi];
        for round in 0..COMPRESSION_ROUNDS {
            let mut equation = LinearCombination::from(Scalar::ZERO);
            let mut public_constant = 0i128;
            let mut assignment = secret.map(|_| 0i128);
            for order in 0..ORDER_COUNT {
                for poly in 0..2 {
                    let signs = derive_signs(&challenge_bytes, qi, round, order, poly, FOLD_DEGREE);
                    let ntt_started = timing.enabled().then(Instant::now);
                    let gradient = negacyclic_correlation(
                        &signs,
                        &public.pk_adjoint_ntt[poly],
                        &public.context,
                        qi,
                        FOLD_DEGREE,
                    )
                    .map_err(|error| R1CSError::GadgetError {
                        description: error.to_string(),
                    })?;
                    if let Some(started) = ntt_started {
                        correlation_ntt += started.elapsed();
                    }
                    for coefficient in 0..FOLD_DEGREE {
                        let u_coeff = gradient[coefficient] as i128;
                        equation =
                            equation + randomness[order].u[coefficient] * scalar_i128(u_coeff);
                        let error_var = if poly == 0 {
                            randomness[order].e1[coefficient]
                        } else {
                            randomness[order].e2[coefficient]
                        };
                        equation = equation + error_var * scalar_i128(signs[coefficient] as i128);
                        let ct = public.ciphertexts[order].polys[poly].rows[qi][coefficient];
                        public_constant -= signs[coefficient] as i128 * ct as i128;
                        if let (Some(total), Some(secret)) = (&mut assignment, secret) {
                            *total += u_coeff * secret.randomness[order].u[coefficient] as i128;
                            let error = if poly == 0 {
                                secret.randomness[order].e1[coefficient]
                            } else {
                                secret.randomness[order].e2[coefficient]
                            };
                            *total += signs[coefficient] as i128 * error as i128;
                            *total -= signs[coefficient] as i128 * ct as i128;
                        }
                    }
                    if poly == 0 {
                        let cached_coefficients = message_dot_cache.as_ref().map(|dots| {
                            let sign_row = (qi * COMPRESSION_ROUNDS + round) * ORDER_COUNT + order;
                            let start = sign_row * PRIVATE_BOOK_OPTION_COUNT;
                            &dots[start..start + PRIVATE_BOOK_OPTION_COUNT]
                        });
                        add_message_dot(
                            &mut equation,
                            &mut assignment,
                            &signs,
                            qi,
                            &public.message_table,
                            &orders[order],
                            secret.map(|secret| secret.witness.orders[order]),
                            cached_coefficients,
                        );
                    }
                }
            }
            equation = equation + scalar_i128(public_constant);

            let quotient = assignment.map(|value| {
                if value % q as i128 != 0 {
                    return Err(R1CSError::GadgetError {
                        description: "honest BFV batch is not divisible by its RNS modulus"
                            .to_owned(),
                    });
                }
                let quotient = value / q as i128;
                if quotient.unsigned_abs() > MAX_ABS_BATCH_QUOTIENT as u128 {
                    return Err(R1CSError::GadgetError {
                        description: "BFV batch quotient exceeded derived integer bound".to_owned(),
                    });
                }
                Ok(quotient)
            });
            let quotient = match quotient {
                Some(result) => Some(result?),
                None => None,
            };
            let quotient_var = cs.allocate(quotient.map(scalar_i128))?;
            let shift = 1u64 << (QUOTIENT_BITS - 1);
            range_lc(
                cs,
                quotient_var + Scalar::from(shift),
                quotient.map(|value| (value + shift as i128) as u64),
                QUOTIENT_BITS,
            )?;
            cs.constrain(equation - quotient_var * Scalar::from(q));
        }
    }
    timing.add_aggregate("3072-negacyclic-correlations", correlation_ntt);
    timing.finish();
    Ok(())
}

/// Batch the fixed relation's public message-table coefficients through the
/// exact WGSL signed-dot kernel. Result order is
/// `[modulus][round][order][option]`, matching the phase-two loop above.
fn precompute_message_dots_wgpu(
    challenge: &[u8; 32],
    table: &[Vec<Vec<u64>>],
) -> std::result::Result<Vec<i128>, R1CSError> {
    use crate::private_book_bfv_wgpu::{precompute_signed_dots_wgpu, SignedDotShape};

    let sign_words = FOLD_DEGREE.div_ceil(32);
    let sign_rows_per_modulus = COMPRESSION_ROUNDS * ORDER_COUNT;
    let sign_rows = FOLD_MODULI.len() * sign_rows_per_modulus;
    let mut packed_signs = vec![0u32; sign_rows * sign_words];
    for qi in 0..FOLD_MODULI.len() {
        for round in 0..COMPRESSION_ROUNDS {
            for order in 0..ORDER_COUNT {
                let row = (qi * COMPRESSION_ROUNDS + round) * ORDER_COUNT + order;
                // Message terms occur only in c0, hence the exact poly=0 row.
                for (coefficient, sign) in derive_signs(challenge, qi, round, order, 0, FOLD_DEGREE)
                    .into_iter()
                    .enumerate()
                {
                    if sign > 0 {
                        packed_signs[row * sign_words + coefficient / 32] |=
                            1 << (coefficient % 32);
                    }
                }
            }
        }
    }

    if table.len() != PRIVATE_BOOK_OPTION_COUNT
        || table.iter().any(|option| {
            option.len() != FOLD_MODULI.len() || option.iter().any(|row| row.len() != FOLD_DEGREE)
        })
    {
        return Err(R1CSError::GadgetError {
            description: "private-book message table has the wrong GPU precompute shape".to_owned(),
        });
    }
    let mut messages =
        Vec::with_capacity(PRIVATE_BOOK_OPTION_COUNT * FOLD_MODULI.len() * FOLD_DEGREE);
    for option in table {
        for modulus in option {
            messages.extend_from_slice(modulus);
        }
    }
    precompute_signed_dots_wgpu(
        SignedDotShape {
            degree: FOLD_DEGREE,
            modulus_count: FOLD_MODULI.len(),
            option_count: PRIVATE_BOOK_OPTION_COUNT,
            sign_rows_per_modulus,
        },
        &packed_signs,
        &messages,
    )
    .map_err(|error| R1CSError::GadgetError {
        description: format!("requested private-book wgpu precompute failed: {error}"),
    })
}

fn add_message_dot(
    equation: &mut LinearCombination,
    assignment: &mut Option<i128>,
    signs: &[i64],
    qi: usize,
    table: &[Vec<Vec<u64>>],
    vars: &OrderVars,
    order: Option<dark_bazaar_private::PrivateOrder>,
    cached_coefficients: Option<&[i128]>,
) {
    let actual_option = order.map(order_option_index);
    for (option_index, option) in vars.options.iter().copied().enumerate() {
        let coefficient = cached_coefficients
            .map(|coefficients| coefficients[option_index])
            .unwrap_or_else(|| signed_dot(signs, &table[option_index][qi]));
        let current = std::mem::take(equation);
        *equation = current + option * scalar_i128(coefficient);
        if let (Some(total), Some(actual_option)) = (assignment.as_mut(), actual_option) {
            if actual_option == option_index {
                *total += coefficient;
            }
        }
    }
}

fn message_coefficient(
    order: dark_bazaar_private::PrivateOrder,
    table: &[Vec<Vec<u64>>],
    qi: usize,
    coefficient: usize,
) -> u64 {
    table[order_option_index(order)][qi][coefficient]
}

fn order_kind(order: dark_bazaar_private::PrivateOrder) -> usize {
    order.limit as usize
        + usize::from(matches!(order.side, dark_bazaar_private::Side::Ask)) * PRICE_COUNT
}

fn order_option_index(order: dark_bazaar_private::PrivateOrder) -> usize {
    order_kind(order) * QUANTITY_COUNT + order.qty as usize
}

fn sample_cbd<R: RngCore>(size: usize, variance: usize, rng: &mut R) -> Result<Vec<i64>> {
    if !(1..=16).contains(&variance) {
        return Err(PrivateBookBfvZkError::InvalidOpening(
            "unsupported BFV CBD variance".to_owned(),
        ));
    }
    let number_bits = 4 * variance;
    let mask_add = ((u64::MAX >> (64 - number_bits)) >> (2 * variance)) as u128;
    let mask_sub = mask_add << (2 * variance);
    let mut pool = 0u128;
    let mut pool_bits = 0usize;
    let mut out = Vec::with_capacity(size);
    for _ in 0..size {
        if pool_bits < number_bits {
            pool |= (rng.next_u64() as u128) << pool_bits;
            pool_bits += 64;
        }
        out.push(((pool & mask_add).count_ones() as i64) - ((pool & mask_sub).count_ones() as i64));
        pool >>= number_bits;
        pool_bits -= number_bits;
    }
    Ok(out)
}

fn bit<CS: ConstraintSystem>(
    cs: &mut CS,
    value: Option<u64>,
) -> std::result::Result<Variable, R1CSError> {
    let assignment = value.map(Scalar::from);
    let (left, right, output) = cs.allocate_multiplier(assignment.zip(assignment))?;
    cs.constrain(left - right);
    cs.constrain(output - left);
    Ok(left)
}

fn range_lc<CS: ConstraintSystem>(
    cs: &mut CS,
    value_lc: LinearCombination,
    value: Option<u64>,
    bits: usize,
) -> std::result::Result<(), R1CSError> {
    let mut bit_sum = LinearCombination::from(Scalar::ZERO);
    for index in 0..bits {
        let bit_value = value.map(|value| (value >> index) & 1);
        let variable = bit(cs, bit_value)?;
        bit_sum = bit_sum + variable * Scalar::from(1u64 << index);
    }
    cs.constrain(value_lc - bit_sum);
    Ok(())
}

#[derive(Clone, Debug)]
struct FeltLc {
    lc: LinearCombination,
    value: Option<u64>,
}

impl FeltLc {
    fn constant(value: u64) -> Self {
        Self {
            lc: LinearCombination::from(Scalar::from(value)),
            value: Some(value),
        }
    }
}

fn constrain_poseidon_root<CS: ConstraintSystem>(
    cs: &mut CS,
    statement: PublicStatement,
    packed_book: LinearCombination,
    packed_value: Option<u64>,
    blinding: Option<[u32; DIGEST_WIDTH]>,
) -> std::result::Result<(), R1CSError> {
    // Preserve the historical FHPZK001 allocation/constraint schedule exactly:
    // each lane is allocated and range-constrained before the next lane.
    let mut state = poseidon_root_prefix(statement, packed_book, packed_value);
    for lane in 0..DIGEST_WIDTH {
        let value = blinding.map(|blinding| u64::from(blinding[lane]));
        let variable = cs.allocate(value.map(Scalar::from))?;
        constrain_canonical_felt(cs, variable.into(), value)?;
        state.push(FeltLc {
            lc: variable.into(),
            value,
        });
    }
    finish_poseidon_root(cs, statement, state)
}

/// Shared fixed-root gadget for continuation proofs whose scalar commitments
/// have already allocated the eight private blinding variables.
///
/// Keeping this as the single implementation is load-bearing: the monolithic
/// same-opening proof and the distributed root-link proof must constrain the
/// exact same arity-16 Poseidon2 permutation and BabyBear canonicality rules.
pub(crate) fn constrain_poseidon_root_with_blinding_variables<CS: ConstraintSystem>(
    cs: &mut CS,
    statement: PublicStatement,
    packed_book: LinearCombination,
    packed_value: Option<u64>,
    blinding_variables: &[Variable; DIGEST_WIDTH],
    blinding: Option<[u32; DIGEST_WIDTH]>,
) -> std::result::Result<(), R1CSError> {
    let mut state = poseidon_root_prefix(statement, packed_book, packed_value);
    for lane in 0..DIGEST_WIDTH {
        let value = blinding.map(|blinding| u64::from(blinding[lane]));
        let variable = blinding_variables[lane];
        constrain_canonical_felt(cs, variable.into(), value)?;
        state.push(FeltLc {
            lc: variable.into(),
            value,
        });
    }
    finish_poseidon_root(cs, statement, state)
}

fn poseidon_root_prefix(
    statement: PublicStatement,
    packed_book: LinearCombination,
    packed_value: Option<u64>,
) -> Vec<FeltLc> {
    let mut state = Vec::with_capacity(POSEIDON_WIDTH);
    state.push(FeltLc::constant(u64::from(ROOT_DOMAIN_TAG)));
    state.push(FeltLc::constant(u64::from(statement.session)));
    state.push(FeltLc::constant(u64::from(RULE_ID)));
    state.push(FeltLc {
        lc: packed_book,
        value: packed_value,
    });
    state
}

fn finish_poseidon_root<CS: ConstraintSystem>(
    cs: &mut CS,
    statement: PublicStatement,
    mut state: Vec<FeltLc>,
) -> std::result::Result<(), R1CSError> {
    state.extend((0..4).map(|_| FeltLc::constant(0)));
    let mut state: [FeltLc; POSEIDON_WIDTH] = state.try_into().expect("arity sixteen");
    state = external_linear_layer(cs, &state)?;
    for constants in RC_EXT_INIT {
        for lane in 0..POSEIDON_WIDTH {
            state[lane] = reduce_felt(
                cs,
                state[lane].lc.clone() + Scalar::from(constants[lane] as u64),
                state[lane]
                    .value
                    .map(|value| value as u128 + constants[lane] as u128),
            )?;
            state[lane] = pow7(cs, state[lane].clone())?;
        }
        state = external_linear_layer(cs, &state)?;
    }
    for (round, constant) in RC_INTERNAL.into_iter().enumerate() {
        state[0] = reduce_felt(
            cs,
            state[0].lc.clone() + Scalar::from(constant as u64),
            state[0].value.map(|value| value as u128 + constant as u128),
        )?;
        state[0] = pow7(cs, state[0].clone())?;
        state = internal_linear_layer(cs, &state, round)?;
    }
    for constants in RC_EXT_FINAL {
        for lane in 0..POSEIDON_WIDTH {
            state[lane] = reduce_felt(
                cs,
                state[lane].lc.clone() + Scalar::from(constants[lane] as u64),
                state[lane]
                    .value
                    .map(|value| value as u128 + constants[lane] as u128),
            )?;
            state[lane] = pow7(cs, state[lane].clone())?;
        }
        state = external_linear_layer(cs, &state)?;
    }
    for lane in 0..DIGEST_WIDTH {
        cs.constrain(state[lane].lc.clone() - Scalar::from(statement.order_root[lane] as u64));
    }
    Ok(())
}

fn pow7<CS: ConstraintSystem>(
    cs: &mut CS,
    value: FeltLc,
) -> std::result::Result<FeltLc, R1CSError> {
    let square = mul_felt(cs, &value, &value)?;
    let fourth = mul_felt(cs, &square, &square)?;
    let sixth = mul_felt(cs, &fourth, &square)?;
    mul_felt(cs, &sixth, &value)
}

fn mul_felt<CS: ConstraintSystem>(
    cs: &mut CS,
    left: &FeltLc,
    right: &FeltLc,
) -> std::result::Result<FeltLc, R1CSError> {
    let (_, _, product) = cs.multiply(left.lc.clone(), right.lc.clone());
    reduce_felt(
        cs,
        product.into(),
        left.value
            .zip(right.value)
            .map(|(left, right)| left as u128 * right as u128),
    )
}

fn external_linear_layer<CS: ConstraintSystem>(
    cs: &mut CS,
    state: &[FeltLc; POSEIDON_WIDTH],
) -> std::result::Result<[FeltLc; POSEIDON_WIDTH], R1CSError> {
    let mut block = Vec::with_capacity(POSEIDON_WIDTH);
    for start in (0..POSEIDON_WIDTH).step_by(4) {
        let coefficients = [[2u64, 3, 1, 1], [1, 2, 3, 1], [1, 1, 2, 3], [3, 1, 1, 2]];
        for row in coefficients {
            block.push(linear_felt(cs, &state[start..start + 4], &row)?);
        }
    }
    let mut out = Vec::with_capacity(POSEIDON_WIDTH);
    for lane in 0..POSEIDON_WIDTH {
        let column = lane % 4;
        let inputs = [
            block[lane].clone(),
            block[column].clone(),
            block[4 + column].clone(),
            block[8 + column].clone(),
            block[12 + column].clone(),
        ];
        out.push(linear_felt(cs, &inputs, &[1, 1, 1, 1, 1])?);
    }
    Ok(out.try_into().expect("Poseidon width"))
}

fn internal_linear_layer<CS: ConstraintSystem>(
    cs: &mut CS,
    state: &[FeltLc; POSEIDON_WIDTH],
    _round: usize,
) -> std::result::Result<[FeltLc; POSEIDON_WIDTH], R1CSError> {
    let mut out = Vec::with_capacity(POSEIDON_WIDTH);
    for lane in 0..POSEIDON_WIDTH {
        let mut inputs = state.to_vec();
        inputs.push(state[lane].clone());
        let mut coefficients = vec![1u64; POSEIDON_WIDTH];
        coefficients.push(u64::from(
            (INTERNAL_DIAG[lane] + BABYBEAR_MODULUS - 1) % BABYBEAR_MODULUS,
        ));
        out.push(linear_felt(cs, &inputs, &coefficients)?);
    }
    Ok(out.try_into().expect("Poseidon width"))
}

fn linear_felt<CS: ConstraintSystem>(
    cs: &mut CS,
    inputs: &[FeltLc],
    coefficients: &[u64],
) -> std::result::Result<FeltLc, R1CSError> {
    let mut lc = LinearCombination::from(Scalar::ZERO);
    let mut raw = Some(0u128);
    for (input, &coefficient) in inputs.iter().zip(coefficients) {
        lc = lc + input.lc.clone() * Scalar::from(coefficient);
        raw = raw
            .zip(input.value)
            .map(|(raw, value)| raw + value as u128 * coefficient as u128);
    }
    reduce_felt(cs, lc, raw)
}

fn reduce_felt<CS: ConstraintSystem>(
    cs: &mut CS,
    raw_lc: LinearCombination,
    raw: Option<u128>,
) -> std::result::Result<FeltLc, R1CSError> {
    let modulus = u128::from(BABYBEAR_MODULUS);
    let value = raw.map(|raw| (raw % modulus) as u64);
    let quotient = raw.map(|raw| (raw / modulus) as u64);
    let variable = cs.allocate(value.map(Scalar::from))?;
    let quotient_var = cs.allocate(quotient.map(Scalar::from))?;
    constrain_canonical_felt(cs, variable.into(), value)?;
    range_lc(cs, quotient_var.into(), quotient, 32)?;
    cs.constrain(raw_lc - variable - quotient_var * Scalar::from(u64::from(BABYBEAR_MODULUS)));
    Ok(FeltLc {
        lc: variable.into(),
        value,
    })
}

fn constrain_canonical_felt<CS: ConstraintSystem>(
    cs: &mut CS,
    lc: LinearCombination,
    value: Option<u64>,
) -> std::result::Result<(), R1CSError> {
    range_lc(cs, lc.clone(), value, 31)?;
    let gap = (1u64 << 31) - u64::from(BABYBEAR_MODULUS);
    range_lc(
        cs,
        lc + Scalar::from(gap),
        value.map(|value| value + gap),
        31,
    )
}

fn scalar_i128(value: i128) -> Scalar {
    if value < 0 {
        -Scalar::from((-value) as u64)
    } else {
        Scalar::from(value as u64)
    }
}

// Exact deployed Poseidon2 constants.  Duplicated here on purpose: this crate
// already depends on the prover half but not directly on dregg-circuit, and the
// constants are pinned by a cross-check test before module integration.
const RC_EXT_INIT: [[u32; 16]; 4] = [
    [
        0x69cbb6af, 0x46ad93f9, 0x60a00f4e, 0x6b1297cd, 0x23189afe, 0x732e7bef, 0x72c246de,
        0x2c941900, 0x0557eede, 0x1580496f, 0x3a3ea77b, 0x54f3f271, 0x0f49b029, 0x47872fe1,
        0x221e2e36, 0x1ab7202e,
    ],
    [
        0x487779a6, 0x3851c9d8, 0x38dc17c0, 0x209f8849, 0x268dcee8, 0x350c48da, 0x5b9ad32e,
        0x0523272b, 0x3f89055b, 0x01e894b2, 0x13ddedde, 0x1b2ef334, 0x7507d8b4, 0x6ceeb94e,
        0x52eb6ba2, 0x50642905,
    ],
    [
        0x05453f3f, 0x06349efc, 0x6922787c, 0x04bfff9c, 0x768c714a, 0x3e9ff21a, 0x15737c9c,
        0x2229c807, 0x0d47f88c, 0x097e0ecc, 0x27eadba0, 0x2d7d29e4, 0x3502aaa0, 0x0f475fd7,
        0x29fbda49, 0x018afffd,
    ],
    [
        0x0315b618, 0x6d4497d1, 0x1b171d9e, 0x52861abd, 0x2e5d0501, 0x3ec8646c, 0x6e5f250a,
        0x148ae8e6, 0x17f5fa4a, 0x3e66d284, 0x0051aa3b, 0x483f7913, 0x2cfe5f15, 0x023427ca,
        0x2cc78315, 0x1e36ea47,
    ],
];
const RC_EXT_FINAL: [[u32; 16]; 4] = [
    [
        0x7290a80d, 0x6f7e5329, 0x598ec8a8, 0x76a859a0, 0x6559e868, 0x657b83af, 0x13271d3f,
        0x1f876063, 0x0aeeae37, 0x706e9ca6, 0x46400cee, 0x72a05c26, 0x2c589c9e, 0x20bd37a7,
        0x6a2d3d10, 0x20523767,
    ],
    [
        0x5b8fe9c4, 0x2aa501d6, 0x1e01ac3e, 0x1448bc54, 0x5ce5ad1c, 0x4918a14d, 0x2c46a83f,
        0x4fcf6876, 0x61d8d5c8, 0x6ddf4ff9, 0x11fda4d3, 0x02933a8f, 0x170eaf81, 0x5a9c314f,
        0x49a12590, 0x35ec52a1,
    ],
    [
        0x58eb1611, 0x5e481e65, 0x367125c9, 0x0eba33ba, 0x1fc28ded, 0x066399ad, 0x0cbec0ea,
        0x75fd1af0, 0x50f5bf4e, 0x643d5f41, 0x6f4fe718, 0x5b3cbbde, 0x1e3afb3e, 0x296fb027,
        0x45e1547b, 0x4a8db2ab,
    ],
    [
        0x59986d19, 0x30bcdfa3, 0x1db63932, 0x1d7c2824, 0x53b33681, 0x0673b747, 0x038a98a3,
        0x2c5bce60, 0x351979cd, 0x5008fb73, 0x547bca78, 0x711af481, 0x3f93bf64, 0x644d987b,
        0x3c8bcd87, 0x608758b8,
    ],
];
const RC_INTERNAL: [u32; 13] = [
    0x5a8053c0, 0x693be639, 0x3858867d, 0x19334f6b, 0x128f0fd8, 0x4e2b1ccb, 0x61210ce0, 0x3c318939,
    0x0b5b2f22, 0x2edb11d5, 0x213effdf, 0x0cac4606, 0x241af16d,
];
const INTERNAL_DIAG: [u32; 16] = [
    2013265920, 2, 3, 1006632962, 4, 5, 1006632961, 2013265919, 2013265918, 2005401602, 1509949442,
    1761607682, 2013265907, 7864321, 125829121, 16,
];

#[cfg(test)]
mod slice_message_table_differential {
    use super::*;
    use crate::private_book_relation::{encrypt_private_book, PrivateBookEncryptionOpening};
    use crate::threshold::{KeygenCoordinator, KeygenSession, ThresholdParty};
    use dregg_circuit_prove::dark_bazaar_private::{statement, PrivateBookWitness, PrivateOrder};
    use std::time::Instant;

    #[test]
    fn exact_modulus0_coefficient0_message_table_matches_lean_descriptor() {
        let params = BfvParams::fold_set();
        let session = KeygenSession::from_seed(2, [0x91; 32]).expect("key session");
        let mut coordinator = KeygenCoordinator::new(session.clone(), params.clone());
        for party in 0..session.n_parties() {
            let (_state, contribution) =
                ThresholdParty::join(&session, party, &params).expect("party keygen");
            coordinator
                .accept(contribution)
                .expect("ordered contribution");
        }
        let public_key = coordinator.finish().expect("collective key");
        let table = derive_exact_message_table(&params, &public_key).expect("exact table");
        let values = table.iter().map(|option| option[0][0]).collect::<Vec<_>>();
        const LEAN_MESSAGE_COEFF0: [u64; PRIVATE_BOOK_OPTION_COUNT] = [
            0,
            64737485388,
            60755567768,
            56773650148,
            52791732528,
            48809814908,
            44827897288,
            40845979668,
            36864062048,
            32882144428,
            28900226808,
            24918309188,
            20936391568,
            16954473948,
            12972556328,
            8990638708,
            37735010824,
            2768701020,
            36521794225,
            1555484421,
            35308577626,
            342267822,
            34095361027,
            67848454232,
            32882144428,
            66635237633,
            31668927829,
            65422021034,
            30455711230,
            64208804435,
            29242494631,
            62995587836,
            6750618640,
            9519319661,
            12288020682,
            15056721703,
            17825422724,
            20594123745,
            23362824766,
            26131525787,
            28900226808,
            31668927829,
            34437628850,
            37206329871,
            39975030892,
            42743731913,
            45512432934,
            48281133955,
            44485629465,
            16269938302,
            56773650148,
            28557958985,
            342267822,
            40845979668,
            12630288505,
            53134000351,
            24918309188,
            65422021034,
            37206329871,
            8990638708,
            49494350554,
            21278659391,
            61782371237,
            33566680074,
            13501237281,
            54004949127,
            25789257964,
            66292969810,
            38077278647,
            9861587484,
            50365299330,
            22149608167,
            62653320013,
            34437628850,
            6221937687,
            46725649533,
            18509958370,
            59013670216,
            30797979053,
            2582287890,
            51236248106,
            54004949127,
            56773650148,
            59542351169,
            62311052190,
            65079753211,
            67848454232,
            1897752244,
            4666453265,
            7435154286,
            10203855307,
            12972556328,
            15741257349,
            18509958370,
            21278659391,
            24047360412,
            20251855922,
            54004949127,
            19038639323,
            52791732528,
            17825422724,
            51578515929,
            16612206125,
            50365299330,
            15398989526,
            49152082731,
            14185772927,
            47938866132,
            12972556328,
            46725649533,
            11759339729,
            45512432934,
            57986866747,
            54004949127,
            50023031507,
            46041113887,
            42059196267,
            38077278647,
            34095361027,
            30113443407,
            26131525787,
            22149608167,
            18167690547,
            14185772927,
            10203855307,
            6221937687,
            2240020067,
            66977505456,
        ];
        assert_eq!(values.as_slice(), LEAN_MESSAGE_COEFF0.as_slice());
    }

    #[test]
    fn production_seeded_ring_validation_is_exact_on_selected_backend() {
        let params = BfvParams::fold_set();
        let session = KeygenSession::from_seed(2, [0xA1; 32]).expect("key session");
        let mut coordinator = KeygenCoordinator::new(session.clone(), params.clone());
        for party in 0..session.n_parties() {
            let (_state, contribution) =
                ThresholdParty::join(&session, party, &params).expect("party keygen");
            coordinator
                .accept(contribution)
                .expect("ordered contribution");
        }
        let public_key = coordinator.finish().expect("collective key");
        let witness = PrivateBookWitness::try_from_orders_with_blinding(
            &[
                PrivateOrder::bid(10, 2),
                PrivateOrder::bid(6, 1),
                PrivateOrder::ask(5, 0),
                PrivateOrder::ask(8, 1),
            ],
            core::array::from_fn(|lane| 23_000 + lane as u32),
        )
        .expect("private book");
        let opening = PrivateBookEncryptionOpening::from_seeds([
            [0x71; 32], [0x72; 32], [0x73; 32], [0x74; 32],
        ]);
        let book = statement(0xDBA2, &witness).expect("private statement");
        let ciphertexts =
            encrypt_private_book(&witness, &opening, &params, &public_key).expect("exact BFV book");
        let public = PublicRelation::derive(book, &ciphertexts, &params, &public_key)
            .expect("canonical public relation");
        let secret = SecretRelation::extract(&witness, &opening).expect("seeded short witness");

        // Independent fhe-math production oracle first; the selected portable
        // backend must satisfy the same 98,304 public ciphertext coefficients.
        let reference_started = Instant::now();
        secret
            .validate_seeded_equations_reference(&public)
            .expect("fhe-math seeded equation oracle");
        let reference_elapsed = reference_started.elapsed();
        let require_wgpu = std::env::var_os("DREGG_REQUIRE_WGPU").is_some();
        let engine = if require_wgpu {
            RnsNttEngine::require_wgpu()
        } else {
            RnsNttEngine::cpu_only()
        };
        let initialization_started = Instant::now();
        if require_wgpu {
            assert!(engine.has_gpu(), "RequireWgpu adapter must initialize");
        }
        let initialization_elapsed = initialization_started.elapsed();
        let started = Instant::now();
        let execution = secret
            .validate_seeded_equations_with_engine(&public, &engine)
            .expect("portable seeded equation validation");
        assert_eq!(execution.plan.input_pairs, ORDER_COUNT * 2);
        assert_eq!(execution.plan.rns_rows_per_polynomial, FOLD_MODULI.len());
        assert_eq!(
            execution.plan.total_rns_rows,
            ORDER_COUNT * 2 * FOLD_MODULI.len()
        );
        assert_eq!(execution.plan.degree, FOLD_DEGREE);
        match &execution.backend {
            RnsNttBackend::Wgpu { adapter } => {
                assert!(require_wgpu);
                assert_eq!(
                    execution.plan.gpu_dispatches,
                    2 * FOLD_DEGREE.ilog2() as usize + 5
                );
                assert_eq!(execution.plan.gpu_coefficient_uploads, 2);
                assert!(matches!(execution.plan.gpu_static_table_uploads, 0 | 3));
                assert_eq!(execution.plan.gpu_queue_submissions, 1);
                assert_eq!(execution.plan.gpu_readbacks, 1);
                eprintln!(
                    "production private-book seeded ring validation GREEN on {adapter}: 8 exact u×pk products/98,304 coefficient checks; fhe-math={:.3}ms, adapter+pipelines={:.3}ms, warm-wgpu={:.3}ms",
                    reference_elapsed.as_secs_f64() * 1e3,
                    initialization_elapsed.as_secs_f64() * 1e3,
                    started.elapsed().as_secs_f64() * 1e3,
                );
            }
            RnsNttBackend::CpuPolicy => {
                assert!(!require_wgpu);
                assert_eq!(execution.plan.gpu_dispatches, 0);
                assert_eq!(execution.plan.gpu_queue_submissions, 0);
            }
            backend => panic!("unexpected seeded validation backend: {backend:?}"),
        }
    }
}
