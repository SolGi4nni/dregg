//! Dregg-native collaborative tensor-code and row-folding substrate.
//!
//! This is an independently written CPU reference for the algebraic seam that a
//! collaborative, BaseFold-like PCS needs:
//!
//! * a message is interpreted as a matrix of bivariate-polynomial coefficients;
//! * column evaluation gives each party one typed row share;
//! * public one-party entrypoints evaluate and fold a row without reading any other
//!   row once the all-row digest has been published;
//! * every FRI-style fold is algebraically row-local; and
//! * canonical row-major recombination is byte-for-byte deterministic and agrees
//!   with the centralized tensor-product encoder.
//!
//! Rows use contiguous natural-order two-adic evaluations
//! `f(1), f(g), ..., f(g^(n-1))`. A binary fold pairs `x` with `-x` and computes
//! `f_even(x^2) + beta * f_odd(x^2)`. This is deliberately a simple, inspectable
//! convention; Plonky3's deployed storage uses bit-reversed layouts in several
//! places, so a future backend adapter must transpose explicitly rather than
//! claiming the layouts are identical.
//!
//! # Security boundary (important)
//!
//! This module is **not a PCS, IOPP, SNARK, or production BaseFold prover**. It has
//! no Merkle/MMCS openings, proximity queries, sumcheck, soundness reduction, or
//! proof verification. [`column_encode_party_shares`] is a deterministic reference
//! and supplies algebraic *support shares*, not private Shamir shares. It provides
//! no witness privacy or zero knowledge. A private construction still needs the
//! randomized packed-sharing and query-masking protocol, with its threshold and
//! leakage proof.
//!
//! The coordinator checks shapes, party-index labels, ordering, and transcript
//! binding, but party indexes are not authenticated identities: one sender can
//! impersonate every label. It also does not prove that a malicious party encoded
//! its assigned input honestly. There is no authenticated transport, Byzantine
//! broadcast, malicious-secure MPC compiler, blame/accountability, dropout
//! recovery, or availability protocol. BLAKE3 gives this prototype a
//! domain-separated deterministic transcript; this module makes no standalone
//! Fiat-Shamir, random-oracle, or post-quantum proof-system claim. Those are named
//! construction obligations, not properties inherited merely by using a hash.
//! Challenges live in the BabyBear base field; a production soundness ledger must
//! also decide and account for an extension-field challenge construction.
//!
//! The vectors are contiguous and party-row-major so the same contract can later
//! back a WGPU buffer. This implementation is CPU-only and makes no performance
//! claim.

use core::fmt;

use p3_baby_bear::BabyBear;
use p3_field::{Field, PrimeCharacteristicRing, PrimeField32, PrimeField64, TwoAdicField};

/// Domain separator for tensor-code state digests.
pub const STATE_DIGEST_DOMAIN_V1: &[u8] = b"dregg.native.collaborative-basefold.state.v1\0";

/// Domain separator for fold challenges.
pub const FOLD_TRANSCRIPT_DOMAIN_V1: &[u8] = b"dregg.native.collaborative-basefold.transcript.v1\0";

/// Maximum two-adic domain supported by BabyBear.
const MAX_TWO_ADICITY: usize = 27;

/// Fail-closed protocol and geometry errors.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CollaborativeBasefoldError {
    /// Every tensor dimension must be non-zero.
    ZeroDimension { dimension: &'static str },
    /// Encoded domains must be powers of two.
    NonPowerOfTwoDomain {
        dimension: &'static str,
        value: usize,
    },
    /// BabyBear has no two-adic subgroup this large.
    DomainExceedsBabyBear {
        dimension: &'static str,
        value: usize,
    },
    /// A code dimension cannot be smaller than its coefficient dimension.
    MessageExceedsCode {
        dimension: &'static str,
        message: usize,
        encoded: usize,
    },
    /// Multiplying matrix dimensions overflowed `usize`.
    ShapeOverflow,
    /// A centralized message did not carry exactly the declared matrix.
    WrongMessageLength { expected: usize, actual: usize },
    /// A distributed round omitted or appended party rows.
    WrongPartyCount { expected: usize, actual: usize },
    /// A party identifier is not in the declared range.
    PartyOutOfRange { party: usize, party_count: usize },
    /// A party supplied more than one row.
    DuplicateParty { party: usize },
    /// Network inputs must arrive in committed party-id order; they are never
    /// silently sorted because order is part of the transcript.
    ReorderedParty {
        position: usize,
        expected: usize,
        actual: usize,
    },
    /// A party share did not carry one coefficient per message column.
    WrongShareWidth {
        party: usize,
        expected: usize,
        actual: usize,
    },
    /// An encoded/folded party row has the wrong width.
    WrongRowWidth {
        party: usize,
        expected: usize,
        actual: usize,
    },
    /// The claimed round and row width do not descend canonically from the
    /// original encoded width.
    RoundShapeMismatch {
        round: usize,
        expected_columns: usize,
        actual_columns: usize,
    },
    /// A one-column row cannot be folded further.
    FinalRowCannotFold,
    /// The challenge came from a different statement, state, width, or round.
    FoldChallengeMismatch,
    /// A centralized reference fold was given a challenge for another round.
    ReferenceRoundMismatch { expected: usize, actual: usize },
}

impl fmt::Display for CollaborativeBasefoldError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ZeroDimension { dimension } => {
                write!(f, "tensor dimension {dimension} must be non-zero")
            }
            Self::NonPowerOfTwoDomain { dimension, value } => write!(
                f,
                "encoded {dimension} domain {value} must be a power of two"
            ),
            Self::DomainExceedsBabyBear { dimension, value } => write!(
                f,
                "encoded {dimension} domain {value} exceeds BabyBear two-adicity {MAX_TWO_ADICITY}"
            ),
            Self::MessageExceedsCode {
                dimension,
                message,
                encoded,
            } => write!(
                f,
                "message {dimension} dimension {message} exceeds encoded dimension {encoded}"
            ),
            Self::ShapeOverflow => f.write_str("tensor shape multiplication overflowed usize"),
            Self::WrongMessageLength { expected, actual } => write!(
                f,
                "centralized message has {actual} coefficients, expected {expected}"
            ),
            Self::WrongPartyCount { expected, actual } => {
                write!(f, "received {actual} party rows, expected {expected}")
            }
            Self::PartyOutOfRange { party, party_count } => write!(
                f,
                "party {party} is outside declared party range 0..{party_count}"
            ),
            Self::DuplicateParty { party } => {
                write!(f, "party {party} supplied more than one row")
            }
            Self::ReorderedParty {
                position,
                expected,
                actual,
            } => write!(
                f,
                "party-row position {position} carries party {actual}, expected {expected}"
            ),
            Self::WrongShareWidth {
                party,
                expected,
                actual,
            } => write!(
                f,
                "party {party} share has width {actual}, expected {expected}"
            ),
            Self::WrongRowWidth {
                party,
                expected,
                actual,
            } => write!(
                f,
                "party {party} encoded row has width {actual}, expected {expected}"
            ),
            Self::RoundShapeMismatch {
                round,
                expected_columns,
                actual_columns,
            } => write!(
                f,
                "fold round {round} requires {expected_columns} columns, received {actual_columns}"
            ),
            Self::FinalRowCannotFold => f.write_str("a one-column row cannot be folded further"),
            Self::FoldChallengeMismatch => f.write_str(
                "fold challenge is not bound to this statement, state, width, and round",
            ),
            Self::ReferenceRoundMismatch { expected, actual } => write!(
                f,
                "reference fold is at round {expected}, challenge is for round {actual}"
            ),
        }
    }
}

impl std::error::Error for CollaborativeBasefoldError {}

/// Validated tensor-code geometry.
///
/// The encoded row count is also the exact party count: party `i` owns encoded
/// tensor row `i`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TensorCodeShape {
    message_rows: usize,
    message_columns: usize,
    party_count: usize,
    encoded_columns: usize,
}

impl TensorCodeShape {
    /// Validate a tensor-product RS geometry.
    pub fn new(
        message_rows: usize,
        message_columns: usize,
        party_count: usize,
        encoded_columns: usize,
    ) -> Result<Self, CollaborativeBasefoldError> {
        for (dimension, value) in [
            ("message rows", message_rows),
            ("message columns", message_columns),
            ("party rows", party_count),
            ("code columns", encoded_columns),
        ] {
            if value == 0 {
                return Err(CollaborativeBasefoldError::ZeroDimension { dimension });
            }
        }
        for (dimension, value) in [("party-row", party_count), ("column", encoded_columns)] {
            if !value.is_power_of_two() {
                return Err(CollaborativeBasefoldError::NonPowerOfTwoDomain { dimension, value });
            }
            if value.ilog2() as usize > MAX_TWO_ADICITY {
                return Err(CollaborativeBasefoldError::DomainExceedsBabyBear { dimension, value });
            }
        }
        if message_rows > party_count {
            return Err(CollaborativeBasefoldError::MessageExceedsCode {
                dimension: "row",
                message: message_rows,
                encoded: party_count,
            });
        }
        if message_columns > encoded_columns {
            return Err(CollaborativeBasefoldError::MessageExceedsCode {
                dimension: "column",
                message: message_columns,
                encoded: encoded_columns,
            });
        }
        message_rows
            .checked_mul(message_columns)
            .and_then(|_| party_count.checked_mul(encoded_columns))
            .ok_or(CollaborativeBasefoldError::ShapeOverflow)?;
        Ok(Self {
            message_rows,
            message_columns,
            party_count,
            encoded_columns,
        })
    }

    /// Number of coefficient rows in the unencoded message.
    pub const fn message_rows(self) -> usize {
        self.message_rows
    }

    /// Number of coefficient columns in the unencoded message.
    pub const fn message_columns(self) -> usize {
        self.message_columns
    }

    /// Number of parties and encoded tensor rows.
    pub const fn party_count(self) -> usize {
        self.party_count
    }

    /// Number of encoded evaluations in every initial party row.
    pub const fn encoded_columns(self) -> usize {
        self.encoded_columns
    }

    fn message_len(self) -> Result<usize, CollaborativeBasefoldError> {
        self.message_rows
            .checked_mul(self.message_columns)
            .ok_or(CollaborativeBasefoldError::ShapeOverflow)
    }

    fn encoded_len(self) -> Result<usize, CollaborativeBasefoldError> {
        self.party_count
            .checked_mul(self.encoded_columns)
            .ok_or(CollaborativeBasefoldError::ShapeOverflow)
    }

    fn expected_columns_at_round(self, round: usize) -> Result<usize, CollaborativeBasefoldError> {
        let max_round = self.encoded_columns.ilog2() as usize;
        if round > max_round {
            return Err(CollaborativeBasefoldError::RoundShapeMismatch {
                round,
                expected_columns: 0,
                actual_columns: 0,
            });
        }
        Ok(self.encoded_columns >> round)
    }

    fn absorb(self, hasher: &mut blake3::Hasher) {
        for value in [
            self.message_rows,
            self.message_columns,
            self.party_count,
            self.encoded_columns,
        ] {
            hasher.update(&(value as u64).to_le_bytes());
        }
    }
}

/// Strong party-row identifier.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PartyIndex(usize);

impl PartyIndex {
    /// Construct an identifier. Geometry validation happens when it enters a round.
    pub const fn new(index: usize) -> Self {
        Self(index)
    }

    /// Canonical numeric identifier.
    pub const fn get(self) -> usize {
        self.0
    }
}

/// One party's row after the tensor's column-encoding phase.
///
/// The row contains coefficients for that party's row polynomial. It is a typed
/// algebraic share, but this type alone makes no privacy claim.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PartyShareInput {
    party: PartyIndex,
    row_coefficients: Vec<BabyBear>,
}

impl PartyShareInput {
    /// Wrap a received party share. The collaborative encoder validates the
    /// numeric row label and exact width, not the sender's identity.
    pub fn from_untrusted(party: PartyIndex, row_coefficients: Vec<BabyBear>) -> Self {
        Self {
            party,
            row_coefficients,
        }
    }

    /// Party that owns the row.
    pub const fn party(&self) -> PartyIndex {
        self.party
    }

    /// Contiguous row-polynomial coefficients.
    pub fn row_coefficients(&self) -> &[BabyBear] {
        &self.row_coefficients
    }
}

/// One party-local encoded or folded row.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PartyEncodedRow {
    party: PartyIndex,
    values: Vec<BabyBear>,
}

impl PartyEncodedRow {
    /// Wrap an untrusted network row. [`DistributedTensorCodeword::from_party_rows`]
    /// performs the exact-set/order/shape validation.
    pub fn from_untrusted(party: PartyIndex, values: Vec<BabyBear>) -> Self {
        Self { party, values }
    }

    /// Party that owns this row.
    pub const fn party(&self) -> PartyIndex {
        self.party
    }

    /// Contiguous natural-order evaluation row.
    pub fn values(&self) -> &[BabyBear] {
        &self.values
    }
}

/// A complete distributed tensor-code or fold-round state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DistributedTensorCodeword {
    shape: TensorCodeShape,
    round: usize,
    columns: usize,
    rows: Vec<PartyEncodedRow>,
}

impl DistributedTensorCodeword {
    /// Validate a complete party-row set reconstructed from network messages.
    pub fn from_party_rows(
        shape: TensorCodeShape,
        round: usize,
        columns: usize,
        rows: Vec<PartyEncodedRow>,
    ) -> Result<Self, CollaborativeBasefoldError> {
        let expected_columns = shape.expected_columns_at_round(round)?;
        if columns != expected_columns || columns == 0 {
            return Err(CollaborativeBasefoldError::RoundShapeMismatch {
                round,
                expected_columns,
                actual_columns: columns,
            });
        }
        validate_party_rows(shape.party_count, columns, &rows)?;
        Ok(Self {
            shape,
            round,
            columns,
            rows,
        })
    }

    /// Original tensor-code geometry.
    pub const fn shape(&self) -> TensorCodeShape {
        self.shape
    }

    /// Number of completed binary folds.
    pub const fn round(&self) -> usize {
        self.round
    }

    /// Current contiguous row width.
    pub const fn columns(&self) -> usize {
        self.columns
    }

    /// Canonically ordered party rows.
    pub fn party_rows(&self) -> &[PartyEncodedRow] {
        &self.rows
    }

    /// Domain-separated digest of all shape, round, identity, and field data.
    ///
    /// This is a transcript input, not a PCS commitment or availability proof.
    pub fn state_digest(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(STATE_DIGEST_DOMAIN_V1);
        self.shape.absorb(&mut hasher);
        hasher.update(&(self.round as u64).to_le_bytes());
        hasher.update(&(self.columns as u64).to_le_bytes());
        for row in &self.rows {
            hasher.update(&(row.party.get() as u64).to_le_bytes());
            hasher.update(&(row.values.len() as u64).to_le_bytes());
            for value in &row.values {
                hasher.update(&value.as_canonical_u32().to_le_bytes());
            }
        }
        *hasher.finalize().as_bytes()
    }

    /// Recombine party rows into canonical contiguous row-major storage.
    pub fn recombine(&self) -> Result<RecombinedCodeword, CollaborativeBasefoldError> {
        validate_party_rows(self.shape.party_count, self.columns, &self.rows)?;
        let capacity = self
            .shape
            .party_count
            .checked_mul(self.columns)
            .ok_or(CollaborativeBasefoldError::ShapeOverflow)?;
        let mut values = Vec::with_capacity(capacity);
        for row in &self.rows {
            values.extend_from_slice(&row.values);
        }
        Ok(RecombinedCodeword {
            party_count: self.shape.party_count,
            round: self.round,
            columns: self.columns,
            values,
        })
    }

    /// Perform one challenge-bound fold independently on every party row.
    pub fn fold(
        &self,
        transcript: &CollaborativeFoldTranscript,
        supplied: &FoldChallenge,
    ) -> Result<Self, CollaborativeBasefoldError> {
        if self.columns == 1 {
            return Err(CollaborativeBasefoldError::FinalRowCannotFold);
        }
        let expected = transcript.challenge(self);
        if &expected != supplied {
            return Err(CollaborativeBasefoldError::FoldChallengeMismatch);
        }
        let published_digest = self.state_digest();
        let next_columns = self.columns / 2;
        let rows = self
            .rows
            .iter()
            .map(|row| {
                fold_party_row_local(
                    self.shape,
                    self.round,
                    self.columns,
                    row,
                    transcript,
                    published_digest,
                    supplied,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        Self::from_party_rows(self.shape, self.round + 1, next_columns, rows)
    }
}

/// Canonically recombined row-major field storage.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RecombinedCodeword {
    party_count: usize,
    round: usize,
    columns: usize,
    values: Vec<BabyBear>,
}

impl RecombinedCodeword {
    /// Number of encoded tensor rows.
    pub const fn party_count(&self) -> usize {
        self.party_count
    }

    /// Number of completed folds.
    pub const fn round(&self) -> usize {
        self.round
    }

    /// Number of contiguous values per row.
    pub const fn columns(&self) -> usize {
        self.columns
    }

    /// Row-major contiguous values, suitable for a future GPU upload.
    pub fn values(&self) -> &[BabyBear] {
        &self.values
    }
}

/// Statement/session-bound transcript context.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CollaborativeFoldTranscript {
    statement_digest: [u8; 32],
    context_digest: [u8; 32],
}

impl CollaborativeFoldTranscript {
    /// Bind challenges to an exact public statement and caller-defined protocol
    /// context (for example, game session plus descriptor identity).
    pub fn new(statement_digest: [u8; 32], context: &[u8]) -> Self {
        let mut context_hasher = blake3::Hasher::new();
        context_hasher.update(FOLD_TRANSCRIPT_DOMAIN_V1);
        context_hasher.update(b"context\0");
        context_hasher.update(&(context.len() as u64).to_le_bytes());
        context_hasher.update(context);
        Self {
            statement_digest,
            context_digest: *context_hasher.finalize().as_bytes(),
        }
    }

    /// Derive the unique challenge for this complete distributed state.
    pub fn challenge(&self, state: &DistributedTensorCodeword) -> FoldChallenge {
        self.challenge_for_published_digest(
            state.shape,
            state.round,
            state.columns,
            state.state_digest(),
        )
        .expect("a validated distributed state has canonical fold geometry")
    }

    /// Derive a challenge from a published all-row digest without reading the rows.
    ///
    /// This is the party-local transcript entrypoint. In this prototype the digest
    /// can be [`DistributedTensorCodeword::state_digest`]; it is not yet a Merkle/MMCS
    /// commitment, so a party still needs the future commitment/opening layer to
    /// establish that the published digest includes its own row and is available.
    pub fn challenge_for_published_digest(
        &self,
        shape: TensorCodeShape,
        round: usize,
        columns: usize,
        state_digest: [u8; 32],
    ) -> Result<FoldChallenge, CollaborativeBasefoldError> {
        let expected_columns = shape.expected_columns_at_round(round)?;
        if columns != expected_columns || columns == 0 {
            return Err(CollaborativeBasefoldError::RoundShapeMismatch {
                round,
                expected_columns,
                actual_columns: columns,
            });
        }
        let mut binding_hasher = blake3::Hasher::new();
        binding_hasher.update(FOLD_TRANSCRIPT_DOMAIN_V1);
        binding_hasher.update(b"fold-binding\0");
        binding_hasher.update(&self.statement_digest);
        binding_hasher.update(&self.context_digest);
        binding_hasher.update(&state_digest);
        shape.absorb(&mut binding_hasher);
        binding_hasher.update(&(round as u64).to_le_bytes());
        binding_hasher.update(&(columns as u64).to_le_bytes());
        let binding = *binding_hasher.finalize().as_bytes();

        Ok(FoldChallenge {
            round,
            state_digest,
            binding,
            value: sample_babybear(binding),
        })
    }
}

/// A challenge tied to one exact distributed fold state.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FoldChallenge {
    round: usize,
    state_digest: [u8; 32],
    binding: [u8; 32],
    value: BabyBear,
}

impl FoldChallenge {
    /// Round this challenge advances.
    pub const fn round(self) -> usize {
        self.round
    }

    /// State digest to which the challenge is bound.
    pub const fn state_digest(self) -> [u8; 32] {
        self.state_digest
    }

    /// Full transcript binding digest.
    pub const fn binding(self) -> [u8; 32] {
        self.binding
    }

    /// Base-field fold challenge.
    pub const fn value(self) -> BabyBear {
        self.value
    }
}

/// Deterministically perform the tensor's column-encoding phase.
///
/// This is the centralized reference/oracle used to pin recombination. It sees the
/// full message and therefore must not be mistaken for a private deployment path.
pub fn column_encode_party_shares(
    shape: TensorCodeShape,
    message_coefficients: &[BabyBear],
) -> Result<Vec<PartyShareInput>, CollaborativeBasefoldError> {
    let expected = shape.message_len()?;
    if message_coefficients.len() != expected {
        return Err(CollaborativeBasefoldError::WrongMessageLength {
            expected,
            actual: message_coefficients.len(),
        });
    }

    let row_generator = BabyBear::two_adic_generator(shape.party_count.ilog2() as usize);
    let mut x = BabyBear::ONE;
    let mut shares = Vec::with_capacity(shape.party_count);
    for party in 0..shape.party_count {
        let mut row_coefficients = Vec::with_capacity(shape.message_columns);
        for column in 0..shape.message_columns {
            let coefficients = (0..shape.message_rows)
                .map(|row| message_coefficients[row * shape.message_columns + column]);
            row_coefficients.push(evaluate_coefficients(coefficients, x));
        }
        shares.push(PartyShareInput {
            party: PartyIndex(party),
            row_coefficients,
        });
        x *= row_generator;
    }
    Ok(shares)
}

/// Encode one party share without reading any other party's row.
pub fn encode_party_share_local(
    shape: TensorCodeShape,
    share: &PartyShareInput,
) -> Result<PartyEncodedRow, CollaborativeBasefoldError> {
    validate_party_share(shape, share)?;
    Ok(PartyEncodedRow {
        party: share.party,
        values: evaluate_on_two_adic_domain(&share.row_coefficients, shape.encoded_columns),
    })
}

/// Row-encode a complete, exact party-share set with no inter-party arithmetic.
///
/// This coordinator convenience validates the exact party set, then invokes the
/// same public one-party entrypoint each prover can run in its own process.
pub fn collaborative_tensor_encode(
    shape: TensorCodeShape,
    shares: &[PartyShareInput],
) -> Result<DistributedTensorCodeword, CollaborativeBasefoldError> {
    validate_party_shares(shape, shares)?;
    let rows = shares
        .iter()
        .map(|share| encode_party_share_local(shape, share))
        .collect::<Result<Vec<_>, _>>()?;
    DistributedTensorCodeword::from_party_rows(shape, 0, shape.encoded_columns, rows)
}

/// Centralized tensor-product RS reference.
///
/// The result must equal `collaborative_tensor_encode(column_encode_party_shares(...)).recombine()`.
pub fn centralized_tensor_encode(
    shape: TensorCodeShape,
    message_coefficients: &[BabyBear],
) -> Result<RecombinedCodeword, CollaborativeBasefoldError> {
    let expected = shape.message_len()?;
    if message_coefficients.len() != expected {
        return Err(CollaborativeBasefoldError::WrongMessageLength {
            expected,
            actual: message_coefficients.len(),
        });
    }

    // Independent direct bivariate evaluation. This deliberately does not call
    // the column-share or party-row encoders, so the equivalence test catches an
    // axis swap or inconsistent party/domain indexing in that pipeline.
    let row_generator = BabyBear::two_adic_generator(shape.party_count.ilog2() as usize);
    let column_generator = BabyBear::two_adic_generator(shape.encoded_columns.ilog2() as usize);
    let mut values = Vec::with_capacity(shape.encoded_len()?);
    let mut x = BabyBear::ONE;
    for _party in 0..shape.party_count {
        let mut y = BabyBear::ONE;
        for _column in 0..shape.encoded_columns {
            let mut x_power = BabyBear::ONE;
            let mut evaluation = BabyBear::ZERO;
            for message_row in 0..shape.message_rows {
                let mut y_power = BabyBear::ONE;
                for message_column in 0..shape.message_columns {
                    evaluation += message_coefficients
                        [message_row * shape.message_columns + message_column]
                        * x_power
                        * y_power;
                    y_power *= y;
                }
                x_power *= x;
            }
            values.push(evaluation);
            y *= column_generator;
        }
        x *= row_generator;
    }
    Ok(RecombinedCodeword {
        party_count: shape.party_count,
        round: 0,
        columns: shape.encoded_columns,
        values,
    })
}

/// Centralized algebraic oracle for one row-local fold.
///
/// This checks round/shape but intentionally does not replace the transcript check
/// on [`DistributedTensorCodeword::fold`].
pub fn fold_recombined_reference(
    input: &RecombinedCodeword,
    challenge: &FoldChallenge,
) -> Result<RecombinedCodeword, CollaborativeBasefoldError> {
    if input.round != challenge.round {
        return Err(CollaborativeBasefoldError::ReferenceRoundMismatch {
            expected: input.round,
            actual: challenge.round,
        });
    }
    if input.columns == 1 {
        return Err(CollaborativeBasefoldError::FinalRowCannotFold);
    }
    let next_columns = input.columns / 2;
    let mut values = Vec::with_capacity(input.party_count * next_columns);
    for row in input.values.chunks_exact(input.columns) {
        // Independent coefficient-domain oracle: inverse DFT the complete row,
        // fold even/odd coefficients, then directly evaluate the result on the
        // descended domain. It shares no folding helper with the party path.
        let coefficients = inverse_two_adic_dft(row);
        let folded_coefficients: Vec<_> = (0..next_columns)
            .map(|i| coefficients[2 * i] + challenge.value * coefficients[2 * i + 1])
            .collect();
        let generator = BabyBear::two_adic_generator(next_columns.ilog2() as usize);
        let mut point = BabyBear::ONE;
        for _ in 0..next_columns {
            let mut power = BabyBear::ONE;
            let mut evaluation = BabyBear::ZERO;
            for coefficient in &folded_coefficients {
                evaluation += *coefficient * power;
                power *= point;
            }
            values.push(evaluation);
            point *= generator;
        }
    }
    Ok(RecombinedCodeword {
        party_count: input.party_count,
        round: input.round + 1,
        columns: next_columns,
        values,
    })
}

/// Fold one party row without reading any other party's row.
///
/// The party checks local shape and independently re-derives the challenge from
/// the public statement/context plus the published all-row digest. This does not
/// establish that the digest includes the party row; that is the future MMCS
/// opening/availability obligation described on
/// [`CollaborativeFoldTranscript::challenge_for_published_digest`].
pub fn fold_party_row_local(
    shape: TensorCodeShape,
    round: usize,
    columns: usize,
    row: &PartyEncodedRow,
    transcript: &CollaborativeFoldTranscript,
    published_digest: [u8; 32],
    challenge: &FoldChallenge,
) -> Result<PartyEncodedRow, CollaborativeBasefoldError> {
    let expected_columns = shape.expected_columns_at_round(round)?;
    if columns != expected_columns || columns == 0 {
        return Err(CollaborativeBasefoldError::RoundShapeMismatch {
            round,
            expected_columns,
            actual_columns: columns,
        });
    }
    let expected_challenge =
        transcript.challenge_for_published_digest(shape, round, columns, published_digest)?;
    if &expected_challenge != challenge {
        return Err(CollaborativeBasefoldError::FoldChallengeMismatch);
    }
    validate_party_row(shape.party_count, columns, row)?;
    if columns == 1 {
        return Err(CollaborativeBasefoldError::FinalRowCannotFold);
    }
    Ok(PartyEncodedRow {
        party: row.party,
        values: fold_natural_two_adic_row(&row.values, challenge.value),
    })
}

fn validate_party_shares(
    shape: TensorCodeShape,
    shares: &[PartyShareInput],
) -> Result<(), CollaborativeBasefoldError> {
    if shares.len() != shape.party_count {
        return Err(CollaborativeBasefoldError::WrongPartyCount {
            expected: shape.party_count,
            actual: shares.len(),
        });
    }
    let mut seen = vec![false; shape.party_count];
    for share in shares {
        let party = share.party.get();
        if party >= shape.party_count {
            return Err(CollaborativeBasefoldError::PartyOutOfRange {
                party,
                party_count: shape.party_count,
            });
        }
        if core::mem::replace(&mut seen[party], true) {
            return Err(CollaborativeBasefoldError::DuplicateParty { party });
        }
    }
    for (position, share) in shares.iter().enumerate() {
        let party = share.party.get();
        if party != position {
            return Err(CollaborativeBasefoldError::ReorderedParty {
                position,
                expected: position,
                actual: party,
            });
        }
        if share.row_coefficients.len() != shape.message_columns {
            return Err(CollaborativeBasefoldError::WrongShareWidth {
                party,
                expected: shape.message_columns,
                actual: share.row_coefficients.len(),
            });
        }
    }
    Ok(())
}

fn validate_party_share(
    shape: TensorCodeShape,
    share: &PartyShareInput,
) -> Result<(), CollaborativeBasefoldError> {
    let party = share.party.get();
    if party >= shape.party_count {
        return Err(CollaborativeBasefoldError::PartyOutOfRange {
            party,
            party_count: shape.party_count,
        });
    }
    if share.row_coefficients.len() != shape.message_columns {
        return Err(CollaborativeBasefoldError::WrongShareWidth {
            party,
            expected: shape.message_columns,
            actual: share.row_coefficients.len(),
        });
    }
    Ok(())
}

fn validate_party_rows(
    party_count: usize,
    columns: usize,
    rows: &[PartyEncodedRow],
) -> Result<(), CollaborativeBasefoldError> {
    if rows.len() != party_count {
        return Err(CollaborativeBasefoldError::WrongPartyCount {
            expected: party_count,
            actual: rows.len(),
        });
    }
    let mut seen = vec![false; party_count];
    for row in rows {
        let party = row.party.get();
        if party >= party_count {
            return Err(CollaborativeBasefoldError::PartyOutOfRange { party, party_count });
        }
        if core::mem::replace(&mut seen[party], true) {
            return Err(CollaborativeBasefoldError::DuplicateParty { party });
        }
    }
    for (position, row) in rows.iter().enumerate() {
        let party = row.party.get();
        if party != position {
            return Err(CollaborativeBasefoldError::ReorderedParty {
                position,
                expected: position,
                actual: party,
            });
        }
        if row.values.len() != columns {
            return Err(CollaborativeBasefoldError::WrongRowWidth {
                party,
                expected: columns,
                actual: row.values.len(),
            });
        }
    }
    Ok(())
}

fn validate_party_row(
    party_count: usize,
    columns: usize,
    row: &PartyEncodedRow,
) -> Result<(), CollaborativeBasefoldError> {
    let party = row.party.get();
    if party >= party_count {
        return Err(CollaborativeBasefoldError::PartyOutOfRange { party, party_count });
    }
    if row.values.len() != columns {
        return Err(CollaborativeBasefoldError::WrongRowWidth {
            party,
            expected: columns,
            actual: row.values.len(),
        });
    }
    Ok(())
}

fn evaluate_coefficients(
    coefficients: impl DoubleEndedIterator<Item = BabyBear>,
    point: BabyBear,
) -> BabyBear {
    coefficients
        .rev()
        .fold(BabyBear::ZERO, |acc, coefficient| acc * point + coefficient)
}

fn evaluate_on_two_adic_domain(coefficients: &[BabyBear], domain_size: usize) -> Vec<BabyBear> {
    let generator = BabyBear::two_adic_generator(domain_size.ilog2() as usize);
    let mut point = BabyBear::ONE;
    let mut evaluations = Vec::with_capacity(domain_size);
    for _ in 0..domain_size {
        evaluations.push(evaluate_coefficients(coefficients.iter().copied(), point));
        point *= generator;
    }
    evaluations
}

/// Quadratic-time inverse DFT used only by the independent CPU test oracle.
fn inverse_two_adic_dft(evaluations: &[BabyBear]) -> Vec<BabyBear> {
    debug_assert!(evaluations.len().is_power_of_two() && !evaluations.is_empty());
    let generator = BabyBear::two_adic_generator(evaluations.len().ilog2() as usize);
    let generator_inverse = generator.inverse();
    let size_inverse = BabyBear::new(evaluations.len() as u32).inverse();
    let mut coefficients = Vec::with_capacity(evaluations.len());
    for coefficient_index in 0..evaluations.len() {
        let step = generator_inverse.exp_u64(coefficient_index as u64);
        let mut power = BabyBear::ONE;
        let mut sum = BabyBear::ZERO;
        for evaluation in evaluations {
            sum += *evaluation * power;
            power *= step;
        }
        coefficients.push(sum * size_inverse);
    }
    coefficients
}

/// Natural-order binary FRI fold over a complete two-adic evaluation row.
fn fold_natural_two_adic_row(row: &[BabyBear], beta: BabyBear) -> Vec<BabyBear> {
    debug_assert!(row.len().is_power_of_two() && row.len() > 1);
    let half = row.len() / 2;
    let generator = BabyBear::two_adic_generator(row.len().ilog2() as usize);
    let inv_two = (BabyBear::ONE + BabyBear::ONE).inverse();
    let mut x = BabyBear::ONE;
    let mut folded = Vec::with_capacity(half);
    for i in 0..half {
        let lo = row[i];
        let hi = row[i + half];
        let even = (lo + hi) * inv_two;
        let odd = (lo - hi) * inv_two * x.inverse();
        folded.push(even + beta * odd);
        x *= generator;
    }
    folded
}

/// Uniformly map a transcript binding to BabyBear using rejection sampling.
fn sample_babybear(binding: [u8; 32]) -> BabyBear {
    let modulus = BabyBear::ORDER_U64 as u128;
    let bound = ((u64::MAX as u128 + 1) / modulus) * modulus;
    let mut hasher = blake3::Hasher::new();
    hasher.update(FOLD_TRANSCRIPT_DOMAIN_V1);
    hasher.update(b"field-challenge\0");
    hasher.update(&binding);
    let mut reader = hasher.finalize_xof();
    loop {
        let mut bytes = [0u8; 8];
        reader.fill(&mut bytes);
        let candidate = u64::from_le_bytes(bytes);
        if (candidate as u128) < bound {
            return BabyBear::new((candidate % BabyBear::ORDER_U64) as u32);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn shape() -> TensorCodeShape {
        TensorCodeShape::new(3, 3, 4, 8).unwrap()
    }

    fn message() -> Vec<BabyBear> {
        (0..9).map(|i| BabyBear::new((17 * i + 3) as u32)).collect()
    }

    fn encoded() -> DistributedTensorCodeword {
        let shape = shape();
        let shares = column_encode_party_shares(shape, &message()).unwrap();
        collaborative_tensor_encode(shape, &shares).unwrap()
    }

    #[test]
    fn collaborative_recombination_matches_central_tensor_reference() {
        let shape = shape();
        let message = message();
        let shares = column_encode_party_shares(shape, &message).unwrap();
        let distributed = collaborative_tensor_encode(shape, &shares).unwrap();
        let recombined = distributed.recombine().unwrap();
        let centralized = centralized_tensor_encode(shape, &message).unwrap();

        assert_eq!(recombined, centralized);
        assert_eq!(recombined.values().len(), 4 * 8);
        for (party, row) in distributed.party_rows().iter().enumerate() {
            assert_eq!(row.party(), PartyIndex::new(party));
            assert_eq!(
                encode_party_share_local(shape, &shares[party]).unwrap(),
                row.clone()
            );
            assert_eq!(
                row.values(),
                &recombined.values()[party * 8..(party + 1) * 8]
            );
        }
    }

    #[test]
    fn every_party_folds_locally_and_matches_centralized_oracle() {
        let state = encoded();
        let transcript = CollaborativeFoldTranscript::new([0x42; 32], b"dark-bazaar/session-19");
        let challenge = transcript.challenge(&state);
        let central_before = state.recombine().unwrap();

        let distributed_after = state.fold(&transcript, &challenge).unwrap();
        let central_after = fold_recombined_reference(&central_before, &challenge).unwrap();
        assert_eq!(distributed_after.recombine().unwrap(), central_after);
        for (before, after) in state
            .party_rows()
            .iter()
            .zip(distributed_after.party_rows())
        {
            assert_eq!(
                fold_party_row_local(
                    state.shape(),
                    0,
                    8,
                    before,
                    &transcript,
                    state.state_digest(),
                    &challenge,
                )
                .unwrap(),
                after.clone()
            );
        }
        assert_eq!(distributed_after.round(), 1);
        assert_eq!(distributed_after.columns(), 4);

        // A second round exercises the descended two-adic domain.
        let challenge2 = transcript.challenge(&distributed_after);
        let twice = distributed_after.fold(&transcript, &challenge2).unwrap();
        assert_eq!(twice.columns(), 2);
        assert_eq!(twice.round(), 2);
    }

    #[test]
    fn fold_matches_even_odd_coefficient_polynomial() {
        let coefficients: Vec<BabyBear> = (1..=6).map(BabyBear::new).collect();
        let evaluations = evaluate_on_two_adic_domain(&coefficients, 8);
        let beta = BabyBear::new(71);
        let folded = fold_natural_two_adic_row(&evaluations, beta);

        let even: Vec<_> = coefficients.iter().step_by(2).copied().collect();
        let odd: Vec<_> = coefficients.iter().skip(1).step_by(2).copied().collect();
        let folded_coefficients: Vec<_> = (0..even.len().max(odd.len()))
            .map(|i| {
                even.get(i).copied().unwrap_or(BabyBear::ZERO)
                    + beta * odd.get(i).copied().unwrap_or(BabyBear::ZERO)
            })
            .collect();
        assert_eq!(folded, evaluate_on_two_adic_domain(&folded_coefficients, 4));
    }

    #[test]
    fn omission_duplicate_and_reorder_fail_closed() {
        let shape = shape();
        let shares = column_encode_party_shares(shape, &message()).unwrap();

        let omitted = &shares[..shares.len() - 1];
        assert_eq!(
            collaborative_tensor_encode(shape, omitted),
            Err(CollaborativeBasefoldError::WrongPartyCount {
                expected: 4,
                actual: 3,
            })
        );

        let mut duplicate = shares.clone();
        duplicate[3] = duplicate[2].clone();
        assert_eq!(
            collaborative_tensor_encode(shape, &duplicate),
            Err(CollaborativeBasefoldError::DuplicateParty { party: 2 })
        );

        let mut reordered = shares.clone();
        reordered.swap(1, 2);
        assert_eq!(
            collaborative_tensor_encode(shape, &reordered),
            Err(CollaborativeBasefoldError::ReorderedParty {
                position: 1,
                expected: 1,
                actual: 2,
            })
        );

        let mut out_of_range = shares;
        out_of_range[3].party = PartyIndex::new(4);
        assert_eq!(
            collaborative_tensor_encode(shape, &out_of_range),
            Err(CollaborativeBasefoldError::PartyOutOfRange {
                party: 4,
                party_count: 4,
            })
        );
    }

    #[test]
    fn wrong_share_row_and_round_shapes_fail_closed() {
        let shape = shape();
        let mut shares = column_encode_party_shares(shape, &message()).unwrap();
        shares[1].row_coefficients.pop();
        assert_eq!(
            collaborative_tensor_encode(shape, &shares),
            Err(CollaborativeBasefoldError::WrongShareWidth {
                party: 1,
                expected: 3,
                actual: 2,
            })
        );

        let state = encoded();
        let mut rows = state.party_rows().to_vec();
        rows[0].values.pop();
        assert_eq!(
            DistributedTensorCodeword::from_party_rows(shape, 0, 8, rows),
            Err(CollaborativeBasefoldError::WrongRowWidth {
                party: 0,
                expected: 8,
                actual: 7,
            })
        );
        assert!(matches!(
            DistributedTensorCodeword::from_party_rows(shape, 1, 8, state.party_rows().to_vec(),),
            Err(CollaborativeBasefoldError::RoundShapeMismatch { .. })
        ));
    }

    #[test]
    fn wrong_statement_context_state_and_round_challenges_refuse() {
        let state = encoded();
        let right = CollaborativeFoldTranscript::new([7; 32], b"session-A");
        let wrong_statement = CollaborativeFoldTranscript::new([8; 32], b"session-A");
        let wrong_context = CollaborativeFoldTranscript::new([7; 32], b"session-B");

        let mut tampered_value = right.challenge(&state);
        tampered_value.value += BabyBear::ONE;
        for challenge in [
            wrong_statement.challenge(&state),
            wrong_context.challenge(&state),
            tampered_value,
        ] {
            assert_eq!(
                state.fold(&right, &challenge),
                Err(CollaborativeBasefoldError::FoldChallengeMismatch)
            );
            assert_eq!(
                fold_party_row_local(
                    state.shape(),
                    state.round(),
                    state.columns(),
                    &state.party_rows()[0],
                    &right,
                    state.state_digest(),
                    &challenge,
                ),
                Err(CollaborativeBasefoldError::FoldChallengeMismatch)
            );
        }

        let challenge0 = right.challenge(&state);
        let state1 = state.fold(&right, &challenge0).unwrap();
        assert_eq!(
            state1.fold(&right, &challenge0),
            Err(CollaborativeBasefoldError::FoldChallengeMismatch)
        );

        // A value mutation changes the state digest and therefore the challenge.
        let mut changed_rows = state.party_rows().to_vec();
        changed_rows[0].values[0] += BabyBear::ONE;
        let changed =
            DistributedTensorCodeword::from_party_rows(shape(), 0, 8, changed_rows).unwrap();
        assert_eq!(
            changed.fold(&right, &challenge0),
            Err(CollaborativeBasefoldError::FoldChallengeMismatch)
        );
    }

    #[test]
    fn challenge_derivation_is_deterministic_and_nonzero_state_bound() {
        let state = encoded();
        let transcript = CollaborativeFoldTranscript::new([9; 32], b"fixture");
        let a = transcript.challenge(&state);
        let b = transcript
            .challenge_for_published_digest(
                state.shape(),
                state.round(),
                state.columns(),
                state.state_digest(),
            )
            .unwrap();
        assert_eq!(a, b);
        assert_eq!(a.round(), 0);
        assert_eq!(a.state_digest(), state.state_digest());
        assert_ne!(a.binding(), [0; 32]);
        assert!(a.value().as_canonical_u64() < BabyBear::ORDER_U64);
    }
}
