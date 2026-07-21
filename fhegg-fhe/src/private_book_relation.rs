//! Exact BFV witness relation for the fixed private `N=4,K=4` Dark Bazaar.
//!
//! This module closes a prerequisite which the receipt layer previously left
//! implicit: it defines one injective plaintext encoding and an executable
//! relation joining the **exact four BFV ciphertexts** to the **same four
//! orders and blinding** used by the Lean-authored private-book root.
//!
//! The encoding does not publish an order side.  Every ciphertext contains:
//!
//! * slots `0..4`: that order's bid-demand unary row (zero for an ask),
//! * slots `4..8`: that order's ask-supply unary row (zero for a bid), and
//! * slot `8`: `kind + 8*quantity`, the same injective seven-bit code absorbed
//!   by `DarkBazaarPrivateDescriptor`.
//!
//! The metadata slot is load-bearing.  Unary rows alone erase side and limit
//! when quantity is zero, so they cannot prove the *same opening* as the
//! private root.  The code slot preserves the exact root opening, including
//! canonical zero-quantity padding, without making it public.  All rows carry
//! the same conservative public bound `127`; quantity is not leaked through
//! `LeanCiphertext::plain_bound`, and four rows cannot wrap the pinned BFV
//! plaintext modulus.
//!
//! # Security status
//!
//! [`verify_private_book_opening`] is an exact NP-relation checker for a prover
//! which already owns the private book and BFV encryption seeds.  It is *not*
//! transferable evidence and deliberately has no receipt/verifier-trait impl.
//! Publishing [`PrivateBookEncryptionOpening`] reveals enough randomness to
//! test plaintext guesses.  The next cryptographic rung must prove this exact
//! relation in zero knowledge (including short BFV randomness/noise), or prove
//! an equivalent committed threshold-decryption relation.  A signature over a
//! successful call would still only be issuer-visible Tier 1 and is not added
//! here.

use std::collections::HashSet;
use std::fmt;

use dregg_circuit_prove::dark_bazaar_private::{
    self, PrivateBookWitness, PrivateOrder, PublicStatement, Side,
};
use fhe::bfv::{Ciphertext, Encoding, Plaintext};
use fhe_traits::{DeserializeParametrized, FheEncoder, FheEncrypter, Serialize as FheSerialize};
use rand_09::rngs::StdRng;
use rand_09::{RngCore, SeedableRng};

use crate::bfv_lean::LeanCiphertext;
use crate::threshold::{BfvParams, CollectivePublicKey};

/// Exact protocol discriminator for the private plaintext layout.
pub const PRIVATE_BOOK_BFV_CODEC_ID: &[u8; 32] = b"FHEGG-PRIVATE-BOOK-BFV-N4K4-V1!!";
/// Four demand slots, four supply slots, then one injective order-code slot.
pub const PRIVATE_BOOK_LIVE_SLOTS: usize = 9;
/// Maximum value of `kind + 8*quantity`, used uniformly for every public row
/// bound so an individual quantity is not disclosed by transport metadata.
pub const PRIVATE_BOOK_PUBLIC_BOUND: u64 = 127;

const RELATION_DOMAIN: &str = "fhegg/private-book-bfv-relation/n4k4/v1";

pub type Result<T> = std::result::Result<T, PrivateBookRelationError>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrivateBookRelationError {
    InvalidParameters,
    InvalidPrivateWitness(String),
    StatementMismatch,
    DuplicateEncryptionSeed,
    BfvEncryption { order: usize },
    CiphertextMismatch { order: usize },
    InvalidCiphertextShape { order: usize },
    BfvFold,
}

impl fmt::Display for PrivateBookRelationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidParameters => write!(f, "BFV parameters do not support private N4K4"),
            Self::InvalidPrivateWitness(error) => write!(f, "invalid private book: {error}"),
            Self::StatementMismatch => write!(f, "private book does not open the public statement"),
            Self::DuplicateEncryptionSeed => {
                write!(
                    f,
                    "private-book ciphertexts reuse BFV encryption randomness"
                )
            }
            Self::BfvEncryption { order } => {
                write!(f, "BFV encryption failed for private order {order}")
            }
            Self::CiphertextMismatch { order } => {
                write!(
                    f,
                    "BFV ciphertext {order} does not open to private order {order}"
                )
            }
            Self::InvalidCiphertextShape { order } => {
                write!(f, "private-book ciphertext {order} has the wrong BFV shape")
            }
            Self::BfvFold => write!(f, "private-book BFV ciphertext fold failed"),
        }
    }
}

impl std::error::Error for PrivateBookRelationError {}

/// Secret encryption-randomness opening for exactly four ordered ciphertexts.
///
/// This type has no wire codec and intentionally omits `Debug`.  It belongs in
/// the proof-producing process only; revealing it is not zero knowledge.
#[derive(Clone)]
pub struct PrivateBookEncryptionOpening {
    seeds: [[u8; 32]; dark_bazaar_private::ORDER_COUNT],
}

impl PrivateBookEncryptionOpening {
    /// Construct from caller-owned, independently sampled seeds.  Duplicate
    /// seeds fail in the relation checker because reusing BFV randomness lets
    /// ciphertext subtraction expose a plaintext difference.
    pub const fn from_seeds(seeds: [[u8; 32]; dark_bazaar_private::ORDER_COUNT]) -> Self {
        Self { seeds }
    }

    /// CSPRNG-backed convenience constructor for a trader/proof worker.
    pub fn fresh() -> Self {
        let mut rng = rand_09::rng();
        let mut seeds = [[0u8; 32]; dark_bazaar_private::ORDER_COUNT];
        for seed in &mut seeds {
            rng.fill_bytes(seed);
        }
        Self { seeds }
    }

    /// Borrow the prover-only deterministic BFV seeds.
    ///
    /// This is crate-visible solely so the zero-knowledge backend can recover
    /// the short `u,e1,e2` coefficient witnesses used by the exact encryption.
    /// It is intentionally not public API: exporting these seeds would make
    /// the corresponding order ciphertexts dictionary-testable.
    pub(crate) const fn prover_seeds(&self) -> &[[u8; 32]; dark_bazaar_private::ORDER_COUNT] {
        &self.seeds
    }
}

/// Four ordered, side-hiding BFV ciphertexts for one fixed private book.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateBookCiphertexts {
    rows: [LeanCiphertext; dark_bazaar_private::ORDER_COUNT],
}

impl PrivateBookCiphertexts {
    pub const fn rows(&self) -> &[LeanCiphertext; dark_bazaar_private::ORDER_COUNT] {
        &self.rows
    }

    pub fn into_rows(self) -> [LeanCiphertext; dark_bazaar_private::ORDER_COUNT] {
        self.rows
    }

    /// Construct transport input after the ordinary strict BFV parser has run.
    /// The exact private format (shape, uniform bound, and plaintext opening)
    /// remains enforced by [`verify_private_book_opening`].
    pub const fn from_rows(rows: [LeanCiphertext; dark_bazaar_private::ORDER_COUNT]) -> Self {
        Self { rows }
    }
}

/// The direct homomorphic aggregate of the four canonical proof rows.
///
/// Slots `0..4` are the encrypted aggregate demand curve, slots `4..8` are
/// aggregate supply, and slot `8` is the sum of the injective order codes.  A
/// masked-decryption/MPC consumer must keep all nine slots shared and select the
/// two curve ranges inside MPC; opening this carrier would reveal the book.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoldedPrivateBookCiphertext {
    ciphertext: LeanCiphertext,
}

impl FoldedPrivateBookCiphertext {
    pub const fn ciphertext(&self) -> &LeanCiphertext {
        &self.ciphertext
    }

    pub fn into_ciphertext(self) -> LeanCiphertext {
        self.ciphertext
    }

    pub const fn demand_slots() -> core::ops::Range<usize> {
        0..dark_bazaar_private::PRICE_COUNT
    }

    pub const fn supply_slots() -> core::ops::Range<usize> {
        dark_bazaar_private::PRICE_COUNT..2 * dark_bazaar_private::PRICE_COUNT
    }

    pub const fn metadata_slot() -> usize {
        2 * dark_bazaar_private::PRICE_COUNT
    }
}

/// Add the exact four proof ciphertexts into one side-hiding packed carrier.
///
/// This deliberately does not accept [`CollectiveOrderRow`]: accepting that
/// older side-specific encoding here would reintroduce the unproved equality
/// seam this path exists to remove.  The fold is just four native BFV additions;
/// no plaintext, secret key, rotation key, or re-encryption is involved.
pub fn fold_private_book_ciphertexts(
    ciphertexts: &PrivateBookCiphertexts,
    params: &BfvParams,
) -> Result<FoldedPrivateBookCiphertext> {
    let aggregate_bound = PRIVATE_BOOK_PUBLIC_BOUND
        .checked_mul(dark_bazaar_private::ORDER_COUNT as u64)
        .ok_or(PrivateBookRelationError::InvalidParameters)?;
    if params.degree() < PRIVATE_BOOK_LIVE_SLOTS
        || aggregate_bound >= params.plaintext_modulus()
        || params.moduli().is_empty()
    {
        return Err(PrivateBookRelationError::InvalidParameters);
    }

    let mut parsed = Vec::with_capacity(dark_bazaar_private::ORDER_COUNT);
    for (order, row) in ciphertexts.rows.iter().enumerate() {
        if row.plain_bound != PRIVATE_BOOK_PUBLIC_BOUND
            || row.degree != params.degree()
            || row.moduli.as_slice() != params.moduli()
            || row.level != 0
            || !row.variable_time
            || row.polys.len() != 2
        {
            return Err(PrivateBookRelationError::InvalidCiphertextShape { order });
        }
        parsed.push(
            Ciphertext::from_bytes(&row.to_fhe_bytes(), params.arc())
                .map_err(|_| PrivateBookRelationError::InvalidCiphertextShape { order })?,
        );
    }

    let mut aggregate = parsed
        .drain(..1)
        .next()
        .expect("fixed private book contains four rows");
    for row in parsed {
        aggregate += &row;
    }
    let ciphertext = LeanCiphertext::from_fhe_bytes(
        &aggregate.to_bytes(),
        params.moduli(),
        params.degree(),
        aggregate_bound,
    )
    .map_err(|_| PrivateBookRelationError::BfvFold)?;
    Ok(FoldedPrivateBookCiphertext { ciphertext })
}

/// Encrypt all four private orders under the collective key using the exact
/// injective layout above.  No side bit or order value is returned separately.
pub fn encrypt_private_book(
    witness: &PrivateBookWitness,
    opening: &PrivateBookEncryptionOpening,
    params: &BfvParams,
    public_key: &CollectivePublicKey,
) -> Result<PrivateBookCiphertexts> {
    validate_envelope(params, opening)?;
    // Reuse the already Lean/Poseidon-grounded constructor as the canonical
    // witness validator.  Session zero is harmless here: only shape and
    // canonical blinding are being checked; the caller's real session is
    // checked in `verify_private_book_opening` below.
    dark_bazaar_private::statement(0, witness)
        .map_err(PrivateBookRelationError::InvalidPrivateWitness)?;

    let mut rows = Vec::with_capacity(dark_bazaar_private::ORDER_COUNT);
    for (order, (&private_order, seed)) in
        witness.orders.iter().zip(opening.seeds.iter()).enumerate()
    {
        rows.push(encrypt_private_book_row(
            order,
            private_order,
            *seed,
            params,
            public_key,
        )?);
    }
    let rows = rows
        .try_into()
        .expect("fixed order count creates exactly four ciphertext rows");
    Ok(PrivateBookCiphertexts { rows })
}

/// Check the complete exact-opening relation used by a future lattice-ZK or
/// committed-decryption proof.
///
/// Success means each canonical ciphertext is byte-for-byte the BFV encryption
/// of its corresponding hidden order under its supplied seed, and those same
/// ordered values plus the supplied blinding recompute the caller-supplied
/// private HidingFRI statement/root.  No digest or caller assertion substitutes
/// for either equality.
pub fn verify_private_book_opening(
    statement: PublicStatement,
    witness: &PrivateBookWitness,
    ciphertexts: &PrivateBookCiphertexts,
    opening: &PrivateBookEncryptionOpening,
    params: &BfvParams,
    public_key: &CollectivePublicKey,
) -> Result<()> {
    validate_envelope(params, opening)?;
    let expected_statement = dark_bazaar_private::statement(statement.session, witness)
        .map_err(PrivateBookRelationError::InvalidPrivateWitness)?;
    if expected_statement != statement {
        return Err(PrivateBookRelationError::StatementMismatch);
    }

    for (order, ((&private_order, seed), actual)) in witness
        .orders
        .iter()
        .zip(opening.seeds.iter())
        .zip(ciphertexts.rows.iter())
        .enumerate()
    {
        let expected = encrypt_private_book_row(order, private_order, *seed, params, public_key)?;
        // Include the non-wire bound explicitly.  `to_fhe_bytes` is the exact
        // canonical ciphertext identity used by the fhEgg claim.
        if actual.plain_bound != PRIVATE_BOOK_PUBLIC_BOUND
            || actual.moduli != params.moduli()
            || actual.degree != params.degree()
            || actual.polys.len() != 2
            || actual.to_fhe_bytes() != expected.to_fhe_bytes()
        {
            return Err(PrivateBookRelationError::CiphertextMismatch { order });
        }
    }
    Ok(())
}

/// Public digest for binding a future proof transcript/verifier id.  This is
/// only a statement digest; it is never accepted as evidence by this module.
pub fn private_book_relation_digest(
    statement: PublicStatement,
    ciphertexts: &PrivateBookCiphertexts,
    params: &BfvParams,
    public_key: &CollectivePublicKey,
) -> [u8; 32] {
    let mut hash = blake3::Hasher::new_derive_key(RELATION_DOMAIN);
    hash.update(PRIVATE_BOOK_BFV_CODEC_ID);
    hash.update(&(params.degree() as u64).to_be_bytes());
    hash.update(&params.plaintext_modulus().to_be_bytes());
    hash.update(&(params.moduli().len() as u64).to_be_bytes());
    for &modulus in params.moduli() {
        hash.update(&modulus.to_be_bytes());
    }
    let key = public_key.pk.to_bytes();
    hash.update(&(key.len() as u64).to_be_bytes());
    hash.update(&key);
    hash.update(&statement.session.to_be_bytes());
    hash.update(&statement.rule.to_be_bytes());
    for lane in statement.order_root {
        hash.update(&lane.to_be_bytes());
    }
    hash.update(&statement.p_star.to_be_bytes());
    hash.update(&statement.v_star.to_be_bytes());
    for row in &ciphertexts.rows {
        let bytes = row.to_fhe_bytes();
        hash.update(&row.plain_bound.to_be_bytes());
        hash.update(&(bytes.len() as u64).to_be_bytes());
        hash.update(&bytes);
    }
    *hash.finalize().as_bytes()
}

fn validate_envelope(params: &BfvParams, opening: &PrivateBookEncryptionOpening) -> Result<()> {
    let no_wrap_bound = PRIVATE_BOOK_PUBLIC_BOUND
        .checked_mul(dark_bazaar_private::ORDER_COUNT as u64)
        .ok_or(PrivateBookRelationError::InvalidParameters)?;
    if params.degree() < PRIVATE_BOOK_LIVE_SLOTS
        || params.plaintext_modulus() <= no_wrap_bound
        || params.moduli().is_empty()
    {
        return Err(PrivateBookRelationError::InvalidParameters);
    }
    let distinct = opening.seeds.iter().copied().collect::<HashSet<_>>();
    if distinct.len() != dark_bazaar_private::ORDER_COUNT {
        return Err(PrivateBookRelationError::DuplicateEncryptionSeed);
    }
    Ok(())
}

fn order_kind(order: PrivateOrder) -> Result<usize> {
    if order.qty > dark_bazaar_private::MAX_QTY
        || order.limit as usize >= dark_bazaar_private::PRICE_COUNT
    {
        return Err(PrivateBookRelationError::InvalidPrivateWitness(
            "order lies outside the fixed N4K4 family".to_owned(),
        ));
    }
    Ok(order.limit as usize
        + match order.side {
            Side::Bid => 0,
            Side::Ask => dark_bazaar_private::PRICE_COUNT,
        })
}

pub(crate) fn private_order_slots(order: PrivateOrder, degree: usize) -> Result<Vec<u64>> {
    let kind = order_kind(order)?;
    let mut slots = vec![0u64; degree];
    let quantity = u64::from(order.qty);
    match order.side {
        Side::Bid => {
            for slot in slots.iter_mut().take(order.limit as usize + 1) {
                *slot = quantity;
            }
        }
        Side::Ask => {
            for slot in slots
                .iter_mut()
                .take(2 * dark_bazaar_private::PRICE_COUNT)
                .skip(dark_bazaar_private::PRICE_COUNT + order.limit as usize)
            {
                *slot = quantity;
            }
        }
    }
    slots[2 * dark_bazaar_private::PRICE_COUNT] = kind as u64 + 8 * quantity;
    Ok(slots)
}

/// Encrypt one row in the exact side-hiding private-book layout.
///
/// This is the trader-ingress primitive for the canonical cutover: a trader can
/// sign and submit the very ciphertext later consumed by
/// [`verify_private_book_opening`] and the transferable proof, instead of also
/// manufacturing a side-specific unary ciphertext.  `order_index` is used only
/// for precise error attribution; the caller binds its position in the signed
/// ingress envelope/claim.
pub fn encrypt_private_book_row(
    order_index: usize,
    order: PrivateOrder,
    seed: [u8; 32],
    params: &BfvParams,
    public_key: &CollectivePublicKey,
) -> Result<LeanCiphertext> {
    let slots = private_order_slots(order, params.degree())?;
    let plaintext = Plaintext::try_encode(&slots, Encoding::simd(), params.arc())
        .map_err(|_| PrivateBookRelationError::BfvEncryption { order: order_index })?;
    let mut rng = StdRng::from_seed(seed);
    let ciphertext: Ciphertext = public_key
        .pk
        .try_encrypt(&plaintext, &mut rng)
        .map_err(|_| PrivateBookRelationError::BfvEncryption { order: order_index })?;
    LeanCiphertext::from_fhe_bytes(
        &ciphertext.to_bytes(),
        params.moduli(),
        params.degree(),
        PRIVATE_BOOK_PUBLIC_BOUND,
    )
    .map_err(|_| PrivateBookRelationError::BfvEncryption { order: order_index })
}
