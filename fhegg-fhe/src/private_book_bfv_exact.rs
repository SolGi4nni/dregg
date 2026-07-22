//! Canonical public coefficients for the exact private-book BFV relation.
//!
//! Both the monolithic proof and the distributed proof workers must consume
//! this module.  It is the single lowering of the deployed `fhe.rs` public key,
//! ciphertexts, exact finite message table, and transcript-derived Rademacher
//! rows into integer equations.  In particular, a distributed backend must not
//! substitute a nearby BFV model or caller-supplied public coefficients.

use std::fmt;
use std::sync::Arc;

use dregg_circuit_prove::dark_bazaar_private::{
    self, PublicStatement, ORDER_COUNT, PRICE_COUNT, RULE_ID,
};
use fhe::bfv::{Ciphertext, Encoding, Plaintext};
use fhe_math::rq::{traits::TryConvertFrom, Poly, Representation};
use fhe_traits::{FheEncoder, FheEncrypter, Serialize as FheSerialize};
use rand_09::rngs::StdRng;
use rand_09::SeedableRng;

use crate::bfv_lean::{LeanCiphertext, FOLD_DEGREE, FOLD_MODULI};
use crate::private_book_distributed_inputs::{
    DERIVED_ORDER_WIDTH, OPTION_COUNT, ROOT_BLINDING_WIDTH,
};
use crate::private_book_relation::{
    private_book_relation_digest, private_order_slots, PrivateBookCiphertexts,
    PRIVATE_BOOK_PUBLIC_BOUND,
};
use crate::threshold::{BfvParams, CollectivePublicKey};

const SIGN_DOMAIN: &str = "fhegg/private-book-bfv-rademacher/n4k4/v1";
const FOLD_PLAINTEXT_MODULUS: u64 = 1_032_193;
const BABYBEAR_MODULUS: u32 = 2_013_265_921;
const QUANTITY_COUNT: usize = dark_bazaar_private::MAX_QTY as usize + 1;

/// Number of independent transcript-derived Rademacher rows per RNS modulus.
pub(crate) const COMPRESSION_ROUNDS: usize = 128;
/// Signed quotient width used by the exact integer relation.
pub(crate) const QUOTIENT_BITS: usize = 24;
/// Number of owner-local quotient equations: three moduli times 128 rows.
pub(crate) const OWNER_BATCH_EQUATION_COUNT: usize = FOLD_MODULI.len() * COMPRESSION_ROUNDS;
/// Conservative exact-integer quotient bound inherited by every backend.
pub(crate) const MAX_ABS_BATCH_QUOTIENT: i64 = 1_130_496;

const _: () = assert!(OPTION_COUNT == 2 * PRICE_COUNT * QUANTITY_COUNT);
const _: () = assert!(MAX_ABS_BATCH_QUOTIENT < (1 << (QUOTIENT_BITS - 1)));
const _: () = assert!((MAX_ABS_BATCH_QUOTIENT as u128) * (FOLD_MODULI[2] as u128) < (1u128 << 59));

/// Fail-closed errors from constructing canonical exact-BFV public data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ExactBfvError {
    WrongParameters,
    InvalidStatement,
    InvalidOwner,
    PublicKeyWire,
    Encoder(String),
    Arithmetic(String),
}

impl fmt::Display for ExactBfvError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WrongParameters => f.write_str("wrong exact-BFV parameters or ciphertext shape"),
            Self::InvalidStatement => f.write_str("invalid private-book public statement"),
            Self::InvalidOwner => f.write_str("invalid exact-BFV owner or degree"),
            Self::PublicKeyWire => f.write_str("malformed collective BFV public key"),
            Self::Encoder(reason) => write!(f, "exact BFV encoder failed: {reason}"),
            Self::Arithmetic(reason) => write!(f, "exact BFV arithmetic failed: {reason}"),
        }
    }
}

impl std::error::Error for ExactBfvError {}

/// One owner-local exact compressed equation.
///
/// `base_coefficients` follows `LocalOrderWitness` exactly:
/// `[kind, quantity, 128 selectors, 9 semantic slots, u, e1, e2, root lanes]`.
/// Only selector and short-polynomial coordinates participate in BFV; the
/// other coefficients are deliberately zero so the distributed commitment
/// layout and the equation layout cannot be confused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ExactBfvBatchEquation {
    pub(crate) base_coefficients: Vec<i128>,
    pub(crate) public_constant: i128,
    pub(crate) modulus: u64,
}

/// Canonical public half of the deployed exact private-book BFV relation.
#[derive(Clone)]
pub(crate) struct ExactBfvPublicRelation {
    statement: PublicStatement,
    pub(crate) pk: LeanCiphertext,
    pub(crate) ciphertexts: [LeanCiphertext; ORDER_COUNT],
    /// `[kind * 16 + quantity][modulus][coefficient]`, obtained from the real
    /// SIMD encoder by same-randomness subtraction.
    pub(crate) message_table: Vec<Vec<Vec<u64>>>,
    pub(crate) pk_adjoint_ntt: [Poly; 2],
    pub(crate) context: Arc<fhe_math::rq::Context>,
    relation_digest: [u8; 32],
}

impl ExactBfvPublicRelation {
    /// Derive every public coefficient and the canonical relation digest from
    /// independently supplied deployed inputs.  No coefficient is accepted
    /// from a prover or distributed worker.
    pub(crate) fn derive(
        statement: PublicStatement,
        ciphertexts: &PrivateBookCiphertexts,
        params: &BfvParams,
        public_key: &CollectivePublicKey,
    ) -> Result<Self, ExactBfvError> {
        validate_public(statement, ciphertexts, params)?;
        let pk = parse_public_key(public_key, params)?;
        let message_table = derive_exact_message_table(params, public_key)?;
        let context = params
            .arc()
            .context_at_level(0)
            .map_err(|error| ExactBfvError::Arithmetic(error.to_string()))?
            .clone();
        let pk_adjoint_ntt = [0usize, 1usize]
            .map(|poly| adjoint_ntt(&pk.polys[poly].rows, &context))
            .into_iter()
            .collect::<Result<Vec<_>, _>>()?
            .try_into()
            .expect("exactly two public-key polynomials");
        let relation_digest =
            private_book_relation_digest(statement, ciphertexts, params, public_key);
        Ok(Self {
            statement,
            pk,
            ciphertexts: ciphertexts.rows().clone(),
            message_table,
            pk_adjoint_ntt,
            context,
            relation_digest,
        })
    }

    /// Digest that a production `DistributedWitnessSession` must bind.
    pub(crate) const fn relation_digest(&self) -> [u8; 32] {
        self.relation_digest
    }

    /// Exact public statement from which this coefficient family and relation
    /// digest were independently derived.
    pub(crate) const fn statement(&self) -> PublicStatement {
        self.statement
    }

    /// Materialize all 384 owner-local equations in `[modulus][round]` order.
    ///
    /// Production is intentionally fixed to the actual degree-4096 `fhe.rs`
    /// ring.  Synthetic small-degree protocol tests must use a visibly test-
    /// only constructor rather than inventing truncated-ring semantics here.
    pub(crate) fn owner_batch_equations(
        &self,
        challenge: &[u8; 32],
        owner: usize,
        degree: usize,
    ) -> Result<Vec<ExactBfvBatchEquation>, ExactBfvError> {
        if owner >= ORDER_COUNT || degree != FOLD_DEGREE {
            return Err(ExactBfvError::InvalidOwner);
        }
        let width = DERIVED_ORDER_WIDTH + 3 * degree + ROOT_BLINDING_WIDTH;
        let u_base = DERIVED_ORDER_WIDTH;
        let e1_base = u_base + degree;
        let e2_base = e1_base + degree;
        let mut equations = Vec::with_capacity(OWNER_BATCH_EQUATION_COUNT);

        for (qi, &modulus) in FOLD_MODULI.iter().enumerate() {
            for round in 0..COMPRESSION_ROUNDS {
                let mut coefficients = vec![0i128; width];
                let mut public_constant = 0i128;
                for poly in 0..2 {
                    let signs = derive_signs(challenge, qi, round, owner, poly, degree);
                    let gradient = negacyclic_correlation(
                        &signs,
                        &self.pk_adjoint_ntt[poly],
                        &self.context,
                        qi,
                        degree,
                    )?;
                    for coefficient in 0..degree {
                        coefficients[u_base + coefficient] += gradient[coefficient] as i128;
                        let error_base = if poly == 0 { e1_base } else { e2_base };
                        coefficients[error_base + coefficient] = signs[coefficient] as i128;
                        public_constant -= signs[coefficient] as i128
                            * self.ciphertexts[owner].polys[poly].rows[qi][coefficient] as i128;
                    }
                    if poly == 0 {
                        for option in 0..OPTION_COUNT {
                            coefficients[2 + option] =
                                signed_dot(&signs, &self.message_table[option][qi]);
                        }
                    }
                }
                equations.push(ExactBfvBatchEquation {
                    base_coefficients: coefficients,
                    public_constant,
                    modulus,
                });
            }
        }
        debug_assert_eq!(equations.len(), OWNER_BATCH_EQUATION_COUNT);
        Ok(equations)
    }
}

pub(crate) fn derive_signs(
    challenge: &[u8; 32],
    modulus: usize,
    round: usize,
    owner: usize,
    poly: usize,
    degree: usize,
) -> Vec<i64> {
    let mut hasher = blake3::Hasher::new_derive_key(SIGN_DOMAIN);
    hasher.update(challenge);
    hasher.update(&(modulus as u64).to_be_bytes());
    hasher.update(&(round as u64).to_be_bytes());
    hasher.update(&(owner as u64).to_be_bytes());
    hasher.update(&(poly as u64).to_be_bytes());
    let mut bytes = vec![0u8; degree.div_ceil(8)];
    hasher.finalize_xof().fill(&mut bytes);
    (0..degree)
        .map(|index| {
            if bytes[index / 8] & (1 << (index % 8)) == 0 {
                -1
            } else {
                1
            }
        })
        .collect()
}

pub(crate) fn signed_dot(signs: &[i64], values: &[u64]) -> i128 {
    signs
        .iter()
        .zip(values)
        .map(|(&sign, &value)| sign as i128 * value as i128)
        .sum()
}

pub(crate) fn negacyclic_correlation(
    signs: &[i64],
    public_adjoint_ntt: &Poly,
    context: &Arc<fhe_math::rq::Context>,
    qi: usize,
    degree: usize,
) -> Result<Vec<u64>, ExactBfvError> {
    if degree != FOLD_DEGREE || signs.len() != degree || qi >= FOLD_MODULI.len() {
        return Err(ExactBfvError::WrongParameters);
    }
    let mut sign_poly = Poly::try_convert_from(signs, context, false, Representation::PowerBasis)
        .map_err(|error| ExactBfvError::Arithmetic(error.to_string()))?;
    sign_poly.change_representation(Representation::Ntt);
    sign_poly *= public_adjoint_ntt;
    sign_poly.change_representation(Representation::PowerBasis);
    let coefficients = Vec::<u64>::from(&sign_poly);
    Ok(coefficients[qi * degree..(qi + 1) * degree].to_vec())
}

pub(crate) fn derive_exact_message_table(
    params: &BfvParams,
    public_key: &CollectivePublicKey,
) -> Result<Vec<Vec<Vec<u64>>>, ExactBfvError> {
    let zero = vec![0u64; FOLD_DEGREE];
    let zero_ct = deterministic_encrypt_slots(&zero, params, public_key)?;
    let mut table = Vec::with_capacity(OPTION_COUNT);
    for kind in 0..2 * PRICE_COUNT {
        for qty in 0..QUANTITY_COUNT {
            let order = dark_bazaar_private::PrivateOrder {
                side: if kind < PRICE_COUNT {
                    dark_bazaar_private::Side::Bid
                } else {
                    dark_bazaar_private::Side::Ask
                },
                limit: (kind % PRICE_COUNT) as u8,
                qty: qty as u8,
            };
            let slots = private_order_slots(order, FOLD_DEGREE)
                .map_err(|error| ExactBfvError::Encoder(error.to_string()))?;
            let option_ct = deterministic_encrypt_slots(&slots, params, public_key)?;
            if option_ct.polys[1] != zero_ct.polys[1] {
                return Err(ExactBfvError::Encoder(
                    "deterministic c1 did not cancel while deriving SIMD table".to_owned(),
                ));
            }
            let mut option_poly = Vec::with_capacity(FOLD_MODULI.len());
            for (qi, &q) in FOLD_MODULI.iter().enumerate() {
                option_poly.push(
                    option_ct.polys[0].rows[qi]
                        .iter()
                        .zip(&zero_ct.polys[0].rows[qi])
                        .map(|(&option, &zero)| {
                            if option >= zero {
                                option - zero
                            } else {
                                q - (zero - option)
                            }
                        })
                        .collect(),
                );
            }
            table.push(option_poly);
        }
    }
    Ok(table)
}

fn validate_public(
    statement: PublicStatement,
    ciphertexts: &PrivateBookCiphertexts,
    params: &BfvParams,
) -> Result<(), ExactBfvError> {
    if params.degree() != FOLD_DEGREE
        || params.moduli() != FOLD_MODULI.as_slice()
        || params.plaintext_modulus() != FOLD_PLAINTEXT_MODULUS
    {
        return Err(ExactBfvError::WrongParameters);
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
        return Err(ExactBfvError::InvalidStatement);
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
        return Err(ExactBfvError::WrongParameters);
    }
    Ok(())
}

fn adjoint_ntt(
    rows: &[Vec<u64>],
    context: &Arc<fhe_math::rq::Context>,
) -> Result<Poly, ExactBfvError> {
    let mut flat = Vec::with_capacity(FOLD_MODULI.len() * FOLD_DEGREE);
    for (qi, row) in rows.iter().enumerate() {
        let q = FOLD_MODULI[qi];
        let mut adjoint = vec![0u64; FOLD_DEGREE];
        adjoint[0] = row[0];
        for coefficient in 1..FOLD_DEGREE {
            adjoint[FOLD_DEGREE - coefficient] = if row[coefficient] == 0 {
                0
            } else {
                q - row[coefficient]
            };
        }
        flat.extend(adjoint);
    }
    let mut poly = Poly::try_convert_from(flat, context, false, Representation::PowerBasis)
        .map_err(|error| ExactBfvError::Arithmetic(error.to_string()))?;
    poly.change_representation(Representation::Ntt);
    Ok(poly)
}

pub(crate) fn parse_public_key(
    public_key: &CollectivePublicKey,
    params: &BfvParams,
) -> Result<LeanCiphertext, ExactBfvError> {
    let bytes = public_key.pk.to_bytes();
    let mut offset = 0usize;
    if bytes.get(offset).copied() != Some(0x0a) {
        return Err(ExactBfvError::PublicKeyWire);
    }
    offset += 1;
    let len = read_varint(&bytes, &mut offset)? as usize;
    let end = offset
        .checked_add(len)
        .filter(|&end| end == bytes.len())
        .ok_or(ExactBfvError::PublicKeyWire)?;
    let parsed =
        LeanCiphertext::from_fhe_bytes(&bytes[offset..end], params.moduli(), params.degree(), 0)
            .map_err(|_| ExactBfvError::PublicKeyWire)?;
    if parsed.level != 0 || parsed.variable_time || parsed.polys.len() != 2 {
        return Err(ExactBfvError::PublicKeyWire);
    }
    Ok(parsed)
}

fn read_varint(bytes: &[u8], offset: &mut usize) -> Result<u64, ExactBfvError> {
    let mut value = 0u64;
    let mut shift = 0u32;
    loop {
        let byte = *bytes.get(*offset).ok_or(ExactBfvError::PublicKeyWire)?;
        *offset += 1;
        if shift >= 64 {
            return Err(ExactBfvError::PublicKeyWire);
        }
        value |= u64::from(byte & 0x7f) << shift;
        if byte & 0x80 == 0 {
            return Ok(value);
        }
        shift += 7;
    }
}

fn deterministic_encrypt_slots(
    slots: &[u64],
    params: &BfvParams,
    public_key: &CollectivePublicKey,
) -> Result<LeanCiphertext, ExactBfvError> {
    let plaintext = Plaintext::try_encode(slots, Encoding::simd(), params.arc())
        .map_err(|error| ExactBfvError::Encoder(error.to_string()))?;
    let mut rng = StdRng::from_seed([0xA7; 32]);
    let ciphertext: Ciphertext = public_key
        .pk
        .try_encrypt(&plaintext, &mut rng)
        .map_err(|error| ExactBfvError::Encoder(error.to_string()))?;
    LeanCiphertext::from_fhe_bytes(&ciphertext.to_bytes(), params.moduli(), params.degree(), 1)
        .map_err(|error| ExactBfvError::Encoder(error.to_string()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use curve25519_dalek::scalar::Scalar;
    use dregg_circuit_prove::dark_bazaar_private::{statement, PrivateBookWitness, PrivateOrder};
    use ed25519_dalek::SigningKey;

    use crate::private_book_distributed_inputs::{
        DistributedWitnessSession, LocalOrderWitness, PrivateSide,
    };
    use crate::private_book_relation::{encrypt_private_book, PrivateBookEncryptionOpening};
    use crate::threshold::{KeygenCoordinator, KeygenSession, ThresholdParty};

    fn scalar_i64(value: i64) -> Scalar {
        if value < 0 {
            -Scalar::from(value.unsigned_abs())
        } else {
            Scalar::from(value as u64)
        }
    }

    fn decode_short(value: Scalar) -> i128 {
        (-32i64..=31)
            .find(|&candidate| scalar_i64(candidate) == value)
            .map(i128::from)
            .expect("distributed short witness remains in the pinned six-bit interval")
    }

    #[test]
    fn owner_equations_are_exact_integer_multiples_for_real_fhe_fixture() {
        let params = BfvParams::fold_set();
        let key_session = KeygenSession::from_seed(2, [0xB1; 32]).expect("key session");
        let mut coordinator = KeygenCoordinator::new(key_session.clone(), params.clone());
        for party in 0..key_session.n_parties() {
            let (_state, contribution) =
                ThresholdParty::join(&key_session, party, &params).expect("party keygen");
            coordinator.accept(contribution).expect("ordered key share");
        }
        let public_key = coordinator.finish().expect("collective key");

        let orders = [
            PrivateOrder::bid(10, 2),
            PrivateOrder::bid(6, 1),
            PrivateOrder::ask(5, 0),
            PrivateOrder::ask(8, 1),
        ];
        let root_blinding = core::array::from_fn(|lane| 17_000 + lane as u32);
        let witness = PrivateBookWitness::try_from_orders_with_blinding(&orders, root_blinding)
            .expect("private book");
        let seeds = [[0x31; 32], [0x32; 32], [0x33; 32], [0x34; 32]];
        let opening = PrivateBookEncryptionOpening::from_seeds(seeds);
        let public = statement(0xDBA2, &witness).expect("public statement");
        let ciphertexts = encrypt_private_book(&witness, &opening, &params, &public_key)
            .expect("real fhe ciphertexts");
        let relation = ExactBfvPublicRelation::derive(public, &ciphertexts, &params, &public_key)
            .expect("canonical exact relation");
        assert_eq!(
            relation.relation_digest(),
            private_book_relation_digest(public, &ciphertexts, &params, &public_key)
        );
        assert!(matches!(
            relation.owner_batch_equations(&[0xC7; 32], 0, 16),
            Err(ExactBfvError::InvalidOwner)
        ));

        let owner_signing = core::array::from_fn::<_, ORDER_COUNT, _>(|owner| {
            SigningKey::from_bytes(&[0x41 + owner as u8; 32])
        });
        let owner_keys = owner_signing
            .each_ref()
            .map(|key| key.verifying_key().to_bytes());
        let worker_keys = [0x61u8, 0x62]
            .into_iter()
            .map(|byte| {
                SigningKey::from_bytes(&[byte; 32])
                    .verifying_key()
                    .to_bytes()
            })
            .collect();
        let session = DistributedWitnessSession::new_for_test(
            relation.relation_digest(),
            [0xD4; 32],
            owner_keys,
            worker_keys,
            FOLD_DEGREE,
        )
        .expect("production distributed session");
        let local = LocalOrderWitness::from_seed(
            &session,
            0,
            PrivateSide::Bid,
            orders[0].limit,
            orders[0].qty,
            seeds[0],
            Some(root_blinding),
        )
        .expect("owner-local exact witness");

        let mut base_values = vec![0i128; session.local_witness_width()];
        let option = orders[0].limit as usize * QUANTITY_COUNT + orders[0].qty as usize;
        base_values[2 + option] = 1;
        for (coordinate, target) in base_values
            [DERIVED_ORDER_WIDTH..DERIVED_ORDER_WIDTH + 3 * FOLD_DEGREE]
            .iter_mut()
            .enumerate()
        {
            *target = decode_short(local.value_for_test(DERIVED_ORDER_WIDTH + coordinate));
        }

        let equations = relation
            .owner_batch_equations(&[0xC7; 32], 0, FOLD_DEGREE)
            .expect("384 production equations");
        assert_eq!(equations.len(), OWNER_BATCH_EQUATION_COUNT);
        for equation in equations {
            let total = equation
                .base_coefficients
                .iter()
                .zip(&base_values)
                .fold(equation.public_constant, |sum, (&coefficient, &value)| {
                    sum + coefficient * value
                });
            assert_eq!(total.rem_euclid(equation.modulus as i128), 0);
            let quotient = total / equation.modulus as i128;
            assert!(quotient.unsigned_abs() <= MAX_ABS_BATCH_QUOTIENT as u128);
        }
    }
}
