//! **`p3-pasta` — Pasta `Fp` as a Plonky3 `PrimeField`, and Mina-Poseidon as a
//! Plonky3 `CryptographicPermutation`.**
//!
//! ## Why this crate exists
//!
//! `circuit-prove/src/dregg_outer_config.rs` makes dregg's ETH-facing proof
//! commit with Poseidon2 over **BN254**, so the gnark verifier hashes natively
//! instead of emulating a foreign 31-bit field — a measured 40.9M → 1.0M R1CS
//! collapse. It gets `Bn254` (a `p3_field::PrimeField`) for free from upstream
//! **`p3-bn254`**.
//!
//! `docs/MINA-FACING-TERMINAL-OPTIONS.md` measures the same lever for Mina and
//! finds it worth **453 → 54 Pickles slices**, and names the one thing that
//! does not exist:
//!
//! > ⚑ **The one piece that does NOT exist, and it is the real cost of this
//! > lever: there is no `p3-pasta`.**
//!
//! This is it. It is the **direct structural twin of `p3-bn254`** — a newtype
//! over an `ark-ff` field plus a permutation adapter — and nothing above it
//! needs to change: `MultiField32PaddingFreeSponge<BabyBear, PastaFp, Perm, 3,
//! 2, 1>`, `TruncatedPermutation<Perm, 2, 1, 3>` and
//! `MultiField32Challenger<BabyBear, PastaFp, Perm, 3, 2>` are the *exact* type
//! shapes `dregg_outer_config.rs` already instantiates.
//!
//! ## ⚑ SUBSTRATE, said out loud (HOUSE LAW #1)
//!
//! **There is no AIR here, no constraint, no gadget and no `air_accepts`.**
//! This crate is *prover plumbing*: which prime field the Merkle/transcript
//! hash lives in, and how to call it. The trace arithmetic a dregg proof
//! commits to is unchanged — `Val = BabyBear`, `Challenge = EF4` — and every
//! AIR remains Lean-authored. Swapping the hash field changes **what the
//! commitment is computed in**, not **what is being proved**. Rust is the
//! correct substrate for exactly this and for nothing more.
//!
//! ## What differs from `p3-bn254`, and why
//!
//! `p3-bn254` hand-rolls its own 4×u64 Montgomery arithmetic. This crate does
//! **not**: it delegates every operation to `mina_curves::pasta::Fp`
//! (`ark_ff::Fp256<MontBackend<FqConfig, 4>>`), because the Mina side of the
//! bridge — `mina-poseidon`'s round constants, o1js's `Field`, kimchi's own
//! sponge — is *defined* over that type. A second implementation of Pasta
//! arithmetic would be a twin to keep in step for no gain, and the repo has a
//! long list of exactly that. The newtype is a **representation adapter**, not
//! a reimplementation.
//!
//! ## The two pins that make this the RIGHT hash
//!
//! 1. [`MinaPoseidonPerm`] is kimchi's own permutation
//!    (`mina_poseidon::permutation::poseidon_block_cipher` with
//!    `PlonkSpongeConstantsKimchi` and `pasta::fp_kimchi::static_params()`) —
//!    the function o1js compiles into its Poseidon gate at **13 measured
//!    o1js rows** (`bridge/mina-zkapp/scripts/mina-poseidon-merkle-rows.ts`).
//! 2. [`compress`] — `TruncatedPermutation<MinaPoseidonPerm, 2, 1, 3>` — is
//!    *literally* o1js `Poseidon.hash([left, right])`, and `tests/` pins that
//!    against the same o1js gold vectors the probe crate uses. Permuting
//!    `[l, r, 0]` and truncating to one element **is** absorbing two lanes at
//!    rate 2 into a zero state and squeezing `state[0]`; kimchi's `absorb` adds
//!    into `state[0..rate]`, which on a zero state is assignment.

use core::cmp::Ordering;
use core::fmt::{self, Debug, Display, Formatter};
use core::hash::{Hash, Hasher};
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use ark_ff::{
    AdditiveGroup, BigInteger, Field as ArkField, MontFp, PrimeField as ArkPrimeField, Zero,
};
use mina_curves::pasta::Fp;
use mina_poseidon::constants::PlonkSpongeConstantsKimchi;
use mina_poseidon::pasta::{FULL_ROUNDS, fp_kimchi};
use mina_poseidon::permutation::poseidon_block_cipher;
use num_bigint::BigUint;
use p3_field::integers::QuotientMap;
use p3_field::op_assign_macros::{
    impl_add_assign, impl_div_methods, impl_mul_methods, impl_sub_assign, ring_sum,
};
use p3_field::{
    Field, Packable, PrimeCharacteristicRing, PrimeField, RawDataSerializable,
    quotient_map_small_int,
};
use p3_symmetric::{CryptographicPermutation, Permutation, TruncatedPermutation};
use rand::Rng;
use rand::distr::{Distribution, StandardUniform};
use serde::{Deserialize, Deserializer, Serialize};

// ============================================================================
// The field
// ============================================================================

/// The Pasta base field `Fp` — the field o1js `Field` and kimchi's Poseidon
/// live in — presented to Plonky3 as a [`PrimeField`].
///
/// `p = 28948022309329048855892746252171976963363056481941560715954676764349967630337`
/// (254.6 bits, two-adicity 32, multiplicative generator 5).
///
/// The inner `Fp` is public: the whole point of this type is to be a *view*, so
/// crossing back to `mina-poseidon` / `mina-curves` must not need a conversion
/// function nobody can find.
#[derive(Copy, Clone, Default, Eq, PartialEq)]
#[must_use]
pub struct PastaFp(pub Fp);

/// `p` as a decimal string — the same literal `mina_curves`'s `#[modulus = …]`
/// carries and the same value o1js reports as `Field.ORDER`.
pub const PASTA_FP_MODULUS_DEC: &str =
    "28948022309329048855892746252171976963363056481941560715954676764349967630337";

/// `(p + 1) / 2`, i.e. `2^{-1} mod p` — the multiplier [`PrimeCharacteristicRing::halve`] uses.
const TWO_INV: Fp =
    MontFp!("14474011154664524427946373126085988481681528240970780357977338382174983815169");

impl PastaFp {
    /// Wrap an `ark-ff` Pasta element.
    #[inline]
    pub const fn new(inner: Fp) -> Self {
        Self(inner)
    }

    /// The canonical little-endian byte encoding (32 bytes, value `< p`).
    ///
    /// ⚑ **Canonical, not Montgomery** — unlike `p3-bn254`, whose `into_bytes`
    /// exposes its internal Montgomery limbs. This side of the bridge is read
    /// by o1js and by the Rust probe, both of which speak canonical integers,
    /// so a Montgomery encoding would be a trap laid for exactly the reader who
    /// needs it. Greenfield: nothing holds the other shape.
    #[inline]
    pub fn to_canonical_bytes_le(self) -> [u8; 32] {
        let mut out = [0u8; 32];
        let bytes = self.0.into_bigint().to_bytes_le();
        out[..bytes.len()].copy_from_slice(&bytes);
        out
    }

    /// Inverse of [`Self::to_canonical_bytes_le`]. `None` unless the bytes are
    /// exactly 32 long and encode a value `< p` — a non-canonical
    /// representative is **refused**, not silently reduced, so two encodings of
    /// one element cannot both be accepted by a commitment.
    #[inline]
    pub fn from_canonical_bytes_le(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != 32 {
            return None;
        }
        let repr = <Fp as ArkPrimeField>::BigInt::try_from(BigUint::from_bytes_le(bytes)).ok()?;
        Fp::from_bigint(repr).map(Self)
    }
}

impl Packable for PastaFp {}

impl Hash for PastaFp {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write(&self.to_canonical_bytes_le());
    }
}

impl Ord for PastaFp {
    /// By CANONICAL value. `ark-ff`'s own `Ord` compares Montgomery limbs,
    /// which is a different (and meaningless) order; p3 asks for a total order
    /// on the field and this is the one a reader expects.
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.into_bigint().cmp(&other.0.into_bigint())
    }
}

impl PartialOrd for PastaFp {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Display for PastaFp {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.as_canonical_biguint(), f)
    }
}

impl Debug for PastaFp {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.as_canonical_biguint(), f)
    }
}

impl Serialize for PastaFp {
    /// Canonical little-endian bytes — see [`PastaFp::to_canonical_bytes_le`].
    #[inline]
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_bytes(&self.to_canonical_bytes_le())
    }
}

impl<'de> Deserialize<'de> for PastaFp {
    #[inline]
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let bytes: Vec<u8> = Deserialize::deserialize(d)?;
        Self::from_canonical_bytes_le(&bytes)
            .ok_or_else(|| serde::de::Error::custom("Invalid Pasta Fp element"))
    }
}

impl PrimeCharacteristicRing for PastaFp {
    type PrimeSubfield = Self;

    const ZERO: Self = Self(<Fp as AdditiveGroup>::ZERO);
    const ONE: Self = Self(<Fp as ArkField>::ONE);
    const TWO: Self = Self(MontFp!("2"));
    const NEG_ONE: Self = Self(MontFp!(
        "28948022309329048855892746252171976963363056481941560715954676764349967630336"
    ));

    #[inline]
    fn from_prime_subfield(f: Self::PrimeSubfield) -> Self {
        f
    }

    #[inline]
    fn halve(&self) -> Self {
        Self(self.0 * TWO_INV)
    }
}

impl RawDataSerializable for PastaFp {
    const NUM_BYTES: usize = 32;

    #[allow(refining_impl_trait)]
    #[inline]
    fn into_bytes(self) -> [u8; 32] {
        self.to_canonical_bytes_le()
    }

    #[inline]
    fn into_u32_stream(input: impl IntoIterator<Item = Self>) -> impl IntoIterator<Item = u32> {
        input.into_iter().flat_map(|x| {
            let b = x.to_canonical_bytes_le();
            core::array::from_fn::<u32, 8, _>(|i| {
                u32::from_le_bytes([b[4 * i], b[4 * i + 1], b[4 * i + 2], b[4 * i + 3]])
            })
        })
    }

    #[inline]
    fn into_u64_stream(input: impl IntoIterator<Item = Self>) -> impl IntoIterator<Item = u64> {
        input.into_iter().flat_map(|x| {
            let b = x.to_canonical_bytes_le();
            core::array::from_fn::<u64, 4, _>(|i| {
                u64::from_le_bytes(b[8 * i..8 * i + 8].try_into().unwrap())
            })
        })
    }

    #[inline]
    fn into_parallel_byte_streams<const N: usize>(
        input: impl IntoIterator<Item = [Self; N]>,
    ) -> impl IntoIterator<Item = [u8; N]> {
        input.into_iter().flat_map(|vector| {
            let bytes = vector.map(|elem| elem.to_canonical_bytes_le());
            (0..Self::NUM_BYTES).map(move |i| core::array::from_fn(|j| bytes[j][i]))
        })
    }

    #[inline]
    fn into_parallel_u32_streams<const N: usize>(
        input: impl IntoIterator<Item = [Self; N]>,
    ) -> impl IntoIterator<Item = [u32; N]> {
        input.into_iter().flat_map(|vector| {
            let words: [[u32; 8]; N] = vector.map(|elem| {
                let b = elem.to_canonical_bytes_le();
                core::array::from_fn(|i| {
                    u32::from_le_bytes([b[4 * i], b[4 * i + 1], b[4 * i + 2], b[4 * i + 3]])
                })
            });
            (0..(Self::NUM_BYTES / 4)).map(move |i| core::array::from_fn(|j| words[j][i]))
        })
    }

    #[inline]
    fn into_parallel_u64_streams<const N: usize>(
        input: impl IntoIterator<Item = [Self; N]>,
    ) -> impl IntoIterator<Item = [u64; N]> {
        input.into_iter().flat_map(|vector| {
            let words: [[u64; 4]; N] = vector.map(|elem| {
                let b = elem.to_canonical_bytes_le();
                core::array::from_fn(|i| {
                    u64::from_le_bytes(b[8 * i..8 * i + 8].try_into().unwrap())
                })
            });
            (0..(Self::NUM_BYTES / 8)).map(move |i| core::array::from_fn(|j| words[j][i]))
        })
    }
}

impl Field for PastaFp {
    type Packing = Self;

    /// `5` — the generator `mina_curves`'s `#[generator = "5"]` declares.
    const GENERATOR: Self = Self(MontFp!("5"));

    #[inline]
    fn is_zero(&self) -> bool {
        self.0.is_zero()
    }

    #[inline]
    fn try_inverse(&self) -> Option<Self> {
        self.0.inverse().map(Self)
    }

    #[inline]
    fn order() -> BigUint {
        BigUint::parse_bytes(PASTA_FP_MODULUS_DEC.as_bytes(), 10)
            .expect("modulus literal is decimal")
    }
}

impl PrimeField for PastaFp {
    #[inline]
    fn as_canonical_biguint(&self) -> BigUint {
        BigUint::from_bytes_le(&self.0.into_bigint().to_bytes_le())
    }
}

quotient_map_small_int!(PastaFp, u128, [u8, u16, u32, u64]);
quotient_map_small_int!(PastaFp, i128, [i8, i16, i32, i64]);

impl QuotientMap<u128> for PastaFp {
    /// `p > 2^254 > u128::MAX`, so every `u128` is canonical.
    #[inline]
    fn from_int(int: u128) -> Self {
        Self(Fp::from(int))
    }

    #[inline]
    fn from_canonical_checked(int: u128) -> Option<Self> {
        Some(Self::from_int(int))
    }

    #[inline]
    unsafe fn from_canonical_unchecked(int: u128) -> Self {
        Self::from_int(int)
    }
}

impl QuotientMap<i128> for PastaFp {
    /// `p > 2^254 > i128::MAX`, so every `i128` is canonical.
    #[inline]
    fn from_int(int: i128) -> Self {
        if int >= 0 {
            <Self as QuotientMap<u128>>::from_int(int as u128)
        } else {
            -<Self as QuotientMap<u128>>::from_int(int.unsigned_abs())
        }
    }

    #[inline]
    fn from_canonical_checked(int: i128) -> Option<Self> {
        Some(Self::from_int(int))
    }

    #[inline]
    unsafe fn from_canonical_unchecked(int: i128) -> Self {
        Self::from_int(int)
    }
}

impl Add for PastaFp {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self(self.0 + rhs.0)
    }
}

impl Sub for PastaFp {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        Self(self.0 - rhs.0)
    }
}

impl Neg for PastaFp {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        Self(-self.0)
    }
}

impl Mul for PastaFp {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        Self(self.0 * rhs.0)
    }
}

impl_add_assign!(PastaFp);
impl_sub_assign!(PastaFp);
impl_mul_methods!(PastaFp);
ring_sum!(PastaFp);
impl_div_methods!(PastaFp, PastaFp);

impl Distribution<PastaFp> for StandardUniform {
    /// Rejection sampling over the 255-bit range. `p ≈ 2^254.6`, so the top bit
    /// is always clear and acceptance is ~78% per trial.
    #[inline]
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> PastaFp {
        loop {
            let mut bytes = [0u8; 32];
            rng.fill_bytes(&mut bytes);
            bytes[31] &= 0x7f; // clear bit 255; p < 2^255
            if let Some(x) = PastaFp::from_canonical_bytes_le(&bytes) {
                return x;
            }
        }
    }
}

// ============================================================================
// The permutation
// ============================================================================

/// Mina-Poseidon's state width. Kimchi's sponge is `t = 3` (rate 2, capacity 1)
/// — the same width `p3-bn254`'s `Poseidon2Bn254<3>` uses, which is why every
/// type above this drops in unchanged.
pub const PASTA_WIDTH: usize = 3;
/// Sponge/duplex rate in Pasta elements (capacity = 1).
pub const PASTA_RATE: usize = 2;
/// Digest size in Pasta elements: ONE native field element per Merkle node.
pub const PASTA_DIGEST_ELEMS: usize = 1;

/// **Kimchi's own Poseidon permutation**, as a Plonky3
/// [`CryptographicPermutation`].
///
/// `α = 7`, 55 full rounds, width 3, `pasta::fp_kimchi::static_params()`. This
/// is the exact function `mina_poseidon::poseidon::ArithmeticSponge` runs
/// between blocks and the exact function o1js's Poseidon gate evaluates — so
/// the Mina-side verifier hashes NATIVELY rather than emulating a foreign
/// prime. Measured at **13 o1js rows** per call.
///
/// ⚠ **55 full rounds is ~2× the S-boxes of `Poseidon2Bn254<3>`** (8 full + 56
/// partial). That is a real dregg-side PROVER cost and it is the price of the
/// Mina-side win; see `DreggMinaConfig`'s docs for the measured figure.
#[derive(Clone, Copy, Debug, Default)]
pub struct MinaPoseidonPerm;

impl Permutation<[PastaFp; PASTA_WIDTH]> for MinaPoseidonPerm {
    #[inline]
    fn permute_mut(&self, state: &mut [PastaFp; PASTA_WIDTH]) {
        let mut inner: [Fp; PASTA_WIDTH] = [state[0].0, state[1].0, state[2].0];
        poseidon_block_cipher::<Fp, PlonkSpongeConstantsKimchi, FULL_ROUNDS>(
            fp_kimchi::static_params(),
            &mut inner,
        );
        for (out, val) in state.iter_mut().zip(inner) {
            *out = PastaFp(val);
        }
    }
}

impl CryptographicPermutation<[PastaFp; PASTA_WIDTH]> for MinaPoseidonPerm {}

/// The MMCS 2→1 node compression: permute `[left, right, 0]`, take lane 0.
///
/// This IS o1js `Poseidon.hash([left, right])` — one native Poseidon gate chain
/// per Merkle level, measured at 13 rows (15.5 with the conditional swap) where
/// the deployed Poseidon2-BabyBear level costs 2,677.
pub type PastaCompress = TruncatedPermutation<MinaPoseidonPerm, 2, PASTA_DIGEST_ELEMS, PASTA_WIDTH>;

/// Out-of-circuit twin of [`PastaCompress`], for KATs and emitters.
#[inline]
pub fn compress(left: PastaFp, right: PastaFp) -> PastaFp {
    let mut state = [left, right, PastaFp::ZERO];
    MinaPoseidonPerm.permute_mut(&mut state);
    state[0]
}

/// The o1js `Poseidon.hash` semantics, for gold-KAT purposes: zero initial
/// state, absorb at rate 2 by ADDITION, squeeze `state[0]` after a final
/// permutation.
///
/// ⚠ This is **not** the MMCS leaf hash. The leaf hash is
/// `MultiField32PaddingFreeSponge`, which OVERWRITES the rate lanes per block
/// rather than adding into them; the two coincide on a single block (a zero
/// state makes `+=` an assignment) and diverge past 16 packed BabyBear lanes.
/// `DreggMinaConfig` uses the p3 sponge; this function exists so the
/// permutation itself can be pinned against o1js's published vectors.
#[inline]
pub fn mina_poseidon_hash(inputs: &[PastaFp]) -> PastaFp {
    let mut state = [PastaFp::ZERO; PASTA_WIDTH];
    let mut n = 0usize;
    for x in inputs {
        if n == PASTA_RATE {
            MinaPoseidonPerm.permute_mut(&mut state);
            n = 0;
        }
        state[n] += *x;
        n += 1;
    }
    MinaPoseidonPerm.permute_mut(&mut state);
    state[0]
}
