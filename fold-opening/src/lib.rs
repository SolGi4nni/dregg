//! **The BFV fold as a common-point opening, not a circuit.**
//!
//! `fhegg_core::bfv_lean::fold_add` is a *linear* map on ciphertexts. The
//! multilinear extension is *also* linear. So if
//!
//! ```text
//!     c_out = sum_k a_k * c_k
//! ```
//!
//! then the MLEs satisfy `chat_out = sum_k a_k * chat_k` **as polynomials**, hence at
//! *every* point. One evaluation at one random common point `r` therefore certifies
//! the entire fold: **zero sumcheck rounds, zero per-addition constraints.**
//!
//! The AIR route must materialise every addition it constrains — `Theta(B*N*L)`. This
//! route commits only the *result* — `Theta(N*L)`. The spec, the three binding
//! conditions and the measured ratio live in
//! `~/dev/zkml-research/notes/fold-as-opening.md`.
//!
//! # SUBSTRATE, said out loud
//!
//! **No AIR, constraint, gadget or `air_accepts` predicate is authored here.** House
//! law: the relation is a Lean object. `notes/fold-as-opening.md` §2 states it in the
//! shape the Lean theorem takes. What lives in this crate is (i) the MLE construction
//! over real deployed-shape ciphertexts, (ii) the Fiat-Shamir binding, (iii) the range
//! leg as a *check on values*, and (iv) adversaries that make the protocol FAIL when a
//! binding condition is removed. None of that is a constraint system.
//!
//! # ⚑ STUB — the one thing this crate does not have
//!
//! **There is no polynomial commitment.** [`FoldOpening::values`] are numbers the
//! prover *asserts*; nothing ties them to [`FoldOpening::commitments`]. A real
//! deployment discharges each `chat_k(r)` against `C_k` with a multilinear PCS
//! (BaseFold/WHIR — `p3-sumcheck`'s `layout` + `commit_base` at the pinned revision is
//! the candidate; see `notes/multilinear-pcs-landscape.md`). Everything upstream of
//! that opening — the limb map, the linearity, the transcript order, the range leg — is
//! real and is what this crate measures.
//!
//! Do **not** read a passing [`verify`] as "the prover knew ciphertexts summing to
//! `c_out`". Read it as: *given* honestly-opened evaluations, the linear relation holds
//! with soundness error `mu / |EF|`, and each of the three binding conditions is
//! demonstrated to be load-bearing by a test that removes it and forges.
//!
//! The commitments themselves are real (a Poseidon2 sponge over the whole limb vector,
//! binding but not hiding and not openable); they exist so the transcript has something
//! honest to absorb, which is what makes the coefficient-binding adversary meaningful.

use fhegg_core::bfv_lean::LeanCiphertext;
use p3_baby_bear::{BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16};
use p3_challenger::{CanObserve, CanSample, DuplexChallenger, FieldChallenger};
use p3_field::extension::BinomialExtensionField;
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_multilinear_util::point::Point;
use p3_multilinear_util::poly::Poly;

/// Base field — the one the deployed STARK prover uses.
pub type F = BabyBear;

/// Challenge field: degree-4 binomial extension, ~2^124 of challenge space.
///
/// ⚑ Sampling `r` from `F` instead would give soundness error `mu / 2^31 ~ 2^-27` on the
/// *whole fold* — below the repo's ~124-bit bar. See `notes/fold-as-opening.md` §2.4.
pub type EF = BinomialExtensionField<BabyBear, 4>;

/// Width-16 Poseidon2 over BabyBear, deployed constants.
pub type Perm16 = Poseidon2BabyBear<16>;

/// The Fiat-Shamir transcript, structurally identical to the deployed
/// `DuplexChallenger` in `circuit/src/stark_zk.rs`.
pub type Challenger = DuplexChallenger<F, Perm16, 16, 8>;

/// A commitment digest. Poseidon2-sponge over the limb vector.
pub type Digest = [F; 8];

/// Radix of the limb decomposition, in bits.
///
/// A deployed RNS residue is up to `0x1_ffff_e0001 ~ 2^37`, which does **not** fit in
/// BabyBear (`p ~ 2^31`). Two 19-bit limbs cover 38 bits with room to spare, and 19 is
/// the largest radix for which `B * 2^w < p` still admits a batch of thousands.
pub const LIMB_BITS: u32 = 19;

/// Limbs per RNS residue.
pub const LIMBS: usize = 2;

/// Exclusive per-limb bound of a *canonical* input: `2^LIMB_BITS`.
pub const LIMB_BOUND: u64 = 1u64 << LIMB_BITS;

/// Builds a fresh transcript over the deployed Poseidon2 constants.
#[must_use]
pub fn challenger() -> Challenger {
    Challenger::new(default_babybear_poseidon2_16())
}

/// The largest fold batch whose lazily-accumulated limbs are guaranteed `< p`, for
/// 0/1 (or unit-magnitude) coefficients.
///
/// Beyond this the accumulator wraps in the *proof field* and the linearity check
/// silently certifies the wrong integer. This is one half of binding condition (b);
/// [`RangeLeg`] is the other and is the one that actually enforces it.
#[must_use]
pub fn max_unit_batch() -> usize {
    // largest B with B * (2^w - 1) <= p - 1
    let p = u64::from(F::ORDER_U32);
    ((p - 1) / (LIMB_BOUND - 1)) as usize
}

// ---------------------------------------------------------------------------
// the limb map — `flat` of the spec
// ---------------------------------------------------------------------------

/// Layout of the flattened limb vector, fixed and public.
///
/// Index order is **poly-major, then modulus, then coefficient, then limb**:
///
/// ```text
///     idx(pi, j, i, l) = (((pi * L) + j) * N + i) * LIMBS + l
/// ```
///
/// Both the prover and the verifier must agree on it; it is part of the statement, not
/// an implementation detail. Changing it changes what `C_k` commits to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Shape {
    /// Polynomials per ciphertext (2 on the fold path).
    pub polys: usize,
    /// RNS moduli (3 deployed).
    pub moduli: usize,
    /// Ring degree (4096 deployed).
    pub degree: usize,
}

impl Shape {
    /// The deployed fold shape: `fhegg_core::bfv_lean::FOLD_DEGREE` and the three
    /// `FOLD_MODULI`, two polynomials.
    #[must_use]
    pub const fn deployed() -> Self {
        Self {
            polys: 2,
            moduli: 3,
            degree: fhegg_core::bfv_lean::FOLD_DEGREE,
        }
    }

    /// Residues per ciphertext, `M = P * L * N`.
    #[must_use]
    pub const fn residues(&self) -> usize {
        self.polys * self.moduli * self.degree
    }

    /// Field elements per ciphertext, `M * LIMBS`.
    #[must_use]
    pub const fn limbs(&self) -> usize {
        self.residues() * LIMBS
    }

    /// Number of MLE variables, `mu = ceil(log2(M * LIMBS))`.
    #[must_use]
    pub fn num_variables(&self) -> usize {
        self.limbs().next_power_of_two().ilog2() as usize
    }

    /// Reads the shape off a parsed ciphertext.
    #[must_use]
    pub fn of(ct: &LeanCiphertext) -> Self {
        Self {
            polys: ct.polys.len(),
            moduli: ct.moduli.len(),
            degree: ct.degree,
        }
    }
}

/// Why a fold-opening operation refused.
#[derive(Debug, PartialEq, Eq)]
pub enum FoldError {
    /// Two inputs disagree on `(P, L, N)`.
    ShapeMismatch { expected: Shape, actual: Shape },
    /// An empty batch has no fold.
    EmptyBatch,
    /// `coeffs.len() != cts.len()`.
    CoefficientCount { cts: usize, coeffs: usize },
    /// A residue was `>= q_j`. The strict wire parser already refuses these; a
    /// hand-built fixture can still carry one, and the limb map would be ambiguous.
    NonCanonical { modulus_index: usize },
    /// The linearity check at the common point failed.
    LinearityFailed { claimed: EF, expected: EF },
    /// A limb of the claimed result exceeded the declared bound: binding condition (b).
    OutOfRange {
        index: usize,
        value: u64,
        bound: u64,
    },
    /// The declared bound is at or above the field order, so the range leg cannot
    /// exclude a `p`-wrap and the whole argument is vacuous.
    BoundExceedsField { bound: u64, order: u64 },
}

impl core::fmt::Display for FoldError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::ShapeMismatch { expected, actual } => {
                write!(f, "shape mismatch: expected {expected:?}, got {actual:?}")
            }
            Self::EmptyBatch => write!(f, "empty batch"),
            Self::CoefficientCount { cts, coeffs } => {
                write!(f, "{cts} ciphertexts but {coeffs} coefficients")
            }
            Self::NonCanonical { modulus_index } => {
                write!(f, "non-canonical residue under modulus {modulus_index}")
            }
            Self::LinearityFailed { claimed, expected } => write!(
                f,
                "linearity failed at the common point: claimed {claimed:?} != {expected:?}"
            ),
            Self::OutOfRange {
                index,
                value,
                bound,
            } => write!(
                f,
                "limb {index} = {value} exceeds the declared bound {bound}"
            ),
            Self::BoundExceedsField { bound, order } => write!(
                f,
                "declared bound {bound} is not below the field order {order}: the range leg \
                 cannot exclude a field wrap, so the linearity check is vacuous"
            ),
        }
    }
}

impl std::error::Error for FoldError {}

type Result<T> = core::result::Result<T, FoldError>;

/// Flattens a canonical parsed ciphertext into its limb vector, `flat(c)`.
///
/// # Errors
///
/// [`FoldError::NonCanonical`] if any residue is `>= q_j`.
pub fn flatten(ct: &LeanCiphertext) -> Result<Vec<F>> {
    let mut out = Vec::with_capacity(Shape::of(ct).limbs());
    for poly in &ct.polys {
        for (modulus_index, (row, &q)) in poly.rows.iter().zip(ct.moduli.iter()).enumerate() {
            for &v in row {
                if v >= q {
                    return Err(FoldError::NonCanonical { modulus_index });
                }
                for l in 0..LIMBS {
                    out.push(F::from_u64(
                        (v >> (LIMB_BITS * l as u32)) & (LIMB_BOUND - 1),
                    ));
                }
            }
        }
    }
    Ok(out)
}

/// A lazily-accumulated fold: limbs summed componentwise, **no carry between limbs and
/// no reduction mod `q_j`**.
///
/// This is the object the linear route certifies. It is a *redundant* representation of
/// the ciphertext `sum_k a_k c_k`: residue `(pi, j, i)` has value
/// `sum_l 2^(l*LIMB_BITS) * limbs[idx(pi,j,i,l)]`, which is congruent to the true sum
/// mod `q_j` but is not reduced and whose limbs are not normalised.
///
/// The deployed `bfv_lean::fold` does **not** produce this — it reduces at every step
/// (`add_row`, `bfv_lean.rs:497`). Lazy accumulation is a *change* to that function, and
/// on our own carrier it is 27% faster (`notes/fold-as-opening.md` §5).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LimbAccumulator {
    /// Shape of every input, carried so the verifier can check the MLE arity.
    pub shape: Shape,
    /// Componentwise limb sums, length `shape.limbs()`. Each entry `< bound`.
    pub limbs: Vec<u64>,
    /// Exclusive per-limb bound the prover declares. Must be `< p`.
    pub bound: u64,
    /// Batch size `B`, carried for accounting only.
    pub terms: usize,
}

impl LimbAccumulator {
    /// `flat` of the accumulator, in the same layout as [`flatten`].
    ///
    /// # Panics
    ///
    /// If a limb does not fit the field. Callers should run [`RangeLeg::check`] first,
    /// which returns an error instead.
    #[must_use]
    pub fn to_field(&self) -> Vec<F> {
        self.limbs
            .iter()
            .map(|&v| {
                assert!(
                    v < u64::from(F::ORDER_U32),
                    "limb {v} does not fit BabyBear; run RangeLeg::check first"
                );
                F::from_u64(v)
            })
            .collect()
    }
}

/// Lazily folds `sum_k a_k * c_k` with **unit-magnitude** coefficients `a_k in {0, 1}` —
/// the deployed shape, where `a_k` is the `side` bit of a signed order envelope
/// (`fhegg-fhe/src/additive.rs:210`).
///
/// No modular reduction and no inter-limb carry occurs, which is exactly the side
/// condition the linear route needs.
///
/// # Errors
///
/// Shape/coefficient mismatches, or a non-canonical input residue.
pub fn lazy_fold(cts: &[LeanCiphertext], coeffs: &[u64]) -> Result<LimbAccumulator> {
    if cts.is_empty() {
        return Err(FoldError::EmptyBatch);
    }
    if cts.len() != coeffs.len() {
        return Err(FoldError::CoefficientCount {
            cts: cts.len(),
            coeffs: coeffs.len(),
        });
    }
    let shape = Shape::of(&cts[0]);
    let mut acc = vec![0u64; shape.limbs()];
    for (ct, &a) in cts.iter().zip(coeffs.iter()) {
        let s = Shape::of(ct);
        if s != shape {
            return Err(FoldError::ShapeMismatch {
                expected: shape,
                actual: s,
            });
        }
        let mut idx = 0usize;
        for poly in &ct.polys {
            for (modulus_index, (row, &q)) in poly.rows.iter().zip(ct.moduli.iter()).enumerate() {
                for &v in row {
                    if v >= q {
                        return Err(FoldError::NonCanonical { modulus_index });
                    }
                    for l in 0..LIMBS {
                        acc[idx] += a * ((v >> (LIMB_BITS * l as u32)) & (LIMB_BOUND - 1));
                        idx += 1;
                    }
                }
            }
        }
    }
    let weight: u64 = coeffs.iter().sum();
    Ok(LimbAccumulator {
        shape,
        limbs: acc,
        bound: weight.max(1) * (LIMB_BOUND - 1) + 1,
        terms: cts.len(),
    })
}

/// A lazily-accumulated fold held as **unreduced RNS residues** — the FHE-side object,
/// with no limb map in it.
///
/// This is what a delayed-reduction BFV accumulator actually holds: `add_row` minus the
/// conditional subtract. It exists so the *FHE-side* price of the no-reduction side
/// condition can be measured against the deployed `fold` without the proof-side limb map
/// contaminating the comparison. It represents the same ciphertext as the
/// [`LimbAccumulator`] built from the same inputs, differing only by carry normalisation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResidueAccumulator {
    /// Shape of every input.
    pub shape: Shape,
    /// `[poly][modulus][coeff]`, unreduced: entries may be `>= q_j`.
    pub rows: Vec<Vec<Vec<u64>>>,
    /// Batch size.
    pub terms: usize,
}

/// The FHE-side lazy fold: componentwise `sum_k a_k * v_k` with **no conditional
/// subtract**, which is the entire difference from `bfv_lean::add_row`.
///
/// # Errors
///
/// Shape or coefficient-count mismatch, or an empty batch.
pub fn lazy_fold_residues(cts: &[LeanCiphertext], coeffs: &[u64]) -> Result<ResidueAccumulator> {
    if cts.is_empty() {
        return Err(FoldError::EmptyBatch);
    }
    if cts.len() != coeffs.len() {
        return Err(FoldError::CoefficientCount {
            cts: cts.len(),
            coeffs: coeffs.len(),
        });
    }
    let shape = Shape::of(&cts[0]);
    // Seed from the first term rather than zero-initialising and adding it, so this does
    // the same B-1 accumulation passes `bfv_lean::fold` does (which clones the first
    // ciphertext). Otherwise the comparison charges lazy an extra full pass, which at
    // B=4 is a 4/3 penalty that is an artefact of the loop shape, not of laziness.
    let a0 = coeffs[0];
    let mut rows: Vec<Vec<Vec<u64>>> = cts[0]
        .polys
        .iter()
        .map(|poly| {
            poly.rows
                .iter()
                .map(|row| row.iter().map(|&v| a0 * v).collect())
                .collect()
        })
        .collect();
    for (ct, &a) in cts.iter().zip(coeffs.iter()).skip(1) {
        if Shape::of(ct) != shape {
            return Err(FoldError::ShapeMismatch {
                expected: shape,
                actual: Shape::of(ct),
            });
        }
        for (pi, poly) in ct.polys.iter().enumerate() {
            for (j, row) in poly.rows.iter().enumerate() {
                let dst = &mut rows[pi][j];
                // The deployed coefficients are the 0/1 `side` selector, so the
                // multiply-free paths are the ones that matter; specialising them keeps
                // the comparison against `add_row` (which has no multiply either) fair.
                match a {
                    0 => {}
                    1 => {
                        for (d, &v) in dst.iter_mut().zip(row.iter()) {
                            *d += v;
                        }
                    }
                    _ => {
                        for (d, &v) in dst.iter_mut().zip(row.iter()) {
                            *d += a * v;
                        }
                    }
                }
            }
        }
    }
    Ok(ResidueAccumulator {
        shape,
        rows,
        terms: cts.len(),
    })
}

/// Binding condition (b), as an enforceable check rather than an assumption.
///
/// The linearity check of §2.3 proves equality **in `F`**, i.e. mod `p`. FHE semantics
/// is equality in `Z`. Mod-`p` equality gives integer equality only if both sides are
/// `< p`. This leg forbids the difference: a claimed result equal to the true sum
/// **plus a multiple of `p`**.
///
/// Cost: `Theta(N*L)` — one range check per *result* limb, never per addition. **This is
/// the `Theta(N*L)` in "the linear route is `Theta(N*L)`".** The linear route does not
/// delete the reduction; it amortises it to once instead of `B` times.
///
/// In a deployed system this is a Lean-authored constraint (a lookup against a range
/// table). Here it is a value check, so the *cost model* below is a derivation, not a
/// measurement of an emitted AIR.
#[derive(Clone, Copy, Debug)]
pub struct RangeLeg {
    /// Exclusive bound every result limb must respect.
    pub bound: u64,
}

impl RangeLeg {
    /// The leg implied by a batch of `terms` unit-coefficient ciphertexts.
    #[must_use]
    pub const fn for_unit_batch(terms: usize) -> Self {
        Self {
            bound: (terms as u64) * (LIMB_BOUND - 1) + 1,
        }
    }

    /// Refuses unless every limb is in range **and** the bound itself is below the
    /// field order.
    ///
    /// The second condition is not decoration: a bound `>= p` makes the leg unable to
    /// exclude a field wrap, and the linearity check then certifies nothing about the
    /// integers. It is the difference between a check and a comment.
    ///
    /// # Errors
    ///
    /// [`FoldError::BoundExceedsField`] or [`FoldError::OutOfRange`].
    pub fn check(&self, acc: &LimbAccumulator) -> Result<()> {
        let order = u64::from(F::ORDER_U32);
        if self.bound > order {
            return Err(FoldError::BoundExceedsField {
                bound: self.bound,
                order,
            });
        }
        for (index, &value) in acc.limbs.iter().enumerate() {
            if value >= self.bound {
                return Err(FoldError::OutOfRange {
                    index,
                    value,
                    bound: self.bound,
                });
            }
        }
        Ok(())
    }

    /// Range-check *sites* this leg costs, i.e. `M * LIMBS`. Independent of `B` — that
    /// is the whole point.
    #[must_use]
    pub const fn sites(shape: Shape) -> usize {
        shape.limbs()
    }
}

// ---------------------------------------------------------------------------
// commitments and the transcript
// ---------------------------------------------------------------------------

/// A Poseidon2 sponge digest of a limb vector.
///
/// Binding, not hiding, and **not openable** — there is no evaluation proof against it.
/// It exists so the transcript absorbs something honest before `r` is drawn, which is
/// what makes the coefficient-binding adversary in the tests meaningful rather than
/// theatrical.
#[must_use]
pub fn commit(limbs: &[F]) -> Digest {
    let mut sponge = challenger();
    sponge.observe(F::from_u64(limbs.len() as u64));
    sponge.observe_slice(limbs);
    sponge.sample_array::<8>()
}

/// Absorbs the public statement and draws the common evaluation point.
///
/// **Order is the statement, not a convention.** `r` is drawn only after every
/// commitment *and* every coefficient has been absorbed. Draw it earlier and a prover
/// solves one equation in `B` unknowns for any result it likes — binding condition (a),
/// demonstrated live by `forges_when_coefficients_are_chosen_after_the_challenge`.
pub fn draw_point(
    shape: Shape,
    commitments: &[Digest],
    out_commitment: &Digest,
    coeffs: &[F],
    bound: u64,
) -> Point<EF> {
    let mut ch = challenger();
    ch.observe(F::from_u64(shape.polys as u64));
    ch.observe(F::from_u64(shape.moduli as u64));
    ch.observe(F::from_u64(shape.degree as u64));
    ch.observe(F::from_u64(commitments.len() as u64));
    for d in commitments {
        ch.observe_slice(d);
    }
    ch.observe_slice(out_commitment);
    ch.observe_slice(coeffs);
    ch.observe(F::from_u64(bound));
    let mu = shape.num_variables();
    Point::new((0..mu).map(|_| ch.sample_algebra_element::<EF>()).collect())
}

// ---------------------------------------------------------------------------
// the protocol
// ---------------------------------------------------------------------------

/// Everything the prover sends. **No opening proofs** — see the crate-level `STUB`.
#[derive(Clone, Debug)]
pub struct FoldOpening {
    /// Shape of every ciphertext in the batch.
    pub shape: Shape,
    /// `C_k = commit(flat(c_k))`, in batch order.
    pub commitments: Vec<Digest>,
    /// `C_out = commit(flat(c_out))`.
    pub out_commitment: Digest,
    /// The public coefficients `a_k`.
    pub coeffs: Vec<F>,
    /// The declared range bound on every result limb.
    pub bound: u64,
    /// `chat_k(r)`, in batch order. ⚑ Asserted, not proved.
    pub values: Vec<EF>,
    /// `chat_out(r)`. ⚑ Asserted, not proved.
    pub out_value: EF,
}

/// Builds the MLE of a limb vector, zero-padded to the next power of two.
#[must_use]
pub fn mle(limbs: &[F]) -> Poly<F> {
    let mut v = limbs.to_vec();
    v.resize(limbs.len().next_power_of_two(), F::ZERO);
    Poly::new(v)
}

/// Proves the fold: commit, draw the common point, evaluate.
///
/// `out` is the lazily-accumulated result. The prover does **not** run a sumcheck; it
/// evaluates `B + 1` multilinears at one point.
///
/// # Errors
///
/// Shape/coefficient mismatch, non-canonical input, or a result limb out of range
/// (which means the prover reduced, or wrapped, or is lying).
pub fn prove(cts: &[LeanCiphertext], coeffs: &[u64], out: &LimbAccumulator) -> Result<FoldOpening> {
    if cts.len() != coeffs.len() {
        return Err(FoldError::CoefficientCount {
            cts: cts.len(),
            coeffs: coeffs.len(),
        });
    }
    RangeLeg { bound: out.bound }.check(out)?;

    let flats: Vec<Vec<F>> = cts.iter().map(flatten).collect::<Result<_>>()?;
    let commitments: Vec<Digest> = flats.iter().map(|f| commit(f)).collect();
    let out_flat = out.to_field();
    let out_commitment = commit(&out_flat);
    let coeff_f: Vec<F> = coeffs.iter().map(|&a| F::from_u64(a)).collect();

    let r = draw_point(
        out.shape,
        &commitments,
        &out_commitment,
        &coeff_f,
        out.bound,
    );

    let values = flats.iter().map(|f| mle(f).eval_base(&r)).collect();
    let out_value = mle(&out_flat).eval_base(&r);

    Ok(FoldOpening {
        shape: out.shape,
        commitments,
        out_commitment,
        coeffs: coeff_f,
        bound: out.bound,
        values,
        out_value,
    })
}

/// What a successful [`verify`] establishes, and what it still owes.
///
/// The `point` is the outstanding obligation made visible in the type: a real
/// deployment must prove `values[k] = chat_k(point)` against `commitments[k]`, and
/// `out_value = chat_out(point)` against `out_commitment`, with a multilinear PCS.
/// **Nothing in this crate consumes `point`** — that absence *is* the stub, and it is
/// deliberately a field rather than a `let _ =` so it cannot be read as discharged.
#[derive(Clone, Debug)]
#[must_use]
pub struct VerifiedAt {
    /// The common opening point the transcript pinned. Owed to a PCS.
    pub point: Point<EF>,
}

/// Verifies a fold opening.
///
/// Redraws `r` from the same transcript and checks the single field equation
/// `chat_out(r) = sum_k a_k * chat_k(r)`. That equation is the entire protocol: **no
/// sumcheck round runs, on either side.**
///
/// ⚑ This does **not** check `values` against `commitments` — there is no PCS here.
/// See the crate-level `STUB` and [`VerifiedAt`].
///
/// # Errors
///
/// [`FoldError::LinearityFailed`], or a bound that cannot exclude a field wrap.
pub fn verify(proof: &FoldOpening) -> Result<VerifiedAt> {
    let order = u64::from(F::ORDER_U32);
    if proof.bound > order {
        return Err(FoldError::BoundExceedsField {
            bound: proof.bound,
            order,
        });
    }
    let point = draw_point(
        proof.shape,
        &proof.commitments,
        &proof.out_commitment,
        &proof.coeffs,
        proof.bound,
    );

    let expected: EF = proof
        .coeffs
        .iter()
        .zip(proof.values.iter())
        .map(|(&a, &v)| v * a)
        .sum();
    if expected != proof.out_value {
        return Err(FoldError::LinearityFailed {
            claimed: proof.out_value,
            expected,
        });
    }
    Ok(VerifiedAt { point })
}

/// Deliberately-broken variants, so the binding conditions can be **refuted**, not just
/// asserted.
///
/// A check that cannot be made to fail is not a check. Each function here removes
/// exactly one binding condition from `notes/fold-as-opening.md` §2.6 so a test can
/// forge against it. **Nothing outside `tests/` may call these.**
pub mod adversary {
    use super::{Digest, EF, F, Point, Shape, challenger};
    use p3_challenger::{CanObserve, FieldChallenger};
    use p3_field::PrimeCharacteristicRing;

    /// [`super::draw_point`] with the coefficients **not** absorbed — binding condition
    /// (a) removed.
    ///
    /// This is the natural mistake: the coefficients feel like they belong to the
    /// witness (they describe *how* the prover folded), so absorbing only the
    /// commitments looks complete. It is a total break.
    #[must_use]
    pub fn draw_point_without_coefficients(
        shape: Shape,
        commitments: &[Digest],
        out_commitment: &Digest,
        bound: u64,
    ) -> Point<EF> {
        let mut ch = challenger();
        ch.observe(F::from_u64(shape.polys as u64));
        ch.observe(F::from_u64(shape.moduli as u64));
        ch.observe(F::from_u64(shape.degree as u64));
        ch.observe(F::from_u64(commitments.len() as u64));
        for d in commitments {
            ch.observe_slice(d);
        }
        ch.observe_slice(out_commitment);
        ch.observe(F::from_u64(bound));
        let mu = shape.num_variables();
        Point::new((0..mu).map(|_| ch.sample_algebra_element::<EF>()).collect())
    }
}

// ---------------------------------------------------------------------------
// cost accounting — DERIVED, and both accountings are reported
// ---------------------------------------------------------------------------

/// Committed field elements under each route.
///
/// The prover is hash-bound and hash work is proportional to committed elements
/// (`notes/prover-floor.md`), so committed elements is the right currency.
///
/// ⚠ Every column count below is a **derivation with named parameters**, not a
/// measurement of an emitted AIR. There is no AIR for `fold_add` in the tree to measure
/// (`notes/prover-floor.md`: "fold_add, ct*pt and ct*ct have no AIR at all"), so this
/// prices the AIR that *would* be written.
#[derive(Clone, Copy, Debug)]
pub struct CostModel {
    /// Base columns a modular-add site commits: the partial sum and the borrow flag.
    pub add_columns: usize,
    /// Base felts one range/lookup argument contributes per site. The repo's measured
    /// figure is 4 (a LogUp extension-field aux column at degree-4 extension).
    pub lookup_felts: usize,
    /// Inter-limb carry columns per residue per add. The linear route has none — that
    /// is what "zero carries" means.
    pub carry_columns: usize,
}

impl Default for CostModel {
    /// Deliberately **conservative to the AIR**: 2 base columns + one range lookup, not
    /// the 34-elements-per-site the repo measures at real circuit sites. If the ratio
    /// holds here it holds a fortiori at 34.
    fn default() -> Self {
        Self {
            add_columns: 2,
            lookup_felts: 4,
            carry_columns: 1,
        }
    }
}

/// A priced comparison at one `(shape, B)`.
#[derive(Clone, Copy, Debug)]
pub struct Accounting {
    /// Batch size.
    pub batch: usize,
    /// AIR-route committed elements, inputs excluded (marginal).
    pub air_marginal: u128,
    /// Linear-route committed elements, inputs excluded (marginal).
    pub linear_marginal: u128,
    /// AIR-route committed elements, inputs included (total system).
    pub air_total: u128,
    /// Linear-route committed elements, inputs included (total system).
    pub linear_total: u128,
}

impl Accounting {
    /// Ratio under marginal accounting — inputs already committed for other reasons
    /// (they are: the attestation already binds every ordered input). **This is the
    /// accounting in which "ratio = B" is true.**
    #[must_use]
    pub fn marginal_ratio(&self) -> f64 {
        self.air_marginal as f64 / self.linear_marginal as f64
    }

    /// Ratio under total-system accounting — every input commitment charged to the
    /// comparison. **This one saturates at the per-add column count, not `B`.**
    #[must_use]
    pub fn total_ratio(&self) -> f64 {
        self.air_total as f64 / self.linear_total as f64
    }
}

/// Prices both routes at one batch size.
#[must_use]
pub fn account(shape: Shape, batch: usize, model: CostModel) -> Accounting {
    let limbs = shape.limbs() as u128;
    let b = batch as u128;
    let adds = b.saturating_sub(1); // a B-term fold is B-1 additions

    // AIR: every addition is a site, on every limb, and each site carries its columns,
    // its range lookup, and an inter-limb carry.
    let per_site = (model.add_columns + model.lookup_felts) as u128;
    let air_marginal = limbs * adds * per_site + limbs * adds * model.carry_columns as u128;
    // Linear: only the result is committed, plus its one-time range leg.
    let linear_marginal = limbs * (1 + model.lookup_felts as u128);

    let inputs = limbs * b;
    Accounting {
        batch,
        air_marginal,
        linear_marginal,
        air_total: air_marginal + inputs,
        linear_total: linear_marginal + inputs,
    }
}

// ---------------------------------------------------------------------------
// fixtures
// ---------------------------------------------------------------------------

/// A deterministic canonical ciphertext at the deployed shape.
///
/// Not an encryption of anything — the fold is an *algebraic* claim about residues and
/// never touches a key. Using real encryptions would change nothing this crate checks
/// and would drag `fhe.rs` keygen into a measurement harness.
#[must_use]
pub fn fixture(shape: Shape, seed: u64) -> LeanCiphertext {
    use fhegg_core::bfv_lean::{FOLD_MODULI, RnsPoly};
    let moduli: Vec<u64> = FOLD_MODULI[..shape.moduli].to_vec();
    let mut state = seed.wrapping_mul(0x9E37_79B9_7F4A_7C15).wrapping_add(1);
    let mut next = move || {
        state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    };
    let polys = (0..shape.polys)
        .map(|_| RnsPoly {
            rows: moduli
                .iter()
                .map(|&q| (0..shape.degree).map(|_| next() % q).collect())
                .collect(),
        })
        .collect();
    LeanCiphertext {
        moduli,
        degree: shape.degree,
        level: 0,
        variable_time: false,
        polys,
        plain_bound: 1,
    }
}
