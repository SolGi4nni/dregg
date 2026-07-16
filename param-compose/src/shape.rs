//! **THE SHAPE** — the build-time bounds that define a VK class, and nothing else.
//!
//! The whole point of this crate is what is NOT in here. A [`ComposeShape`] carries
//! *maxima* (fuel/DoS bounds), never content:
//!
//!   * no role list — a role is an opaque field element the ruleset addresses by value;
//!   * no rule table — the coefficients are WITNESSED and bound to a public `ruleset_root`;
//!   * no param names or count — `max_params` is a bound; the ACTIVE `param_count` is
//!     runtime data bound into `subjects_root`;
//!   * no subject count — `max_subjects` is a bound; the ACTIVE `subject_count` is a PI.
//!
//! So a new game / creature system / institution is a **new ruleset root + new content
//! under an existing VK**, as long as it fits the shape's bounds. Only crossing a BOUND
//! (more subjects, more params, more knots) mints a new VK — the same way a bigger board
//! mints a new size class, not a new kernel.

/// The deployed program-validation caps this AIR is measured against
/// (`dregg_circuit::dsl::circuit`). Re-exported here so the budget story is local.
pub use dregg_circuit::dsl::circuit::{MAX_CONSTRAINT_DEGREE, MAX_PUBLIC_INPUTS, MAX_TRACE_WIDTH};

/// **THE BINDING WIDTH.** Number of BabyBear felts in a committed root (`ruleset_root`,
/// `subjects_root`, `outcome_commitment`, `explanation_root`) — the native output width of
/// the `cap_node8` compression the digest is built from (see [`crate::digest`]).
///
/// Each felt carries ~31 bits, so 8 felts give a ~248-bit digest with a ~124-bit collision
/// floor, matching the deployed 8-felt `WideHash` / `CellState::compute_commitment_8` and
/// sitting above the ~112.6-bit FRI soundness floor.
///
/// # It is not a knob (it used to be)
///
/// The digest is a Merkle-Damgård chain over `ConstraintExpr::MerkleHash8` — the native
/// `cap_node8` arity-16 compression, ONE Poseidon2 site whose 8 output lanes are all
/// program-owned columns. So all 8 felts are bound by one site at zero lane-column cost.
/// This width used to be a `ComposeShape` field (`W`) because the custom-leaf lowering
/// once REFUSED `MerkleHash8` and the AIR reached ~124 bits only via `W = 8` parallel
/// 4-ary (`Hash4to1`) chains — paying an 8× site multiplier and 7 lane columns per site in
/// the lowered leaf. That refusal is gone (`circuit/src/custom_leaf_lowering.rs`), so the
/// multiplier and the knob are gone with it.
pub const DIGEST_FELTS: usize = 8;

/// Default width of the subject-identity namespace, in bits (268M identities).
///
/// # Why identities are bounded at all (and why the bound is a SHAPE field, not a constant)
///
/// Canonical ordering is enforced as a STRICT INCREASE of identity across active
/// subjects, which needs a field COMPARISON. `forced_ge0` is only sound when the compared
/// range is small relative to `p ≈ 2^31`: on a full-width 31-bit value BOTH `d` and
/// `-d-1` reduce into range, the comparison bit goes free, and the gadget silently
/// becomes VACUOUS — an ordering tooth with no teeth. Bounding identities to `2^b` with
/// `b <= ~28` keeps `p - d - 1 ≈ 2·10^9` far above `2^(b+1)`, so exactly one comparison
/// bit satisfies the range gadget.
///
/// This bounds the identity ENCODING — never the number of subjects or their kinds. It
/// rides [`ComposeShape::identity_bits`] rather than a crate constant because it is the
/// AIR's single biggest column cost (a `b`-bit namespace spends `b` range columns per
/// subject plus `b+1` per ordering comparison, ~200 columns at the realistic shape), and
/// because a fixed 28 would be exactly the silently-fixed count this crate exists to
/// refuse. A realm sizes its identity namespace; the VK follows the shape.
pub const DEFAULT_IDENTITY_BITS: usize = 28;

/// The largest identity width the ordering comparison stays sound at. Above this the
/// `forced_ge0` non-vacuity margin against `p ≈ 2^31` closes and the tooth goes vacuous;
/// [`ComposeShape::identity_bits_sound`] is the check.
pub const MAX_SOUND_IDENTITY_BITS: usize = 28;

/// The public-input layout version this AIR publishes (PI slot
/// [`crate::pi::ABI_VERSION`]). Bumped when the PI layout changes, so a historical
/// receipt's decoder is selected by a committed value rather than by the server build.
pub const PARAM_COMPOSE_ABI_VERSION: u64 = 1;

/// A composition's build-time bounds. The VK is a function of the shape (plus the AIR
/// code) — NOT of the ruleset, the roles, or the content.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ComposeShape {
    /// Max subjects (actor, partner, equipped, room, weather, institution, ...).
    pub max_subjects: usize,
    /// Max typed params each subject projects.
    pub max_params: usize,
    /// Max sparse LINEAR terms the ruleset may carry.
    pub max_linear: usize,
    /// Max sparse KNOTS (signed pairwise products) the ruleset may carry.
    pub max_knots: usize,
    /// Width of the subject-identity namespace, in bits. See [`DEFAULT_IDENTITY_BITS`].
    pub identity_bits: usize,
}

impl ComposeShape {
    /// A shape at the default identity namespace. The binding width is fixed at
    /// [`DIGEST_FELTS`] (the native `cap_node8` output width).
    pub fn new(
        max_subjects: usize,
        max_params: usize,
        max_linear: usize,
        max_knots: usize,
    ) -> Self {
        ComposeShape {
            max_subjects,
            max_params,
            max_linear,
            max_knots,
            identity_bits: DEFAULT_IDENTITY_BITS,
        }
    }

    /// The same bounds over a narrower/wider identity namespace. The AIR's biggest column
    /// lever: see [`DEFAULT_IDENTITY_BITS`].
    pub fn with_identity_bits(mut self, bits: usize) -> Self {
        self.identity_bits = bits;
        self
    }

    /// Range width of the identity ordering comparison (`id[i+1] - id[i] - 1 >= 0`), whose
    /// honest term lies in `[0, 2^identity_bits)` — one bit of headroom.
    pub fn identity_cmp_bits(&self) -> usize {
        self.identity_bits + 1
    }

    /// Whether the ordering comparison is NON-VACUOUS at this identity width. See
    /// [`MAX_SOUND_IDENTITY_BITS`].
    pub fn identity_bits_sound(&self) -> bool {
        self.identity_bits >= 1 && self.identity_bits <= MAX_SOUND_IDENTITY_BITS
    }

    /// **THE FUEL BOUND.** Total Poseidon2 chip sites the AIR emits at this shape — the
    /// dominant prover cost and the DoS meter a host prices a composition by. Every term
    /// is a bound from the shape alone: a caller can price a composition WITHOUT seeing
    /// its content.
    ///
    /// One `MerkleHash8` (arity-16 `node8`) site absorbs [`crate::digest::ABSORB_RATE`] (8)
    /// felts, so each of the four streams costs `ceil(len / 8)` sites — no `W` multiplier,
    /// because one node8 site binds all 8 digest felts.
    pub fn hash_sites(&self) -> usize {
        let chunks = |n: usize| n.div_ceil(crate::digest::ABSORB_RATE).max(1);
        chunks(self.subjects_stream_len())
            + chunks(self.ruleset_stream_len())
            + chunks(1)
            + chunks(self.explanation_stream_len())
    }

    /// Felts in the canonical subjects stream (`crate::digest`).
    pub fn subjects_stream_len(&self) -> usize {
        2 + self.max_subjects * (3 + self.max_params)
    }

    /// Felts in the canonical ruleset stream.
    pub fn ruleset_stream_len(&self) -> usize {
        4 + self.max_linear * 4 + self.max_knots * 6
    }

    /// Felts in the explanation stream (one contribution per rule term).
    pub fn explanation_stream_len(&self) -> usize {
        self.max_linear + self.max_knots
    }

    /// Public inputs this shape publishes, including the 16-felt door state prefix.
    pub fn public_input_count(&self) -> usize {
        crate::pi::public_input_count()
    }

    /// Whether the PI layout fits the deployed 64-PI cap.
    pub fn pis_fit(&self) -> bool {
        self.public_input_count() <= MAX_PUBLIC_INPUTS
    }
}
