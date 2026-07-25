//! **THE TYPED PROJECTIONS AND THE VERSIONED RULESET** — the runtime data. All of it is
//! content: nothing here is a Rust type whose shape encodes a game.
//!
//! A [`Subject`] is what the AIR is GIVEN: an identity, a ROLE TAG, and a bounded vector
//! of typed params. The AIR never reads a heap; it reads projections. That the projection
//! faithfully names a real entity is the schema/projection layer's obligation (see
//! [`Subject::identity`]).

/// The canonical value of an absent role. An ACTIVE subject's role must be non-zero
/// (`crate::air` enforces it), so `0` unambiguously means "no subject here".
pub const ROLE_ABSENT: u64 = 0;

/// A typed projection of one participating entity.
///
/// The role tags §9.3 names — actor, partner, equipped, room, weather, institution — are
/// simply `u64` values a ruleset addresses. This crate knows none of them: a role is an
/// opaque tag, and the role vocabulary is content published under a schema root.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Subject {
    /// The entity's identity within this composition's namespace, range-checked to
    /// `2^IDENTITY_BITS` in-circuit (`crate::shape::IDENTITY_BITS`).
    ///
    /// **The exact reach of the in-circuit duplicate tooth.** The AIR enforces that no two
    /// subjects share an identity — over the identities it is GIVEN. That an identity
    /// faithfully names a distinct real entity is the projection layer's obligation, not
    /// this AIR's: identity is opaque to the composition. This is the honest boundary of
    /// "duplicate rejection is in-circuit" — the AIR cannot be handed the same dragon
    /// twice under one identity, and a host that mints two identities for one entity is
    /// caught by the ledger/schema layer that issues them, not here.
    pub identity: u64,
    /// The role tag this subject occupies. Must be non-zero and unique among the
    /// subjects of one composition (`crate::air` enforces both) — a role is a KEY.
    pub role: u64,
    /// The typed params, in schema slot order. Length must be `<= param_count`; slots at
    /// or past `param_count` are canonically ZERO (see `crate::reference`).
    pub params: Vec<i64>,
}

/// A sparse LINEAR term: `coeff * <subject with `role`>.params[param]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinearTerm {
    /// The role whose projection supplies the value. Addressed by ROLE, never by slot
    /// index — slot order is a canonicalization artifact (identity-sorted) a ruleset
    /// author cannot predict, so a ruleset that named slots would be content-dependent.
    pub role: u64,
    /// Which param slot of that subject.
    pub param: usize,
    /// Signed coefficient.
    pub coeff: i64,
}

/// **A KNOT** — a signed pairwise relation: `coeff * A.params[pa] * B.params[pb]`.
///
/// This is the nonlinear part, and the reason this AIR must exist at all: the declarative
/// `StateConstraint` vocabulary is LINEAR (`AffineLe` / `AffineEq`), so nothing in it can
/// MULTIPLY two state values. A knot is a degree-2 product of two subjects' params, which
/// only a hand-written Custom-VK AIR can check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Knot {
    /// Role supplying the left factor.
    pub role_a: u64,
    /// Param slot of the left factor.
    pub param_a: usize,
    /// Role supplying the right factor.
    pub role_b: u64,
    /// Param slot of the right factor.
    pub param_b: usize,
    /// Signed coefficient.
    pub coeff: i64,
}

/// **THE NAMED COMPOSITION LAW.** Versioned, and committed as `ruleset_root` — a PUBLIC
/// INPUT, never implied by the build.
///
/// Every field is WITNESSED in-circuit and bound to `ruleset_root`, so the AIR cannot use
/// coefficients other than the ones the published root names. Changing balance mints a new
/// root; it never changes what an old receipt meant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ruleset {
    /// Catalog identity of the law.
    pub id: u64,
    /// Version of the law under that identity.
    pub version: u64,
    /// Sparse linear terms.
    pub linear: Vec<LinearTerm>,
    /// Sparse knots — the nonlinear part.
    pub knots: Vec<Knot>,
}

/// One bounded composition: the subjects, the law, and the schema's active param width.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Composition {
    /// The participating projections, in ANY order — `crate::reference` canonicalizes.
    pub subjects: Vec<Subject>,
    /// The law.
    pub ruleset: Ruleset,
    /// The schema's active param width. Params at or past this index are canonically
    /// zero; a rule term addressing one is REFUSED (`crate::air`).
    pub param_count: usize,
}

/// Why a composition is not well-formed (host-side; each has an in-circuit twin that
/// makes the same shape UNSATISFIABLE rather than merely unbuildable).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ComposeError {
    /// Two subjects share an identity — the duplicate the canonical ordering refuses.
    DuplicateIdentity(u64),
    /// Two subjects share a role tag; a role is a KEY, so role -> subject would not be a
    /// function and the composition would be malleable.
    DuplicateRole(u64),
    /// An active subject used the reserved absent tag.
    AbsentRoleTag,
    /// A rule term addresses a role no subject occupies. Fail-closed: absent means
    /// UNPROVABLE, never silently zero (see `crate::reference`).
    UnresolvedRole(u64),
    /// A rule term addresses a param slot at or past `param_count`.
    ParamOutOfRange { param: usize, param_count: usize },
    /// The composition exceeds a shape bound (the fuel/DoS cap).
    ExceedsShape(&'static str),
    /// An identity exceeds the range the in-circuit ordering comparison is sound over.
    IdentityOutOfRange(u64),
    /// **BLOCKED, NOT FAKED.** Lean has no byte-pinned descriptor at this shape, so the
    /// Lean-authored AIR is not reachable from Rust. There is no Rust-authored fallback AIR to
    /// degrade to; widening the reachable set is a Lean change (a new `#guard`-pinned instance).
    /// See `crate::lean_descriptor`.
    NoLeanDescriptor,
    /// The produced witness does NOT satisfy the emitted descriptor. A witness-generator fault —
    /// refused here rather than handed to the prover. See `crate::witness::compose_trace_accepts`.
    WitnessRefusedByDescriptor,
}

impl core::fmt::Display for ComposeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ComposeError::DuplicateIdentity(i) => write!(f, "duplicate subject identity {i}"),
            ComposeError::DuplicateRole(r) => write!(f, "duplicate role tag {r}"),
            ComposeError::AbsentRoleTag => write!(f, "an active subject used role tag 0"),
            ComposeError::UnresolvedRole(r) => write!(f, "no subject occupies role {r}"),
            ComposeError::ParamOutOfRange { param, param_count } => {
                write!(f, "param slot {param} is at/past param_count {param_count}")
            }
            ComposeError::ExceedsShape(what) => write!(f, "exceeds shape bound: {what}"),
            ComposeError::IdentityOutOfRange(i) => write!(f, "identity {i} out of range"),
            ComposeError::NoLeanDescriptor => write!(
                f,
                "no Lean-pinned param-compose descriptor at this shape (blocked, not faked)"
            ),
            ComposeError::WitnessRefusedByDescriptor => write!(
                f,
                "the produced witness does not satisfy the emitted param-compose descriptor"
            ),
        }
    }
}
