//! **THE PUBLIC-INPUT LAYOUT** — a bounded list of ROOTS + counts, riding the Custom-VK
//! door's `[old_commit8 ‖ new_commit8 ‖ ..app]` ABI.
//!
//! ```text
//!   [ 0.. 8)  old_commit8          the door ABI (dregg_circuit::effect_vm::custom_state_binding)
//!   [ 8..16)  new_commit8          the door ABI
//!    16       abi_version          the layout version (a committed decoder selector)
//!    17       subject_count        active subjects        (<= shape.max_subjects)
//!    18       param_count          active params/subject  (<= shape.max_params)
//!    19       linear_count         active linear terms    (<= shape.max_linear)
//!    20       knot_count           active knots           (<= shape.max_knots)
//!   [21..29)  ruleset_root     THE NAMED COMPOSITION LAW (8 felts)
//!   [29..37)  subjects_root    the canonical ordered (identity, role, params) list
//!   [37..45)  outcome_commitment
//!   [45..53)  explanation_root  the per-term contribution vector
//! ```
//!
//! At the fixed `DIGEST_FELTS = 8` binding width: **53 PIs**, of which 37 are app PIs —
//! inside the door's 48-app / 64-total budget.
//!
//! # Why per-subject roots are NOT in the PIs
//!
//! `HOARDLIGHT-LIVING-WORLD.md` §9.3 names the cul-de-sac precisely: public inputs must
//! not be "a fixed Rust struct whose field count encodes Stage 1". A layout with one root
//! slot per subject does exactly that — the PI count would encode N, so a five-subject
//! scene would need a new layout, a new ABI version, and a new verifier contract.
//!
//! Instead a SINGLE `subjects_root` binds the canonical ordered list at ~124 bits, and
//! the count rides its own slot. The layout is then **constant in N** — every subject's
//! identity, role tag, and param vector is bound just as tightly, and the host names
//! WHICH subjects participated by opening `subjects_root` in the receipt (a commitment
//! opening, which is what the receipt/explanation schema carries anyway). Growing the
//! scene changes a BOUND, never the ABI.

use dregg_circuit::effect_vm::custom_state_binding::CUSTOM_PI_STATE_PREFIX_LEN;

use crate::digest::DIGEST_FELTS;

/// The door's `[old_commit8 ‖ new_commit8]` prefix width (16). App PIs start here.
pub const APP_BASE: usize = CUSTOM_PI_STATE_PREFIX_LEN;

/// PI slot: the composition ABI version ([`crate::shape::PARAM_COMPOSE_ABI_VERSION`]).
pub const ABI_VERSION: usize = APP_BASE;
/// PI slot: active subject count.
pub const SUBJECT_COUNT: usize = APP_BASE + 1;
/// PI slot: active params per subject.
pub const PARAM_COUNT: usize = APP_BASE + 2;
/// PI slot: active linear rule terms.
pub const LINEAR_COUNT: usize = APP_BASE + 3;
/// PI slot: active knots.
pub const KNOT_COUNT: usize = APP_BASE + 4;
/// First root slot. Roots follow in order: ruleset, subjects, outcome, explanation, each
/// [`DIGEST_FELTS`] felts wide.
pub const ROOTS_BASE: usize = APP_BASE + 5;

/// Offset of `ruleset_root`.
pub const fn ruleset_root_base() -> usize {
    ROOTS_BASE
}
/// Offset of `subjects_root`.
pub const fn subjects_root_base() -> usize {
    ROOTS_BASE + DIGEST_FELTS
}
/// Offset of `outcome_commitment`.
pub const fn outcome_commitment_base() -> usize {
    ROOTS_BASE + 2 * DIGEST_FELTS
}
/// Offset of `explanation_root`.
pub const fn explanation_root_base() -> usize {
    ROOTS_BASE + 3 * DIGEST_FELTS
}

/// Total public inputs (including the 16-felt door prefix).
pub const fn public_input_count() -> usize {
    ROOTS_BASE + 4 * DIGEST_FELTS
}

/// App public inputs (what the door's 48-PI app budget is spent on).
pub const fn app_public_input_count() -> usize {
    public_input_count() - APP_BASE
}
