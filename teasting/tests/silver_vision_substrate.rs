//! Silver-vision substrate choreography tests.
//!
//! Layer: **multi-actor / multi-federation choreography**. These tests
//! drive multiple cells (often across federation boundaries) through a
//! scripted sequence and assert end-state invariants. Where unit tests
//! (`tests/`) prove "the cell evaluator accepts X" and protocol-tests
//! prove "across all randomized X, invariant Y holds", THIS layer proves
//! "actor A and actor B, following the script, end up with the substrate
//! they think they have."
//!
//! Cross-references:
//! - `SILVER-VISION-E2E-VERIFICATION.md` — the full silver-vision rubric.
//! - `STAGE-7-GAMMA-2-PI-DESIGN.md` — bilateral binding (we exercise the
//!   pair-construction half here).
//! - `AUTHORIZATION-CUSTOM-DESIGN.md` — Auth::Custom across actors.
//! - `EXECUTOR-HONESTY-AUDIT.md` — every cross-actor threat that this
//!   layer is the right place to dramatize.
//!
//! Status: nearly every test is `#[ignore]`'d on a specific lane. Until
//! the substrate lands, this file provides the scenario shapes — when
//! the lane lands the unblock is to remove the ignore + flesh out the
//! body (the harness pieces exist in `dregg_teasting::*`).
