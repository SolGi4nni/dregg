//! **`binding_tooth`** — the REASON ASSERTION for every p3-recursion BINDING-NODE refusal tooth.
//!
//! # Why this exists, and why it is in `src/` and not `tests/`
//!
//! [`dregg_circuit::refusal::must_refuse`] closes half of CRATE-EXCELLENCE-PLAN §P1(b): it proves
//! the fold *returned `Err`* rather than crashing, so a stray `unwrap` in trace assembly can no
//! longer satisfy a forgery tooth. It does **not** close the other half. `must_refuse` still
//! accepts **any** `Err`, and on the `prove_turn_chain_recursive` / binding-node path there are
//! many, most of which are NOT this tooth firing:
//!
//! * `TurnChainError::TurnProofInvalid` from `carrier_claim_pins_admitted` — the leg's descriptor
//!   does not carry the STEP-3 claim pins. Fail-closed and correct, but it refuses **before** the
//!   binding node is ever built, so the binding is untested. This one is live and likely: it is
//!   exactly what the mid-big-bang descriptor drift produces.
//! * `TurnChainError::TurnProofInvalid` with `"backing leaf mint failed"` / `"sub-proof leaf mint
//!   failed"` — the adversary's own sub-proof did not mint. The fold never saw the forged claim.
//! * `TurnChainError::ChainBreak` / `WideChainBreak` / `MissingWideAnchor` — the test's chain
//!   plumbing is broken, not the adversary's claim.
//! * `TurnChainError::RecursionFailed` — an OPERATIONAL fault (FRI, OOM, trace shape). The
//!   `BindingUnsat`-vs-`ProverFailed` distinction §P3(2) names is destroyed here, so an any-`Err`
//!   tooth reads an out-of-memory kill as "the forgery was rejected".
//! * `JointAggError::AggregationProofInvalid` from one of the node's own **pre-connect** guards —
//!   `"…carries no expose_claim table"`, `"…exposes N claim lane(s) but … requires M"`,
//!   `"app_root_len must be nonzero"`. Every one of those returns before a single `cb.connect` is
//!   emitted, so a tooth satisfied by them is measuring the node's arity check, not its binding.
//!
//! Each of those keeps an any-`Err` tooth **green with the binding wide open**. So the tooth must
//! assert *which* refusal fired.
//!
//! ⚑ **THE LIFT (2026-08-10).** This module used to live at `circuit-prove/tests/binding_tooth/`,
//! where only the eight `tests/*_binding_deployed_tooth.rs` integration files could reach it. A
//! `tests/` module is invisible to a `#[cfg(test)] mod` inside `src/` — the integration target
//! links this crate as an external rlib, and the in-lib unit tests link nothing of `tests/`. So
//! the **eleven** in-lib fold teeth in [`crate::joint_turn_recursive`] and the thirteen in the
//! `*_leaf_adapter` unit-test modules had no way to say which refusal they meant, and every one of
//! them was a bare `must_refuse` whose result was discarded. Moving it to `src/` is the same move
//! [`dregg_circuit::refusal`] already made, for the same reason and with the same justification:
//! this module has **no accept path** — every function either returns or panics — so shipping it in
//! a production build arms nothing and can only make a test stricter.
//!
//! # The mechanism this asserts, and why `WitnessConflict` IS the refusal
//!
//! The binding node (`joint_turn_recursive::prove_claim_binding_node_segmented` and its per-carrier
//! siblings) `connect`s the leg's CLAIMED lanes to the sub-proof's GENUINE in-circuit lanes:
//!
//! ```ignore
//! // IGNORED: a QUOTED line lifted from `joint_turn_recursive`, shown in isolation —
//! // `cb`, `ev`, `cs` and `claim_len` are that function's locals, not bindings here.
//! for k in 0..claim_len { cb.connect(ev[SEG_WIDTH + k], cs[k]); }
//! ```
//!
//! `p3_circuit`'s `connect` is **not** a constraint row — it is a union-find merge
//! (`circuit/src/builder/expression_builder.rs:895` pushes onto `pending_connects`;
//! `builder/compiler/lowerer/state.rs:83` builds a `ConnectDsu` and `alloc_witness` gives every
//! member of a connect class **one shared `WitnessId`**). So a connected pair is enforced
//! *implicitly*: both exprs write the same witness slot, and a forged claim surfaces when the
//! second writer disagrees with the first:
//!
//! ```ignore
//! // IGNORED: source QUOTED from the `p3_circuit` dependency at the path in the comment
//! // below — `slot`, `widx` and `self` belong to that crate's `Runner`, not to this test.
//! // p3_circuit circuit/src/tables/runner.rs:502
//! if let Some(existing_value) = slot.as_ref() {
//!     if *existing_value == value { return Ok(()); }
//!     return Err(self.witness_conflict(widx, existing_value, value));
//! }
//! ```
//!
//! That `Err` propagates out of `build_and_prove_aggregation_layer_with_expose` as
//! `VerificationError::Circuit(CircuitError::WitnessConflict { .. })`, is wrapped by the adapter
//! into `JointAggError::AggregationProofInvalid`, and is wrapped again by the fold arm into
//! `TurnChainError::TurnProofInvalid { index, reason }` — where `reason` is a `format!` chain. ⚑
//! WHICH TEXT arrives depends on the arm's specifier: `{e:?}` yields the **derived Debug**
//! (`Circuit(WitnessConflict { .. })`) and `{e}` yields the `thiserror` **Display** (`Circuit
//! error: Witness conflict: WitnessId(204) already set to 1, …`). Both are live in this tree, which
//! is why [`BINDING_CONNECT_MARKERS`] is a two-element set and not the one string this paragraph
//! used to name.
//!
//! Two properties make [`BINDING_CONNECT_MARKERS`] the honest thing to assert rather than a
//! laundered any-`Err`:
//!
//! 1. It is **specific to the binding**. Nothing else on this path produces it: it means two
//!    `connect`ed lanes carried different values, which for these nodes means precisely "the leg's
//!    claim is not what the sub-proof proves".
//! 2. It is **unconditional** — `set_witness`'s check carries no `cfg(debug_assertions)` gate
//!    (unlike the p3 batch prover's unsat panics, which vanish under `--release`). So this reason
//!    is the same reason in a release build, and the tooth is not measuring a debug artifact. This
//!    matters more than it looks: `refusal.rs`'s own header records sixteen `pasta_*` teeth that
//!    sat RED for ten days because they asserted a RELEASE-ONLY string. Everything asserted here
//!    holds in both profiles.
//!
//! Hence [`dregg_circuit::refusal::must_refuse`] — NOT `must_refuse_or_unsat_panic` — is correct
//! for the binding-node sites: a typed `Err` genuinely is the mechanism, and a panic here would be
//! a real bug, not a refusal.
//!
//! # The other two shapes on this rail, which are NOT the connect
//!
//! Not every `must_refuse` on the rail is a connect tooth, and pretending otherwise would be its
//! own rubber stamp:
//!
//! * **The node's fail-closed ARITY guards** ([`assert_node_refused_fail_closed`]) — "a
//!   commitment-only leaf must not be laundered through the state node". The tooth's subject IS the
//!   guard, the refusal fires before any `connect`, and a `WitnessConflict` there would mean the
//!   guard did not hold. So that tooth asserts the guard's own message and asserts the ABSENCE of
//!   every connect marker.
//! * **The LEAF's PI pins** — "a forged tuple has no satisfying assembly, `PiBinding{First}`
//!   requires `row0[col] == pi[col]`". That is an AIR constraint, not a `connect`, and the right
//!   assertion is [`dregg_circuit::refusal::assert_violated_constraint_not_bus`], which is the
//!   profile-independent form of "a violated constraint, not a bus imbalance".

use dregg_circuit::refusal::shape_fault;

use crate::ivc_turn_chain::TurnChainError;
use crate::joint_turn_aggregation::JointAggError;

/// The two renderings of the ONE thing that IS a binding `connect` refusing: two expressions forced
/// onto one `ConnectDsu` witness slot with different values. Unconditional in every build profile —
/// see the module header.
///
/// ⚑ **BOTH, because the rendering depends on the arm's format specifier and nothing announces
/// which.** `p3_circuit::CircuitError` is `#[derive(Debug, Error)]` with
///
/// ```text
/// #[error("Witness conflict: WitnessId({witness_id}) already set to {existing}, cannot reassign …")]
/// WitnessConflict { .. }
/// ```
///
/// so an arm that wrote `format!("…: {e:?}")` hands us the DERIVED text `Circuit(WitnessConflict
/// { .. })`, and an arm that wrote `format!("…: {e}")` hands us the `thiserror` text `Circuit
/// error: Witness conflict: …`. Both are live in this tree today, measured 2026-08-10 by reading
/// the arms: `joint_turn_recursive`'s six nodes and `fold_accumulator_segments` use `{e:?}`;
/// `mina_phase2_chain_leaf::fold_chain_links` uses `{e}`. A tooth asserting only `"WitnessConflict"`
/// is therefore RED-by-construction on the `{e}` arms — the same shape as the sixteen `pasta_*`
/// teeth `refusal.rs` records, one layer up. Assert the SET.
pub const BINDING_CONNECT_MARKERS: [&str; 2] = ["WitnessConflict", "Witness conflict"];

/// The [`BINDING_CONNECT_MARKERS`] entry `reason` trips, if any.
pub fn binding_connect_marker(reason: &str) -> Option<&'static str> {
    BINDING_CONNECT_MARKERS
        .iter()
        .copied()
        .find(|m| reason.contains(m))
}

/// Refusals that fire **before** the node emits its first `cb.connect`, verified by reading every
/// early `return Err` in [`crate::joint_turn_recursive`]'s binding nodes and the `*_leaf_adapter`
/// siblings.
///
/// A connect tooth satisfied by one of these has measured the node's ARITY PRE-FLIGHT, not its
/// binding — the `Err`-side twin of [`dregg_circuit::refusal::SHAPE_FAULT_MARKERS`], one layer up.
/// The `WitnessConflict` assertion already excludes them; this list is the second net, and it is
/// what makes the failure message say *which* pre-connect guard fired instead of "not
/// WitnessConflict".
pub const PRE_CONNECT_REFUSAL_MARKERS: [&str; 6] = [
    // `expose_claim_instance_index` returned None — the child was minted by the wrong wrap.
    "carries no expose_claim",
    // the cs_lanes / ev_lanes fail-closed width guards.
    "claim lane(s)",
    // `app_root_len == 0` / the fields-root width guard.
    "must be nonzero",
    "root width must be exactly 8",
    // the fold arm minted the adversary's own sub-proof and IT failed — the fold never saw the claim.
    "leaf mint failed",
    // ⚑ `carrier_claim_pins_admitted` and the `fold_vk_pin` gate — the leg's descriptor lacks the
    // STEP-3 claim pins, or a child carries no preprocessed commitment. Every one of those four
    // refusals ends `refusing to fold …`, and this marker was `"claim pins"` for about an hour
    // while I wrote it: a string that appears NOWHERE in the tree. An UNREACHABLE marker in a
    // discriminator is the same defect one level up — it excludes nothing while reading as though
    // it does. Verified by grep against HEAD (`ivc_turn_chain.rs:3728/3769/3846/3863/3871`,
    // `fold_vk_pin.rs:196`).
    "refusing to fold",
];

/// The [`PRE_CONNECT_REFUSAL_MARKERS`] entry `reason` trips, if any.
pub fn pre_connect_marker(reason: &str) -> Option<&'static str> {
    PRE_CONNECT_REFUSAL_MARKERS
        .iter()
        .copied()
        .find(|m| reason.contains(m))
}

/// Print the refusal a tooth actually got, unconditionally, so a GREEN run is still a MEASUREMENT
/// and not a claim.
///
/// ⚠ This is deliberately not gated on an env var or a `cfg`. An assertion helper that can be
/// silenced from outside is the fail-open gate class this tree already records; this only ever
/// adds a line of output. Read them with `cargo nextest run … --success-output immediate` (or
/// `cargo test -- --nocapture`) and grep `REFUSAL MEASURED`.
pub fn report_refusal(what: &str, reason: &str) {
    eprintln!("REFUSAL MEASURED [{what}]: {reason}");
}

/// The core: `reason` is the BINDING `connect` refusing, in the node named by `arm`.
///
/// Four clauses, each excluding a way this tooth could be green while measuring nothing:
///
/// 1. it is not a **shape/arity** fault (delegated to `refusal::shape_fault`, so the two lists
///    cannot drift);
/// 2. it is not one of the node's own **pre-connect** guards ([`PRE_CONNECT_REFUSAL_MARKERS`]);
/// 3. it names `arm`, so the refusal came from *this* carrier's node and not a sibling's;
/// 4. it names one of [`BINDING_CONNECT_MARKERS`] — the connect itself.
#[track_caller]
pub fn assert_binding_connect_conflict(what: &str, arm: &str, reason: &str) {
    report_refusal(what, reason);
    if let Some(m) = shape_fault(reason) {
        panic!(
            "{what}: refused with a SHAPE/ARITY fault ({m:?}), not the binding connect. The trace's \
             GEOMETRY was rejected before the constraint system read one cell, so this tooth \
             witnessed NOTHING.\n  got: {reason}"
        );
    }
    if let Some(m) = pre_connect_marker(reason) {
        panic!(
            "{what}: refused by a PRE-CONNECT guard ({m:?}) — the node returned before it emitted a \
             single `cb.connect`, so the binding this tooth names was never exercised. Fix the \
             fixture so the children carry the lanes the node requires; if the guard itself IS the \
             subject, say so with `assert_node_refused_fail_closed`.\n  got: {reason}"
        );
    }
    assert!(
        reason.contains(arm),
        "{what}: the refusal must come from `{arm}` — the carrier's BINDING NODE. A refusal naming \
         a different arm, or naming no arm at all, means the forgery was stopped somewhere else and \
         this tooth witnessed nothing about the binding.\n  got: {reason}"
    );
    assert!(
        binding_connect_marker(reason).is_some(),
        "{what}: the binding `connect` must be what conflicted. One of \
         {BINDING_CONNECT_MARKERS:?} IS the forged claim meeting the sub-proof's genuine lanes on \
         the shared witness slot the ConnectDsu allocated (p3_circuit tables/runner.rs:502 — \
         unconditional, so this holds under --release too). Any other failure inside the node means \
         the fold never reached the binding.\n  got: {reason}"
    );
}

/// Require that a **binding NODE** call (returning [`JointAggError`]) refused because its `connect`
/// conflicted — the in-lib form, for the fold teeth that call `prove_*_binding_node*` directly.
///
/// `arm` is the node's own reason prefix (e.g. `"state-binding custom fold aggregation node
/// failed"`), which pins *which* node refused.
#[track_caller]
pub fn assert_node_refused_by_binding_connect(what: &str, err: &JointAggError, arm: &str) {
    let JointAggError::AggregationProofInvalid { reason } = err;
    assert_binding_connect_conflict(what, arm, reason);
}

/// The DUAL: require that a binding node refused **fail-closed, before the connect**, with the
/// specific guard the tooth names.
///
/// For teeth whose subject genuinely IS an arity guard ("a commitment-only leaf must not be
/// laundered through the state-binding node"). Such a refusal is real, but it is a **different
/// statement** than the binding, and a tooth that accepted either would be satisfied by both. So
/// this asserts the guard's message positively AND asserts the connect marker's ABSENCE: a
/// `WitnessConflict` here would mean the node built the connect anyway, i.e. the fail-closed guard
/// did not hold and the leaf WAS laundered through.
#[track_caller]
pub fn assert_node_refused_fail_closed(what: &str, err: &JointAggError, expected: &str) {
    let JointAggError::AggregationProofInvalid { reason } = err;
    report_refusal(what, reason);
    assert!(
        reason.contains(expected),
        "{what}: the node must refuse with its fail-closed guard.\n  expected to contain: \
         {expected}\n  got: {reason}"
    );
    if let Some(m) = binding_connect_marker(reason) {
        panic!(
            "{what}: the node reached its `cb.connect` and refused THERE ({m:?}) — so the \
             fail-closed guard this tooth names did NOT hold, and the mis-shaped child was admitted \
             into the binding instead of being refused before it.\n  got: {reason}"
        );
    }
}

/// Require that `err` is the carrier leg's BINDING NODE refusing a forged claim — the specific
/// refusal the tooth claims — and not any of the other `Err`s the *chain fold* can produce.
///
/// `arm` is the fold arm's own reason prefix (e.g. `"segmented factory-binding node failed"`),
/// which pins *which* carrier's binding node refused. A refusal naming a different arm, or naming
/// no arm at all, means the forgery was stopped somewhere else and this tooth witnessed nothing.
///
/// The carrier leg is turn **0** in all 8 files' `build_chain`, so the index is asserted too: a
/// refusal on turn 1 (the plain companion leg) would be the chain plumbing failing, not the tooth.
#[track_caller]
pub fn assert_refused_by_binding_node(err: &TurnChainError, arm: &str) {
    let TurnChainError::TurnProofInvalid { index, reason } = err else {
        panic!(
            "the forged claim must be refused by the carrier leg's BINDING NODE \
             (TurnProofInvalid), but a DIFFERENT tooth fired — so this tooth witnessed nothing \
             about the binding. A ChainBreak/MissingWideAnchor means the chain plumbing broke; a \
             RecursionFailed is an OPERATIONAL fault (FRI/OOM/shape), not a refusal.\n  got: \
             {err:?}"
        )
    };
    assert_eq!(
        *index, 0,
        "the carrier leg is turn 0 of the chain; a refusal on turn {index} is the companion leg \
         or the chain plumbing failing, not the binding tooth.\n  got: {reason}"
    );
    assert_binding_connect_conflict(
        &format!("the carrier leg's forged claim vs `{arm}`"),
        arm,
        reason,
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A real measured node refusal — the shape `format!("{e:?}")` produces on this rail.
    fn conflict(arm: &str) -> JointAggError {
        JointAggError::AggregationProofInvalid {
            reason: format!(
                "{arm}: Circuit(WitnessConflict {{ witness_id: WitnessId(256), existing: 1, new: \
                 204 }})"
            ),
        }
    }

    #[test]
    fn a_connect_conflict_naming_the_arm_passes() {
        assert_node_refused_by_binding_connect(
            "probe",
            &conflict("state-binding custom fold aggregation node failed"),
            "state-binding custom fold aggregation node failed",
        );
    }

    /// ⚑ THE WHOLE POINT: the pre-connect ARITY guard must not satisfy a connect tooth. This is the
    /// exact string `prove_custom_binding_node_state_segmented` returns for an 8-lane leaf, and it
    /// fires before a single `cb.connect` exists.
    #[test]
    #[should_panic(expected = "refused by a PRE-CONNECT guard")]
    fn the_lane_count_guard_does_not_satisfy_a_connect_tooth() {
        assert_node_refused_by_binding_connect(
            "probe",
            &JointAggError::AggregationProofInvalid {
                reason: "custom sub-proof leaf exposes 8 claim lane(s) but the state-binding fold \
                         requires 24 (commitment(8) ‖ old8 ‖ new8)"
                    .to_string(),
            },
            "state-binding custom fold aggregation node failed",
        );
    }

    #[test]
    #[should_panic(expected = "refused by a PRE-CONNECT guard")]
    fn a_sub_proof_that_never_minted_does_not_satisfy_a_connect_tooth() {
        assert_refused_by_binding_node(
            &TurnChainError::TurnProofInvalid {
                index: 0,
                reason: "custom state-binding sub-proof leaf mint failed: OodEvaluationMismatch"
                    .to_string(),
            },
            "state-binding custom-binding node failed",
        );
    }

    /// An OOM / FRI fault surfaces as `RecursionFailed`, and the whole finding is that it used to
    /// read as "the forgery was rejected".
    #[test]
    #[should_panic(expected = "OPERATIONAL fault")]
    fn an_operational_fault_is_not_a_refusal() {
        assert_refused_by_binding_node(
            &TurnChainError::RecursionFailed {
                reason: "aggregate: fri proof of work failed".to_string(),
            },
            "state-binding custom-binding node failed",
        );
    }

    #[test]
    #[should_panic(expected = "must come from")]
    fn a_refusal_from_a_different_arm_is_not_this_tooth() {
        assert_node_refused_by_binding_connect(
            "probe",
            &conflict("segmented sovereign-binding aggregation node failed"),
            "state-binding custom fold aggregation node failed",
        );
    }

    #[test]
    #[should_panic(expected = "SHAPE/ARITY fault")]
    fn a_shape_fault_is_not_a_refusal() {
        assert_node_refused_by_binding_connect(
            "probe",
            &JointAggError::AggregationProofInvalid {
                reason: "arm: base row width 3065 must equal descriptor trace_width 1963"
                    .to_string(),
            },
            "arm",
        );
    }

    /// The dual, both poles: the fail-closed guard tooth passes on its guard and REDS if the node
    /// admitted the mis-shaped child into the connect instead.
    #[test]
    fn the_fail_closed_tooth_passes_on_its_own_guard() {
        assert_node_refused_fail_closed(
            "probe",
            &JointAggError::AggregationProofInvalid {
                reason: "custom sub-proof leaf exposes 8 claim lane(s) but the state-binding fold \
                         requires 24"
                    .to_string(),
            },
            "claim lane(s)",
        );
    }

    #[test]
    #[should_panic(expected = "did NOT hold")]
    fn the_fail_closed_tooth_reds_if_the_child_reached_the_connect() {
        assert_node_refused_fail_closed(
            "probe",
            &conflict("claim lane(s) — but it reached the connect anyway"),
            "claim lane(s)",
        );
    }
}
