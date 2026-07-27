//! **`binding_tooth`** — the shared REASON ASSERTION for the 8 `*_binding_deployed_tooth.rs` files.
//!
//! # Why this exists
//!
//! [`dregg_circuit::refusal::must_refuse`] closes half of CRATE-EXCELLENCE-PLAN §P1(b): it proves
//! the fold *returned `Err`* rather than crashing, so a stray `unwrap` in trace assembly can no
//! longer satisfy a forgery tooth. It does **not** close the other half. `must_refuse` still
//! accepts **any** `Err`, and on the `prove_turn_chain_recursive` path there are many, most of
//! which are NOT this tooth firing:
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
//!
//! Each of those keeps an any-`Err` tooth **green with the binding wide open**. So the tooth must
//! assert *which* refusal fired.
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
//! `TurnChainError::TurnProofInvalid { index, reason }` — where `reason` is a `format!("{e:?}")`
//! chain, so the **derived Debug** text (`WitnessConflict`), not the `Display` text
//! (`"Witness conflict: ..."`), is what reaches us.
//!
//! Two properties make `"WitnessConflict"` the honest thing to assert rather than a laundered
//! any-`Err`:
//!
//! 1. It is **specific to the binding**. Nothing else on this path produces it: it means two
//!    `connect`ed lanes carried different values, which for these nodes means precisely "the leg's
//!    claim is not what the sub-proof proves".
//! 2. It is **unconditional** — `set_witness`'s check carries no `cfg(debug_assertions)` gate
//!    (unlike the p3 batch prover's unsat panics, which vanish under `--release`). So this reason
//!    is the same reason in a release build, and the tooth is not measuring a debug artifact.
//!
//! Hence [`dregg_circuit::refusal::must_refuse`] — NOT `must_refuse_or_unsat_panic` — is correct
//! for these 8 sites: a typed `Err` genuinely is the mechanism, and a panic here would be a real
//! bug, not a refusal.

use dregg_circuit_prove::ivc_turn_chain::TurnChainError;

/// Require that `err` is the carrier leg's BINDING NODE refusing a forged claim — the specific
/// refusal the tooth claims — and not any of the other `Err`s the fold can produce.
///
/// `arm` is the fold arm's own reason prefix (e.g. `"segmented factory-binding node failed"`),
/// which pins *which* carrier's binding node refused. A refusal naming a different arm, or naming
/// no arm at all, means the forgery was stopped somewhere else and this tooth witnessed nothing.
///
/// The carrier leg is turn **0** in all 8 files' `build_chain`, so the index is asserted too: a
/// refusal on turn 1 (the plain companion leg) would be the chain plumbing failing, not the tooth.
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
    assert!(
        reason.contains(arm),
        "the refusal must come from `{arm}` — the carrier's BINDING NODE. A refusal from the \
         claim-pin ADMISSION gate (before the node is built) or from the backing/sub-proof LEAF \
         MINT (before the node sees the claim) leaves the binding UNTESTED.\n  got: {reason}"
    );
    assert!(
        reason.contains("WitnessConflict"),
        "the binding `connect` must be what conflicted. `WitnessConflict` IS the forged claim \
         meeting the sub-proof's genuine lanes on the shared witness slot the ConnectDsu allocated \
         (p3_circuit tables/runner.rs:502 — unconditional, so this holds under --release too). Any \
         other failure inside the node means the fold never reached the binding.\n  got: {reason}"
    );
}
