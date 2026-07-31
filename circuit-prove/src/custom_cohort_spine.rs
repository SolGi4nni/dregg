//! Claim-preserving recursion for one logical custom turn split across several
//! homogeneous EffectVM cohort legs.
//!
//! A custom proof can describe the whole state transition while the deployed
//! EffectVM proves that transition as a chain of cohort legs.  Descent v2 put
//! its `Custom` carrier before the ordinary `SetField` writes, so that Custom
//! leg ended before the state it attested existed.  Binding the direct proof to
//! that first leg would therefore be unsatisfiable; binding only its commitment
//! there and trusting the final fields on the host would be unsound for a pure
//! light client.
//!
//! The narrow v3 composition puts the ordinary writes first and a no-op Custom
//! carrier last.  That terminal Custom member already publishes every needed
//! claim, so no ordinary SetField descriptor needs a new exposure epoch:
//!
//! ```text
//! ordinary write prefix: segment
//! terminal Custom:       segment || proof_commitment8 || program_vk8
//!                                || final_app_fields(L) || final_fields_root8
//!                         \                     /
//!                    claim-preserving segment spine
//!                                  |
//! whole carrier: segment || proof_commitment8 || program_vk8
//!                        || final_app_fields(L) || final_fields_root8
//!                                  |
//!                           direct IR2 proof leaf
//! ```
//!
//! Every merge verifies both child proofs, connects the two adjacent state
//! anchors, recomputes the ordered segment digest, and re-exposes the selected
//! claims.  The final node then connects the direct proof's declared old/new
//! roots to the *whole* segment endpoints and its commitment/VK/application
//! claims/map root to the terminal committed Custom state.
//! No new transition semantics are introduced: the ordinary Lean-authored
//! Custom and SetField cohort descriptors remain the execution authority.
//!
//! The recursive half is complete here.  The live producer still needs a
//! verifier-committed placement epoch authorizing the declared SetField range
//! immediately *before* its paired Custom, plus SDK emission of that terminal
//! sentinel.  The legacy Custom-before-writes policy remains fail-closed; until
//! the new placement contract lands, this module is deliberately not wired
//! into the SDK producer.

use p3_recursion::{BatchOnly, ProveNextLayerParams, RecursionOutput, Target};

use crate::custom_leaf_adapter::custom_app_root_claim_len;
use crate::ivc_turn_chain::{
    SEG_ANCHOR_WIDTH, SEG_COUNT, SEG_DIGEST_FIRST, SEG_DIGEST_WIDTH, SEG_FIRST_OLD, SEG_LAST_NEW,
    SEG_WIDTH, expose_claim_instance_index, seg_poseidon_commit,
};
use crate::joint_turn_aggregation::JointAggError;
use crate::joint_turn_recursive::{CUSTOM_COMMIT_LEN, CUSTOM_COMMIT_PI_LO};
use crate::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, create_recursion_backend_with_coeff_lookups,
};

const D: usize = 4;
const PROGRAM_VK_LEN: usize = 8;
const POST_FIELDS_ROOT_LEN: usize = 8;

type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

fn invalid(reason: impl Into<String>) -> JointAggError {
    JointAggError::AggregationProofInvalid {
        reason: reason.into(),
    }
}

fn exposed_claim_len(output: &RecursionOutput<DreggRecursionConfig>) -> usize {
    output
        .0
        .non_primitives
        .iter()
        .find(|entry| entry.op_type.as_str() == "expose_claim")
        .map_or(0, |entry| entry.public_values.len())
}

fn require_claim_len(
    output: &RecursionOutput<DreggRecursionConfig>,
    expected: usize,
    role: &str,
) -> Result<usize, JointAggError> {
    let actual = exposed_claim_len(output);
    if actual != expected {
        return Err(invalid(format!(
            "{role} exposes {actual} claim lane(s), expected exactly {expected}; refusing an \
             ambiguous whole-turn cohort-spine layout"
        )));
    }
    expose_claim_instance_index(&output.0).ok_or_else(|| {
        invalid(format!(
            "{role} carries no expose_claim instance despite its claimed layout"
        ))
    })
}

/// Compute the parent ordered segment while enforcing state continuity.
///
/// This is the claim-returning twin of
/// [`crate::ivc_turn_chain::segment_combine_expose`].  Keeping the exact same
/// indices and [`seg_poseidon_commit`] routine makes a claim-preserving spine
/// indistinguishable from the ordinary segment tree at its public segment.
fn combine_segment_targets(
    cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
    left: &[Target],
    right: &[Target],
) -> Vec<Target> {
    debug_assert!(left.len() >= SEG_WIDTH && right.len() >= SEG_WIDTH);
    for lane in 0..SEG_ANCHOR_WIDTH {
        cb.connect(left[SEG_LAST_NEW + lane], right[SEG_FIRST_OLD + lane]);
    }

    let count = cb.add(left[SEG_COUNT], right[SEG_COUNT]);
    let mut digest_inputs = Vec::with_capacity(2 * SEG_DIGEST_WIDTH);
    digest_inputs.extend_from_slice(&left[SEG_DIGEST_FIRST..SEG_DIGEST_FIRST + SEG_DIGEST_WIDTH]);
    digest_inputs.extend_from_slice(&right[SEG_DIGEST_FIRST..SEG_DIGEST_FIRST + SEG_DIGEST_WIDTH]);
    let digest = seg_poseidon_commit(cb, &digest_inputs);

    let mut segment = Vec::with_capacity(SEG_WIDTH);
    segment.extend_from_slice(&left[SEG_FIRST_OLD..SEG_FIRST_OLD + SEG_ANCHOR_WIDTH]);
    segment.extend_from_slice(&right[SEG_LAST_NEW..SEG_LAST_NEW + SEG_ANCHOR_WIDTH]);
    segment.push(count);
    segment.extend_from_slice(&digest);
    debug_assert_eq!(segment.len(), SEG_WIDTH);
    segment
}

/// Merge two adjacent segment proofs while retaining explicitly-sized claim
/// suffixes from both children.
///
/// Each child must expose exactly `segment || suffix`.  The parent exposes
/// `combined_segment || left_suffix || right_suffix`.  Exact lengths are
/// mandatory: silently ignoring a lane would make later offsets mean something
/// different under the same host call.
///
/// The intended whole-turn construction folds an ordinary write prefix
/// (`left_suffix_len = 0`) into a terminal Custom carrying
/// [`terminal_custom_suffix_len`] claims.  The primitive is kept
/// length-parametric so the same sound spine can serve other proof-native game
/// transitions without inventing a new aggregation circuit for every app.
pub fn prove_segment_merge_preserving_claims(
    left: &RecursionOutput<DreggRecursionConfig>,
    left_suffix_len: usize,
    right: &RecursionOutput<DreggRecursionConfig>,
    right_suffix_len: usize,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    let left_idx = require_claim_len(left, SEG_WIDTH + left_suffix_len, "left cohort segment")?;
    let right_idx = require_claim_len(right, SEG_WIDTH + right_suffix_len, "right cohort segment")?;

    let left_input = left.into_recursion_input::<BatchOnly>();
    let right_input = right.into_recursion_input::<BatchOnly>();
    let backend = create_recursion_backend_with_coeff_lookups();
    let params = ProveNextLayerParams::default();

    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>],
                       _left_vk_cap: &[Target],
                       _right_vk_cap: &[Target]| {
        let left_claim = left_apt
            .get(left_idx)
            .expect("left cohort expose_claim instance present");
        let right_claim = right_apt
            .get(right_idx)
            .expect("right cohort expose_claim instance present");
        debug_assert_eq!(left_claim.len(), SEG_WIDTH + left_suffix_len);
        debug_assert_eq!(right_claim.len(), SEG_WIDTH + right_suffix_len);

        let mut parent = combine_segment_targets(cb, left_claim, right_claim);
        parent.extend_from_slice(&left_claim[SEG_WIDTH..]);
        parent.extend_from_slice(&right_claim[SEG_WIDTH..]);
        cb.expose_as_public_output(&parent);
    };

    p3_recursion::build_and_prove_aggregation_layer_with_expose::<
        DreggRecursionConfig,
        BatchOnly,
        BatchOnly,
        _,
        D,
    >(
        &left_input,
        &right_input,
        config,
        &backend,
        &params,
        None,
        Some(&expose),
    )
    .map_err(|error| invalid(format!("claim-preserving cohort merge failed: {error:?}")))
}

/// Bind a direct-IR2 application proof to a complete multi-cohort turn.
///
/// `whole_turn_carrier` must be the result of the claim-preserving spine and
/// expose exactly:
///
/// ```text
/// segment || custom_proof_commitment8 || program_vk8
///         || final_app_fields(app_root_len) || final_fields_root8
/// ```
///
/// `direct_subproof_leaf` must be minted by
/// [`crate::custom_leaf_adapter::prove_direct_ir2_leaf_with_app_and_fields_root_commitment`]
/// and therefore expose exactly:
///
/// ```text
/// custom_proof_commitment8 || old8 || new8 || app_root(L)
///                          || post_fields_root8 || canonical_program_vk8
/// ```
///
/// Every surface is connected in-circuit.  In particular the direct proof's
/// `new8` is compared with the *terminal* segment root, never the Custom
/// head's intermediate root.
pub fn prove_direct_ir2_whole_turn_binding_node_segmented(
    whole_turn_carrier: &RecursionOutput<DreggRecursionConfig>,
    direct_subproof_leaf: &RecursionOutput<DreggRecursionConfig>,
    config: &DreggRecursionConfig,
    app_root_len: usize,
) -> Result<RecursionOutput<DreggRecursionConfig>, JointAggError> {
    if app_root_len == 0 {
        return Err(invalid(
            "whole-turn direct-IR2 binding requires a nonzero application root width",
        ));
    }

    let carrier_len =
        SEG_WIDTH + CUSTOM_COMMIT_LEN + PROGRAM_VK_LEN + app_root_len + POST_FIELDS_ROOT_LEN;
    let direct_len =
        custom_app_root_claim_len(app_root_len) + POST_FIELDS_ROOT_LEN + PROGRAM_VK_LEN;
    let carrier_idx =
        require_claim_len(whole_turn_carrier, carrier_len, "whole-turn cohort carrier")?;
    let direct_idx = require_claim_len(
        direct_subproof_leaf,
        direct_len,
        "direct-IR2 sub-proof leaf",
    )?;

    let carrier_input = whole_turn_carrier.into_recursion_input::<BatchOnly>();
    let direct_input = direct_subproof_leaf.into_recursion_input::<BatchOnly>();
    let backend = create_recursion_backend_with_coeff_lookups();
    let params = ProveNextLayerParams::default();

    let l = app_root_len;
    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       carrier_apt: &[Vec<Target>],
                       direct_apt: &[Vec<Target>],
                       _left_vk_cap: &[Target],
                       _right_vk_cap: &[Target]| {
        let carrier = carrier_apt
            .get(carrier_idx)
            .expect("whole-turn carrier expose_claim instance present");
        let direct = direct_apt
            .get(direct_idx)
            .expect("direct-IR2 expose_claim instance present");
        debug_assert_eq!(carrier.len(), carrier_len);
        debug_assert_eq!(direct.len(), direct_len);

        let carrier_commit = SEG_WIDTH;
        let carrier_vk = carrier_commit + CUSTOM_COMMIT_LEN;
        let carrier_app = carrier_vk + PROGRAM_VK_LEN;
        let carrier_fields_root = carrier_app + l;

        let direct_commit = 0;
        let direct_old = CUSTOM_COMMIT_LEN;
        let direct_new = direct_old + SEG_ANCHOR_WIDTH;
        let direct_app = custom_app_root_claim_len(0);
        let direct_fields_root = custom_app_root_claim_len(l);
        let direct_vk = direct_fields_root + POST_FIELDS_ROOT_LEN;

        // Proof identity and PI commitment originate at the Custom head.
        for lane in 0..CUSTOM_COMMIT_LEN {
            cb.connect(carrier[carrier_commit + lane], direct[direct_commit + lane]);
        }
        for lane in 0..PROGRAM_VK_LEN {
            cb.connect(carrier[carrier_vk + lane], direct[direct_vk + lane]);
        }

        // State meaning spans the complete cohort chain.
        for lane in 0..SEG_ANCHOR_WIDTH {
            cb.connect(carrier[SEG_FIRST_OLD + lane], direct[direct_old + lane]);
            cb.connect(carrier[SEG_LAST_NEW + lane], direct[direct_new + lane]);
        }

        // Application state comes from the terminal committed wide leg.
        for lane in 0..l {
            cb.connect(carrier[carrier_app + lane], direct[direct_app + lane]);
        }
        for lane in 0..POST_FIELDS_ROOT_LEN {
            cb.connect(
                carrier[carrier_fields_root + lane],
                direct[direct_fields_root + lane],
            );
        }

        cb.expose_as_public_output(&carrier[..SEG_WIDTH]);
    };

    p3_recursion::build_and_prove_aggregation_layer_with_expose::<
        DreggRecursionConfig,
        BatchOnly,
        BatchOnly,
        _,
        D,
    >(
        &carrier_input,
        &direct_input,
        config,
        &backend,
        &params,
        None,
        Some(&expose),
    )
    .map_err(|error| invalid(format!("whole-turn direct-IR2 binding failed: {error:?}")))
}

/// Claim widths for a complete whole-turn carrier.  Kept public so producer
/// code can build exact descriptor-leaf claim slices without re-authoring the
/// layout arithmetic.
pub const fn whole_turn_carrier_suffix_len(app_root_len: usize) -> usize {
    CUSTOM_COMMIT_LEN + PROGRAM_VK_LEN + app_root_len + POST_FIELDS_ROOT_LEN
}

/// The terminal suffix: final application fields plus the exact fields-map
/// root.  The terminal leg's field slice is selected by the verifier-declared
/// app-write policy; this function only fixes its claim layout.
pub const fn terminal_suffix_len(app_root_len: usize) -> usize {
    app_root_len + POST_FIELDS_ROOT_LEN
}

/// Complete suffix published by the terminal Custom sentinel: proof
/// commitment, canonical program VK, application fields, and exact fields-map
/// root, in the order consumed by the whole-turn binding node.
pub const fn terminal_custom_suffix_len(app_root_len: usize) -> usize {
    whole_turn_carrier_suffix_len(app_root_len)
}

/// PI slice the Custom head must retain from the deployed wide descriptor.
pub const fn custom_head_commit_pi_slice() -> (usize, usize) {
    (CUSTOM_COMMIT_PI_LO, CUSTOM_COMMIT_LEN)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn descent_six_count_layout_has_no_aliasing() {
        let l = 6;
        assert_eq!(terminal_suffix_len(l), 14);
        assert_eq!(whole_turn_carrier_suffix_len(l), 30);
        assert_eq!(terminal_custom_suffix_len(l), 30);

        let carrier_commit = SEG_WIDTH;
        let carrier_vk = carrier_commit + CUSTOM_COMMIT_LEN;
        let carrier_app = carrier_vk + PROGRAM_VK_LEN;
        let carrier_fields_root = carrier_app + l;
        let carrier_end = carrier_fields_root + POST_FIELDS_ROOT_LEN;
        assert_eq!(carrier_end, SEG_WIDTH + whole_turn_carrier_suffix_len(l));

        let direct_app = custom_app_root_claim_len(0);
        let direct_fields_root = custom_app_root_claim_len(l);
        let direct_vk = direct_fields_root + POST_FIELDS_ROOT_LEN;
        let direct_end = direct_vk + PROGRAM_VK_LEN;
        assert_eq!(direct_app, CUSTOM_COMMIT_LEN + 2 * SEG_ANCHOR_WIDTH);
        assert_eq!(direct_fields_root, direct_app + l);
        assert_eq!(
            direct_end,
            custom_app_root_claim_len(l) + POST_FIELDS_ROOT_LEN + PROGRAM_VK_LEN
        );
    }

    #[test]
    fn zero_width_application_root_is_not_a_valid_spine_policy() {
        assert_eq!(terminal_suffix_len(0), POST_FIELDS_ROOT_LEN);
        // The arithmetic helper remains total, while the proving entry point
        // explicitly refuses zero.  This pins the API split without paying a
        // recursion proof in the default test set.
        assert_eq!(whole_turn_carrier_suffix_len(0), 24);
    }
}
