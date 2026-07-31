//! Durable rotated-state acceptance anchor for exact FNSP-v3.
//!
//! The proof-facing rotated trace carries a 179-felt BEFORE payload and an AFTER payload.  A live
//! verifier must not accept those 179 felts from the proof or caller: doing so would let a valid
//! exact-nullifier transition float free of the durable actor state it is supposed to update.
//! This module builds the frame from the durable [`Cell`] and [`V9RotationContext`] instead:
//!
//! 1. [`compute_rotated_pre_limbs`] authors the canonical 178 pre-iroot limbs;
//! 2. the context's durable `iroot` becomes limb 178;
//! 3. the context's nullifier octet must equal the independently reconstructed prior `FNS3`;
//! 4. AFTER is derived by replacing only the exact eight [`NULLIFIER_OFFSETS`]; and
//! 5. both outer commitments are recomputed with the consensus chip chain and checked against
//!    [`crate::state_commit::cell_state_commitment`].
//!
//! The resulting object contains no proof bytes and has no constructor from an arbitrary payload.
//! It is additive and non-live until the v3 verifier/finalizer compares its sixteen expected public
//! lanes and the store atomically commits the corresponding exact append records.

use dregg_cell::Cell;
use dregg_cell::commitment::{
    V9_NUM_PRE_LIMBS, V9RotationContext, compute_rotated_pre_limbs, digest8_to_bytes32,
};
use dregg_circuit::Faithful8;
use dregg_circuit::exact_nullifier_aafi::Digest8;
use dregg_circuit::exact_nullifier_aafi_rotated_trace::{
    NULLIFIER_OFFSETS, OUTER_PUBLIC_INPUTS, ROTATED_IROOT_OFFSET, ROTATED_PAYLOAD_WIDTH,
    ROTATED_PRE_LIMBS, STABLE_FRAME_CELLS,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::poseidon2::wire_commit_8_chip;
use std::error::Error;
use std::fmt;

const _: () = {
    assert!(V9_NUM_PRE_LIMBS == ROTATED_PRE_LIMBS);
    assert!(ROTATED_IROOT_OFFSET == ROTATED_PRE_LIMBS);
    assert!(ROTATED_PAYLOAD_WIDTH == ROTATED_PRE_LIMBS + 1);
    assert!(OUTER_PUBLIC_INPUTS == 16);
    // ⚑ A LITERAL. This read `== 171` until the nine-lane epoch replaced it with `==
    // ROTATED_PAYLOAD_WIDTH - NULLIFIER_OFFSETS.len()` — which IS the definition of
    // `STABLE_FRAME_CELLS` in `exact_nullifier_aafi_rotated_trace`, so the cross-crate pin became
    // `x == x`. 178 → 184 moves it 171 → 177.
    assert!(STABLE_FRAME_CELLS == 177);
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExactFnspV3AnchorSide {
    Before,
    After,
}

/// Fail-closed errors at the durable rotated-state boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExactFnspV3DurableAnchorError {
    NonCanonicalFns3 {
        side: ExactFnspV3AnchorSide,
        lane: usize,
        value: u32,
    },
    NonCanonicalDurableLimb {
        offset: usize,
        value: u32,
    },
    PriorFns3ContextMismatch {
        lane: usize,
    },
    RotatedGeometry {
        expected: usize,
        actual: usize,
    },
    ConsensusCommitmentMismatch {
        side: ExactFnspV3AnchorSide,
    },
    OuterInputLength {
        expected: usize,
        actual: usize,
    },
    NonCanonicalOuterInput {
        lane: usize,
        value: u32,
    },
    OuterCommitmentMismatch {
        lane: usize,
        expected: u32,
        actual: u32,
    },
    ChainDiscontinuity {
        transition: usize,
        lane: usize,
    },
}

impl fmt::Display for ExactFnspV3DurableAnchorError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NonCanonicalFns3 { side, lane, value } => write!(
                f,
                "exact FNSP-v3 {side:?} FNS3 lane {lane} is non-canonical: {value}"
            ),
            Self::NonCanonicalDurableLimb { offset, value } => write!(
                f,
                "exact FNSP-v3 durable rotated limb {offset} is non-canonical: {value}"
            ),
            Self::PriorFns3ContextMismatch { lane } => write!(
                f,
                "exact FNSP-v3 prior FNS3 lane {lane} disagrees with durable rotation context"
            ),
            Self::RotatedGeometry { expected, actual } => write!(
                f,
                "exact FNSP-v3 durable rotation has {actual} pre-limbs, expected {expected}"
            ),
            Self::ConsensusCommitmentMismatch { side } => write!(
                f,
                "exact FNSP-v3 {side:?} outer commitment disagrees with consensus chip anchor"
            ),
            Self::OuterInputLength { expected, actual } => write!(
                f,
                "exact FNSP-v3 outer public input length {actual}, expected {expected}"
            ),
            Self::NonCanonicalOuterInput { lane, value } => write!(
                f,
                "exact FNSP-v3 outer public lane {lane} is non-canonical: {value}"
            ),
            Self::OuterCommitmentMismatch {
                lane,
                expected,
                actual,
            } => write!(
                f,
                "exact FNSP-v3 outer public lane {lane} is {actual}, expected {expected}"
            ),
            Self::ChainDiscontinuity { transition, lane } => write!(
                f,
                "exact FNSP-v3 transition {transition} prior lane {lane} does not continue the previous AFTER"
            ),
        }
    }
}

impl Error for ExactFnspV3DurableAnchorError {}

/// Canonical durable BEFORE/AFTER frame and its expected verifier-facing outer commitments.
///
/// Payload fields are private.  The only public constructor rebuilds them from durable state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactFnspV3DurableAnchor {
    before_payload: [BabyBear; ROTATED_PAYLOAD_WIDTH],
    after_payload: [BabyBear; ROTATED_PAYLOAD_WIDTH],
    before_commit: Digest8,
    after_commit: Digest8,
}

impl ExactFnspV3DurableAnchor {
    pub fn before_payload(&self) -> &[BabyBear; ROTATED_PAYLOAD_WIDTH] {
        &self.before_payload
    }

    pub fn after_payload(&self) -> &[BabyBear; ROTATED_PAYLOAD_WIDTH] {
        &self.after_payload
    }

    pub fn before_commit(&self) -> Digest8 {
        self.before_commit
    }

    pub fn after_commit(&self) -> Digest8 {
        self.after_commit
    }

    /// The exact public lanes 60..75 expected by the FNSP-v3 descriptor.
    pub fn expected_outer_public_inputs(&self) -> [u32; OUTER_PUBLIC_INPUTS] {
        let mut out = [0u32; OUTER_PUBLIC_INPUTS];
        for (slot, felt) in out
            .iter_mut()
            .zip(self.before_commit.into_iter().chain(self.after_commit))
        {
            *slot = felt.as_u32();
        }
        out
    }

    /// Strict verifier comparison for the outer 8+8 public lanes.
    pub fn verify_outer_public_inputs(
        &self,
        claimed: &[u32],
    ) -> Result<(), ExactFnspV3DurableAnchorError> {
        if claimed.len() != OUTER_PUBLIC_INPUTS {
            return Err(ExactFnspV3DurableAnchorError::OuterInputLength {
                expected: OUTER_PUBLIC_INPUTS,
                actual: claimed.len(),
            });
        }
        let expected = self.expected_outer_public_inputs();
        for (lane, (&actual, &expected)) in claimed.iter().zip(expected.iter()).enumerate() {
            if actual >= BABYBEAR_P {
                return Err(ExactFnspV3DurableAnchorError::NonCanonicalOuterInput {
                    lane,
                    value: actual,
                });
            }
            if actual != expected {
                return Err(ExactFnspV3DurableAnchorError::OuterCommitmentMismatch {
                    lane,
                    expected,
                    actual,
                });
            }
        }
        Ok(())
    }
}

/// Derive the exact rotated-state boundary from durable actor/context state.
///
/// `context.nullifier_root` is the durable exact-v3 authority and must carry `prior_fns3`.  The
/// function never repairs a mismatch by overwriting it: a caller that races or supplies the wrong
/// prior token is refused before an AFTER frame exists.
pub fn derive_exact_fnsp_v3_durable_anchor(
    actor: &Cell,
    context: &V9RotationContext,
    prior_fns3: Digest8,
    successor_fns3: Digest8,
) -> Result<ExactFnspV3DurableAnchor, ExactFnspV3DurableAnchorError> {
    validate_digest(ExactFnspV3AnchorSide::Before, prior_fns3)?;
    validate_digest(ExactFnspV3AnchorSide::After, successor_fns3)?;
    for (lane, (&durable, &prior)) in context
        .nullifier_root
        .limbs()
        .iter()
        .zip(prior_fns3.iter())
        .enumerate()
    {
        if durable != prior {
            return Err(ExactFnspV3DurableAnchorError::PriorFns3ContextMismatch { lane });
        }
    }

    let pre_limbs = compute_rotated_pre_limbs(actor, context);
    if pre_limbs.len() != ROTATED_PRE_LIMBS {
        return Err(ExactFnspV3DurableAnchorError::RotatedGeometry {
            expected: ROTATED_PRE_LIMBS,
            actual: pre_limbs.len(),
        });
    }
    let mut before_payload = [BabyBear::ZERO; ROTATED_PAYLOAD_WIDTH];
    before_payload[..ROTATED_PRE_LIMBS].copy_from_slice(&pre_limbs);
    before_payload[ROTATED_IROOT_OFFSET] = context.iroot;
    validate_payload(&before_payload)?;

    // The context equality above is not enough: pin the exact layout scatter too.  A future layout
    // drift cannot silently put the right octet in the wrong eight cells.
    for (lane, offset) in NULLIFIER_OFFSETS.iter().copied().enumerate() {
        if before_payload[offset] != prior_fns3[lane] {
            return Err(ExactFnspV3DurableAnchorError::PriorFns3ContextMismatch { lane });
        }
    }

    let mut after_payload = before_payload;
    for (lane, offset) in NULLIFIER_OFFSETS.iter().copied().enumerate() {
        after_payload[offset] = successor_fns3[lane];
    }

    let before_commit = wire_commit_8_chip(
        &before_payload[..ROTATED_PRE_LIMBS],
        before_payload[ROTATED_IROOT_OFFSET],
    );
    let consensus_before = crate::state_commit::cell_state_commitment(actor, context);
    if digest8_to_bytes32(before_commit) != consensus_before {
        return Err(ExactFnspV3DurableAnchorError::ConsensusCommitmentMismatch {
            side: ExactFnspV3AnchorSide::Before,
        });
    }

    let mut after_context = *context;
    after_context.nullifier_root = digest_as_faithful(successor_fns3);
    let after_commit = wire_commit_8_chip(
        &after_payload[..ROTATED_PRE_LIMBS],
        after_payload[ROTATED_IROOT_OFFSET],
    );
    let consensus_after = crate::state_commit::cell_state_commitment(actor, &after_context);
    if digest8_to_bytes32(after_commit) != consensus_after {
        return Err(ExactFnspV3DurableAnchorError::ConsensusCommitmentMismatch {
            side: ExactFnspV3AnchorSide::After,
        });
    }

    debug_assert!(
        (0..ROTATED_PAYLOAD_WIDTH)
            .filter(|offset| !NULLIFIER_OFFSETS.contains(offset))
            .all(|offset| before_payload[offset] == after_payload[offset])
    );
    Ok(ExactFnspV3DurableAnchor {
        before_payload,
        after_payload,
        before_commit,
        after_commit,
    })
}

/// Derive a multi-spend chain while advancing only the exact FNS3 octet in the durable context.
///
/// Each pair is independently pinned.  Pair `i+1` must begin exactly at pair `i`'s successor;
/// there is no sorting, gap repair, or caller-supplied stable frame.
pub fn derive_exact_fnsp_v3_durable_anchor_chain(
    actor: &Cell,
    initial_context: &V9RotationContext,
    transitions: &[(Digest8, Digest8)],
) -> Result<Vec<ExactFnspV3DurableAnchor>, ExactFnspV3DurableAnchorError> {
    let mut context = *initial_context;
    let mut previous_successor: Option<Digest8> = None;
    let mut anchors = Vec::with_capacity(transitions.len());
    for (transition, &(prior, successor)) in transitions.iter().enumerate() {
        if let Some(previous) = previous_successor {
            if let Some(lane) = previous
                .iter()
                .zip(prior.iter())
                .position(|(before, after)| before != after)
            {
                return Err(ExactFnspV3DurableAnchorError::ChainDiscontinuity { transition, lane });
            }
        }
        let anchor = derive_exact_fnsp_v3_durable_anchor(actor, &context, prior, successor)?;
        context.nullifier_root = digest_as_faithful(successor);
        previous_successor = Some(successor);
        anchors.push(anchor);
    }
    Ok(anchors)
}

fn validate_digest(
    side: ExactFnspV3AnchorSide,
    digest: Digest8,
) -> Result<(), ExactFnspV3DurableAnchorError> {
    for (lane, felt) in digest.into_iter().enumerate() {
        let value = felt.as_u32();
        if value >= BABYBEAR_P {
            return Err(ExactFnspV3DurableAnchorError::NonCanonicalFns3 { side, lane, value });
        }
    }
    Ok(())
}

fn validate_payload(
    payload: &[BabyBear; ROTATED_PAYLOAD_WIDTH],
) -> Result<(), ExactFnspV3DurableAnchorError> {
    for (offset, felt) in payload.iter().copied().enumerate() {
        let value = felt.as_u32();
        if value >= BABYBEAR_P {
            return Err(ExactFnspV3DurableAnchorError::NonCanonicalDurableLimb { offset, value });
        }
    }
    Ok(())
}

fn digest_as_faithful(digest: Digest8) -> Faithful8 {
    // Every lane was checked canonical before this conversion, so the full 32-byte split is an
    // exact round trip rather than a modular reduction.
    Faithful8::from_bytes32(&digest8_to_bytes32(digest))
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::commitment::RotationCarrierMaterial;
    use dregg_circuit::exact_nullifier_aafi::ExactNullifierAafi;

    fn actor() -> Cell {
        let mut cell = Cell::new([7u8; 32], [9u8; 32]);
        assert!(cell.state.credit_balance(500));
        cell.state.set_nonce(11);
        cell
    }

    fn context(prior_fns3: Digest8) -> V9RotationContext {
        V9RotationContext {
            // the empty-ledger faithful 8-felt cells root (wound #23: the field is `Faithful8`,
            // so a fixture must name a faithful constructor, not an arbitrary felt)
            cells_root: dregg_circuit::heap_root::empty_heap_root_8(),
            nullifier_root: digest_as_faithful(prior_fns3),
            commitments_root: Faithful8::ZERO,
            revoked_root: Faithful8::ZERO,
            iroot: BabyBear::new(202),
            material: RotationCarrierMaterial::default(),
        }
    }

    fn first_transition() -> (ExactNullifierAafi, Digest8, Digest8) {
        let mut accumulator = ExactNullifierAafi::new();
        let prior = accumulator.state_commit();
        let witness = accumulator
            .prepare_insert([0x44; 32], 44)
            .expect("first exact append");
        let successor = witness.successor_state_commit;
        accumulator
            .apply_witness(&witness)
            .expect("apply first exact append");
        (accumulator, prior, successor)
    }

    #[test]
    fn durable_anchor_builds_all_179_limbs_and_preserves_the_other_171() {
        let (_, prior, successor) = first_transition();
        let ctx = context(prior);
        let anchor = derive_exact_fnsp_v3_durable_anchor(&actor(), &ctx, prior, successor)
            .expect("durable anchor");

        assert_eq!(anchor.before_payload().len(), 179);
        assert_eq!(anchor.after_payload().len(), 179);
        let changed: Vec<_> = anchor
            .before_payload()
            .iter()
            .zip(anchor.after_payload().iter())
            .enumerate()
            .filter_map(|(offset, (before, after))| (before != after).then_some(offset))
            .collect();
        assert_eq!(changed, NULLIFIER_OFFSETS);
        assert_eq!(179 - changed.len(), STABLE_FRAME_CELLS);
        assert_eq!(
            anchor.before_payload()[ROTATED_IROOT_OFFSET],
            anchor.after_payload()[ROTATED_IROOT_OFFSET]
        );
        assert_eq!(
            digest8_to_bytes32(anchor.before_commit()),
            crate::state_commit::cell_state_commitment(&actor(), &ctx)
        );
        anchor
            .verify_outer_public_inputs(&anchor.expected_outer_public_inputs())
            .expect("honest public anchors");
    }

    #[test]
    fn durable_anchor_refuses_wrong_prior_fns3_and_noncanonical_context() {
        let (_, prior, successor) = first_transition();
        let ctx = context(prior);
        let mut wrong = prior;
        wrong[3] += BabyBear::ONE;
        assert_eq!(
            derive_exact_fnsp_v3_durable_anchor(&actor(), &ctx, wrong, successor),
            Err(ExactFnspV3DurableAnchorError::PriorFns3ContextMismatch { lane: 3 })
        );

        let mut noncanonical_prior = prior;
        noncanonical_prior[0] = BabyBear(BABYBEAR_P);
        assert_eq!(
            derive_exact_fnsp_v3_durable_anchor(&actor(), &ctx, noncanonical_prior, successor,),
            Err(ExactFnspV3DurableAnchorError::NonCanonicalFns3 {
                side: ExactFnspV3AnchorSide::Before,
                lane: 0,
                value: BABYBEAR_P,
            })
        );

        let mut malformed_ctx = ctx;
        malformed_ctx.iroot = BabyBear(BABYBEAR_P);
        assert_eq!(
            derive_exact_fnsp_v3_durable_anchor(&actor(), &malformed_ctx, prior, successor),
            Err(ExactFnspV3DurableAnchorError::NonCanonicalDurableLimb {
                offset: ROTATED_IROOT_OFFSET,
                value: BABYBEAR_P,
            })
        );
    }

    #[test]
    fn unrelated_durable_state_moves_outer_anchor_and_old_claim_refuses() {
        let (_, prior, successor) = first_transition();
        let ctx = context(prior);
        let original_actor = actor();
        let original = derive_exact_fnsp_v3_durable_anchor(&original_actor, &ctx, prior, successor)
            .expect("original anchor");

        let mut changed_actor = original_actor;
        changed_actor.state.set_nonce(12);
        let changed = derive_exact_fnsp_v3_durable_anchor(&changed_actor, &ctx, prior, successor)
            .expect("changed durable actor anchor");
        assert_ne!(original.before_payload()[2], changed.before_payload()[2]);
        assert_ne!(original.before_commit(), changed.before_commit());
        assert!(matches!(
            changed.verify_outer_public_inputs(&original.expected_outer_public_inputs()),
            Err(ExactFnspV3DurableAnchorError::OuterCommitmentMismatch { .. })
        ));
    }

    #[test]
    fn forged_or_noncanonical_outer_commit_refuses() {
        let (_, prior, successor) = first_transition();
        let anchor =
            derive_exact_fnsp_v3_durable_anchor(&actor(), &context(prior), prior, successor)
                .expect("anchor");
        let mut forged = anchor.expected_outer_public_inputs();
        forged[9] = (forged[9] + 1) % BABYBEAR_P;
        assert!(matches!(
            anchor.verify_outer_public_inputs(&forged),
            Err(ExactFnspV3DurableAnchorError::OuterCommitmentMismatch { lane: 9, .. })
        ));
        forged[9] = BABYBEAR_P;
        assert_eq!(
            anchor.verify_outer_public_inputs(&forged),
            Err(ExactFnspV3DurableAnchorError::NonCanonicalOuterInput {
                lane: 9,
                value: BABYBEAR_P,
            })
        );
        assert!(matches!(
            anchor.verify_outer_public_inputs(&forged[..15]),
            Err(ExactFnspV3DurableAnchorError::OuterInputLength { .. })
        ));
    }

    #[test]
    fn multi_spend_chain_requires_after_to_equal_next_before() {
        let (accumulator, first_prior, first_successor) = first_transition();
        let second_witness = accumulator
            .prepare_insert([0x88; 32], 88)
            .expect("second exact append");
        let second_successor = second_witness.successor_state_commit;
        let transitions = [
            (first_prior, first_successor),
            (first_successor, second_successor),
        ];
        let anchors = derive_exact_fnsp_v3_durable_anchor_chain(
            &actor(),
            &context(first_prior),
            &transitions,
        )
        .expect("two-spend anchor chain");
        assert_eq!(anchors.len(), 2);
        assert_eq!(anchors[0].after_payload(), anchors[1].before_payload());
        assert_eq!(anchors[0].after_commit(), anchors[1].before_commit());

        let mut disconnected = first_successor;
        disconnected[0] += BabyBear::ONE;
        assert_eq!(
            derive_exact_fnsp_v3_durable_anchor_chain(
                &actor(),
                &context(first_prior),
                &[
                    (first_prior, first_successor),
                    (disconnected, second_successor),
                ],
            ),
            Err(ExactFnspV3DurableAnchorError::ChainDiscontinuity {
                transition: 1,
                lane: 0,
            })
        );
    }
}
