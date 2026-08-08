//! The production [`DeshieldVerifier`] — the shielded **OFF-RAMP**
//! ([`dregg_turn::action::Effect::Deshield`]), over `dregg-circuit-prove`.
//!
//! This is the PROVER half of the seam described in `dregg_turn::shielded_verifier`. It is
//! deliberately VERIFY-RETURNS-VALUE: it receives the wire input payload, the DECLARED cleartext
//! credit and the executor's committed root, runs the two Lean-emitted relations, and returns the
//! validated nullifier. It has no access to the `LedgerJournal`, the `Ledger`, or the
//! `TurnExecutor` — the core `apply_deshield` path performs (and journals) the nullifier
//! consumption and the cleartext credit.
//!
//! **The AIR is AUTHORED IN LEAN.** Both relations this call runs are Lean-authored:
//! `dregg-shielded-spend-complete-fsi2::v1` (`ShieldedSpendCompleteEmit.lean`, 557 cols, 25 PIs)
//! and `dregg-shielded-deshield-value-link::v1` (`ShieldedDeshieldValueLinkEmit.lean`, 161 cols,
//! 24 PIs). This crate hands them public inputs; it authors no constraint.
//!
//! Nothing here is `#[cfg]`'d: this crate IS the prover, so a shape change in
//! `dregg-circuit-prove` or in `dregg_turn::action` is a compile error HERE, at the source.

use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::shielded::ShieldedDeshield;
use dregg_turn::action::ShieldedInputPayload;
use dregg_turn::error::TurnError;
use dregg_turn::shielded_verifier::{DeshieldVerifier, VerifiedDeshield};

/// The real deshield verifier. Inject with
/// [`dregg_turn::executor::TurnExecutor::set_deshield_verifier`].
#[derive(Clone, Copy, Debug, Default)]
pub struct CircuitDeshieldVerifier;

impl CircuitDeshieldVerifier {
    pub const fn new() -> Self {
        Self
    }
}

fn invalid(reason: String) -> TurnError {
    TurnError::InvalidEffect { reason }
}

impl DeshieldVerifier for CircuitDeshieldVerifier {
    fn verify(
        &self,
        input: &ShieldedInputPayload,
        credit_value: u64,
        credit_asset: u64,
        link_proof: &[u8],
        committed_root: [BabyBear; 8],
    ) -> Result<VerifiedDeshield, TurnError> {
        // Reconstruct the published deshield from its wire parts.
        //
        // ⚑ No root parameter here either. `from_serialized_parts` has none, and the payload has
        // no field that could supply one — the committed root arrives as `committed_root`, from
        // executor state.
        //
        // ⚑ The CREDIT is supplied from the EFFECT's declared public fields, which is the whole
        // point of this signature: it becomes the value-link statement's `vLimb[4] ++ aLimb[4]`
        // public inputs, so the relation is judged against the number the ledger is about to
        // record, not against a number the proof chose for itself.
        let deshield = ShieldedDeshield::from_serialized_parts(
            vec![(
                input.nullifier,
                input.spend_wide_binding,
                input.spend_proof.clone(),
            )],
            credit_value,
            credit_asset,
            link_proof.to_vec(),
        )
        .map_err(|e| invalid(format!("deshield payload malformed: {e}")))?;

        // `ShieldedDeshield::verify` runs, in order:
        //
        //   1. THE COMMITTED-ROOT SPEND (seam #15, inherited). The complete-spend proof is judged
        //      against `committed_root`, which came from `note_shielded.root8()`. A spend proving
        //      membership in a tree the attacker built folds to `R != committed_root` and refuses.
        //
        //   2. THE ARITY GATE. One spent note — the arity the value-link descriptor states.
        //      Anything else refuses BY NAME rather than being admitted without a conservation
        //      statement, exactly as `ShieldedTransfer` refuses 1-in/2-out.
        //
        //   3. ⚑ THE OFF-RAMP VALUE LINK — what this route exists for.
        //
        //      The theft it refuses: a deshield that CREDITS MORE CLEARTEXT than the note it
        //      spends holds. That is the on-ramp's mint-worth-more pointed the other way, and it
        //      is the EASIER one, because the credited value is a plain `u64` on the wire while
        //      the spent note's value is hidden. Nothing about "the proof verified" would catch
        //      it if the credit were merely carried alongside.
        //
        //      It is caught because the credit is not carried alongside. The relation reads ONE
        //      set of canonical 16-bit limb columns for BOTH the spent note's sixteen carrier
        //      lanes and the published credit limbs — the same absorb block the transfer's value
        //      link uses, IMPORTED from `WideValueBindingEmit` rather than mirrored (the Lean
        //      `absorb_block_is_the_transfer_value_links` is an `rfl` against the transfer link's
        //      own emitted site). There is no second value cell, so an inflated credit is not
        //      rejected — it has no satisfying trace (`inflated_credit_unsat`). Crediting a
        //      different ASSET likewise (`substituted_credit_asset_unsat`).
        //
        //      The sixteen lanes handed to the link come off the spend proof AFTER step 1, so the
        //      link is judged against a public input of an already-verified proof, not against its
        //      own claim (the `ShieldedWideJoinPin.join_still_decouples` discipline).
        //
        //      Range proofs are absent and not missed: the credit's four value-limb cells are
        //      booleanity-pinned in the AIR, so `0 <= v < 2^64` is a property of the trace and the
        //      Rust-side recomposition over the integers cannot alias or overflow.
        deshield
            .verify(committed_root)
            .map_err(|e| invalid(format!("deshield rejected: {e}")))?;

        // Both relations passed. Hand back ONLY the validated datum. The nullifier is read off the
        // VERIFIED deshield (not re-read from the untrusted payload).
        //
        // ⚑ No value is returned, and that absence is deliberate — see `VerifiedDeshield`. There
        // is nothing left for the executor to compare: acceptance above already MEANS the declared
        // credit is what the spent note holds.
        let nullifiers = deshield.nullifiers();
        let nullifier = nullifiers
            .first()
            .copied()
            .ok_or_else(|| invalid("deshield verified with no nullifier".into()))?;
        Ok(VerifiedDeshield {
            nullifier: nullifier.as_u32(),
        })
    }
}
