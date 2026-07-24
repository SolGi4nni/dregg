//! The production [`ShieldedTransferVerifier`] — gates 1 and 2 of a shielded
//! transfer (privacy M2-a), over `dregg-circuit-prove`.
//!
//! This is the PROVER half of the seam described in
//! `dregg_turn::shielded_verifier`. It is deliberately VERIFY-RETURNS-VALUE: it
//! receives the wire payload, runs the hiding uni-STARK join and the Pedersen
//! conservation/range side, and returns the validated nullifiers and output
//! commitments. It has no access to the `LedgerJournal`, the `Ledger`, or the
//! `TurnExecutor` — the core executor performs (and journals) every state
//! mutation. That is what lets `JournalEntry` stay `pub(crate)` in `dregg-turn`.
//!
//! Nothing here is `#[cfg]`'d: this crate IS the prover, so a shape change in
//! `dregg-circuit-prove` or in `dregg_turn::action` is a compile error HERE, at
//! the source.

use dregg_cell::ShieldedNoteCommitment;
use dregg_circuit_prove::shielded::{
    ShieldedTransfer, ShieldedValueLeg, WideValueBindingProof, verify_stark_with_wide_bindings,
    wide_transfer_message,
};
use dregg_turn::action::{ShieldedLeg, ShieldedTransferPayload};
use dregg_turn::error::TurnError;
use dregg_turn::shielded_verifier::{ShieldedTransferVerifier, VerifiedShieldedTransfer};

/// The real shielded-transfer verifier. Inject with
/// [`dregg_turn::executor::TurnExecutor::set_shielded_transfer_verifier`].
#[derive(Clone, Copy, Debug, Default)]
pub struct CircuitShieldedTransferVerifier;

impl CircuitShieldedTransferVerifier {
    pub const fn new() -> Self {
        Self
    }
}

fn invalid(reason: String) -> TurnError {
    TurnError::InvalidEffect { reason }
}

impl ShieldedTransferVerifier for CircuitShieldedTransferVerifier {
    fn verify(
        &self,
        payload: &ShieldedTransferPayload,
    ) -> Result<VerifiedShieldedTransfer, TurnError> {
        // Reconstruct every mandatory full-width proof first. There is no
        // compatibility fallback: a pre-cutover one-felt-only payload cannot
        // reach the no-mint verifier.
        let wide_bindings: Vec<WideValueBindingProof> = payload
            .inputs
            .iter()
            .map(|input| {
                WideValueBindingProof::from_serialized_parts(
                    input.legacy_value_binding,
                    input.wide_value_binding,
                    &input.wide_value_proof,
                )
            })
            .collect::<Result<_, _>>()
            .map_err(|e| invalid(format!("shielded wide value binding malformed: {e}")))?;

        // Reconstruct the published shielded transfer from its wire payload,
        // deserializing each hidden note-spend proof.
        let leg = |l: &ShieldedLeg| ShieldedValueLeg {
            asset_type: l.asset_type,
            commitment_bytes: l.commitment_bytes,
        };
        let transfer = ShieldedTransfer::from_serialized_parts(
            payload.merkle_root,
            payload
                .inputs
                .iter()
                .map(|i| (i.nullifier, i.legacy_value_binding, i.spend_proof.clone()))
                .collect(),
            payload.input_legs.iter().map(leg).collect(),
            payload.output_legs.iter().map(leg).collect(),
            payload.output_range_proofs.clone(),
        )
        .map_err(|e| invalid(format!("shielded transfer payload malformed: {e}")))?;

        // GATE 1: membership/nullifier plus exactly one canonical full-u64
        // binding per input. The legacy felt is now only an equality join.
        verify_stark_with_wide_bindings(&transfer, &wide_bindings)
            .map_err(|e| invalid(format!("shielded wide STARK verification failed: {e}")))?;
        // The structural inflation gate: exactly one range proof per output.
        transfer
            .check_range_proof_shape()
            .map_err(|e| invalid(format!("shielded range-proof shape rejected: {e}")))?;

        // GATE 2: the hidden Pedersen side — conservation (Σ in = Σ out) AND each
        // output's range proof, over the transfer's binding transcript.
        let message = wide_transfer_message(&transfer, &wide_bindings)
            .map_err(|e| invalid(format!("shielded wide transcript rejected: {e}")))?;
        dregg_cell_crypto::value_commitment::verify_full_conservation_bytes(
            &transfer.input_commitment_bytes(),
            &transfer.output_commitment_bytes(),
            &payload.conservation,
            &transfer.output_range_proofs,
            &message,
        )
        .map_err(|e| invalid(format!("shielded value conservation/range rejected: {e:?}")))?;

        // Both gates passed. Hand back ONLY the validated data. The nullifiers are
        // read off the VERIFIED transfer (not re-read from the untrusted payload),
        // and the output commitments are the legs whose range proofs and
        // conservation were just accepted.
        Ok(VerifiedShieldedTransfer {
            nullifiers: transfer.nullifiers().iter().map(|nf| nf.as_u32()).collect(),
            output_commitments: transfer
                .output_legs
                .iter()
                .map(|leg| ShieldedNoteCommitment(leg.commitment_bytes))
                .collect(),
        })
    }
}
