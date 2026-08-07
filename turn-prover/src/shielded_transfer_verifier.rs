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
use dregg_circuit::field::BabyBear;
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
        committed_root: [BabyBear; 8],
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
        // ⚑ No root parameter. `from_serialized_parts` has none, and the payload has no field that
        // could supply one — the committed root arrives as `committed_root`, from executor state.
        let transfer = ShieldedTransfer::from_serialized_parts(
            payload
                .inputs
                .iter()
                .map(|i| (i.nullifier, i.spend_wide_binding, i.spend_proof.clone()))
                .collect(),
            payload.input_legs.iter().map(leg).collect(),
            payload.output_legs.iter().map(leg).collect(),
            payload.output_range_proofs.clone(),
        )
        .map_err(|e| invalid(format!("shielded transfer payload malformed: {e}")))?;

        // GATE 1: the COMPLETE-spend STARK under the EXECUTOR'S committed root, plus the
        // cryptographic SAME-OPENING join of each input's wide sidecar to the spend proof's OWN
        // full-`u64` wide carrier (the value coordinate the conservation clears).
        //
        // ⚑ SAY THE SUBSTRATE OUT LOUD. Both relations are AUTHORED IN LEAN:
        // `dregg-shielded-spend-complete-fsi2::v1` (`ShieldedSpendCompleteEmit.lean`, 557 cols,
        // 25 PIs) and the wide sidecar (`WideValueBindingEmit.lean`). This crate hands them
        // witnesses and public inputs; it authors no constraint.
        //
        // ⚑ FLAG DAY — this call site used to FAIL CLOSED, deliberately, and now it does not.
        // The note that stood here explained that the retired spend circuit published only a
        // one-felt `value_binding`, so there was no ring-side full-`u64` carrier for the join, and
        // that `ring_wide_bindings` was therefore passed EMPTY — no shielded transfer succeeded at
        // all. The complete spend PI-pins its own sixteen `cap_node8` lanes (`carrierPins`), so
        // `verify_stark_with_wide_bindings` reads the ring binding off each verified input. It is
        // not the sidecar's claim handed back to itself — that is the vacuity
        // `ShieldedWideJoinPin.join_still_decouples` names — it is a public input of a SEPARATE
        // proof, checked first.
        //
        // ⚑ AND: `committed_root` is the seam-#15 pin. A spend proving membership in a tree the
        // attacker built folds to `R != committed_root` and refuses inside this call.
        verify_stark_with_wide_bindings(&transfer, &wide_bindings, committed_root)
            .map_err(|e| invalid(format!("shielded wide STARK verification failed: {e}")))?;
        // The structural inflation gate: exactly one range proof per output.
        transfer
            .check_range_proof_shape()
            .map_err(|e| invalid(format!("shielded range-proof shape rejected: {e}")))?;

        // GATE 2: the hidden Pedersen side — conservation (Σ in = Σ out) AND each output's range
        // proof, over the transfer's binding transcript.
        //
        // ⚑ THE CONSERVATION RECONCILIATION, stated as a chain — each link is a check above:
        //   note value `v` (witness-only in the complete spend)
        //     →[Lean `carrierPins`]      the sixteen ring carrier lanes
        //     →[`verify_same_opening`]   the sidecar's sixteen lanes  (GATE 1)
        //     →[Lean wide-sidecar relation] a canonical full-`u64` `(value, asset)` opening
        //     →[this transcript]         absorbed into `message`
        //     →[Schnorr excess + Bulletproofs] `Σ C_in = Σ C_out`, every output in `[0, 2^64)`
        // The transcript also absorbs `committed_root`, so a conservation proof cannot be replayed
        // against a different accumulator state.
        //
        // ⚑ NAMED RESIDUAL, unchanged by this route and NOT closed by it: the Pedersen leg's own
        // `v` is bound to the STARK-side `v` only through this TRANSCRIPT, not by an equality the
        // circuit enforces. `dregg_cell_crypto::value_commitment::verify_value_link` is the
        // compatibility bridge and it is exercised in TESTS ONLY. The wide join makes both proofs
        // open the SAME `(value, asset)` as each other; it does not make either of them open the
        // value the Ristretto commitment holds. That is the value-link leg, and it is still open.
        let message = wide_transfer_message(&transfer, &wide_bindings, committed_root)
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
