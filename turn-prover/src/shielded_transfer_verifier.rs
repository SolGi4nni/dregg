//! The production [`ShieldedTransferVerifier`] — the cryptographic half of a shielded transfer,
//! over `dregg-circuit-prove`.
//!
//! This is the PROVER half of the seam described in `dregg_turn::shielded_verifier`. It is
//! deliberately VERIFY-RETURNS-VALUE: it receives the wire payload, runs the two Lean-emitted
//! relations, and returns the validated nullifiers and minted note commitments. It has no access to
//! the `LedgerJournal`, the `Ledger`, or the `TurnExecutor` — the core executor performs (and
//! journals) every state mutation. That is what lets `JournalEntry` stay `pub(crate)` in
//! `dregg-turn`.
//!
//! Nothing here is `#[cfg]`'d: this crate IS the prover, so a shape change in
//! `dregg-circuit-prove` or in `dregg_turn::action` is a compile error HERE, at the source.

use dregg_cell::ShieldedNoteCommitment;
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::shielded::ShieldedTransfer;
use dregg_turn::action::ShieldedTransferPayload;
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
        // Reconstruct the published shielded transfer from its wire payload, deserializing each
        // hidden proof.
        //
        // ⚑ No root parameter. `from_serialized_parts` has none, and the payload has no field that
        // could supply one — the committed root arrives as `committed_root`, from executor state.
        let transfer = ShieldedTransfer::from_serialized_parts(
            payload
                .inputs
                .iter()
                .map(|i| (i.nullifier, i.spend_wide_binding, i.spend_proof.clone()))
                .collect(),
            payload
                .outputs
                .iter()
                .map(|o| (o.note_commitment, o.link_proof.clone()))
                .collect(),
        )
        .map_err(|e| invalid(format!("shielded transfer payload malformed: {e}")))?;

        // ⚑ SAY THE SUBSTRATE OUT LOUD. Both relations this call runs are AUTHORED IN LEAN:
        // `dregg-shielded-spend-complete-fsi2::v1` (`ShieldedSpendCompleteEmit.lean`, 557 cols,
        // 25 PIs) and `dregg-shielded-transfer-value-link::v1`
        // (`ShieldedTransferValueLinkEmit.lean`, 164 cols, 17 PIs). This crate hands them public
        // inputs; it authors no constraint.
        //
        // `ShieldedTransfer::verify` runs, in order:
        //
        //   1. THE COMMITTED-ROOT SPEND (seam #15). Every input's complete-spend proof is judged
        //      against `committed_root`, which came from `note_shielded.root8()`. A spend proving
        //      membership in a tree the attacker built folds to `R != committed_root` and refuses.
        //
        //   2. THE ARITY GATE. One input, one output — the arity the value-link descriptor states.
        //      Anything else refuses rather than being admitted without a conservation statement.
        //
        //   3. ⚑ THE VALUE LINK — what this route exists for, and what the #15 lane left open.
        //      The residual it named, verbatim: "the Pedersen leg's own `v` is bound to the
        //      STARK-side `v` only through this TRANSCRIPT, not by an equality the circuit
        //      enforces … it does not make either of them open the value the Ristretto commitment
        //      holds." So a spender who genuinely owned a note worth 1 published legs worth
        //      1_000_000 and `verify_full_conservation_bytes` cleared over those legs.
        //
        //      There is no check that closes that: BabyBear cannot open a Ristretto point without
        //      non-native curve arithmetic in-AIR, and a sigma protocol cannot open a Poseidon2
        //      image without the hash in-group. So the Pedersen leg is GONE — no `input_legs`, no
        //      `output_legs`, no `output_range_proofs`, no `conservation`, and no transcript to
        //      carry them. What an output publishes is a Poseidon2 NOTE COMMITMENT, and the
        //      value-link relation forces it and the spend's sixteen carrier lanes to be functions
        //      of ONE canonical 16-bit limb opening. A minted note worth more (or less) than the
        //      spent one has no satisfying trace.
        //
        //      The sixteen lanes handed to the link come off the spend proof AFTER step 1, so the
        //      link is judged against a public input of an already-verified proof, not against its
        //      own claim (the `ShieldedWideJoinPin.join_still_decouples` discipline).
        //
        //      Range proofs are gone with the group that needed them: the value's four limb cells
        //      are booleanity-pinned in the AIR, so `0 <= v < 2^64` is a property of the trace.
        transfer
            .verify(committed_root)
            .map_err(|e| invalid(format!("shielded transfer rejected: {e}")))?;

        // Both relations passed. Hand back ONLY the validated data. The nullifiers are read off the
        // VERIFIED transfer (not re-read from the untrusted payload), and the output commitments
        // are the note commitments the value link just bound to the spent value — Poseidon2 leaves
        // the complete-spend relation can open, so what arrives is spendable.
        Ok(VerifiedShieldedTransfer {
            nullifiers: transfer.nullifiers().iter().map(|nf| nf.as_u32()).collect(),
            output_commitments: transfer
                .output_note_commitments()
                .into_iter()
                .map(ShieldedNoteCommitment)
                .collect(),
        })
    }
}
