//! The shielded-transfer verification seam (privacy M2-a).
//!
//! A shielded transfer is admitted on a hiding uni-STARK plus a Pedersen
//! conservation/range side, and both verifiers live in `dregg-circuit-prove` —
//! the PROOF crate, not this one. Rather than pull that dependency into the core
//! executor behind a `#[cfg(feature = "prover")]` (whose un-selected arm is never
//! type-checked in a given build, the exact brittleness this campaign retires),
//! the core defines the seam and `dregg-turn-prover` implements it.
//!
//! ## Verify-returns-VALUE (why the trait does not take the journal)
//!
//! The naive extraction hands the implementor `&mut LedgerJournal` so it can
//! record the spend and the shielded-note append itself. That would force
//! `JournalEntry` / `LedgerJournal` to become `pub`, promoting ~30 undo-log
//! variants to cross-crate ABI and re-opening the non-exhaustive-`match` hazard
//! one crate further out — i.e. exactly the bug class the extraction exists to
//! kill.
//!
//! So the trait is pure verification: it receives the wire payload, runs every
//! cryptographic gate, and RETURNS the validated data ([`VerifiedShieldedTransfer`]).
//! The core `apply` path then performs the nullifier consumption and the shielded
//! accumulator append, journaling each mutation. The implementor never sees the
//! journal, the ledger, or the executor. `JournalEntry` stays `pub(crate)` and its
//! exhaustive matches stay in-crate, where a missing arm is a same-build error.
//!
//! ## Fail-closed by absence
//!
//! [`crate::executor::TurnExecutor`] holds `Option<Arc<dyn ShieldedTransferVerifier>>`.
//! No verifier injected ⇒ `Effect::ShieldedTransfer` is refused, which is the
//! identical behavior to the old `#[cfg(not(feature = "prover"))]` stub — now
//! enforced by the type system and a crate boundary instead of a cfg matrix.

use dregg_cell::ShieldedNoteCommitment;

use crate::action::ShieldedTransferPayload;
use crate::error::TurnError;

/// What a shielded-transfer verifier RETURNS on accept: the two pieces of state
/// the core executor must land, and nothing else.
///
/// Every field is data the verifier *derived from proofs it just checked* — not a
/// re-read of the untrusted payload. In particular `nullifiers` are the field
/// elements recovered from the verified STARK statement, so the core's
/// double-spend gate consumes exactly what was proven, and `output_commitments`
/// are the legs whose range proofs and conservation the verifier accepted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedShieldedTransfer {
    /// The revealed input nullifiers as canonical BabyBear field elements, in the
    /// verified transfer's order. The core domain-separates each into the 32-byte
    /// `note_nullifiers` key space (a shielded nullifier must never collide with a
    /// cleartext one) and consumes it once, journaled.
    pub nullifiers: Vec<u32>,
    /// The output notes' hiding commitments, in leg order, to append to the
    /// committed-capable shielded accumulator (journaled for rollback).
    pub output_commitments: Vec<ShieldedNoteCommitment>,
}

/// The injected verifier for [`crate::action::Effect::ShieldedTransfer`].
///
/// Implemented by `dregg_turn_prover::CircuitShieldedTransferVerifier` over
/// `dregg-circuit-prove`; injected with
/// [`crate::executor::TurnExecutor::set_shielded_transfer_verifier`].
pub trait ShieldedTransferVerifier: Send + Sync {
    /// Run EVERY cryptographic gate over the wire payload and return the
    /// validated data, or the refusal.
    ///
    /// Implementors must be side-effect free with respect to ledger state: this
    /// is called mid-`apply` and its `Err` must leave nothing behind. The state
    /// mutations (nullifier consumption, accumulator append) belong to the core
    /// executor, which journals them.
    fn verify(
        &self,
        payload: &ShieldedTransferPayload,
    ) -> Result<VerifiedShieldedTransfer, TurnError>;
}
