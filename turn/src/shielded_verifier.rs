//! The shielded-transfer verification seam (privacy M2-a).
//!
//! A shielded transfer is admitted on a hiding uni-STARK plus a Pedersen
//! conservation/range side, and both verifiers live in `dregg-circuit-prove` —
//! the PROOF crate, not this one. Rather than pull that dependency into the core
//! executor behind a cfg-gate on a `prover` feature (whose un-selected arm is
//! never type-checked in a given build, the exact brittleness this campaign
//! retires — and which no longer exists on `dregg-turn` at all as of PR3), the
//! core defines the seam and `dregg-turn-prover` implements it.
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

/// What a [`ShieldOpeningVerifier`] RETURNS on accept: the `(value, asset, note
/// commitment)` the Lean-authored shield-opening relation PROVED, read off the
/// verified public claim — never re-read from the untrusted wire.
///
/// The core `apply_shield` path binds these against the effect's declared public
/// fields (`value == piVALUE`, the Shield-A boundary conservation) and appends
/// `note_commitment` to the shielded accumulator. A claim decoupled from the proof
/// never reaches here — the verifier's `.piBinding`s reject it first (Lean
/// `shield_value_decouple_unsat`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifiedShieldOpening {
    /// The proven public value `piVALUE` — the shielded note's worth.
    pub value: u64,
    /// The proven public asset `piASSET`.
    pub asset_type: u64,
    /// The minted note commitment the proof opened (`piCM`), as its canonical
    /// 32-byte encoding — the leaf the core appends to `note_shielded`.
    pub note_commitment: [u8; 32],
}

/// The injected verifier for [`crate::action::Effect::Shield`]'s MINT half — the
/// shield-opening relation `piCM = hash_fact(piVALUE, [piASSET, owner, rand])`.
///
/// Implemented by `dregg_turn_prover::CircuitShieldOpeningVerifier` over
/// `dregg-circuit-prove`'s `verify_shield_opening` (which reads the byte-pinned
/// Lean golden `dregg-shielded-shield::v1`); injected with
/// [`crate::executor::TurnExecutor::set_shield_opening_verifier`]. Fail-closed by
/// absence: no verifier injected ⇒ `Effect::Shield` is refused, exactly as the
/// `ShieldedTransferVerifier` seam behaves.
///
/// Pure verification, like [`ShieldedTransferVerifier`]: it receives the wire
/// public fields plus the proof bytes, runs the STARK gate, and returns the
/// proven data. It never sees the journal, the ledger, or the executor — the core
/// `apply_shield` path performs (and journals) the debit and the accumulator
/// append.
pub trait ShieldOpeningVerifier: Send + Sync {
    /// Verify the shield-opening proof against the declared public claim
    /// `(value, asset_type, note_commitment)`, returning the proven data or the
    /// refusal. `value`/`asset_type` are the effect's public fields;
    /// `note_commitment` is its canonical 32-byte encoding; `shield_proof` is the
    /// postcard `Ir2BatchProof`. A claim not backed by the proof MUST reject.
    fn verify(
        &self,
        value: u64,
        asset_type: u64,
        note_commitment: [u8; 32],
        shield_proof: &[u8],
    ) -> Result<VerifiedShieldOpening, TurnError>;
}
