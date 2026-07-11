//! Error types for verification and drawing.

use thiserror::Error;

/// A verifier rejected randomness evidence.
///
/// Every variant is a *detectable* failure a re-executing light client raises
/// when re-deriving the seed from `(request, evidence)`. None of these are
/// availability/abort failures — those are a policy concern outside the pure
/// verifier (see the crate docs on selective abort).
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum VerifyError {
    /// The evidence's opening does not match its bound commitment (e.g. a
    /// tampered commit-reveal `server_reveal` no longer hashes to the recorded
    /// `server_commitment`).
    #[error("commitment mismatch: evidence opening does not match its bound commitment")]
    CommitmentMismatch,

    /// The draw transcript recomputed from the re-derived seed does not match
    /// the transcript commitment in the evidence. This fires when `draw_count`,
    /// `event_kind`, the action, the pre-state, or any seed input was altered
    /// after the evidence was produced — i.e. **grinding was detected**.
    #[error("draw-transcript mismatch: seed/draw_count grinding detected")]
    TranscriptMismatch,

    /// The evidence's source kind is not the one this verifier understands
    /// (e.g. calling `CommitReveal::seed` on `EvidenceKind::Beacon` evidence).
    #[error("evidence source kind does not match this verifier")]
    SourceMismatch,

    /// The evidence was produced under a derivation version this build does not
    /// support.
    #[error("unsupported derivation version {found} (this build derives v{expected})")]
    UnsupportedVersion { expected: u32, found: u32 },

    /// The source requires an external backend that is not wired in this slice
    /// (the `Hybrid` delayed-beacon + VRF stub). The trait shape is fixed; the
    /// backend is a documented follow-up.
    #[error("source backend unavailable: {0}")]
    BackendUnavailable(&'static str),

    /// An LB-VRF evidence field (public key / output / proof) was not the canonical
    /// byte length its `pqvrf` structure requires, so it could not be decoded. A
    /// verifier rejects it before running the proof check.
    #[error("malformed LB-VRF evidence: {0}")]
    MalformedVrfEvidence(&'static str),

    /// `pqvrf::verify` rejected the LB-VRF `(output, proof)` under the evidence's
    /// public key and the request's event id. This is the one-output-per-input
    /// tooth: a forged output or proof (one the LB-VRF secret never produced for
    /// this input) fails here, its uniqueness reducing to Module-SIS.
    #[error("LB-VRF proof failed verification (forged output/proof under the committed key)")]
    VrfProofInvalid,

    /// The evidence's VRF key-chain root and beacon parameters do not reproduce the
    /// request's `game_binding`. The key-chain or beacon was not the one committed
    /// at genesis (escape hatches #1/#2): a swapped key-chain root, beacon, or
    /// schedule is rejected.
    #[error(
        "genesis binding mismatch: VRF key-chain root / beacon params were not bound at genesis"
    )]
    GenesisBindingMismatch,

    /// The hybrid evidence's epoch public key is not the key committed at leaf
    /// `seq` of the genesis key-chain root — the Merkle membership proof does not
    /// verify. The server tried to evaluate under a key from a different (or fresh)
    /// epoch than the one this transition's `seq` binds (escape hatch #1).
    #[error("epoch key mismatch: the eval key is not the genesis-committed key for this seq")]
    EpochKeyMismatch,

    /// The beacon round in the evidence is not the schedule-derived round for this
    /// event's `seq`. The server cannot pick a favourable already-published round
    /// (escape hatch #2, schedule layer).
    #[error("beacon round mismatch: round is not the one the schedule binds to this seq")]
    BeaconRoundMismatch,

    /// The beacon output does not verify against the pinned beacon parameters for
    /// its round (e.g. it does not chain to the genesis-pinned hash-chain anchor).
    #[error("beacon output failed verification against the pinned beacon parameters")]
    BeaconVerifyFailed,
}

/// A draw was requested outside the bounds fixed by the request.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum DrawError {
    /// `index >= draw_count`. `draw_count` is bound into the `EventId`, so the
    /// legal index range is fixed before the seed exists; an out-of-range draw
    /// is never part of a valid transcript.
    #[error("draw index {index} out of range (draw_count = {draw_count})")]
    IndexOutOfRange { index: u32, draw_count: u32 },

    /// A bounded draw was requested with `n == 0`; `0..0` is empty.
    #[error("bounded draw requires a non-zero bound")]
    ZeroBound,
}
