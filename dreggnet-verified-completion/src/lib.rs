//! A deliberately small boundary between replay-verifiable games and progression.
//!
//! The game remains the authority for its rules.  A progression system receives a
//! [`VerifiedCompletion`] only by calling [`CompletionVerifier::verify_completion`]; the
//! implementation is responsible for fresh replay and for checking the game's terminal
//! predicate.  This crate neither interprets commands nor manufactures another game's
//! completion format.

use std::collections::BTreeMap;

/// The immutable identity and replay-derived trajectory of one accepted completion.
///
/// `program_id`, `world_root`, and `completion_root` keep three distinct bindings: which
/// rules were executed, which genesis instance they ran against, and the exact terminal
/// journal head.  Metrics are complete genesis-through-terminal series supplied by the
/// game verifier, not counters submitted separately by a client.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedCompletion {
    program_id: [u8; 32],
    world_root: [u8; 32],
    completion_root: [u8; 32],
    actor: String,
    turns: usize,
    metrics: BTreeMap<String, Vec<u64>>,
}

impl VerifiedCompletion {
    /// Construct replay-derived facts inside a game-specific verifier implementation.
    ///
    /// This constructor rejects ambiguous identities and empty metric trajectories.  It
    /// cannot by itself prove that its caller replayed a game; that trust boundary is the
    /// Rust implementation of [`CompletionVerifier`], just as it is for every concrete
    /// `verify_completion` function.
    pub fn new(
        program_id: [u8; 32],
        world_root: [u8; 32],
        completion_root: [u8; 32],
        actor: impl Into<String>,
        turns: usize,
        metrics: BTreeMap<String, Vec<u64>>,
    ) -> Result<Self, &'static str> {
        let actor = actor.into();
        if actor.is_empty() {
            return Err("a verified completion must bind a non-empty actor");
        }
        if metrics.values().any(Vec::is_empty) {
            return Err("a verified metric trajectory cannot be empty");
        }
        Ok(Self {
            program_id,
            world_root,
            completion_root,
            actor,
            turns,
            metrics,
        })
    }

    pub const fn program_id(&self) -> [u8; 32] {
        self.program_id
    }

    pub const fn world_root(&self) -> [u8; 32] {
        self.world_root
    }

    pub const fn completion_root(&self) -> [u8; 32] {
        self.completion_root
    }

    pub fn actor(&self) -> &str {
        &self.actor
    }

    pub const fn turns(&self) -> usize {
        self.turns
    }

    /// The replay-derived genesis-through-terminal values of `name`.
    pub fn metric(&self, name: &str) -> Option<&[u64]> {
        self.metrics.get(name).map(Vec::as_slice)
    }

    /// A collision-resistant tuple for replay/dedup indexes.
    pub const fn key(&self) -> VerifiedCompletionKey {
        VerifiedCompletionKey {
            program_id: self.program_id,
            world_root: self.world_root,
            completion_root: self.completion_root,
        }
    }
}

/// The exact program, world, and terminal record head of a completion.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VerifiedCompletionKey {
    pub program_id: [u8; 32],
    pub world_root: [u8; 32],
    pub completion_root: [u8; 32],
}

/// A game-specific, fresh completion verifier.
///
/// Implementations must treat the completion object as untrusted, replay its record from
/// the named genesis under the named program, check its terminal success predicate, and
/// derive every returned fact from that replay.  Consumers call this method themselves;
/// they do not accept a serialized [`VerifiedCompletion`] from a player.
pub trait CompletionVerifier {
    type Error: std::fmt::Display + Send + Sync + 'static;

    fn verify_completion(&self) -> Result<VerifiedCompletion, Self::Error>;
}
