//! Proof tier markers — informational classification of proof backends.
//!
//! The codebase has multiple proof backends (custom STARK, Kimchi native, Mina/Pickles,
//! structural stubs). All produce bytes that look like
//! "proofs," but only a subset provide real cryptographic soundness guarantees.
//!
//! This module introduces:
//! - [`ProofTier`]: an enum marking whether a proof is production-grade, experimental,
//!   or structural-only. Used for logging, metrics, and diagnostics.
//! - [`CryptographicProof`]: a marker trait that proof types implement to declare their tier.
//! - [`VerifiedProof`]: a wrapper returned by verification functions that carries the tier.
//!
//! **Tier is informational only and NOT used for verification acceptance decisions.**
//! A proof is accepted if it passes cryptographic STARK verification for a known AIR.
//! Structural stubs cannot produce valid STARK proofs, so they are naturally rejected
//! by the cryptographic check without needing a separate tier gate. The tier enum is
//! retained for diagnostics, logging, and metrics (e.g., tracking which backends are
//! producing proofs in the wild).

use std::fmt;

/// Proof tiers — informational classification for logging and metrics.
///
/// This enum is NOT used for verification acceptance decisions. A proof is accepted
/// if it passes cryptographic STARK verification. The tier is metadata indicating
/// the backend's maturity level.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ProofTier {
    /// Real cryptographic proof with full soundness guarantees.
    /// Produced by: Plonky3, Poseidon2 STARK, Kimchi native, Pickles.
    Production,
    /// Proof from a backend that is in development. May have known weaknesses.
    /// Produced by: custom STARK (base-field only).
    Experimental,
    /// Structural validation only — no cryptographic guarantees.
    /// Historically produced by the retired "constraint prover" (now honestly
    /// renamed in [`crate::constraint_prover`], which no longer poses as a
    /// proof backend). No live producer constructs this tier.
    /// Such artifacts cannot pass STARK verification and are rejected naturally.
    Structural,
}

impl fmt::Display for ProofTier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProofTier::Production => write!(f, "Production"),
            ProofTier::Experimental => write!(f, "Experimental"),
            ProofTier::Structural => write!(f, "Structural"),
        }
    }
}

/// Marker trait for proofs that declare their cryptographic strength tier.
///
/// Backends implement this on their proof types so that verification boundaries
/// can reject non-production proofs without needing to know which specific backend
/// produced them.
pub trait CryptographicProof {
    /// Returns the tier of this proof.
    fn tier(&self) -> ProofTier;
}

/// A verified proof that carries its tier information.
///
/// Returned by verification functions. The tier is informational metadata for
/// logging and metrics — it is NOT used for acceptance decisions.
#[derive(Clone, Debug)]
pub struct VerifiedProof {
    /// The tier of the backend that produced this proof.
    tier: ProofTier,
    /// The backend name (for diagnostics).
    backend: &'static str,
    /// The federation root the proof was verified against (if applicable).
    pub federation_root: Option<[u8; 32]>,
}

impl VerifiedProof {
    /// Create a new verified proof with the given tier and backend name.
    pub fn new(tier: ProofTier, backend: &'static str) -> Self {
        Self {
            tier,
            backend,
            federation_root: None,
        }
    }

    /// Create a verified proof with federation root binding.
    pub fn with_federation_root(tier: ProofTier, backend: &'static str, root: [u8; 32]) -> Self {
        Self {
            tier,
            backend,
            federation_root: Some(root),
        }
    }

    /// Returns the tier of this verified proof.
    pub fn tier(&self) -> ProofTier {
        self.tier
    }

    /// Returns the backend name that produced this proof.
    pub fn backend(&self) -> &'static str {
        self.backend
    }

    /// Returns true if this proof is production-grade.
    pub fn is_production(&self) -> bool {
        self.tier == ProofTier::Production
    }

    /// Returns true if this proof is at least experimental (not structural).
    pub fn is_cryptographic(&self) -> bool {
        matches!(self.tier, ProofTier::Production | ProofTier::Experimental)
    }
}

impl CryptographicProof for VerifiedProof {
    fn tier(&self) -> ProofTier {
        self.tier
    }
}

// ============================================================================
// Tier assignments for each backend
// ============================================================================

/// Returns the proof tier for the custom STARK backend.
///
/// The custom STARK uses extension-field (BabyBear^4) composition for 124-bit
/// security on constraint combination. However, the Fiat-Shamir transcript and
/// FRI implementation are hobby-grade compared to Plonky3. Demoted to
/// Experimental now that Plonky3 is the production prover.
pub fn stark_tier() -> ProofTier {
    ProofTier::Experimental
}

// `constraint_prover_tier()` was DELETED 2026-07-17: zero callers workspace-wide,
// and it advertised the constraint VALIDATOR (`constraint_prover::ConstraintValidator`)
// as a proof backend, which it is not.

/// Returns the proof tier for the Plonky3 backend.
///
/// Plonky3 is a battle-tested proving system. Production-grade when available.
pub fn plonky3_tier() -> ProofTier {
    ProofTier::Production
}

// ============================================================================
// Backend name constants
// ============================================================================

/// Backend name for the custom STARK prover.
pub const STARK_BACKEND: &str = "custom-stark";
// `CONSTRAINT_PROVER_BACKEND` deleted 2026-07-17 (zero callers; there is no
// constraint-prover proof backend — see `constraint_prover` module docs).
/// Backend name for Plonky3.
pub const PLONKY3_BACKEND: &str = "plonky3";
