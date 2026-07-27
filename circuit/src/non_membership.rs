//! General-purpose non-membership proving system.
//!
//! Generalizes revocation-specific non-membership to any property set. The core idea:
//! state "element X is NOT in set S" via a polynomial-evaluation accumulator over
//! BabyBear^4, regardless of what the set represents (revocation, suspension, blacklist,
//! role exclusion, etc.).
//!
//! # Scope: this module states the accumulator, it does not prove it
//!
//! What lives here is the SET SIDE: the set-bound challenge `alpha`, the accumulator
//! `Acc = prod(alpha - h_i)` over the set, and [`NonMembershipCheck`] — the composable
//! description of "this attribute is not in that set". The AIR that actually PROVES a
//! non-membership witness against `(Acc, alpha)` is [`crate::dsl::accumulator`]
//! (`accumulator_dsl_circuit` / `generate_accumulator_trace`, 9 public inputs:
//! `Acc[0..4]`, `alpha[4..8]`, `num_ancestors[8]`).
//!
//! # Usage
//!
//! ```
//! use dregg_circuit::field::BabyBear;
//! use dregg_circuit::non_membership::{
//!     NonMembershipCheck, NonMembershipExtElem, NonMembershipProver, SetIdentifier,
//!     compute_set_accumulator,
//! };
//!
//! let suspended = vec![BabyBear::new(11), BabyBear::new(22), BabyBear::new(33)];
//! let set_id = SetIdentifier::new("suspended");
//! let prover = NonMembershipProver::with_set_id(&suspended, set_id.clone());
//!
//! // The accumulator IS the polynomial evaluation at the set-bound challenge.
//! assert_eq!(
//!     prover.accumulator(),
//!     compute_set_accumulator(&suspended, prover.alpha()),
//! );
//!
//! // A MEMBER is a root: `(alpha - h)` divides `Acc` exactly.
//! let member = suspended[1];
//! let rest: Vec<BabyBear> = suspended.iter().copied().filter(|h| *h != member).collect();
//! let alpha_minus_member = prover.alpha().sub(NonMembershipExtElem::from_base(member));
//! assert_eq!(
//!     prover.accumulator(),
//!     compute_set_accumulator(&rest, prover.alpha()).mul(alpha_minus_member),
//! );
//!
//! // The set identifier is mixed into `alpha`, so the SAME elements under a different
//! // set name yield a different challenge — this is what blocks cross-set replay.
//! let other = NonMembershipProver::with_set_id(&suspended, SetIdentifier::new("blacklisted"));
//! assert_ne!(prover.alpha(), other.alpha());
//! assert_ne!(prover.accumulator(), other.accumulator());
//!
//! // What a consumer composes into a derivation: the attribute, the set, and the
//! // `(Acc, alpha)` pair a verifier needs — never the set itself.
//! let check = NonMembershipCheck {
//!     attribute: "user_id".to_string(),
//!     set_id,
//!     accumulator: prover.accumulator(),
//!     alpha: prover.alpha(),
//!     num_elements: 1,
//! };
//! assert_eq!(check.attribute, "user_id");
//! ```

use crate::accumulator_types::{ExtElem, compute_accumulator};
use crate::field::BabyBear;
use crate::poseidon2::hash_many;

// Re-export key types from accumulator_types for convenience.
pub use crate::accumulator_types::ExtElem as NonMembershipExtElem;

/// Identifier for a property set (e.g., "suspended", "blacklisted", "revoked").
///
/// The set_id is incorporated into the alpha challenge derivation to ensure
/// that proofs are bound to a specific set and cannot be replayed across sets.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SetIdentifier {
    /// Human-readable name (used for debugging/logging only).
    pub name: String,
    /// Domain separator: a field element derived from the set's identity.
    /// Different sets MUST have different domain separators.
    pub domain_sep: BabyBear,
}

impl SetIdentifier {
    /// Create a new set identifier from a name.
    /// The domain separator is derived by hashing the name.
    pub fn new(name: &str) -> Self {
        let name_hash = blake3::hash(name.as_bytes());
        let bytes = name_hash.as_bytes();
        let domain_sep = BabyBear::new(
            u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]) % crate::field::BABYBEAR_P,
        );
        Self {
            name: name.to_string(),
            domain_sep,
        }
    }

    /// Create a set identifier from a raw domain separator.
    pub fn from_raw(name: &str, domain_sep: BabyBear) -> Self {
        Self {
            name: name.to_string(),
            domain_sep,
        }
    }

    /// The "revocation" set identifier (backward compatible with AccumulatorNonRevocationAir).
    pub fn revocation() -> Self {
        Self {
            name: "revocation".to_string(),
            domain_sep: BabyBear::new(0x7265766F), // "revo"
        }
    }
}

/// A non-membership check to be composed with derivation proofs.
///
/// This specifies that a particular attribute's hash must NOT appear in
/// a given property set.
#[derive(Clone, Debug)]
pub struct NonMembershipCheck {
    /// The attribute being checked (e.g., "user_id", "credential_hash").
    pub attribute: String,
    /// The property set this element must NOT be in.
    pub set_id: SetIdentifier,
    /// The accumulator value for the property set.
    pub accumulator: ExtElem,
    /// The alpha challenge for the property set.
    pub alpha: ExtElem,
    /// Number of elements being checked.
    pub num_elements: usize,
}

/// Builder/prover for non-membership proofs.
///
/// Encapsulates the set's accumulator state and provides methods to
/// prove and verify non-membership of elements.
#[derive(Clone, Debug)]
pub struct NonMembershipProver {
    /// The set's elements (needed for witness generation).
    set_elements: Vec<BabyBear>,
    /// The computed accumulator value.
    accumulator: ExtElem,
    /// The alpha challenge derived from the set.
    alpha: ExtElem,
    /// The set identifier.
    set_id: SetIdentifier,
}

impl NonMembershipProver {
    /// Create a new non-membership prover for a given set.
    ///
    /// Uses the default alpha derivation (same as the revocation system).
    pub fn new(set_elements: &[BabyBear]) -> Self {
        Self::with_set_id(set_elements, SetIdentifier::revocation())
    }

    /// Create a non-membership prover with a specific set identifier.
    ///
    /// The set identifier is mixed into the alpha derivation, ensuring
    /// proofs for different sets cannot be confused.
    pub fn with_set_id(set_elements: &[BabyBear], set_id: SetIdentifier) -> Self {
        let alpha = derive_alpha_for_set(set_elements, &set_id);
        let accumulator = compute_accumulator(set_elements, alpha);
        Self {
            set_elements: set_elements.to_vec(),
            accumulator,
            alpha,
            set_id,
        }
    }

    /// Create a prover with an explicit alpha challenge.
    ///
    /// Use this when the alpha is provided externally (e.g., from a federation).
    pub fn with_explicit_alpha(
        set_elements: &[BabyBear],
        alpha: ExtElem,
        set_id: SetIdentifier,
    ) -> Self {
        let accumulator = compute_accumulator(set_elements, alpha);
        Self {
            set_elements: set_elements.to_vec(),
            accumulator,
            alpha,
            set_id,
        }
    }

    /// Get the accumulator value for this set.
    pub fn accumulator(&self) -> ExtElem {
        self.accumulator
    }

    /// Get the alpha challenge for this set.
    pub fn alpha(&self) -> ExtElem {
        self.alpha
    }

    /// Get the set identifier.
    pub fn set_id(&self) -> &SetIdentifier {
        &self.set_id
    }
}

/// Derive the alpha challenge for a specific set, incorporating the set identifier.
///
/// This ensures that proofs for different sets (revocation, suspension, etc.)
/// use different alpha values and cannot be cross-replayed.
pub fn derive_alpha_for_set(set_elements: &[BabyBear], set_id: &SetIdentifier) -> ExtElem {
    // Mix the set identifier's domain separator into the alpha derivation.
    let domain_sep = hash_many(&[
        BabyBear::new(0x64726567), // "dreg"
        BabyBear::new(0x672D6E6D), // "g-nm" (non-membership)
        set_id.domain_sep,
        BabyBear::new(set_elements.len() as u32),
    ]);

    // Hash domain separator with set elements for binding.
    let binding = if set_elements.is_empty() {
        domain_sep
    } else {
        let mut elems = vec![domain_sep];
        let sample_count = set_elements.len().min(16);
        for &h in &set_elements[..sample_count] {
            elems.push(h);
        }
        hash_many(&elems)
    };

    // Generate 4 independent BabyBear elements for the extension field challenge.
    let h0 = binding;
    let h1 = hash_many(&[h0, BabyBear::new(1)]);
    let h2 = hash_many(&[h0, BabyBear::new(2)]);
    let h3 = hash_many(&[h0, BabyBear::new(3)]);

    ExtElem([h0, h1, h2, h3])
}

/// Compute the accumulator value for a set (delegates to accumulator_types).
pub fn compute_set_accumulator(set_elements: &[BabyBear], alpha: ExtElem) -> ExtElem {
    compute_accumulator(set_elements, alpha)
}

// ============================================================================
// Integration with derivation system
// ============================================================================

// ============================================================================
// Tests
// ============================================================================
