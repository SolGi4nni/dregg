//! The privacy tier lattice (`DREGGFI-PRIVACY-TIERS.md` §1, §3).
//!
//! Three deliberate points on the privacy ↔ generality ↔ cost frontier, each a
//! privacy *posture* over ONE verified soundness kernel:
//!
//! - **`Dark`** (Tier 0) — no viewer. Inputs stay encrypted; only the public
//!   result opens. Admissible iff FHE-tractable (`§3`: public matrices,
//!   data-independent iteration, one packable prox, inside the FHE envelope).
//! - **`Shielded`** (Tier 1) — private-from-the-world; the solver/prover sees
//!   plaintext. Admissible iff STARK-tractable (a bounded oblivious convex
//!   circuit the hiding STARK carries).
//! - **`Open`** (Tier 2) — public; fully general. Admissible iff expressible to
//!   the general matcher at all.
//!
//! The ordering is by PRIVACY: `Dark < Shielded < Open` (`Dark` is most
//! private). Admissibility is monotone the easy way — **Tier-0-admissible ⇒
//! Tier-1-admissible ⇒ Tier-2-admissible** — because more visibility only ever
//! *adds* expressible mechanisms. So "the most private tier a product can
//! honestly run at" is the **minimum** admissible tier in this order, and the
//! compiler computes exactly that (`compile::most_private_admissible`).

use serde::Serialize;
use std::fmt;

/// A privacy posture. `Ord` is the privacy order: `Dark < Shielded < Open`, so
/// `min` over an admissible set is the MOST-PRIVATE admissible tier.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Serialize)]
pub enum Tier {
    /// Tier 0 — DARK. No viewer; FHE, encrypted inputs, only the result opens.
    Dark,
    /// Tier 1 — SHIELDED. Private-from-the-world; the solver sees plaintext.
    Shielded,
    /// Tier 2 — OPEN. Public, fully general.
    Open,
}

impl Tier {
    /// The three tiers in privacy order (most private first) — the search order
    /// `most_private_admissible` walks.
    pub const ALL: [Tier; 3] = [Tier::Dark, Tier::Shielded, Tier::Open];

    /// The human-facing label (`DREGGFI-PRIVACY-TIERS.md` §1).
    pub fn label(self) -> &'static str {
        match self {
            Tier::Dark => "Tier 0 DARK (no viewer)",
            Tier::Shielded => "Tier 1 SHIELDED (private-from-the-world, solver sees)",
            Tier::Open => "Tier 2 OPEN (public, fair-by-proof)",
        }
    }

    /// A short name for error messages (`Tier 0/Dark`), avoiding the awkward
    /// long label mid-sentence.
    pub fn short(self) -> &'static str {
        match self {
            Tier::Dark => "Tier 0/Dark",
            Tier::Shielded => "Tier 1/Shielded",
            Tier::Open => "Tier 2/Open",
        }
    }

    /// The tractability class a product must land in to be admissible here.
    pub fn tractability(self) -> &'static str {
        match self {
            Tier::Dark => {
                "FHE-tractable (public matrices, aggregation/affine core, bounded FHE envelope)"
            }
            Tier::Shielded => {
                "STARK-tractable (bounded oblivious convex circuit; solver sees plaintext)"
            }
            Tier::Open => "public-general (any intent the matcher expresses)",
        }
    }

    /// `true` iff `self` is at least as private as `other` (i.e. `self ≤ other`
    /// in the privacy order). Reporting `self` when the author claimed `other`
    /// is honest exactly when this holds.
    pub fn at_least_as_private_as(self, other: Tier) -> bool {
        self <= other
    }
}

impl fmt::Display for Tier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.label())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn privacy_order_is_dark_shielded_open() {
        assert!(Tier::Dark < Tier::Shielded);
        assert!(Tier::Shielded < Tier::Open);
        // most-private = min
        let admissible = [Tier::Shielded, Tier::Open];
        assert_eq!(admissible.iter().copied().min().unwrap(), Tier::Shielded);
    }

    #[test]
    fn at_least_as_private() {
        assert!(Tier::Dark.at_least_as_private_as(Tier::Shielded));
        assert!(Tier::Shielded.at_least_as_private_as(Tier::Shielded));
        assert!(!Tier::Open.at_least_as_private_as(Tier::Shielded));
    }
}
