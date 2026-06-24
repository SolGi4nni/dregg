//! `AdmissionReason` — the legible "why" of a turn the verified executor REFUSED at admission.
//!
//! The verified executor's admission predicate (`Dregg2.Exec.Admission.admissible`) is a fold of
//! eight named, theorem-backed gates; the FIRST failing gate's identity is the refusal reason. The
//! Lean side names it (`Dregg2.Exec.AdmissionReason.AdmissionReason`) and tags each case `0..11`
//! for the wire (`reasonCode`); this is the `dregg-turn`-local PURE mirror, so the FFI-free `turn`
//! crate can name the reason in its error surface without linking the Lean archive.
//!
//! The Lean keystone `admissionReason_eq_admitted_iff` proves the reason is FAITHFUL: it reports
//! [`AdmissionReason::Admitted`] iff the turn genuinely passes admission (every gate), and any
//! reject reason iff it genuinely does not — so the reason can never lie about admission. The wire
//! corollary `reasonCode_eq_zero_iff_admits` is the same fact at the byte boundary (code `0` iff
//! admitted), which `dregg-lean-ffi::AdmissionReason::from_code` decodes.

use serde::{Deserialize, Serialize};

/// The theorem-backed reason a turn was refused at admission. One variant per gate of the verified
/// `admissible` predicate, in its `&&` short-circuit order, plus [`Admitted`](Self::Admitted).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AdmissionReason {
    /// Code 0: every admission gate passed — the turn was genuinely admitted.
    Admitted,
    /// Code 1: the call-forest is empty — there is nothing to execute.
    EmptyForest,
    /// Code 2: the agent cell is not a member account of this ledger.
    NoSuchAgent,
    /// Code 3: the agent cell is a member but not lifecycle-live (Destroyed/Sealed).
    DeadAgent,
    /// Code 4: the turn's `valid_until` has passed relative to the host clock.
    Expired,
    /// Code 5: the turn's nonce does not match the agent's stored nonce (replay / stale).
    NonceMismatch,
    /// Code 6: the declared fee is negative.
    NegativeFee,
    /// Code 7: the agent cannot cover the fee from its balance.
    Underfunded,
    /// Code 8: the agent cell is in the migration freeze-set.
    AgentFrozen,
    /// Code 9: some cell the forest writes is frozen.
    WriteSetFrozen,
    /// Code 10: the turn's `previous_receipt_hash` ≠ the agent's stored receipt-chain head.
    ChainHeadMismatch,
    /// Code 11: the fee exceeds the silo's Stingray budget slice.
    OverBudget,
}

impl AdmissionReason {
    /// Decode from the wire code (`Dregg2.Exec.AdmissionReason.reasonCode`). `None` for an
    /// out-of-range code (fail-closed — never silently mis-name a gate).
    pub fn from_code(code: u64) -> Option<Self> {
        Some(match code {
            0 => Self::Admitted,
            1 => Self::EmptyForest,
            2 => Self::NoSuchAgent,
            3 => Self::DeadAgent,
            4 => Self::Expired,
            5 => Self::NonceMismatch,
            6 => Self::NegativeFee,
            7 => Self::Underfunded,
            8 => Self::AgentFrozen,
            9 => Self::WriteSetFrozen,
            10 => Self::ChainHeadMismatch,
            11 => Self::OverBudget,
            _ => return None,
        })
    }

    /// The stable wire tag of this reason (the inverse of [`from_code`](Self::from_code)).
    pub fn code(self) -> u64 {
        match self {
            Self::Admitted => 0,
            Self::EmptyForest => 1,
            Self::NoSuchAgent => 2,
            Self::DeadAgent => 3,
            Self::Expired => 4,
            Self::NonceMismatch => 5,
            Self::NegativeFee => 6,
            Self::Underfunded => 7,
            Self::AgentFrozen => 8,
            Self::WriteSetFrozen => 9,
            Self::ChainHeadMismatch => 10,
            Self::OverBudget => 11,
        }
    }

    /// `true` iff this is [`Admitted`](Self::Admitted) — the turn passed every admission gate. By
    /// the Lean keystone this is equivalent to `admissible = true`.
    pub fn is_admitted(self) -> bool {
        matches!(self, Self::Admitted)
    }

    /// A human-readable, stranger-facing explanation of the refusal — the legible "why" that
    /// replaces a bare `false`.
    pub fn explain(self) -> &'static str {
        match self {
            Self::Admitted => "the turn passed every admission gate",
            Self::EmptyForest => "refused: the turn carries no actions (an empty call-forest)",
            Self::NoSuchAgent => "refused: the agent cell is not an account on this ledger",
            Self::DeadAgent => {
                "refused: the agent cell is destroyed or sealed and cannot author a turn"
            }
            Self::Expired => "refused: the turn's valid-until deadline has already passed",
            Self::NonceMismatch => {
                "refused: the turn's nonce does not match the agent's next nonce (replay or stale turn)"
            }
            Self::NegativeFee => "refused: the declared fee is negative",
            Self::Underfunded => "refused: the agent's balance cannot cover the declared fee",
            Self::AgentFrozen => {
                "refused: the agent cell is frozen for migration; no turns may execute against it"
            }
            Self::WriteSetFrozen => {
                "refused: a cell this turn would write is frozen for migration"
            }
            Self::ChainHeadMismatch => {
                "refused: the turn's previous-receipt-hash does not match the agent's receipt-chain head"
            }
            Self::OverBudget => "refused: the fee exceeds this silo's remaining budget slice",
        }
    }
}

impl core::fmt::Display for AdmissionReason {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.explain())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The wire tags round-trip and match the Lean `reasonCode` (`0..11`, `&&`-order). This is the
    /// Rust side of the wire contract proved faithful in Lean (`reasonCode_eq_zero_iff_admits`).
    #[test]
    fn code_roundtrips_and_matches_lean_order() {
        for code in 0..=11u64 {
            let r = AdmissionReason::from_code(code).expect("code in range decodes");
            assert_eq!(r.code(), code, "code {code} round-trips");
        }
        // out-of-range is fail-closed
        assert_eq!(AdmissionReason::from_code(12), None);
        // code 0 is the unique admitted tag (the wire-faithfulness anchor)
        assert!(AdmissionReason::from_code(0).unwrap().is_admitted());
        for code in 1..=11u64 {
            assert!(
                !AdmissionReason::from_code(code).unwrap().is_admitted(),
                "code {code} is a reject reason, not admitted"
            );
        }
    }

    /// Every reject reason renders a distinct, non-empty, stranger-facing string (no silent
    /// `false`).
    #[test]
    fn every_reason_explains() {
        let all = [
            AdmissionReason::EmptyForest,
            AdmissionReason::NoSuchAgent,
            AdmissionReason::DeadAgent,
            AdmissionReason::Expired,
            AdmissionReason::NonceMismatch,
            AdmissionReason::NegativeFee,
            AdmissionReason::Underfunded,
            AdmissionReason::AgentFrozen,
            AdmissionReason::WriteSetFrozen,
            AdmissionReason::ChainHeadMismatch,
            AdmissionReason::OverBudget,
        ];
        for r in all {
            assert!(r.explain().starts_with("refused:"), "{r:?} explains a refusal");
            assert_eq!(r.to_string(), r.explain());
        }
        assert!(!AdmissionReason::Admitted.explain().starts_with("refused:"));
    }
}
