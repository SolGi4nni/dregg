//! Canonical intent lifecycle state machine.
//!
//! Intent lifecycle in dregg flows through five states:
//!
//! ```text
//!   Pending ──submit──▶ Matched ──seal──▶ Sealed ──fulfill──▶ Fulfilled ──settle──▶ Settled
//!      │                  │                  │                    │
//!      │                  │                  │                    │
//!      └── Expired (timeout / GC, any state before Settled) ──────┘
//! ```
//!
//! ## Per SLOT-CAVEATS-DESIGN.md §`AllowedTransitions`
//!
//! When the intent pool migrates to a cell-program pattern (per
//! `STORAGE-AS-CELL-PROGRAMS.md`), the intent cell's `status` slot will
//! carry an `AllowedTransitions { allowed: Vec<(old_val, new_val)>,
//! slot_index }` caveat enforcing exactly the transitions enumerated by
//! [`ALLOWED_TRANSITIONS`] below. No application code will need to
//! re-check transitions — the executor's slot-caveat layer does so.
//!
//! This module ships the *schema* now (the const transition table and
//! the [`IntentLifecycleState`] enum). The cell-program migration is a
//! separate lane.
//!
//! ## Why an enum and not a string
//!
//! Slot values are 32-byte field elements. We encode each state as a
//! distinguishable `[u8; 32]` via [`IntentLifecycleState::as_slot_value`].
//! The encoding is stable (it's the BLAKE3-derive of the variant name
//! under a fixed domain) so receipts and slot caveats reference the
//! same bytes across runs.

use serde::{Deserialize, Serialize};

/// The lifecycle state of an intent in its containing pool / cell.
///
/// Encoded into a slot value via [`Self::as_slot_value`]; an
/// `AllowedTransitions` slot caveat enforces that the cell's `status`
/// slot only moves between adjacent states in [`ALLOWED_TRANSITIONS`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum IntentLifecycleState {
    /// Initial state. Intent posted, not yet matched by any candidate.
    Pending,
    /// A solver / matcher has surfaced a candidate counterparty; the
    /// intent is *committed* to a match but not yet sealed.
    Matched,
    /// The match has been sealed (lowered to a `SealedTurn`). The
    /// payment / settlement turn is queued for execution but has not
    /// yet committed.
    Sealed,
    /// The sealed turn committed; the fulfillment artifact (macaroon
    /// or STARK proof) has been delivered to the intent creator.
    Fulfilled,
    /// Final state. Payment / asset transfer has cleared on-chain
    /// (for ring settlements: the entire ring committed). The intent
    /// is closed.
    Settled,
    /// Terminal: the intent expired or was withdrawn before fulfillment.
    Expired,
}

impl IntentLifecycleState {
    /// The canonical 32-byte slot encoding for this state.
    ///
    /// The encoding is BLAKE3-derive("dregg-intent-state-v1", &[byte]).
    /// The byte is the variant index. The derivation gives every state
    /// a high-entropy value distinguishable from "uninitialized
    /// zeroed" and from arbitrary attacker-chosen values.
    pub fn as_slot_value(self) -> [u8; 32] {
        let idx: u8 = match self {
            Self::Pending => 0x00,
            Self::Matched => 0x01,
            Self::Sealed => 0x02,
            Self::Fulfilled => 0x03,
            Self::Settled => 0x04,
            Self::Expired => 0xFF,
        };
        blake3::derive_key("dregg-intent-state-v1", &[idx])
    }

    /// Recover a state from its slot encoding. Returns `None` if the
    /// bytes don't match any known state — typically meaning the slot
    /// has been written by something other than the canonical
    /// transition path.
    pub fn from_slot_value(bytes: &[u8; 32]) -> Option<Self> {
        for st in [
            Self::Pending,
            Self::Matched,
            Self::Sealed,
            Self::Fulfilled,
            Self::Settled,
            Self::Expired,
        ] {
            if st.as_slot_value() == *bytes {
                return Some(st);
            }
        }
        None
    }

    /// Whether this is a terminal state (no further transitions).
    pub fn is_terminal(self) -> bool {
        matches!(self, Self::Settled | Self::Expired)
    }
}

/// The canonical list of allowed (from, to) transitions.
///
/// This is the schema an `AllowedTransitions` slot caveat would carry
/// for the intent cell's `status` slot. Listed explicitly so reviewers
/// can audit at a glance.
///
/// Order: each tuple is `(from, to)`. Every transition both:
/// 1. Is structurally valid (the destination state's invariants are
///    achievable from the source's invariants).
/// 2. Is *unidirectional* — no transition rolls a state back. A
///    Fulfilled intent does not return to Matched.
pub const ALLOWED_TRANSITIONS: &[(IntentLifecycleState, IntentLifecycleState)] = &[
    // Normal flow.
    (IntentLifecycleState::Pending, IntentLifecycleState::Matched),
    (IntentLifecycleState::Matched, IntentLifecycleState::Sealed),
    (
        IntentLifecycleState::Sealed,
        IntentLifecycleState::Fulfilled,
    ),
    (
        IntentLifecycleState::Fulfilled,
        IntentLifecycleState::Settled,
    ),
    // Withdrawal / expiry: any non-settled state can transition to
    // Expired. Once Settled, the intent is closed for good.
    (IntentLifecycleState::Pending, IntentLifecycleState::Expired),
    (IntentLifecycleState::Matched, IntentLifecycleState::Expired),
    (IntentLifecycleState::Sealed, IntentLifecycleState::Expired),
    (
        IntentLifecycleState::Fulfilled,
        IntentLifecycleState::Expired,
    ),
];

/// Check whether a `(from, to)` transition is allowed by the canonical
/// schema. Cell-program migrations will move this enforcement into the
/// slot-caveat layer; today it serves as the authoritative oracle for
/// application-level callers.
pub fn is_allowed_transition(from: IntentLifecycleState, to: IntentLifecycleState) -> bool {
    ALLOWED_TRANSITIONS
        .iter()
        .any(|(f, t)| *f == from && *t == to)
}

/// The slot-index convention for the intent cell's `status` slot.
///
/// Slot 0 is reserved for the canonical lifecycle status. Other slots
/// (per the cell-program design) hold the intent body, bond amounts,
/// match metadata, etc.
pub const STATUS_SLOT_INDEX: u8 = 0;

/// Build an `AllowedTransitions` schema description that a future cell-
/// program slot caveat will consume. Returned as a `Vec<([u8;32],
/// [u8;32])>` — the slot-encoding pair for each transition.
///
/// This is the bridge between this module's enum world and the slot-
/// caveat's byte-level world. When the cell-program migration lands,
/// this is what gets fed into `StateConstraint::AllowedTransitions`.
pub fn allowed_transitions_as_slot_pairs() -> Vec<([u8; 32], [u8; 32])> {
    ALLOWED_TRANSITIONS
        .iter()
        .map(|(f, t)| (f.as_slot_value(), t.as_slot_value()))
        .collect()
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn states_have_unique_slot_values() {
        let states = [
            IntentLifecycleState::Pending,
            IntentLifecycleState::Matched,
            IntentLifecycleState::Sealed,
            IntentLifecycleState::Fulfilled,
            IntentLifecycleState::Settled,
            IntentLifecycleState::Expired,
        ];
        let values: Vec<[u8; 32]> = states.iter().map(|s| s.as_slot_value()).collect();
        for i in 0..values.len() {
            for j in (i + 1)..values.len() {
                assert_ne!(
                    values[i], values[j],
                    "states {i} and {j} produced the same slot value"
                );
            }
        }
    }

    #[test]
    fn roundtrip_slot_value() {
        for st in [
            IntentLifecycleState::Pending,
            IntentLifecycleState::Matched,
            IntentLifecycleState::Sealed,
            IntentLifecycleState::Fulfilled,
            IntentLifecycleState::Settled,
            IntentLifecycleState::Expired,
        ] {
            let bytes = st.as_slot_value();
            assert_eq!(IntentLifecycleState::from_slot_value(&bytes), Some(st));
        }
    }

    #[test]
    fn unknown_slot_bytes_decode_to_none() {
        assert_eq!(IntentLifecycleState::from_slot_value(&[0u8; 32]), None);
        assert_eq!(IntentLifecycleState::from_slot_value(&[0xCC; 32]), None);
    }

    #[test]
    fn normal_flow_transitions_allowed() {
        use IntentLifecycleState::*;
        assert!(is_allowed_transition(Pending, Matched));
        assert!(is_allowed_transition(Matched, Sealed));
        assert!(is_allowed_transition(Sealed, Fulfilled));
        assert!(is_allowed_transition(Fulfilled, Settled));
    }

    #[test]
    fn expiry_from_nonterminal_states_allowed() {
        use IntentLifecycleState::*;
        assert!(is_allowed_transition(Pending, Expired));
        assert!(is_allowed_transition(Matched, Expired));
        assert!(is_allowed_transition(Sealed, Expired));
        assert!(is_allowed_transition(Fulfilled, Expired));
    }

    #[test]
    fn rollbacks_rejected() {
        use IntentLifecycleState::*;
        // Settled is terminal; nothing goes back.
        assert!(!is_allowed_transition(Settled, Pending));
        assert!(!is_allowed_transition(Settled, Matched));
        assert!(!is_allowed_transition(Settled, Sealed));
        assert!(!is_allowed_transition(Settled, Fulfilled));
        assert!(!is_allowed_transition(Settled, Expired));
        // Fulfilled doesn't roll back to Sealed.
        assert!(!is_allowed_transition(Fulfilled, Sealed));
        // Pending doesn't skip directly to Sealed.
        assert!(!is_allowed_transition(Pending, Sealed));
    }

    #[test]
    fn settled_is_terminal() {
        assert!(IntentLifecycleState::Settled.is_terminal());
        assert!(IntentLifecycleState::Expired.is_terminal());
        assert!(!IntentLifecycleState::Pending.is_terminal());
        assert!(!IntentLifecycleState::Matched.is_terminal());
        assert!(!IntentLifecycleState::Sealed.is_terminal());
        assert!(!IntentLifecycleState::Fulfilled.is_terminal());
    }

    #[test]
    fn slot_pairs_count_matches_table() {
        let pairs = allowed_transitions_as_slot_pairs();
        assert_eq!(pairs.len(), ALLOWED_TRANSITIONS.len());
        // Each pair's bytes must roundtrip to the corresponding enum.
        for (i, (from_bytes, to_bytes)) in pairs.iter().enumerate() {
            let (from_enum, to_enum) = ALLOWED_TRANSITIONS[i];
            assert_eq!(
                IntentLifecycleState::from_slot_value(from_bytes),
                Some(from_enum)
            );
            assert_eq!(
                IntentLifecycleState::from_slot_value(to_bytes),
                Some(to_enum)
            );
        }
    }
}
