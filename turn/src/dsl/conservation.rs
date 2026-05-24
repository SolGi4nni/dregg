//! Derive an action's `balance_change` from its emitted effects.
//!
//! Per DESIGN-dsl.md §5: rather than the user writing
//! `.balance_change(delta)` on the builder (and getting it wrong, as the
//! gallery audit found), the framework computes the delta from the
//! `Transfer` / `NoteSpend` / `NoteCreate` / `CreateEscrow` effects
//! emitted by the action, summed from the perspective of the caller.

use pyana_cell::CellId;

use crate::action::Effect;

/// Compute the net balance change for `target` (the action caller) implied
/// by `effects`. Uses checked arithmetic — saturates at `i64::MAX` / `i64::MIN`
/// to avoid panics when conservation is grossly violated (the executor will
/// reject those anyway).
pub fn derive_balance_change(target: CellId, effects: &[Effect]) -> i64 {
    let mut delta: i64 = 0;
    for e in effects {
        let contrib: i64 = match e {
            Effect::Transfer { from, to, amount } => {
                let mut c: i64 = 0;
                if *from == target {
                    c = c.saturating_sub(*amount as i64);
                }
                if *to == target {
                    c = c.saturating_add(*amount as i64);
                }
                c
            }
            Effect::NoteSpend { value, .. } => -(*value as i64),
            Effect::NoteCreate { value, .. } => *value as i64,
            Effect::CreateEscrow { cell, amount, .. } if *cell == target => {
                -(*amount as i64)
            }
            Effect::CreateCommittedEscrow { amount, .. } => -(*amount as i64),
            // ReleaseEscrow / RefundEscrow / Release*Committed: the executor
            // moves the funds; we don't double-count here. The recipient's
            // action separately reflects the credit.
            _ => 0,
        };
        delta = delta.saturating_add(contrib);
    }
    delta
}

#[cfg(test)]
mod tests {
    use super::*;
    use pyana_cell::CellId;

    fn cell(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    #[test]
    fn no_effects_zero_delta() {
        let c = cell(1);
        assert_eq!(derive_balance_change(c, &[]), 0);
    }

    #[test]
    fn transfer_out_is_negative() {
        let a = cell(1);
        let b = cell(2);
        let e = Effect::Transfer {
            from: a,
            to: b,
            amount: 100,
        };
        assert_eq!(derive_balance_change(a, &[e]), -100);
    }

    #[test]
    fn transfer_in_is_positive() {
        let a = cell(1);
        let b = cell(2);
        let e = Effect::Transfer {
            from: a,
            to: b,
            amount: 100,
        };
        assert_eq!(derive_balance_change(b, &[e]), 100);
    }

    #[test]
    fn self_transfer_is_zero() {
        let a = cell(1);
        let e = Effect::Transfer {
            from: a,
            to: a,
            amount: 100,
        };
        assert_eq!(derive_balance_change(a, &[e]), 0);
    }
}
