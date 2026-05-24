//! Solver bond escrow with slashing.
//!
//! Lane Intent-α landed the `SolverSubmission.bond` field but the bond
//! itself was a number-on-the-struct check only — no value was actually
//! transferred or held. Per SLOT-CAVEATS-DESIGN.md the production
//! shape is:
//!
//! ```text
//! cell: SolverEscrow
//!   slot[0] = bond_locked: u64                    (BoundedBy slot[1])
//!   slot[1] = bond_balance: u64                   (Monotonic)
//!   slot[2] = solver_id:    [u8; 32]
//!   slot[3] = batch_id:     u64
//! ```
//!
//! The `BoundedBy { index: 0, witness_index: 1 }` caveat on slot 0
//! enforces that `bond_locked <= bond_balance` at all times. A
//! fulfillment transition decrements `bond_locked` (releasing the
//! bond); a slash transition decrements both `bond_locked` AND
//! `bond_balance` (the bond is forfeited).
//!
//! This module ships the *escrow tracker* — the in-memory mirror of
//! the escrow cell. When the cell-program migration lands, the
//! tracker's API will swap to talk to the cell directly. For now it
//! lets the trustless engine actually hold bonds and slash them
//! during challenge-window resolutions.

use std::collections::HashMap;

use crate::IntentId;

/// Errors from the bond escrow.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BondError {
    /// The solver has insufficient balance to post the requested bond.
    InsufficientBalance { available: u64, requested: u64 },
    /// The bond is already posted for this (solver, batch).
    AlreadyPosted,
    /// No bond posted for this (solver, batch).
    NotPosted,
    /// The escrow's `BoundedBy { bond_locked <= bond_balance }` invariant
    /// would be violated. (Should not happen in normal flow.)
    BoundViolated { locked: u64, balance: u64 },
}

impl std::fmt::Display for BondError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InsufficientBalance {
                available,
                requested,
            } => write!(
                f,
                "insufficient bond balance: have {available}, need {requested}"
            ),
            Self::AlreadyPosted => write!(f, "bond already posted for this submission"),
            Self::NotPosted => write!(f, "no bond posted for this submission"),
            Self::BoundViolated { locked, balance } => write!(
                f,
                "BoundedBy violated: bond_locked={locked} > bond_balance={balance}"
            ),
        }
    }
}

impl std::error::Error for BondError {}

/// Key identifying a posted bond: (solver_id, batch_id).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BondKey {
    pub solver_id: [u8; 32],
    pub batch_id: u64,
}

/// A single solver's escrow account.
#[derive(Clone, Debug, Default)]
struct SolverAccount {
    /// Balance currently held by the escrow (slot[1]).
    bond_balance: u64,
    /// Currently locked against active submissions (slot[0]).
    /// Invariant: `bond_locked <= bond_balance`. This is the
    /// `BoundedBy { index: bond_locked, witness_index: bond_balance }`
    /// caveat — `BoundedBy` here meaning "this slot's value is bounded
    /// above by another slot's value", a la SLOT-CAVEATS-DESIGN.md.
    bond_locked: u64,
    /// Per-submission locks, so multi-batch solvers don't conflate
    /// bonds.
    locks: HashMap<u64, u64>, // batch_id -> amount locked
}

/// In-memory bond escrow.
///
/// Production cell-program migration: each solver's `SolverAccount`
/// becomes a `SolverEscrow` cell, the per-solver `bond_balance` /
/// `bond_locked` become slots, and `lock` / `release` / `slash`
/// become method calls that produce slot-update effects. The state
/// machine here is the same.
#[derive(Clone, Debug, Default)]
pub struct BondEscrow {
    accounts: HashMap<[u8; 32], SolverAccount>,
    /// Optional intent-side mapping: which IntentIds were paired with
    /// which solver+batch. Lets `slash_for_intent` find the bond.
    intent_bonds: HashMap<IntentId, BondKey>,
}

impl BondEscrow {
    /// Construct an empty escrow.
    pub fn new() -> Self {
        Self::default()
    }

    /// Deposit funds into a solver's escrow account (out-of-band,
    /// typically from a turn that transferred the value).
    pub fn deposit(&mut self, solver_id: &[u8; 32], amount: u64) {
        let acct = self.accounts.entry(*solver_id).or_default();
        acct.bond_balance = acct.bond_balance.saturating_add(amount);
    }

    /// Withdraw unencumbered funds. Fails if the requested amount
    /// exceeds `bond_balance - bond_locked`.
    pub fn withdraw(&mut self, solver_id: &[u8; 32], amount: u64) -> Result<(), BondError> {
        let acct = self.accounts.entry(*solver_id).or_default();
        let free = acct.bond_balance.saturating_sub(acct.bond_locked);
        if amount > free {
            return Err(BondError::InsufficientBalance {
                available: free,
                requested: amount,
            });
        }
        acct.bond_balance -= amount;
        Ok(())
    }

    /// Lock `amount` of the solver's balance against a submission.
    /// Returns `AlreadyPosted` if a bond is already locked for the
    /// same (solver, batch) — submissions are one-bond-per-pair.
    pub fn lock(
        &mut self,
        solver_id: &[u8; 32],
        batch_id: u64,
        amount: u64,
    ) -> Result<(), BondError> {
        let acct = self.accounts.entry(*solver_id).or_default();
        if acct.locks.contains_key(&batch_id) {
            return Err(BondError::AlreadyPosted);
        }
        let new_locked = acct.bond_locked.saturating_add(amount);
        if new_locked > acct.bond_balance {
            return Err(BondError::InsufficientBalance {
                available: acct.bond_balance.saturating_sub(acct.bond_locked),
                requested: amount,
            });
        }
        acct.locks.insert(batch_id, amount);
        acct.bond_locked = new_locked;
        Ok(())
    }

    /// Release a previously-locked bond (the solver won the auction
    /// uncontested, or finalized successfully). The amount returns
    /// to free balance.
    pub fn release(&mut self, solver_id: &[u8; 32], batch_id: u64) -> Result<u64, BondError> {
        let acct = self.accounts.entry(*solver_id).or_default();
        let amount = acct.locks.remove(&batch_id).ok_or(BondError::NotPosted)?;
        acct.bond_locked = acct.bond_locked.saturating_sub(amount);
        debug_assert!(
            acct.bond_locked <= acct.bond_balance,
            "BoundedBy invariant: locked={} balance={}",
            acct.bond_locked,
            acct.bond_balance
        );
        Ok(amount)
    }

    /// Slash a locked bond — the solver lost the challenge, or
    /// otherwise misbehaved. Bond is decremented from BOTH
    /// `bond_locked` and `bond_balance` (the funds are forfeited).
    /// Returns the slashed amount.
    pub fn slash(&mut self, solver_id: &[u8; 32], batch_id: u64) -> Result<u64, BondError> {
        let acct = self.accounts.entry(*solver_id).or_default();
        let amount = acct.locks.remove(&batch_id).ok_or(BondError::NotPosted)?;
        acct.bond_locked = acct.bond_locked.saturating_sub(amount);
        acct.bond_balance = acct.bond_balance.saturating_sub(amount);
        debug_assert!(
            acct.bond_locked <= acct.bond_balance,
            "BoundedBy invariant violated after slash"
        );
        Ok(amount)
    }

    /// Bind an intent to a solver+batch so a later
    /// [`Self::slash_for_intent`] can find the bond.
    pub fn bind_intent(&mut self, intent: IntentId, key: BondKey) {
        self.intent_bonds.insert(intent, key);
    }

    /// Slash the bond associated with an intent (used by the
    /// fulfillment-failure path: a solver whose ring includes
    /// this intent did not deliver).
    pub fn slash_for_intent(&mut self, intent: &IntentId) -> Result<u64, BondError> {
        let key = self
            .intent_bonds
            .remove(intent)
            .ok_or(BondError::NotPosted)?;
        self.slash(&key.solver_id, key.batch_id)
    }

    /// Free balance available to a solver.
    pub fn free_balance(&self, solver_id: &[u8; 32]) -> u64 {
        self.accounts
            .get(solver_id)
            .map(|a| a.bond_balance.saturating_sub(a.bond_locked))
            .unwrap_or(0)
    }

    /// Total balance (including locked).
    pub fn balance(&self, solver_id: &[u8; 32]) -> u64 {
        self.accounts
            .get(solver_id)
            .map(|a| a.bond_balance)
            .unwrap_or(0)
    }

    /// Currently locked amount for a solver.
    pub fn locked(&self, solver_id: &[u8; 32]) -> u64 {
        self.accounts
            .get(solver_id)
            .map(|a| a.bond_locked)
            .unwrap_or(0)
    }

    /// Currently locked for a specific (solver, batch) pair.
    pub fn locked_for(&self, key: &BondKey) -> u64 {
        self.accounts
            .get(&key.solver_id)
            .and_then(|a| a.locks.get(&key.batch_id))
            .copied()
            .unwrap_or(0)
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn solver() -> [u8; 32] {
        [0xAA; 32]
    }

    #[test]
    fn deposit_increases_balance() {
        let mut esc = BondEscrow::new();
        esc.deposit(&solver(), 1000);
        assert_eq!(esc.balance(&solver()), 1000);
        assert_eq!(esc.free_balance(&solver()), 1000);
    }

    #[test]
    fn lock_reduces_free_balance() {
        let mut esc = BondEscrow::new();
        esc.deposit(&solver(), 1000);
        esc.lock(&solver(), 1, 300).unwrap();
        assert_eq!(esc.balance(&solver()), 1000);
        assert_eq!(esc.locked(&solver()), 300);
        assert_eq!(esc.free_balance(&solver()), 700);
    }

    #[test]
    fn double_lock_same_batch_rejected() {
        let mut esc = BondEscrow::new();
        esc.deposit(&solver(), 1000);
        esc.lock(&solver(), 1, 300).unwrap();
        let err = esc.lock(&solver(), 1, 200).unwrap_err();
        assert_eq!(err, BondError::AlreadyPosted);
    }

    #[test]
    fn lock_two_batches_independently() {
        let mut esc = BondEscrow::new();
        esc.deposit(&solver(), 1000);
        esc.lock(&solver(), 1, 300).unwrap();
        esc.lock(&solver(), 2, 400).unwrap();
        assert_eq!(esc.locked(&solver()), 700);
        assert_eq!(esc.free_balance(&solver()), 300);
    }

    #[test]
    fn lock_overshoot_rejected() {
        let mut esc = BondEscrow::new();
        esc.deposit(&solver(), 500);
        let err = esc.lock(&solver(), 1, 1000).unwrap_err();
        assert!(matches!(err, BondError::InsufficientBalance { .. }));
    }

    #[test]
    fn release_returns_to_free() {
        let mut esc = BondEscrow::new();
        esc.deposit(&solver(), 1000);
        esc.lock(&solver(), 1, 300).unwrap();
        let amount = esc.release(&solver(), 1).unwrap();
        assert_eq!(amount, 300);
        assert_eq!(esc.locked(&solver()), 0);
        assert_eq!(esc.free_balance(&solver()), 1000);
    }

    #[test]
    fn slash_decrements_both_locked_and_balance() {
        let mut esc = BondEscrow::new();
        esc.deposit(&solver(), 1000);
        esc.lock(&solver(), 1, 300).unwrap();
        let amount = esc.slash(&solver(), 1).unwrap();
        assert_eq!(amount, 300);
        assert_eq!(esc.balance(&solver()), 700);
        assert_eq!(esc.locked(&solver()), 0);
        assert_eq!(esc.free_balance(&solver()), 700);
    }

    #[test]
    fn withdraw_takes_only_free_balance() {
        let mut esc = BondEscrow::new();
        esc.deposit(&solver(), 1000);
        esc.lock(&solver(), 1, 400).unwrap();
        // Free is 600; withdrawing 700 should fail.
        let err = esc.withdraw(&solver(), 700).unwrap_err();
        assert!(matches!(err, BondError::InsufficientBalance { .. }));
        // Withdrawing 600 should succeed.
        esc.withdraw(&solver(), 600).unwrap();
        assert_eq!(esc.balance(&solver()), 400);
        assert_eq!(esc.locked(&solver()), 400);
        assert_eq!(esc.free_balance(&solver()), 0);
    }

    #[test]
    fn release_unposted_returns_not_posted() {
        let mut esc = BondEscrow::new();
        esc.deposit(&solver(), 1000);
        let err = esc.release(&solver(), 99).unwrap_err();
        assert_eq!(err, BondError::NotPosted);
    }

    #[test]
    fn slash_for_intent_resolves_via_intent_binding() {
        let mut esc = BondEscrow::new();
        esc.deposit(&solver(), 1000);
        esc.lock(&solver(), 1, 200).unwrap();
        let intent_id = [0x77u8; 32];
        esc.bind_intent(
            intent_id,
            BondKey {
                solver_id: solver(),
                batch_id: 1,
            },
        );
        let slashed = esc.slash_for_intent(&intent_id).unwrap();
        assert_eq!(slashed, 200);
        assert_eq!(esc.balance(&solver()), 800);
    }
}
