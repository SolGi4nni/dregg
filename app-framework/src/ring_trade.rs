//! Ring trade participation trait for dregg apps.
//!
//! Wraps `dregg_intent::solver` types. Apps that want to contribute liquidity
//! to multi-party ring trades implement [`RingTradeParticipant`] and register
//! with a solver coordinator. The solver calls `exchange_offers` to enumerate
//! what the app currently offers, then calls `settle_leg` / `rollback_leg` for
//! the legs it assigns to this app in an atomic settlement round.
//!
//! # Usage
//!
//! ```ignore
//! use dregg_app_framework::ring_trade::{RingTradeParticipant, ExchangeSpec, Settlement};
//!
//! impl RingTradeParticipant for MyAMM {
//!     type Error = MyError;
//!     fn exchange_offers(&self) -> Vec<ExchangeSpec> { self.pool_offers() }
//!     fn settle_leg(&mut self, s: &Settlement) -> Result<(), MyError> { self.execute(s) }
//!     fn rollback_leg(&mut self, s: &Settlement) -> Result<(), MyError> { self.undo(s) }
//! }
//! ```

pub use dregg_intent::solver::{ExchangeSpec, IntentNode, RingSolver, RingTrade, Settlement};

/// An opaque identifier for a single leg in a ring trade.
///
/// Derived from the settlement's `from`/`to` commitments and asset. Apps can
/// use this to correlate `settle_leg` and `rollback_leg` calls.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LegId(pub [u8; 32]);

impl LegId {
    /// Derive a `LegId` from a `Settlement`'s fields.
    pub fn from_settlement(s: &Settlement) -> Self {
        let mut hasher = blake3::Hasher::new();
        hasher.update(&s.from.0);
        hasher.update(&s.to.0);
        hasher.update(&s.asset);
        hasher.update(&s.amount.to_le_bytes());
        LegId(*hasher.finalize().as_bytes())
    }
}

/// Apps implement this trait to register as a participant in ring trades.
///
/// The framework calls these methods during atomic settlement. All legs in a
/// ring must succeed; if any `settle_leg` fails the coordinator calls
/// `rollback_leg` on each previously-settled app in reverse order.
pub trait RingTradeParticipant {
    /// Error type returned by settle/rollback operations.
    type Error: std::fmt::Debug;

    /// Return the exchange offers this app currently has available.
    ///
    /// Called by the solver coordinator before each solve round to populate the
    /// intent graph. The returned specs should reflect the app's current state
    /// (pool depths, order book, etc.).
    fn exchange_offers(&self) -> Vec<ExchangeSpec>;

    /// Settle a single leg of a ring trade involving this app.
    ///
    /// Called atomically as part of multi-app settlement. If this returns `Ok`,
    /// the leg is committed. If it returns `Err`, the coordinator calls
    /// `rollback_leg` on all previously settled apps.
    fn settle_leg(&mut self, settlement: &Settlement) -> Result<(), Self::Error>;

    /// Roll back a previously settled leg if a peer in the ring fails.
    ///
    /// Must be idempotent — it may be called even if the original `settle_leg`
    /// did not fully succeed (e.g., partial state change before error).
    fn rollback_leg(&mut self, settlement: &Settlement) -> Result<(), Self::Error>;
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_intent::CommitmentId;

    #[test]
    fn leg_id_is_deterministic() {
        let s = Settlement {
            from: CommitmentId([1u8; 32]),
            to: CommitmentId([2u8; 32]),
            asset: [3u8; 32],
            amount: 42,
        };
        let id1 = LegId::from_settlement(&s);
        let id2 = LegId::from_settlement(&s);
        assert_eq!(id1, id2);
    }
}
