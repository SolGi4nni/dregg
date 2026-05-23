//! Ring trade participation trait for pyana apps.
//!
//! Wraps `pyana_intent::solver` types. Apps that want to contribute liquidity
//! to multi-party ring trades implement [`RingTradeParticipant`] and register
//! with a solver coordinator. The solver calls `exchange_offers` to enumerate
//! what the app currently offers, then calls `settle_leg` / `rollback_leg` for
//! the legs it assigns to this app in an atomic settlement round.
//!
//! # Usage
//!
//! ```ignore
//! use pyana_app_framework::ring_trade::{RingTradeParticipant, ExchangeSpec, Settlement};
//!
//! impl RingTradeParticipant for MyAMM {
//!     type Error = MyError;
//!     fn exchange_offers(&self) -> Vec<ExchangeSpec> { self.pool_offers() }
//!     fn settle_leg(&mut self, s: &Settlement) -> Result<(), MyError> { self.execute(s) }
//!     fn rollback_leg(&mut self, s: &Settlement) -> Result<(), MyError> { self.undo(s) }
//! }
//! ```

pub use pyana_intent::solver::{ExchangeSpec, IntentNode, RingSolver, RingTrade, Settlement};

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
    use pyana_intent::CommitmentId;
    use pyana_intent::exchange::AssetId;

    struct DummyParticipant {
        offer: AssetId,
        want: AssetId,
        settled: Vec<Settlement>,
    }

    #[derive(Debug)]
    struct Never;

    impl RingTradeParticipant for DummyParticipant {
        type Error = Never;

        fn exchange_offers(&self) -> Vec<ExchangeSpec> {
            vec![ExchangeSpec {
                offer_asset: self.offer,
                offer_amount: 1000,
                want_asset: self.want,
                want_min_amount: 900,
                min_rate: None,
                max_rate: None,
            }]
        }

        fn settle_leg(&mut self, s: &Settlement) -> Result<(), Never> {
            self.settled.push(s.clone());
            Ok(())
        }

        fn rollback_leg(&mut self, _s: &Settlement) -> Result<(), Never> {
            self.settled.pop();
            Ok(())
        }
    }

    #[test]
    fn trait_wiring_compiles_and_works() {
        let mut p = DummyParticipant {
            offer: [0xAA; 32],
            want: [0xBB; 32],
            settled: Vec::new(),
        };

        let offers = p.exchange_offers();
        assert_eq!(offers.len(), 1);
        assert_eq!(offers[0].offer_amount, 1000);

        let s = Settlement {
            from: CommitmentId([0u8; 32]),
            to: CommitmentId([1u8; 32]),
            asset: [0xAA; 32],
            amount: 1000,
        };

        p.settle_leg(&s).unwrap();
        assert_eq!(p.settled.len(), 1);

        p.rollback_leg(&s).unwrap();
        assert_eq!(p.settled.len(), 0);
    }

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
