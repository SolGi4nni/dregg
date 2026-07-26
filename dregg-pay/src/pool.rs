//! [`SwapPool`] — WHO paid into the `$DREGG` pile, and what that stake is worth as a vote.
//!
//! # The gap this closes
//!
//! [`Treasury`] carries the pile as ONE aggregate number
//! ([`Treasury::dregg_balance`]): it knows how much `$DREGG` accumulated and NOTHING
//! about who paid it in. [`CreditLedger`](crate::ledger::CreditLedger) is per-user but
//! records *run credits*, a spendable balance that is debited away by play — it is not a
//! record of contribution. So a vote whose weight is a function of a voter's stake in the
//! pile had no ledger to read. This module is that ledger.
//!
//! # The weight is QUADRATIC and INTEGER-EXACT
//!
//! ```text
//! weight(contributor) = isqrt(atomic $DREGG that contributor paid into the pool)
//! ```
//!
//! [`quadratic_weight`] is [`u64::isqrt`] — the exact integer square root (the unique `w`
//! with `w² ≤ x < (w+1)²`). Every number on this path is `u64`/`u128`; there is no float
//! anywhere in the weight or in the value accounting, so the weight is a deterministic
//! function of the ledger and two nodes computing it cannot disagree.
//!
//! Quadratic means paying 4× buys 2× the vote: a contributor with 100× another's stake
//! votes with 10× the weight, not 100×. A contributor who paid NOTHING has
//! `isqrt(0) = 0` and is refused outright — zero weight is never a ballot
//! ([`collective_choice::VoteError::ZeroWeight`] is the engine's own floor beneath this
//! one).
//!
//! # The pool is PINNED, and retired exactly once
//!
//! [`SwapPool::snapshot`] freezes the current epoch's per-contributor ledger into a
//! [`PoolSnapshot`]. A proposal votes over THAT — so a contribution made after the
//! proposal opens cannot buy weight in a vote already in flight, and the amount the
//! proposal swaps is fixed at propose time. The snapshot's entries are private: it can
//! only be produced by [`SwapPool::snapshot`], never assembled by a caller with invented
//! contributions (the same tooth [`SwapAuthorization`](crate::swap::SwapAuthorization)
//! uses for its signature).
//!
//! [`SwapPool::close`] retires a swapped pool: it subtracts exactly the snapshot's
//! per-contributor amounts (contributions that arrived AFTER the snapshot survive into
//! the next pool) and bumps the epoch. Closing a snapshot whose epoch is not current is
//! [`PoolError::StaleSnapshot`] — fail closed, so one passed vote cannot retire the
//! ledger twice.
//!
//! # Contributor identity
//!
//! A contributor is keyed by their [`DepositAddress`] — the per-user HD-derived ed25519
//! public key the payment actually landed on, carried on every
//! [`PaymentReceived`]. It is already this crate's per-user identity and it is already a
//! 32-byte key, so it is directly the voter identity the vote engine takes. This inherits
//! `dregg-pay`'s custodial trust model unchanged (the operator derives the address and
//! mediates the ballot); it is not a claim that the contributor signed anything. The
//! non-custodial upgrade is the
//! [`OwnerBinding`](dregg_governance::holding_weight::OwnerBinding) shape — a signature
//! by the holder's own wallet key over the voter identity — and is NOT built here.

use std::collections::{BTreeMap, HashSet};
use std::sync::Mutex;

use crate::config::{Asset, DepositAddress, UserId};
use crate::treasury::{Treasury, TreasuryStore};
use crate::watcher::{PaymentReceived, PaymentRef};

/// **The quadratic vote weight** of a contribution: the exact integer square root of the
/// atomic `$DREGG` paid in.
///
/// `isqrt` is the unique `w` with `w² ≤ x < (w+1)²` — integer-exact, no float, no
/// rounding policy to disagree about. `quadratic_weight(0) == 0`, which is what makes a
/// non-contributor's ballot a refusal rather than a silent zero-weight vote.
pub fn quadratic_weight(contributed_atomic: u64) -> u64 {
    contributed_atomic.isqrt()
}

/// What recording a payment did. Every variant is total: nothing partially applies.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ContributionOutcome {
    /// A `$DREGG` payment: credited to the treasury pile AND attributed to the payer's
    /// pool share.
    Contributed {
        /// The contributor's cumulative atomic `$DREGG` in the current pool.
        contributed_total: u64,
        /// The pool's cumulative atomic `$DREGG` across all contributors.
        pool_total: u64,
        /// The contributor's quadratic weight at this new total.
        weight: u64,
    },
    /// A USDC payment: credited to the treasury FUEL tank and attributed to nobody. USDC
    /// is not the pile, so it buys no weight in a pile swap — by construction, not by
    /// omission.
    FuelNotPool,
    /// This payment reference was already processed. Nothing changed — not the treasury,
    /// not the pool. (The pool's dedup set gates BOTH sides, so a re-observed payment can
    /// never double the pile *or* double a contributor's weight.)
    AlreadyRecorded,
    /// The contribution would overflow the `u64` contribution or pool total. REFUSED:
    /// nothing changed and the reference is deliberately left UNprocessed so an operator
    /// can resolve it. Never saturated — a saturating total would silently flatten two
    /// different whales onto one weight.
    Overflow,
}

/// Why a pool operation was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PoolError {
    /// The snapshot is not of the pool's CURRENT epoch — it was already retired by an
    /// earlier [`SwapPool::close`], or it belongs to another pool. Fail closed: a pool is
    /// retired exactly once, so one passed vote cannot draw the ledger down twice.
    StaleSnapshot {
        /// The epoch the snapshot was taken in.
        snapshot_epoch: u64,
        /// The pool's current epoch.
        pool_epoch: u64,
    },
}

impl std::fmt::Display for PoolError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PoolError::StaleSnapshot {
                snapshot_epoch,
                pool_epoch,
            } => write!(
                f,
                "pool snapshot is from epoch {snapshot_epoch}, the pool is at epoch {pool_epoch} — already retired"
            ),
        }
    }
}

impl std::error::Error for PoolError {}

/// A FROZEN per-contributor picture of the pool at one moment — the object a swap
/// proposal is pinned to.
///
/// It fixes both halves of the proposal at propose time: the electorate-and-weights (so
/// buying `$DREGG` after seeing the vote buys no influence over it) and the amount (so
/// "the whole pool" means one definite number). `entries` is private and only
/// [`SwapPool::snapshot`] constructs one — a caller cannot assemble a snapshot with
/// contributions nobody made.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoolSnapshot {
    /// The pool epoch this snapshot was taken in. [`SwapPool::close`] accepts only a
    /// snapshot of the pool's current epoch.
    epoch: u64,
    /// Total atomic `$DREGG` in the pool at snapshot time — the ALL-OR-NOTHING amount a
    /// proposal over this snapshot swaps.
    total: u64,
    /// Per-contributor atomic `$DREGG`. Private: a snapshot is minted by
    /// [`SwapPool::snapshot`] alone.
    entries: BTreeMap<DepositAddress, u64>,
    /// The display name behind each contributor address, carried for receipts.
    users: BTreeMap<DepositAddress, UserId>,
}

impl PoolSnapshot {
    /// The pool epoch this snapshot froze.
    pub fn epoch(&self) -> u64 {
        self.epoch
    }

    /// The total atomic `$DREGG` in the pool — the ALL-OR-NOTHING swap amount.
    pub fn total(&self) -> u64 {
        self.total
    }

    /// How many distinct contributors the pool has.
    pub fn contributor_count(&self) -> usize {
        self.entries.len()
    }

    /// What `who` contributed to this pool (0 if they contributed nothing).
    pub fn contributed(&self, who: &DepositAddress) -> u64 {
        self.entries.get(who).copied().unwrap_or(0)
    }

    /// **`who`'s quadratic vote weight in this pool** — `isqrt(contributed)`. A
    /// non-contributor is `0`, which every caller here treats as a refusal, not a vote.
    pub fn weight(&self, who: &DepositAddress) -> u64 {
        quadratic_weight(self.contributed(who))
    }

    /// The [`UserId`] behind a contributor address, for receipts.
    pub fn user(&self, who: &DepositAddress) -> Option<&UserId> {
        self.users.get(who)
    }

    /// Every `(contributor, contributed, weight)` in the pool, in address order.
    pub fn contributors(&self) -> Vec<(DepositAddress, u64, u64)> {
        self.entries
            .iter()
            .map(|(a, &c)| (*a, c, quadratic_weight(c)))
            .collect()
    }

    /// The electorate: every contributor's address as a 32-byte voter key. Pinned into
    /// the poll cell's electorate-root commitment when the proposal opens.
    pub fn electorate(&self) -> Vec<[u8; 32]> {
        self.entries.keys().map(|a| a.0).collect()
    }

    /// The total quadratic weight in the pool — `Σ isqrt(contributed)`, the denominator
    /// an operator sizes a quorum against. `None` on `u64` overflow (refused, never
    /// wrapped: a wrapped total would understate the electorate and make any quorum look
    /// reachable).
    pub fn total_weight(&self) -> Option<u64> {
        self.entries
            .values()
            .try_fold(0u64, |acc, &c| acc.checked_add(quadratic_weight(c)))
    }
}

/// The per-contributor pile ledger. All methods take `&self` (interior mutability) so it
/// can be shared exactly like [`Treasury`].
#[derive(Default)]
pub struct SwapPool {
    state: Mutex<PoolState>,
}

#[derive(Default)]
struct PoolState {
    epoch: u64,
    total: u64,
    entries: BTreeMap<DepositAddress, u64>,
    users: BTreeMap<DepositAddress, UserId>,
    /// Processed payment references — the idempotency key, gating BOTH the treasury
    /// credit and the pool attribution so the two can never disagree.
    processed: HashSet<PaymentRef>,
}

impl SwapPool {
    /// A fresh, empty pool at epoch 0.
    pub fn new() -> Self {
        SwapPool::default()
    }

    /// The current pool epoch (bumped by each [`SwapPool::close`]).
    pub fn epoch(&self) -> u64 {
        self.state.lock().unwrap().epoch
    }

    /// The pool's cumulative atomic `$DREGG` across all contributors.
    pub fn total(&self) -> u64 {
        self.state.lock().unwrap().total
    }

    /// What `who` has contributed to the current pool.
    pub fn contributed(&self, who: &DepositAddress) -> u64 {
        self.state
            .lock()
            .unwrap()
            .entries
            .get(who)
            .copied()
            .unwrap_or(0)
    }

    /// `who`'s live quadratic weight — `isqrt` of their current contribution. A vote uses
    /// the PINNED [`PoolSnapshot::weight`] instead; this is the live read for display.
    pub fn weight(&self, who: &DepositAddress) -> u64 {
        quadratic_weight(self.contributed(who))
    }

    /// **Record an observed payment: treasury AND attribution, in one call.**
    ///
    /// This is the front door precisely so the two cannot drift apart. A `$DREGG` payment
    /// grows the treasury pile *and* the payer's pool share; a USDC payment fuels the
    /// tank and is attributed to nobody (USDC is not the pile). Idempotent by
    /// [`PaymentReceived::reference`] over BOTH effects: re-observing a payment moves
    /// neither the treasury nor the pool.
    ///
    /// Fails closed on overflow: nothing moves and the reference is left unprocessed.
    pub fn record_payment<S: TreasuryStore>(
        &self,
        payment: &PaymentReceived,
        treasury: &Treasury<S>,
    ) -> ContributionOutcome {
        let mut state = self.state.lock().unwrap();
        if state.processed.contains(&payment.reference) {
            return ContributionOutcome::AlreadyRecorded;
        }

        match payment.asset {
            Asset::Usdc => {
                state.processed.insert(payment.reference.clone());
                drop(state);
                treasury.record_payment(Asset::Usdc, payment.amount);
                ContributionOutcome::FuelNotPool
            }
            Asset::Dregg => {
                let who = payment.deposit_address;
                let current = state.entries.get(&who).copied().unwrap_or(0);
                // checked, never saturating: two whales must not collapse to one weight.
                let (Some(contributed_total), Some(pool_total)) = (
                    current.checked_add(payment.amount),
                    state.total.checked_add(payment.amount),
                ) else {
                    return ContributionOutcome::Overflow;
                };
                state.entries.insert(who, contributed_total);
                state.users.insert(who, payment.user.clone());
                state.total = pool_total;
                state.processed.insert(payment.reference.clone());
                drop(state);
                treasury.record_payment(Asset::Dregg, payment.amount);
                ContributionOutcome::Contributed {
                    contributed_total,
                    pool_total,
                    weight: quadratic_weight(contributed_total),
                }
            }
        }
    }

    /// **Pin the pool** — freeze the current epoch's per-contributor ledger into the
    /// [`PoolSnapshot`] a swap proposal votes over. Later contributions do not enter this
    /// snapshot.
    pub fn snapshot(&self) -> PoolSnapshot {
        let state = self.state.lock().unwrap();
        PoolSnapshot {
            epoch: state.epoch,
            total: state.total,
            entries: state.entries.clone(),
            users: state.users.clone(),
        }
    }

    /// **Retire a swapped pool.** Subtracts exactly `snapshot`'s per-contributor amounts
    /// (anything contributed AFTER the snapshot survives into the next pool) and bumps
    /// the epoch. Returns the new epoch.
    ///
    /// Refuses a snapshot from any epoch but the current one
    /// ([`PoolError::StaleSnapshot`]) — a pool is retired exactly once, so one passed vote
    /// cannot draw the contribution ledger down twice.
    pub fn close(&self, snapshot: &PoolSnapshot) -> Result<u64, PoolError> {
        let mut state = self.state.lock().unwrap();
        if snapshot.epoch != state.epoch {
            return Err(PoolError::StaleSnapshot {
                snapshot_epoch: snapshot.epoch,
                pool_epoch: state.epoch,
            });
        }
        for (who, &swapped) in &snapshot.entries {
            match state.entries.get(who).copied().unwrap_or(0) {
                live if live > swapped => {
                    state.entries.insert(*who, live - swapped);
                }
                _ => {
                    state.entries.remove(who);
                    state.users.remove(who);
                }
            }
        }
        state.total = state.total.saturating_sub(snapshot.total);
        state.epoch += 1;
        Ok(state.epoch)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::treasury::InMemoryTreasuryStore;

    const ALICE_ADDR: DepositAddress = DepositAddress([0xA1u8; 32]);
    const BOB_ADDR: DepositAddress = DepositAddress([0xB2u8; 32]);
    const CAROL_ADDR: DepositAddress = DepositAddress([0xC3u8; 32]);

    fn treasury() -> Treasury<InMemoryTreasuryStore> {
        Treasury::new(InMemoryTreasuryStore::new(), 6)
    }

    fn pay(
        user: &str,
        addr: DepositAddress,
        asset: Asset,
        amount: u64,
        reference: &str,
    ) -> PaymentReceived {
        PaymentReceived {
            user: UserId::from(user),
            deposit_address: addr,
            asset,
            amount,
            reference: PaymentRef(reference.to_string()),
        }
    }

    #[test]
    fn quadratic_weight_is_the_exact_integer_square_root() {
        // The DEFINING property, checked at boundaries and across scale: w² ≤ x < (w+1)².
        // (u128 so the (w+1)² of a near-u64::MAX input does not overflow the check.)
        for x in [
            0u64,
            1,
            2,
            3,
            4,
            8,
            9,
            10,
            99,
            100,
            101,
            9_999,
            10_000,
            10_001,
            1_000_000,
            100_000_000,
            123_456_789,
            u64::MAX - 1,
            u64::MAX,
        ] {
            let w = quadratic_weight(x) as u128;
            let x = x as u128;
            assert!(w * w <= x, "isqrt({x}) = {w} but {w}² > {x}");
            assert!((w + 1) * (w + 1) > x, "isqrt({x}) = {w} is not maximal");
        }
        // The named anchors.
        assert_eq!(quadratic_weight(0), 0, "no contribution, no weight");
        assert_eq!(quadratic_weight(100_000_000), 10_000);
    }

    #[test]
    fn weight_is_quadratic_not_linear() {
        // THE RULE: paying 4× buys 2× the vote, not 4×. A linear (identity) weight would
        // fail every line here.
        assert_eq!(quadratic_weight(1_000_000), 1_000);
        assert_eq!(quadratic_weight(4_000_000), 2_000, "4× stake ⇒ 2× weight");
        assert_eq!(quadratic_weight(16_000_000), 4_000, "16× stake ⇒ 4× weight");
        // A whale with 100× a minnow's stake votes with 10×, not 100×.
        let minnow = quadratic_weight(1_000_000);
        let whale = quadratic_weight(100_000_000);
        assert_eq!(whale / minnow, 10);
        // And splitting one stake across two addresses LOSES weight (√a+√b < √(a+b) is
        // false — it is the other way; the sybil GAINS). Recorded honestly: quadratic
        // weight without an identity cost is sybil-favourable, and the identity here is
        // the operator-derived deposit address, one per user.
        assert!(
            quadratic_weight(500_000) + quadratic_weight(500_000) > quadratic_weight(1_000_000),
            "two half-stakes out-weigh one whole stake — sybil resistance rests on the \
             one-deposit-address-per-user derivation, not on the weight function",
        );
    }

    #[test]
    fn a_dregg_payment_grows_both_the_pile_and_the_payers_share() {
        let pool = SwapPool::new();
        let t = treasury();
        let out = pool.record_payment(
            &pay("alice", ALICE_ADDR, Asset::Dregg, 1_000_000, "tx1"),
            &t,
        );
        assert_eq!(
            out,
            ContributionOutcome::Contributed {
                contributed_total: 1_000_000,
                pool_total: 1_000_000,
                weight: 1_000,
            }
        );
        assert_eq!(t.dregg_balance(), 1_000_000, "the pile grew");
        assert_eq!(pool.contributed(&ALICE_ADDR), 1_000_000);
        assert_eq!(pool.weight(&ALICE_ADDR), 1_000);
        // A second contributor is attributed separately.
        pool.record_payment(&pay("bob", BOB_ADDR, Asset::Dregg, 4_000_000, "tx2"), &t);
        assert_eq!(pool.total(), 5_000_000);
        assert_eq!(pool.weight(&BOB_ADDR), 2_000);
        assert_eq!(
            pool.contributed(&CAROL_ADDR),
            0,
            "someone who never paid has no share"
        );
        assert_eq!(pool.weight(&CAROL_ADDR), 0, "and therefore no weight");
    }

    #[test]
    fn a_usdc_payment_is_fuel_and_buys_no_pool_weight() {
        // REJECT polarity: USDC funds the tank. It is not the pile, so it confers no
        // weight in a vote about swapping the pile.
        let pool = SwapPool::new();
        let t = treasury();
        assert_eq!(
            pool.record_payment(
                &pay("alice", ALICE_ADDR, Asset::Usdc, 5_000_000, "usdc1"),
                &t
            ),
            ContributionOutcome::FuelNotPool
        );
        assert_eq!(t.usdc_balance(), 5_000_000, "the fuel tank grew");
        assert_eq!(t.dregg_balance(), 0, "the pile did not");
        assert_eq!(pool.contributed(&ALICE_ADDR), 0);
        assert_eq!(pool.weight(&ALICE_ADDR), 0);
        assert_eq!(pool.total(), 0);
    }

    #[test]
    fn re_observing_a_payment_doubles_neither_the_pile_nor_the_weight() {
        // A double-credited contribution would be a double-weighted VOTER, so the
        // idempotency key gates the attribution as strictly as the balance.
        let pool = SwapPool::new();
        let t = treasury();
        let p = pay("alice", ALICE_ADDR, Asset::Dregg, 9_000_000, "same-tx");
        assert!(matches!(
            pool.record_payment(&p, &t),
            ContributionOutcome::Contributed { .. }
        ));
        assert_eq!(
            pool.record_payment(&p, &t),
            ContributionOutcome::AlreadyRecorded
        );
        assert_eq!(t.dregg_balance(), 9_000_000, "the pile did not double");
        assert_eq!(pool.contributed(&ALICE_ADDR), 9_000_000);
        assert_eq!(pool.weight(&ALICE_ADDR), 3_000, "the weight did not double");
    }

    #[test]
    fn an_overflowing_contribution_is_refused_and_changes_nothing() {
        let pool = SwapPool::new();
        let t = treasury();
        pool.record_payment(&pay("alice", ALICE_ADDR, Asset::Dregg, u64::MAX, "big"), &t);
        assert_eq!(pool.total(), u64::MAX);
        assert_eq!(
            pool.record_payment(&pay("bob", BOB_ADDR, Asset::Dregg, 1, "one-more"), &t),
            ContributionOutcome::Overflow,
        );
        assert_eq!(pool.total(), u64::MAX, "nothing moved");
        assert_eq!(pool.contributed(&BOB_ADDR), 0);
        // The reference is left UNprocessed, so an operator can retry after resolving it.
        assert_eq!(
            pool.record_payment(&pay("bob", BOB_ADDR, Asset::Dregg, 1, "one-more"), &t),
            ContributionOutcome::Overflow,
            "a refused contribution did not burn its idempotency key on a success path",
        );
    }

    #[test]
    fn a_snapshot_is_pinned_and_later_contributions_do_not_enter_it() {
        // THE PIN: buying $DREGG after a proposal opens must not buy influence over it.
        let pool = SwapPool::new();
        let t = treasury();
        pool.record_payment(&pay("alice", ALICE_ADDR, Asset::Dregg, 1_000_000, "a1"), &t);
        let pinned = pool.snapshot();
        assert_eq!(pinned.total(), 1_000_000);
        assert_eq!(pinned.contributor_count(), 1);

        // Bob pays AFTER the pin, and alice tops up.
        pool.record_payment(&pay("bob", BOB_ADDR, Asset::Dregg, 4_000_000, "b1"), &t);
        pool.record_payment(&pay("alice", ALICE_ADDR, Asset::Dregg, 3_000_000, "a2"), &t);

        // The pinned snapshot is unmoved: bob has no weight in it, alice's is her
        // as-of-pin stake.
        assert_eq!(pinned.total(), 1_000_000, "the pinned amount did not grow");
        assert_eq!(
            pinned.weight(&BOB_ADDR),
            0,
            "a late payer has no weight here"
        );
        assert_eq!(
            pinned.weight(&ALICE_ADDR),
            1_000,
            "as-of-pin, not as-of-now"
        );
        assert_eq!(pinned.electorate(), vec![ALICE_ADDR.0]);
        // The LIVE pool did move.
        assert_eq!(pool.total(), 8_000_000);
        assert_eq!(pool.weight(&ALICE_ADDR), 2_000);
    }

    #[test]
    fn total_weight_sums_the_quadratic_weights() {
        let pool = SwapPool::new();
        let t = treasury();
        pool.record_payment(&pay("alice", ALICE_ADDR, Asset::Dregg, 1_000_000, "a"), &t);
        pool.record_payment(&pay("bob", BOB_ADDR, Asset::Dregg, 4_000_000, "b"), &t);
        pool.record_payment(&pay("carol", CAROL_ADDR, Asset::Dregg, 9_000_000, "c"), &t);
        let snap = pool.snapshot();
        // 1000 + 2000 + 3000 — NOT isqrt(14_000_000) = 3741, and NOT 14_000_000.
        assert_eq!(snap.total_weight(), Some(6_000));
        assert_eq!(snap.total(), 14_000_000);
        assert_eq!(
            snap.contributors(),
            vec![
                (ALICE_ADDR, 1_000_000, 1_000),
                (BOB_ADDR, 4_000_000, 2_000),
                (CAROL_ADDR, 9_000_000, 3_000),
            ]
        );
    }

    #[test]
    fn closing_retires_the_pool_exactly_once_and_carries_later_payments_forward() {
        let pool = SwapPool::new();
        let t = treasury();
        pool.record_payment(&pay("alice", ALICE_ADDR, Asset::Dregg, 1_000_000, "a1"), &t);
        let snap = pool.snapshot();
        // A contribution that lands between the pin and the settlement belongs to the
        // NEXT pool, not to the one being retired.
        pool.record_payment(&pay("bob", BOB_ADDR, Asset::Dregg, 4_000_000, "b1"), &t);

        assert_eq!(pool.close(&snap).unwrap(), 1, "epoch bumped");
        assert_eq!(
            pool.contributed(&ALICE_ADDR),
            0,
            "the swapped share is retired"
        );
        assert_eq!(
            pool.contributed(&BOB_ADDR),
            4_000_000,
            "the post-pin contribution survives"
        );
        assert_eq!(pool.total(), 4_000_000);

        // REJECT polarity: the same snapshot cannot retire the ledger a second time.
        assert_eq!(
            pool.close(&snap),
            Err(PoolError::StaleSnapshot {
                snapshot_epoch: 0,
                pool_epoch: 1
            }),
        );
        assert_eq!(pool.total(), 4_000_000, "the refused close moved nothing");
        assert_eq!(pool.contributed(&BOB_ADDR), 4_000_000);
    }
}
