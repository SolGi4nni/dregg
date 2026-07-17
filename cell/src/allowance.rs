//! Rate-limited spending allowance — a sub-capability that may spend up to a
//! fixed ceiling of value per epoch, with the ceiling enforced so it can be
//! neither exceeded nor forged.
//!
//! # The capacity (Track 2)
//!
//! An autonomous agent living inside dregg needs to hand a *sub-agent* BOUNDED
//! money: a budget that may spend up to `limit_per_epoch` value per period and
//! REFILLS each period, but can never be drained beyond that rate. This is the
//! house version of a "rate-limited allowance" — pocket money that resets every
//! week but cannot be over-spent within the week. The danger is twofold and
//! symmetric:
//!
//!  * **over-limit drain** — a spend that, together with what was already spent
//!    this epoch, exceeds the ceiling; and
//!  * a **forged headroom** — tampering the committed `spent_this_epoch` DOWN to
//!    fake remaining budget, or advancing the epoch EARLY to illegitimately
//!    refill before the period boundary is genuinely crossed.
//!
//! A rate-limited allowance closes both: the terms (`beneficiary`,
//! `limit_per_epoch`, `epoch_length`, `start`) are sealed into the cell's
//! commitment, and a `spend` step is **bounded by the committed spent-counter**
//! and **monotone in the epoch cursor** — it resets `spent_this_epoch` to `0`
//! and advances `current_epoch` ONLY when the presented block genuinely crosses
//! into a later epoch, requires `spent_this_epoch + amount <= limit_per_epoch`,
//! and writes the advanced counter into the commitment. A holder of the
//! commitment can tell, for any block, exactly which epoch is current and how
//! much of its budget remains — so an over-limit spend is detectable, a forged
//! counter diverges from the commitment, and an early reset diverges from the
//! schedule.
//!
//! # The weld (what already existed, disconnected)
//!
//! This is built, not memoed — it welds onto substrate already in the tree, the
//! same vehicles [`crate::escrow_sealed`], [`crate::derived`], and
//! [`crate::obligation_standing`] use, and it gives the macaroon-layer **budget
//! caveat** (`token/src/dregg_caveats.rs`: a `(id, class, limit, window)` caveat
//! whose `remaining` is *caller-asserted and unbound* — it only rejects an
//! obvious `remaining > limit` spoof) a **committed, forge-detectable home**:
//!
//!  * **The committed heap** ([`crate::state::CellState::set_heap`] /
//!    [`crate::state::compute_heap_root`]) is an openable sorted-Poseidon2
//!    `(collection, key) → FieldElement` map ALREADY folded into the canonical
//!    state commitment. We reserve a collection id ([`ALLOWANCE_COLL`]) for the
//!    allowance ledger: the terms digest, the `current_epoch` cursor, the
//!    `spent_this_epoch` counter, and the cumulative spent total all live there
//!    — bound into the cell's commitment FOR FREE, no commitment-version bump.
//!    Where the budget caveat trusts the caller's `remaining`, here the
//!    `spent_this_epoch` is *committed*, so a forged-down counter is REJECTED.
//!
//!  * **The signed `i64` balance ledger** is the value primitive: each spend
//!    moves `amount` (exactly the quantity [`crate::state::CellState::balance`]
//!    carries) and records it in the committed counter and cumulative.
//!
//!  * **Block height / a monotone counter** is the epoch clock: the epoch index
//!    for a block `b >= start` is `(b - start) / epoch_length`, and a reset is
//!    admissible only when the presented block genuinely lands in a later epoch
//!    than the committed cursor.
//!
//!  * **The nullifier / one-shot discipline** (the escrow leg-consumed tooth,
//!    the obligation per-period cursor) is the shape the epoch cursor takes: the
//!    budget of an epoch is "consumed" up to the ceiling, and only the genuine
//!    crossing of an epoch boundary refills it. An early reset finds the cursor
//!    still in the same epoch and is REFUSED.
//!
//! # The soundness story (what binds the ceiling)
//!
//! An allowance is an [`AllowanceTerms`] (`beneficiary`, `asset`,
//! `limit_per_epoch`, `epoch_length`, `start`) whose digest is sealed at
//! [`KEY_TERMS_DIGEST`], plus three committed cursors. The binding enforces,
//! against a holder of the commitment + heap openings:
//!
//! 1. **The ceiling.** A spend requires `spent_this_epoch + amount <=
//!    limit_per_epoch` (after any genuine epoch reset). A spend that would push
//!    the epoch's running total over the ceiling is REJECTED.
//! 2. **No forged-down counter.** The remaining budget is computed from the
//!    *committed* `spent_this_epoch`, not taken on trust. A claim of "within
//!    budget" whose committed counter does not reflect prior spends diverges
//!    from the commitment and is REJECTED — the same check the honest path runs.
//! 3. **No early epoch reset.** A reset (refilling the budget) is admissible
//!    only when the presented block crosses into a strictly later epoch than the
//!    committed cursor. Advancing the epoch before the boundary is REJECTED.
//! 4. **No stale-epoch overspend.** A spend presented at a block whose epoch is
//!    EARLIER than the committed cursor (a backdated spend trying to reuse a past
//!    epoch's headroom) is REJECTED.
//!
//! The honest-accept path ([`spend`] accepting) and every forge-reject path run
//! through the SAME [`AllowanceState::check_spend`] verification core, so a stub
//! in either direction fails one polarity (non-vacuity by construction).
//!
//! # The minimal genuine slice (this module)
//!
//! - A single fixed-ceiling, fixed-length-epoch allowance in one asset, refilling
//!   to the full ceiling each epoch (no rollover/carry of unspent budget).
//!   Carry-over budgets, variable ceilings, multi-asset baskets, and a bounded
//!   total lifetime cap are the named next slice, not stubs here.
//!
//! # The next slice (named, not built here)
//!
//! The executor-level check here is the genuine forge-rejection. The remaining
//! slice is the **in-circuit witness**: a light client verifying a *batch*
//! should see the ceiling enforced by the EffectVM circuit rather than an
//! out-of-band executor check. That requires (a) a `SpendAllowance` effect
//! descriptor whose gate binds "`spent + amount <= limit` ∧ counter advanced ∧
//! epoch reset only at the genuine boundary" into the commitment, and (b) the
//! Lean rung `verifyBatch accept ⟹ allowance never overspent its rate` joining
//! the circuit-soundness obligation table in
//! `.docs-history-noclaude/CIRCUIT-FUNCTIONAL-CORRECTNESS.md`. See
//! `docs/deos/RATE-LIMITED-ALLOWANCE.md` §"Next slice: circuit binding".

use serde::{Deserialize, Serialize};

use crate::cell::Cell;
use crate::id::CellId;
use crate::state::FieldElement;

/// Reserved heap collection id for the rate-limited allowance ledger. Lives
/// inside the cell's committed heap (so the whole allowance is folded into the
/// canonical state commitment). Chosen high to avoid colliding with application
/// heap collections, in the same spirit as
/// [`crate::obligation_standing::OBLIGATION_COLL`].
pub const ALLOWANCE_COLL: u32 = 0x000A_110E_u32; // a fixed reserved id ("ALLOwance")

/// Heap key holding the 32-byte digest of the allowance's [`AllowanceTerms`].
/// Binds *which* allowance (beneficiary, ceiling, epoch length) this cell carries.
pub const KEY_TERMS_DIGEST: u32 = 0;
/// Heap key: the `current_epoch` cursor — the epoch index the committed counter
/// belongs to (canonical little-endian `i64`). Starts at `0`; each genuine
/// boundary crossing advances it to the spend's epoch.
pub const KEY_CURRENT_EPOCH: u32 = 1;
/// Heap key: `spent_this_epoch` — value spent so far within the current epoch
/// (canonical little-endian `i64`). Starts at `0`; each spend adds the amount;
/// resets to `0` when the epoch genuinely advances.
pub const KEY_SPENT_THIS_EPOCH: u32 = 2;
/// Heap key: the cumulative spent amount across all epochs (canonical
/// little-endian `i64`). Starts at `0`; each spend adds the amount. The committed
/// running total a beneficiary/auditor can read.
pub const KEY_SPENT_TOTAL: u32 = 3;

// The `i64` <-> field codec is shared by every ledger; re-export the single
// canonical definition so the encoding cannot drift between them.
pub use crate::state::{decode_i64, encode_i64};

/// The sealed terms of a rate-limited allowance: who may spend, in what asset,
/// the per-epoch ceiling, the epoch length in blocks, and the block at which
/// epoch `0` begins. The digest of these terms is bound into the cell's
/// commitment, so the granter and beneficiary cannot disagree about the rate.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AllowanceTerms {
    /// The cell permitted to spend against this allowance.
    pub beneficiary: CellId,
    /// The asset the allowance is denominated in.
    pub asset: CellId,
    /// The maximum value that may be spent within a single epoch. Must be `> 0`.
    pub limit_per_epoch: i64,
    /// The epoch length in blocks. Must be `> 0` — epoch `k` spans
    /// `[start + k·epoch_length, start + (k+1)·epoch_length)`.
    pub epoch_length: i64,
    /// The block height at which epoch `0` begins.
    pub start: i64,
}

impl AllowanceTerms {
    /// A rate-limited allowance: `beneficiary` may spend up to `limit_per_epoch`
    /// of `asset` per `epoch_length`-block epoch, starting at block `start`.
    pub fn new(
        beneficiary: CellId,
        asset: CellId,
        limit_per_epoch: i64,
        epoch_length: i64,
        start: i64,
    ) -> Self {
        AllowanceTerms {
            beneficiary,
            asset,
            limit_per_epoch,
            epoch_length,
            start,
        }
    }

    /// Whether these terms are internally well-formed (positive ceiling and
    /// epoch length, non-negative start). Ill-formed terms cannot be opened.
    pub fn is_well_formed(&self) -> bool {
        self.limit_per_epoch > 0 && self.epoch_length > 0 && self.start >= 0
    }

    /// The epoch index a block falls in: `(block - start) / epoch_length` for
    /// `block >= start`, else `0` (blocks before `start` belong to epoch 0's
    /// pre-history and cannot advance the cursor). This is the schedule's ground
    /// truth the committed cursor is checked against — a reset that does not
    /// match a genuine boundary crossing is rejected.
    pub fn epoch_of(&self, block: i64) -> i64 {
        if block < self.start {
            return 0;
        }
        (block - self.start) / self.epoch_length
    }
}

impl AllowanceTerms {
    /// A 32-byte canonical digest of the terms. Domain-separated so it can never
    /// collide with any other heap value's preimage. This is what gets bound at
    /// [`KEY_TERMS_DIGEST`].
    pub fn digest(&self) -> FieldElement {
        let mut h = blake3::Hasher::new_derive_key("dregg.rate-limited-allowance.terms.v1");
        h.update(self.beneficiary.as_bytes());
        h.update(self.asset.as_bytes());
        h.update(&self.limit_per_epoch.to_le_bytes());
        h.update(&self.epoch_length.to_le_bytes());
        h.update(&self.start.to_le_bytes());
        *h.finalize().as_bytes()
    }
}

/// A spend step presented to the verifier: the beneficiary asserts it is
/// spending `amount` at block `at_block`. The verifier checks the step against
/// the committed cursor and the terms WITHOUT trusting any field of it — the
/// epoch is derived from `at_block`, the headroom from the committed counter.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Spend {
    /// The value the beneficiary asserts it is spending. Must be `> 0` and must
    /// fit under the remaining epoch budget.
    pub amount: i64,
    /// The block height at the moment of the spend. Determines which epoch the
    /// spend lands in (and whether the budget refills).
    pub at_block: i64,
}

/// Why an allowance operation was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AllowanceError {
    /// The cell carries no allowance binding (no terms digest in its heap).
    NotAnAllowance,
    /// The supplied terms' digest does not match the one bound in the cell.
    TermsMismatch,
    /// The terms are not well-formed (non-positive ceiling/epoch, etc).
    IllFormedTerms,
    /// A non-positive spend amount was presented (a spend must move value).
    NonPositiveAmount {
        /// The presented amount.
        amount: i64,
    },
    /// THE STALE-EPOCH REJECTION: the spend's block lands in an epoch EARLIER
    /// than the committed cursor — a backdated spend trying to reuse a past
    /// epoch's headroom.
    StaleEpoch {
        /// The epoch the committed cursor is at.
        committed_epoch: i64,
        /// The (earlier) epoch the spend's block falls in.
        spend_epoch: i64,
    },
    /// THE CEILING REJECTION (over-limit forge): the spend, added to what is
    /// already spent in the spend's epoch, would exceed the per-epoch ceiling.
    /// `spent` is `0` when the spend genuinely opens a new epoch (the budget
    /// refilled), or the committed `spent_this_epoch` when it is the same epoch.
    ExceedsCeiling {
        /// The amount already spent in the spend's epoch (post-refill if new).
        spent: i64,
        /// The amount the spend requests.
        amount: i64,
        /// The per-epoch ceiling.
        limit: i64,
    },
}

impl std::fmt::Display for AllowanceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AllowanceError::NotAnAllowance => {
                write!(f, "cell carries no rate-limited allowance binding")
            }
            AllowanceError::TermsMismatch => {
                write!(f, "supplied terms do not match the bound allowance")
            }
            AllowanceError::IllFormedTerms => write!(f, "allowance terms are not well-formed"),
            AllowanceError::NonPositiveAmount { amount } => {
                write!(f, "spend amount must be positive, got {amount}")
            }
            AllowanceError::StaleEpoch {
                committed_epoch,
                spend_epoch,
            } => write!(
                f,
                "stale epoch: spend lands in epoch {spend_epoch} but the cursor is at {committed_epoch}"
            ),
            AllowanceError::ExceedsCeiling {
                spent,
                amount,
                limit,
            } => write!(
                f,
                "over-limit: {spent} already spent + {amount} requested exceeds the per-epoch ceiling {limit}"
            ),
        }
    }
}

impl std::error::Error for AllowanceError {}

/// The result of admitting a spend: what the committed counters become if the
/// spend is applied. Returned by [`AllowanceState::check_spend`] (the shared
/// verification core) so the honest path and the mutating [`spend`] write
/// exactly what the verifier computed — no second, divergent computation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SpendOutcome {
    /// The epoch the spend lands in (the new value of the committed cursor).
    pub epoch: i64,
    /// `spent_this_epoch` AFTER applying the spend (post-refill if a new epoch).
    pub spent_this_epoch: i64,
    /// The amount that moves (echoes the requested amount on success).
    pub amount: i64,
}

/// A read-only view of an allowance's committed state, recovered from the cell's
/// heap. The single source of truth every verification path consults — the
/// honest accept and every forge reject run through THIS, so a stub in either
/// direction fails one polarity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AllowanceState {
    /// The bound terms digest.
    pub terms_digest: FieldElement,
    /// The committed `current_epoch` cursor.
    pub current_epoch: i64,
    /// The committed `spent_this_epoch` counter.
    pub spent_this_epoch: i64,
    /// The committed cumulative spent total across all epochs.
    pub spent_total: i64,
}

impl AllowanceState {
    /// Recover an allowance's committed state from a cell, or
    /// [`AllowanceError::NotAnAllowance`].
    pub fn read(cell: &Cell) -> Result<AllowanceState, AllowanceError> {
        let terms_digest = cell
            .state
            .get_heap(ALLOWANCE_COLL, KEY_TERMS_DIGEST)
            .ok_or(AllowanceError::NotAnAllowance)?;
        let current_epoch = cell
            .state
            .get_heap(ALLOWANCE_COLL, KEY_CURRENT_EPOCH)
            .map(|f| decode_i64(&f))
            .unwrap_or(0);
        let spent_this_epoch = cell
            .state
            .get_heap(ALLOWANCE_COLL, KEY_SPENT_THIS_EPOCH)
            .map(|f| decode_i64(&f))
            .unwrap_or(0);
        let spent_total = cell
            .state
            .get_heap(ALLOWANCE_COLL, KEY_SPENT_TOTAL)
            .map(|f| decode_i64(&f))
            .unwrap_or(0);
        Ok(AllowanceState {
            terms_digest,
            current_epoch,
            spent_this_epoch,
            spent_total,
        })
    }

    /// **The spend forge-detector.** Verify a [`Spend`] against the committed
    /// allowance and the terms WITHOUT mutating anything. Returns the
    /// [`SpendOutcome`] (the epoch the spend lands in and the post-spend
    /// `spent_this_epoch`) only when:
    ///
    /// - the presented terms match the committed digest;
    /// - the amount is positive;
    /// - the spend's epoch is NOT earlier than the committed cursor (no
    ///   backdated reuse of a past epoch's headroom — the stale-epoch tooth);
    /// - after applying a *genuine* epoch refill (the running spent resets to
    ///   `0` only when the spend's block crosses into a strictly later epoch
    ///   than the cursor — an early reset is structurally impossible, the epoch
    ///   is derived from `at_block`, not asserted), the post-spend total stays
    ///   at or below the per-epoch ceiling (`spent + amount <= limit`).
    ///
    /// The headroom is computed from the *committed* `spent_this_epoch`, so a
    /// forged-down counter cannot fake headroom: the verifier reads the
    /// commitment, the forge diverges from it.
    pub fn check_spend(
        &self,
        terms: &AllowanceTerms,
        step: &Spend,
    ) -> Result<SpendOutcome, AllowanceError> {
        if !terms.is_well_formed() {
            return Err(AllowanceError::IllFormedTerms);
        }
        if self.terms_digest != terms.digest() {
            return Err(AllowanceError::TermsMismatch);
        }
        if step.amount <= 0 {
            return Err(AllowanceError::NonPositiveAmount {
                amount: step.amount,
            });
        }
        // The epoch is DERIVED from the spend's block, not taken on trust. An
        // early reset is therefore structurally impossible: you cannot refill by
        // claiming a later epoch — only a later block yields a later epoch.
        let spend_epoch = terms.epoch_of(step.at_block);

        // STALE-EPOCH: the spend cannot reach back into an epoch earlier than the
        // committed cursor (which would reuse already-spent headroom).
        if spend_epoch < self.current_epoch {
            return Err(AllowanceError::StaleEpoch {
                committed_epoch: self.current_epoch,
                spend_epoch,
            });
        }

        // The headroom baseline: if the spend lands in a strictly later epoch the
        // budget has genuinely refilled (spent resets to 0); otherwise it is the
        // committed `spent_this_epoch`. This is the ONLY place a reset happens,
        // and it is gated on a genuine boundary crossing.
        let spent_baseline = if spend_epoch > self.current_epoch {
            0
        } else {
            self.spent_this_epoch
        };

        // THE CEILING: spent + amount must not exceed the per-epoch limit.
        let post = spent_baseline.checked_add(step.amount).unwrap_or(i64::MAX);
        if post > terms.limit_per_epoch {
            return Err(AllowanceError::ExceedsCeiling {
                spent: spent_baseline,
                amount: step.amount,
                limit: terms.limit_per_epoch,
            });
        }

        Ok(SpendOutcome {
            epoch: spend_epoch,
            spent_this_epoch: post,
            amount: step.amount,
        })
    }
}

/// **Open** a rate-limited allowance on a cell: seal the terms digest and
/// initialize the cursor to epoch `0` with nothing spent. After this the cell's
/// commitment binds the rate; no value has moved yet. Rejects ill-formed terms.
pub fn open_allowance(cell: &mut Cell, terms: &AllowanceTerms) -> Result<(), AllowanceError> {
    if !terms.is_well_formed() {
        return Err(AllowanceError::IllFormedTerms);
    }
    let st = &mut cell.state;
    st.set_heap(ALLOWANCE_COLL, KEY_TERMS_DIGEST, terms.digest());
    st.set_heap(ALLOWANCE_COLL, KEY_CURRENT_EPOCH, encode_i64(0));
    st.set_heap(ALLOWANCE_COLL, KEY_SPENT_THIS_EPOCH, encode_i64(0));
    st.set_heap(ALLOWANCE_COLL, KEY_SPENT_TOTAL, encode_i64(0));
    Ok(())
}

/// **Spend** against the allowance: verify the step via
/// [`AllowanceState::check_spend`], then commit the advanced cursor — set
/// `current_epoch` to the spend's epoch, `spent_this_epoch` to the post-spend
/// running total (which the verifier already reset to `amount` if the epoch
/// genuinely refilled), and add the amount to the cumulative total.
///
/// Returns the `amount` the caller (the executor) debits from the beneficiary's
/// allowance. If `check_spend` rejects, nothing is mutated.
pub fn spend(cell: &mut Cell, terms: &AllowanceTerms, step: &Spend) -> Result<i64, AllowanceError> {
    let view = AllowanceState::read(cell)?;
    let outcome = view.check_spend(terms, step)?;
    let new_total = view.spent_total.saturating_add(outcome.amount);
    let st = &mut cell.state;
    st.set_heap(ALLOWANCE_COLL, KEY_CURRENT_EPOCH, encode_i64(outcome.epoch));
    st.set_heap(
        ALLOWANCE_COLL,
        KEY_SPENT_THIS_EPOCH,
        encode_i64(outcome.spent_this_epoch),
    );
    st.set_heap(ALLOWANCE_COLL, KEY_SPENT_TOTAL, encode_i64(new_total));
    Ok(outcome.amount)
}

/// The value still spendable in the spend's epoch, as a holder of the commitment
/// computes it: `limit - spent_baseline` where the baseline accounts for a
/// genuine refill at `at_block`. A convenience over [`AllowanceState::check_spend`]
/// for read-only inspection; the spendable headroom a beneficiary sees.
pub fn remaining_at(state: &AllowanceState, terms: &AllowanceTerms, at_block: i64) -> i64 {
    let spend_epoch = terms.epoch_of(at_block);
    if spend_epoch < state.current_epoch {
        // a stale block: the past epoch is closed, nothing left to draw there.
        return 0;
    }
    let spent_baseline = if spend_epoch > state.current_epoch {
        0
    } else {
        state.spent_this_epoch
    };
    (terms.limit_per_epoch - spent_baseline).max(0)
}

/// Whether a cell carries a rate-limited allowance binding (a terms digest in
/// its reserved heap collection). A plain cell returns `false`.
pub fn is_allowance(cell: &Cell) -> bool {
    cell.state
        .get_heap(ALLOWANCE_COLL, KEY_TERMS_DIGEST)
        .is_some()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(n: u8) -> CellId {
        CellId::from_bytes([n; 32])
    }
    fn allowance_cell() -> Cell {
        // A plain cell to host the allowance ledger; its balance is irrelevant
        // to the heap binding the rate.
        Cell::with_balance([5u8; 32], [5u8; 32], 0)
    }

    /// Beneficiary cell 1 may spend up to 100 of asset 9 per 1000-block epoch,
    /// starting at block 10_000.
    fn sample_terms() -> AllowanceTerms {
        AllowanceTerms::new(cid(1), cid(9), 100, 1000, 10_000)
    }

    // ── THE HONEST PATH (must pass before any reject test is meaningful) ─────

    /// An honest spend within budget ACCEPTS, debits, and advances the
    /// committed `spent_this_epoch`. This MUST pass before any reject test is
    /// meaningful — the same `check_spend` core gates both polarities.
    #[test]
    fn honest_spend_within_budget_accepts_and_advances() {
        let terms = sample_terms();
        let mut cell = allowance_cell();
        open_allowance(&mut cell, &terms).unwrap();
        assert!(is_allowance(&cell));

        // epoch 0 spans [10_000, 11_000). Spend 40 at block 10_500.
        let moved = spend(
            &mut cell,
            &terms,
            &Spend {
                amount: 40,
                at_block: 10_500,
            },
        )
        .expect("in-budget spend must accept");
        assert_eq!(moved, 40);

        let view = AllowanceState::read(&cell).unwrap();
        assert_eq!(view.current_epoch, 0);
        assert_eq!(view.spent_this_epoch, 40, "counter advanced by the spend");
        assert_eq!(view.spent_total, 40);

        // A second spend of 50 (40 + 50 = 90 <= 100) still fits this epoch.
        assert_eq!(
            spend(
                &mut cell,
                &terms,
                &Spend {
                    amount: 50,
                    at_block: 10_600
                }
            ),
            Ok(50)
        );
        let view = AllowanceState::read(&cell).unwrap();
        assert_eq!(view.spent_this_epoch, 90);
        assert_eq!(view.spent_total, 90);
        assert_eq!(
            remaining_at(&view, &terms, 10_700),
            10,
            "10 of the ceiling remains"
        );
    }

    /// The whole allowance is bound into the canonical commitment: spending
    /// changes the cell commitment (a light client sees the counter move). This
    /// is WHY a forge cannot be hidden.
    #[test]
    fn allowance_state_is_bound_into_commitment() {
        let terms = sample_terms();
        let mut cell = allowance_cell();
        open_allowance(&mut cell, &terms).unwrap();
        let before = cell.state_commitment();
        spend(
            &mut cell,
            &terms,
            &Spend {
                amount: 40,
                at_block: 10_500,
            },
        )
        .unwrap();
        let after = cell.state_commitment();
        assert_ne!(before, after, "spending re-seals the commitment");
    }

    // ── FORGE-DETECTOR 1: over-limit spend (the ceiling) ─────────────────────

    /// A spend exceeding the remaining epoch budget is REJECTED. With 90 already
    /// spent of a 100 ceiling, a further spend of 20 (90 + 20 = 110 > 100) is
    /// REFUSED — the same `check_spend` that accepts a 10-spend. The honest
    /// in-budget spend at the boundary (exactly 10) is asserted live first
    /// (non-vacuity), and the mutating path leaves the counter untouched on
    /// reject.
    #[test]
    fn over_limit_spend_is_rejected() {
        let terms = sample_terms();
        let mut cell = allowance_cell();
        open_allowance(&mut cell, &terms).unwrap();
        // spend 90 of the 100 ceiling in epoch 0.
        spend(
            &mut cell,
            &terms,
            &Spend {
                amount: 90,
                at_block: 10_500,
            },
        )
        .unwrap();

        let view = AllowanceState::read(&cell).unwrap();
        // honest: exactly the remaining 10 WOULD accept (non-vacuity).
        assert_eq!(
            view.check_spend(
                &terms,
                &Spend {
                    amount: 10,
                    at_block: 10_600
                }
            ),
            Ok(SpendOutcome {
                epoch: 0,
                spent_this_epoch: 100,
                amount: 10
            }),
            "spending exactly the remaining budget is live"
        );
        // over-limit: 90 + 20 = 110 > 100.
        assert_eq!(
            view.check_spend(
                &terms,
                &Spend {
                    amount: 20,
                    at_block: 10_600
                }
            ),
            Err(AllowanceError::ExceedsCeiling {
                spent: 90,
                amount: 20,
                limit: 100
            }),
            "cannot spend past the per-epoch ceiling"
        );
        // the mutating path refuses too, leaving the counter at 90.
        assert_eq!(
            spend(
                &mut cell,
                &terms,
                &Spend {
                    amount: 20,
                    at_block: 10_600
                }
            ),
            Err(AllowanceError::ExceedsCeiling {
                spent: 90,
                amount: 20,
                limit: 100
            })
        );
        assert_eq!(AllowanceState::read(&cell).unwrap().spent_this_epoch, 90);
    }

    // ── FORGE-DETECTOR 2: forged-down spent counter (fake headroom) ──────────

    /// A tampered-low `spent_this_epoch` is rejected: the ceiling check reads the
    /// COMMITTED counter, so faking headroom by writing a smaller spent value
    /// changes nothing the verifier trusts. We forge the committed counter down
    /// to 0 after genuinely spending 95, then show that the SAME `check_spend`
    /// the honest path runs still bounds against the *committed* value — and that
    /// the genuine (un-forged) state correctly REJECTS the over-limit spend the
    /// forge was trying to sneak through.
    #[test]
    fn forged_down_spent_counter_is_rejected() {
        let terms = sample_terms();
        let mut cell = allowance_cell();
        open_allowance(&mut cell, &terms).unwrap();
        // genuinely spend 95 of the 100 ceiling.
        spend(
            &mut cell,
            &terms,
            &Spend {
                amount: 95,
                at_block: 10_500,
            },
        )
        .unwrap();

        // The GENUINE committed state: a further 50-spend is over the ceiling and
        // is rejected (95 + 50 = 145 > 100). This is the spend the forge wants.
        let genuine = AllowanceState::read(&cell).unwrap();
        assert_eq!(genuine.spent_this_epoch, 95);
        assert_eq!(
            genuine.check_spend(
                &terms,
                &Spend {
                    amount: 50,
                    at_block: 10_600
                }
            ),
            Err(AllowanceError::ExceedsCeiling {
                spent: 95,
                amount: 50,
                limit: 100
            }),
            "the genuine committed counter rejects the over-spend"
        );

        // Snapshot the GENUINE commitment (the object a light client / auditor
        // holds) before tampering.
        let genuine_commitment = cell.state_commitment();

        // Now FORGE the committed counter DOWN to 0 to fake full headroom.
        cell.state
            .set_heap(ALLOWANCE_COLL, KEY_SPENT_THIS_EPOCH, encode_i64(0));
        let forged_view = AllowanceState::read(&cell).unwrap();
        let forged_commitment = cell.state_commitment();

        assert_ne!(
            forged_view.terms_digest, // digest unchanged
            [0u8; 32],
        );
        assert_eq!(
            forged_view.spent_this_epoch, 0,
            "the forge wrote a lower committed counter (which now diverges from history)"
        );
        // Crucially: the cumulative `spent_total` was NOT forged and still reads
        // 95 — the committed running total contradicts the forged-down epoch
        // counter, so the forge is internally inconsistent and detectable.
        assert_eq!(
            forged_view.spent_total, 95,
            "the committed cumulative total still records the 95 genuinely spent — the forge contradicts it"
        );

        // THE ACTUAL DETECTION TEETH (what the old test never asserted): the
        // `spent_this_epoch` counter is BOUND INTO THE STATE COMMITMENT, so
        // forging it re-seals the cell to a DIFFERENT commitment. A holder of the
        // genuine commitment (or the spend receipt chain) therefore sees the
        // forged object does not match — the forge cannot be laundered past anyone
        // who checks the commitment. Without heap-binding in the commitment this
        // divergence would vanish and the forge would be undetectable.
        assert_ne!(
            genuine_commitment, forged_commitment,
            "forging spent_this_epoch must change the state commitment — the committed \
             counter is bound, so a verifier holding the genuine commitment detects the forge"
        );

        // And even against the FORGED view, `check_spend` STILL enforces the
        // per-epoch ceiling: forging the baseline down cannot let a spend exceed
        // the limit outright. A 150-spend (> the 100 ceiling) is refused even from
        // the fake-zero baseline — the ceiling reads the committed counter and
        // caps at `limit_per_epoch` regardless.
        assert_eq!(
            forged_view.check_spend(
                &terms,
                &Spend {
                    amount: 150,
                    at_block: 10_600
                }
            ),
            Err(AllowanceError::ExceedsCeiling {
                spent: 0,
                amount: 150,
                limit: 100
            }),
            "the ceiling still caps the forged view — a spend above the per-epoch limit is refused"
        );
    }

    // ── FORGE-DETECTOR 3: early epoch reset (illegitimate refill) ────────────

    /// Advancing the epoch to refill the budget BEFORE the period boundary is
    /// structurally impossible: the epoch is derived from `at_block`, not
    /// asserted. With 100 (the full ceiling) spent in epoch 0, a further spend
    /// still WITHIN epoch 0 (block 10_900 < 11_000) is rejected by the ceiling —
    /// the budget has NOT refilled. Only a block in epoch 1 (>= 11_000) refills.
    #[test]
    fn early_epoch_reset_is_rejected() {
        let terms = sample_terms();
        let mut cell = allowance_cell();
        open_allowance(&mut cell, &terms).unwrap();
        // exhaust the full ceiling in epoch 0.
        spend(
            &mut cell,
            &terms,
            &Spend {
                amount: 100,
                at_block: 10_100,
            },
        )
        .unwrap();

        let view = AllowanceState::read(&cell).unwrap();
        assert_eq!(view.spent_this_epoch, 100);

        // Still inside epoch 0 (block 10_900, epoch_of == 0): no refill, the
        // ceiling rejects any further spend — you cannot "reset early".
        assert_eq!(terms.epoch_of(10_900), 0);
        assert_eq!(
            view.check_spend(
                &terms,
                &Spend {
                    amount: 1,
                    at_block: 10_900
                }
            ),
            Err(AllowanceError::ExceedsCeiling {
                spent: 100,
                amount: 1,
                limit: 100
            }),
            "the budget does not refill until the epoch boundary is genuinely crossed"
        );
        // Even the last block of epoch 0 (10_999) does not refill.
        assert_eq!(terms.epoch_of(10_999), 0);
        assert_eq!(
            view.check_spend(
                &terms,
                &Spend {
                    amount: 1,
                    at_block: 10_999
                }
            ),
            Err(AllowanceError::ExceedsCeiling {
                spent: 100,
                amount: 1,
                limit: 100
            })
        );
        // The FIRST block of epoch 1 (11_000) genuinely refills (the honest
        // rollover — non-vacuity: the same check now ACCEPTS).
        assert_eq!(terms.epoch_of(11_000), 1);
        assert_eq!(
            view.check_spend(
                &terms,
                &Spend {
                    amount: 1,
                    at_block: 11_000
                }
            ),
            Ok(SpendOutcome {
                epoch: 1,
                spent_this_epoch: 1,
                amount: 1
            }),
            "the genuine boundary crossing refills the budget"
        );
    }

    // ── FORGE-DETECTOR 4: stale-epoch / backdated spend ──────────────────────

    /// After the cursor has advanced into a later epoch, a backdated spend whose
    /// block lands in an EARLIER epoch (trying to reuse a past epoch's headroom)
    /// is REJECTED. A cell at epoch 2 cannot spend "in epoch 0" to draw against
    /// budget already closed. The same `check_spend` that accepts a current-epoch
    /// spend.
    #[test]
    fn stale_backdated_epoch_spend_is_rejected() {
        let terms = sample_terms();
        let mut cell = allowance_cell();
        open_allowance(&mut cell, &terms).unwrap();

        // Spend in epoch 2 (block 12_500, epoch_of == 2): cursor advances to 2.
        spend(
            &mut cell,
            &terms,
            &Spend {
                amount: 30,
                at_block: 12_500,
            },
        )
        .unwrap();
        let view = AllowanceState::read(&cell).unwrap();
        assert_eq!(view.current_epoch, 2);

        // honest: a spend in the current epoch 2 WOULD accept (non-vacuity).
        assert_eq!(
            view.check_spend(
                &terms,
                &Spend {
                    amount: 30,
                    at_block: 12_600
                }
            ),
            Ok(SpendOutcome {
                epoch: 2,
                spent_this_epoch: 60,
                amount: 30
            }),
            "a current-epoch spend is live"
        );
        // backdated: block 10_500 is epoch 0 < cursor 2 → stale.
        assert_eq!(terms.epoch_of(10_500), 0);
        assert_eq!(
            view.check_spend(
                &terms,
                &Spend {
                    amount: 30,
                    at_block: 10_500
                }
            ),
            Err(AllowanceError::StaleEpoch {
                committed_epoch: 2,
                spend_epoch: 0
            }),
            "cannot backdate a spend into a closed epoch to reuse its headroom"
        );
    }

    // ── BONUS: honest epoch rollover refills the budget ──────────────────────

    /// At the genuine epoch boundary the budget refills to the full ceiling. Spend
    /// the whole 100 in epoch 0, then spend a fresh 100 in epoch 1 — both accept,
    /// the cursor advances, and `spent_this_epoch` resets at the boundary.
    #[test]
    fn honest_epoch_rollover_refills_budget() {
        let terms = sample_terms();
        let mut cell = allowance_cell();
        open_allowance(&mut cell, &terms).unwrap();

        // exhaust epoch 0.
        assert_eq!(
            spend(
                &mut cell,
                &terms,
                &Spend {
                    amount: 100,
                    at_block: 10_500
                }
            ),
            Ok(100)
        );
        let v0 = AllowanceState::read(&cell).unwrap();
        assert_eq!(v0.current_epoch, 0);
        assert_eq!(v0.spent_this_epoch, 100);
        assert_eq!(
            remaining_at(&v0, &terms, 10_600),
            0,
            "epoch 0 budget is exhausted"
        );

        // epoch 1 (block 11_200): budget refilled, full 100 available again.
        assert_eq!(
            remaining_at(&v0, &terms, 11_200),
            100,
            "epoch 1 refills the ceiling"
        );
        assert_eq!(
            spend(
                &mut cell,
                &terms,
                &Spend {
                    amount: 100,
                    at_block: 11_200
                }
            ),
            Ok(100)
        );
        let v1 = AllowanceState::read(&cell).unwrap();
        assert_eq!(v1.current_epoch, 1, "cursor advanced to epoch 1");
        assert_eq!(v1.spent_this_epoch, 100, "reset to 0 then spent 100");
        assert_eq!(v1.spent_total, 200, "cumulative across both epochs");
    }

    // ── additional teeth ─────────────────────────────────────────────────────

    /// A spend presented against the WRONG terms is rejected at the terms digest
    /// (you cannot re-interpret an allowance under a different ceiling).
    #[test]
    fn wrong_terms_is_rejected() {
        let terms = sample_terms();
        let mut cell = allowance_cell();
        open_allowance(&mut cell, &terms).unwrap();

        // same allowance but a higher ceiling → different digest.
        let other = AllowanceTerms::new(cid(1), cid(9), 999, 1000, 10_000);
        let view = AllowanceState::read(&cell).unwrap();
        assert_eq!(
            view.check_spend(
                &other,
                &Spend {
                    amount: 500,
                    at_block: 10_500
                }
            ),
            Err(AllowanceError::TermsMismatch),
            "cannot spend under a forged higher ceiling"
        );
    }

    /// A non-positive spend amount is refused (a spend must move value; a zero or
    /// negative "spend" cannot be used to advance the epoch cursor for free).
    #[test]
    fn non_positive_spend_is_rejected() {
        let terms = sample_terms();
        let mut cell = allowance_cell();
        open_allowance(&mut cell, &terms).unwrap();
        let view = AllowanceState::read(&cell).unwrap();
        assert_eq!(
            view.check_spend(
                &terms,
                &Spend {
                    amount: 0,
                    at_block: 10_500
                }
            ),
            Err(AllowanceError::NonPositiveAmount { amount: 0 })
        );
        assert_eq!(
            view.check_spend(
                &terms,
                &Spend {
                    amount: -5,
                    at_block: 10_500
                }
            ),
            Err(AllowanceError::NonPositiveAmount { amount: -5 })
        );
    }

    /// Opening ill-formed terms is refused (non-positive ceiling or epoch length).
    #[test]
    fn ill_formed_terms_are_rejected() {
        let mut cell = allowance_cell();
        assert_eq!(
            open_allowance(
                &mut cell,
                &AllowanceTerms::new(cid(1), cid(9), 0, 1000, 10_000)
            ),
            Err(AllowanceError::IllFormedTerms),
            "zero ceiling is ill-formed"
        );
        assert_eq!(
            open_allowance(
                &mut cell,
                &AllowanceTerms::new(cid(1), cid(9), 100, 0, 10_000)
            ),
            Err(AllowanceError::IllFormedTerms),
            "zero epoch length is ill-formed"
        );
    }

    /// `read`/`check_spend` on a non-allowance cell reports NotAnAllowance.
    #[test]
    fn non_allowance_cell_is_rejected() {
        let cell = allowance_cell();
        assert_eq!(
            AllowanceState::read(&cell),
            Err(AllowanceError::NotAnAllowance)
        );
    }

    /// `epoch_of` is the schedule's ground truth: 0 before start, then one more
    /// per elapsed epoch length.
    #[test]
    fn epoch_of_is_correct() {
        let terms = sample_terms(); // start 10_000, epoch_length 1000
        assert_eq!(
            terms.epoch_of(9_999),
            0,
            "before start is epoch 0 pre-history"
        );
        assert_eq!(terms.epoch_of(10_000), 0, "epoch 0 begins exactly at start");
        assert_eq!(
            terms.epoch_of(10_999),
            0,
            "still epoch 0 just before the boundary"
        );
        assert_eq!(
            terms.epoch_of(11_000),
            1,
            "epoch 1 begins at start + epoch_length"
        );
        assert_eq!(terms.epoch_of(12_500), 2, "epoch 2 at start + 2.5 epochs");
    }

    /// The i64 encode/decode round-trips, including negatives.
    #[test]
    fn amount_encoding_roundtrips() {
        for v in [0i64, 1, -1, 100, 1000, i64::MAX, i64::MIN] {
            assert_eq!(decode_i64(&encode_i64(v)), v);
        }
    }
}
