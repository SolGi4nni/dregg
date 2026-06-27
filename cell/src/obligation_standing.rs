//! Standing (recurring) obligation — a first-class, schedule-enforced commitment
//! that a cell OWES a fixed amount to a beneficiary every PERIOD blocks.
//!
//! # The capacity (Track 2)
//!
//! An autonomous agent living inside dregg needs to carry *standing* duties:
//! rent, a subscription, a periodic payment, a recurring tithe. Unlike a
//! one-shot bonded obligation (the deadline-and-slash
//! [`crate::blueprint::ObligationTerms`]), a STANDING obligation is *recurring* —
//! it owes `amount` at block `start`, again at `start + period`, again at
//! `start + 2·period`, and so on, forever (or until a bounded count). The danger
//! the agent must be protected from is twofold and symmetric:
//!
//!  * the obligor (or a malicious bookkeeper) **silently SKIPPING** a due
//!    period — claiming "all paid up" while a period went undischarged; and
//!  * a **FORGED discharge** — claiming a period was paid early (before it came
//!    due), paid twice (double-discharge), or paid more/less than committed.
//!
//! A standing obligation closes both: the schedule (`amount`, `period`, `start`,
//! `beneficiary`, `obligor`) is sealed into the cell's commitment, and a
//! `discharge` step is **one-shot per period** and **monotone in the cursor** —
//! it advances a committed `next_due` cursor by exactly one period, can only run
//! once the schedule clock has reached the current due block, and writes the
//! discharged amount into the committed ledger. A holder of the commitment can
//! tell, for any block height, exactly how many periods MUST have been
//! discharged — so a skip is detectable and a forge diverges from the commitment.
//!
//! # The weld (what already existed, disconnected)
//!
//! This is built, not memoed — it welds onto substrate already in the tree, the
//! same vehicles [`crate::escrow_sealed`] and [`crate::derived`] use:
//!
//!  * **The committed heap** ([`crate::state::CellState::set_heap`] /
//!    [`crate::state::compute_heap_root`]) is an openable sorted-Poseidon2
//!    `(collection, key) → FieldElement` map ALREADY folded into the canonical
//!    state commitment. We reserve a collection id ([`OBLIGATION_COLL`]) for the
//!    standing-obligation ledger: the schedule digest, the `next_due` cursor, the
//!    count of discharged periods, and the cumulative discharged amount all live
//!    there — bound into the cell's commitment FOR FREE, no commitment-version
//!    bump.
//!
//!  * **The signed `i64` balance ledger** is the value primitive: each discharge
//!    moves `amount` (exactly the quantity [`crate::state::CellState::balance`]
//!    carries) and records it in the committed cumulative.
//!
//!  * **Block height / a monotone counter** is the schedule clock: the due block
//!    for period `k` is `start + k·period`, and a discharge is admissible only
//!    when the presented clock has reached the current due block.
//!
//!  * **The nullifier / one-shot discipline** (the escrow leg-consumed tooth) is
//!    the shape the per-period cursor takes: a discharge for period `k` is
//!    admissible only when `next_due == start + k·period`, and it advances the
//!    cursor to `start + (k+1)·period`. A second discharge of period `k` finds
//!    the cursor already past it and is REFUSED — a spent period is a spent
//!    nullifier.
//!
//! # The soundness story (what binds the schedule)
//!
//! A standing obligation is an [`ObligationTerms`] (`obligor`, `beneficiary`,
//! `asset`, `amount`, `period`, `start`, optional bounded `count`) whose digest
//! is sealed at [`KEY_TERMS_DIGEST`], plus three committed cursors. The binding
//! enforces, against a holder of the commitment + heap openings:
//!
//! 1. **No early/forged discharge.** A discharge for the current period requires
//!    the presented schedule clock to have reached that period's due block
//!    (`start + k·period`). A discharge presented before due is REJECTED.
//! 2. **No double-discharge (one-shot per period).** The `next_due` cursor moves
//!    forward by exactly one period on each discharge. A second discharge of an
//!    already-discharged period finds the cursor advanced and is REJECTED.
//! 3. **No over-discharge.** The discharged amount must equal the schedule's
//!    committed `amount`. A discharge asserting more (or less) than the sealed
//!    amount diverges from the commitment and is REJECTED.
//! 4. **No silent skip / staleness forge.** [`ObligationState::audit`] computes,
//!    from the schedule and a presented clock, how many periods MUST have been
//!    discharged by now, and checks the committed `count`/cursor reflect it. A
//!    cell claiming "all met" whose committed cursor lags the schedule is
//!    REJECTED — the same `audit` the honest path satisfies.
//!
//! The honest-accept path ([`discharge`] accepting) and every forge-reject path
//! run through the SAME [`ObligationState::check_discharge`] /
//! [`ObligationState::audit`] verification core, so a stub in either direction
//! fails one polarity (non-vacuity by construction).
//!
//! # The minimal genuine slice (this module)
//!
//! - A single fixed-amount, fixed-period standing obligation with an optional
//!   bounded count. Variable amounts, grace windows, partial discharges, and
//!   multi-beneficiary splits are the named next slice, not stubs here.
//!
//! # The next slice (named, not built here)
//!
//! The executor-level check here is the genuine forge-rejection. The remaining
//! slice is the **in-circuit witness**: a light client verifying a *batch*
//! should see the schedule-discharge invariant enforced by the EffectVM circuit
//! rather than an out-of-band executor check. That requires (a) a
//! `DischargeObligation` effect descriptor whose gate binds
//! "due ∧ not-yet-discharged ⟹ discharged ∧ cursor advanced by one period" into
//! the commitment, and (b) the Lean rung
//! `verifyBatch accept ⟹ obligation honored on schedule` joining the
//! circuit-soundness obligation table in
//! `docs/CIRCUIT-FUNCTIONAL-CORRECTNESS.md`. See
//! `docs/deos/STANDING-OBLIGATION.md` §"Next slice: circuit binding".

use serde::{Deserialize, Serialize};

use crate::cell::Cell;
use crate::id::CellId;
use crate::state::FieldElement;

/// Reserved heap collection id for the standing-obligation ledger. Lives inside
/// the cell's committed heap (so the whole obligation is folded into the
/// canonical state commitment). Chosen high to avoid colliding with application
/// heap collections, in the same spirit as [`crate::escrow_sealed::ESCROW_COLL`].
pub const OBLIGATION_COLL: u32 = 0x000B_116A_u32; // a fixed reserved id ("oBLIGAtion")

/// Heap key holding the 32-byte digest of the obligation's [`ObligationTerms`].
/// Binds *which* schedule this cell owes.
pub const KEY_TERMS_DIGEST: u32 = 0;
/// Heap key: the `next_due` cursor — the block height at which the NEXT
/// undischarged period falls due (canonical little-endian `i64`). Starts at
/// `terms.start`; each discharge advances it by `terms.period`.
pub const KEY_NEXT_DUE: u32 = 1;
/// Heap key: the count of periods discharged so far (canonical little-endian
/// `i64`). Starts at `0`; each discharge increments it by `1`.
pub const KEY_DISCHARGED_COUNT: u32 = 2;
/// Heap key: the cumulative discharged amount (canonical little-endian `i64`).
/// Starts at `0`; each discharge adds `terms.amount`. The committed running
/// total a beneficiary can audit against the schedule.
pub const KEY_DISCHARGED_TOTAL: u32 = 3;

/// Encode an `i64` as a 32-byte heap [`FieldElement`] (little-endian, low 8
/// bytes). Round-trips with [`decode_i64`].
pub fn encode_i64(value: i64) -> FieldElement {
    let mut f = [0u8; 32];
    f[0..8].copy_from_slice(&value.to_le_bytes());
    f
}

/// Decode a heap field back to the `i64` it encodes (low 8 bytes).
pub fn decode_i64(f: &FieldElement) -> i64 {
    let mut buf = [0u8; 8];
    buf.copy_from_slice(&f[0..8]);
    i64::from_le_bytes(buf)
}

/// The sealed terms of a standing obligation: who owes, to whom, in what asset,
/// how much per period, the period length in blocks, the first due block, and an
/// optional bounded count of periods (`0` = unbounded). The digest of these
/// terms is bound into the cell's commitment, so the obligor and beneficiary
/// cannot disagree about what was owed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObligationTerms {
    /// The cell that OWES (and from whose balance each discharge is drawn).
    pub obligor: CellId,
    /// The cell that is OWED (the recipient of each discharge).
    pub beneficiary: CellId,
    /// The asset each discharge is denominated in.
    pub asset: CellId,
    /// The amount owed each period. Must be `> 0`.
    pub amount: i64,
    /// The period length in blocks. Must be `> 0` — period `k` falls due at
    /// `start + k·period`.
    pub period: i64,
    /// The block height at which period `0` falls due (the first discharge).
    pub start: i64,
    /// The bounded number of periods this obligation runs, or `0` for unbounded.
    /// When bounded, a discharge of period `>= count` is REJECTED.
    pub count: i64,
}

impl ObligationTerms {
    /// A standing obligation: `obligor` owes `amount` of `asset` to
    /// `beneficiary` every `period` blocks, starting at block `start`, for
    /// `count` periods (`0` = unbounded).
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        obligor: CellId,
        beneficiary: CellId,
        asset: CellId,
        amount: i64,
        period: i64,
        start: i64,
        count: i64,
    ) -> Self {
        ObligationTerms {
            obligor,
            beneficiary,
            asset,
            amount,
            period,
            start,
            count,
        }
    }

    /// Whether these terms are internally well-formed (positive amount/period,
    /// non-negative start/count). Ill-formed terms cannot be opened.
    pub fn is_well_formed(&self) -> bool {
        self.amount > 0 && self.period > 0 && self.start >= 0 && self.count >= 0
    }

    /// The block height at which period `k` (0-indexed) falls due.
    pub fn due_block(&self, k: i64) -> i64 {
        self.start.saturating_add(k.saturating_mul(self.period))
    }

    /// How many periods MUST have been discharged by the time the schedule clock
    /// reaches `clock` — i.e. how many due blocks `<= clock` have passed (capped
    /// at a bounded `count`). This is the schedule's ground truth that the
    /// committed cursor is audited against: a committed `discharged_count` below
    /// this at `clock` is a SILENT SKIP.
    pub fn periods_due_by(&self, clock: i64) -> i64 {
        if clock < self.start {
            return 0;
        }
        // number of k>=0 with start + k*period <= clock  ==  (clock-start)/period + 1
        let elapsed = clock - self.start;
        let due = elapsed / self.period + 1;
        if self.count > 0 && due > self.count {
            self.count
        } else {
            due
        }
    }

    /// A 32-byte canonical digest of the terms. Domain-separated so it can never
    /// collide with any other heap value's preimage. This is what gets bound at
    /// [`KEY_TERMS_DIGEST`].
    pub fn digest(&self) -> FieldElement {
        let mut h = blake3::Hasher::new_derive_key("dregg.standing-obligation.terms.v1");
        h.update(self.obligor.as_bytes());
        h.update(self.beneficiary.as_bytes());
        h.update(self.asset.as_bytes());
        h.update(&self.amount.to_le_bytes());
        h.update(&self.period.to_le_bytes());
        h.update(&self.start.to_le_bytes());
        h.update(&self.count.to_le_bytes());
        *h.finalize().as_bytes()
    }
}

/// A discharge step presented to the verifier: the obligor asserts it is paying
/// period `period_index` worth `amount`, with the schedule clock at `clock`. The
/// verifier checks the step against the committed cursor and schedule WITHOUT
/// trusting any field of it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Discharge {
    /// Which period (0-indexed) the obligor asserts it is discharging. Must equal
    /// the committed cursor's current period — you cannot skip ahead or replay.
    pub period_index: i64,
    /// The amount the obligor asserts it is paying. Must equal the schedule's
    /// committed `amount` — over- or under-statement is rejected.
    pub amount: i64,
    /// The schedule clock (block height) at the moment of discharge. Must have
    /// reached the period's due block — an early discharge is rejected.
    pub clock: i64,
}

/// Why a standing-obligation operation was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ObligationError {
    /// The cell carries no standing-obligation binding (no terms digest).
    NotAnObligation,
    /// The supplied terms' digest does not match the one bound in the cell.
    TermsMismatch,
    /// The terms are not well-formed (non-positive amount/period, etc).
    IllFormedTerms,
    /// THE EARLY-DISCHARGE REJECTION: the schedule clock has not yet reached the
    /// period's due block.
    NotYetDue {
        /// The block at which the period falls due.
        due_block: i64,
        /// The presented clock, which is `< due_block`.
        clock: i64,
    },
    /// THE ONE-SHOT / SKIP REJECTION: the presented `period_index` is not the
    /// current period the cursor expects. (Replaying an already-discharged
    /// period, or jumping ahead of the cursor.)
    WrongPeriod {
        /// The period the cursor expects next.
        expected: i64,
        /// The period the discharge presented.
        presented: i64,
    },
    /// THE OVER/UNDER-DISCHARGE REJECTION: the discharged amount does not equal
    /// the schedule's committed amount.
    AmountMismatch {
        /// What the schedule committed to.
        owed: i64,
        /// What the discharge asserted.
        presented: i64,
    },
    /// The obligation is bounded and all `count` periods are already discharged;
    /// there is nothing further owed.
    Completed {
        /// The bounded count of periods.
        count: i64,
    },
    /// THE SILENT-SKIP / STALENESS REJECTION (the audit forge-detector): at the
    /// presented clock the committed `discharged_count` is below the number of
    /// periods the schedule says MUST be discharged by now.
    BehindSchedule {
        /// How many periods the schedule requires discharged by the audited clock.
        required: i64,
        /// How many the committed cursor actually reflects.
        committed: i64,
    },
}

impl std::fmt::Display for ObligationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ObligationError::NotAnObligation => {
                write!(f, "cell carries no standing-obligation binding")
            }
            ObligationError::TermsMismatch => {
                write!(f, "supplied terms do not match the bound obligation")
            }
            ObligationError::IllFormedTerms => write!(f, "obligation terms are not well-formed"),
            ObligationError::NotYetDue { due_block, clock } => {
                write!(
                    f,
                    "not yet due: period falls due at block {due_block}, clock is {clock}"
                )
            }
            ObligationError::WrongPeriod {
                expected,
                presented,
            } => {
                write!(
                    f,
                    "wrong period: cursor expects {expected}, discharge presented {presented}"
                )
            }
            ObligationError::AmountMismatch { owed, presented } => {
                write!(
                    f,
                    "amount mismatch: owed {owed}, discharge presented {presented}"
                )
            }
            ObligationError::Completed { count } => {
                write!(f, "obligation completed: all {count} periods discharged")
            }
            ObligationError::BehindSchedule {
                required,
                committed,
            } => {
                write!(
                    f,
                    "behind schedule: {required} periods due, only {committed} committed"
                )
            }
        }
    }
}

impl std::error::Error for ObligationError {}

/// A read-only view of a standing obligation's committed state, recovered from
/// the cell's heap. The single source of truth every verification path consults
/// — the honest accept and every forge reject run through THIS, so a stub in
/// either direction fails one polarity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObligationState {
    /// The bound terms digest.
    pub terms_digest: FieldElement,
    /// The committed `next_due` cursor (block height of the next undischarged
    /// period).
    pub next_due: i64,
    /// The committed count of periods discharged so far.
    pub discharged_count: i64,
    /// The committed cumulative discharged amount.
    pub discharged_total: i64,
}

impl ObligationState {
    /// Recover an obligation's committed state from a cell, or
    /// [`ObligationError::NotAnObligation`].
    pub fn read(cell: &Cell) -> Result<ObligationState, ObligationError> {
        let terms_digest = cell
            .state
            .get_heap(OBLIGATION_COLL, KEY_TERMS_DIGEST)
            .ok_or(ObligationError::NotAnObligation)?;
        let next_due = cell
            .state
            .get_heap(OBLIGATION_COLL, KEY_NEXT_DUE)
            .map(|f| decode_i64(&f))
            .unwrap_or(0);
        let discharged_count = cell
            .state
            .get_heap(OBLIGATION_COLL, KEY_DISCHARGED_COUNT)
            .map(|f| decode_i64(&f))
            .unwrap_or(0);
        let discharged_total = cell
            .state
            .get_heap(OBLIGATION_COLL, KEY_DISCHARGED_TOTAL)
            .map(|f| decode_i64(&f))
            .unwrap_or(0);
        Ok(ObligationState {
            terms_digest,
            next_due,
            discharged_count,
            discharged_total,
        })
    }

    /// **The discharge forge-detector.** Verify a [`Discharge`] against the
    /// committed obligation and the terms WITHOUT mutating anything. Returns the
    /// `amount` that will move (and the period being discharged) only when:
    ///
    /// - the presented terms match the committed digest;
    /// - the obligation is not already completed (bounded count exhausted);
    /// - the presented `period_index` is exactly the cursor's current period
    ///   (no replay, no skip — the one-shot tooth);
    /// - the presented `clock` has reached that period's due block (no early
    ///   discharge);
    /// - the presented `amount` equals the schedule's committed `amount` (no
    ///   over/under-discharge).
    pub fn check_discharge(
        &self,
        terms: &ObligationTerms,
        step: &Discharge,
    ) -> Result<i64, ObligationError> {
        if !terms.is_well_formed() {
            return Err(ObligationError::IllFormedTerms);
        }
        if self.terms_digest != terms.digest() {
            return Err(ObligationError::TermsMismatch);
        }
        // Which period does the committed cursor expect next? Derived from the
        // cursor, NOT taken on trust from the step. next_due == start + k*period.
        let expected_period = (self.next_due - terms.start) / terms.period;

        // Bounded-count completion: nothing further is owed.
        if terms.count > 0 && expected_period >= terms.count {
            return Err(ObligationError::Completed { count: terms.count });
        }
        // ONE-SHOT / NO-SKIP: the step must name exactly the cursor's period.
        if step.period_index != expected_period {
            return Err(ObligationError::WrongPeriod {
                expected: expected_period,
                presented: step.period_index,
            });
        }
        // NO EARLY DISCHARGE: the clock must have reached this period's due block.
        let due_block = terms.due_block(expected_period);
        if step.clock < due_block {
            return Err(ObligationError::NotYetDue {
                due_block,
                clock: step.clock,
            });
        }
        // NO OVER/UNDER-DISCHARGE: the amount must equal the committed schedule.
        if step.amount != terms.amount {
            return Err(ObligationError::AmountMismatch {
                owed: terms.amount,
                presented: step.amount,
            });
        }
        Ok(terms.amount)
    }

    /// **The silent-skip / staleness forge-detector.** At the audited `clock`,
    /// the schedule says [`ObligationTerms::periods_due_by`] periods MUST be
    /// discharged. This checks the committed `discharged_count` is not behind
    /// that — a cell claiming "all met" whose committed cursor lags the schedule
    /// is REJECTED. The same `audit` the honest, on-schedule cell satisfies.
    ///
    /// Returns `Ok(required)` (the number of periods that must be discharged by
    /// now) when the committed state is at-or-ahead of schedule.
    pub fn audit(&self, terms: &ObligationTerms, clock: i64) -> Result<i64, ObligationError> {
        if !terms.is_well_formed() {
            return Err(ObligationError::IllFormedTerms);
        }
        if self.terms_digest != terms.digest() {
            return Err(ObligationError::TermsMismatch);
        }
        let required = terms.periods_due_by(clock);
        if self.discharged_count < required {
            return Err(ObligationError::BehindSchedule {
                required,
                committed: self.discharged_count,
            });
        }
        Ok(required)
    }
}

/// **Open** a standing obligation on a cell: seal the terms digest and initialize
/// the cursor to the first due block, with zero periods discharged. After this
/// the cell's commitment binds the schedule; nothing is discharged yet. Rejects
/// ill-formed terms.
pub fn open_obligation(cell: &mut Cell, terms: &ObligationTerms) -> Result<(), ObligationError> {
    if !terms.is_well_formed() {
        return Err(ObligationError::IllFormedTerms);
    }
    let st = &mut cell.state;
    st.set_heap(OBLIGATION_COLL, KEY_TERMS_DIGEST, terms.digest());
    st.set_heap(OBLIGATION_COLL, KEY_NEXT_DUE, encode_i64(terms.start));
    st.set_heap(OBLIGATION_COLL, KEY_DISCHARGED_COUNT, encode_i64(0));
    st.set_heap(OBLIGATION_COLL, KEY_DISCHARGED_TOTAL, encode_i64(0));
    Ok(())
}

/// **Discharge** the current period: verify the step via
/// [`ObligationState::check_discharge`], then advance the committed cursor by one
/// period, increment the discharged count, and add the amount to the cumulative
/// total. One-shot per period: a second discharge of the same period finds the
/// cursor advanced and is REJECTED.
///
/// Returns the `amount` the caller (the executor) moves from obligor to
/// beneficiary. If `check_discharge` rejects, nothing is mutated.
pub fn discharge(
    cell: &mut Cell,
    terms: &ObligationTerms,
    step: &Discharge,
) -> Result<i64, ObligationError> {
    let view = ObligationState::read(cell)?;
    let moved = view.check_discharge(terms, step)?;
    let new_next_due = view.next_due.saturating_add(terms.period);
    let new_count = view.discharged_count.saturating_add(1);
    let new_total = view.discharged_total.saturating_add(moved);
    let st = &mut cell.state;
    st.set_heap(OBLIGATION_COLL, KEY_NEXT_DUE, encode_i64(new_next_due));
    st.set_heap(OBLIGATION_COLL, KEY_DISCHARGED_COUNT, encode_i64(new_count));
    st.set_heap(OBLIGATION_COLL, KEY_DISCHARGED_TOTAL, encode_i64(new_total));
    Ok(moved)
}

/// Whether a cell carries a standing-obligation binding (a terms digest in its
/// reserved heap collection). A plain cell returns `false`.
pub fn is_obligation(cell: &Cell) -> bool {
    cell.state
        .get_heap(OBLIGATION_COLL, KEY_TERMS_DIGEST)
        .is_some()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(n: u8) -> CellId {
        CellId::from_bytes([n; 32])
    }
    fn obligation_cell() -> Cell {
        // A plain cell to host the obligation ledger; its balance is irrelevant
        // to the heap binding the schedule.
        Cell::with_balance([7u8; 32], [7u8; 32], 0)
    }

    /// Obligor cell 1 owes 50 of asset 9 to beneficiary cell 2, every 100 blocks,
    /// starting at block 1000, unbounded.
    fn sample_terms() -> ObligationTerms {
        ObligationTerms::new(cid(1), cid(2), cid(9), 50, 100, 1000, 0)
    }

    /// THE HONEST PATH: an on-schedule discharge accepts, advances the cursor by
    /// one period, increments the count, and adds the amount. This MUST pass
    /// before any reject test is meaningful — the same `check_discharge` core
    /// gates both polarities.
    #[test]
    fn honest_on_schedule_discharge_accepts_and_advances() {
        let terms = sample_terms();
        let mut cell = obligation_cell();
        open_obligation(&mut cell, &terms).unwrap();
        assert!(is_obligation(&cell));

        // Period 0 falls due at block 1000. At clock 1000 it is due.
        let step0 = Discharge {
            period_index: 0,
            amount: 50,
            clock: 1000,
        };
        let moved =
            discharge(&mut cell, &terms, &step0).expect("on-schedule discharge must accept");
        assert_eq!(moved, 50);

        let view = ObligationState::read(&cell).unwrap();
        assert_eq!(view.next_due, 1100, "cursor advances by one period");
        assert_eq!(view.discharged_count, 1);
        assert_eq!(view.discharged_total, 50);

        // Period 1 falls due at 1100; at clock 1150 it is due.
        let step1 = Discharge {
            period_index: 1,
            amount: 50,
            clock: 1150,
        };
        assert_eq!(discharge(&mut cell, &terms, &step1), Ok(50));
        let view = ObligationState::read(&cell).unwrap();
        assert_eq!(view.next_due, 1200);
        assert_eq!(view.discharged_count, 2);
        assert_eq!(view.discharged_total, 100);
    }

    /// The whole obligation is bound into the canonical commitment: discharging a
    /// period changes the cell commitment (a light client sees the cursor move).
    /// This is WHY a forge cannot be hidden.
    #[test]
    fn obligation_state_is_bound_into_commitment() {
        let terms = sample_terms();
        let mut cell = obligation_cell();
        open_obligation(&mut cell, &terms).unwrap();
        let before = cell.state_commitment();
        discharge(
            &mut cell,
            &terms,
            &Discharge {
                period_index: 0,
                amount: 50,
                clock: 1000,
            },
        )
        .unwrap();
        let after = cell.state_commitment();
        assert_ne!(
            before, after,
            "discharging a period re-seals the commitment"
        );
    }

    // ── FORGE-DETECTOR 1: early / not-yet-due discharge ──────────────────────

    /// Discharging before the period's due block is rejected. Period 0 is due at
    /// 1000; a discharge at clock 999 is REFUSED — the same `check_discharge` the
    /// honest path passes at clock 1000.
    #[test]
    fn early_discharge_is_rejected() {
        let terms = sample_terms();
        let mut cell = obligation_cell();
        open_obligation(&mut cell, &terms).unwrap();

        let view = ObligationState::read(&cell).unwrap();
        // honest, on-time at 1000 WOULD accept (non-vacuity).
        assert_eq!(
            view.check_discharge(
                &terms,
                &Discharge {
                    period_index: 0,
                    amount: 50,
                    clock: 1000
                }
            ),
            Ok(50),
            "on-time discharge is live"
        );
        // one block early is refused.
        assert_eq!(
            view.check_discharge(
                &terms,
                &Discharge {
                    period_index: 0,
                    amount: 50,
                    clock: 999
                }
            ),
            Err(ObligationError::NotYetDue {
                due_block: 1000,
                clock: 999
            }),
            "cannot discharge before the due block"
        );
        // and the mutating path refuses too, leaving the cursor untouched.
        assert_eq!(
            discharge(
                &mut cell,
                &terms,
                &Discharge {
                    period_index: 0,
                    amount: 50,
                    clock: 999
                }
            ),
            Err(ObligationError::NotYetDue {
                due_block: 1000,
                clock: 999
            })
        );
        assert_eq!(ObligationState::read(&cell).unwrap().discharged_count, 0);
    }

    /// A forged jump-ahead: presenting period 1 while the cursor still expects
    /// period 0 (trying to discharge a future period whose block has passed but
    /// skipping the current one) is rejected at the cursor check.
    #[test]
    fn skip_ahead_period_is_rejected() {
        let terms = sample_terms();
        let mut cell = obligation_cell();
        open_obligation(&mut cell, &terms).unwrap();

        let view = ObligationState::read(&cell).unwrap();
        // clock is well past period 1's due block (1100), but cursor expects 0.
        assert_eq!(
            view.check_discharge(
                &terms,
                &Discharge {
                    period_index: 1,
                    amount: 50,
                    clock: 5000
                }
            ),
            Err(ObligationError::WrongPeriod {
                expected: 0,
                presented: 1
            }),
            "cannot skip the current period to discharge a later one"
        );
    }

    // ── FORGE-DETECTOR 2: double-discharge (one-shot) ────────────────────────

    /// After an honest discharge of period 0, a second discharge of period 0 is
    /// rejected: the cursor has advanced to expect period 1. The SAME core that
    /// accepted period 0 now refuses its replay.
    #[test]
    fn double_discharge_of_one_period_is_rejected() {
        let terms = sample_terms();
        let mut cell = obligation_cell();
        open_obligation(&mut cell, &terms).unwrap();

        // honest discharge of period 0.
        assert_eq!(
            discharge(
                &mut cell,
                &terms,
                &Discharge {
                    period_index: 0,
                    amount: 50,
                    clock: 1000
                }
            ),
            Ok(50)
        );

        // replay of period 0 — cursor now expects 1.
        let view = ObligationState::read(&cell).unwrap();
        assert_eq!(
            view.check_discharge(
                &terms,
                &Discharge {
                    period_index: 0,
                    amount: 50,
                    clock: 1000
                }
            ),
            Err(ObligationError::WrongPeriod {
                expected: 1,
                presented: 0
            }),
            "a discharged period cannot be discharged again (one-shot)"
        );
        // and the mutating replay path refuses too — total stays at one period.
        assert_eq!(
            discharge(
                &mut cell,
                &terms,
                &Discharge {
                    period_index: 0,
                    amount: 50,
                    clock: 1000
                }
            ),
            Err(ObligationError::WrongPeriod {
                expected: 1,
                presented: 0
            })
        );
        assert_eq!(ObligationState::read(&cell).unwrap().discharged_total, 50);
    }

    // ── FORGE-DETECTOR 3: over / under-discharge ─────────────────────────────

    /// A discharge asserting MORE than the committed amount is rejected. The
    /// schedule owes 50; a discharge of 9999 is REFUSED. (And under-statement is
    /// equally refused — the amount must equal the committed schedule.)
    #[test]
    fn over_or_under_discharge_is_rejected() {
        let terms = sample_terms();
        let mut cell = obligation_cell();
        open_obligation(&mut cell, &terms).unwrap();

        let view = ObligationState::read(&cell).unwrap();
        // honest exactly-50 accepts (non-vacuity).
        assert_eq!(
            view.check_discharge(
                &terms,
                &Discharge {
                    period_index: 0,
                    amount: 50,
                    clock: 1000
                }
            ),
            Ok(50)
        );
        // over-discharge.
        assert_eq!(
            view.check_discharge(
                &terms,
                &Discharge {
                    period_index: 0,
                    amount: 9_999,
                    clock: 1000
                }
            ),
            Err(ObligationError::AmountMismatch {
                owed: 50,
                presented: 9_999
            }),
            "cannot discharge more than the schedule owes"
        );
        // under-discharge.
        assert_eq!(
            view.check_discharge(
                &terms,
                &Discharge {
                    period_index: 0,
                    amount: 1,
                    clock: 1000
                }
            ),
            Err(ObligationError::AmountMismatch {
                owed: 50,
                presented: 1
            }),
            "cannot under-pay a period"
        );
    }

    // ── FORGE-DETECTOR 4: silent skip / staleness (the audit tooth) ──────────

    /// A cell that claims "all met" but whose committed cursor lags the schedule
    /// is REJECTED by `audit`. By block 1250, periods 0 (due 1000), 1 (due 1100),
    /// and 2 (due 1200) MUST be discharged — three periods. A cell that only
    /// discharged period 0 is BEHIND. The SAME `audit` an on-schedule cell passes.
    #[test]
    fn behind_schedule_silent_skip_is_rejected() {
        let terms = sample_terms();
        let mut cell = obligation_cell();
        open_obligation(&mut cell, &terms).unwrap();

        // discharge ONLY period 0, then let the clock run to 1250.
        discharge(
            &mut cell,
            &terms,
            &Discharge {
                period_index: 0,
                amount: 50,
                clock: 1000,
            },
        )
        .unwrap();

        let view = ObligationState::read(&cell).unwrap();
        // By block 1250 the schedule demands 3 periods discharged.
        assert_eq!(terms.periods_due_by(1250), 3);
        assert_eq!(
            view.audit(&terms, 1250),
            Err(ObligationError::BehindSchedule {
                required: 3,
                committed: 1
            }),
            "a cell that skipped periods 1 and 2 is behind schedule"
        );

        // An honest cell that discharged all three periods passes the SAME audit.
        let mut honest = obligation_cell();
        open_obligation(&mut honest, &terms).unwrap();
        discharge(
            &mut honest,
            &terms,
            &Discharge {
                period_index: 0,
                amount: 50,
                clock: 1000,
            },
        )
        .unwrap();
        discharge(
            &mut honest,
            &terms,
            &Discharge {
                period_index: 1,
                amount: 50,
                clock: 1100,
            },
        )
        .unwrap();
        discharge(
            &mut honest,
            &terms,
            &Discharge {
                period_index: 2,
                amount: 50,
                clock: 1200,
            },
        )
        .unwrap();
        let honest_view = ObligationState::read(&honest).unwrap();
        assert_eq!(
            honest_view.audit(&terms, 1250),
            Ok(3),
            "an on-schedule cell passes the audit"
        );
    }

    // ── additional teeth ─────────────────────────────────────────────────────

    /// A discharge presented against the WRONG terms is rejected at the terms
    /// digest (you cannot re-interpret an obligation under a different schedule).
    #[test]
    fn wrong_terms_is_rejected() {
        let terms = sample_terms();
        let mut cell = obligation_cell();
        open_obligation(&mut cell, &terms).unwrap();

        // same schedule but a different amount → different digest.
        let other = ObligationTerms::new(cid(1), cid(2), cid(9), 51, 100, 1000, 0);
        let view = ObligationState::read(&cell).unwrap();
        assert_eq!(
            view.check_discharge(
                &other,
                &Discharge {
                    period_index: 0,
                    amount: 51,
                    clock: 1000
                }
            ),
            Err(ObligationError::TermsMismatch)
        );
        assert_eq!(
            view.audit(&other, 1250),
            Err(ObligationError::TermsMismatch)
        );
    }

    /// A bounded obligation refuses a discharge past its count. A 2-period
    /// obligation accepts periods 0 and 1, then refuses period 2 as Completed.
    #[test]
    fn bounded_obligation_completes() {
        let terms = ObligationTerms::new(cid(1), cid(2), cid(9), 50, 100, 1000, 2);
        let mut cell = obligation_cell();
        open_obligation(&mut cell, &terms).unwrap();

        assert_eq!(
            discharge(
                &mut cell,
                &terms,
                &Discharge {
                    period_index: 0,
                    amount: 50,
                    clock: 1000
                }
            ),
            Ok(50)
        );
        assert_eq!(
            discharge(
                &mut cell,
                &terms,
                &Discharge {
                    period_index: 1,
                    amount: 50,
                    clock: 1100
                }
            ),
            Ok(50)
        );
        // period 2 is past the bounded count.
        assert_eq!(
            discharge(
                &mut cell,
                &terms,
                &Discharge {
                    period_index: 2,
                    amount: 50,
                    clock: 1200
                }
            ),
            Err(ObligationError::Completed { count: 2 })
        );
        // a bounded obligation that discharged all its periods is never "behind".
        assert_eq!(
            ObligationState::read(&cell).unwrap().audit(&terms, 9_999),
            Ok(2)
        );
    }

    /// `periods_due_by` is the schedule's ground truth: 0 before start, then one
    /// more per elapsed period, capped at a bounded count.
    #[test]
    fn periods_due_by_is_correct() {
        let terms = sample_terms(); // start 1000, period 100, unbounded
        assert_eq!(terms.periods_due_by(999), 0, "nothing due before start");
        assert_eq!(
            terms.periods_due_by(1000),
            1,
            "period 0 due exactly at start"
        );
        assert_eq!(
            terms.periods_due_by(1099),
            1,
            "still only period 0 just before period 1"
        );
        assert_eq!(terms.periods_due_by(1100), 2, "period 1 due at 1100");
        assert_eq!(terms.periods_due_by(1250), 3, "periods 0,1,2 due by 1250");

        let bounded = ObligationTerms::new(cid(1), cid(2), cid(9), 50, 100, 1000, 2);
        assert_eq!(
            bounded.periods_due_by(99_999),
            2,
            "capped at the bounded count"
        );
    }

    /// Opening ill-formed terms is refused (non-positive amount or period).
    #[test]
    fn ill_formed_terms_are_rejected() {
        let mut cell = obligation_cell();
        assert_eq!(
            open_obligation(
                &mut cell,
                &ObligationTerms::new(cid(1), cid(2), cid(9), 0, 100, 1000, 0)
            ),
            Err(ObligationError::IllFormedTerms),
            "zero amount is ill-formed"
        );
        assert_eq!(
            open_obligation(
                &mut cell,
                &ObligationTerms::new(cid(1), cid(2), cid(9), 50, 0, 1000, 0)
            ),
            Err(ObligationError::IllFormedTerms),
            "zero period is ill-formed"
        );
    }

    /// `read`/`check_discharge` on a non-obligation cell reports NotAnObligation.
    #[test]
    fn non_obligation_cell_is_rejected() {
        let cell = obligation_cell();
        assert_eq!(
            ObligationState::read(&cell),
            Err(ObligationError::NotAnObligation)
        );
    }

    /// The i64 encode/decode round-trips, including negatives.
    #[test]
    fn amount_encoding_roundtrips() {
        for v in [0i64, 1, -1, 50, 1000, i64::MAX, i64::MIN] {
            assert_eq!(decode_i64(&encode_i64(v)), v);
        }
    }

    /// **The Lean rung: this executor invariant is PROVEN, not just smoke-tested.**
    ///
    /// The recurring-discharge invariant enforced here — a period is discharged
    /// once-per-period, on-schedule, never early, never double, never over/under,
    /// never silently skipped — is the EXECUTOR image of the proven Lean rung
    /// `metatheory/Dregg2/Deos/StandingObligation.lean`, grounded BY REUSE of the
    /// committed-heap root (`Substrate.Heap.root_binds_get`) + the StrictMonotonic
    /// `next_due` cursor discipline (`cursor_strict_mono`, the same monotone-slot
    /// law the version/supply slots ride). This test mirrors that rung's `#guard`
    /// witnesses (owe 50 every 100 blocks from block 1000) so the Rust is checked
    /// against the proven statement:
    ///
    ///   * `opened_cursor` / `opened_discharge_accepts` — opening commits
    ///     `next_due = start`; a period-0 discharge of exactly 50 at clock 1000
    ///     accepts and advances the cursor strictly to 1100 (`cursor_strict_mono`),
    ///     moving the committed root (`forged_cursor_moves_root`);
    ///   * `replay_rejected` — a replay of period 0 is refused (the cursor now
    ///     expects period 1: the one-shot tooth);
    ///   * `early_discharge_rejected` — a discharge at clock 999 (due 1000) refused;
    ///   * `over_discharge_rejected` — amounts 9999 and 1 both refused;
    ///   * `behind_schedule_rejected` — by clock 1250 the schedule demands 3
    ///     periods; a cell that discharged only 1 is behind (audit refuses), while
    ///     an on-schedule cell passes the SAME audit.
    #[test]
    fn invariant_matches_lean_rung() {
        let terms = sample_terms(); // owe 50 / 100 blocks / start 1000 / unbounded

        // `opened_cursor` + `opened_discharge_accepts` + `cursor_strict_mono` +
        // `forged_cursor_moves_root`: opening commits next_due = start; the period-0
        // discharge accepts, advances the cursor strictly, and moves the root.
        let mut cell = obligation_cell();
        open_obligation(&mut cell, &terms).unwrap();
        assert_eq!(ObligationState::read(&cell).unwrap().next_due, 1000);
        let before = cell.state_commitment();
        assert_eq!(
            discharge(
                &mut cell,
                &terms,
                &Discharge {
                    period_index: 0,
                    amount: 50,
                    clock: 1000
                }
            ),
            Ok(50)
        );
        let after = cell.state_commitment();
        assert_ne!(
            before, after,
            "forged_cursor_moves_root: the cursor advance moves the root"
        );
        let view = ObligationState::read(&cell).unwrap();
        assert_eq!(view.next_due, 1100, "cursor_strict_mono: 1000 < 1100");
        assert_eq!(view.discharged_count, 1);

        // `replay_rejected`: a replay of period 0 is refused (cursor expects 1).
        assert_eq!(
            view.check_discharge(
                &terms,
                &Discharge {
                    period_index: 0,
                    amount: 50,
                    clock: 1000
                }
            ),
            Err(ObligationError::WrongPeriod {
                expected: 1,
                presented: 0
            })
        );

        // `early_discharge_rejected`: one block early (clock 999, due 1100 now).
        let mut fresh = obligation_cell();
        open_obligation(&mut fresh, &terms).unwrap();
        let fview = ObligationState::read(&fresh).unwrap();
        assert_eq!(
            fview.check_discharge(
                &terms,
                &Discharge {
                    period_index: 0,
                    amount: 50,
                    clock: 999
                }
            ),
            Err(ObligationError::NotYetDue {
                due_block: 1000,
                clock: 999
            })
        );

        // `over_discharge_rejected`: amounts 9999 and 1 both refused.
        assert!(matches!(
            fview.check_discharge(
                &terms,
                &Discharge {
                    period_index: 0,
                    amount: 9_999,
                    clock: 1000
                }
            ),
            Err(ObligationError::AmountMismatch {
                owed: 50,
                presented: 9_999
            })
        ));
        assert!(matches!(
            fview.check_discharge(
                &terms,
                &Discharge {
                    period_index: 0,
                    amount: 1,
                    clock: 1000
                }
            ),
            Err(ObligationError::AmountMismatch {
                owed: 50,
                presented: 1
            })
        ));

        // `behind_schedule_rejected`: by clock 1250 three periods are due; a cell
        // that discharged only period 0 is behind, while an on-schedule cell passes.
        assert_eq!(terms.periods_due_by(1250), 3);
        assert_eq!(
            view.audit(&terms, 1250),
            Err(ObligationError::BehindSchedule {
                required: 3,
                committed: 1
            })
        );
        let mut on_schedule = obligation_cell();
        open_obligation(&mut on_schedule, &terms).unwrap();
        for (k, clk) in [(0, 1000), (1, 1100), (2, 1200)] {
            discharge(
                &mut on_schedule,
                &terms,
                &Discharge {
                    period_index: k,
                    amount: 50,
                    clock: clk,
                },
            )
            .unwrap();
        }
        assert_eq!(
            ObligationState::read(&on_schedule)
                .unwrap()
                .audit(&terms, 1250),
            Ok(3)
        );
    }
}
