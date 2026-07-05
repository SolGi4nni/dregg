//! # hosted-lease — the hosting lease, dregg-native.
//!
//! The operated layer rents durable execution to agents. This crate is that lease built on
//! the proven [`starbridge_execution_lease`] capacity rather than a local struct:
//! the meter is a real [`StandingObligation`](dregg_cell::obligation_standing)
//! whose forge-detectors bite (no early / double / over / under / skipped
//! discharge), the durable execution image is the lease cell's committed umem
//! heap (`EXEC_COLL`), and the checkpoint cursor is `Monotonic` — a rewind or
//! forge of the durable image is a real refusal the executor re-enforces.
//!
//! [`HostedLease`] is the seam a hosted runtime binds to. A Hermes/webcell
//! runtime reads the lease's durable image, runs the agent's code, and calls
//! [`HostedLease::checkpoint`] to advance the cursor with the new state digest and
//! whatever working memory the run produced — so the durable state survives, is
//! passable (a cell + its heap is a portable image), and is witnessed (a light
//! client sees the checkpoint cursor move). The rent is [`HostedLease::meter`] a
//! period (the amount a conserving `Transfer` must move to the provider) plus the
//! lapse audit that reclaims a delinquent slot.

use dregg_cell::Cell;

pub use starbridge_execution_lease::{
    EXEC_COLL, FieldElement, KEY_DIGEST, KEY_STEP, LeaseError, LeaseTerms, WORKING_BASE,
    advance_checkpoint, checkpoint_step, field_from_u64, is_lapsed, lapse_if_behind, mark_lapsed,
    meter_period, open_durable_image, open_lease,
};

// THE FUSED METER: the proven `dregg_cell::prepaid_lease` capacity (escrow ⊗
// obligation in ONE atomic discharge, Lean rung `PrepaidLease.lean`). A hosted
// lease can ride this INSTEAD of the obligation meter so metering (the cursor
// advance) and the reserve draw are a single write — drift-unrepresentable. The
// prepaid names are re-exported (aliased, since `LeaseError`/`LeaseTerms` already
// name the execution-lease ones) for callers building the fused path.
pub use dregg_cell::prepaid_lease;
pub use dregg_cell::prepaid_lease::{
    DischargePeriod, LeaseError as PrepaidLeaseError, LeaseState as PrepaidLeaseState,
    LeaseTerms as PrepaidLeaseTerms,
};

/// **How a hosted lease meters and draws its rent.** ADDITIVE: the [`Obligation`]
/// path is byte-compatible for existing holders (grain-fork) — a
/// [`StandingObligation`](dregg_cell::obligation_standing) cursor metered per
/// period, PAID by a separate settlement draw (meter and pay are two enforced
/// pieces coupled by app control flow). The [`Prepaid`] path FUSES them: the
/// [`dregg_cell::prepaid_lease`] capacity draws rent from a sealed reserve in the
/// SAME atomic write that advances the meter cursor, so meter/pay drift is a type
/// error, not a discipline.
///
/// [`Obligation`]: Metering::Obligation
/// [`Prepaid`]: Metering::Prepaid
pub enum Metering {
    /// The original StandingObligation meter + a separate settlement draw.
    Obligation,
    /// The FUSED prepaid meter: one atomic meter-advance ⊗ reserve-draw write. The
    /// carried terms are the sealed prepaid schedule + reserve.
    Prepaid(PrepaidLeaseTerms),
}

/// A durable-execution lease the operated layer hosts: the lease cell (rent obligor, payer,
/// and holder of the committed execution image) paired with its sealed terms and the
/// [`Metering`] that draws its rent.
///
/// `terms` is the obligation-shaped schedule view (provider/lease/asset/rent/
/// period/start/max), present for EVERY lease so [`terms()`](HostedLease::terms)
/// stays infallible for existing holders — for a [`Metering::Prepaid`] lease it is
/// the exec-shaped mirror of the prepaid schedule (same parties, rent, schedule).
/// The seam a hosted Hermes/webcell runtime binds to.
pub struct HostedLease {
    cell: Cell,
    terms: LeaseTerms,
    metering: Metering,
}

/// Project the exec-shaped [`LeaseTerms`] (the obligation schedule view) from a
/// fused [`PrepaidLeaseTerms`]: the prepaid `lessee` is the exec `lease` (obligor/
/// payer), the prepaid `lessor` is the exec `provider` (beneficiary). So
/// [`HostedLease::terms`] returns a consistent schedule view for BOTH meters.
fn exec_terms_of(prepaid: &PrepaidLeaseTerms) -> LeaseTerms {
    LeaseTerms::new(
        prepaid.lessor,
        prepaid.lessee,
        prepaid.asset,
        prepaid.rent.max(0) as u64,
        prepaid.period,
        prepaid.start,
        prepaid.count,
    )
}

impl HostedLease {
    /// Open a durable-execution lease on `cell` under `terms`, initialised to
    /// `genesis_digest` (the checkpoint of the agent's genesis execution image).
    /// Seals the rent obligation, pins the `WriteOnce` economics, and writes the
    /// genesis checkpoint into both the scalar slots and the committed heap.
    pub fn open(
        mut cell: Cell,
        terms: LeaseTerms,
        genesis_digest: FieldElement,
    ) -> Result<HostedLease, LeaseError> {
        open_lease(&mut cell, &terms, genesis_digest)?;
        Ok(HostedLease {
            cell,
            terms,
            metering: Metering::Obligation,
        })
    }

    /// **Open a lease on the FUSED prepaid meter** — the drift-unrepresentable twin
    /// of [`open`](HostedLease::open). Seals the [`EXEC_COLL`] durable-image genesis
    /// (via [`open_durable_image`], NO obligation meter) AND the
    /// [`prepaid_lease::open_lease`] fused meter+reserve (its own sealed schedule +
    /// prepaid budget in the disjoint `PREPAID_LEASE_COLL`). After this, rent is
    /// metered by [`check_bill`](HostedLease::check_bill) / [`discharge`](HostedLease::discharge)
    /// — the reserve draw and meter advance are one atomic write. Rejects
    /// ill-formed prepaid terms.
    pub fn open_prepaid(
        mut cell: Cell,
        prepaid_terms: PrepaidLeaseTerms,
        genesis_digest: FieldElement,
    ) -> Result<HostedLease, PrepaidLeaseError> {
        open_durable_image(&mut cell, genesis_digest);
        prepaid_lease::open_lease(&mut cell, &prepaid_terms)?;
        let terms = exec_terms_of(&prepaid_terms);
        Ok(HostedLease {
            cell,
            terms,
            metering: Metering::Prepaid(prepaid_terms),
        })
    }

    /// Meter one rent period: discharge the period on the standing obligation (the
    /// recurring forge-detectors bite) and return the rent amount a conserving
    /// `Transfer` must move from the lease to the provider. Does not itself move
    /// value — pair it with the platform's settlement (a real on-chain transfer).
    ///
    /// The OBLIGATION path only; a [`Metering::Prepaid`] lease meters through the
    /// fused [`discharge`](HostedLease::discharge) (which moves the reserve draw in
    /// the same write) — calling `meter` on it is a no-such-meter refusal, not a
    /// silent second cursor.
    pub fn meter(&mut self, period_index: i64, clock: i64) -> Result<u64, LeaseError> {
        meter_period(&mut self.cell, &self.terms, period_index, clock)
    }

    /// **Read-only bill gate for the fused prepaid meter** — the rent this period
    /// WILL draw, refusing off-schedule / replay / over-draw / exhausted-reserve
    /// (`InsufficientBudget`) BEFORE any value moves, via
    /// [`PrepaidLeaseState::check_discharge`]. The platform calls this FIRST, builds
    /// the settlement charge from the returned rent, settles, then
    /// [`discharge`](HostedLease::discharge)s — so a refused bill moves nothing.
    /// Refuses a lease that is not on the prepaid meter ([`PrepaidLeaseError::NotALease`]).
    pub fn check_bill(&self, period_index: i64, clock: i64) -> Result<i64, PrepaidLeaseError> {
        match &self.metering {
            Metering::Prepaid(pt) => {
                let state = PrepaidLeaseState::read(&self.cell)?;
                let step = DischargePeriod {
                    period_index,
                    amount: pt.rent,
                    clock,
                };
                state.check_discharge(pt, &step)
            }
            Metering::Obligation => Err(PrepaidLeaseError::NotALease),
        }
    }

    /// **Discharge one period on the fused prepaid meter** — the ONE atomic write
    /// that advances the meter cursor AND draws exactly the sealed rent from the
    /// prepaid reserve ([`prepaid_lease::discharge_period`]). Returns the drawn
    /// rent. Same forge-detectors as [`check_bill`](HostedLease::check_bill); on any
    /// refusal NOTHING is mutated (no half-metered period). Refuses a lease that is
    /// not on the prepaid meter.
    pub fn discharge(&mut self, period_index: i64, clock: i64) -> Result<i64, PrepaidLeaseError> {
        match &self.metering {
            Metering::Prepaid(pt) => {
                let pt = pt.clone();
                let step = DischargePeriod {
                    period_index,
                    amount: pt.rent,
                    clock,
                };
                prepaid_lease::discharge_period(&mut self.cell, &pt, &step)
            }
            Metering::Obligation => Err(PrepaidLeaseError::NotALease),
        }
    }

    /// Advance the durable execution image: move the checkpoint cursor forward,
    /// re-bind the state digest, and write the run's `working` memory (keys must be
    /// `>= WORKING_BASE`) into the committed image. Refuses on a lapsed lease. This
    /// is what a hosted runtime calls after a step of the agent's execution.
    pub fn checkpoint(
        &mut self,
        new_digest: FieldElement,
        working: &[(u32, FieldElement)],
    ) -> Result<u64, LeaseError> {
        advance_checkpoint(&mut self.cell, new_digest, working)
    }

    /// Lapse the lease if a rent period went undischarged by `clock` (the provider
    /// reclaims the slot; further delivery is refused). Returns whether it lapsed.
    ///
    /// On the OBLIGATION meter this audits the standing-obligation schedule. On the
    /// FUSED prepaid meter it audits the prepaid schedule
    /// ([`PrepaidLeaseState::audit`] → `BehindSchedule`) AND applies the reserve
    /// backstop (a dry reserve — the next rent no longer covered — also lapses),
    /// latching [`LAPSED_SLOT`](starbridge_execution_lease::LAPSED_SLOT) via
    /// [`mark_lapsed`] so [`is_lapsed`](HostedLease::is_lapsed) and the durable
    /// image agree (the same latch the obligation path sets).
    pub fn lapse_if_behind(&mut self, clock: i64) -> Result<bool, LeaseError> {
        match &self.metering {
            Metering::Obligation => lapse_if_behind(&mut self.cell, &self.terms, clock),
            Metering::Prepaid(pt) => {
                if is_lapsed(&self.cell) {
                    return Ok(true);
                }
                let pt = pt.clone();
                // No prepaid binding to audit ⇒ nothing to lapse (fail-open read).
                let Ok(state) = PrepaidLeaseState::read(&self.cell) else {
                    return Ok(false);
                };
                let behind = matches!(
                    state.audit(&pt, clock),
                    Err(PrepaidLeaseError::BehindSchedule { .. })
                );
                // The reserve backstop: a reserve that can no longer cover the next
                // rent is a lapse (the fused meter cannot advance past what was
                // prepaid — the same tooth `check_bill` returns `InsufficientBudget`
                // for, mirrored into the LAPSED latch).
                let reserve_dry = state.remaining_budget < pt.rent;
                if behind || reserve_dry {
                    mark_lapsed(&mut self.cell);
                    Ok(true)
                } else {
                    Ok(false)
                }
            }
        }
    }

    /// Whether the lease has lapsed (non-payment).
    pub fn is_lapsed(&self) -> bool {
        is_lapsed(&self.cell)
    }

    /// The current durable checkpoint step (how many times the execution image has
    /// advanced).
    pub fn step(&self) -> u64 {
        checkpoint_step(&self.cell)
    }

    /// Read a working-memory value from the durable execution image (a key the
    /// hosted runtime wrote via [`checkpoint`](HostedLease::checkpoint)).
    pub fn read_working(&self, key: u32) -> Option<FieldElement> {
        self.cell.state.get_heap(EXEC_COLL, key)
    }

    /// The lease's sealed terms — the obligation-shaped schedule view
    /// (provider/lease/asset/rent/period/start/max), present for BOTH meters (for a
    /// [`Metering::Prepaid`] lease it is the exec-shaped mirror of the prepaid
    /// schedule). Infallible for every existing holder.
    pub fn terms(&self) -> &LeaseTerms {
        &self.terms
    }

    /// The lease's [`Metering`] — whether rent is drawn via the byte-compatible
    /// obligation meter or the FUSED prepaid meter.
    pub fn metering(&self) -> &Metering {
        &self.metering
    }

    /// Borrow the underlying lease cell (for settlement / commitment / witnessing).
    pub fn cell(&self) -> &Cell {
        &self.cell
    }

    /// Mutably borrow the underlying lease cell — for a lifecycle layer that seals or
    /// advances its OWN state slots on the same cell (e.g. the vat lifecycle machine,
    /// slots disjoint from the lease's own `KEY_STEP`/`KEY_DIGEST`/working range). The
    /// caller is responsible for keeping the lease's economic slots intact; this does
    /// not re-open or re-meter the lease.
    pub fn cell_mut(&mut self) -> &mut Cell {
        &mut self.cell
    }

    /// Wrap an ALREADY-OPENED lease cell under `terms` — the constructor for a caller
    /// that opened the lease itself (e.g. via `starbridge_vat::lifecycle::open_vat`,
    /// which opens the lease AND seals the vat lifecycle in one pass), rather than
    /// through [`HostedLease::open`]. Does NOT call `open_lease`, so it never
    /// double-opens the (WriteOnce-sealed) economic slots.
    pub fn from_cell(cell: Cell, terms: LeaseTerms) -> HostedLease {
        HostedLease {
            cell,
            terms,
            metering: Metering::Obligation,
        }
    }

    /// Wrap an ALREADY-OPENED **fused prepaid** lease cell under `prepaid_terms` —
    /// the [`Metering::Prepaid`] twin of [`from_cell`](HostedLease::from_cell), for
    /// a caller that opened the durable image + the prepaid meter itself (e.g. via
    /// [`starbridge_vat::lifecycle::open_vat_prepaid`](https://docs.rs), which opens
    /// both AND seals the vat lifecycle in one pass). Does NOT re-open anything.
    pub fn from_cell_prepaid(cell: Cell, prepaid_terms: PrepaidLeaseTerms) -> HostedLease {
        let terms = exec_terms_of(&prepaid_terms);
        HostedLease {
            cell,
            terms,
            metering: Metering::Prepaid(prepaid_terms),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::{Cell, CellId};

    fn cid(n: u8) -> CellId {
        CellId::from_bytes([n; 32])
    }

    fn lease_cell() -> Cell {
        Cell::with_balance([7u8; 32], [9u8; 32], 10_000)
    }

    /// provider=2, lease=7, asset=9; rent 100 every 50 blocks from block 1000.
    fn terms() -> LeaseTerms {
        LeaseTerms::new(cid(2), cid(7), cid(9), 100, 50, 1000, 0)
    }

    #[test]
    fn the_dregg_native_lease_lifecycle_holds_end_to_end() {
        let mut lease = HostedLease::open(lease_cell(), terms(), field_from_u64(0xB0))
            .expect("open a well-formed lease");
        assert_eq!(lease.step(), 0);
        assert!(!lease.is_lapsed());

        // Meter period 0: the rent is the sealed 100.
        assert_eq!(lease.meter(0, 1000), Ok(100));
        // The recurring forge-detector bites a double-discharge of the same period.
        assert!(lease.meter(0, 1000).is_err());
        // And a not-yet-due future period.
        assert!(lease.meter(1, 1000).is_err());

        // The hosted runtime advances the durable image twice, writing working mem.
        let s1 = lease
            .checkpoint(field_from_u64(0xA1), &[(WORKING_BASE, field_from_u64(42))])
            .expect("advance the checkpoint");
        assert_eq!(s1, 1);
        assert_eq!(lease.read_working(WORKING_BASE), Some(field_from_u64(42)));
        let s2 = lease
            .checkpoint(field_from_u64(0xA2), &[])
            .expect("advance again");
        assert_eq!(s2, 2);

        // Non-payment past the next due block lapses the lease; delivery then stops.
        let lapsed = lease.lapse_if_behind(1100).expect("audit the schedule");
        assert!(lapsed);
        assert!(lease.is_lapsed());
        assert!(
            lease.checkpoint(field_from_u64(0xA3), &[]).is_err(),
            "a lapsed lease refuses further delivery"
        );
    }

    #[test]
    fn ill_formed_terms_are_refused() {
        let bad = LeaseTerms::new(cid(2), cid(7), cid(9), 0, 50, 1000, 0);
        assert!(HostedLease::open(lease_cell(), bad, field_from_u64(0)).is_err());
    }

    // ── the FUSED prepaid meter ───────────────────────────────────────────────

    /// lessee=7 (the lease cell), lessor=2 (provider), asset=9; rent 100 every 50
    /// blocks from block 1000, unbounded, prepaid `budget`.
    fn prepaid_terms(budget: i64) -> PrepaidLeaseTerms {
        PrepaidLeaseTerms::new(cid(7), cid(2), cid(9), 100, 50, 1000, 0, budget)
    }

    /// **METER AND DRAW ARE ONE WRITE.** After N fused bills the reserve is exactly
    /// `budget − N·rent`, the drawn total is exactly `N·rent == discharged_count·rent`,
    /// and `remaining + drawn == budget` at every step — the cursor advance and the
    /// reserve draw cannot disagree because `discharge` is the single mutation.
    #[test]
    fn fused_bill_meters_and_draws_in_one_write() {
        let terms = prepaid_terms(300); // exactly three periods
        let mut lease =
            HostedLease::open_prepaid(lease_cell(), terms.clone(), field_from_u64(0xB0)).unwrap();

        for k in 0..3i64 {
            let clk = 1000 + k * 50;
            // read-only gate returns the rent it WILL draw.
            assert_eq!(lease.check_bill(k, clk), Ok(100));
            // the fused write draws exactly that rent AND advances the cursor.
            assert_eq!(lease.discharge(k, clk), Ok(100));
            let n = k + 1;
            let view = PrepaidLeaseState::read(lease.cell()).unwrap();
            assert_eq!(
                view.remaining_budget,
                300 - n * 100,
                "reserve == budget − n·rent"
            );
            assert_eq!(view.drawn_total, n * 100, "drawn == n·rent");
            assert_eq!(
                view.drawn_total,
                view.discharged_count * 100,
                "drawn == discharged_count·rent (meter == draw)"
            );
            assert_eq!(view.remaining_budget + view.drawn_total, 300, "Σδ = 0");
        }
    }

    /// **The reserve backstop biting in `check_bill`, BEFORE any draw.** With the
    /// reserve exhausted the fourth bill is refused `InsufficientBudget` by the
    /// read-only gate — and the mutating `discharge` refuses too, leaving the meter
    /// un-advanced (drift is unrepresentable: no metered-but-unpaid period).
    #[test]
    fn a_bill_past_the_reserve_is_refused_and_the_meter_does_not_advance() {
        let terms = prepaid_terms(200); // exactly two periods
        let mut lease = HostedLease::open_prepaid(lease_cell(), terms, field_from_u64(0)).unwrap();
        assert_eq!(lease.discharge(0, 1000), Ok(100));
        assert_eq!(lease.discharge(1, 1050), Ok(100));
        // The reserve is dry; the on-schedule period 2 is refused by the gate.
        assert_eq!(
            lease.check_bill(2, 1100),
            Err(PrepaidLeaseError::InsufficientBudget {
                remaining: 0,
                rent: 100
            })
        );
        // The mutating path refuses identically, meter un-advanced.
        assert_eq!(
            lease.discharge(2, 1100),
            Err(PrepaidLeaseError::InsufficientBudget {
                remaining: 0,
                rent: 100
            })
        );
        assert_eq!(
            PrepaidLeaseState::read(lease.cell())
                .unwrap()
                .discharged_count,
            2,
            "the meter did not advance past the reserve"
        );
    }

    /// **Re-billing a discharged period is `WrongPeriod`** (the one-shot meter): the
    /// cursor advanced, so a replay of period 0 is refused with no second draw.
    #[test]
    fn re_billing_a_period_is_wrong_period() {
        let terms = prepaid_terms(300);
        let mut lease = HostedLease::open_prepaid(lease_cell(), terms, field_from_u64(0)).unwrap();
        assert_eq!(lease.discharge(0, 1000), Ok(100));
        assert_eq!(
            lease.check_bill(0, 1000),
            Err(PrepaidLeaseError::WrongPeriod {
                expected: 1,
                presented: 0
            })
        );
        assert_eq!(
            PrepaidLeaseState::read(lease.cell()).unwrap().drawn_total,
            100,
            "no double-draw"
        );
    }

    /// **An off-schedule bill is `NotYetDue`** with nothing drawn: period 0 due at
    /// 1000, a bill at clock 999 is refused by the gate.
    #[test]
    fn an_off_schedule_bill_is_not_yet_due() {
        let terms = prepaid_terms(300);
        let lease = HostedLease::open_prepaid(lease_cell(), terms, field_from_u64(0)).unwrap();
        assert_eq!(
            lease.check_bill(0, 999),
            Err(PrepaidLeaseError::NotYetDue {
                due_block: 1000,
                clock: 999
            })
        );
        // On-time at 1000 WOULD accept (non-vacuity).
        assert_eq!(lease.check_bill(0, 1000), Ok(100));
    }

    /// **The durable image still binds a session over `EXEC_COLL` on a prepaid
    /// lease** — checkpoint/read_working/step are the disjoint durable-image half,
    /// unchanged by the fused meter (the three collections coexist).
    #[test]
    fn checkpoint_binds_over_exec_coll_on_a_prepaid_lease() {
        let terms = prepaid_terms(300);
        let mut lease = HostedLease::open_prepaid(lease_cell(), terms, field_from_u64(0)).unwrap();
        assert_eq!(lease.step(), 0);
        let s1 = lease
            .checkpoint(field_from_u64(0xA1), &[(WORKING_BASE, field_from_u64(42))])
            .expect("advance the durable image on a prepaid lease");
        assert_eq!(s1, 1);
        assert_eq!(lease.read_working(WORKING_BASE), Some(field_from_u64(42)));
        // A bill on the (disjoint) prepaid meter does not disturb the image cursor.
        assert_eq!(lease.discharge(0, 1000), Ok(100));
        assert_eq!(
            lease.step(),
            1,
            "the prepaid draw did not move the image cursor"
        );
    }

    /// **A behind-schedule prepaid lease lapses via the prepaid audit path**, and a
    /// drained-reserve lease lapses via the reserve backstop — both latch LAPSED so
    /// `is_lapsed` and further delivery agree.
    #[test]
    fn a_prepaid_lease_lapses_behind_schedule_and_on_a_dry_reserve() {
        // behind schedule: never billed, clock runs past due.
        let mut behind =
            HostedLease::open_prepaid(lease_cell(), prepaid_terms(300), field_from_u64(0)).unwrap();
        assert!(!behind.is_lapsed());
        assert_eq!(
            behind.lapse_if_behind(1100),
            Ok(true),
            "behind schedule lapses"
        );
        assert!(behind.is_lapsed());
        assert!(
            behind.checkpoint(field_from_u64(9), &[]).is_err(),
            "a lapsed prepaid lease refuses further delivery"
        );

        // reserve dry: paid up on schedule but the reserve is exhausted.
        let mut dry =
            HostedLease::open_prepaid(lease_cell(), prepaid_terms(200), field_from_u64(0)).unwrap();
        assert_eq!(dry.discharge(0, 1000), Ok(100));
        assert_eq!(dry.discharge(1, 1050), Ok(100));
        // At clock 1050 the schedule wants 2 periods and 2 are paid — NOT behind —
        // but the reserve is dry, so the backstop lapses it.
        assert_eq!(dry.lapse_if_behind(1050), Ok(true), "a dry reserve lapses");
        assert!(dry.is_lapsed());
    }
}
