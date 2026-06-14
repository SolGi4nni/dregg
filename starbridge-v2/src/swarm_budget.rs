//! THE STINGRAY CEILING WELD (N9) — the swarm's *verified* shared budget.
//!
//! N1 gave the swarm a FLOOR budget model: a plain per-member conserved counter
//! (`spent`) with an optional `ceiling`, summed into a [`SwarmBudget`] aggregate
//! ([`crate::swarm::BudgetMeter`]). It is exact for a single-image swarm, but the
//! bound it offers — "the swarm spent at most B" — is a *summation the swarm
//! owns*, not a guarantee a verified primitive enforces. That is simbi's gap: a
//! UI counter, not a conservation bound.
//!
//! This module closes that gap by replacing the floor with a real
//! [`dregg_coord::StingrayCounter`] (`coord/src/budget.rs`) as the swarm's shared
//! budget — wired the way the SDK's `runtime.rs::set_budget_gate` attaches a
//! `BudgetSlice` to an executor: every dispatch DRAWS against the shared slice
//! BEFORE its turn runs, and a draw that would exceed the ceiling is REFUSED by
//! the counter's gate (`StingrayCounter::try_debit` → [`BudgetError::SliceExhausted`])
//! — fail-closed, not faked.
//!
//! # Why one silo (the single-image shared pool)
//!
//! The `StingrayCounter` is a Byzantine-tolerant *distributed* budget: it slices
//! an agent's balance across `n` silos so each can spend locally up to its slice
//! ceiling without coordination, with the sum of ceilings deliberately exceeding
//! the true balance (the overspend bounded by `f · ceiling`, reconciled at
//! rebalance). For a **single-image swarm** the honest topology is `n = 1`,
//! `f = 0` (the single-machine collapse, `docs/dregg4-vision`: the honest bounds
//! are distributed bounds; `n = 1` collapses them to the strong property). At
//! `f = 0` the slice-ceiling formula `balance · (f+1)/(2f+1)` is exactly `balance`,
//! so the ONE slice's ceiling IS the whole pool `B`, and `try_debit` refuses any
//! draw past `B`. The conservation invariant is then unconditional and tight:
//!
//! > `counter.total_spent()  ==  Σ (every member draw that committed)`   (CONSERVES)
//! > `counter.total_spent()  ≤   B`                                       (BOUNDED)
//!
//! Every swarm member draws against this ONE shared slice (the silo id is a fixed
//! pool tag, not a per-member silo — the pool is shared, which is the whole
//! point). So "could this swarm have cost more than `B`?" is answered by the
//! counter's own gate, PROVABLY, across N members — the depth lift from a UI
//! counter to a verified conservation bound.
//!
//! # The draw is metered-real and digest-identified
//!
//! A dispatch draws the executor's GENUINE `receipt.computrons_used` (the same
//! figure N1 summed), under a fresh BLAKE3 debit digest (the receipt hash — a
//! content-addressed, one-shot identifier, exactly the trustline draw gate's
//! anti-replay leg `BudgetSlice::try_debit_fresh`). Because the draw is the real
//! metered cost and the gate refuses past `B`, the bound is on the genuine cost,
//! enforced AT the seam.
//!
//! The ceiling check is done with [`StingrayCounter::try_debit`] in two phases:
//!   1. PRE-CHECK (`would_overspend`): before a member's turn runs, ask the
//!      counter whether drawing the dispatch's *prospective* cost would breach
//!      the slice. If so, REFUSE (no turn commits — fail-closed).
//!   2. SETTLE (`draw`): after the turn commits, draw the turn's *actual* metered
//!      cost against the slice (conservation: the counter now reflects exactly
//!      the committed spend).
//!
//! Phase 1 cannot under-charge the gate (the prospective cost is the post-commit
//! cost in a deterministic metered world — see the swarm tests), and phase 2 is
//! the conservation tooth: `total_spent()` equals the sum of drawn metered costs.

use dregg_cell::CellId;
use dregg_coord::{BudgetError, BudgetSlice, StingrayCounter};

/// The fixed pool tag — the single silo id the whole swarm's shared slice lives
/// under (`n = 1`, the single-image shared pool). It is NOT a per-member silo:
/// every member draws against this ONE slice, which is what makes the bound a
/// SHARED pool rather than N independent floors.
pub const SWARM_POOL_SILO: [u8; 32] = [0x5Au8; 32];

/// Why a Stingray draw was refused. A thin, swarm-legible projection of the
/// counter's [`BudgetError`] (the only refusal a single-silo, single-image pool
/// can produce from a draw is a slice exhaustion or — defensively — an unknown
/// silo / duplicate digest).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StingrayDrawError {
    /// THE CEILING FIRING — the shared pool's slice cannot cover the draw. The
    /// `remaining` headroom and the `requested` amount are the counter's own
    /// figures (fail-closed: the counter is UNMOVED — `try_debit` refuses before
    /// touching `spent`). This is the verified conservation bound biting AT the
    /// seam, not a best-effort UI check.
    PoolExhausted { remaining: u64, requested: u64 },
    /// A draw digest was replayed against the shared slice — the one-shot
    /// anti-replay leg (`BudgetSlice::try_debit_fresh`). The counter is unmoved.
    /// (Defensive: the swarm draws under fresh receipt-hash digests, so this
    /// fires only if a caller reuses a digest.)
    DuplicateDraw { digest: [u8; 32] },
    /// The shared slice is missing (the pool was constructed without its silo) —
    /// a construction bug, surfaced rather than panicked.
    PoolMissing,
    /// Any other counter error, carried verbatim (the counter is the authority).
    Counter(BudgetError),
}

impl StingrayDrawError {
    fn from_counter(e: BudgetError) -> Self {
        match e {
            BudgetError::SliceExhausted { remaining, requested, .. } => {
                StingrayDrawError::PoolExhausted { remaining, requested }
            }
            BudgetError::DuplicateDebit { digest } => StingrayDrawError::DuplicateDraw { digest },
            BudgetError::UnknownSilo { .. } => StingrayDrawError::PoolMissing,
            other => StingrayDrawError::Counter(other),
        }
    }

    /// A short operator-legible label.
    pub fn label(&self) -> String {
        match self {
            StingrayDrawError::PoolExhausted { remaining, requested } => format!(
                "REFUSED — shared pool exhausted (draw {requested} > remaining {remaining}; the conservation bound bit)"
            ),
            StingrayDrawError::DuplicateDraw { digest } => format!(
                "REFUSED — draw digest replayed (0x{}…)",
                hex::encode(&digest[..4])
            ),
            StingrayDrawError::PoolMissing => "REFUSED — shared pool slice missing".to_string(),
            StingrayDrawError::Counter(e) => format!("REFUSED — counter: {e}"),
        }
    }
}

/// THE SWARM'S VERIFIED SHARED BUDGET — a real [`dregg_coord::StingrayCounter`]
/// owning the swarm's pool, wired as a single-image shared slice (`n = 1`,
/// `f = 0`). Every member draws against the ONE slice; `total_spent()` conserves
/// (== Σ drawn metered costs) and is bounded by the ceiling `B` (a draw past `B`
/// is refused by the gate). This is the N9 depth lift over N1's floor model.
#[derive(Clone, Debug)]
pub struct StingraySwarmBudget {
    /// The real conserved counter (the verified primitive). The shared slice
    /// lives at [`SWARM_POOL_SILO`].
    counter: StingrayCounter,
    /// The pool ceiling `B` (the slice ceiling at `f = 0` — the whole pool).
    ceiling: u64,
}

impl StingraySwarmBudget {
    /// Open a shared budget pool of `ceiling` computrons, owned by `agent` (the
    /// swarm coordinator cell — the agent whose budget the pool slices). The pool
    /// is ONE shared slice (`n = 1`, `f = 0`): the slice ceiling IS `ceiling`, and
    /// every member draws against it.
    ///
    /// Panics only on the impossible: `StingrayCounter::new` requires
    /// `silos.len() ≥ 3·f + 1`; with one silo and `f = 0` that is `1 ≥ 1`, always
    /// satisfied — so the `expect` cannot fire.
    pub fn open(agent: CellId, ceiling: u64) -> Self {
        let counter = StingrayCounter::new(agent, ceiling, vec![SWARM_POOL_SILO], 0)
            .expect("one silo at f=0 always satisfies n ≥ 3f+1 = 1");
        StingraySwarmBudget { counter, ceiling }
    }

    /// The pool ceiling `B` — the verified upper bound on `total_drawn`.
    pub fn ceiling(&self) -> u64 {
        self.ceiling
    }

    /// THE CONSERVED TOTAL — the sum of every committed draw, read straight from
    /// the counter (`StingrayCounter::total_spent`). This IS the conservation
    /// face: it equals `Σ (drawn metered costs)` by the counter's own accounting,
    /// never a re-derived estimate.
    pub fn total_drawn(&self) -> u64 {
        self.counter.total_spent()
    }

    /// The pool's remaining headroom under the ceiling (`B − total_drawn`,
    /// saturating at 0) — the counter's own `remaining` on the shared slice.
    pub fn remaining(&self) -> u64 {
        self.counter.remaining(&SWARM_POOL_SILO).unwrap_or(0)
    }

    /// Whether the pool is exhausted (no further bounded draw is possible).
    pub fn is_exhausted(&self) -> bool {
        self.remaining() == 0
    }

    /// **PRE-CHECK** — would drawing `amount` breach the shared pool? Asks the
    /// counter (no mutation): `amount > remaining`. This is the fail-closed gate
    /// the dispatch consults BEFORE its turn runs, so a would-be over-draw never
    /// commits a turn.
    pub fn would_overspend(&self, amount: u64) -> bool {
        amount > self.remaining()
    }

    /// **SETTLE A DRAW** — draw `amount` against the shared slice under `digest`
    /// (a one-shot, content-addressed identifier — the committed turn's receipt
    /// hash). Returns `Ok(())` if the draw is within the ceiling (the counter's
    /// `total_spent` grows by exactly `amount` — the conservation step), or
    /// [`StingrayDrawError::PoolExhausted`] if it would breach `B` (the counter is
    /// UNMOVED — fail-closed). A replayed `digest` is refused
    /// ([`StingrayDrawError::DuplicateDraw`]).
    ///
    /// This is the verified twin of N1's `spent += computrons`: where the floor
    /// model just added to a counter the swarm owned, this draws against a real
    /// `StingrayCounter` whose gate REFUSES an over-ceiling draw — the bound is
    /// the primitive's, not the swarm's.
    pub fn draw(&mut self, amount: u64, digest: [u8; 32]) -> Result<(), StingrayDrawError> {
        self.counter
            .try_debit_fresh(SWARM_POOL_SILO, amount, digest)
            .map_err(StingrayDrawError::from_counter)
    }

    /// **REFUND** a draw to the shared slice (the trustline repay leg: `spent`
    /// restores, but committed digests stay burned). Used when a drawn-against
    /// dispatch is later compensated. Returns the counter's result.
    pub fn refund(&mut self, amount: u64) -> Result<(), StingrayDrawError> {
        self.counter
            .refund(SWARM_POOL_SILO, amount)
            .map_err(StingrayDrawError::from_counter)
    }

    /// A read-only handle on the underlying counter (for assertions / a richer
    /// panel that wants the raw slice state). The counter is the authority; this
    /// never bypasses its gate.
    pub fn counter(&self) -> &StingrayCounter {
        &self.counter
    }

    /// THE SDK-SHAPED SLICE — the `BudgetSlice` the SDK's
    /// `runtime.rs::set_budget_gate` would attach to an executor for THIS pool, so
    /// the cockpit (or a node executor) can gate turns on the identical slice the
    /// swarm draws against. This is the seam to the SDK's `BudgetGate`: the swarm's
    /// shared pool IS a `BudgetSlice`, drawable both here and at an executor's
    /// per-turn gate, never two divergent models.
    pub fn sdk_slice(&self) -> Option<BudgetSlice> {
        self.counter.silo_states.get(&SWARM_POOL_SILO).cloned()
    }
}

/// THE AGGREGATE METER STRIP, Stingray-backed — the verified twin of
/// [`crate::swarm::SwarmBudget`]. Where the floor aggregate SUMMED per-member
/// counters, this reflects the SHARED counter directly: `total_drawn` and
/// `ceiling` are the pool's own figures (`StingrayCounter::total_spent` and the
/// slice ceiling), so the panel shows a conservation bound, not a summation.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct StingrayBudgetView {
    /// The conserved total drawn across ALL members (== `counter.total_spent()`).
    pub total_drawn: u64,
    /// The pool ceiling `B` (the verified upper bound).
    pub ceiling: u64,
    /// `B − total_drawn`, saturating at 0 (the pool's remaining headroom).
    pub remaining: u64,
    /// Whether the pool is exhausted (the "amber → red" boundary the panel colors).
    pub exhausted: bool,
}

impl StingrayBudgetView {
    /// Reflect the live pool into the panel strip.
    pub fn of(budget: &StingraySwarmBudget) -> Self {
        StingrayBudgetView {
            total_drawn: budget.total_drawn(),
            ceiling: budget.ceiling(),
            remaining: budget.remaining(),
            exhausted: budget.is_exhausted(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn agent() -> CellId {
        CellId::from_bytes([0xC0u8; 32])
    }

    fn digest(n: u64) -> [u8; 32] {
        *blake3::Hasher::new_derive_key("starbridge-stingray-test-v1")
            .update(&n.to_le_bytes())
            .finalize()
            .as_bytes()
    }

    #[test]
    fn an_opened_pool_has_the_full_ceiling_as_headroom_and_zero_drawn() {
        let b = StingraySwarmBudget::open(agent(), 10_000);
        assert_eq!(b.ceiling(), 10_000);
        assert_eq!(b.total_drawn(), 0, "nothing drawn yet");
        assert_eq!(b.remaining(), 10_000, "at f=0 the one slice ceiling IS the whole pool");
        assert!(!b.is_exhausted());
    }

    #[test]
    fn draws_conserve_total_drawn_is_the_sum_of_drawn_amounts() {
        // THE CONSERVATION TOOTH: total_drawn() == Σ drawn amounts, by the
        // counter's own accounting (StingrayCounter::total_spent).
        let mut b = StingraySwarmBudget::open(agent(), 10_000);
        b.draw(300, digest(1)).expect("first draw within ceiling");
        b.draw(450, digest(2)).expect("second draw within ceiling");
        b.draw(250, digest(3)).expect("third draw within ceiling");
        assert_eq!(
            b.total_drawn(),
            300 + 450 + 250,
            "the conserved total is exactly the sum of the drawn amounts"
        );
        assert_eq!(b.remaining(), 10_000 - 1_000, "headroom shrank by the drawn sum");
    }

    #[test]
    fn a_draw_past_the_ceiling_is_refused_by_the_gate_not_faked() {
        // THE OVER-DRAW REFUSAL: a draw that would breach B is refused by the
        // counter's gate (PoolExhausted) and the counter is UNMOVED — fail-closed.
        let mut b = StingraySwarmBudget::open(agent(), 1_000);
        b.draw(600, digest(1)).expect("first draw fits");
        assert_eq!(b.total_drawn(), 600);
        // A second draw of 500 would reach 1_100 > 1_000 — REFUSED.
        assert!(b.would_overspend(500), "the pre-check sees the breach");
        let r = b.draw(500, digest(2));
        match r {
            Err(StingrayDrawError::PoolExhausted { remaining, requested }) => {
                assert_eq!(remaining, 400, "the counter's own remaining headroom");
                assert_eq!(requested, 500);
            }
            other => panic!("expected PoolExhausted, got {other:?}"),
        }
        // FAIL-CLOSED: the refused draw moved nothing.
        assert_eq!(b.total_drawn(), 600, "a refused draw is unmoved — the gate held");
        assert_eq!(b.remaining(), 400);
    }

    #[test]
    fn a_draw_landing_exactly_on_the_ceiling_is_admitted() {
        // The ceiling is the inclusive bound the pool may REACH but not pass.
        let mut b = StingraySwarmBudget::open(agent(), 1_000);
        b.draw(600, digest(1)).expect("600 fits");
        b.draw(400, digest(2)).expect("landing exactly on the ceiling is admitted");
        assert_eq!(b.total_drawn(), 1_000);
        assert!(b.is_exhausted(), "the pool is now exactly exhausted");
        // One more unit is refused.
        assert!(matches!(
            b.draw(1, digest(3)),
            Err(StingrayDrawError::PoolExhausted { .. })
        ));
    }

    #[test]
    fn a_replayed_draw_digest_is_refused_one_shot() {
        let mut b = StingraySwarmBudget::open(agent(), 10_000);
        b.draw(100, digest(7)).expect("first use of the digest");
        let r = b.draw(100, digest(7));
        assert!(
            matches!(r, Err(StingrayDrawError::DuplicateDraw { .. })),
            "a replayed digest is refused (one-shot), got {r:?}"
        );
        // The counter is unmoved by the replay.
        assert_eq!(b.total_drawn(), 100, "the replay drew nothing");
    }

    #[test]
    fn a_refund_restores_headroom_the_repay_leg() {
        let mut b = StingraySwarmBudget::open(agent(), 1_000);
        b.draw(800, digest(1)).expect("draw fits");
        assert_eq!(b.remaining(), 200);
        b.refund(300).expect("refund restores spent");
        assert_eq!(b.total_drawn(), 500, "refund decremented the conserved total");
        assert_eq!(b.remaining(), 500);
        // After the refund there is headroom for a fresh draw again.
        b.draw(400, digest(2)).expect("a fresh draw fits in the restored headroom");
        assert_eq!(b.total_drawn(), 900);
    }

    #[test]
    fn the_aggregate_view_reflects_the_counter_not_a_summation() {
        let mut b = StingraySwarmBudget::open(agent(), 5_000);
        b.draw(1_200, digest(1)).expect("draw");
        let v = StingrayBudgetView::of(&b);
        assert_eq!(v.total_drawn, 1_200, "the view reads the counter's total_spent");
        assert_eq!(v.ceiling, 5_000);
        assert_eq!(v.remaining, 3_800);
        assert!(!v.exhausted);
        // The aggregate view's total_drawn IS the counter's total_spent (the
        // verified conservation figure), never a re-summed estimate.
        assert_eq!(v.total_drawn, b.counter().total_spent());
    }

    #[test]
    fn the_sdk_slice_is_the_same_budget_slice_the_set_budget_gate_would_attach() {
        // THE SDK SEAM: the pool exposes the `BudgetSlice` the SDK's
        // `runtime::set_budget_gate` attaches to an executor — the swarm's shared
        // pool IS a BudgetSlice, drawable both here and at an executor's per-turn
        // gate (never two divergent models).
        let mut b = StingraySwarmBudget::open(agent(), 2_000);
        b.draw(700, digest(1)).expect("draw");
        let slice = b.sdk_slice().expect("the shared slice exists");
        assert_eq!(slice.ceiling, 2_000, "the slice ceiling IS the pool ceiling B");
        assert_eq!(slice.spent, 700, "the slice's spent matches the pool's total_drawn");
        assert_eq!(slice.remaining(), 1_300);
        // The slice's spent equals the counter's total_spent (one model).
        assert_eq!(slice.spent, b.total_drawn());
    }
}
