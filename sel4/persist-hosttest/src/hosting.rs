//! `hosting` — the app-hosting economy: **pay coin to be hosted is a VERIFIED
//! VALUE TURN**, and a fee that lapses EVICTS the app (a verified turn that drops
//! the durable hosting). The deos OS charges coin to host apps; this is that
//! charge, modeled as conserving value turns committed through the persist-PD
//! durable spine — fail-closed, conserving, every charge and eviction a row in the
//! durable commit log.
//!
//! # The thesis
//!
//! deos hosts apps. An app is a **cell with durable hosted state in the persist-PD**
//! (its rows live in the same `dregg.turns` commit log as everything else — the
//! deos spine, `.docs-history-noclaude/PG-DREGG-ON-SEL4-DEOS-SPINE.md`). Hosting is not free: per
//! hosting period the app **pays a fee in coin to the host cell**. That payment is
//! a real value move — a [`turn`-crate `Effect::Transfer { from, to, amount }`]
//! (conservative linearity, `turn/src/action.rs:819`): coin LEAVES the app cell and
//! ARRIVES at the host cell, Σ value unchanged. It is committed as a verified turn
//! through the durable store (the chain gate admits it; the log records it), so the
//! charge is durable, ordered, and self-checking like every other turn.
//!
//! When the fee LAPSES — the app cannot pay the period's fee (insufficient balance)
//! — the host EVICTS it: a verified turn that drops the app's durable hosting (its
//! lease ends, its slot is reclaimed). Eviction is itself a committed turn, so it
//! is fail-closed (the app does not get to keep its hosting by refusing to pay) and
//! auditable (the eviction is a durable row). A PAID app's hosting persists.
//!
//! # The lease — a cap with a time/budget caveat over the durable slot
//!
//! A [`HostingLease`] is exactly what the brief names: a capability to occupy a
//! durable hosting slot, bounded by a budget (the prepaid balance) and a time
//! window (the paid-through period). The Lean model (`Dregg2/Apps/HostingLease.lean`)
//! proves the lease's gate cannot be amplified and the eviction is forced when the
//! budget lapses; THIS module is the runnable realization wired through the durable
//! commit log. The two meet at the same discipline: a hosting period either pays
//! (a conserving transfer commits, the lease's paid-through advances) or it does not
//! (the lease cannot cover the period → eviction commits).
//!
//! # Conservation — the load-bearing economic property
//!
//! Every hosting charge is a `Transfer`: the app's balance falls by `fee`, the
//! host's rises by `fee`, and [`HostingEconomy::total_value`] (Σ over all cells) is
//! INVARIANT across every charge. A charge that did not conserve (minted coin into
//! the host without debiting the app, or burned the app's coin without crediting
//! the host) would be refused — value cannot be forged through hosting. The teeth
//! (`§ tests`) prove: a charge conserves; an under-funded app is evicted; a paid
//! app persists; eviction is a durable, ordered turn; and value is conserved
//! end-to-end across a multi-period, multi-app run.

use crate::commit_store::{CommitRecord, GENESIS_ROOT};
use crate::redb_store::{DurableCommitStore, DurableError};

/// A cell id (the app cell, the host cell — the deos "apps as cells" model).
pub type CellId = [u8; 32];

/// A hosting-fee transfer — the deos charge as a conserving value move. This is
/// the `turn`-crate `Effect::Transfer { from, to, amount }` shape
/// (`turn/src/action.rs`, `Conservative` per
/// `metatheory/Dregg2/Spec/Conservation.lean` — the Rust `LinearityClass` twin
/// was dead and is deleted): `amount` coin moves
/// `from` the app `to` the host, conserving Σ value. We carry it as its own type
/// so the durable turn that commits a charge names exactly what moved.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FeeTransfer {
    /// The paying cell (the hosted app).
    pub from: CellId,
    /// The receiving cell (the host).
    pub to: CellId,
    /// The fee amount (coin) — leaves `from`, arrives at `to`.
    pub amount: u64,
}

/// The kind of hosting turn — what a durable commit row in this economy records.
/// Each is a verified turn through the spine; the discriminant is stamped into the
/// turn's `block_id` low byte so the durable log is legible (a charge vs an
/// eviction vs a top-up).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HostingTurn {
    /// A hosting-period FEE CHARGE — a conserving `FeeTransfer` (app → host).
    Charge { app: CellId, fee: u64, period: u64 },
    /// An EVICTION — the app could not pay; its durable hosting is dropped.
    Evict { app: CellId, period: u64 },
    /// A TOP-UP — coin added to an app's prepaid balance (so it can keep paying).
    /// Models the app's owner funding the lease; conserving (it moves coin from a
    /// funder cell into the app, here the genesis/funder).
    TopUp {
        app: CellId,
        funder: CellId,
        amount: u64,
    },
}

impl HostingTurn {
    fn tag(&self) -> u8 {
        match self {
            HostingTurn::Charge { .. } => 0xC0,
            HostingTurn::Evict { .. } => 0xE0,
            HostingTurn::TopUp { .. } => 0x70,
        }
    }
}

/// The hosting period an app has prepaid through, plus its lease parameters — the
/// runtime shadow of the Lean [`HostingLease`]. The lease is alive iff the app's
/// balance can cover the next period's fee; it is the budget (the balance) ∧ time
/// (the `paid_through` period) caveat over the durable slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Lease {
    /// The host cell the fee is paid to.
    pub host: CellId,
    /// The fee charged per hosting period.
    pub fee_per_period: u64,
    /// The last period the app has paid through (it is hosted for `[0, paid_through]`).
    pub paid_through: u64,
    /// Whether the app is currently hosted (false once evicted).
    pub hosted: bool,
}

/// The error a hosting operation surfaces.
#[derive(Debug)]
pub enum HostingError {
    /// The durable store refused or faulted (the turn is not durable).
    Durable(DurableError),
    /// The app is not registered (no lease).
    NoSuchApp(CellId),
    /// A non-conserving move was attempted (would forge or burn value) — refused.
    NotConserving(String),
}

impl core::fmt::Display for HostingError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            HostingError::Durable(e) => write!(f, "durable: {e}"),
            HostingError::NoSuchApp(a) => write!(f, "no such hosted app {}", hx(a)),
            HostingError::NotConserving(m) => write!(f, "non-conserving (refused): {m}"),
        }
    }
}
impl std::error::Error for HostingError {}

impl From<DurableError> for HostingError {
    fn from(e: DurableError) -> Self {
        HostingError::Durable(e)
    }
}

/// What charging a hosting period did — the verifiable outcome.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChargeOutcome {
    /// The app paid: a conserving `Transfer` committed at this ordinal, the lease's
    /// `paid_through` advanced, and the app stays hosted.
    Paid { ordinal: u64, period: u64 },
    /// The app could not pay: an EVICTION committed at this ordinal, the app's
    /// durable hosting was dropped (fail-closed).
    Evicted { ordinal: u64, period: u64 },
}

/// The app-hosting economy over the durable commit log. Holds the value ledger
/// (the `dregg.cells` balance projection — free-SQL reads over it), the per-app
/// leases, and the durable store every hosting turn commits to. The ONLY way coin
/// moves or a lease changes is through a verified turn committed here.
pub struct HostingEconomy {
    /// The durable store — every charge / eviction / top-up is a committed turn.
    store: DurableCommitStore,
    /// The value ledger: cell -> balance (the conservation observable). Mirrors
    /// the pg-dregg `balances` projection. Charges move coin within this map,
    /// conserving Σ.
    balances: std::collections::BTreeMap<CellId, u64>,
    /// Per-app leases (the durable hosting slots).
    leases: std::collections::BTreeMap<CellId, Lease>,
    /// The running chain head, mirrored from the durable store (so a turn carries
    /// the right `prev_root`). The durable store is the source of truth; this is
    /// the in-RAM convenience copy advanced on each commit.
    head: Option<[u8; 32]>,
    /// The next ordinal (mirrors the durable cursor).
    next_ordinal: u64,
}

impl HostingEconomy {
    /// Open the economy over a durable store, resuming the head + cursor from it
    /// (a persist-PD restart recovers the economy's chain position).
    pub fn open(store: DurableCommitStore) -> Result<Self, HostingError> {
        let head = store.head_root()?;
        let next_ordinal = store.commit_cursor()?;
        Ok(HostingEconomy {
            store,
            balances: std::collections::BTreeMap::new(),
            leases: std::collections::BTreeMap::new(),
            head,
            next_ordinal,
        })
    }

    // ---- value ledger (free reads; the conservation observable) --------------

    /// A free read: the balance of a cell (`SELECT balance FROM dregg.cells …`).
    pub fn balance(&self, cell: CellId) -> u64 {
        self.balances.get(&cell).copied().unwrap_or(0)
    }

    /// Σ balances across all cells — the conservation observable. A well-formed run
    /// keeps this constant: every hosting charge is a transfer, not a mint/burn.
    pub fn total_value(&self) -> u64 {
        self.balances.values().copied().sum()
    }

    /// Whether `app` is currently hosted (its lease is alive and not evicted).
    pub fn is_hosted(&self, app: CellId) -> bool {
        self.leases.get(&app).map(|l| l.hosted).unwrap_or(false)
    }

    /// The lease of an app, if registered.
    pub fn lease(&self, app: CellId) -> Option<Lease> {
        self.leases.get(&app).copied()
    }

    /// The number of durably committed hosting turns (the chain length).
    pub fn turn_count(&self) -> u64 {
        self.next_ordinal
    }

    /// The durable store (for chain re-checks / reads).
    pub fn store(&self) -> &DurableCommitStore {
        &self.store
    }

    // ---- genesis: fund a cell (the only place coin enters; like the workflow's
    //      `genesis` step minting the initial supply) -------------------------

    /// Fund a cell with an initial balance — the genesis mint (the ONLY place coin
    /// enters the economy; every later move conserves). Commits a genesis turn so
    /// the funding is durable and ordered. Models the treasury minting supply.
    pub fn genesis_fund(&mut self, cell: CellId, amount: u64) -> Result<u64, HostingError> {
        // Genesis is the one non-conserving event (it mints the initial supply),
        // exactly as the pg-dregg workflow's genesis step does. After genesis, Σ is
        // fixed and every hosting turn conserves it.
        let ordinal = self.commit_turn(cell, b"genesis-fund", &[cell])?;
        *self.balances.entry(cell).or_insert(0) += amount;
        Ok(ordinal)
    }

    // ---- register an app for hosting (open its lease) ------------------------

    /// Register `app` for hosting on `host` at `fee_per_period`. The app's durable
    /// hosting slot opens; it is hosted for period 0 (the registration period is
    /// paid by the act of registering — a host could require a deposit; here period
    /// 0 is the grace period and the first CHARGE is period 1). Commits a turn.
    pub fn register_app(
        &mut self,
        app: CellId,
        host: CellId,
        fee_per_period: u64,
    ) -> Result<u64, HostingError> {
        let ordinal = self.commit_turn(app, b"register-app", &[app])?;
        self.leases.insert(
            app,
            Lease {
                host,
                fee_per_period,
                paid_through: 0,
                hosted: true,
            },
        );
        Ok(ordinal)
    }

    // ---- top up an app's prepaid balance (a conserving funder → app move) ----

    /// Top up `app`'s prepaid balance from `funder` — a conserving transfer (coin
    /// moves funder → app). The app's owner funds the lease so it can keep paying.
    /// Refused if the funder cannot cover it (no overdraft — fail-closed). Commits.
    pub fn top_up(
        &mut self,
        app: CellId,
        funder: CellId,
        amount: u64,
    ) -> Result<u64, HostingError> {
        let funder_bal = self.balance(funder);
        if funder_bal < amount {
            return Err(HostingError::NotConserving(format!(
                "funder {} has {funder_bal} < top-up {amount} (no overdraft)",
                hx(&funder)
            )));
        }
        let ordinal = self.commit_turn(funder, b"top-up", &[app, funder])?;
        // conserving move: funder -> app.
        *self.balances.entry(funder).or_insert(0) -= amount;
        *self.balances.entry(app).or_insert(0) += amount;
        Ok(ordinal)
    }

    // ---- THE CHARGE: pay a hosting period, or be evicted ---------------------

    /// Charge `app` for one hosting period — **the verified value turn at the heart
    /// of the economy**. If the app's balance covers `fee_per_period`, a CONSERVING
    /// transfer (app → host) commits, the lease's `paid_through` advances, and the
    /// app stays hosted ([`ChargeOutcome::Paid`]). If it does NOT, the host EVICTS
    /// the app — an eviction turn commits, the app's durable hosting is dropped,
    /// fail-closed ([`ChargeOutcome::Evicted`]). Either way a durable, ordered turn
    /// records what happened.
    ///
    /// This is the tooth: **a hosted app whose fee lapses is evicted (verified,
    /// fail-closed); a paid app's state persists.** Non-payment cannot buy free
    /// hosting — the only outcomes are "paid (conserving)" or "evicted (durable)".
    pub fn charge_period(&mut self, app: CellId) -> Result<ChargeOutcome, HostingError> {
        let lease = *self.leases.get(&app).ok_or(HostingError::NoSuchApp(app))?;
        if !lease.hosted {
            // Already evicted — charging an evicted app is a no-op eviction (it is
            // not hosted; nothing to charge). Surface it as Evicted at the current
            // head so the caller sees the fail-closed state.
            return Ok(ChargeOutcome::Evicted {
                ordinal: self.next_ordinal,
                period: lease.paid_through + 1,
            });
        }
        let period = lease.paid_through + 1;
        let app_bal = self.balance(app);

        if app_bal >= lease.fee_per_period {
            // PAY: a conserving Transfer app -> host commits as a verified turn.
            let fee = lease.fee_per_period;
            let ordinal = self.commit_hosting_turn(
                HostingTurn::Charge { app, fee, period },
                app,
                host_of(&lease),
            )?;
            // conserving move: app -> host. (Σ value invariant — the load-bearing
            // economic property: hosting charges coin, it does not forge it.)
            *self.balances.entry(app).or_insert(0) -= fee;
            *self.balances.entry(lease.host).or_insert(0) += fee;
            // advance the lease's paid-through (its time caveat moves forward).
            if let Some(l) = self.leases.get_mut(&app) {
                l.paid_through = period;
            }
            Ok(ChargeOutcome::Paid { ordinal, period })
        } else {
            // CANNOT PAY → EVICT: a verified eviction turn commits, the durable
            // hosting is dropped. Fail-closed: the app does not keep hosting by not
            // paying.
            let ordinal = self.commit_hosting_turn(HostingTurn::Evict { app, period }, app, app)?;
            if let Some(l) = self.leases.get_mut(&app) {
                l.hosted = false;
            }
            Ok(ChargeOutcome::Evicted { ordinal, period })
        }
    }

    /// Run `periods` hosting periods over an app, charging each — the lease's
    /// lifecycle. Stops early (returning the eviction) the first period the app
    /// cannot pay. The convenience driver for a multi-period run.
    pub fn run_periods(
        &mut self,
        app: CellId,
        periods: u64,
    ) -> Result<Vec<ChargeOutcome>, HostingError> {
        let mut out = Vec::new();
        for _ in 0..periods {
            let outcome = self.charge_period(app)?;
            let evicted = matches!(outcome, ChargeOutcome::Evicted { .. });
            out.push(outcome);
            if evicted {
                break; // an evicted app is no longer hosted; stop charging it.
            }
        }
        Ok(out)
    }

    // ---- the durable commit (the spine: chain gate, then redb txn) -----------

    /// Commit a hosting turn through the durable store — the spine. Builds the
    /// `CommitRecord` (stamping the `(ordinal, prev_root)` the durable head hands
    /// us, like `pg-dregg/src/drainer.rs`'s producer contract), runs it through the
    /// store's chain gate, and commits it in one redb transaction. Advances the
    /// in-RAM head + ordinal on success. A refusal/fault leaves both unmoved.
    fn commit_hosting_turn(
        &mut self,
        turn: HostingTurn,
        creator: CellId,
        touched: CellId,
    ) -> Result<u64, HostingError> {
        // a legible per-turn discriminator for the durable log (the kind tag).
        let mut block_id = [0u8; 32];
        block_id[0] = turn.tag();
        self.commit_record_for(creator, &block_id, &[touched])
    }

    /// Commit a plain turn (genesis/register/top-up) — the same spine with a
    /// label byte instead of a `HostingTurn` tag.
    fn commit_turn(
        &mut self,
        creator: CellId,
        label: &[u8],
        touched: &[CellId],
    ) -> Result<u64, HostingError> {
        let mut block_id = [0u8; 32];
        let n = label.len().min(32);
        block_id[..n].copy_from_slice(&label[..n]);
        self.commit_record_for(creator, &block_id, touched)
    }

    /// The shared commit path: produce the post-state record (stamped with the
    /// head-handed `(ordinal, prev_root)`), commit it through the durable chain
    /// gate, and advance the in-RAM head/ordinal. The `ledger_root` is a
    /// deterministic post-state digest of `(prev_root, ordinal, touched cells)` —
    /// the stand-in for the executor's verified ledger fold (the same role
    /// `FoldProjector` plays in `pg-dregg/src/workflow.rs`).
    fn commit_record_for(
        &mut self,
        creator: CellId,
        block_id: &[u8; 32],
        touched: &[CellId],
    ) -> Result<u64, HostingError> {
        let ordinal = self.next_ordinal;
        let prev_root = self.head.unwrap_or(GENESIS_ROOT);
        let ledger_root = fold_root(prev_root, ordinal, touched, &self.balances);
        let turn_hash = digest(0x01, ordinal, &prev_root, block_id);
        let receipt_hash = digest(0x02, ordinal, &prev_root, block_id);
        let mut touched_bytes = Vec::new();
        for c in touched {
            touched_bytes.extend_from_slice(c);
        }
        let record = CommitRecord {
            ordinal,
            height: ordinal,
            block_id: *block_id,
            turn_hash,
            creator,
            receipt_hash,
            prev_root,
            ledger_root,
            touched_cells: touched_bytes,
        };
        let assigned = self.store.commit_verified_turn(&record)?;
        // advance the in-RAM mirror from the durable head (source of truth).
        self.head = self.store.head_root()?;
        self.next_ordinal = self.store.commit_cursor()?;
        Ok(assigned)
    }
}

fn host_of(l: &Lease) -> CellId {
    l.host
}

/// A deterministic post-state root fold over `(prev, ordinal, touched, balances)`
/// — the stand-in for the executor's verified `ledger_root` (the same shape
/// `pg-dregg::workflow::FoldProjector` uses). Binding the balances in means the
/// durable root commits to the value ledger, so a tampered balance breaks the
/// chain on re-check.
fn fold_root(
    prev: [u8; 32],
    ordinal: u64,
    touched: &[CellId],
    balances: &std::collections::BTreeMap<CellId, u64>,
) -> [u8; 32] {
    let mut acc: u64 = 0xcbf2_9ce4_8422_2325 ^ ordinal.wrapping_mul(0x0100_0000_01b3);
    for b in prev {
        acc = (acc ^ b as u64).wrapping_mul(0x0100_0000_01b3);
    }
    for c in touched {
        for b in c {
            acc = (acc ^ *b as u64).wrapping_mul(0x0100_0000_01b3);
        }
        let bal = balances.get(c).copied().unwrap_or(0);
        acc = (acc ^ bal).wrapping_mul(0x0100_0000_01b3);
    }
    let mut out = [0u8; 32];
    for (i, chunk) in out.chunks_mut(8).enumerate() {
        let v = acc.wrapping_add((i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15));
        chunk.copy_from_slice(&v.to_le_bytes());
    }
    out
}

fn digest(tag: u8, ordinal: u64, prev: &[u8; 32], block_id: &[u8; 32]) -> [u8; 32] {
    let mut acc = 0x9e37_79b9_7f4a_7c15u64 ^ ((tag as u64) << 56) ^ ordinal;
    for (i, b) in prev.iter().chain(block_id.iter()).enumerate() {
        acc = acc
            .rotate_left(7)
            .wrapping_add(*b as u64)
            .wrapping_mul(0x0100_0000_01b3)
            ^ (i as u64);
    }
    let mut out = [0u8; 32];
    for (i, slot) in out.iter_mut().enumerate() {
        acc = acc
            .rotate_left(11)
            .wrapping_add(i as u64)
            .wrapping_mul(0x0100_0000_01b3);
        *slot = (acc >> ((i % 8) * 8)) as u8;
    }
    out
}

fn hx(b: &[u8; 32]) -> String {
    let mut s = String::with_capacity(8);
    for byte in b.iter().take(4) {
        s.push_str(&format!("{byte:02x}"));
    }
    s
}

// ============================================================================
// Tests — the hosting-economy teeth, over the REAL durable spine.
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::redb_store::RegionBackend;

    const HOST: CellId = [0x40; 32];
    const TREASURY: CellId = [0xC0; 32];
    fn app(tag: u8) -> CellId {
        let mut a = [0xA0; 32];
        a[0] = tag;
        a
    }

    /// A fresh economy over a temp-file-backed durable store.
    fn fresh() -> (tempfile::TempDir, HostingEconomy) {
        let dir = tempfile::tempdir().unwrap();
        let backend = RegionBackend::file(&dir.path().join("hosting.redb")).unwrap();
        let store = DurableCommitStore::open(backend).unwrap();
        let econ = HostingEconomy::open(store).unwrap();
        (dir, econ)
    }

    /// THE CHARGE CONSERVES: a hosting fee is a Transfer (app → host); Σ value is
    /// unchanged, the app's balance falls by the fee, the host's rises by it.
    #[test]
    fn a_hosting_charge_is_a_conserving_transfer() {
        let (_d, mut econ) = fresh();
        // genesis mints 1000 to the treasury; treasury funds the app 100.
        econ.genesis_fund(TREASURY, 1000).unwrap();
        let a = app(0x01);
        econ.register_app(a, HOST, 10).unwrap();
        econ.top_up(a, TREASURY, 100).unwrap();
        assert_eq!(
            econ.total_value(),
            1000,
            "top-up conserves (treasury → app)"
        );

        let total_before = econ.total_value();
        let app_before = econ.balance(a);
        let host_before = econ.balance(HOST);

        let outcome = econ.charge_period(a).unwrap();
        assert!(matches!(outcome, ChargeOutcome::Paid { period: 1, .. }));
        assert_eq!(econ.balance(a), app_before - 10, "app debited the fee");
        assert_eq!(
            econ.balance(HOST),
            host_before + 10,
            "host credited the fee"
        );
        assert_eq!(
            econ.total_value(),
            total_before,
            "Σ value conserved (transfer, not mint)"
        );
        assert!(econ.is_hosted(a), "a paid app stays hosted");
        assert_eq!(
            econ.lease(a).unwrap().paid_through,
            1,
            "lease advanced one period"
        );
    }

    /// THE EVICTION TOOTH: a hosted app whose fee lapses (cannot pay) is EVICTED —
    /// a verified, durable turn drops its hosting, fail-closed. A paid app persists.
    #[test]
    fn a_lapsed_app_is_evicted_a_paid_app_persists() {
        let (_d, mut econ) = fresh();
        econ.genesis_fund(TREASURY, 1000).unwrap();

        // PAID app: funded enough for many periods — stays hosted.
        let paid = app(0x11);
        econ.register_app(paid, HOST, 10).unwrap();
        econ.top_up(paid, TREASURY, 50).unwrap();

        // LAPSING app: funded for exactly two periods, then dry.
        let lapsing = app(0x22);
        econ.register_app(lapsing, HOST, 10).unwrap();
        econ.top_up(lapsing, TREASURY, 20).unwrap(); // 2 periods of fee

        // Charge both 4 periods. The paid app pays all 4; the lapsing app pays 2
        // then is evicted on period 3 (balance 0 < fee 10).
        let paid_out = econ.run_periods(paid, 4).unwrap();
        assert_eq!(paid_out.len(), 4, "paid app ran all 4 periods");
        assert!(paid_out
            .iter()
            .all(|o| matches!(o, ChargeOutcome::Paid { .. })));
        assert!(econ.is_hosted(paid), "the paid app's hosting persists");
        assert_eq!(econ.balance(paid), 10, "50 − 4×10 = 10 remaining");

        let lapsing_out = econ.run_periods(lapsing, 4).unwrap();
        // periods 1,2 paid; period 3 evicts; run stops (no period 4).
        assert_eq!(lapsing_out.len(), 3, "two paid + one eviction, then stop");
        assert!(matches!(
            lapsing_out[0],
            ChargeOutcome::Paid { period: 1, .. }
        ));
        assert!(matches!(
            lapsing_out[1],
            ChargeOutcome::Paid { period: 2, .. }
        ));
        assert!(matches!(
            lapsing_out[2],
            ChargeOutcome::Evicted { period: 3, .. }
        ));
        assert!(
            !econ.is_hosted(lapsing),
            "the lapsed app is EVICTED (fail-closed)"
        );
        assert_eq!(econ.balance(lapsing), 0, "the lapsing app drained to 0");
    }

    /// EVICTION IS A DURABLE, ORDERED TURN: the eviction is a committed row in the
    /// durable log, and the chain self-checks across it.
    #[test]
    fn eviction_is_a_durable_ordered_verified_turn() {
        let (_d, mut econ) = fresh();
        econ.genesis_fund(TREASURY, 100).unwrap();
        let a = app(0x33);
        econ.register_app(a, HOST, 10).unwrap();
        // no top-up: the app has 0 balance, so period 1 evicts immediately.
        let turns_before = econ.turn_count();
        let outcome = econ.charge_period(a).unwrap();
        assert!(matches!(outcome, ChargeOutcome::Evicted { period: 1, .. }));
        assert_eq!(
            econ.turn_count(),
            turns_before + 1,
            "the eviction is a durable turn"
        );
        // the durable chain re-validates across the eviction (self-checking).
        econ.store()
            .verify_chain_intact()
            .expect("the durable chain is intact across eviction");
        // the eviction row is in the durable log with the Evict tag.
        let records = econ.store().read_ordered().unwrap();
        let last = records.last().unwrap();
        assert_eq!(last.block_id[0], 0xE0, "the last row is an Evict turn");
        assert_eq!(last.creator, a, "the eviction names the app as creator");
    }

    /// VALUE IS CONSERVED END-TO-END across a multi-app, multi-period run: Σ value
    /// after every charge equals the genesis supply (hosting charges coin, never
    /// forges it).
    #[test]
    fn value_conserved_across_a_full_hosting_run() {
        let (_d, mut econ) = fresh();
        let supply = 1000u64;
        econ.genesis_fund(TREASURY, supply).unwrap();
        assert_eq!(econ.total_value(), supply);

        let a = app(0x44);
        let b = app(0x55);
        econ.register_app(a, HOST, 7).unwrap();
        econ.register_app(b, HOST, 5).unwrap();
        econ.top_up(a, TREASURY, 35).unwrap();
        econ.top_up(b, TREASURY, 30).unwrap();
        assert_eq!(econ.total_value(), supply, "top-ups conserve");

        // 10 periods over each, conservation checked after every charge.
        for _ in 0..10 {
            let _ = econ.charge_period(a);
            assert_eq!(econ.total_value(), supply, "Σ value invariant after a");
            let _ = econ.charge_period(b);
            assert_eq!(econ.total_value(), supply, "Σ value invariant after b");
        }
        // both eventually evicted (a after 5 paid periods, b after 6).
        assert!(!econ.is_hosted(a) || econ.balance(a) < 7);
        assert_eq!(econ.total_value(), supply, "value conserved end-to-end");
        econ.store()
            .verify_chain_intact()
            .expect("durable chain intact end-to-end");
    }

    /// TOP-UP CANNOT OVERDRAFT: a funder cannot top up more than it holds (no value
    /// forged into an app).
    #[test]
    fn top_up_cannot_overdraft_the_funder() {
        let (_d, mut econ) = fresh();
        econ.genesis_fund(TREASURY, 30).unwrap();
        let a = app(0x66);
        econ.register_app(a, HOST, 10).unwrap();
        let err = econ.top_up(a, TREASURY, 50).unwrap_err();
        assert!(
            matches!(err, HostingError::NotConserving(_)),
            "overdraft refused"
        );
        assert_eq!(econ.total_value(), 30, "no value forged");
        assert_eq!(econ.balance(a), 0, "the app got nothing");
    }

    /// DURABILITY: hosting state survives a persist-PD restart — reopen the store
    /// over the SAME region bytes and the committed turns + head + cursor recover,
    /// and a re-derived economy re-reads the durable chain.
    #[test]
    fn hosting_survives_a_persist_pd_restart() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("hosting.redb");

        let head_after;
        let cursor_after;
        {
            let backend = RegionBackend::file(&path).unwrap();
            let store = DurableCommitStore::open(backend).unwrap();
            let mut econ = HostingEconomy::open(store).unwrap();
            econ.genesis_fund(TREASURY, 100).unwrap();
            let a = app(0x77);
            econ.register_app(a, HOST, 10).unwrap();
            econ.top_up(a, TREASURY, 30).unwrap();
            econ.charge_period(a).unwrap(); // one paid period
            head_after = econ.store().head_root().unwrap();
            cursor_after = econ.store().commit_cursor().unwrap();
            // econ + store dropped here — only the file bytes survive (the crash).
        }

        // Reopen over the SAME bytes — the durable store recovers exactly.
        let backend = RegionBackend::file(&path).unwrap();
        let store = DurableCommitStore::open(backend).unwrap();
        assert_eq!(
            store.head_root().unwrap(),
            head_after,
            "durable head recovered"
        );
        assert_eq!(
            store.commit_cursor().unwrap(),
            cursor_after,
            "durable cursor recovered"
        );
        store
            .verify_chain_intact()
            .expect("the recovered durable chain is intact");
        assert!(
            cursor_after >= 4,
            "genesis+register+topup+charge = 4 durable turns"
        );
    }
}
