//! `$DREGG`-paid, real-AI dungeon runs — the bot's consumption of the committed
//! [`dregg_pay`] backend + the [`dregg_narrator`] hosted narrator.
//!
//! The loop this wires:
//!
//! 1. **`/buy-credits`** issues the caller's deterministic per-user Solana deposit address
//!    ([`HdDeposit::deposit_address`]) — same user ⇒ same address — and shows the price per run.
//! 2. A **payment poll** ([`PayState::poll_and_credit`]) polls the [`Watcher`] for that address and
//!    credits run-credits via [`CreditLedger::credit`], **idempotent** by the payment reference (a
//!    re-poll never double-credits).
//! 3. **`/credits`** reads [`CreditLedger::balance`] (persisted in sqlite, so it survives restart).
//! 4. A **paid `/dungeon` run** ([`PayState::try_paid_run`]) debits ONE credit
//!    ([`CreditLedger::debit`]) and routes to **real Bedrock** ([`dregg_narrator::metered_converse`])
//!    under a **PER-RUN USD budget** — a fresh [`BudgetLedger`] capped at `usd_per_run` at a unique
//!    path, so the debited credit *is* the budget. This is NOT the single global `$20` cap (a public
//!    bot on one shared cap would let one run drain everyone). An **empty balance** falls back to the
//!    FREE tier (ollama/scripted) — the paid backend is never free-ridden.
//!
//! **Safety.** Nothing mainnet is hardcoded: the mint/treasury/seed are operator config
//! ([`PayConfig::from_env`]); with no operator env the bot falls back to a DEVNET/MOCK
//! config with a throwaway seed and a [`MockWatcher`]. **The watcher is selected by
//! config** ([`select_watcher`]): an operator-supplied config gets the REAL
//! [`SolanaWatcher`] over the configured RPC — watch-only (it reads token-account state,
//! holds no key, and never touches the seed) — while the mock is reachable ONLY
//! explicitly (the no-env devnet fallback, or `DREGG_PAY_MOCK=1` on a non-mainnet
//! network). A mainnet config can never ride the mock, and a mainnet config without a
//! real RPC fails loudly at construction — never a silent mock on a real network. The
//! SWEEPER holding the custody seed still runs as a separate operator service.

use std::path::PathBuf;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use dregg_narrator::{
    BudgetLedger, ConverseBackend, ConverseRequest, DEFAULT_MODEL, ModelRegistry, NarratorError,
    metered_converse,
};
use dregg_pay::{
    AccountFetcher, ChainId, CreditLedger, CreditOutcome, CreditStore, DepositAddress,
    DepositAddressBook, DepositAddressProvider, FetchedAccount, HdDeposit, MockChain, MockWatcher,
    MultichainHoldings, Network, PayConfig, PayRole, PaymentRef, ProvenForeignHolding,
    SolanaWatcher, Treasury, TreasuryError, TreasurySlot, TreasuryStore, TreasuryView, UserId,
    WatchError, Watcher,
};

use crate::db::Database;

// ─────────────────────────────────────────────────────────────────────────────
// The sqlite-backed CreditStore — dregg-pay's `CreditStore` trait over the bot's
// async sqlx `Database`. Credits + processed-refs persist; they survive restart.
// ─────────────────────────────────────────────────────────────────────────────

/// A [`CreditStore`] persisted in the bot's sqlite database. The trait is SYNC (interior
/// mutability) but the bot's `Database` is async sqlx, so each method drives the async query to
/// completion on the current Tokio runtime via [`tokio::task::block_in_place`] (the bot runs on the
/// multi-thread runtime; drive it from a runtime worker). Balances + credited references live in
/// `pay_credits` / `pay_processed`, so a fresh process re-opening the same DB sees the same credits.
pub struct SqliteCreditStore {
    db: Database,
    handle: tokio::runtime::Handle,
}

impl SqliteCreditStore {
    /// Wrap a `Database`. `handle` is the runtime to fall back to when a store method is somehow
    /// called from OUTSIDE any runtime; inside a runtime worker the current handle is used.
    pub fn new(db: Database, handle: tokio::runtime::Handle) -> Self {
        SqliteCreditStore { db, handle }
    }

    /// Drive an async DB future to completion synchronously — the sync↔async bridge the sync
    /// [`CreditStore`] trait forces. Inside a multi-thread runtime worker this uses
    /// `block_in_place` (no deadlock, no nested-runtime panic); outside any runtime it blocks on the
    /// stored handle.
    fn block<F: std::future::Future>(&self, fut: F) -> F::Output {
        match tokio::runtime::Handle::try_current() {
            Ok(current) => tokio::task::block_in_place(move || current.block_on(fut)),
            Err(_) => self.handle.block_on(fut),
        }
    }
}

impl CreditStore for SqliteCreditStore {
    fn balance(&self, user: &UserId) -> u64 {
        self.block(self.db.pay_credit_balance(&user.0)).unwrap_or(0)
    }
    fn set_balance(&self, user: &UserId, credits: u64) {
        let _ = self.block(self.db.pay_set_credit_balance(&user.0, credits));
    }
    fn is_processed(&self, reference: &PaymentRef) -> bool {
        self.block(self.db.pay_is_processed(&reference.0))
            .unwrap_or(false)
    }
    fn mark_processed(&self, reference: &PaymentRef) {
        let _ = self.block(self.db.pay_mark_processed(&reference.0));
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The sqlite-backed TreasuryStore — dregg-pay's two-balance `TreasuryStore` over the
// bot's async sqlx `Database`. The FUEL (`usdc`) + PILE (`dregg`) balances persist in
// `pay_treasury`, so detected game revenue that landed in the treasury survives a
// restart, exactly like the credit ledger.
// ─────────────────────────────────────────────────────────────────────────────

/// A [`TreasuryStore`] persisted in the bot's sqlite database. Same sync↔async bridge as
/// [`SqliteCreditStore`]: the trait is SYNC (interior mutability) but the `Database` is
/// async sqlx, so each method drives the query to completion on the current Tokio runtime
/// via [`tokio::task::block_in_place`]. The two balances live in the single `pay_treasury`
/// row, so a fresh process re-opening the same DB sees the same fuel + pile.
pub struct SqliteTreasuryStore {
    db: Database,
    handle: tokio::runtime::Handle,
}

impl SqliteTreasuryStore {
    /// Wrap a `Database`. `handle` is the fallback runtime when a store method is called
    /// from OUTSIDE any runtime; inside a runtime worker the current handle is used.
    pub fn new(db: Database, handle: tokio::runtime::Handle) -> Self {
        SqliteTreasuryStore { db, handle }
    }

    /// Drive an async DB future to completion synchronously — the same bridge
    /// [`SqliteCreditStore::block`] uses.
    fn block<F: std::future::Future>(&self, fut: F) -> F::Output {
        match tokio::runtime::Handle::try_current() {
            Ok(current) => tokio::task::block_in_place(move || current.block_on(fut)),
            Err(_) => self.handle.block_on(fut),
        }
    }
}

impl TreasuryStore for SqliteTreasuryStore {
    fn usdc_balance(&self) -> u64 {
        self.block(self.db.pay_treasury_usdc()).unwrap_or(0)
    }
    fn dregg_balance(&self) -> u64 {
        self.block(self.db.pay_treasury_dregg()).unwrap_or(0)
    }
    fn set_usdc_balance(&self, v: u64) {
        let _ = self.block(self.db.pay_treasury_set_usdc(v));
    }
    fn set_dregg_balance(&self, v: u64) {
        let _ = self.block(self.db.pay_treasury_set_dregg(v));
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The PAID narrator — real Bedrock under a PER-RUN USD budget.
// ─────────────────────────────────────────────────────────────────────────────

/// A single-run counter so per-run budget-ledger files never collide within a process.
static RUN_SEQ: AtomicU64 = AtomicU64::new(0);

/// A produced paid narration + the honest kind of what produced it and what it cost.
#[derive(Clone, Debug)]
pub struct PaidNarration {
    /// The narration text.
    pub text: String,
    /// The honest kind: `bedrock:<model-id>` — the model that ACTUALLY narrated.
    pub kind: String,
    /// The USD the per-run ledger recorded for this call (post true-up).
    pub usd_spent: f64,
}

/// The real-AI narrator for a PAID run. Each [`Self::narrate`] runs one metered Converse against
/// `backend` under a FRESH [`BudgetLedger`] capped at `usd_per_run` — a per-run budget, not a shared
/// global cap. In production `backend` is a [`dregg_narrator::BedrockClient`]; tests inject a mock
/// [`ConverseBackend`], so the whole gate is driven with no AWS call and no spend.
///
/// `Clone` (all fields are cheaply clonable — the backend is an `Arc`) so the live `/dungeon` path
/// can move it into [`tokio::task::spawn_blocking`]: the real Bedrock client drives its OWN runtime
/// with `block_on`, which must NOT run on a bot async worker, so the hosted call runs off-worker.
#[derive(Clone)]
pub struct PaidNarrator {
    backend: Arc<dyn ConverseBackend + Send + Sync>,
    registry: ModelRegistry,
    model: String,
    usd_per_run: f64,
    max_tokens: u32,
    ledger_dir: PathBuf,
}

impl PaidNarrator {
    /// Build a paid narrator. `model` must be priced in `registry` or every call fails closed with
    /// [`NarratorError::UnpricedModel`]. `ledger_dir` holds the ephemeral per-run budget files.
    pub fn new(
        backend: Arc<dyn ConverseBackend + Send + Sync>,
        registry: ModelRegistry,
        model: impl Into<String>,
        usd_per_run: f64,
        max_tokens: u32,
        ledger_dir: PathBuf,
    ) -> Self {
        PaidNarrator {
            backend,
            registry,
            model: model.into(),
            usd_per_run,
            max_tokens,
            ledger_dir,
        }
    }

    /// The model id this narrator targets.
    pub fn model(&self) -> &str {
        &self.model
    }

    /// Narrate one room under a PER-RUN budget. Enforces reserve → call → true-up via
    /// [`metered_converse`] on a fresh, uniquely-pathed [`BudgetLedger`] capped at `usd_per_run`
    /// (so it starts at `$0` and can never spend more than one run's budget). The per-run ledger
    /// file is deleted afterward (disk-mindful; the persistent CREDIT accounting is the sqlite
    /// ledger, not this ephemeral USD file).
    pub fn narrate(&self, system: &str, user: &str) -> Result<PaidNarration, NarratorError> {
        let _ = std::fs::create_dir_all(&self.ledger_dir);
        let seq = RUN_SEQ.fetch_add(1, Ordering::Relaxed);
        let path = self
            .ledger_dir
            .join(format!("run-{}-{seq}.json", std::process::id()));
        let ledger = BudgetLedger::new(&path, self.usd_per_run);

        let req = ConverseRequest::plain(self.model.as_str(), system, user, self.max_tokens);
        let result = metered_converse(&ledger, &self.registry, self.backend.as_ref(), &req);
        let usd_spent = ledger.spent_usd().unwrap_or(0.0);

        // Best-effort cleanup of the ephemeral per-run budget file + its lock sidecar.
        let _ = std::fs::remove_file(&path);
        let mut lock = path.clone().into_os_string();
        lock.push(".lock");
        let _ = std::fs::remove_file(PathBuf::from(lock));

        let resp = result?;
        Ok(PaidNarration {
            text: resp.text,
            kind: format!("bedrock:{}", self.model),
            usd_spent,
        })
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// PayState — everything the bot needs to earn: config, deposit provider, the
// credit ledger (sqlite-backed), the watcher, and the paid narrator.
// ─────────────────────────────────────────────────────────────────────────────

/// Where a [`PayState`] resolves a user's deposit address — the CUSTODY SPLIT made a
/// type. A watch-only bot never holds the signing seed; it serves addresses from a
/// public book the seed-holding sweeper published.
pub enum DepositSource {
    /// Seed-bearing HD derivation (the sweeper role, and the devnet-mock fallback).
    /// Total: every user deterministically derives an address. Holds the seed.
    Custodial(HdDeposit),
    /// Seed-free: a public [`DepositAddressBook`] the sweeper published (the
    /// production bot). Holds NO key. A user not yet in the book is fail-closed
    /// ([`DepositError::NotProvisioned`]) — never a guessed or wrong address.
    WatchOnly(DepositAddressBook),
}

impl DepositSource {
    /// `true` on the seed-free watch-only path.
    pub fn is_watch_only(&self) -> bool {
        matches!(self, DepositSource::WatchOnly(_))
    }

    /// Resolve `user`'s deposit address; fail-closed on an unprovisioned watch-only
    /// user (the custodial path always resolves).
    pub fn address_checked(&self, user: &UserId) -> Result<DepositAddress, DepositError> {
        match self {
            DepositSource::Custodial(hd) => Ok(hd.deposit_address(user)),
            DepositSource::WatchOnly(book) => book
                .address_for_user(user)
                .ok_or_else(|| DepositError::NotProvisioned(user.clone())),
        }
    }
}

/// Why a watch-only deposit-address lookup failed.
#[derive(Clone, Debug)]
pub enum DepositError {
    /// The sweeper has not yet published this user's address to the book. Refresh the
    /// book (run the sweeper keygen over the current roster and republish) — the bot
    /// never guesses an address it cannot derive.
    NotProvisioned(UserId),
}

impl std::fmt::Display for DepositError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DepositError::NotProvisioned(user) => write!(
                f,
                "no deposit address provisioned for user {user} (watch-only): the sweeper \
                 must publish this user's address into DREGG_PAY_ADDRESS_BOOK"
            ),
        }
    }
}

impl std::error::Error for DepositError {}

/// The bot's payment/earning state. Held in `BotState`; the pay commands + the `/dungeon` gate
/// read it. Devnet/mock by default (a throwaway seed + a [`MockWatcher`]); mainnet is an operator
/// env flip ([`PayConfig::from_env`]).
pub struct PayState {
    /// Operator config (mint/treasury/seed/price/network). Nothing mainnet hardcoded.
    pub config: PayConfig,
    /// The per-user deposit-address source, SPLIT BY CUSTODY ROLE ([`PayRole`]):
    /// seed-bearing HD derivation ([`DepositSource::Custodial`] — the sweeper/devnet
    /// path) or a seed-free published [`DepositAddressBook`] ([`DepositSource::WatchOnly`]
    /// — the production bot, which holds NO custody key).
    pub deposits: DepositSource,
    /// The per-user run-credit ledger over the sqlite [`SqliteCreditStore`].
    pub ledger: CreditLedger<SqliteCreditStore>,
    /// The payment watcher, SELECTED BY CONFIG ([`select_watcher`]): the real
    /// [`SolanaWatcher`] over the configured RPC for an operator-supplied config
    /// (watch-only — no key, no seed), a [`MockWatcher`] only on the explicit
    /// devnet/mock paths. A mainnet config never rides the mock.
    pub watcher: Arc<dyn Watcher + Send + Sync>,
    /// The bot database (for the user→deposit-index map).
    pub db: Database,
    /// The real-AI paid narrator, if a hosted backend is configured (else paid runs fall back free).
    pub paid: Option<PaidNarrator>,
    /// The two-balance TREASURY the detected game revenue lands in: a USDC payment fuels
    /// the tank ([`Treasury::spend_inference_usd`] draws it down per real-AI run,
    /// fail-closed on empty), a `$DREGG` payment grows the illiquid pile. Persisted over
    /// [`SqliteTreasuryStore`] so it survives a restart. [`PayState::poll_and_credit`]
    /// routes every newly-detected payment through [`Treasury::record_payment`] — this is
    /// the revenue-landing join, live in the game loop (not just in dregg-pay's tests).
    pub treasury: Treasury<SqliteTreasuryStore>,
    /// The NON-CUSTODIAL multichain treasury VIEW: the treasury's declared per-chain
    /// positions (its own addresses + assets), against which cross-chain proof-of-holdings
    /// facts are bound and summed. [`PayState::treasury_holdings`] reports the proven
    /// cross-chain total; only facts binding to a declared position AND backed by a real
    /// consensus proof are counted (a forged/foreign/unproven fact is refused).
    pub treasury_view: TreasuryView,
}

/// The outcome of a gated `/dungeon` narration attempt for one user.
pub enum PaidRunResult {
    /// The user had a run-credit; Bedrock narrated under the per-run budget; ONE credit was debited.
    Paid {
        /// The real-AI narration + honest kind + USD cost.
        narration: PaidNarration,
        /// The user's run-credit balance AFTER the debit.
        remaining: u64,
    },
    /// The user has no run-credits — the caller falls back to the FREE tier / prompts `/buy-credits`.
    NoCredits,
    /// The user HAD a credit but the paid backend failed (unconfigured / budget / network). The
    /// credit was **NOT** debited; the caller falls back to the free tier and surfaces this honestly.
    PaidFailed(NarratorError),
}

impl PayState {
    /// The caller's deterministic Solana deposit address (same user ⇒ same address).
    ///
    /// # Panics
    /// On a WATCH-ONLY [`PayState`] whose published [`DepositAddressBook`] has not yet
    /// provisioned this user. The custodial / devnet paths always resolve, so this is
    /// total for the currently-wired constructors; a watch-only adopter must call
    /// [`PayState::deposit_address_checked`] and handle [`DepositError::NotProvisioned`].
    pub fn deposit_address(&self, discord_id: &str) -> DepositAddress {
        self.deposits
            .address_checked(&UserId::from(discord_id))
            .expect(
                "deposit_address on a watch-only PayState hit an unprovisioned user; \
                 use deposit_address_checked and handle NotProvisioned",
            )
    }

    /// The caller's deposit address, fail-closed on a watch-only bot that has not yet
    /// been handed this user's published address. The watch-only-safe form of
    /// [`PayState::deposit_address`].
    pub fn deposit_address_checked(
        &self,
        discord_id: &str,
    ) -> Result<DepositAddress, DepositError> {
        self.deposits.address_checked(&UserId::from(discord_id))
    }

    /// The base58 deposit address to show a user.
    pub fn deposit_address_base58(&self, discord_id: &str) -> String {
        self.deposit_address(discord_id).to_base58()
    }

    /// Atomic `$DREGG` units per one run credit.
    pub fn price_per_run(&self) -> u64 {
        self.config.price_per_run
    }

    /// Whether the pay backend is on mainnet (real funds) or devnet (safe default).
    pub fn network(&self) -> Network {
        self.config.network
    }

    /// The caller's persisted run-credit balance.
    pub fn balance(&self, discord_id: &str) -> u64 {
        self.ledger.balance(&UserId::from(discord_id))
    }

    /// The caller's persisted run-credit balance **as a `Result`** — the display-honest read.
    ///
    /// [`PayState::balance`] rides the sync [`CreditStore`] trait, whose sqlite impl maps a
    /// storage failure to `0` ([`SqliteCreditStore::balance`] `unwrap_or(0)`). That is the right
    /// degradation for the GATE (a run it cannot price falls back to the free tier) but a lie on
    /// a DISPLAY surface: "you have 0 credits" and "the ledger could not be read" are different
    /// facts, and a user who just paid real `$DREGG` must never be shown the first when the truth
    /// is the second. `/credits` and `/buy-credits` read through here and render a read failure
    /// as "unavailable right now — not a zero", never as `0`.
    pub async fn balance_checked(&self, discord_id: &str) -> Result<u64, sqlx::Error> {
        self.db.pay_credit_balance(discord_id).await
    }

    /// Spend ONE run-credit ([`CreditLedger::debit`]); the balance remaining, or an error when the
    /// user has none. The live `/dungeon` path calls this on a runtime worker AFTER a successful
    /// off-worker Bedrock narration, so a failed hosted call never burns a credit.
    pub fn debit_one(&self, discord_id: &str) -> Result<u64, dregg_pay::DebitError> {
        self.ledger.debit(&UserId::from(discord_id))
    }

    /// Whether a paid run is currently possible for `discord_id`: the user has ≥ 1 credit AND a
    /// hosted narrator backend is configured. (`false` ⇒ the caller uses the free tier.)
    pub fn can_run_paid(&self, discord_id: &str) -> bool {
        self.paid.is_some() && self.balance(discord_id) > 0
    }

    /// Persist the user→deposit-index assignment (first assignment wins, so the address is stable),
    /// so an operator can later migrate to collision-free monotonic indices without changing it.
    pub async fn record_deposit_assignment(&self, discord_id: &str) -> Result<(), sqlx::Error> {
        let user = UserId::from(discord_id);
        let index = dregg_pay::user_index(&user);
        // Watch-only + not-yet-provisioned: nothing to persist until the sweeper
        // publishes this user's address. Not an error — the next book refresh fills it.
        let addr = match self.deposits.address_checked(&user) {
            Ok(a) => a.to_base58(),
            Err(_) => return Ok(()),
        };
        self.db
            .pay_assign_deposit_index(discord_id, index, &addr, now_secs())
            .await
    }

    /// **Poll the watcher for this user's deposit address and credit any new payment.** Idempotent
    /// via the payment reference (a re-poll never double-credits). Returns every credit outcome
    /// observed this poll (empty when nothing new landed).
    ///
    /// **The revenue-landing join.** Every payment newly processed this poll is also routed
    /// through the [`Treasury`] ([`Treasury::record_payment`]): a USDC payment fuels the tank,
    /// a `$DREGG` payment grows the pile — the dual-asset accounting, live in the game loop.
    /// A re-observed payment (`AlreadyCredited`) is idempotent at the ledger AND here, so the
    /// treasury never double-counts.
    pub fn poll_and_credit(&self, discord_id: &str) -> Result<Vec<CreditOutcome>, WatchError> {
        let user = UserId::from(discord_id);
        // Watch-only + not-yet-provisioned: there is no address to poll yet. An
        // address the bot cannot resolve is nothing to watch — return empty, not an
        // error (the sweeper's next book publish makes it observable).
        let addr = match self.deposits.address_checked(&user) {
            Ok(a) => a,
            Err(_) => return Ok(Vec::new()),
        };
        let payments = self.watcher.poll(&user, &addr)?;
        let mut outcomes = Vec::with_capacity(payments.len());
        for p in &payments {
            let outcome = self.ledger.credit(p);
            // Route only NEWLY-received revenue into the treasury. `Credited` /
            // `BelowOneRun` both mean the ledger processed this reference for the first
            // time (real money arrived, sub-run dust included); `AlreadyCredited` /
            // `BalanceOverflow` must NOT touch the treasury (no double-count / not banked).
            if matches!(
                outcome,
                CreditOutcome::Credited { .. } | CreditOutcome::BelowOneRun { .. }
            ) {
                self.treasury.record_payment(p.asset, p.amount);
            }
            outcomes.push(outcome);
        }
        Ok(outcomes)
    }

    /// The treasury's FUEL balance (atomic USDC) — what the real-AI runs burn.
    pub fn treasury_fuel(&self) -> u64 {
        self.treasury.usdc_balance()
    }

    /// The treasury's PILE balance (atomic `$DREGG`) — the accumulating illiquid holding.
    pub fn treasury_pile(&self) -> u64 {
        self.treasury.dregg_balance()
    }

    /// Draw down the fuel tank for one real-AI run costing `cost_usd` (real USD).
    /// Fails closed with [`TreasuryError::InsufficientFuel`] when the tank is dry — the
    /// "must refuel" signal. This is the treasury side of EVERY run regardless of how it
    /// was paid: a `$DREGG`-paid run still burns USD fuel while only the pile grew.
    pub fn treasury_spend_inference_usd(&self, cost_usd: f64) -> Result<u64, TreasuryError> {
        self.treasury.spend_inference_usd(cost_usd)
    }

    /// **The multichain view seam.** Report the treasury's PROVEN cross-chain holdings by
    /// binding each supplied [`ProvenForeignHolding`] fact (rendered by the light clients,
    /// pointed at the treasury's own addresses) to a declared position in
    /// [`PayState::treasury_view`]. A fact is COUNTED only when it binds to a declared
    /// (chain, address, asset) position AND carries a real consensus proof; a fact for a
    /// foreign address, an untracked chain, an unproven RPC echo, or a duplicate is
    /// refused (fail-closed) and reported in [`MultichainHoldings::rejected`].
    pub fn treasury_holdings(&self, facts: &[ProvenForeignHolding]) -> MultichainHoldings {
        self.treasury_view.proven_holdings(facts)
    }

    /// The treasury's declared per-chain positions (its own addresses + assets).
    pub fn treasury_slots(&self) -> &[TreasurySlot] {
        self.treasury_view.slots()
    }

    /// **The gate seam.** Try a PAID real-AI run for `discord_id`:
    ///
    /// * balance `0` ⇒ [`PaidRunResult::NoCredits`] (caller uses the free tier / prompts to buy);
    /// * else narrate via real Bedrock under the per-run budget, then — only on success —
    ///   [`CreditLedger::debit`] one credit ⇒ [`PaidRunResult::Paid`];
    /// * a paid-backend failure ⇒ [`PaidRunResult::PaidFailed`] and NO debit (fall back free).
    ///
    /// Debiting AFTER a successful narration means a failed hosted call never burns a credit.
    pub fn try_paid_run(&self, discord_id: &str, system: &str, prompt: &str) -> PaidRunResult {
        let user = UserId::from(discord_id);
        if self.ledger.balance(&user) == 0 {
            return PaidRunResult::NoCredits;
        }
        let Some(paid) = &self.paid else {
            return PaidRunResult::PaidFailed(NarratorError::Backend(
                "no hosted narrator backend configured (set AWS creds / DREGG_NARRATOR=bedrock)"
                    .to_string(),
            ));
        };
        match paid.narrate(system, prompt) {
            Ok(narration) => {
                let remaining = self.ledger.debit(&user).unwrap_or(0);
                PaidRunResult::Paid {
                    narration,
                    remaining,
                }
            }
            Err(e) => PaidRunResult::PaidFailed(e),
        }
    }

    /// A minimal DEVNET/MOCK pay state with NO hosted backend (paid runs fall back to the free
    /// tier). Never touches AWS or the network — for constructing a `BotState` in contexts that do
    /// not exercise paid narration (e.g. the HTTP-surface tests). Does not query the store, so it is
    /// safe to build from any runtime flavor. The [`MockWatcher`] here is EXPLICIT — it is this
    /// constructor's honest name, and the config is always the devnet/mock fallback.
    pub fn devnet_mock_no_backend(
        db: Database,
        bot_secret: &[u8; 32],
        handle: tokio::runtime::Handle,
    ) -> PayState {
        let config = devnet_mock_config(bot_secret);
        let deposits = DepositSource::Custodial(HdDeposit::new(&config));
        let store = SqliteCreditStore::new(db.clone(), handle.clone());
        let ledger = CreditLedger::new(store, config.price_per_run.max(1));
        let watcher: Arc<dyn Watcher + Send + Sync> = Arc::new(MockWatcher::new(MockChain::new()));
        let treasury = Treasury::new(
            SqliteTreasuryStore::new(db.clone(), handle),
            config.usdc_decimals,
        );
        let treasury_view = build_treasury_view(&config);
        PayState {
            config,
            deposits,
            ledger,
            watcher,
            db,
            paid: None,
            treasury,
            treasury_view,
        }
    }

    /// Build the pay state from the operator environment, falling back to a DEVNET/MOCK config.
    ///
    /// * [`PayConfig::from_env`] is used when the `DREGG_PAY_*` env is set (the operator path, the
    ///   only route to mainnet); otherwise a devnet config with a THROWAWAY seed derived from the
    ///   bot secret and placeholder (non-mainnet) mint/treasury. If `DREGG_PAY_NETWORK=mainnet`
    ///   is set but the config is incomplete, this PANICS naming the missing piece — a requested
    ///   real network never silently rides the devnet/mock fallback.
    /// * **The watcher is selected by config** ([`select_watcher`]): an operator-supplied config
    ///   gets the REAL [`SolanaWatcher`] over `DREGG_PAY_RPC` (watch-only — it observes deposit
    ///   addresses over JSON-RPC and never touches the custody seed; the seed-holding SWEEPER is
    ///   a separate operator service). The [`MockWatcher`] is reachable ONLY explicitly: the
    ///   no-env devnet fallback, or `DREGG_PAY_MOCK=1` on a non-mainnet network. A mainnet
    ///   config with the mock flag, or without a real RPC, PANICS at construction (fail loud,
    ///   never a silent mock on a real network).
    /// * The paid narrator is wired to real Bedrock when AWS creds appear present; otherwise `None`
    ///   (paid runs fall back to the free tier).
    pub fn from_env_or_devnet(
        db: Database,
        bot_secret: &[u8; 32],
        handle: tokio::runtime::Handle,
    ) -> PayState {
        let (config, from_operator_env) = match PayConfig::from_env() {
            Ok(config) => (config, true),
            Err(e) => {
                // The fallback is DEVNET/MOCK. If the operator ASKED for mainnet, an
                // incomplete config must fail loud — never a mock silently watching
                // (i.e. not watching) a real network's money.
                if matches!(std::env::var("DREGG_PAY_NETWORK").as_deref(), Ok("mainnet")) {
                    panic!(
                        "DREGG_PAY_NETWORK=mainnet but the pay config is incomplete ({e}); \
                         refusing the devnet/mock fallback on a real-network request — set the \
                         missing DREGG_PAY_* variable or unset DREGG_PAY_NETWORK"
                    );
                }
                (devnet_mock_config(bot_secret), false)
            }
        };
        let selected = select_watcher(
            &config,
            from_operator_env,
            explicit_mock_flag(),
            handle.clone(),
        )
        .unwrap_or_else(|e| panic!("pay watcher construction refused: {e}"));
        tracing::info!(
            "Pay watcher selected: {} (network={:?}, rpc={})",
            selected.kind(),
            config.network,
            config.rpc_endpoint
        );
        let watcher = selected.into_watcher();
        // ── CUSTODY SPLIT ─────────────────────────────────────────────────────
        // This constructor builds the SEED-BEARING (custodial) deposit source: it
        // holds `DREGG_PAY_SEED` and can derive every user's key. That is correct for
        // the devnet-mock fallback (throwaway seed) and for a deliberately-custodial
        // operator, but a PUBLIC bot host should run WATCH-ONLY
        // ([`PayState::watch_only_from_env`], which never loads the seed). Make the
        // posture explicit and loud so custody is never silent.
        let role = PayRole::from_env();
        if from_operator_env && config.has_seed() {
            if role.is_sweeper() {
                tracing::warn!(
                    "Pay custody: DREGG_PAY_ROLE=sweeper — this process HOLDS the HD seed and \
                     can move every user's deposit. Run it only in the operator's secured signer, \
                     never on the public bot host."
                );
            } else {
                tracing::warn!(
                    "Pay custody: this process loaded DREGG_PAY_SEED and is therefore CUSTODIAL, \
                     though DREGG_PAY_ROLE is not 'sweeper'. A public bot should be WATCH-ONLY: \
                     publish a DepositAddressBook from the sweeper and construct the pay state via \
                     watch_only_from_env (no seed). Set DREGG_PAY_ROLE=sweeper to acknowledge \
                     custody, or move to the watch-only path."
                );
            }
        }
        let deposits = DepositSource::Custodial(HdDeposit::new(&config));
        let store = SqliteCreditStore::new(db.clone(), handle.clone());
        let ledger = CreditLedger::new(store, config.price_per_run.max(1));
        let paid = build_bedrock_narrator();
        let treasury = Treasury::new(
            SqliteTreasuryStore::new(db.clone(), handle),
            config.usdc_decimals,
        );
        let treasury_view = build_treasury_view(&config);
        PayState {
            config,
            deposits,
            ledger,
            watcher,
            db,
            paid,
            treasury,
            treasury_view,
        }
    }

    /// Build a **WATCH-ONLY (seed-free) pay state** from the operator environment —
    /// the intended production discord-bot path, splitting the seed OUT of the bot.
    ///
    /// It reads the PUBLIC config ([`PayConfig::watch_only_from_env`], which never
    /// reads `DREGG_PAY_SEED`), constructs the REAL [`SolanaWatcher`] over the
    /// configured RPC ([`select_watcher`]), and serves deposit addresses from the
    /// public [`DepositAddressBook`] the sweeper published at the file named by
    /// `DREGG_PAY_ADDRESS_BOOK`. This process holds NO custody key: a host compromise
    /// leaks no seed and cannot move user funds.
    ///
    /// Fails closed with a [`dregg_pay::ConfigError`] when the public config is
    /// incomplete or the address-book file is missing/unreadable/malformed — a
    /// watch-only bot never falls back to a guessed address or a silent mock.
    ///
    /// The seed-holding sweeper is a SEPARATE service
    /// ([`PayState::from_env_or_devnet`] with `DREGG_PAY_ROLE=sweeper`, run in the
    /// operator's secured signer); it periodically re-derives the book over the
    /// current user roster ([`DepositAddressBook::generate_for_users`]) and
    /// republishes it here.
    ///
    /// NOTE (adoption seam): a watch-only deposit lookup is fallible for a not-yet-
    /// provisioned user, so the command layer must call
    /// [`PayState::deposit_address_checked`] (not [`PayState::deposit_address`]) and
    /// surface [`DepositError::NotProvisioned`] ("your address is being provisioned —
    /// try again shortly"). Wiring `main.rs` to this constructor + that command change
    /// is the remaining step to flip the default.
    pub fn watch_only_from_env(
        db: Database,
        handle: tokio::runtime::Handle,
    ) -> Result<PayState, dregg_pay::ConfigError> {
        let config = PayConfig::watch_only_from_env()?;
        // Real watcher by config (watch-only observation; no seed touched). A
        // watch-only deployment is always an operator-supplied config.
        let selected = select_watcher(&config, true, explicit_mock_flag(), handle.clone())
            .unwrap_or_else(|e| panic!("pay watcher construction refused: {e}"));
        tracing::info!(
            "Pay (watch-only) watcher selected: {} (network={:?}, rpc={})",
            selected.kind(),
            config.network,
            config.rpc_endpoint
        );
        let watcher = selected.into_watcher();
        let book_path = std::env::var("DREGG_PAY_ADDRESS_BOOK").map_err(|_| {
            dregg_pay::ConfigError::MissingEnv("DREGG_PAY_ADDRESS_BOOK".to_string())
        })?;
        let tsv = std::fs::read_to_string(&book_path).map_err(|e| {
            dregg_pay::ConfigError::BadValue(format!("DREGG_PAY_ADDRESS_BOOK ({book_path}): {e}"))
        })?;
        let book = DepositAddressBook::from_tsv(&tsv)?;
        tracing::info!(
            "Pay (watch-only): loaded {} published deposit addresses from {} (no seed held)",
            book.len(),
            book_path
        );
        let deposits = DepositSource::WatchOnly(book);
        let store = SqliteCreditStore::new(db.clone(), handle.clone());
        let ledger = CreditLedger::new(store, config.price_per_run.max(1));
        let paid = build_bedrock_narrator();
        let treasury = Treasury::new(
            SqliteTreasuryStore::new(db.clone(), handle),
            config.usdc_decimals,
        );
        let treasury_view = build_treasury_view(&config);
        Ok(PayState {
            config,
            deposits,
            ledger,
            watcher,
            db,
            paid,
            treasury,
            treasury_view,
        })
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Watcher selection — the REAL SolanaWatcher by config; the mock only EXPLICITLY.
//
// The healed sin: both PayState constructors used to build a MockWatcher
// UNCONDITIONALLY, so a Mainnet config handed out real deposit addresses that
// NOTHING watched. Selection is now a pure, tested function of the config.
// ─────────────────────────────────────────────────────────────────────────────

/// The devnet default RPC endpoint `PayConfig` falls back to when `DREGG_PAY_RPC` is
/// unset. On a MAINNET config this default means "no real RPC was configured" — a
/// mainnet watcher pointed at devnet observes nothing real, which is the same
/// unwatched-money sin — so selection treats it as missing and fails loud.
const DEVNET_DEFAULT_RPC: &str = "https://api.devnet.solana.com";

/// `DREGG_PAY_MOCK=1` (or `true`) — the ONLY named flag that puts an
/// operator-supplied non-mainnet config on the [`MockWatcher`].
fn explicit_mock_flag() -> bool {
    matches!(
        std::env::var("DREGG_PAY_MOCK").as_deref(),
        Ok("1") | Ok("true")
    )
}

/// Why watcher construction was REFUSED. Loud and named — never a silent mock on a
/// real-network config.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WatcherSelectError {
    /// `DREGG_PAY_MOCK` was set on a MAINNET config. Real funds never ride the mock,
    /// even on request — that combination is a misconfiguration, not a choice.
    MockOnMainnet,
    /// The network is real but no usable RPC endpoint was configured (empty, or —
    /// on mainnet — still the devnet default, i.e. `DREGG_PAY_RPC` was never set).
    RpcMissing {
        /// The network that demanded a real RPC.
        network: Network,
        /// The endpoint that was rejected (empty or the devnet default).
        endpoint: String,
    },
}

impl std::fmt::Display for WatcherSelectError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            WatcherSelectError::MockOnMainnet => write!(
                f,
                "DREGG_PAY_MOCK is set on a MAINNET config — real funds never ride the \
                 mock watcher; unset DREGG_PAY_MOCK or set DREGG_PAY_NETWORK=devnet"
            ),
            WatcherSelectError::RpcMissing { network, endpoint } => write!(
                f,
                "network={network:?} needs a real Solana RPC endpoint but DREGG_PAY_RPC \
                 is not usable (got {endpoint:?}); set DREGG_PAY_RPC to your cluster's \
                 JSON-RPC URL"
            ),
        }
    }
}

impl std::error::Error for WatcherSelectError {}

/// The watcher [`select_watcher`] chose — kept concrete so callers (and tests) can
/// see WHICH path was selected before erasing to `Arc<dyn Watcher>`.
pub enum SelectedWatcher {
    /// The REAL path: [`SolanaWatcher`] over JSON-RPC. Watch-only — it reads SPL
    /// token-account state for the deposit addresses; it holds no key and never
    /// touches `DREGG_PAY_SEED`.
    RealSolana(SolanaWatcher<RpcAccountFetcher>),
    /// The explicit devnet/mock path: [`MockWatcher`] over a fresh [`MockChain`].
    Mock(MockWatcher),
}

impl SelectedWatcher {
    /// `true` on the real Solana-RPC path.
    pub fn is_real(&self) -> bool {
        matches!(self, SelectedWatcher::RealSolana(_))
    }

    /// The honest label surfaced in the boot log.
    pub fn kind(&self) -> &'static str {
        match self {
            SelectedWatcher::RealSolana(_) => "solana-rpc (real, watch-only)",
            SelectedWatcher::Mock(_) => "mock (explicit devnet/mock)",
        }
    }

    /// Erase to the trait object [`PayState`] polls.
    pub fn into_watcher(self) -> Arc<dyn Watcher + Send + Sync> {
        match self {
            SelectedWatcher::RealSolana(w) => Arc::new(w),
            SelectedWatcher::Mock(w) => Arc::new(w),
        }
    }
}

// The inner watchers aren't `Debug`; print just the selected variant (its honest
// `kind()` label) so `select_watcher(...).unwrap_err()` and test assertions work
// without a derive cascade onto `SolanaWatcher` / `MockWatcher`.
impl std::fmt::Debug for SelectedWatcher {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("SelectedWatcher")
            .field(&self.kind())
            .finish()
    }
}

/// **Select the payment watcher from the config** — pure in its inputs, so the rule
/// is directly testable (no env mutation):
///
/// * **Mainnet** ⇒ the REAL [`SolanaWatcher`] over the configured RPC, always.
///   `explicit_mock` on mainnet is refused ([`WatcherSelectError::MockOnMainnet`]);
///   an empty RPC or the untouched devnet default is refused
///   ([`WatcherSelectError::RpcMissing`]). Never a silent mock, never a mainnet
///   watcher pointed at devnet.
/// * **Devnet, operator-supplied config** (`from_operator_env`) ⇒ the REAL watcher
///   against the configured (devnet) RPC — the operator named a real mint on a real
///   cluster — unless `explicit_mock` asks for the [`MockWatcher`] by name.
/// * **Devnet fallback config** (no `DREGG_PAY_*` env; `from_operator_env == false`)
///   ⇒ the [`MockWatcher`]. The fallback's mint/treasury are throwaway blake3
///   derivations that exist on NO cluster, so a real watcher there would be
///   meaningless; the mock is the honest labeled interim.
///
/// Construction is watch-only and offline: it builds the RPC client but performs no
/// network call until the first [`Watcher::poll`]. It never reads the seed.
pub fn select_watcher(
    config: &PayConfig,
    from_operator_env: bool,
    explicit_mock: bool,
    handle: tokio::runtime::Handle,
) -> Result<SelectedWatcher, WatcherSelectError> {
    let rpc = config.rpc_endpoint.trim();
    if config.network.is_mainnet() {
        if explicit_mock {
            return Err(WatcherSelectError::MockOnMainnet);
        }
        if rpc.is_empty() || rpc == DEVNET_DEFAULT_RPC {
            return Err(WatcherSelectError::RpcMissing {
                network: config.network,
                endpoint: config.rpc_endpoint.clone(),
            });
        }
        return Ok(SelectedWatcher::RealSolana(SolanaWatcher::new(
            config,
            RpcAccountFetcher::new(rpc, handle),
        )));
    }
    // Non-mainnet: the mock is allowed, but only EXPLICITLY — the bot's own no-env
    // devnet fallback, or the named DREGG_PAY_MOCK flag.
    if explicit_mock || !from_operator_env {
        return Ok(SelectedWatcher::Mock(MockWatcher::new(MockChain::new())));
    }
    if rpc.is_empty() {
        return Err(WatcherSelectError::RpcMissing {
            network: config.network,
            endpoint: config.rpc_endpoint.clone(),
        });
    }
    Ok(SelectedWatcher::RealSolana(SolanaWatcher::new(
        config,
        RpcAccountFetcher::new(rpc, handle),
    )))
}

/// The production [`AccountFetcher`]: Solana JSON-RPC `getTokenAccountsByOwner`
/// (`finalized` commitment, base64 encoding) over the configured endpoint. This is
/// the injected-transport seam [`SolanaWatcher`] polls through.
///
/// **Watch-only.** It READS the deposit wallet's SPL token account (balance + owner
/// program + slot); it holds no keypair, signs nothing, and never sees
/// `DREGG_PAY_SEED`. Everything trust-bearing (SPL-program ownership, mint match,
/// token-owner attribution) is re-checked fail-closed by [`SolanaWatcher::poll`] on
/// the DECODED bytes — the RPC's word is transport, not proof.
///
/// The [`Watcher`] trait is sync but the bot's HTTP client is async, so each fetch
/// drives the request to completion via the same `block_in_place` bridge
/// [`SqliteCreditStore::block`] uses (the bot runs the multi-thread runtime).
pub struct RpcAccountFetcher {
    client: reqwest::Client,
    endpoint: String,
    handle: tokio::runtime::Handle,
}

impl RpcAccountFetcher {
    /// A fetcher against `endpoint`. Builds the client only — no network call here.
    pub fn new(endpoint: impl Into<String>, handle: tokio::runtime::Handle) -> Self {
        RpcAccountFetcher {
            client: reqwest::Client::new(),
            endpoint: endpoint.into(),
            handle,
        }
    }

    /// The endpoint this fetcher polls.
    pub fn endpoint(&self) -> &str {
        &self.endpoint
    }

    /// Drive an async future to completion from the sync `Watcher::poll` — the same
    /// sync↔async bridge as [`SqliteCreditStore::block`].
    fn block<F: std::future::Future>(&self, fut: F) -> F::Output {
        match tokio::runtime::Handle::try_current() {
            Ok(current) => tokio::task::block_in_place(move || current.block_on(fut)),
            Err(_) => self.handle.block_on(fut),
        }
    }
}

impl AccountFetcher for RpcAccountFetcher {
    fn fetch_token_account(
        &self,
        owner: &DepositAddress,
        mint: &[u8; 32],
    ) -> Result<Option<FetchedAccount>, WatchError> {
        let body = serde_json::json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "getTokenAccountsByOwner",
            "params": [
                owner.to_base58(),
                { "mint": bs58::encode(mint).into_string() },
                { "encoding": "base64", "commitment": "finalized" },
            ],
        });
        let resp: serde_json::Value = self.block(async {
            self.client
                .post(&self.endpoint)
                .json(&body)
                .send()
                .await
                .map_err(|e| WatchError::Rpc(format!("rpc send to {}: {e}", self.endpoint)))?
                .error_for_status()
                .map_err(|e| WatchError::Rpc(format!("rpc http status: {e}")))?
                .json::<serde_json::Value>()
                .await
                .map_err(|e| WatchError::Rpc(format!("rpc response not json: {e}")))
        })?;
        if let Some(err) = resp.get("error") {
            return Err(WatchError::Rpc(format!("rpc error: {err}")));
        }
        let result = resp
            .get("result")
            .ok_or_else(|| WatchError::Rpc("rpc response missing `result`".to_string()))?;
        let slot = result
            .pointer("/context/slot")
            .and_then(|s| s.as_u64())
            .ok_or_else(|| WatchError::Rpc("rpc response missing `context.slot`".to_string()))?;
        let value = result
            .get("value")
            .and_then(|v| v.as_array())
            .ok_or_else(|| WatchError::Rpc("rpc response missing `value` array".to_string()))?;
        // No token account for this (owner, mint) yet — nothing landed. NOT an error.
        let Some(entry) = value.first() else {
            return Ok(None);
        };
        let account = entry
            .get("account")
            .ok_or_else(|| WatchError::Rpc("rpc entry missing `account`".to_string()))?;
        let data_b64 = account
            .pointer("/data/0")
            .and_then(|d| d.as_str())
            .ok_or_else(|| WatchError::Rpc("rpc account missing base64 `data`".to_string()))?;
        let encoding = account.pointer("/data/1").and_then(|d| d.as_str());
        if encoding != Some("base64") {
            return Err(WatchError::Rpc(format!(
                "rpc account data encoding is {encoding:?}, expected base64"
            )));
        }
        use base64::Engine as _;
        let data = base64::engine::general_purpose::STANDARD
            .decode(data_b64)
            .map_err(|e| WatchError::Rpc(format!("rpc account data not base64: {e}")))?;
        let owner_program_b58 = account
            .get("owner")
            .and_then(|o| o.as_str())
            .ok_or_else(|| WatchError::Rpc("rpc account missing `owner` program".to_string()))?;
        let owner_program: [u8; 32] = bs58::decode(owner_program_b58)
            .into_vec()
            .ok()
            .and_then(|v| v.try_into().ok())
            .ok_or_else(|| {
                WatchError::Rpc(format!(
                    "rpc account `owner` program not a 32-byte base58 key: {owner_program_b58}"
                ))
            })?;
        Ok(Some(FetchedAccount {
            data,
            owner_program,
            slot,
        }))
    }
}

/// Build the treasury's declared multichain positions from operator config.
///
/// Always declares the **Solana** position — the treasury's own Solana address
/// ([`PayConfig::treasury`]) holding the `$DREGG` mint ([`PayConfig::mint`]) — which the
/// Solana bridge light client can prove non-custodially. Additional per-chain positions
/// (USDC on Base, a denom on a Cosmos hub) are OPERATOR-DECLARED via env — each a
/// base58-encoded 32-byte chain-scoped address + asset (a Solana pubkey, or a
/// left-zero-padded 20-byte EVM/Cosmos address, the same convention
/// [`ProvenForeignHolding::holder`] uses):
///
/// * `DREGG_TREASURY_BASE_ADDR` + `DREGG_TREASURY_BASE_ASSET` → a USDC-on-Base position;
/// * `DREGG_TREASURY_COSMOS_ADDR` + `DREGG_TREASURY_COSMOS_ASSET` + `DREGG_TREASURY_COSMOS_CHAIN`
///   → a position on the named Cosmos hub.
///
/// A missing/unparseable pair is simply not declared (the view stays honest — it never
/// claims a position the operator did not declare). Pointing a proof-of-holdings relayer
/// at these addresses is a named residual (per-chain revenue landing beyond Solana).
fn build_treasury_view(config: &PayConfig) -> TreasuryView {
    let mut slots = vec![TreasurySlot::new(
        ChainId::Solana,
        config.treasury.to_bytes(),
        config.mint,
        "$DREGG on Solana (treasury)",
    )];
    if let Some(slot) = env_slot(
        ChainId::BASE,
        "DREGG_TREASURY_BASE_ADDR",
        "DREGG_TREASURY_BASE_ASSET",
        "USDC on Base (treasury)",
    ) {
        slots.push(slot);
    }
    let cosmos_chain = std::env::var("DREGG_TREASURY_COSMOS_CHAIN")
        .ok()
        .filter(|s| !s.trim().is_empty());
    if let Some(chain_id) = cosmos_chain {
        if let Some(slot) = env_slot(
            ChainId::cosmos(chain_id.trim()),
            "DREGG_TREASURY_COSMOS_ADDR",
            "DREGG_TREASURY_COSMOS_ASSET",
            "denom on Cosmos (treasury)",
        ) {
            slots.push(slot);
        }
    }
    TreasuryView::new(slots)
}

/// Read one operator-declared cross-chain treasury position from env (a base58 32-byte
/// address + asset). `None` if either var is absent or does not decode to 32 bytes — a
/// malformed declaration is skipped, never guessed.
fn env_slot(
    chain: ChainId,
    addr_var: &str,
    asset_var: &str,
    label: &'static str,
) -> Option<TreasurySlot> {
    let addr = dregg_pay::parse_pubkey_base58(&std::env::var(addr_var).ok()?).ok()?;
    let asset = dregg_pay::parse_pubkey_base58(&std::env::var(asset_var).ok()?).ok()?;
    Some(TreasurySlot::new(chain, addr, asset, label))
}

/// A DEVNET/MOCK [`PayConfig`] with a THROWAWAY seed derived from the bot secret and
/// clearly-non-mainnet placeholder mint/treasury. Never a real mainnet value. `price_per_run` from
/// `DREGG_PAY_PRICE_PER_RUN` (default `1_000_000` atomic units = 1 `$DREGG` at 6 decimals).
fn devnet_mock_config(bot_secret: &[u8; 32]) -> PayConfig {
    let seed = blake3::derive_key("dregg-discord-bot/pay-devnet-seed/v1", bot_secret);
    let mint = blake3::derive_key("dregg-discord-bot/pay-devnet-mock-mint/v1", bot_secret);
    let treasury = DepositAddress(blake3::derive_key(
        "dregg-discord-bot/pay-devnet-mock-treasury/v1",
        bot_secret,
    ));
    let price_per_run = std::env::var("DREGG_PAY_PRICE_PER_RUN")
        .ok()
        .and_then(|v| v.parse::<u64>().ok())
        .unwrap_or(1_000_000);
    let mut cfg = PayConfig::devnet_mock(seed.to_vec(), mint, treasury, price_per_run.max(1));
    cfg.network = Network::Devnet;
    cfg
}

/// Wire the paid narrator to real Bedrock when it appears configured, using a per-run USD budget.
/// Returns `None` when no hosted backend is available (paid runs then fall back to the free tier).
fn build_bedrock_narrator() -> Option<PaidNarrator> {
    // Only build a Bedrock client when the operator opted in (`DREGG_NARRATOR=bedrock`) or AWS
    // credentials appear present; otherwise there is no paid backend and runs stay free.
    let opted_in = matches!(std::env::var("DREGG_NARRATOR").as_deref(), Ok("bedrock"))
        || std::env::var_os("AWS_ACCESS_KEY_ID").is_some()
        || std::env::var_os("AWS_PROFILE").is_some();
    if !opted_in {
        return None;
    }
    let client = dregg_narrator::BedrockClient::from_env().ok()?;
    let backend: Arc<dyn ConverseBackend + Send + Sync> = Arc::new(client);
    let model = std::env::var("DREGG_NARRATOR_MODEL")
        .ok()
        .filter(|m| !m.trim().is_empty())
        .unwrap_or_else(|| DEFAULT_MODEL.to_string());
    let usd_per_run = std::env::var("DREGG_NARRATOR_USD_PER_RUN")
        .ok()
        .and_then(|v| v.trim().parse::<f64>().ok())
        .filter(|v| *v > 0.0)
        .unwrap_or(0.05);
    Some(PaidNarrator::new(
        backend,
        ModelRegistry::builtin(),
        model,
        usd_per_run,
        run_max_tokens(),
        run_ledger_dir(),
    ))
}

/// The per-run narration output ceiling (also what the reservation charges at the output rate).
pub fn run_max_tokens() -> u32 {
    std::env::var("DREGG_NARRATOR_MAX_TOKENS")
        .ok()
        .and_then(|v| v.trim().parse::<u32>().ok())
        .filter(|v| *v > 0)
        .unwrap_or(400)
}

/// Where ephemeral per-run budget-ledger files live (`DREGG_NARRATOR_RUN_DIR` or a temp subdir).
fn run_ledger_dir() -> PathBuf {
    std::env::var_os("DREGG_NARRATOR_RUN_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| std::env::temp_dir().join("dregg-pay-runs"))
}

/// Unix seconds now.
fn now_secs() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_narrator::{CLAUDE_HAIKU_4_5, ConverseResponse};
    use dregg_pay::{Asset, MockChain, MockWatcher};

    /// A deterministic mock Converse backend — canned narration + fixed token usage. NEVER touches
    /// AWS; the whole paid gate is driven with no spend. Mirrors the shape a real Bedrock call
    /// returns so the ledger true-up records a real (tiny) cost.
    struct MockBackend {
        reply: String,
        input_tokens: u32,
        output_tokens: u32,
    }
    impl ConverseBackend for MockBackend {
        fn converse(&self, _req: &ConverseRequest) -> Result<ConverseResponse, String> {
            Ok(ConverseResponse {
                text: self.reply.clone(),
                tool_calls: Vec::new(),
                stop_reason: "end_turn".to_string(),
                input_tokens: self.input_tokens,
                output_tokens: self.output_tokens,
            })
        }
    }

    /// A backend that ALWAYS fails — proves a paid failure does NOT burn a credit.
    struct FailingBackend;
    impl ConverseBackend for FailingBackend {
        fn converse(&self, _req: &ConverseRequest) -> Result<ConverseResponse, String> {
            Err("simulated bedrock outage".to_string())
        }
    }

    fn test_bot_secret() -> [u8; 32] {
        [7u8; 32]
    }

    fn build_pay_state(
        db: Database,
        chain: MockChain,
        backend: Arc<dyn ConverseBackend + Send + Sync>,
        ledger_dir: PathBuf,
        price_per_run: u64,
    ) -> PayState {
        build_pay_state_for_asset(db, chain, backend, ledger_dir, price_per_run, Asset::Dregg)
    }

    /// Like [`build_pay_state`] but the mock watcher tags observed payments as `asset`, so a
    /// driven test can exercise the USDC (fuel) or `$DREGG` (pile) treasury-routing leg.
    fn build_pay_state_for_asset(
        db: Database,
        chain: MockChain,
        backend: Arc<dyn ConverseBackend + Send + Sync>,
        ledger_dir: PathBuf,
        price_per_run: u64,
        asset: Asset,
    ) -> PayState {
        // A DEVNET/MOCK config with a throwaway seed — never a real mainnet value.
        let seed = blake3::derive_key("test-pay-seed", &test_bot_secret());
        let mint = [9u8; 32];
        let treasury_addr = DepositAddress([2u8; 32]);
        let config = PayConfig::devnet_mock(seed.to_vec(), mint, treasury_addr, price_per_run);
        let deposits = DepositSource::Custodial(HdDeposit::new(&config));
        let handle = tokio::runtime::Handle::current();
        let store = SqliteCreditStore::new(db.clone(), handle.clone());
        let ledger = CreditLedger::new(store, price_per_run);
        let watcher: Arc<dyn Watcher + Send + Sync> =
            Arc::new(MockWatcher::for_asset(chain, asset));
        let paid = PaidNarrator::new(
            backend,
            ModelRegistry::builtin(),
            CLAUDE_HAIKU_4_5, // priced in the builtin registry
            0.05,             // ample per-run budget
            64,
            ledger_dir,
        );
        let treasury = Treasury::new(
            SqliteTreasuryStore::new(db.clone(), handle),
            config.usdc_decimals,
        );
        let treasury_view = build_treasury_view(&config);
        PayState {
            config,
            deposits,
            ledger,
            watcher,
            db,
            paid: Some(paid),
            treasury,
            treasury_view,
        }
    }

    /// THE HARD GATE, DRIVEN on the MOCK path (no live Discord, no AWS, no funds):
    /// buy → deterministic address → mock payment credits (idempotent) → balance reflects it →
    /// a paid run debits one credit + routes to (mock) Bedrock under a per-run budget →
    /// an empty balance falls back to the free tier → credits PERSIST across a fresh store open.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn full_paid_dungeon_loop_driven_on_the_mock_path() {
        let tmp = tempfile::tempdir().unwrap();
        let db_path = tmp.path().join("credits.db");
        let db_url = format!("sqlite://{}?mode=rwc", db_path.display());
        let ledger_dir = tmp.path().join("runs");

        let db = Database::connect(&db_url).await.unwrap();
        let chain = MockChain::new();
        let backend: Arc<dyn ConverseBackend + Send + Sync> = Arc::new(MockBackend {
            reply: "The vault door groans open; brine floods the ankles of the party.".to_string(),
            input_tokens: 120,
            output_tokens: 48,
        });
        let price_per_run: u64 = 1_000_000; // 1 $DREGG at 6 decimals
        let pay = build_pay_state(
            db.clone(),
            chain.clone(),
            backend,
            ledger_dir,
            price_per_run,
        );

        let user = "424242424242424242";

        // (1) /buy-credits — the deterministic per-user deposit address (same user ⇒ same address).
        let addr1 = pay.deposit_address_base58(user);
        let addr2 = pay.deposit_address_base58(user);
        assert_eq!(addr1, addr2, "same user derives the same deposit address");
        pay.record_deposit_assignment(user).await.unwrap();
        let (idx, stored_addr) = db.pay_get_deposit_index(user).await.unwrap().unwrap();
        assert_eq!(
            stored_addr, addr1,
            "the user→index map persisted the address"
        );
        println!(
            "[buy-credits] user={user} deposit_address={addr1} index={idx} price_per_run={price_per_run}"
        );

        // (2) starts empty.
        assert_eq!(pay.balance(user), 0, "no credits before paying");

        // (3) A payment LANDS on-chain (the mock devnet chain), then a poll credits it.
        let deposit = pay.deposit_address(user); // DepositAddress
        chain.credit_onchain(&deposit, 3 * price_per_run + 250); // 3 runs + dust
        let outcomes = pay.poll_and_credit(user).unwrap();
        assert_eq!(outcomes.len(), 1, "one payment observed");
        match &outcomes[0] {
            CreditOutcome::Credited {
                runs, new_balance, ..
            } => {
                assert_eq!(*runs, 3, "3 runs credited (dust discarded)");
                assert_eq!(*new_balance, 3);
            }
            other => panic!("expected Credited, got {other:?}"),
        }
        assert_eq!(pay.balance(user), 3, "balance reflects the payment");
        println!("[credit] paid 3×price+dust → balance={}", pay.balance(user));

        // (3b) IDEMPOTENT — a re-poll with no new payment does NOT double-credit.
        let again = pay.poll_and_credit(user).unwrap();
        assert!(again.is_empty(), "re-poll sees nothing new");
        assert_eq!(pay.balance(user), 3, "no double-credit");
        // (Idempotency-by-reference — the same payment reference never double-credits — is
        // covered by dregg-pay's own tests + the re-poll assertion above; the earlier
        // manual-reference reconstruction was brittle to dregg-pay's reference scheme.)

        // (4) A PAID /dungeon run — debits ONE credit and routes to (mock) Bedrock under a per-run budget.
        match pay.try_paid_run(
            user,
            "You are the dungeon master.",
            "Describe the drowned antechamber.",
        ) {
            PaidRunResult::Paid {
                narration,
                remaining,
            } => {
                assert_eq!(remaining, 2, "one credit debited");
                assert!(
                    narration.kind.starts_with("bedrock:"),
                    "honest kind: {}",
                    narration.kind
                );
                assert!(
                    !narration.text.trim().is_empty(),
                    "real-AI narration produced"
                );
                assert!(
                    narration.usd_spent > 0.0,
                    "the per-run budget recorded a real cost"
                );
                println!(
                    "[paid-run] kind={} usd_spent={:.6} remaining={remaining}\n           narration={}",
                    narration.kind, narration.usd_spent, narration.text
                );
            }
            _ => panic!("a funded run must be PAID and debit a credit"),
        }
        assert_eq!(pay.balance(user), 2, "balance decremented by the paid run");

        // (5) Drain the remaining credits, then an EMPTY balance FALLS BACK to the free tier.
        assert!(matches!(
            pay.try_paid_run(user, "s", "p"),
            PaidRunResult::Paid { remaining: 1, .. }
        ));
        assert!(matches!(
            pay.try_paid_run(user, "s", "p"),
            PaidRunResult::Paid { remaining: 0, .. }
        ));
        assert_eq!(pay.balance(user), 0);
        match pay.try_paid_run(user, "s", "p") {
            PaidRunResult::NoCredits => println!(
                "[free-fallback] empty balance → free tier (no free-ride of the paid backend)"
            ),
            other => panic!(
                "an empty balance must fall back, not run paid: {}",
                match other {
                    PaidRunResult::Paid { .. } => "Paid",
                    PaidRunResult::PaidFailed(_) => "PaidFailed",
                    PaidRunResult::NoCredits => "NoCredits",
                }
            ),
        }

        // (6) CREDITS PERSIST across a fresh store open (sqlite) — re-credit one run, then reopen.
        chain.credit_onchain(&deposit, price_per_run);
        let _ = pay.poll_and_credit(user).unwrap();
        assert_eq!(pay.balance(user), 1, "one more run credited");
        drop(pay);
        drop(db);
        let db2 = Database::connect(&db_url).await.unwrap();
        let bal = db2.pay_credit_balance(user).await.unwrap();
        assert_eq!(bal, 1, "credits survived a fresh sqlite open (persistence)");
        println!("[persist] reopened DB → balance={bal} (survives restart)");
        println!(
            "HARD GATE PASSED: buy → credit → balance → paid-debit → empty-falls-back → persists"
        );
    }

    /// A paid-backend FAILURE must NOT burn a credit — the caller falls back to the free tier and
    /// the user keeps their balance.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn a_paid_failure_does_not_burn_a_credit() {
        let tmp = tempfile::tempdir().unwrap();
        let db_url = format!("sqlite://{}?mode=rwc", tmp.path().join("c.db").display());
        let db = Database::connect(&db_url).await.unwrap();
        let chain = MockChain::new();
        let backend: Arc<dyn ConverseBackend + Send + Sync> = Arc::new(FailingBackend);
        let price = 100u64;
        let pay = build_pay_state(db, chain.clone(), backend, tmp.path().join("runs"), price);
        let user = "9";
        chain.credit_onchain(&pay.deposit_address(user), price);
        pay.poll_and_credit(user).unwrap();
        assert_eq!(pay.balance(user), 1);
        match pay.try_paid_run(user, "s", "p") {
            PaidRunResult::PaidFailed(_) => {}
            _ => panic!("a failing backend must report PaidFailed"),
        }
        assert_eq!(
            pay.balance(user),
            1,
            "a failed paid call did NOT debit the credit"
        );
    }

    /// THE REVENUE-LANDING JOIN, DRIVEN in the LIVE PayState loop: a detected payment
    /// routes through the Treasury (not just in dregg-pay's own tests). A `$DREGG` payment
    /// lands in the PILE via `poll_and_credit`; a USDC payment lands in the FUEL tank; a
    /// `$DREGG`-paid run still burns USD fuel while only the pile grew (the dual-asset
    /// asymmetry); the treasury persists across a fresh store open; a re-poll never
    /// double-counts.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn treasury_joins_the_live_revenue_loop_dual_asset() {
        let tmp = tempfile::tempdir().unwrap();
        let db_path = tmp.path().join("treasury.db");
        let db_url = format!("sqlite://{}?mode=rwc", db_path.display());
        let db = Database::connect(&db_url).await.unwrap();

        let price: u64 = 1_000_000; // 1 $DREGG at 6 decimals
        let ok_backend: Arc<dyn ConverseBackend + Send + Sync> = Arc::new(MockBackend {
            reply: "brine".to_string(),
            input_tokens: 10,
            output_tokens: 4,
        });

        // ── (A) a $DREGG payment routes to the PILE through the LIVE poll loop ──
        let dregg_chain = MockChain::new();
        let pay = build_pay_state_for_asset(
            db.clone(),
            dregg_chain.clone(),
            ok_backend.clone(),
            tmp.path().join("runs-dregg"),
            price,
            Asset::Dregg,
        );
        let user = "700700700700700700";
        assert_eq!(pay.treasury_pile(), 0);
        assert_eq!(pay.treasury_fuel(), 0);

        let deposit = pay.deposit_address(user);
        dregg_chain.credit_onchain(&deposit, 3 * price + 250); // 3 runs + dust
        let outs = pay.poll_and_credit(user).unwrap();
        assert_eq!(outs.len(), 1, "one payment observed");
        assert_eq!(pay.balance(user), 3, "3 run-credits minted");
        // The FULL received amount (dust included) landed in the pile; the fuel is untouched.
        assert_eq!(
            pay.treasury_pile(),
            3 * price + 250,
            "$DREGG revenue routed to the pile in the live loop"
        );
        assert_eq!(pay.treasury_fuel(), 0, "$DREGG did not touch the fuel tank");

        // A re-poll (no new money) must NOT double-count the treasury.
        let again = pay.poll_and_credit(user).unwrap();
        assert!(again.is_empty(), "re-poll sees nothing new");
        assert_eq!(pay.treasury_pile(), 3 * price + 250, "no double-count");

        // ── (B) the dual-asset asymmetry: a run burns USD fuel, pile only grows ──
        // Operator refuels the tank; a $DREGG-paid run still costs real USD inference.
        pay.treasury.deposit_usdc(100_000); // $0.10 of fuel
        let fuel_before = pay.treasury_fuel();
        let remaining = pay.treasury_spend_inference_usd(0.01).unwrap(); // ~Bedrock cost
        assert!(remaining < fuel_before, "the run drew down the fuel");
        assert_eq!(
            pay.treasury_pile(),
            3 * price + 250,
            "the pile is untouched by inference — it is not fuel"
        );

        // ── (C) a USDC payment routes to the FUEL tank through the SAME live loop ──
        let usdc_chain = MockChain::new();
        let pay_usdc = build_pay_state_for_asset(
            db.clone(),
            usdc_chain.clone(),
            ok_backend,
            tmp.path().join("runs-usdc"),
            price,
            Asset::Usdc,
        );
        // Fuel starts where (B) left it (same persistent treasury row) — record the base.
        let fuel_base = pay_usdc.treasury_fuel();
        let usdc_user = "800800800800800800";
        let usdc_deposit = pay_usdc.deposit_address(usdc_user);
        usdc_chain.credit_onchain(&usdc_deposit, 2 * price);
        let _ = pay_usdc.poll_and_credit(usdc_user).unwrap();
        assert_eq!(
            pay_usdc.treasury_fuel(),
            fuel_base + 2 * price,
            "USDC revenue routed to the fuel tank in the live loop"
        );

        // ── (D) the treasury PERSISTS across a fresh store open (sqlite) ──
        let pile_now = pay.treasury_pile();
        let fuel_now = pay_usdc.treasury_fuel();
        drop(pay);
        drop(pay_usdc);
        drop(db);
        let db2 = Database::connect(&db_url).await.unwrap();
        assert_eq!(
            db2.pay_treasury_dregg().await.unwrap(),
            pile_now,
            "the pile survived a fresh sqlite open"
        );
        assert_eq!(
            db2.pay_treasury_usdc().await.unwrap(),
            fuel_now,
            "the fuel survived a fresh sqlite open"
        );
        println!(
            "[treasury-join] pile={pile_now} fuel={fuel_now} — dual-asset revenue landed + persisted"
        );
    }

    /// THE MULTICHAIN VIEW, EXPOSED + DRIVEN through the PayState accessor: the running
    /// service reports the treasury's proven cross-chain holdings over its declared
    /// per-chain addresses. An honest fact pointed at the treasury's own address is
    /// counted; a forged fact (someone else's address), an untracked chain, and an
    /// unproven RPC echo are each REFUSED, fail-closed.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn multichain_view_reports_proven_cross_chain_holdings() {
        let tmp = tempfile::tempdir().unwrap();
        let db_url = format!("sqlite://{}?mode=rwc", tmp.path().join("mc.db").display());
        let db = Database::connect(&db_url).await.unwrap();
        let backend: Arc<dyn ConverseBackend + Send + Sync> = Arc::new(MockBackend {
            reply: "x".into(),
            input_tokens: 1,
            output_tokens: 1,
        });
        let mut pay = build_pay_state(db, MockChain::new(), backend, tmp.path().join("runs"), 1);

        // The default live view always declares the Solana position (treasury addr + mint).
        assert!(
            pay.treasury_slots()
                .iter()
                .any(|s| s.chain == ChainId::Solana),
            "the live view declares the Solana treasury position"
        );

        // Declare a richer multichain view (throwaway fixture addresses — NEVER mainnet):
        // USDC on Base + $DREGG on Solana + a denom on a Cosmos hub.
        const BASE_TREASURY: [u8; 32] = [0x11; 32];
        const SOLANA_TREASURY: [u8; 32] = [0x22; 32];
        const COSMOS_TREASURY: [u8; 32] = [0x33; 32];
        const USDC_ON_BASE: [u8; 32] = [0xAA; 32];
        const DREGG_ON_SOLANA: [u8; 32] = [0xBB; 32];
        const DENOM_ON_COSMOS: [u8; 32] = [0xCC; 32];
        pay.treasury_view = TreasuryView::new(vec![
            TreasurySlot::new(ChainId::BASE, BASE_TREASURY, USDC_ON_BASE, "USDC on Base"),
            TreasurySlot::new(
                ChainId::Solana,
                SOLANA_TREASURY,
                DREGG_ON_SOLANA,
                "$DREGG on Solana",
            ),
            TreasurySlot::new(
                ChainId::cosmos("cosmoshub-4"),
                COSMOS_TREASURY,
                DENOM_ON_COSMOS,
                "ATOM on Cosmos Hub",
            ),
        ]);

        let fact = |chain, holder, asset, amount, proven| ProvenForeignHolding {
            chain,
            holder,
            asset,
            amount,
            snapshot: 100,
            consensus_proven: proven,
        };
        let attacker = [0xEE; 32];
        let facts = vec![
            // honest, our address → counted
            fact(ChainId::BASE, BASE_TREASURY, USDC_ON_BASE, 5_000_000, true),
            fact(
                ChainId::Solana,
                SOLANA_TREASURY,
                DREGG_ON_SOLANA,
                900_000_000,
                true,
            ),
            // forged: someone else's address on a tracked chain → NotOurPosition
            fact(ChainId::BASE, attacker, USDC_ON_BASE, 9_999_999, true),
            // untracked chain (Ethereum) → UntrackedChain
            fact(ChainId::ETHEREUM, BASE_TREASURY, USDC_ON_BASE, 1, true),
            // our address + asset, but no consensus proof → Unproven (fail closed)
            fact(
                ChainId::cosmos("cosmoshub-4"),
                COSMOS_TREASURY,
                DENOM_ON_COSMOS,
                42_000_000,
                false,
            ),
        ];

        let held = pay.treasury_holdings(&facts);

        // Only the two honest facts are counted; the total is exactly their sum.
        assert_eq!(held.holdings.len(), 2, "two honest holdings counted");
        assert_eq!(held.chains_proven(), 2);
        assert_eq!(held.amount_on(ChainId::BASE), 5_000_000);
        assert_eq!(held.amount_on(ChainId::Solana), 900_000_000);
        assert_eq!(held.total_amount(), 5_000_000 + 900_000_000);

        // The three bad facts are each refused with a legible, fail-closed reason.
        assert_eq!(held.rejected.len(), 3);
        use dregg_pay::HoldingRejection;
        assert!(
            held.rejected
                .iter()
                .any(|r| r.reason == HoldingRejection::NotOurPosition),
            "the forged foreign-address fact is refused"
        );
        assert!(
            held.rejected
                .iter()
                .any(|r| r.reason == HoldingRejection::UntrackedChain),
            "the untracked-chain fact is refused"
        );
        assert!(
            held.rejected
                .iter()
                .any(|r| r.reason == HoldingRejection::Unproven),
            "the unproven RPC-echo fact is refused (fail closed)"
        );
        println!(
            "[treasury-view] proven cross-chain total={} over {} chains ({} facts refused)",
            held.total_amount(),
            held.chains_proven(),
            held.rejected.len()
        );
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Watcher SELECTION — the healed sin. A real-network config must get the
    // REAL SolanaWatcher; the mock only explicitly; misconfig fails LOUD, never
    // a silent mock. `select_watcher` is pure in its inputs, so these tests
    // mutate no env and touch no network (construction never polls).
    // ─────────────────────────────────────────────────────────────────────────

    /// A throwaway config (never mainnet values) with the network/RPC under test.
    fn selection_cfg(network: Network, rpc: &str) -> PayConfig {
        let mut c = PayConfig::devnet_mock(
            *b"seedseedseedseedseedseedseedseed",
            [9u8; 32],
            DepositAddress([2u8; 32]),
            100,
        );
        c.network = network;
        c.rpc_endpoint = rpc.to_string();
        c
    }

    /// A MAINNET config with a configured RPC selects the REAL watcher — the
    /// exact case that used to silently ride the mock.
    #[tokio::test]
    async fn mainnet_config_selects_the_real_solana_watcher() {
        let cfg = selection_cfg(Network::Mainnet, "https://rpc.mainnet.example.invalid");
        let selected = select_watcher(&cfg, true, false, tokio::runtime::Handle::current())
            .expect("a mainnet config with an RPC constructs the real watcher");
        assert!(selected.is_real(), "mainnet must get the REAL watcher");
        assert_eq!(selected.kind(), "solana-rpc (real, watch-only)");
    }

    /// The mock flag on a MAINNET config is REFUSED — real funds never ride the
    /// mock, even on request.
    #[tokio::test]
    async fn mainnet_never_rides_the_mock_even_explicitly() {
        let cfg = selection_cfg(Network::Mainnet, "https://rpc.mainnet.example.invalid");
        let err = select_watcher(&cfg, true, true, tokio::runtime::Handle::current())
            .expect_err("DREGG_PAY_MOCK on mainnet must refuse");
        assert_eq!(err, WatcherSelectError::MockOnMainnet);
        assert!(
            err.to_string().contains("DREGG_PAY_MOCK"),
            "the refusal names the flag: {err}"
        );
    }

    /// A MAINNET config with no usable RPC (empty, or the untouched devnet
    /// default meaning DREGG_PAY_RPC was never set) fails LOUD at construction,
    /// naming DREGG_PAY_RPC — never a silent mock, never a mainnet watcher
    /// pointed at devnet.
    #[tokio::test]
    async fn mainnet_without_a_real_rpc_fails_loud_not_mock() {
        for rpc in ["", "  ", DEVNET_DEFAULT_RPC] {
            let cfg = selection_cfg(Network::Mainnet, rpc);
            let err = select_watcher(&cfg, true, false, tokio::runtime::Handle::current())
                .expect_err("mainnet with no real RPC must refuse construction");
            assert!(
                matches!(err, WatcherSelectError::RpcMissing { .. }),
                "expected RpcMissing for rpc={rpc:?}, got {err:?}"
            );
            assert!(
                err.to_string().contains("DREGG_PAY_RPC"),
                "the error names what is missing: {err}"
            );
        }
    }

    /// An OPERATOR-supplied devnet config (env-configured mint + cluster) gets
    /// the real watcher against the devnet RPC by default.
    #[tokio::test]
    async fn operator_devnet_config_gets_the_real_watcher() {
        let cfg = selection_cfg(Network::Devnet, DEVNET_DEFAULT_RPC);
        let selected = select_watcher(&cfg, true, false, tokio::runtime::Handle::current())
            .expect("an operator devnet config constructs the real watcher");
        assert!(selected.is_real());
    }

    /// The explicit mock flag on a NON-mainnet config selects the mock — the
    /// named, honest testing path.
    #[tokio::test]
    async fn explicit_mock_flag_selects_the_mock_on_devnet() {
        let cfg = selection_cfg(Network::Devnet, DEVNET_DEFAULT_RPC);
        let selected = select_watcher(&cfg, true, true, tokio::runtime::Handle::current())
            .expect("explicit mock on devnet is allowed");
        assert!(!selected.is_real());
        assert_eq!(selected.kind(), "mock (explicit devnet/mock)");
    }

    /// The no-env devnet FALLBACK config (throwaway blake3 mint that exists on
    /// no cluster) stays on the mock — the labeled interim, not a silent one.
    #[tokio::test]
    async fn no_env_devnet_fallback_stays_mock() {
        let cfg = selection_cfg(Network::Devnet, DEVNET_DEFAULT_RPC);
        let selected = select_watcher(&cfg, false, false, tokio::runtime::Handle::current())
            .expect("the devnet fallback constructs the mock");
        assert!(!selected.is_real());
    }

    /// An operator devnet config with an EMPTY RPC also fails loud (not mock).
    #[tokio::test]
    async fn operator_devnet_with_empty_rpc_fails_loud() {
        let cfg = selection_cfg(Network::Devnet, "");
        let err = select_watcher(&cfg, true, false, tokio::runtime::Handle::current())
            .expect_err("an operator config with no RPC must refuse");
        assert!(matches!(err, WatcherSelectError::RpcMissing { .. }));
    }

    // ─────────────────────────────────────────────────────────────────────────
    // The REAL transport, polled — a local mock Solana JSON-RPC server. The
    // HTTP + JSON-RPC + base64 + SPL-layout decode path is the production one;
    // only the cluster behind the socket is canned. NEVER a real cluster.
    // (The live `solana-test-validator` round-trip — real cluster software,
    // still no real funds — is the named residual; see the lane report.)
    // ─────────────────────────────────────────────────────────────────────────

    /// THE CUSTODY SPLIT, at the deposit-source seam: a WATCH-ONLY source holds no
    /// seed and serves only the addresses the sweeper PUBLISHED. A provisioned user
    /// resolves to exactly the published address; an unprovisioned user is fail-closed
    /// [`DepositError::NotProvisioned`] — never a guessed or wrong address (the
    /// "no funds to the void" invariant).
    #[test]
    fn watch_only_deposit_source_is_fail_closed_for_unprovisioned_users() {
        let alice = UserId::from("alice");
        let published = DepositAddress([0x7Au8; 32]);
        let mut book = DepositAddressBook::new();
        book.insert(dregg_pay::user_index(&alice), published);

        let watch_only = DepositSource::WatchOnly(book);
        assert!(
            watch_only.is_watch_only(),
            "no seed on the watch-only source"
        );
        assert_eq!(
            watch_only.address_checked(&alice).unwrap(),
            published,
            "a provisioned user resolves to the published address, exactly"
        );
        assert!(
            matches!(
                watch_only.address_checked(&UserId::from("bob")),
                Err(DepositError::NotProvisioned(_))
            ),
            "an unprovisioned user is fail-closed, never a guessed address"
        );
    }

    /// The deposit address the mock RPC simulates an outage for.
    const RPC_OUTAGE_OWNER: [u8; 32] = [0xEE; 32];

    /// A canned Solana JSON-RPC `getTokenAccountsByOwner`: echoes the queried
    /// (owner, mint) back as a real 165-byte SPL token-account layout holding a
    /// finalized balance of 750, owned by the SPL Token program — exactly the
    /// shape a real RPC returns. The outage owner returns a JSON-RPC error.
    async fn mock_solana_rpc(
        axum::Json(req): axum::Json<serde_json::Value>,
    ) -> axum::Json<serde_json::Value> {
        assert_eq!(
            req["method"], "getTokenAccountsByOwner",
            "the fetcher issues getTokenAccountsByOwner"
        );
        let owner: [u8; 32] = bs58::decode(req["params"][0].as_str().unwrap())
            .into_vec()
            .unwrap()
            .try_into()
            .unwrap();
        if owner == RPC_OUTAGE_OWNER {
            return axum::Json(serde_json::json!({
                "jsonrpc": "2.0", "id": 1,
                "error": { "code": -32000, "message": "simulated rpc outage" },
            }));
        }
        let mint: [u8; 32] = bs58::decode(req["params"][1]["mint"].as_str().unwrap())
            .into_vec()
            .unwrap()
            .try_into()
            .unwrap();
        let mut data = vec![0u8; 165];
        data[0..32].copy_from_slice(&mint);
        data[32..64].copy_from_slice(&owner);
        data[64..72].copy_from_slice(&750u64.to_le_bytes());
        use base64::Engine as _;
        let b64 = base64::engine::general_purpose::STANDARD.encode(&data);
        axum::Json(serde_json::json!({
            "jsonrpc": "2.0", "id": 1,
            "result": {
                "context": { "apiVersion": "2.3.0", "slot": 424_242 },
                "value": [{
                    "pubkey": bs58::encode([7u8; 32]).into_string(),
                    "account": {
                        "data": [b64, "base64"],
                        "executable": false,
                        "lamports": 2_039_280u64,
                        "owner": bs58::encode(dregg_pay::config::SPL_TOKEN_PROGRAM_ID)
                            .into_string(),
                        "rentEpoch": 0,
                    },
                }],
            },
        }))
    }

    /// The mainnet-selected REAL watcher, polled through the production
    /// `RpcAccountFetcher` transport: observes the finalized balance as one
    /// attributed payment, dedups on re-poll, and surfaces a transport failure
    /// as a WatchError (fail closed) — never a silent empty poll.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn real_watcher_polls_through_the_rpc_transport_and_dedups() {
        let app = axum::Router::new().route("/", axum::routing::post(mock_solana_rpc));
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let endpoint = format!("http://{}/", listener.local_addr().unwrap());
        tokio::spawn(async move { axum::serve(listener, app).await.unwrap() });

        let cfg = selection_cfg(Network::Mainnet, &endpoint);
        let selected = select_watcher(&cfg, true, false, tokio::runtime::Handle::current())
            .expect("mainnet + rpc constructs the real watcher");
        let SelectedWatcher::RealSolana(watcher) = selected else {
            panic!("mainnet must select the real watcher");
        };

        let user = UserId::from("alice");
        let deposit = DepositAddress([1u8; 32]);
        let got = watcher.poll(&user, &deposit).unwrap();
        assert_eq!(got.len(), 1, "one finalized payment observed");
        assert_eq!(got[0].amount, 750);
        assert_eq!(got[0].asset, Asset::Dregg);
        assert_eq!(got[0].user, user);
        assert!(
            got[0].reference.0.contains("424242"),
            "the payment ref binds the finalized slot: {}",
            got[0].reference
        );

        // Same finalized balance on re-poll ⇒ nothing new (watcher-level dedup).
        assert!(
            watcher.poll(&user, &deposit).unwrap().is_empty(),
            "re-poll at the same balance credits nothing"
        );

        // A transport failure is an ERROR the caller sees, not a silent empty.
        let outage = DepositAddress(RPC_OUTAGE_OWNER);
        assert!(
            matches!(watcher.poll(&user, &outage), Err(WatchError::Rpc(_))),
            "an RPC failure fails closed"
        );
        println!(
            "[real-transport] getTokenAccountsByOwner → SPL decode → 750 credited once, \
             deduped, outage fails closed"
        );
    }
}
