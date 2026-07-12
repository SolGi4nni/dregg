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
//! 3. **`/balance`** reads [`CreditLedger::balance`] (persisted in sqlite, so it survives restart).
//! 4. A **paid `/dungeon` run** ([`PayState::try_paid_run`]) debits ONE credit
//!    ([`CreditLedger::debit`]) and routes to **real Bedrock** ([`dregg_narrator::metered_converse`])
//!    under a **PER-RUN USD budget** — a fresh [`BudgetLedger`] capped at `usd_per_run` at a unique
//!    path, so the debited credit *is* the budget. This is NOT the single global `$20` cap (a public
//!    bot on one shared cap would let one run drain everyone). An **empty balance** falls back to the
//!    FREE tier (ollama/scripted) — the paid backend is never free-ridden.
//!
//! **Safety.** Nothing mainnet is hardcoded: the mint/treasury/seed are operator config
//! ([`PayConfig::from_env`]); the bot defaults to a DEVNET/MOCK config with a throwaway
//! seed and a [`MockWatcher`] for the interim. The watcher/sweeper holding the custody seed
//! ideally run as a separate operator service; the bot polls a mock/devnet watcher until then.

use std::path::PathBuf;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use dregg_narrator::{
    BudgetLedger, ConverseBackend, ConverseRequest, DEFAULT_MODEL, ModelRegistry, NarratorError,
    metered_converse,
};
use dregg_pay::{
    CreditLedger, CreditOutcome, CreditStore, DepositAddress, DepositAddressProvider, HdDeposit,
    Network, PayConfig, PaymentRef, UserId, WatchError, Watcher,
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

/// The bot's payment/earning state. Held in `BotState`; the pay commands + the `/dungeon` gate
/// read it. Devnet/mock by default (a throwaway seed + a [`MockWatcher`]); mainnet is an operator
/// env flip ([`PayConfig::from_env`]).
pub struct PayState {
    /// Operator config (mint/treasury/seed/price/network). Nothing mainnet hardcoded.
    pub config: PayConfig,
    /// The per-user deposit-address provider (the "B" HD-deposit model).
    pub hd: HdDeposit,
    /// The per-user run-credit ledger over the sqlite [`SqliteCreditStore`].
    pub ledger: CreditLedger<SqliteCreditStore>,
    /// The payment watcher — [`MockWatcher`] on devnet (interim), a Solana watcher for prod.
    pub watcher: Arc<dyn Watcher + Send + Sync>,
    /// The bot database (for the user→deposit-index map).
    pub db: Database,
    /// The real-AI paid narrator, if a hosted backend is configured (else paid runs fall back free).
    pub paid: Option<PaidNarrator>,
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
    pub fn deposit_address(&self, discord_id: &str) -> DepositAddress {
        self.hd.deposit_address(&UserId::from(discord_id))
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
        let addr = self.hd.deposit_address(&user).to_base58();
        self.db
            .pay_assign_deposit_index(discord_id, index, &addr, now_secs())
            .await
    }

    /// **Poll the watcher for this user's deposit address and credit any new payment.** Idempotent
    /// via the payment reference (a re-poll never double-credits). Returns every credit outcome
    /// observed this poll (empty when nothing new landed).
    pub fn poll_and_credit(&self, discord_id: &str) -> Result<Vec<CreditOutcome>, WatchError> {
        let user = UserId::from(discord_id);
        let addr = self.hd.deposit_address(&user);
        let payments = self.watcher.poll(&user, &addr)?;
        Ok(payments.iter().map(|p| self.ledger.credit(p)).collect())
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
    /// safe to build from any runtime flavor.
    pub fn devnet_mock_no_backend(
        db: Database,
        bot_secret: &[u8; 32],
        handle: tokio::runtime::Handle,
    ) -> PayState {
        let config = devnet_mock_config(bot_secret);
        let hd = HdDeposit::new(&config);
        let store = SqliteCreditStore::new(db.clone(), handle);
        let ledger = CreditLedger::new(store, config.price_per_run.max(1));
        let watcher: Arc<dyn Watcher + Send + Sync> =
            Arc::new(dregg_pay::MockWatcher::new(dregg_pay::MockChain::new()));
        PayState {
            config,
            hd,
            ledger,
            watcher,
            db,
            paid: None,
        }
    }

    /// Build the pay state from the operator environment, falling back to a DEVNET/MOCK config.
    ///
    /// * [`PayConfig::from_env`] is used when the `DREGG_PAY_*` env is set (the operator path, the
    ///   only route to mainnet); otherwise a devnet config with a THROWAWAY seed derived from the
    ///   bot secret and placeholder (non-mainnet) mint/treasury.
    /// * The watcher is a [`MockWatcher`] for the interim (the bot polls a mock/devnet watcher; the
    ///   real seed-holding Solana watcher/sweeper run as a separate operator service).
    /// * The paid narrator is wired to real Bedrock when AWS creds appear present; otherwise `None`
    ///   (paid runs fall back to the free tier).
    pub fn from_env_or_devnet(
        db: Database,
        bot_secret: &[u8; 32],
        handle: tokio::runtime::Handle,
    ) -> PayState {
        let config = PayConfig::from_env().unwrap_or_else(|_| devnet_mock_config(bot_secret));
        let hd = HdDeposit::new(&config);
        let store = SqliteCreditStore::new(db.clone(), handle);
        let ledger = CreditLedger::new(store, config.price_per_run.max(1));
        let watcher: Arc<dyn Watcher + Send + Sync> =
            Arc::new(dregg_pay::MockWatcher::new(dregg_pay::MockChain::new()));
        let paid = build_bedrock_narrator();
        PayState {
            config,
            hd,
            ledger,
            watcher,
            db,
            paid,
        }
    }
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
    use dregg_pay::{MockChain, MockWatcher};

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
        // A DEVNET/MOCK config with a throwaway seed — never a real mainnet value.
        let seed = blake3::derive_key("test-pay-seed", &test_bot_secret());
        let mint = [9u8; 32];
        let treasury = DepositAddress([2u8; 32]);
        let config = PayConfig::devnet_mock(seed.to_vec(), mint, treasury, price_per_run);
        let hd = HdDeposit::new(&config);
        let store = SqliteCreditStore::new(db.clone(), tokio::runtime::Handle::current());
        let ledger = CreditLedger::new(store, price_per_run);
        let watcher: Arc<dyn Watcher + Send + Sync> = Arc::new(MockWatcher::new(chain));
        let paid = PaidNarrator::new(
            backend,
            ModelRegistry::builtin(),
            CLAUDE_HAIKU_4_5, // priced in the builtin registry
            0.05,             // ample per-run budget
            64,
            ledger_dir,
        );
        PayState {
            config,
            hd,
            ledger,
            watcher,
            db,
            paid: Some(paid),
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
}
