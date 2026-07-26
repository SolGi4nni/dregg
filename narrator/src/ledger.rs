//! # BudgetLedger — the load-bearing piece: a HARD USD ceiling checked at OUR layer.
//!
//! AWS Budgets are notification-only and lag hours — useless as a ceiling. So this ledger
//! enforces the cap itself, around every hosted call, in two beats:
//!
//! * **Pre-flight RESERVATION** ([`BudgetLedger::reserve`]) — before ANY network call, an
//!   upper-bound cost is estimated (a conservative input-token estimate `ceil(bytes/3)` at the
//!   input rate, plus the FULL `max_tokens` charged at the OUTPUT rate). The reservation is
//!   folded into `total_spent_usd` IMMEDIATELY and persisted, so a concurrent invocation — in
//!   this process or another — sees it as already spent. If `spent + reservation > cap`, the
//!   call is refused ([`NarratorError::BudgetExhausted`]) and the reservation is NOT taken:
//!   the network is never touched. That ordering is the whole point.
//! * **Post-flight TRUE-UP** ([`BudgetLedger::true_up`]) — the response's real
//!   `inputTokens`/`outputTokens` price the exact cost, which REPLACES the reservation
//!   (`spent += actual - reservation`). A failed call is [`BudgetLedger::refund`]ed (it cost
//!   nothing). Every mutation runs under an exclusive advisory lock on a sidecar `.lock` file
//!   and persists via write-temp + fsync + atomic rename, so nothing can race past the cap and
//!   no torn write can corrupt the ledger.
//!
//! **Fail-closed on corruption.** A MISSING ledger starts fresh at $0.00 (first run). An
//! UNPARSEABLE ledger refuses ALL calls ([`NarratorError::LedgerCorrupt`]) until an operator
//! resets it explicitly ([`BudgetLedger::reset`]) — it is NEVER silently zeroed, because a
//! silent reset would be a trivial budget bypass (corrupt the file → spend resets → cap gone).

use std::collections::BTreeMap;
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};

use fs2::FileExt;
use serde::{Deserialize, Serialize};

use crate::NarratorError;

/// The default hard ceiling, in USD, when `DREGG_NARRATOR_BUDGET_USD` is unset.
pub const DEFAULT_CAP_USD: f64 = 20.00;

/// WHERE a price came from — the security-relevant provenance of a rate.
///
/// You cannot enforce a budget on a cost you do not know. When a rate is not machine-verifiable,
/// it MUST be pinned as a deliberate UPPER BOUND: if a pinned rate is too LOW the ceiling LEAKS
/// (you sail past the cap and the ledger never notices), so an unverified rate over-charges us —
/// the ceiling can then only ever trip EARLY, never late. `source` is persisted into the ledger
/// and surfaced in logs so this provenance is never invisible.
#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
#[serde(tag = "kind")]
pub enum PriceSource {
    /// A rate read from the PROVIDER'S OWN machine-readable price list — the AWS Pricing API /
    /// bulk price list, or a provider catalog endpoint that publishes per-model rates (Chutes'
    /// `GET /v1/models` → `pricing.{prompt,completion}`). `api` names the exact source and
    /// `date` when it was read.
    ///
    /// It is "verified" in the sense that matters here: nobody typed the number in, so it cannot
    /// be a typo or a wishful under-estimate the way an [`Self::OperatorOverride`] can. It is
    /// still a SNAPSHOT — a provider may raise a published rate afterwards, and a process holding
    /// this would keep metering at the old one until it re-read. That residual is bounded by how
    /// often the rate is re-read (for a catalog read at construction: one process lifetime), and
    /// it is the reason `date` is part of the provenance rather than decoration.
    Verified { api: String, date: String },
    /// A deliberate over-estimate pinned because no verified rate exists. It can only trip the
    /// ceiling early. `rationale` records WHY the bound is safe (which dominating rate it uses).
    ConservativeUpperBound { rationale: String },
    /// An operator-supplied rate (via `DREGG_NARRATOR_PRICE_*`). It is trusted at the operator's
    /// discretion and is NOT guaranteed to be an upper bound — an operator who sets it BELOW true
    /// cost leaks the ceiling, so we label it honestly rather than laundering it as conservative.
    OperatorOverride,
}

impl PriceSource {
    /// A short tag for logs (`verified` / `conservative-upper-bound` / `operator-override`).
    pub fn tag(&self) -> &'static str {
        match self {
            PriceSource::Verified { .. } => "verified",
            PriceSource::ConservativeUpperBound { .. } => "conservative-upper-bound",
            PriceSource::OperatorOverride => "operator-override",
        }
    }
}

/// A per-model price sheet, in USD per 1,000 tokens, carrying its provenance.
///
/// We deliberately use the HIGHER, conservative rows — over-charging our OWN ledger fails safe
/// (we refuse a hair early, never a hair late).
#[derive(Clone, Debug, PartialEq)]
pub struct Pricing {
    /// USD per 1,000 INPUT tokens.
    pub input_per_1k: f64,
    /// USD per 1,000 OUTPUT tokens.
    pub output_per_1k: f64,
    /// Where these rates came from (verified vs a deliberate upper bound).
    pub source: PriceSource,
}

impl Pricing {
    /// The conservative UPPER-BOUND cost of a call whose prompt is `prompt_bytes` long and that
    /// may emit up to `max_tokens`: input tokens bounded by `prompt_bytes` (a token is ≥ 1 byte,
    /// so `input_tokens ≤ bytes` is a true ceiling even for adversarial byte-fallback tokenization)
    /// at the input rate, plus the FULL `max_tokens` at the output rate. This is what the
    /// reservation charges; `true_up` then replaces it with the exact cost, so over-estimating the
    /// input costs nothing but keeps the ceiling from ever leaking on a single call.
    pub fn reservation_cost(&self, prompt_bytes: usize, max_tokens: u32) -> f64 {
        let est_input = prompt_bytes as f64;
        est_input / 1000.0 * self.input_per_1k + max_tokens as f64 / 1000.0 * self.output_per_1k
    }

    /// The EXACT cost of a completed call, from the response's real token counts.
    pub fn actual_cost(&self, input_tokens: u32, output_tokens: u32) -> f64 {
        input_tokens as f64 / 1000.0 * self.input_per_1k
            + output_tokens as f64 / 1000.0 * self.output_per_1k
    }
}

pub(crate) fn env_f64(key: &str) -> Option<f64> {
    std::env::var(key).ok().and_then(|v| v.trim().parse().ok())
}

/// The persisted ledger state. `total_spent_usd` folds in any OUTSTANDING reservations (a
/// reservation is counted as spend the instant it is taken, and corrected on true-up), so a
/// concurrent reader never under-counts.
#[derive(Serialize, Deserialize, Clone, Debug, Default, PartialEq)]
pub struct LedgerState {
    /// Total USD spent, INCLUDING outstanding (not-yet-trued-up) reservations.
    pub total_spent_usd: f64,
    /// Count of COMPLETED (trued-up) calls.
    pub calls: u64,
    /// Per-model breakdown (keyed by model id), completed calls only.
    #[serde(default)]
    pub per_model: BTreeMap<String, ModelSpend>,
}

/// Per-model completed-call accounting, including the price + its provenance so the ledger file
/// itself records WHICH rate (verified vs upper-bound) was charged.
#[derive(Serialize, Deserialize, Clone, Debug, Default, PartialEq)]
pub struct ModelSpend {
    pub calls: u64,
    pub spent_usd: f64,
    pub input_tokens: u64,
    pub output_tokens: u64,
    /// The rate charged for this model (USD per 1,000 tokens) + where it came from. `Option` so
    /// a ledger written by an older build still deserializes.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub input_per_1k: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub output_per_1k: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub price_source: Option<PriceSource>,
}

/// A taken reservation — hold it across the network call, then either [`BudgetLedger::true_up`]
/// it with the real usage or [`BudgetLedger::refund`] it on failure. NOT `Clone`: this is a linear
/// token that must be consumed EXACTLY once — cloning it would let a double true-up/refund subtract
/// `amount` from `total_spent_usd` twice and silently un-cap the budget.
#[derive(Debug)]
#[must_use = "a reservation must be trued-up or refunded, else it permanently counts as spend"]
pub struct Reservation {
    amount: f64,
    model: String,
}

impl Reservation {
    /// The reserved USD amount (the upper-bound cost held against the cap).
    pub fn amount(&self) -> f64 {
        self.amount
    }
    /// The model this reservation was taken for.
    pub fn model(&self) -> &str {
        &self.model
    }
}

/// The USD ceiling enforcer. Cheap to clone (it holds only a path + the cap); it caches NO
/// balance in memory — every operation re-reads the on-disk state under the lock, so separate
/// processes and threads always agree on the running total.
#[derive(Clone, Debug)]
pub struct BudgetLedger {
    path: PathBuf,
    cap_usd: f64,
}

impl BudgetLedger {
    /// A ledger at an explicit path + cap.
    pub fn new(path: impl Into<PathBuf>, cap_usd: f64) -> BudgetLedger {
        BudgetLedger {
            path: path.into(),
            cap_usd,
        }
    }

    /// The ledger resolved from the environment: path from `DREGG_NARRATOR_LEDGER` (default
    /// `~/.dregg/narrator-ledger.json`), cap from `DREGG_NARRATOR_BUDGET_USD` (default $20.00).
    pub fn from_env() -> BudgetLedger {
        let path = std::env::var_os("DREGG_NARRATOR_LEDGER")
            .map(PathBuf::from)
            .unwrap_or_else(default_ledger_path);
        let cap_usd = env_f64("DREGG_NARRATOR_BUDGET_USD").unwrap_or(DEFAULT_CAP_USD);
        BudgetLedger { path, cap_usd }
    }

    /// The hard ceiling, in USD.
    pub fn cap_usd(&self) -> f64 {
        self.cap_usd
    }

    /// The ledger file path.
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// The current total spent (including outstanding reservations). Fails closed on a corrupt
    /// ledger.
    pub fn spent_usd(&self) -> Result<f64, NarratorError> {
        Ok(self.snapshot()?.total_spent_usd)
    }

    /// A read-only snapshot of the whole ledger state. Fails closed on corruption.
    pub fn snapshot(&self) -> Result<LedgerState, NarratorError> {
        self.with_lock(|state| Ok(state.clone()))
    }

    /// Explicitly reset the ledger to a fresh $0.00 state — the ONLY sanctioned way to clear a
    /// corrupt ledger (a corrupt ledger otherwise refuses every call). An operator action.
    pub fn reset(&self) -> Result<(), NarratorError> {
        self.ensure_parent()?;
        let lock = self.lock_file()?;
        lock.lock_exclusive().map_err(io_err)?;
        let res = self.write_state(&LedgerState::default());
        let _ = FileExt::unlock(&lock);
        res
    }

    /// **Pre-flight.** Reserve the upper-bound cost of a call. Folds the reservation into the
    /// persisted total IMMEDIATELY (so concurrent callers see it), or refuses with
    /// [`NarratorError::BudgetExhausted`] — WITHOUT taking the reservation — when it would push
    /// the total past the cap. Callers MUST NOT touch the network until this returns `Ok`.
    pub fn reserve(
        &self,
        model: &str,
        prompt_bytes: usize,
        max_tokens: u32,
        pricing: &Pricing,
    ) -> Result<Reservation, NarratorError> {
        let cap = self.cap_usd;
        let cost = pricing.reservation_cost(prompt_bytes, max_tokens);
        self.with_lock(|state| {
            if state.total_spent_usd + cost > cap {
                return Err(NarratorError::BudgetExhausted {
                    spent: state.total_spent_usd,
                    cap,
                });
            }
            state.total_spent_usd += cost;
            Ok(Reservation {
                amount: cost,
                model: model.to_string(),
            })
        })
    }

    /// **Post-flight.** Replace `reservation` with the EXACT usage-priced cost and record the
    /// completed call (bumping `calls` and the per-model breakdown). Returns the actual cost.
    pub fn true_up(
        &self,
        reservation: Reservation,
        input_tokens: u32,
        output_tokens: u32,
        pricing: &Pricing,
    ) -> Result<f64, NarratorError> {
        let actual = pricing.actual_cost(input_tokens, output_tokens);
        self.with_lock(|state| {
            // Remove the reservation, add the real cost. Clamp at 0 to guard float drift.
            state.total_spent_usd = (state.total_spent_usd - reservation.amount + actual).max(0.0);
            state.calls += 1;
            let m = state
                .per_model
                .entry(reservation.model.clone())
                .or_default();
            m.calls += 1;
            m.spent_usd += actual;
            m.input_tokens += input_tokens as u64;
            m.output_tokens += output_tokens as u64;
            m.input_per_1k = Some(pricing.input_per_1k);
            m.output_per_1k = Some(pricing.output_per_1k);
            m.price_source = Some(pricing.source.clone());
            Ok(actual)
        })
    }

    /// **On failure.** Release a reservation whose call never completed — it cost nothing.
    pub fn refund(&self, reservation: Reservation) -> Result<(), NarratorError> {
        self.with_lock(|state| {
            state.total_spent_usd = (state.total_spent_usd - reservation.amount).max(0.0);
            Ok(())
        })
    }

    // ── internals ──────────────────────────────────────────────────────────────────────────

    /// Run `f` over the ledger state under the exclusive lock. On `Ok`, the (possibly mutated)
    /// state is persisted atomically before the lock is released; on `Err`, nothing is written.
    fn with_lock<T>(
        &self,
        f: impl FnOnce(&mut LedgerState) -> Result<T, NarratorError>,
    ) -> Result<T, NarratorError> {
        self.ensure_parent()?;
        let lock = self.lock_file()?;
        lock.lock_exclusive().map_err(io_err)?;
        let result = (|| {
            let mut state = self.read_state()?;
            let out = f(&mut state)?;
            self.write_state(&state)?;
            Ok(out)
        })();
        let _ = FileExt::unlock(&lock);
        result
    }

    fn ensure_parent(&self) -> Result<(), NarratorError> {
        if let Some(dir) = self.path.parent() {
            if !dir.as_os_str().is_empty() {
                std::fs::create_dir_all(dir).map_err(io_err)?;
            }
        }
        Ok(())
    }

    /// The sidecar lock file (`<ledger>.lock`) — separate from the ledger so the atomic rename
    /// that replaces the ledger never invalidates a held lock handle's inode.
    fn lock_file(&self) -> Result<std::fs::File, NarratorError> {
        let mut p = self.path.clone().into_os_string();
        p.push(".lock");
        std::fs::OpenOptions::new()
            .create(true)
            .read(true)
            .write(true)
            .open(PathBuf::from(p))
            .map_err(io_err)
    }

    /// Read + parse the ledger. MISSING → a fresh $0.00 state (first run). PRESENT but empty,
    /// whitespace, or unparseable → [`NarratorError::LedgerCorrupt`] (fail-closed: refuse every
    /// call). `write_state` only ever writes non-empty JSON, so an existing-but-empty file is
    /// anomalous (truncation / damage / a stray `touch`) — treating it as $0 would silently
    /// un-cap the budget, so we refuse it too. Delete the file to deliberately reset.
    fn read_state(&self) -> Result<LedgerState, NarratorError> {
        let mut file = match std::fs::File::open(&self.path) {
            Ok(f) => f,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(LedgerState::default()),
            Err(e) => return Err(io_err(e)),
        };
        file.seek(SeekFrom::Start(0)).map_err(io_err)?;
        let mut buf = String::new();
        file.read_to_string(&mut buf).map_err(io_err)?;
        if buf.trim().is_empty() {
            return Err(NarratorError::LedgerCorrupt {
                path: self.path.display().to_string(),
                reason: "ledger file is present but empty/whitespace — refusing (fail-closed); \
                         delete it to reset to $0"
                    .to_string(),
            });
        }
        serde_json::from_str(&buf).map_err(|e| NarratorError::LedgerCorrupt {
            path: self.path.display().to_string(),
            reason: e.to_string(),
        })
    }

    /// Persist `state` atomically: write a temp sibling, fsync, rename over the ledger.
    fn write_state(&self, state: &LedgerState) -> Result<(), NarratorError> {
        let json =
            serde_json::to_string_pretty(state).map_err(|e| NarratorError::Io(e.to_string()))?;
        let mut tmp = self.path.clone().into_os_string();
        tmp.push(format!(".tmp.{}", std::process::id()));
        let tmp = PathBuf::from(tmp);
        {
            let mut f = std::fs::File::create(&tmp).map_err(io_err)?;
            f.write_all(json.as_bytes()).map_err(io_err)?;
            f.sync_all().map_err(io_err)?;
        }
        std::fs::rename(&tmp, &self.path).map_err(io_err)?;
        Ok(())
    }
}

fn io_err(e: std::io::Error) -> NarratorError {
    NarratorError::Io(e.to_string())
}

/// `~/.dregg/narrator-ledger.json` (or `./narrator-ledger.json` if `$HOME` is unset).
fn default_ledger_path() -> PathBuf {
    match std::env::var_os("HOME") {
        Some(home) => PathBuf::from(home)
            .join(".dregg")
            .join("narrator-ledger.json"),
        None => PathBuf::from("narrator-ledger.json"),
    }
}
