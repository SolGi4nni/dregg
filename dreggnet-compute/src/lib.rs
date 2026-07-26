//! # DreggNet offering #compute — a COMPUTE EXCHANGE (a market for compute).
//!
//! The dungeon (offering #0) proved the [`Offering`] abstraction over a *game*; the market
//! ([`dreggnet_market`]) over an *auction*; a grain over *compute execution*; polis over
//! *governance*. This crate — the **8th offering** — proves it reaches a **metered compute
//! market**: someone posts a unit of work with an escrowed budget, a worker claims it, runs it,
//! submits a result, and the escrow settles conserved to the worker. It wraps the REAL
//! compute-exchange substrate ([`starbridge_compute_exchange`]) as a [`ComputeOffering`]:
//!
//!   * **POST** ([`advance`](Offering::advance) with [`TURN_POST`]) — a requester lists a job with
//!     a **budget**. A real verified `post` turn ([`build_post_action`]) escrows the budget on the
//!     job cell — `BUDGET` is `WriteOnce` (frozen), `STATE → POSTED`, a genuine [`TurnReceipt`].
//!     The job cell carries the compute-job policy FOR LIFE ([`job_program`]).
//!   * **CLAIM** ([`TURN_CLAIM`]) — a **worker** claims the job at a price `≤ budget`. This is the
//!     substrate's **cap-gated** `bid` ([`fire_bid`] at [`PROVIDER_RIGHTS`]): a real verified turn
//!     binds `PROVIDER_HASH`, writes `BID := price`, advances `STATE POSTED → BID`. The teeth are
//!     the substrate's: a **double-claim** on an already-claimed job is a **real refusal** (the
//!     `POSTED` precondition fails — nothing submitted, anti-ghost); an **over-budget claim** is a
//!     **real executor refusal** (`FieldLteField(BID <= BUDGET)`); a claim with an insufficient cap
//!     is a **real cap refusal**.
//!   * **SETTLE** ([`TURN_SETTLE`]) — the requester releases the escrow once the worker's **result**
//!     is submitted (the result rides the settle affordance's [`Action::text`], the SUBMIT step
//!     folded into settle — the substrate has no separate result method). The substrate's `settle`
//!     ([`fire_settle`] at [`REQUESTER_RIGHTS`]) reads the live `BID` + `BUDGET` and pays the worker
//!     **in full** — `PAID := claim`, `REFUNDED := budget − claim` — the FLASHWELL
//!     `AffineEq(PAID + REFUNDED == BUDGET)` conserving the escrow (**Σδ = 0**, the budget moves to
//!     the worker). A **settle without a valid claim** (no worker), a **settle without a submitted
//!     result**, or a **below-floor job** does **NOT** settle; a settle fired by a non-requester is
//!     a real **cap** refusal.
//!
//! [`verify`](Offering::verify) re-checks the committed chain against on-ledger truth: the escrow
//! conserves (`PAID + REFUNDED == BUDGET`, Σδ = 0), the paid amount is the worker's claim (the
//! budget really moved to the worker), and the on-ledger `PROVIDER_HASH` is the **real claimant**
//! (the winner is who actually claimed). [`render`](Offering::render) / [`actions`](Offering::actions)
//! paint the open job + the post/claim/settle affordances as cap-gated deos affordances.
//!
//! ## The substrate wrapped (consumed, not re-implemented)
//!
//! [`starbridge_compute_exchange`] — its life-of-cell [`job_program`] (the four organ caveats:
//! BUDGET `FieldLteField`, ACCEPTED `WriteOnce`, FLASHWELL `AffineEq`/`AffineLe`, LIFECYCLE
//! `StrictMonotonic`), its `post`/`bid`/`settle` turn-builders + `fire_bid`/`fire_settle` (the
//! cap∧state-gated fires through the embedded verified executor), and its slot schema. We consume
//! the whole job lifecycle + settlement; we re-implement neither. See the `[HONEST SCOPE]` note at
//! the bottom for what a fuller compute market (real GPU workers, a verifiable-compute proof of the
//! run, a wallet-to-wallet token transfer) adds.

use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};

use dregg_app_framework::{
    AgentCipherclerk, AppCipherclerk, AuthRequired, DeosApp, EmbeddedExecutor, FireExecuteError,
    TurnReceipt, field_from_bytes,
};
use dregg_types::CellId;

use starbridge_compute_exchange::{
    BID_SLOT, BUDGET_SLOT, PAID_SLOT, PROVIDER_HASH_SLOT, PROVIDER_RIGHTS, REFUNDED_SLOT,
    REQUESTER_RIGHTS, STATE_BID, STATE_POSTED, STATE_SETTLED, STATE_SLOT, build_post_action,
    fire_bid, fire_settle, job_app, job_program, spec_digest,
};

use deos_view::{MenuItem, ViewNode};

/// The affordance verb a **requester** fires to post a job. `arg` is the job BUDGET (the escrow,
/// the ceiling a claim may cost). One job per session (a re-post is refused). `text` optionally
/// carries the job-spec payload (sealed as `SPEC_HASH`).
pub const TURN_POST: &str = "post";

/// **The budget a fresh POST affordance is PRESENTED with.** Not a policy — a requester types
/// their own over it on any frontend that renders `arg` as a number — but it must be a value
/// [`ComputeOffering::advance`] actually accepts, because a presented affordance a player fires
/// unchanged has to LAND. It was `0`, which `do_post` refuses outright ("a job budget must be
/// positive"), so the single control a fresh compute session offered could only ever refuse.
pub const DEFAULT_JOB_BUDGET: i64 = 100;

/// The affordance verb a **worker** fires to claim the job. `arg` is the claim PRICE — the cost the
/// worker charges (`≤ budget`, the substrate's budget gate). The claim binds the worker as the sole
/// `PROVIDER_HASH`; a double-claim is a real refusal.
pub const TURN_CLAIM: &str = "claim";

/// The affordance verb the **requester** fires to settle: release the escrow to the worker. `arg`
/// is unused; `text` carries the worker's submitted **result** (the SUBMIT step folded in — a settle
/// with no result is refused). The escrow settles conserved (`PAID + REFUNDED == BUDGET`).
pub const TURN_SETTLE: &str = "settle";

/// A live compute-exchange session over the REAL substrate. Owns the embedded verified executor +
/// the deos job app (the on-ledger job cell IS the requester's own cell, carrying [`job_program`]
/// for life), the job terms (budget, floor), the bound requester + claiming worker, the worker's
/// submitted result, and the accumulated [`TurnReceipt`] chain (post + claim + settle — each a real
/// verified turn).
pub struct ComputeSession {
    /// The agent driving the session (the job cell's owner; signs every turn).
    cclerk: AppCipherclerk,
    /// The real embedded verified executor — the sole referee of every POST/CLAIM/SETTLE turn.
    executor: EmbeddedExecutor,
    /// The deos-native job app (the compute job as a composed `DeosApp`; the cap∧state-gated
    /// `bid`/`settle` fires re-enforced by the executor). Built at [`open`](Offering::open).
    app: DeosApp,
    /// The on-ledger job cell (`None` until POST births it) — the requester's own cell, carrying
    /// the compute-job policy (`WriteOnce(BUDGET)` + `StrictMonotonic(STATE)`) FOR LIFE.
    job_cell: Option<CellId>,
    /// The escrowed budget (bound at POST; the ceiling a claim may cost).
    budget: u64,
    /// The market floor — a job whose budget is below it does NOT settle (the minimum viable job).
    floor: u64,
    /// The requester (bound at POST; the party who escrows + settles).
    requester: Option<DreggIdentity>,
    /// The claiming worker (bound at CLAIM; the sole provider). A second claim is refused.
    worker: Option<DreggIdentity>,
    /// The worker's on-ledger provider handle string (hashed into `PROVIDER_HASH`) — verify()
    /// re-derives it to confirm the on-ledger claimant is the real worker.
    worker_handle: Option<String>,
    /// The claim price (the cost the worker charges; `PAID` at settlement).
    claim_price: u64,
    /// The worker's submitted result (the SUBMIT step; required before SETTLE releases the escrow).
    result: Option<String>,
    /// Whether the escrow has settled to the worker.
    settled: bool,
    /// The committed receipt chain (post + claim + settle).
    receipts: Vec<TurnReceipt>,
    /// The deterministic session seed (a re-derivation under this seed reproduces the job identity).
    seed: u64,
}

impl ComputeSession {
    /// Whether a job has been posted (the escrow is bound, `STATE == POSTED`).
    pub fn is_posted(&self) -> bool {
        self.job_cell.is_some()
    }

    /// Whether a worker has claimed the job (`STATE == BID`).
    pub fn is_claimed(&self) -> bool {
        self.worker.is_some()
    }

    /// Whether the escrow has settled to the worker (`STATE == SETTLED`).
    pub fn is_settled(&self) -> bool {
        self.settled
    }

    /// The escrowed budget bound at POST.
    pub fn budget(&self) -> u64 {
        self.budget
    }

    /// The claim price the worker charges (`0` until claimed).
    pub fn claim_price(&self) -> u64 {
        self.claim_price
    }

    /// The number of real verified turns committed (post + claim + settle).
    pub fn receipts_len(&self) -> usize {
        self.receipts.len()
    }

    /// The live on-ledger `STATE` code (`None` until posted): `POSTED` / `BID` / `SETTLED`.
    pub fn onledger_state(&self) -> Option<u64> {
        let cell = self.job_cell?;
        let state = self.executor.cell_state(cell)?;
        Some(field_to_u64(&state.fields[STATE_SLOT]))
    }

    /// The committed settlement, read off the on-ledger job cell: `(paid, refunded, budget)`.
    /// `None` until posted. After a real SETTLE, `paid + refunded == budget` (Σδ = 0) and
    /// `paid == claim_price` (the budget moved to the worker).
    pub fn onledger_settlement(&self) -> Option<(u64, u64, u64)> {
        let cell = self.job_cell?;
        let state = self.executor.cell_state(cell)?;
        Some((
            field_to_u64(&state.fields[PAID_SLOT]),
            field_to_u64(&state.fields[REFUNDED_SLOT]),
            field_to_u64(&state.fields[BUDGET_SLOT]),
        ))
    }

    /// The settlement conservation delta δ = PAID + REFUNDED − BUDGET, read off the on-ledger cell.
    /// `0` on a conserved settle (Σδ = 0). `None` until posted.
    pub fn settlement_delta(&self) -> Option<i128> {
        let (paid, refunded, budget) = self.onledger_settlement()?;
        Some(paid as i128 + refunded as i128 - budget as i128)
    }

    /// Whether the on-ledger `PROVIDER_HASH` is the recorded claimant (the winner is the real
    /// worker). `false` if unclaimed / no cell.
    pub fn onledger_claimant_matches(&self) -> bool {
        let (Some(cell), Some(handle)) = (self.job_cell, self.worker_handle.as_ref()) else {
            return false;
        };
        let Some(state) = self.executor.cell_state(cell) else {
            return false;
        };
        state.fields[PROVIDER_HASH_SLOT] == field_from_bytes(handle.as_bytes())
    }

    /// The cap tier an actor holds on this job, on the observer ⊂ worker ⊂ requester ladder: the
    /// requester (who posted) holds [`REQUESTER_RIGHTS`] (settle + all), the claiming worker holds
    /// [`PROVIDER_RIGHTS`] (claim + view), anyone else is an observer ([`AuthRequired::Signature`]).
    fn cap_for(&self, actor: &DreggIdentity) -> AuthRequired {
        if self.requester.as_ref() == Some(actor) {
            REQUESTER_RIGHTS
        } else if self.worker.as_ref() == Some(actor) {
            PROVIDER_RIGHTS
        } else {
            AuthRequired::Signature
        }
    }

    /// A stable on-ledger worker handle from a [`DreggIdentity`] (hashed into `PROVIDER_HASH`).
    fn handle_of(who: &DreggIdentity) -> String {
        who.as_str().to_string()
    }
}

/// **The compute-exchange offering** — a stateless factory over the compute-job substrate. Each
/// [`open`](Offering::open) deploys a fresh [`ComputeSession`] (its own embedded executor + deos
/// job app); each session hosts ONE job driven POST → CLAIM → SETTLE.
pub struct ComputeOffering {
    /// Run-credits a CLAIM's confined pricing overlay costs (`0` → free tier). The substrate turns
    /// are always free + verifiable; this only prices an optional intelligence overlay a frontend
    /// runs (e.g. estimating the compute cost of a job spec).
    claim_credits: u64,
    /// The market floor — a job whose budget is below it does NOT settle (the minimum viable job).
    /// `0` → no floor.
    floor: u64,
}

impl ComputeOffering {
    /// The free-tier compute exchange (no credit debited per action; no floor).
    pub fn new() -> Self {
        ComputeOffering {
            claim_credits: 0,
            floor: 0,
        }
    }

    /// Set the market floor: a job whose budget is below `floor` does NOT settle.
    pub fn with_floor(mut self, floor: u64) -> Self {
        self.floor = floor;
        self
    }

    /// A paid-tier exchange: each CLAIM costs `credits` run-credits (a frontend debits them; the
    /// substrate turn itself is always free + verifiable).
    pub fn paid_claims(mut self, credits: u64) -> Self {
        self.claim_credits = credits;
        self
    }

    /// POST — a requester lists a job with an escrowed budget. Installs the job program on the job
    /// cell and submits a real verified `post` turn ([`build_post_action`]): `BUDGET` (`WriteOnce`,
    /// frozen), `REQUESTER_HASH`, `SPEC_HASH`, `STATE → POSTED`. The Landed receipt is the post turn.
    fn do_post(&self, s: &mut ComputeSession, input: &Action, actor: DreggIdentity) -> Outcome {
        if s.is_posted() {
            return Outcome::Refused(
                "this session already has a posted job (one job per session)".into(),
            );
        }
        let budget = input.arg.max(0) as u64;
        if budget == 0 {
            return Outcome::Refused("a job budget must be positive".into());
        }
        let cell = s.cclerk.cell_id();

        // Install the life-of-cell compute-job program so the executor re-enforces the four organ
        // caveats on every touching turn, then fund the agent cell so the post turn's budget is
        // covered.
        s.executor.install_program(cell, job_program());
        s.executor.with_ledger_mut(|ledger| {
            if let Some(agent) = ledger.get_mut(&cell) {
                agent.state.set_balance(1_000_000_000);
            }
        });

        // The sealed job spec — the confined execution's task description (here a stable digest of
        // the spec payload; see [HONEST SCOPE]).
        let spec = match &input.text {
            Some(t) => spec_digest(t.as_bytes()),
            None => spec_digest(format!("dreggnet-compute job seed={}", s.seed).as_bytes()),
        };
        let requester = ComputeSession::handle_of(&actor);
        let post = build_post_action(&s.cclerk, cell, &requester, budget, &spec);
        let receipt = match s.executor.submit_action(&s.cclerk, post) {
            Ok(r) => r,
            Err(e) => return Outcome::Refused(format!("the job failed to post: {e}")),
        };

        s.job_cell = Some(cell);
        s.budget = budget;
        s.requester = Some(actor);
        s.receipts.push(receipt.clone());
        Outcome::Landed {
            receipt,
            ended: false,
        }
    }

    /// CLAIM — a worker claims the job at a price `≤ budget`. The substrate's cap-gated `bid`
    /// ([`fire_bid`] at [`PROVIDER_RIGHTS`]): binds `PROVIDER_HASH`, writes `BID := price`, advances
    /// `STATE POSTED → BID`. A double-claim is a real refusal (the `POSTED` precondition fails —
    /// anti-ghost); an over-budget claim is a real executor refusal (`FieldLteField`).
    fn do_claim(&self, s: &mut ComputeSession, input: &Action, actor: DreggIdentity) -> Outcome {
        if !s.is_posted() {
            return Outcome::Refused("nothing is posted yet — POST a job first".into());
        }
        if s.is_settled() {
            return Outcome::Refused("the job has already settled".into());
        }
        if input.arg < 0 {
            return Outcome::Refused("a claim price must be non-negative".into());
        }
        let price = input.arg as u64;
        let held = PROVIDER_RIGHTS;

        if s.is_claimed() {
            // THE ANTI-DOUBLE-CLAIM TOOTH — the job is already claimed (STATE == BID), so the
            // substrate's `bid` POSTED precondition now FAILS. We fire the claim anyway; the deos
            // state gate refuses it IN-BAND and nothing is submitted (anti-ghost).
            let handle = ComputeSession::handle_of(&actor);
            return match fire_bid(&s.app, &held, &handle, price, &s.cclerk, &s.executor) {
                Ok(_) => Outcome::Refused(
                    "a double-claim unexpectedly committed (the POSTED precondition should have refused it)"
                        .into(),
                ),
                Err(e) => Outcome::Refused(format!("double-claim refused: {e}")),
            };
        }

        let handle = ComputeSession::handle_of(&actor);
        match fire_bid(&s.app, &held, &handle, price, &s.cclerk, &s.executor) {
            Ok(receipt) => {
                s.worker = Some(actor);
                s.worker_handle = Some(handle);
                s.claim_price = price;
                s.receipts.push(receipt.clone());
                Outcome::Landed {
                    receipt,
                    ended: false,
                }
            }
            Err(e) => Outcome::Refused(claim_refusal(e)),
        }
    }

    /// SETTLE — the requester releases the escrow to the worker once the worker's **result** is
    /// submitted. The result rides `input.text` (the SUBMIT step folded in). The substrate's
    /// `settle` ([`fire_settle`]) reads live `BID` + `BUDGET` and pays the worker in full
    /// (`PAID := claim`, `REFUNDED := budget − claim`), the FLASHWELL `AffineEq` conserving the
    /// escrow (Σδ = 0). Refused: no valid claim (no worker), no submitted result, a below-floor
    /// job, or a non-requester actor (the cap tooth).
    fn do_settle(&self, s: &mut ComputeSession, input: &Action, actor: DreggIdentity) -> Outcome {
        if !s.is_posted() {
            return Outcome::Refused("nothing is posted yet — POST a job first".into());
        }
        if s.is_settled() {
            return Outcome::Refused("the job has already settled".into());
        }
        // THE NO-VALID-WORKER TOOTH — a settle with no claim does not settle.
        if !s.is_claimed() {
            return Outcome::Refused("no worker has claimed the job — nothing to settle".into());
        }
        // THE RESULT (SUBMIT) TOOTH — the worker must submit a result before the escrow releases.
        let result = match input.text.as_deref() {
            Some(t) if !t.trim().is_empty() => t.to_string(),
            _ => {
                return Outcome::Refused(
                    "no result submitted — the worker must submit a result before settlement"
                        .into(),
                );
            }
        };
        // THE FLOOR TOOTH — a job whose budget is below the market floor does not settle.
        if s.budget < s.floor {
            return Outcome::Refused(format!(
                "the job budget {} is below the market floor {} — it does not settle",
                s.budget, s.floor
            ));
        }

        // The cap tooth: a settle needs REQUESTER_RIGHTS (root). A worker/observer firing settle is
        // refused IN-BAND by the substrate's cap gate (nothing submitted, anti-ghost).
        let held = s.cap_for(&actor);
        match fire_settle(&s.app, &held, &s.cclerk, &s.executor) {
            Ok(receipt) => {
                s.result = Some(result);
                s.settled = true;
                s.receipts.push(receipt.clone());
                Outcome::Landed {
                    receipt,
                    ended: true,
                }
            }
            Err(e) => Outcome::Refused(settle_refusal(e)),
        }
    }
}

impl Default for ComputeOffering {
    fn default() -> Self {
        ComputeOffering::new()
    }
}

impl Offering for ComputeOffering {
    type Session = ComputeSession;

    fn open(&self, cfg: SessionConfig) -> Result<ComputeSession, OfferingError> {
        let seed = cfg.seed.unwrap_or(1);
        // A deterministic federation id from the seed (stable job identity per session).
        let fed = *blake3::hash(format!("dreggnet-compute fed seed={seed}").as_bytes()).as_bytes();
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), fed);
        let executor = EmbeddedExecutor::new(&cclerk, "default");
        // The deos job app over this session's cclerk + executor (the same job cell POST installs).
        let app = job_app(&cclerk, &executor);
        Ok(ComputeSession {
            cclerk,
            executor,
            app,
            job_cell: None,
            budget: 0,
            floor: self.floor,
            requester: None,
            worker: None,
            worker_handle: None,
            claim_price: 0,
            result: None,
            settled: false,
            receipts: Vec::new(),
            seed,
        })
    }

    fn actions(&self, session: &ComputeSession) -> Vec<Action> {
        if !session.is_posted() {
            // ⚑ THE PRESENTED BUDGET MUST BE ONE THE EXECUTOR ACCEPTS. This affordance presented
            // `arg = 0`, and `do_post` hard-refuses a zero budget ("a job budget must be
            // positive") — so the ONLY control a fresh compute session offered was a dead one:
            // pressing exactly what the page said, unchanged, always refused. A frontend that
            // renders `arg` as an editable number (the web does) shows this as the DEFAULT, so it
            // must be a value that lands. `DEFAULT_JOB_BUDGET` is that default; a requester still
            // types their own over it.
            return vec![Action::new(
                format!("Post a compute job (escrow a budget — {DEFAULT_JOB_BUDGET} to start)"),
                TURN_POST,
                DEFAULT_JOB_BUDGET,
                true,
            )];
        }
        if session.is_settled() {
            return Vec::new();
        }
        if !session.is_claimed() {
            return vec![
                Action::new(
                    "Claim the job (a worker offers a price ≤ budget)",
                    TURN_CLAIM,
                    0,
                    true,
                ),
                // SETTLE carries the worker's RESULT on its [`Action::text`] payload (the SUBMIT
                // step folded in — [`do_settle`] hard-refuses on a `None` result). It SOLICITS
                // that text (`taking_text`) so a chat frontend can route the typed result into
                // it; without this the result is always `None` and an in-chat settle is
                // impossible.
                Action::new(
                    "Settle — release the escrow to the worker",
                    TURN_SETTLE,
                    0,
                    false,
                )
                .taking_text(),
            ];
        }
        vec![
            Action::new("Claim the job", TURN_CLAIM, 0, false),
            Action::new(
                "Settle — release the escrow to the worker (submit the result)",
                TURN_SETTLE,
                0,
                true,
            )
            .taking_text(),
        ]
    }

    fn advance(
        &self,
        session: &mut ComputeSession,
        input: Action,
        actor: DreggIdentity,
    ) -> Outcome {
        match input.turn.as_str() {
            TURN_POST => self.do_post(session, &input, actor),
            TURN_CLAIM => self.do_claim(session, &input, actor),
            TURN_SETTLE => self.do_settle(session, &input, actor),
            other => Outcome::Refused(format!("unknown compute affordance: {other}")),
        }
    }

    /// Re-verify the committed chain against on-ledger truth. Before settlement: the job cell is
    /// present and the `STATE` code matches the recorded lifecycle (`POSTED`/`BID`), and — if
    /// claimed — the on-ledger `PROVIDER_HASH` is the real worker. After settlement: the escrow
    /// conserves (`PAID + REFUNDED == BUDGET`, Σδ = 0), the paid amount is the worker's claim (the
    /// budget moved to the worker), and the claimant is real. A forged/inconsistent chain breaks.
    fn verify(&self, session: &ComputeSession) -> VerifyReport {
        let turns = session.receipts_len();
        let Some(cell) = session.job_cell else {
            return VerifyReport::broken(turns, "nothing posted — no chain to verify");
        };
        let Some(state) = session.executor.cell_state(cell) else {
            return VerifyReport::broken(turns, "the job cell is not in the ledger");
        };

        // The escrowed budget is frozen at the posted value (WriteOnce).
        let budget = field_to_u64(&state.fields[BUDGET_SLOT]);
        if budget != session.budget {
            return VerifyReport::broken(turns, "the on-ledger BUDGET is not the posted escrow");
        }

        let onledger_state = field_to_u64(&state.fields[STATE_SLOT]);

        if !session.is_claimed() {
            // Posted, not claimed: STATE must be POSTED.
            if onledger_state != STATE_POSTED {
                return VerifyReport::broken(turns, "posted job is not in STATE POSTED on-ledger");
            }
            return VerifyReport::ok(turns);
        }

        // Claimed: the on-ledger PROVIDER_HASH must be the real worker, BID the real claim.
        if !session.onledger_claimant_matches() {
            return VerifyReport::broken(
                turns,
                "the on-ledger PROVIDER_HASH is not the recorded claimant",
            );
        }
        let onledger_bid = field_to_u64(&state.fields[BID_SLOT]);
        if onledger_bid != session.claim_price {
            return VerifyReport::broken(
                turns,
                "the on-ledger BID is not the recorded claim price",
            );
        }

        if !session.is_settled() {
            // Claimed, not settled: STATE must be BID.
            if onledger_state != STATE_BID {
                return VerifyReport::broken(turns, "claimed job is not in STATE BID on-ledger");
            }
            return VerifyReport::ok(turns);
        }

        // Settled: STATE == SETTLED, and the escrow conserves to the worker.
        if onledger_state != STATE_SETTLED {
            return VerifyReport::broken(turns, "settled job is not in STATE SETTLED on-ledger");
        }
        let paid = field_to_u64(&state.fields[PAID_SLOT]);
        let refunded = field_to_u64(&state.fields[REFUNDED_SLOT]);
        // Conservation Σδ = 0: PAID + REFUNDED == BUDGET (the FLASHWELL the executor enforced).
        if paid as i128 + refunded as i128 - budget as i128 != 0 {
            return VerifyReport::broken(
                turns,
                "the settlement did not conserve the escrow (Σδ ≠ 0)",
            );
        }
        // The budget moved to the worker: PAID is the worker's claim price.
        if paid != session.claim_price {
            return VerifyReport::broken(
                turns,
                "the paid amount is not the worker's claim (the budget did not move to the worker)",
            );
        }
        VerifyReport::ok(turns)
    }

    fn render(&self, session: &ComputeSession) -> Surface {
        let mut children: Vec<ViewNode> = Vec::new();

        if !session.is_posted() {
            children.push(ViewNode::Text(
                "No job yet. A requester posts a unit of work with an escrowed budget.".into(),
            ));
        } else {
            let state = match session.onledger_state() {
                Some(STATE_POSTED) => "POSTED (open for claims)",
                Some(STATE_BID) => "CLAIMED (worker running)",
                Some(STATE_SETTLED) => "SETTLED",
                _ => "—",
            };
            children.push(ViewNode::Section {
                title: "Job".into(),
                tag: "muted".into(),
                children: vec![ViewNode::Text(format!(
                    "budget {} · floor {} · state {} · claim {}",
                    session.budget, session.floor, state, session.claim_price
                ))],
            });
            if session.is_settled() {
                if let Some((paid, refunded, budget)) = session.onledger_settlement() {
                    children.push(ViewNode::Section {
                        title: "Settled".into(),
                        tag: "genuine".into(),
                        children: vec![ViewNode::Text(format!(
                            "paid {} to the worker · refunded {} to the requester · escrow conserved (Σδ=0: {})",
                            paid,
                            refunded,
                            paid + refunded == budget
                        ))],
                    });
                }
            }
        }

        children.push(ViewNode::Section {
            title: "Verified turns".into(),
            tag: "genuine".into(),
            children: vec![ViewNode::Text(session.receipts_len().to_string())],
        });

        let items: Vec<MenuItem> = self
            .actions(session)
            .into_iter()
            .map(|a| MenuItem {
                label: a.label,
                turn: a.turn,
                arg: a.arg,
                enabled: a.enabled,
            })
            .collect();
        if !items.is_empty() {
            children.push(ViewNode::Section {
                title: "Compute actions".into(),
                tag: "accent".into(),
                children: vec![ViewNode::Menu { items }],
            });
        }

        Surface(ViewNode::Section {
            title: "DreggNet Compute — a market for compute".into(),
            tag: "accent".into(),
            children,
        })
    }

    fn price(&self, input: &Action) -> RunCost {
        // The substrate turns are always free + verifiable; only a CLAIM carries the optional
        // confined-pricing overlay a frontend runs (the free tier by default).
        if input.turn == TURN_CLAIM {
            RunCost::credits(self.claim_credits)
        } else {
            RunCost::free()
        }
    }
}

/// Human message for a refused CLAIM — an over-budget claim (`FieldLteField`) is an executor
/// refusal; an insufficient-cap claim is a gate refusal.
fn claim_refusal(e: FireExecuteError) -> String {
    match e {
        FireExecuteError::Executor(inner) => {
            format!("the claim was refused by the executor (over budget / program): {inner}")
        }
        FireExecuteError::Gate(inner) => format!("the claim was refused at the gate: {inner}"),
    }
}

/// Human message for a refused SETTLE — a non-conserving settle is an executor refusal; a
/// non-requester settle is a cap-gate refusal.
fn settle_refusal(e: FireExecuteError) -> String {
    match e {
        FireExecuteError::Executor(inner) => {
            format!("the settle was refused by the executor (non-conserving / program): {inner}")
        }
        FireExecuteError::Gate(inner) => {
            format!("the settle was refused at the cap gate (needs requester rights): {inner}")
        }
    }
}

/// Read a `u64` from the last 8 big-endian bytes of a field element (the inverse of
/// `field_from_u64` for the amount / state registers the job cell stores).
fn field_to_u64(f: &[u8; 32]) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

// [HONEST SCOPE] — what this offering wraps, and what a fuller compute market adds.
//
// WRAPPED (consumed, not re-implemented): the compute-exchange substrate's whole job lifecycle —
// its life-of-cell `job_program` (BUDGET `FieldLteField`, ACCEPTED `WriteOnce`, FLASHWELL
// `AffineEq`/`AffineLe`, LIFECYCLE `StrictMonotonic`), its `build_post_action` post turn, and its
// cap∧state-gated `fire_bid`/`fire_settle` fires through the embedded verified executor. POST =
// `post` (escrow the budget), CLAIM = `bid` (a worker claims ≤ budget, cap-gated), SETTLE =
// `settle` (PAID := claim, REFUNDED := budget − claim, conserved). The refusals are the substrate's
// real teeth: a double-claim (POSTED precondition), an over-budget claim (`FieldLteField`), a
// non-conserving settle (`AffineEq`), a non-requester settle (cap gate). Conservation is the
// substrate's FLASHWELL: PAID + REFUNDED == BUDGET (Σδ = 0), field-accounting on the job cell — it
// is NOT a wallet-to-wallet `Effect::Transfer` between token balances (the substrate models the
// escrow split as committed cell fields, not moving `dregg-payable` balances). "The budget moves to
// the worker" means PAID (the worker's price) is credited on-ledger, refunded to the requester,
// with no mint/burn — the executor-enforced conservation, not a fungible token move.
//
// STUBBED: the confined EXECUTION. The worker's "result" is an offering-level attestation (the
// SUBMIT step folded into SETTLE via the settle affordance's `text`); it is NOT a real grain /
// ToolGateway confined run, and SETTLE checks only that a non-empty result was submitted, not that
// it is the correct output of the job spec. The `SPEC_HASH` seals the task description but no proof
// binds the result to it.
//
// A FULLER COMPUTE MARKET adds: real GPU/CPU workers running the job in a grain-turn / ToolGateway
// jail (a real metered confined execution, not a stubbed digest); a verifiable-compute proof that
// the submitted result is the correct output of the sealed spec (so SETTLE releases on a PROVEN
// result, not an attested one); a wallet-to-wallet token settlement via `Effect::Transfer` /
// `dregg-payable` (so value moves between real balances, not just cell fields); a metering /
// billing dimension (pay per unit of compute consumed, not a flat claim price); and a
// multi-worker / bidding market (many workers competing for a job, the requester picking the best
// price — this offering's one-claim-per-job is the substrate's WriteOnce(PROVIDER_HASH) single
// provider).
