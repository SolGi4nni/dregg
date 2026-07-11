//! # ORGAN 4 — THE GATEWAY: a live tool-calling agent becomes a mandated inhabitant.
//!
//! A clean Rust seam that turns an inbound, untrusted tool-call into a
//! cap-gated, metered, receipted DELEGATED turn on the verified executor — or an
//! IN-BAND refusal. Any external loop (a buildr agent, a hermes agent, an MCP
//! host) drives it through one method: [`ToolGateway::invoke`]. The gateway holds
//! no policy of its own; the GRANTOR pins the mandate ([`ToolGrant`]) at
//! delegation time, and every call is admitted IFF the delegated policy admits
//! it.
//!
//! ## What this welds (REUSE, not rebuild)
//!
//! * The PROVEN admission crown — `metatheory/Dregg2/Apps/ToolAccessDelegation.lean`:
//!   `delegAdmit g now tool old new = SCOPE ∧ DEADLINE ∧ rate(new = old+1 ∧ 0 ≤ old ∧ new ≤ rateLimit)`,
//!   and `tool_invocation_commit_iff_admit` (the executor's caveat gate commits a
//!   metered `calls_made : c → c+1` write IFF that predicate holds), with the
//!   over-rate / past-deadline / out-of-scope rejection TEETH. [`deleg_admit`] in
//!   this module is the byte-faithful Rust mirror of that Lean predicate; the
//!   `tool_gateway_admit_mirrors_lean_delegadmit` test pins the SAME decision
//!   vector the Lean `#guard`s witness.
//! * The cap-gated executor path — [`crate::SubAgent`] / [`crate::AgentRuntime::spawn_sub_agent_scoped`]:
//!   the worker carries a public-key biscuit credential scoped to EXACTLY the
//!   granted tool method, presented as `Authorization::Token`, so the EXECUTOR
//!   (`verify_token_authorization`) — not an out-of-band `cap.verify()` — admits
//!   the metered write. A call under any other method is rejected by the executor
//!   with `TokenInsufficientCapability`.
//!
//! ## The two enforcement surfaces, both load-bearing
//!
//! A tool invocation is a single scalar write: the worker cell's `calls_made`
//! slot advances `c → c+1`. Admission folds the WHOLE delegated policy:
//!
//! 1. **In-band, before submission** — [`deleg_admit`] decides SCOPE ∧ DEADLINE ∧
//!    RATE exactly as the Lean predicate. A FALSE verdict is a
//!    [`GatewayRefusal`] returned as an `Err` (the anti-ghost tooth — a `Result`
//!    error, NEVER a panic, and NO turn is submitted, so no spend, no counter
//!    advance).
//! 2. **In the executor** — the worker cell carries a [`mandate_program`]
//!    (`FieldLte { calls_made ≤ rateLimit }` ∧ `Monotonic { calls_made }`): even
//!    if a caller bypassed [`deleg_admit`], the executor's own cell-program check
//!    rejects an over-rate or rolled-back counter write. The rate ceiling is
//!    bound into the committed transition, not merely pre-checked.
//!
//! A granted call therefore COMMITS with a receipt and a conserved spend (the
//! counter moves, total balance does not), and an out-of-mandate call is REFUSED
//! in-band — the exact both-polarity shape the Lean crown proves.
//!
//! ## The DATA PLANE — the gateway as a ROUTER, not only a gate
//!
//! [`ToolGateway::invoke`] gates + meters + executes INLINE (synchronous). But a
//! real data plane ROUTES the call: the gate is the on-ramp, not the whole road.
//! [`ToolGateway::enqueue`] runs the SAME admission/metering gate, then ENQUEUES
//! the admitted tool-call onto the gateway's inbox toward an EXECUTION
//! ENVIRONMENT (the worker's executor cell), returning a non-blocking
//! [`RoutedHandle`] (an `EventualRef`-shaped promise) INSTEAD of blocking. The
//! executor later DRAINS the queue ([`ToolGateway::drive_executor`]), runs the
//! metered turn, and the RESULT comes back as a resolved promise plus a
//! [`DeliveryReceipt`] (custody-receipt-shaped: a signed-shape witness that the
//! work was dequeued toward, and executed by, the executor). The caller
//! [`poll`](RoutedHandle::status)s / [`resolve`](ToolGateway::resolve)s the
//! handle to collect the [`RoutedResult`].
//!
//! So the full road is: **admit → enqueue → (execute elsewhere) → results-back**,
//! with the metering + receipts intact, and a refusal short-circuiting at the
//! on-ramp (no enqueue, no spend, no counter advance).
//!
//! The promise/result channel reuses the verified [`PendingTurnRegistry`] /
//! `EventualRef` resolution shape from `dregg_turn` (the cascading
//! resolve/broken-propagation machinery), rather than reinventing it. The queue
//! is modelled as the gateway's in-crate inbox (`VecDeque` of routed work) toward
//! the worker's executor cell; wiring it to the cross-crate captp `MerkleQueue` +
//! real `CustodyReceipt` (so the route can cross a federation / a relay) is the
//! next slice — the ENQUEUE → EXECUTE → RESULTS-BACK shape here is real and
//! tested, not a synchronous rename.

use std::collections::VecDeque;

use dregg_cell::CellId;
use dregg_cell::interface::MethodSig;
use dregg_cell::program::{CellProgram, StateConstraint, field_from_u64};
use dregg_payable::{AssetId, InvokeAuthority, InvokeRefused, Payable};
use dregg_token::Attenuation;
use dregg_turn::action::Action;
use dregg_turn::{
    Effect, PendingTurnRegistry, ResolutionCondition, ResolutionOutcome, TurnReceipt,
};

use crate::cipherclerk::HeldToken;
use crate::error::SdkError;
use crate::runtime::{AgentRuntime, SubAgent};

/// The slot index on the worker cell that holds the rate counter `calls_made`.
///
/// Mirrors the Lean `callsMadeSlot` (`"calls_made"`); here it is a fixed cell
/// field slot so the executor's `FieldLte` / `Monotonic` constraints bite on it.
/// Slot 4 is the conventional first general-purpose slot (slots 0..3 are commonly
/// reserved by other programs); the gateway owns the worker cell, so this choice
/// is private to the mandate.
pub const CALLS_MADE_SLOT: u8 = 4;

/// The grantor's pinned delegation parameters — the immutable bundle fixed at
/// delegation time. The byte-faithful Rust mirror of the Lean `Grant`
/// (`Dregg2.Apps.ToolAccessDelegation.Grant`).
///
/// * `tool_id` — the single allowlisted tool / MCP id the worker is scoped to
///   (the SCOPE). An invocation presenting any other tool id is refused.
/// * `rate_limit` — the granted invocation ceiling `N`: at most `N` calls under
///   this mandate (the RATE).
/// * `deadline` — the expiry height/clock: an invocation presented at
///   `now > deadline` is refused (the DEADLINE).
/// * `tool_method` — the executor-level method verb the worker's biscuit
///   credential is scoped to. This is the SCOPE's executor face: the cap_token
///   covers exactly this method, so the executor rejects a turn under any other
///   verb with `TokenInsufficientCapability`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ToolGrant {
    /// The single allowlisted tool / MCP id (the SCOPE, in-band face).
    pub tool_id: i64,
    /// The granted invocation ceiling `N` (the RATE).
    pub rate_limit: i64,
    /// The expiry height/clock (the DEADLINE).
    pub deadline: i64,
    /// The executor method verb the worker's credential is scoped to (the
    /// SCOPE's executor face).
    pub tool_method: String,
}

/// **The per-call PRICE a tool/model provider charges through the gateway** — the
/// market half of the mandate. Where [`ToolGrant`] meters HOW MANY times a
/// consumer may invoke (the rate budget), a [`Charge`] meters WHAT IT COSTS: each
/// admitted invocation moves `price` of value from the consumer (the gateway's
/// worker cell) to the `provider` cell, and the consumer's spend is capped at
/// `budget`.
///
/// This is the "pay to access another agent's tools/models" layer of the agent
/// service economy: a provider agent B offers a tool through the gateway with a
/// price; a consumer agent A's call is cap-checked + rate-metered (the
/// [`ToolGrant`]) AND charged (this [`Charge`]) — a real conserving
/// [`Effect::Transfer`] from A to B riding the SAME metered turn, so the charge
/// commits atomically with the meter or not at all.
///
/// The `Effect::Transfer` the charge emits is EXACTLY what the app-framework
/// `Payable::pay` DSI desugars to (the one conserved per-asset Σδ=0 kernel
/// effect): the gateway is the metered front door to the same value medium the
/// `Payable` apps transact over, so a tool-call's payment is a balance the
/// provider's cell can spend onward.
///
/// ## Two enforcement surfaces (mirroring the rate budget)
///
/// 1. **In-band, before submission** — `spent + price <= budget`. Over-budget is
///    a [`GatewayRefusal::OverBudget`] returned as an `Err` (the anti-ghost
///    tooth: no turn, no spend, no charge).
/// 2. **In the executor** — the charge rides as an [`Effect::Transfer`]
///    (`LinearityClass::Conservative`): if the consumer cannot actually pay
///    (balance `< price`), the kernel's per-asset conservation check REJECTS the
///    metered turn, so a non-paying call cannot meter. Over-budget is the fast
///    in-band cap; insolvency is the conserved backstop under it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Charge {
    /// The per-call price the provider charges (moved consumer → provider).
    pub price: u64,
    /// The provider cell that receives each call's payment (agent B).
    pub provider: CellId,
    /// The consumer's total spend allowance under this mandate: cumulative
    /// `spent` may never exceed this (the VALUE budget, the money analogue of the
    /// grant's rate ceiling).
    pub budget: u64,
}

impl Charge {
    /// A charge of `price` per call, paid to `provider`, capped at `budget` total.
    pub fn new(price: u64, provider: CellId, budget: u64) -> Charge {
        Charge {
            price,
            provider,
            budget,
        }
    }
}

/// **The consumer's spend account, as a [`Payable`] cell.**
///
/// The gateway's worker cell IS the consumer's spend account: it holds the value
/// (`asset` = its `token_id`) the per-call charge moves out of. Implementing
/// [`Payable`] on this handle is what makes the gateway charge go through the REAL
/// `Payable::pay` desugar — [`Payable::pay_resolved`] routes `pay` through the
/// canonical [`dregg_payable::payable_descriptor`] (verified DFA → `Signature`
/// cap-gate → conserving [`Effect::Transfer`]), the SAME route the app
/// framework's `Payable::pay` uses. Not a parallel hand-rolled `Transfer`.
#[derive(Clone, Copy, Debug)]
struct ConsumerSpendAccount {
    /// The consumer's value cell (the gateway worker cell) — the `from` of the pay.
    cell: CellId,
    /// The asset the consumer denominates value in (its `token_id`).
    asset: AssetId,
}

impl Payable for ConsumerSpendAccount {
    fn payable_cell(&self) -> CellId {
        self.cell
    }
    fn payable_asset(&self) -> AssetId {
        self.asset
    }
}

/// **`deleg_admit`** — the folded delegated-policy predicate, the byte-faithful
/// Rust mirror of the Lean `delegAdmit g now tool old new`
/// (`Dregg2.Apps.ToolAccessDelegation.delegAdmit`).
///
/// Returns `true` IFF the delegated policy admits the invocation that advances
/// the rate counter `old → new`, presented at height `now` for tool `tool` under
/// grant `g`. Fail-closed on every conjunct, in the SAME order as the Lean:
///
/// 1. SCOPE — `tool == g.tool_id`;
/// 2. DEADLINE — `now <= g.deadline`;
/// 3. single-step increment — `new == old + 1`;
/// 4. sane prior count — `0 <= old`;
/// 5. RATE — `new <= g.rate_limit`.
pub fn deleg_admit(g: &ToolGrant, now: i64, tool: i64, old: i64, new: i64) -> bool {
    tool == g.tool_id && now <= g.deadline && new == old + 1 && 0 <= old && new <= g.rate_limit
}

/// The mandate cell program installed on the worker cell — the executor-side
/// half of the rate enforcement.
///
/// `FieldLte { calls_made <= rate_limit }` binds the RATE ceiling into the
/// committed transition (the executor rejects any write whose post-state counter
/// exceeds `rate_limit`), and `Monotonic { calls_made }` forbids rolling the
/// counter back to forge head-room. Together they are the executor's own
/// realization of the rate conjunct of [`deleg_admit`] — so even a caller that
/// bypassed the in-band check cannot drive the counter past the granted ceiling.
///
/// (SCOPE and DEADLINE are enforced in-band by [`deleg_admit`] and at the
/// executor by the worker's method-scoped biscuit credential / the runtime's
/// block height; the cell program carries the rate + no-rollback invariants that
/// are purely intrinsic to the counter slot.)
pub fn mandate_program(rate_limit: i64) -> CellProgram {
    let ceiling = if rate_limit < 0 { 0 } else { rate_limit as u64 };
    CellProgram::Predicate(vec![
        // RATE: the post-state counter never exceeds the granted ceiling.
        StateConstraint::FieldLte {
            index: CALLS_MADE_SLOT,
            value: field_from_u64(ceiling),
        },
        // NO ROLLBACK: the counter can never decrease (no forged head-room).
        StateConstraint::Monotonic {
            index: CALLS_MADE_SLOT,
        },
    ])
}

/// Why the gateway refused a tool call IN-BAND (returned as the `Err` of
/// [`ToolGateway::invoke`] — the anti-ghost tooth: a refusal is a value, never a
/// panic, and NO turn is submitted).
///
/// Each variant is the negation of one [`deleg_admit`] conjunct, named so the
/// caller (and an audit trail) can see exactly which leg of the mandate bit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GatewayRefusal {
    /// SCOPE: the presented tool id is not the granted one.
    OutOfScope {
        /// The tool id the call presented.
        presented: i64,
        /// The single tool id the grant allows.
        granted: i64,
    },
    /// DEADLINE: the call was presented after the granted expiry.
    PastDeadline {
        /// The height the call was presented at.
        now: i64,
        /// The granted expiry height.
        deadline: i64,
    },
    /// RATE: the rate budget is exhausted (the counter is already at the
    /// granted ceiling, so the next call would exceed it).
    OverRate {
        /// The counter value before this (refused) call.
        calls_made: i64,
        /// The granted ceiling `N`.
        rate_limit: i64,
    },
    /// VALUE BUDGET: paying for this call would push cumulative spend past the
    /// consumer's allowance (`spent + price > budget`). The market analogue of
    /// [`OverRate`](GatewayRefusal::OverRate): the consumer is out of money on
    /// this mandate before the call is even attempted.
    OverBudget {
        /// The value already spent under this mandate.
        spent: u64,
        /// The per-call price that would have been charged.
        price: u64,
        /// The consumer's total spend allowance.
        budget: u64,
    },
}

impl std::fmt::Display for GatewayRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GatewayRefusal::OutOfScope { presented, granted } => write!(
                f,
                "tool call out of scope: presented tool {presented}, mandate grants only {granted}"
            ),
            GatewayRefusal::PastDeadline { now, deadline } => write!(
                f,
                "tool call past deadline: presented at height {now}, mandate expired at {deadline}"
            ),
            GatewayRefusal::OverRate {
                calls_made,
                rate_limit,
            } => write!(
                f,
                "tool call over rate: {calls_made} calls already made, mandate grants {rate_limit}"
            ),
            GatewayRefusal::OverBudget {
                spent,
                price,
                budget,
            } => write!(
                f,
                "tool call over budget: {spent} already spent + {price} price exceeds the {budget} allowance"
            ),
        }
    }
}

impl std::error::Error for GatewayRefusal {}

/// The outcome of an admitted, committed tool invocation: the executor receipt
/// proving the metered turn committed, plus the new counter value.
#[derive(Clone, Debug)]
pub struct ToolReceipt {
    /// The executor receipt for the metered turn (proof the call committed).
    pub receipt: TurnReceipt,
    /// The rate counter AFTER this call (`calls_made` post-invocation).
    pub calls_made: i64,
    /// How many calls remain on the mandate (`rate_limit - calls_made`).
    pub remaining: i64,
    /// The value charged for THIS call (the per-call `price`; `0` for an
    /// unpriced mandate). The conserved `Effect::Transfer` for this amount rode
    /// the metered turn, so the receipt witnesses the payment as well as the
    /// authorization — the "charge recorded in the verdict".
    pub paid: u64,
}

/// A custody-receipt-shaped DELIVERY WITNESS: proof that a routed tool-call's
/// work was dequeued toward — and executed by — the execution environment.
///
/// This is the data-plane analogue of the captp `CustodyReceipt`: where that
/// receipt witnesses a relay accepting custody of a box into a recipient's queue
/// (the recipient's drain witnessing delivery), THIS receipt witnesses the
/// gateway's executor draining a routed tool-call out of the inbox and committing
/// it. The headline fact — "this specific routed call, by its `routed_hash`, was
/// delivered to the executor" — is a sticky, content-addressed witness, the same
/// shape custody accountability turns on.
///
/// Field-for-shape with the captp receipt's accountability binding:
/// * `routed_hash` — the content-address of the routed call (the turn hash of the
///   enqueued metered turn); binds the receipt to a SPECIFIC routed call.
/// * `executor_cell` — the execution environment the call was delivered TO (here
///   the worker's executor cell; the cross-federation case binds the inbox owner).
/// * `enqueued_at` / `delivered_at` — the height the call was enqueued and the
///   height the executor drained + committed it (the delivery transition).
///
/// The next slice replaces this in-crate witness with a real, Ed25519-signed
/// captp `CustodyReceipt` once the route crosses a relay / federation boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeliveryReceipt {
    /// The content-address of the routed call (the enqueued turn's hash).
    pub routed_hash: [u8; 32],
    /// The execution environment the call was delivered to (worker executor cell).
    pub executor_cell: CellId,
    /// The height the call was enqueued onto the inbox.
    pub enqueued_at: i64,
    /// The height the executor drained and committed the call.
    pub delivered_at: i64,
}

/// The terminal result of a ROUTED tool-call once the executor has drained the
/// queue and run the work: the [`ToolReceipt`] (proof + conserved spend + meter),
/// plus the [`DeliveryReceipt`] (proof the work was routed to and executed by the
/// execution environment). This is what [`ToolGateway::resolve`] hands back when a
/// [`RoutedHandle`] completes.
#[derive(Clone, Debug)]
pub struct RoutedResult {
    /// The executor receipt + meter for the metered turn (same as the inline path).
    pub tool_receipt: ToolReceipt,
    /// The custody-receipt-shaped delivery witness.
    pub delivery: DeliveryReceipt,
}

/// The status of a routed tool-call's promise (mirrors `dregg_turn::PendingStatus`,
/// kept local so the gateway's data-plane surface is self-contained).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RoutedStatus {
    /// Enqueued, awaiting the executor's drain.
    Pending,
    /// Drained + executed; the [`RoutedResult`] is available via
    /// [`ToolGateway::resolve`].
    Delivered,
    /// The route broke (the executor rejected the work, or it was dropped); the
    /// reason is available via [`ToolGateway::resolve`].
    Broken,
}

/// A non-blocking PROMISE for a routed tool-call: the on-ramp return of
/// [`ToolGateway::enqueue`]. `EventualRef`-shaped (it carries the source turn
/// hash that identifies the routed work in the pending registry), it is polled via
/// [`RoutedHandle::status`] and resolved via [`ToolGateway::resolve`] once the
/// executor has drained the queue.
#[derive(Clone, Debug)]
pub struct RoutedHandle {
    /// The hash identifying the routed call in the pending registry (the
    /// `EventualRef::source_turn` of the promise; the routed work's turn hash).
    pub routed_hash: [u8; 32],
    /// The tool id the routed call presented (for audit / correlation).
    pub tool: i64,
    /// The height the call was enqueued (its on-ramp clock).
    pub enqueued_at: i64,
}

impl RoutedHandle {
    /// The routed work's content-address (the `EventualRef`-shaped promise key).
    pub fn routed_hash(&self) -> [u8; 32] {
        self.routed_hash
    }
}

/// The error surface of [`ToolGateway::invoke`]: either an in-band mandate
/// refusal, or an underlying SDK/executor error (spawn / submission failure).
#[derive(Debug)]
pub enum ToolCallError {
    /// The delegated policy refused the call IN-BAND (the anti-ghost tooth).
    Refused(GatewayRefusal),
    /// An underlying SDK/executor error (e.g. the executor rejected the metered
    /// write — the cell-program rate/monotonic backstop, or a credential failure).
    Sdk(SdkError),
}

impl std::fmt::Display for ToolCallError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ToolCallError::Refused(r) => write!(f, "mandate refused tool call: {r}"),
            ToolCallError::Sdk(e) => write!(f, "tool call execution error: {e}"),
        }
    }
}

impl std::error::Error for ToolCallError {}

impl From<SdkError> for ToolCallError {
    fn from(e: SdkError) -> Self {
        ToolCallError::Sdk(e)
    }
}

/// THE GATEWAY — a mandated inhabitant wrapping a cap-gated worker.
///
/// Construct one with [`ToolGateway::admit`] (the grantor delegates a
/// [`ToolGrant`] to a freshly spawned worker). Then any external loop drives
/// inbound tool-calls through [`ToolGateway::invoke`]: a granted call commits
/// with a [`ToolReceipt`]; an out-of-mandate call is refused in-band as a
/// [`GatewayRefusal`].
///
/// The gateway owns the worker [`SubAgent`] (its biscuit credential is scoped to
/// `grant.tool_method`) and tracks the rate counter; the worker cell carries the
/// [`mandate_program`] backstop.
pub struct ToolGateway {
    /// The grantor's pinned mandate.
    grant: ToolGrant,
    /// The provider's per-call PRICE + the consumer's spend budget, if this is a
    /// PAID (metered-market) mandate. `None` = a free mandate (rate-only, the
    /// original gateway shape). When `Some`, every admitted call charges
    /// `charge.price` consumer → `charge.provider` on the metered turn.
    charge: Option<Charge>,
    /// Cumulative value spent under this mandate (advances by `charge.price` on
    /// each committed/reserved paid call). Capped at `charge.budget` in-band.
    spent: u64,
    /// The asset (the worker cell's `token_id`) the consumer denominates value in
    /// — bound into the `Payable` charge route as the payment's asset tag so the
    /// charge desugars to a Transfer in the consumer's own asset.
    consumer_asset: AssetId,
    /// The cap-gated worker the gateway drives.
    worker: SubAgent,
    /// The worker cell id (the mandate cell carrying `calls_made`).
    worker_cell: CellId,
    /// The rate counter, kept in lock-step with the worker cell's
    /// `calls_made` slot (advanced only on a committed invocation).
    ///
    /// ROUTED-PATH NOTE: admission for a routed call reserves a counter slot at
    /// ENQUEUE time (so two concurrently-enqueued calls cannot both pass the rate
    /// gate against the same `old`), and the executor's metered turn at DRAIN time
    /// advances the on-ledger slot to match. `calls_made` therefore tracks the
    /// reserved (admitted-and-routed) count, the cell's slot the committed count;
    /// a broken route releases the reservation.
    calls_made: i64,
    /// THE DATA-PLANE INBOX — the queue of admitted routed tool-calls awaiting the
    /// execution environment's drain. Modelled here as an in-crate `VecDeque`
    /// toward the worker's executor cell; the next slice routes this through the
    /// captp `MerkleQueue` so the route can cross a relay / federation.
    inbox: VecDeque<RoutedWork>,
    /// THE RESULT CHANNEL — the verified `dregg_turn` promise registry. Each
    /// routed call registers a pending entry keyed by its routed hash; the
    /// executor's drain resolves it (Resolved → delivery, Broken → broken route),
    /// reusing the cascading resolve/broken-propagation machinery rather than
    /// reinventing it.
    pending: PendingTurnRegistry,
    /// The terminal results of drained routed calls, keyed by routed hash, awaiting
    /// the caller's [`ToolGateway::resolve`]. A delivered route lands an
    /// `Ok(RoutedResult)`; a broken route lands an `Err(reason)`.
    results: std::collections::HashMap<[u8; 32], Result<RoutedResult, String>>,
}

/// One admitted routed tool-call sitting on the gateway's inbox, awaiting the
/// execution environment's drain. Carries everything the executor needs to run the
/// metered turn and emit the delivery witness.
#[derive(Clone, Debug)]
struct RoutedWork {
    /// The routed call's content-address (the EventualRef-shaped promise key).
    routed_hash: [u8; 32],
    /// The new counter value this call commits (`old + 1`), reserved at enqueue.
    new_count: i64,
    /// The tool's actual effects (beyond the metered counter advance + charge).
    work: Vec<Effect>,
    /// The value reserved for this routed call's charge at enqueue (`0` for a
    /// free mandate); released back to the budget if the route breaks.
    charged: u64,
    /// The height the call was enqueued (for the delivery receipt).
    enqueued_at: i64,
}

impl ToolGateway {
    /// Admit a worker into the world under a delegated tool mandate.
    ///
    /// The grantor (`runtime`, holding `parent_token`) delegates `grant` to a
    /// freshly spawned [`SubAgent`] scoped to `grant.tool_method`, installs the
    /// [`mandate_program`] (rate ceiling + monotonic counter) on the worker
    /// cell, and returns a gateway ready to admit inbound tool-calls.
    ///
    /// The worker's biscuit credential is the executor-enforced SCOPE: a turn
    /// under any verb other than `grant.tool_method` is rejected by the executor
    /// itself. The cell program is the executor-enforced RATE backstop.
    pub fn admit(
        runtime: &AgentRuntime,
        parent_token: &HeldToken,
        grant: ToolGrant,
    ) -> Result<Self, SdkError> {
        Self::admit_priced(runtime, parent_token, grant, None)
    }

    /// Admit a worker under a delegated tool mandate WITH a per-call PRICE — the
    /// metered, PAID market gateway.
    ///
    /// Identical to [`ToolGateway::admit`] (same cap-gated worker, same
    /// rate/scope/deadline mandate, same executor-side backstop), but every
    /// admitted call additionally CHARGES `charge.price` from the consumer (the
    /// worker cell) to `charge.provider` via a conserving [`Effect::Transfer`]
    /// riding the metered turn, with cumulative spend capped at `charge.budget`.
    ///
    /// Pass `None` for `charge` to admit a free (rate-only) mandate — exactly
    /// what [`ToolGateway::admit`] does. This is the "pay to access agent B's
    /// tools" gateway: B is `charge.provider`, the price is per-call, the
    /// consumer (the worker A drives) pays out of its own balance, conserved.
    pub fn admit_priced(
        runtime: &AgentRuntime,
        parent_token: &HeldToken,
        grant: ToolGrant,
        charge: Option<Charge>,
    ) -> Result<Self, SdkError> {
        // Spawn a worker scoped to EXACTLY the granted tool method. Its biscuit
        // credential covers only `grant.tool_method`, so the executor rejects a
        // call under any other verb with `TokenInsufficientCapability`.
        let worker = runtime.spawn_sub_agent_scoped(
            &Attenuation::default(),
            parent_token,
            &[grant.tool_method.as_str()],
        )?;
        let worker_cell = worker.cell_id();

        // Install the mandate program (rate ceiling + monotonic counter) on the
        // worker cell — the executor's own realization of the rate conjunct, the
        // backstop under the in-band `deleg_admit`. The worker cell lives in the
        // runtime's shared ledger, so we reach it via the runtime handle. We also
        // read the worker cell's `token_id` here — the asset the consumer spends
        // in, bound into the `Payable` charge route.
        let consumer_asset = {
            let mut ledger = runtime.ledger().lock().unwrap();
            ledger
                .update_with(&worker_cell, |cell| {
                    cell.program = mandate_program(grant.rate_limit);
                })
                .map_err(|e| SdkError::Rejected(format!("install mandate program: {e}")))?;
            ledger
                .get(&worker_cell)
                .map(|c| *c.token_id())
                .unwrap_or([0u8; 32])
        };

        Ok(ToolGateway {
            grant,
            charge,
            spent: 0,
            consumer_asset,
            worker,
            worker_cell,
            calls_made: 0,
            inbox: VecDeque::new(),
            pending: PendingTurnRegistry::new(),
            results: std::collections::HashMap::new(),
        })
    }

    /// Admit a worker AND stamp the OWNER-SIGNED ENVELOPE (upgrade-safety keystone, made
    /// live at spawn). The worker's authority-widening slots — `set_permissions`,
    /// `delegate`, `set_verification_key` — are gated to `owner_vk_hash`
    /// (= `dregg_turn::executor::owner_envelope::owner_envelope_vk(&owner_pubkey)`, pinned to
    /// `RenterAnchor.pubkey`). The worker is host-keyed (fresh cipherclerk), so
    /// `AuthRequired::Signature` slots (e.g. `set_state`, advancing `calls_made`) stay
    /// host-satisfiable — but a provider running standard node software CANNOT craft a
    /// `Delegate`/`SetPermissions` turn that WIDENS its own authority over the worker through
    /// the executor, because it lacks the owner key (fail-closed even with no verifier
    /// registered). The direct-Ledger-mutation adversary is caught separately by the owner's
    /// checkpoint countersignature (R1) at passive verify.
    pub fn admit_enveloped(
        runtime: &AgentRuntime,
        parent_token: &HeldToken,
        grant: ToolGrant,
        owner_vk_hash: [u8; 32],
    ) -> Result<Self, SdkError> {
        let worker = runtime.spawn_sub_agent_scoped(
            &Attenuation::default(),
            parent_token,
            &[grant.tool_method.as_str()],
        )?;
        let worker_cell = worker.cell_id();

        let consumer_asset = {
            let mut ledger = runtime.ledger().lock().unwrap();
            ledger
                .update_with(&worker_cell, |cell| {
                    cell.program = mandate_program(grant.rate_limit);
                    cell.permissions = dregg_cell::Permissions::enveloped_worker(owner_vk_hash);
                })
                .map_err(|e| SdkError::Rejected(format!("install enveloped mandate: {e}")))?;
            ledger
                .get(&worker_cell)
                .map(|c| *c.token_id())
                .unwrap_or([0u8; 32])
        };

        Ok(ToolGateway {
            grant,
            charge: None,
            spent: 0,
            consumer_asset,
            worker,
            worker_cell,
            calls_made: 0,
            inbox: VecDeque::new(),
            pending: PendingTurnRegistry::new(),
            results: std::collections::HashMap::new(),
        })
    }

    /// **Fund the consumer's spend account from a REAL funded source.**
    ///
    /// The gateway's worker cell IS the consumer's spend account — the cell the
    /// per-call charge debits. By default a worker is born with a fixed balance;
    /// this is the path that funds it for real: it moves `amount` from `funder`'s
    /// cell INTO the spend account via a conserving [`Effect::Transfer`],
    /// authorized by the funder's OWN capability credential (the funder signs the
    /// funding turn — the value genuinely leaves the consumer's account). The
    /// charges this gateway then settles debit value the consumer ACTUALLY
    /// transferred in, not a magic birth-balance.
    ///
    /// The funder must hold value in the same asset as the worker cell (same
    /// `token_id` / domain — e.g. another worker the same runtime spawned) for the
    /// transfer to conserve. Returns the funding turn's receipt.
    #[must_use = "dropping the TurnReceipt silently discards proof the funding committed"]
    pub fn fund(&self, funder: &SubAgent, amount: u64) -> Result<TurnReceipt, SdkError> {
        funder.execute(vec![Effect::Transfer {
            from: funder.cell_id(),
            to: self.worker_cell,
            amount,
        }])
    }

    /// The grantor's pinned mandate.
    pub fn grant(&self) -> &ToolGrant {
        &self.grant
    }

    /// The worker cell id (the mandate cell).
    pub fn worker_cell(&self) -> CellId {
        self.worker_cell
    }

    /// The calls made so far under this mandate.
    pub fn calls_made(&self) -> i64 {
        self.calls_made
    }

    /// Test-only direct access to the cap-gated worker, used to exercise the
    /// EXECUTOR-side cell-program backstop independently of the in-band
    /// [`deleg_admit`] check (a bypass an in-band-skipping caller would attempt).
    #[doc(hidden)]
    pub fn worker_for_test(&self) -> &SubAgent {
        &self.worker
    }

    /// The calls remaining on the mandate (`rate_limit - calls_made`).
    pub fn remaining(&self) -> i64 {
        self.grant.rate_limit - self.calls_made
    }

    /// The provider's price + consumer budget for a PAID mandate (`None` for a
    /// free, rate-only mandate).
    pub fn charge(&self) -> Option<&Charge> {
        self.charge.as_ref()
    }

    /// The cumulative value spent under this mandate so far (`0` for an unpriced
    /// mandate, or before any paid call commits/reserves).
    pub fn spent(&self) -> u64 {
        self.spent
    }

    /// The value budget remaining on the mandate (`budget - spent`); `None` for
    /// an unpriced mandate.
    pub fn budget_remaining(&self) -> Option<u64> {
        self.charge
            .as_ref()
            .map(|c| c.budget.saturating_sub(self.spent))
    }

    /// The per-call price of a paid mandate (`0` for a free mandate).
    fn price(&self) -> u64 {
        self.charge.as_ref().map_or(0, |c| c.price)
    }

    /// IN-BAND value-budget check — the market analogue of the rate conjunct.
    /// Returns the [`GatewayRefusal::OverBudget`] leg iff paying for one more
    /// call would push cumulative spend past the consumer's allowance. `None`
    /// (admit) for a free mandate or one with budget head-room.
    fn budget_refusal(&self) -> Option<GatewayRefusal> {
        let charge = self.charge.as_ref()?;
        if self.spent + charge.price > charge.budget {
            Some(GatewayRefusal::OverBudget {
                spent: self.spent,
                price: charge.price,
                budget: charge.budget,
            })
        } else {
            None
        }
    }

    /// The consumer's spend account as a [`Payable`] cell — the worker cell + its
    /// asset. `None` for a free mandate.
    fn consumer_account(&self) -> Option<ConsumerSpendAccount> {
        self.charge.as_ref().map(|_| ConsumerSpendAccount {
            cell: self.worker_cell,
            asset: self.consumer_asset,
        })
    }

    /// **Resolve THIS mandate's per-call charge through the REAL `Payable::pay`
    /// path.** Routes a `pay` of `charge.price` from the consumer's spend account
    /// (the worker cell) to `charge.provider` through the canonical
    /// [`dregg_payable::payable_descriptor`] — verified DFA route → `Signature`
    /// cap-gate → desugar to the ONE conserving [`Effect::Transfer`]. Returns the
    /// resolved `(Action, MethodSig)` so a caller can confirm the charge IS a
    /// `Payable` pay (`action.method == pay`, the `MethodSig` from the canonical
    /// descriptor), not a hand-rolled Transfer. `None` for a free mandate.
    ///
    /// This is the one source of truth the app framework's `Payable::pay` also
    /// uses; the gateway and the apps transact over the same value medium.
    pub fn charge_invocation(&self) -> Option<Result<(Action, MethodSig), InvokeRefused>> {
        let (account, charge) = (self.consumer_account()?, self.charge.as_ref()?);
        Some(account.pay_resolved(charge.price, charge.provider, InvokeAuthority::Signature))
    }

    /// Prepend the per-call charge's conserving [`Effect::Transfer`] (consumer →
    /// provider) to the tool's work, if this is a paid mandate. The transfer is
    /// the desugar of a REAL `Payable::pay` ([`Self::charge_invocation`]) — the
    /// SAME verified, route-table-dispatched effect the apps transact over, not a
    /// parallel hand-rolled one. It rides the SAME metered turn the counter
    /// advance does, so the charge commits atomically with the meter (or the whole
    /// turn is rejected — e.g. the consumer cannot pay, the conserved backstop
    /// under the in-band budget cap).
    fn charged_effects(&self, work: Vec<Effect>) -> Result<Vec<Effect>, ToolCallError> {
        match self.charge_invocation() {
            Some(Ok((action, _sig))) => {
                // `action.effects` is exactly the conserving Transfer the canonical
                // `Payable::pay` desugars to — one source of truth.
                let mut v = action.effects;
                v.extend(work);
                Ok(v)
            }
            Some(Err(e)) => Err(ToolCallError::Sdk(SdkError::Rejected(format!(
                "payable charge route refused: {e}"
            )))),
            None => Ok(work),
        }
    }

    /// THE SEAM — admit an inbound tool-call.
    ///
    /// `tool` is the tool/MCP id the call presents; `now` is the presentation
    /// height/clock; `work` is the effects the call performs on the worker cell
    /// (the tool's actual work, beyond the metered counter advance — pass an
    /// empty `Vec` for a pure metered invocation).
    ///
    /// Admission folds the WHOLE delegated policy via [`deleg_admit`] (SCOPE ∧
    /// DEADLINE ∧ RATE):
    ///
    /// * **granted** (`deleg_admit == true`) — the metered `calls_made : c → c+1`
    ///   write (plus `work`) is submitted through the cap-gated worker; on commit
    ///   it returns a [`ToolReceipt`] (proof + conserved spend). The cell-program
    ///   rate/monotonic backstop and the worker's method-scoped credential are
    ///   the executor's independent enforcement of the same policy.
    /// * **refused** (`deleg_admit == false`) — NO turn is submitted; the call
    ///   returns `Err(ToolCallError::Refused(..))` naming the leg that bit (the
    ///   anti-ghost tooth: a `Result` error, never a panic, no spend, no counter
    ///   advance).
    pub fn invoke(
        &mut self,
        tool: i64,
        now: i64,
        work: Vec<Effect>,
    ) -> Result<ToolReceipt, ToolCallError> {
        let old = self.calls_made;
        let new = old + 1;

        // §1 — IN-BAND admission (the byte-faithful Lean `delegAdmit` mirror).
        // Fail-closed, naming the leg that bit. NO turn is submitted on refusal.
        if !deleg_admit(&self.grant, now, tool, old, new) {
            return Err(ToolCallError::Refused(
                self.diagnose_refusal(tool, now, old),
            ));
        }
        // §1b — IN-BAND value-budget admission (the market conjunct). A paid call
        // whose price would exceed the consumer's allowance is refused in-band as
        // `OverBudget` — no turn, no spend, no charge.
        if let Some(refusal) = self.budget_refusal() {
            return Err(ToolCallError::Refused(refusal));
        }

        // §2 — the metered write: advance the rate counter `c → c+1`, with the
        // per-call CHARGE (a conserving consumer → provider `Effect::Transfer`)
        // and the tool's `work` riding the SAME turn. The worker presents its
        // method-scoped biscuit credential; the executor admits it, the
        // cell-program rate/monotonic backstop re-checks the counter, AND the
        // kernel's per-asset conservation check enforces the charge (an
        // insolvent consumer's turn is rejected — the conserved backstop under
        // the in-band budget cap).
        let charged = self.charged_effects(work)?;
        let mut effects = Vec::with_capacity(charged.len() + 1);
        effects.push(Effect::SetField {
            cell: self.worker_cell,
            index: CALLS_MADE_SLOT as usize,
            value: field_from_u64(new as u64),
        });
        effects.extend(charged);

        let receipt = self
            .worker
            .execute_method(&self.grant.tool_method, effects)?;

        // The call committed: advance the tracked counter AND the spend in
        // lock-step (the on-ledger Transfer already moved the value; `spent`
        // tracks it for the in-band budget cap).
        self.calls_made = new;
        let paid = self.price();
        self.spent += paid;
        Ok(ToolReceipt {
            receipt,
            calls_made: new,
            remaining: self.remaining(),
            paid,
        })
    }

    // ── THE DATA PLANE — admit → enqueue → (execute elsewhere) → results-back ──

    /// THE ROUTED ON-RAMP — admit a tool-call and ENQUEUE it (non-blocking).
    ///
    /// Runs the SAME admission gate as [`invoke`](Self::invoke) ([`deleg_admit`]:
    /// SCOPE ∧ DEADLINE ∧ RATE), then — instead of executing inline — ENQUEUES the
    /// admitted call onto the gateway's inbox toward the execution environment and
    /// returns a non-blocking [`RoutedHandle`] (an `EventualRef`-shaped promise).
    /// The metered counter slot is RESERVED here (so a second concurrent enqueue
    /// gates against the reserved `old + 1`, not a stale count); the executor's
    /// metered turn advances the on-ledger slot when it drains the call.
    ///
    /// * **granted** — the call is enqueued; a [`RoutedHandle`] is returned. The
    ///   work has NOT run yet; drive it with [`drive_executor`](Self::drive_executor),
    ///   then collect the [`RoutedResult`] with [`resolve`](Self::resolve).
    /// * **refused** — NO enqueue, no reservation; returns
    ///   `Err(ToolCallError::Refused(..))` naming the leg that bit (the on-ramp
    ///   short-circuits exactly as the inline gate does).
    pub fn enqueue(
        &mut self,
        tool: i64,
        now: i64,
        work: Vec<Effect>,
    ) -> Result<RoutedHandle, ToolCallError> {
        let old = self.calls_made;
        let new = old + 1;

        // §1 — IN-BAND admission, the SAME gate as the inline path. NO enqueue,
        // no reservation on refusal (the anti-ghost tooth at the on-ramp).
        if !deleg_admit(&self.grant, now, tool, old, new) {
            return Err(ToolCallError::Refused(
                self.diagnose_refusal(tool, now, old),
            ));
        }
        // §1b — IN-BAND value-budget admission (the market conjunct), the SAME
        // gate the inline path runs. Over-budget short-circuits at the on-ramp:
        // no enqueue, no reservation.
        if let Some(refusal) = self.budget_refusal() {
            return Err(ToolCallError::Refused(refusal));
        }

        // Build the charge desugar FIRST (through the real `Payable::pay` route)
        // so a (theoretical) route refusal short-circuits BEFORE any reservation —
        // no leaked rate/value budget on an un-enqueued call.
        let charged_work = self.charged_effects(work.clone())?;

        // RESERVE the counter slot AND the spend: the admitted call now owns
        // `old → new` of the rate budget and `price` of the value budget, so a
        // second enqueue this turn gates against both reservations (no
        // double-spend of either between enqueue and drain). A broken drain
        // releases both reservations.
        self.calls_made = new;
        let charged = self.price();
        self.spent += charged;

        // Build the metered turn NOW (at enqueue) so the routed call's
        // content-address IS the turn hash — the same identity the executor will
        // commit, and the EventualRef::source_turn / pending-registry key for the
        // result channel. The charge + work ride this turn; the executor reruns
        // the same shape at drain time through the cap-gated worker.
        let mut effects = Vec::with_capacity(charged_work.len() + 1);
        effects.push(Effect::SetField {
            cell: self.worker_cell,
            index: CALLS_MADE_SLOT as usize,
            value: field_from_u64(new as u64),
        });
        effects.extend(charged_work);
        let routed_turn = self.build_routed_turn(new, effects);
        let routed_hash = routed_turn.hash();

        // §2 — register the promise in the verified pending registry (the result
        // channel), keyed by the routed turn hash, then ENQUEUE onto the data-plane
        // inbox toward the executor. The condition is AwaitHeight(now): the executor's
        // drive_executor pass resolves it (mirroring how a node drives a registry
        // entry to a real receipt), and await_routed dependents cascade off it.
        self.pending.submit_pending_at(
            routed_turn,
            ResolutionCondition::AwaitHeight(now.max(0) as u64),
            u64::MAX,
            now.max(0) as u64,
        );
        self.inbox.push_back(RoutedWork {
            routed_hash,
            new_count: new,
            work,
            charged,
            enqueued_at: now,
        });

        Ok(RoutedHandle {
            routed_hash,
            tool,
            enqueued_at: now,
        })
    }

    /// THE EXECUTION ENVIRONMENT'S DRAIN — run every enqueued routed call.
    ///
    /// This is the "execute elsewhere" half of the data plane: the executor drains
    /// the inbox, runs each admitted call's metered turn through the cap-gated
    /// worker (the SAME executor path the inline [`invoke`](Self::invoke) uses), and
    /// resolves the call's promise in the result channel — `Resolved` with a
    /// [`RoutedResult`] (tool receipt + delivery witness) on commit, `Broken` if
    /// the executor rejects the metered write (which also RELEASES the reserved
    /// counter slot, so the rate budget is not leaked by a failed route).
    ///
    /// `now` is the drain height (stamped into the [`DeliveryReceipt`] as
    /// `delivered_at`). Returns the routed hashes drained this pass. Idempotent on
    /// an empty inbox (returns an empty vec).
    pub fn drive_executor(&mut self, now: i64) -> Vec<[u8; 32]> {
        let mut drained = Vec::new();
        while let Some(item) = self.inbox.pop_front() {
            drained.push(item.routed_hash);

            // The metered write + the charge + the tool's payload ride one turn —
            // identical to the inline path, but executed at DRAIN time, not
            // enqueue time. A route refusal (theoretical) breaks the route and
            // releases the reservation, same as an executor rejection.
            let charged_work = match self.charged_effects(item.work.clone()) {
                Ok(c) => c,
                Err(e) => {
                    if self.calls_made == item.new_count {
                        self.calls_made = item.new_count - 1;
                    }
                    self.spent = self.spent.saturating_sub(item.charged);
                    let reason = format!("routed charge route refused: {e}");
                    let _events = self.pending.resolve(
                        item.routed_hash,
                        ResolutionOutcome::Broken(dregg_turn::BrokenReason::TurnRejected(
                            dregg_turn::TurnError::PreconditionFailed {
                                description: reason.clone(),
                            },
                        )),
                    );
                    self.results.insert(item.routed_hash, Err(reason));
                    continue;
                }
            };
            let mut effects = Vec::with_capacity(charged_work.len() + 1);
            effects.push(Effect::SetField {
                cell: self.worker_cell,
                index: CALLS_MADE_SLOT as usize,
                value: field_from_u64(item.new_count as u64),
            });
            effects.extend(charged_work);

            match self.worker.execute_method(&self.grant.tool_method, effects) {
                Ok(receipt) => {
                    let tool_receipt = ToolReceipt {
                        receipt,
                        calls_made: item.new_count,
                        remaining: self.grant.rate_limit - item.new_count,
                        paid: item.charged,
                    };
                    let delivery = DeliveryReceipt {
                        routed_hash: item.routed_hash,
                        executor_cell: self.worker_cell,
                        enqueued_at: item.enqueued_at,
                        delivered_at: now,
                    };
                    // Resolve the promise in the verified registry (cascades to any
                    // dependents), then stash the terminal result for the caller's
                    // resolve(). The registry entry is the EventualRef-shaped
                    // promise; the stashed RoutedResult is its resolved value.
                    let _events = self.pending.resolve(
                        item.routed_hash,
                        ResolutionOutcome::Resolved(tool_receipt.receipt.clone()),
                    );
                    self.results.insert(
                        item.routed_hash,
                        Ok(RoutedResult {
                            tool_receipt,
                            delivery,
                        }),
                    );
                }
                Err(e) => {
                    // BROKEN ROUTE: release the reserved counter slot AND the
                    // reserved spend (the executor did NOT commit, so neither the
                    // rate budget nor the value budget must be consumed), then
                    // mark the promise broken.
                    if self.calls_made == item.new_count {
                        self.calls_made = item.new_count - 1;
                    }
                    self.spent = self.spent.saturating_sub(item.charged);
                    let reason = format!("routed execution rejected: {e}");
                    let _events = self.pending.resolve(
                        item.routed_hash,
                        ResolutionOutcome::Broken(dregg_turn::BrokenReason::TurnRejected(
                            dregg_turn::TurnError::PreconditionFailed {
                                description: reason.clone(),
                            },
                        )),
                    );
                    self.results.insert(item.routed_hash, Err(reason));
                }
            }
        }
        drained
    }

    /// Poll a routed handle's status WITHOUT consuming the result.
    ///
    /// `Pending` while still on the inbox (the executor has not drained it),
    /// `Delivered` once [`drive_executor`](Self::drive_executor) committed it (the
    /// [`RoutedResult`] is ready for [`resolve`](Self::resolve)), `Broken` if the
    /// route broke.
    pub fn status(&self, handle: &RoutedHandle) -> RoutedStatus {
        match self.results.get(&handle.routed_hash) {
            Some(Ok(_)) => RoutedStatus::Delivered,
            Some(Err(_)) => RoutedStatus::Broken,
            None => RoutedStatus::Pending,
        }
    }

    /// AWAIT / RESOLVE a routed handle — collect the [`RoutedResult`] once the
    /// executor has delivered it (the "results-back" terminus of the data plane).
    ///
    /// Returns:
    /// * `Ok(RoutedResult)` — the route delivered: the [`ToolReceipt`] (proof +
    ///   conserved spend + advanced meter) and the [`DeliveryReceipt`] (custody
    ///   witness that the work was routed to and executed by the executor).
    /// * `Err(ToolCallError::Sdk(..))` — either the route broke (the executor
    ///   rejected the metered write), or the handle is still pending / unknown.
    ///
    /// Consumes the stashed result (a routed call resolves once), so a second
    /// `resolve` of the same handle reports it as no-longer-known.
    pub fn resolve(&mut self, handle: &RoutedHandle) -> Result<RoutedResult, ToolCallError> {
        match self.results.remove(&handle.routed_hash) {
            Some(Ok(result)) => Ok(result),
            Some(Err(reason)) => Err(ToolCallError::Sdk(SdkError::Rejected(reason))),
            None => Err(ToolCallError::Sdk(SdkError::Rejected(format!(
                "routed call {:02x}{:02x}.. not yet delivered (drive the executor first)",
                handle.routed_hash[0], handle.routed_hash[1]
            )))),
        }
    }

    /// The number of routed calls currently enqueued (awaiting the executor's
    /// drain) — the inbox depth.
    pub fn inbox_depth(&self) -> usize {
        self.inbox.len()
    }

    /// Build the metered turn for a routed call — its hash is the routed call's
    /// content-address (the `EventualRef`-shaped promise key in the result channel,
    /// and the identity the executor commits). The `reserved_count` makes each
    /// routed call's turn distinct (it rides as the worker cell's nonce), so two
    /// calls under one mandate get distinct promise keys.
    ///
    /// The turn carries the worker's method-scoped credential; the executor reruns
    /// this same shape at drain time via [`SubAgent::execute_method`].
    fn build_routed_turn(&self, reserved_count: i64, effects: Vec<Effect>) -> dregg_turn::Turn {
        use crate::raw::{
            Action, Authorization, CallForest, CommitmentMode, DelegationMode, symbol,
        };
        let action = Action {
            target: self.worker_cell,
            method: symbol(&self.grant.tool_method),
            args: Vec::new(),
            authorization: Authorization::Token {
                encoded: self.worker.cap_token().to_vec(),
                key_ref: dregg_turn::TokenKeyRef::BiscuitIssuer {
                    issuer_pubkey: [0u8; 32],
                },
                discharges: Vec::new(),
            },
            preconditions: Default::default(),
            effects,
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        };
        let mut forest = CallForest::new();
        forest.add_root(action);
        crate::raw::Turn {
            agent: self.worker_cell,
            nonce: reserved_count as u64,
            call_forest: forest,
            fee: 5_000,
            memo: None,
            valid_until: None,
            depends_on: Vec::new(),
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            previous_receipt_hash: None,
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        }
    }

    /// Register a routed call's promise in the result channel under an explicit
    /// resolution condition. The default [`enqueue`](Self::enqueue) registers an
    /// `AwaitHeight` placeholder resolved by the drain; this hook lets a caller
    /// declare a routed call DEPENDS on another routed call (promise pipelining:
    /// the dependent stays pending until its dependency's drain resolves), reusing
    /// the verified registry's cascading resolution.
    pub fn await_routed(&mut self, handle: &RoutedHandle, on: [u8; 32]) {
        self.pending.register_dependent(on, handle.routed_hash);
    }

    /// Decide which mandate leg refused a call (for the [`GatewayRefusal`]). Only
    /// reached when [`deleg_admit`] returned `false`; reports the conjuncts in
    /// the same precedence the predicate checks them (scope, then deadline, then
    /// rate), so the most fundamental violation is surfaced first.
    fn diagnose_refusal(&self, tool: i64, now: i64, old: i64) -> GatewayRefusal {
        if tool != self.grant.tool_id {
            GatewayRefusal::OutOfScope {
                presented: tool,
                granted: self.grant.tool_id,
            }
        } else if now > self.grant.deadline {
            GatewayRefusal::PastDeadline {
                now,
                deadline: self.grant.deadline,
            }
        } else {
            // The only remaining way `deleg_admit` is false (given new = old+1,
            // 0 <= old by construction) is `new > rate_limit` — the rate is
            // exhausted.
            GatewayRefusal::OverRate {
                calls_made: old,
                rate_limit: self.grant.rate_limit,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The demo grant from the Lean §8 witness: tool 77, rate 3, deadline 100.
    fn demo_grant() -> ToolGrant {
        ToolGrant {
            tool_id: 77,
            rate_limit: 3,
            deadline: 100,
            tool_method: "search".to_string(),
        }
    }

    #[test]
    fn tool_gateway_admit_mirrors_lean_delegadmit() {
        // BOTH-POLARITY at the predicate level: this is the EXACT decision vector
        // the Lean `#guard`s witness in `ToolAccessDelegation.lean §8`. A drift on
        // either side is a divergence between the Rust seam and the proven crown.
        let g = demo_grant();

        // The three legal advances (in-scope tool 77, in-time now 50, 1..3 <= 3):
        assert!(deleg_admit(&g, 50, 77, 0, 1), "invocation 1 admitted");
        assert!(deleg_admit(&g, 50, 77, 1, 2), "invocation 2 admitted");
        assert!(
            deleg_admit(&g, 50, 77, 2, 3),
            "invocation 3 admitted (the last)"
        );

        // The TEETH (each negated conjunct), matching the Lean `== false` guards:
        assert!(
            !deleg_admit(&g, 50, 77, 3, 4),
            "invocation 4 over-rate (4 > 3)"
        );
        assert!(!deleg_admit(&g, 50, 99, 0, 1), "out-of-scope tool 99");
        assert!(
            !deleg_admit(&g, 101, 77, 0, 1),
            "past-deadline now 101 > 100"
        );

        // Non-single-step and negative-old also fail closed (the increment +
        // sane-prior conjuncts):
        assert!(
            !deleg_admit(&g, 50, 77, 0, 2),
            "not a single-step increment"
        );
        assert!(!deleg_admit(&g, 50, 77, -1, 0), "negative prior count");
    }

    #[test]
    fn mandate_program_carries_rate_and_monotonic() {
        // The installed program is exactly the rate ceiling + monotonic counter
        // (the executor-side backstop) — non-vacuous: two real constraints on the
        // calls_made slot.
        match mandate_program(3) {
            CellProgram::Predicate(cs) => {
                assert_eq!(cs.len(), 2);
                assert!(matches!(
                    cs[0],
                    StateConstraint::FieldLte { index, .. } if index == CALLS_MADE_SLOT
                ));
                assert!(matches!(
                    cs[1],
                    StateConstraint::Monotonic { index } if index == CALLS_MADE_SLOT
                ));
            }
            other => panic!("expected a Predicate program, got {other:?}"),
        }
    }
}
