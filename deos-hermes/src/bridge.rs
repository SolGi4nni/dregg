//! THE BRIDGE — a Hermes ACP tool-call becomes a cap-gated, receipted dregg turn.
//!
//! [`HermesGateway`] is the deos-side seam. It owns the grantor handle (the
//! [`AgentRuntime`](dregg_sdk::AgentRuntime) + root [`HeldToken`](dregg_sdk::HeldToken))
//! and a [`GrantRegistry`] (deos's per-kind mandate). For each Hermes
//! [`ToolKind`], it lazily ADMITS a cap-gated worker under that kind's
//! [`ToolGrant`](dregg_sdk::ToolGrant) — a real `ToolGateway` over the verified
//! executor. Every inbound [`ToolCallRequest`] is then routed through
//! [`ToolGateway::invoke`](dregg_sdk::ToolGateway::invoke):
//!
//! * ADMITTED — the metered `calls_made : c → c+1` write COMMITS through the
//!   cap-gated worker on the verified executor, yielding a real [`ToolReceipt`]
//!   (the `turn_hash` is the receipt id). deos returns [`PermissionOutcome::Allow`]
//!   to Hermes over ACP, and the call proceeds.
//! * REFUSED — `delegAdmit` returned false (scope / deadline / rate). NO turn,
//!   NO spend. deos returns [`PermissionOutcome::Reject`] naming the leg that
//!   bit — the IN-BAND refusal Hermes sees.
//!
//! The enforcement is ENTIRELY the proven `ToolGateway`'s; this module only maps
//! the ACP tool-call onto the gate and the gate's verdict back onto ACP. No new
//! policy, no new crypto, no bypass.

use std::collections::HashMap;

use dregg_sdk::{
    AgentRuntime, CellId, Charge, GatewayRefusal, HeldToken, SubAgent, ToolCallError, ToolGateway,
    ToolGrant,
};
use dregg_turn::{Effect, TurnReceipt};

use crate::acp::{PermissionOutcome, ToolCallRequest, ToolKind};
use crate::grant_registry::{GrantRegistry, MandateKey};
use crate::tool_effects;

/// **deos's tool MARKET policy** — the PAID half of the mandate. When a
/// [`HermesGateway`] carries one, every confined tool-call is not only
/// cap-checked + rate-metered but CHARGED: a per-call price moves from the
/// consumer (the confined session's worker cell) to the `provider` cell, riding
/// the SAME metered turn (a conserving [`Effect::Transfer`], the same one
/// `Payable::pay` desugars to). This is the "pay to access deos's tools/models"
/// layer — the confined agent pays for the capabilities it exercises.
#[derive(Clone, Debug)]
pub struct ToolMarket {
    /// The provider cell paid for tool access (deos's tool/model provider cell —
    /// agent B receives each call's charge).
    pub provider: CellId,
    /// The default per-call price (used for a tool with no explicit override).
    pub default_price: u64,
    /// The spend budget per mandate (per [`MandateKey`] worker) — the value
    /// ceiling that, like the rate ceiling, refuses a call in-band once reached.
    pub budget: u64,
    /// The SESSION-WIDE spend ceiling, pooled across EVERY worker this session
    /// admits. Where [`ToolMarket::budget`] bounds spend per [`MandateKey`] worker,
    /// this bounds the consumer's TOTAL spend across all its tool-calls: once
    /// cumulative session spend (`HermesGateway::total_spent`) plus the next call's
    /// price would exceed it, the call is refused in-band even if the per-worker
    /// budget still has head-room. `None` = no session cap (per-worker only).
    pub session_budget: Option<u64>,
    /// Per-tool price overrides, keyed by exact Hermes tool name (a scarcer /
    /// dearer tool charges more than the default).
    pub price_overrides: HashMap<String, u64>,
}

impl ToolMarket {
    /// A flat market: every tool-call costs `default_price`, paid to `provider`,
    /// each mandate budgeted at `budget`. No session-wide cap (per-worker only) —
    /// add one with [`ToolMarket::with_session_budget`].
    pub fn flat(provider: CellId, default_price: u64, budget: u64) -> ToolMarket {
        ToolMarket {
            provider,
            default_price,
            budget,
            session_budget: None,
            price_overrides: HashMap::new(),
        }
    }

    /// Pin a per-tool price override (e.g. `delegate_task` costs more than a
    /// `web_search`).
    pub fn with_price(mut self, tool: &str, price: u64) -> ToolMarket {
        self.price_overrides.insert(tool.to_string(), price);
        self
    }

    /// Pin a SESSION-WIDE spend ceiling pooled across every worker this session
    /// admits — the consumer's TOTAL spend bound (see [`ToolMarket::session_budget`]).
    pub fn with_session_budget(mut self, session_budget: u64) -> ToolMarket {
        self.session_budget = Some(session_budget);
        self
    }

    /// The per-call price for a resolved [`MandateKey`]: the per-tool override if
    /// one is pinned, else the default.
    fn price_for_key(&self, key: &MandateKey) -> u64 {
        match key {
            MandateKey::Tool(name) => *self
                .price_overrides
                .get(name)
                .unwrap_or(&self.default_price),
            MandateKey::Kind(_) => self.default_price,
        }
    }
}

/// The deos-side bridge: one [`ToolGateway`] per [`MandateKey`] (a per-tool
/// grant where deos pinned one, else the per-kind floor), lazily admitted,
/// fronting every Hermes tool-call over ACP.
pub struct HermesGateway<'rt> {
    /// The grantor: the runtime that admits workers and runs their turns.
    runtime: &'rt AgentRuntime,
    /// The root token the grantor delegates each worker's mandate from.
    root_token: HeldToken,
    /// deos's per-tool / per-kind mandate over this Hermes session.
    registry: GrantRegistry,
    /// deos's tool MARKET policy, if this session is PAID. `None` = a free
    /// (rate-only) session — the original gateway shape. When `Some`, every
    /// admitted worker is a PAID worker ([`ToolGateway::admit_priced`]).
    market: Option<ToolMarket>,
    /// The cap-gated worker per [`MandateKey`], admitted on first use under that
    /// key's grant. (One `ToolGateway` = one delegated worker + one metered
    /// counter.) A per-tool grant is its OWN worker, independent of its kind.
    gateways: HashMap<MandateKey, ToolGateway>,
}

impl<'rt> HermesGateway<'rt> {
    /// Open a bridge for a Hermes session: deos (the grantor, holding
    /// `root_token` on `runtime`) confines the session under `registry`.
    pub fn new(
        runtime: &'rt AgentRuntime,
        root_token: HeldToken,
        registry: GrantRegistry,
    ) -> HermesGateway<'rt> {
        HermesGateway {
            runtime,
            root_token,
            registry,
            market: None,
            gateways: HashMap::new(),
        }
    }

    /// Open a PAID bridge: as [`HermesGateway::new`], but every confined
    /// tool-call is also CHARGED under `market` — a per-call price moves from the
    /// confined session's worker cell to the market's provider cell on the
    /// metered turn (the "pay to access deos's tools/models" seam). Over-budget /
    /// insolvent calls are refused in-band exactly as over-rate calls are.
    pub fn new_paid(
        runtime: &'rt AgentRuntime,
        root_token: HeldToken,
        registry: GrantRegistry,
        market: ToolMarket,
    ) -> HermesGateway<'rt> {
        HermesGateway {
            runtime,
            root_token,
            registry,
            market: Some(market),
            gateways: HashMap::new(),
        }
    }

    /// The market policy this session charges under (`None` for a free session).
    pub fn market(&self) -> Option<&ToolMarket> {
        self.market.as_ref()
    }

    /// The [`Charge`] for a resolved [`MandateKey`] under the session market
    /// (`None` for a free session): the key's per-call price, paid to the
    /// market provider, budgeted at the market budget.
    fn charge_for_key(&self, key: &MandateKey) -> Option<Charge> {
        self.market
            .as_ref()
            .map(|m| Charge::new(m.price_for_key(key), m.provider, m.budget))
    }

    /// **The SESSION-WIDE budget check** (GAP 2) — pool spend across EVERY worker.
    ///
    /// Returns `Some(reason)` iff this session carries a [`ToolMarket::session_budget`]
    /// and paying for one more call routed to `key` would push the consumer's TOTAL
    /// spend across ALL its workers ([`HermesGateway::total_spent`]) past that
    /// ceiling. This bites even when the per-worker [`ToolMarket::budget`] still has
    /// head-room — a consumer's whole-session spend is bounded, not just per-worker.
    /// `None` (admit) for a free session, a session with no cap, or one with
    /// session head-room.
    fn session_budget_refusal(&self, key: &MandateKey) -> Option<String> {
        let market = self.market.as_ref()?;
        let session_cap = market.session_budget?;
        let price = market.price_for_key(key);
        let session_spent = self.total_spent();
        if session_spent + price > session_cap {
            Some(format!(
                "session budget exhausted: {session_spent} spent across the session + {price} \
                 price exceeds the {session_cap} session allowance"
            ))
        } else {
            None
        }
    }

    /// The grant deos pinned for a kind (for inspection / a session dock).
    pub fn grant_for(&self, kind: ToolKind) -> &ToolGrant {
        self.registry.grant_for(kind)
    }

    /// The registry deos confined this session under (for the mandate inspector).
    pub fn registry(&self) -> &GrantRegistry {
        &self.registry
    }

    /// Lazily admit (or fetch) the cap-gated worker for a [`MandateKey`]. The
    /// worker's biscuit credential is scoped to EXACTLY the key's `tool_method`,
    /// and its cell carries the `mandate_program` rate/monotonic backstop — both
    /// installed by the proven [`ToolGateway::admit`].
    fn gateway_for(&mut self, key: &MandateKey) -> Result<&mut ToolGateway, ToolCallError> {
        if !self.gateways.contains_key(key) {
            let grant = self.registry.grant_for_key(key).clone();
            // PAID session → admit a charging worker; free session → admit a
            // rate-only worker (the original shape). The charge rides every
            // metered turn this worker commits.
            let charge = self.charge_for_key(key);
            let gw = ToolGateway::admit_priced(self.runtime, &self.root_token, grant, charge)
                .map_err(ToolCallError::Sdk)?;
            self.gateways.insert(key.clone(), gw);
        }
        Ok(self
            .gateways
            .get_mut(key)
            .expect("just inserted the gateway for this key"))
    }

    /// The confinement WORKER CELL a call's mandate routes to (admitting the
    /// worker if it is not yet standing). Lets a caller that supplies its own
    /// `work` witness (e.g. `run_js`, whose evaluated script is not the wire
    /// payload) build an [`Effect::EmitEvent`] bound to the EXACT cell the
    /// metered turn will commit on — the same cell [`Self::admit_with_work`]
    /// derives internally for the auto-witness path.
    pub fn worker_cell_for(&mut self, call: &ToolCallRequest) -> Result<CellId, ToolCallError> {
        let key = self.registry.key_for_tool(&call.name);
        Ok(self.gateway_for(&key)?.worker_cell())
    }

    /// THE SEAM — admit a Hermes ACP tool-call as a cap-gated, metered,
    /// receipted dregg turn (or refuse it in-band), with the tool's SIDE-EFFECT
    /// riding the SAME metered turn.
    ///
    /// `now` is the presentation clock/height (the ACP request arrival time).
    /// The call's payload is translated by [`tool_effects::effects_for_call`]
    /// into a witness `Vec<Effect>` that rides the metered turn, so the
    /// committed receipt witnesses WHAT the call did (the path written, the URL
    /// fetched), not just that it was authorized.
    ///
    /// The call's name resolves a [`MandateKey`] (a tight per-tool grant if deos
    /// pinned one, else the per-kind floor); the gate's `delegAdmit` then folds
    /// SCOPE ∧ DEADLINE ∧ RATE. The returned [`PermissionOutcome`] is exactly
    /// what deos sends back to Hermes over the ACP `session/request_permission`.
    pub fn admit_call(&mut self, call: &ToolCallRequest, now: i64) -> PermissionOutcome {
        self.admit_with_work(call, now, None)
    }

    /// As [`HermesGateway::admit_call`], but with EXPLICIT `work` overriding the
    /// auto-derived tool witness. Pass `Some(vec![])` for a pure metered
    /// admission (the metering alone IS the receipted proof the call was
    /// authorized); pass `None` to let the bridge derive the witness from the
    /// call payload (the default `admit_call` behavior).
    pub fn admit_with_work(
        &mut self,
        call: &ToolCallRequest,
        now: i64,
        work: Option<Vec<Effect>>,
    ) -> PermissionOutcome {
        // Tightest-wins routing: a per-tool grant if pinned, else the kind floor.
        let key = self.registry.key_for_tool(&call.name);
        // The in-band tool id the gate checks scope against is the grant's id —
        // the ACP wire does not carry our scalar id, so the grantor's per-key id
        // IS the scope key. A call routed to the right worker is in-scope there;
        // the RATE + DEADLINE legs do the live confinement.
        let tool_id = self.registry.tool_id_for_key(&key);

        // GAP 2 — the SESSION-WIDE budget cap, checked BEFORE the per-worker gate:
        // pool spend across every worker so the consumer's TOTAL spend is bounded.
        // Refused in-band (no worker touched, no turn, no charge) once the session
        // cap is hit, even if this worker's per-mandate budget still has head-room.
        if let Some(reason) = self.session_budget_refusal(&key) {
            return PermissionOutcome::Reject {
                tool_call_id: call.tool_call_id.clone(),
                reason,
            };
        }

        let gw = match self.gateway_for(&key) {
            Ok(gw) => gw,
            Err(e) => {
                return PermissionOutcome::Reject {
                    tool_call_id: call.tool_call_id.clone(),
                    reason: format!("could not admit worker for {}: {e}", key.label()),
                };
            }
        };

        // The tool's side-effect rides the SAME metered turn (unless overridden).
        let work = work.unwrap_or_else(|| tool_effects::effects_for_call(call, gw.worker_cell()));

        match gw.invoke(tool_id, now, work) {
            Ok(receipt) => PermissionOutcome::Allow {
                tool_call_id: call.tool_call_id.clone(),
                receipt: hex32(&receipt.receipt.turn_hash),
                remaining: receipt.remaining,
                paid: receipt.paid,
            },
            Err(ToolCallError::Refused(refusal)) => PermissionOutcome::Reject {
                tool_call_id: call.tool_call_id.clone(),
                reason: describe_refusal(&refusal),
            },
            Err(ToolCallError::Sdk(e)) => PermissionOutcome::Reject {
                tool_call_id: call.tool_call_id.clone(),
                reason: format!("executor rejected the metered turn: {e}"),
            },
        }
    }

    /// **Fund a session worker's spend account for real** (GAP 3).
    ///
    /// By default a worker cell is born with a fixed balance. This is the path that
    /// funds it from the consumer's OWN account: it moves `amount` from `funder`'s
    /// cell into the worker the given `tool_name` routes to (admitting that worker
    /// if needed), via a conserving [`Effect::Transfer`] the funder authorizes. The
    /// charges that worker subsequently settles debit value the consumer GENUINELY
    /// transferred in, not a magic birth-balance. `funder` must hold value in the
    /// worker's asset (same runtime/domain).
    pub fn fund_worker(
        &mut self,
        tool_name: &str,
        funder: &SubAgent,
        amount: u64,
    ) -> Result<TurnReceipt, ToolCallError> {
        let key = self.registry.key_for_tool(tool_name);
        let gw = self.gateway_for(&key)?;
        gw.fund(funder, amount).map_err(ToolCallError::Sdk)
    }

    /// Calls made so far on a kind's mandate (0 if never invoked). Counts only
    /// the per-kind worker — tools with their own per-tool grant meter separately
    /// (see [`HermesGateway::calls_made_for_tool`] /
    /// [`HermesGateway::calls_made_for_key`]).
    pub fn calls_made(&self, kind: ToolKind) -> i64 {
        self.calls_made_for_key(&MandateKey::Kind(kind))
    }

    /// Calls made so far on the worker a given tool routes to (its per-tool
    /// grant if pinned, else its kind floor).
    pub fn calls_made_for_tool(&self, name: &str) -> i64 {
        let key = self.registry.key_for_tool(name);
        self.calls_made_for_key(&key)
    }

    /// Calls made so far on a specific [`MandateKey`]'s worker (0 if never
    /// admitted).
    pub fn calls_made_for_key(&self, key: &MandateKey) -> i64 {
        self.gateways.get(key).map_or(0, |gw| gw.calls_made())
    }

    /// Value SPENT so far on a specific [`MandateKey`]'s worker (0 if never
    /// admitted or a free session) — the per-mandate charge tally.
    pub fn spent_for_key(&self, key: &MandateKey) -> u64 {
        self.gateways.get(key).map_or(0, |gw| gw.spent())
    }

    /// Total value spent across every admitted worker this session (the
    /// session-wide charge tally for the mandate inspector / dock).
    pub fn total_spent(&self) -> u64 {
        self.gateways.values().map(|gw| gw.spent()).sum()
    }

    /// Every mandate key that has been admitted (a live worker exists), for the
    /// inspector. Keys never touched this session are absent (calls_made 0).
    pub fn admitted_keys(&self) -> Vec<MandateKey> {
        let mut keys: Vec<MandateKey> = self.gateways.keys().cloned().collect();
        keys.sort_by_key(|k| k.label());
        keys
    }
}

/// A human-readable refusal reason naming the mandate leg that bit — the text
/// deos surfaces to Hermes / the editor on a [`PermissionOutcome::Reject`].
fn describe_refusal(refusal: &GatewayRefusal) -> String {
    match refusal {
        GatewayRefusal::OutOfScope { presented, granted } => {
            format!("out of scope: tool {presented} not granted (mandate covers {granted})")
        }
        GatewayRefusal::PastDeadline { now, deadline } => {
            format!("past deadline: presented at {now}, mandate expired at {deadline}")
        }
        GatewayRefusal::OverRate {
            calls_made,
            rate_limit,
        } => format!("rate exhausted: {calls_made} of {rate_limit} calls used this mandate window"),
        GatewayRefusal::OverBudget {
            spent,
            price,
            budget,
        } => format!(
            "budget exhausted: {spent} spent + {price} price exceeds the {budget} allowance this mandate"
        ),
        // NOT a mandate leg — the verified admission oracle reached NO VERDICT, so the call is
        // refused fail-closed. Say so plainly: this is an operator/build problem (the linked archive
        // lacks `dregg_deleg_admit`, or this target cannot link it), not the user overrunning a caveat.
        GatewayRefusal::OracleUnavailable { reason } => format!(
            "refused fail-closed: the verified admission oracle reached no verdict ({reason})"
        ),
    }
}

/// Hex-encode a 32-byte receipt hash as the ACP-visible receipt id.
fn hex32(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}
