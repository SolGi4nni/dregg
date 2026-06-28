//! Drive-your-Hermes-from-your-channel — the per-user confined agent loop.
//!
//! A message in a user's semi-private channel ([`crate::channels`]) drives THAT
//! user's own Hermes instance. Every message becomes a cap-gated, metered,
//! RECEIPTED dregg turn through the PROVEN [`ToolGateway`](dregg_sdk::ToolGateway)
//! over the verified executor — or an in-band refusal the user sees. This is the
//! ADOS thesis (a turn = the exercise of an attenuable proof-carrying token over
//! owned state, leaving a verifiable receipt) realized per Discord user.
//!
//! # What is REAL vs. the named seam (honest)
//!
//! REAL — and proven offline by the tests in this module:
//! * the [`ToolGateway`](dregg_sdk::ToolGateway) path: `admit` + `invoke` run on
//!   the verified Lean executor and yield a genuine
//!   [`TurnReceipt`](dregg_turn::TurnReceipt) (the receipt hash is the proof the
//!   metered turn committed);
//! * the per-user binding: each user's runtime + root token are derived from
//!   THEIR own custodial seed (the same seed [`crate::cipherclerk::seed_for`]
//!   gives their cell), so a user's Hermes is bounded by their own identity and
//!   the grant ceilings deos pins — not an ambient one;
//! * the in-band refusal: an over-rate / out-of-mandate / past-deadline message
//!   is refused with NO turn and NO spend, naming the leg that bit.
//!
//! THE SEAM (the live-Hermes brain): here the *tool-call* is derived
//! DETERMINISTICALLY from the message text by [`classify`] — a small command
//! grammar (`read …`, `search …`, `fetch …`, `run …`, `write …`, else a `chat`).
//! In the live integration this classifier is replaced by the actual Hermes LLM
//! over the **Agent Client Protocol** (the canonical seam is `deos-hermes`'s
//! [`HermesGateway`] driving an `acp_client` against a real `hermes-acp`
//! subprocess). The *enforcement seam this module wires* — message → cap-gated
//! metered receipted turn → reply — is identical either way; only the producer of
//! the tool-call changes. This shim keeps zero new build surface (it reuses the
//! SDK's `ToolGateway` already in the bot's graph) while the heavyweight
//! `deos-hermes`/firmament ACP transport stays the named live target.

use std::collections::HashMap;
use std::sync::{Arc, RwLock};

use dregg_sdk::{
    AgentCipherclerk, AgentRuntime, Attenuation, CellId, Charge, GatewayRefusal, HeldToken,
    SdkError, ToolCallError, ToolGateway, ToolGrant,
};

use crate::llm_provider::{LlmPolicy, PermissionDenied, Provider};

/// The ACP tool classes deos confines a Hermes session under (mirrors
/// `deos_hermes::ToolKind`). The classifier maps a message's leading verb to one
/// of these; each is an independently-metered cap-gated worker.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ToolKind {
    Read,
    Search,
    Fetch,
    Execute,
    Edit,
    Chat,
    /// The LLM "brain" call — a metered, cap-gated, PAID inference turn driven by
    /// the user's OWN ported-in provider key ([`crate::llm_provider`]). Unlike the
    /// other kinds (rate-only), the LLM gateway is admitted with a value `Charge`
    /// so the user's token BUDGET is enforced on-ledger alongside the rate.
    Llm,
}

impl ToolKind {
    pub fn as_str(self) -> &'static str {
        match self {
            ToolKind::Read => "Read",
            ToolKind::Search => "Search",
            ToolKind::Fetch => "Fetch",
            ToolKind::Execute => "Execute",
            ToolKind::Edit => "Edit",
            ToolKind::Chat => "Chat",
            ToolKind::Llm => "Llm",
        }
    }

    /// A stable, distinct in-band tool id per kind (the SCOPE's in-band face).
    fn tool_id(self) -> i64 {
        match self {
            ToolKind::Read => 10,
            ToolKind::Search => 20,
            ToolKind::Fetch => 30,
            ToolKind::Execute => 40,
            ToolKind::Edit => 50,
            ToolKind::Chat => 90,
            ToolKind::Llm => 80,
        }
    }

    /// The executor method verb the worker's biscuit credential is scoped to.
    fn method(self) -> &'static str {
        match self {
            ToolKind::Read => "tool.read",
            ToolKind::Search => "tool.search",
            ToolKind::Fetch => "tool.fetch",
            ToolKind::Execute => "tool.execute",
            ToolKind::Edit => "tool.edit",
            ToolKind::Chat => "tool.chat",
            ToolKind::Llm => "tool.llm",
        }
    }

    /// deos's default rate ceiling per kind — the dangerous classes are tight,
    /// the read-only / chat classes generous.
    fn default_rate(self) -> i64 {
        match self {
            ToolKind::Read => 200,
            ToolKind::Search => 100,
            ToolKind::Fetch => 50,
            ToolKind::Execute => 20,
            ToolKind::Edit => 30,
            ToolKind::Chat => 500,
            ToolKind::Llm => 100,
        }
    }
}

/// A classified tool-call derived from a channel message: which class, the Hermes
/// tool name, and the remaining argument text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClassifiedCall {
    pub kind: ToolKind,
    pub tool: String,
    pub arg: String,
}

/// Classify a channel message into a tool-call. THE SEAM: in the live
/// integration the Hermes LLM produces this over ACP; here a small command
/// grammar derives it deterministically so the enforcement loop is exercised
/// end-to-end without model credentials.
pub fn classify(message: &str) -> ClassifiedCall {
    let trimmed = message.trim();
    let (verb, rest) = match trimmed.split_once(char::is_whitespace) {
        Some((v, r)) => (v, r.trim()),
        None => (trimmed, ""),
    };
    let (kind, tool) = match verb.to_ascii_lowercase().as_str() {
        "read" | "cat" | "open" => (ToolKind::Read, "read_file"),
        "search" | "grep" | "find" => (ToolKind::Search, "search"),
        "fetch" | "get" | "browse" => (ToolKind::Fetch, "web_search"),
        "run" | "exec" | "shell" | "terminal" => (ToolKind::Execute, "terminal"),
        "write" | "edit" | "patch" => (ToolKind::Edit, "write_file"),
        _ => (ToolKind::Chat, "chat"),
    };
    ClassifiedCall {
        kind,
        tool: tool.to_string(),
        arg: rest.to_string(),
    }
}

/// The verdict the channel loop posts back to the user.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HermesVerdict {
    /// The classified call this verdict is for.
    pub call: ClassifiedCall,
    /// Whether the gateway admitted the call (a metered turn committed).
    pub allowed: bool,
    /// The committed turn hash (hex), present iff `allowed`.
    pub receipt: Option<String>,
    /// Calls remaining on this kind's mandate after the call.
    pub remaining: Option<i64>,
    /// The refusal reason naming the leg that bit, present iff `!allowed`.
    pub reason: Option<String>,
}

impl HermesVerdict {
    /// The user-facing one-line summary posted to the channel.
    pub fn summary(&self) -> String {
        if self.allowed {
            let r = self.receipt.as_deref().unwrap_or("");
            let short = &r[..r.len().min(16)];
            format!(
                "✅ `{}` ({}) — cap-gated turn committed · receipt `{}…` · {} calls left",
                self.call.tool,
                self.call.kind.as_str(),
                short,
                self.remaining.unwrap_or_default()
            )
        } else {
            format!(
                "⛔ `{}` ({}) refused in-band — {}",
                self.call.tool,
                self.call.kind.as_str(),
                self.reason.as_deref().unwrap_or("no mandate")
            )
        }
    }
}

/// One user's confined Hermes session: a runtime + root token derived from the
/// user's own seed, and a lazily-admitted cap-gated worker per [`ToolKind`].
///
/// Held across messages so rate budgets accumulate within the session window —
/// a user who burns their `Execute` mandate sees the next `run` refused in-band.
pub struct ChannelHermes {
    runtime: AgentRuntime,
    root: HeldToken,
    deadline: i64,
    grants: HashMap<ToolKind, ToolGrant>,
    gateways: HashMap<ToolKind, ToolGateway>,
    /// The BYO-key policy bounding LLM-brain calls (allowed providers/models,
    /// token budget, rate). `None` until the user sets a key + policy.
    policy: Option<LlmPolicy>,
    /// The PRICED gateway for LLM-brain calls — admitted lazily from [`policy`]
    /// on the first authorized call. Distinct from the rate-only [`gateways`]
    /// because it carries a value [`Charge`] enforcing the token budget.
    llm_gateway: Option<ToolGateway>,
    /// The sink cell each LLM call's value charge is paid to (a spawned sibling
    /// worker, so the conserving transfer commits offline). Spawned lazily.
    llm_sink: Option<CellId>,
}

impl ChannelHermes {
    /// Open a confined session for a user, bound to their own custodial `seed`
    /// (the same 32-byte seed [`crate::cipherclerk::seed_for`] derives — so this
    /// agent descends from the user's identity). `deadline` is the session-wide
    /// mandate expiry (a clock/height ceiling shared by every grant).
    pub fn for_user(seed: [u8; 32], deadline: i64) -> Self {
        let mut cclerk = AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(seed));
        // The root token the user delegates each worker's mandate from, minted
        // under the user's own seed (their authority, not an ambient one).
        let root = cclerk.mint_token(&seed, "hermes-channel");
        let runtime = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "hermes-channel");

        let mut grants = HashMap::new();
        for kind in [
            ToolKind::Read,
            ToolKind::Search,
            ToolKind::Fetch,
            ToolKind::Execute,
            ToolKind::Edit,
            ToolKind::Chat,
        ] {
            grants.insert(
                kind,
                ToolGrant {
                    tool_id: kind.tool_id(),
                    rate_limit: kind.default_rate(),
                    deadline,
                    tool_method: kind.method().to_string(),
                },
            );
        }

        ChannelHermes {
            runtime,
            root,
            deadline,
            grants,
            gateways: HashMap::new(),
            policy: None,
            llm_gateway: None,
            llm_sink: None,
        }
    }

    /// Install the BYO-key policy bounding this user's LLM-brain calls (allowed
    /// providers/models, token budget, rate). Chainable.
    pub fn with_llm_policy(mut self, policy: LlmPolicy) -> Self {
        self.policy = Some(policy);
        self
    }

    /// Set/replace the BYO-key policy (e.g. after the user rotates their key or
    /// adjusts their budget via `/key`). Resets the priced gateway so the new
    /// budget/rate take effect on the next call.
    pub fn set_llm_policy(&mut self, policy: LlmPolicy) {
        self.policy = Some(policy);
        self.llm_gateway = None;
    }

    /// The currently installed policy, if any.
    pub fn policy(&self) -> Option<&LlmPolicy> {
        self.policy.as_ref()
    }

    /// Override a kind's grant (tighten a rate ceiling / deny a class). Used by
    /// the deny-by-default tests and available for per-user policy.
    pub fn with_grant(mut self, kind: ToolKind, rate_limit: i64) -> Self {
        let grant = ToolGrant {
            tool_id: kind.tool_id(),
            rate_limit,
            deadline: self.deadline,
            tool_method: kind.method().to_string(),
        };
        self.grants.insert(kind, grant);
        self
    }

    /// Lazily admit (or fetch) the cap-gated worker for a kind.
    fn gateway_for(&mut self, kind: ToolKind) -> Result<&mut ToolGateway, ToolCallError> {
        if !self.gateways.contains_key(&kind) {
            let grant = self.grants.get(&kind).cloned().expect("grant per kind");
            let gw =
                ToolGateway::admit(&self.runtime, &self.root, grant).map_err(ToolCallError::Sdk)?;
            self.gateways.insert(kind, gw);
        }
        Ok(self.gateways.get_mut(&kind).expect("just inserted"))
    }

    /// THE LOOP — drive a channel message as a cap-gated, metered, receipted turn
    /// (or an in-band refusal). `now` is the presentation clock (message arrival
    /// height/time). Returns the verdict to post back.
    pub fn drive(&mut self, message: &str, now: i64) -> HermesVerdict {
        let call = classify(message);
        let kind = call.kind;
        let tool_id = kind.tool_id();

        let gw = match self.gateway_for(kind) {
            Ok(gw) => gw,
            Err(e) => {
                return HermesVerdict {
                    call,
                    allowed: false,
                    receipt: None,
                    remaining: None,
                    reason: Some(format!("could not admit worker: {e}")),
                };
            }
        };

        // The metering alone IS the receipted proof the call was authorized; we
        // pass an empty work witness (the live brain's tool payload would ride
        // here — the named seam). The receipt witnesses the authorization.
        match gw.invoke(tool_id, now, vec![]) {
            Ok(receipt) => HermesVerdict {
                call,
                allowed: true,
                receipt: Some(hex32(&receipt.receipt.turn_hash)),
                remaining: Some(receipt.remaining),
                reason: None,
            },
            Err(ToolCallError::Refused(refusal)) => HermesVerdict {
                call,
                allowed: false,
                receipt: None,
                remaining: None,
                reason: Some(describe_refusal(&refusal)),
            },
            Err(ToolCallError::Sdk(e)) => HermesVerdict {
                call,
                allowed: false,
                receipt: None,
                remaining: None,
                reason: Some(format!("executor rejected the metered turn: {e}")),
            },
        }
    }

    /// Calls committed so far on a kind's mandate (0 if never invoked).
    pub fn calls_made(&self, kind: ToolKind) -> i64 {
        self.gateways.get(&kind).map_or(0, |gw| gw.calls_made())
    }

    /// Lazily admit (or fetch) the PRICED LLM gateway carrying the token budget.
    /// Spawns a value sink (a sibling worker) on first use so the per-call charge
    /// is a real conserving transfer between same-asset cells. The value budget is
    /// quantized to call-units (`token_budget / est_tokens_per_call`) with a
    /// per-call price of 1, so the charge commits within the worker's birth
    /// balance while `OverBudget` bites exactly when the token allowance is spent.
    fn llm_gateway_for(&mut self, policy: &LlmPolicy) -> Result<&mut ToolGateway, SdkError> {
        if self.llm_gateway.is_none() {
            let sink = match self.llm_sink {
                Some(c) => c,
                None => {
                    let s = self.runtime.spawn_sub_agent_scoped(
                        &Attenuation::default(),
                        &self.root,
                        &["sink"],
                    )?;
                    let c = s.cell_id();
                    self.llm_sink = Some(c);
                    c
                }
            };
            let grant = ToolGrant {
                tool_id: ToolKind::Llm.tool_id(),
                rate_limit: policy.rate_limit,
                deadline: self.deadline,
                tool_method: ToolKind::Llm.method().to_string(),
            };
            let est = policy.est_tokens_per_call.max(1);
            let budget_units = (policy.token_budget / est).max(1);
            let charge = Charge::new(1, sink, budget_units);
            let gw = ToolGateway::admit_priced(&self.runtime, &self.root, grant, Some(charge))?;
            self.llm_gateway = Some(gw);
        }
        Ok(self.llm_gateway.as_mut().expect("just inserted"))
    }

    /// THE LLM BRAIN SEAM — authorize an inference call on the user's OWN key.
    ///
    /// All enforcement is IN-BAND, before any (paid) provider call:
    ///
    /// 1. **permission** — the policy must permit `provider` (and `model`);
    /// 2. **token budget + rate** — the priced [`ToolGateway`] admits the call IFF
    ///    rate AND token-budget head-room remain, committing a real cap-gated
    ///    metered turn (the receipt) and charging one budget unit. An over-budget
    ///    / over-rate / past-deadline call is REFUSED in-band naming the leg — no
    ///    provider call, no spend.
    ///
    /// On `allowed`, the caller performs the actual provider call (mock in tests /
    /// live behind `HERMES_LIVE_LLM`) with the user's key and may record the real
    /// token usage; the budget the gateway enforces is the pre-call estimate (the
    /// only thing knowable before the call).
    pub fn authorize_llm(&mut self, provider: Provider, model: &str, now: i64) -> LlmVerdict {
        let policy = match self.policy.clone() {
            Some(p) => p,
            None => {
                return LlmVerdict::refused(
                    provider,
                    model,
                    "no LLM policy set (the user has not ported in a key)",
                );
            }
        };

        // §1 — provider/model permission (deny-by-policy, in-band).
        if let Err(denied) = policy.permit(provider, model) {
            return LlmVerdict::refused(provider, model, &denied_reason(&denied));
        }

        // §2 — admit (lazily) the priced LLM gateway, then meter the call.
        let est = policy.est_tokens_per_call.max(1);
        let gw = match self.llm_gateway_for(&policy) {
            Ok(gw) => gw,
            Err(e) => {
                return LlmVerdict::refused(
                    provider,
                    model,
                    &format!("could not admit LLM worker: {e}"),
                );
            }
        };
        match gw.invoke(ToolKind::Llm.tool_id(), now, vec![]) {
            Ok(receipt) => {
                let spent_units = gw.spent();
                let budget_units = gw.charge().map(|c| c.budget).unwrap_or(0);
                LlmVerdict {
                    provider,
                    model: model.to_string(),
                    allowed: true,
                    receipt: Some(hex32(&receipt.receipt.turn_hash)),
                    remaining_calls: Some(receipt.remaining),
                    tokens_spent: spent_units.saturating_mul(est),
                    token_budget: budget_units.saturating_mul(est),
                    reason: None,
                }
            }
            Err(ToolCallError::Refused(r)) => {
                LlmVerdict::refused(provider, model, &describe_refusal_llm(&r, est))
            }
            Err(ToolCallError::Sdk(e)) => LlmVerdict::refused(
                provider,
                model,
                &format!("executor rejected the metered LLM turn: {e}"),
            ),
        }
    }

    /// LLM-brain calls committed so far this session (0 if never invoked).
    pub fn llm_calls_made(&self) -> i64 {
        self.llm_gateway.as_ref().map_or(0, |gw| gw.calls_made())
    }
}

/// The verdict of an [`ChannelHermes::authorize_llm`] decision — posted back to
/// the user and recorded in the per-channel ledger.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LlmVerdict {
    /// The provider this call was authorized against.
    pub provider: Provider,
    /// The model requested.
    pub model: String,
    /// Whether the metered LLM turn committed (the user's key-use was authorized).
    pub allowed: bool,
    /// The committed turn hash (hex), present iff `allowed`.
    pub receipt: Option<String>,
    /// LLM calls remaining on the rate mandate after this call.
    pub remaining_calls: Option<i64>,
    /// Tokens charged against the budget so far this window (estimate-based).
    pub tokens_spent: u64,
    /// The total token budget for the window.
    pub token_budget: u64,
    /// The refusal reason naming the leg that bit, present iff `!allowed`.
    pub reason: Option<String>,
}

impl LlmVerdict {
    fn refused(provider: Provider, model: &str, reason: &str) -> Self {
        LlmVerdict {
            provider,
            model: model.to_string(),
            allowed: false,
            receipt: None,
            remaining_calls: None,
            tokens_spent: 0,
            token_budget: 0,
            reason: Some(reason.to_string()),
        }
    }

    /// The user-facing one-line summary posted to the channel.
    pub fn summary(&self) -> String {
        if self.allowed {
            let r = self.receipt.as_deref().unwrap_or("");
            let short = &r[..r.len().min(16)];
            format!(
                "🧠 `{}`/`{}` — authorized · receipt `{}…` · {} tokens of {} budget · {} calls left",
                self.provider.as_str(),
                self.model,
                short,
                self.tokens_spent,
                self.token_budget,
                self.remaining_calls.unwrap_or_default()
            )
        } else {
            format!(
                "⛔ `{}`/`{}` LLM call refused in-band — {}",
                self.provider.as_str(),
                self.model,
                self.reason.as_deref().unwrap_or("no mandate")
            )
        }
    }
}

/// A human-readable permission refusal (the provider/model gate).
fn denied_reason(denied: &PermissionDenied) -> String {
    denied.to_string()
}

/// Like [`describe_refusal`] but translates the LLM gateway's call-unit
/// `OverBudget` into a token-budget message (the user's mental model is tokens).
fn describe_refusal_llm(r: &GatewayRefusal, est: u64) -> String {
    match r {
        GatewayRefusal::OverBudget { spent, budget, .. } => format!(
            "token budget exhausted: {} of {} tokens used this window",
            spent.saturating_mul(est),
            budget.saturating_mul(est)
        ),
        other => describe_refusal(other),
    }
}

/// A human-readable refusal naming the mandate leg that bit (the text the user
/// sees in their channel).
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
            "budget exhausted: {spent} spent + {price} price exceeds the {budget} allowance"
        ),
    }
}

/// Seconds since the Unix epoch — the presentation clock for a channel message.
fn now_secs() -> i64 {
    use std::time::{SystemTime, UNIX_EPOCH};
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
}

/// THE CHANNEL LOOP — route a Discord message in a managed channel to its
/// owner's confined Hermes, commit the cap-gated turn, record it, reply.
///
/// Called from the gateway message handler. Non-managed channels and bot
/// messages are ignored. Only the channel owner (or the admin co-driving) drives
/// the owner's session; the session is held in [`crate::BotState`] so rate
/// budgets accumulate across messages.
pub async fn on_message(
    ctx: &serenity::all::Context,
    msg: &serenity::all::Message,
    state: &crate::BotState,
) {
    if msg.author.bot {
        return;
    }
    let content = msg.content.trim();
    if content.is_empty() {
        return;
    }

    let channel_id = msg.channel_id.get().to_string();
    let chan = match state.db.get_user_channel(&channel_id).await {
        Ok(Some(c)) => c,
        _ => return, // not a DreggNet Cloud per-user channel
    };

    let author = msg.author.id.get();
    let owner: u64 = chan.discord_id.parse().unwrap_or(0);
    let is_admin = state.config.admin_discord_id == Some(author);
    if author != owner && !is_admin {
        // Semi-private posture: peers may read (if permitted) but only the owner
        // or the admin drives the owner's agent.
        return;
    }

    let now = now_secs();
    let seed = crate::cipherclerk::seed_for(&state.config.bot_secret, owner);
    let deadline = now + 60 * 60 * 24 * 30; // a generous 30-day session window

    // ── BYO-key LLM brain ────────────────────────────────────────────────────
    // A conversational message (classified `Chat`) is routed through the user's
    // OWN ported-in provider key when one is set — metered + permissioned by the
    // dregg gateway. Tool-verb messages (read/search/…) keep the existing
    // cap-gated classifier path below.
    if classify(content).kind == ToolKind::Chat {
        if let Ok(Some(rec)) = state.db.get_llm_key(&owner.to_string()).await {
            llm_brain_message(ctx, msg, state, owner, seed, deadline, now, content, rec).await;
            return;
        }
    }

    // Drive the owner's session synchronously; the std lock is never held across
    // an await (the verdict is produced, then the guard drops).
    let verdict = {
        let mut sessions = state
            .channel_hermes
            .lock()
            .unwrap_or_else(|p| p.into_inner());
        let hermes = sessions
            .entry(owner)
            .or_insert_with(|| ChannelHermes::for_user(seed, deadline));
        hermes.drive(content, now)
    };

    // Append to the per-channel agent ledger (the admin portal monitors this).
    let _ = state
        .db
        .record_hermes_activity(
            &owner.to_string(),
            &channel_id,
            content,
            &verdict.call.tool,
            verdict.call.kind.as_str(),
            verdict.allowed,
            verdict.receipt.as_deref(),
            verdict.remaining,
            verdict.reason.as_deref(),
            now,
        )
        .await;

    let _ = msg.channel_id.say(&ctx.http, verdict.summary()).await;
}

/// THE BYO-KEY LLM BRAIN LOOP — drive a conversational channel message through
/// the owner's OWN provider key, metered + permissioned by dregg.
///
/// Authorization (permission ∧ token-budget ∧ rate) is enforced IN-BAND on the
/// gateway before any provider call; the actual call runs ONLY when the operator
/// has enabled live calls (`HERMES_LIVE_LLM`). The decrypted key is held
/// transiently for the request and dropped.
#[allow(clippy::too_many_arguments)]
async fn llm_brain_message(
    ctx: &serenity::all::Context,
    msg: &serenity::all::Message,
    state: &crate::BotState,
    owner: u64,
    seed: [u8; 32],
    deadline: i64,
    now: i64,
    content: &str,
    rec: crate::db::LlmKeyRecord,
) {
    let channel_id = msg.channel_id.get().to_string();
    let provider = Provider::parse(&rec.provider).unwrap_or(Provider::Anthropic);
    let model = if rec.model.trim().is_empty() {
        provider.default_model().to_string()
    } else {
        rec.model.clone()
    };

    // Authorize synchronously — the std lock is never held across an await.
    let verdict = {
        let mut sessions = state
            .channel_hermes
            .lock()
            .unwrap_or_else(|p| p.into_inner());
        let hermes = sessions
            .entry(owner)
            .or_insert_with(|| ChannelHermes::for_user(seed, deadline));
        if hermes.policy().is_none() {
            hermes.set_llm_policy(LlmPolicy::for_provider(
                provider,
                rec.token_budget.max(0) as u64,
                rec.rate_limit,
            ));
        }
        hermes.authorize_llm(provider, &model, now)
    };

    // Record the metered LLM verdict in the per-channel agent ledger.
    let _ = state
        .db
        .record_hermes_activity(
            &owner.to_string(),
            &channel_id,
            content,
            "llm.chat",
            "Llm",
            verdict.allowed,
            verdict.receipt.as_deref(),
            verdict.remaining_calls,
            verdict.reason.as_deref(),
            now,
        )
        .await;

    if !verdict.allowed {
        let _ = msg.channel_id.say(&ctx.http, verdict.summary()).await;
        return;
    }

    // Authorized. The live provider call runs only when the operator enabled it;
    // otherwise post the enforcement verdict (the loop is proven offline).
    let live = std::env::var("HERMES_LIVE_LLM")
        .map(|v| v != "0" && !v.is_empty())
        .unwrap_or(false);
    if live {
        match run_live_llm(state, owner, provider, &model, content).await {
            Ok(text) => {
                let footer = format!(
                    "\n\n— {} tokens of {} budget · {} calls left",
                    verdict.tokens_spent,
                    verdict.token_budget,
                    verdict.remaining_calls.unwrap_or_default()
                );
                let _ = msg
                    .channel_id
                    .say(&ctx.http, format!("{}{footer}", truncate_discord(&text)))
                    .await;
            }
            Err(e) => {
                let _ = msg
                    .channel_id
                    .say(&ctx.http, format!("⚠️ provider call failed: {e}"))
                    .await;
            }
        }
    } else {
        let _ = msg
            .channel_id
            .say(
                &ctx.http,
                format!(
                    "{}\n_(live calls disabled — set `HERMES_LIVE_LLM=1` to call your provider with your key)_",
                    verdict.summary()
                ),
            )
            .await;
    }
}

/// Decrypt the user's key and call the provider (the live path). The plaintext
/// key is held only for the request and dropped (zeroized). Errors are redacted —
/// the key never appears in a returned message.
async fn run_live_llm(
    state: &crate::BotState,
    owner: u64,
    provider: Provider,
    model: &str,
    prompt: &str,
) -> Result<String, String> {
    let rec = state
        .db
        .get_llm_key(&owner.to_string())
        .await
        .map_err(|e| format!("db error: {e}"))?
        .ok_or_else(|| "key not found".to_string())?;
    let sealed = crate::key_vault::EncryptedKey::from_b64(&rec.nonce_b64, &rec.ciphertext_b64)
        .map_err(|e| e.to_string())?;
    let key = crate::key_vault::open(&state.config.bot_secret, owner, provider.as_str(), &sealed)
        .map_err(|_| "could not decrypt your key — re-set it with /key".to_string())?;
    let client = reqwest::Client::new();
    crate::llm_provider::live_complete(&client, provider, model, &key, prompt, 1024)
        .await
        .map(|c| c.text)
        .map_err(|e| e.to_string())
}

/// Clamp a provider reply to fit a Discord message.
fn truncate_discord(s: &str) -> String {
    const MAX: usize = 1800;
    if s.chars().count() <= MAX {
        s.to_string()
    } else {
        let mut t: String = s.chars().take(MAX).collect();
        t.push('…');
        t
    }
}

/// Hex-encode a 32-byte receipt hash.
fn hex32(bytes: &[u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    fn seed() -> [u8; 32] {
        [3u8; 32]
    }

    #[test]
    fn classify_maps_verbs_to_tool_kinds() {
        assert_eq!(classify("read README.md").kind, ToolKind::Read);
        assert_eq!(classify("search for foo").kind, ToolKind::Search);
        assert_eq!(classify("fetch https://x").kind, ToolKind::Fetch);
        assert_eq!(classify("run ls -la").kind, ToolKind::Execute);
        assert_eq!(classify("write notes.txt hi").kind, ToolKind::Edit);
        // Anything not a known verb is a chat (the generous default class).
        assert_eq!(classify("hello there agent").kind, ToolKind::Chat);
        assert_eq!(classify("run rm -rf /").tool, "terminal");
        assert_eq!(classify("read foo").arg, "foo");
    }

    #[test]
    fn a_message_becomes_a_real_cap_gated_receipted_turn() {
        // GENUINE ✓ — a `read` message, in-time, within the Read rate. The
        // metered turn COMMITS on the verified executor and the verdict carries a
        // real 64-hex turn hash + the remaining budget. This is the proven loop:
        // message → cap-gated hermes turn → reply.
        let mut hermes = ChannelHermes::for_user(seed(), 1_000_000);
        let verdict = hermes.drive("read README.md", 100);

        assert!(verdict.allowed, "an in-rate read commits: {verdict:?}");
        let receipt = verdict
            .receipt
            .clone()
            .expect("a committed turn has a receipt");
        assert_eq!(
            receipt.len(),
            64,
            "receipt is a hex-encoded 32-byte turn hash"
        );
        assert!(receipt.chars().all(|c| c.is_ascii_hexdigit()));
        assert_eq!(verdict.remaining, Some(199), "one Read-200 budget consumed");
        assert_eq!(hermes.calls_made(ToolKind::Read), 1);
        assert!(verdict.summary().contains("committed"));
    }

    #[test]
    fn over_rate_message_refused_in_band_no_turn() {
        // CHEAT ✗ — tighten Execute to rate 1; the second `run` exceeds it and is
        // refused IN-BAND naming the rate leg. No turn, no counter advance.
        let mut hermes =
            ChannelHermes::for_user(seed(), 1_000_000).with_grant(ToolKind::Execute, 1);

        let first = hermes.drive("run echo hi", 100);
        assert!(first.allowed, "first call commits: {first:?}");

        let second = hermes.drive("run echo again", 100);
        assert!(!second.allowed, "second exceeds the rate-1 mandate");
        assert!(
            second.reason.as_deref().unwrap().contains("rate exhausted"),
            "names the rate leg: {second:?}"
        );
        assert_eq!(
            hermes.calls_made(ToolKind::Execute),
            1,
            "the refusal did not advance the counter"
        );
        assert!(second.summary().contains("refused"));
    }

    #[test]
    fn denied_class_refuses_on_first_attempt() {
        // deos can deny a whole class: Execute rate 0 → every `run` fails closed
        // in-band on the first attempt.
        let mut hermes =
            ChannelHermes::for_user(seed(), 1_000_000).with_grant(ToolKind::Execute, 0);
        let verdict = hermes.drive("run anything", 100);
        assert!(!verdict.allowed);
        assert!(
            verdict
                .reason
                .as_deref()
                .unwrap()
                .contains("rate exhausted")
        );
        assert_eq!(hermes.calls_made(ToolKind::Execute), 0);
    }

    #[test]
    fn past_deadline_message_refused_in_band() {
        // A message presented after the session mandate deadline is refused
        // in-band even with rate head-room.
        let mut hermes = ChannelHermes::for_user(seed(), 1_000);
        let verdict = hermes.drive("read file", 2_000);
        assert!(!verdict.allowed);
        assert!(verdict.reason.as_deref().unwrap().contains("past deadline"));
    }

    #[test]
    fn kinds_are_independently_metered() {
        let mut hermes = ChannelHermes::for_user(seed(), 1_000_000);
        assert!(hermes.drive("read a", 10).allowed);
        assert!(hermes.drive("search b", 10).allowed);
        assert_eq!(hermes.calls_made(ToolKind::Read), 1);
        assert_eq!(hermes.calls_made(ToolKind::Search), 1);
        assert_eq!(
            hermes.calls_made(ToolKind::Execute),
            0,
            "untouched class stays 0"
        );
    }

    // ─── BYO-key LLM brain: metered + permissioned key-use ───────────────────

    use crate::key_vault::PlaintextKey;
    use crate::llm_provider::{LlmTransport, MockTransport};

    #[test]
    fn an_llm_call_is_authorized_metered_and_drives_a_mock_provider() {
        // GENUINE ✓ — a permitted, in-budget, in-rate LLM call commits a REAL
        // cap-gated metered turn (a 64-hex receipt) and debits the token budget;
        // then a MOCK provider drives the reply (no network, no paid call).
        let policy = LlmPolicy::for_provider(Provider::Anthropic, 200_000, 50);
        let mut hermes = ChannelHermes::for_user(seed(), 1_000_000).with_llm_policy(policy);

        let v = hermes.authorize_llm(Provider::Anthropic, "claude-opus-4-8", 100);
        assert!(v.allowed, "permitted in-budget call commits: {v:?}");
        let receipt = v.receipt.clone().expect("a committed turn has a receipt");
        assert_eq!(receipt.len(), 64, "receipt is a hex 32-byte turn hash");
        assert_eq!(v.remaining_calls, Some(49), "one of 50 LLM calls consumed");
        assert!(v.tokens_spent > 0, "the budget was debited");
        assert_eq!(hermes.llm_calls_made(), 1);

        // The provider call itself is mocked — proves the brain seam offline.
        let mock = MockTransport::default();
        let out = mock
            .complete(
                Provider::Anthropic,
                "claude-opus-4-8",
                &PlaintextKey::new("sk-ant-mock"),
                "hello",
            )
            .unwrap();
        assert_eq!(out.text, "mock reply");
        assert_eq!(out.tokens_used, 1_500);
    }

    #[test]
    fn over_token_budget_refused_before_the_call() {
        // CHEAT ✗ — token_budget == est_tokens_per_call → exactly one call of
        // budget. The second is refused IN-BAND on the budget leg, BEFORE any
        // provider call (no spend).
        let policy = LlmPolicy::for_provider(Provider::OpenAi, 2_000, 50); // est=2000 → 1 unit
        let mut hermes = ChannelHermes::for_user(seed(), 1_000_000).with_llm_policy(policy);

        let first = hermes.authorize_llm(Provider::OpenAi, "gpt-4o", 10);
        assert!(first.allowed, "first call within budget: {first:?}");

        let second = hermes.authorize_llm(Provider::OpenAi, "gpt-4o", 10);
        assert!(!second.allowed, "second exceeds the token budget");
        assert!(
            second
                .reason
                .as_deref()
                .unwrap()
                .contains("token budget exhausted"),
            "names the budget leg: {second:?}"
        );
        assert_eq!(
            hermes.llm_calls_made(),
            1,
            "the over-budget refusal did not advance the meter"
        );
    }

    #[test]
    fn over_rate_llm_call_refused() {
        // Rate 1 with a huge budget → the second call is refused on the RATE leg
        // (distinct from the budget leg).
        let policy = LlmPolicy::for_provider(Provider::DeepSeek, 1_000_000, 1);
        let mut hermes = ChannelHermes::for_user(seed(), 1_000_000).with_llm_policy(policy);

        assert!(
            hermes
                .authorize_llm(Provider::DeepSeek, "deepseek-chat", 10)
                .allowed
        );
        let second = hermes.authorize_llm(Provider::DeepSeek, "deepseek-chat", 10);
        assert!(!second.allowed);
        assert!(
            second.reason.as_deref().unwrap().contains("rate"),
            "names the rate leg: {second:?}"
        );
    }

    #[test]
    fn disallowed_provider_refused_with_no_metered_turn() {
        // The permission gate bites BEFORE the gateway: a provider not in the
        // user's allowed set is refused with no metered turn.
        let policy = LlmPolicy::for_provider(Provider::Anthropic, 200_000, 50);
        let mut hermes = ChannelHermes::for_user(seed(), 1_000_000).with_llm_policy(policy);

        let v = hermes.authorize_llm(Provider::OpenAi, "gpt-4o", 10);
        assert!(!v.allowed);
        assert!(v.reason.as_deref().unwrap().contains("not permitted"));
        assert_eq!(
            hermes.llm_calls_made(),
            0,
            "a permission refusal commits no metered turn"
        );
    }

    #[test]
    fn no_policy_refuses_the_llm_brain() {
        // Without a ported-in key (no policy), the brain is unavailable; the
        // classifier path still works.
        let mut hermes = ChannelHermes::for_user(seed(), 1_000_000);
        let v = hermes.authorize_llm(Provider::Anthropic, "claude-opus-4-8", 10);
        assert!(!v.allowed);
        assert!(v.reason.as_deref().unwrap().contains("not ported in a key"));
    }
}
