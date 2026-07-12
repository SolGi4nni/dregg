//! # OFFERING #1 — a HOSTED, CONFINED HERMES AGENT as a [`dreggnet_offerings::Offering`].
//!
//! The dungeon ([`dreggnet_offerings::dungeon`]) is offering #0 — a confined,
//! verifiable, per-session **game**. This crate is the first **non-game**
//! instance of the SAME abstraction: a jailed AI agent. It proves the offering
//! shape carries a category that is not a scripted world at all — a live agent
//! loop — over the identical `open`/`advance`/`verify`/`render`/`price` surface.
//!
//! ## The model
//!
//! * a **session** ([`HermesSession`]) is a **confined agent**: a per-session
//!   [`AgentRuntime`](dregg_sdk::AgentRuntime) + root token derived from the
//!   session seed (the agent descends from a real identity, not an ambient one),
//!   and a lazily-admitted cap-gated **worker per tool class** — each a real
//!   [`ToolGateway`](dregg_sdk::ToolGateway) carrying a RATE cap
//!   ([`ToolGrant`](dregg_sdk::ToolGrant)) AND a VALUE budget
//!   ([`Charge`](dregg_sdk::Charge));
//! * an **advance** ([`Offering::advance`]) is **one metered, cap-bounded turn**:
//!   a mock [`Brain`] classifies the user's input into a proposed tool-call, and
//!   the **executor referees it** through the gateway — an in-mandate call lands a
//!   real [`TurnReceipt`](dregg_sdk::ToolReceipt) ([`Outcome::Landed`]); a
//!   rate-exhausted / over-budget / out-of-mandate call is a real
//!   [`GatewayRefusal`](dregg_sdk::GatewayRefusal) ([`Outcome::Refused`]) that
//!   commits nothing — **the confinement tooth: the agent CANNOT exceed its
//!   cell's mandate**, no matter what its brain proposes;
//! * **verify** ([`Offering::verify`]) re-derives a fresh identically-seeded
//!   confined agent and re-drives the recorded inputs, confirming it reproduces
//!   the committed **confinement decision chain** (each step's admit/refuse verdict
//!   + the rate/value meters). A forged / reordered / relabeled record fails
//!   replay — the same replay tooth the dungeon uses over its world state.
//!
//! ## What is REAL vs. the mock brain (honest scope)
//!
//! REAL substrate, proven by the tests here:
//! * the [`ToolGateway`](dregg_sdk::ToolGateway) path — `admit_priced` + `invoke`
//!   run on the verified executor and yield a genuine
//!   [`TurnReceipt`](dregg_sdk::ToolReceipt) (the receipt hash is proof the metered
//!   turn committed);
//! * the RATE cap AND the VALUE `Charge` budget — an over-rate or over-budget call
//!   is refused with NO turn and NO spend, naming the leg that bit;
//! * the per-session binding — the agent's runtime + root token descend from the
//!   session seed.
//!
//! THE BRAIN SEAM — real by default. The [`Brain`] that maps an input to a
//! tool-call is the REAL [`deos_hermes::ResidentBrain`] by default
//! ([`ResidentBrainAdapter`]): the on-box `LocalBrain` with no key, a live Anthropic
//! / OpenAI-compatible brain when the operator's `ANTHROPIC_API_KEY` /
//! `HERMES_API_KEY` is set. The scripted [`ScriptedBrain`] (a small command grammar,
//! the same shape as `discord-bot/src/hermes_channel.rs`'s `classify`) is RETAINED as
//! the hermetic mock the enforcement tests wire in ([`HermesOffering::scripted`]).
//! The **enforcement seam** — input → cap-gated metered receipted turn → response —
//! is identical for either brain; only the producer of the tool-call changes, so the
//! confinement is brain-agnostic. HONEST SCOPE: a live BYO-key brain run needs a
//! provider key in the env; the offering's replay-`verify` determinism holds for the
//! deterministic on-box / scripted brains (a fresh-state brain over the same input
//! yields the same class), the load-bearing property being the confinement chain.

use std::collections::HashMap;
use std::sync::{Arc, RwLock};

use dregg_sdk::{
    AgentCipherclerk, AgentRuntime, Attenuation, CellId, Charge, GatewayRefusal, HeldToken,
    SdkError, ToolCallError, ToolGateway, ToolGrant,
};

use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};

use deos_hermes::{AgentConvo, BrainStep, LlmBrain, ResidentBrain, resident_brain_from_env};

use deos_view::{MenuItem, ViewNode};

/// The affordance verb a Hermes input fires — a free-text prompt to the confined
/// agent. The [`Action::label`] carries the message text; the [`Brain`] classifies
/// it into a proposed tool-call the executor then referees.
pub const TURN_PROMPT: &str = "prompt";

/// The hosted offering's display name.
pub const HERMES_NAME: &str = "Hosted Hermes";

/// The confined agent's mandate, stated for the user.
pub const HERMES_MANDATE: &str = "drive a jailed agent one cap-bounded, metered, receipted turn at a time — it cannot exceed its cell's mandate";

// ─────────────────────────────────────────────────────────────────────────────
// The tool classes the agent is confined under.
// ─────────────────────────────────────────────────────────────────────────────

/// The ACP-style tool classes a confined Hermes session is bounded under (mirrors
/// `deos_hermes::ToolKind` / the discord-bot's `hermes_channel::ToolKind`). Each is
/// an independently-metered, cap-gated worker: a rate ceiling ([`ToolGrant`]) and a
/// value budget ([`Charge`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ToolKind {
    /// Read-only file access (generous).
    Read,
    /// Search / grep (generous).
    Search,
    /// Web fetch (moderate — the value-budget demo class).
    Fetch,
    /// Shell / terminal execution (tight — the dangerous class).
    Execute,
    /// File writes / edits (tight).
    Edit,
    /// Conversational fall-through (the default class).
    Chat,
}

impl ToolKind {
    /// Every class, for enumeration (the affordance surface, replay, tests).
    pub const ALL: [ToolKind; 6] = [
        ToolKind::Read,
        ToolKind::Search,
        ToolKind::Fetch,
        ToolKind::Execute,
        ToolKind::Edit,
        ToolKind::Chat,
    ];

    /// The stable display id.
    pub fn as_str(self) -> &'static str {
        match self {
            ToolKind::Read => "Read",
            ToolKind::Search => "Search",
            ToolKind::Fetch => "Fetch",
            ToolKind::Execute => "Execute",
            ToolKind::Edit => "Edit",
            ToolKind::Chat => "Chat",
        }
    }

    /// A stable, distinct in-band tool id per class (the SCOPE's in-band face —
    /// the id the gateway's [`ToolGrant`] allowlists).
    pub fn tool_id(self) -> i64 {
        match self {
            ToolKind::Read => 10,
            ToolKind::Search => 20,
            ToolKind::Fetch => 30,
            ToolKind::Execute => 40,
            ToolKind::Edit => 50,
            ToolKind::Chat => 90,
        }
    }

    /// The executor method verb the worker's biscuit credential is scoped to (the
    /// SCOPE's executor face — a turn under any other verb is rejected by the
    /// executor itself with `TokenInsufficientCapability`).
    pub fn method(self) -> &'static str {
        match self {
            ToolKind::Read => "tool.read",
            ToolKind::Search => "tool.search",
            ToolKind::Fetch => "tool.fetch",
            ToolKind::Execute => "tool.execute",
            ToolKind::Edit => "tool.edit",
            ToolKind::Chat => "tool.chat",
        }
    }

    /// The default rate ceiling per class — dangerous classes tight, read-only /
    /// chat classes generous (mirrors the discord-bot's deos defaults).
    pub fn default_rate(self) -> i64 {
        match self {
            ToolKind::Read => 200,
            ToolKind::Search => 100,
            ToolKind::Fetch => 50,
            ToolKind::Execute => 20,
            ToolKind::Edit => 30,
            ToolKind::Chat => 500,
        }
    }
}

/// **The confinement profile** — per-class rate ceiling + value budget the session
/// admits each worker under. The RATE meters HOW MANY calls a class permits
/// (the [`ToolGrant`] ceiling); the BUDGET meters the cumulative VALUE the class may
/// spend (the [`Charge`] allowance, at a per-call price of 1). Either can be the
/// binding constraint: a tight rate makes `OverRate` bite first, a tight budget
/// makes `OverBudget` bite first — the two independent teeth of the mandate.
#[derive(Clone, Debug)]
pub struct Confinement {
    /// Per-class `(rate_limit, value_budget)`. A class absent from the map uses its
    /// [`ToolKind::default_rate`] for both (rate == budget → budget non-binding).
    caps: HashMap<ToolKind, (i64, u64)>,
}

impl Default for Confinement {
    /// The default profile: each class at its [`ToolKind::default_rate`], budget
    /// equal to the rate (so the rate is the binding constraint by default).
    fn default() -> Self {
        let mut caps = HashMap::new();
        for kind in ToolKind::ALL {
            let r = kind.default_rate();
            caps.insert(kind, (r, r.max(0) as u64));
        }
        Confinement { caps }
    }
}

impl Confinement {
    /// The `(rate_limit, value_budget)` for a class.
    pub fn for_kind(&self, kind: ToolKind) -> (i64, u64) {
        self.caps.get(&kind).copied().unwrap_or_else(|| {
            let r = kind.default_rate();
            (r, r.max(0) as u64)
        })
    }

    /// Tighten (or open) a class's RATE ceiling (chainable). Keeps the budget
    /// non-binding (== the new rate) unless [`Self::with_budget`] narrows it.
    pub fn with_rate(mut self, kind: ToolKind, rate_limit: i64) -> Self {
        self.caps
            .insert(kind, (rate_limit, rate_limit.max(0) as u64));
        self
    }

    /// Tighten a class's VALUE budget (chainable) while leaving its rate. Set a
    /// budget below the rate to make `OverBudget` the binding tooth for that class.
    pub fn with_budget(mut self, kind: ToolKind, value_budget: u64) -> Self {
        let rate = self
            .caps
            .get(&kind)
            .map(|(r, _)| *r)
            .unwrap_or_else(|| kind.default_rate());
        self.caps.insert(kind, (rate, value_budget));
        self
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The BRAIN seam — a mock/scripted classifier stands in for the live LLM.
// ─────────────────────────────────────────────────────────────────────────────

/// A tool-call the [`Brain`] proposes from a user input — which class, the tool
/// name, and the remaining argument text. The confinement referees the CLASS; the
/// tool/arg are the payload the live brain would drive (empty in the metered turn's
/// work here — the named seam).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HermesCall {
    /// The confined class this call is metered under.
    pub kind: ToolKind,
    /// The Hermes tool name (display / the live brain's payload target).
    pub tool: String,
    /// The argument text (the rest of the message).
    pub arg: String,
}

/// **The agent's brain** — the producer of a tool-call from an input. THE SEAM: in
/// the live integration this is the real Hermes LLM over ACP; the offering's tests
/// drive a scripted [`ScriptedBrain`] so the enforcement loop is proven with no
/// model credentials. Implementations must be deterministic (a given input yields
/// the same call) so the session replay-verifies.
pub trait Brain: Send + Sync {
    /// Propose a tool-call for `input`.
    fn propose(&self, input: &str) -> HermesCall;

    /// The agent's textual response for a landed call (the mock overlay a live
    /// brain would generate). Default: a scripted acknowledgement.
    fn respond(&self, call: &HermesCall) -> String {
        format!("[{}] {} {}", call.kind.as_str(), call.tool, call.arg.trim())
            .trim()
            .to_string()
    }

    /// A secret-free label naming this brain seam — the offering reports it
    /// ([`HermesOffering::brain_seam`]) so a caller can confirm which producer is
    /// wired: the REAL resident brain at deploy vs the scripted mock in tests. NEVER
    /// includes a credential (the resident label is on-box / a provider NAME only).
    fn seam_label(&self) -> String {
        "custom brain seam".to_string()
    }
}

/// A deterministic scripted brain — a small command grammar mapping a leading verb
/// to a [`ToolKind`] (`read …` / `search …` / `fetch …` / `run …` / `write …`,
/// else `chat`). The mock stand-in for the live LLM; the enforcement seam it drives
/// is identical to the real one.
#[derive(Clone, Debug, Default)]
pub struct ScriptedBrain;

impl Brain for ScriptedBrain {
    fn propose(&self, input: &str) -> HermesCall {
        let trimmed = input.trim();
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
        HermesCall {
            kind,
            tool: tool.to_string(),
            arg: rest.to_string(),
        }
    }

    fn seam_label(&self) -> String {
        "scripted-mock".to_string()
    }
}

/// Test-facing alias for the deterministic scripted mock brain — the name the
/// enforcement tests wire in (the confinement is brain-agnostic; the mock keeps the
/// tests hermetic, no env / no network / no key).
pub type MockBrain = ScriptedBrain;

// ─────────────────────────────────────────────────────────────────────────────
// The REAL brain seam — the deos_hermes::ResidentBrain, behind the same `Brain`.
// ─────────────────────────────────────────────────────────────────────────────

/// **The REAL brain seam** — wraps [`deos_hermes::ResidentBrain`] (the on-box /
/// BYO-key resident brain resolver) behind this crate's [`Brain`] trait, so a
/// deployed [`HermesOffering`] drives a real closed-loop brain by DEFAULT while the
/// confinement/metering enforcement is unchanged.
///
/// THE ADAPTER (the named seam): the resident brain speaks
/// [`deos_hermes::LlmBrain`] — `&mut self`, a running [`AgentConvo`] → a
/// [`BrainStep`] (call a tool / finish) in a decide→observe loop; this crate's
/// [`Brain`] is a deterministic, `&self`, single-input → [`HermesCall`] classifier.
/// The adapter bridges them by building a FRESH resident brain per `propose` (from a
/// factory) and taking its FIRST step over a one-shot [`AgentConvo`], mapping the
/// proposed Hermes tool name to the confined [`ToolKind`] it is metered under. Fresh
/// state + the same input yields the same class for the deterministic on-box brain,
/// so the offering's replay-`verify` holds.
///
/// A live BYO-key brain calls the model provider inside `propose` (needs a key,
/// non-hermetic) — the deploy path; the tests pin the scripted mock via
/// [`HermesOffering::scripted`] instead.
pub struct ResidentBrainAdapter {
    /// Builds a fresh resident brain per proposal. Default:
    /// [`deos_hermes::resident_brain_from_env`] — `ANTHROPIC_API_KEY` → live
    /// Anthropic, `HERMES_API_KEY` → an OpenAI-compatible endpoint, else the on-box
    /// `LocalBrain` (hermetic, keyless).
    factory: Arc<dyn Fn() -> ResidentBrain + Send + Sync>,
    /// The working directory the one-shot [`AgentConvo`] opens in (presentational —
    /// the confinement referees the tool CLASS, not the cwd/args).
    cwd: String,
}

impl Default for ResidentBrainAdapter {
    fn default() -> Self {
        ResidentBrainAdapter::from_env()
    }
}

impl ResidentBrainAdapter {
    /// The default resident seam: resolve the brain from the operator environment on
    /// each proposal (BYO key → live provider; else the hermetic on-box brain). The
    /// factory stores the resolver — no env is read until a proposal drives it.
    pub fn from_env() -> Self {
        ResidentBrainAdapter {
            factory: Arc::new(resident_brain_from_env),
            cwd: ".".to_string(),
        }
    }

    /// A resident seam over a caller-supplied brain factory (e.g. a fixed on-box
    /// brain, or a deterministic test double) — chainable with [`Self::with_cwd`].
    pub fn with_factory(factory: Arc<dyn Fn() -> ResidentBrain + Send + Sync>) -> Self {
        ResidentBrainAdapter {
            factory,
            cwd: ".".to_string(),
        }
    }

    /// Set the working directory the one-shot conversation opens in (chainable).
    pub fn with_cwd(mut self, cwd: impl Into<String>) -> Self {
        self.cwd = cwd.into();
        self
    }

    /// A secret-free description of the resolved resident brain ("on-box …" / a
    /// provider NAME) — builds a brain and reads its label; never touches the
    /// network, never prints a credential.
    pub fn describe(&self) -> String {
        (self.factory)().describe()
    }
}

impl Brain for ResidentBrainAdapter {
    fn propose(&self, input: &str) -> HermesCall {
        let mut brain = (self.factory)();
        let convo = AgentConvo::new(&self.cwd, input);
        match brain.next_step(&convo) {
            BrainStep::CallTool { name, arguments } => {
                // The confinement referees the CLASS; the arg text is presentational
                // (empty for `Null`, the string body for a string, else compact JSON).
                let arg = if arguments.is_null() {
                    String::new()
                } else if let Some(s) = arguments.as_str() {
                    s.to_string()
                } else {
                    arguments.to_string()
                };
                HermesCall {
                    kind: tool_kind_for(&name),
                    tool: name,
                    arg,
                }
            }
            BrainStep::Finish { text } => HermesCall {
                kind: ToolKind::Chat,
                tool: "chat".to_string(),
                arg: text,
            },
        }
    }

    fn seam_label(&self) -> String {
        format!("resident: {}", self.describe())
    }
}

/// Map a resident brain's Hermes tool NAME to the confined [`ToolKind`] it is
/// metered under — mirrors [`ScriptedBrain`]'s verb→class routing and the tool
/// surface `deos_hermes`'s brains advertise (`web_search` / `read_file` /
/// `write_file` / `terminal`). An unknown tool falls into the conversational
/// [`ToolKind::Chat`] class (the safe default the gate still meters).
fn tool_kind_for(name: &str) -> ToolKind {
    match name {
        "read_file" | "read" | "cat" | "open" => ToolKind::Read,
        "search" | "grep" | "find" => ToolKind::Search,
        "web_search" | "fetch" | "web" | "browse" => ToolKind::Fetch,
        "terminal" | "run" | "shell" | "exec" => ToolKind::Execute,
        "write_file" | "edit" | "write" | "patch" => ToolKind::Edit,
        _ => ToolKind::Chat,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The committed confinement record.
// ─────────────────────────────────────────────────────────────────────────────

/// One driven turn's committed confinement record — the input, the class the brain
/// routed it to, and the executor's VERDICT (admit/refuse + the meters). The replay
/// verifier reproduces exactly this chain from a fresh identically-seeded agent; a
/// forged entry diverges.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HermesStep {
    /// The user input driving this turn.
    pub input: String,
    /// The presentation clock the turn was metered at.
    pub now: i64,
    /// The class the brain routed the input to (the metered mandate).
    pub kind: ToolKind,
    /// Whether the executor admitted the call (a real metered turn committed).
    pub allowed: bool,
    /// The committed turn hash (hex), present iff `allowed` — a genuine receipt.
    pub receipt: Option<String>,
    /// The rate calls remaining on this class's mandate after the turn (iff
    /// `allowed`; a refusal does not advance the counter).
    pub remaining: Option<i64>,
    /// The cumulative VALUE spent on this class after the turn (the `Charge` meter).
    pub spent: u64,
    /// The refusal reason naming the leg that bit (iff `!allowed`).
    pub reason: Option<String>,
}

/// **A confined Hermes session** — offering #1's live state. Owns the per-session
/// [`AgentRuntime`] + root token (derived from the session seed), the lazily-admitted
/// cap-gated worker per class, the shared value sink each class's [`Charge`] pays to,
/// the presentation clock, and the committed [`HermesStep`] chain [`Offering::verify`]
/// re-verifies by replay.
pub struct HermesSession {
    /// The u64 config seed — [`Offering::verify`] re-opens an identically-seeded
    /// session from it to replay the confinement chain.
    seed: u64,
    /// The per-session confined agent runtime.
    runtime: AgentRuntime,
    /// The root token every worker's mandate is delegated from (minted under the
    /// session seed — the agent's own authority, not an ambient one).
    root: HeldToken,
    /// The session-wide mandate expiry (a clock ceiling shared by every grant).
    deadline: i64,
    /// The confinement profile (per-class rate + value budget).
    confinement: Confinement,
    /// The lazily-admitted cap-gated worker per class (rate cap + value `Charge`).
    gateways: HashMap<ToolKind, ToolGateway>,
    /// The shared value sink each class's per-call charge is paid to (a spawned
    /// sibling worker, so the conserving transfer commits offline). Spawned lazily.
    sink: Option<CellId>,
    /// The presentation clock — advances one tick per driven turn.
    clock: i64,
    /// The committed confinement chain (every driven turn, landed or refused).
    steps: Vec<HermesStep>,
    /// The agent's last textual response (the mock brain's overlay), for `render`.
    last_response: Option<String>,
}

impl HermesSession {
    /// The committed confinement chain (every driven turn).
    pub fn steps(&self) -> &[HermesStep] {
        &self.steps
    }

    /// The number of real committed (landed) turns so far — each carries a genuine
    /// receipt.
    pub fn committed_turns(&self) -> usize {
        self.steps.iter().filter(|s| s.allowed).count()
    }

    /// The rate calls remaining on a class's mandate (full head-room if the class
    /// has never been admitted).
    pub fn rate_remaining(&self, kind: ToolKind) -> i64 {
        match self.gateways.get(&kind) {
            Some(gw) => gw.remaining(),
            None => self.confinement.for_kind(kind).0,
        }
    }

    /// The value budget remaining on a class's mandate.
    pub fn budget_remaining(&self, kind: ToolKind) -> u64 {
        match self.gateways.get(&kind) {
            Some(gw) => gw.budget_remaining().unwrap_or(0),
            None => self.confinement.for_kind(kind).1,
        }
    }

    /// Whether a class currently has head-room (rate AND budget) for one more call —
    /// the affordance's `enabled` decoration (the executor stays the sole referee).
    pub fn has_headroom(&self, kind: ToolKind) -> bool {
        self.rate_remaining(kind) > 0 && self.budget_remaining(kind) > 0
    }

    /// The agent's last response (the mock brain's overlay).
    pub fn last_response(&self) -> Option<&str> {
        self.last_response.as_deref()
    }

    /// Lazily spawn (once) the shared value sink each class's `Charge` pays to.
    fn ensure_sink(&mut self) -> Result<CellId, SdkError> {
        if let Some(c) = self.sink {
            return Ok(c);
        }
        let s =
            self.runtime
                .spawn_sub_agent_scoped(&Attenuation::default(), &self.root, &["sink"])?;
        let c = s.cell_id();
        self.sink = Some(c);
        Ok(c)
    }

    /// Lazily admit (or fetch) the cap-gated PRICED worker for a class — the RATE
    /// grant AND the value `Charge` budget, on the verified executor.
    fn gateway_for(&mut self, kind: ToolKind) -> Result<&mut ToolGateway, SdkError> {
        if !self.gateways.contains_key(&kind) {
            let (rate, budget) = self.confinement.for_kind(kind);
            let sink = self.ensure_sink()?;
            let grant = ToolGrant {
                tool_id: kind.tool_id(),
                rate_limit: rate,
                deadline: self.deadline,
                tool_method: kind.method().to_string(),
            };
            // Per-call price of 1 against a `budget` allowance: the value tooth
            // bites when the class's cumulative spend reaches `budget`.
            let charge = Charge::new(1, sink, budget);
            let gw = ToolGateway::admit_priced(&self.runtime, &self.root, grant, Some(charge))?;
            self.gateways.insert(kind, gw);
        }
        Ok(self.gateways.get_mut(&kind).expect("just inserted"))
    }
}

/// **The Hermes offering** — offering #1. A stateless factory over a confined-agent
/// universe; each [`open`](Offering::open) deploys a fresh [`HermesSession`]. Carries
/// the [`Confinement`] profile (the mandate each session's workers are admitted
/// under), the [`Brain`] seam (the REAL [`deos_hermes::ResidentBrain`] by default —
/// on-box, or a live BYO-key brain; the scripted mock in tests), the per-turn
/// inference [`RunCost`], and the session mandate window.
pub struct HermesOffering {
    confinement: Confinement,
    brain: Arc<dyn Brain>,
    /// Run-credits a turn's confined inference costs (`0` → free tier). The
    /// substrate turn is always free + verifiable; this prices the mock/live brain.
    inference_credits: u64,
    /// The session mandate window (added to the base clock to fix each session's
    /// `deadline`). A generous default; tighten it to demonstrate the deadline leg.
    deadline_span: i64,
}

impl Default for HermesOffering {
    fn default() -> Self {
        HermesOffering::new()
    }
}

impl HermesOffering {
    /// The default confined offering: the default [`Confinement`], the REAL
    /// [`deos_hermes::ResidentBrain`] seam ([`ResidentBrainAdapter::from_env`] —
    /// on-box by default, a live BYO-key brain when a provider key is set), the free
    /// inference tier, a generous 30-day-equivalent window. Use [`Self::scripted`]
    /// for the hermetic mock-brain test constructor.
    pub fn new() -> Self {
        HermesOffering {
            confinement: Confinement::default(),
            brain: Arc::new(ResidentBrainAdapter::from_env()),
            inference_credits: 0,
            deadline_span: 60 * 60 * 24 * 30,
        }
    }

    /// The offering wired with the deterministic scripted mock [`Brain`]
    /// ([`ScriptedBrain`] / [`MockBrain`]) — the hermetic TEST constructor (no env,
    /// no network, no key). The confinement/metering substrate is identical to
    /// [`Self::new`]; only the brain seam differs. [`Self::new`] instead resolves the
    /// REAL [`deos_hermes::ResidentBrain`] seam.
    pub fn scripted() -> Self {
        HermesOffering::new().with_brain(Arc::new(ScriptedBrain))
    }

    /// The secret-free label of the wired brain seam — `resident: …` for the real
    /// default resident brain (on-box / a provider name), `scripted-mock` for the
    /// test mock. Lets a caller confirm the default swap without driving a turn.
    pub fn brain_seam(&self) -> String {
        self.brain.seam_label()
    }

    /// Set the confinement profile (per-class rate + value budget) — chainable.
    pub fn with_confinement(mut self, confinement: Confinement) -> Self {
        self.confinement = confinement;
        self
    }

    /// Swap the [`Brain`] seam — the live LLM at deploy, a scripted mock in tests.
    pub fn with_brain(mut self, brain: Arc<dyn Brain>) -> Self {
        self.brain = brain;
        self
    }

    /// Price a turn's confined inference at `credits` run-credits (the frontend
    /// debits them; the substrate turn stays free + verifiable).
    pub fn with_inference_credits(mut self, credits: u64) -> Self {
        self.inference_credits = credits;
        self
    }

    /// Set the session mandate window (the span added to the base clock to fix the
    /// `deadline`). Tighten it to demonstrate the past-deadline refusal leg.
    pub fn with_deadline_span(mut self, span: i64) -> Self {
        self.deadline_span = span;
        self
    }

    /// The confinement profile this offering admits sessions under.
    pub fn confinement(&self) -> &Confinement {
        &self.confinement
    }

    /// Derive the 32-byte agent root key from a u64 config seed (domain-separated),
    /// so a session has a deterministic, replay-verifiable identity.
    fn seed_bytes(seed: u64) -> [u8; 32] {
        blake3::derive_key("dreggnet-hermes.session-root.v1", &seed.to_le_bytes())
    }

    /// Drive ONE metered, cap-bounded turn: the brain proposes a call, the executor
    /// referees it through the class's gateway, and the verdict is recorded. Shared
    /// by [`Offering::advance`] (live) and [`Offering::verify`] (replay).
    fn drive(&self, session: &mut HermesSession, input: &str) -> Outcome {
        let call = self.brain.propose(input);
        let kind = call.kind;
        let now = session.clock;
        session.clock += 1;

        let gw = match session.gateway_for(kind) {
            Ok(gw) => gw,
            Err(e) => {
                let reason = format!("could not admit confined worker: {e}");
                session.steps.push(HermesStep {
                    input: input.to_string(),
                    now,
                    kind,
                    allowed: false,
                    receipt: None,
                    remaining: None,
                    spent: 0,
                    reason: Some(reason.clone()),
                });
                return Outcome::Refused(reason);
            }
        };

        // The metered turn: advance the class's rate counter c → c+1, ride the
        // per-call `Charge` (a conserving consumer → sink transfer). An empty work
        // witness — the live brain's tool payload would ride here (the named seam);
        // the receipt witnesses the AUTHORIZATION + the metered spend.
        match gw.invoke(kind.tool_id(), now, vec![]) {
            Ok(tool_receipt) => {
                let remaining = tool_receipt.remaining;
                let spent = gw.spent();
                let receipt_hex = hex32(&tool_receipt.receipt.turn_hash);
                let response = self.brain.respond(&call);
                session.last_response = Some(response);
                session.steps.push(HermesStep {
                    input: input.to_string(),
                    now,
                    kind,
                    allowed: true,
                    receipt: Some(receipt_hex),
                    remaining: Some(remaining),
                    spent,
                    reason: None,
                });
                Outcome::Landed {
                    receipt: tool_receipt.receipt,
                    ended: false,
                }
            }
            Err(ToolCallError::Refused(refusal)) => {
                let spent = gw.spent();
                let reason = describe_refusal(&refusal);
                session.steps.push(HermesStep {
                    input: input.to_string(),
                    now,
                    kind,
                    allowed: false,
                    receipt: None,
                    remaining: None,
                    spent,
                    reason: Some(reason.clone()),
                });
                Outcome::Refused(reason)
            }
            Err(ToolCallError::Sdk(e)) => {
                let spent = gw.spent();
                let reason = format!("executor rejected the metered turn: {e}");
                session.steps.push(HermesStep {
                    input: input.to_string(),
                    now,
                    kind,
                    allowed: false,
                    receipt: None,
                    remaining: None,
                    spent,
                    reason: Some(reason.clone()),
                });
                Outcome::Refused(reason)
            }
        }
    }
}

impl Offering for HermesOffering {
    type Session = HermesSession;

    /// Deploy a fresh confined agent: build the per-session runtime + root token from
    /// the config seed, pin the mandate window, and return a session ready to drive.
    /// Workers (the cap-gated tool classes) are admitted lazily on first use.
    fn open(&self, cfg: SessionConfig) -> Result<HermesSession, OfferingError> {
        let seed = cfg.seed.unwrap_or(1);
        let key = Self::seed_bytes(seed);
        let mut cclerk = AgentCipherclerk::from_key_bytes(zeroize::Zeroizing::new(key));
        let root = cclerk.mint_token(&key, "hermes-session");
        let runtime = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "hermes-session");

        // The base clock is 1; the mandate window fixes the shared deadline.
        let base_clock = 1;
        let deadline = base_clock + self.deadline_span;

        Ok(HermesSession {
            seed,
            runtime,
            root,
            deadline,
            confinement: self.confinement.clone(),
            gateways: HashMap::new(),
            sink: None,
            clock: base_clock,
            steps: Vec::new(),
            last_response: None,
        })
    }

    /// The tool classes the confined agent can currently exercise — the cap-gated
    /// affordances a frontend renders. Each is an [`Action`] whose `enabled` is the
    /// class's live head-room (rate AND budget); the executor stays the sole referee.
    fn actions(&self, session: &HermesSession) -> Vec<Action> {
        ToolKind::ALL
            .iter()
            .map(|&kind| {
                Action::new(
                    format!(
                        "{} — {} calls / {} budget left",
                        kind.as_str(),
                        session.rate_remaining(kind),
                        session.budget_remaining(kind),
                    ),
                    TURN_PROMPT,
                    kind.tool_id(),
                    session.has_headroom(kind),
                )
            })
            .collect()
    }

    /// **Drive one metered, cap-bounded turn.** [`Action::label`] carries the user's
    /// input; the [`Brain`] classifies it into a proposed tool-call; the executor
    /// referees it through the class's gateway. An in-mandate call lands a real
    /// [`TurnReceipt`](dregg_sdk::ToolReceipt) ([`Outcome::Landed`]); a rate-exhausted
    /// / over-budget / out-of-mandate call is a real refusal ([`Outcome::Refused`])
    /// that commits nothing — the confinement tooth. `actor` is session metadata (the
    /// executor signs with the confined worker's own cap).
    fn advance(
        &self,
        session: &mut HermesSession,
        input: Action,
        _actor: DreggIdentity,
    ) -> Outcome {
        if input.turn != TURN_PROMPT {
            return Outcome::Refused(format!("unknown affordance: {}", input.turn));
        }
        self.drive(session, &input.label)
    }

    /// **Re-verify the confinement chain by REPLAY** — re-derive a fresh
    /// identically-seeded confined agent and re-drive the recorded inputs, confirming
    /// it reproduces exactly the committed confinement decision chain (each step's
    /// class + admit/refuse verdict + the rate/value meters). A forged / reordered /
    /// relabeled record diverges. (Receipt HASHES are per-session identities, not
    /// compared; the load-bearing content is the confinement DECISION + the meters,
    /// which are a deterministic function of the seed + the input sequence.)
    fn verify(&self, session: &HermesSession) -> VerifyReport {
        let committed = session.committed_turns();
        let mut fresh = match self.open(SessionConfig {
            seed: Some(session.seed),
        }) {
            Ok(s) => s,
            Err(e) => return VerifyReport::broken(committed, format!("re-open failed: {e}")),
        };

        for (i, recorded) in session.steps.iter().enumerate() {
            let _ = self.drive(&mut fresh, &recorded.input);
            let replayed = match fresh.steps.get(i) {
                Some(s) => s,
                None => {
                    return VerifyReport::broken(committed, format!("replay produced no step {i}"));
                }
            };
            if replayed.kind != recorded.kind
                || replayed.allowed != recorded.allowed
                || replayed.remaining != recorded.remaining
                || replayed.spent != recorded.spent
            {
                return VerifyReport::broken(
                    committed,
                    format!(
                        "replay diverged at step {i}: recorded (kind={:?}, allowed={}, remaining={:?}, spent={}) vs replayed (kind={:?}, allowed={}, remaining={:?}, spent={})",
                        recorded.kind,
                        recorded.allowed,
                        recorded.remaining,
                        recorded.spent,
                        replayed.kind,
                        replayed.allowed,
                        replayed.remaining,
                        replayed.spent,
                    ),
                );
            }
        }
        VerifyReport::ok(committed)
    }

    /// Render the confined agent as a **deos affordance [`Surface`]**: the agent's
    /// last response + the mandate + the committed-turn count, and the tool classes
    /// as a cap-gated affordance [`Menu`](ViewNode::Menu) (each row a class with its
    /// live head-room; an exhausted class is a dimmed `!enabled` row).
    fn render(&self, session: &HermesSession) -> Surface {
        let response = session
            .last_response()
            .unwrap_or("Send a prompt (e.g. `read notes.txt`, `search foo`, `run ls`) to drive one confined turn.");

        let items = self
            .actions(session)
            .into_iter()
            .map(|a| MenuItem {
                label: a.label,
                turn: a.turn,
                arg: a.arg,
                enabled: a.enabled,
            })
            .collect();

        let children = vec![
            ViewNode::Text(response.to_string()),
            ViewNode::Section {
                title: "Mandate".to_string(),
                tag: "muted".to_string(),
                children: vec![ViewNode::Text(HERMES_MANDATE.to_string())],
            },
            ViewNode::Section {
                title: "Committed turns".to_string(),
                tag: "genuine".to_string(),
                children: vec![ViewNode::Text(session.committed_turns().to_string())],
            },
            ViewNode::Section {
                title: "Tool classes".to_string(),
                tag: "accent".to_string(),
                children: vec![ViewNode::Menu { items }],
            },
        ];

        Surface(ViewNode::Section {
            title: format!("{HERMES_NAME} — confined agent"),
            tag: "accent".to_string(),
            children,
        })
    }

    /// The turn's [`RunCost`] — the free tier by default; the paid tier prices the
    /// confined inference (which the frontend debits + runs). The substrate turn
    /// itself is always free + verifiable.
    fn price(&self, _input: &Action) -> RunCost {
        RunCost::credits(self.inference_credits)
    }
}

/// A human-readable refusal naming the mandate leg that bit — the text an
/// [`Outcome::Refused`] carries (the confinement's in-band face).
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
            "value budget exhausted: {spent} spent + {price} price exceeds the {budget} allowance"
        ),
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

// ─────────────────────────────────────────────────────────────────────────────
// The replay-tamper tooth — an in-crate test (it reaches the session's private
// `steps` to forge the committed record). The end-to-end driven flow
// (open → advance → verify → render) lives in `tests/driven.rs`.
// ─────────────────────────────────────────────────────────────────────────────
#[cfg(test)]
mod tamper_tests {
    use super::*;

    /// A legal line re-verifies by replay; then a FORGED committed record (a refused
    /// step relabeled as allowed) fails replay — the recomputed truth diverges from
    /// the tampered claim. The confinement chain tooth, through the [`Offering`] API.
    #[test]
    fn a_forged_verdict_fails_replay() {
        // Execute confined to rate 1: the second `run` is a real refusal. The mock
        // brain keeps the replay deterministic (the enforcement is brain-agnostic).
        let off = HermesOffering::scripted()
            .with_confinement(Confinement::default().with_rate(ToolKind::Execute, 1));
        let mut s = off.open(SessionConfig::with_seed(7)).expect("open");
        let actor = DreggIdentity("user".to_string());

        assert!(
            off.advance(&mut s, prompt("run echo hi"), actor.clone())
                .landed(),
            "the first Execute call lands"
        );
        let second = off.advance(&mut s, prompt("run echo again"), actor.clone());
        assert!(
            !second.landed(),
            "the second Execute call is refused (rate 1)"
        );
        assert!(off.verify(&s).verified, "the honest chain re-verifies");

        // Forge the record: claim the refused second step was allowed.
        s.steps[1].allowed = true;
        s.steps[1].remaining = Some(0);
        let report = off.verify(&s);
        assert!(
            !report.verified,
            "a forged verdict must fail replay: {}",
            report.detail
        );
    }

    fn prompt(text: &str) -> Action {
        Action::new(text, TURN_PROMPT, 0, true)
    }
}
