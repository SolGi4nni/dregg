//! `agent_toolkit` — the **AGENT TOOLKIT** for the Verifiable Agent Cloud.
//!
//! The [`agent`](crate::agent) onramp gives an autonomous agent a budget + a cap
//! bundle and runs it confined: every decided action is cap-gated, metered, and
//! receipted. But in the bare local path an `invoke` *does nothing* — there is no
//! live service behind it. This module supplies the live services: it wraps
//! capabilities dregg **already has** as cap-gated, metered, receipted
//! invoke-able **tools**, so an agent's cap bundle can grant
//! `{run_tests, verify_deploy, check_health}` and the agent actually does QA and
//! ops, not "trust me, I tested".
//!
//! Each tool is a [`ToolKit`] entry behind the existing `invoke` rail, so it
//! inherits the three guarantees for free:
//!
//! - **cap-gated** — a tool not named in the agent's bundle is refused
//!   (`invoke:<tool>` is outside the cap set) *before* it runs;
//! - **metered** — every call is drawn from the replenishing-budget cell; an
//!   exhausted budget refuses further calls in-band (the runaway is contained);
//! - **receipted** — the tool's *verdict* (did the tests pass? did the deploy
//!   verify? is the node healthy?) is bound into the action's receipt, so the QA
//!   result is itself tamper-evident — a forged "tests passed" breaks the
//!   signature.
//! - **execution-witnessed** — beyond the tamper-evident verdict bit, the
//!   compute-tier tools (`run_tests` / `with_witnessed_verify_deploy`) bind a
//!   [`WitnessedRun`](crate::agent::WitnessedRun) — `(command · code_root ·
//!   result)` — into the receipt: the test command, a commitment to the code it
//!   ran (the `code_root`, tied to the deploy's `content_root` so the tests
//!   provably ran on the *deployed* code), and the result (exit + output digest).
//!   [`verify_witnessed_qa`](crate::agent::verify_witnessed_qa) re-executes the
//!   bound and rejects a verdict the execution does not reproduce — so the proof
//!   is "the substrate ran *these* tests on *this* code with *this* result", not
//!   the agent runtime's say-so. The honest residual: the re-execution still runs
//!   in the same compute substrate; full operator-independence needs the tier run
//!   attested by the federation / light client (the in-circuit witness, the
//!   circuit-soundness lane). Layer 4 — whether a suite is *meaningful* — is never
//!   claimed.
//!
//! ## The tools
//!
//! - [`Toolkit::with_run_tests`] — run a test workload through an **injected
//!   compute runner** ([`RunFn`]) and return pass/fail. The QA primitive. The
//!   open core does not own a sandbox; the host injects one (a `Fn(&str,&str) ->
//!   Result<RunReport, String>`), so the witness binding lives here while the
//!   execution lives wherever the host wires it.
//! - [`Toolkit::with_run_workload`] — run an arbitrary workload through the same
//!   injected runner (a load / economy check). Optional.
//! - [`Toolkit::with_check_health`] — probe a [`HealthSnapshot`] and flag
//!   anomalies (consensus divergence, conservation breach, errors, liveness
//!   lapse). The prod-monitoring primitive.
//! - [`Toolkit::with_verify_receipts`] — re-witness a receipt chain with
//!   [`crate::receipt::verify_chain`] (the trustless monitor of the receipt
//!   log).
//! - [`Toolkit::with_verify_deploy`] — wire an external deploy verifier (e.g.
//!   an external served-bytes verifier, the served-bytes-match-the-
//!   committed-root check) as an invoke target. The toolkit does not
//!   re-implement verification; it *wires the existing one* behind the rail. The
//!   caller injects the closure (the crate that owns `verify_site_bundle` sits
//!   above `exec`, so the seam is a closure to avoid a dependency cycle).
//!
//! ## Safe-autonomous vs reviewed-go
//!
//! The tools, the wiring, and the tests are **safe-autonomous** (the local /
//! mock path: the workload runs in the in-process wasm sandbox, the health probe
//! is a supplied snapshot, the verify closure is a pure re-witness). Pointing
//! `check_health` / `monitor` at the **live edge / prod** (the node `/health`,
//! the `dregg-ops` aggregate) is **reviewed-go**: the operator supplies a
//! probe closure that fetches the live read surface.

use std::collections::BTreeMap;

use crate::receipt::{BodyHasher, ReceiptBody, verify_chain};

use crate::agent::{ToolKit, ToolOutcome, WitnessedRun};

// ── execution-witnessing commitments (the Layer-3 binding) ────────────────────

/// The **code commitment** to a workload's source — the `code_root` a witnessed
/// run binds. It is the content commitment a verifier ties to the deploy's
/// published `content_root`: when `run_tests` runs against the deployed artifact,
/// this root equals the deployed root, so a re-witness can confirm *the tests ran
/// on the code that was actually deployed*. (A domain-separated hash of the
/// source bytes, hex-encoded — the std stand-in for the cell's Poseidon2 heap
/// root, the same role `webapp::content_root` plays for served bytes.)
pub fn code_root(source: &str) -> String {
    let mut h = BodyHasher::new(b"dregg-agent-code-root-v1");
    h.field(source.as_bytes());
    hex32(h.finalize())
}

/// The **result digest** over a run's output values — the `output_digest` a
/// witnessed run binds, so the recorded result is itself re-checkable (not a
/// free-form summary string).
fn output_digest(values: &[String]) -> [u8; 32] {
    let mut h = BodyHasher::new(b"dregg-agent-output-digest-v1");
    h.u64(values.len() as u64);
    for v in values {
        h.field(v.as_bytes());
    }
    h.finalize()
}

/// The **command** string a witnessed run binds (the exact test invocation:
/// lang · entrypoint).
fn tests_command(lang: &str) -> String {
    format!("run_tests[lang={lang},entry=run]")
}

/// Map a run's output to an exit / failure count by the `run_tests` convention: a
/// leading `0`/`ok`/`pass`/`true` is exit `0` (green); a numeric leading value is
/// that failure count; anything else is exit `1`.
fn exit_of(values: &[String]) -> i64 {
    let first = values.first().map(|s| s.trim()).unwrap_or("");
    if matches!(first, "0" | "ok" | "OK" | "pass" | "PASS" | "true") {
        return 0;
    }
    first.parse::<i64>().unwrap_or(1)
}

/// Lowercase-hex of a 32-byte digest.
fn hex32(b: [u8; 32]) -> String {
    let mut s = String::with_capacity(64);
    for x in b {
        s.push_str(&format!("{x:02x}"));
    }
    s
}

/// A registered tool's handler: it receives the agent's committed cell heap
/// (read-only context) and returns its verdict. The cap-gate + meter + receipt
/// around it is the `invoke` rail this toolkit plugs into.
pub type ToolFn = Box<dyn Fn(&BTreeMap<String, String>) -> ToolOutcome + Send + Sync>;

/// A **priced** tool's handler: it receives the spend's dollar amount (USD-cents,
/// already drawn from the budget cell before this runs) and the agent's committed
/// cells, and returns its verdict. The seam a budget-gated, variable-amount spend
/// (e.g. an outbound Stripe payout) plugs into.
pub type PricedToolFn = Box<dyn Fn(i64, &BTreeMap<String, String>) -> ToolOutcome + Send + Sync>;

/// The concrete toolkit: a registry of named tools the `invoke` rail dispatches
/// to. Build it with the `with_*` constructors, then run an agent with
/// [`AgentCloud::run_with_toolkit`](crate::agent::AgentCloud::run_with_toolkit).
#[derive(Default)]
pub struct Toolkit {
    tools: BTreeMap<String, ToolFn>,
    priced_tools: BTreeMap<String, PricedToolFn>,
}

impl Toolkit {
    /// An empty toolkit. Add tools with the `with_*` builders.
    pub fn new() -> Toolkit {
        Toolkit {
            tools: BTreeMap::new(),
            priced_tools: BTreeMap::new(),
        }
    }

    /// Register a **priced** tool under `name` — a tool reached by a
    /// [`Spend`](crate::agent::AgentAction::Spend) whose handler receives the spend
    /// amount (USD-cents) already drawn from the budget. The budget gate has
    /// already refused any over-ceiling amount *before* this runs, so the handler
    /// only ever sees a funded amount (no money moves on a refusal).
    pub fn with_priced_tool(
        mut self,
        name: impl Into<String>,
        f: impl Fn(i64, &BTreeMap<String, String>) -> ToolOutcome + Send + Sync + 'static,
    ) -> Toolkit {
        self.priced_tools.insert(name.into(), Box::new(f));
        self
    }

    /// Wire a **budget-gated outbound Stripe spend** tool (`stripe_pay`): a priced
    /// tool whose dollar amount is drawn from the budget cell. `payout` performs
    /// the payout for `amount_cents` and returns `Ok(payout_id)` / `Err(reason)`
    /// (the live path shells the Stripe Link CLI / a payout API; the demo injects a
    /// deterministic recorded stand-in). The amount itself is bound into the
    /// receipt (`cost`) by the run loop, so a forged "I paid $X" breaks the
    /// signature; this tool records the payout id + amount in the verdict summary.
    pub fn with_stripe_pay(
        self,
        name: impl Into<String>,
        payout: impl Fn(i64) -> Result<String, String> + Send + Sync + 'static,
    ) -> Toolkit {
        self.with_priced_tool(name, move |amount_cents, _cells| {
            match payout(amount_cents) {
                Ok(payout_id) => ToolOutcome::pass(format!(
                    "stripe payout of {amount_cents}c submitted (payout {payout_id})"
                )),
                Err(reason) => ToolOutcome::fail(format!("stripe payout FAILED: {reason}")),
            }
        })
    }

    /// Register an arbitrary tool under `name`. The lower-level seam every named
    /// constructor builds on — use it to wire a capability the named helpers
    /// don't cover (e.g. an external `verify_site_bundle`).
    pub fn with_tool(
        mut self,
        name: impl Into<String>,
        f: impl Fn(&BTreeMap<String, String>) -> ToolOutcome + Send + Sync + 'static,
    ) -> Toolkit {
        self.tools.insert(name.into(), Box::new(f));
        self
    }

    /// The registered tool names (flat + priced) — the services an agent's bundle
    /// should grant to reach them.
    pub fn names(&self) -> Vec<String> {
        self.tools
            .keys()
            .chain(self.priced_tools.keys())
            .cloned()
            .collect()
    }

    /// `true` iff `name` is registered (as a flat or a priced tool).
    pub fn has(&self, name: &str) -> bool {
        self.tools.contains_key(name) || self.priced_tools.contains_key(name)
    }

    // ── check_health / monitor (std-only) ────────────────────────────────────

    /// Wire a **health / monitoring** tool: `probe` returns the current
    /// [`HealthSnapshot`], the tool flags any anomalies (divergence > 0,
    /// conservation breach, errors, liveness lapse) and returns pass (healthy)
    /// or fail (the named anomalies). The safe-autonomous path supplies a local
    /// snapshot; pointing `probe` at the live node `/health` / `dregg-ops`
    /// aggregate is the reviewed-go substitution behind the same seam.
    pub fn with_check_health(
        self,
        name: impl Into<String>,
        probe: impl Fn() -> HealthSnapshot + Send + Sync + 'static,
    ) -> Toolkit {
        self.with_tool(name, move |_cells| {
            let snap = probe();
            let anomalies = snap.anomalies();
            if anomalies.is_empty() {
                ToolOutcome::pass(format!("healthy: {}", snap.note))
            } else {
                ToolOutcome::fail(format!("anomalies flagged: {}", anomalies.join("; ")))
            }
        })
    }

    /// Wire a **receipt-log monitor**: `fetch` yields the recent receipt chain,
    /// the tool re-witnesses it with [`verify_chain`] (signed, unbroken,
    /// tamper-evident). The trustless "is the log intact?" probe. Generic over
    /// any [`ReceiptBody`], so it monitors deploy / publish / agent chains alike.
    pub fn with_verify_receipts<R, F>(self, name: impl Into<String>, fetch: F) -> Toolkit
    where
        R: ReceiptBody,
        F: Fn() -> Vec<R> + Send + Sync + 'static,
    {
        self.with_tool(name, move |_cells| {
            let rs = fetch();
            match verify_chain(&rs) {
                Ok(()) => ToolOutcome::pass(format!(
                    "receipt chain re-witnessed: {} receipt(s) intact",
                    rs.len()
                )),
                Err(e) => ToolOutcome::fail(format!("receipt chain INVALID: {e:?}")),
            }
        })
    }

    // ── verify_deploy (external verifier injected) ───────────────────────────

    /// Wire a **deploy verifier** as an invoke target: `verify` performs the
    /// trustless re-witness (e.g. an external served-bytes verifier —
    /// the served bytes re-hash to the committed root and the receipt chain is
    /// intact) and returns `Ok(detail)` on success or `Err(reason)` on a
    /// mismatch. The toolkit does not re-implement verification; it routes the
    /// existing one through the cap-gated / metered / receipted rail so the QA is
    /// itself a receipted proof. A closure is taken (rather than depending on the
    /// webapp crate) because the crate that owns the verifier sits *above*
    /// `exec` — wiring it here would be a dependency cycle.
    pub fn with_verify_deploy(
        self,
        name: impl Into<String>,
        verify: impl Fn() -> Result<String, String> + Send + Sync + 'static,
    ) -> Toolkit {
        self.with_tool(name, move |_cells| match verify() {
            Ok(detail) => ToolOutcome::pass(format!("deploy verified: {detail}")),
            Err(reason) => ToolOutcome::fail(format!("deploy verify FAILED: {reason}")),
        })
    }

    /// Wire a **witnessed deploy verifier**: like [`with_verify_deploy`], but the
    /// verdict carries a [`WitnessedRun`] binding `(command, code_root, result)`
    /// tied to the deployed `content_root`, so [`crate::agent::verify_witnessed_qa`]
    /// can confirm the verify ran against the code that was actually deployed and
    /// reproduced this result. `verify` returns `Ok(detail)` / `Err(reason)`; the
    /// binding's `code_root` is the deployed `content_root` and its result digest
    /// is over `(ok, detail)`.
    ///
    /// [`with_verify_deploy`]: Toolkit::with_verify_deploy
    pub fn with_witnessed_verify_deploy(
        self,
        name: impl Into<String>,
        deployed_root: impl Into<String>,
        verify: impl Fn() -> Result<String, String> + Send + Sync + 'static,
    ) -> Toolkit {
        let deployed_root = deployed_root.into();
        self.with_tool(name, move |_cells| {
            let (ok, detail) = match verify() {
                Ok(detail) => (true, detail),
                Err(reason) => (false, reason),
            };
            let witnessed = WitnessedRun {
                command: "verify_deploy[served-bytes==content_root]".to_string(),
                code_root: deployed_root.clone(),
                exit: if ok { 0 } else { 1 },
                output_digest: output_digest(&[ok.to_string(), detail.clone()]),
            };
            let oc = if ok {
                ToolOutcome::pass(format!("deploy verified: {detail}"))
            } else {
                ToolOutcome::fail(format!("deploy verify FAILED: {detail}"))
            };
            oc.with_witness(witnessed)
        })
    }
}

// ── run_tests / run_workload (the injected compute runner) ───────────────────

/// What an injected compute run reports back: the workload's returned values and
/// the enforcement grade it ran under. The HOST produces this (a sandbox engine
/// — e.g. the cloud's owned wasmi sandbox tier); this crate binds the witness
/// around it and never depends on the engine itself.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RunReport {
    /// The workload's returned values (the first one decides the `run_tests`
    /// pass/fail by the convention in [`exit_of`]).
    pub values: Vec<String>,
    /// The enforcement grade the run executed under (a free-form label the host
    /// supplies, e.g. `WasmSandbox` / `OsSandbox` / `MicroVm`), bound into the
    /// verdict summary so the receipt records *how* it ran.
    pub enforcement: String,
}

impl RunReport {
    /// Assemble a report from returned values and an enforcement label.
    pub fn new(
        values: impl IntoIterator<Item = impl Into<String>>,
        enforcement: impl Into<String>,
    ) -> RunReport {
        RunReport {
            values: values.into_iter().map(Into::into).collect(),
            enforcement: enforcement.into(),
        }
    }
}

/// A **compute runner**: given `(lang, source)`, execute the workload and report
/// its [`RunReport`], or an `Err(reason)` on an execution error. The host injects
/// it (the cloud wires a real sandbox engine); the open core never owns one — so
/// `dregg-agent` has no compute-engine dependency, only this seam.
pub type RunFn = Box<dyn Fn(&str, &str) -> Result<RunReport, String> + Send + Sync>;

impl Toolkit {
    /// Wire a **run_tests** tool: run the test workload `source` (in `lang`)
    /// through the injected `run` runner, and decide pass/fail by the `run_tests`
    /// convention (a workload that returns `0` / `ok` / `pass` / `true` passed;
    /// anything else, or an execution error, failed). The QA primitive: the agent
    /// runs the suite, gets a *real* result, sealed into its receipt chain with a
    /// [`WitnessedRun`] binding tied to the code's `code_root`.
    pub fn with_run_tests<F>(
        self,
        name: impl Into<String>,
        lang: impl Into<String>,
        source: impl Into<String>,
        run: F,
    ) -> Toolkit
    where
        F: Fn(&str, &str) -> Result<RunReport, String> + Send + Sync + 'static,
    {
        let lang = lang.into();
        let source = source.into();
        self.with_tool(name, move |_cells| run_tests_verdict(&lang, &source, &run))
    }

    /// Wire a **run_workload** tool: run an arbitrary workload through the injected
    /// `run` runner and report its result. Unlike `run_tests` this reports the
    /// returned values without a pass/fail convention — a successful run is `pass`
    /// (the workload completed inside its sandbox + budget), an execution error is
    /// `fail`.
    pub fn with_run_workload<F>(
        self,
        name: impl Into<String>,
        lang: impl Into<String>,
        source: impl Into<String>,
        run: F,
    ) -> Toolkit
    where
        F: Fn(&str, &str) -> Result<RunReport, String> + Send + Sync + 'static,
    {
        let lang = lang.into();
        let source = source.into();
        self.with_tool(name, move |_cells| match run(&lang, &source) {
            Ok(out) => ToolOutcome::pass(format!(
                "workload ran [{}] enforcement={}",
                out.values.join(","),
                out.enforcement
            )),
            Err(e) => ToolOutcome::fail(format!("workload errored: {e}")),
        })
    }
}

/// Run a test workload through the injected `run` runner and turn its result into
/// a verdict by the run_tests convention: a returned `0` / `ok` / `pass` / `true`
/// is a pass (zero failures); anything else is a fail; an execution error is a
/// fail naming the cause.
///
/// On a run that actually executed (Ok), the verdict carries a [`WitnessedRun`]
/// binding `(command, code_root, exit, output_digest)` — the Layer-3 execution
/// witness re-checked by [`crate::agent::verify_witnessed_qa`]. An execution
/// error carries no witness (nothing ran to witness).
fn run_tests_verdict<F>(lang: &str, source: &str, run: &F) -> ToolOutcome
where
    F: Fn(&str, &str) -> Result<RunReport, String>,
{
    match run(lang, source) {
        Ok(out) => {
            let exit = exit_of(&out.values);
            let witnessed = WitnessedRun {
                command: tests_command(lang),
                code_root: code_root(source),
                exit,
                output_digest: output_digest(&out.values),
            };
            let oc = if exit == 0 {
                ToolOutcome::pass(format!(
                    "tests passed [{}] enforcement={}",
                    out.values.join(","),
                    out.enforcement
                ))
            } else {
                ToolOutcome::fail(format!(
                    "tests FAILED [{}] enforcement={}",
                    out.values.join(","),
                    out.enforcement
                ))
            };
            oc.with_witness(witnessed)
        }
        Err(e) => ToolOutcome::fail(format!("test run errored: {e}")),
    }
}

/// The **re-witness oracle** for a `run_tests` binding: re-execute the workload
/// (the declared `source` the binding's `code_root` commits to) through the
/// injected `run` runner and reproduce its `(exit, output_digest)`. Handed to
/// [`crate::agent::verify_witnessed_qa`] as the `rerun` closure: a runtime that
/// recorded a result its execution does not produce is caught when this returns a
/// different [`ReWitness`](crate::agent::ReWitness).
///
/// Returns `None` (un-re-witnessable, rejected fail-closed) when the supplied
/// `source` does not match the binding's `code_root` (the verifier was handed the
/// wrong code) or the workload could not be executed.
pub fn rewitness_run_tests<F>(
    lang: &str,
    source: &str,
    bound: &WitnessedRun,
    run: F,
) -> Option<crate::agent::ReWitness>
where
    F: Fn(&str, &str) -> Result<RunReport, String>,
{
    // The verifier must hold the code the binding commits to — else it cannot
    // reproduce the run (and must not accept it).
    if code_root(source) != bound.code_root {
        return None;
    }
    let out = run(lang, source).ok()?;
    Some(crate::agent::ReWitness {
        exit: exit_of(&out.values),
        output_digest: output_digest(&out.values),
    })
}

impl ToolKit for Toolkit {
    fn invoke(
        &self,
        service: &str,
        amount_cents: Option<i64>,
        cells: &BTreeMap<String, String>,
    ) -> ToolOutcome {
        // A priced spend dispatches to the priced registry (the amount in hand);
        // a flat invoke dispatches to the flat registry.
        if let Some(amount) = amount_cents {
            if let Some(f) = self.priced_tools.get(service) {
                return f(amount, cells);
            }
        }
        match self.tools.get(service) {
            Some(f) => f(cells),
            // The rail already cap-gated the call, so reaching here means the
            // bundle granted `invoke:<service>` but no tool is registered under
            // it — a real (receipted) fail, not a refusal.
            None => ToolOutcome::fail(format!("no tool `{service}` registered on this toolkit")),
        }
    }
}

/// A point-in-time health/o11y reading the [`Toolkit::with_check_health`] tool
/// evaluates. The fields mirror the anomaly signals the `dregg-ops` dashboard
/// alerts on; a probe assembles one from a live read surface (the node
/// `/health` + `/metrics`, the receipt log) or, in the safe-autonomous path,
/// from a local snapshot.
#[derive(Clone, Debug)]
pub struct HealthSnapshot {
    /// `dregg_consensus_differential_divergence_total` — the rust↔lean
    /// finalized-order DISAGREEMENT counter. ANY non-zero value is a real
    /// consensus-bug signal and is flagged.
    pub divergence: u64,
    /// Whether the value-conservation invariant holds (`Σδ = 0`). `false` is a
    /// conservation breach — a flagged anomaly.
    pub conservation_ok: bool,
    /// Errors observed in the recent log/window.
    pub errors: u64,
    /// Whether liveness has lapsed (no recent block / progress).
    pub lapsed: bool,
    /// A human note for the healthy case (what was checked).
    pub note: String,
}

impl Default for HealthSnapshot {
    fn default() -> HealthSnapshot {
        HealthSnapshot {
            divergence: 0,
            conservation_ok: true,
            errors: 0,
            lapsed: false,
            note: String::new(),
        }
    }
}

impl HealthSnapshot {
    /// A healthy snapshot (no anomalies) with a descriptive note.
    pub fn healthy(note: impl Into<String>) -> HealthSnapshot {
        HealthSnapshot {
            note: note.into(),
            ..Default::default()
        }
    }

    /// The anomalies this snapshot exhibits — empty means healthy.
    pub fn anomalies(&self) -> Vec<String> {
        let mut a = Vec::new();
        if self.divergence > 0 {
            a.push(format!(
                "consensus divergence {} (rust↔lean finalized-order disagreement)",
                self.divergence
            ));
        }
        if !self.conservation_ok {
            a.push("conservation breach (Σδ ≠ 0)".to_string());
        }
        if self.errors > 0 {
            a.push(format!("{} error(s) in the recent log", self.errors));
        }
        if self.lapsed {
            a.push("liveness lapse (no recent progress)".to_string());
        }
        a
    }

    /// `true` iff there are no anomalies.
    pub fn is_healthy(&self) -> bool {
        self.anomalies().is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::agent::{
        AgentAction, AgentCloud, AgentSpec, AgentVerifyError, PlannedBrain, ReWitness,
        WitnessVerifyError, WitnessedRun, verify_agent_run, verify_witnessed_qa,
    };
    use crate::receipt::ChainError;

    /// A stand-in suite `source` string for a suite reporting `n` failures
    /// (0 = green). The bytes only matter for the `code_root` commitment; the
    /// injected runner decides the verdict.
    fn wat_returning(n: i32) -> String {
        format!("(module (func (export \"run\") (result i32) (i32.const {n})))")
    }

    /// A mock compute runner: reports `values` ran under `WasmSandbox`. The
    /// injected-engine seam, std-only — proving the budget·cap·receipt·witness
    /// braid needs no real sandbox (the cloud wires an owned sandbox behind this seam).
    fn runner(
        values: &'static [&'static str],
    ) -> impl Fn(&str, &str) -> Result<RunReport, String> + Send + Sync {
        move |_lang, _source| Ok(RunReport::new(values.iter().copied(), "WasmSandbox"))
    }

    /// A spec granting the named services + a `/scratch` cell at cost 1/action.
    fn spec(id: &str, budget: i64, services: &[&str]) -> AgentSpec {
        let mut s = AgentSpec::new(id, budget);
        s.services = services.iter().map(|s| s.to_string()).collect();
        s.cells = vec!["/deploy".to_string()];
        s
    }

    // ── The tools are invoke-able, cap-gated, metered, receipted ─────────────

    #[test]
    fn tools_are_invoke_able_metered_and_receipted() {
        let cloud = AgentCloud::from_seed([20u8; 32]);
        let handle = cloud
            .deploy(&spec("agent:qa", 10, &["run_tests", "check_health"]))
            .unwrap();
        let toolkit = Toolkit::new()
            .with_run_tests("run_tests", "wat", wat_returning(0), runner(&["0"]))
            .with_check_health("check_health", || {
                HealthSnapshot::healthy("node up, 0 divergence")
            });

        let plan = vec![
            AgentAction::Invoke {
                service: "run_tests".into(),
            },
            AgentAction::Invoke {
                service: "check_health".into(),
            },
        ];
        let report = cloud.run_with_toolkit(&handle, &mut PlannedBrain::new(plan), &toolkit);

        assert_eq!(report.admitted, 2, "both granted tools ran");
        assert_eq!(report.consumed, 2, "each drew from the budget");
        assert_eq!(report.receipts.len(), 2, "each call is receipted");
        // The verdicts are bound into the receipts and all passed.
        assert!(
            report.all_tools_passed(),
            "the QA passed: {:?}",
            report.tool_results()
        );
        // The whole QA sequence re-witnesses without trusting the host.
        verify_agent_run(&report).expect("the QA run re-witnesses");
    }

    // ── TOOTH: a tool not in the bundle is REFUSED ───────────────────────────

    #[test]
    fn a_tool_not_in_the_bundle_is_refused() {
        let cloud = AgentCloud::from_seed([21u8; 32]);
        // The bundle grants ONLY check_health — not verify_deploy.
        let handle = cloud
            .deploy(&spec("agent:narrow", 10, &["check_health"]))
            .unwrap();
        let toolkit = Toolkit::new()
            .with_check_health("check_health", || HealthSnapshot::healthy("ok"))
            .with_verify_deploy("verify_deploy", || Ok("would-verify".into()));

        let plan = vec![
            AgentAction::Invoke {
                service: "check_health".into(),
            }, // granted
            AgentAction::Invoke {
                service: "verify_deploy".into(),
            }, // NOT granted
        ];
        let report = cloud.run_with_toolkit(&handle, &mut PlannedBrain::new(plan), &toolkit);

        assert_eq!(report.admitted, 1, "only the granted tool ran");
        assert_eq!(report.cap_refused, 1, "the ungranted tool is refused");
        assert_eq!(report.receipts.len(), 1, "the refused call left no receipt");
        // The refused tool never ran (no verdict for it).
        let results = report.tool_results();
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].0, "invoke:check_health");
    }

    // ── TOOTH: a failing test is a real, receipted result (not a refusal) ────

    #[test]
    fn a_failing_test_is_receipted_as_fail() {
        let cloud = AgentCloud::from_seed([22u8; 32]);
        let handle = cloud
            .deploy(&spec("agent:red", 10, &["run_tests"]))
            .unwrap();
        // The suite reports 3 failures (non-zero) → the tool verdict is FAIL.
        let toolkit =
            Toolkit::new().with_run_tests("run_tests", "wat", wat_returning(3), runner(&["3"]));
        let plan = vec![AgentAction::Invoke {
            service: "run_tests".into(),
        }];
        let report = cloud.run_with_toolkit(&handle, &mut PlannedBrain::new(plan), &toolkit);

        assert_eq!(report.admitted, 1, "the test still ran (and was charged)");
        assert_eq!(report.consumed, 1, "a failing test still draws budget");
        assert_eq!(
            report.receipts.len(),
            1,
            "a fail is a real receipted result"
        );
        let (_, ok, summary) = &report.tool_results()[0];
        assert!(!ok, "the verdict is FAIL: {summary}");
        assert!(summary.contains("FAILED"), "names the failure: {summary}");
        // A fail is still a sound, re-witnessable receipt.
        verify_agent_run(&report).expect("a fail receipt still re-witnesses");
    }

    // ── TOOTH: a forged QA verdict breaks the receipt signature ──────────────

    #[test]
    fn a_forged_qa_verdict_breaks_the_receipt() {
        let cloud = AgentCloud::from_seed([23u8; 32]);
        let handle = cloud
            .deploy(&spec("agent:forge", 10, &["check_health"]))
            .unwrap();
        // A snapshot WITH an anomaly → the honest verdict is FAIL.
        let toolkit = Toolkit::new().with_check_health("check_health", || HealthSnapshot {
            divergence: 1,
            ..Default::default()
        });
        let plan = vec![AgentAction::Invoke {
            service: "check_health".into(),
        }];
        let mut report = cloud.run_with_toolkit(&handle, &mut PlannedBrain::new(plan), &toolkit);

        // Honest: the monitor flagged the anomaly.
        assert!(!report.tool_results()[0].1, "honest verdict is fail");
        verify_agent_run(&report).expect("the honest fail re-witnesses");

        // Forge the verdict to "passed" after sealing → the signature no longer
        // matches (the verdict is bound into the receipt body).
        report.receipts[0].tool_ok = Some(true);
        assert!(matches!(
            verify_agent_run(&report),
            Err(AgentVerifyError::Chain(ChainError::BadSignature { .. }))
        ));
    }

    // ── TOOTH: over-budget bounds the QA sequence ────────────────────────────

    #[test]
    fn over_budget_bounds_the_qa() {
        let cloud = AgentCloud::from_seed([24u8; 32]);
        // Budget 2: only two QA calls fit; the rest are bounded.
        let handle = cloud
            .deploy(&spec("agent:bound", 2, &["check_health"]))
            .unwrap();
        let toolkit =
            Toolkit::new().with_check_health("check_health", || HealthSnapshot::healthy("ok"));
        let plan: Vec<AgentAction> = (0..10)
            .map(|_| AgentAction::Invoke {
                service: "check_health".into(),
            })
            .collect();
        let report = cloud.run_with_toolkit(&handle, &mut PlannedBrain::new(plan), &toolkit);

        assert_eq!(report.admitted, 2, "the budget admits exactly two QA calls");
        assert_eq!(report.budget_refused, 8, "the rest are bounded");
        assert_eq!(report.headroom, 0, "the ceiling is fully drawn");
        verify_agent_run(&report).unwrap();
    }

    // ── verify_receipts re-witnesses a chain, and catches a broken one ───────

    #[test]
    fn verify_receipts_tool_re_witnesses_a_chain() {
        // A genuine agent run produces a sound receipt chain; the monitor tool
        // re-witnesses it. A spliced chain is caught.
        let cloud = AgentCloud::from_seed([25u8; 32]);
        let handle = cloud
            .deploy(&spec("agent:src", 10, &["check_health"]))
            .unwrap();
        let tk0 =
            Toolkit::new().with_check_health("check_health", || HealthSnapshot::healthy("ok"));
        let plan: Vec<AgentAction> = (0..4)
            .map(|_| AgentAction::Invoke {
                service: "check_health".into(),
            })
            .collect();
        let source = cloud.run_with_toolkit(&handle, &mut PlannedBrain::new(plan), &tk0);

        // GOOD: a tool fetching the intact chain passes.
        let good = source.receipts.clone();
        let good_tk = Toolkit::new().with_verify_receipts("monitor", move || good.clone());
        let oc = good_tk.invoke("monitor", None, &BTreeMap::new());
        assert!(oc.ok, "intact chain re-witnesses: {}", oc.summary);

        // BAD: a tool fetching a spliced chain fails.
        let mut bad = source.receipts.clone();
        bad.remove(1);
        let bad_tk = Toolkit::new().with_verify_receipts("monitor", move || bad.clone());
        let oc = bad_tk.invoke("monitor", None, &BTreeMap::new());
        assert!(!oc.ok, "a spliced chain is caught");
        assert!(
            oc.summary.contains("INVALID"),
            "names the break: {}",
            oc.summary
        );
    }

    // ── THE LOOP: deploy → test → verify → monitor, all receipted ────────────

    #[test]
    fn the_self_verifying_qa_ops_loop() {
        let cloud = AgentCloud::from_seed([26u8; 32]);
        // The agent's bundle grants the QA/ops tools + its own /deploy cell.
        let handle = cloud
            .deploy(&spec(
                "agent:devops",
                20,
                &["run_tests", "verify_deploy", "check_health"],
            ))
            .unwrap();

        // The toolkit: run_tests over a green suite, a deploy verifier (the
        // injection seam where the real verify_site_bundle would be wired), and
        // a health probe.
        let toolkit = Toolkit::new()
            .with_run_tests("run_tests", "wat", wat_returning(0), runner(&["0"]))
            .with_verify_deploy("verify_deploy", || {
                Ok("served bytes match the committed root; receipt chain intact".into())
            })
            .with_check_health("check_health", || {
                HealthSnapshot::healthy("node up · 0 divergence · Σδ=0")
            });

        // deploy → test → verify → monitor.
        let plan = vec![
            AgentAction::CellWrite {
                path: "/deploy".into(),
                value: "site:blog@commit-abc".into(),
            },
            AgentAction::Invoke {
                service: "run_tests".into(),
            },
            AgentAction::Invoke {
                service: "verify_deploy".into(),
            },
            AgentAction::Invoke {
                service: "check_health".into(),
            },
        ];
        let report = cloud.run_with_toolkit(&handle, &mut PlannedBrain::new(plan), &toolkit);

        // The whole QA/ops sequence ran, was metered, and is receipted.
        assert_eq!(report.admitted, 4, "deploy + 3 QA/ops calls");
        assert_eq!(report.consumed, 4);
        assert_eq!(
            report.receipts.len(),
            4,
            "the whole sequence is in the chain"
        );
        assert_eq!(
            report.cells.get("/deploy"),
            Some(&"site:blog@commit-abc".to_string())
        );

        // Every QA/ops verdict passed.
        let results = report.tool_results();
        assert_eq!(results.len(), 3, "run_tests + verify_deploy + check_health");
        assert!(report.all_tools_passed(), "QA/ops all green: {results:?}");
        assert!(results.iter().any(|(a, ..)| a == "invoke:run_tests"));
        assert!(results.iter().any(|(a, ..)| a == "invoke:verify_deploy"));
        assert!(results.iter().any(|(a, ..)| a == "invoke:check_health"));

        // The whole self-verifying loop re-witnesses without trusting the host.
        let v = verify_agent_run(&report).expect("the self-QA loop re-witnesses");
        assert_eq!(v.actions, 4);
    }

    // ═════ LAYER 3 — EXECUTION-WITNESSING ════════════════════════════════════
    // The verdict is bound to a WITNESSED tier execution, not the runtime's word:
    // run_tests binds (command, code_root, result), `verify` re-executes the bound
    // (command, code_root) and the code_root must equal the deployed root.

    /// run_tests binds a witnessed `(command, code_root, result)` that ties to the
    /// deployed root and re-witnesses against a re-execution of the same code.
    #[test]
    fn run_tests_binds_a_witnessed_execution_tied_to_the_deploy() {
        let cloud = AgentCloud::from_seed([30u8; 32]);
        let handle = cloud
            .deploy(&spec("agent:wit", 10, &["run_tests"]))
            .unwrap();
        // The deployed code's content commitment (in the real flow this is the
        // deploy receipt's content_root; here it is the code the tests run on).
        let src = wat_returning(0);
        let deployed_root = code_root(&src);

        let toolkit = Toolkit::new().with_run_tests("run_tests", "wat", &src, runner(&["0"]));
        let plan = vec![
            AgentAction::CellWrite {
                path: "/deploy".into(),
                value: deployed_root.clone(),
            },
            AgentAction::Invoke {
                service: "run_tests".into(),
            },
        ];
        let report = cloud.run_with_toolkit(&handle, &mut PlannedBrain::new(plan), &toolkit);
        verify_agent_run(&report).expect("the chain + bound re-witness");

        // The run_tests receipt carries a witnessed binding tied to the deploy.
        let w = report
            .receipts
            .iter()
            .find_map(|r| r.witnessed.clone())
            .expect("run_tests bound a witnessed execution");
        assert_eq!(
            w.code_root, deployed_root,
            "the tests ran on the deployed code"
        );
        assert_eq!(w.exit, 0, "green suite → exit 0");

        // LAYER 3: re-witness the execution — re-run the bound (command, code_root)
        // and confirm it reproduces the recorded result, on the deployed code.
        let v = verify_witnessed_qa(&report, &deployed_root, |w| {
            rewitness_run_tests("wat", &src, w, runner(&["0"]))
        })
        .expect("the witnessed execution re-witnesses");
        assert_eq!(v.witnessed, 1, "one witnessed run");
        assert_eq!(v.passed, 1, "and it really passed on re-execution");
    }

    /// TOOTH: if the tests ran against code that is NOT what was deployed, the
    /// code_root tie catches it (the QA did not run on the deployed code).
    #[test]
    fn verify_catches_tests_run_on_code_that_was_not_deployed() {
        let cloud = AgentCloud::from_seed([31u8; 32]);
        let handle = cloud
            .deploy(&spec("agent:wrongcode", 10, &["run_tests"]))
            .unwrap();
        // The tests ran on `tested_src`, but a DIFFERENT artifact was deployed.
        let tested_src = wat_returning(0);
        let deployed_src = wat_returning(7);
        let deployed_root = code_root(&deployed_src);

        let toolkit =
            Toolkit::new().with_run_tests("run_tests", "wat", &tested_src, runner(&["0"]));
        let plan = vec![AgentAction::Invoke {
            service: "run_tests".into(),
        }];
        let report = cloud.run_with_toolkit(&handle, &mut PlannedBrain::new(plan), &toolkit);
        verify_agent_run(&report).expect("the chain still re-witnesses");

        // The witnessed code_root is the tested code, not the deployed code → ✗.
        let err = verify_witnessed_qa(&report, &deployed_root, |w| {
            rewitness_run_tests("wat", &tested_src, w, runner(&["0"]))
        })
        .expect_err("tests on non-deployed code must be caught");
        assert!(
            matches!(err, WitnessVerifyError::CodeRootMismatch { .. }),
            "{err}"
        );
    }

    /// TOOTH (std): a LYING RUNTIME — one that records a passing verdict its
    /// execution does not actually produce — is caught on re-witness, because the
    /// re-execution reproduces a DIFFERENT result than the recorded binding.
    #[test]
    fn verify_catches_a_runtime_that_recorded_a_result_its_execution_does_not_produce() {
        let cloud = AgentCloud::from_seed([32u8; 32]);
        let handle = cloud
            .deploy(&spec("agent:liar", 10, &["run_tests"]))
            .unwrap();
        let deployed_root = code_root("the-deployed-code");

        // The runtime SEALS a green witnessed binding (exit 0) — a valid signature
        // over a claim. (A real lying runtime fabricates this without running.)
        let claimed = WitnessedRun {
            command: "run_tests[lang=wat,tier=Sandboxed,entry=run]".into(),
            code_root: deployed_root.clone(),
            exit: 0,
            output_digest: [0u8; 32],
        };
        let toolkit = Toolkit::new().with_tool("run_tests", move |_| {
            ToolOutcome::pass("tests passed [0]").with_witness(claimed.clone())
        });
        let plan = vec![AgentAction::Invoke {
            service: "run_tests".into(),
        }];
        let report = cloud.run_with_toolkit(&handle, &mut PlannedBrain::new(plan), &toolkit);
        // The chain itself re-witnesses (the runtime signed a consistent chain)…
        verify_agent_run(&report).expect("the chain is internally consistent");

        // …but re-executing the bound code reproduces a DIFFERENT result (exit 3),
        // so the recorded verdict does not match the witnessed execution → ✗.
        let err = verify_witnessed_qa(&report, &deployed_root, |_w| {
            Some(ReWitness {
                exit: 3,
                output_digest: [9u8; 32],
            })
        })
        .expect_err("a fabricated verdict must be caught");
        assert!(
            matches!(err, WitnessVerifyError::ExecutionMismatch { .. }),
            "{err}"
        );
    }

    /// TOOTH (std): an un-re-executable witnessed binding is rejected fail-closed
    /// (the verifier could not reproduce the run → not accepted).
    #[test]
    fn an_un_re_witnessable_binding_is_rejected_fail_closed() {
        let cloud = AgentCloud::from_seed([33u8; 32]);
        let handle = cloud
            .deploy(&spec("agent:opaque", 10, &["run_tests"]))
            .unwrap();
        let deployed_root = code_root("deployed");
        let w = WitnessedRun {
            command: "run_tests[opaque]".into(),
            code_root: deployed_root.clone(),
            exit: 0,
            output_digest: [1u8; 32],
        };
        let toolkit = Toolkit::new().with_tool("run_tests", move |_| {
            ToolOutcome::pass("green").with_witness(w.clone())
        });
        let plan = vec![AgentAction::Invoke {
            service: "run_tests".into(),
        }];
        let report = cloud.run_with_toolkit(&handle, &mut PlannedBrain::new(plan), &toolkit);
        let err = verify_witnessed_qa(&report, &deployed_root, |_w| None)
            .expect_err("an un-reproducible binding is not accepted");
        assert!(
            matches!(err, WitnessVerifyError::NotReWitnessable { .. }),
            "{err}"
        );
    }

    /// TOOTH (std): the witnessed binding is SIGNED — tampering it post-seal breaks
    /// the receipt signature (so the bound the re-witness re-checks cannot be
    /// edited after the fact).
    #[test]
    fn a_forged_witnessed_binding_breaks_the_receipt() {
        let cloud = AgentCloud::from_seed([34u8; 32]);
        let handle = cloud
            .deploy(&spec("agent:tamper", 10, &["run_tests"]))
            .unwrap();
        let w = WitnessedRun {
            command: "run_tests[x]".into(),
            code_root: code_root("c"),
            exit: 3,
            output_digest: [2u8; 32],
        };
        let toolkit = Toolkit::new().with_tool("run_tests", move |_| {
            ToolOutcome::fail("red [3]").with_witness(w.clone())
        });
        let plan = vec![AgentAction::Invoke {
            service: "run_tests".into(),
        }];
        let mut report = cloud.run_with_toolkit(&handle, &mut PlannedBrain::new(plan), &toolkit);
        verify_agent_run(&report).expect("the honest fail re-witnesses");

        // Forge the witnessed exit to green AFTER sealing → the signature breaks.
        if let Some(w) = report.receipts[0].witnessed.as_mut() {
            w.exit = 0;
        }
        assert!(matches!(
            verify_agent_run(&report),
            Err(AgentVerifyError::Chain(ChainError::BadSignature { .. }))
        ));
    }
}
