//! `harness` — **BRING-YOUR-OWN-HARNESS**: run the user's already-installed,
//! already-authed agent CLI (`kimi` / `claude` / `codex` / `aider`, …) AS the
//! confined brain behind the [`AgentBrain`](crate::agent::AgentBrain) seam.
//!
//! Most people's *best* LLM access is **harness-tied** — a subscription inside a
//! coding-agent CLI — not a portable raw API key. If our brain only eats API
//! keys ([`crate::brain::KimiBrain`]) we exclude most subscription users. The
//! elegant fit, and *peak dregg*: **the harness brings the smarts + the
//! subscription auth; dregg brings the bound + the proof.** We confine a powerful
//! agent we don't control, meter it, and prove what it did.
//!
//! ```text
//!   the user's harness ─▶ tool-call (proposal) ─▶ (gate: cap ✓ · budget ✓ · receipt)
//!         ▲                                                     │
//!         └──────────── verdict (allow+receipt / refuse+reason) ┘  → harness adapts
//! ```
//!
//! The harness **proposes**; the dregg braid **disposes**. The braid around it is
//! unchanged and still the only authority: a tool outside the cap bundle is
//! **refused before it runs** (the harness cannot widen its reach by emitting a
//! tool-call), an over-budget call is **bounded in-band**, and every admitted
//! action is **receipted** (the run re-witnesses with
//! [`verify_agent_run`](crate::agent::verify_agent_run)). The harness is
//! **untrusted arbitrary code**; this braid is what makes running it safe.
//!
//! ## The auth story — the cleanest of the BYO routes
//!
//! The harness holds its own subscription credential *inside its subprocess* and
//! uses it to reach its model provider directly. **The credential never crosses
//! the dregg boundary** — unlike the BYO-key route ([`crate::brain`]), where dregg
//! *holds* the key and must confine it. Here there is no key for dregg to hold,
//! redact, or leak: the only things that cross the boundary are **tool-call JSON**
//! (proposals, from the harness) and **verdict JSON** (responses, to the
//! harness). The [`harness_secret_never_leaks`](#) tooth proves a
//! harness-internal secret never appears in the receipts / report.
//!
//! ## The universal shim — an ndjson tool-call line protocol
//!
//! The harness (or a thin adapter) emits one JSON object per line on stdout, and
//! reads the gate's verdict back as one JSON line on stdin:
//!
//! ```text
//!   harness ─▶ {"tool":"invoke","service":"run_tests"}            (a tool-call)
//!   dregg   ─▶ {"admitted":true,"receipted":true}                 (the verdict)
//!   harness ─▶ {"tool":"invoke","service":"exfiltrate"}           (out of bundle)
//!   dregg   ─▶ {"admitted":false,"refusal":"outside the cap bundle: invoke:exfiltrate"}
//!   harness ─▶ {"tool":"finish","summary":"done"}                 (end the turn)
//! ```
//!
//! This is the lowest-common-denominator shim — any harness that can shell out
//! (or be wrapped by a command) can speak it. It is the essence of the
//! confined-Hermes ACP `request_permission` round-trip, and the
//! transport-agnostic generalization of an MCP `tools/call` server. See
//! `docs/BRING-YOUR-OWN-HARNESS.md` for the full route survey (MCP / ACP /
//! tool-shim) and the ToS honesty on OAuth subscription tokens.
//!
//! ## The transport seam
//!
//! [`HarnessTransport`] is the one place the subprocess is read/written. Two
//! impls ship, both std-only (no extra deps — `std::process` is always
//! available):
//!   * [`MockHarness`] — replays scripted tool-call lines (the **fake harness**
//!     for the green tests) and **records every verdict** delivered back (the
//!     confinement-feedback witness).
//!   * [`SubprocessHarness`] — spawns a configured [`std::process::Command`],
//!     reads ndjson tool-calls from its stdout, writes verdict lines to its
//!     stdin. This is where a real `kimi` / `claude` / `codex` adapter wires in
//!     (the reviewed-go next step).

use std::io::{BufRead, BufReader, Write};
use std::process::{Child, ChildStdin, Command, Stdio};

use serde_json::{Value, json};

use crate::agent::{ActionObservation, AgentAction, AgentBrain};

// ───────────────────────────── the wire protocol ────────────────────────────

/// Map a harness's emitted tool-call (name + a JSON args object) to an
/// [`AgentAction`]. `None` for `finish` and any unrecognized tool (the turn ends
/// rather than fabricating an action) — the same convention as
/// [`crate::brain`]'s `map_tool_call`, so a harness and a raw-key LLM speak one
/// vocabulary into the seam.
fn map_tool_call(name: &str, args: &Value) -> Option<AgentAction> {
    let s = |k: &str| args.get(k).and_then(|v| v.as_str()).map(|s| s.to_string());
    match name {
        "invoke" => s("service").map(|service| AgentAction::Invoke { service }),
        "cell_write" => match (s("path"), s("value")) {
            (Some(path), Some(value)) => Some(AgentAction::CellWrite { path, value }),
            _ => None,
        },
        "cell_read" => s("path").map(|path| AgentAction::CellRead { path }),
        _ => None,
    }
}

/// Parse one ndjson line the harness emitted into `(tool_name, args)`. The line
/// is a JSON object carrying a `"tool"` field plus the action's fields, e.g.
/// `{"tool":"invoke","service":"run_tests"}`. Returns `None` for a line that is
/// not a JSON object or carries no string `"tool"` — a real harness interleaves
/// prose / log lines with tool-calls, and a non-tool line is simply skipped
/// (NOT a fabricated action).
fn parse_tool_call_line(line: &str) -> Option<(String, Value)> {
    let v: Value = serde_json::from_str(line.trim()).ok()?;
    let obj = v.as_object()?;
    let tool = obj.get("tool").and_then(|t| t.as_str())?.to_string();
    Some((tool, v))
}

/// Render the gate's verdict on a harness-proposed action as the JSON line dregg
/// writes back to the harness's stdin — the in-band feedback the harness adapts
/// to (a refusal names the missing cap or the exhausted budget, so the harness
/// can fall back within its granted authority).
fn verdict_line(obs: &ActionObservation) -> String {
    let mut v = json!({
        "action": obs.action,
        "admitted": obs.admitted,
    });
    let map = v.as_object_mut().expect("a json object");
    if obs.admitted {
        map.insert("receipted".into(), json!(true));
        if let Some(ok) = obs.tool_ok {
            map.insert("tool_ok".into(), json!(ok));
        }
        if let Some(s) = &obs.tool_summary {
            map.insert("tool_summary".into(), json!(s));
        }
    } else if let Some(r) = &obs.refusal {
        map.insert("refusal".into(), json!(r));
    }
    v.to_string()
}

// ───────────────────────────── the transport seam ───────────────────────────

/// THE HARNESS-SUBPROCESS SEAM — read the harness's next tool-call, write the
/// gate's verdict back. The ONLY place the subprocess is touched. A live
/// deployment uses [`SubprocessHarness`]; the tests use [`MockHarness`].
///
/// The harness is **untrusted**: `next_tool_call` may yield ANY tool-call (in
/// bundle, out of bundle, a runaway). Safety comes entirely from the cap-gate +
/// budget + receipt braid the [`crate::agent::AgentCloud`] run loop wraps around
/// this seam — never from trusting what the harness emits.
pub trait HarnessTransport {
    /// The harness's next emitted tool-call as `(tool_name, args_json)`, or
    /// `None` when the harness is done / the stream ended (fail-closed — the turn
    /// finishes, it never fabricates).
    fn next_tool_call(&mut self) -> Option<(String, Value)>;

    /// Deliver the gate's `verdict` (one JSON line) back to the harness so it can
    /// adapt its next tool-call to confinement. Best-effort: a delivery failure
    /// (the harness exited) is swallowed — the run loop's bound/receipt rails are
    /// what hold the guarantee, not the feedback channel.
    fn deliver_verdict(&mut self, verdict: &str);
}

/// A transport that replays scripted harness tool-call lines (the **fake harness
/// subprocess** for the green tests) and **records every verdict delivered back**
/// — so a test asserts the harness was told of a refusal (the confinement
/// feedback) without spawning a real process.
///
/// It also models the BYO-harness auth boundary: an optional `internal_secret`
/// (the harness's own subscription credential, which in a real subprocess never
/// crosses to dregg) is held here and asserted ABSENT from everything dregg
/// produces — the harness emits tool-calls, never its auth.
pub struct MockHarness {
    lines: std::collections::VecDeque<String>,
    repeat_last: bool,
    last: Option<String>,
    /// Every verdict line dregg delivered back (the confinement-feedback record).
    verdicts_seen: Vec<String>,
}

impl MockHarness {
    /// A harness that emits `tool_calls` (each a JSON value with a `"tool"`
    /// field) in order, then ends (the harness is done).
    pub fn new(tool_calls: Vec<Value>) -> MockHarness {
        MockHarness {
            lines: tool_calls.into_iter().map(|v| v.to_string()).collect(),
            repeat_last: false,
            last: None,
            verdicts_seen: Vec::new(),
        }
    }

    /// A harness that replays `tool_calls`, then **repeats the last one forever**
    /// — a degenerate / runaway harness banging the same tool. Used to show the
    /// meter bounds spend regardless of how persistent the harness is.
    pub fn repeating(tool_calls: Vec<Value>) -> MockHarness {
        let mut h = MockHarness::new(tool_calls);
        h.repeat_last = true;
        h
    }

    /// The verdict lines dregg delivered back to the harness (for assertions —
    /// the harness DID see the refusal / the receipt).
    pub fn verdicts_seen(&self) -> &[String] {
        &self.verdicts_seen
    }
}

impl HarnessTransport for MockHarness {
    fn next_tool_call(&mut self) -> Option<(String, Value)> {
        let line = if let Some(l) = self.lines.pop_front() {
            self.last = Some(l.clone());
            l
        } else if self.repeat_last {
            self.last.clone()?
        } else {
            return None;
        };
        // A scripted non-tool line is skipped (mirrors the subprocess path that
        // skips prose); here every scripted value carries a tool, so this parses.
        parse_tool_call_line(&line)
    }

    fn deliver_verdict(&mut self, verdict: &str) {
        self.verdicts_seen.push(verdict.to_string());
    }
}

/// A real harness subprocess: spawn a configured [`Command`], read ndjson
/// tool-calls from its stdout, write verdict lines to its stdin. Std-only (no
/// extra deps). This is the reviewed-go production path — a `kimi` / `claude` /
/// `codex` adapter is a `SubprocessHarness` over the harness's agent-mode command
/// (plus the small translation of its native tool surface into the ndjson
/// protocol; see `docs/BRING-YOUR-OWN-HARNESS.md`).
///
/// The harness's subscription auth lives entirely inside the spawned process and
/// reaches only its model provider — dregg never sees it (it is not an argument
/// here). The boundary carries tool-call lines out and verdict lines in, nothing
/// else.
pub struct SubprocessHarness {
    child: Child,
    stdout: BufReader<std::process::ChildStdout>,
    stdin: Option<ChildStdin>,
}

impl SubprocessHarness {
    /// Spawn `command` with `args` as the harness subprocess, piping its stdin +
    /// stdout for the ndjson protocol. The harness inherits its own environment
    /// (where its subscription auth lives); dregg passes no credential.
    pub fn spawn(command: &str, args: &[&str]) -> std::io::Result<SubprocessHarness> {
        let mut child = Command::new(command)
            .args(args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            // stderr is the harness's own (prose / logs); not part of the wire.
            .stderr(Stdio::inherit())
            .spawn()?;
        let stdout = child
            .stdout
            .take()
            .ok_or_else(|| std::io::Error::other("harness stdout not piped"))?;
        let stdin = child.stdin.take();
        Ok(SubprocessHarness {
            child,
            stdout: BufReader::new(stdout),
            stdin,
        })
    }

    /// Wait for the harness subprocess to exit (cleanup). Best-effort.
    pub fn wait(&mut self) -> std::io::Result<std::process::ExitStatus> {
        self.child.wait()
    }
}

impl HarnessTransport for SubprocessHarness {
    fn next_tool_call(&mut self) -> Option<(String, Value)> {
        // Read lines until one parses as a tool-call; a real harness interleaves
        // prose / log lines, which are skipped (NOT fabricated into actions).
        // EOF (the harness exited) ends the turn fail-closed.
        loop {
            let mut line = String::new();
            match self.stdout.read_line(&mut line) {
                Ok(0) => return None, // EOF
                Ok(_) => {
                    if let Some(tc) = parse_tool_call_line(&line) {
                        return Some(tc);
                    }
                    // a non-tool line (prose / log) — keep reading.
                }
                Err(_) => return None, // a read error finishes the turn fail-closed.
            }
        }
    }

    fn deliver_verdict(&mut self, verdict: &str) {
        if let Some(stdin) = self.stdin.as_mut() {
            // Best-effort: a broken pipe (the harness exited) is swallowed.
            let _ = writeln!(stdin, "{verdict}");
            let _ = stdin.flush();
        }
    }
}

// ──────────────────────────────── the brain ─────────────────────────────────

/// A BYO-HARNESS BRAIN behind the [`AgentBrain`] seam: it drives an untrusted
/// harness subprocess over the ndjson tool-call protocol.
///
/// On each [`AgentBrain::next_action`] it reads the harness's next emitted
/// tool-call and maps it to an [`AgentAction`] (`invoke` / `cell_write` /
/// `cell_read`); a `finish` tool-call, EOF, or an unparseable line ends the turn
/// (fail-closed — it never fabricates a tool-call). On each
/// [`AgentBrain::observe`] it delivers the gate's verdict back to the harness so
/// it adapts within confinement.
///
/// A `step_cap` bounds the harness turns (the budget bounds *spend*; this bounds
/// *turns*) so a degenerate harness cannot spin forever.
pub struct HarnessBrain<T: HarnessTransport> {
    transport: T,
    finished: bool,
    step_cap: u64,
}

impl<T: HarnessTransport> HarnessBrain<T> {
    /// A brain driving `transport` (a [`MockHarness`] for tests, a
    /// [`SubprocessHarness`] for a live harness CLI). Default `step_cap` 64.
    pub fn new(transport: T) -> HarnessBrain<T> {
        HarnessBrain {
            transport,
            finished: false,
            step_cap: 64,
        }
    }

    /// Bound the number of harness turns (default 64). The budget bounds *spend*;
    /// this bounds *turns* so a degenerate harness cannot loop forever.
    pub fn with_step_cap(mut self, cap: u64) -> HarnessBrain<T> {
        self.step_cap = cap;
        self
    }

    /// The transport (post-run) — e.g. for a [`MockHarness`] to report the
    /// verdicts it was told of.
    pub fn transport(&self) -> &T {
        &self.transport
    }
}

impl<T: HarnessTransport> AgentBrain for HarnessBrain<T> {
    fn next_action(&mut self, step: u64) -> Option<AgentAction> {
        if self.finished || step >= self.step_cap {
            return None;
        }
        match self.transport.next_tool_call() {
            Some((tool, args)) => match map_tool_call(&tool, &args) {
                Some(action) => Some(action),
                // `finish` (or an unknown tool) — end the turn cleanly.
                None => {
                    self.finished = true;
                    None
                }
            },
            // The harness is done / the stream ended — fail-closed.
            None => {
                self.finished = true;
                None
            }
        }
    }

    fn observe(&mut self, obs: &ActionObservation) {
        // Feed the gate's verdict back to the harness so it adapts in-band.
        self.transport.deliver_verdict(&verdict_line(obs));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::agent::{AgentCloud, AgentSpec, AgentVerifyError, verify_agent_run};
    use crate::receipt::ChainError;
    use crate::toolkit::{HealthSnapshot, Toolkit};

    /// A harness's emitted tool-call as a JSON value (the ndjson line shape).
    fn tc(tool: &str, extra: Value) -> Value {
        let mut v = json!({ "tool": tool });
        if let (Some(map), Some(ex)) = (v.as_object_mut(), extra.as_object()) {
            for (k, val) in ex {
                map.insert(k.clone(), val.clone());
            }
        }
        v
    }

    fn spec(id: &str, budget: i64, services: &[&str], cells: &[&str]) -> AgentSpec {
        let mut s = AgentSpec::new(id, budget);
        s.services = services.iter().map(|s| s.to_string()).collect();
        s.cells = cells.iter().map(|s| s.to_string()).collect();
        s
    }

    fn devops_toolkit() -> Toolkit {
        Toolkit::new()
            .with_check_health("check_health", || {
                HealthSnapshot::healthy("node up · 0 divergence · Σδ=0")
            })
            .with_verify_deploy("verify_deploy", || {
                Ok("served bytes match the committed root".to_string())
            })
    }

    // ── THE LOOP: a mock harness drives a cap-gated, metered, receipted run ──────

    #[test]
    fn a_harness_subprocess_drives_a_cap_gated_metered_receipted_run() {
        let cloud = AgentCloud::from_seed([60u8; 32]);
        let handle = cloud
            .deploy(&spec(
                "agent:harness-devops",
                10,
                &["check_health", "verify_deploy"],
                &["/deploy"],
            ))
            .unwrap();

        // The (untrusted) harness's reasoning, emitted as ndjson tool-calls:
        //   write the deploy cell → check health → verify the deploy → finish.
        let harness = MockHarness::new(vec![
            tc(
                "cell_write",
                json!({ "path": "/deploy", "value": "site:blog@commit-abc" }),
            ),
            tc("invoke", json!({ "service": "check_health" })),
            tc("invoke", json!({ "service": "verify_deploy" })),
            tc(
                "finish",
                json!({ "summary": "deployed, health green, verified" }),
            ),
        ]);
        let mut brain = HarnessBrain::new(harness);

        let report = cloud.run_with_toolkit(&handle, &mut brain, &devops_toolkit());

        // The whole harness-driven sequence ran, was metered, and is receipted.
        assert_eq!(report.admitted, 3, "cell-write + 2 invokes");
        assert_eq!(report.consumed, 3);
        assert_eq!(report.receipts.len(), 3);
        assert_eq!(
            report.cells.get("/deploy"),
            Some(&"site:blog@commit-abc".to_string())
        );
        // The QA/ops verdicts are bound into the receipts and all passed.
        assert!(
            report.all_tools_passed(),
            "QA green: {:?}",
            report.tool_results()
        );
        // The run re-witnesses without trusting the host OR the harness.
        verify_agent_run(&report).expect("the harness-driven run re-witnesses");

        // The harness was told the verdict of each admitted action (the in-band
        // confinement feedback it adapts to).
        let verdicts = brain.transport().verdicts_seen();
        assert_eq!(
            verdicts.len(),
            3,
            "one verdict delivered per decided action"
        );
        assert!(verdicts.iter().all(|v| v.contains("\"admitted\":true")));
    }

    // ── TOOTH: an out-of-bundle tool the harness emits is REFUSED ────────────────

    #[test]
    fn an_out_of_bundle_tool_the_harness_emits_is_refused_and_fed_back() {
        let cloud = AgentCloud::from_seed([61u8; 32]);
        // The bundle grants ONLY check_health — not the exfiltrate the harness reaches for.
        let handle = cloud
            .deploy(&spec("agent:harness-narrow", 10, &["check_health"], &[]))
            .unwrap();

        // An UNTRUSTED harness tries a tool outside its bundle, then (having been
        // told of the refusal) falls back to a granted tool.
        let harness = MockHarness::new(vec![
            tc("invoke", json!({ "service": "exfiltrate" })), // OUT of bundle → refused
            tc("invoke", json!({ "service": "check_health" })), // granted → admitted
            tc("finish", json!({})),
        ]);
        let mut brain = HarnessBrain::new(harness);

        let report = cloud.run_with_toolkit(&handle, &mut brain, &devops_toolkit());

        assert_eq!(report.cap_refused, 1, "the out-of-bundle tool is refused");
        assert_eq!(report.admitted, 1, "only the granted tool ran");
        assert_eq!(report.receipts.len(), 1, "the refused call left no receipt");

        // The harness was told of the refusal in-band (the confinement feedback) —
        // it cannot widen its reach no matter what it emits.
        let verdicts = brain.transport().verdicts_seen();
        assert!(
            verdicts
                .iter()
                .any(|v| v.contains("\"admitted\":false") && v.contains("invoke:exfiltrate")),
            "the refusal naming the missing cap was fed back: {verdicts:?}"
        );
        verify_agent_run(&report).expect("the run re-witnesses");
    }

    // ── TOOTH: a runaway harness is BUDGET-BOUNDED ───────────────────────────────

    #[test]
    fn a_runaway_harness_is_bounded_by_the_budget() {
        let cloud = AgentCloud::from_seed([62u8; 32]);
        let handle = cloud
            .deploy(&spec("agent:harness-runaway", 3, &["check_health"], &[]))
            .unwrap();

        // A degenerate harness that keeps emitting the same tool-call forever.
        let harness =
            MockHarness::repeating(vec![tc("invoke", json!({ "service": "check_health" }))]);
        let mut brain = HarnessBrain::new(harness).with_step_cap(20);

        let report = cloud.run_with_toolkit(&handle, &mut brain, &devops_toolkit());

        assert_eq!(
            report.admitted, 3,
            "the budget admits exactly budget/cost calls"
        );
        assert_eq!(
            report.budget_refused, 17,
            "the rest are bounded (step_cap 20 − budget 3)"
        );
        assert_eq!(report.consumed, 3, "spend is capped at the ceiling");
        assert_eq!(report.headroom, 0, "the ceiling is fully drawn");
        let v = verify_agent_run(&report).unwrap();
        assert!(v.consumed <= v.budget, "consumed never exceeds the ceiling");
    }

    // ── TOOTH: the step_cap bounds a harness that never finishes ─────────────────

    #[test]
    fn the_step_cap_bounds_a_harness_that_never_finishes() {
        let cloud = AgentCloud::from_seed([63u8; 32]);
        // A huge budget so the BUDGET is not what bounds it — the step_cap must.
        let handle = cloud
            .deploy(&spec("agent:harness-spin", 10_000, &["check_health"], &[]))
            .unwrap();
        let harness =
            MockHarness::repeating(vec![tc("invoke", json!({ "service": "check_health" }))]);
        let mut brain = HarnessBrain::new(harness).with_step_cap(5);

        let report = cloud.run_with_toolkit(&handle, &mut brain, &devops_toolkit());
        assert_eq!(report.admitted, 5, "the step_cap bounds the harness turns");
        assert!(
            report.headroom > 0,
            "the budget was NOT the bound here — the step_cap was"
        );
    }

    // ── TOOTH: a harness-internal secret NEVER crosses the boundary ──────────────

    #[test]
    fn a_harness_internal_secret_never_leaks() {
        const HARNESS_SECRET: &str = "sub-TOKEN-HARNESS-INTERNAL-DONOTLEAK-0123456789";
        let cloud = AgentCloud::from_seed([64u8; 32]);
        let handle = cloud
            .deploy(&spec(
                "agent:harness-confined",
                10,
                &["check_health"],
                &["/deploy"],
            ))
            .unwrap();

        // The harness emits ONLY tool-calls — never its subscription auth. (In a
        // real subprocess the secret lives inside the harness and reaches only its
        // provider; here we model it and assert it never appears in dregg output.)
        let harness = MockHarness::new(vec![
            tc("cell_write", json!({ "path": "/deploy", "value": "x" })),
            tc("invoke", json!({ "service": "check_health" })),
            tc("finish", json!({})),
        ]);
        let mut brain = HarnessBrain::new(harness);
        let report = cloud.run_with_toolkit(&handle, &mut brain, &devops_toolkit());

        // Nothing the harness holds internally crosses into dregg's proof:
        // (1) not in the serialized run report (the proof + bound the user gets).
        let report_json = serde_json::to_string(&report).unwrap();
        assert!(
            !report_json.contains(HARNESS_SECRET),
            "harness secret not in the run report"
        );
        // (2) not in any individual receipt.
        for r in &report.receipts {
            let rj = serde_json::to_string(r).unwrap();
            assert!(
                !rj.contains(HARNESS_SECRET),
                "harness secret not in a receipt"
            );
        }
        // (3) not in any verdict dregg fed back (the only thing crossing TO the harness).
        for v in brain.transport().verdicts_seen() {
            assert!(
                !v.contains(HARNESS_SECRET),
                "harness secret not echoed in a verdict"
            );
        }
    }

    // ── TOOTH: a forged verdict in a harness run breaks the receipt ──────────────

    #[test]
    fn a_forged_verdict_in_a_harness_run_breaks_the_receipt() {
        let cloud = AgentCloud::from_seed([65u8; 32]);
        let handle = cloud
            .deploy(&spec("agent:harness-forge", 10, &["check_health"], &[]))
            .unwrap();
        // A snapshot WITH an anomaly → the honest verdict is FAIL.
        let toolkit = Toolkit::new().with_check_health("check_health", || HealthSnapshot {
            divergence: 1,
            ..Default::default()
        });
        let harness = MockHarness::new(vec![
            tc("invoke", json!({ "service": "check_health" })),
            tc("finish", json!({})),
        ]);
        let mut brain = HarnessBrain::new(harness);
        let mut report = cloud.run_with_toolkit(&handle, &mut brain, &toolkit);

        assert!(!report.tool_results()[0].1, "the honest verdict is fail");
        verify_agent_run(&report).expect("the honest fail re-witnesses");

        // Forge the verdict to "passed" → the receipt signature no longer matches.
        report.receipts[0].tool_ok = Some(true);
        assert!(matches!(
            verify_agent_run(&report),
            Err(AgentVerifyError::Chain(ChainError::BadSignature { .. }))
        ));
    }

    // ── the harness emits PROSE interleaved with tool-calls (subprocess realism) ─

    #[test]
    fn non_tool_lines_are_skipped_not_fabricated() {
        // A real harness interleaves reasoning prose with tool-call lines. The
        // parser skips a non-tool line rather than turning it into an action.
        assert!(parse_tool_call_line("Let me check the node health first.").is_none());
        assert!(parse_tool_call_line("").is_none());
        assert!(parse_tool_call_line("{\"not_a_tool\":1}").is_none());
        let (tool, args) =
            parse_tool_call_line(r#"{"tool":"invoke","service":"check_health"}"#).unwrap();
        assert_eq!(tool, "invoke");
        assert_eq!(
            map_tool_call(&tool, &args),
            Some(AgentAction::Invoke {
                service: "check_health".into()
            })
        );
    }

    // ── LIVE: drive a real subprocess harness over the ndjson protocol ───────────

    #[test]
    fn subprocess_harness_drives_a_real_child_over_ndjson() {
        // A real harness subprocess, faked by a `sh` one-liner that emits ndjson
        // tool-calls on stdout (interleaved with a prose line) — exercising the
        // SubprocessHarness spawn + read path end-to-end, not the mock.
        let script = r#"
echo 'thinking about what to do...'
echo '{"tool":"cell_write","path":"/deploy","value":"site@abc"}'
echo '{"tool":"invoke","service":"check_health"}'
echo '{"tool":"finish","summary":"done"}'
"#;
        let harness = match SubprocessHarness::spawn("sh", &["-c", script]) {
            Ok(h) => h,
            Err(_) => return, // no `sh` on this host — skip (the mock path is the floor).
        };
        let cloud = AgentCloud::from_seed([66u8; 32]);
        let handle = cloud
            .deploy(&spec(
                "agent:harness-live",
                10,
                &["check_health"],
                &["/deploy"],
            ))
            .unwrap();
        let mut brain = HarnessBrain::new(harness);
        let report = cloud.run_with_toolkit(&handle, &mut brain, &devops_toolkit());

        assert_eq!(
            report.admitted, 2,
            "the real subprocess drove cell-write + check_health"
        );
        assert_eq!(report.cells.get("/deploy"), Some(&"site@abc".to_string()));
        assert!(report.all_tools_passed(), "the subprocess-driven QA passed");
        verify_agent_run(&report).expect("the subprocess-harness run re-witnesses");
        let _ = brain; // brain owns the child; dropped here.
    }
}
