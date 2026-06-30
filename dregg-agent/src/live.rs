//! `live` — the **flexible live run**: the `run.json` artifact a real adaptive
//! agent emits, and its host-untrusted re-witness.
//!
//! The agent takes an **arbitrary natural-language goal** + a budget + a cap
//! bundle and runs a real reason → act → observe loop on a live model: the model
//! decides the next tool call, the run loop cap-gates + meters + receipts it, runs
//! it for real, and feeds the result back. A judge can hand it a *different* goal
//! and watch it adapt — that is the proof it is not scripted.
//!
//! [`LiveRun`] is the whole record (goal · model · the granted bundle · the
//! receipt chain · the narrated transcript); [`verify_live`] re-witnesses it
//! offline (chain intact + signed, the spend bound holds, the sub-agent chain
//! too), so `dregg-agent verify run.json` needs only the file. A tampered
//! line breaks the ed25519 receipt signature.

use serde::{Deserialize, Serialize};

use crate::agent::{ActionOutcome, AgentRunReport, verify_agent_run};

/// One narrated step of the reason → act → observe loop (derived from the signed
/// run log + receipts — every line traces to a receipt or a refusal).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LiveStep {
    /// The 1-based step ordinal.
    pub n: u64,
    /// The action label the model decided (`git_clone:…`, `shell:…`, `spend:…`).
    pub action: String,
    /// `admitted` / `cap-refused: <cap>` / `budget-refused (headroom N)`.
    pub outcome: String,
    /// For an admitted tool call: the real tool verdict summary (truncated).
    pub tool_summary: Option<String>,
    /// The budget units this step drew (0 for a refusal).
    pub cost: i64,
}

/// The whole live run — the `run.json` a non-witness re-verifies offline.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LiveRun {
    /// The natural-language goal the agent was given.
    pub goal: String,
    /// The model id that drove it (e.g. `nvidia/llama-3.3-nemotron-super-49b-v1`).
    pub model: String,
    /// The provider endpoint (no key — the key never enters the record).
    pub endpoint: String,
    /// How the budget was funded — an honest source note (operator allowance, or a
    /// real Stripe test PaymentIntent when a test key is present).
    pub funding: String,
    /// The budget ceiling, in cents.
    pub budget_cents: i64,
    /// The granted cap bundle (display form; a resource prefix renders with `*`).
    pub caps: Vec<String>,
    /// The workdir the operator tools were confined to.
    pub workdir: String,
    /// The main agent run — one re-witnessable receipt chain.
    pub run: AgentRunReport,
    /// An optional forked sub-agent run (the SCALE / attenuation demo).
    pub subagent_run: Option<AgentRunReport>,
    /// The narrated reason → act → observe transcript.
    pub transcript: Vec<LiveStep>,
}

impl LiveRun {
    /// The real tool calls the agent made (admitted ops/invokes), for a quick
    /// "what did it actually do?" rollup.
    pub fn tool_calls(&self) -> usize {
        self.run.receipts.len()
    }
}

/// Build the narrated transcript from a run report's signed log + receipts. Every
/// admitted step is paired with its receipt (verdict + cost) in order.
pub fn transcript_of(report: &AgentRunReport) -> Vec<LiveStep> {
    let mut steps = Vec::new();
    let mut ri = 0usize;
    for (i, rec) in report.log.iter().enumerate() {
        let (outcome, tool_summary, cost) = match &rec.outcome {
            ActionOutcome::Admitted => {
                let r = report.receipts.get(ri);
                ri += 1;
                (
                    "admitted".to_string(),
                    r.and_then(|r| r.tool_summary.clone()),
                    r.map(|r| r.cost).unwrap_or(0),
                )
            }
            ActionOutcome::CapRefused { cap } => {
                (format!("REFUSED — outside the cap bundle ({cap})"), None, 0)
            }
            ActionOutcome::BudgetRefused { headroom } => (
                format!("REFUSED in-band — over budget (headroom {headroom}); no effect"),
                None,
                0,
            ),
        };
        steps.push(LiveStep {
            n: (i + 1) as u64,
            action: rec.action.clone(),
            outcome,
            tool_summary,
            cost,
        });
    }
    steps
}

/// What re-witnessing a [`LiveRun`] confirmed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LiveVerified {
    /// Admitted actions in the main chain.
    pub actions: usize,
    /// Budget consumed (≤ ceiling).
    pub consumed: i64,
    /// Un-drawn headroom (the could-have bound).
    pub headroom: i64,
    /// The budget ceiling.
    pub budget: i64,
    /// Admitted actions in the sub-agent chain (0 if none).
    pub subagent_actions: usize,
}

/// **Re-witness a live run offline, trusting no host:** the main receipt chain is
/// signed + unbroken + tamper-evident; consumed stays at/under the ceiling and
/// agrees with the chain tip; the sub-agent chain (if any) re-witnesses too.
pub fn verify_live(run: &LiveRun) -> Result<LiveVerified, String> {
    let main = verify_agent_run(&run.run).map_err(|e| format!("agent run: {e}"))?;
    if run.run.budget != run.budget_cents {
        return Err(format!(
            "budget mismatch: report {} != funded {}",
            run.run.budget, run.budget_cents
        ));
    }
    let subagent_actions = match &run.subagent_run {
        Some(sub) => {
            verify_agent_run(sub)
                .map_err(|e| format!("sub-agent run: {e}"))?
                .actions
        }
        None => 0,
    };
    Ok(LiveVerified {
        actions: main.actions,
        consumed: main.consumed,
        headroom: main.headroom,
        budget: main.budget,
        subagent_actions,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::agent::{AgentAction, AgentCloud, AgentSpec, PlannedBrain, ToolCall};
    use crate::toolkit::Toolkit;
    use crate::tools::{OperatorTools, ShellOut};
    use std::path::Path;

    fn op(tool: &str, kv: &[(&str, &str)]) -> AgentAction {
        AgentAction::Op(ToolCall::new(
            tool,
            kv.iter().map(|(k, v)| (k.to_string(), v.to_string())),
        ))
    }

    #[test]
    fn a_live_run_record_re_witnesses_and_a_tamper_is_caught() {
        let wd = std::env::temp_dir().join(format!("dregg-live-{}", std::process::id()));
        std::fs::create_dir_all(&wd).unwrap();
        let cloud = AgentCloud::from_seed([90u8; 32]);
        let handle = cloud
            .deploy(&AgentSpec::new("agent:live", 100).with_shell())
            .unwrap();
        let toolkit =
            OperatorTools::new(Toolkit::new(), &wd).with_shell(|cmd: &str, _cwd: &Path| {
                Ok(ShellOut {
                    exit: 0,
                    stdout: format!("ok: {cmd}"),
                    stderr: String::new(),
                    new_cwd: None,
                })
            });
        let report = cloud.run_with_toolkit(
            &handle,
            &mut PlannedBrain::new(vec![op("shell", &[("cmd", "echo hi")])]),
            &toolkit,
        );
        let mut run = LiveRun {
            goal: "say hi".into(),
            model: "test".into(),
            endpoint: "test".into(),
            funding: "operator allowance".into(),
            budget_cents: 100,
            caps: handle.caps.clone(),
            workdir: wd.to_string_lossy().into(),
            transcript: transcript_of(&report),
            run: report,
            subagent_run: None,
        };
        let v = verify_live(&run).expect("the live run re-witnesses");
        assert_eq!(v.actions, 1);
        assert_eq!(run.transcript.len(), 1);
        assert_eq!(run.transcript[0].outcome, "admitted");

        // Tamper a receipt verdict → BadSignature on re-witness.
        run.run.receipts[0].tool_ok = Some(false);
        assert!(verify_live(&run).is_err(), "the tamper is caught");
        std::fs::remove_dir_all(&wd).ok();
    }
}
